//! Independent certificate validation. Reconstruct the method tree, check all
//! inherited task ordering against a linearization, and replay primitive state
//! transitions. No search flaw lists or BinaryOrderings are used here.
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use super::model::Problem;
use super::plan::{Decomposition, Occurrence};

#[derive(Clone, Debug)]
pub struct Certificate {
    pub root: usize,
    /// Every primitive occurrence exactly once, in execution order.
    pub steps: Vec<Occurrence>,
    pub decompositions: Vec<Decomposition>,
}

impl Certificate {
    /// Grounded PANDA certificate. Keep generated guards/noops and original
    /// task/method names so pandaPIparser can reconstruct the source hierarchy.
    pub fn to_panda(&self, problem: &Problem) -> Result<String, String> {
        validate(problem, self)?;
        let mut out = String::from("==>\n");
        for step in &self.steps {
            writeln!(out, "{} {}", step.id, problem.tasks[step.task].name).unwrap();
        }
        writeln!(out, "root {}", self.root).unwrap();
        for decomposition in &self.decompositions {
            write!(
                out,
                "{} {} -> {}",
                decomposition.parent.id,
                problem.tasks[decomposition.parent.task].name,
                problem.methods[decomposition.method].name
            )
            .unwrap();
            for child in &decomposition.children {
                write!(out, " {}", child.id).unwrap();
            }
            out.push('\n');
        }
        out.push_str("<==\n");
        Ok(out)
    }
}

/// Returns the independently recomputed primitive action cost.
pub fn validate(problem: &Problem, certificate: &Certificate) -> Result<u64, String> {
    let valid_id = |id| id != 0 && id != usize::MAX;
    if !valid_id(certificate.root) {
        return Err("invalid root occurrence ID".into());
    }
    let mut leaves = HashMap::new();
    for (position, step) in certificate.steps.iter().enumerate() {
        if !valid_id(step.id) || step.task >= problem.actions.len() {
            return Err("invalid primitive occurrence".into());
        }
        if leaves.insert(step.id, (step.task, position)).is_some() {
            return Err("duplicate primitive occurrence".into());
        }
    }
    let mut decompositions = HashMap::new();
    for d in &certificate.decompositions {
        if !valid_id(d.parent.id)
            || leaves.contains_key(&d.parent.id)
            || decompositions.insert(d.parent.id, d).is_some()
        {
            return Err("duplicate or invalid decomposed occurrence".into());
        }
    }
    let mut pending = vec![Occurrence {
        id: certificate.root,
        task: problem.root,
    }];
    let mut seen = HashSet::new();
    let mut traversal = Vec::new();
    while let Some(expected) = pending.pop() {
        if !valid_id(expected.id) || !seen.insert(expected.id) {
            return Err("decomposition reuses an occurrence or contains a cycle".into());
        }
        if expected.task < problem.actions.len() {
            if leaves.get(&expected.id).map(|&(task, _)| task) != Some(expected.task) {
                return Err(
                    "required primitive occurrence is missing or has the wrong task".into(),
                );
            }
        } else {
            let d = decompositions
                .get(&expected.id)
                .ok_or("compound occurrence has no decomposition")?;
            let method = problem.methods.get(d.method).ok_or("unknown method")?;
            if d.parent != expected
                || method.task != expected.task
                || d.children.len() != method.subtasks.len()
                || d.children
                    .iter()
                    .zip(&method.subtasks)
                    .any(|(child, &task)| child.task != task)
            {
                return Err("decomposition does not instantiate its method".into());
            }
            pending.extend(d.children.iter().copied());
        }
        traversal.push(expected);
    }
    if seen.len() != leaves.len() + decompositions.len() {
        return Err("certificate contains occurrences outside the root decomposition".into());
    }
    // Descendant spans certify that EVERY primitive below an ordered child
    // precedes EVERY primitive below its successor. Empty children have no span.
    let mut spans: HashMap<usize, Option<(usize, usize)>> = HashMap::new();
    for occurrence in traversal.into_iter().rev() {
        if let Some(&(_, position)) = leaves.get(&occurrence.id) {
            spans.insert(occurrence.id, Some((position, position)));
            continue;
        }
        let d = decompositions[&occurrence.id];
        let method = &problem.methods[d.method];
        let mut edges = vec![Vec::new(); d.children.len()];
        for &(a, b) in &method.orderings {
            edges[a].push(b);
        }
        for a in 0..d.children.len() {
            let Some((_, last_a)) = spans[&d.children[a].id] else {
                continue;
            };
            let mut reachable = vec![false; d.children.len()];
            let mut stack = edges[a].clone();
            while let Some(b) = stack.pop() {
                if reachable[b] {
                    continue;
                }
                reachable[b] = true;
                if let Some((first_b, _)) = spans[&d.children[b].id] {
                    if last_a >= first_b {
                        return Err("linearization violates method ordering".into());
                    }
                }
                // Follow paths through empty children too: A < empty < B
                // still entails A < B after decomposition.
                stack.extend(&edges[b]);
            }
        }
        let span = d
            .children
            .iter()
            .filter_map(|c| spans[&c.id])
            .reduce(|(lo, hi), (a, b)| (lo.min(a), hi.max(b)));
        spans.insert(occurrence.id, span);
    }
    let mut state = vec![false; problem.facts.len()];
    for &fact in &problem.initial {
        state[fact] = true;
    }
    let mut cost = 0u64;
    for step in &certificate.steps {
        let action = &problem.actions[step.task];
        if action.preconditions.iter().any(|&f| !state[f]) {
            return Err(format!(
                "occurrence {} has an unsatisfied precondition",
                step.id
            ));
        }
        for &fact in &action.delete {
            state[fact] = false;
        }
        for &fact in &action.add {
            state[fact] = true;
        }
        cost = cost
            .checked_add(action.cost)
            .ok_or("certificate cost overflow")?;
    }
    if problem.goal.iter().any(|&f| !state[f]) {
        return Err("final state does not satisfy the goal".into());
    }
    Ok(cost)
}
