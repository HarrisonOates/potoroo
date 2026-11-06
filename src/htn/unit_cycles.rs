//! Optional elimination of repeated tasks along unary decomposition chains.
//!
//! A unit method has exactly one compound subtask. In this strict grounded
//! model it adds no actions, conditions or internal orderings. A round trip
//! A -> ... -> A through unit methods can therefore be removed from a finite
//! decomposition tree without changing its primitive occurrences, inherited
//! orderings or cost. Every executable primitive plan has a representative
//! without such a round trip. The original method IDs remain in certificates.
//!
//! This deliberately removes some decomposition witnesses, unlike systematic
//! flaw selection alone. It does not prune recursion with siblings, even if
//! they are nullable or zero-cost, and does not ensure A* completeness. Compare
//! the broader empty/growing cycles in Yousefi et al., ICAPS 2025:
//! https://yousefi.ai/static/papers/Yousefi2025Incompleteness.pdf
use std::time::Instant;

use super::model::{MethodId, Problem};
use super::plan::{Occurrence, Plan};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum UnitCyclePolicy {
    /// Retain all decomposition histories, including unary round trips.
    #[default]
    Keep,
    /// Prune unary round trips; preserve primitive plans and their costs.
    Prune,
}

pub(crate) struct UnitCyclePruner {
    component: Vec<usize>,
    cyclic_method: Vec<bool>,
}

impl UnitCyclePruner {
    /// Iterative Kosaraju on unit edges only. Noncyclic methods never need a
    /// history scan. No per-plan fields or transitive closure are introduced.
    pub(crate) fn new(problem: &Problem, deadline: Option<Instant>) -> Option<Self> {
        let expired = || deadline.is_some_and(|d| Instant::now() >= d);
        let n = problem.tasks.len();
        let mut forward = vec![Vec::new(); n];
        let mut reverse = vec![Vec::new(); n];
        for method in &problem.methods {
            if expired() {
                return None;
            }
            if let [child] = method.subtasks.as_slice() {
                if !problem.tasks[*child].primitive {
                    forward[method.task].push(*child);
                    reverse[*child].push(method.task);
                }
            }
        }
        let mut visited = vec![false; n];
        let mut order = Vec::with_capacity(n);
        let mut stack = Vec::new();
        for root in 0..n {
            if expired() {
                return None;
            }
            if visited[root] {
                continue;
            }
            visited[root] = true;
            stack.push((root, 0));
            while let Some((task, next)) = stack.last_mut() {
                if expired() {
                    return None;
                }
                if let Some(&child) = forward[*task].get(*next) {
                    *next += 1;
                    if !visited[child] {
                        visited[child] = true;
                        stack.push((child, 0));
                    }
                } else {
                    order.push(*task);
                    stack.pop();
                }
            }
        }
        let mut component = vec![usize::MAX; n];
        let mut pending = Vec::new();
        for root in order.into_iter().rev() {
            if expired() {
                return None;
            }
            if component[root] != usize::MAX {
                continue;
            }
            component[root] = root;
            pending.push(root);
            while let Some(task) = pending.pop() {
                if expired() {
                    return None;
                }
                for &parent in &reverse[task] {
                    if expired() {
                        return None;
                    }
                    if component[parent] == usize::MAX {
                        component[parent] = root;
                        pending.push(parent);
                    }
                }
            }
        }
        let mut cyclic_method = Vec::with_capacity(problem.methods.len());
        for method in &problem.methods {
            if expired() {
                return None;
            }
            cyclic_method.push(matches!(method.subtasks.as_slice(), [child]
                if !problem.tasks[*child].primitive
                    && component[method.task] == component[*child]));
        }
        Some(Self {
            component,
            cyclic_method,
        })
    }

    /// Only the chosen occurrence's uninterrupted unit ancestry matters.
    /// Repetitions in siblings or above a branching method are independent.
    /// `None` means cancellation, never a pruning decision.
    pub(crate) fn prunes(
        &self,
        problem: &Problem,
        plan: &Plan,
        parent: Occurrence,
        method: MethodId,
        deadline: Option<Instant>,
    ) -> Option<bool> {
        if !self.cyclic_method[method] {
            return Some(false);
        }
        let target = problem.methods[method].subtasks[0];
        if target == parent.task {
            return Some(true);
        }
        let mut ancestor = parent.id;
        for decomposition in plan.decompositions() {
            if deadline.is_some_and(|d| Instant::now() >= d) {
                return None;
            }
            // Plan::decompose allocates each method's children contiguously.
            let Some(first) = decomposition.children.first() else {
                continue;
            };
            let last = decomposition.children.last().unwrap();
            if !(first.id..=last.id).contains(&ancestor) {
                continue;
            }
            if decomposition.children.len() != 1
                || self.component[decomposition.parent.task] != self.component[target]
            {
                return Some(false);
            }
            if decomposition.parent.task == target {
                return Some(true);
            }
            ancestor = decomposition.parent.id;
        }
        Some(false)
    }

    pub(crate) fn has_cycles(&self) -> bool {
        self.cyclic_method.iter().any(|&cyclic| cyclic)
    }
}
