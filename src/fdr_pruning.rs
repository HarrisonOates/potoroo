//! Finite-domain recursion and minimality pruning.
//!
//! Implements exact recursion (Smith & Peot, AIPS 1996) and cutset minimality
//! (Kambhampati, IJCAI 1995). Ground facts permit exact equality checks.
//! The fact/operator graph filters recursion candidates using SCCs and
//! memoizes reachability queries.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::fdr::{Fact, Task};
use crate::fdr_pocl::{CausalLink, PartialPlan};
use crate::orderings::{BinaryOrderings, StepTime};
use crate::plan::{GOAL_ID, INIT_ID};

/// Returns true iff `before` is necessarily before `after`.
fn necessarily_before(orderings: &BinaryOrderings, before: usize, after: usize) -> bool {
    before != after && !orderings.possibly_after(before, StepTime::AtEnd, after, StepTime::AtStart)
}

/// Returns true iff `before` could still come before `after`.
fn possibly_before(orderings: &BinaryOrderings, before: usize, after: usize) -> bool {
    orderings.possibly_before(before, StepTime::AtEnd, after, StepTime::AtStart)
}

// ---------------------------------------------------------------------------
// The operator graph
// ---------------------------------------------------------------------------

/// The operator graph of a finite-domain task: facts and operators, with its
/// strongly connected components.
#[derive(Debug)]
pub struct FactGraph {
    /// First fact index of each variable, so a fact's node is
    /// `var_base[variable] + value`.
    var_base: Vec<usize>,
    /// Number of fact nodes; operator `o` is node `n_facts + o`.
    n_facts: usize,
    /// Node adjacency: fact -> achieving operators, operator -> required facts.
    adjacency: Vec<Vec<usize>>,
    /// Component id per node.
    component: Vec<usize>,
    /// Operator ids in each component.
    operators_in_component: Vec<Vec<usize>>,
    /// Whether each fact node lies on a cycle.
    cyclic: Vec<bool>,
    /// Memoised relevant-operator sets, keyed by fact node.
    relevant: RefCell<HashMap<usize, Rc<HashSet<usize>>>>,
}

impl FactGraph {
    /// Builds the graph and its components.
    pub fn build(task: &Task) -> Self {
        let mut var_base = Vec::with_capacity(task.variables.len() + 1);
        let mut n_facts = 0usize;
        for variable in &task.variables {
            var_base.push(n_facts);
            n_facts += variable.values.len();
        }
        var_base.push(n_facts);

        let total = n_facts + task.operators.len();
        let mut adjacency: Vec<Vec<usize>> = vec![Vec::new(); total];
        for (operator_id, operator) in task.operators.iter().enumerate() {
            let node = n_facts + operator_id;
            // Operator -> the facts it requires. Over-approximated with the
            // conditions of conditional effects: a larger graph merges more into
            // its components, which makes both uses of this graph decline to
            // prune more often, never less.
            for fact in operator.preconditions() {
                if let Some(index) = fact_node(&var_base, fact) {
                    adjacency[node].push(index);
                }
            }
            for effect in &operator.effects {
                for &condition in &effect.conditions {
                    if let Some(index) = fact_node(&var_base, condition) {
                        adjacency[node].push(index);
                    }
                }
                // Fact -> the operators that can assign it.
                if let Some(index) = fact_node(&var_base, effect.assignment()) {
                    adjacency[index].push(node);
                }
            }
        }
        for row in &mut adjacency {
            row.sort_unstable();
            row.dedup();
        }

        let component = crate::opgraph::tarjan(&adjacency);
        let mut component_size = vec![0usize; total];
        for &id in &component {
            component_size[id] += 1;
        }
        let mut operators_in_component: Vec<Vec<usize>> = vec![Vec::new(); total];
        for operator_id in 0..task.operators.len() {
            operators_in_component[component[n_facts + operator_id]].push(operator_id);
        }
        let cyclic = (0..n_facts)
            .map(|node| component_size[component[node]] > 1 || adjacency[node].contains(&node))
            .collect();

        FactGraph {
            var_base,
            n_facts,
            adjacency,
            component,
            operators_in_component,
            cyclic,
            relevant: RefCell::new(HashMap::new()),
        }
    }

    /// Whether a fact's node lies on a cycle — Theorem 2's filter.
    pub fn may_recurse(&self, fact: Fact) -> bool {
        fact_node(&self.var_base, fact).is_some_and(|node| self.cyclic[node])
    }

    /// Operator ids in the same component as a fact.
    fn operators_in_scc(&self, fact: Fact) -> Option<&[usize]> {
        let node = fact_node(&self.var_base, fact)?;
        Some(&self.operators_in_component[self.component[node]])
    }

    /// Operators that could take part in achieving a fact, computed once per
    /// fact and remembered.
    fn relevant_operators(&self, fact: Fact) -> Option<Rc<HashSet<usize>>> {
        let node = fact_node(&self.var_base, fact)?;
        if let Some(cached) = self.relevant.borrow().get(&node) {
            return Some(cached.clone());
        }
        let mut seen = vec![false; self.adjacency.len()];
        let mut stack = vec![node];
        seen[node] = true;
        let mut operators = HashSet::new();
        while let Some(current) = stack.pop() {
            if current >= self.n_facts {
                operators.insert(current - self.n_facts);
            }
            for &next in &self.adjacency[current] {
                if !seen[next] {
                    seen[next] = true;
                    stack.push(next);
                }
            }
        }
        let shared = Rc::new(operators);
        self.relevant.borrow_mut().insert(node, shared.clone());
        Some(shared)
    }
}

fn fact_node(var_base: &[usize], fact: Fact) -> Option<usize> {
    let base = *var_base.get(fact.variable)?;
    let end = *var_base.get(fact.variable + 1)?;
    let index = base + fact.value;
    (index < end).then_some(index)
}

// ---------------------------------------------------------------------------
// Recursion
// ---------------------------------------------------------------------------

/// A recursion found in a plan: the links it regresses through, and the steps
/// inside the loop.
#[derive(Debug, Clone)]
pub struct Recursion {
    root_links: Vec<CausalLink>,
    region: HashSet<usize>,
}

/// Whether the recursion rule could fire on this plan.
///
/// Allocation-free: an open condition on a cycle whose fact already labels a
/// link in the plan. Everything else stops here.
pub fn recursion_may_apply(plan: &PartialPlan, graph: &FactGraph) -> bool {
    if plan.links.is_empty() || plan.open_conditions.is_empty() {
        return false;
    }
    plan.open_conditions.iter().any(|open| {
        graph.may_recurse(open.condition)
            && plan
                .links
                .iter()
                .any(|link| link.condition == open.condition)
    })
}

/// Whether the plan can be discarded by Smith & Peot's Theorem 1 or Theorem 4.
///
/// Call [`recursion_may_apply`] first; this assumes it passed.
pub fn recursion_prunable(plan: &PartialPlan, task: &Task, graph: &FactGraph) -> bool {
    let Some((anchor, recursion)) = plan.open_conditions.iter().find_map(|open| {
        suspension_of(plan, task, graph, open.condition, open.consumer)
            .map(|recursion| (open.clone(), recursion))
    }) else {
        return false;
    };

    // Theorem 1: every open condition suspended, as a recursion in its own
    // right or as a loop predecessor of one, and no unresolved threats.
    if plan.threats(task).is_empty() {
        let all_suspended = plan.open_conditions.iter().all(|open| {
            open == &anchor
                || is_loop_predecessor(plan, open.consumer, &recursion)
                || suspension_of(plan, task, graph, open.condition, open.consumer).is_some()
        });
        if all_suspended {
            return true;
        }
    }

    theorem_four(plan, task, graph, anchor.condition, &recursion)
}

/// The recursion suspending an open condition, if any.
fn suspension_of(
    plan: &PartialPlan,
    task: &Task,
    graph: &FactGraph,
    condition: Fact,
    consumer: usize,
) -> Option<Recursion> {
    if !graph.may_recurse(condition) {
        return None;
    }
    let recursion = recursion_of(plan, condition, consumer)?;
    if links_out_of_region(plan, &recursion) {
        return None;
    }
    if has_loop_threat(plan, task, condition, &recursion) {
        return None;
    }
    Some(recursion)
}

/// Definition 1: every causal-link path from the open condition to the goal
/// crosses a link carrying the same fact, and those links' producers are
/// mutually unordered.
fn recursion_of(plan: &PartialPlan, condition: Fact, consumer: usize) -> Option<Recursion> {
    if goal_reachable_avoiding(plan, consumer, condition) {
        return None;
    }
    let forward = reachable_forward(plan, consumer);
    let to_goal = reaches_goal(plan);
    let root_links: Vec<CausalLink> = plan
        .links
        .iter()
        .filter(|link| {
            link.condition == condition
                && to_goal.contains(&link.producer)
                && forward.contains(&link.producer)
        })
        .cloned()
        .collect();
    if root_links.is_empty() {
        return None;
    }

    for (i, left) in root_links.iter().enumerate() {
        for right in &root_links[i + 1..] {
            if left.producer == right.producer {
                continue;
            }
            if necessarily_before(&plan.orderings, left.producer, right.producer)
                || necessarily_before(&plan.orderings, right.producer, left.producer)
            {
                return None;
            }
        }
    }

    let producers: HashSet<usize> = root_links.iter().map(|link| link.producer).collect();
    let reaches_producer = reachable_backward_from(plan, &producers);
    let region: HashSet<usize> = forward.intersection(&reaches_producer).copied().collect();

    Some(Recursion { root_links, region })
}

/// Definition 3, read generously: any step with an effect that could clobber the
/// condition and that is not already ordered after the whole loop counts as a
/// loop threat. Over-counting suspends less and so prunes less, which is the
/// safe direction.
fn has_loop_threat(
    plan: &PartialPlan,
    task: &Task,
    condition: Fact,
    recursion: &Recursion,
) -> bool {
    for step in plan.steps.iter() {
        if recursion.region.contains(&step.id) {
            continue;
        }
        let threatens = task.operators[step.operator]
            .effects
            .iter()
            .any(|effect| effect.variable == condition.variable && effect.post != condition.value);
        if !threatens {
            continue;
        }
        let after_everything = recursion
            .root_links
            .iter()
            .all(|link| !possibly_before(&plan.orderings, step.id, link.consumer));
        if !after_everything {
            return true;
        }
    }
    false
}

/// Smith & Peot's first re-enabling event: a link leaving the loop region for a
/// consumer outside it.
fn links_out_of_region(plan: &PartialPlan, recursion: &Recursion) -> bool {
    let root_consumers: HashSet<usize> = recursion
        .root_links
        .iter()
        .map(|link| link.consumer)
        .collect();
    plan.links.iter().any(|link| {
        recursion.region.contains(&link.producer)
            && !recursion.region.contains(&link.consumer)
            && !root_consumers.contains(&link.consumer)
    })
}

/// Definition 2: every causal-link path from this open condition to the goal
/// crosses a root link.
fn is_loop_predecessor(plan: &PartialPlan, consumer: usize, recursion: &Recursion) -> bool {
    let roots: HashSet<(usize, usize)> = recursion
        .root_links
        .iter()
        .map(|link| (link.producer, link.consumer))
        .collect();
    let mut seen: HashSet<usize> = HashSet::from([consumer]);
    let mut stack = vec![consumer];
    while let Some(node) = stack.pop() {
        if node == GOAL_ID {
            return false;
        }
        for link in plan.links.iter().filter(|link| link.producer == node) {
            if roots.contains(&(link.producer, link.consumer)) {
                continue;
            }
            if seen.insert(link.consumer) {
                stack.push(link.consumer);
            }
        }
    }
    true
}

/// Theorem 4: prune while open conditions remain, when none of them can reach
/// into the loop or threaten a root link.
fn theorem_four(
    plan: &PartialPlan,
    task: &Task,
    graph: &FactGraph,
    anchor: Fact,
    recursion: &Recursion,
) -> bool {
    let Some(scc_operators) = graph.operators_in_scc(anchor) else {
        return false;
    };

    let mut relevant: HashSet<usize> = HashSet::new();
    for open in plan.open_conditions.iter() {
        if open.condition == anchor {
            continue;
        }
        match graph.relevant_operators(open.condition) {
            Some(operators) => relevant.extend(operators.iter().copied()),
            None => return false,
        }
    }

    // (1) No relevant operator lies in the anchor's component.
    if relevant.iter().any(|id| scc_operators.contains(id)) {
        return false;
    }

    // (2) No relevant operator threatens a root link.
    for &operator_id in &relevant {
        for effect in &task.operators[operator_id].effects {
            for link in &recursion.root_links {
                if effect.variable == link.condition.variable && effect.post != link.condition.value
                {
                    return false;
                }
            }
        }
    }

    // (3) No unresolved threat to a root link.
    for threat in plan.threats(task) {
        let threatened = &plan.links[threat.link];
        if recursion.root_links.iter().any(|link| {
            link.producer == threatened.producer && link.consumer == threatened.consumer
        }) {
            return false;
        }
    }

    true
}

// -- causal-link reachability ------------------------------------------------

fn goal_reachable_avoiding(plan: &PartialPlan, start: usize, cut: Fact) -> bool {
    let mut seen: HashSet<usize> = HashSet::from([start]);
    let mut stack = vec![start];
    while let Some(node) = stack.pop() {
        if node == GOAL_ID {
            return true;
        }
        for link in plan.links.iter().filter(|link| link.producer == node) {
            if link.condition == cut {
                continue;
            }
            if seen.insert(link.consumer) {
                stack.push(link.consumer);
            }
        }
    }
    false
}

fn reachable_forward(plan: &PartialPlan, start: usize) -> HashSet<usize> {
    let mut seen: HashSet<usize> = HashSet::from([start]);
    let mut stack = vec![start];
    while let Some(node) = stack.pop() {
        for link in plan.links.iter().filter(|link| link.producer == node) {
            if seen.insert(link.consumer) {
                stack.push(link.consumer);
            }
        }
    }
    seen
}

fn reaches_goal(plan: &PartialPlan) -> HashSet<usize> {
    reachable_backward_from(plan, &HashSet::from([GOAL_ID]))
}

fn reachable_backward_from(plan: &PartialPlan, seeds: &HashSet<usize>) -> HashSet<usize> {
    let mut seen: HashSet<usize> = seeds.clone();
    let mut stack: Vec<usize> = seeds.iter().copied().collect();
    while let Some(node) = stack.pop() {
        for link in plan.links.iter().filter(|link| link.consumer == node) {
            if seen.insert(link.producer) {
                stack.push(link.producer);
            }
        }
    }
    seen
}

// ---------------------------------------------------------------------------
// Minimality
// ---------------------------------------------------------------------------

/// Whether the minimality rule could fire on this plan.
pub fn minimality_may_apply(plan: &PartialPlan) -> bool {
    plan.steps.len() >= 3 && !plan.links.is_empty()
}

/// Conditions of links necessarily spanning `step`.
fn np_cutset(plan: &PartialPlan, step: usize) -> Vec<Fact> {
    plan.links
        .iter()
        .filter(|link| {
            link.producer != step
                && link.consumer != step
                && necessarily_before(&plan.orderings, link.producer, step)
                && necessarily_before(&plan.orderings, step, link.consumer)
        })
        .map(|link| link.condition)
        .collect()
}

/// Conditions of links possibly spanning `step`, plus those supporting it.
fn pp_cutset(plan: &PartialPlan, step: usize) -> Vec<Fact> {
    plan.links
        .iter()
        .filter(|link| {
            if link.consumer == step {
                return true;
            }
            link.producer != step
                && possibly_before(&plan.orderings, link.producer, step)
                && possibly_before(&plan.orderings, step, link.consumer)
        })
        .map(|link| link.condition)
        .collect()
}

fn step_strictly_between(plan: &PartialPlan, before: usize, after: usize) -> bool {
    plan.steps.iter().any(|step| {
        necessarily_before(&plan.orderings, before, step.id)
            && necessarily_before(&plan.orderings, step.id, after)
    })
}

/// Kambhampati's cutset-prune, over finite-domain facts.
///
/// The reading is [`crate::minimality`]'s, including both guards it adds to the
/// published statement: the possibly-spanning set takes in the links that
/// *terminate* at `s″`, and some step must lie strictly between the two anchors.
pub fn minimality_prunable(plan: &PartialPlan) -> bool {
    let candidates = plan
        .steps
        .iter()
        .map(|step| step.id)
        .chain(std::iter::once(GOAL_ID));

    for second in candidates {
        let precedes = plan.open_conditions.iter().all(|open| {
            open.consumer == second || necessarily_before(&plan.orderings, open.consumer, second)
        });
        if !precedes {
            continue;
        }
        let inner = pp_cutset(plan, second);
        if inner.is_empty() {
            continue;
        }
        for first in plan.steps.iter().map(|step| step.id) {
            if first == second || first == INIT_ID {
                continue;
            }
            if !necessarily_before(&plan.orderings, first, second) {
                continue;
            }
            if !step_strictly_between(plan, first, second) {
                continue;
            }
            let outer = np_cutset(plan, first);
            if outer.len() >= inner.len() && inner.iter().all(|fact| outer.contains(fact)) {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fdr::{Effect, Operator, Variable};

    /// A two-location map with roads both ways: `at` is recursive, `rested` is
    /// not.
    fn travel_task() -> Task {
        Task {
            variables: vec![
                Variable {
                    name: "at".to_string(),
                    values: vec!["a".to_string(), "b".to_string()],
                },
                Variable {
                    name: "rested".to_string(),
                    values: vec!["no".to_string(), "yes".to_string()],
                },
            ],
            mutex_groups: vec![],
            initial: vec![0, 0],
            goals: vec![Fact::new(0, 1), Fact::new(1, 1)],
            operators: vec![
                Operator {
                    name: "drive-a-b".to_string(),
                    prevail: vec![],
                    effects: vec![Effect {
                        conditions: vec![],
                        variable: 0,
                        pre: Some(0),
                        post: 1,
                    }],
                    cost: 1,
                },
                Operator {
                    name: "drive-b-a".to_string(),
                    prevail: vec![],
                    effects: vec![Effect {
                        conditions: vec![],
                        variable: 0,
                        pre: Some(1),
                        post: 0,
                    }],
                    cost: 1,
                },
                Operator {
                    name: "sleep".to_string(),
                    prevail: vec![],
                    effects: vec![Effect {
                        conditions: vec![],
                        variable: 1,
                        pre: Some(0),
                        post: 1,
                    }],
                    cost: 1,
                },
            ],
            axioms: vec![],
        }
    }

    #[test]
    fn a_reversible_variable_lands_on_a_cycle() {
        let task = travel_task();
        let graph = FactGraph::build(&task);
        // `drive-a-b` needs at=a and gives at=b, `drive-b-a` the reverse, so
        // both values of `at` sit on a cycle through the two operators.
        assert!(graph.may_recurse(Fact::new(0, 0)));
        assert!(graph.may_recurse(Fact::new(0, 1)));
    }

    #[test]
    fn a_one_way_variable_does_not() {
        let task = travel_task();
        let graph = FactGraph::build(&task);
        // Nothing ever sets `rested` back to no, so it is on no cycle.
        assert!(!graph.may_recurse(Fact::new(1, 1)));
    }

    #[test]
    fn relevant_operators_are_memoised_and_transitive() {
        let task = travel_task();
        let graph = FactGraph::build(&task);
        let first = graph
            .relevant_operators(Fact::new(0, 1))
            .expect("at=b is a known fact");
        // Reaching at=b needs drive-a-b, which needs at=a, which needs
        // drive-b-a: both are relevant, `sleep` is not.
        assert!(first.contains(&0) && first.contains(&1));
        assert!(!first.contains(&2));
        let again = graph
            .relevant_operators(Fact::new(0, 1))
            .expect("at=b is a known fact");
        assert!(Rc::ptr_eq(&first, &again), "the set should be memoised");
    }

    #[test]
    fn neither_rule_applies_to_an_empty_plan() {
        let task = travel_task();
        let graph = FactGraph::build(&task);
        let plan = PartialPlan::initial(&task);
        assert!(!recursion_may_apply(&plan, &graph));
        assert!(!minimality_may_apply(&plan));
        assert!(!minimality_prunable(&plan));
    }
}
