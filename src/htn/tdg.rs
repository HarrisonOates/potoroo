//! Static task-decomposition graph relaxation. Methods are AND nodes and tasks
//! are OR nodes. Preconditions, deletes and orderings are ignored here.
//!
//! A generalized Dijkstra traversal settles nonnegative minimum primitive costs;
//! repeated child occurrences contribute repeatedly. Pure recursion stays
//! unreachable, while empty methods and recursive exits seed finite costs.
//!
//! Structural cost recurrence: Bercher et al., "An Admissible HTN Planning
//! Heuristic" (IJCAI 2017), Definitions 2–3. This does not yet implement the
//! paper's delete-relaxed reachability pruning or node-specific TDG updates.
//! https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.090/Publikationen/2017/Bercher17AdmissibleHTNHeuristic.pdf
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashSet, VecDeque};
use std::time::Instant;

use super::model::{FactId, MethodId, Problem, TaskId};
use super::plan::{Occurrence, Plan};

/// Bounds saturate one above the largest representable solution cost. This is
/// distinct from `None` (no finite decomposition), including for deep recursion.
pub const COST_CAP: u128 = u64::MAX as u128 + 1;

#[derive(Debug)]
pub struct Tdg {
    task_costs: Vec<Option<u128>>,
    method_costs: Vec<Option<u128>>,
    may_add: Vec<HashSet<FactId>>,
}

impl Tdg {
    pub fn new(problem: &Problem) -> Self {
        Self::with_deadline(problem, None).expect("no deadline")
    }

    /// `None` means cancellation, not structural unreachability.
    pub(crate) fn with_deadline(problem: &Problem, deadline: Option<Instant>) -> Option<Self> {
        let expired = || deadline.is_some_and(|d| Instant::now() >= d);
        let mut parents = vec![Vec::new(); problem.tasks.len()];
        let mut pending = Vec::with_capacity(problem.methods.len());
        let mut sums = vec![0u128; problem.methods.len()];
        let mut ready = BinaryHeap::new();
        for (task, action) in problem.actions.iter().enumerate() {
            ready.push(Reverse((action.cost as u128, task)));
        }
        for (id, method) in problem.methods.iter().enumerate() {
            if expired() {
                return None;
            }
            pending.push(method.subtasks.len());
            if method.subtasks.is_empty() {
                ready.push(Reverse((0, method.task)));
            }
            for &task in &method.subtasks {
                // Keep one edge per occurrence, not one per task schema.
                parents[task].push(id);
            }
        }
        let mut task_costs = vec![None; problem.tasks.len()];
        while let Some(Reverse((cost, task))) = ready.pop() {
            if expired() {
                return None;
            }
            if task_costs[task].is_some() {
                continue;
            }
            task_costs[task] = Some(cost);
            for &method in &parents[task] {
                if expired() {
                    return None;
                }
                sums[method] = (sums[method] + cost).min(COST_CAP);
                pending[method] -= 1;
                if pending[method] == 0 {
                    ready.push(Reverse((sums[method], problem.methods[method].task)));
                }
            }
        }
        let method_costs: Vec<_> = pending
            .iter()
            .zip(sums)
            .map(|(&left, sum)| (left == 0).then_some(sum))
            .collect();

        // Only productive methods can occur in a complete decomposition. These
        // edges propagate possible positive effects, never guaranteed effects.
        let mut productive_parents = vec![Vec::new(); problem.tasks.len()];
        for (id, method) in problem.methods.iter().enumerate() {
            if expired() {
                return None;
            }
            if method_costs[id].is_some() {
                for &task in &method.subtasks {
                    productive_parents[task].push(method.task);
                }
            }
        }
        for parents in &mut productive_parents {
            parents.sort_unstable();
            parents.dedup();
        }
        let mut may_add = vec![HashSet::new(); problem.tasks.len()];
        let mut effects = VecDeque::new();
        for (task, action) in problem.actions.iter().enumerate() {
            for &fact in &action.add {
                may_add[task].insert(fact);
                effects.push_back((task, fact));
            }
        }
        while let Some((task, fact)) = effects.pop_front() {
            if expired() {
                return None;
            }
            for &parent in &productive_parents[task] {
                if expired() {
                    return None;
                }
                if may_add[parent].insert(fact) {
                    effects.push_back((parent, fact));
                }
            }
        }
        if expired() {
            return None;
        }
        Some(Self {
            task_costs,
            method_costs,
            may_add,
        })
    }

    /// Minimum primitive cost of a decomposition, capped at `COST_CAP`.
    /// `None` proves there is no finite primitive decomposition.
    pub fn task_cost(&self, task: TaskId) -> Option<u128> {
        self.task_costs[task]
    }

    pub fn method_cost(&self, method: MethodId) -> Option<u128> {
        self.method_costs[method]
    }

    /// A conservative reachability test, not an abstract task's causal effect.
    pub fn may_add(&self, task: TaskId, fact: FactId) -> bool {
        self.may_add[task].contains(&fact)
    }

    pub(crate) fn method_may_add(&self, problem: &Problem, method: MethodId, fact: FactId) -> bool {
        self.method_cost(method).is_some()
            && problem.methods[method]
                .subtasks
                .iter()
                .any(|&task| self.may_add(task, fact))
    }

    /// Remaining primitive cost. Active primitives are already charged to g;
    /// only active compound *occurrences* contribute to h.
    pub fn remaining_cost(&self, problem: &Problem, plan: &Plan) -> Option<u128> {
        plan.tasks()
            .filter(|t| !problem.tasks[t.task].primitive)
            .try_fold(0u128, |sum, t| {
                self.task_cost(t.task).map(|c| (sum + c).min(COST_CAP))
            })
    }

    /// Check a method before allocating its children (which might overflow g).
    pub(crate) fn replacement_cost(
        &self,
        problem: &Problem,
        plan: &Plan,
        parent: Occurrence,
        method: MethodId,
    ) -> Option<u128> {
        let start = (plan.cost() as u128 + self.method_cost(method)?).min(COST_CAP);
        plan.tasks()
            .filter(|t| t.id != parent.id && !problem.tasks[t.task].primitive)
            .try_fold(start, |sum, t| {
                self.task_cost(t.task).map(|c| (sum + c).min(COST_CAP))
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::htn::{Action, Method, Task};

    #[test]
    fn partial_plan_bound_counts_only_remaining_compound_occurrences() {
        let problem = Problem::new(
            vec![],
            [2, 3]
                .into_iter()
                .map(|cost| Action {
                    cost,
                    preconditions: vec![],
                    add: vec![],
                    delete: vec![],
                })
                .collect(),
            (0..4)
                .map(|id| Task {
                    name: format!("t{id}"),
                    primitive: id < 2,
                })
                .collect(),
            vec![
                Method {
                    name: "pair".into(),
                    task: 2,
                    subtasks: vec![1, 1],
                    orderings: vec![],
                },
                Method {
                    name: "root".into(),
                    task: 3,
                    subtasks: vec![0, 2, 2],
                    orderings: vec![],
                },
            ],
            vec![],
            vec![],
            3,
        )
        .unwrap();
        let tdg = Tdg::new(&problem);
        let mut plan = Plan::initial(&problem);
        for (g, h, method) in [(0, 14, 1), (2, 12, 0), (8, 6, 0)] {
            assert_eq!(plan.cost(), g);
            assert_eq!(tdg.remaining_cost(&problem, &plan), Some(h));
            let parent = plan.compound(&problem).unwrap();
            assert_eq!(
                tdg.replacement_cost(&problem, &plan, parent, method),
                Some(14)
            );
            plan = plan.decompose(&problem, parent, method).unwrap().unwrap();
        }
        assert_eq!(plan.cost(), 14);
        assert_eq!(tdg.remaining_cost(&problem, &plan), Some(0));
    }
}
