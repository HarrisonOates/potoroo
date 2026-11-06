//! Modification-aware TDG guidance: estimate remaining decompositions and
//! causal-link insertions, not primitive action cost. See Bercher et al.,
//! IJCAI 2017, Definition 4:
//! https://bercher.net/publications/2017/Bercher2017AdmissibleHTNHeuristic.pdf
//!
//! Primitive task weights are their precondition counts; a compound costs one
//! decomposition plus its cheapest method's child weights. In a partial plan,
//! existing primitives are represented by its open conditions (including the
//! final goals), so established links are not charged again. Threat repairs and
//! ordering constraints are ignored: zero does not imply a solution.
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::time::Instant;

use super::model::{MethodId, Problem, TaskId};
use super::plan::Plan;
use super::refine::Refinement;

/// A static refinement-effort estimate, independent of action costs. Counts
/// saturate at `u128::MAX`; saturation never causes cost pruning or an error.
pub struct ModificationTdg {
    tasks: Vec<Option<u128>>,
    children: Vec<Option<u128>>,
}

impl ModificationTdg {
    pub fn new(problem: &Problem) -> Self {
        Self::with_deadline(problem, None).expect("no deadline")
    }

    pub(crate) fn with_deadline(problem: &Problem, deadline: Option<Instant>) -> Option<Self> {
        let expired = || deadline.is_some_and(|d| Instant::now() >= d);
        if expired() {
            return None;
        }
        let mut parents = vec![Vec::new(); problem.tasks.len()];
        let mut pending = Vec::with_capacity(problem.methods.len());
        let mut sums = vec![0u128; problem.methods.len()];
        let mut ready = BinaryHeap::new();
        for (task, action) in problem.actions.iter().enumerate() {
            if expired() {
                return None;
            }
            ready.push(Reverse((action.preconditions.len() as u128, task)));
        }
        for (id, method) in problem.methods.iter().enumerate() {
            if expired() {
                return None;
            }
            pending.push(method.subtasks.len());
            if method.subtasks.is_empty() {
                ready.push(Reverse((1, method.task)));
            }
            for &task in &method.subtasks {
                parents[task].push(id);
            }
        }
        let mut tasks = vec![None; problem.tasks.len()];
        while let Some(Reverse((effort, task))) = ready.pop() {
            if expired() {
                return None;
            }
            if tasks[task].is_some() {
                continue;
            }
            tasks[task] = Some(effort);
            for &method in &parents[task] {
                if expired() {
                    return None;
                }
                sums[method] = sums[method].saturating_add(effort);
                pending[method] -= 1;
                if pending[method] == 0 {
                    ready.push(Reverse((
                        sums[method].saturating_add(1),
                        problem.methods[method].task,
                    )));
                }
            }
        }
        if expired() {
            return None;
        }
        Some(Self {
            tasks,
            children: pending
                .into_iter()
                .zip(sums)
                .map(|(left, sum)| (left == 0).then_some(sum))
                .collect(),
        })
    }

    /// `None` means no finite primitive decomposition; it is not saturation.
    pub fn task_effort(&self, task: TaskId) -> Option<u128> {
        self.tasks[task]
    }

    /// Effort of a method's children, excluding the method application itself.
    pub fn subtask_effort(&self, method: MethodId) -> Option<u128> {
        self.children[method]
    }

    pub fn remaining_effort(&self, problem: &Problem, plan: &Plan) -> Option<u128> {
        plan.tasks()
            .filter(|t| !problem.tasks[t.task].primitive)
            .try_fold(plan.open_conditions().count() as u128, |sum, task| {
                self.tasks[task.task].map(|e| sum.saturating_add(e))
            })
    }

    pub(crate) fn after_refinement(
        &self,
        problem: &Problem,
        child: &Plan,
        refinement: Refinement,
        parent_effort: u128,
    ) -> u128 {
        // Subtraction from a saturated sum loses information. Rebuild the sum
        // in that rare case; ordinary refinements update it in constant time.
        if parent_effort == u128::MAX {
            return self.remaining_effort(problem, child).unwrap_or(u128::MAX);
        }
        match refinement {
            Refinement::Support(..) => parent_effort
                .checked_sub(1)
                .expect("an open condition contributes one refinement"),
            Refinement::Order(..) => parent_effort,
            Refinement::Decompose { parent, method, .. } => parent_effort
                .checked_sub(self.tasks[parent.task].expect("productive parent"))
                .expect("the parent occurrence contributes its effort")
                .saturating_add(self.children[method].expect("productive method")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::htn::{Action, Method, Task};
    use crate::plan::INIT_ID;

    fn fixture() -> Problem {
        Problem::new(
            vec!["p".into(), "q".into()],
            vec![
                Action {
                    cost: 100,
                    preconditions: vec![],
                    add: vec![0],
                    delete: vec![],
                },
                Action {
                    cost: 0,
                    preconditions: vec![0, 1],
                    add: vec![],
                    delete: vec![],
                },
            ],
            (0..7)
                .map(|id| Task {
                    name: format!("t{id}"),
                    primitive: id < 2,
                })
                .collect(),
            [
                (2, vec![3]),
                (2, vec![1]),
                (3, vec![2]),
                (3, vec![0]),
                (4, vec![]),
                (4, vec![4]),
                (5, vec![5]),
                (6, vec![2, 2, 4]),
            ]
            .into_iter()
            .enumerate()
            .map(|(id, (task, subtasks))| Method {
                name: format!("m{id}"),
                task,
                subtasks,
                orderings: vec![],
            })
            .collect(),
            vec![0, 1],
            vec![0],
            6,
        )
        .unwrap()
    }

    #[test]
    fn counts_refinements_with_recursion_empty_methods_and_repetition() {
        let p = fixture();
        let h = ModificationTdg::new(&p);
        // Primitive action cost does not contribute to modification effort.
        for (task, expected) in [Some(0), Some(2), Some(2), Some(1), Some(1), None, Some(6)]
            .into_iter()
            .enumerate()
        {
            assert_eq!(h.task_effort(task), expected);
        }
        assert_eq!(h.subtask_effort(7), Some(5));
        assert_eq!(h.subtask_effort(6), None);
        assert_eq!(h.remaining_effort(&p, &Plan::initial(&p)), Some(7));
        assert!(ModificationTdg::with_deadline(&p, Some(Instant::now())).is_none());
    }

    #[test]
    fn incremental_effort_matches_open_conditions_and_active_occurrences() {
        let p = fixture();
        let h = ModificationTdg::new(&p);
        let mut plan = Plan::initial(&p);
        let mut effort = h.remaining_effort(&p, &plan).unwrap();
        let root = plan.compound(&p).unwrap();
        let root_decomposition = Refinement::Decompose {
            parent: root,
            method: 7,
            for_support: true,
            focus: Some(*plan.open_conditions().next().unwrap()),
        };
        let advance = |plan: &mut Plan, refinement: Refinement, effort: &mut u128| {
            let child = refinement.apply(&p, plan).unwrap().unwrap();
            *effort = h.after_refinement(&p, &child, refinement, *effort);
            assert_eq!(Some(*effort), h.remaining_effort(&p, &child));
            *plan = child;
        };
        advance(&mut plan, root_decomposition, &mut effort);
        assert_eq!(effort, 6);
        // Focus retains the original open condition; it is counted exactly once.
        let mut ordinary = plan.clone();
        ordinary.support_focus = None;
        assert_eq!(h.remaining_effort(&p, &ordinary), Some(effort));
        plan = ordinary;
        let compound = *plan.tasks().find(|t| t.task == 2).unwrap();
        advance(
            &mut plan,
            Refinement::Decompose {
                parent: compound,
                method: 1,
                for_support: false,
                focus: None,
            },
            &mut effort,
        );
        assert_eq!(effort, 6);
        let open = *plan.open_conditions().next().unwrap();
        advance(&mut plan, Refinement::Support(open, INIT_ID), &mut effort);
        assert_eq!(effort, 5);
        let primitive = plan.tasks().find(|t| t.task == 1).unwrap().id;
        let compound = plan.tasks().find(|t| t.task == 2).unwrap().id;
        advance(
            &mut plan,
            Refinement::Order(primitive, compound),
            &mut effort,
        );
        assert_eq!(effort, 5);
    }

    #[test]
    fn saturation_is_not_unreachability_and_incremental_updates_can_leave_it() {
        let p = Problem::new(
            vec![],
            vec![],
            (0..129)
                .map(|id| Task {
                    name: format!("t{id}"),
                    primitive: false,
                })
                .collect(),
            (0..129)
                .map(|task| Method {
                    name: format!("m{task}"),
                    task,
                    subtasks: match task {
                        0 => vec![],
                        128 => vec![127],
                        _ => vec![task - 1, task - 1],
                    },
                    orderings: vec![],
                })
                .collect(),
            vec![],
            vec![],
            128,
        )
        .unwrap();
        let h = ModificationTdg::new(&p);
        let mut plan = Plan::initial(&p);
        let mut effort = h.remaining_effort(&p, &plan).unwrap();
        assert_eq!(effort, u128::MAX);
        for (method, expected) in [(128, u128::MAX), (127, u128::MAX - 1)] {
            let refinement = Refinement::Decompose {
                parent: plan.compound(&p).unwrap(),
                method,
                for_support: false,
                focus: None,
            };
            let child = refinement.apply(&p, &plan).unwrap().unwrap();
            effort = h.after_refinement(&p, &child, refinement, effort);
            assert_eq!(effort, expected);
            assert_eq!(h.remaining_effort(&p, &child), Some(expected));
            assert_eq!(child.cost(), 0);
            plan = child;
        }
    }
}
