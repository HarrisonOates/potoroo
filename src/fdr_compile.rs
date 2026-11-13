//! Full occurrence/order/link compilation for native finite-domain POCL.
//! Evaluate the compiled initial state, subtracting committed cost afterward.
//! Unconditional, axiom-free tasks only. FF uses native additive supporters;
//! LM-cut uses the existing native evaluator. Neither invokes FD per node.
use crate::external::FdHeuristic;
use crate::fdr::{Effect, Fact, Operator, Task, Variable};
use crate::fdr_pocl::PartialPlan;
use crate::orderings::StepTime;
use crate::params::ActionCost;
use crate::plan::{GOAL_ID, INIT_ID};

pub(crate) fn validate(task: &Task, costs: ActionCost) -> Result<(), String> {
    if !task.axioms.is_empty()
        || task
            .operators
            .iter()
            .any(|o| o.effects.iter().any(|e| !e.conditions.is_empty()))
    {
        return Err("native COMPILE requires unconditional effects and no axioms".into());
    }
    if task
        .operators
        .iter()
        .any(|o| costs.resolve(o.cost) >= u32::MAX as usize)
    {
        return Err("native COMPILE action costs must fit below u32::MAX".into());
    }
    Ok(())
}

fn assignment(variable: usize, pre: Option<usize>, post: usize) -> Effect {
    Effect {
        conditions: vec![],
        variable,
        pre,
        post,
    }
}

/// Original actions can be inserted anywhere allowed by link guards. Each
/// committed occurrence must execute once, after all its ordering predecessors.
pub(crate) fn build(task: &Task, plan: &PartialPlan, costs: ActionCost) -> Task {
    let mut result = task.clone();
    for op in &mut result.operators {
        op.cost = costs.resolve(op.cost);
    }
    let mut steps = plan.steps().copied().collect::<Vec<_>>();
    steps.sort_by_key(|s| s.id);
    let mut links = plan.links().copied().collect::<Vec<_>>();
    links.reverse();
    let exec_start = result.variables.len();
    for step in &steps {
        result.variables.push(Variable {
            name: format!("exec-{}", step.id),
            values: vec!["pending".into(), "done".into()],
        });
        result.initial.push(0);
        result.goals.push(Fact::new(exec_start + step.id - 1, 1));
    }
    let guard_start = result.variables.len();
    for (i, link) in links.iter().enumerate() {
        result.variables.push(Variable {
            name: format!("link-{i}"),
            values: vec!["protected".into(), "unprotected".into()],
        });
        result.initial.push(usize::from(link.producer != INIT_ID));
    }
    let threatens = |op: &Operator, fact: Fact| {
        op.effects
            .iter()
            .any(|e| e.variable == fact.variable && e.post != fact.value)
    };
    for op in &mut result.operators {
        for (i, link) in links.iter().enumerate() {
            if threatens(op, link.condition) {
                op.prevail.push(Fact::new(guard_start + i, 1));
            }
        }
    }
    for step in &steps {
        let mut op = task.operators[step.operator].clone();
        op.name = format!("step-{}-{}", step.id, op.name);
        op.cost = costs.resolve(op.cost);
        op.effects
            .push(assignment(exec_start + step.id - 1, Some(0), 1));
        for predecessor in &steps {
            if predecessor.id != step.id
                && !plan.orderings.possibly_after(
                    predecessor.id,
                    StepTime::AtEnd,
                    step.id,
                    StepTime::AtStart,
                )
            {
                op.prevail
                    .push(Fact::new(exec_start + predecessor.id - 1, 1));
            }
        }
        for (i, link) in links.iter().enumerate() {
            let guard = guard_start + i;
            if link.producer == step.id {
                op.effects.push(assignment(guard, None, 0));
            } else if link.consumer == step.id {
                op.effects.push(assignment(guard, None, 1));
            } else if threatens(&op, link.condition) {
                op.prevail.push(Fact::new(guard, 1));
            }
            debug_assert!(link.producer != GOAL_ID && link.consumer != INIT_ID);
        }
        result.operators.push(op);
    }
    result
}

pub(crate) fn remaining(task: &Task, committed_cost: usize, backend: FdHeuristic) -> Option<f32> {
    let total = match backend {
        FdHeuristic::Ff => {
            let requirements = task
                .operators
                .iter()
                .map(|o| o.effects.iter().map(|_| o.preconditions()).collect())
                .collect::<Vec<Vec<Vec<Fact>>>>();
            crate::cl_relax::CompiledRelaxation::new(task, &requirements, ActionCost::Task)
                .evaluate(&[])?
                .ff
        }
        FdHeuristic::LmCut => crate::lmcut::FdrLmCut::new(task, ActionCost::Task)
            .expect("validated native compilation")
            .evaluate([], task.goals.iter().copied())? as f32,
        _ => unreachable!("native compiled backend validated"),
    };
    Some((total - committed_cost as f32).max(0.0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fdr_pocl::Step;
    use crate::orderings::{BinaryOrderings, Ordering};
    use std::cmp::Reverse;
    use std::collections::{BinaryHeap, HashMap};
    use std::rc::Rc;

    // Independent concrete Dijkstra checks the compiled transition system,
    // including costs, rather than another relaxed-heuristic implementation.
    fn optimal(task: &Task) -> Option<usize> {
        let mut queue = BinaryHeap::from([(Reverse(0), task.initial.clone())]);
        let mut best = HashMap::from([(task.initial.clone(), 0)]);
        while let Some((Reverse(cost), state)) = queue.pop() {
            if best[&state] != cost {
                continue;
            }
            if task.goals.iter().all(|g| state[g.variable] == g.value) {
                return Some(cost);
            }
            for op in &task.operators {
                if !op
                    .preconditions()
                    .iter()
                    .all(|p| state[p.variable] == p.value)
                {
                    continue;
                }
                let mut next = state.clone();
                for effect in &op.effects {
                    next[effect.variable] = effect.post;
                }
                let new_cost = cost + op.cost;
                if best.get(&next).is_none_or(|&old| new_cost < old) {
                    best.insert(next.clone(), new_cost);
                    queue.push((Reverse(new_cost), next));
                }
            }
        }
        None
    }

    fn chain() -> Task {
        Task {
            variables: vec![Variable {
                name: "position".into(),
                values: vec!["a".into(), "b".into(), "c".into()],
            }],
            initial: vec![0],
            goals: vec![Fact::new(0, 2)],
            mutex_groups: vec![],
            axioms: vec![],
            operators: vec![
                Operator {
                    name: "ab".into(),
                    prevail: vec![],
                    effects: vec![assignment(0, Some(0), 1)],
                    cost: 2,
                },
                Operator {
                    name: "bc".into(),
                    prevail: vec![],
                    effects: vec![assignment(0, Some(1), 2)],
                    cost: 5,
                },
            ],
        }
    }

    #[test]
    fn compilation_preserves_costs_occurrences_and_orderings() {
        let task = chain();
        let mut order = Rc::new(BinaryOrderings::new());
        order = order
            .refine_with_step(
                Ordering::new(INIT_ID, StepTime::AtEnd, 1, StepTime::AtStart),
                1,
            )
            .unwrap();
        order = order
            .refine(Ordering::new(
                1,
                StepTime::AtEnd,
                GOAL_ID,
                StepTime::AtStart,
            ))
            .unwrap();
        // The public initial plan is filled through its test-only constructor.
        let mut plan =
            PartialPlan::test_assembled(vec![Step { id: 1, operator: 1 }], vec![], order, 5);
        let compiled = build(&task, &plan, ActionCost::Task);
        assert_eq!(optimal(&compiled), Some(7));
        assert_eq!(remaining(&compiled, 5, FdHeuristic::LmCut), Some(2.0));
        let mut order = plan.orderings.clone();
        order = order
            .refine_with_step(
                Ordering::new(INIT_ID, StepTime::AtEnd, 2, StepTime::AtStart),
                2,
            )
            .unwrap();
        order = order
            .refine(Ordering::new(
                2,
                StepTime::AtEnd,
                GOAL_ID,
                StepTime::AtStart,
            ))
            .unwrap();
        let valid = order
            .refine(Ordering::new(2, StepTime::AtEnd, 1, StepTime::AtStart))
            .unwrap();
        plan = PartialPlan::test_assembled(
            vec![Step { id: 1, operator: 1 }, Step { id: 2, operator: 0 }],
            vec![],
            valid,
            7,
        );
        let compiled = build(&task, &plan, ActionCost::Task);
        assert_eq!(optimal(&compiled), Some(7));
        assert_eq!(remaining(&compiled, 7, FdHeuristic::LmCut), Some(0.0));
        plan.orderings = order
            .refine(Ordering::new(1, StepTime::AtEnd, 2, StepTime::AtStart))
            .unwrap();
        assert_eq!(optimal(&build(&task, &plan, ActionCost::Task)), None);
        assert_eq!(
            optimal(&build(
                &task,
                &PartialPlan::initial(&task),
                ActionCost::Unit
            )),
            Some(2)
        );
    }

    #[test]
    fn finite_additive_overflow_does_not_prune_a_mandatory_chain() {
        // Full ordering closure gives marker h_add(i) = 2^i - 1 even
        // though the concrete task only needs i unit-cost actions.
        for n in [31, 32, 40] {
            let task = Task {
                variables: vec![Variable {
                    name: "position".into(),
                    values: (0..=n).map(|i| i.to_string()).collect(),
                }],
                initial: vec![0],
                goals: vec![Fact::new(0, n)],
                mutex_groups: vec![],
                axioms: vec![],
                operators: (0..n)
                    .map(|i| Operator {
                        name: format!("advance-{i}"),
                        prevail: vec![],
                        effects: vec![assignment(0, Some(i), i + 1)],
                        cost: 1,
                    })
                    .collect(),
            };
            let mut order = Rc::new(BinaryOrderings::new());
            for id in 1..=n {
                order = order
                    .refine_with_step(
                        Ordering::new(id - 1, StepTime::AtEnd, id, StepTime::AtStart),
                        id,
                    )
                    .unwrap();
            }
            let plan = PartialPlan::test_assembled(
                (0..n)
                    .map(|i| Step {
                        id: i + 1,
                        operator: i,
                    })
                    .collect(),
                vec![],
                order,
                n,
            );
            let compiled = build(&task, &plan, ActionCost::Unit);
            assert_eq!(optimal(&compiled), Some(n));
            assert!(
                remaining(&compiled, n, FdHeuristic::Ff).is_some(),
                "reachable chain of {n} actions"
            );
            assert_eq!(remaining(&compiled, n, FdHeuristic::LmCut), Some(0.0));
        }
    }

    #[test]
    fn finite_aggregate_cost_overflow_is_not_a_dead_end() {
        let mut task = chain();
        for op in &mut task.operators {
            op.cost = (u32::MAX as usize / 2) + 1;
        }
        validate(&task, ActionCost::Task).unwrap();
        let compiled = build(&task, &PartialPlan::initial(&task), ActionCost::Task);
        assert_eq!(optimal(&compiled), Some(u32::MAX as usize + 1));
        for backend in [FdHeuristic::Ff, FdHeuristic::LmCut] {
            // Numeric estimates saturate, but reachability must remain finite.
            assert_eq!(remaining(&compiled, 0, backend), Some(u32::MAX as f32));
        }
    }

    #[test]
    fn repeated_operator_occurrences_need_separate_executions() {
        let mut task = chain();
        task.goals = vec![Fact::new(0, 1)];
        task.operators[1] = Operator {
            name: "reset".into(),
            prevail: vec![],
            effects: vec![assignment(0, Some(1), 0)],
            cost: 3,
        };
        let order = Rc::new(BinaryOrderings::new())
            .refine_with_step(Ordering::new(1, StepTime::AtEnd, 2, StepTime::AtStart), 2)
            .unwrap();
        let plan = PartialPlan::test_assembled(
            vec![Step { id: 1, operator: 0 }, Step { id: 2, operator: 0 }],
            vec![],
            order,
            4,
        );
        // Two distinct ab occurrences require an intervening inserted reset.
        assert_eq!(optimal(&build(&task, &plan, ActionCost::Task)), Some(7));
    }

    #[test]
    fn real_link_protects_until_consumer_even_if_consumer_deletes_it() {
        let task = Task {
            variables: vec![Variable {
                name: "p".into(),
                values: vec!["false".into(), "true".into()],
            }],
            initial: vec![0],
            goals: vec![Fact::new(0, 0)],
            mutex_groups: vec![],
            axioms: vec![],
            operators: vec![
                Operator {
                    name: "produce".into(),
                    prevail: vec![],
                    effects: vec![assignment(0, None, 1)],
                    cost: 1,
                },
                Operator {
                    name: "consume".into(),
                    prevail: vec![],
                    effects: vec![assignment(0, Some(1), 0)],
                    cost: 1,
                },
                Operator {
                    name: "threat".into(),
                    prevail: vec![],
                    effects: vec![assignment(0, None, 0)],
                    cost: 1,
                },
            ],
        };
        let order = Rc::new(BinaryOrderings::new())
            .refine_with_step(Ordering::new(1, StepTime::AtEnd, 2, StepTime::AtStart), 2)
            .unwrap();
        let link = crate::fdr_pocl::CausalLink {
            producer: 1,
            consumer: 2,
            condition: Fact::new(0, 1),
            effect: Some(0),
        };
        let plan = PartialPlan::test_assembled(
            vec![Step { id: 1, operator: 0 }, Step { id: 2, operator: 1 }],
            vec![link],
            order,
            2,
        );
        let compiled = build(&task, &plan, ActionCost::Unit);
        assert_eq!(optimal(&compiled), Some(2));
        let applicable = |op: &Operator, state: &[usize]| {
            op.preconditions()
                .iter()
                .all(|p| state[p.variable] == p.value)
        };
        let mut state = compiled.initial.clone();
        for effect in &compiled.operators[3].effects {
            state[effect.variable] = effect.post;
        }
        assert!(
            !applicable(&compiled.operators[2], &state),
            "inserted deleter inside protected interval"
        );
        assert!(
            applicable(&compiled.operators[4], &state),
            "consumer may delete its consumed fact"
        );
        for effect in &compiled.operators[4].effects {
            state[effect.variable] = effect.post;
        }
        assert!(
            applicable(&compiled.operators[2], &state),
            "guard released after consumption"
        );
    }

    #[test]
    fn initial_to_goal_link_blocks_future_deleters() {
        let mut task = chain();
        task.variables.push(Variable {
            name: "protected".into(),
            values: vec!["false".into(), "true".into()],
        });
        task.initial.push(1);
        task.goals.push(Fact::new(1, 1));
        task.operators[0].effects.push(assignment(1, None, 0));
        task.operators[1].effects.push(assignment(1, None, 1));
        let plan = PartialPlan::initial(&task);
        assert_eq!(optimal(&build(&task, &plan, ActionCost::Task)), Some(7));
        let plan = PartialPlan::test_assembled(
            vec![],
            vec![crate::fdr_pocl::CausalLink {
                producer: INIT_ID,
                consumer: GOAL_ID,
                condition: Fact::new(1, 1),
                effect: None,
            }],
            Rc::new(BinaryOrderings::new()),
            0,
        );
        assert_eq!(optimal(&build(&task, &plan, ActionCost::Task)), None);
    }
}
