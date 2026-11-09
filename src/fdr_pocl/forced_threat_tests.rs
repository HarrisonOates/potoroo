use super::*;
use crate::fdr::{Effect, Operator, Variable};
use crate::heuristics::FlawSelectionOrder;

fn fixture(initial_producer: bool, deletes: usize) -> (Task, PartialPlan) {
    let task = Task {
        variables: vec![Variable {
            name: "x".into(),
            values: vec!["off".into(), "on".into()],
        }],
        mutex_groups: vec![],
        initial: vec![1],
        goals: vec![],
        axioms: vec![],
        operators: vec![
            Operator {
                name: "read".into(),
                prevail: vec![Fact::new(0, 1)],
                effects: vec![],
                cost: 1,
            },
            Operator {
                name: "delete".into(),
                prevail: vec![],
                effects: vec![Effect {
                    conditions: vec![],
                    variable: 0,
                    pre: None,
                    post: 0,
                }],
                cost: 1,
            },
            Operator {
                name: "restore".into(),
                prevail: vec![],
                effects: vec![Effect {
                    conditions: vec![],
                    variable: 0,
                    pre: None,
                    post: 1,
                }],
                cost: 1,
            },
        ],
    };
    let mut steps = vec![Step { id: 1, operator: 0 }];
    steps.extend((2..deletes + 2).map(|id| Step { id, operator: 1 }));
    let producer = if initial_producer {
        INIT_ID
    } else {
        deletes + 2
    };
    if !initial_producer {
        steps.push(Step {
            id: producer,
            operator: 2,
        });
    }
    let mut orders = Rc::new(BinaryOrderings::new());
    for step in &steps {
        orders = orders
            .refine_with_step(
                Ordering::new(step.id, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                step.id,
            )
            .unwrap();
    }
    if !initial_producer {
        orders = orders
            .refine(Ordering::new(
                producer,
                StepTime::AtEnd,
                1,
                StepTime::AtStart,
            ))
            .unwrap();
    }
    let count = steps.len();
    let plan = PartialPlan::assemble(
        steps,
        vec![CausalLink {
            producer,
            consumer: 1,
            condition: Fact::new(0, 1),
            effect: (!initial_producer).then_some(0),
        }],
        vec![],
        orders,
        (2..deletes + 2)
            .map(|step| Threat {
                step,
                effect: 0,
                link: 0,
            })
            .collect(),
        count,
        count + 1,
    );
    (task, plan)
}

#[test]
fn forced_threats_preserve_support_and_all_action_occurrences() {
    let (task, plan) = fixture(true, 3);
    let planner = Planner::new(&task);
    let mut stats = SearchStats::default();
    let child = planner
        .propagate_threats(plan.clone(), &Parameters::default(), 10, &mut stats)
        .unwrap();
    assert_eq!(stats.threat_forced, 3);
    assert!(child.threats.is_empty());
    assert_eq!(child.num_steps(), plan.num_steps());
    assert_eq!(child.cost(), plan.cost());
    assert_eq!(
        child.links().collect::<Vec<_>>(),
        plan.links().collect::<Vec<_>>()
    );
    for d in 2..5 {
        assert!(is_ordered_before(&child.orderings, 1, d));
    }
    assert!(
        !is_ordered_before(&child.orderings, 2, 3),
        "independent deletes stay unordered"
    );
}

#[test]
fn forced_threats_leave_both_ordering_and_confrontation_choices_open() {
    let (task, plan) = fixture(false, 2);
    let mut stats = SearchStats::default();
    let child = Planner::new(&task)
        .propagate_threats(plan, &Parameters::default(), 10, &mut stats)
        .unwrap();
    assert_eq!(stats.threat_forced, 0);
    assert_eq!(child.threats.len(), 2);
    let (mut task, plan) = fixture(true, 1);
    task.variables.push(Variable {
        name: "guard".into(),
        values: vec!["off".into(), "on".into()],
    });
    task.initial.push(0);
    task.operators[1].effects[0]
        .conditions
        .push(Fact::new(1, 1));
    let planner = Planner::new(&task);
    assert!(!planner.confrontations(&plan, &plan.threats[0]).is_empty());
    let child = planner
        .propagate_threats(plan, &Parameters::default(), 10, &mut stats)
        .unwrap();
    assert_eq!(stats.threat_forced, 0);
    assert_eq!(child.threats.len(), 1);
}

#[test]
fn forced_threats_reject_impossible_links_and_obey_limits() {
    let (task, plan) = fixture(true, 20);
    let planner = Planner::new(&task);
    for (budget, expected) in [(0, 0), (1, 1), (100, 16)] {
        let mut stats = SearchStats::default();
        let child = planner
            .propagate_threats(plan.clone(), &Parameters::default(), budget, &mut stats)
            .unwrap();
        assert_eq!(stats.threat_forced, expected);
        assert_eq!(child.threats.len(), 20 - expected);
    }
    let mut stats = SearchStats::default();
    let params = Parameters {
        deadline: Some(Instant::now()),
        ..Parameters::default()
    };
    let child = planner
        .propagate_threats(plan.clone(), &params, 100, &mut stats)
        .unwrap();
    assert_eq!(child.threats.len(), 20);
    assert_eq!(stats.threat_forced, 0);
    let mut impossible = plan;
    impossible.orderings = impossible
        .orderings
        .refine(Ordering::new(21, StepTime::AtEnd, 1, StepTime::AtStart))
        .unwrap();
    assert!(planner
        .propagate_threats(impossible, &Parameters::default(), 100, &mut stats)
        .is_none());
}

#[test]
fn bounded_lifo_delays_large_support_sets_without_becoming_global_lr() {
    let mut task = Task {
        variables: vec![],
        mutex_groups: vec![],
        initial: vec![0; 3],
        goals: vec![],
        axioms: vec![],
        operators: vec![],
    };
    for (variable, count) in [2, 4, 12].into_iter().enumerate() {
        task.variables.push(Variable {
            name: format!("v{variable}"),
            values: vec!["off".into(), "on".into()],
        });
        task.goals.push(Fact::new(variable, 1));
        for a in 0..count {
            task.operators.push(Operator {
                name: format!("a{variable}-{a}"),
                prevail: vec![],
                effects: vec![Effect {
                    conditions: vec![],
                    variable,
                    pre: None,
                    post: 1,
                }],
                cost: 1,
            });
        }
    }
    let planner = Planner::new(&task);
    let plan = PartialPlan::initial(&task);
    for (order, expected) in [
        ("ZLIFO", 2),
        ("{n,s}LIFO/{o}LR", 0),
        ("{n}LIFO/{o}0LIFO/{o}1NEW/{o}8LIFO/{o}LR/{s}LIFO", 1),
    ] {
        let SelectedFlaw::Open(open) =
            planner.select_flaw(&plan, &FlawSelectionOrder::parse(order).unwrap())
        else {
            panic!("expected open")
        };
        assert_eq!(open.condition.variable, expected);
    }
}

#[test]
fn search_compresses_ordering_chains_replays_and_counts_elided_nodes() {
    let mut task = Task {
        variables: (0..6)
            .map(|v| Variable {
                name: format!("v{v}"),
                values: vec!["off".into(), "on".into()],
            })
            .collect(),
        mutex_groups: vec![],
        initial: vec![1, 0, 0, 0, 0, 0],
        goals: vec![
            Fact::new(5, 1),
            Fact::new(1, 1),
            Fact::new(2, 1),
            Fact::new(3, 1),
            Fact::new(4, 1),
        ],
        axioms: vec![],
        operators: vec![],
    };
    let effect = |variable, post| Effect {
        conditions: vec![],
        variable,
        pre: None,
        post,
    };
    for variable in 1..5 {
        task.operators.push(Operator {
            name: format!("read-{variable}"),
            prevail: vec![Fact::new(0, 1)],
            effects: vec![effect(variable, 1)],
            cost: 1,
        });
    }
    task.operators.push(Operator {
        name: "consume".into(),
        prevail: vec![],
        effects: vec![effect(0, 0), effect(5, 1)],
        cost: 1,
    });
    for algorithm in [
        SearchAlgorithm::A,
        SearchAlgorithm::Gbfs,
        SearchAlgorithm::Bfs,
        SearchAlgorithm::Alt,
        SearchAlgorithm::LazyGbfs,
    ] {
        for limit in [4, 8, 12, 100] {
            let params = Parameters {
                search_algorithm: algorithm,
                search_limits: vec![limit],
                flaw_orders: vec![FlawSelectionOrder::parse("{n,s}LIFO/{o}LIFO").unwrap()],
                prune: crate::pruning::PruneOptions::parse("threats").unwrap(),
                ..Parameters::default()
            };
            let (outcome, stats) = solve_with_params(&task, &params).unwrap();
            assert!(stats.nodes_generated <= limit);
            if let Outcome::Solved(solution) = outcome {
                assert_eq!(solution.plan.cost(), 5);
                let mut state = task.initial.clone();
                for id in solution.operators {
                    let op = &task.operators[id];
                    assert!(op
                        .preconditions()
                        .iter()
                        .all(|f| state[f.variable] == f.value));
                    for e in &op.effects {
                        state[e.variable] = e.post;
                    }
                }
                assert!(task.goals.iter().all(|f| state[f.variable] == f.value));
                assert!(stats.threat_forced > 0);
            } else {
                assert!(limit < 100);
            }
        }
    }
}

#[test]
fn propagated_threat_search_agrees_with_small_state_space_oracle() {
    let mut seed = 91823u64;
    let mut random = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        seed >> 32
    };
    for case in 0..96 {
        let initial = (random() % 8) as usize;
        let goal = (random() % 8) as usize;
        let mut task = Task {
            variables: (0..3)
                .map(|v| Variable {
                    name: format!("v{v}"),
                    values: vec!["off".into(), "on".into()],
                })
                .collect(),
            mutex_groups: vec![],
            initial: (0..3).map(|v| (initial >> v) & 1).collect(),
            goals: (0..3).map(|v| Fact::new(v, (goal >> v) & 1)).collect(),
            axioms: vec![],
            operators: vec![],
        };
        for op in 0..6 {
            let mask = (random() % 8) as usize;
            let values = (random() % 8) as usize;
            let variable = (random() % 3) as usize;
            let post = (random() % 2) as usize;
            let conditions = if random() % 3 == 0 {
                vec![Fact::new((random() % 3) as usize, (random() % 2) as usize)]
            } else {
                vec![]
            };
            task.operators.push(Operator {
                name: format!("a{op}"),
                prevail: (0..3)
                    .filter(|v| mask & (1 << v) != 0)
                    .map(|v| Fact::new(v, (values >> v) & 1))
                    .collect(),
                effects: vec![Effect {
                    conditions,
                    variable,
                    pre: None,
                    post,
                }],
                cost: 1,
            });
        }
        let applicable = |state: usize, facts: &[Fact]| {
            facts.iter().all(|f| ((state >> f.variable) & 1) == f.value)
        };
        let advance = |state: usize, op: &Operator| {
            let mut next = state;
            for e in &op.effects {
                if applicable(state, &e.conditions) {
                    next = (next & !(1 << e.variable)) | (e.post << e.variable);
                }
            }
            next
        };
        let mut distances = [usize::MAX; 8];
        distances[initial] = 0;
        let mut queue = std::collections::VecDeque::from([initial]);
        while let Some(state) = queue.pop_front() {
            for op in &task.operators {
                if !applicable(state, &op.prevail) {
                    continue;
                }
                let next = advance(state, op);
                if distances[next] == usize::MAX {
                    distances[next] = distances[state] + 1;
                    queue.push_back(next);
                }
            }
        }
        for force in [false, true] {
            let params = Parameters {
                search_algorithm: SearchAlgorithm::Bfs,
                search_limits: vec![200],
                prune: crate::pruning::PruneOptions {
                    threats: force,
                    ..Default::default()
                },
                ..Parameters::default()
            };
            let (outcome, stats) = solve_with_params(&task, &params).unwrap();
            assert!(stats.nodes_generated <= 200);
            match outcome {
                Outcome::Solved(solution) => {
                    assert_eq!(
                        solution.plan.num_steps(),
                        distances[goal],
                        "case {case}, force={force}"
                    );
                    let mut state = initial;
                    for id in solution.operators {
                        let op = &task.operators[id];
                        assert!(applicable(state, &op.prevail));
                        state = advance(state, op);
                    }
                    assert_eq!(state, goal);
                }
                Outcome::NoSolution => assert_eq!(
                    distances[goal],
                    usize::MAX,
                    "false dead end case {case}, force={force}"
                ),
                Outcome::LimitReached => {}
            }
        }
    }
}
