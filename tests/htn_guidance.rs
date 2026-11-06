#![cfg(feature = "htn")]

use potoroo::htn::{
    search,
    tdg::{Tdg, COST_CAP},
    validate, AStarTieBreak, Action, Config, FlawSelection, Method, Outcome, Problem,
    SearchStrategy, Solution, StopReason, Task, TdgMode, UnitCyclePolicy,
};

fn action(cost: u64, pre: &[usize], add: &[usize], delete: &[usize]) -> Action {
    Action {
        cost,
        preconditions: pre.into(),
        add: add.into(),
        delete: delete.into(),
    }
}

fn method(task: usize, subtasks: &[usize], orderings: &[(usize, usize)]) -> Method {
    Method {
        name: format!("m{task}-{}", subtasks.len()),
        task,
        subtasks: subtasks.into(),
        orderings: orderings.into(),
    }
}

fn problem(
    actions: Vec<Action>,
    compounds: usize,
    methods: Vec<Method>,
    initial: &[usize],
    goal: &[usize],
) -> Problem {
    let tasks: Vec<_> = (0..actions.len() + compounds)
        .map(|i| Task {
            name: format!("t{i}[]"),
            primitive: i < actions.len(),
        })
        .collect();
    let root = tasks.len() - 1;
    Problem::new(
        vec!["p".into(), "q".into()],
        actions,
        tasks,
        methods,
        initial.into(),
        goal.into(),
        root,
    )
    .unwrap()
}

fn config(strategy: SearchStrategy, flaws: FlawSelection) -> Config {
    Config {
        strategy,
        flaws,
        node_limit: Some(20_000),
        ..Config::default()
    }
}

fn solved(outcome: Outcome) -> Solution {
    match outcome {
        Outcome::Solved(solution) => solution,
        other => panic!("expected solution: {other:?}"),
    }
}

fn modes() -> impl Iterator<Item = Config> {
    [
        SearchStrategy::BreadthFirst,
        SearchStrategy::AStar,
        SearchStrategy::Greedy,
    ]
    .into_iter()
    .flat_map(|strategy| {
        [
            FlawSelection::DecompositionFirst,
            FlawSelection::Interleaved,
            FlawSelection::Systematic,
        ]
        .into_iter()
        .flat_map(move |flaws| {
            [
                TdgMode::Static,
                TdgMode::Recompute,
                TdgMode::Lazy,
                TdgMode::LazyCached,
            ]
            .into_iter()
            .flat_map(move |tdg| {
                [
                    AStarTieBreak::Fifo,
                    AStarTieBreak::LargerG,
                    AStarTieBreak::Modification,
                ]
                .into_iter()
                .filter(move |tie| strategy == SearchStrategy::AStar || *tie == AStarTieBreak::Fifo)
                .flat_map(move |astar_tie| {
                    [false, true].into_iter().flat_map(move |support_bound| {
                        [false, true].into_iter().map(move |relaxed_bound| Config {
                            tdg,
                            astar_tie,
                            support_bound,
                            relaxed_bound,
                            ..config(strategy, flaws)
                        })
                    })
                })
            })
        })
    })
}

#[test]
fn astar_secondary_guidance_shortens_equal_cost_plateaus() {
    let p = problem(
        vec![action(1, &[], &[], &[])],
        2,
        vec![
            method(1, &[0], &[]),
            method(2, &[1], &[]),
            method(2, &[0], &[]),
        ],
        &[],
        &[],
    );
    for tdg in [
        TdgMode::Static,
        TdgMode::Recompute,
        TdgMode::Lazy,
        TdgMode::LazyCached,
    ] {
        for astar_tie in [
            AStarTieBreak::Fifo,
            AStarTieBreak::LargerG,
            AStarTieBreak::Modification,
        ] {
            let result = search(
                &p,
                &Config {
                    strategy: SearchStrategy::AStar,
                    astar_tie,
                    tdg,
                    ..Config::default()
                },
            )
            .unwrap();
            let expanded = if astar_tie == AStarTieBreak::Fifo {
                3
            } else {
                2
            };
            assert_eq!(result.stats.expanded, expanded);
            assert_eq!(result.stats.max_f_plateau, expanded);
            assert_eq!(result.stats.equal_f_expanded, expanded - 1);
            let s = solved(result.outcome);
            assert_eq!(s.cost, 1);
            assert!(s.cost_optimal);
        }
    }
}

#[test]
fn modification_guidance_keeps_action_cost_primary_and_other_queues_unchanged() {
    let p = problem(
        vec![action(1, &[], &[], &[]), action(9, &[], &[], &[])],
        3,
        vec![
            method(2, &[0], &[]),
            method(3, &[2], &[]),
            method(4, &[3], &[]),
            method(4, &[1], &[]),
        ],
        &[],
        &[],
    );
    for strategy in [
        SearchStrategy::BreadthFirst,
        SearchStrategy::Greedy,
        SearchStrategy::AStar,
    ] {
        let mut baseline = None;
        for astar_tie in [
            AStarTieBreak::Fifo,
            AStarTieBreak::LargerG,
            AStarTieBreak::Modification,
        ] {
            let result = search(
                &p,
                &Config {
                    strategy,
                    astar_tie,
                    ..Config::default()
                },
            )
            .unwrap();
            let s = solved(result.outcome);
            if strategy == SearchStrategy::AStar {
                assert_eq!(s.cost, 1); // The cost-9 goal has zero remaining modification effort.
                assert!(s.cost_optimal);
            } else {
                let signature = (
                    result.stats.generated,
                    result.stats.expanded,
                    s.certificate.to_panda(&p).unwrap(),
                );
                assert_eq!(result.stats.max_f_plateau, 0);
                assert_eq!(result.stats.equal_f_expanded, 0);
                if let Some(expected) = &baseline {
                    assert_eq!(&signature, expected);
                } else {
                    baseline = Some(signature);
                }
            }
        }
    }
}

#[test]
fn modification_ties_can_starve_an_exit_within_one_recursive_cost_plateau() {
    // Every action-cost f is zero. The empty method makes root's static
    // modification estimate cheap, but cannot achieve the goal. Repeatedly
    // choosing root -> root therefore outranks the longer executable exit.
    // FIFO eventually takes that exit; secondary guidance need not be fair.
    let p = problem(
        vec![action(0, &[], &[0], &[])],
        4,
        vec![
            method(1, &[0], &[]),
            method(2, &[1], &[]),
            method(3, &[2], &[]),
            method(4, &[4], &[]),
            method(4, &[], &[]),
            method(4, &[3], &[]),
        ],
        &[],
        &[0],
    );
    for astar_tie in [
        AStarTieBreak::Fifo,
        AStarTieBreak::LargerG,
        AStarTieBreak::Modification,
    ] {
        let result = search(
            &p,
            &Config {
                strategy: SearchStrategy::AStar,
                astar_tie,
                node_limit: Some(100),
                ..Config::default()
            },
        )
        .unwrap();
        if astar_tie == AStarTieBreak::Modification {
            assert!(matches!(
                result.outcome,
                Outcome::Stopped(StopReason::NodeLimit)
            ));
        } else {
            let s = solved(result.outcome);
            assert_eq!(s.cost, 0);
            assert!(s.cost_optimal);
        }
    }
    for mut cfg in modes() {
        cfg.unit_cycles = UnitCyclePolicy::Prune;
        cfg.node_limit = Some(100);
        let result = search(&p, &cfg).unwrap();
        assert!(result.stats.unit_cycles_pruned > 0);
        let s = solved(result.outcome);
        assert_eq!(s.cost, 0);
        assert_eq!(s.cost_optimal, cfg.strategy == SearchStrategy::AStar);
    }
}

#[test]
fn unit_cycle_pruning_matches_exhaustive_graph_reachability() {
    // All 512 directed graphs on three compound tasks, including self loops.
    // Each reachable exit yields exactly one action, so graph reachability is
    // an independent oracle for primitive languages and their minimum costs.
    for edges in 0..512 {
        let mut methods = Vec::new();
        let mut reach = [[false; 3]; 3];
        for (a, row) in reach.iter_mut().enumerate() {
            for (b, reachable) in row.iter_mut().enumerate() {
                if edges & (1 << (3 * a + b)) != 0 {
                    methods.push(method(a + 2, &[b + 2], &[]));
                    *reachable = true;
                }
            }
            row[a] = true;
        }
        for via in 0..3 {
            for a in 0..3 {
                for b in 0..3 {
                    reach[a][b] |= reach[a][via] && reach[via][b];
                }
            }
        }
        methods.extend([
            method(2, &[0], &[]),
            method(3, &[1], &[]),
            method(4, &[], &[]), // Cheap structurally, but cannot achieve p.
        ]);
        let p = problem(
            vec![action(3, &[], &[0], &[]), action(7, &[], &[0], &[])],
            3,
            methods,
            &[],
            &[0],
        );
        let optimum = if reach[2][0] {
            Some(3)
        } else if reach[2][1] {
            Some(7)
        } else {
            None
        };
        for mut cfg in modes() {
            cfg.unit_cycles = UnitCyclePolicy::Prune;
            cfg.node_limit = Some(100);
            let result = search(&p, &cfg).unwrap();
            match (optimum, result.outcome) {
                (None, Outcome::NoSolution) => {}
                (Some(cost), Outcome::Solved(s)) => {
                    assert_eq!(s.certificate.steps.len(), 1);
                    let task = s.certificate.steps[0].task;
                    assert!(reach[2][task]);
                    assert_eq!(validate::validate(&p, &s.certificate).unwrap(), s.cost);
                    if cfg.strategy == SearchStrategy::AStar {
                        assert_eq!(s.cost, cost, "graph={edges} config={cfg:?}");
                        assert!(s.cost_optimal);
                    }
                }
                (expected, actual) => {
                    panic!("graph={edges} config={cfg:?}: expected {expected:?}, got {actual:?}");
                }
            }
        }
    }
}

#[test]
fn unit_cycles_keep_repeated_siblings_and_inherited_partial_orders() {
    let p = problem(
        vec![
            action(1, &[], &[0], &[]),
            action(2, &[0], &[1], &[]),
            action(3, &[1], &[], &[]),
        ],
        3,
        vec![
            method(3, &[4], &[]),
            method(4, &[3], &[]),
            method(4, &[1], &[]),
            method(5, &[0, 3, 3, 2], &[(0, 1), (0, 2), (1, 3), (2, 3)]),
        ],
        &[],
        &[],
    );
    for mut cfg in modes() {
        cfg.unit_cycles = UnitCyclePolicy::Prune;
        let s = solved(search(&p, &cfg).unwrap().outcome);
        assert_eq!(s.cost, 8);
        assert_eq!(
            s.certificate
                .steps
                .iter()
                .map(|t| t.task)
                .collect::<Vec<_>>(),
            [0, 1, 1, 2]
        );
        assert_eq!(s.certificate.decompositions.len(), 5);
    }
}

#[test]
fn unit_ancestry_restarts_after_recursion_with_primitive_or_compound_siblings() {
    for compound_sibling in [false, true] {
        // A -> B -> prepare,A -> B -> consume is essential. The extra B -> A
        // method is a redundant unit cycle. Rejecting every repeated task on
        // the ancestry would incorrectly remove the only executable solution.
        let mut methods = vec![
            method(3, &[2], &[]),
            method(2, &[3], &[]),
            method(2, &[if compound_sibling { 4 } else { 0 }, 3], &[(0, 1)]),
            method(2, &[1], &[]),
        ];
        if compound_sibling {
            methods.extend([method(4, &[0], &[]), method(5, &[3], &[])]);
        }
        let p = problem(
            vec![action(1, &[0], &[1], &[0]), action(1, &[1], &[], &[])],
            if compound_sibling { 4 } else { 2 },
            methods,
            &[0],
            &[1],
        );
        for mut cfg in modes() {
            cfg.unit_cycles = UnitCyclePolicy::Prune;
            let s = solved(search(&p, &cfg).unwrap().outcome);
            assert_eq!(s.cost, 2);
            assert_eq!(
                s.certificate
                    .steps
                    .iter()
                    .map(|t| t.task)
                    .collect::<Vec<_>>(),
                [0, 1]
            );
        }
    }
}

#[test]
fn unit_cycle_pruning_preserves_empty_exits_and_does_not_prune_growing_cycles() {
    let empty = problem(
        vec![],
        2,
        vec![
            method(1, &[0], &[]),
            method(0, &[1], &[]),
            method(0, &[], &[]),
        ],
        &[],
        &[],
    );
    for mut cfg in modes() {
        cfg.unit_cycles = UnitCyclePolicy::Prune;
        let s = solved(search(&empty, &cfg).unwrap().outcome);
        assert_eq!(s.cost, 0);
        assert!(s.certificate.steps.is_empty());
        assert_eq!(s.certificate.decompositions.len(), 2);
    }
    // A -> A,A may generate arbitrarily many actions: it is not a unit cycle.
    // Nullable siblings still leave an infinite f=0 plateau before a cost-1 goal.
    let growing = problem(
        vec![action(1, &[], &[0], &[])],
        1,
        vec![
            method(1, &[1, 1], &[]),
            method(1, &[], &[]),
            method(1, &[0], &[]),
        ],
        &[],
        &[0],
    );
    let result = search(
        &growing,
        &Config {
            strategy: SearchStrategy::AStar,
            unit_cycles: UnitCyclePolicy::Prune,
            node_limit: Some(50),
            ..Config::default()
        },
    )
    .unwrap();
    assert!(matches!(
        result.outcome,
        Outcome::Stopped(StopReason::NodeLimit)
    ));
    assert_eq!(result.stats.unit_cycles_pruned, 0);
    // Necessary support raises that lower-cost plateau without deleting any
    // decomposition histories. All modes can now take the cost-1 exit.
    for mut cfg in modes().filter(|cfg| cfg.support_bound) {
        cfg.node_limit = Some(100);
        let s = solved(search(&growing, &cfg).unwrap().outcome);
        assert_eq!(s.cost, 1);
        assert_eq!(s.cost_optimal, cfg.strategy == SearchStrategy::AStar);
    }
}

#[test]
fn support_bounds_do_not_charge_shared_achievers_twice() {
    // Both goals can share the cost-4 action. Adding their individual cost
    // increments would incorrectly prefer the shallow cost-7 alternative.
    let p = problem(
        vec![action(7, &[], &[0, 1], &[]), action(4, &[], &[0, 1], &[])],
        2,
        vec![
            method(2, &[], &[]),
            method(2, &[1], &[]),
            method(3, &[2], &[]),
            method(3, &[0], &[]),
        ],
        &[],
        &[0, 1],
    );
    for cfg in modes().filter(|cfg| cfg.support_bound && cfg.strategy == SearchStrategy::AStar) {
        let result = search(&p, &cfg).unwrap();
        assert!(result.stats.support_tables > 0);
        let s = solved(result.outcome);
        assert_eq!(s.cost, 4);
        assert!(s.cost_optimal);
    }
}

#[test]
fn support_bounds_can_still_have_recursive_plateaus_for_joint_requirements() {
    // One required achiever costs 1, but an executable solution needs both
    // actions. A -> A,A can still grow forever below the true cost of 2.
    let p = problem(
        vec![action(1, &[], &[0], &[]), action(1, &[0], &[1], &[])],
        1,
        vec![
            method(2, &[2, 2], &[]),
            method(2, &[], &[]),
            method(2, &[0], &[]),
            method(2, &[1], &[]),
        ],
        &[],
        &[1],
    );
    for astar_tie in [
        AStarTieBreak::Fifo,
        AStarTieBreak::LargerG,
        AStarTieBreak::Modification,
    ] {
        let result = search(
            &p,
            &Config {
                strategy: SearchStrategy::AStar,
                support_bound: true,
                astar_tie,
                node_limit: Some(100),
                ..Config::default()
            },
        )
        .unwrap();
        assert!(matches!(
            result.outcome,
            Outcome::Stopped(StopReason::NodeLimit)
        ));
    }
    let s = solved(
        search(
            &p,
            &Config {
                support_bound: true,
                node_limit: Some(1000),
                ..Config::default()
            },
        )
        .unwrap()
        .outcome,
    );
    assert_eq!(s.cost, 2);
    // h_max sees the prep -> finish chain, so growing the network no longer
    // leaves an infinite plateau strictly below the cost-2 solution.
    for mut cfg in modes().filter(|cfg| {
        cfg.relaxed_bound
            && cfg.strategy == SearchStrategy::AStar
            && cfg.flaws == FlawSelection::Systematic
    }) {
        cfg.node_limit = Some(1000);
        let result = search(&p, &cfg).unwrap();
        assert!(
            matches!(result.outcome, Outcome::Solved(_)),
            "{cfg:?}: {:?}",
            result.outcome
        );
        let s = solved(result.outcome);
        assert_eq!(s.cost, 2);
        assert_eq!(s.cost_optimal, cfg.strategy == SearchStrategy::AStar);
    }
}

#[test]
fn relaxed_execution_bounds_preserve_shared_support_and_committed_costs() {
    // The cost-4 action supports two occurrences of the cost-1 consumer.
    // Their total cost is 6, not 10. The root also offers a shallow cost-7 exit.
    let p = problem(
        vec![
            action(4, &[], &[0], &[]),
            action(1, &[0], &[1], &[]),
            action(7, &[], &[1], &[]),
        ],
        2,
        vec![
            method(3, &[0], &[]),
            method(4, &[3, 1, 1], &[]),
            method(4, &[2], &[]),
        ],
        &[],
        &[1],
    );
    for cfg in modes().filter(|cfg| cfg.relaxed_bound && cfg.strategy == SearchStrategy::AStar) {
        let result = search(&p, &cfg).unwrap();
        assert!(result.stats.relaxed_evaluated > 0);
        let s = solved(result.outcome);
        assert_eq!(s.cost, 6, "{cfg:?}");
        assert!(s.cost_optimal);
        assert_eq!(validate::validate(&p, &s.certificate).unwrap(), 6);
    }
}

#[test]
fn relaxed_execution_rejects_unseeded_support_cycles() {
    let p = problem(
        vec![action(0, &[0], &[1], &[]), action(0, &[1], &[0], &[])],
        1,
        vec![method(2, &[0, 1], &[])],
        &[],
        &[0],
    );
    for cfg in modes().filter(|cfg| cfg.relaxed_bound) {
        let result = search(&p, &cfg).unwrap();
        assert!(matches!(result.outcome, Outcome::NoSolution));
        // Eager/recomputed TDG can already discover this dead end.
        if cfg.tdg == TdgMode::Static {
            assert_eq!(result.stats.relaxed_pruned, 1);
            assert_eq!(result.stats.expanded, 0);
        }
    }
}

#[test]
fn relaxed_execution_still_underestimates_independent_joint_goals() {
    // Each goal costs 1 separately, so h_max and necessary support both give
    // 1. Their conjunction costs 2: an infinite cheaper plateau remains.
    let p = problem(
        vec![action(1, &[], &[0], &[]), action(1, &[], &[1], &[])],
        1,
        vec![
            method(2, &[2, 2], &[]),
            method(2, &[], &[]),
            method(2, &[0], &[]),
            method(2, &[1], &[]),
        ],
        &[],
        &[0, 1],
    );
    for astar_tie in [
        AStarTieBreak::Fifo,
        AStarTieBreak::LargerG,
        AStarTieBreak::Modification,
    ] {
        let result = search(
            &p,
            &Config {
                strategy: SearchStrategy::AStar,
                support_bound: true,
                relaxed_bound: true,
                astar_tie,
                node_limit: Some(100),
                ..Config::default()
            },
        )
        .unwrap();
        assert!(matches!(
            result.outcome,
            Outcome::Stopped(StopReason::NodeLimit)
        ));
    }
    let s = solved(
        search(
            &p,
            &Config {
                support_bound: true,
                relaxed_bound: true,
                node_limit: Some(1000),
                ..Config::default()
            },
        )
        .unwrap()
        .outcome,
    );
    assert_eq!(s.cost, 2);
}

#[test]
fn tdg_handles_productive_mutual_recursion_empty_exits_and_repeated_children() {
    let p = problem(
        vec![action(7, &[], &[0], &[]), action(3, &[], &[1], &[])],
        5,
        vec![
            method(2, &[3], &[]),
            method(2, &[0, 0], &[]),
            method(3, &[2], &[]),
            method(3, &[1, 1], &[]),
            method(4, &[4], &[]),
            method(4, &[], &[]),
            method(5, &[0, 5], &[]), // No exit, despite an apparent achiever.
            method(6, &[2, 2, 4], &[]),
            method(6, &[5], &[]),
        ],
        &[],
        &[],
    );
    let tdg = Tdg::new(&p);
    assert_eq!(tdg.task_cost(2), Some(6));
    assert_eq!(tdg.task_cost(3), Some(6));
    assert_eq!(tdg.method_cost(1), Some(14));
    assert_eq!(tdg.task_cost(4), Some(0));
    assert_eq!(tdg.task_cost(5), None);
    assert_eq!(tdg.task_cost(6), Some(12));
    assert!(tdg.may_add(2, 0) && tdg.may_add(2, 1));
    assert!(!tdg.may_add(4, 0) && !tdg.may_add(5, 0));
    for flaws in [
        FlawSelection::DecompositionFirst,
        FlawSelection::Interleaved,
        FlawSelection::Systematic,
    ] {
        let s = solved(
            search(&p, &config(SearchStrategy::AStar, flaws))
                .unwrap()
                .outcome,
        );
        assert_eq!(s.cost, 12);
        assert_eq!(s.certificate.steps.len(), 4);
        assert!(s.cost_optimal);
        assert_eq!(tdg.remaining_cost(&p, &s.plan), Some(0));
    }
}

#[test]
fn structural_dead_ends_are_distinct_from_limits_and_cost_overflow() {
    let dead = problem(vec![], 1, vec![method(0, &[0], &[])], &[], &[]);
    let guided = config(SearchStrategy::AStar, FlawSelection::Interleaved);
    let result = search(&dead, &guided).unwrap();
    assert!(matches!(result.outcome, Outcome::NoSolution));
    assert_eq!(result.stats.tdg_pruned, 1);
    assert!(matches!(
        search(
            &dead,
            &Config {
                node_limit: Some(0),
                ..guided.clone()
            }
        )
        .unwrap()
        .outcome,
        Outcome::Stopped(StopReason::NodeLimit)
    ));
    let huge = problem(
        vec![action(u64::MAX, &[], &[], &[])],
        1,
        vec![method(1, &[0, 0], &[])],
        &[],
        &[],
    );
    assert_eq!(Tdg::new(&huge).task_cost(1), Some(COST_CAP));
    assert!(search(&huge, &guided)
        .unwrap_err()
        .contains("cost overflow"));
    let exact = problem(vec![action(u64::MAX, &[], &[], &[])], 0, vec![], &[], &[]);
    assert_eq!(
        solved(search(&exact, &guided).unwrap().outcome).cost,
        u64::MAX
    );
    // An overflowing alternative must not abort the representable solution.
    let alternative = problem(
        vec![action(u64::MAX, &[], &[], &[]), action(2, &[], &[], &[])],
        1,
        vec![method(2, &[0, 0], &[]), method(2, &[1], &[])],
        &[],
        &[],
    );
    let result = search(&alternative, &guided).unwrap();
    assert_eq!(result.stats.cost_bound_pruned, 1);
    assert_eq!(solved(result.outcome).cost, 2);
    // Overflowing alternatives cannot turn failure into a false UNSAT claim.
    let impossible = problem(
        vec![action(u64::MAX, &[], &[], &[]), action(2, &[0], &[], &[])],
        1,
        vec![method(2, &[0, 0], &[]), method(2, &[1], &[])],
        &[],
        &[],
    );
    assert!(search(&impossible, &guided)
        .unwrap_err()
        .contains("cost overflow"));
}

#[test]
fn deep_cost_bounds_saturate_without_becoming_unreachable() {
    let mut methods = vec![method(1, &[0, 0], &[])];
    for task in 2..=160 {
        methods.push(method(task, &[task - 1, task - 1], &[]));
    }
    let p = problem(vec![action(1, &[], &[], &[])], 160, methods, &[], &[]);
    let tdg = Tdg::new(&p);
    assert_eq!(tdg.task_cost(63), Some(1u128 << 63));
    assert_eq!(tdg.task_cost(64), Some(COST_CAP));
    assert_eq!(tdg.task_cost(160), Some(COST_CAP));
}

#[test]
fn astar_optimises_cost_across_different_refinement_depths() {
    let p = problem(
        vec![action(9, &[], &[], &[]), action(1, &[], &[], &[])],
        2,
        vec![
            method(2, &[1, 1], &[]),
            method(3, &[0], &[]),
            method(3, &[2], &[]),
        ],
        &[],
        &[],
    );
    for flaws in [
        FlawSelection::DecompositionFirst,
        FlawSelection::Interleaved,
        FlawSelection::Systematic,
    ] {
        let bfs = solved(
            search(&p, &config(SearchStrategy::BreadthFirst, flaws))
                .unwrap()
                .outcome,
        );
        let astar = solved(
            search(&p, &config(SearchStrategy::AStar, flaws))
                .unwrap()
                .outcome,
        );
        assert_eq!(bfs.cost, 9);
        assert!(!bfs.cost_optimal);
        assert_eq!(astar.cost, 2);
        assert!(astar.cost_optimal);
        // Losing the cheaper branch at a depth cutoff invalidates optimality.
        let bounded = solved(
            search(
                &p,
                &Config {
                    max_depth: Some(1),
                    ..config(SearchStrategy::AStar, flaws)
                },
            )
            .unwrap()
            .outcome,
        );
        assert_eq!(bounded.cost, 9);
        assert!(!bounded.cost_optimal);
    }
}

#[test]
fn breadth_first_is_fair_when_astar_has_an_infinite_lower_cost_plateau() {
    let p = problem(
        vec![action(0, &[0], &[], &[]), action(1, &[], &[], &[])],
        2,
        vec![
            method(2, &[2], &[]),
            method(2, &[0], &[]),
            method(3, &[2], &[]),
            method(3, &[1], &[]),
        ],
        &[],
        &[],
    );
    // TDG ignores the unsatisfied precondition, so the recursive branch has f=0.
    let bfs = solved(search(&p, &Config::default()).unwrap().outcome);
    assert_eq!(bfs.cost, 1);
    assert!(matches!(
        search(
            &p,
            &Config {
                node_limit: Some(50),
                ..config(SearchStrategy::AStar, FlawSelection::DecompositionFirst)
            }
        )
        .unwrap()
        .outcome,
        Outcome::Stopped(StopReason::NodeLimit)
    ));
    for mut cfg in modes() {
        cfg.unit_cycles = UnitCyclePolicy::Prune;
        cfg.node_limit = Some(50);
        let s = solved(search(&p, &cfg).unwrap().outcome);
        assert_eq!(s.cost, 1);
        assert_eq!(s.cost_optimal, cfg.strategy == SearchStrategy::AStar);
    }
}

#[test]
fn later_decomposition_can_threaten_an_established_initial_link() {
    for edges in [vec![], vec![(0, 1)]] {
        // The consumer of initial p is linked before the compound is expanded.
        // Its newly introduced delete must then be ordered after the consumer.
        let p = problem(
            vec![action(1, &[], &[], &[0]), action(1, &[0], &[], &[])],
            2,
            vec![method(2, &[0], &[]), method(3, &[2, 1], &edges)],
            &[0],
            &[],
        );
        for strategy in [
            SearchStrategy::BreadthFirst,
            SearchStrategy::AStar,
            SearchStrategy::Greedy,
        ] {
            let result = search(&p, &config(strategy, FlawSelection::Interleaved)).unwrap();
            if edges.is_empty() {
                assert!(result.stats.threat_orderings > 0);
                let s = solved(result.outcome);
                assert_eq!(
                    s.certificate
                        .steps
                        .iter()
                        .map(|t| t.task)
                        .collect::<Vec<_>>(),
                    [1, 0]
                );
            } else {
                assert!(matches!(result.outcome, Outcome::NoSolution));
            }
        }
    }
}

#[test]
fn a_future_supporter_must_be_considered_even_when_initial_support_exists() {
    // initial p -> consumer fails because of the forced intervening delete.
    // The only solution obtains a fresh p from the still-abstract restorer.
    let p = problem(
        vec![
            action(1, &[], &[], &[0]),
            action(1, &[], &[0], &[]),
            action(1, &[0], &[], &[]),
        ],
        2,
        vec![
            method(3, &[1], &[]),
            method(4, &[0, 3, 2], &[(0, 1), (1, 2)]),
        ],
        &[0],
        &[],
    );
    for strategy in [
        SearchStrategy::BreadthFirst,
        SearchStrategy::AStar,
        SearchStrategy::Greedy,
    ] {
        let result = search(&p, &config(strategy, FlawSelection::Interleaved)).unwrap();
        assert!(result.stats.support_decompositions > 0);
        let s = solved(result.outcome);
        assert_eq!(
            s.certificate
                .steps
                .iter()
                .map(|t| t.task)
                .collect::<Vec<_>>(),
            [0, 1, 2]
        );
    }
}

#[test]
fn compound_after_consumer_cannot_provide_support_and_empty_tasks_stay_required() {
    let impossible = problem(
        vec![action(1, &[], &[0], &[]), action(1, &[0], &[], &[])],
        2,
        vec![method(2, &[0], &[]), method(3, &[1, 2], &[(0, 1)])],
        &[],
        &[],
    );
    for cfg in modes() {
        assert!(matches!(
            search(&impossible, &cfg).unwrap().outcome,
            Outcome::NoSolution
        ));
    }
    let empty = problem(
        vec![],
        2,
        vec![method(0, &[], &[]), method(1, &[0, 0], &[])],
        &[0],
        &[0],
    );
    let s = solved(
        search(
            &empty,
            &config(SearchStrategy::AStar, FlawSelection::Interleaved),
        )
        .unwrap()
        .outcome,
    );
    assert!(s.certificate.steps.is_empty());
    assert_eq!(s.certificate.decompositions.len(), 3);
}

// Independent oracle: flatten each method choice, enumerate all permutations,
// enforce inherited edges, and simulate facts. No TDG or causal-link routines.
fn executable(
    actions: &[Action],
    tasks: &[usize; 3],
    edges: &[(usize, usize)],
    initial: bool,
) -> bool {
    for order in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let mut position = [0; 3];
        for (i, &occurrence) in order.iter().enumerate() {
            position[occurrence] = i;
        }
        if edges.iter().any(|&(a, b)| position[a] >= position[b]) {
            continue;
        }
        let mut state = initial;
        let mut valid = true;
        for occurrence in order {
            let a = &actions[tasks[occurrence]];
            if !a.preconditions.is_empty() && !state {
                valid = false;
                break;
            }
            if !a.delete.is_empty() {
                state = false;
            }
            if !a.add.is_empty() {
                state = true;
            }
        }
        if valid && state {
            return true;
        }
    }
    false
}

#[test]
fn all_search_modes_match_an_independent_hierarchical_oracle() {
    let variants = [
        action(0, &[], &[0], &[]),
        action(3, &[], &[], &[0]),
        action(1, &[0], &[], &[]),
        action(2, &[0], &[], &[0]),
    ];
    for code in 0..64 {
        let actions = vec![
            variants[code % 4].clone(),
            variants[(code / 4) % 4].clone(),
            variants[code / 16].clone(),
        ];
        // Root = left(0; 1 or 2) || right(2); optional left internal edge and
        // optional all-left-before-right inheritance. Repetition is intentional.
        for ordered_left in [false, true] {
            for ordered_root in [false, true] {
                for initial in [false, true] {
                    let mut edges = Vec::new();
                    if ordered_left {
                        edges.push((0, 1));
                    }
                    if ordered_root {
                        edges.extend([(0, 2), (1, 2)]);
                    }
                    let expected = [1, 2]
                        .into_iter()
                        .filter_map(|choice| {
                            let tasks = [0, choice, 2];
                            executable(&actions, &tasks, &edges, initial)
                                .then(|| tasks.iter().map(|&t| actions[t].cost).sum::<u64>())
                        })
                        .min();
                    let p = problem(
                        actions.clone(),
                        3,
                        vec![
                            method(3, &[0, 1], if ordered_left { &[(0, 1)] } else { &[] }),
                            method(3, &[0, 2], if ordered_left { &[(0, 1)] } else { &[] }),
                            method(4, &[2], &[]),
                            method(5, &[3, 4], if ordered_root { &[(0, 1)] } else { &[] }),
                        ],
                        if initial { &[0] } else { &[] },
                        &[0],
                    );
                    for cfg in modes() {
                        let result = search(&p, &cfg).unwrap();
                        match (result.outcome, expected) {
                            (Outcome::NoSolution, None) => {},
                            (Outcome::Solved(s), Some(optimum)) => {
                                assert_eq!(validate::validate(&p, &s.certificate).unwrap(), s.cost);
                                if cfg.strategy == SearchStrategy::AStar {
                                    assert!(s.cost_optimal);
                                    assert_eq!(s.cost, optimum);
                                }
                            },
                            (actual, expected) => panic!("code={code} left={ordered_left} root={ordered_root} init={initial} config={cfg:?}: {actual:?}, expected={expected:?}"),
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn lazy_tdg_reranks_without_spending_node_budget_and_caches_equivalent_networks() {
    // The root can supply p through an expensive alternative. Selecting either
    // of two identical X branches removes that enabler: X then costs 8, exceeds
    // u64, or is impossible. A direct cost-3 solution is already in OPEN.
    // Both X entries must be repaired/pruned before expansion, without charging
    // a new node for requeueing. Their distinct histories share a relaxed bound.
    for expensive in [None, Some(4), Some(u64::MAX)] {
        let mut methods = vec![
            method(4, &[0], &[]),
            method(5, &[4], &[]),
            method(5, &[4], &[]),
            method(5, &[1], &[]),
            method(5, &[3, 0], &[]),
        ];
        if expensive.is_some() {
            methods.push(method(4, &[2, 2], &[]));
        }
        let p = problem(
            vec![
                action(1, &[0], &[], &[]),
                action(3, &[], &[], &[]),
                action(expensive.unwrap_or(4), &[], &[], &[]),
                action(50, &[], &[0], &[]),
            ],
            2,
            methods,
            &[],
            &[],
        );
        for (tdg, astar_tie) in [TdgMode::Lazy, TdgMode::LazyCached]
            .into_iter()
            .flat_map(|tdg| {
                [
                    AStarTieBreak::Fifo,
                    AStarTieBreak::LargerG,
                    AStarTieBreak::Modification,
                ]
                .into_iter()
                .map(move |tie| (tdg, tie))
            })
        {
            let result = search(
                &p,
                &Config {
                    strategy: SearchStrategy::AStar,
                    tdg,
                    astar_tie,
                    node_limit: Some(5),
                    ..Config::default()
                },
            )
            .unwrap();
            assert_eq!(result.stats.generated, 5);
            assert_eq!(result.stats.expanded, 2);
            assert_eq!(
                result.stats.tdg_requeued,
                if expensive == Some(4) { 2 } else { 0 }
            );
            assert_eq!(
                result.stats.cost_bound_pruned,
                if expensive == Some(u64::MAX) { 2 } else { 0 }
            );
            assert_eq!(
                result.stats.tdg_pruned,
                if expensive.is_none() { 2 } else { 0 }
            );
            assert_eq!(
                result.stats.tdg_cache_hits,
                usize::from(tdg == TdgMode::LazyCached)
            );
            assert_eq!(
                result.stats.tdg_recomputed,
                if tdg == TdgMode::LazyCached { 3 } else { 4 }
            );
            let solution = solved(result.outcome);
            assert_eq!(solution.cost, 3);
            assert!(solution.cost_optimal);
            assert_eq!(validate::validate(&p, &solution.certificate).unwrap(), 3);
        }
    }
}

#[test]
fn lazy_hmax_repairs_priorities_and_prunes_before_expansion() {
    // At the root, the cost-0 p-achiever makes q look cheap. The two X choices
    // lose it, leaving cost 5, overflow, or no supporter. Defer these checks
    // until selection, but repair them before accepting the cost-3 competitor.
    for expensive in [None, Some(4), Some(u64::MAX)] {
        let mut methods = vec![
            method(5, &[], &[]),
            method(6, &[5, 0], &[]),
            method(7, &[6], &[]),
            method(7, &[6], &[]),
            method(7, &[1], &[]),
            method(7, &[3, 4], &[]),
        ];
        if expensive.is_some() {
            methods.push(method(5, &[2], &[]));
        }
        let p = problem(
            vec![
                action(1, &[0], &[1], &[]),
                action(3, &[], &[1], &[]),
                action(expensive.unwrap_or(4), &[], &[0], &[]),
                action(0, &[], &[0], &[]),
                action(0, &[1], &[], &[]),
            ],
            3,
            methods,
            &[],
            &[1],
        );
        for astar_tie in [
            AStarTieBreak::Fifo,
            AStarTieBreak::LargerG,
            AStarTieBreak::Modification,
        ] {
            let result = search(
                &p,
                &Config {
                    strategy: SearchStrategy::AStar,
                    astar_tie,
                    relaxed_bound: true,
                    node_limit: Some(5),
                    ..Config::default()
                },
            )
            .unwrap();
            assert_eq!(result.stats.generated, 5);
            assert_eq!(result.stats.expanded, 3);
            assert_eq!(
                result.stats.relaxed_requeued,
                if expensive == Some(4) { 2 } else { 0 }
            );
            assert_eq!(
                result.stats.cost_bound_pruned,
                if expensive == Some(u64::MAX) { 2 } else { 0 }
            );
            assert_eq!(
                result.stats.relaxed_pruned,
                if expensive.is_none() { 2 } else { 0 }
            );
            assert_eq!(result.stats.relaxed_cache_hits, 1);
            assert_eq!(result.stats.relaxed_shared, 0);
            let s = solved(result.outcome);
            assert_eq!(s.cost, 3);
            assert!(s.cost_optimal);
            assert_eq!(validate::validate(&p, &s.certificate).unwrap(), 3);
        }
    }
}
