#![cfg(feature = "htn")]

use potoroo::htn::{
    search,
    tdg::{Tdg, COST_CAP},
    validate, AStarTieBreak, Action, Config, FlawSelection, Method, Outcome, Problem,
    SearchStrategy, Solution, StopReason, Task, TdgMode,
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
                .map(move |astar_tie| Config {
                    tdg,
                    astar_tie,
                    ..config(strategy, flaws)
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
