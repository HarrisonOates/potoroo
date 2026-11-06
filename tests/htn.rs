#![cfg(feature = "htn")]

use potoroo::htn::{
    input, search, validate, Action, Config, Method, Outcome, Problem, StopReason, Task,
};
use std::time::Instant;

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
    let tasks = (0..actions.len() + compounds)
        .map(|i| Task {
            name: format!("t{i}[]"),
            primitive: i < actions.len(),
        })
        .collect::<Vec<_>>();
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

fn solve(p: &Problem) -> potoroo::htn::Solution {
    match search(
        p,
        &Config {
            node_limit: Some(20_000),
            ..Config::default()
        },
    )
    .unwrap()
    .outcome
    {
        Outcome::Solved(s) => s,
        other => panic!("expected solution, got {other:?}"),
    }
}

#[test]
fn repeated_effectless_tasks_are_required_and_costed() {
    let p = problem(
        vec![action(7, &[], &[], &[])],
        1,
        vec![method(1, &[0, 0], &[])],
        &[],
        &[],
    );
    let s = solve(&p);
    assert_eq!(s.cost, 14);
    assert_eq!(s.certificate.steps.len(), 2);
    assert_ne!(s.certificate.steps[0].id, s.certificate.steps[1].id);
    let mut missing = s.certificate.clone();
    missing.steps.pop();
    assert!(validate::validate(&p, &missing).is_err());
    let mut reused = s.certificate.clone();
    reused.decompositions[0].children[1].id = reused.decompositions[0].children[0].id;
    assert!(validate::validate(&p, &reused).is_err());
}

#[test]
fn causal_support_can_come_from_a_later_decomposition() {
    // Both roots must be decomposed before classifying the consumer as dead.
    let p = problem(
        vec![action(1, &[], &[0], &[]), action(1, &[0], &[1], &[])],
        3,
        vec![
            method(2, &[0], &[]),
            method(3, &[1], &[]),
            method(4, &[2, 3], &[]),
        ],
        &[],
        &[1],
    );
    let s = solve(&p);
    assert_eq!(
        s.certificate
            .steps
            .iter()
            .map(|s| s.task)
            .collect::<Vec<_>>(),
        [0, 1]
    );
}

#[test]
fn unrelated_subtrees_can_interleave() {
    // left = produce < finish; right = consume. Only produce,consume,finish works.
    let p = problem(
        vec![
            action(2, &[], &[0], &[]),
            action(3, &[0], &[1], &[0]),
            action(5, &[1], &[], &[]),
        ],
        3,
        vec![
            method(3, &[0, 2], &[(0, 1)]),
            method(4, &[1], &[]),
            method(5, &[3, 4], &[]),
        ],
        &[],
        &[1],
    );
    let s = solve(&p);
    assert_eq!(s.cost, 10);
    assert_eq!(
        s.certificate
            .steps
            .iter()
            .map(|s| s.task)
            .collect::<Vec<_>>(),
        [0, 1, 2]
    );
}

#[test]
fn external_orderings_apply_to_all_descendants_without_serializing_siblings() {
    let p = problem(
        vec![action(0, &[], &[], &[])],
        3,
        vec![
            method(1, &[0, 0], &[]),
            method(2, &[0, 0], &[]),
            method(3, &[1, 2], &[(0, 1)]),
        ],
        &[],
        &[],
    );
    let s = solve(&p);
    let left = s
        .certificate
        .decompositions
        .iter()
        .find(|d| d.parent.task == 1)
        .unwrap();
    let right = s
        .certificate
        .decompositions
        .iter()
        .find(|d| d.parent.task == 2)
        .unwrap();
    for a in &left.children {
        for b in &right.children {
            assert!(s.plan.ordered_before(a.id, b.id));
        }
    }
    assert!(!s
        .plan
        .ordered_before(left.children[0].id, left.children[1].id));
    assert!(!s
        .plan
        .ordered_before(left.children[1].id, left.children[0].id));
    let mut bad = s.certificate.clone();
    bad.steps.swap(1, 2);
    assert!(validate::validate(&p, &bad)
        .unwrap_err()
        .contains("ordering"));
}

#[test]
fn cannot_insert_a_classical_achiever_outside_the_hierarchy() {
    let p = problem(
        vec![action(1, &[], &[0], &[]), action(1, &[0], &[], &[])],
        1,
        vec![method(2, &[1], &[])],
        &[],
        &[],
    );
    assert!(matches!(
        search(&p, &Config::default()).unwrap().outcome,
        Outcome::NoSolution
    ));
}

#[test]
fn threats_are_resolved_by_ordering_required_occurrences() {
    let p = problem(
        vec![action(1, &[], &[], &[0]), action(1, &[0], &[1], &[])],
        1,
        vec![method(2, &[0, 1], &[])],
        &[0],
        &[1],
    );
    let result = search(&p, &Config::default()).unwrap();
    assert!(result.stats.threat_orderings > 0);
    let Outcome::Solved(s) = result.outcome else {
        panic!("expected solved")
    };
    assert_eq!(
        s.certificate
            .steps
            .iter()
            .map(|s| s.task)
            .collect::<Vec<_>>(),
        [1, 0]
    );
    let impossible = problem(
        vec![action(1, &[], &[], &[0]), action(1, &[0], &[1], &[])],
        1,
        vec![method(2, &[0, 1], &[(0, 1)])],
        &[0],
        &[1],
    );
    assert!(matches!(
        search(&impossible, &Config::default()).unwrap().outcome,
        Outcome::NoSolution
    ));
}

#[test]
fn primitive_root_goals_and_simultaneous_add_delete() {
    let p = problem(vec![action(4, &[], &[0], &[0])], 0, vec![], &[], &[0]);
    assert_eq!(solve(&p).cost, 4);
    let impossible = problem(vec![action(1, &[0], &[], &[])], 0, vec![], &[], &[]);
    assert!(matches!(
        search(&impossible, &Config::default()).unwrap().outcome,
        Outcome::NoSolution
    ));
}

#[test]
fn empty_methods_preserve_transitive_external_ordering() {
    let p = problem(
        vec![action(0, &[], &[], &[]), action(0, &[], &[], &[])],
        2,
        vec![
            method(2, &[], &[]),
            method(3, &[0, 2, 1], &[(0, 1), (1, 2)]),
        ],
        &[],
        &[],
    );
    let s = solve(&p);
    assert_eq!(
        s.certificate
            .steps
            .iter()
            .map(|s| s.task)
            .collect::<Vec<_>>(),
        [0, 1]
    );
    let mut wrong = s.certificate.clone();
    wrong.steps.reverse();
    assert!(validate::validate(&p, &wrong)
        .unwrap_err()
        .contains("ordering"));
    let empty = problem(vec![], 1, vec![method(0, &[], &[])], &[], &[]);
    assert!(solve(&empty).certificate.steps.is_empty());
}

#[test]
fn recursion_and_resource_limits_do_not_claim_unsolvability() {
    let p = problem(
        vec![],
        1,
        vec![method(0, &[0], &[]), method(0, &[], &[])],
        &[],
        &[],
    );
    assert!(solve(&p).certificate.steps.is_empty());
    let loop_only = problem(vec![], 1, vec![method(0, &[0], &[])], &[], &[]);
    // Exercise cutoffs without TDG pruning, which proves this loop unsolvable.
    let baseline = Config {
        flaws: potoroo::htn::FlawSelection::DecompositionFirst,
        ..Config::default()
    };
    let cases = [
        (
            Config {
                node_limit: Some(8),
                ..baseline.clone()
            },
            StopReason::NodeLimit,
        ),
        (
            Config {
                node_limit: Some(0),
                ..baseline.clone()
            },
            StopReason::NodeLimit,
        ),
        (
            Config {
                max_depth: Some(3),
                ..baseline.clone()
            },
            StopReason::DepthLimit,
        ),
        (
            Config {
                deadline: Some(Instant::now()),
                ..baseline
            },
            StopReason::Deadline,
        ),
    ];
    for (config, expected) in cases {
        assert!(
            matches!(search(&loop_only, &config).unwrap().outcome, Outcome::Stopped(reason) if reason == expected)
        );
    }
    let dead = problem(vec![], 1, vec![], &[], &[]);
    assert!(matches!(
        search(
            &dead,
            &Config {
                max_depth: Some(0),
                ..Config::default()
            }
        )
        .unwrap()
        .outcome,
        Outcome::NoSolution
    ));
}

#[test]
fn validator_rejects_wrong_methods_extra_steps_and_inexecutable_plans() {
    let p = problem(
        vec![action(1, &[], &[0], &[]), action(1, &[0], &[1], &[])],
        1,
        vec![method(2, &[0, 1], &[])],
        &[],
        &[1],
    );
    let s = solve(&p);
    let mut bad = s.certificate.clone();
    bad.steps.reverse();
    assert!(validate::validate(&p, &bad)
        .unwrap_err()
        .contains("precondition"));
    let mut bad = s.certificate.clone();
    bad.decompositions[0].method = usize::MAX;
    assert!(validate::validate(&p, &bad).is_err());
    let mut bad = s.certificate.clone();
    bad.steps
        .push(potoroo::htn::plan::Occurrence { id: 1234, task: 0 });
    assert!(validate::validate(&p, &bad).is_err());
    let mut bad = s.certificate.clone();
    bad.decompositions[0].children.reverse();
    assert!(validate::validate(&p, &bad).is_err());
}

#[test]
fn cost_overflow_is_an_error() {
    let p = problem(
        vec![action(u64::MAX, &[], &[], &[])],
        1,
        vec![method(1, &[0, 0], &[])],
        &[],
        &[],
    );
    assert!(search(&p, &Config::default())
        .unwrap_err()
        .contains("cost overflow"));
}

const GROUND: &str = "\
;; Grounded PANDA format
1
p[]
1
0 0 var0
0
0
0
1
3
-1
0 0 -1
-1
-1
0 -1
2
0 make[]
1 root[]
1
1
do-make
1
0 0 -1
0 1 -1
";

#[test]
fn grounded_reader_preserves_multiplicity_and_rejects_malformed_input() {
    let p = input::read(GROUND).unwrap();
    assert_eq!(solve(&p).cost, 6);
    assert!(input::read(&GROUND.replace("0 0 -1\n-1", "1 0 0 -1\n-1"))
        .unwrap_err()
        .contains("conditional effects"));
    for malformed in [
        GROUND.replace("0 1 -1", "0 1 1 0 -1"), // cycle
        GROUND.replace("0 1 -1", "0 -1"),       // odd edge list
        GROUND.replace("0 1 -1", "0 9 -1"),     // invalid occurrence
        GROUND.replace("0 0 -1\n0 1", "0 999 -1\n0 1"),
        GROUND.replace("0 0 -1\n-1", "0 9 -1\n-1"), // invalid fact
        GROUND.replace("0 make[]", "1 make[]"),
        GROUND.replace("\n3\n", "\n-3\n"),
        GROUND.replace("0 0 -1\n-1", "1 0 0 -1\n-1"), // conditional effect
        format!("{GROUND}\n123"),
    ] {
        assert!(
            input::read(&malformed).is_err(),
            "accepted malformed input: {malformed}"
        );
    }
    // Every prefix ending at a line boundary must produce an error, not panic.
    for (offset, _) in GROUND.match_indices('\n') {
        if offset < GROUND.trim_end().len() {
            assert!(input::read(&GROUND[..offset]).is_err());
        }
    }
}

/// Independent finite oracle: enumerate all six linearisations of a fixed
/// three-occurrence network and execute directly, without causal-link search.
fn oracle(actions: &[Action], edges: &[(usize, usize)], initial: bool) -> bool {
    for order in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let mut position = [0; 3];
        for (i, &a) in order.iter().enumerate() {
            position[a] = i;
        }
        if edges.iter().any(|&(a, b)| position[a] >= position[b]) {
            continue;
        }
        let mut state = initial;
        let mut valid = true;
        for a in order {
            if !actions[a].preconditions.is_empty() && !state {
                valid = false;
                break;
            }
            if !actions[a].delete.is_empty() {
                state = false;
            }
            if !actions[a].add.is_empty() {
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
fn finite_oracle_matches_causal_search_on_1024_networks() {
    let variants = [
        action(1, &[], &[0], &[]),
        action(1, &[], &[], &[0]),
        action(1, &[0], &[], &[]),
        action(1, &[0], &[], &[0]),
    ];
    let possible_edges = [(0, 1), (0, 2), (1, 2)];
    for code in 0..64 {
        let actions = vec![
            variants[code % 4].clone(),
            variants[(code / 4) % 4].clone(),
            variants[code / 16].clone(),
        ];
        for mask in 0..8 {
            let edges: Vec<_> = possible_edges
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, &e)| e)
                .collect();
            for initial in [false, true] {
                let expected = oracle(&actions, &edges, initial);
                let p = problem(
                    actions.clone(),
                    1,
                    vec![method(3, &[0, 1, 2], &edges)],
                    if initial { &[0] } else { &[] },
                    &[0],
                );
                let result = search(
                    &p,
                    &Config {
                        node_limit: Some(20_000),
                        ..Config::default()
                    },
                )
                .unwrap();
                assert!(!matches!(result.outcome, Outcome::Stopped(_)));
                assert_eq!(
                    matches!(result.outcome, Outcome::Solved(_)),
                    expected,
                    "code={code} mask={mask} initial={initial}"
                );
            }
        }
    }
}
