//! Exhaust the refinement tree, including every linearization of every solution.
//! Compare against an independent decomposition/permutation/state-space oracle.
use std::collections::{BTreeMap, HashMap, HashSet};

use super::plan::Plan;
use super::refine::{self, FlawSelection};
use super::tdg::Tdg;
use super::validate::{self, Certificate};
use super::{search, Action, Config, Method, Outcome, Problem, SearchStrategy, StopReason, Task};

type Path = Vec<usize>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Witness {
    methods: Vec<(Path, usize)>,
    execution: Vec<Path>,
}

#[derive(Clone, Default)]
struct Network {
    methods: Vec<(Path, usize)>,
    leaves: Vec<(Path, usize)>,
    edges: Vec<(usize, usize)>,
}

// This oracle never calls Plan, refinement, TDG or the production validator.
fn networks(p: &Problem, task: usize, path: Path) -> Vec<Network> {
    assert!(
        path.len() < 8,
        "oracle fixtures must have finite, small trees"
    );
    if p.tasks()[task].primitive {
        return vec![Network {
            leaves: vec![(path, task)],
            ..Network::default()
        }];
    }
    let mut result = Vec::new();
    for (mid, method) in p
        .methods()
        .iter()
        .enumerate()
        .filter(|(_, m)| m.task == task)
    {
        let n = method.subtasks.len();
        let mut before = vec![vec![false; n]; n];
        for &(a, b) in &method.orderings {
            before[a][b] = true;
        }
        // Close before flattening: ordering paths through empty children count.
        for k in 0..n {
            for a in 0..n {
                for b in 0..n {
                    before[a][b] |= before[a][k] && before[k][b];
                }
            }
        }
        let initial = Network {
            methods: vec![(path.clone(), mid)],
            ..Network::default()
        };
        let mut partials = vec![(initial, Vec::<std::ops::Range<usize>>::new())];
        for (slot, &child) in method.subtasks.iter().enumerate() {
            let mut child_path = path.clone();
            child_path.push(slot);
            let options = networks(p, child, child_path);
            let mut next = Vec::new();
            for (prefix, spans) in partials {
                for suffix in &options {
                    let mut joined = prefix.clone();
                    let offset = joined.leaves.len();
                    joined.methods.extend(suffix.methods.clone());
                    joined.leaves.extend(suffix.leaves.clone());
                    joined
                        .edges
                        .extend(suffix.edges.iter().map(|&(a, b)| (a + offset, b + offset)));
                    let mut spans = spans.clone();
                    spans.push(offset..joined.leaves.len());
                    next.push((joined, spans));
                }
            }
            partials = next;
        }
        for (mut network, spans) in partials {
            for a in 0..n {
                for b in 0..n {
                    if before[a][b] {
                        for x in spans[a].clone() {
                            for y in spans[b].clone() {
                                network.edges.push((x, y));
                            }
                        }
                    }
                }
            }
            network.methods.sort();
            result.push(network);
        }
    }
    result
}

fn permutations(n: usize) -> Vec<Vec<usize>> {
    fn visit(prefix: &mut Vec<usize>, n: usize, result: &mut Vec<Vec<usize>>) {
        if prefix.len() == n {
            result.push(prefix.clone());
        } else {
            for i in 0..n {
                if !prefix.contains(&i) {
                    prefix.push(i);
                    visit(prefix, n, result);
                    prefix.pop();
                }
            }
        }
    }
    assert!(n <= 6);
    let mut result = Vec::new();
    visit(&mut Vec::new(), n, &mut result);
    result
}

fn executes(p: &Problem, tasks: impl Iterator<Item = usize>) -> bool {
    let mut state: HashSet<_> = p.initial().iter().copied().collect();
    for task in tasks {
        let action = &p.actions()[task];
        if !action.preconditions.iter().all(|f| state.contains(f)) {
            return false;
        }
        for f in &action.delete {
            state.remove(f);
        }
        state.extend(&action.add);
    }
    p.goal().iter().all(|f| state.contains(f))
}

fn oracle(p: &Problem) -> HashSet<Witness> {
    let mut result = HashSet::new();
    for network in networks(p, p.root(), vec![]) {
        for order in permutations(network.leaves.len()) {
            let mut positions = vec![0; order.len()];
            for (pos, &i) in order.iter().enumerate() {
                positions[i] = pos;
            }
            if network
                .edges
                .iter()
                .all(|&(a, b)| positions[a] < positions[b])
                && executes(p, order.iter().map(|&i| network.leaves[i].1))
            {
                result.insert(Witness {
                    methods: network.methods.clone(),
                    execution: order.iter().map(|&i| network.leaves[i].0.clone()).collect(),
                });
            }
        }
    }
    result
}

fn enumerate(p: &Problem, policy: FlawSelection) -> (HashMap<Witness, usize>, usize) {
    let tdg = Tdg::new(p);
    let mut pending = vec![Plan::initial(p)];
    let mut result = HashMap::new();
    let mut visited = 0;
    while let Some(plan) = pending.pop() {
        visited += 1;
        assert!(visited < 200_000, "unexpected refinement explosion");
        let done = plan.compound(p).is_none()
            && plan.open_conditions().next().is_none()
            && plan.support_focus.is_none()
            && plan
                .threat(p, policy == FlawSelection::Systematic)
                .is_none();
        if !done {
            for choice in refine::choices(p, &plan, policy, Some(&tdg), None).unwrap() {
                if let Some(child) = choice.apply(p, &plan).unwrap() {
                    pending.push(child);
                }
            }
            continue;
        }
        // Name occurrences by method slots, independently of allocation order.
        let mut paths = BTreeMap::from([(1, vec![])]);
        let history: Vec<_> = plan.decompositions().cloned().collect();
        let mut methods = Vec::new();
        for d in history.iter().rev() {
            let path = paths[&d.parent.id].clone();
            methods.push((path.clone(), d.method));
            for (slot, child) in d.children.iter().enumerate() {
                let mut child_path = path.clone();
                child_path.push(slot);
                paths.insert(child.id, child_path);
            }
        }
        methods.sort();
        let leaves: Vec<_> = plan.tasks().copied().collect();
        for order in permutations(leaves.len()) {
            if order.iter().enumerate().any(|(i, &a)| {
                order[i + 1..]
                    .iter()
                    .any(|&b| plan.ordered_before(leaves[b].id, leaves[a].id))
            }) {
                continue;
            }
            assert!(executes(p, order.iter().map(|&i| leaves[i].task)));
            let certificate = Certificate {
                root: 1,
                steps: order.iter().map(|&i| leaves[i]).collect(),
                decompositions: history.clone(),
            };
            assert_eq!(validate::validate(p, &certificate).unwrap(), plan.cost());
            let witness = Witness {
                methods: methods.clone(),
                execution: order
                    .iter()
                    .map(|&i| paths[&leaves[i].id].clone())
                    .collect(),
            };
            *result.entry(witness).or_insert(0) += 1;
        }
    }
    (result, visited)
}

fn check(p: &Problem) -> (usize, usize) {
    let expected = oracle(p);
    let (actual, nodes) = enumerate(p, FlawSelection::Systematic);
    assert_eq!(actual.keys().cloned().collect::<HashSet<_>>(), expected);
    assert!(
        actual.values().all(|&n| n == 1),
        "duplicate witnesses: {actual:?}"
    );
    (expected.len(), nodes)
}

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
    let n = actions.len() + compounds;
    let tasks = (0..n)
        .map(|id| Task {
            name: format!("t{id}"),
            primitive: id < actions.len(),
        })
        .collect();
    Problem::new(
        vec!["p".into(), "q".into()],
        actions,
        tasks,
        methods,
        initial.into(),
        goal.into(),
        n - 1,
    )
    .unwrap()
}

#[test]
fn subtree_commitments_remove_redundant_decomposition_paths() {
    let p = problem(
        vec![action(1, &[], &[0], &[])],
        3,
        vec![
            method(1, &[0], &[]),
            method(2, &[0], &[]),
            method(3, &[1, 2], &[]),
        ],
        &[],
        &[0],
    );
    let (witnesses, nodes) = check(&p);
    let (baseline, baseline_nodes) = enumerate(&p, FlawSelection::Interleaved);
    assert_eq!(witnesses, 2);
    assert!(baseline.values().any(|&n| n > 1));
    assert!(nodes < baseline_nodes);
    eprintln!("two achiever subtrees: {baseline_nodes} -> {nodes} nodes; {} -> {witnesses} witness visits", baseline.values().sum::<usize>());
}

#[test]
fn initial_and_positive_supporters_partition_execution_orders() {
    let p = problem(
        vec![action(1, &[], &[0], &[]), action(1, &[0], &[], &[])],
        2,
        vec![method(2, &[0], &[]), method(3, &[0, 2, 1], &[])],
        &[0],
        &[],
    );
    let (witnesses, _) = check(&p);
    assert_eq!(witnesses, 6);
    let (baseline, _) = enumerate(&p, FlawSelection::Interleaved);
    assert!(baseline.values().any(|&n| n > 1));
}

#[test]
fn focused_supporter_can_get_its_own_preconditions_from_another_subtree() {
    let p = problem(
        vec![action(1, &[1], &[0], &[]), action(1, &[], &[1], &[])],
        3,
        vec![
            method(2, &[0], &[]),
            method(3, &[1], &[]),
            method(4, &[2, 3], &[]),
        ],
        &[],
        &[0],
    );
    assert_eq!(check(&p).0, 1);
}

#[test]
fn empty_tasks_and_identical_methods_keep_distinct_hierarchy_witnesses() {
    let p = problem(
        vec![action(0, &[], &[0], &[]), action(2, &[0], &[], &[])],
        2,
        vec![
            method(2, &[], &[]),
            method(2, &[], &[]),
            method(3, &[0, 2, 1], &[(0, 1), (1, 2)]),
        ],
        &[],
        &[],
    );
    assert_eq!(check(&p).0, 2);
}

#[test]
fn systematic_refinement_covers_each_finite_witness_once() {
    let mut witnesses = 0;
    for code in 0..128 {
        let actions = (0..3)
            .map(|i| {
                let pre = if code & (1 << i) == 0 {
                    vec![]
                } else {
                    vec![i % 2]
                };
                let add = vec![(i + 1) % 2];
                let del = if code & (8 << i) == 0 {
                    vec![]
                } else {
                    vec![i % 2]
                };
                action(i as u64, &pre, &add, &del)
            })
            .collect();
        let initial = if code & 64 == 0 { vec![] } else { vec![0, 1] };
        let p = problem(
            actions,
            3,
            vec![
                method(3, &[0, 1], &[(0, 1)]),
                method(3, &[], &[]),
                method(4, &[2], &[]),
                method(4, &[0, 0], &[]),
                method(5, &[3, 4], if code % 3 == 0 { &[(0, 1)] } else { &[] }),
            ],
            &initial,
            &[1],
        );
        witnesses += check(&p).0;
    }
    assert!(witnesses > 100);
    eprintln!("128 finite models: {witnesses} distinct executable hierarchy witnesses, each visited exactly once");
}

#[test]
fn recursive_support_focus_retains_finite_exits_and_astar_costs() {
    // Equal lower bounds leave FIFO ties free to reach the finite exit.
    let p = problem(
        vec![action(3, &[], &[0], &[])],
        1,
        vec![method(1, &[1], &[]), method(1, &[0], &[])],
        &[],
        &[0],
    );
    for strategy in [
        SearchStrategy::BreadthFirst,
        SearchStrategy::AStar,
        SearchStrategy::Greedy,
    ] {
        let result = search(
            &p,
            &Config {
                strategy,
                flaws: FlawSelection::Systematic,
                node_limit: Some(100),
                ..Config::default()
            },
        )
        .unwrap();
        let Outcome::Solved(solution) = result.outcome else {
            panic!(
                "lost finite recursive exit with {strategy:?}: {:?}",
                result.outcome
            )
        };
        assert_eq!(solution.cost, 3);
        assert_eq!(solution.cost_optimal, strategy == SearchStrategy::AStar);
    }
}

#[test]
fn systematicity_does_not_remove_astar_recursive_plateaus() {
    // The empty method makes the structural TDG bound zero even though it
    // cannot achieve the goal. The recursive f=0 branch can starve the f=3 exit.
    let p = problem(
        vec![action(3, &[], &[0], &[])],
        1,
        vec![
            method(1, &[1], &[]),
            method(1, &[], &[]),
            method(1, &[0], &[]),
        ],
        &[],
        &[0],
    );
    let config = Config {
        flaws: FlawSelection::Systematic,
        node_limit: Some(50),
        ..Config::default()
    };
    assert!(matches!(
        search(&p, &config).unwrap().outcome,
        Outcome::Solved(_)
    ));
    assert!(matches!(
        search(
            &p,
            &Config {
                strategy: SearchStrategy::AStar,
                ..config
            }
        )
        .unwrap()
        .outcome,
        Outcome::Stopped(StopReason::NodeLimit)
    ));
}
