use potoroo::heuristics::Heuristic;
use potoroo::params::{Parameters, SearchAlgorithm};
use potoroo::parser::{bind_action_costs, lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::search::{plan, Outcome, SearchContext};

fn solve(domain: &str, problem: &str, params: Parameters) -> Outcome {
    let ParsedUnit::Domain(d) = read_pddl(domain).unwrap() else {
        panic!("domain")
    };
    let mut domain = lower_domain(&d).unwrap();
    let ParsedUnit::Problem(p) = read_pddl(problem).unwrap() else {
        panic!("problem")
    };
    let problem = lower_problem(&p, &domain).unwrap();
    bind_action_costs(&mut domain, &problem).unwrap();
    plan(&SearchContext::new(&domain, &problem, &params))
}

fn params() -> Parameters {
    Parameters {
        heuristic: Heuristic::parse("UCPOP").unwrap(),
        search_limits: vec![2_000],
        ..Parameters::default()
    }
}

#[test]
fn external_evaluator_failure_does_not_report_a_solvable_problem_unsolvable() {
    let output = std::process::Command::new(assert_cmd::cargo::cargo_bin!("potoroo"))
        .args([
            "-h",
            "COMPILE_LMCUT",
            "-l",
            "10000",
            "examples/gripper-domain.pddl",
            "examples/gripper-2.pddl",
        ])
        .env("POTOROO_FD", "/potoroo-review-missing/fast-downward.py")
        .output()
        .unwrap();
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(!stdout.contains("no plan"), "{stdout}\n{stderr}");
    assert_eq!(stderr.matches("using h=0").count(), 1);
}

#[test]
fn cli_rejects_nonfinite_and_negative_weights() {
    for weight in ["NaN", "inf", "-1"] {
        let output = std::process::Command::new(assert_cmd::cargo::cargo_bin!("potoroo"))
            .args([
                "-w",
                weight,
                "examples/gripper-domain.pddl",
                "examples/gripper-2.pddl",
            ])
            .output()
            .unwrap();
        assert!(!output.status.success(), "accepted weight {weight}");
        assert!(String::from_utf8(output.stderr)
            .unwrap()
            .contains("invalid weight"));
    }
}

const QUANT_DOMAIN: &str = "(define (domain quant)
    (:requirements :adl :typing) (:types item other)
    (:predicates (p ?x - item) (pair ?x - item ?y - item)))";

#[test]
fn existential_goal_requires_an_object_of_its_type() {
    let result = solve(
        QUANT_DOMAIN,
        "(define (problem p) (:domain quant)
        (:objects o - other) (:init)
        (:goal (exists (?x - item) (= ?x ?x))))",
        params(),
    );
    assert!(matches!(result, Outcome::NoSolution));
}

#[test]
fn existential_inequalities_need_a_jointly_consistent_witness() {
    let result = solve(
        QUANT_DOMAIN,
        "(define (problem p) (:domain quant)
        (:objects a - item) (:init)
        (:goal (exists (?x ?y - item) (not (= ?x ?y)))))",
        params(),
    );
    assert!(matches!(result, Outcome::NoSolution));
}

#[test]
fn universal_expansion_preserves_a_false_body() {
    let result = solve(
        QUANT_DOMAIN,
        "(define (problem p) (:domain quant)
        (:objects a - item) (:init)
        (:goal (forall (?x - item) (or))))",
        params(),
    );
    assert!(matches!(result, Outcome::NoSolution));
}

#[test]
fn universal_instances_have_independent_existential_witnesses() {
    let result = solve(
        QUANT_DOMAIN,
        "(define (problem p) (:domain quant)
        (:objects a b - item) (:init (pair a a) (pair b b))
        (:goal (forall (?x - item) (exists (?y - item) (pair ?x ?y)))))",
        params(),
    );
    assert!(matches!(result, Outcome::Solved(_)));
}

#[test]
fn grounding_preserves_the_types_of_quantified_variables() {
    let domain = "(define (domain quant) (:requirements :adl :typing)
        (:types item other) (:predicates (p ?x - item) (done))
        (:action finish :parameters () :precondition (forall (?x - item) (p ?x))
            :effect (done)))";
    let problem = "(define (problem p) (:domain quant)
        (:objects a - item b - other) (:init (p a)) (:goal (done)))";
    let result = solve(
        domain,
        problem,
        Parameters {
            ground_actions: true,
            ..params()
        },
    );
    assert!(matches!(result, Outcome::Solved(_)));
}

#[test]
fn lifted_costs_choose_the_cheapest_unconstrained_argument() {
    let domain = "(define (domain cost) (:requirements :strips :typing :action-costs)
        (:types item) (:predicates (done))
        (:functions (total-cost) - number (price ?x - item) - number)
        (:action finish :parameters (?x - item) :precondition (and)
            :effect (and (done) (increase (total-cost) (price ?x)))))";
    let problem = "(define (problem p) (:domain cost) (:objects expensive cheap - item)
        (:init (= (total-cost) 0) (= (price expensive) 9) (= (price cheap) 1))
        (:goal (done)) (:metric minimize (total-cost)))";
    let Outcome::Solved(plan) = solve(
        domain,
        problem,
        Parameters {
            heuristic: Heuristic::parse("ADD").unwrap(),
            search_algorithm: SearchAlgorithm::A,
            ..params()
        },
    ) else {
        panic!("solvable task")
    };
    assert_eq!(plan.cost(), 1);
}

#[test]
fn replay_rejects_a_plan_whose_flaw_list_lost_a_goal() {
    let ParsedUnit::Domain(d) = read_pddl(QUANT_DOMAIN).unwrap() else {
        panic!("domain")
    };
    let domain = lower_domain(&d).unwrap();
    let ParsedUnit::Problem(p) = read_pddl(
        "(define (problem p) (:domain quant)
        (:objects a - item) (:init) (:goal (p a)))",
    )
    .unwrap() else {
        panic!("problem")
    };
    let problem = lower_problem(&p, &domain).unwrap();
    let params = params();
    let ctx = SearchContext::new(&domain, &problem, &params);
    let mut broken = potoroo::plan::Plan::make_initial_plan(&ctx).unwrap();
    let plan = std::rc::Rc::get_mut(&mut broken).unwrap();
    plan.open_conds = None;
    plan.num_open_conds = 0;
    assert!(potoroo::validate::is_valid_solution(plan, &ctx).is_err());
}

/// Exhaustive state-space BFS is independent of POCL refinement, heuristics,
/// bindings and causal links. Use it as an oracle on reproducible small tasks
/// containing negative preconditions and conditional effects.
#[test]
fn tiny_tasks_agree_with_exhaustive_state_search() {
    type ConditionalAssignment = (Option<(usize, bool)>, usize, bool);
    #[derive(Clone)]
    struct Op {
        pre: Vec<(usize, bool)>,
        effects: Vec<ConditionalAssignment>,
    }
    fn satisfies(state: usize, literals: &[(usize, bool)]) -> bool {
        literals
            .iter()
            .all(|&(fact, value)| ((state >> fact) & 1 != 0) == value)
    }
    fn literal((fact, value): (usize, bool)) -> String {
        if value {
            format!("(p{fact})")
        } else {
            format!("(not (p{fact}))")
        }
    }
    let mut rng = 17u64;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng as usize
    };
    let mut solved = 0;
    for case in 0..64 {
        let initial = next() % 8;
        let goal = vec![(next() % 3, next() % 2 != 0), (next() % 3, next() % 2 != 0)];
        let mut ops = Vec::new();
        for _ in 0..4 {
            let pre = vec![(next() % 3, next() % 2 != 0)];
            let mut effects = Vec::new();
            for fact in 0..3 {
                if next() % 2 == 0 {
                    let guard = if next() % 3 == 0 {
                        Some((next() % 3, next() % 2 != 0))
                    } else {
                        None
                    };
                    effects.push((guard, fact, next() % 2 != 0));
                }
            }
            ops.push(Op { pre, effects });
        }
        let mut distances = [usize::MAX; 8];
        distances[initial] = 0;
        let mut queue = std::collections::VecDeque::from([initial]);
        let mut optimum = None;
        while let Some(state) = queue.pop_front() {
            if satisfies(state, &goal) {
                optimum = Some(distances[state]);
                break;
            }
            for op in &ops {
                if !satisfies(state, &op.pre) {
                    continue;
                }
                let mut successor = state;
                for &(guard, fact, value) in &op.effects {
                    if guard.is_none_or(|g| satisfies(state, &[g])) {
                        if value {
                            successor |= 1 << fact;
                        } else {
                            successor &= !(1 << fact);
                        }
                    }
                }
                if distances[successor] == usize::MAX {
                    distances[successor] = distances[state] + 1;
                    queue.push_back(successor);
                }
            }
        }
        let mut domain =
            "(define (domain tiny) (:requirements :adl) (:predicates (p0) (p1) (p2))".to_string();
        for (i, op) in ops.iter().enumerate() {
            let pre = op
                .pre
                .iter()
                .copied()
                .map(literal)
                .collect::<Vec<_>>()
                .join(" ");
            let effects = op
                .effects
                .iter()
                .map(|&(guard, fact, value)| {
                    let effect = literal((fact, value));
                    guard.map_or_else(
                        || effect.clone(),
                        |g| format!("(when {} {effect})", literal(g)),
                    )
                })
                .collect::<Vec<_>>()
                .join(" ");
            domain.push_str(&format!(
                "(:action a{i} :parameters () :precondition (and {pre}) :effect (and {effects}))"
            ));
        }
        domain.push(')');
        let init = (0..3)
            .filter(|f| initial & (1 << f) != 0)
            .map(|f| literal((f, true)))
            .collect::<Vec<_>>()
            .join(" ");
        let goals = goal
            .iter()
            .copied()
            .map(literal)
            .collect::<Vec<_>>()
            .join(" ");
        let problem =
            format!("(define (problem p) (:domain tiny) (:init {init}) (:goal (and {goals})))");
        use potoroo::fdr::{Effect, Fact, Operator, Task, Variable};
        let fact = |(variable, value): (usize, bool)| Fact::new(variable, usize::from(value));
        let task = Task {
            variables: (0..3)
                .map(|i| Variable {
                    name: format!("p{i}"),
                    values: vec!["false".into(), "true".into()],
                })
                .collect(),
            mutex_groups: vec![],
            initial: (0..3).map(|f| (initial >> f) & 1).collect(),
            goals: goal.iter().copied().map(fact).collect(),
            operators: ops
                .iter()
                .enumerate()
                .map(|(i, op)| Operator {
                    name: format!("a{i}"),
                    prevail: op.pre.iter().copied().map(fact).collect(),
                    effects: op
                        .effects
                        .iter()
                        .map(|&(guard, variable, value)| Effect {
                            conditions: guard.into_iter().map(fact).collect(),
                            variable,
                            pre: None,
                            post: usize::from(value),
                        })
                        .collect(),
                    cost: 1,
                })
                .collect(),
            axioms: vec![],
        };
        for search_algorithm in [
            SearchAlgorithm::Bfs,
            SearchAlgorithm::LazyGbfs,
            SearchAlgorithm::LazyGbfsDual,
        ] {
            let search_params = Parameters {
                search_algorithm,
                heuristic: Heuristic::parse("ADD").unwrap(),
                search_limits: vec![200],
                ..params()
            };
            let (fdr_outcome, _) =
                potoroo::fdr_pocl::solve_with_params(&task, &search_params).unwrap();
            match fdr_outcome {
                potoroo::fdr_pocl::Outcome::Solved(solution) => {
                    let minimum = optimum
                        .unwrap_or_else(|| panic!("FDR case {case}: solved an impossible task"));
                    if search_algorithm == SearchAlgorithm::Bfs {
                        assert_eq!(solution.plan.num_steps(), minimum, "FDR case {case}");
                    }
                    let mut state = initial;
                    for index in solution.operators {
                        let op = &ops[index];
                        assert!(
                            satisfies(state, &op.pre),
                            "FDR case {case}: inapplicable operator"
                        );
                        let old = state;
                        for &(guard, fact, value) in &op.effects {
                            if guard.is_none_or(|g| satisfies(old, &[g])) {
                                if value {
                                    state |= 1 << fact;
                                } else {
                                    state &= !(1 << fact);
                                }
                            }
                        }
                    }
                    assert!(satisfies(state, &goal), "FDR case {case}: goal not reached");
                }
                potoroo::fdr_pocl::Outcome::NoSolution => {
                    assert!(optimum.is_none(), "FDR case {case}: false dead end")
                }
                potoroo::fdr_pocl::Outcome::LimitReached => {}
            }
            match solve(
                &domain,
                &problem,
                Parameters {
                    search_algorithm,
                    heuristic: Heuristic::parse("ADD").unwrap(),
                    ..params()
                },
            ) {
                Outcome::Solved(plan) => {
                    let minimum =
                        optimum.unwrap_or_else(|| panic!("case {case}: solved an impossible task"));
                    if search_algorithm == SearchAlgorithm::Bfs {
                        assert_eq!(
                            plan.num_steps(),
                            minimum,
                            "case {case}: BFS must minimize steps"
                        );
                    }
                    solved += 1;
                }
                Outcome::NoSolution => assert!(
                    optimum.is_none(),
                    "case {case}: rejected a solvable task ({search_algorithm:?})"
                ),
                Outcome::LimitReached => {}
            }
        }
    }
    assert!(
        solved > 30,
        "exercise successful replay as well as dead ends"
    );
}
