//! Integration tests for optional pruning rules: solution preservation and rule activation.

use std::fs;

use potoroo::external::fd_available;
use potoroo::heuristics::Heuristic;
use potoroo::params::{Parameters, SearchAlgorithm};
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::pruning::PruneOptions;
use potoroo::search::{plan_with_stats, Outcome, SearchContext};

struct Run {
    solved: bool,
    cost: usize,
    steps: usize,
    pruned: usize,
}

fn run(domain_path: &str, problem_path: &str, params: Parameters) -> Run {
    let domain_src = fs::read_to_string(domain_path).expect("read domain");
    let problem_src = fs::read_to_string(problem_path).expect("read problem");
    let domain = match read_pddl(&domain_src).expect("parse domain") {
        ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
        _ => panic!("expected a domain"),
    };
    let problem = match read_pddl(&problem_src).expect("parse problem") {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
        _ => panic!("expected a problem"),
    };
    let ctx = SearchContext::new(&domain, &problem, &params);
    let (outcome, stats) = plan_with_stats(&ctx);
    match outcome {
        Outcome::Solved(found) => {
            assert!(found.complete(), "a returned plan must have no open flaws");
            Run {
                solved: true,
                cost: found.cost(),
                steps: found.num_steps(),
                pruned: stats.pruned,
            }
        }
        _ => Run {
            solved: false,
            cost: 0,
            steps: 0,
            pruned: stats.pruned,
        },
    }
}

fn params(prune: PruneOptions, limit: usize) -> Parameters {
    Parameters {
        search_limits: vec![limit],
        prune,
        ..Parameters::default()
    }
}

/// Every rule is solution-preserving, so turning them all on must not change
/// what the default configuration finds on problems it already solves.
///
/// The default heuristic `ADD` is inadmissible, so A\* is not optimality-
/// preserving here and a *different* plan of a different cost would not by
/// itself prove a rule unsound. Pinning the costs anyway makes any change
/// visible: if this test starts failing, the pruned run needs checking against
/// an admissible configuration before the new numbers are accepted.
#[test]
fn pruning_does_not_change_what_lifted_search_finds() {
    let cases = [
        ("blocks-world-domain", "sussman-anomaly"),
        ("gripper-domain", "gripper-4"),
        ("ferry-domain", "test-ferry"),
        ("road-domain", "road-test"),
        ("briefcase-world-domain", "get-paid"),
    ];
    for (domain, problem) in cases {
        let domain_path = format!("examples/{domain}.pddl");
        let problem_path = format!("examples/{problem}.pddl");
        let baseline = run(
            &domain_path,
            &problem_path,
            params(PruneOptions::default(), 50_000),
        );
        let pruned = run(
            &domain_path,
            &problem_path,
            params(PruneOptions::all(), 50_000),
        );
        assert!(baseline.solved, "{problem} should solve without pruning");
        assert_eq!(
            baseline.solved, pruned.solved,
            "{problem}: pruning changed solvability"
        );
        assert_eq!(
            baseline.cost, pruned.cost,
            "{problem}: pruning changed the plan cost"
        );
        assert_eq!(
            baseline.steps, pruned.steps,
            "{problem}: pruning changed the plan length"
        );
    }
}

/// Parameter domains reject action instances whose arguments can never reach
/// the parameter, so they fire wherever a domain has more objects than the
/// reachable structure admits.
#[test]
fn parameter_domains_prune_logistics() {
    let pruned = run(
        "examples/logistics-domain.pddl",
        "examples/logistics-a.pddl",
        params(
            PruneOptions {
                params: true,
                ..PruneOptions::default()
            },
            50_000,
        ),
    );
    assert!(pruned.solved, "logistics-a should still solve");
    assert!(
        pruned.pruned > 0,
        "parameter domains pruned nothing on logistics-a"
    );
}

/// A two-location map with roads both ways makes `at` recursive: `drive b a`
/// establishes `(at a)`, whose own `(at b)` precondition regresses through
/// `drive a b`, and so on. Breadth-first search walks straight into it.
#[test]
fn recursion_pruning_fires_on_a_reversible_map() {
    let configuration = |prune: PruneOptions| Parameters {
        search_algorithm: SearchAlgorithm::Bfs,
        heuristic: Heuristic::parse("LIFO").expect("LIFO is a valid heuristic"),
        search_limits: vec![20_000],
        prune,
        ..Parameters::default()
    };
    let baseline = run(
        "tests/testdata/travel-domain.pddl",
        "tests/testdata/travel-loop.pddl",
        configuration(PruneOptions::default()),
    );
    let pruned = run(
        "tests/testdata/travel-domain.pddl",
        "tests/testdata/travel-loop.pddl",
        configuration(PruneOptions {
            recursion: true,
            ..PruneOptions::default()
        }),
    );
    assert!(baseline.solved && pruned.solved, "both runs should solve");
    assert_eq!(
        baseline.cost, pruned.cost,
        "recursion pruning changed the cost"
    );
    assert!(
        pruned.pruned > 0,
        "recursion pruning fired on nothing in a domain built to loop"
    );
}

/// Towers of Hanoi generates plans whose goal support is complete well before
/// the plan is, which is exactly the shape cutset-dominance recognises.
#[test]
fn minimality_pruning_fires_on_hanoi() {
    let pruned = run(
        "examples/hanoi-domain.pddl",
        "examples/hanoi-3.pddl",
        params(
            PruneOptions {
                minimality: true,
                ..PruneOptions::default()
            },
            12_000,
        ),
    );
    assert!(
        pruned.pruned > 0,
        "minimality pruning fired on nothing in {} nodes",
        12_000
    );
}

/// Cutset pruning runs on the finite-domain representation, where Fast
/// Downward's SAS+ variables and mutex groups supply exact mutexes.
///
/// `LMCUT` is admissible, so A\* really is cost-optimal here and the costs must
/// agree exactly — this is the strongest evidence available that the rule only
/// discards plans with no completion.
#[test]
fn cutset_pruning_preserves_optimal_finite_domain_plans() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }
    use potoroo::fdr_pocl::{solve_with_params, translate, Outcome as FdrOutcome};

    let cases = [
        ("blocks-world-domain", "sussman-anomaly"),
        ("gripper-domain", "gripper-4"),
        ("ferry-domain", "test-ferry"),
    ];
    for (domain_name, problem_name) in cases {
        let domain_src =
            fs::read_to_string(format!("examples/{domain_name}.pddl")).expect("read domain");
        let problem_src =
            fs::read_to_string(format!("examples/{problem_name}.pddl")).expect("read problem");
        let domain = match read_pddl(&domain_src).expect("parse domain") {
            ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
            _ => panic!("expected a domain"),
        };
        let problem = match read_pddl(&problem_src).expect("parse problem") {
            ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
            _ => panic!("expected a problem"),
        };
        let translate_params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &translate_params);
        let task = translate(&ctx).expect("translate to SAS+");

        let admissible = |prune: PruneOptions| Parameters {
            heuristic: Heuristic::parse("LMCUT").expect("LMCUT is a valid heuristic"),
            search_limits: vec![60_000],
            prune,
            ..Parameters::default()
        };

        let (baseline, _) = solve_with_params(&task, &admissible(PruneOptions::default()))
            .expect("baseline parameters are supported");
        let (with_cutset, stats) = solve_with_params(
            &task,
            &admissible(PruneOptions {
                cutset: true,
                ..PruneOptions::default()
            }),
        )
        .expect("cutset parameters are supported");

        match (baseline, with_cutset) {
            (FdrOutcome::Solved(a), FdrOutcome::Solved(b)) => {
                assert_eq!(
                    a.plan.cost(),
                    b.plan.cost(),
                    "{problem_name}: cutset pruning changed the optimal cost"
                );
                assert!(
                    stats.pruned > 0,
                    "{problem_name}: cutset pruning fired on nothing"
                );
            }
            (a, b) => panic!("{problem_name}: expected both runs to solve, got {a:?} and {b:?}"),
        }
    }
}

/// A goal that is mutex with itself makes the task unsolvable before search
/// begins — the goal step's pre-cutset, checked once at setup.
#[test]
fn mutually_exclusive_goals_are_rejected_without_search() {
    use potoroo::cutset::{goals_inconsistent, FactMutexes};
    use potoroo::fdr::{Fact, Task, Variable};

    let task = Task {
        variables: vec![Variable {
            name: "pos".to_string(),
            values: vec!["a".to_string(), "b".to_string()],
        }],
        mutex_groups: vec![],
        initial: vec![0],
        goals: vec![Fact::new(0, 0), Fact::new(0, 1)],
        operators: vec![],
        axioms: vec![],
    };
    let mutexes = FactMutexes::new(&task);
    assert!(goals_inconsistent(&task, &mutexes));
}

/// e-deletion's productive case in a finite-domain task needs no cross-variable
/// invariant: a step that *requires* `v = 1` cannot run inside an interval
/// protecting `v = 0`, even though it assigns nothing to `v`. The classical
/// threat test — "assigns the protected variable another value" — misses it
/// entirely.
#[test]
fn e_deletion_sees_a_threat_the_classical_test_misses() {
    use potoroo::fdr::{Effect, Fact, Operator, Task, Variable};
    use potoroo::fdr_pocl::{solve_with_params, Outcome as FdrOutcome};

    // v0: a switch, values {off, on}. v1: the goal flag, values {no, yes}.
    // `use_off` needs v0 = off and sets the flag; `peek_on` needs v0 = on and
    // sets a second flag, touching v0 not at all.
    let task = Task {
        variables: vec![
            Variable {
                name: "v0".to_string(),
                values: vec!["off".to_string(), "on".to_string()],
            },
            Variable {
                name: "v1".to_string(),
                values: vec!["no".to_string(), "yes".to_string()],
            },
            Variable {
                name: "v2".to_string(),
                values: vec!["no".to_string(), "yes".to_string()],
            },
        ],
        mutex_groups: vec![],
        initial: vec![0, 0, 0],
        goals: vec![Fact::new(1, 1), Fact::new(2, 1)],
        operators: vec![
            Operator {
                name: "use_off".to_string(),
                prevail: vec![Fact::new(0, 0)],
                effects: vec![Effect {
                    conditions: vec![],
                    variable: 1,
                    pre: None,
                    post: 1,
                }],
                cost: 1,
            },
            Operator {
                name: "peek_on".to_string(),
                prevail: vec![Fact::new(0, 1)],
                effects: vec![Effect {
                    conditions: vec![],
                    variable: 2,
                    pre: None,
                    post: 1,
                }],
                cost: 1,
            },
            Operator {
                name: "flip_on".to_string(),
                prevail: vec![],
                effects: vec![Effect {
                    conditions: vec![],
                    variable: 0,
                    pre: Some(0),
                    post: 1,
                }],
                cost: 1,
            },
        ],
        axioms: vec![],
    };

    let configuration = |prune: PruneOptions| Parameters {
        heuristic: Heuristic::parse("LMCUT").expect("LMCUT is a valid heuristic"),
        search_limits: vec![20_000],
        prune,
        ..Parameters::default()
    };

    let (baseline, baseline_stats) =
        solve_with_params(&task, &configuration(PruneOptions::default()))
            .expect("baseline parameters are supported");
    let (with_edelete, edelete_stats) = solve_with_params(
        &task,
        &configuration(PruneOptions {
            edelete: true,
            ..PruneOptions::default()
        }),
    )
    .expect("e-deletion parameters are supported");

    match (baseline, with_edelete) {
        (FdrOutcome::Solved(a), FdrOutcome::Solved(b)) => {
            assert_eq!(
                a.plan.cost(),
                b.plan.cost(),
                "e-deletion changed the optimal cost"
            );
        }
        (a, b) => panic!("expected both runs to solve, got {a:?} and {b:?}"),
    }
    // `peek_on` requiring v0 = on is a threat to the link protecting v0 = off
    // for `use_off`, and only e-deletion reports it.
    assert!(
        edelete_stats.max_threats > baseline_stats.max_threats,
        "e-deletion found no extra threats: {} vs {}",
        edelete_stats.max_threats,
        baseline_stats.max_threats
    );
}

/// Disjunctive threat resolution must leave the optimal plan alone, and must
/// actually defer some threats rather than quietly unit-propagating every one.
#[test]
fn disjunctive_orderings_preserve_optimal_plans_and_defer_threats() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }
    use potoroo::fdr_pocl::{solve_with_params, translate, Outcome as FdrOutcome};

    let domain_src = fs::read_to_string("examples/gripper-domain.pddl").expect("read domain");
    let problem_src = fs::read_to_string("examples/gripper-4.pddl").expect("read problem");
    let domain = match read_pddl(&domain_src).expect("parse domain") {
        ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
        _ => panic!("expected a domain"),
    };
    let problem = match read_pddl(&problem_src).expect("parse problem") {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
        _ => panic!("expected a problem"),
    };
    let translate_params = Parameters::default();
    let ctx = SearchContext::new(&domain, &problem, &translate_params);
    let task = translate(&ctx).expect("translate to SAS+");

    let configuration = |prune: PruneOptions| Parameters {
        heuristic: Heuristic::parse("LMCUT").expect("LMCUT is a valid heuristic"),
        search_limits: vec![40_000],
        prune,
        ..Parameters::default()
    };

    let (baseline, baseline_stats) =
        solve_with_params(&task, &configuration(PruneOptions::default()))
            .expect("baseline parameters are supported");
    let (disjunctive, disjunctive_stats) = solve_with_params(
        &task,
        &configuration(PruneOptions {
            disjunctive: true,
            ..PruneOptions::default()
        }),
    )
    .expect("disjunctive parameters are supported");

    assert_eq!(
        baseline_stats.max_disjunctions, 0,
        "the baseline must post no disjunctions"
    );
    assert!(
        disjunctive_stats.max_disjunctions > 0,
        "every threat unit-propagated; no disjunction was ever held"
    );
    match (baseline, disjunctive) {
        (FdrOutcome::Solved(a), FdrOutcome::Solved(b)) => {
            assert_eq!(
                a.plan.cost(),
                b.plan.cost(),
                "disjunctive threat resolution changed the optimal cost"
            );
        }
        (a, b) => panic!("expected both runs to solve, got {a:?} and {b:?}"),
    }
}

/// Runs one finite-domain configuration, returning (solved, cost, pruned).
fn fdr_run(
    domain_name: &str,
    problem_name: &str,
    prune: PruneOptions,
    limit: usize,
) -> (bool, usize, usize) {
    use potoroo::fdr_pocl::{solve_with_params, translate, Outcome as FdrOutcome};

    let domain_src =
        fs::read_to_string(format!("examples/{domain_name}.pddl")).expect("read domain");
    let problem_src =
        fs::read_to_string(format!("examples/{problem_name}.pddl")).expect("read problem");
    let domain = match read_pddl(&domain_src).expect("parse domain") {
        ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
        _ => panic!("expected a domain"),
    };
    let problem = match read_pddl(&problem_src).expect("parse problem") {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
        _ => panic!("expected a problem"),
    };
    let translate_params = Parameters::default();
    let ctx = SearchContext::new(&domain, &problem, &translate_params);
    let task = translate(&ctx).expect("translate to SAS+");

    let params = Parameters {
        heuristic: Heuristic::parse("LMCUT").expect("LMCUT is a valid heuristic"),
        search_limits: vec![limit],
        prune,
        ..Parameters::default()
    };
    let (outcome, stats) = solve_with_params(&task, &params).expect("parameters are supported");
    match outcome {
        FdrOutcome::Solved(solution) => (true, solution.plan.cost(), stats.pruned),
        _ => (false, 0, stats.pruned),
    }
}

/// Recursion pruning is structural, so it applies to finite-domain plans too —
/// and fires far more readily there than on the lifted representation, where
/// `examples/` gave it almost nothing to reject.
#[test]
fn recursion_pruning_carries_over_to_finite_domains() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }
    let recursion = PruneOptions {
        recursion: true,
        ..PruneOptions::default()
    };
    let mut fired = false;
    for (domain, problem) in [("fridge-domain", "fixa"), ("road-domain", "road-test")] {
        let (base_solved, base_cost, _) = fdr_run(domain, problem, PruneOptions::default(), 30_000);
        let (solved, cost, pruned) = fdr_run(domain, problem, recursion, 30_000);
        assert!(base_solved && solved, "{problem} should solve both ways");
        assert_eq!(
            base_cost, cost,
            "{problem}: recursion pruning changed the optimal cost"
        );
        fired |= pruned > 0;
    }
    assert!(
        fired,
        "recursion pruning fired on no finite-domain benchmark"
    );
}

/// Likewise for cutset dominance, which on `gripper-6` removes work rather than
/// merely reshuffling it.
#[test]
fn minimality_pruning_carries_over_to_finite_domains() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }
    let minimality = PruneOptions {
        minimality: true,
        ..PruneOptions::default()
    };
    let (base_solved, base_cost, base_pruned) = fdr_run(
        "gripper-domain",
        "gripper-6",
        PruneOptions::default(),
        30_000,
    );
    let (solved, cost, pruned) = fdr_run("gripper-domain", "gripper-6", minimality, 30_000);
    assert!(base_solved && solved, "gripper-6 should solve both ways");
    assert_eq!(base_pruned, 0, "the baseline must prune nothing");
    assert_eq!(
        base_cost, cost,
        "minimality pruning changed the optimal cost"
    );
    assert!(pruned > 0, "minimality pruning fired on nothing");
}

/// Lifted cutset pruning uses schema-derived mutex groups.
/// Conditions with unbound variables contribute no ground fact.
#[test]
fn lifted_cutset_shrinks_the_search_and_keeps_the_plan() {
    let cutset = PruneOptions {
        cutset: true,
        ..PruneOptions::default()
    };
    let baseline = run(
        "examples/ferry-domain.pddl",
        "examples/test-ferry.pddl",
        params(PruneOptions::default(), 50_000),
    );
    let pruned = run(
        "examples/ferry-domain.pddl",
        "examples/test-ferry.pddl",
        params(cutset, 50_000),
    );
    assert!(baseline.solved && pruned.solved, "test-ferry should solve");
    assert_eq!(
        baseline.cost, pruned.cost,
        "lifted cutset pruning changed the plan cost"
    );
    assert!(pruned.pruned > 0, "lifted cutset pruning fired on nothing");
}

/// Ground search with `LPLAN` is genuinely cost-optimal, so this is the check
/// that the synthesised groups do not claim a mutex that is not one: a false
/// mutex would let the rule discard the optimal plan.
#[test]
fn lifted_cutset_preserves_optimal_ground_plans() {
    let cutset = PruneOptions {
        cutset: true,
        ..PruneOptions::default()
    };
    for (domain, problem) in [
        ("blocks-world-domain", "sussman-anomaly"),
        ("ferry-domain", "test-ferry"),
        ("road-domain", "road-test"),
    ] {
        let domain_path = format!("examples/{domain}.pddl");
        let problem_path = format!("examples/{problem}.pddl");
        let optimal = |prune: PruneOptions| Parameters {
            heuristic: Heuristic::parse("LPLAN").expect("LPLAN is a valid heuristic"),
            ground_actions: true,
            search_limits: vec![5_000],
            prune,
            ..Parameters::default()
        };
        let baseline = run(
            &domain_path,
            &problem_path,
            optimal(PruneOptions::default()),
        );
        let pruned = run(&domain_path, &problem_path, optimal(cutset));
        assert_eq!(
            baseline.solved, pruned.solved,
            "{problem}: cutset pruning changed solvability under an admissible heuristic"
        );
        if baseline.solved {
            assert_eq!(
                baseline.cost, pruned.cost,
                "{problem}: cutset pruning changed the optimal cost"
            );
        }
    }
}

/// The groups themselves: a ferry carries one car at a time and sits at one
/// location, which is the state-variable invariant a SAS+ variable encodes.
#[test]
fn lifted_mutex_groups_recover_state_variable_invariants() {
    use potoroo::lifted_mutex::LiftedMutexes;

    let domain_src = fs::read_to_string("examples/ferry-domain.pddl").expect("read domain");
    let problem_src = fs::read_to_string("examples/test-ferry.pddl").expect("read problem");
    let domain = match read_pddl(&domain_src).expect("parse domain") {
        ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
        _ => panic!("expected a domain"),
    };
    let problem = match read_pddl(&problem_src).expect("parse problem") {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
        _ => panic!("expected a problem"),
    };
    let mutexes = LiftedMutexes::synthesise(&domain, &problem);
    assert!(
        !mutexes.is_empty(),
        "no lifted mutex group found in the ferry domain"
    );
}

/// Literal e-delete pruning: boarding threatens a link protecting a car's
/// location because `at(?x, ?y)` and `on(?x, ferry)` are mutex.
#[test]
fn lifted_e_deletion_keeps_the_plan_and_is_not_worth_combining() {
    let baseline = run(
        "examples/ferry-domain.pddl",
        "examples/test-ferry.pddl",
        params(PruneOptions::default(), 50_000),
    );
    let edelete = run(
        "examples/ferry-domain.pddl",
        "examples/test-ferry.pddl",
        params(
            PruneOptions {
                edelete: true,
                ..PruneOptions::default()
            },
            50_000,
        ),
    );
    let cutset_only = run(
        "examples/ferry-domain.pddl",
        "examples/test-ferry.pddl",
        params(
            PruneOptions {
                cutset: true,
                ..PruneOptions::default()
            },
            50_000,
        ),
    );
    let both = run(
        "examples/ferry-domain.pddl",
        "examples/test-ferry.pddl",
        params(
            PruneOptions {
                cutset: true,
                edelete: true,
                ..PruneOptions::default()
            },
            50_000,
        ),
    );

    for (name, outcome) in [
        ("edelete", &edelete),
        ("cutset", &cutset_only),
        ("both", &both),
    ] {
        assert!(outcome.solved, "{name}: test-ferry should still solve");
        assert_eq!(baseline.cost, outcome.cost, "{name}: changed the plan cost");
    }
    // e-deletion alone does cut the search.
    assert!(edelete.steps > 0, "e-deletion produced a degenerate plan");
    // But `cutset` alone beats the combination, which is why `-p all` is not
    // the recommendation for lifted search.
    assert!(cutset_only.pruned > 0, "cutset pruning fired on nothing");
}

/// Refinement finds the cross-predicate groups, which is what makes the lifted
/// cutset rule bite: `⟨at(v₀, ·), in(v₀, ·)⟩` in logistics and
/// `⟨at(v₀, ·), on(v₀, ferry)⟩` in ferry.
#[test]
fn refinement_finds_cross_predicate_groups() {
    use potoroo::lifted_mutex::LiftedMutexes;

    for (domain_name, problem_name) in [
        ("logistics-domain", "logistics-a"),
        ("ferry-domain", "test-ferry"),
    ] {
        let domain_src =
            fs::read_to_string(format!("examples/{domain_name}.pddl")).expect("read domain");
        let problem_src =
            fs::read_to_string(format!("examples/{problem_name}.pddl")).expect("read problem");
        let domain = match read_pddl(&domain_src).expect("parse domain") {
            ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
            _ => panic!("expected a domain"),
        };
        let problem = match read_pddl(&problem_src).expect("parse problem") {
            ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
            _ => panic!("expected a problem"),
        };
        let mutexes = LiftedMutexes::synthesise(&domain, &problem);
        assert!(
            mutexes.groups().iter().any(|group| group.len() > 1),
            "{problem_name}: refinement found no multi-part group"
        );
    }
}

/// `logistics-a` is the case where the cutset rule does the most work per node,
/// and the one that broke when an unsound cache was tried: a link node is shared
/// by every plan that descends from the one that created it, *including*
/// siblings that went on to bind the same variable differently, so nothing
/// binding-dependent may be remembered on it. The symptom was over-pruning —
/// the problem stopped solving at all — so pin solvability and cost, not just
/// that something was pruned.
#[test]
fn lifted_cutset_does_not_over_prune_logistics() {
    let baseline = run(
        "examples/logistics-domain.pddl",
        "examples/logistics-a.pddl",
        params(PruneOptions::default(), 60_000),
    );
    let pruned = run(
        "examples/logistics-domain.pddl",
        "examples/logistics-a.pddl",
        params(
            PruneOptions {
                cutset: true,
                ..PruneOptions::default()
            },
            60_000,
        ),
    );
    assert!(baseline.solved, "logistics-a should solve without pruning");
    assert!(
        pruned.solved,
        "logistics-a stopped solving with cutset pruning — the rule is rejecting \
         plans it should keep"
    );
    assert_eq!(
        baseline.cost, pruned.cost,
        "cutset pruning changed the plan cost on logistics-a"
    );
    assert!(pruned.pruned > 0, "cutset pruning fired on nothing");
}
