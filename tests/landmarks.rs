//! Lifted landmark heuristic regressions.

use std::fs;

use potoroo::heuristics::Heuristic;
use potoroo::landmarks::LiftedLandmarks;
use potoroo::lifted_mutex::LiftedMutexes;
use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::search::{plan_with_stats, Outcome, SearchContext};

struct Run {
    solved: bool,
    cost: usize,
    generated: usize,
}

fn task(
    domain_file: &str,
    problem_file: &str,
) -> (potoroo::domain::Domain, potoroo::problem::Problem) {
    let domain_src = fs::read_to_string(format!("examples/{domain_file}")).expect("read domain");
    let problem_src = fs::read_to_string(format!("examples/{problem_file}")).expect("read problem");
    let domain = match read_pddl(&domain_src).expect("parse domain") {
        ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
        _ => panic!("expected a domain"),
    };
    let problem = match read_pddl(&problem_src).expect("parse problem") {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
        _ => panic!("expected a problem"),
    };
    (domain, problem)
}

fn run(domain_file: &str, problem_file: &str, heuristic: &str, limit: usize) -> Run {
    let domain_src = fs::read_to_string(format!("examples/{domain_file}")).expect("read domain");
    let problem_src = fs::read_to_string(format!("examples/{problem_file}")).expect("read problem");
    let domain = match read_pddl(&domain_src).expect("parse domain") {
        ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
        _ => panic!("expected a domain"),
    };
    let problem = match read_pddl(&problem_src).expect("parse problem") {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
        _ => panic!("expected a problem"),
    };
    let params = Parameters {
        heuristic: Heuristic::parse(heuristic).expect("valid heuristic"),
        search_limits: vec![limit],
        ..Parameters::default()
    };
    let ctx = SearchContext::new(&domain, &problem, &params);
    let (outcome, stats) = plan_with_stats(&ctx);
    match outcome {
        Outcome::Solved(found) => {
            assert!(found.complete(), "a returned plan must have no open flaws");
            Run {
                solved: true,
                cost: found.cost(),
                generated: stats.nodes_generated,
            }
        }
        _ => Run {
            solved: false,
            cost: 0,
            generated: stats.nodes_generated,
        },
    }
}

/// The point of the whole exercise: a problem the delete-relaxation heuristics
/// cannot solve, and landmarks can.
#[test]
fn landmarks_solve_a_problem_delete_relaxation_cannot() {
    let limit = 20_000;
    let add = run("flat-tire-domain.pddl", "fixit.pddl", "ADD", limit);
    let relax = run("flat-tire-domain.pddl", "fixit.pddl", "RELAX", limit);
    let landmarks = run("flat-tire-domain.pddl", "fixit.pddl", "LM", limit);

    assert!(!add.solved, "ADD unexpectedly solved fixit within {limit}");
    assert!(
        !relax.solved,
        "RELAX unexpectedly solved fixit within {limit}"
    );
    assert!(
        landmarks.solved,
        "the landmark heuristic no longer solves fixit"
    );
    assert!(
        landmarks.generated < add.generated,
        "landmarks generated {} nodes, no better than ADD's {}",
        landmarks.generated,
        add.generated
    );
}

/// ADD with landmark tiebreaking on the ferry fixture.
#[test]
fn landmarks_sharpen_add_on_ferry() {
    let add = run("ferry-domain.pddl", "test-ferry.pddl", "ADD", 20_000);
    let composed = run("ferry-domain.pddl", "test-ferry.pddl", "ADD/LM", 20_000);
    assert!(add.solved && composed.solved);
    assert_eq!(add.cost, composed.cost, "composition changed the plan cost");
    assert!(
        composed.generated < add.generated,
        "ADD/LM generated {} nodes against ADD's {}",
        composed.generated,
        add.generated
    );
}

/// Extraction must find something to count on every domain it is offered, or
/// the heuristic silently degenerates to plain `g`.
#[test]
fn extraction_finds_landmarks_on_every_example_domain() {
    for (domain_file, problem_file) in [
        ("blocks-world-domain.pddl", "sussman-anomaly.pddl"),
        ("ferry-domain.pddl", "test-ferry.pddl"),
        ("gripper-domain.pddl", "gripper-6.pddl"),
        ("logistics-domain.pddl", "logistics-a.pddl"),
        ("flat-tire-domain.pddl", "fixit.pddl"),
    ] {
        let domain_src =
            fs::read_to_string(format!("examples/{domain_file}")).expect("read domain");
        let problem_src =
            fs::read_to_string(format!("examples/{problem_file}")).expect("read problem");
        let domain = match read_pddl(&domain_src).expect("parse domain") {
            ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
            _ => panic!("expected a domain"),
        };
        let problem = match read_pddl(&problem_src).expect("parse problem") {
            ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
            _ => panic!("expected a problem"),
        };
        let landmarks = LiftedLandmarks::extract(&domain, &problem);
        assert!(
            !landmarks.is_empty(),
            "{problem_file}: no landmarks extracted"
        );
    }
}

/// Soundness, pinned end to end: a landmark claimed of a task must hold of
/// every solution to it, so a complete plan leaves nothing outstanding. This is
/// the assertion that would break first if a FAM cut were taken across a
/// transition the graph is missing.
#[test]
fn a_solution_achieves_every_landmark() {
    for (domain_file, problem_file) in [
        ("ferry-domain.pddl", "test-ferry.pddl"),
        ("gripper-domain.pddl", "gripper-4.pddl"),
        ("blocks-world-domain.pddl", "sussman-anomaly.pddl"),
        ("logistics-domain.pddl", "logistics-a.pddl"),
    ] {
        let (domain, problem) = task(domain_file, problem_file);
        let mutexes = LiftedMutexes::synthesise(&domain, &problem);
        let landmarks = LiftedLandmarks::extract_with_mutexes(&domain, &problem, &mutexes);
        assert!(
            !landmarks.actions().is_empty(),
            "{problem_file}: the FAM cuts found nothing"
        );

        let params = Parameters {
            heuristic: Heuristic::parse("ADD").expect("valid heuristic"),
            search_limits: vec![200_000],
            ..Parameters::default()
        };
        let ctx = SearchContext::new(&domain, &problem, &params);
        let Outcome::Solved(plan) = plan_with_stats(&ctx).0 else {
            panic!("{problem_file}: ADD no longer solves this");
        };
        assert_eq!(
            landmarks.count(&plan, false),
            0,
            "{problem_file}: a solution left landmarks outstanding"
        );
        assert_eq!(
            landmarks.count(&plan, true),
            0,
            "{problem_file}: the orderings claimed a landmark of a solution"
        );
    }
}

/// What the cuts buy over backchaining: an argument backchaining has to leave
/// free. Every ferry car must board *at its own starting location*, which no
/// intersection of preconditions can say, because the location only shows up
/// once the group's transition graph is traced from that car's initial value.
#[test]
fn a_cut_pins_an_argument_backchaining_leaves_free() {
    let (domain, problem) = task("ferry-domain.pddl", "test-ferry.pddl");
    let mutexes = LiftedMutexes::synthesise(&domain, &problem);
    let landmarks = LiftedLandmarks::extract_with_mutexes(&domain, &problem, &mutexes);
    let pinned = landmarks.actions().iter().any(|cut| {
        cut.alternatives.iter().all(|action| {
            action.name == "board" && action.args.iter().all(|argument| argument.is_some())
        })
    });
    assert!(
        pinned,
        "no fully pinned `board` landmark among {:?}",
        landmarks.actions()
    );
}

/// The cuts must add to what backchaining alone counts, or `LMF` is `LM` with
/// an extra mutex synthesis for nothing.
#[test]
fn the_cuts_add_to_the_count() {
    let (domain, problem) = task("gripper-domain.pddl", "gripper-4.pddl");
    let mutexes = LiftedMutexes::synthesise(&domain, &problem);
    let plain = LiftedLandmarks::extract(&domain, &problem);
    let with_cuts = LiftedLandmarks::extract_with_mutexes(&domain, &problem, &mutexes);
    assert!(
        with_cuts.len() >= plain.len() && !with_cuts.actions().is_empty(),
        "the cuts contributed nothing: {} facts and {} cuts against {} facts",
        with_cuts.len(),
        with_cuts.actions().len(),
        plain.len()
    );
}
