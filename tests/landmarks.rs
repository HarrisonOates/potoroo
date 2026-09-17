//! Lifted landmark heuristic regressions.

use std::fs;

use potoroo::heuristics::Heuristic;
use potoroo::landmarks::LiftedLandmarks;
use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::search::{plan_with_stats, Outcome, SearchContext};

struct Run {
    solved: bool,
    cost: usize,
    generated: usize,
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
