//! Integration test: plan the Sussman anomaly in both lifted and ground modes
//! and compare the formatted plan body against the golden files produced by the
//! reference VHPOP binary.

use std::fs;

use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::search::{format_plan_body, plan, Outcome, SearchContext};

fn solve(ground: bool) -> String {
    let domain_src = fs::read_to_string("examples/blocks-world-domain.pddl")
        .expect("read blocks-world-domain.pddl");
    let problem_src =
        fs::read_to_string("examples/sussman-anomaly.pddl").expect("read sussman-anomaly.pddl");

    let domain = match read_pddl(&domain_src).expect("parse domain") {
        ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
        _ => panic!("expected a domain"),
    };
    let problem = match read_pddl(&problem_src).expect("parse problem") {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
        _ => panic!("expected a problem"),
    };

    let mut params = Parameters::default();
    params.ground_actions = ground;

    let ctx = SearchContext::new(&domain, &problem, &params);
    let solution = match plan(&ctx) {
        Outcome::Solved(p) => p,
        _ => panic!("a plan exists"),
    };
    assert!(solution.complete(), "returned plan must be complete");
    format_plan_body(&ctx, &solution)
}

fn golden(name: &str) -> String {
    // Golden files contain a trailing newline; the formatted body does not.
    fs::read_to_string(format!("tests/testdata/{name}"))
        .expect("read golden")
        .trim_end_matches('\n')
        .to_string()
}

#[test]
fn sussman_anomaly_lifted() {
    let body = solve(false);
    assert_eq!(body, golden("sussman_anomaly_lifted.golden"));
}

#[test]
fn sussman_anomaly_ground() {
    let body = solve(true);
    assert_eq!(body, golden("sussman_anomaly_ground.golden"));
}
