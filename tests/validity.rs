//! Integration test: every solution the planner returns must pass the
//! independent POCL validity checker (`potoroo::validate::is_valid_solution`).
//! This guards against silently-emitted invalid plans across representative
//! domains, in both lifted and ground mode and under several heuristics.

use std::fs;

use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::search::{plan, Outcome, SearchContext};
use potoroo::validate::is_valid_solution;

/// Solves `(domain, problem)` and asserts the returned plan is a valid POCL
/// solution under the independent checker.
fn check(domain_file: &str, problem_file: &str, heuristic: &str, ground: bool) {
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

    let mut params = Parameters::default();
    params.ground_actions = ground;
    params.heuristic = potoroo::heuristics::Heuristic::parse(heuristic).expect("valid heuristic");

    let ctx = SearchContext::new(&domain, &problem, &params);
    let solution = match plan(&ctx) {
        Outcome::Solved(p) => p,
        Outcome::LimitReached => panic!("search limit reached for {problem_file}"),
        Outcome::NoSolution => panic!("no solution found for {problem_file}"),
    };

    if let Err(e) = is_valid_solution(&solution, &ctx) {
        panic!("invalid solution for {problem_file} ({heuristic}, ground={ground}): {e}");
    }
}

#[test]
fn sussman_valid_lifted() {
    check("blocks-world-domain.pddl", "sussman-anomaly.pddl", "UCPOP", false);
}

#[test]
fn sussman_valid_ground() {
    check("blocks-world-domain.pddl", "sussman-anomaly.pddl", "UCPOP", true);
}

#[test]
fn sussman_valid_add() {
    check("blocks-world-domain.pddl", "sussman-anomaly.pddl", "ADD", false);
}

#[test]
fn gripper_valid_lifted() {
    check("gripper-domain.pddl", "gripper-2.pddl", "UCPOP", false);
}

#[test]
fn gripper_valid_ground_add() {
    check("gripper-domain.pddl", "gripper-2.pddl", "ADD", true);
}

#[test]
fn hanoi_valid_lifted() {
    check("hanoi-domain.pddl", "hanoi-3.pddl", "UCPOP", false);
}

#[test]
fn sussman_valid_relax_lifted() {
    check("blocks-world-domain.pddl", "sussman-anomaly.pddl", "RELAX", false);
}

#[test]
fn sussman_valid_relaxr_ground() {
    check("blocks-world-domain.pddl", "sussman-anomaly.pddl", "RELAXR", true);
}

#[test]
fn gripper_valid_relax_ground() {
    check("gripper-domain.pddl", "gripper-2.pddl", "RELAX", true);
}

#[test]
fn sussman_valid_sample_ff_ground() {
    check("blocks-world-domain.pddl", "sussman-anomaly.pddl", "SAMPLE_FF", true);
}

#[test]
fn gripper_valid_sample_ff_ground() {
    check("gripper-domain.pddl", "gripper-2.pddl", "SAMPLE_FF:3", true);
}
