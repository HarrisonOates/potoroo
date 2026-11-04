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
        ground_actions: ground,
        heuristic: potoroo::heuristics::Heuristic::parse(heuristic).expect("valid heuristic"),
        ..Parameters::default()
    };

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
    check(
        "blocks-world-domain.pddl",
        "sussman-anomaly.pddl",
        "UCPOP",
        false,
    );
}

#[test]
fn sussman_valid_ground() {
    check(
        "blocks-world-domain.pddl",
        "sussman-anomaly.pddl",
        "UCPOP",
        true,
    );
}

#[test]
fn sussman_valid_add() {
    check(
        "blocks-world-domain.pddl",
        "sussman-anomaly.pddl",
        "ADD",
        false,
    );
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
    check(
        "blocks-world-domain.pddl",
        "sussman-anomaly.pddl",
        "RELAX",
        false,
    );
}

#[test]
fn sussman_valid_relaxr_ground() {
    check(
        "blocks-world-domain.pddl",
        "sussman-anomaly.pddl",
        "RELAXR",
        true,
    );
}

#[test]
fn gripper_valid_relax_ground() {
    check("gripper-domain.pddl", "gripper-2.pddl", "RELAX", true);
}

#[test]
fn sussman_valid_sample_ff_ground() {
    check(
        "blocks-world-domain.pddl",
        "sussman-anomaly.pddl",
        "SAMPLE_FF",
        true,
    );
}

#[test]
fn gripper_valid_sample_ff_ground() {
    check("gripper-domain.pddl", "gripper-2.pddl", "SAMPLE_FF:3", true);
}

// ---------------------------------------------------------------------------
// Closed-world links
// ---------------------------------------------------------------------------
//
// flat-tire's `open` relies on `Plan::new_cw_link`: `(not (locked ?x))` holds
// only by closed-world absence from `:init`. No domain above exercises that,
// which is why `link_supported`'s gap on it went unnoticed (see validate.rs).

#[test]
fn flat_tire_closed_world_link_valid_lifted() {
    check("flat-tire-domain.pddl", "fix1.pddl", "ADD", false);
}

#[test]
fn flat_tire_closed_world_link_valid_ground() {
    check("flat-tire-domain.pddl", "fix1.pddl", "ADD", true);
}

#[test]
fn flat_tire_closed_world_link_valid_lifted_2() {
    check("flat-tire-domain.pddl", "fix2.pddl", "ADD", false);
}

// ---------------------------------------------------------------------------
// ADL examples. These exercise conditional effects, universally quantified
// effects, and quantified/disjunctive preconditions. They were parsed and
// lowered by the coverage tests but never solved, so nothing checked the plans
// the planner returned for them.
// ---------------------------------------------------------------------------

#[test]
fn mcd_blocks_world_valid_under_quantified_preconditions_and_effects() {
    // `forall` in both preconditions and effects, with a nested `or` inside a
    // `when` — the richest ADL example in the corpus.
    check(
        "mcd-blocks-world-domain.pddl",
        "mcd-sussman-anomaly.pddl",
        "ADD",
        false,
    );
    check(
        "mcd-blocks-world-domain.pddl",
        "mcd-sussman-anomaly.pddl",
        "UCPOP",
        false,
    );
}

#[test]
fn briefcase_world_valid_under_conditional_effects() {
    check("briefcase-world-domain.pddl", "get-paid.pddl", "ADD", false);
    check(
        "briefcase-world-domain.pddl",
        "get-paid.pddl",
        "UCPOP",
        false,
    );
}

#[test]
fn trains_valid_under_an_existential_goal() {
    check("trains-domain.pddl", "trains1.pddl", "ADD", false);
    check("trains-domain.pddl", "trains1.pddl", "UCPOP", false);
}

#[test]
fn robot_valid_under_a_universally_quantified_conditional_effect() {
    check("robot-domain.pddl", "r-test1.pddl", "ADD", false);
    check("robot-domain.pddl", "r-test1.pddl", "UCPOP", false);
}

#[test]
fn ho_world_valid_under_conditional_effects() {
    check("ho-world-domain.pddl", "ho-demo.pddl", "UCPOP", false);
}

#[test]
fn mcd_blocks_world_valid_ground() {
    check(
        "mcd-blocks-world-domain.pddl",
        "mcd-sussman-anomaly.pddl",
        "ADD",
        true,
    );
}

/// The lifted landmark heuristic is the only one that solves `fixit`, so its
/// plan has never been through the independent checker under any other
/// configuration. A heuristic that unlocks a problem is exactly the one whose
/// output most needs verifying.
#[test]
fn flat_tire_valid_under_landmarks() {
    check("flat-tire-domain.pddl", "fixit.pddl", "LM", false);
}

#[test]
fn ferry_valid_under_landmarks() {
    check("ferry-domain.pddl", "test-ferry.pddl", "LM", false);
}

#[test]
fn sussman_valid_under_landmarks() {
    check(
        "blocks-world-domain.pddl",
        "sussman-anomaly.pddl",
        "LM",
        false,
    );
}
