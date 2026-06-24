//! Phase 1: causal-link compilation round-trips through Fast Downward.
//!
//! Verifies that the PDDL emitted by `CompiledProblem::emit_pddl` is accepted by
//! the frozen Fast Downward submodule and yields a finite initial heuristic
//! value, for both the initial plan (no steps/links) and a full solution plan
//! (committed steps + causal links + guards). Skips (passes) when FD is absent.

use std::fs;

use potoroo::compile::CompiledProblem;
use potoroo::external::{fd_available, run_fd_heuristic, FdHeuristic, HResult};
use potoroo::heuristics::Heuristic;
use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::plan::Plan;
use potoroo::search::{plan, Outcome, SearchContext};
use potoroo::validate::is_valid_solution;

fn load(domain_file: &str, problem_file: &str) -> (vhpop::domain::Domain, vhpop::problem::Problem) {
    let domain_src = fs::read_to_string(format!("examples/{domain_file}")).expect("read domain");
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
    (domain, problem)
}

#[test]
fn compile_initial_plan_emits_pddl() {
    let (domain, problem) = load("blocks-world-domain.pddl", "sussman-anomaly.pddl");
    let params = Parameters::default();
    let ctx = SearchContext::new(&domain, &problem, &params);
    let initial = Plan::make_initial_plan(&ctx).expect("initial plan");

    let compiled = CompiledProblem::compile(&initial, &ctx);
    let (dom_pddl, prob_pddl) = compiled.emit_pddl(&ctx);

    // Structural sanity: a valid PDDL shell with the compiled domain/problem.
    assert!(dom_pddl.contains("(define (domain pocl-compiled)"));
    assert!(prob_pddl.contains("(define (problem pocl-compiled-prob)"));
    assert!(dom_pddl.contains("(:predicates"));
    assert!(prob_pddl.contains("(:goal"));

    if !fd_available() {
        eprintln!("skipping FD round-trip: Fast Downward not available");
        return;
    }
    // The initial plan's compiled task is essentially the original problem (no
    // committed steps, no links), so FD must accept it and return a finite h.
    match run_fd_heuristic(&dom_pddl, &prob_pddl, FdHeuristic::Ff).expect("FD run") {
        HResult::Finite(h) => assert!(h >= 0.0, "expected a finite non-negative h, got {h}"),
        HResult::Infinite => panic!("initial-plan compilation should be solvable (finite h)"),
    }
}

#[test]
fn compile_solution_plan_round_trips() {
    let (domain, problem) = load("blocks-world-domain.pddl", "sussman-anomaly.pddl");
    let params = Parameters::default();
    let ctx = SearchContext::new(&domain, &problem, &params);

    let solution = match plan(&ctx) {
        Outcome::Solved(p) => p,
        _ => panic!("sussman has a solution"),
    };

    let compiled = CompiledProblem::compile(&solution, &ctx);
    let (dom_pddl, prob_pddl) = compiled.emit_pddl(&ctx);

    // The solution plan has committed steps and causal links, so the compiled
    // domain must contain step actions and guard propositions.
    assert!(dom_pddl.contains("(:action step-"), "expected committed step actions");
    assert!(dom_pddl.contains("(guard-0)"), "expected at least one causal-link guard");
    assert!(dom_pddl.contains("(exec-pos-"), "expected step execution indicators");

    if !fd_available() {
        eprintln!("skipping FD round-trip: Fast Downward not available");
        return;
    }
    // FD must accept the emitted PDDL and return a finite value (the compiled
    // task is solvable: applying the committed step actions reaches the goal).
    match run_fd_heuristic(&dom_pddl, &prob_pddl, FdHeuristic::Ff).expect("FD run") {
        HResult::Finite(h) => assert!(h >= 0.0, "expected a finite non-negative h, got {h}"),
        HResult::Infinite => panic!("solution compilation should be solvable (finite h)"),
    }
}

#[test]
fn compile_heuristic_ranks_initial_plan() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward not available");
        return;
    }
    let (domain, problem) = load("blocks-world-domain.pddl", "sussman-anomaly.pddl");
    let mut params = Parameters::default();
    params.heuristic = Heuristic::parse("COMPILE_FF").expect("parse COMPILE_FF");
    let ctx = SearchContext::new(&domain, &problem, &params);
    let initial = Plan::make_initial_plan(&ctx).expect("initial plan");
    let rank = initial.rank(&ctx);
    assert!(rank[0].is_finite(), "COMPILE_FF rank must be finite, got {}", rank[0]);
}

/// Ground-search fast path: grounds the compiled task to FDR and invokes only
/// the `downward` binary (no Python translator). Fast enough to run in the
/// suite. Validates the returned plan with the independent checker.
#[test]
fn compile_ground_fast_path_solves_sussman() {
    if !vhpop::external::downward_available() {
        eprintln!("skipping: downward binary not available");
        return;
    }
    let (domain, problem) = load("blocks-world-domain.pddl", "sussman-anomaly.pddl");
    let mut params = Parameters::default();
    params.ground_actions = true;
    params.heuristic = Heuristic::parse("COMPILE_FF").expect("parse COMPILE_FF");
    let ctx = SearchContext::new(&domain, &problem, &params);
    let solution = match plan(&ctx) {
        Outcome::Solved(p) => p,
        _ => panic!("ground COMPILE_FF should solve sussman"),
    };
    is_valid_solution(&solution, &ctx).expect("ground COMPILE_FF solution must be valid");
}

#[test]
fn compile_ground_fast_path_solves_gripper() {
    if !vhpop::external::downward_available() {
        eprintln!("skipping: downward binary not available");
        return;
    }
    let (domain, problem) = load("gripper-domain.pddl", "gripper-2.pddl");
    let mut params = Parameters::default();
    params.ground_actions = true;
    params.heuristic = Heuristic::parse("COMPILE_FF").expect("parse COMPILE_FF");
    let ctx = SearchContext::new(&domain, &problem, &params);
    let solution = match plan(&ctx) {
        Outcome::Solved(p) => p,
        _ => panic!("ground COMPILE_FF should solve gripper-2"),
    };
    is_valid_solution(&solution, &ctx).expect("ground COMPILE_FF solution must be valid");
}

// Ignored by default: drives the LIFTED search with one full FD driver run
// (Python translator + search) per generated node, so it takes ~2 minutes even
// on tiny sussman. The ground fast path above is the fast equivalent. Run with
// `cargo test --release --test compile -- --ignored compile_heuristic_solves`.
#[test]
#[ignore = "slow: one FD subprocess per search node (~2 min); run with --ignored"]
fn compile_heuristic_solves_sussman() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward not available");
        return;
    }
    // End-to-end: drive the search with the compilation heuristic on the tiny
    // sussman instance and validate the returned plan with the independent
    // checker.
    let (domain, problem) = load("blocks-world-domain.pddl", "sussman-anomaly.pddl");
    let mut params = Parameters::default();
    params.heuristic = Heuristic::parse("COMPILE_FF").expect("parse COMPILE_FF");
    let ctx = SearchContext::new(&domain, &problem, &params);
    let solution = match plan(&ctx) {
        Outcome::Solved(p) => p,
        _ => panic!("COMPILE_FF should solve sussman"),
    };
    is_valid_solution(&solution, &ctx).expect("COMPILE_FF solution must be valid");
}
