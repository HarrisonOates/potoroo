//! Smoke test: a single Lplan evaluation on a small initial plan, to check the
//! LP encoding produces a sensible finite value at a reasonable per-node cost.

use std::fs;
use std::time::Instant;

use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::plan::Plan;
use potoroo::search::SearchContext;

fn eval(domain_file: &str, problem_file: &str) -> (f32, f32, std::time::Duration) {
    let domain_src = fs::read_to_string(format!("examples/{domain_file}")).unwrap();
    let problem_src = fs::read_to_string(format!("examples/{problem_file}")).unwrap();
    let domain = match read_pddl(&domain_src).unwrap() {
        ParsedUnit::Domain(d) => lower_domain(&d).unwrap(),
        _ => panic!(),
    };
    let problem = match read_pddl(&problem_src).unwrap() {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).unwrap(),
        _ => panic!(),
    };
    let mut params = Parameters::default();
    params.ground_actions = true;
    let ctx = SearchContext::new(&domain, &problem, &params);
    let initial = Plan::make_initial_plan(&ctx).expect("initial plan");
    let t = Instant::now();
    let h = vhpop::lplan::lplan_rank(&initial, &ctx, params.weight);
    let dt = t.elapsed();
    (h, params.weight, dt)
}

#[test]
fn lplan_sussman_initial_eval() {
    let (h, _w, dt) = eval("blocks-world-domain.pddl", "sussman-anomaly.pddl");
    eprintln!("sussman initial Lplan h = {h}, took {dt:?}");
    assert!(h.is_finite());
    // The optimal sussman plan has 3 steps; an admissible heuristic must not
    // exceed it.
    assert!(h <= 3.0 + 1e-3, "h={h} should be admissible (<= 3)");
}

#[test]
fn lplan_gripper_initial_eval() {
    let (h, _w, dt) = eval("gripper-domain.pddl", "gripper-2.pddl");
    eprintln!("gripper-2 initial Lplan h = {h}, took {dt:?}");
    assert!(h.is_finite());
    assert!(h <= 3.0 + 1e-3, "h={h} should be admissible (<= 3)");
}

/// End-to-end: the LPLAN heuristic drives the search to a valid optimal solution.
/// `#[ignore]`d because the per-node LP cost makes this ~30s (the heuristic is
/// deliberately expensive — Bylander's own planner needed ~1s/node). Run with
/// `cargo test --test lplan_smoke -- --ignored`.
#[test]
#[ignore = "slow: ~30s of LP solving"]
fn lplan_sussman_solves_valid_optimal() {
    use potoroo::search::{plan, Outcome};
    use potoroo::validate::is_valid_solution;

    let domain_src = fs::read_to_string("examples/blocks-world-domain.pddl").unwrap();
    let problem_src = fs::read_to_string("examples/sussman-anomaly.pddl").unwrap();
    let domain = match read_pddl(&domain_src).unwrap() {
        ParsedUnit::Domain(d) => lower_domain(&d).unwrap(),
        _ => panic!(),
    };
    let problem = match read_pddl(&problem_src).unwrap() {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).unwrap(),
        _ => panic!(),
    };
    let mut params = Parameters::default();
    params.ground_actions = true;
    params.heuristic = vhpop::heuristics::Heuristic::parse("LPLAN").unwrap();
    let ctx = SearchContext::new(&domain, &problem, &params);
    let sol = match plan(&ctx) {
        Outcome::Solved(p) => p,
        Outcome::LimitReached => panic!("search limit reached"),
        Outcome::NoSolution => panic!("no solution found"),
    };
    assert_eq!(sol.num_steps(), 3, "sussman optimal is 3 steps");
    is_valid_solution(&sol, &ctx).expect("LPLAN solution must be valid");
}
