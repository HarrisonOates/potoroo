//! Characterises the weakness Bylander identifies in the Lplan heuristic, so a
//! future tightening of the relaxation shows up as a measurable change.
//!
//! Bylander, *A Linear Programming Heuristic for Optimal Planning*, AAAI-97,
//! p. 697: because the relaxation lets operator variables take fractional
//! values, conflicting operators can each "half fire" and their effects
//! superpose. He works the example `op3(0) = op4(0) = op3(1) = op4(1) = 0.5`,
//! and concludes: "This 'superposition' of operators in relaxed solutions is a
//! major reason why the heuristic can lead to poor results."
//!
//! Tower of Hanoi is his stated pathological case: the heuristic "gives a value
//! of 2n for the distance from the initial state to the goal state. However,
//! the shortest plan requires 2^n - 1 steps, so the heuristic is exponentially
//! bad for this domain."

use std::fs;

use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::plan::Plan;
use potoroo::search::SearchContext;

fn initial_h(domain_file: &str, problem_file: &str) -> f32 {
    let domain_src = fs::read_to_string(format!("examples/{domain_file}")).unwrap();
    let problem_src = fs::read_to_string(format!("examples/{problem_file}")).unwrap();
    let domain = match read_pddl(&domain_src).unwrap() {
        ParsedUnit::Domain(d) => lower_domain(&d).unwrap(),
        _ => panic!("expected a domain"),
    };
    let problem = match read_pddl(&problem_src).unwrap() {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).unwrap(),
        _ => panic!("expected a problem"),
    };
    let params = Parameters {
        ground_actions: true,
        ..Parameters::default()
    };
    let ctx = SearchContext::new(&domain, &problem, &params);
    let initial = Plan::make_initial_plan(&ctx).expect("initial plan");
    potoroo::lplan::lplan_rank(&initial, &ctx, params.weight)
}

#[test]
fn the_estimate_stays_admissible_where_it_is_exact() {
    // Sussman's optimal plan is 3 steps and Lplan finds exactly that.
    let h = initial_h("blocks-world-domain.pddl", "sussman-anomaly.pddl");
    assert!(h <= 3.0 + 1e-3, "h={h} must not exceed the optimal 3");
    assert!(h >= 3.0 - 1e-3, "h={h} is expected to be exact here");
}

#[test]
fn superposition_leaves_a_large_gap_on_tower_of_hanoi() {
    // Three disks: the shortest plan is 2^3 - 1 = 7 steps.
    let h = initial_h("hanoi-domain.pddl", "hanoi-3.pddl");
    assert!(h <= 7.0 + 1e-3, "h={h} must stay admissible (<= 7)");
    // The gap is the point of this test. The horizon cap here is 6, and the
    // estimate comes in below it, so this is the relaxation being loose rather
    // than the scan being truncated. Bylander predicts 2n = 6 for his encoding;
    // over the causal-link compilation it is weaker still.
    assert!(
        h < 6.0,
        "h={h}: expected the superposition gap to leave the estimate below 2n=6"
    );
}
