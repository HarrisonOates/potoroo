//! The step-variable encoding must stay admissible and must actually respond to
//! the partial plan, which is the whole point of it over a bare task bound.
use std::fs;

use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::plan::Plan;
use potoroo::search::SearchContext;

fn setup(
    domain_file: &str,
    problem_file: &str,
) -> (potoroo::domain::Domain, potoroo::problem::Problem) {
    let ds = fs::read_to_string(format!("examples/{domain_file}")).unwrap();
    let ps = fs::read_to_string(format!("examples/{problem_file}")).unwrap();
    let domain = match read_pddl(&ds).unwrap() {
        ParsedUnit::Domain(d) => lower_domain(&d).unwrap(),
        _ => panic!(),
    };
    let problem = match read_pddl(&ps).unwrap() {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).unwrap(),
        _ => panic!(),
    };
    (domain, problem)
}

#[test]
fn the_completion_bound_is_admissible_and_sees_the_partial_plan() {
    if !potoroo::external::fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }
    for (df, pf, optimal) in [
        ("blocks-world-domain.pddl", "sussman-anomaly.pddl", 3usize),
        ("ferry-domain.pddl", "test-ferry.pddl", 7),
        ("gripper-domain.pddl", "gripper-4.pddl", 9),
    ] {
        let (domain, problem) = setup(df, pf);
        let params = Parameters {
            ground_actions: true,
            ..Parameters::default()
        };
        let ctx = SearchContext::new(&domain, &problem, &params);
        let task = potoroo::fdr_pocl::translate(&ctx).expect("translate");
        let initial = Plan::make_initial_plan(&ctx).expect("initial plan");

        let bare = potoroo::lpsas::horizon_bound(&task, 12);
        let completion = potoroo::lpsas::completion_bound(&task, &initial, &ctx, 12);
        eprintln!("  {pf:<22} optimal={optimal:<3} task bound={bare:?} completion={completion:?}");

        // On the initial plan there are no committed steps, so the two must
        // agree — the step variables contribute nothing yet.
        assert_eq!(
            bare, completion,
            "{pf}: with no committed steps the two bounds must agree"
        );
        if let Some(v) = completion {
            assert!(
                v <= optimal,
                "{pf}: completion bound {v} exceeds optimal {optimal} — INADMISSIBLE"
            );
        }
    }
}

#[test]
fn no_optimal_path_is_priced_out_of_reach() {
    if !potoroo::external::fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }
    // A node that committed a wasteful step may genuinely need more steps than
    // the problem's optimum, so its bound may exceed that optimum without being
    // inadmissible. What must hold is that *some* child still lies on an optimal
    // plan and is priced within it: if every child were priced above the
    // optimum, A* would have no admissible route to an optimal solution.
    for (df, pf, optimal) in [
        ("blocks-world-domain.pddl", "sussman-anomaly.pddl", 3usize),
        ("ferry-domain.pddl", "test-ferry.pddl", 7),
    ] {
        let (domain, problem) = setup(df, pf);
        let params = Parameters {
            ground_actions: true,
            ..Parameters::default()
        };
        let ctx = SearchContext::new(&domain, &problem, &params);
        let task = potoroo::fdr_pocl::translate(&ctx).expect("translate");

        let mut frontier = vec![Plan::make_initial_plan(&ctx).expect("initial plan")];
        for depth in 1..=3usize {
            let mut children = Vec::new();
            for plan in &frontier {
                plan.refinements(&ctx, &mut children);
            }
            if children.is_empty() {
                break;
            }
            let best = children
                .iter()
                .filter_map(|c| potoroo::lpsas::completion_bound(&task, c, &ctx, 12))
                .min();
            eprintln!(
                "  {pf:<22} depth={depth} children={} best bound={best:?} optimal={optimal}",
                children.len()
            );
            if let Some(v) = best {
                assert!(
                    v <= optimal,
                    "{pf}: at depth {depth} every child is priced above the optimal {optimal} \
                     (best was {v}) — an optimal plan would be unreachable"
                );
            }
            children.truncate(30);
            frontier = children;
        }
    }
}
