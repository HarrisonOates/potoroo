//! Admissibility cross-check on a wider set of domains.

use potoroo::lpsas::Operators;
use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::search::SearchContext;
use std::fs;

/// Cross-checks the relaxation against the exact answer on domains beyond the
/// usual set. Holding the operators integral makes the estimate exact, so it is
/// the oracle every relaxed bound has to sit under.
///
/// `#[ignore]`d because the exact side solves a mixed-integer program per probe
/// and takes about a minute:
/// `cargo test --release --features highs-lp --test lpsas_extra -- --ignored --nocapture`
#[test]
#[ignore = "slow: the oracle side is a MIP per probe"]
fn the_relaxation_never_exceeds_the_exact_answer() {
    if !potoroo::external::fd_available() {
        return;
    }
    for (df, pf) in [
        ("ferry-domain.pddl", "test-ferry.pddl"),
        ("gripper-domain.pddl", "gripper-8.pddl"),
        ("monkey-domain.pddl", "monkey-test2.pddl"),
    ] {
        let ds = fs::read_to_string(format!("examples/{df}")).unwrap();
        let ps = fs::read_to_string(format!("examples/{pf}")).unwrap();
        let domain = match read_pddl(&ds).unwrap() {
            ParsedUnit::Domain(d) => lower_domain(&d).unwrap(),
            _ => panic!(),
        };
        let problem = match read_pddl(&ps).unwrap() {
            ParsedUnit::Problem(p) => lower_problem(&p, &domain).unwrap(),
            _ => panic!(),
        };
        let params = Parameters {
            ground_actions: true,
            ..Parameters::default()
        };
        let ctx = SearchContext::new(&domain, &problem, &params);
        let Ok(task) = potoroo::fdr_pocl::translate(&ctx) else {
            println!("{pf}: translate failed");
            continue;
        };
        let lp = potoroo::lpsas::horizon_bound(&task, 16, Operators::Fractional);
        let exact = potoroo::lpsas::horizon_bound(&task, 16, Operators::Integral);
        println!(
            "{pf:<22} vars={:<3} ops={:<5} LP={lp:?} exact={exact:?}",
            task.variables.len(),
            task.operators.len()
        );
        if let (Some(l), Some(e)) = (lp, exact) {
            assert!(
                l <= e,
                "{pf}: LP bound {l} exceeds the exact {e} — INADMISSIBLE"
            );
        }
    }
}
