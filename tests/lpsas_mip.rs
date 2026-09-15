//! SAS+ relaxation with integral operator variables.
use std::fs;
use std::time::Instant;

use potoroo::lpsas::Operators;
use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::search::SearchContext;

/// Held out of the default run: each probe is a mixed-integer program, which is
/// seconds on gripper even with HiGHS and far worse under the pure-Rust microlp
/// the default build uses. It measures rather than asserts, so run it
/// deliberately:
/// `cargo test --release --features highs-lp --test lpsas_mip -- --ignored --nocapture`
#[test]
#[ignore = "slow: solves a mixed-integer program per probe"]
fn integral_operators_against_the_relaxation() {
    if !potoroo::external::fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }
    println!(
        "{:<22} {:>8} {:>10} {:>12} {:>10} {:>12}",
        "problem", "optimal", "LP", "LP time", "MIP", "MIP time"
    );
    for (df, pf, optimal) in [
        ("blocks-world-domain.pddl", "sussman-anomaly.pddl", 3usize),
        ("ferry-domain.pddl", "test-ferry.pddl", 7),
        ("hanoi-domain.pddl", "hanoi-3.pddl", 7),
        ("gripper-domain.pddl", "gripper-4.pddl", 9),
        ("monkey-domain.pddl", "monkey-test1.pddl", 6),
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
        let task = potoroo::fdr_pocl::translate(&ctx).expect("translate");

        let t0 = Instant::now();
        let lp = potoroo::lpsas::horizon_bound(&task, 12, Operators::Fractional);
        let lp_time = t0.elapsed();
        let t1 = Instant::now();
        let mip = potoroo::lpsas::horizon_bound(&task, 12, Operators::Integral);
        let mip_time = t1.elapsed();

        println!(
            "{pf:<22} {optimal:>8} {:>10} {:>12?} {:>10} {:>12?}",
            lp.map(|v| v.to_string()).unwrap_or_else(|| "-".into()),
            lp_time,
            mip.map(|v| v.to_string()).unwrap_or_else(|| "-".into()),
            mip_time
        );
        for (name, got) in [("LP", lp), ("MIP", mip)] {
            if let Some(v) = got {
                assert!(
                    v <= optimal,
                    "{pf}: {name} gave {v} > optimal {optimal} — INADMISSIBLE"
                );
            }
        }
    }
}
