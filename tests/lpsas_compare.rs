//! Measures the SAS+ encoding against the boolean one on the same tasks.
use std::fs;
use std::time::Instant;

use potoroo::lplan::Tightenings;
use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::plan::Plan;
use potoroo::search::SearchContext;

fn compare(domain_file: &str, problem_file: &str, optimal: f32) {
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
    let params = Parameters {
        ground_actions: true,
        ..Parameters::default()
    };
    let ctx = SearchContext::new(&domain, &problem, &params);
    let initial = Plan::make_initial_plan(&ctx).expect("initial plan");

    let t0 = Instant::now();
    let boolean = potoroo::lplan::lplan_rank(&initial, &ctx, params.weight, Tightenings::NONE);
    let t_bool = t0.elapsed();
    let t1 = Instant::now();
    let tightened = potoroo::lplan::lplan_rank(&initial, &ctx, params.weight, Tightenings::ALL);
    let t_tight = t1.elapsed();

    let task = potoroo::fdr_pocl::translate(&ctx).expect("translate");
    let t2 = Instant::now();
    let sas = potoroo::lpsas::horizon_bound(&task, 12);
    let t_sas = t2.elapsed();

    println!(
        "{problem_file:<22} opt={optimal:<4} LPLAN={boolean:<4}({:>5?}) LPLAN2={tightened:<4}({:>5?}) SAS+={:<4}({:>5?})  vars={} ops={}",
        t_bool, t_tight,
        sas.map(|v| v.to_string()).unwrap_or_else(|| "-".into()),
        t_sas, task.variables.len(), task.operators.len()
    );
    if let Some(v) = sas {
        assert!(
            v as f32 <= optimal + 1e-3,
            "{problem_file}: SAS+ gave {v} > optimal {optimal} — INADMISSIBLE"
        );
    }
}

#[test]
fn sas_encoding_against_the_boolean_one() {
    if !potoroo::external::fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }
    compare("blocks-world-domain.pddl", "sussman-anomaly.pddl", 3.0);
    compare("hanoi-domain.pddl", "hanoi-3.pddl", 7.0);
    compare("ferry-domain.pddl", "test-ferry.pddl", 7.0);
    compare("gripper-domain.pddl", "gripper-4.pddl", 9.0);
    compare("monkey-domain.pddl", "monkey-test1.pddl", 6.0);
}
