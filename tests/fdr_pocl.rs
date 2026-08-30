//! End-to-end smoke test for the experimental PDDL -> SAS+ -> ground POCL path.

use std::fs;

use potoroo::external::fd_available;
use potoroo::fdr::Task;
use potoroo::fdr_pocl::{solve_with_params, translate, Outcome};
use potoroo::heuristics::Heuristic;
use potoroo::params::{Parameters, SearchAlgorithm};
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::search::SearchContext;

fn translate_example(domain_path: &str, problem_path: &str) -> Task {
    let domain_src = fs::read_to_string(domain_path).unwrap();
    let problem_src = fs::read_to_string(problem_path).unwrap();
    let domain = match read_pddl(&domain_src).unwrap() {
        ParsedUnit::Domain(domain) => lower_domain(&domain).unwrap(),
        _ => panic!("expected domain"),
    };
    let problem = match read_pddl(&problem_src).unwrap() {
        ParsedUnit::Problem(problem) => lower_problem(&problem, &domain).unwrap(),
        _ => panic!("expected problem"),
    };
    let params = Parameters::default();
    let ctx = SearchContext::new(&domain, &problem, &params);
    translate(&ctx).unwrap()
}

#[test]
fn sussman_uses_multi_valued_facts_and_solves() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }

    let task = translate_example(
        "examples/blocks-world-domain.pddl",
        "examples/sussman-anomaly.pddl",
    );
    assert_eq!(task.variables.len(), 6);
    assert_eq!(task.multi_valued_variables(), 3);
    assert_eq!(task.num_facts(), 15);

    let search_params = Parameters {
        search_algorithm: SearchAlgorithm::Gbfs,
        heuristic: Heuristic::parse("ADD/UCPOP").unwrap(),
        search_limits: vec![200_000],
        ..Parameters::default()
    };
    let (outcome, stats) = solve_with_params(&task, &search_params).unwrap();
    let Outcome::Solved(solution) = outcome else {
        panic!("expected the finite-domain POCL experiment to solve Sussman");
    };
    assert!(solution.plan.complete(&task));
    assert_eq!(
        solution.format(&task),
        "1:(puton c table a)\n2:(puton b c table)\n3:(puton a b table)"
    );
    assert!(stats.h_evals > 0);
}

#[test]
fn native_lmcut_heuristics_solve_sussman() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }

    let task = translate_example(
        "examples/blocks-world-domain.pddl",
        "examples/sussman-anomaly.pddl",
    );
    for heuristic in ["LMCUT", "LMCUTR"] {
        let params = Parameters {
            search_algorithm: SearchAlgorithm::Gbfs,
            heuristic: Heuristic::parse(heuristic).unwrap(),
            search_limits: vec![1_000],
            ..Parameters::default()
        };
        let (outcome, stats) = solve_with_params(&task, &params).unwrap();
        let Outcome::Solved(solution) = outcome else {
            panic!("{heuristic} did not solve Sussman");
        };
        assert_eq!(solution.operators.len(), 3);
        assert!(solution.plan.complete(&task));
        assert!(stats.h_evals > 0);
    }
}

#[test]
fn gripper_rejects_cyclic_orderings_instead_of_diving() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }

    let task = translate_example("examples/gripper-domain.pddl", "examples/gripper-4.pddl");
    let params = Parameters {
        search_algorithm: SearchAlgorithm::Gbfs,
        heuristic: Heuristic::parse("ADD").unwrap(),
        search_limits: vec![500],
        ..Parameters::default()
    };
    let (outcome, stats) = solve_with_params(&task, &params).unwrap();
    let Outcome::Solved(solution) = outcome else {
        panic!("expected FDR GBFS to solve Gripper-4 without entering a move cycle");
    };

    assert_eq!(solution.operators.len(), 11);
    assert!(stats.nodes_generated < 500);
    assert!(stats.max_steps <= 11);
}
