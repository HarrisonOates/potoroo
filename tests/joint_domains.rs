use std::fs;

use potoroo::heuristics::{FlawSelectionOrder, Heuristic};
use potoroo::params::{Parameters, SearchAlgorithm};
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::pruning::PruneOptions;
use potoroo::search::{plan, Outcome, SearchContext};

fn solve(domain: &str, problem: &str, joint: bool, ground: bool, bfs: bool) -> usize {
    let ParsedUnit::Domain(parsed) = read_pddl(domain).unwrap() else {
        panic!()
    };
    let domain = lower_domain(&parsed).unwrap();
    let ParsedUnit::Problem(parsed) = read_pddl(problem).unwrap() else {
        panic!()
    };
    let problem = lower_problem(&parsed, &domain).unwrap();
    let params = Parameters {
        flaw_orders: vec![FlawSelectionOrder::parse("ZLIFO").unwrap()],
        heuristic: Heuristic::parse(if bfs { "LIFO" } else { "ADD/LIFO" }).unwrap(),
        search_algorithm: if bfs {
            SearchAlgorithm::Bfs
        } else {
            SearchAlgorithm::A
        },
        ground_actions: ground,
        prune: PruneOptions {
            joint,
            ..PruneOptions::default()
        },
        search_limits: vec![50_000],
        ..Parameters::default()
    };
    let ctx = SearchContext::new(&domain, &problem, &params);
    let Outcome::Solved(solution) = plan(&ctx) else {
        panic!("no solution: joint={joint}, ground={ground}, bfs={bfs}")
    };
    potoroo::validate::is_valid_solution(&solution, &ctx).unwrap();
    potoroo::validate::is_executable_solution(&solution, &ctx).unwrap();
    solution.cost()
}

#[test]
fn zlifo_solutions_remain_valid_with_joint_domains() {
    for (domain, problem) in [
        ("blocks-world-domain", "sussman-anomaly"),
        ("gripper-domain", "gripper-2"),
        ("ferry-domain", "test-ferry"),
        ("road-domain", "road-test"),
        ("briefcase-world-domain", "get-paid"),
    ] {
        let domain = fs::read_to_string(format!("examples/{domain}.pddl")).unwrap();
        let problem = fs::read_to_string(format!("examples/{problem}.pddl")).unwrap();
        for ground in [false, true] {
            solve(&domain, &problem, false, ground, false);
            solve(&domain, &problem, true, ground, false);
        }
    }
}

#[test]
fn quantified_disjunctive_negative_and_conditional_preconditions_are_safe() {
    let domain = "(define (domain adl-joint)
        (:requirements :adl) (:types item)
        (:predicates (eligible ?x - item) (blocked ?x - item) (ready ?x - item) (done))
        (:action prepare :parameters (?x - item)
            :precondition (and (eligible ?x) (not (blocked ?x)))
            :effect (when (eligible ?x) (ready ?x)))
        (:action finish :parameters ()
            :precondition (and (exists (?x - item) (ready ?x))
                (forall (?y - item) (or (blocked ?y) (ready ?y))))
            :effect (done)))";
    let problem = "(define (problem adl-joint-p) (:domain adl-joint)
        (:objects a b - item) (:init (eligible a) (blocked b)) (:goal (done)))";
    for ground in [false, true] {
        for joint in [false, true] {
            assert_eq!(solve(domain, problem, joint, ground, true), 2);
        }
    }
}

#[test]
fn breadth_first_optimum_is_preserved() {
    let domain = fs::read_to_string("examples/gripper-domain.pddl").unwrap();
    let problem = fs::read_to_string("examples/gripper-2.pddl").unwrap();
    let baseline = solve(&domain, &problem, false, false, true);
    assert_eq!(baseline, solve(&domain, &problem, true, false, true));
}
