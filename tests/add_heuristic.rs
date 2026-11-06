//! Integration test: plan the Sussman anomaly with the additive `ADD`
//! planning-graph heuristic in both lifted and ground modes, and compare the
//! formatted plan body against the established golden files. Explicit `ADD`,
//! `ADDR`, and the default `ADD/LIFO` yield the same optimal plan here, so the
//! golden files are shared.

use std::fs;

use potoroo::heuristics::Heuristic;
use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::search::{format_plan_body, plan, Outcome, SearchContext};

fn solve(heuristic: &str, ground: bool) -> String {
    let domain_src = fs::read_to_string("examples/blocks-world-domain.pddl")
        .expect("read blocks-world-domain.pddl");
    let problem_src =
        fs::read_to_string("examples/sussman-anomaly.pddl").expect("read sussman-anomaly.pddl");

    let domain = match read_pddl(&domain_src).expect("parse domain") {
        ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
        _ => panic!("expected a domain"),
    };
    let problem = match read_pddl(&problem_src).expect("parse problem") {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
        _ => panic!("expected a problem"),
    };

    let params = Parameters {
        heuristic: Heuristic::parse(heuristic).expect("valid heuristic"),
        ground_actions: ground,
        ..Parameters::default()
    };

    let ctx = SearchContext::new(&domain, &problem, &params);
    let solution = match plan(&ctx) {
        Outcome::Solved(p) => p,
        _ => panic!("a plan exists"),
    };
    assert!(solution.complete(), "returned plan must be complete");
    format_plan_body(&ctx, &solution)
}

fn golden(name: &str) -> String {
    fs::read_to_string(format!("tests/testdata/{name}"))
        .expect("read golden")
        .trim_end_matches('\n')
        .to_string()
}

#[test]
fn sussman_anomaly_add_lifted() {
    let body = solve("ADD", false);
    assert_eq!(body, golden("sussman_anomaly_lifted.golden"));
}

#[test]
fn sussman_anomaly_add_ground() {
    let body = solve("ADD", true);
    assert_eq!(body, golden("sussman_anomaly_ground.golden"));
}

#[test]
fn sussman_anomaly_addr_lifted() {
    let body = solve("ADDR", false);
    assert_eq!(body, golden("sussman_anomaly_lifted.golden"));
}

fn negative_cost_task() -> (potoroo::domain::Domain, potoroo::problem::Problem) {
    let domain = match read_pddl(
        "(define (domain negative-cost)
          (:requirements :strips :typing :negative-preconditions)
          (:types item)
          (:predicates (p ?x - item))
          (:action clear :parameters (?x - item)
            :precondition (and) :effect (not (p ?x))))",
    )
    .unwrap()
    {
        ParsedUnit::Domain(d) => lower_domain(&d).unwrap(),
        _ => unreachable!(),
    };
    let problem = match read_pddl(
        "(define (problem negative-cost) (:domain negative-cost)
          (:objects a b - item) (:init (p a) (p b))
          (:goal (not (p a))))",
    )
    .unwrap()
    {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).unwrap(),
        _ => unreachable!(),
    };
    (domain, problem)
}

#[test]
fn lifted_negative_literal_uses_the_cost_of_its_negation() {
    use potoroo::bindings::{Binding, Bindings};
    use potoroo::formula::Atom;
    use potoroo::terms::{Term, Variable};

    let (domain, problem) = negative_cost_task();
    let params = Parameters::default();
    let ctx = SearchContext::new(&domain, &problem, &params);
    let pg = ctx.planning_graph();
    let types = ctx.type_ctx();
    let a = problem
        .objects
        .find_object(Some(&domain.constants), "a")
        .unwrap();
    let ground = Atom {
        predicate: domain.predicates.find_predicate("p").unwrap(),
        terms: vec![Term::Object(a)],
    };
    let lifted = Atom {
        predicate: ground.predicate,
        terms: vec![Term::Variable(Variable(0))],
    };
    let empty = Bindings::empty();
    let bound = empty
        .add(
            &types,
            &[Binding::new(Variable(0), 1, Term::Object(a), 0, true)],
            false,
        )
        .unwrap();

    // p is initially true. Its negation needs one clear action, for either
    // object. Ground, fully bound and unbound lookups must all charge for it.
    assert_eq!(pg.heuristic_value_atom(&ground, 0, None).add_cost(), 0.0);
    for value in [
        pg.heuristic_value_negation(&ground, 0, None),
        pg.heuristic_value_negation(&ground, 1, Some((&types, &empty))),
        pg.heuristic_value_negation(&lifted, 1, Some((&types, &bound))),
        pg.heuristic_value_negation(&lifted, 1, Some((&types, &empty))),
    ] {
        assert_eq!(value.add_cost(), 1.0);
        assert_eq!(value.add_work(), 1);
    }
}

#[test]
fn lifted_and_ground_add_ranks_charge_for_negative_goals() {
    let (domain, problem) = negative_cost_task();
    for ground_actions in [false, true] {
        for heuristic in ["ADD/ADD_COST/ADD_WORK", "ADDR/ADDR_COST/ADDR_WORK"] {
            let params = Parameters {
                ground_actions,
                heuristic: Heuristic::parse(heuristic).unwrap(),
                ..Parameters::default()
            };
            let ctx = SearchContext::new(&domain, &problem, &params);
            let initial = potoroo::plan::Plan::make_initial_plan(&ctx).unwrap();
            let (rank, greedy_rank) = initial.rank_both(&ctx);
            assert_eq!(rank, vec![1.0; 3], "{heuristic}, ground={ground_actions}");
            assert_eq!(
                &greedy_rank[..3],
                &[1.0; 3],
                "{heuristic}, ground={ground_actions}"
            );

            let Outcome::Solved(solution) = plan(&ctx) else {
                panic!("negative goal should be solvable, ground={ground_actions}");
            };
            assert_eq!(solution.num_steps(), 1);
            potoroo::validate::is_valid_solution(&solution, &ctx).unwrap();
        }
    }
}
