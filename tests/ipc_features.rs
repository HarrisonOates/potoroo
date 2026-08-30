use potoroo::external::fd_available;
use potoroo::fdr_pocl::{solve_with_params as solve_fdr, translate, Outcome as FdrOutcome};
use potoroo::heuristics::Heuristic;
use potoroo::params::{ActionCost, Parameters, SearchAlgorithm};
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::problem::Metric;
use potoroo::search::{plan, Outcome, SearchContext};

const COST_DOMAIN: &str = r#"
(define (domain cost-choice)
  (:requirements :strips :action-costs)
  (:predicates (start) (middle) (done))
  (:functions (total-cost) - number)
  (:action direct
    :parameters ()
    :precondition (start)
    :effect (and (done) (increase (total-cost) 9)))
  (:action cheap-first
    :parameters ()
    :precondition (start)
    :effect (and (middle) (increase (total-cost) 2)))
  (:action cheap-second
    :parameters ()
    :precondition (middle)
    :effect (and (done) (increase (total-cost) 2))))
"#;

const COST_PROBLEM: &str = r#"
(define (problem cost-choice-p)
  (:domain cost-choice)
  (:init (start) (= (total-cost) 0))
  (:goal (done))
  (:metric minimize (total-cost)))
"#;

fn lower(
    domain_source: &str,
    problem_source: &str,
) -> (potoroo::domain::Domain, potoroo::problem::Problem) {
    let domain = match read_pddl(domain_source).unwrap() {
        ParsedUnit::Domain(domain) => lower_domain(&domain).unwrap(),
        _ => panic!("expected domain"),
    };
    let problem = match read_pddl(problem_source).unwrap() {
        ParsedUnit::Problem(problem) => lower_problem(&problem, &domain).unwrap(),
        _ => panic!("expected problem"),
    };
    (domain, problem)
}

#[test]
fn lowers_restricted_pddl_action_costs() {
    let (domain, problem) = lower(COST_DOMAIN, COST_PROBLEM);
    assert!(domain.requirements.action_costs);
    assert_eq!(problem.metric, Some(Metric::MinimizeTotalCost));
    assert_eq!(
        domain
            .actions
            .iter()
            .map(|action| action.cost)
            .collect::<Vec<_>>(),
        vec![9, 2, 2]
    );
}

#[test]
fn lifted_search_accumulates_cost_only_for_new_steps() {
    let (domain, problem) = lower(COST_DOMAIN, COST_PROBLEM);
    let params = Parameters {
        heuristic: Heuristic::parse("ADD").unwrap(),
        search_limits: vec![10_000],
        ..Parameters::default()
    };
    let context = SearchContext::new(&domain, &problem, &params);
    let Outcome::Solved(solution) = plan(&context) else {
        panic!("expected lifted action-cost task to be solved");
    };
    assert_eq!(solution.num_steps(), 2);
    assert_eq!(solution.cost(), 4);
}

#[test]
fn fdr_astar_optimizes_declared_cost_and_unit_override_optimizes_length() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }
    let (domain, problem) = lower(COST_DOMAIN, COST_PROBLEM);
    let translate_params = Parameters::default();
    let context = SearchContext::new(&domain, &problem, &translate_params);
    let task = translate(&context).unwrap();
    assert_eq!(
        task.operators
            .iter()
            .map(|operator| operator.cost)
            .collect::<Vec<_>>(),
        vec![2, 2, 9]
    );

    let task_costs = Parameters {
        search_algorithm: SearchAlgorithm::A,
        heuristic: Heuristic::parse("LMCUTR").unwrap(),
        search_limits: vec![10_000],
        ..Parameters::default()
    };
    let (outcome, _) = solve_fdr(&task, &task_costs).unwrap();
    let FdrOutcome::Solved(solution) = outcome else {
        panic!("expected task-cost A* to solve");
    };
    assert_eq!(solution.plan.cost(), 4);
    assert_eq!(solution.operators.len(), 2);

    let unit_costs = Parameters {
        action_cost: ActionCost::Unit,
        ..task_costs
    };
    let (outcome, _) = solve_fdr(&task, &unit_costs).unwrap();
    let FdrOutcome::Solved(solution) = outcome else {
        panic!("expected unit-cost A* to solve");
    };
    assert_eq!(solution.plan.cost(), 1);
    assert_eq!(solution.operators.len(), 1);
}

#[test]
fn original_task_emitter_keeps_quantifiers_disjunction_and_type_hierarchy() {
    let domain_source = r#"
    (define (domain quantified)
      (:requirements :strips :typing :disjunctive-preconditions
                     :universal-preconditions :existential-preconditions)
      (:types vehicle - object truck - vehicle)
      (:predicates (seen ?x - vehicle) (ready))
      (:action finish
        :parameters ()
        :precondition (forall (?x - vehicle)
                        (or (seen ?x) (exists (?y - truck) (seen ?y))))
        :effect (ready)))
    "#;
    let problem_source = r#"
    (define (problem quantified-p)
      (:domain quantified)
      (:objects t - truck)
      (:init (seen t))
      (:goal (or (ready) (seen t))))
    "#;
    let (domain, problem) = lower(domain_source, problem_source);
    let (emitted_domain, emitted_problem) = potoroo::pddl_emit::emit_original(&domain, &problem);
    assert!(emitted_domain.contains("truck - vehicle"));
    assert!(emitted_domain.contains("(forall (?v0 - vehicle)"));
    assert!(emitted_domain.contains("(exists (?v1 - truck)"));
    assert!(emitted_problem.contains("(:goal (or (ready) (seen t)))"));
    assert!(matches!(
        read_pddl(&emitted_domain).unwrap(),
        ParsedUnit::Domain(_)
    ));
    assert!(matches!(
        read_pddl(&emitted_problem).unwrap(),
        ParsedUnit::Problem(_)
    ));
}

fn solve_adl_goal(goal: &str) -> usize {
    let domain_source = r#"
    (define (domain adl-goal)
      (:requirements :strips :typing :disjunctive-preconditions
                     :existential-preconditions :universal-preconditions)
      (:types item)
      (:predicates (clean ?x - item))
      (:action clean
        :parameters (?x - item)
        :precondition (and)
        :effect (clean ?x)))
    "#;
    let problem_source = format!(
        "(define (problem adl-goal-p)\n\
           (:domain adl-goal)\n\
           (:objects a b - item)\n\
           (:init)\n\
           (:goal {goal}))"
    );
    let (domain, problem) = lower(domain_source, &problem_source);
    let params = Parameters {
        search_algorithm: SearchAlgorithm::A,
        heuristic: Heuristic::parse("ADD").unwrap(),
        search_limits: vec![10_000],
        ..Parameters::default()
    };
    let context = SearchContext::new(&domain, &problem, &params);
    let task = translate(&context).unwrap();
    assert!(!task.axioms.is_empty(), "test must exercise SAS+ axioms");
    let (outcome, _) = solve_fdr(&task, &params).unwrap();
    let FdrOutcome::Solved(solution) = outcome else {
        panic!("expected normalized ADL task to be solved");
    };
    solution.operators.len()
}

#[test]
fn fdr_supports_fd_axioms_from_quantified_and_disjunctive_goals() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }
    assert_eq!(solve_adl_goal("(exists (?x - item) (clean ?x))"), 1);
    assert_eq!(solve_adl_goal("(or (clean a) (clean b))"), 1);
    assert_eq!(solve_adl_goal("(forall (?x - item) (clean ?x))"), 2);
}

#[test]
fn fdr_supports_universal_preconditions_and_conditional_universal_effects() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }
    let domain_source = r#"
    (define (domain quantified-actions)
      (:requirements :strips :typing :universal-preconditions
                     :conditional-effects)
      (:types item)
      (:predicates (marked ?x - item) (enabled) (painted ?x - item) (done))
      (:action mark
        :parameters (?x - item)
        :precondition (and)
        :effect (marked ?x))
      (:action finish
        :parameters ()
        :precondition (forall (?x - item) (marked ?x))
        :effect (done))
      (:action enable
        :parameters ()
        :precondition (and)
        :effect (enabled))
      (:action paint-all
        :parameters ()
        :precondition (and)
        :effect (forall (?x - item)
                  (when (enabled) (painted ?x)))))
    "#;
    let base_problem = |goal: &str| {
        format!(
            "(define (problem quantified-actions-p)\n\
               (:domain quantified-actions)\n\
               (:objects a b - item)\n\
               (:init)\n\
               (:goal {goal}))"
        )
    };

    let solve = |goal: &str, heuristic: &str| {
        let problem_source = base_problem(goal);
        let (domain, problem) = lower(domain_source, &problem_source);
        let params = Parameters {
            search_algorithm: SearchAlgorithm::A,
            heuristic: Heuristic::parse(heuristic).unwrap(),
            search_limits: vec![10_000],
            ..Parameters::default()
        };
        let context = SearchContext::new(&domain, &problem, &params);
        let task = translate(&context).unwrap();
        let (outcome, _) = solve_fdr(&task, &params).unwrap();
        let FdrOutcome::Solved(solution) = outcome else {
            panic!("expected quantified action task to be solved");
        };
        solution.operators.len()
    };

    assert_eq!(solve("(done)", "ADD"), 3);
    assert_eq!(solve("(forall (?x - item) (painted ?x))", "ADD"), 2);
}
