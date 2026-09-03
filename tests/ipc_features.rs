use potoroo::external::fd_available;
use potoroo::fdr_pocl::{solve_with_params as solve_fdr, translate, Outcome as FdrOutcome};
use potoroo::heuristics::Heuristic;
use potoroo::params::{ActionCost, Parameters, SearchAlgorithm};
use potoroo::parser::{bind_action_costs, lower_domain, lower_problem, read_pddl, ParsedUnit};
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

// ---------------------------------------------------------------------------
// IPC 2023 language coverage
// ---------------------------------------------------------------------------
//
// The 2023 classical dataset exercises PDDL surface syntax and an action-cost
// idiom that the earlier examples never did. Each test below pins one of those.

/// `:parameters(...)` with no separating space, padding before a closing paren,
/// and a declaration/use case mismatch. All three are legal PDDL -- parens are
/// self-delimiting and names are case-insensitive -- and all three appear in
/// IPC 2023's labyrinth domain.
const PERMISSIVE_DOMAIN: &str = r#"
(define (domain permissive)
  (:requirements :adl)
  (:types NODE - object)
  (:constants Home - NODE)
  (:predicates (LINK ?a - node ?b - node) (visited ?n - node))
  (:action go
:parameters(?from - NODE ?to - node)
    :precondition (and (visited ?from ) (link ?from ?to))
    :effect (visited ?to)))
"#;

const PERMISSIVE_PROBLEM: &str = r#"
(define (problem permissive-p)
  (:domain PERMISSIVE)
  (:objects Away - node)
  (:init (visited home) (Link HOME away))
  (:goal (VISITED Away)))
"#;

#[test]
fn parses_permissive_paren_spacing_and_folds_name_case() {
    let (domain, problem) = lower(PERMISSIVE_DOMAIN, PERMISSIVE_PROBLEM);
    // One `link` predicate, not one per spelling.
    assert_eq!(domain.actions.len(), 1);
    assert_eq!(problem.init_atoms.len(), 2);

    let params = Parameters {
        heuristic: Heuristic::parse("ADD").unwrap(),
        search_limits: vec![10_000],
        ..Parameters::default()
    };
    let context = SearchContext::new(&domain, &problem, &params);
    let Outcome::Solved(solution) = plan(&context) else {
        panic!("expected the case-folded task to be solved");
    };
    assert_eq!(solution.num_steps(), 1);
}

/// `(increase (total-cost) (drive-cost))`: the cost is a nullary function whose
/// value the *problem* fixes in `:init`. Every cost-bearing IPC 2023 domain
/// uses this form rather than a literal.
const FUNCTION_COST_DOMAIN: &str = r#"
(define (domain function-cost)
  (:requirements :strips :action-costs)
  (:predicates (at-a) (at-b))
  (:functions (total-cost) - number (drive-cost) - number)
  (:action drive
    :parameters ()
    :precondition (at-a)
    :effect (and (at-b) (increase (total-cost) (drive-cost)))))
"#;

fn function_cost_problem(name: &str, cost: u32) -> String {
    format!(
        "(define (problem {name})
           (:domain function-cost)
           (:init (at-a) (= (total-cost) 0) (= (drive-cost) {cost}))
           (:goal (at-b))
           (:metric minimize (total-cost)))"
    )
}

#[test]
fn resolves_action_costs_from_nullary_init_functions() {
    let source = function_cost_problem("fc-p", 7);
    let (mut domain, problem) = lower(FUNCTION_COST_DOMAIN, &source);
    // Unbound, the schema carries only the constant part.
    assert_eq!(domain.actions[0].cost_base, 0);
    assert_eq!(domain.actions[0].cost, 0);

    bind_action_costs(&mut domain, &problem).unwrap();
    assert_eq!(domain.actions[0].cost, 7);
}

#[test]
fn cost_binding_is_idempotent_across_problems_sharing_a_domain() {
    let first = function_cost_problem("fc-1", 7);
    let (mut domain, problem_one) = lower(FUNCTION_COST_DOMAIN, &first);

    let second = function_cost_problem("fc-2", 2);
    let problem_two = match read_pddl(&second).unwrap() {
        ParsedUnit::Problem(problem) => lower_problem(&problem, &domain).unwrap(),
        _ => panic!("expected problem"),
    };

    // Rebinding must recompute from the constant base, not accumulate.
    bind_action_costs(&mut domain, &problem_one).unwrap();
    assert_eq!(domain.actions[0].cost, 7);
    bind_action_costs(&mut domain, &problem_two).unwrap();
    assert_eq!(domain.actions[0].cost, 2);
    bind_action_costs(&mut domain, &problem_two).unwrap();
    assert_eq!(domain.actions[0].cost, 2);
    bind_action_costs(&mut domain, &problem_one).unwrap();
    assert_eq!(domain.actions[0].cost, 7);
}

#[test]
fn reports_a_cost_function_the_problem_never_assigns() {
    let source = "(define (problem fc-missing)
                    (:domain function-cost)
                    (:init (at-a) (= (total-cost) 0))
                    (:goal (at-b))
                    (:metric minimize (total-cost)))";
    let (mut domain, problem) = lower(FUNCTION_COST_DOMAIN, source);
    let message = bind_action_costs(&mut domain, &problem)
        .expect_err("an unassigned cost function must be reported")
        .to_string();
    assert!(message.contains("drive-cost"), "unexpected error: {message}");
}

/// Two schemas achieve `cursor`, and their parameter at index 1 is a `marker`
/// in one and a `slot` in the other -- sibling types, so neither substitutes
/// for the other. Both are generated as step 1 of sibling refinements of the
/// same parent, and `step_var_types` is keyed by step id alone, so whichever
/// registers last would type *both* children's variables. Typing `pick`'s `?m`
/// as `place`'s `?t` makes the `(tagged ?m)` lookup match no ground atom, so
/// `pick` is ranked unreachable and dropped -- and since `place` really is
/// dead, the search then reports no solution for a one-step task.
///
/// This is IPC 2023's folding domain in miniature, where `rotate`'s
/// `?fromdir - direction` was being typed as `rotate-first-pass`'s `?n1 - node`.
/// `place` is declared second so it is the sibling that registers last.
const SIBLING_TYPE_DOMAIN: &str = r#"
(define (domain sibling-types)
  (:requirements :adl)
  (:types marker slot - object)
  (:predicates
    (tagged ?m - marker)
    (blocked ?t - slot)
    (cursor ?s - slot))
  (:action pick
    :parameters (?s - slot ?m - marker)
    :precondition (tagged ?m)
    :effect (cursor ?s))
  (:action place
    :parameters (?s - slot ?t - slot)
    :precondition (blocked ?t)
    :effect (cursor ?s)))
"#;

const SIBLING_TYPE_PROBLEM: &str = r#"
(define (problem sibling-types-p)
  (:domain sibling-types)
  (:objects m1 - marker s1 - slot)
  (:init (tagged m1))
  (:goal (cursor s1)))
"#;

#[test]
fn sibling_refinements_do_not_share_each_others_parameter_types() {
    let (domain, problem) = lower(SIBLING_TYPE_DOMAIN, SIBLING_TYPE_PROBLEM);
    let params = Parameters {
        heuristic: Heuristic::parse("ADD").unwrap(),
        search_limits: vec![10_000],
        ..Parameters::default()
    };
    let context = SearchContext::new(&domain, &problem, &params);
    let Outcome::Solved(solution) = plan(&context) else {
        panic!("ADD must not rank a reachable sibling refinement as unreachable");
    };
    assert_eq!(solution.num_steps(), 1);
}

/// `(not (WALL ?c))` over an unbound `?c`, where `WALL` is static. The negation
/// of a static atom can only ever hold because the atom is *absent*, and the
/// relaxed graph tracks only negations some action achieves -- so the lookup has
/// to reason about the tuples the pattern admits but the relation does not
/// contain. Valuing it infinite makes ADD prune every move, as it did on IPC
/// 2023's ricochet-robots.
const NEGATED_STATIC_DOMAIN: &str = r#"
(define (domain negated-static)
  (:requirements :adl)
  (:types cell - object)
  (:predicates (WALL ?c - cell) (at ?c - cell) (visited ?c - cell))
  (:action move
    :parameters (?from - cell ?to - cell)
    :precondition (and (at ?from) (not (WALL ?from)))
    :effect (and (not (at ?from)) (at ?to) (visited ?to))))
"#;

const NEGATED_STATIC_PROBLEM: &str = r#"
(define (problem negated-static-p)
  (:domain negated-static)
  (:objects c1 c2 c3 - cell)
  (:init (at c1) (WALL c3))
  (:goal (visited c2)))
"#;

#[test]
fn negated_static_literal_over_unbound_variables_is_reachable() {
    let (domain, problem) = lower(NEGATED_STATIC_DOMAIN, NEGATED_STATIC_PROBLEM);
    let params = Parameters {
        heuristic: Heuristic::parse("ADD").unwrap(),
        search_limits: vec![10_000],
        ..Parameters::default()
    };
    let context = SearchContext::new(&domain, &problem, &params);
    let Outcome::Solved(solution) = plan(&context) else {
        panic!("one blocked cell must not make every move look unreachable");
    };
    assert_eq!(solution.num_steps(), 1);
}

/// A parameterless action whose whole effect is `forall`-`when`, as in IPC
/// 2023's rubiks-cube. The relaxed graph enumerates schema parameters from the
/// precondition; a quantified effect's own variables need enumerating too, or
/// the action contributes nothing and everything downstream of it looks
/// unreachable. `finish` sits downstream of `prime`'s quantified effect, so
/// ADD has to value `(ready t1)` finitely for the plan to be found at all.
const QUANTIFIED_EFFECT_DOMAIN: &str = r#"
(define (domain quantified-effect)
  (:requirements :adl)
  (:types tile - object)
  (:predicates (here ?t - tile) (ready ?t - tile) (done ?t - tile))
  (:action prime
    :parameters ()
    :precondition (and)
    :effect (forall (?t - tile) (when (here ?t) (ready ?t))))
  (:action finish
    :parameters (?t - tile)
    :precondition (ready ?t)
    :effect (done ?t)))
"#;

const QUANTIFIED_EFFECT_PROBLEM: &str = r#"
(define (problem quantified-effect-p)
  (:domain quantified-effect)
  (:objects t1 t2 - tile)
  (:init (here t1) (here t2))
  (:goal (done t1)))
"#;

#[test]
fn relaxed_graph_applies_universally_quantified_effects() {
    let (domain, problem) = lower(QUANTIFIED_EFFECT_DOMAIN, QUANTIFIED_EFFECT_PROBLEM);
    let params = Parameters {
        heuristic: Heuristic::parse("ADD").unwrap(),
        search_limits: vec![10_000],
        ..Parameters::default()
    };
    let context = SearchContext::new(&domain, &problem, &params);
    let Outcome::Solved(solution) = plan(&context) else {
        panic!("a quantified effect must make its literals reachable");
    };
    assert_eq!(solution.num_steps(), 2);
}

/// A disjunctive precondition, as in IPC 2023's recharging-robots
/// (`(or (CONNECTED ?from ?to) (CONNECTED ?to ?from))`). Separating an effect
/// from such a precondition must not assert that every disjunct is false: that
/// contradicts the precondition itself, so the step's open conditions can never
/// all close and the search runs forever without ever completing a plan.
const DISJUNCTIVE_PRECONDITION_DOMAIN: &str = r#"
(define (domain disjunctive-move)
  (:requirements :adl)
  (:types loc robot - object)
  (:predicates (CONN ?a - loc ?b - loc) (at ?r - robot ?l - loc))
  (:action move
    :parameters (?r - robot ?from - loc ?to - loc)
    :precondition (and (at ?r ?from) (or (CONN ?from ?to) (CONN ?to ?from)))
    :effect (and (not (at ?r ?from)) (at ?r ?to))))
"#;

const DISJUNCTIVE_PRECONDITION_PROBLEM: &str = r#"
(define (problem disjunctive-move-p)
  (:domain disjunctive-move)
  (:objects r1 - robot l1 l2 - loc)
  (:init (at r1 l1) (CONN l1 l2))
  (:goal (at r1 l2)))
"#;

#[test]
fn effect_separator_preserves_a_disjunctive_precondition() {
    let (domain, problem) = lower(
        DISJUNCTIVE_PRECONDITION_DOMAIN,
        DISJUNCTIVE_PRECONDITION_PROBLEM,
    );
    let params = Parameters {
        heuristic: Heuristic::parse("ADD").unwrap(),
        search_limits: vec![10_000],
        ..Parameters::default()
    };
    let context = SearchContext::new(&domain, &problem, &params);
    let Outcome::Solved(solution) = plan(&context) else {
        panic!("a disjunctive precondition must not make its own action unusable");
    };
    assert_eq!(solution.num_steps(), 1);
}
