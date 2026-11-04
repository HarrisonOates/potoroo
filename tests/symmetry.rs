//! Interchangeable-object pruning (`-p symmetry`): the classes it finds, and
//! that skipping the non-canonical achievers leaves the plan found unchanged.

use std::fs;

use potoroo::heuristics::Heuristic;
use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::pruning::PruneOptions;
use potoroo::search::SearchContext;
use potoroo::symmetry::ObjectSymmetries;

fn load(
    domain_name: &str,
    problem_name: &str,
) -> (potoroo::domain::Domain, potoroo::problem::Problem) {
    let domain_src =
        fs::read_to_string(format!("examples/{domain_name}.pddl")).expect("read domain");
    let problem_src =
        fs::read_to_string(format!("examples/{problem_name}.pddl")).expect("read problem");
    let domain = match read_pddl(&domain_src).expect("parse domain") {
        ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
        _ => panic!("expected a domain"),
    };
    let problem = match read_pddl(&problem_src).expect("parse problem") {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
        _ => panic!("expected a problem"),
    };
    (domain, problem)
}

fn fd_available() -> bool {
    potoroo::external::fd_available()
}

#[test]
fn gripper_has_two_interchangeable_grippers_and_nothing_else() {
    let (domain, problem) = load("gripper-domain", "gripper-4");
    let symmetries = ObjectSymmetries::compute(&domain, &problem);
    // The balls are named by the goal and the rooms differ in the initial
    // state; only the two grippers are alike.
    assert_eq!(
        symmetries.classes(),
        &[vec!["left".to_string(), "right".to_string()]]
    );
    assert_eq!(symmetries.by_name("left"), Some((0, 0)));
    assert_eq!(symmetries.by_name("RIGHT"), Some((0, 1)));
    assert_eq!(symmetries.by_name("ball1"), None);
}

#[test]
fn objects_the_goal_names_are_never_interchangeable() {
    // Every block of the Sussman anomaly appears in the goal.
    let (domain, problem) = load("blocks-world-domain", "sussman-anomaly");
    assert!(ObjectSymmetries::compute(&domain, &problem).is_empty());
}

#[test]
fn a_cost_function_that_tells_objects_apart_keeps_them_apart() {
    // `road-test` prices its roads through a function of their endpoints;
    // interchangeable locations would need equal road lengths too.
    let (domain, problem) = load("road-domain", "road-test");
    let symmetries = ObjectSymmetries::compute(&domain, &problem);
    for class in symmetries.classes() {
        for name in class {
            let object = problem
                .objects
                .find_object(Some(&domain.constants), name)
                .expect("a class names a problem object");
            assert!(
                !problem.init_values.iter().any(|(fluent, _)| fluent
                    .terms
                    .contains(&potoroo::terms::Term::Object(object))),
                "{name} is priced by a cost function and must not be in a class"
            );
        }
    }
}

/// The rule discards only children with a renamed sibling, so the plan found
/// costs the same under an admissible heuristic — and on gripper it fires.
#[test]
fn symmetry_pruning_keeps_the_optimal_cost_on_finite_domains() {
    if !fd_available() {
        eprintln!("skipping: Fast Downward translator not available");
        return;
    }
    use potoroo::fdr_pocl::{solve_with_context, translate, Outcome};

    let (domain, problem) = load("gripper-domain", "gripper-6");
    let translate_params = Parameters::default();
    let ctx = SearchContext::new(&domain, &problem, &translate_params);
    let task = translate(&ctx).expect("translate to SAS+");
    let symmetries = ctx.object_symmetries();

    let run = |prune: PruneOptions| {
        let params = Parameters {
            heuristic: Heuristic::parse("LMCUT").expect("LMCUT is a valid heuristic"),
            search_limits: vec![50_000],
            prune,
            ..Parameters::default()
        };
        let (outcome, stats) =
            solve_with_context(&task, &params, Some(&symmetries), None).expect("supported");
        match outcome {
            Outcome::Solved(solution) => {
                (solution.plan.cost(), stats.nodes_generated, stats.pruned)
            }
            other => panic!("gripper-6 should solve: {other:?}"),
        }
    };
    let (base_cost, base_generated, _) = run(PruneOptions::default());
    let (cost, generated, pruned) = run(PruneOptions {
        symmetry: true,
        ..PruneOptions::default()
    });
    // Baseline search also prunes unresolvable threats; compare the work
    // left by symmetry pruning rather than requiring a zero baseline count.
    assert_eq!(base_cost, cost, "symmetry pruning changed the optimal cost");
    assert!(pruned > 0, "symmetry pruning fired on nothing");
    assert!(
        generated < base_generated,
        "symmetry pruning should shrink the search ({generated} vs {base_generated})"
    );
}
