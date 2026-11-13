//! Explicit investigation of the corrected compiled-heuristic cost convention.
//! Requires local Fast Downward; writes SAS witnesses under target/.
use potoroo::compile::ground_task;
use potoroo::external::{FdHeuristic, HResult};
use potoroo::heuristics::Heuristic;
use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::plan::Plan;
use potoroo::search::SearchContext;

#[test]
#[ignore]
fn record_compiled_ff_cost_accounting() {
    let ParsedUnit::Domain(d) = read_pddl("(define (domain chain) (:requirements :strips) (:predicates (p) (q)) (:action make-p :parameters () :precondition (and) :effect (p)) (:action make-q :parameters () :precondition (p) :effect (q)))").unwrap() else { panic!() };
    let domain = lower_domain(&d).unwrap();
    let ParsedUnit::Problem(p) =
        read_pddl("(define (problem chain-p) (:domain chain) (:init) (:goal (q)))").unwrap()
    else {
        panic!()
    };
    let problem = lower_problem(&p, &domain).unwrap();
    let params = Parameters {
        ground_actions: true,
        heuristic: Heuristic::parse("COMPILE_FF").unwrap(),
        ..Parameters::default()
    };
    let ctx = SearchContext::new(&domain, &problem, &params);
    let mut plan = Plan::make_initial_plan(&ctx).unwrap();
    let folder = std::path::Path::new("target/relax-investigation/compile-corrected-accounting");
    std::fs::create_dir_all(folder).unwrap();
    println!("committed_cost,compiled_ff,corrected_rank,paper_remaining,paper_rank,compiled_lmcut,lmcut_remaining");
    for index in 0..3 {
        let compiled = ground_task(&plan, &ctx);
        std::fs::write(folder.join(format!("step-{index}.sas")), compiled.to_sas()).unwrap();
        let HResult::Finite(h) = compiled.heuristic(FdHeuristic::Ff).unwrap() else {
            panic!()
        };
        let HResult::Finite(lmcut) = compiled.heuristic(FdHeuristic::LmCut).unwrap() else {
            panic!()
        };
        let g = plan.cost() as f32;
        let remaining = (h - g).max(0.0);
        println!(
            "{g},{h},{},{remaining},{},{lmcut},{}",
            plan.rank(&ctx)[0],
            g + remaining,
            (lmcut - g).max(0.0)
        );
        assert_eq!(g, index as f32);
        assert_eq!(plan.rank(&ctx)[0], g + remaining);
        let (rank, greedy) = params.heuristic.plan_rank_both(
            &plan,
            5.0,
            &domain.predicates,
            &ctx.type_ctx(),
            None,
            &ctx,
        );
        assert_eq!(rank[0], g + 5.0 * remaining);
        assert_eq!(greedy[0], 5.0 * remaining);
        if plan.complete() {
            assert_eq!(index, 2);
            break;
        }
        let mut children = vec![];
        plan.refinements(&ctx, &mut children);
        assert_eq!(children.len(), 1);
        plan = children.pop().unwrap();
    }
    assert!(plan.complete());
}
