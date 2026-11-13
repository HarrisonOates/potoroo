//! Measure literal ADD and RELAX on identical plans selected by ADD.
//! Run explicitly with --ignored --nocapture; DIAG_DOMAIN/DIAG_PROBLEM select
//! the inputs, DIAG_GROUND=1 enables grounding, DIAG_NODES caps expansions.
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::hint::black_box;
use std::rc::Rc;
use std::time::Instant;

use potoroo::heuristics::{FlawSelectionOrder, Heuristic};
use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::plan::Plan;
use potoroo::search::SearchContext;

struct Node(f32, usize, Rc<Plan>);
impl PartialEq for Node {
    fn eq(&self, o: &Self) -> bool {
        self.cmp(o) == Ordering::Equal
    }
}
impl Eq for Node {}
impl PartialOrd for Node {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Node {
    fn cmp(&self, o: &Self) -> Ordering {
        o.0.total_cmp(&self.0).then(self.1.cmp(&o.1))
    }
}

#[test]
#[ignore]
fn compare_literal_heuristics_on_identical_plans() {
    let ds = std::fs::read_to_string(std::env::var("DIAG_DOMAIN").expect("DIAG_DOMAIN")).unwrap();
    let ps = std::fs::read_to_string(std::env::var("DIAG_PROBLEM").expect("DIAG_PROBLEM")).unwrap();
    let domain = match read_pddl(&ds).unwrap() {
        ParsedUnit::Domain(d) => lower_domain(&d).unwrap(),
        _ => panic!("domain"),
    };
    let problem = match read_pddl(&ps).unwrap() {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).unwrap(),
        _ => panic!("problem"),
    };
    let params = Parameters {
        // Request RELAX metadata even though ADD selects the measurement plans.
        heuristic: Heuristic::parse("RELAX/ADD/LIFO").unwrap(),
        ground_actions: std::env::var("DIAG_GROUND").is_ok_and(|s| s == "1"),
        flaw_orders: vec![FlawSelectionOrder::parse("ZLIFO").unwrap()],
        ..Parameters::default()
    };
    let budget = std::env::var("DIAG_NODES").map_or(6000, |s| s.parse().unwrap());
    let ctx = SearchContext::new(&domain, &problem, &params);
    let pg = ctx.planning_graph();
    let types = ctx.type_ctx();
    let add = Heuristic::parse("ADD").unwrap();
    let rank =
        |plan: &Rc<Plan>| add.plan_rank(plan, 1.0, &domain.predicates, &types, Some(&pg), &ctx)[0];
    let root = Plan::make_initial_plan(&ctx).unwrap();
    let mut queue = BinaryHeap::new();
    queue.push(Node(rank(&root), 0, root));
    let mut generated = 1;
    let mut last_depth = None;
    println!("kind,visited,steps,opens,h_add,h_relax,f_add,f_relax,add_ns,relax_ns");
    for visited in 0..budget {
        let Some(Node(_, _, plan)) = queue.pop() else {
            break;
        };
        for step in potoroo::chain::iter(&plan.steps) {
            ctx.register_step(step.id, &step.action);
        }
        if last_depth.is_none_or(|depth| plan.num_steps() > depth) || plan.complete() {
            last_depth = Some(plan.num_steps());
            let fa = rank(&plan);
            let hr = pg
                .relaxed_plan_size(&ctx, &plan, false)
                .unwrap_or(f32::INFINITY);
            let time = |relax| {
                let start = Instant::now();
                for _ in 0..100 {
                    if relax {
                        black_box(pg.relaxed_plan_size(&ctx, black_box(&plan), false));
                    } else {
                        black_box(rank(black_box(&plan)));
                    }
                }
                start.elapsed().as_nanos() / 100
            };
            println!(
                "sample,{visited},{},{},{},{hr},{fa},{},{},{}",
                plan.num_steps(),
                plan.num_open_conds(),
                fa - plan.cost() as f32,
                hr + plan.cost() as f32,
                time(false),
                time(true)
            );
        }
        if plan.complete() {
            println!(
                "solved,visited={visited},generated={generated},steps={}",
                plan.num_steps()
            );
            break;
        }
        let mut children = Vec::new();
        plan.refinements(&ctx, &mut children);
        for child in children {
            child.id.set(generated);
            ctx.register_newest_step(&child, plan.num_steps());
            let value = rank(&child);
            if value.is_finite() {
                queue.push(Node(value, generated, child));
            }
            generated += 1;
            if generated >= 200_000 {
                return;
            }
        }
    }
}
