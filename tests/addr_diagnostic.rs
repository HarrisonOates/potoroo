//! Characterises `ADDR` (VHPOP's h^r_add) against `ADD` as a partial plan grows.
//!
//! `ADDR` differs from `ADD` only in `reuse_literal`, which reports an open
//! condition as free when any existing step carries a same-sign effect that
//! unifies with it and is not explicitly ordered after the consumer -- exactly
//! the rule of Younes & Simmons (2003), §3.1.2. That check scans every step and
//! every effect for every open condition, so its cost should grow with plan
//! size while `ADD`'s stays flat.
//!
//! A small best-first search (ranked by ADD) supplies realistic plans; both
//! estimates are then measured on the same plan whenever the search reaches a
//! new maximum step count.
//!
//!   cargo test --release --test addr_diagnostic -- --nocapture

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::rc::Rc;
use std::time::Instant;

use potoroo::heuristics::Heuristic;
use potoroo::params::Parameters;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::plan::Plan;
use potoroo::search::SearchContext;

/// Min-heap entry ordered by rank (lower is better).
struct Node(f32, usize, Rc<Plan>);
impl PartialEq for Node {
    fn eq(&self, o: &Self) -> bool {
        self.cmp(o) == Ordering::Equal
    }
}
impl Eq for Node {}
impl Ord for Node {
    fn cmp(&self, o: &Self) -> Ordering {
        // Reversed: BinaryHeap is a max-heap, we want the smallest rank first.
        o.0.total_cmp(&self.0).then(o.1.cmp(&self.1))
    }
}
impl PartialOrd for Node {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

fn load(dp: &str, pp: &str) -> (potoroo::domain::Domain, potoroo::problem::Problem) {
    let ds = std::fs::read_to_string(dp).expect("read domain");
    let ps = std::fs::read_to_string(pp).expect("read problem");
    let domain = match read_pddl(&ds).expect("parse domain") {
        ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
        _ => panic!("expected a domain"),
    };
    let problem = match read_pddl(&ps).expect("parse problem") {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
        _ => panic!("expected a problem"),
    };
    (domain, problem)
}

// A measurement tool, not a regression test: it prints a table and its numbers
// are timing-dependent, so it stays out of ordinary `cargo test` runs.
// Run it explicitly with `--ignored`.
#[test]
#[ignore]
fn addr_value_and_cost_against_plan_depth() {
    let dp = std::env::var("DIAG_DOMAIN").unwrap_or_else(|_| "examples/gripper-domain.pddl".into());
    let pp = std::env::var("DIAG_PROBLEM").unwrap_or_else(|_| "examples/gripper-6.pddl".into());
    let budget: usize = std::env::var("DIAG_NODES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(6000);
    let (domain, problem) = load(&dp, &pp);

    // The context's heuristic only drives the search; both estimates below are
    // computed explicitly, so the comparison is against identical plans.
    let params = Parameters {
        heuristic: Heuristic::parse("ADD").expect("ADD"),
        ..Parameters::default()
    };
    let ctx = SearchContext::new(&domain, &problem, &params);

    let h_add = Heuristic::parse("ADD_COST").expect("ADD_COST");
    let h_addr = Heuristic::parse("ADDR_COST").expect("ADDR_COST");
    let pg = ctx.planning_graph();
    let type_ctx = ctx.type_ctx();

    // Repeat each evaluation: a single one is far too fast to time reliably.
    const REPS: u32 = 25;
    let timed = |h: &Heuristic, p: &Rc<Plan>| -> (f32, f64) {
        let mut v = 0.0;
        let start = Instant::now();
        for _ in 0..REPS {
            v = h.plan_rank(p, 1.0, &domain.predicates, &type_ctx, Some(&*pg), &ctx)[0];
        }
        (v, start.elapsed().as_nanos() as f64 / REPS as f64 / 1000.0)
    };

    let root = Plan::make_initial_plan(&ctx).expect("initial plan");
    let mut open: BinaryHeap<Node> = BinaryHeap::new();
    open.push(Node(0.0, 0, root));

    let mut serial = 0usize;
    let mut deepest = 0usize;
    println!(
        "\n{:>6} {:>6} {:>9} {:>9} {:>10} {:>10} {:>8}",
        "steps", "open", "h_ADD", "h_ADDR", "ADD_us", "ADDR_us", "ratio"
    );

    let mut rows: Vec<(usize, f64, f64)> = Vec::new();
    let mut expanded = 0usize;

    while let Some(Node(_, _, plan)) = open.pop() {
        expanded += 1;
        if expanded > budget {
            break;
        }
        for s in potoroo::chain::iter(&plan.steps) {
            ctx.register_step(s.id, &s.action);
        }

        // Report the first time the search reaches each new plan size.
        if plan.num_steps() > deepest {
            deepest = plan.num_steps();
            let (v_add, t_add) = timed(&h_add, &plan);
            let (v_addr, t_addr) = timed(&h_addr, &plan);
            println!(
                "{:>6} {:>6} {:>9.1} {:>9.1} {:>10.2} {:>10.2} {:>7.1}x",
                plan.num_steps(),
                plan.num_open_conds(),
                v_add,
                v_addr,
                t_add,
                t_addr,
                t_addr / t_add.max(1e-9)
            );
            rows.push((plan.num_steps(), t_add, t_addr));
        }

        if plan.complete() {
            println!("(solved at {} steps)", plan.num_steps());
            break;
        }

        let mut kids: Vec<Rc<Plan>> = Vec::new();
        plan.refinements(&ctx, &mut kids);
        let parent_steps = plan.num_steps();
        for kid in kids {
            serial += 1;
            kid.id.set(serial);
            ctx.register_newest_step(&kid, parent_steps);
            let r = h_add.plan_rank(&kid, 1.0, &domain.predicates, &type_ctx, Some(&*pg), &ctx)[0];
            if r.is_finite() {
                // g + h, so the search actually descends rather than thrashing.
                open.push(Node(kid.cost() as f32 + r, serial, kid));
            }
        }
    }

    if let (Some(first), Some(last)) = (rows.first(), rows.last()) {
        println!(
            "\nADD   {:.2}us at {} steps -> {:.2}us at {} steps  ({:.1}x)",
            first.1,
            first.0,
            last.1,
            last.0,
            last.1 / first.1.max(1e-9)
        );
        println!(
            "ADDR  {:.2}us at {} steps -> {:.2}us at {} steps  ({:.1}x)",
            first.2,
            first.0,
            last.2,
            last.0,
            last.2 / first.2.max(1e-9)
        );
    }
    println!("expanded {expanded} nodes, deepest {deepest} steps");
}
