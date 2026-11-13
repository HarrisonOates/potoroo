//! Opt-in measurements for the RELAX investigation. No production search changes.
use super::*;
use crate::fdr::{Effect, Operator, Variable};
use crate::heuristics::FlawSelectionOrder;
use std::hint::black_box;
use std::time::Instant;

/// Evaluate both heuristics on the same ADD-selected plans. DIAG_SAS is a
/// previously translated task. Repetitions measure evaluator cost without
/// mixing different search trajectories or translator time.
#[test]
#[ignore]
fn compare_on_identical_partial_plans() {
    let source = std::fs::read_to_string(std::env::var("DIAG_SAS").expect("DIAG_SAS"))
        .expect("read SAS task");
    let task = Task::parse(&source).expect("parse SAS task");
    let planner = Planner::new(&task);
    let params = Parameters {
        heuristic: Heuristic::parse("ADD/LIFO").unwrap(),
        ..Parameters::default()
    };
    let flaws = FlawSelectionOrder::parse("ZLIFO").unwrap();
    let mut queue = BinaryHeap::new();
    let root = Rc::new(PartialPlan::initial(&task));
    queue.push(QueuedPlan {
        rank: planner.compute_rank_both(&root, &params).0,
        plan: root,
        is_lazy: false,
    });
    let mut generated = 1;
    let mut last_depth = None;
    let mut barriers = 0;
    println!("kind,visited,steps,opens,distinct_opens,h_add,h_relax,f_add,f_relax,add_ns,relax_ns");
    for visited in 0..5000 {
        let Some(node) = queue.pop() else { break };
        let plan = node.plan;
        let add = planner.open_estimate(&plan, false).cost;
        let relax = planner
            .relaxed_plan_size(&plan, false)
            .unwrap_or(f32::INFINITY);
        if last_depth.is_none_or(|depth| plan.num_steps() > depth) || plan.complete(&task) {
            last_depth = Some(plan.num_steps());
            let time = |relax: bool| {
                let start = Instant::now();
                for _ in 0..1000 {
                    if relax {
                        black_box(planner.relaxed_plan_size(black_box(&plan), false));
                    } else {
                        black_box(planner.open_estimate(black_box(&plan), false));
                    }
                }
                start.elapsed().as_nanos() / 1000
            };
            let distinct = plan
                .open_conditions()
                .map(|o| o.condition)
                .collect::<HashSet<_>>()
                .len();
            println!(
                "sample,{visited},{},{},{distinct},{add},{relax},{},{},{},{}",
                plan.num_steps(),
                plan.num_open_conditions(),
                add + plan.cost() as f32,
                relax + plan.cost() as f32,
                time(false),
                time(true)
            );
        }
        if plan.complete(&task) && linearize_and_validate(&plan, &task).is_some() {
            println!(
                "solved,visited={visited},generated={generated},steps={}",
                plan.num_steps()
            );
            break;
        }
        for mut child in planner.refinements(&plan, &flaws) {
            child.id = generated;
            generated += 1;
            let rank = planner.compute_rank_both(&child, &params).0;
            if !rank[0].is_finite() {
                continue;
            }
            if barriers < 12 {
                let cr = planner
                    .relaxed_plan_size(&child, false)
                    .unwrap_or(f32::INFINITY);
                if cr.is_finite()
                    && cr + child.cost() as f32 > relax + plan.cost() as f32
                    && rank[0] <= add + plan.cost() as f32
                {
                    println!("barrier,parent_steps={},child_steps={},parent_add_f={},child_add_f={},parent_relax_f={},child_relax_f={}",
                        plan.num_steps(), child.num_steps(), add + plan.cost() as f32, rank[0],
                        relax + plan.cost() as f32, cr + child.cost() as f32);
                    barriers += 1;
                }
            }
            queue.push(QueuedPlan {
                plan: Rc::new(child),
                rank,
                is_lazy: false,
            });
            if generated >= 200_000 {
                return;
            }
        }
    }
}

/// The same required fact occurs at distinct consumers. Committing its
/// producer can raise RELAX's g+h while ADD's g+h stays constant: extraction
/// still charges the producer to support the remaining goal. This is a
/// minimal witness of a search barrier, not a proposed correctness change.
#[test]
fn committed_support_can_raise_relax_rank_while_add_stays_flat() {
    let task = Task {
        variables: (0..3)
            .map(|i| Variable {
                name: format!("v{i}"),
                values: vec!["false".into(), "true".into()],
            })
            .collect(),
        initial: vec![0; 3],
        goals: vec![Fact::new(1, 1), Fact::new(2, 1)],
        operators: (0..3)
            .map(|i| Operator {
                name: format!("make-{i}"),
                prevail: if i == 0 {
                    vec![]
                } else {
                    vec![Fact::new(0, 1)]
                },
                effects: vec![Effect {
                    conditions: vec![],
                    variable: i,
                    pre: None,
                    post: 1,
                }],
                cost: 1,
            })
            .collect(),
        mutex_groups: vec![],
        axioms: vec![],
    };
    let planner = Planner::new(&task);
    let flaws = FlawSelectionOrder::parse("ZLIFO").unwrap();
    let root = Rc::new(PartialPlan::initial(&task));
    let first = Rc::new(
        planner
            .refinements(&root, &flaws)
            .into_iter()
            .find(|p| p.num_steps() == 1)
            .unwrap(),
    );
    let support = planner
        .refinements(&first, &flaws)
        .into_iter()
        .find(|p| p.num_steps() == 2)
        .unwrap();
    let f = |p: &PartialPlan, relax| {
        p.cost() as f32
            + if relax {
                planner.relaxed_plan_size(p, false).unwrap()
            } else {
                planner.open_estimate(p, false).cost
            }
    };
    assert_eq!(
        (f(&root, false), f(&first, false), f(&support, false)),
        (4.0, 4.0, 4.0)
    );
    assert_eq!(
        (f(&root, true), f(&first, true), f(&support, true)),
        (3.0, 3.0, 4.0)
    );
    let params = Parameters {
        heuristic: Heuristic::parse("REPOP").unwrap(),
        ..Parameters::default()
    };
    let scores: Vec<_> = [&*root, &*first, &support]
        .into_iter()
        .map(|plan| planner.compute_rank_both(plan, &params).0.to_vec()[0])
        .collect();
    assert_eq!(scores, vec![3.0, 3.0, 3.0]);
    // Paper-style parallel extraction still charges the committed producer
    // when it supports a potential future action rather than a current open.
    // FFR's VHPOP-style TOP-LEVEL filter does not address that recursive case.
    for heuristic in ["FF", "FFR"] {
        let params = Parameters {
            heuristic: Heuristic::parse(heuristic).unwrap(),
            ..Parameters::default()
        };
        let scores: Vec<_> = [&*root, &*first, &support]
            .into_iter()
            .map(|plan| planner.compute_rank_both(plan, &params).0.to_vec()[0])
            .collect();
        assert_eq!(scores, vec![3.0, 3.0, 4.0], "{heuristic}");
    }
}
