//! Regression tests for causal-link effort, distinct from additive action cost.
use super::*;
use crate::fdr::{Effect, Operator, Variable};
use crate::heuristics::FlawSelectionOrder;

fn variable(name: &str) -> Variable {
    Variable {
        name: name.into(),
        values: vec!["off".into(), "on".into()],
    }
}

fn operator(name: &str, pre: Vec<Fact>, effect: usize, cost: usize) -> Operator {
    Operator {
        name: name.into(),
        prevail: pre,
        effects: vec![Effect {
            conditions: vec![],
            variable: effect,
            pre: None,
            post: 1,
        }],
        cost,
    }
}

fn task() -> Task {
    Task {
        variables: vec![variable("a"), variable("b"), variable("p"), variable("q")],
        initial: vec![1, 1, 0, 0],
        goals: vec![Fact::new(2, 1), Fact::new(3, 1)],
        mutex_groups: vec![],
        axioms: vec![],
        operators: vec![
            operator(
                "p-from-two-initials",
                vec![Fact::new(0, 1), Fact::new(1, 1)],
                2,
                1,
            ),
            operator("q-direct", vec![], 3, 1),
        ],
    }
}

#[test]
fn native_effort_counts_initial_links_and_changes_mw_flaw_choice() {
    let task = task();
    let planner = Planner::new(&task);
    let values = &planner.base_relaxed;
    assert_eq!((values.cost[0][1], values.work[0][1]), (0.0, 1));
    assert_eq!((values.cost[2][1], values.work[2][1]), (1.0, 3));
    assert_eq!((values.cost[3][1], values.work[3][1]), (1.0, 1));
    let plan = PartialPlan::initial(&task);
    for (policy, fact) in [("MC-Loc", Fact::new(3, 1)), ("MW-Loc", Fact::new(2, 1))] {
        let flaw = planner.select_flaw(&plan, &FlawSelectionOrder::parse(policy).unwrap());
        let SelectedFlaw::Open(open) = flaw else {
            panic!("expected an open condition")
        };
        assert_eq!(open.condition, fact, "{policy}");
    }
    assert_eq!(planner.open_estimate(&plan, false).work, 4);
}

#[test]
fn native_effort_follows_cost_minimizing_support_not_independent_minimum() {
    let mut task = task();
    task.operators
        .push(operator("expensive-direct-p", vec![], 2, 2));
    let planner = Planner::new(&task);
    assert_eq!(
        (
            planner.base_relaxed.cost[2][1],
            planner.base_relaxed.work[2][1]
        ),
        (1.0, 3)
    );
    drop(planner);
    task.operators.swap(0, 2);
    let planner = Planner::new(&task);
    assert_eq!(
        (
            planner.base_relaxed.cost[2][1],
            planner.base_relaxed.work[2][1]
        ),
        (1.0, 3)
    );
    drop(planner);
    task.operators.swap(0, 2);
    task.operators[2].cost = 1;
    let planner = Planner::new(&task);
    assert_eq!(
        (
            planner.base_relaxed.cost[2][1],
            planner.base_relaxed.work[2][1]
        ),
        (1.0, 1)
    );
    // Work's tie breaker does not silently change RELAX's existing tie policy.
    assert_eq!(planner.base_relaxed.achiever[2][1].unwrap().operator, 0);
}

#[test]
fn native_reused_support_still_costs_one_link_and_keeps_preconditions() {
    let task = task();
    let planner = Planner::new(&task);
    let mut plan = PartialPlan::initial(&task);
    plan.push_step(Step { id: 1, operator: 0 });
    for condition in task.operators[0].preconditions() {
        plan.push_open(OpenCondition {
            consumer: 1,
            condition,
        });
    }
    let reused = planner.relaxed_values(&plan, true);
    assert_eq!((reused.cost[2][1], reused.work[2][1]), (0.0, 1));
    assert_eq!(planner.open_estimate(&plan, true).work, 4);
}

#[test]
fn derived_support_effort_counts_its_expansion_and_base_links() {
    let mut task = task();
    task.operators.clear();
    task.initial[2] = 1; // The last value is the derived variable's default.
    task.goals = vec![Fact::new(2, 0)];
    task.axioms = vec![crate::fdr::Axiom {
        conditions: vec![Fact::new(0, 1), Fact::new(1, 1)],
        variable: 2,
        pre: 1,
        post: 0,
    }];
    let planner = Planner::new(&task);
    assert_eq!(
        (
            planner.base_relaxed.cost[2][0],
            planner.base_relaxed.work[2][0]
        ),
        (0.0, 3)
    );
}

#[test]
fn finite_effort_saturates_without_marking_reachable_goals_dead() {
    let layers = 34;
    let mut task = Task {
        variables: (0..2 * layers)
            .map(|i| variable(&format!("x{i}")))
            .collect(),
        initial: vec![0; 2 * layers],
        goals: vec![Fact::new(2 * layers - 1, 1)],
        operators: vec![],
        mutex_groups: vec![],
        axioms: vec![],
    };
    task.initial[0] = 1;
    task.initial[1] = 1;
    for layer in 1..layers {
        for target in 2 * layer..2 * layer + 2 {
            task.operators.push(operator(
                &format!("make{target}"),
                vec![Fact::new(2 * layer - 2, 1), Fact::new(2 * layer - 1, 1)],
                target,
                1,
            ));
        }
    }
    let planner = Planner::new(&task);
    let estimate = planner.open_estimate(&PartialPlan::initial(&task), false);
    assert!(estimate.cost.is_finite());
    assert_eq!(estimate.work, i32::MAX - 1);
    assert!(!planner.base_relaxed.cost[0][0].is_finite());
    assert_eq!(planner.base_relaxed.work[0][0], i32::MAX);
    let mut plan = PartialPlan::initial(&task);
    plan.push_open(OpenCondition {
        consumer: GOAL_ID,
        condition: Fact::new(2 * layers - 2, 1),
    });
    assert_eq!(planner.open_estimate(&plan, false).work, i32::MAX - 1);
    plan.push_open(OpenCondition {
        consumer: GOAL_ID,
        condition: Fact::new(0, 0),
    });
    assert_eq!(planner.open_estimate(&plan, false).work, i32::MAX);
}
