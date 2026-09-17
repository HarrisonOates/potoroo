//! Cutset-based minimality pruning (Kambhampati, IJCAI 1995, Strategy 2).
//!
//! A necessarily-spanning cutset may dominate a later possibly-spanning
//! cutset once all open conditions precede the later step. The comparison
//! includes links terminating at the later step: their conditions must remain
//! available if the intervening segment is removed.
//!
//! Require a step strictly between the endpoints and compare literals by
//! syntactic equality. With non-negative costs, removing redundant steps
//! preserves an optimal solution.

use std::rc::Rc;

use crate::chain;
use crate::flaws::OpenCondition;
use crate::formula::Literal;
use crate::orderings::{BinaryOrderings, StepTime};
use crate::plan::{Plan, GOAL_ID, INIT_ID};

/// Returns true iff `before` is necessarily before `after`.
fn necessarily_before(orderings: &BinaryOrderings, before: usize, after: usize) -> bool {
    before != after && !orderings.possibly_after(before, StepTime::AtEnd, after, StepTime::AtStart)
}

/// Returns true iff `before` could still come before `after`.
fn possibly_before(orderings: &BinaryOrderings, before: usize, after: usize) -> bool {
    orderings.possibly_before(before, StepTime::AtEnd, after, StepTime::AtStart)
}

/// Conditions of links that necessarily span `step`.
fn np_cutset(plan: &Plan, step: usize) -> Vec<Rc<Literal>> {
    chain::iter(&plan.links)
        .filter(|link| {
            link.from_id != step
                && link.to_id != step
                && necessarily_before(&plan.orderings, link.from_id, step)
                && necessarily_before(&plan.orderings, step, link.to_id)
        })
        .map(|link| link.condition.clone())
        .collect()
}

/// Conditions of links that possibly span `step`, plus those supporting it.
fn pp_cutset(plan: &Plan, step: usize) -> Vec<Rc<Literal>> {
    chain::iter(&plan.links)
        .filter(|link| {
            if link.to_id == step {
                // `step`'s own support: it must hold when `step` executes.
                return true;
            }
            link.from_id != step
                && possibly_before(&plan.orderings, link.from_id, step)
                && possibly_before(&plan.orderings, step, link.to_id)
        })
        .map(|link| link.condition.clone())
        .collect()
}

/// Whether `outer` contains every condition of `inner`, by syntactic equality.
fn dominates(outer: &[Rc<Literal>], inner: &[Rc<Literal>]) -> bool {
    inner
        .iter()
        .all(|needed| outer.iter().any(|have| have.as_ref() == needed.as_ref()))
}

/// Whether some step lies strictly between `before` and `after`.
fn step_strictly_between(plan: &Plan, before: usize, after: usize) -> bool {
    chain::iter(&plan.steps).any(|step| {
        necessarily_before(&plan.orderings, before, step.id)
            && necessarily_before(&plan.orderings, step.id, after)
    })
}

/// Whether every open condition's consumer necessarily precedes `step` —
/// condition (2), which is what stops pp-cutset(`step`) from growing again.
fn all_open_conditions_precede(plan: &Plan, step: usize, orderings: &BinaryOrderings) -> bool {
    chain::iter(&plan.open_conds).all(|oc: &OpenCondition| {
        oc.step_id == step || necessarily_before(orderings, oc.step_id, step)
    })
}

/// Whether the plan is provably non-minimal and may be discarded.
pub fn prunable(plan: &Plan) -> bool {
    // Nothing to remove without at least three real steps (two anchors and
    // something between them).
    if plan.num_steps() < 3 || plan.num_links == 0 {
        return false;
    }

    // Candidate `s″`: a real step, or the goal step. The initial step is never
    // a candidate — nothing precedes it.
    let mut candidates: Vec<usize> = chain::iter(&plan.steps).map(|step| step.id).collect();
    candidates.push(GOAL_ID);

    for &second in &candidates {
        if !all_open_conditions_precede(plan, second, &plan.orderings) {
            continue;
        }
        let inner = pp_cutset(plan, second);
        if inner.is_empty() {
            // An empty requirement is dominated by anything, which would let
            // the rule fire on plans it has learned nothing about. Decline.
            continue;
        }
        for first in chain::iter(&plan.steps) {
            if first.id == second || first.id == INIT_ID {
                continue;
            }
            if !necessarily_before(&plan.orderings, first.id, second) {
                continue;
            }
            if !step_strictly_between(plan, first.id, second) {
                continue;
            }
            if dominates(&np_cutset(plan, first.id), &inner) {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::params::Parameters;
    use crate::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
    use crate::search::SearchContext;

    /// The initial plan of any task has no steps, so the rule declines.
    #[test]
    fn declines_on_a_plan_with_too_few_steps() {
        let domain_src = std::fs::read_to_string("examples/blocks-world-domain.pddl")
            .expect("read blocks-world-domain.pddl");
        let problem_src = std::fs::read_to_string("examples/sussman-anomaly.pddl")
            .expect("read sussman-anomaly.pddl");
        let domain = match read_pddl(&domain_src).expect("parse domain") {
            ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
            _ => panic!("expected a domain"),
        };
        let problem = match read_pddl(&problem_src).expect("parse problem") {
            ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
            _ => panic!("expected a problem"),
        };
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let initial = Plan::make_initial_plan(&ctx).expect("an initial plan exists");
        assert!(!prunable(&initial));
    }
}
