//! Independent POCL plan-validity checker.
//!
//! Implements Definition 1 of the position paper ("Reviving POCL Planning"): a
//! complete plan is a *solution* iff every precondition is supported by a causal
//! link and there are no unresolved causal threats. This module deliberately
//! **recomputes** both invariants from the plan's steps, links, orderings, and
//! bindings rather than trusting the planner's own `open_conds`/`unsafes`
//! bookkeeping — it is the correctness oracle for heuristics that cannot be
//! differentially checked against the reference (which lacks them).
//!
//! Historically the dangerous bug class in this port was *invalid, too-short
//! plans emitted silently as solutions* (e.g. the quantified-effect threat bug),
//! because the `debug_assert` guarding plan construction is compiled out in
//! release. Recomputing threats here catches exactly that class.

use crate::chain;
use crate::formula::Literal;
use crate::orderings::StepTime;
use crate::plan::{Link, Plan, Step, INIT_ID};
use crate::search::SearchContext;

/// Checks that `plan` is a valid POCL solution. Returns `Ok(())` if so, or
/// `Err(reason)` describing the first violation found.
///
/// Three independent checks:
/// 1. No open conditions remain (every precondition is closed by a link).
/// 2. Each causal link is *supported*: its producer step has an effect whose
///    literal unifies with the link condition under the plan's bindings.
/// 3. Each causal link is *unthreatened*: no step with a clobbering effect can be
///    ordered into the protected interval (recomputed, not read from `unsafes`).
pub fn is_valid_solution(plan: &Plan, ctx: &SearchContext) -> Result<(), String> {
    // (1) No open conditions.
    if plan.num_open_conds != 0 || plan.open_conds.is_some() {
        return Err(format!(
            "plan has {} open condition(s); not a complete solution",
            plan.num_open_conds
        ));
    }

    // (2) Every causal link is supported by an effect of its producer.
    for link in chain::iter(&plan.links) {
        if !link_supported(plan, ctx, &link) {
            return Err(format!(
                "causal link {} --{:?}--> {} is unsupported: producer has no effect \
                 unifying with the link condition",
                link.from_id, link.condition, link.to_id
            ));
        }
    }

    // (3) No causal link is threatened.
    for link in chain::iter(&plan.links) {
        if let Some(threat_id) = link_threatened_by(plan, ctx, &link) {
            return Err(format!(
                "causal link {} --{:?}--> {} is threatened by step {}",
                link.from_id, link.condition, link.to_id, threat_id
            ));
        }
    }

    Ok(())
}

fn find_step(plan: &Plan, id: usize) -> Option<Step> {
    chain::iter(&plan.steps).find(|s| s.id == id).cloned()
}

/// Whether the producer of `link` has an effect whose literal positively unifies
/// with the link's protected condition under the plan's bindings.
///
/// A negative link from `INIT_ID` is a separate case: [`Plan::new_cw_link`]
/// supports a negative open condition by the *absence* of a matching init
/// atom under the closed-world assumption, protected by the inequality goals
/// it adds rather than by any actual init effect -- init's effects are always
/// positive, so `unify` below can never match a negative link condition
/// against one (it requires matching polarity), and every task relying on
/// this (e.g. any domain with `:negative-preconditions` whose negated
/// preconditions are never explicitly asserted false) would otherwise be
/// reported unsupported.
fn link_supported(plan: &Plan, ctx: &SearchContext, link: &Link) -> bool {
    let Some(producer) = find_step(plan, link.from_id) else {
        return false;
    };
    let type_ctx = ctx.type_ctx();
    if link.from_id == INIT_ID && link.condition.negative() {
        let atom = Literal::Atom(link.condition.atom().clone());
        return producer.action.effects.iter().all(|e| {
            !plan
                .bindings
                .unify(&type_ctx, &e.literal, link.from_id, &atom, link.to_id)
        });
    }
    producer.action.effects.iter().any(|e| {
        plan.bindings
            .unify(&type_ctx, &e.literal, link.from_id, &link.condition, link.to_id)
    })
}

/// Recomputes whether any step threatens `link`, returning the threatening step
/// id if so. Reports rather than records, and does not consult the plan's stored
/// `unsafes`.
fn link_threatened_by(plan: &Plan, ctx: &SearchContext, link: &Link) -> Option<usize> {
    let orderings = &plan.orderings;
    let bindings = &plan.bindings;
    let type_ctx = ctx.type_ctx();
    let lt1 = link.effect_time;
    let lt2 = link.condition_time.end_time();

    for s in chain::iter(&plan.steps) {
        // Cheap window prune: the step must be orderable strictly between the
        // link's producer and consumer.
        if !(orderings.possibly_not_after(link.from_id, lt1, s.id, StepTime::AtEnd)
            && orderings.possibly_not_before(link.to_id, lt2, s.id, StepTime::AtStart))
        {
            continue;
        }
        for e in s.action.effects.iter() {
            // A contradictory link condition means the effect can never fire in a
            // way that clobbers, so it is not a real threat.
            if e.link_condition.contradiction() {
                continue;
            }
            let et = StepTime::AtEnd;
            if (s.id != link.to_id)
                && orderings.possibly_not_after(link.from_id, lt1, s.id, et)
                && orderings.possibly_not_before(link.to_id, lt2, s.id, et)
            {
                let neg_condition = link.condition.negative();
                if (neg_condition || (link.from_id != s.id))
                    && bindings.affects(&type_ctx, &e.literal, s.id, &link.condition, link.to_id)
                {
                    return Some(s.id);
                }
            }
        }
    }
    None
}
