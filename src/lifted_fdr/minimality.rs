//! Cutset-based minimality pruning (Kambhampati, IJCAI 1995, Strategy 2) for
//! lifted FDR plans, with the paper's cutsets.
//!
//! The np-cutset of a step `s′` is its out-links and the links necessarily
//! spanning it; the pp-cutset of `s″` is its out-links and the links possibly
//! spanning it. A plan is discarded when a real step `s′` necessarily precedes
//! a real step `s″`, every open condition's consumer is `s″` or necessarily
//! precedes it, and every pp-cutset(`s″`) condition necessarily codesignates
//! with some np-cutset(`s′`) condition.
//!
//! Soundness: in any linearization of a completion, the steps after `s′` up to
//! and including `s″` can be removed. Every value they give past `s″` is a
//! pp-cutset condition, which a link spanning the point just after `s′`
//! already carries; the link from the removed producer protected it from
//! there to its consumer, so it still holds. Removing steps adds no threats
//! and relaxes bindings, so a completion of a pruned plan is never minimal.
//! The comparison persists under refinement: np-cutsets only grow (links and
//! orderings are only added); new links only support open conditions, which
//! are at or before `s″`, so they neither leave `s″` nor span it, and
//! pp-cutsets only shrink; and terms that resolve alike (the same object or
//! binding class) stay codesignated as bindings are added.

use crate::orderings::{BinaryOrderings, StepTime};

use super::binds::Resolved;
use super::plan::{Ctx, Link, Plan};
use super::task::LValue;

fn necessarily_before(orderings: &BinaryOrderings, before: usize, after: usize) -> bool {
    before != after && !orderings.possibly_after(before, StepTime::AtEnd, after, StepTime::AtStart)
}

fn possibly_before(orderings: &BinaryOrderings, before: usize, after: usize) -> bool {
    orderings.possibly_before(before, StepTime::AtEnd, after, StepTime::AtStart)
}

/// A link condition under the plan's bindings: equal keys necessarily
/// codesignate.
#[derive(PartialEq)]
struct Key {
    var: u32,
    part: Option<u16>,
    terms: Vec<Resolved>,
}

fn key(ctx: &Ctx, plan: &Plan, link: &Link) -> Key {
    let consumer = link.consumer();
    let fact = ctx.condition(plan, consumer, link.cond);
    let b = &plan.bindings;
    let mut terms: Vec<Resolved> = fact.inv.iter().map(|t| b.resolve(*t, consumer)).collect();
    let part = match &fact.value {
        LValue::None => None,
        LValue::Part { part, args } => {
            terms.extend(args.iter().map(|t| b.resolve(*t, consumer)));
            Some(*part)
        }
    };
    Key { var: fact.var, part, terms }
}

/// Whether the plan is provably non-minimal and may be discarded.
pub fn prunable(ctx: &Ctx, plan: &Plan) -> bool {
    let n = plan.num_steps();
    if n < 2 || plan.links.is_none() {
        return false;
    }
    let orderings = &plan.orderings;
    let links: Vec<Link> = crate::chain::iter(&plan.links).copied().collect();
    let opens: Vec<usize> = crate::chain::iter(&plan.opens).map(|o| o.consumer()).collect();
    let mut keys: Vec<Option<Key>> = (0..links.len()).map(|_| None).collect();
    let mut np: Vec<Option<Vec<usize>>> = vec![None; n + 1];
    for second in 1..=n {
        if !opens.iter().all(|&c| c == second || necessarily_before(orderings, c, second)) {
            continue;
        }
        let pp: Vec<usize> = (0..links.len())
            .filter(|&i| {
                let link = &links[i];
                link.producer() == second
                    || (link.consumer() != second
                        && possibly_before(orderings, link.producer(), second)
                        && possibly_before(orderings, second, link.consumer()))
            })
            .collect();
        for first in 1..=n {
            if !necessarily_before(orderings, first, second) {
                continue;
            }
            let np = np[first].get_or_insert_with(|| {
                (0..links.len())
                    .filter(|&i| {
                        let link = &links[i];
                        link.producer() == first
                            || (link.consumer() != first
                                && necessarily_before(orderings, link.producer(), first)
                                && necessarily_before(orderings, first, link.consumer()))
                    })
                    .collect()
            });
            for &i in np.iter().chain(&pp) {
                if keys[i].is_none() {
                    keys[i] = Some(key(ctx, plan, &links[i]));
                }
            }
            if pp.iter().all(|&i| np.iter().any(|&j| i == j || keys[i] == keys[j])) {
                return true;
            }
        }
    }
    false
}
