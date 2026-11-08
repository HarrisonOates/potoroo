//! Flaw selection for lifted FDR plans, interpreting Potoroo's flaw-order
//! language (`{n,s,o,l,t,u}[max]ORDER`, VHPOP's notation) as the ground FDR
//! planner does.
//!
//! A threat is separable (`{s}`) unless it is definite: when separation or
//! agreement could still remove it. Refinements are counted as in VHPOP:
//! separation is one refinement. Open conditions count consistent supporters
//! (initial facts, existing steps, schema achievers; Pollack, Joslin &
//! Paolucci's I + S + N), stopping once the criterion's bound is exceeded.
//! There are no static open conditions: static atoms are binding
//! constraints, propagated when steps are linked.

use crate::chain;
use crate::heuristics::{FlawSelectionOrder, OrderType, SelectionCriterion};

use super::heuristic::Estimator;
use super::plan::{count_refinements, count_threat_options, definite, only_new_step, unsafe_open, Ctx, Open, Plan, Threat};

pub enum Flaw {
    Threat(Threat),
    Open(Open),
    /// A threat with no resolution: the plan has no completion.
    Dead,
}

struct Candidate {
    flaw: Flaw,
    is_threat: bool,
    refinements: usize,
    recency: usize,
    has_new: bool,
    estimate: f32,
}

pub fn select(ctx: &Ctx, plan: &Plan, order: &FlawSelectionOrder, estimator: &Estimator) -> Flaw {
    let threats: Vec<Threat> = chain::iter(&plan.threats).copied().collect();
    let mut threat_counts: Vec<Option<Option<usize>>> = vec![None; threats.len()];
    let opens: Vec<Open> = chain::iter(&plan.opens).copied().collect();
    let local_consumer = opens.first().map(|o| o.consumer);
    for criterion in order.criteria() {
        let mut candidates = Vec::new();
        if criterion.non_separable || criterion.separable {
            for (position, threat) in threats.iter().enumerate() {
                let count = *threat_counts[position].get_or_insert_with(|| count_threat_options(ctx, plan, threat));
                let Some(refinements) = count else {
                    // No longer a threat: dropping it is free.
                    return Flaw::Threat(*threat);
                };
                if refinements == 0 {
                    return Flaw::Dead;
                }
                let separable = !definite(ctx, plan, threat);
                let applies = (criterion.non_separable && criterion.separable)
                    || (criterion.separable && separable)
                    || (criterion.non_separable && !separable);
                if applies && refinements as i64 <= criterion.max_refinements as i64 {
                    candidates.push(Candidate {
                        flaw: Flaw::Threat(*threat),
                        is_threat: true,
                        refinements,
                        recency: threats.len() - 1 - position,
                        has_new: false,
                        estimate: 0.0,
                    });
                }
            }
        }
        for (position, open) in opens.iter().enumerate() {
            if !open_matches(ctx, plan, criterion, *open, local_consumer) {
                continue;
            }
            let refinements = if matches!(criterion.order, OrderType::Lr | OrderType::Mr) {
                count_refinements(ctx, plan, *open, usize::MAX)
            } else if criterion.max_refinements < i32::MAX {
                count_refinements(ctx, plan, *open, criterion.max_refinements as usize + 1)
            } else {
                0
            };
            if refinements as i64 > criterion.max_refinements as i64 {
                continue;
            }
            let has_new = criterion.order == OrderType::New && only_new_step(ctx, plan, *open);
            let estimate = match criterion.order {
                OrderType::Lc | OrderType::Mc => estimator.open_value(ctx, plan, *open).add_cost(),
                OrderType::Lw | OrderType::Mw => estimator.open_value(ctx, plan, *open).add_work() as f32,
                _ => 0.0,
            };
            candidates.push(Candidate {
                flaw: Flaw::Open(*open),
                is_threat: false,
                refinements,
                recency: opens.len() - 1 - position,
                has_new,
                estimate,
            });
        }
        if let Some(candidate) = choose(candidates, criterion.order) {
            return candidate.flaw;
        }
    }
    // Every criterion passed over the remaining flaws: take the newest.
    match (threats.first(), opens.first()) {
        (Some(t), _) => Flaw::Threat(*t),
        (None, Some(o)) => Flaw::Open(*o),
        (None, None) => unreachable!("an incomplete plan has a flaw"),
    }
}

fn open_matches(
    ctx: &Ctx,
    plan: &Plan,
    criterion: &SelectionCriterion,
    open: Open,
    local_consumer: Option<usize>,
) -> bool {
    criterion.open_cond
        || (criterion.local_open_cond && Some(open.consumer) == local_consumer)
        || (criterion.unsafe_open_cond && unsafe_open(ctx, plan, open))
}

/// The ground FDR planner's candidate preference (`choose_candidate`).
fn choose(candidates: Vec<Candidate>, order: OrderType) -> Option<Candidate> {
    let prefer = |l: &Candidate, r: &Candidate| match order {
        OrderType::Lifo | OrderType::Random => (l.is_threat, l.recency) > (r.is_threat, r.recency),
        OrderType::Fifo => {
            if l.is_threat != r.is_threat {
                !l.is_threat
            } else {
                l.recency < r.recency
            }
        }
        OrderType::Lr => {
            l.refinements < r.refinements
                || (l.refinements == r.refinements && (l.is_threat, l.recency) > (r.is_threat, r.recency))
        }
        OrderType::Mr => {
            l.refinements > r.refinements
                || (l.refinements == r.refinements && (l.is_threat, l.recency) > (r.is_threat, r.recency))
        }
        OrderType::New => (l.has_new, l.recency) > (r.has_new, r.recency),
        OrderType::Reuse => (!l.has_new, l.recency) > (!r.has_new, r.recency),
        OrderType::Lc | OrderType::Lw => {
            l.estimate < r.estimate || (l.estimate == r.estimate && l.recency > r.recency)
        }
        OrderType::Mc | OrderType::Mw => {
            l.estimate > r.estimate || (l.estimate == r.estimate && l.recency > r.recency)
        }
    };
    let mut selected: Option<Candidate> = None;
    for candidate in candidates {
        if selected.as_ref().is_none_or(|current| prefer(&candidate, current)) {
            selected = Some(candidate);
        }
    }
    selected
}
