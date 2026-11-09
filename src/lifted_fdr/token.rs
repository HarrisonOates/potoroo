//! Value-token deficits for lifted FDR plans (the ground planner's `TADD`,
//! `src/token.rs` on `investigate/relax-vs-add`, lifted).
//!
//! A step that requires `v(t̄) = a` and overwrites `v(t̄)` ends one segment of
//! value `a`; no other step can end the same segment. So in any completion,
//! per fact, `destroyers + [goal] <= [init] + producers`. A shortfall among
//! committed steps must be met by new producers, each costing at least the
//! cheapest achiever.
//!
//! Lifted facts may differ only by unbound terms, so per-fact counts become a
//! matching: each destroyer (and competing goal) needs a distinct supply, an
//! initial value or a committed write that may unify with it and may precede
//! it. Destroyers left unmatched by a maximum matching need new producers in
//! every completion (orderings, bindings and other variables relaxed).

use super::binds::{LBindings, Resolved};
use super::plan::{Ctx, Plan, GOAL_ID};
use super::task::{LFact, LValue, LiftedTask};

/// `part` for a `none` value.
const NONE: u16 = u16::MAX;

/// Static per-task tables.
pub struct Tokens {
    /// Per schema: `(condition, assignment)` pairs where the step requires a
    /// value of an instance it overwrites (same variable, same instance terms).
    destroys: Vec<Vec<(usize, usize)>>,
    /// Cheapest schema writing each `(variable, part)`.
    repro: crate::fasthash::FastMap<(u32, u16), f32>,
}

#[derive(PartialEq)]
struct Key {
    var: u32,
    inv: Vec<Resolved>,
    part: u16,
    args: Vec<Resolved>,
}

fn key(b: &LBindings, f: &LFact, step: usize) -> Key {
    let (part, args) = match &f.value {
        LValue::None => (NONE, Vec::new()),
        LValue::Part { part, args } => (*part, args.iter().map(|t| b.resolve(*t, step)).collect()),
    };
    Key {
        var: f.var,
        inv: f.inv.iter().map(|t| b.resolve(*t, step)).collect(),
        part,
        args,
    }
}

fn can_equal(b: &LBindings, x: Resolved, y: Resolved) -> bool {
    match (x, y) {
        (Resolved::Object(a), Resolved::Object(c)) => a == c,
        (Resolved::Object(o), Resolved::Class(k)) | (Resolved::Class(k), Resolved::Object(o)) => b.domain(k).contains(o),
        (Resolved::Class(a), Resolved::Class(c)) => {
            a == c || (!b.distinct(a).contains(&c) && b.domain(a).intersects(b.domain(c)))
        }
    }
}

fn may_unify(b: &LBindings, k: &Key, other: &Key) -> bool {
    k.var == other.var
        && k.part == other.part
        && k.inv.iter().zip(&other.inv).all(|(x, y)| can_equal(b, *x, *y))
        && k.args.iter().zip(&other.args).all(|(x, y)| can_equal(b, *x, *y))
}

impl Tokens {
    pub fn new(task: &LiftedTask) -> Tokens {
        let mut destroys = Vec::with_capacity(task.schemas.len());
        let mut repro: crate::fasthash::FastMap<(u32, u16), f32> = Default::default();
        for schema in &task.schemas {
            let mut pairs = Vec::new();
            for (ci, c) in schema.conditions.iter().enumerate() {
                for (ai, a) in schema.assigns.iter().enumerate() {
                    if a.fact.var == c.var && a.fact.inv == c.inv && a.fact.value != c.value {
                        pairs.push((ci, ai));
                    }
                }
            }
            destroys.push(pairs);
            for a in &schema.assigns {
                let part = match &a.fact.value {
                    LValue::None => NONE,
                    LValue::Part { part, .. } => *part,
                };
                let cost = schema.cost as f32;
                let slot = repro.entry((a.fact.var, part)).or_insert(f32::INFINITY);
                if cost < *slot {
                    *slot = cost;
                }
            }
        }
        Tokens { destroys, repro }
    }

    /// Reproduction cost of the destroyers (and goals) that no distinct
    /// supply can serve, or infinity when one has no achiever. Each needs its
    /// own segment: an initial value or a producer's write that may unify
    /// with it and may precede it. The shortfall is their number minus a
    /// maximum matching to supplies. `charged` are the open conditions ADD
    /// already prices with a new producer, as `(consumer, condition)`.
    pub fn deficit(&self, ctx: &Ctx, plan: &Plan, charged: &[(usize, u16)]) -> f32 {
        let b = &plan.bindings;
        // Demands: (key, consumer step).
        let mut demands: Vec<(Key, usize)> = Vec::new();
        for s in 1..=plan.num_steps() {
            let index = plan.steps[s - 1] as usize;
            let schema = &ctx.task.schemas[index];
            for &(ci, ai) in &self.destroys[index] {
                let cond = &schema.conditions[ci];
                if cond.value == LValue::None
                    || charged.iter().any(|&(c, k)| c == s && k as usize == ci)
                {
                    continue;
                }
                let k = key(b, cond, s);
                // A write certainly equal to the required value ends nothing.
                if key(b, &schema.assigns[ai].fact, s) == k {
                    continue;
                }
                demands.push((k, s));
            }
        }
        if demands.is_empty() {
            return 0.0;
        }
        // Goals on a demanded variable compete for the same segments.
        for (gi, g) in ctx.task.goal.iter().enumerate() {
            if g.value == LValue::None
                || !demands.iter().any(|(k, _)| k.var == g.var)
                || charged.iter().any(|&(c, k)| c == GOAL_ID && k as usize == gi)
            {
                continue;
            }
            demands.push((key(b, g, GOAL_ID), GOAL_ID));
        }
        // Supplies: (key, producer step or 0 for the initial state).
        let mut supplies: Vec<(Key, usize)> = Vec::new();
        let vars: Vec<u32> = {
            let mut v: Vec<u32> = demands.iter().map(|(k, _)| k.var).collect();
            v.sort_unstable();
            v.dedup();
            v
        };
        for &var in &vars {
            for (inv, value) in ctx.init_by_var.get(&var).map(|v| v.as_slice()).unwrap_or(&[]) {
                if let LValue::Part { part, args } = value {
                    supplies.push((
                        Key {
                            var,
                            inv: inv.iter().map(|o| Resolved::Object(*o)).collect(),
                            part: *part,
                            args: args.iter().map(|t| Resolved::Object(t.as_object())).collect(),
                        },
                        super::plan::INIT_ID,
                    ));
                }
            }
        }
        for s in 1..=plan.num_steps() {
            for a in &ctx.schema_of(plan, s).assigns {
                if a.fact.value != LValue::None && vars.binary_search(&a.fact.var).is_ok() {
                    supplies.push((key(b, &a.fact, s), s));
                }
            }
        }
        // Edges (supplies indexed by variable and value part), then Kuhn's
        // augmenting paths.
        // Bucketed by variable, value part and first instance object (`None`
        // when unbound or absent): a demand bound there scans its bucket and
        // the unbound one; an unbound demand scans every bucket of its value.
        type Bucket = (u32, u16, Option<crate::terms::Object>);
        let first = |k: &Key| match k.inv.first() {
            Some(Resolved::Object(o)) => Some(*o),
            _ => None,
        };
        let mut by_value: crate::fasthash::FastMap<Bucket, Vec<usize>> = Default::default();
        let mut by_part: crate::fasthash::FastMap<(u32, u16), Vec<usize>> = Default::default();
        for (j, (k, _)) in supplies.iter().enumerate() {
            by_value.entry((k.var, k.part, first(k))).or_default().push(j);
            by_part.entry((k.var, k.part)).or_default().push(j);
        }
        let empty: Vec<usize> = Vec::new();
        let edges: Vec<Vec<usize>> = demands
            .iter()
            .map(|(d, consumer)| {
                let candidates: Box<dyn Iterator<Item = usize>> = match first(d) {
                    Some(o) => Box::new(
                        by_value
                            .get(&(d.var, d.part, Some(o)))
                            .unwrap_or(&empty)
                            .iter()
                            .chain(by_value.get(&(d.var, d.part, None)).unwrap_or(&empty))
                            .copied(),
                    ),
                    None => Box::new(by_part.get(&(d.var, d.part)).unwrap_or(&empty).iter().copied()),
                };
                candidates
                    .filter(|&j| {
                        let (k, producer) = &supplies[j];
                        *producer != *consumer
                            && may_unify(b, d, k)
                            && (*producer == super::plan::INIT_ID
                                || plan.orderings.possibly_before(
                                    *producer,
                                    crate::orderings::StepTime::AtEnd,
                                    *consumer,
                                    crate::orderings::StepTime::AtStart,
                                ))
                    })
                    .collect()
            })
            .collect();
        let mut owner: Vec<Option<usize>> = vec![None; supplies.len()];
        fn augment(i: usize, edges: &[Vec<usize>], owner: &mut [Option<usize>], seen: &mut [bool]) -> bool {
            for &j in &edges[i] {
                if seen[j] {
                    continue;
                }
                seen[j] = true;
                if owner[j].is_none_or(|o| augment(o, edges, owner, seen)) {
                    owner[j] = Some(i);
                    return true;
                }
            }
            false
        }
        let mut total = 0.0;
        let mut seen = vec![false; supplies.len()];
        for i in 0..demands.len() {
            seen.iter_mut().for_each(|x| *x = false);
            if !augment(i, &edges, &mut owner, &mut seen) {
                let k = &demands[i].0;
                let cost = self.repro.get(&(k.var, k.part)).copied().unwrap_or(f32::INFINITY);
                if !cost.is_finite() {
                    return f32::INFINITY;
                }
                total += cost;
            }
        }
        total
    }
}
