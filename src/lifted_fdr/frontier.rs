//! Frontier dominance: a plan-space counterpart of a state-space closed list.
//!
//! Split a plan into a frontier `F` (every open condition's consumer, the
//! steps before them, and any step not ordered after all of these) and a
//! settled part `U` (the rest), where every `F` step necessarily precedes
//! every `U` step. Every future step is ordered before some open condition's
//! consumer, so before all of `U`. From then on `U` is fixed: no new link
//! leaves or enters it, and no future step falls inside a `U` link.
//! Everything the completions of the frontier depend on is the frontier itself
//! plus the conditions the interface links carry into `U` (links from `F` or
//! the initial state to `U` or the goal), which future frontier steps must not
//! threaten.
//!
//! Two plans whose frontiers are identical (up to renaming steps and binding
//! classes) therefore have the same frontier completions, except that one
//! needing fewer interface conditions admits every completion of the other.
//! A plan is dominated by an earlier-expanded one with an identical frontier,
//! a subset of its interface, and no greater cost. Its completions are no
//! cheaper than ones under the earlier plan, so the earlier plan's subtree
//! suffices. This catches transpositions: settled parts built in different
//! orders that leave the same regressed requirement.
//!
//! Binding classes may couple the two parts through static relations, so a
//! key is formed only when no class appears in both `F` and `U` and no `F`
//! class is constrained distinct from a class outside `F`; interface
//! conditions are then ground.

use crate::fasthash::FastMap;
use crate::orderings::{BinaryOrderings, StepTime};
use crate::terms::{Term, Variable};

use super::binds::{ClassId, Resolved};
use super::plan::{Ctx, Plan, GOAL_ID, INIT_ID};
use super::task::LValue;

fn necessarily_before(orderings: &BinaryOrderings, before: usize, after: usize) -> bool {
    before != after && !orderings.possibly_after(before, StepTime::AtEnd, after, StepTime::AtStart)
}

/// Why a plan has no frontier key, for diagnostics.
#[derive(Debug, Clone, Copy)]
pub enum NoKey {
    Threats,
    GoalOpen,
    NothingSettled,
    SharedClass,
    Distinct,
}

pub struct Key {
    frontier: Vec<u32>,
    interface: Vec<u32>,
}

/// The plan's frontier key, if it has a clean split.
pub fn key(ctx: &Ctx, plan: &Plan) -> Result<Key, NoKey> {
    let n = plan.num_steps();
    let orderings = &plan.orderings;
    let mut in_f = vec![false; n + 1];
    for open in crate::chain::iter(&plan.opens) {
        let c = open.consumer();
        if c == GOAL_ID {
            return Err(NoKey::GoalOpen);
        }
        in_f[c] = true;
    }
    // Close under predecessors, then pull in any step not after all of `F`.
    loop {
        let mut changed = false;
        for t in 1..=n {
            if in_f[t] {
                continue;
            }
            let before_some = (1..=n).any(|p| in_f[p] && necessarily_before(orderings, t, p));
            let after_all = (1..=n).all(|p| !in_f[p] || necessarily_before(orderings, p, t));
            if before_some || !after_all {
                in_f[t] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    if (1..=n).all(|t| in_f[t]) {
        return Err(NoKey::NothingSettled);
    }
    let b = &plan.bindings;
    let classes_of = |s: usize| {
        let schema = ctx.schema_of(plan, s);
        (0..schema.var_count).filter_map(move |i| match b.resolve(Term::Variable(Variable(schema.var_base + i)), s) {
            Resolved::Class(k) => Some(k),
            Resolved::Object(_) => None,
        })
    };
    let mut f_classes: Vec<ClassId> = (1..=n).filter(|&s| in_f[s]).flat_map(classes_of).collect();
    f_classes.sort_unstable();
    f_classes.dedup();
    for s in (1..=n).filter(|&s| !in_f[s]) {
        if classes_of(s).any(|k| f_classes.binary_search(&k).is_ok()) {
            return Err(NoKey::SharedClass);
        }
    }
    for &k in &f_classes {
        if b.distinct(k).iter().any(|&d| f_classes.binary_search(&b.representative(d)).is_err()) {
            return Err(NoKey::Distinct);
        }
    }
    // Canonical step order: schema, then arguments with classes as wildcards,
    // then step id (a tie may miss a match, never make a false one).
    const VAR: u32 = u32::MAX;
    let args = |s: usize| -> Vec<u32> {
        let schema = ctx.schema_of(plan, s);
        (0..schema.var_count)
            .map(|i| match b.resolve(Term::Variable(Variable(schema.var_base + i)), s) {
                Resolved::Object(o) => o.0,
                Resolved::Class(_) => VAR,
            })
            .collect()
    };
    let mut steps: Vec<(u32, Vec<u32>, usize)> =
        (1..=n).filter(|&s| in_f[s]).map(|s| (plan.steps[s - 1], args(s), s)).collect();
    steps.sort_unstable();
    let mut index = vec![u32::MAX; n + 1];
    for (i, (_, _, s)) in steps.iter().enumerate() {
        index[*s] = i as u32 + 1;
    }
    let step_index = |s: usize| if s == INIT_ID { 0 } else { index[s] };
    let mut rename: FastMap<ClassId, u32> = Default::default();
    let mut frontier = vec![steps.len() as u32];
    for (schema_index, _, s) in &steps {
        frontier.push(*schema_index);
        let schema = ctx.schema_of(plan, *s);
        for i in 0..schema.var_count {
            frontier.push(match b.resolve(Term::Variable(Variable(schema.var_base + i)), *s) {
                Resolved::Object(o) => o.0,
                Resolved::Class(k) => {
                    let next = rename.len() as u32;
                    VAR - 1 - *rename.entry(k).or_insert(next)
                }
            });
        }
    }
    // Orderings among frontier steps.
    for (_, _, s) in &steps {
        let mut word = 0u32;
        for (j, (_, _, t)) in steps.iter().enumerate() {
            if necessarily_before(orderings, *s, *t) {
                word |= 1 << (j % 32);
            }
            if j % 32 == 31 || j + 1 == steps.len() {
                frontier.push(word);
                word = 0;
            }
        }
    }
    // Class domains and distinctness, in renaming order.
    let mut renamed: Vec<(u32, ClassId)> = rename.iter().map(|(&k, &i)| (i, k)).collect();
    renamed.sort_unstable();
    for (_, k) in &renamed {
        let domain: Vec<u32> = b.domain(*k).iter().map(|o| o.0).collect();
        frontier.push(domain.len() as u32);
        frontier.extend(domain);
        let mut distinct: Vec<u32> = b.distinct(*k).iter().map(|d| rename[&b.representative(*d)]).collect();
        distinct.sort_unstable();
        distinct.dedup();
        frontier.push(distinct.len() as u32);
        frontier.extend(distinct);
    }
    // Links into frontier steps, and open conditions.
    let mut inner: Vec<[u32; 4]> = Vec::new();
    let mut interface: Vec<Vec<u32>> = Vec::new();
    for link in crate::chain::iter(&plan.links) {
        let (p, c) = (link.producer(), link.consumer());
        if c != GOAL_ID && in_f[c] {
            inner.push([step_index(p), index[c], link.cond as u32, link.assign as u32]);
        } else if p == INIT_ID || (p != GOAL_ID && in_f[p]) {
            let fact = ctx.condition(plan, c, link.cond);
            let mut row = vec![step_index(p), fact.var];
            let mut bound = true;
            let mut push = |t: &Term| match b.resolve(*t, c) {
                Resolved::Object(o) => row.push(o.0),
                Resolved::Class(_) => bound = false,
            };
            fact.inv.iter().for_each(&mut push);
            match &fact.value {
                LValue::None => push(&Term::Object(crate::terms::Object(VAR))),
                LValue::Part { part, args } => {
                    push(&Term::Object(crate::terms::Object(*part as u32)));
                    args.iter().for_each(&mut push);
                }
            }
            if !bound {
                // Only a goal with free variables gets here.
                return Err(NoKey::SharedClass);
            }
            interface.push(row);
        }
    }
    // Threats: a frontier step against a link into the frontier or the
    // interface (no other pair can threaten).
    let mut threats: Vec<Vec<u32>> = Vec::new();
    for t in crate::chain::iter(&plan.threats) {
        let (s, link) = (t.step(), t.link);
        if s == GOAL_ID || s == INIT_ID || !in_f[s] {
            return Err(NoKey::Threats);
        }
        let (p, c) = (link.producer(), link.consumer());
        let mut row = vec![index[s], t.assign as u32, step_index(p), link.cond as u32];
        if c != GOAL_ID && in_f[c] {
            row.push(index[c]);
        } else {
            // A settled consumer is named by the condition it needs.
            row.push(u32::MAX);
            let fact = ctx.condition(plan, c, link.cond);
            row.push(fact.var);
            for t in fact.inv.iter().chain(match &fact.value {
                LValue::None => [].iter(),
                LValue::Part { args, .. } => args.iter(),
            }) {
                match b.resolve(*t, c) {
                    Resolved::Object(o) => row.push(o.0),
                    Resolved::Class(_) => return Err(NoKey::SharedClass),
                }
            }
        }
        threats.push(row);
    }
    threats.sort_unstable();
    frontier.push(threats.len() as u32);
    for row in threats {
        frontier.push(row.len() as u32);
        frontier.extend(row);
    }
    inner.sort_unstable();
    frontier.push(inner.len() as u32);
    frontier.extend(inner.into_iter().flatten());
    let mut opens: Vec<[u32; 2]> =
        crate::chain::iter(&plan.opens).map(|o| [index[o.consumer()], o.cond as u32]).collect();
    opens.sort_unstable();
    frontier.extend(opens.into_iter().flatten());
    interface.sort_unstable();
    interface.dedup();
    let mut flat = Vec::new();
    for row in interface {
        flat.push(row.len() as u32);
        flat.extend(row);
    }
    Ok(Key { frontier, interface: flat })
}

fn rows(flat: &[u32]) -> Vec<&[u32]> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < flat.len() {
        let len = flat[i] as usize;
        out.push(&flat[i + 1..i + 1 + len]);
        i += 1 + len;
    }
    out
}

/// Frontiers of expanded plans with their interfaces and costs.
#[derive(Default)]
pub struct Closed {
    table: FastMap<Vec<u32>, Vec<(Vec<u32>, usize)>>,
    pub entries: usize,
}

impl Closed {
    /// Whether an expanded plan dominates one with `key` and `cost`; if not,
    /// records it.
    pub fn dominated_or_insert(&mut self, key: Key, cost: usize) -> bool {
        let list = self.table.entry(key.frontier).or_default();
        let mine = rows(&key.interface);
        let dominated = list.iter().any(|(interface, c)| {
            *c <= cost && rows(interface).iter().all(|r| mine.contains(r))
        });
        if !dominated {
            list.push((key.interface, cost));
            self.entries += 1;
        }
        dominated
    }
}
