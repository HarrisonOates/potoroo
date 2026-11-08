//! Lifted FDR partial plans and their refinement.
//!
//! A step is a schema whose variables are scoped by the step id in the shared
//! [`Bindings`]. A causal link protects the consumer's condition `G(t̄)=y`
//! from its producer to its consumer. Step `w` with assignment `G(ū):=x`
//! threatens it when `w` may fall between them, `ū` may co-designate with `t̄`,
//! and `x` may differ from `y` (the SAS⁺ clobbering test, lifted as in FAPE).
//!
//! A threat is resolved by demotion, promotion, disjoint separation (for the
//! first position `i` that may differ: `u_j = t_j` for `j < i` and
//! `u_i ≠ t_i`), or agreement (equal instance and equal value, so the write is
//! not a change).

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::bindings::{Binding, Bindings, StepVarTypes, TypeContext};
use crate::chain::{self, Chain};
use crate::formula::Atom;
use crate::orderings::{BinaryOrderings, Ordering, StepTime};
use crate::predicates::Predicate;
use crate::terms::{Object, Term, Variable};
use crate::types::Type;

use super::task::{LFact, LValue, LiftedTask};

pub use crate::plan::{GOAL_ID, INIT_ID};

/// No producer assignment: the link is supported by the initial state.
pub const FROM_INIT: u16 = u16::MAX;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Link {
    pub producer: usize,
    pub consumer: usize,
    /// Condition index at the consumer (goal index for the goal step).
    pub cond: u16,
    /// Producer assignment index, or [`FROM_INIT`].
    pub assign: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Open {
    pub consumer: usize,
    pub cond: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Threat {
    pub step: usize,
    pub assign: u16,
    pub link: Link,
}

#[derive(Debug, Clone)]
pub struct Plan {
    /// Schema of real step `id` at index `id - 1`.
    pub steps: Rc<Vec<u32>>,
    pub links: Option<Rc<Chain<Link>>>,
    pub opens: Option<Rc<Chain<Open>>>,
    pub threats: Option<Rc<Chain<Threat>>>,
    pub orderings: Rc<BinaryOrderings>,
    pub bindings: Rc<Bindings>,
    pub cost: usize,
    pub num_opens: usize,
    pub num_threats: usize,
}

/// Types of global schema variables, for [`TypeContext`].
pub struct GlobalTypes(pub Vec<Type>);

impl StepVarTypes for GlobalTypes {
    fn var_type(&self, var: Variable, _: usize) -> Type {
        self.0[var.0 as usize]
    }
}

/// Static atoms by predicate, with per-position object indexes.
pub struct StaticIndex {
    tuples: HashMap<Predicate, Vec<Vec<Object>>>,
    members: HashSet<Atom>,
    by_position: HashMap<(Predicate, usize, Object), Vec<u32>>,
}

impl StaticIndex {
    pub fn new(atoms: &HashSet<Atom>) -> Self {
        let mut tuples: HashMap<Predicate, Vec<Vec<Object>>> = HashMap::new();
        let mut sorted: Vec<&Atom> = atoms.iter().collect();
        sorted.sort_by(|a, b| (a.predicate.0, &a.terms).cmp(&(b.predicate.0, &b.terms)));
        let mut by_position: HashMap<(Predicate, usize, Object), Vec<u32>> = HashMap::new();
        for atom in sorted {
            let rows = tuples.entry(atom.predicate).or_default();
            let row: Vec<Object> = atom.terms.iter().map(|t| t.as_object()).collect();
            for (i, o) in row.iter().enumerate() {
                by_position
                    .entry((atom.predicate, i, *o))
                    .or_default()
                    .push(rows.len() as u32);
            }
            rows.push(row);
        }
        StaticIndex {
            tuples,
            members: atoms.clone(),
            by_position,
        }
    }

    /// Whether some static atom matches `atom` with bound terms `bound`.
    fn possible(&self, atom: &Atom, bound: &[Term]) -> bool {
        let Some(rows) = self.tuples.get(&atom.predicate) else {
            return false;
        };
        if bound.iter().all(|t| t.object()) {
            return self.members.contains(&Atom {
                predicate: atom.predicate,
                terms: bound.to_vec(),
            });
        }
        let mut best: Option<&Vec<u32>> = None;
        for (i, t) in bound.iter().enumerate() {
            if let Term::Object(o) = t {
                match self.by_position.get(&(atom.predicate, i, *o)) {
                    None => return false,
                    Some(list) if best.is_none_or(|b| list.len() < b.len()) => best = Some(list),
                    _ => {}
                }
            }
        }
        let matches = |row: &Vec<Object>| {
            bound
                .iter()
                .zip(row)
                .all(|(t, o)| !matches!(t, Term::Object(b) if b != o))
        };
        match best {
            Some(list) => list.iter().any(|&r| matches(&rows[r as usize])),
            None => !rows.is_empty(),
        }
    }

    pub fn contains(&self, atom: &Atom) -> bool {
        self.members.contains(atom)
    }

    /// Rows of a static predicate.
    pub fn rows(&self, predicate: Predicate) -> &[Vec<Object>] {
        self.tuples.get(&predicate).map(|v| v.as_slice()).unwrap_or(&[])
    }
}

/// What refinement needs from the task.
pub struct Ctx<'a> {
    pub task: &'a LiftedTask,
    pub types: TypeContext<'a>,
    pub statics: StaticIndex,
    /// Assignments by variable: (schema, assignment index).
    pub writers: HashMap<u32, Vec<(u32, u16)>>,
    /// Initial values by variable.
    pub init_by_var: HashMap<u32, Vec<(Vec<Object>, LValue)>>,
    /// Initial facts per (variable, part) as rows `inv ++ counted args`.
    pub init_rows: HashMap<(u32, u16), (Vec<Vec<Object>>, HashSet<Vec<Object>>)>,
    /// A new step's parameters still free after linking are bound on
    /// insertion when their domain has at most this many objects (0: never).
    pub bind_limit: usize,
}

impl<'a> Ctx<'a> {
    pub fn new(task: &'a LiftedTask, types: TypeContext<'a>) -> Self {
        let mut writers: HashMap<u32, Vec<(u32, u16)>> = HashMap::new();
        for (s, schema) in task.schemas.iter().enumerate() {
            for (a, assign) in schema.assigns.iter().enumerate() {
                writers.entry(assign.fact.var).or_default().push((s as u32, a as u16));
            }
        }
        let mut init_by_var: HashMap<u32, Vec<(Vec<Object>, LValue)>> = HashMap::new();
        let mut init: Vec<_> = task.init.iter().collect();
        init.sort();
        for ((var, inv), value) in init {
            init_by_var.entry(*var).or_default().push((inv.clone(), value.clone()));
        }
        let mut init_rows: HashMap<(u32, u16), (Vec<Vec<Object>>, HashSet<Vec<Object>>)> = HashMap::new();
        for (var, entries) in &init_by_var {
            for (inv, value) in entries {
                if let LValue::Part { part, args } = value {
                    let mut row = inv.clone();
                    row.extend(args.iter().map(|t| t.as_object()));
                    let table = init_rows.entry((*var, *part)).or_default();
                    table.1.insert(row.clone());
                    table.0.push(row);
                }
            }
        }
        Ctx {
            task,
            types,
            init_rows,
            statics: StaticIndex::new(&task.static_atoms),
            writers,
            init_by_var,
            bind_limit: std::env::var("POTOROO_LFDR_BIND")
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(0),
        }
    }

    pub fn schema_of(&self, plan: &Plan, step: usize) -> &super::task::LSchema {
        &self.task.schemas[plan.steps[step - 1] as usize]
    }

    /// The condition a link or open condition protects.
    pub fn condition(&self, plan: &Plan, consumer: usize, cond: u16) -> &LFact {
        if consumer == GOAL_ID {
            &self.task.goal[cond as usize]
        } else {
            &self.schema_of(plan, consumer).conditions[cond as usize]
        }
    }

    pub fn assignment(&self, plan: &Plan, step: usize, assign: u16) -> &LFact {
        &self.schema_of(plan, step).assigns[assign as usize].fact
    }
}

/// An equality or inequality between scoped terms.
type Constraint = (Term, usize, Term, usize, bool);

/// Adds scoped (in)equalities, or `None` if inconsistent.
fn constrain(ctx: &Ctx, bindings: &Rc<Bindings>, constraints: &[Constraint]) -> Option<Rc<Bindings>> {
    let mut new = Vec::with_capacity(constraints.len());
    for &(l, ls, r, rs, eq) in constraints {
        let l = bindings.binding(l, ls);
        let r = bindings.binding(r, rs);
        match (l, r) {
            (Term::Object(a), Term::Object(b)) => {
                if (a == b) != eq {
                    return None;
                }
            }
            (Term::Variable(v), t) => new.push(Binding::new(v, ls, t, rs, eq)),
            (t, Term::Variable(v)) => new.push(Binding::new(v, rs, t, ls, eq)),
        }
    }
    if new.is_empty() {
        return Some(bindings.clone());
    }
    bindings.add(&ctx.types, &new, false)
}

/// Equalities unifying two facts' instances and values, or `None` when their
/// variables or value kinds differ.
fn unifier(f: &LFact, fs: usize, g: &LFact, gs: usize, out: &mut Vec<Constraint>) -> bool {
    if f.var != g.var {
        return false;
    }
    for (a, b) in f.inv.iter().zip(&g.inv) {
        out.push((*a, fs, *b, gs, true));
    }
    match (&f.value, &g.value) {
        (LValue::None, LValue::None) => true,
        (LValue::Part { part: p, args: a }, LValue::Part { part: q, args: b }) if p == q => {
            for (x, y) in a.iter().zip(b) {
                out.push((*x, fs, *y, gs, true));
            }
            true
        }
        _ => false,
    }
}

impl Plan {
    pub fn initial(ctx: &Ctx) -> Option<Plan> {
        let mut opens = None;
        for i in (0..ctx.task.goal.len()).rev() {
            opens = chain::cons(
                Open {
                    consumer: GOAL_ID,
                    cond: i as u16,
                },
                opens,
            );
        }
        let mut bindings = Bindings::empty();
        let goal_constraints: Vec<Constraint> = ctx
            .task
            .goal_equalities
            .iter()
            .map(|(l, r)| (*l, GOAL_ID, *r, GOAL_ID, true))
            .chain(
                ctx.task
                    .goal_inequalities
                    .iter()
                    .map(|(l, r)| (*l, GOAL_ID, *r, GOAL_ID, false)),
            )
            .collect();
        bindings = constrain(ctx, &bindings, &goal_constraints)?;
        Some(Plan {
            steps: Rc::new(Vec::new()),
            links: None,
            num_opens: ctx.task.goal.len(),
            opens,
            threats: None,
            orderings: Rc::new(BinaryOrderings::new()),
            bindings,
            cost: 0,
            num_threats: 0,
        })
    }

    pub fn num_steps(&self) -> usize {
        self.steps.len()
    }

    pub fn complete(&self) -> bool {
        self.num_opens == 0 && self.num_threats == 0
    }

    fn without_open(&self, open: Open) -> Plan {
        let mut plan = self.clone();
        plan.opens = chain::remove(&self.opens, &open);
        plan.num_opens -= 1;
        plan
    }

    fn without_threat(&self, threat: Threat) -> Plan {
        let mut plan = self.clone();
        plan.threats = chain::remove(&self.threats, &threat);
        plan.num_threats -= 1;
        plan
    }

    fn add_threat(&mut self, threat: Threat) {
        self.threats = chain::cons(threat, self.threats.take());
        self.num_threats += 1;
    }
}

fn before(a: usize, b: usize) -> Ordering {
    Ordering::new(a, StepTime::AtEnd, b, StepTime::AtStart)
}

/// Whether step `w`'s assignment may clobber `link` under the current
/// orderings and bindings.
pub fn threatens(ctx: &Ctx, plan: &Plan, w: usize, assign: u16, link: &Link) -> bool {
    if w == link.producer || w == link.consumer {
        return false;
    }
    let f = ctx.condition(plan, link.consumer, link.cond);
    let g = ctx.assignment(plan, w, assign);
    if f.var != g.var {
        return false;
    }
    if !(plan.orderings.possibly_after(w, StepTime::AtEnd, link.producer, StepTime::AtEnd)
        && plan.orderings.possibly_before(w, StepTime::AtEnd, link.consumer, StepTime::AtStart))
    {
        return false;
    }
    let b = &plan.bindings;
    let c = link.consumer;
    if !f
        .inv
        .iter()
        .zip(&g.inv)
        .all(|(t, u)| b.terms_can_equal(&ctx.types, *u, w, *t, c))
    {
        return false;
    }
    match (&f.value, &g.value) {
        (LValue::None, LValue::None) => false,
        (LValue::Part { part: p, args: a }, LValue::Part { part: q, args: x }) if p == q => {
            !a.iter().zip(x).all(|(y, v)| b.terms_equal(*v, w, *y, c))
        }
        _ => true,
    }
}

/// Threats between a new link and every step.
fn link_threats(ctx: &Ctx, plan: &mut Plan, link: Link) {
    let var = ctx.condition(plan, link.consumer, link.cond).var;
    for w in 1..=plan.num_steps() {
        let schema = ctx.schema_of(plan, w);
        for (a, assign) in schema.assigns.iter().enumerate() {
            if assign.fact.var == var && threatens(ctx, plan, w, a as u16, &link) {
                plan.add_threat(Threat {
                    step: w,
                    assign: a as u16,
                    link,
                });
            }
        }
    }
}

/// Threats from a new step against every existing link.
fn step_threats(ctx: &Ctx, plan: &mut Plan, w: usize) {
    let links: Vec<Link> = chain::iter(&plan.links).copied().collect();
    let n = ctx.schema_of(plan, w).assigns.len();
    for link in links {
        for a in 0..n as u16 {
            if threatens(ctx, plan, w, a, &link) {
                plan.add_threat(Threat { step: w, assign: a, link });
            }
        }
    }
}

/// Static and in-step constraints of `step` hold under the bindings, as far
/// as they are decided.
pub fn step_statics_possible(ctx: &Ctx, plan: &Plan, step: usize) -> bool {
    let schema = ctx.schema_of(plan, step);
    let resolve = |a: &Atom| -> Vec<Term> {
        a.terms.iter().map(|t| plan.bindings.binding(*t, step)).collect()
    };
    schema.statics.iter().all(|a| ctx.statics.possible(a, &resolve(a)))
        && schema.negated_statics.iter().all(|a| {
            let terms = resolve(a);
            !(terms.iter().all(|t| t.object())
                && ctx.statics.contains(&Atom {
                    predicate: a.predicate,
                    terms,
                }))
        })
}

pub fn all_statics_possible(ctx: &Ctx, plan: &Plan) -> bool {
    (1..=plan.num_steps()).all(|s| step_statics_possible(ctx, plan, s))
}

/// Adds the link `producer → consumer` (bindings already unified), then the
/// constraints that keep a `none` write from being overridden by an add of
/// the same step, and the new threats. Several children when that constraint
/// is a disjunction.
fn finish_link(ctx: &Ctx, mut plan: Plan, link: Link, out: &mut Vec<Plan>) {
    plan.links = chain::cons(link, plan.links.take());
    let mut variants = vec![plan];
    if link.producer != INIT_ID && link.producer != GOAL_ID {
        let fact = ctx.assignment(&variants[0], link.producer, link.assign).clone();
        if fact.value == LValue::None {
            let schema = ctx.schema_of(&variants[0], link.producer);
            for add in schema.assigns.iter().filter(|a| a.fact.var == fact.var && a.fact.value != LValue::None) {
                // The add wins when its instance co-designates: require a
                // differing position (disjoint branches).
                let mut next = Vec::new();
                for plan in variants {
                    for i in 0..fact.inv.len() {
                        let mut cs: Vec<Constraint> = (0..i)
                            .map(|j| (fact.inv[j], link.producer, add.fact.inv[j], link.producer, true))
                            .collect();
                        cs.push((fact.inv[i], link.producer, add.fact.inv[i], link.producer, false));
                        if let Some(b) = constrain(ctx, &plan.bindings, &cs) {
                            let mut p = plan.clone();
                            p.bindings = b;
                            next.push(p);
                        }
                    }
                }
                variants = next;
            }
        }
    }
    for mut plan in variants {
        let Some(bindings) = propagate_statics(ctx, &plan) else {
            continue;
        };
        plan.bindings = bindings;
        link_threats(ctx, &mut plan, link);
        out.push(plan);
    }
}

/// Children resolving an open condition: new steps, reused steps, init.
pub fn refine_open(ctx: &Ctx, plan: &Plan, open: Open) -> Vec<Plan> {
    let base = plan.without_open(open);
    let fact = ctx.condition(plan, open.consumer, open.cond).clone();
    let c = open.consumer;
    let mut out = Vec::new();
    let mut cs = Vec::new();
    // New steps.
    for &(schema_index, a) in ctx.writers.get(&fact.var).map(|v| v.as_slice()).unwrap_or(&[]) {
        let schema = &ctx.task.schemas[schema_index as usize];
        let n = base.num_steps() + 1;
        cs.clear();
        if !unifier(&schema.assigns[a as usize].fact, n, &fact, c, &mut cs) {
            continue;
        }
        for (l, r) in &schema.equalities {
            cs.push((*l, n, *r, n, true));
        }
        for (l, r) in &schema.inequalities {
            cs.push((*l, n, *r, n, false));
        }
        let Some(orderings) = base.orderings.refine_with_step(before(n, c), n) else {
            continue;
        };
        let Some(bindings) = constrain(ctx, &base.bindings, &cs) else {
            continue;
        };
        let mut child = base.clone();
        let mut steps = (*base.steps).clone();
        steps.push(schema_index);
        child.steps = Rc::new(steps);
        child.orderings = orderings;
        child.bindings = bindings;
        child.cost += schema.cost;
        for k in (0..schema.conditions.len()).rev() {
            child.opens = chain::cons(
                Open {
                    consumer: n,
                    cond: k as u16,
                },
                child.opens.take(),
            );
            child.num_opens += 1;
        }
        step_threats(ctx, &mut child, n);
        let mut linked = Vec::new();
        finish_link(
            ctx,
            child,
            Link {
                producer: n,
                consumer: c,
                cond: open.cond,
                assign: a,
            },
            &mut linked,
        );
        for plan in linked {
            bind_small(ctx, plan, n, ctx.bind_limit, &mut out);
        }
    }
    // Reuse.
    for w in 1..=base.num_steps() {
        if w == c || !base.orderings.possibly_before(w, StepTime::AtEnd, c, StepTime::AtStart) {
            continue;
        }
        let schema = ctx.schema_of(&base, w);
        for (a, assign) in schema.assigns.iter().enumerate() {
            cs.clear();
            if !unifier(&assign.fact, w, &fact, c, &mut cs) {
                continue;
            }
            let Some(orderings) = base.orderings.refine(before(w, c)) else {
                continue;
            };
            let Some(bindings) = constrain(ctx, &base.bindings, &cs) else {
                continue;
            };
            let mut child = base.clone();
            child.orderings = orderings;
            child.bindings = bindings;
            // A new ordering can retire no threat but may create none either:
            // existing threats are re-checked on selection.
            finish_link(
                ctx,
                child,
                Link {
                    producer: w,
                    consumer: c,
                    cond: open.cond,
                    assign: a as u16,
                },
                &mut out,
            );
        }
    }
    // Initial state.
    let link = Link {
        producer: INIT_ID,
        consumer: c,
        cond: open.cond,
        assign: FROM_INIT,
    };
    match &fact.value {
        LValue::Part { part, .. } => {
            // One child: the condition's tuple must be an initial fact, a
            // table constraint that `propagate_statics` narrows, rather than
            // one child per matching fact.
            if ctx.init_rows.contains_key(&(fact.var, *part)) {
                finish_link(ctx, base.clone(), link, &mut out);
            }
        }
        LValue::None => {
            // Instances with no initial member, consistent with the bindings.
            let domains: Vec<Vec<Object>> = fact
                .inv
                .iter()
                .map(|t| match base.bindings.binding(*t, c) {
                    Term::Object(o) => vec![o],
                    Term::Variable(v) => base.bindings.domain(&ctx.types, v, c).into_iter().collect(),
                })
                .collect();
            let mut tuple = Vec::with_capacity(domains.len());
            fn product(
                i: usize,
                domains: &[Vec<Object>],
                tuple: &mut Vec<Object>,
                visit: &mut dyn FnMut(&[Object]),
            ) {
                if i == domains.len() {
                    visit(tuple);
                    return;
                }
                for &o in &domains[i] {
                    tuple.push(o);
                    product(i + 1, domains, tuple, visit);
                    tuple.pop();
                }
            }
            product(0, &domains, &mut tuple, &mut |inv: &[Object]| {
                if ctx.task.init.contains_key(&(fact.var, inv.to_vec())) {
                    return;
                }
                let cs: Vec<Constraint> = fact
                    .inv
                    .iter()
                    .zip(inv)
                    .map(|(t, o)| (*t, c, Term::Object(*o), INIT_ID, true))
                    .collect();
                if let Some(bindings) = constrain(ctx, &base.bindings, &cs) {
                    let mut child = base.clone();
                    child.bindings = bindings;
                    finish_link(ctx, child, link, &mut out);
                }
            });
        }
    }
    out
}

/// Children resolving a threat, or the plan without it when the threat is no
/// longer possible.
pub fn refine_threat(ctx: &Ctx, plan: &Plan, threat: Threat) -> Vec<Plan> {
    let base = plan.without_threat(threat);
    let link = threat.link;
    let w = threat.step;
    if !threatens(ctx, &base, w, threat.assign, &link) {
        return vec![base];
    }
    let mut out = Vec::new();
    let f = ctx.condition(&base, link.consumer, link.cond).clone();
    let g = ctx.assignment(&base, w, threat.assign).clone();
    let c = link.consumer;
    // Children are pushed least promising first: ties go to the newest.
    // Agreement: the same instance receives the protected value.
    let mut cs = Vec::new();
    if unifier(&g, w, &f, c, &mut cs) && !matches!(f.value, LValue::None) {
        if let Some(bindings) = constrain(ctx, &base.bindings, &cs) {
            let mut child = base.clone();
            child.bindings = bindings;
            if let Some(bindings) = propagate_statics(ctx, &child) {
                child.bindings = bindings;
                out.push(child);
            }
        }
    }
    // Demotion: before the producer.
    if link.producer != INIT_ID {
        if let Some(orderings) = base.orderings.refine(before(w, link.producer)) {
            let mut child = base.clone();
            child.orderings = orderings;
            out.push(child);
        }
    }
    // Promotion: after the consumer.
    if link.consumer != GOAL_ID {
        if let Some(orderings) = base.orderings.refine(before(link.consumer, w)) {
            let mut child = base.clone();
            child.orderings = orderings;
            out.push(child);
        }
    }
    // Separation on the first differing position, first position last.
    for i in (0..f.inv.len()).rev() {
        let mut cs: Vec<Constraint> = (0..i).map(|j| (g.inv[j], w, f.inv[j], c, true)).collect();
        cs.push((g.inv[i], w, f.inv[i], c, false));
        if let Some(bindings) = constrain(ctx, &base.bindings, &cs) {
            let mut child = base.clone();
            child.bindings = bindings;
            if let Some(bindings) = propagate_statics(ctx, &child) {
                child.bindings = bindings;
                out.push(child);
            }
        }
    }
    out
}

/// Supporters of an open condition whose unifier is consistent, counted up to
/// `limit`: an upper bound on its refinements, for ZLIFO selection.
pub fn count_refinements(ctx: &Ctx, plan: &Plan, open: Open, limit: usize) -> usize {
    let fact = ctx.condition(plan, open.consumer, open.cond);
    let c = open.consumer;
    let mut count = 0;
    let mut cs = Vec::new();
    let consistent = |cs: &[Constraint]| constrain(ctx, &plan.bindings, cs).is_some();
    let n = plan.num_steps() + 1;
    for &(schema_index, a) in ctx.writers.get(&fact.var).map(|v| v.as_slice()).unwrap_or(&[]) {
        let schema = &ctx.task.schemas[schema_index as usize];
        cs.clear();
        if unifier(&schema.assigns[a as usize].fact, n, fact, c, &mut cs) && consistent(&cs) {
            count += 1;
            if count >= limit {
                return count;
            }
        }
    }
    for w in 1..plan.num_steps() + 1 {
        if w == c || !plan.orderings.possibly_before(w, StepTime::AtEnd, c, StepTime::AtStart) {
            continue;
        }
        for assign in &ctx.schema_of(plan, w).assigns {
            cs.clear();
            if unifier(&assign.fact, w, fact, c, &mut cs) && consistent(&cs) {
                count += 1;
                if count >= limit {
                    return count;
                }
            }
        }
    }
    match &fact.value {
        // Initial support is one refinement: a table constraint.
        LValue::Part { part, .. } => {
            if ctx.init_rows.contains_key(&(fact.var, *part)) {
                count += 1;
            }
        }
        // Counting `none` instances needs enumeration; assume several.
        LValue::None => count += limit,
    }
    count
}

/// Whether an existing step that may precede the consumer has an assignment
/// the bindings already equate with the open condition (reuse for ADD). Mere
/// unifiability would let one unbound step discount every condition it might
/// support, though it supports only one instance.
pub fn reusable(ctx: &Ctx, plan: &Plan, open: Open) -> bool {
    let fact = ctx.condition(plan, open.consumer, open.cond);
    let c = open.consumer;
    let b = &plan.bindings;
    let mut cs = Vec::new();
    for w in 1..plan.num_steps() + 1 {
        if w == c || !plan.orderings.possibly_before(w, StepTime::AtEnd, c, StepTime::AtStart) {
            continue;
        }
        for assign in &ctx.schema_of(plan, w).assigns {
            cs.clear();
            if unifier(&assign.fact, w, fact, c, &mut cs)
                && cs.iter().all(|&(l, ls, r, rs, _)| b.terms_equal(l, ls, r, rs))
            {
                return true;
            }
        }
    }
    false
}

/// A threat no separation or agreement can remove: the instances are already
/// co-designated and the values certainly differ. Others are postponed until
/// the bindings decide them (VHPOP's delayed separable threats).
pub fn definite(ctx: &Ctx, plan: &Plan, threat: &Threat) -> bool {
    let link = &threat.link;
    let w = threat.step;
    let c = link.consumer;
    let f = ctx.condition(plan, c, link.cond);
    let g = ctx.assignment(plan, w, threat.assign);
    let b = &plan.bindings;
    if !f.inv.iter().zip(&g.inv).all(|(t, u)| b.terms_equal(*u, w, *t, c)) {
        return false;
    }
    match (&f.value, &g.value) {
        (LValue::Part { part: p, args: a }, LValue::Part { part: q, args: x }) if p == q => {
            a.iter().zip(x).any(|(y, v)| {
                matches!(
                    (b.binding(*y, c), b.binding(*v, w)),
                    (Term::Object(o1), Term::Object(o2)) if o1 != o2
                )
            })
        }
        _ => true,
    }
}

enum TableSet<'a> {
    Static(Predicate),
    Init(&'a HashSet<Vec<Object>>),
}

/// Generalised arc consistency over the steps' static atoms and over the
/// initial-state links (their tuple must be an initial fact). Domains are kept
/// per equality class (a representative step variable), start from the type
/// and non-codesignation domain, and shrink to the projections of the static
/// rows that agree with them. `None` when some atom has no supporting row.
/// Classes left with one object are bound, which also sharpens threat
/// detection and the heuristic's patterns.
pub fn propagate_statics(ctx: &Ctx, plan: &Plan) -> Option<Rc<Bindings>> {
    propagate_domains(ctx, plan).map(|(bindings, _)| bindings)
}

/// [`propagate_statics`], also returning the narrowed domains of the classes
/// that table or distinctness constraints touch.
pub fn propagate_domains(
    ctx: &Ctx,
    plan: &Plan,
) -> Option<(Rc<Bindings>, HashMap<crate::bindings::StepVariable, HashSet<Object>>)> {
    use crate::bindings::StepVariable;
    let b = &plan.bindings;
    let mut domains: HashMap<StepVariable, HashSet<Object>> = HashMap::new();
    // Table constraints: (terms, scope, rows, membership).
    let mut tables: Vec<(Vec<Term>, usize, &[Vec<Object>], TableSet)> = Vec::new();
    for step in 1..=plan.num_steps() {
        for atom in &ctx.schema_of(plan, step).statics {
            tables.push((
                atom.terms.clone(),
                step,
                ctx.statics.rows(atom.predicate),
                TableSet::Static(atom.predicate),
            ));
        }
    }
    for link in chain::iter(&plan.links) {
        if link.producer != INIT_ID {
            continue;
        }
        let f = ctx.condition(plan, link.consumer, link.cond);
        if let LValue::Part { part, args } = &f.value {
            let (rows, set) = &ctx.init_rows[&(f.var, *part)];
            let mut terms = f.inv.clone();
            terms.extend(args.iter().copied());
            tables.push((terms, link.consumer, rows.as_slice(), TableSet::Init(set)));
        }
    }
    let mut changed = true;
    let mut rounds = 0;
    while changed && rounds < 16 {
        changed = false;
        rounds += 1;
        for (atom_terms, step, rows, set) in &tables {
            let step = *step;
            let terms: Vec<Result<Object, StepVariable>> = atom_terms
                .iter()
                .map(|t| match b.binding(*t, step) {
                    Term::Object(o) => Ok(o),
                    Term::Variable(v) => Err(b.representative(v, step)),
                })
                .collect();
            if terms.iter().all(|t| t.is_ok()) {
                let ground: Vec<Object> = terms.iter().map(|t| *t.as_ref().unwrap()).collect();
                let member = match set {
                    TableSet::Static(predicate) => ctx.statics.contains(&Atom {
                        predicate: *predicate,
                        terms: ground.iter().map(|o| Term::Object(*o)).collect(),
                    }),
                    TableSet::Init(set) => set.contains(&ground),
                };
                if !member {
                    return None;
                }
                continue;
            }
            for (i, t) in atom_terms.iter().enumerate() {
                if let Err(rep) = terms[i] {
                    domains.entry(rep).or_insert_with(|| {
                        let Term::Variable(v) = b.binding(*t, step) else { unreachable!() };
                        b.domain(&ctx.types, v, step).into_iter().collect()
                    });
                }
            }
            let mut support: Vec<HashSet<Object>> = vec![HashSet::new(); terms.len()];
            let mut any = false;
            'rows: for row in rows.iter() {
                let mut seen: Vec<(StepVariable, Object)> = Vec::new();
                for (i, t) in terms.iter().enumerate() {
                    match t {
                        Ok(o) => {
                            if row[i] != *o {
                                continue 'rows;
                            }
                        }
                        Err(rep) => {
                            if !domains[rep].contains(&row[i]) {
                                continue 'rows;
                            }
                            if let Some((_, o)) = seen.iter().find(|(r, _)| r == rep) {
                                if *o != row[i] {
                                    continue 'rows;
                                }
                            } else {
                                seen.push((*rep, row[i]));
                            }
                        }
                    }
                }
                any = true;
                for (i, t) in terms.iter().enumerate() {
                    if t.is_err() {
                        support[i].insert(row[i]);
                    }
                }
            }
            if !any {
                return None;
            }
            for (i, t) in terms.iter().enumerate() {
                if let Err(rep) = t {
                    let domain = domains.get_mut(rep).unwrap();
                    let before = domain.len();
                    domain.retain(|o| support[i].contains(o));
                    if domain.len() != before {
                        changed = true;
                    }
                }
            }
        }
    }
    if !distinct_feasible(ctx, plan, &mut domains) {
        return None;
    }
    let mut new = Vec::new();
    for (&(v, step), domain) in &domains {
        if domain.len() == 1 {
            let o = *domain.iter().next().unwrap();
            new.push(Binding::new(v, step, Term::Object(o), step, true));
        }
    }
    let bindings = if new.is_empty() { b.clone() } else { b.add(&ctx.types, &new, false)? };
    let mut probe = plan.clone();
    probe.bindings = bindings.clone();
    // Negated statics, once decided.
    if !(1..=probe.num_steps()).all(|s| step_statics_possible(ctx, &probe, s)) {
        return None;
    }
    Some((bindings, domains))
}

/// Binds each free parameter of `step` whose domain has at most `limit`
/// objects, one child per object (selective early commitment).
fn bind_small(ctx: &Ctx, plan: Plan, step: usize, limit: usize, out: &mut Vec<Plan>) {
    if limit == 0 {
        out.push(plan);
        return;
    }
    let free = ctx.schema_of(&plan, step).parameters.iter().find_map(|v| {
        match plan.bindings.binding(Term::Variable(*v), step) {
            Term::Variable(var) => {
                let domain = plan.bindings.domain(&ctx.types, var, step);
                (domain.len() <= limit).then_some((var, domain))
            }
            Term::Object(_) => None,
        }
    });
    let Some((var, domain)) = free else {
        out.push(plan);
        return;
    };
    for o in domain {
        let Some(bindings) = plan
            .bindings
            .add(&ctx.types, &[Binding::new(var, step, Term::Object(o), step, true)], false)
        else {
            continue;
        };
        let mut child = plan.clone();
        child.bindings = bindings;
        let Some(bindings) = propagate_statics(ctx, &child) else {
            continue;
        };
        child.bindings = bindings;
        bind_small(ctx, child, step, limit, out);
    }
}

/// Whether the only consistent supporter would be a new step (no reuse, no
/// initial fact).
pub fn only_new_step(ctx: &Ctx, plan: &Plan, open: Open) -> bool {
    let fact = ctx.condition(plan, open.consumer, open.cond);
    let c = open.consumer;
    let mut cs = Vec::new();
    for w in 1..plan.num_steps() + 1 {
        if w == c || !plan.orderings.possibly_before(w, StepTime::AtEnd, c, StepTime::AtStart) {
            continue;
        }
        for assign in &ctx.schema_of(plan, w).assigns {
            cs.clear();
            if unifier(&assign.fact, w, fact, c, &mut cs) && constrain(ctx, &plan.bindings, &cs).is_some() {
                return false;
            }
        }
    }
    if let LValue::None = fact.value {
        return false;
    }
    for (inv, value) in ctx.init_by_var.get(&fact.var).map(|v| v.as_slice()).unwrap_or(&[]) {
        let ground = LFact {
            var: fact.var,
            inv: inv.iter().map(|o| Term::Object(*o)).collect(),
            value: value.clone(),
        };
        cs.clear();
        if unifier(&ground, INIT_ID, fact, c, &mut cs) && constrain(ctx, &plan.bindings, &cs).is_some() {
            return false;
        }
    }
    true
}

/// Resolutions of a threat that are consistent on their own: demotion,
/// promotion, separation (once), agreement. Static propagation is not
/// run, so this bounds the children of [`refine_threat`] from above. A threat
/// that is no longer possible counts as `None` (it is simply dropped).
pub fn count_threat_options(ctx: &Ctx, plan: &Plan, threat: &Threat) -> Option<usize> {
    let link = &threat.link;
    let w = threat.step;
    if !threatens(ctx, plan, w, threat.assign, link) {
        return None;
    }
    let c = link.consumer;
    let mut n = 0;
    if link.producer != INIT_ID
        && plan.orderings.possibly_before(w, StepTime::AtEnd, link.producer, StepTime::AtStart)
    {
        n += 1;
    }
    if c != GOAL_ID && plan.orderings.possibly_before(c, StepTime::AtEnd, w, StepTime::AtStart) {
        n += 1;
    }
    let f = ctx.condition(plan, c, link.cond);
    let g = ctx.assignment(plan, w, threat.assign);
    let mut cs: Vec<Constraint> = Vec::new();
    // Separation counts once, as VHPOP's disjunctive separation goal does.
    for i in 0..f.inv.len() {
        cs.clear();
        cs.extend((0..i).map(|j| (g.inv[j], w, f.inv[j], c, true)));
        cs.push((g.inv[i], w, f.inv[i], c, false));
        if constrain(ctx, &plan.bindings, &cs).is_some() {
            n += 1;
            break;
        }
    }
    cs.clear();
    if !matches!(f.value, LValue::None)
        && unifier(g, w, f, c, &mut cs)
        && constrain(ctx, &plan.bindings, &cs).is_some()
    {
        n += 1;
    }
    Some(n)
}

/// Whether some step that may precede the consumer may write the condition's
/// instance to another value (VHPOP's unsafe open condition).
pub fn unsafe_open(ctx: &Ctx, plan: &Plan, open: Open) -> bool {
    let c = open.consumer;
    let f = ctx.condition(plan, c, open.cond);
    let b = &plan.bindings;
    (1..=plan.num_steps()).any(|w| {
        w != c
            && plan.orderings.possibly_before(w, StepTime::AtEnd, c, StepTime::AtStart)
            && ctx.schema_of(plan, w).assigns.iter().any(|a| {
                let g = &a.fact;
                g.var == f.var
                    && f.inv.iter().zip(&g.inv).all(|(t, u)| b.terms_can_equal(&ctx.types, *u, w, *t, c))
                    && match (&f.value, &g.value) {
                        (LValue::None, LValue::None) => false,
                        (LValue::Part { part: p, args: x }, LValue::Part { part: q, args: y }) if p == q => {
                            !x.iter().zip(y).all(|(s, t)| b.terms_equal(*t, w, *s, c))
                        }
                        _ => true,
                    }
            })
    })
}

/// Hall's condition on non-codesignation: a set of pairwise distinct classes
/// needs at least as many objects as it has members. Sets are grown greedily
/// from each class over its distinct neighbours, so this is a sound but
/// incomplete all-different check (Younes & Simmons, AIPS 2002, note that
/// separation inequalities alone hide such conflicts).
fn distinct_feasible(
    ctx: &Ctx,
    plan: &Plan,
    domains: &mut HashMap<crate::bindings::StepVariable, HashSet<Object>>,
) -> bool {
    use crate::bindings::StepVariable;
    let b = &plan.bindings;
    let mut classes: Vec<StepVariable> = Vec::new();
    let mut seen = HashSet::new();
    for step in 1..=plan.num_steps() {
        for v in &ctx.schema_of(plan, step).parameters {
            if let Term::Variable(var) = b.binding(Term::Variable(*v), step) {
                let rep = b.representative(var, step);
                if seen.insert(rep) {
                    classes.push(rep);
                }
            }
        }
    }
    let mut neighbours: HashMap<StepVariable, HashSet<StepVariable>> = HashMap::new();
    for &rep in &classes {
        let set: HashSet<StepVariable> = b
            .non_codesignated(rep.0, rep.1)
            .into_iter()
            .filter_map(|(v, s)| match b.binding(Term::Variable(v), s) {
                Term::Variable(var) => Some(b.representative(var, s)),
                Term::Object(_) => None,
            })
            .filter(|r| *r != rep)
            .collect();
        if !set.is_empty() {
            neighbours.insert(rep, set);
        }
    }
    if neighbours.is_empty() {
        return true;
    }
    let domain_of = |rep: StepVariable, domains: &mut HashMap<StepVariable, HashSet<Object>>| -> HashSet<Object> {
        domains
            .entry(rep)
            .or_insert_with(|| b.domain(&ctx.types, rep.0, rep.1).into_iter().collect())
            .clone()
    };
    for (&start, adjacent) in &neighbours {
        let mut clique = vec![start];
        let mut union = domain_of(start, domains);
        let mut candidates: Vec<StepVariable> = adjacent.iter().copied().collect();
        candidates.sort();
        for u in candidates {
            if clique.iter().all(|c| neighbours.get(&u).is_some_and(|n| n.contains(c))) {
                clique.push(u);
                union.extend(domain_of(u, domains));
                if clique.len() > union.len() {
                    return false;
                }
            }
        }
    }
    true
}

/// Unbound step-parameter classes with their propagated domains (two or more
/// objects; singletons are bound by propagation), smallest first.
pub fn binding_candidates(ctx: &Ctx, plan: &Plan) -> Vec<(crate::bindings::StepVariable, Vec<Object>)> {
    let Some((_, domains)) = propagate_domains(ctx, plan) else {
        return Vec::new();
    };
    let b = &plan.bindings;
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for step in 1..=plan.num_steps() {
        for v in &ctx.schema_of(plan, step).parameters {
            let Term::Variable(var) = b.binding(Term::Variable(*v), step) else {
                continue;
            };
            let rep = b.representative(var, step);
            if !seen.insert(rep) {
                continue;
            }
            let mut domain: Vec<Object> = match domains.get(&rep) {
                Some(d) => d.iter().copied().collect(),
                None => b.domain(&ctx.types, var, step).into_iter().collect(),
            };
            domain.sort();
            if domain.len() >= 2 {
                out.push((rep, domain));
            }
        }
    }
    out.sort_by_key(|(rep, d)| (d.len(), *rep));
    out
}

/// Children binding one class to each object of its domain.
pub fn refine_bind(ctx: &Ctx, plan: &Plan, class: crate::bindings::StepVariable, objects: &[Object]) -> Vec<Plan> {
    let mut out = Vec::new();
    // Ties go to the newest child: push in reverse so the first object is
    // tried first.
    for &o in objects.iter().rev() {
        let Some(bindings) = plan
            .bindings
            .add(&ctx.types, &[Binding::new(class.0, class.1, Term::Object(o), class.1, true)], false)
        else {
            continue;
        };
        let mut child = plan.clone();
        child.bindings = bindings;
        if let Some(bindings) = propagate_statics(ctx, &child) {
            child.bindings = bindings;
            out.push(child);
        }
    }
    out
}

/// Classes appearing in a threat's instance or values.
pub fn threat_classes(ctx: &Ctx, plan: &Plan, threat: &Threat) -> Vec<crate::bindings::StepVariable> {
    let b = &plan.bindings;
    let link = &threat.link;
    let mut out = Vec::new();
    let mut add = |f: &LFact, step: usize| {
        let mut terms: Vec<Term> = f.inv.clone();
        if let LValue::Part { args, .. } = &f.value {
            terms.extend(args.iter().copied());
        }
        for t in terms {
            if let Term::Variable(v) = b.binding(t, step) {
                out.push(b.representative(v, step));
            }
        }
    };
    add(ctx.condition(plan, link.consumer, link.cond), link.consumer);
    add(ctx.assignment(plan, threat.step, threat.assign), threat.step);
    out
}

/// Forward checking of a binding against threats: the objects of `class`
/// that leave every threat touching it with at least one repair, each with
/// the number of those threats that the binding removes outright (separated
/// or agreeing). Objects that kill a threat are pruned.
pub fn viable_values(
    ctx: &Ctx,
    plan: &Plan,
    class: crate::bindings::StepVariable,
    objects: &[Object],
    touching: &[Threat],
) -> Vec<(Object, usize)> {
    let mut out = Vec::new();
    for &o in objects {
        let Some(bindings) = plan
            .bindings
            .add(&ctx.types, &[Binding::new(class.0, class.1, Term::Object(o), class.1, true)], false)
        else {
            continue;
        };
        let mut probe = plan.clone();
        probe.bindings = bindings;
        let mut removed = 0;
        let mut dead = false;
        for t in touching {
            match count_threat_options(ctx, &probe, t) {
                None => removed += 1,
                Some(0) => {
                    dead = true;
                    break;
                }
                Some(_) => {}
            }
        }
        if !dead {
            out.push((o, removed));
        }
    }
    out
}
