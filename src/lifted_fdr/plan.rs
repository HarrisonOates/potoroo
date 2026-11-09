//! Lifted FDR partial plans and their refinement.
//!
//! A step is a schema whose variables are scoped by the step id in the
//! plan's [`LBindings`]. A causal link protects the consumer's condition `G(t̄)=y`
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

use crate::bindings::{StepVarTypes, TypeContext};
use crate::chain::{self, Chain};
use crate::formula::Atom;
use crate::orderings::{BinaryOrderings, Ordering, StepTime};
use crate::predicates::Predicate;
use crate::terms::{Object, Term, Variable};
use crate::types::Type;

use super::binds::{ClassId, Constraint, LBindings, Resolved};
use super::objset::ObjSet;
use super::task::{LFact, LValue, LiftedTask};

pub use crate::plan::{GOAL_ID, INIT_ID};

/// No producer assignment: the link is supported by the initial state.
pub const FROM_INIT: u16 = u16::MAX;

/// Step ids are stored as `u32` (the goal as `u32::MAX`): plans hold many
/// links, open conditions and threats in persistent chains.
#[inline]
fn pack(step: usize) -> u32 {
    if step == GOAL_ID {
        u32::MAX
    } else {
        step as u32
    }
}

#[inline]
fn unpack(step: u32) -> usize {
    if step == u32::MAX {
        GOAL_ID
    } else {
        step as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Link {
    producer: u32,
    consumer: u32,
    /// Condition index at the consumer (goal index for the goal step).
    pub cond: u16,
    /// Producer assignment index, or [`FROM_INIT`].
    pub assign: u16,
}

impl Link {
    pub fn new(producer: usize, consumer: usize, cond: u16, assign: u16) -> Link {
        Link {
            producer: pack(producer),
            consumer: pack(consumer),
            cond,
            assign,
        }
    }

    #[inline]
    pub fn producer(&self) -> usize {
        unpack(self.producer)
    }

    #[inline]
    pub fn consumer(&self) -> usize {
        unpack(self.consumer)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Open {
    consumer: u32,
    pub cond: u16,
}

impl Open {
    pub fn new(consumer: usize, cond: u16) -> Open {
        Open {
            consumer: pack(consumer),
            cond,
        }
    }

    #[inline]
    pub fn consumer(&self) -> usize {
        unpack(self.consumer)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Threat {
    step: u32,
    pub assign: u16,
    pub link: Link,
}

impl Threat {
    pub fn new(step: usize, assign: u16, link: Link) -> Threat {
        Threat {
            step: pack(step),
            assign,
            link,
        }
    }

    #[inline]
    pub fn step(&self) -> usize {
        unpack(self.step)
    }
}

/// Which child of a flaw's refinement: enough to rebuild exactly that child
/// from its parent, since children are generated deterministically. Queued
/// children can be kept as `(parent, flaw, choice)` and rebuilt when popped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Choice {
    NewStep { schema: u32, assign: u16, variant: u8 },
    Reuse { step: u32, assign: u16, variant: u8 },
    /// Initial-state support; `instance` indexes the `none` enumeration.
    Init { instance: u32, variant: u8 },
    /// The threat is no longer possible.
    Drop,
    Agree,
    Demote,
    Promote,
    Separate(u8),
    Bind(Object),
}

impl Choice {
    fn with_variant(self, v: u8) -> Choice {
        match self {
            Choice::NewStep { schema, assign, .. } => Choice::NewStep { schema, assign, variant: v },
            Choice::Reuse { step, assign, .. } => Choice::Reuse { step, assign, variant: v },
            Choice::Init { instance, .. } => Choice::Init { instance, variant: v },
            other => other,
        }
    }

    fn variant(self) -> Option<u8> {
        match self {
            Choice::NewStep { variant, .. } | Choice::Reuse { variant, .. } | Choice::Init { variant, .. } => {
                Some(variant)
            }
            _ => None,
        }
    }

    /// Whether `self` names the candidate `key`, whatever its variant.
    fn names(self, key: Choice) -> bool {
        self.with_variant(0) == key.with_variant(0)
    }
}

/// Children with the choices that rebuild them.
pub type Children = Vec<(Choice, Plan)>;

#[derive(Debug, Clone)]
pub struct Plan {
    /// Schema of real step `id` at index `id - 1`.
    pub steps: super::pvec::PVec<u32>,
    pub links: Option<Rc<Chain<Link>>>,
    pub opens: Option<Rc<Chain<Open>>>,
    pub threats: Option<Rc<Chain<Threat>>>,
    pub orderings: Rc<BinaryOrderings>,
    pub bindings: LBindings,
    pub cost: usize,
    pub num_opens: usize,
    pub num_threats: usize,
}

/// A relation (static predicate or a variable's initial values) with a
/// membership set and per-position row indexes.
#[derive(Default)]
pub struct Table {
    pub rows: Vec<Vec<Object>>,
    set: crate::fasthash::FastSet<Vec<Object>>,
    by_position: crate::fasthash::FastMap<(usize, Object), Vec<u32>>,
}

impl Table {
    fn push(&mut self, row: Vec<Object>) {
        if !self.set.insert(row.clone()) {
            return;
        }
        let index = self.rows.len() as u32;
        for (i, o) in row.iter().enumerate() {
            self.by_position.entry((i, *o)).or_default().push(index);
        }
        self.rows.push(row);
    }

    fn contains(&self, row: &[Object]) -> bool {
        self.set.contains(row)
    }

    fn with(&self, position: usize, object: Object) -> &[u32] {
        self.by_position.get(&(position, object)).map_or(&[], |v| v.as_slice())
    }
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
    pub init_rows: HashMap<(u32, u16), Table>,
    /// Static relations by predicate.
    pub static_tables: HashMap<Predicate, Table>,
    /// Number of objects (ids are contiguous from 0).
    pub num_objects: usize,
    /// Objects of each type, as bitsets.
    type_sets: std::cell::RefCell<HashMap<Type, ObjSet>>,
    /// Interchangeable objects (Fox & Long), for breaking value symmetry in
    /// binding flaws; `None` disables it.
    pub symmetries: Option<Rc<crate::symmetry::ObjectSymmetries>>,
    /// Order separated and agreeing threats between the link's ends.
    pub systematic_threats: bool,
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
        let mut init_rows: HashMap<(u32, u16), Table> = HashMap::new();
        for (var, entries) in &init_by_var {
            for (inv, value) in entries {
                if let LValue::Part { part, args } = value {
                    let mut row = inv.clone();
                    row.extend(args.iter().map(|t| t.as_object()));
                    init_rows.entry((*var, *part)).or_default().push(row);
                }
            }
        }
        let mut static_tables: HashMap<Predicate, Table> = HashMap::new();
        let mut statics: Vec<&Atom> = task.static_atoms.iter().collect();
        statics.sort_by(|a, b| (a.predicate.0, &a.terms).cmp(&(b.predicate.0, &b.terms)));
        for atom in statics {
            static_tables
                .entry(atom.predicate)
                .or_default()
                .push(atom.terms.iter().map(|t| t.as_object()).collect());
        }
        Ctx {
            task,
            types,
            init_rows,
            static_tables,
            type_sets: Default::default(),
            num_objects: types.constants.owned_objects().count() + types.objects.owned_objects().count(),
            symmetries: None,
            systematic_threats: std::env::var_os("POTOROO_LFDR_SYSTHREAT").is_some(),
            statics: StaticIndex::new(&task.static_atoms),
            writers,
            init_by_var,
        }
    }

    /// The objects of a global variable's type.
    pub fn type_set(&self, var: Variable) -> ObjSet {
        let ty = self.task.var_types[var.0 as usize];
        self.type_sets
            .borrow_mut()
            .entry(ty)
            .or_insert_with(|| self.types.compatible_objects(ty).into_iter().collect())
            .clone()
    }

    /// Adds a step of `schema` to the plan's bindings.
    fn add_step_bindings(&self, bindings: &mut LBindings, schema: &super::task::LSchema) {
        bindings.add_step(
            schema.var_base,
            (0..schema.var_count).map(|i| self.type_set(Variable(schema.var_base + i))),
        );
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

/// Adds scoped (in)equalities, or `None` if inconsistent.
fn constrain(_ctx: &Ctx, bindings: &LBindings, constraints: &[Constraint]) -> Option<LBindings> {
    bindings.add(constraints)
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
                Open::new(GOAL_ID, i as u16),
                opens,
            );
        }
        let mut bindings = LBindings::default();
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
            steps: Default::default(),
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
    if w == link.producer() || w == link.consumer() {
        return false;
    }
    let f = ctx.condition(plan, link.consumer(), link.cond);
    let g = ctx.assignment(plan, w, assign);
    if f.var != g.var {
        return false;
    }
    if !(plan.orderings.possibly_after(w, StepTime::AtEnd, link.producer(), StepTime::AtEnd)
        && plan.orderings.possibly_before(w, StepTime::AtEnd, link.consumer(), StepTime::AtStart))
    {
        return false;
    }
    let b = &plan.bindings;
    let c = link.consumer();
    if !f
        .inv
        .iter()
        .zip(&g.inv)
        .all(|(t, u)| b.terms_can_equal(*u, w, *t, c))
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
    let var = ctx.condition(plan, link.consumer(), link.cond).var;
    for w in 1..=plan.num_steps() {
        let schema = ctx.schema_of(plan, w);
        for (a, assign) in schema.assigns.iter().enumerate() {
            if assign.fact.var == var && threatens(ctx, plan, w, a as u16, &link) {
                plan.add_threat(Threat::new(w, a as u16, link));
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
                plan.add_threat(Threat::new(w, a, link));
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
/// is a disjunction; each is tagged with `key` and its variant index, and
/// `only` keeps just the variant it names.
fn finish_link(ctx: &Ctx, mut plan: Plan, link: Link, key: Choice, only: Option<Choice>, out: &mut Children) {
    plan.links = chain::cons(link, plan.links.take());
    let mut variants = vec![plan];
    if link.producer() != INIT_ID && link.producer() != GOAL_ID {
        let fact = ctx.assignment(&variants[0], link.producer(), link.assign).clone();
        if fact.value == LValue::None {
            let schema = ctx.schema_of(&variants[0], link.producer());
            for add in schema.assigns.iter().filter(|a| a.fact.var == fact.var && a.fact.value != LValue::None) {
                // The add wins when its instance co-designates: require a
                // differing position (disjoint branches).
                let mut next = Vec::new();
                for plan in variants {
                    for i in 0..fact.inv.len() {
                        let mut cs: Vec<Constraint> = (0..i)
                            .map(|j| (fact.inv[j], link.producer(), add.fact.inv[j], link.producer(), true))
                            .collect();
                        cs.push((fact.inv[i], link.producer(), add.fact.inv[i], link.producer(), false));
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
    for (v, mut plan) in variants.into_iter().enumerate() {
        let choice = key.with_variant(v as u8);
        if only.is_some_and(|o| o.variant() != choice.variant()) {
            continue;
        }
        // A new initial-state link is a new table constraint: check it now
        // when ground, else have propagation revisit its classes.
        if link.producer() == INIT_ID {
            let f = ctx.condition(&plan, link.consumer(), link.cond);
            if let LValue::Part { part, args } = &f.value {
                let terms: Vec<Resolved> = f
                    .inv
                    .iter()
                    .chain(args)
                    .map(|t| plan.bindings.resolve(*t, link.consumer()))
                    .collect();
                if terms.iter().all(|t| matches!(t, Resolved::Object(_))) {
                    let row: Vec<Object> = terms
                        .iter()
                        .map(|t| match t {
                            Resolved::Object(o) => *o,
                            Resolved::Class(_) => unreachable!(),
                        })
                        .collect();
                    if !ctx.init_rows[&(f.var, *part)].contains(&row) {
                        continue;
                    }
                }
                for t in terms {
                    if let Resolved::Class(k) = t {
                        plan.bindings.touch(k);
                    }
                }
            }
        }
        let Some(bindings) = propagate_statics(ctx, &plan) else {
            continue;
        };
        plan.bindings = bindings;
        link_threats(ctx, &mut plan, link);
        out.push((choice, plan));
    }
}

/// Children resolving an open condition: new steps, reused steps, init.
/// With `only`, just the child that choice names (for rebuilding a queued
/// child).
pub fn refine_open(ctx: &Ctx, plan: &Plan, open: Open, only: Option<Choice>) -> Children {
    let base = plan.without_open(open);
    let fact = ctx.condition(plan, open.consumer(), open.cond).clone();
    let c = open.consumer();
    let mut out = Vec::new();
    let mut cs = Vec::new();
    // New steps.
    for &(schema_index, a) in ctx.writers.get(&fact.var).map(|v| v.as_slice()).unwrap_or(&[]) {
        let key = Choice::NewStep {
            schema: schema_index,
            assign: a,
            variant: 0,
        };
        if only.is_some_and(|o| !o.names(key)) {
            continue;
        }
        let schema = &ctx.task.schemas[schema_index as usize];
        // Static atoms without variables are decided now.
        if schema
            .statics
            .iter()
            .any(|a| a.terms.iter().all(|t| t.object()) && !ctx.statics.contains(a))
        {
            continue;
        }
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
        let mut with_step = base.bindings.clone();
        ctx.add_step_bindings(&mut with_step, schema);
        let Some(bindings) = constrain(ctx, &with_step, &cs) else {
            continue;
        };
        let mut child = base.clone();
        child.steps.push(schema_index);
        child.orderings = orderings;
        child.bindings = bindings;
        child.cost += schema.cost;
        for k in (0..schema.conditions.len()).rev() {
            child.opens = chain::cons(Open::new(n, k as u16), child.opens.take());
            child.num_opens += 1;
        }
        step_threats(ctx, &mut child, n);
        finish_link(ctx, child, Link::new(n, c, open.cond, a), key, only, &mut out);
    }
    // Reuse.
    for w in 1..=base.num_steps() {
        if w == c || !base.orderings.possibly_before(w, StepTime::AtEnd, c, StepTime::AtStart) {
            continue;
        }
        let schema = ctx.schema_of(&base, w);
        for (a, assign) in schema.assigns.iter().enumerate() {
            let key = Choice::Reuse {
                step: w as u32,
                assign: a as u16,
                variant: 0,
            };
            if only.is_some_and(|o| !o.names(key)) {
                continue;
            }
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
            finish_link(ctx, child, Link::new(w, c, open.cond, a as u16), key, only, &mut out);
        }
    }
    // Initial state.
    let link = Link::new(INIT_ID, c, open.cond, FROM_INIT);
    match &fact.value {
        LValue::Part { part, .. } => {
            // One child: the condition's tuple must be an initial fact, a
            // table constraint that `propagate_statics` narrows, rather than
            // one child per matching fact.
            let key = Choice::Init { instance: 0, variant: 0 };
            if ctx.init_rows.contains_key(&(fact.var, *part)) && only.is_none_or(|o| o.names(key)) {
                finish_link(ctx, base.clone(), link, key, only, &mut out);
            }
        }
        LValue::None => {
            // Instances with no initial member, consistent with the bindings.
            let domains: Vec<Vec<Object>> = fact
                .inv
                .iter()
                .map(|t| match base.bindings.resolve(*t, c) {
                    Resolved::Object(o) => vec![o],
                    Resolved::Class(k) => base.bindings.domain(k).iter().collect(),
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
            let mut index = 0u32;
            product(0, &domains, &mut tuple, &mut |inv: &[Object]| {
                let key = Choice::Init {
                    instance: index,
                    variant: 0,
                };
                index += 1;
                if only.is_some_and(|o| !o.names(key)) || ctx.task.init.contains_key(&(fact.var, inv.to_vec())) {
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
                    finish_link(ctx, child, link, key, only, &mut out);
                }
            });
        }
    }
    out
}

/// Extends `witness` (an object per class id, from an ancestor) to a solution
/// of the plan's binding constraints, or `None`. Classes whose inherited
/// value is missing or no longer allowed are searched depth-first, smallest
/// domain first, within `budget` assignments; every static atom, negated
/// static and initial-state link is checked as a table lookup once its
/// classes have values. The bindings are not changed.
pub fn extend_witness(ctx: &Ctx, plan: &Plan, witness: &[Option<Object>], budget: usize) -> Option<Vec<Option<Object>>> {
    let b = &plan.bindings;
    let mut w: Vec<Option<Object>> = (0..b.num_classes() as ClassId)
        .map(|c| b.value(c).or_else(|| witness.get(c as usize).copied().flatten()))
        .collect();
    // Classes to search: unbound with no valid inherited value.
    let unbound: Vec<ClassId> = b.unbound_classes().collect();
    let mut missing: Vec<ClassId> = Vec::new();
    for &c in &unbound {
        let ok = w[c as usize].is_some_and(|o| b.domain(c).contains(o));
        if !ok {
            w[c as usize] = None;
            missing.push(c);
        }
    }
    // Distinct pairs between inherited values that now collide.
    for &c in &unbound {
        if let Some(o) = w[c as usize] {
            if b.distinct(c).iter().any(|&d| d != c && rep_value(b, &w, d) == Some(o)) && !missing.contains(&c) {
                w[c as usize] = None;
                missing.push(c);
            }
        }
    }
    // Constraints: a step's static atom (negated or not) or an initial-state
    // link, as borrowed terms resolved on demand.
    struct Spec<'t> {
        inv: &'t [Term],
        args: &'t [Term],
        step: usize,
        table: Option<&'t Table>,
        positive: bool,
    }
    let mut specs: Vec<Spec> = Vec::new();
    for step in 1..=plan.num_steps() {
        let schema = ctx.schema_of(plan, step);
        for (atoms, positive) in [(&schema.statics, true), (&schema.negated_statics, false)] {
            for atom in atoms {
                specs.push(Spec {
                    inv: &atom.terms,
                    args: &[],
                    step,
                    table: ctx.static_tables.get(&atom.predicate),
                    positive,
                });
            }
        }
    }
    for link in chain::iter(&plan.links) {
        if link.producer() != INIT_ID {
            continue;
        }
        let f = ctx.condition(plan, link.consumer(), link.cond);
        if let LValue::Part { part, args } = &f.value {
            specs.push(Spec {
                inv: &f.inv,
                args,
                step: link.consumer(),
                table: ctx.init_rows.get(&(f.var, *part)),
                positive: true,
            });
        }
    }
    let mut row: Vec<Object> = Vec::new();
    let mut holds = |spec: &Spec, w: &[Option<Object>]| -> Option<bool> {
        row.clear();
        for t in spec.inv.iter().chain(spec.args) {
            row.push(match b.resolve(*t, spec.step) {
                Resolved::Object(o) => o,
                Resolved::Class(k) => rep_value(b, w, k)?,
            });
        }
        let member = spec.table.is_some_and(|t| t.contains(&row));
        Some(member == spec.positive)
    };
    // Constraints over inherited values only: a failure means some class in
    // them must be searched again. Rather than diagnose, give up.
    let mut pending: Vec<usize> = Vec::new();
    for (i, spec) in specs.iter().enumerate() {
        match holds(spec, &w) {
            Some(true) => {}
            Some(false) => return None,
            None => pending.push(i),
        }
    }
    if missing.is_empty() {
        return Some(w);
    }
    missing.sort_by_key(|&c| (b.domain(c).len(), c));
    // The pending constraints each mention, by the last missing class
    // (in search order) they contain: checked once that class has a value.
    let position = |c: ClassId| missing.iter().position(|&m| m == c);
    let mut at: Vec<Vec<usize>> = vec![Vec::new(); missing.len()];
    for i in pending {
        let spec = &specs[i];
        let last = spec
            .inv
            .iter()
            .chain(spec.args)
            .filter_map(|t| match b.resolve(*t, spec.step) {
                Resolved::Class(k) => position(rep_class(b, k)),
                Resolved::Object(_) => None,
            })
            .max()?;
        at[last].push(i);
    }
    let mut budget = budget;
    fn search(
        i: usize,
        missing: &[ClassId],
        at: &[Vec<usize>],
        b: &LBindings,
        w: &mut Vec<Option<Object>>,
        budget: &mut usize,
        check: &mut dyn FnMut(usize, &[Option<Object>]) -> bool,
    ) -> bool {
        if i == missing.len() {
            return true;
        }
        let c = missing[i];
        for o in b.domain(c).iter() {
            if *budget == 0 {
                return false;
            }
            *budget -= 1;
            if b.distinct(c).iter().any(|&d| rep_value(b, w, d) == Some(o)) {
                continue;
            }
            w[c as usize] = Some(o);
            if at[i].iter().all(|&s| check(s, w)) && search(i + 1, missing, at, b, w, budget, check) {
                return true;
            }
        }
        w[c as usize] = None;
        false
    }
    let mut check = |s: usize, w: &[Option<Object>]| holds(&specs[s], w) == Some(true);
    search(0, &missing, &at, b, &mut w, &mut budget, &mut check).then_some(w)
}

/// A class's representative (following merges).
fn rep_class(b: &LBindings, c: ClassId) -> ClassId {
    b.representative(c)
}

/// The value of a class: its constant, else the witness's value for its
/// representative.
fn rep_value(b: &LBindings, w: &[Option<Object>], c: ClassId) -> Option<Object> {
    let r = b.representative(c);
    b.value(r).or_else(|| w.get(r as usize).copied().flatten())
}

/// The plan without threats that no longer threaten; the same plan when
/// every threat still does.
pub fn without_stale_threats(ctx: &Ctx, plan: Rc<Plan>) -> Rc<Plan> {
    let stale: Vec<Threat> = chain::iter(&plan.threats)
        .filter(|t| !threatens(ctx, &plan, t.step(), t.assign, &t.link))
        .copied()
        .collect();
    if stale.is_empty() {
        return plan;
    }
    let mut pruned = (*plan).clone();
    for t in stale {
        pruned.threats = chain::remove(&pruned.threats, &t);
        pruned.num_threats -= 1;
    }
    Rc::new(pruned)
}

/// Resolves, in place, every threat with at most one resolution left: none
/// kills the plan (`None`), one is applied, and stale threats are dropped.
/// Repeats while that changes something, at most `rounds` times. Each such
/// threat would otherwise be a search node with a single child.
pub fn force_threats(ctx: &Ctx, plan: Rc<Plan>, rounds: usize) -> Option<Rc<Plan>> {
    let mut plan = plan;
    for _ in 0..rounds {
        let mut changed = false;
        let threats: Vec<Threat> = chain::iter(&plan.threats).copied().collect();
        for t in threats {
            if !chain::iter(&plan.threats).any(|u| *u == t) {
                continue;
            }
            match count_threat_options(ctx, &plan, &t) {
                Some(0) => return None,
                None | Some(1) => {
                    let mut children = refine_threat(ctx, &plan, t, None);
                    match children.len() {
                        0 => return None,
                        1 => {
                            plan = Rc::new(children.pop().unwrap().1);
                            changed = true;
                        }
                        _ => {}
                    }
                }
                Some(_) => {}
            }
        }
        if !changed {
            break;
        }
    }
    Some(plan)
}

/// Children resolving a threat, or the plan without it when the threat is no
/// longer possible. With `only`, just the child that choice names.
pub fn refine_threat(ctx: &Ctx, plan: &Plan, threat: Threat, only: Option<Choice>) -> Children {
    let base = plan.without_threat(threat);
    let link = threat.link;
    let w = threat.step();
    if !threatens(ctx, &base, w, threat.assign, &link) {
        return vec![(Choice::Drop, base)];
    }
    let wanted = |c: Choice| only.is_none_or(|o| o == c);
    let mut out = Vec::new();
    let f = ctx.condition(&base, link.consumer(), link.cond).clone();
    let g = ctx.assignment(&base, w, threat.assign).clone();
    let c = link.consumer();
    // Children are pushed least promising first: ties go to the newest.
    // Agreement: the same instance receives the protected value.
    let mut cs = Vec::new();
    if wanted(Choice::Agree) && unifier(&g, w, &f, c, &mut cs) && !matches!(f.value, LValue::None) {
        if let Some(bindings) = constrain(ctx, &base.bindings, &cs) {
            if let Some(mut child) = between(ctx, &base, w, &link) {
                child.bindings = bindings;
                if let Some(bindings) = propagate_statics(ctx, &child) {
                    child.bindings = bindings;
                    out.push((Choice::Agree, child));
                }
            }
        }
    }
    // Demotion: before the producer.
    if wanted(Choice::Demote) && link.producer() != INIT_ID {
        if let Some(orderings) = base.orderings.refine(before(w, link.producer())) {
            let mut child = base.clone();
            child.orderings = orderings;
            out.push((Choice::Demote, child));
        }
    }
    // Promotion: after the consumer.
    if wanted(Choice::Promote) && link.consumer() != GOAL_ID {
        if let Some(orderings) = base.orderings.refine(before(link.consumer(), w)) {
            let mut child = base.clone();
            child.orderings = orderings;
            out.push((Choice::Promote, child));
        }
    }
    // Separation on the first differing position, first position last.
    for i in (0..f.inv.len()).rev() {
        if !wanted(Choice::Separate(i as u8)) {
            continue;
        }
        let mut cs: Vec<Constraint> = (0..i).map(|j| (g.inv[j], w, f.inv[j], c, true)).collect();
        cs.push((g.inv[i], w, f.inv[i], c, false));
        if let Some(bindings) = constrain(ctx, &base.bindings, &cs) {
            if let Some(mut child) = between(ctx, &base, w, &link) {
                child.bindings = bindings;
                if let Some(bindings) = propagate_statics(ctx, &child) {
                    child.bindings = bindings;
                    out.push((Choice::Separate(i as u8), child));
                }
            }
        }
    }
    out
}

/// The plan for a separation or agreement child. With systematic threat
/// resolution (`POTOROO_LFDR_SYSTHREAT`), `w` is also ordered between the
/// link's ends, so the children partition the completions: demotion puts `w`
/// before the producer, promotion after the consumer, and the rest between.
/// `None` when that ordering is inconsistent.
fn between(ctx: &Ctx, base: &Plan, w: usize, link: &Link) -> Option<Plan> {
    let mut child = base.clone();
    if ctx.systematic_threats {
        let mut orderings = base.orderings.clone();
        if link.producer() != INIT_ID {
            orderings = orderings.refine(before(link.producer(), w))?;
        }
        if link.consumer() != GOAL_ID {
            orderings = orderings.refine(before(w, link.consumer()))?;
        }
        child.orderings = orderings;
    }
    Some(child)
}

/// Whether a unifier between a not-yet-added step `n` and the plan is
/// consistent as far as types and existing domains tell: an upper bound for
/// counting refinements without adding the step.
fn new_step_compatible(ctx: &Ctx, plan: &Plan, cs: &[Constraint], n: usize) -> bool {
    let side = |t: Term, step: usize| -> Option<ObjSet> {
        match t {
            Term::Object(o) => Some(std::iter::once(o).collect()),
            Term::Variable(v) if step == n => Some(ctx.type_set(v)),
            Term::Variable(_) => match plan.bindings.resolve(t, step) {
                Resolved::Object(o) => Some(std::iter::once(o).collect()),
                Resolved::Class(k) => Some(plan.bindings.domain(k).clone()),
            },
        }
    };
    cs.iter().all(|&(l, ls, r, rs, equal)| {
        !equal || matches!((side(l, ls), side(r, rs)), (Some(a), Some(b)) if a.intersects(&b))
    })
}

/// Supporters of an open condition whose unifier is consistent, counted up to
/// `limit`: an upper bound on its refinements, for ZLIFO selection.
pub fn count_refinements(ctx: &Ctx, plan: &Plan, open: Open, limit: usize) -> usize {
    let fact = ctx.condition(plan, open.consumer(), open.cond);
    let c = open.consumer();
    let mut count = 0;
    let mut cs = Vec::new();
    let consistent = |cs: &[Constraint]| constrain(ctx, &plan.bindings, cs).is_some();
    let n = plan.num_steps() + 1;
    for &(schema_index, a) in ctx.writers.get(&fact.var).map(|v| v.as_slice()).unwrap_or(&[]) {
        let schema = &ctx.task.schemas[schema_index as usize];
        cs.clear();
        if unifier(&schema.assigns[a as usize].fact, n, fact, c, &mut cs) && new_step_compatible(ctx, plan, &cs, n) {
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
    let fact = ctx.condition(plan, open.consumer(), open.cond);
    let c = open.consumer();
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
    let w = threat.step();
    let c = link.consumer();
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

/// Generalised arc consistency over the steps' static atoms and over the
/// initial-state links (their tuple must be an initial fact), per equality
/// class, then Hall's condition over distinct classes. The narrowed domains
/// are written back to the bindings, which binds classes left with one
/// object; that may narrow distinct classes, so the pass repeats until
/// nothing changes. `None` when some constraint has no supporting row.
pub fn propagate_statics(ctx: &Ctx, plan: &Plan) -> Option<LBindings> {
    let mut bindings = plan.bindings.clone();
    loop {
        // Only constraints over classes changed since the last propagation
        // can have lost support: the parent's domains are already narrowed.
        let dirty: crate::fasthash::FastSet<ClassId> = bindings.take_dirty().into_iter().collect();
        if dirty.is_empty() {
            break;
        }
        let narrowed = narrow(ctx, plan, &bindings, &dirty)?;
        for (class, domain) in narrowed {
            if !bindings.restrict(class, &domain) {
                return None;
            }
        }
    }
    // Negated statics, once decided (positive ones are table constraints).
    for step in 1..=plan.num_steps() {
        for atom in &ctx.schema_of(plan, step).negated_statics {
            let terms: Vec<Term> = atom.terms.iter().map(|t| bindings.binding(*t, step)).collect();
            if terms.iter().all(|t| t.object())
                && ctx.statics.contains(&Atom {
                    predicate: atom.predicate,
                    terms,
                })
            {
                return None;
            }
        }
    }
    Some(bindings)
}

/// One arc-consistency fixpoint under `b`, starting from the constraints
/// over `dirty` classes: the classes whose domains shrank, with their new
/// domains, or `None` when inconsistent. Constraints are only materialised
/// when active or reached through a shrinking domain.
fn narrow(
    ctx: &Ctx,
    plan: &Plan,
    b: &LBindings,
    dirty: &crate::fasthash::FastSet<ClassId>,
) -> Option<Vec<(ClassId, ObjSet)>> {
    use crate::fasthash::{FastMap, FastSet};
    // Constraint specifications, borrowed: a static atom of a step or an
    // initial-state link (its variable's instance and value arguments).
    struct Spec<'t> {
        inv: &'t [Term],
        args: &'t [Term],
        step: usize,
        table: &'t Table,
    }
    let empty = Table::default();
    let mut specs: Vec<Spec> = Vec::new();
    for step in 1..=plan.num_steps() {
        for atom in &ctx.schema_of(plan, step).statics {
            specs.push(Spec {
                inv: &atom.terms,
                args: &[],
                step,
                table: ctx.static_tables.get(&atom.predicate).unwrap_or(&empty),
            });
        }
    }
    for link in chain::iter(&plan.links) {
        if link.producer() != INIT_ID {
            continue;
        }
        let f = ctx.condition(plan, link.consumer(), link.cond);
        if let LValue::Part { part, args } = &f.value {
            specs.push(Spec {
                inv: &f.inv,
                args,
                step: link.consumer(),
                table: &ctx.init_rows[&(f.var, *part)],
            });
        }
    }
    let terms_of = |spec: &Spec| -> Vec<Resolved> {
        spec.inv.iter().chain(spec.args).map(|t| b.resolve(*t, spec.step)).collect()
    };
    let touches = |spec: &Spec, classes: &dyn Fn(ClassId) -> bool| {
        spec.inv
            .iter()
            .chain(spec.args)
            .any(|t| matches!(t, Term::Variable(v) if classes(b.class(*v, spec.step))))
    };
    let object = |t: &Resolved| match t {
        Resolved::Object(o) => Some(*o),
        Resolved::Class(_) => None,
    };
    // Materialised constraints by spec index, and the worklist.
    let mut built: FastMap<usize, Vec<Resolved>> = FastMap::default();
    let mut queued: FastSet<usize> = FastSet::default();
    let mut worklist: Vec<usize> = Vec::new();
    let mut domains: FastMap<ClassId, ObjSet> = FastMap::default();
    for (index, spec) in specs.iter().enumerate() {
        if !touches(spec, &|k| dirty.contains(&k)) {
            continue;
        }
        let terms = terms_of(spec);
        if terms.iter().all(|t| object(t).is_some()) {
            let ground: Vec<Object> = terms.iter().filter_map(object).collect();
            if !spec.table.contains(&ground) {
                return None;
            }
            continue;
        }
        built.insert(index, terms);
        queued.insert(index);
        worklist.push(index);
    }
    let mut support: Vec<ObjSet> = Vec::new();
    let mut scratch: Vec<u32> = Vec::new();
    let mut seen: Vec<(ClassId, Object)> = Vec::new();
    while let Some(index) = worklist.pop() {
        queued.remove(&index);
        let table = specs[index].table;
        let terms = built[&index].clone();
        for t in &terms {
            if let Resolved::Class(k) = t {
                domains.entry(*k).or_insert_with(|| b.domain(*k).clone());
            }
        }
        // Candidate rows: the shortest index list over bound positions or a
        // small domain's objects, else every row.
        let mut bound: Option<&[u32]> = None;
        for (i, t) in terms.iter().enumerate() {
            if let Resolved::Object(o) = t {
                let list = table.with(i, *o);
                if bound.is_none_or(|l| list.len() < l.len()) {
                    bound = Some(list);
                }
            }
        }
        let mut gathered = false;
        if bound.is_none() {
            let mut best: Option<(usize, usize)> = None;
            for (i, t) in terms.iter().enumerate() {
                if let Resolved::Class(k) = t {
                    // Estimating costs a lookup per object: only for small
                    // domains, where gathering beats scanning every row.
                    if domains[k].len() > 64 {
                        continue;
                    }
                    let size: usize = domains[k].iter().map(|o| table.with(i, o).len()).sum();
                    if best.is_none_or(|(_, s)| size < s) {
                        best = Some((i, size));
                    }
                }
            }
            if let Some((i, size)) = best {
                if size < table.rows.len() {
                    let Resolved::Class(k) = terms[i] else { unreachable!() };
                    scratch.clear();
                    scratch.extend(domains[&k].iter().flat_map(|o| table.with(i, o).iter().copied()));
                    scratch.sort_unstable();
                    gathered = true;
                }
            }
        }
        let rows: Box<dyn Iterator<Item = u32> + '_> = match (bound, gathered) {
            (Some(list), _) => Box::new(list.iter().copied()),
            (None, true) => Box::new(scratch.iter().copied()),
            (None, false) => Box::new(0..table.rows.len() as u32),
        };
        // Reuse the support sets: clear rather than reallocate.
        while support.len() < terms.len() {
            support.push(ObjSet::new(ctx.num_objects));
        }
        for set in support.iter_mut().take(terms.len()) {
            set.clear();
        }
        let mut any = false;
        'rows: for r in rows {
            let row = &table.rows[r as usize];
            seen.clear();
            for (i, t) in terms.iter().enumerate() {
                match t {
                    Resolved::Object(o) => {
                        if row[i] != *o {
                            continue 'rows;
                        }
                    }
                    Resolved::Class(k) => {
                        if !domains[k].contains(row[i]) {
                            continue 'rows;
                        }
                        if let Some((_, o)) = seen.iter().find(|(r, _)| r == k) {
                            if *o != row[i] {
                                continue 'rows;
                            }
                        } else {
                            seen.push((*k, row[i]));
                        }
                    }
                }
            }
            any = true;
            for (i, t) in terms.iter().enumerate() {
                if let Resolved::Class(_) = t {
                    support[i].insert(row[i]);
                }
            }
        }
        if !any {
            return None;
        }
        for (i, t) in terms.iter().enumerate() {
            let Resolved::Class(k) = *t else { continue };
            let domain = domains.get_mut(&k).unwrap();
            if !domain.intersect_with(&support[i]) {
                continue;
            }
            if domain.is_empty() {
                return None;
            }
            // Revisit every other constraint over this class.
            for (other, spec) in specs.iter().enumerate() {
                if other == index || queued.contains(&other) || !touches(spec, &|c| c == k) {
                    continue;
                }
                let terms = built.entry(other).or_insert_with(|| terms_of(spec));
                if terms.iter().any(|t| object(t).is_none()) {
                    queued.insert(other);
                    worklist.push(other);
                }
            }
        }
    }
    if !distinct_feasible(b, &mut domains) {
        return None;
    }
    let mut narrowed: Vec<(ClassId, ObjSet)> = domains.into_iter().filter(|(k, d)| d != b.domain(*k)).collect();
    narrowed.sort_by_key(|(k, _)| *k);
    Some(narrowed)
}


/// Whether the only consistent supporter would be a new step (no reuse, no
/// initial fact).
pub fn only_new_step(ctx: &Ctx, plan: &Plan, open: Open) -> bool {
    let fact = ctx.condition(plan, open.consumer(), open.cond);
    let c = open.consumer();
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
    let w = threat.step();
    if !threatens(ctx, plan, w, threat.assign, link) {
        return None;
    }
    let c = link.consumer();
    let mut n = 0;
    if link.producer() != INIT_ID
        && plan.orderings.possibly_before(w, StepTime::AtEnd, link.producer(), StepTime::AtStart)
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
    let c = open.consumer();
    let f = ctx.condition(plan, c, open.cond);
    let b = &plan.bindings;
    (1..=plan.num_steps()).any(|w| {
        w != c
            && plan.orderings.possibly_before(w, StepTime::AtEnd, c, StepTime::AtStart)
            && ctx.schema_of(plan, w).assigns.iter().any(|a| {
                let g = &a.fact;
                g.var == f.var
                    && f.inv.iter().zip(&g.inv).all(|(t, u)| b.terms_can_equal(*u, w, *t, c))
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

/// Hall's condition on distinct classes: a set of pairwise distinct classes
/// needs at least as many objects as it has members. Sets are grown greedily
/// from each class over its distinct neighbours, so this is a sound but
/// incomplete all-different check (Younes & Simmons, AIPS 2002, note that
/// separation inequalities alone hide such conflicts).
fn distinct_feasible(b: &LBindings, domains: &mut crate::fasthash::FastMap<ClassId, ObjSet>) -> bool {
    for start in b.unbound_classes() {
        let adjacent: Vec<ClassId> = b
            .distinct(start)
            .iter()
            .copied()
            .filter(|&d| b.domain(d).len() > 1)
            .collect();
        if adjacent.is_empty() {
            continue;
        }
        let domain_of = |k: ClassId, domains: &crate::fasthash::FastMap<ClassId, ObjSet>| -> ObjSet {
            domains.get(&k).cloned().unwrap_or_else(|| b.domain(k).clone())
        };
        let mut clique = vec![start];
        let mut union = domain_of(start, domains);
        for u in adjacent {
            if clique.iter().all(|c| b.distinct(u).contains(c)) {
                clique.push(u);
                union.union_with(&domain_of(u, domains));
                if clique.len() > union.len() {
                    return false;
                }
            }
        }
    }
    true
}

/// Unbound step-parameter classes with their domains (two or more objects;
/// singletons are bound eagerly), smallest first, each with the domain after
/// value-symmetry breaking (the children worth trying).
pub fn binding_candidates(ctx: &Ctx, plan: &Plan) -> Vec<(ClassId, Vec<Object>, Vec<Object>)> {
    let b = &plan.bindings;
    let used = if ctx.symmetries.is_some() { used_objects(ctx, plan) } else { HashSet::new() };
    let mut out = Vec::new();
    for class in b.unbound_classes() {
        let domain: Vec<Object> = b.domain(class).iter().collect();
        if domain.len() >= 2 {
            let mut reduced = domain.clone();
            if let Some(symmetries) = &ctx.symmetries {
                break_symmetry(symmetries, &mut reduced, &used);
            }
            out.push((class, domain, reduced));
        }
    }
    out.sort_by_key(|(class, _, d)| (d.len(), *class));
    out
}

/// Children binding one class to each object of its domain.
pub fn refine_bind(ctx: &Ctx, plan: &Plan, class: ClassId, objects: &[Object]) -> Children {
    let mut out = Vec::new();
    // Ties go to the newest child: push in reverse so the first object is
    // tried first.
    for &o in objects.iter().rev() {
        let Some(bindings) = plan.bindings.bind(class, o) else {
            continue;
        };
        let mut child = plan.clone();
        child.bindings = bindings;
        if let Some(bindings) = propagate_statics(ctx, &child) {
            child.bindings = bindings;
            out.push((Choice::Bind(o), child));
        }
    }
    out
}

/// Classes appearing in a threat's instance or values.
pub fn threat_classes(ctx: &Ctx, plan: &Plan, threat: &Threat) -> Vec<ClassId> {
    let b = &plan.bindings;
    let link = &threat.link;
    let mut out = Vec::new();
    let mut add = |f: &LFact, step: usize| {
        let mut terms: Vec<Term> = f.inv.clone();
        if let LValue::Part { args, .. } = &f.value {
            terms.extend(args.iter().copied());
        }
        for t in terms {
            if let Resolved::Class(k) = b.resolve(t, step) {
                out.push(k);
            }
        }
    };
    add(ctx.condition(plan, link.consumer(), link.cond), link.consumer());
    add(ctx.assignment(plan, threat.step(), threat.assign), threat.step());
    out
}

/// Forward checking of a binding against threats: the objects of `class`
/// that leave every threat touching it with at least one repair, each with
/// the number of those threats that the binding removes outright (separated
/// or agreeing). Objects that kill a threat are pruned.
pub fn viable_values(
    ctx: &Ctx,
    plan: &Plan,
    class: ClassId,
    objects: &[Object],
    touching: &[Threat],
) -> Vec<(Object, usize)> {
    let mut out = Vec::new();
    for &o in objects {
        let Some(bindings) = plan.bindings.bind(class, o) else {
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

/// Objects the plan already names: bound step parameters.
fn used_objects(ctx: &Ctx, plan: &Plan) -> HashSet<Object> {
    let mut used = HashSet::new();
    for step in 1..=plan.num_steps() {
        for v in &ctx.schema_of(plan, step).parameters {
            if let Term::Object(o) = plan.bindings.binding(Term::Variable(*v), step) {
                used.insert(o);
            }
        }
    }
    used
}

/// Keeps, of each class of interchangeable objects, the members the plan
/// already uses and the first unused one: binding to another unused member
/// yields a renaming of that child.
fn break_symmetry(symmetries: &crate::symmetry::ObjectSymmetries, domain: &mut Vec<Object>, used: &HashSet<Object>) {
    let mut first_unused: HashMap<usize, (usize, Object)> = HashMap::new();
    for &o in domain.iter() {
        if used.contains(&o) {
            continue;
        }
        if let Some((class, rank)) = symmetries.by_object(o) {
            let entry = first_unused.entry(class).or_insert((rank, o));
            if rank < entry.0 {
                *entry = (rank, o);
            }
        }
    }
    domain.retain(|o| {
        used.contains(o)
            || match symmetries.by_object(*o) {
                None => true,
                Some((class, _)) => first_unused[&class].1 == *o,
            }
    });
}
