//! Lifted finite-domain tasks (Helmert, AIJ 2009, §5, applied schematically).
//!
//! A schematic invariant ([`super::invariants`]) with invariant parameters `x̄` becomes a schematic
//! variable `G(x̄)`. Its values are the group's parts over their counted
//! arguments, plus `none` unless the group is proved exactly-one. Fluent
//! predicates no chosen group covers become binary variables over all their
//! arguments. Predicates no effect mentions stay static atoms.
//!
//! Schemas are rewritten to conditions `G(t̄)=v` and assignments `G(t̄):=v`.
//! A delete paired with an add on the syntactically same instance disappears
//! into the add; an unpaired delete assigns `none`. The rewrite is exact for
//! the supported fragment: conjunctive preconditions over positive atoms,
//! negated binary atoms and (in)equalities, and unconditional effects. Anything
//! else is rejected with [`Unsupported`].

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use crate::domain::Domain;
use crate::formula::{Atom, Formula, Literal};
use super::invariants::{ISlot, Invariant};
use crate::predicates::Predicate;
use crate::problem::Problem;
use crate::terms::{Object, Term, Variable};
use crate::types::Type;

/// Why a task is outside the supported fragment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unsupported(pub String);

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unsupported by --lifted-fdr: {}; use --fdr-pocl", self.0)
    }
}

impl std::error::Error for Unsupported {}

/// One lifted atom of a variable: a predicate whose argument positions are
/// invariant parameters of the variable or counted value arguments.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarPart {
    pub predicate: Predicate,
    /// Per argument position: `Ok(i)` is invariant parameter `i`, `Err(j)` is
    /// counted argument `j` of the value.
    pub slots: Vec<Result<usize, usize>>,
    /// Number of counted arguments.
    pub counted: usize,
}

/// A schematic state variable `G(x̄)`.
#[derive(Debug, Clone)]
pub struct LVar {
    pub name: String,
    /// Number of invariant parameters.
    pub arity: usize,
    pub parts: Vec<VarPart>,
    /// Whether `none` is a value: false only for proved exactly-one groups.
    pub has_none: bool,
    /// Binary variables are uncovered fluent predicates: one part, no counted
    /// arguments.
    pub binary: bool,
}

/// A value term of a variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LValue {
    None,
    Part { part: u16, args: Vec<Term> },
}

impl LValue {
    pub fn ground(&self) -> bool {
        match self {
            LValue::None => true,
            LValue::Part { args, .. } => args.iter().all(|t| t.object()),
        }
    }
}

/// `var(inv) = value`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LFact {
    pub var: u32,
    pub inv: Vec<Term>,
    pub value: LValue,
}

impl LFact {
    pub fn ground(&self) -> bool {
        self.inv.iter().all(|t| t.object()) && self.value.ground()
    }
}

/// `var(inv) := value`. A schema's `none` assignments come first and take
/// effect before its value assignments, so when a deleted and an added instance
/// co-designate the add wins. Optionally requiring the condition at `pre` (an index
/// into the schema's conditions on the same instance).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assign {
    pub fact: LFact,
    pub pre: Option<usize>,
}

/// A rewritten action schema.
#[derive(Debug, Clone)]
pub struct LSchema {
    /// Index into `Domain::actions`.
    pub action: usize,
    pub name: String,
    pub parameters: Vec<Variable>,
    /// Emptied by compilation: variables are global, typed by
    /// [`LiftedTask::var_types`].
    pub var_types: Vec<Type>,
    /// The schema's global variables are `var_base .. var_base + var_count`.
    pub var_base: u32,
    pub var_count: u32,
    pub conditions: Vec<LFact>,
    pub statics: Vec<Atom>,
    /// Static atoms that must be false.
    pub negated_statics: Vec<Atom>,
    pub equalities: Vec<(Term, Term)>,
    pub inequalities: Vec<(Term, Term)>,
    pub assigns: Vec<Assign>,
    pub cost: usize,
}

/// A ground instance key: variable and invariant arguments.
pub type Instance = (u32, Vec<Object>);

/// A lifted finite-domain task.
#[derive(Debug, Clone)]
pub struct LiftedTask {
    pub vars: Vec<LVar>,
    pub schemas: Vec<LSchema>,
    /// Instances with a true member initially; absent instances are `none`.
    pub init: HashMap<Instance, LValue>,
    pub goal: Vec<LFact>,
    pub goal_inequalities: Vec<(Term, Term)>,
    pub goal_equalities: Vec<(Term, Term)>,
    /// Static atoms true initially.
    pub static_atoms: HashSet<Atom>,
    /// Fluent predicate -> (variable, part).
    pub covered: HashMap<Predicate, (u32, u16)>,
    /// Types of the global schema variables. Each schema's variables are
    /// renumbered into a disjoint range, so a variable's type does not depend
    /// on the step it is scoped to.
    pub var_types: Vec<Type>,
    /// A static goal atom is false initially.
    pub unsolvable: bool,
}

impl LiftedTask {
    /// Compiles `domain` and `problem`.
    pub fn compile(domain: &Domain, problem: &Problem) -> Result<Self, Unsupported> {
        let fluent = fluent_predicates(domain);
        let invariants = super::invariants::synthesise(domain, problem, &fluent);
        let negated = negated_predicates(domain, problem)?;
        let mut task = LiftedTask {
            vars: Vec::new(),
            schemas: Vec::new(),
            init: HashMap::new(),
            goal: Vec::new(),
            goal_inequalities: Vec::new(),
            goal_equalities: Vec::new(),
            static_atoms: HashSet::new(),
            covered: HashMap::new(),
            var_types: Vec::new(),
            unsolvable: false,
        };
        task.choose_cover(domain, &invariants, &fluent, &negated);
        for (index, action) in domain.actions.iter().enumerate() {
            // One schema per disjunct of the precondition's DNF.
            let branches = dnf(&action.precondition)
                .ok_or_else(|| Unsupported(format!("a quantifier or over {MAX_BRANCHES} disjuncts in {}", action.name)))?;
            for branch in branches {
                let precondition = Formula::Conjunction(branch);
                let mut schema = task.rewrite_schema(domain, index, action, &precondition)?;
                globalise(&mut schema, &mut task.var_types);
                task.schemas.push(schema);
            }
        }
        for atom in &problem.init_order {
            if !fluent.contains(&atom.predicate) {
                task.static_atoms.insert(atom.clone());
                continue;
            }
            let fact = task.fact_of(atom);
            let key = (fact.var, fact.inv.iter().map(|t| t.as_object()).collect());
            if let Some(previous) = task.init.insert(key, fact.value.clone()) {
                if previous != fact.value {
                    return Err(Unsupported(format!(
                        "two initial members of one instance of {}",
                        task.vars[fact.var as usize].name
                    )));
                }
            }
        }
        task.compile_goal(domain, &problem.goal)?;
        task.prove_exactly_one(domain, problem);
        Ok(task)
    }

    /// Greedy cover, largest groups first: each fluent predicate belongs to at
    /// most one variable. Groups with constant slots, a predicate repeated in
    /// a group, or a negated predicate in a multi-valued position are skipped.
    fn choose_cover(
        &mut self,
        domain: &Domain,
        invariants: &[Invariant],
        fluent: &HashSet<Predicate>,
        negated: &HashSet<Predicate>,
    ) {
        let mut groups: Vec<&Invariant> = invariants.iter().collect();
        // Largest first; among equals, fewer invariant parameters (fewer,
        // larger variables), then synthesis order.
        groups.sort_by_key(|g| (std::cmp::Reverse(g.parts.len()), g.arity));
        for group in groups {
            let predicates: Vec<Predicate> = group.parts.iter().map(|p| p.predicate).collect();
            let mut distinct = predicates.clone();
            distinct.sort_by_key(|p| p.0);
            distinct.dedup();
            if distinct.len() != predicates.len()
                || predicates.iter().any(|p| self.covered.contains_key(p) || !fluent.contains(p))
                || predicates.iter().any(|p| negated.contains(p))
            {
                continue;
            }
            let var = self.vars.len() as u32;
            let mut parts = Vec::new();
            for (index, part) in group.parts.iter().enumerate() {
                let mut counted = 0;
                let slots = part
                    .slots
                    .iter()
                    .map(|slot| match slot {
                        ISlot::Param(i) => Ok(*i),
                        ISlot::Counted => {
                            counted += 1;
                            Err(counted - 1)
                        }
                    })
                    .collect();
                parts.push(VarPart {
                    predicate: part.predicate,
                    slots,
                    counted,
                });
                self.covered.insert(part.predicate, (var, index as u16));
            }
            let name = format!(
                "G{}[{}]",
                var,
                predicates
                    .iter()
                    .map(|p| domain.predicates.name(*p))
                    .collect::<Vec<_>>()
                    .join(",")
            );
            self.vars.push(LVar {
                name,
                arity: group.arity,
                parts,
                has_none: true,
                binary: false,
            });
        }
        let mut uncovered: Vec<Predicate> = fluent
            .iter()
            .copied()
            .filter(|p| !self.covered.contains_key(p))
            .collect();
        uncovered.sort_by_key(|p| p.0);
        for predicate in uncovered {
            let arity = domain.predicates.parameters(predicate).len();
            let var = self.vars.len() as u32;
            self.vars.push(LVar {
                name: domain.predicates.name(predicate).to_string(),
                arity,
                parts: vec![VarPart {
                    predicate,
                    slots: (0..arity).map(Ok).collect(),
                    counted: 0,
                }],
                has_none: true,
                binary: true,
            });
            self.covered.insert(predicate, (var, 0));
        }
    }

    /// The fact an atom of a covered predicate denotes.
    pub fn fact_of(&self, atom: &Atom) -> LFact {
        let (var, part) = self.covered[&atom.predicate];
        let vp = &self.vars[var as usize].parts[part as usize];
        let arity = self.vars[var as usize].arity;
        let mut inv = vec![None; arity];
        let mut args = vec![None; vp.counted];
        for (slot, term) in vp.slots.iter().zip(&atom.terms) {
            match slot {
                Ok(i) => inv[*i] = Some(*term),
                Err(j) => args[*j] = Some(*term),
            }
        }
        LFact {
            var,
            inv: inv.into_iter().map(|t| t.expect("every invariant parameter occurs")).collect(),
            value: LValue::Part {
                part,
                args: args.into_iter().map(|t| t.expect("counted slot")).collect(),
            },
        }
    }

    /// The atom a part value denotes, or `None` for the `none` value.
    pub fn atom_of(&self, fact: &LFact) -> Option<Atom> {
        let LValue::Part { part, args } = &fact.value else {
            return None;
        };
        let vp = &self.vars[fact.var as usize].parts[*part as usize];
        Some(Atom {
            predicate: vp.predicate,
            terms: vp
                .slots
                .iter()
                .map(|slot| match slot {
                    Ok(i) => fact.inv[*i],
                    Err(j) => args[*j],
                })
                .collect(),
        })
    }

    fn rewrite_schema(
        &self,
        domain: &Domain,
        index: usize,
        action: &crate::action::ActionSchema,
        precondition: &Formula,
    ) -> Result<LSchema, Unsupported> {
        let mut schema = LSchema {
            action: index,
            name: action.name.clone(),
            parameters: action.parameters.clone(),
            var_types: action.var_types.clone(),
            conditions: Vec::new(),
            statics: Vec::new(),
            negated_statics: Vec::new(),
            equalities: Vec::new(),
            inequalities: Vec::new(),
            assigns: Vec::new(),
            cost: action.cost,
            var_base: 0,
            var_count: 0,
        };
        if !action.cost_specs.is_empty() || !action.conditional_costs.is_empty() {
            if action.cost_specs.iter().any(|s| !s.is_argument_free()) || !action.conditional_costs.is_empty() {
                return Err(Unsupported(format!("parameter-dependent cost in {}", action.name)));
            }
        }
        let mut literals = Vec::new();
        flatten(precondition, &mut literals, &mut schema.equalities, &mut schema.inequalities)
            .map_err(|what| Unsupported(format!("{what} in the precondition of {}", action.name)))?;
        for (positive, atom) in literals {
            if domain.predicates.is_static(atom.predicate) || !self.covered.contains_key(&atom.predicate) {
                if positive {
                    schema.statics.push(atom);
                } else {
                    schema.negated_statics.push(atom);
                }
                continue;
            }
            let fact = if positive {
                self.fact_of(&atom)
            } else {
                let (var, _) = self.covered[&atom.predicate];
                if !self.vars[var as usize].binary {
                    return Err(Unsupported(format!("negated group atom in {}", action.name)));
                }
                LFact {
                    var,
                    inv: atom.terms.clone(),
                    value: LValue::None,
                }
            };
            if let Some(existing) = schema
                .conditions
                .iter()
                .find(|c| c.var == fact.var && c.inv == fact.inv)
            {
                if *existing != fact {
                    // Two different values for one instance: never applicable.
                    return Err(Unsupported(format!("contradictory precondition in {}", action.name)));
                }
                continue;
            }
            schema.conditions.push(fact);
        }
        let mut adds: Vec<LFact> = Vec::new();
        let mut deletes: Vec<LFact> = Vec::new();
        for effect in &action.effects {
            if !effect.parameters.is_empty() || effect.conditional() {
                return Err(Unsupported(format!("conditional or quantified effect in {}", action.name)));
            }
            match &effect.literal {
                Literal::Atom(atom) => adds.push(self.fact_of(atom)),
                Literal::Negation(atom) => deletes.push(self.fact_of(atom)),
            }
        }
        for add in &adds {
            if adds.iter().filter(|a| a.var == add.var && a.inv == add.inv).count() > 1 {
                return Err(Unsupported(format!("two adds on one instance in {}", action.name)));
            }
            let pre = schema
                .conditions
                .iter()
                .position(|c| c.var == add.var && c.inv == add.inv);
            schema.assigns.push(Assign {
                fact: add.clone(),
                pre,
            });
        }
        // Deletes take effect before adds (STRIPS semantics), so `none`
        // assignments precede value assignments. A delete on the syntactically
        // same instance as an add is subsumed by it.
        let mut nones = Vec::new();
        for delete in &deletes {
            if adds.iter().any(|a| a.var == delete.var && a.inv == delete.inv)
                || nones.iter().any(|a: &Assign| a.fact.var == delete.var && a.fact.inv == delete.inv)
            {
                continue;
            }
            let pre = schema
                .conditions
                .iter()
                .position(|c| c.var == delete.var && c.inv == delete.inv);
            // STRIPS deletes only the named atom: when the precondition does
            // not pin the instance to it, another member may hold and survive.
            let pinned = pre.is_some_and(|p| schema.conditions[p].value == delete.value);
            if !pinned && !self.vars[delete.var as usize].binary {
                return Err(Unsupported(format!("delete of an unrequired group atom in {}", action.name)));
            }
            nones.push(Assign {
                fact: LFact {
                    var: delete.var,
                    inv: delete.inv.clone(),
                    value: LValue::None,
                },
                pre,
            });
        }
        nones.append(&mut schema.assigns);
        schema.assigns = nones;
        Ok(schema)
    }

    fn compile_goal(&mut self, domain: &Domain, goal: &Formula) -> Result<(), Unsupported> {
        let mut literals = Vec::new();
        flatten(goal, &mut literals, &mut self.goal_equalities, &mut self.goal_inequalities)
            .map_err(|what| Unsupported(format!("{what} in the goal")))?;
        for (positive, atom) in literals {
            if domain.predicates.is_static(atom.predicate) || !self.covered.contains_key(&atom.predicate) {
                // Static: decided by the initial state.
                if !atom.terms.iter().all(|t| t.object()) {
                    return Err(Unsupported("lifted static atom in the goal".into()));
                }
                if self.static_atoms.contains(&atom) != positive {
                    self.unsolvable = true;
                }
                continue;
            }
            let fact = if positive {
                self.fact_of(&atom)
            } else {
                let (var, _) = self.covered[&atom.predicate];
                if !self.vars[var as usize].binary {
                    return Err(Unsupported("negated group atom in the goal".into()));
                }
                LFact {
                    var,
                    inv: atom.terms.clone(),
                    value: LValue::None,
                }
            };
            if !self.goal.contains(&fact) {
                self.goal.push(fact);
            }
        }
        Ok(())
    }

    /// A group is exactly-one when every instance over its parameter types has
    /// an initial member and no schema assigns it `none`.
    fn prove_exactly_one(&mut self, domain: &Domain, problem: &Problem) {
        for var in 0..self.vars.len() {
            if self.vars[var].binary {
                continue;
            }
            if self
                .schemas
                .iter()
                .any(|s| s.assigns.iter().any(|a| a.fact.var == var as u32 && a.fact.value == LValue::None))
            {
                continue;
            }
            let Some(types) = self.parameter_types(domain, var) else {
                continue;
            };
            let mut instances: u64 = 1;
            for ty in &types {
                instances = instances.saturating_mul(objects_of(domain, problem, *ty).len() as u64);
            }
            let initial = self.init.keys().filter(|(v, _)| *v == var as u32).count() as u64;
            if initial == instances {
                self.vars[var].has_none = false;
            }
        }
    }

    /// Invariant parameter types, when every part agrees on them.
    pub fn parameter_types(&self, domain: &Domain, var: usize) -> Option<Vec<Type>> {
        let v = &self.vars[var];
        let mut types = vec![None; v.arity];
        for part in &v.parts {
            let signature = domain.predicates.parameters(part.predicate);
            for (slot, ty) in part.slots.iter().zip(signature) {
                if let Ok(i) = slot {
                    match types[*i] {
                        None => types[*i] = Some(*ty),
                        Some(t) if t == *ty => {}
                        Some(_) => return None,
                    }
                }
            }
        }
        types.into_iter().collect()
    }

    /// Human-readable fact, for diagnostics.
    pub fn fact_name(&self, domain: &Domain, problem: &Problem, fact: &LFact) -> String {
        let term = |t: &Term| match t {
            Term::Object(o) => problem.objects.object_name(Some(&domain.constants), *o).to_string(),
            Term::Variable(v) => format!("?{}", v.0),
        };
        let inv: Vec<String> = fact.inv.iter().map(term).collect();
        let value = match &fact.value {
            LValue::None => "none".to_string(),
            LValue::Part { part, args } => {
                let p = &self.vars[fact.var as usize].parts[*part as usize];
                let args: Vec<String> = args.iter().map(term).collect();
                format!("{}({})", domain.predicates.name(p.predicate), args.join(","))
            }
        };
        format!("{}({})={}", self.vars[fact.var as usize].name, inv.join(","), value)
    }
}

/// Renumbers a schema's variables into a fresh global range.
fn globalise(schema: &mut LSchema, var_types: &mut Vec<Type>) {
    let offset = var_types.len() as u32;
    var_types.extend(schema.var_types.iter().copied());
    schema.var_base = offset;
    schema.var_count = schema.var_types.len() as u32;
    let map = |t: &mut Term| {
        if let Term::Variable(v) = t {
            *v = Variable(v.0 + offset);
        }
    };
    let map_fact = |f: &mut LFact| {
        f.inv.iter_mut().for_each(map);
        if let LValue::Part { args, .. } = &mut f.value {
            args.iter_mut().for_each(map);
        }
    };
    schema.parameters.iter_mut().for_each(|v| *v = Variable(v.0 + offset));
    schema.conditions.iter_mut().for_each(map_fact);
    schema.assigns.iter_mut().for_each(|a| map_fact(&mut a.fact));
    for atom in schema.statics.iter_mut().chain(schema.negated_statics.iter_mut()) {
        atom.terms.iter_mut().for_each(map);
    }
    for (l, r) in schema.equalities.iter_mut().chain(schema.inequalities.iter_mut()) {
        map(l);
        map(r);
    }
    schema.var_types = Vec::new();
}

/// Objects of type `ty`, constants first.
pub fn objects_of(domain: &Domain, problem: &Problem, ty: Type) -> Vec<Object> {
    domain
        .constants
        .owned_objects()
        .chain(problem.objects.owned_objects())
        .filter(|(_, t)| domain.types.subtype(*t, ty))
        .map(|(o, _)| o)
        .collect()
}

fn fluent_predicates(domain: &Domain) -> HashSet<Predicate> {
    let mut fluent = HashSet::new();
    for action in &domain.actions {
        for effect in &action.effects {
            fluent.insert(effect.literal.atom().predicate);
        }
    }
    fluent
}

/// Predicates that occur negated in a precondition or the goal.
fn negated_predicates(domain: &Domain, problem: &Problem) -> Result<HashSet<Predicate>, Unsupported> {
    fn go(f: &Formula, out: &mut HashSet<Predicate>) {
        match f {
            Formula::Negation(a) => {
                out.insert(a.predicate);
            }
            Formula::Conjunction(fs) | Formula::Disjunction(fs) => fs.iter().for_each(|f| go(f, out)),
            Formula::Exists { body, .. } | Formula::Forall { body, .. } => go(body, out),
            _ => {}
        }
    }
    let mut out = HashSet::new();
    for action in &domain.actions {
        go(&action.precondition, &mut out);
    }
    go(&problem.goal, &mut out);
    Ok(out)
}

/// Largest number of disjuncts a precondition may expand to.
const MAX_BRANCHES: usize = 16;

/// Disjunctive normal form as conjunctions of literals and (in)equalities, or
/// `None` for quantifiers or more than [`MAX_BRANCHES`] disjuncts. An empty
/// list is unsatisfiable.
fn dnf(f: &Formula) -> Option<Vec<Vec<Rc<Formula>>>> {
    match f {
        Formula::True => Some(vec![Vec::new()]),
        Formula::False => Some(Vec::new()),
        Formula::Atom(_) | Formula::Negation(_) | Formula::Equality { .. } | Formula::Inequality { .. } => {
            Some(vec![vec![Rc::new(f.clone())]])
        }
        Formula::Conjunction(parts) => {
            let mut out: Vec<Vec<Rc<Formula>>> = vec![Vec::new()];
            for part in parts {
                let branches = dnf(part)?;
                let mut next = Vec::new();
                for prefix in &out {
                    for branch in &branches {
                        let mut joined = prefix.clone();
                        joined.extend(branch.iter().cloned());
                        next.push(joined);
                    }
                }
                if next.len() > MAX_BRANCHES {
                    return None;
                }
                out = next;
            }
            Some(out)
        }
        Formula::Disjunction(parts) => {
            let mut out = Vec::new();
            for part in parts {
                out.extend(dnf(part)?);
                if out.len() > MAX_BRANCHES {
                    return None;
                }
            }
            Some(out)
        }
        Formula::Exists { .. } | Formula::Forall { .. } => None,
    }
}

/// Splits a conjunction into literals and (in)equalities.
fn flatten(
    f: &Formula,
    literals: &mut Vec<(bool, Atom)>,
    equalities: &mut Vec<(Term, Term)>,
    inequalities: &mut Vec<(Term, Term)>,
) -> Result<(), &'static str> {
    match f {
        Formula::True => Ok(()),
        Formula::False => Err("a contradiction"),
        Formula::Atom(a) => {
            literals.push((true, a.clone()));
            Ok(())
        }
        Formula::Negation(a) => {
            literals.push((false, a.clone()));
            Ok(())
        }
        Formula::Equality { left, right, .. } => {
            equalities.push((*left, *right));
            Ok(())
        }
        Formula::Inequality { left, right, .. } => {
            inequalities.push((*left, *right));
            Ok(())
        }
        Formula::Conjunction(fs) => fs
            .iter()
            .try_for_each(|f| flatten(f, literals, equalities, inequalities)),
        Formula::Disjunction(_) => Err("a disjunction"),
        Formula::Exists { .. } => Err("an existential"),
        Formula::Forall { .. } => Err("a universal"),
    }
}
