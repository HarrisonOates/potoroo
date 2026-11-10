//! Schematic mutex invariants for lifted FDR variables
//! (Helmert, AIJ 2009, §5.1; Fišer, AAAI 2020).
//!
//! A candidate is a set of lifted atoms over shared invariant parameters and
//! per-part counted positions. It is an invariant when at most one member per
//! invariant assignment holds initially and every schema that adds a member
//! also deletes a required member of the same instance. Unlike
//! [`crate::lifted_mutex`], one schema may add into several instances when no
//! two of them can co-designate, by object identity, disjoint types or a
//! precondition inequality. That admits groups such as sokoban's
//! `at(?thing, ·)`, where `push` moves the player and a stone at once.
//!
//! The planners using `lifted_mutex` are unaffected: this synthesis serves
//! only the lifted FDR compiler.

use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

use crate::domain::Domain;
use crate::formula::{Atom, Formula, Literal};
use crate::predicates::Predicate;
use crate::problem::Problem;
use crate::terms::{Object, Term};
use crate::types::Type;

const MAX_PARTS: usize = 4;
const MAX_CANDIDATES: usize = 20_000;

/// A part's argument position: invariant parameter `i`, or counted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ISlot {
    Param(usize),
    Counted,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IPart {
    pub predicate: Predicate,
    pub slots: Vec<ISlot>,
}

/// At most one member holds per assignment of the `arity` invariant
/// parameters, in every reachable state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Invariant {
    pub arity: usize,
    pub parts: Vec<IPart>,
}

impl Invariant {
    fn key(&self) -> (usize, Vec<IPart>) {
        let mut parts = self.parts.clone();
        parts.sort();
        (self.arity, parts)
    }
}

struct SchemaFacts {
    adds: Vec<Atom>,
    deletes: Vec<Atom>,
    uncertain: HashSet<Predicate>,
    required: Vec<Atom>,
    var_types: Vec<Type>,
    inequalities: HashSet<(Term, Term)>,
}

/// Synthesises invariants over the fluent predicates of `domain`.
pub fn synthesise(
    domain: &Domain,
    problem: &Problem,
    fluent: &HashSet<Predicate>,
) -> Vec<Invariant> {
    let schemas: Vec<SchemaFacts> = domain
        .actions
        .iter()
        .map(|action| {
            let mut adds = Vec::new();
            let mut deletes = Vec::new();
            let mut uncertain = HashSet::new();
            for effect in &action.effects {
                let atom = effect.literal.atom().clone();
                if effect.conditional() || !effect.parameters.is_empty() {
                    uncertain.insert(atom.predicate);
                    continue;
                }
                match &effect.literal {
                    Literal::Atom(_) => adds.push(atom),
                    Literal::Negation(_) => deletes.push(atom),
                }
            }
            let mut required = Vec::new();
            let mut inequalities = HashSet::new();
            entailed(&action.precondition, &mut required, &mut inequalities);
            SchemaFacts {
                adds,
                deletes,
                uncertain,
                required,
                var_types: action.var_types.clone(),
                inequalities,
            }
        })
        .collect();
    let mut objects: HashMap<Type, HashSet<Object>> = HashMap::new();
    let mut objects_of = |ty: Type| -> HashSet<Object> {
        objects
            .entry(ty)
            .or_insert_with(|| {
                super::task::objects_of(domain, problem, ty)
                    .into_iter()
                    .collect()
            })
            .clone()
    };
    // Per schema, per pair of variables: may they co-designate?
    let can_equal = |schema: &SchemaFacts,
                     a: Term,
                     b: Term,
                     objects_of: &mut dyn FnMut(Type) -> HashSet<Object>| {
        if a == b {
            return true;
        }
        if schema.inequalities.contains(&(a, b)) || schema.inequalities.contains(&(b, a)) {
            return false;
        }
        match (a, b) {
            (Term::Object(x), Term::Object(y)) => x == y,
            (Term::Variable(v), Term::Object(o)) | (Term::Object(o), Term::Variable(v)) => {
                objects_of(schema.var_types[v.0 as usize]).contains(&o)
            }
            (Term::Variable(v), Term::Variable(w)) => {
                let left = objects_of(schema.var_types[v.0 as usize]);
                let right = objects_of(schema.var_types[w.0 as usize]);
                !left.is_disjoint(&right)
            }
        }
    };

    let mut queue = VecDeque::new();
    let mut seen = HashSet::new();
    let mut predicates: Vec<Predicate> = fluent.iter().copied().collect();
    predicates.sort_by_key(|p| p.0);
    for &predicate in &predicates {
        let arity = domain.predicates.parameters(predicate).len();
        for counted in (0..arity).map(Some).chain(std::iter::once(None)) {
            let mut slots = Vec::with_capacity(arity);
            let mut next = 0;
            for position in 0..arity {
                if Some(position) == counted {
                    slots.push(ISlot::Counted);
                } else {
                    slots.push(ISlot::Param(next));
                    next += 1;
                }
            }
            let candidate = Invariant {
                arity: next,
                parts: vec![IPart { predicate, slots }],
            };
            if seen.insert(candidate.key()) {
                queue.push_back(candidate);
            }
        }
    }

    let mut found = Vec::new();
    let mut tested = 0;
    'candidates: while let Some(candidate) = queue.pop_front() {
        tested += 1;
        if tested > MAX_CANDIDATES {
            break;
        }
        if !at_most_one_initially(&candidate, problem) {
            continue;
        }
        let mut refinements = Vec::new();
        let mut unbalanced = false;
        for schema in &schemas {
            if candidate
                .parts
                .iter()
                .any(|p| schema.uncertain.contains(&p.predicate))
            {
                continue 'candidates;
            }
            let mut entering: Vec<(usize, Vec<Term>)> = Vec::new();
            for (index, added) in schema.adds.iter().enumerate() {
                for part in &candidate.parts {
                    let mut sigma = vec![None; candidate.arity];
                    if match_lifted(part, added, &mut sigma) {
                        let Some(sigma) = sigma.into_iter().collect::<Option<Vec<Term>>>() else {
                            // Enters for every value of a parameter.
                            continue 'candidates;
                        };
                        entering.push((index, sigma));
                    }
                }
            }
            for (i, (left_add, left)) in entering.iter().enumerate() {
                for (right_add, right) in &entering[i + 1..] {
                    if left_add == right_add && left == right {
                        continue;
                    }
                    if left
                        .iter()
                        .zip(right)
                        .all(|(a, b)| can_equal(schema, *a, *b, &mut objects_of))
                    {
                        // Two members could enter one instance at once.
                        continue 'candidates;
                    }
                }
            }
            for (_, sigma) in &entering {
                let paired = schema.deletes.iter().any(|deleted| {
                    schema.required.contains(deleted)
                        && candidate.parts.iter().any(|part| {
                            let mut check: Vec<Option<Term>> =
                                sigma.iter().map(|t| Some(*t)).collect();
                            match_lifted(part, deleted, &mut check)
                                && check.iter().zip(sigma).all(|(c, s)| *c == Some(*s))
                        })
                });
                if paired {
                    continue;
                }
                unbalanced = true;
                for deleted in &schema.deletes {
                    if schema.required.contains(deleted) {
                        refinements.push(derive_part(deleted, sigma));
                    }
                }
            }
        }
        if !unbalanced {
            found.push(candidate);
            continue;
        }
        if candidate.parts.len() >= MAX_PARTS {
            continue;
        }
        for part in refinements {
            // Every part must name every invariant parameter, so that a
            // member identifies its instance.
            let names_all = (0..candidate.arity).all(|i| part.slots.contains(&ISlot::Param(i)));
            if !names_all || candidate.parts.contains(&part) || !fluent.contains(&part.predicate) {
                continue;
            }
            let mut refined = candidate.clone();
            refined.parts.push(part);
            if seen.insert(refined.key()) {
                queue.push_back(refined);
            }
        }
    }
    found
}

fn entailed(
    formula: &Rc<Formula>,
    atoms: &mut Vec<Atom>,
    inequalities: &mut HashSet<(Term, Term)>,
) {
    match formula.as_ref() {
        Formula::Atom(atom) => atoms.push(atom.clone()),
        Formula::Inequality { left, right, .. } => {
            inequalities.insert((*left, *right));
        }
        Formula::Conjunction(parts) => parts.iter().for_each(|p| entailed(p, atoms, inequalities)),
        _ => {}
    }
}

fn match_lifted(part: &IPart, atom: &Atom, sigma: &mut [Option<Term>]) -> bool {
    if part.predicate != atom.predicate || part.slots.len() != atom.terms.len() {
        return false;
    }
    for (slot, term) in part.slots.iter().zip(&atom.terms) {
        if let ISlot::Param(index) = slot {
            match sigma[*index] {
                Some(bound) if bound != *term => return false,
                Some(_) => {}
                None => sigma[*index] = Some(*term),
            }
        }
    }
    true
}

/// The part that lets `deleted` balance an add under `sigma`: terms the
/// assignment binds become its parameters, everything else is counted.
fn derive_part(deleted: &Atom, sigma: &[Term]) -> IPart {
    IPart {
        predicate: deleted.predicate,
        slots: deleted
            .terms
            .iter()
            .map(|term| match sigma.iter().position(|bound| bound == term) {
                Some(index) => ISlot::Param(index),
                None => ISlot::Counted,
            })
            .collect(),
    }
}

fn at_most_one_initially(candidate: &Invariant, problem: &Problem) -> bool {
    let mut members: HashMap<Vec<Object>, &Atom> = HashMap::new();
    for atom in &problem.init_order {
        for part in &candidate.parts {
            if part.predicate != atom.predicate {
                continue;
            }
            let mut key = vec![None; candidate.arity];
            let mut ok = true;
            for (slot, term) in part.slots.iter().zip(&atom.terms) {
                if let ISlot::Param(i) = slot {
                    let o = term.as_object();
                    match key[*i] {
                        Some(bound) if bound != o => ok = false,
                        _ => key[*i] = Some(o),
                    }
                }
            }
            if !ok {
                continue;
            }
            let key: Vec<Object> = key.into_iter().map(|o| o.expect("bound")).collect();
            if let Some(previous) = members.insert(key, atom) {
                if previous != atom {
                    return false;
                }
            }
        }
    }
    true
}
