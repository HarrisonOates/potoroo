//! Schema instantiation helpers shared by the search context and the planning
//! graph builder.

use std::collections::HashMap;
use std::rc::Rc;

use crate::effect::Effect;
use crate::formula::{Atom, Formula, Literal};
use crate::terms::{Object, Term, Variable};

/// Whether a precondition's (in)equality literals are all satisfied by `subst`.
pub(crate) fn precondition_consistent(f: &Rc<Formula>, subst: &HashMap<Variable, Object>) -> bool {
    match f.as_ref() {
        Formula::Conjunction(cs) => cs.iter().all(|c| precondition_consistent(c, subst)),
        Formula::Equality { left, right, .. } => resolve(*left, subst) == resolve(*right, subst),
        Formula::Inequality { left, right, .. } => resolve(*left, subst) != resolve(*right, subst),
        _ => true,
    }
}

pub(crate) fn resolve(t: Term, subst: &HashMap<Variable, Object>) -> Term {
    match t {
        Term::Variable(v) => subst.get(&v).map(|&o| Term::Object(o)).unwrap_or(t),
        Term::Object(_) => t,
    }
}

pub(crate) fn instantiate_formula(
    f: &Rc<Formula>,
    subst: &HashMap<Variable, Object>,
) -> Rc<Formula> {
    match f.as_ref() {
        Formula::True | Formula::False => f.clone(),
        Formula::Atom(a) => Rc::new(Formula::Atom(instantiate_atom(a, subst))),
        Formula::Negation(a) => Rc::new(Formula::Negation(instantiate_atom(a, subst))),
        Formula::Equality {
            left,
            left_id,
            right,
            right_id,
        } => Rc::new(Formula::Equality {
            left: resolve(*left, subst),
            left_id: *left_id,
            right: resolve(*right, subst),
            right_id: *right_id,
        }),
        Formula::Inequality {
            left,
            left_id,
            right,
            right_id,
        } => Rc::new(Formula::Inequality {
            left: resolve(*left, subst),
            left_id: *left_id,
            right: resolve(*right, subst),
            right_id: *right_id,
        }),
        Formula::Conjunction(cs) => {
            Formula::conjoin_all(cs.iter().map(|c| instantiate_formula(c, subst)))
        }
        Formula::Disjunction(ds) => {
            Formula::disjoin_all(ds.iter().map(|d| instantiate_formula(d, subst)))
        }
        Formula::Exists { params, body } => Rc::new(Formula::Exists {
            params: params.clone(),
            body: instantiate_formula(body, subst),
        }),
        Formula::Forall { params, body } => Rc::new(Formula::Forall {
            params: params.clone(),
            body: instantiate_formula(body, subst),
        }),
    }
}

pub(crate) fn instantiate_atom(a: &Atom, subst: &HashMap<Variable, Object>) -> Atom {
    Atom {
        predicate: a.predicate,
        terms: a.terms.iter().map(|&t| resolve(t, subst)).collect(),
    }
}

pub(crate) fn instantiate_effect(e: &Effect, subst: &HashMap<Variable, Object>) -> Effect {
    let literal = match &e.literal {
        Literal::Atom(a) => Literal::Atom(instantiate_atom(a, subst)),
        Literal::Negation(a) => Literal::Negation(instantiate_atom(a, subst)),
    };
    Effect {
        parameters: e.parameters.clone(),
        condition: instantiate_formula(&e.condition, subst),
        literal,
        when: e.when,
        link_condition: instantiate_formula(&e.link_condition, subst),
    }
}
