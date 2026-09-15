//! Schema instantiation helpers shared by the search context and the planning
//! graph builder.

use std::rc::Rc;

use crate::effect::Effect;
use crate::fasthash::FastMap;
use crate::formula::{Atom, Formula, Literal};
use crate::terms::{Object, Term, Variable};
use crate::types::Type;

/// Whether a precondition's (in)equality literals are all satisfied by `subst`.
pub(crate) fn precondition_consistent(f: &Rc<Formula>, subst: &[Option<Object>]) -> bool {
    match f.as_ref() {
        Formula::Conjunction(cs) => cs.iter().all(|c| precondition_consistent(c, subst)),
        Formula::Equality { left, right, .. } => resolve(*left, subst) == resolve(*right, subst),
        Formula::Inequality { left, right, .. } => resolve(*left, subst) != resolve(*right, subst),
        _ => true,
    }
}

pub(crate) fn resolve(t: Term, subst: &[Option<Object>]) -> Term {
    match t {
        Term::Variable(v) => subst
            .get(v.0 as usize)
            .copied()
            .flatten()
            .map(Term::Object)
            .unwrap_or(t),
        Term::Object(_) => t,
    }
}

pub(crate) fn instantiate_formula(f: &Rc<Formula>, subst: &[Option<Object>]) -> Rc<Formula> {
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

pub(crate) fn instantiate_atom(a: &Atom, subst: &[Option<Object>]) -> Atom {
    Atom {
        predicate: a.predicate,
        terms: a.terms.iter().map(|&t| resolve(t, subst)).collect(),
    }
}

pub(crate) fn instantiate_effect(e: &Effect, subst: &[Option<Object>]) -> Effect {
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

/// The upper bound on how many instances one quantifier may expand into. Beyond
/// it the quantified conjunct is relaxed away rather than enumerated: dropping a
/// requirement can only make the graph more optimistic, so the estimate stays a
/// lower bound and no reachable action is ever discarded.
pub(crate) const QUANTIFIER_EXPANSION_BUDGET: usize = 4096;

/// Collects the variables bound by any quantifier in `f`.
///
/// The planning graph pre-computes an object domain per type; quantified
/// precondition variables need one just as schema parameters and
/// quantified-effect variables do.
pub(crate) fn quantified_variables(f: &Rc<Formula>, out: &mut Vec<Variable>) {
    match f.as_ref() {
        Formula::Exists { params, body } | Formula::Forall { params, body } => {
            out.extend_from_slice(params);
            quantified_variables(body, out);
        }
        Formula::Conjunction(fs) | Formula::Disjunction(fs) => {
            for f in fs {
                quantified_variables(f, out);
            }
        }
        _ => {}
    }
}

/// Instantiates `f` under `subst`, expanding quantifiers over their variables'
/// object domains: `exists` becomes a disjunction, `forall` a conjunction.
///
/// [`instantiate_formula`] keeps the binder, which is right for the lifted
/// search — the body's variables stay free and are resolved through the plan's
/// bindings. The planning graph has no bindings, and reads a ground atom's value
/// from a table keyed by ground atoms, so a surviving binder leaves free
/// variables that match no key and the whole formula reads as unreachable. That
/// discards every instance of the action, and with it any goal only that action
/// achieves.
///
/// Expanding here also gives the graph the right arithmetic for free: the
/// existing `Disjunction` value is the minimum over disjuncts and `Conjunction`
/// the sum over conjuncts, which is exactly `exists`/`forall` under h_add.
pub(crate) fn instantiate_formula_expanded(
    f: &Rc<Formula>,
    subst: &mut Vec<Option<Object>>,
    var_types: &[Type],
    type_domains: &FastMap<Type, Vec<Object>>,
) -> Rc<Formula> {
    match f.as_ref() {
        Formula::Conjunction(cs) => Formula::conjoin_all(
            cs.iter()
                .map(|c| instantiate_formula_expanded(c, subst, var_types, type_domains)),
        ),
        Formula::Disjunction(ds) => Formula::disjoin_all(
            ds.iter()
                .map(|d| instantiate_formula_expanded(d, subst, var_types, type_domains)),
        ),
        Formula::Exists { params, body } => {
            expand_quantifier(params, body, subst, var_types, type_domains, true)
        }
        Formula::Forall { params, body } => {
            expand_quantifier(params, body, subst, var_types, type_domains, false)
        }
        // No binder below this point: the cheaper substitution suffices.
        _ => instantiate_formula(f, subst),
    }
}

/// Expands one quantifier into the disjunction (`existential`) or conjunction of
/// its body over every combination of objects its variables admit. Returns
/// [`Formula::True`] when the expansion would exceed
/// [`QUANTIFIER_EXPANSION_BUDGET`] or a variable's domain is unknown, relaxing
/// the requirement away rather than reporting it unreachable.
fn expand_quantifier(
    params: &[Variable],
    body: &Rc<Formula>,
    subst: &mut Vec<Option<Object>>,
    var_types: &[Type],
    type_domains: &FastMap<Type, Vec<Object>>,
    existential: bool,
) -> Rc<Formula> {
    let mut domains: Vec<&[Object]> = Vec::with_capacity(params.len());
    let mut instances: usize = 1;
    for &v in params {
        let Some(ty) = var_types.get(v.0 as usize) else {
            return Rc::new(Formula::True);
        };
        let Some(domain) = type_domains.get(ty) else {
            return Rc::new(Formula::True);
        };
        instances = instances.saturating_mul(domain.len());
        if instances > QUANTIFIER_EXPANSION_BUDGET {
            return Rc::new(Formula::True);
        }
        domains.push(domain.as_slice());
    }

    // An empty domain leaves nothing to satisfy the body: no witness for
    // `exists`, and vacuous truth for `forall`.
    if instances == 0 {
        return Rc::new(if existential {
            Formula::False
        } else {
            Formula::True
        });
    }

    let saved: Vec<Option<Object>> = params
        .iter()
        .map(|v| subst.get(v.0 as usize).copied().flatten())
        .collect();

    let mut parts: Vec<Rc<Formula>> = Vec::with_capacity(instances);
    let mut odometer = vec![0usize; params.len()];
    loop {
        for (i, &v) in params.iter().enumerate() {
            let slot = v.0 as usize;
            if subst.len() <= slot {
                subst.resize(slot + 1, None);
            }
            subst[slot] = Some(domains[i][odometer[i]]);
        }
        parts.push(instantiate_formula_expanded(
            body,
            subst,
            var_types,
            type_domains,
        ));

        let mut digit = params.len();
        loop {
            if digit == 0 {
                // Every combination has been visited.
                for (i, &v) in params.iter().enumerate() {
                    subst[v.0 as usize] = saved[i];
                }
                return if existential {
                    Formula::disjoin_all(parts)
                } else {
                    Formula::conjoin_all(parts)
                };
            }
            digit -= 1;
            odometer[digit] += 1;
            if odometer[digit] < domains[digit].len() {
                break;
            }
            odometer[digit] = 0;
        }
    }
}
