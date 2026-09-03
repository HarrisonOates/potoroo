//! Logical formulas.
//!
//! Formulas are shared via [`Rc`]. The constructors flatten nested
//! conjunctions/disjunctions and short-circuit on `True`/`False`.
//! [`Formula::negation`] pushes negation inward via De Morgan and quantifier
//! duality.

use std::collections::HashMap;
use std::rc::Rc;

use crate::predicates::Predicate;
use crate::terms::{Term, Variable};

/// An atomic formula: a predicate applied to terms.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Atom {
    pub predicate: Predicate,
    pub terms: Vec<Term>,
}

/// A literal is a (possibly negated) atom.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Atom(Atom),
    Negation(Atom),
}

impl Literal {
    pub fn atom(&self) -> &Atom {
        match self {
            Literal::Atom(a) | Literal::Negation(a) => a,
        }
    }

    pub fn negative(&self) -> bool {
        matches!(self, Literal::Negation(_))
    }

    /// Returns the complementary literal.
    pub fn negate(&self) -> Literal {
        match self {
            Literal::Atom(a) => Literal::Negation(a.clone()),
            Literal::Negation(a) => Literal::Atom(a.clone()),
        }
    }

    /// Lifts this literal into a formula.
    pub fn to_formula(&self) -> Rc<Formula> {
        match self {
            Literal::Atom(a) => Rc::new(Formula::Atom(a.clone())),
            Literal::Negation(a) => Rc::new(Formula::Negation(a.clone())),
        }
    }
}

/// A logical formula.
#[derive(Debug, Clone)]
pub enum Formula {
    /// The tautology.
    True,
    /// The contradiction.
    False,
    /// A positive literal.
    Atom(Atom),
    /// A negative literal.
    Negation(Atom),
    /// Equality of two terms (`=`).
    ///
    /// `left_id`/`right_id` are the step ids the terms are scoped to. They are
    /// `None` for (in)equalities coming from action preconditions / goals (where
    /// the scoping step is supplied later by `add_goal`), and `Some(id)` for the
    /// separation (in)equalities synthesised during threat resolution, where the
    /// two terms belong to *different* steps.
    Equality {
        left: Term,
        left_id: Option<usize>,
        right: Term,
        right_id: Option<usize>,
    },
    /// Inequality of two terms (`(not (= ..))`).
    Inequality {
        left: Term,
        left_id: Option<usize>,
        right: Term,
        right_id: Option<usize>,
    },
    /// Conjunction (flattened).
    Conjunction(Vec<Rc<Formula>>),
    /// Disjunction (flattened).
    Disjunction(Vec<Rc<Formula>>),
    /// Existential quantification.
    Exists { params: Vec<Variable>, body: Rc<Formula> },
    /// Universal quantification.
    Forall { params: Vec<Variable>, body: Rc<Formula> },
}

impl Formula {
    pub fn tautology(&self) -> bool {
        matches!(self, Formula::True)
    }

    pub fn contradiction(&self) -> bool {
        matches!(self, Formula::False)
    }

    /// An equality with unscoped terms (ids resolved later by `add_goal`).
    pub fn equality(left: Term, right: Term) -> Rc<Formula> {
        Rc::new(Formula::Equality {
            left,
            left_id: None,
            right,
            right_id: None,
        })
    }

    /// An inequality with unscoped terms (ids resolved later by `add_goal`).
    pub fn inequality(left: Term, right: Term) -> Rc<Formula> {
        Rc::new(Formula::Inequality {
            left,
            left_id: None,
            right,
            right_id: None,
        })
    }

    /// Returns this formula with each free variable replaced according to
    /// `subst` (identity for variables not in the map). Used for forall-effect
    /// parameter renaming (variable→fresh variable) and universal-base expansion
    /// (variable→object). Quantifier-bound variables shadow the substitution
    /// within their body.
    pub fn substitute(self: &Rc<Formula>, subst: &HashMap<Variable, Term>) -> Rc<Formula> {
        if subst.is_empty() {
            return self.clone();
        }
        match self.as_ref() {
            Formula::True | Formula::False => self.clone(),
            Formula::Atom(a) => Rc::new(Formula::Atom(subst_atom(a, subst))),
            Formula::Negation(a) => Rc::new(Formula::Negation(subst_atom(a, subst))),
            Formula::Equality {
                left,
                left_id,
                right,
                right_id,
            } => Rc::new(Formula::Equality {
                left: subst_term(*left, subst),
                left_id: *left_id,
                right: subst_term(*right, subst),
                right_id: *right_id,
            }),
            Formula::Inequality {
                left,
                left_id,
                right,
                right_id,
            } => Rc::new(Formula::Inequality {
                left: subst_term(*left, subst),
                left_id: *left_id,
                right: subst_term(*right, subst),
                right_id: *right_id,
            }),
            Formula::Conjunction(cs) => {
                Rc::new(Formula::Conjunction(cs.iter().map(|c| c.substitute(subst)).collect()))
            }
            Formula::Disjunction(ds) => {
                Rc::new(Formula::Disjunction(ds.iter().map(|d| d.substitute(subst)).collect()))
            }
            Formula::Exists { params, body } => {
                let inner = shadowed(subst, params);
                Rc::new(Formula::Exists {
                    params: params.clone(),
                    body: body.substitute(&inner),
                })
            }
            Formula::Forall { params, body } => {
                let inner = shadowed(subst, params);
                Rc::new(Formula::Forall {
                    params: params.clone(),
                    body: body.substitute(&inner),
                })
            }
        }
    }

    /// Returns the formula that must hold for `effect_lit` to *not* interfere
    /// with this formula (a precondition) asserted at the same time — i.e. the
    /// disjunction of inequalities keeping them from denoting the same literal.
    /// Used by `strengthen_effects`.
    pub fn separator(self: &Rc<Formula>, effect_lit: &Literal) -> Rc<Formula> {
        match self.as_ref() {
            Formula::True | Formula::False => Rc::new(Formula::True),
            Formula::Atom(a) => sep_literal(false, a, effect_lit),
            Formula::Negation(a) => sep_literal(true, a, effect_lit),
            Formula::Equality { .. } | Formula::Inequality { .. } => Rc::new(Formula::True),
            Formula::Conjunction(cs) => {
                let mut result = Rc::new(Formula::True);
                for c in cs {
                    let s = c.separator(effect_lit);
                    if s.contradiction() {
                        return Rc::new(Formula::False);
                    }
                    result = Formula::and(result, s);
                }
                result
            }
            // `(!d | sep(d))` per disjunct: whichever one held stays true, since
            // we don't know which. Plain `!d` would assert none of them hold --
            // the negation of the precondition being separated.
            Formula::Disjunction(ds) => {
                let mut result = Rc::new(Formula::True);
                for d in ds {
                    let s = Formula::or(d.negation(), d.separator(effect_lit));
                    if s.contradiction() {
                        return Rc::new(Formula::False);
                    }
                    result = Formula::and(result, s);
                }
                result
            }
            Formula::Exists { body, .. } | Formula::Forall { body, .. } => {
                body.separator(effect_lit)
            }
        }
    }

    /// Conjoins two formulas, flattening nested conjunctions and simplifying
    /// against `True`/`False`.
    pub fn and(f1: Rc<Formula>, f2: Rc<Formula>) -> Rc<Formula> {
        if f1.contradiction() {
            return f1;
        }
        if f2.contradiction() {
            return f2;
        }
        if f1.tautology() {
            return f2;
        }
        if f2.tautology() {
            return f1;
        }
        let mut conjuncts = Vec::new();
        Self::push_conjuncts(&mut conjuncts, &f1);
        Self::push_conjuncts(&mut conjuncts, &f2);
        Rc::new(Formula::Conjunction(conjuncts))
    }

    fn push_conjuncts(out: &mut Vec<Rc<Formula>>, f: &Rc<Formula>) {
        match f.as_ref() {
            Formula::Conjunction(cs) => out.extend(cs.iter().cloned()),
            _ => out.push(f.clone()),
        }
    }

    /// Disjoins two formulas, flattening nested disjunctions and simplifying
    /// against `True`/`False`.
    pub fn or(f1: Rc<Formula>, f2: Rc<Formula>) -> Rc<Formula> {
        if f1.tautology() {
            return f1;
        }
        if f2.tautology() {
            return f2;
        }
        if f1.contradiction() {
            return f2;
        }
        if f2.contradiction() {
            return f1;
        }
        let mut disjuncts = Vec::new();
        Self::push_disjuncts(&mut disjuncts, &f1);
        Self::push_disjuncts(&mut disjuncts, &f2);
        Rc::new(Formula::Disjunction(disjuncts))
    }

    fn push_disjuncts(out: &mut Vec<Rc<Formula>>, f: &Rc<Formula>) {
        match f.as_ref() {
            Formula::Disjunction(ds) => out.extend(ds.iter().cloned()),
            _ => out.push(f.clone()),
        }
    }

    /// Builds the conjunction of a list, flattening and simplifying. The empty
    /// conjunction is `True`.
    pub fn conjoin_all<I: IntoIterator<Item = Rc<Formula>>>(items: I) -> Rc<Formula> {
        let mut acc = Rc::new(Formula::True);
        for f in items {
            acc = Formula::and(acc, f);
        }
        acc
    }

    /// Builds the disjunction of a list, flattening and simplifying. The empty
    /// disjunction is `False`.
    pub fn disjoin_all<I: IntoIterator<Item = Rc<Formula>>>(items: I) -> Rc<Formula> {
        let mut acc = Rc::new(Formula::False);
        for f in items {
            acc = Formula::or(acc, f);
        }
        acc
    }

    /// Returns the negation, pushing it inward via De Morgan / quantifier
    /// duality.
    pub fn negation(self: &Rc<Formula>) -> Rc<Formula> {
        match self.as_ref() {
            Formula::True => Rc::new(Formula::False),
            Formula::False => Rc::new(Formula::True),
            Formula::Atom(a) => Rc::new(Formula::Negation(a.clone())),
            Formula::Negation(a) => Rc::new(Formula::Atom(a.clone())),
            Formula::Equality {
                left,
                left_id,
                right,
                right_id,
            } => Rc::new(Formula::Inequality {
                left: *left,
                left_id: *left_id,
                right: *right,
                right_id: *right_id,
            }),
            Formula::Inequality {
                left,
                left_id,
                right,
                right_id,
            } => Rc::new(Formula::Equality {
                left: *left,
                left_id: *left_id,
                right: *right,
                right_id: *right_id,
            }),
            // De Morgan: !(a & b) == !a | !b.
            Formula::Conjunction(cs) => {
                Formula::disjoin_all(cs.iter().map(|c| c.negation()))
            }
            // De Morgan: !(a | b) == !a & !b.
            Formula::Disjunction(ds) => {
                Formula::conjoin_all(ds.iter().map(|d| d.negation()))
            }
            // !exists x. p == forall x. !p.
            Formula::Exists { params, body } => Rc::new(Formula::Forall {
                params: params.clone(),
                body: body.negation(),
            }),
            // !forall x. p == exists x. !p.
            Formula::Forall { params, body } => Rc::new(Formula::Exists {
                params: params.clone(),
                body: body.negation(),
            }),
        }
    }
}

/// The separator of a precondition literal (sign `precond_neg`, atom `a`)
/// against an effect literal: `True` if they cannot denote the same literal
/// (different sign/predicate, or a constant clash), `False` if they are forced
/// equal, else the disjunction of inequalities that keeps them apart.
fn sep_literal(precond_neg: bool, a: &Atom, effect_lit: &Literal) -> Rc<Formula> {
    if precond_neg != effect_lit.negative() {
        return Rc::new(Formula::True);
    }
    match atom_separator(a, effect_lit.atom()) {
        None => Rc::new(Formula::True),
        Some(f) => f,
    }
}

/// Unifies two atoms positionally, returning the disjunction of inequalities
/// needed to keep them distinct: `None` if they cannot unify (different
/// predicate/arity or a constant clash, so they are already distinct), `False`
/// if they are identical (cannot be separated), else the `OR` of `t1 != t2`
/// over the differing positions.
pub(crate) fn atom_separator(a1: &Atom, a2: &Atom) -> Option<Rc<Formula>> {
    if a1.predicate != a2.predicate || a1.terms.len() != a2.terms.len() {
        return None;
    }
    let mut disj: Option<Rc<Formula>> = None;
    for (&t1, &t2) in a1.terms.iter().zip(a2.terms.iter()) {
        match (t1, t2) {
            (Term::Object(o1), Term::Object(o2)) => {
                if o1 != o2 {
                    return None; // constant clash: cannot unify, already distinct
                }
            }
            _ => {
                let ineq = Formula::inequality(t1, t2);
                disj = Some(match disj {
                    None => ineq,
                    Some(d) => Formula::or(d, ineq),
                });
            }
        }
    }
    Some(disj.unwrap_or_else(|| Rc::new(Formula::False)))
}

fn subst_term(t: Term, subst: &HashMap<Variable, Term>) -> Term {
    match t {
        Term::Variable(v) => subst.get(&v).copied().unwrap_or(t),
        Term::Object(_) => t,
    }
}

fn subst_atom(a: &Atom, subst: &HashMap<Variable, Term>) -> Atom {
    Atom {
        predicate: a.predicate,
        terms: a.terms.iter().map(|&t| subst_term(t, subst)).collect(),
    }
}

/// Returns `subst` with the given quantifier-bound parameters removed (so they
/// are not substituted within the quantifier's body).
fn shadowed(subst: &HashMap<Variable, Term>, params: &[Variable]) -> HashMap<Variable, Term> {
    if params.is_empty() {
        return subst.clone();
    }
    subst
        .iter()
        .filter(|(v, _)| !params.contains(v))
        .map(|(&v, &t)| (v, t))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::terms::Object;

    fn atom(p: u32) -> Rc<Formula> {
        Rc::new(Formula::Atom(Atom {
            predicate: Predicate(p),
            terms: vec![Term::Object(Object(0))],
        }))
    }

    #[test]
    fn conjunction_flattens() {
        let inner = Formula::and(atom(0), atom(1));
        let outer = Formula::and(inner, atom(2));
        match outer.as_ref() {
            Formula::Conjunction(cs) => assert_eq!(cs.len(), 3),
            _ => panic!("expected flattened conjunction"),
        }
    }

    #[test]
    fn and_with_true_collapses() {
        let f = Formula::and(Rc::new(Formula::True), atom(0));
        assert!(matches!(f.as_ref(), Formula::Atom(_)));
    }

    #[test]
    fn de_morgan() {
        let conj = Formula::and(atom(0), atom(1));
        let neg = conj.negation();
        match neg.as_ref() {
            Formula::Disjunction(ds) => {
                assert_eq!(ds.len(), 2);
                assert!(ds.iter().all(|d| matches!(d.as_ref(), Formula::Negation(_))));
            }
            _ => panic!("expected disjunction of negations"),
        }
    }

    #[test]
    fn quantifier_duality() {
        let body = atom(0);
        let exists = Rc::new(Formula::Exists {
            params: vec![Variable(0)],
            body,
        });
        match exists.negation().as_ref() {
            Formula::Forall { body, .. } => assert!(matches!(body.as_ref(), Formula::Negation(_))),
            _ => panic!("expected forall"),
        }
    }
}
