//! Action effects.
//!
//! A single [`Effect`] adds or deletes one literal. Conditional effects carry a
//! non-`True` [`condition`](Effect::condition); universally quantified effects
//! carry [`parameters`](Effect::parameters). Classical effects are always
//! `AtEnd`.

use std::rc::Rc;

use crate::formula::{atom_separator, Formula, Literal};
use crate::terms::Variable;

/// Temporal annotation for an effect. For the classical subset only
/// [`AtEnd`](EffectTime::AtEnd) is produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectTime {
    AtStart,
    AtEnd,
}

/// A single effect: under `condition`, asserts `literal`.
#[derive(Debug, Clone)]
pub struct Effect {
    /// Universally quantified variables (from `(forall ...)`).
    pub parameters: Vec<Variable>,
    /// Condition guarding the effect; `True` for unconditional effects.
    pub condition: Rc<Formula>,
    pub literal: Literal,
    pub when: EffectTime,
    /// Extra condition synthesised by `strengthen_effects` so an effect does not
    /// clobber a same-step effect or the action's own precondition (e.g. the
    /// `(not (= ?from ?to))` on `move`'s effects). Added as a goal at link time
    /// and used to prune impossible threats.
    pub link_condition: Rc<Formula>,
}

impl Effect {
    /// Constructs an unconditional, unquantified `AtEnd` effect.
    pub fn new(literal: Literal) -> Self {
        Effect {
            parameters: Vec::new(),
            condition: Rc::new(Formula::True),
            literal,
            when: EffectTime::AtEnd,
            link_condition: Rc::new(Formula::True),
        }
    }

    pub fn conditional(&self) -> bool {
        !self.condition.tautology()
    }
}

/// Strengthens an action's effects by computing their `link_condition`s, so an
/// effect cannot clobber a same-step effect or the action's own precondition.
/// This is essential for search efficiency: e.g. it gives `move`'s effects the
/// `(not (= ?from ?to))` condition, which propagates `?from != ?to` at link
/// time and prunes a huge number of otherwise-unconstrained plans.
pub fn strengthen_effects(effects: &mut [Effect], precondition: &Rc<Formula>) {
    // Part 1: separate each negative effect from same-time positive effects with
    // the same quantified parameters.
    let snapshot: Vec<Effect> = effects.to_vec();
    for ei in effects.iter_mut() {
        let neg = match &ei.literal {
            Literal::Negation(a) => a.clone(),
            Literal::Atom(_) => continue,
        };
        let mut cond = Rc::new(Formula::True);
        for ej in &snapshot {
            if cond.contradiction() {
                break;
            }
            let pos = match &ej.literal {
                Literal::Atom(a) => a,
                Literal::Negation(_) => continue,
            };
            if ei.when != ej.when || ei.parameters != ej.parameters {
                continue;
            }
            if let Some(sep) = atom_separator(&neg, pos) {
                // The negative effect only "fires" against this positive one when
                // they are separated, or the positive effect's condition fails.
                let term = Formula::or(sep, ej.condition.negation());
                cond = Formula::and(cond, term);
            }
        }
        if !cond.tautology() {
            ei.link_condition = Formula::and(ei.link_condition.clone(), cond);
        }
    }

    // Part 2: separate every effect from the action's precondition.
    for ei in effects.iter_mut() {
        let sep = precondition.separator(&ei.literal);
        ei.link_condition = Formula::and(ei.link_condition.clone(), sep);
    }
}
