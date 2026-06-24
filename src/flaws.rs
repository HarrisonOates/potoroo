//! Plan flaws: open conditions, threatened links (unsafes), and the flaw enum.

use std::rc::Rc;

use crate::effect::Effect;
use crate::formula::{Formula, Literal};
use crate::orderings::StepTime;
use crate::plan::Link;
use crate::predicates::PredicateTable;

/// Time stamp on a literal open condition. For the classical subset only
/// `AtStart` is produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FormulaTime {
    AtStart,
}

impl FormulaTime {
    pub fn start_time(self) -> StepTime {
        StepTime::AtStart
    }

    pub fn end_time(self) -> StepTime {
        StepTime::AtStart
    }
}

/// An open condition: a subgoal of `step_id` not yet supported by a link.
#[derive(Debug, Clone)]
pub struct OpenCondition {
    pub step_id: usize,
    pub condition: Rc<Formula>,
    pub when: FormulaTime,
}

impl OpenCondition {
    /// Returns the literal of a literal open condition, if any.
    pub fn literal(&self) -> Option<Literal> {
        match self.condition.as_ref() {
            Formula::Atom(a) => Some(Literal::Atom(a.clone())),
            Formula::Negation(a) => Some(Literal::Negation(a.clone())),
            _ => None,
        }
    }

    pub fn inequality(&self) -> Option<(crate::terms::Term, crate::terms::Term)> {
        match self.condition.as_ref() {
            Formula::Inequality { left, right, .. } => Some((*left, *right)),
            _ => None,
        }
    }

    pub fn disjunction(&self) -> Option<&[Rc<Formula>]> {
        match self.condition.as_ref() {
            Formula::Disjunction(ds) => Some(ds),
            _ => None,
        }
    }

    /// Checks if this is a static (non-goal) literal open condition.
    pub fn is_static(&self, predicates: &PredicateTable) -> bool {
        if self.step_id == crate::plan::GOAL_ID {
            return false;
        }
        match self.literal() {
            Some(l) => predicates.is_static(l.atom().predicate),
            None => false,
        }
    }
}

/// Structural identity for chain removal. Open conditions in a plan are unique
/// by `(step_id, condition)`; identity is by pointer equality on the `Rc`.
impl PartialEq for OpenCondition {
    fn eq(&self, other: &Self) -> bool {
        self.step_id == other.step_id
            && self.when == other.when
            && Rc::ptr_eq(&self.condition, &other.condition)
    }
}

/// A threatened causal link: `step_id`'s `effect` may clobber `link`.
#[derive(Debug, Clone)]
pub struct Unsafe {
    pub link: Link,
    pub step_id: usize,
    pub effect: Effect,
}

/// Structural identity for chain removal. A plan never holds two structurally
/// identical unsafes.
impl PartialEq for Unsafe {
    fn eq(&self, other: &Self) -> bool {
        self.link == other.link
            && self.step_id == other.step_id
            && self.effect.literal == other.effect.literal
            && Rc::ptr_eq(&self.effect.condition, &other.effect.condition)
            && self.effect.when == other.effect.when
            && self.effect.parameters == other.effect.parameters
    }
}

/// A plan flaw (`OpenCondition` or `Unsafe`).
#[derive(Debug, Clone)]
pub enum Flaw {
    Unsafe(Unsafe),
    OpenCondition(OpenCondition),
}
