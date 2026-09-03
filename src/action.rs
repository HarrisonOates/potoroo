//! Actions: lifted schemas and ground actions.

use std::rc::Rc;

use crate::effect::Effect;
use crate::formula::Formula;
use crate::functions::Function;
use crate::terms::{Object, Variable};

/// A lifted action schema (an `:action` definition).
#[derive(Debug, Clone)]
pub struct ActionSchema {
    /// Unique id assigned during lowering.
    pub id: usize,
    pub name: String,
    /// Schema parameters, in declaration order.
    pub parameters: Vec<Variable>,
    /// Types of every variable in this schema's scope, indexed by variable
    /// index (parameters plus any quantified-effect variables). Snapshots the
    /// per-schema `TermTable` so binding/type reasoning works during search.
    pub var_types: Vec<crate::types::Type>,
    pub precondition: Rc<Formula>,
    pub effects: Vec<Effect>,
    /// Declared PDDL action cost. Costless classical domains use one. Equals
    /// `cost_base` until [`crate::parser::bind_action_costs`] resolves
    /// `cost_functions` against a problem.
    pub cost: usize,
    /// Sum of the literal `N` in every `(increase (total-cost) N)`. Kept apart
    /// from `cost` so rebinding is idempotent across problems.
    pub cost_base: usize,
    /// Nullary functions named by `(increase (total-cost) (f))`, resolved
    /// against a problem's `:init`.
    pub cost_functions: Vec<Function>,
}

/// A fully ground action, produced by instantiation.
#[derive(Debug, Clone)]
pub struct GroundAction {
    pub id: usize,
    pub name: String,
    pub arguments: Vec<Object>,
    pub precondition: Rc<Formula>,
    pub effects: Vec<Effect>,
    pub cost: usize,
}
