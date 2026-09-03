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
    /// Declared PDDL action cost, resolved against a problem. Costless
    /// classical domains use one. Equals `cost_base` until
    /// [`crate::parser::bind_action_costs`] folds in `cost_functions`.
    pub cost: usize,
    /// The constant part of the declared cost, i.e. the sum of the literal `N`
    /// in every `(increase (total-cost) N)`. Kept separately so cost binding
    /// stays idempotent when one domain is reused across several problems.
    pub cost_base: usize,
    /// Nullary functions summed into the cost by `(increase (total-cost) (f))`.
    /// Their values are state-independent and come from the problem's `:init`,
    /// so they can only be resolved once a problem is known.
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
