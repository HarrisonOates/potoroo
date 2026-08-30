//! Actions: lifted schemas and ground actions.

use std::rc::Rc;

use crate::effect::Effect;
use crate::formula::Formula;
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
    /// Declared PDDL action cost. Costless classical domains use one.
    pub cost: usize,
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
