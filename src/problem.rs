//! Lowered PDDL problems.

use std::collections::HashSet;
use std::rc::Rc;

use crate::expressions::Fluent;
use crate::formula::{Atom, Formula};
use crate::terms::TermTable;

/// Supported classical optimization metric.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Metric {
    MinimizeTotalCost,
}

/// A lowered problem.
///
/// The problem borrows nothing from its domain directly; instead it records the
/// referenced domain name and its `objects` table is constructed as an extension
/// of the domain's constant table (see [`crate::terms::TermTable::with_parent`]).
#[derive(Debug)]
pub struct Problem {
    pub name: String,
    /// Name of the domain this problem refers to (`:domain X`).
    pub domain_name: String,
    /// Problem objects, extending the domain constants.
    pub objects: TermTable,
    pub init_atoms: HashSet<Atom>,
    /// Initial atoms in PDDL declaration order. The order is observable through
    /// achiever-map iteration and plan-id tie-breaking, so we preserve it
    /// alongside the set used for membership tests.
    pub init_order: Vec<Atom>,
    /// Initial general numeric fluent assignments. The supported total-cost
    /// initialization is normalized away during lowering.
    pub init_values: Vec<(Fluent, f64)>,
    pub goal: Rc<Formula>,
    /// Types of any variables introduced while lowering the goal (existential
    /// quantifiers), indexed by variable index. Used for type reasoning at the
    /// goal step.
    pub goal_var_types: Vec<crate::types::Type>,
    /// Optional optimization metric. The classical subset supports only
    /// `(:metric minimize (total-cost))`.
    pub metric: Option<Metric>,
}
