//! Actions: lifted schemas and ground actions.

use std::rc::Rc;

use crate::effect::Effect;
use crate::formula::Formula;
use crate::functions::Function;
use crate::terms::{Object, Term, Variable};

/// One `(increase (total-cost) ...)` right-hand side.
#[derive(Debug, Clone)]
pub enum CostSpec {
    /// A literal `N`.
    Constant(usize),
    /// A function applied to terms in the schema's scope. `terms` is empty for
    /// the nullary `(increase (total-cost) (f))` form and holds the action's
    /// parameters for the IPC form `(increase (total-cost) (road-length ?a ?b))`.
    Fluent {
        function: Function,
        terms: Vec<Term>,
    },
}

impl CostSpec {
    /// Whether this cost is a single number known without any argument binding.
    pub fn is_argument_free(&self) -> bool {
        match self {
            CostSpec::Constant(_) => true,
            CostSpec::Fluent { terms, .. } => terms.is_empty(),
        }
    }
}

/// An `(increase (total-cost) ...)` guarded by a `when` or nested in a `forall`.
///
/// Recorded but priced at zero: whether the guard holds is a property of the
/// state the step is applied in, which a partial order does not fix. Zero keeps
/// the plan's `g` an admissible lower bound, in line with how an unbound
/// parameterised cost is priced. No IPC benchmark family uses this form.
#[derive(Debug, Clone)]
pub struct ConditionalCost {
    pub parameters: Vec<Variable>,
    pub condition: std::rc::Rc<Formula>,
    pub spec: CostSpec,
}

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
    pub effects: Vec<Rc<Effect>>,
    /// Declared PDDL action cost. Costless classical domains use one.
    ///
    /// Exact when every entry of `cost_specs` is argument-free. Otherwise it is
    /// the **minimum over compatible instances**: a lower bound on what any
    /// ground instance of this schema can cost, so a lifted step whose cost
    /// arguments are still unbound never over-prices the plan and A* stays
    /// admissible. Grounding resolves the exact value per instance.
    ///
    /// Equals `cost_base` until [`crate::parser::bind_action_costs`] resolves
    /// `cost_specs` against a problem.
    pub cost: usize,
    /// Sum of the literal `N` in every `(increase (total-cost) N)`. Kept apart
    /// from `cost` so rebinding is idempotent across problems.
    pub cost_base: usize,
    /// The non-constant `(increase (total-cost) ...)` terms, in occurrence
    /// order, resolved against a problem's `:init`.
    pub cost_specs: Vec<CostSpec>,
    /// Increases guarded by a `when`/`forall`. See [`ConditionalCost`].
    pub conditional_costs: Vec<ConditionalCost>,
}

impl ActionSchema {
    /// The exact cost of the ground instance binding this schema's parameters to
    /// `arguments`, or `None` when a cost function it names has no value for the
    /// resulting argument tuple. Callers fall back to [`ActionSchema::cost`],
    /// which is a lower bound.
    ///
    /// Conditional increases are excluded: see [`ConditionalCost`].
    pub fn instance_cost(
        &self,
        arguments: &[Object],
        values: &std::collections::HashMap<(Function, Vec<Object>), f64>,
    ) -> Option<usize> {
        if self.cost_specs.is_empty() {
            return Some(self.cost_base);
        }
        let mut binding: Vec<Option<Object>> = vec![None; self.var_types.len()];
        for (index, parameter) in self.parameters.iter().enumerate() {
            let slot = parameter.0 as usize;
            if slot < binding.len() {
                binding[slot] = arguments.get(index).copied();
            }
        }

        let mut cost = self.cost_base;
        for spec in &self.cost_specs {
            let add = match spec {
                CostSpec::Constant(n) => *n,
                CostSpec::Fluent { function, terms } => {
                    let mut applied = Vec::with_capacity(terms.len());
                    for term in terms {
                        applied.push(match term {
                            Term::Object(o) => *o,
                            Term::Variable(v) => (*binding.get(v.0 as usize)?)?,
                        });
                    }
                    let value = *values.get(&(*function, applied))?;
                    if !value.is_finite() || value < 0.0 || value.fract() != 0.0 {
                        return None;
                    }
                    value as usize
                }
            };
            cost = cost.checked_add(add)?;
        }
        Some(cost)
    }
}

/// A fully ground action, produced by instantiation.
#[derive(Debug, Clone)]
pub struct GroundAction {
    pub id: usize,
    pub name: String,
    pub arguments: Vec<Object>,
    pub precondition: Rc<Formula>,
    pub effects: Vec<Rc<Effect>>,
    pub cost: usize,
}
