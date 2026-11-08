//! Plan ranking for lifted FDR search.
//!
//! ADD sums, over open conditions, the additive cost of the cheapest reachable
//! ground atom the condition's pattern admits under the plan's bindings
//! (the lifted planner's relaxed planning graph). A part value is its atom; a
//! `none` value (only negated binary atoms in the supported fragment) is the
//! atom's negation. A condition an existing step or the initial state may
//! supply consistently costs nothing under ADDR (reuse, as in the ground FDR
//! ADDR).

use std::rc::Rc;

use crate::domain::Domain;
use crate::params::Parameters;
use crate::planning_graph::{HeuristicValue, PlanningGraph};
use crate::problem::Problem;
use crate::search::SearchContext;

use super::plan::{reusable, Ctx, Plan};
use super::task::LValue;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// Number of open conditions.
    Oc,
    /// Additive cost of open conditions (VHPOP ADD; no reuse, as FDR `ADD`).
    Add,
    /// ADD where a condition an existing step already supplies costs nothing.
    Addr,
}

pub struct Estimator {
    kind: Kind,
    graph: Option<Rc<PlanningGraph>>,
}

impl Estimator {
    pub fn new(_ctx: &Ctx, domain: &Domain, problem: &Problem, kind: Kind) -> Self {
        let graph = match kind {
            Kind::Oc => None,
            Kind::Add | Kind::Addr => {
                let params = Parameters::default();
                let search = SearchContext::new(domain, problem, &params);
                Some(search.planning_graph())
            }
        };
        Estimator { kind, graph }
    }

    /// The planning-graph value of one open condition (infinite when no graph
    /// is built).
    pub fn open_value(&self, ctx: &Ctx, plan: &Plan, open: super::plan::Open) -> HeuristicValue {
        let Some(graph) = self.graph.as_ref() else {
            return HeuristicValue::ZERO;
        };
        let fact = ctx.condition(plan, open.consumer, open.cond);
        match &fact.value {
            LValue::Part { .. } => {
                let atom = ctx.task.atom_of(fact).expect("part value");
                graph.heuristic_value_atom(&atom, open.consumer, Some((&ctx.types, &plan.bindings)))
            }
            LValue::None => {
                let predicate = ctx.task.vars[fact.var as usize].parts[0].predicate;
                let atom = crate::formula::Atom {
                    predicate,
                    terms: fact.inv.clone(),
                };
                graph.heuristic_value_negation(&atom, open.consumer, Some((&ctx.types, &plan.bindings)))
            }
        }
    }

    pub fn estimate(&self, ctx: &Ctx, plan: &Plan) -> f32 {
        match self.kind {
            Kind::Oc => plan.num_opens as f32,
            Kind::Add | Kind::Addr => {
                let reuse = self.kind == Kind::Addr;
                let mut total = 0.0;
                for open in crate::chain::iter(&plan.opens) {
                    let value = self.open_value(ctx, plan, *open);
                    let cost = value.add_cost();
                    if cost == 0.0 {
                        continue;
                    }
                    let reused = reuse && reusable(ctx, plan, *open);
                    if !cost.is_finite() || cost >= i32::MAX as f32 {
                        if reused {
                            continue;
                        }
                        return f32::INFINITY;
                    }
                    if reused {
                        continue;
                    }
                    total += cost;
                }
                total
            }
        }
    }
}
