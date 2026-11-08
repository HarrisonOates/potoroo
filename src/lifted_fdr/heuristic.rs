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


use crate::bindings::StepVariable;
use crate::formula::Atom;
use crate::planning_graph::hv_min;
use crate::terms::{Object, Term};

use super::plan::{propagate_domains, reusable, Ctx, Plan};
use super::task::LValue;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// Number of open conditions.
    Oc,
    /// ADD over the graph's pattern minimum, ignoring narrowed domains
    /// (VHPOP's lifted ADD).
    Padd,
    /// Additive cost of open conditions (VHPOP ADD; no reuse, as FDR `ADD`).
    Add,
    /// ADD where a condition an existing step already supplies costs nothing.
    Addr,
}

pub use super::plan::Domains;

/// Largest product of narrowed domains enumerated per condition.
const ENUMERATION_LIMIT: usize = 512;

impl Kind {
    pub fn parse(name: &str) -> Result<Kind, String> {
        match name.to_ascii_uppercase().as_str() {
            "OC" => Ok(Kind::Oc),
            "ADD" => Ok(Kind::Add),
            "PADD" => Ok(Kind::Padd),
            "ADDR" => Ok(Kind::Addr),
            _ => Err(format!("unknown lifted FDR heuristic `{name}` (OC, ADD, PADD, ADDR)")),
        }
    }
}

pub struct Estimator {
    kind: Kind,
    /// Evaluate conditions over propagated binding domains (not for PADD).
    use_domains: bool,
    graph: Option<Rc<PlanningGraph>>,
}

impl Estimator {
    /// An estimator sharing the planning graph in `graph`, building it on
    /// first need.
    pub fn new_shared(
        domain: &Domain,
        problem: &Problem,
        kind: Kind,
        graph: &mut Option<Rc<PlanningGraph>>,
    ) -> Self {
        let needed = kind != Kind::Oc;
        if needed && graph.is_none() {
            let params = Parameters::default();
            let search = SearchContext::new(domain, problem, &params);
            *graph = Some(search.planning_graph());
        }
        Estimator {
            kind,
            graph: if needed { graph.clone() } else { None },
            use_domains: matches!(kind, Kind::Add | Kind::Addr),
        }
    }

    /// The planning-graph value of one open condition (infinite when no graph
    /// is built).
    pub fn open_value(&self, ctx: &Ctx, plan: &Plan, open: super::plan::Open) -> HeuristicValue {
        self.open_value_in(ctx, plan, open, None)
    }

    /// The planning-graph value of one open condition: the cheapest ground
    /// atom it admits. With `domains` (from [`propagate_domains`]), variables
    /// whose class the static and initial-state tables narrowed range over
    /// those objects only, enumerated when the product is small; other
    /// variables keep the graph's pattern minimum over type-compatible
    /// objects.
    pub fn open_value_in(
        &self,
        ctx: &Ctx,
        plan: &Plan,
        open: super::plan::Open,
        domains: Option<&Domains>,
    ) -> HeuristicValue {
        let Some(graph) = self.graph.as_ref() else {
            return HeuristicValue::ZERO;
        };
        let fact = ctx.condition(plan, open.consumer, open.cond);
        let (atom, negated) = match &fact.value {
            LValue::Part { .. } => (ctx.task.atom_of(fact).expect("part value"), false),
            LValue::None => (
                Atom {
                    predicate: ctx.task.vars[fact.var as usize].parts[0].predicate,
                    terms: fact.inv.clone(),
                },
                true,
            ),
        };
        let value_of = |atom: &Atom| {
            if negated {
                graph.heuristic_value_negation(atom, open.consumer, Some((&ctx.types, &plan.bindings)))
            } else {
                graph.heuristic_value_atom(atom, open.consumer, Some((&ctx.types, &plan.bindings)))
            }
        };
        let Some(domains) = domains else {
            return value_of(&atom);
        };
        // Positions per narrowed class.
        let b = &plan.bindings;
        let mut classes: Vec<(StepVariable, Vec<usize>, Vec<Object>)> = Vec::new();
        for (i, t) in atom.terms.iter().enumerate() {
            if let Term::Variable(v) = b.binding(*t, open.consumer) {
                let rep = b.representative(v, open.consumer);
                if let Some(domain) = domains.get(&rep) {
                    match classes.iter_mut().find(|(r, _, _)| *r == rep) {
                        Some((_, positions, _)) => positions.push(i),
                        None => {
                            let objects: Vec<Object> = domain.iter().collect();
                            classes.push((rep, vec![i], objects));
                        }
                    }
                }
            }
        }
        let product = classes.iter().try_fold(1usize, |acc, (_, _, d)| acc.checked_mul(d.len()));
        if classes.is_empty() || product.is_none_or(|p| p > ENUMERATION_LIMIT) {
            return value_of(&atom);
        }
        if product == Some(0) {
            return HeuristicValue::INFINITE;
        }
        let mut best = HeuristicValue::INFINITE;
        let mut index = vec![0usize; classes.len()];
        // Substitute bound terms once, so candidates that end up ground take
        // the graph's direct lookup instead of pattern resolution.
        let mut probe = atom.clone();
        for t in probe.terms.iter_mut() {
            *t = b.binding(*t, open.consumer);
        }
        loop {
            for (k, (_, positions, objects)) in classes.iter().enumerate() {
                for &p in positions {
                    probe.terms[p] = Term::Object(objects[index[k]]);
                }
            }
            best = hv_min(best, value_of(&probe));
            if best.zero() {
                return best;
            }
            let mut k = 0;
            loop {
                if k == classes.len() {
                    return best;
                }
                index[k] += 1;
                if index[k] < classes[k].2.len() {
                    break;
                }
                index[k] = 0;
                k += 1;
            }
        }
    }

    pub fn estimate(&self, ctx: &Ctx, plan: &Plan) -> f32 {
        match self.kind {
            Kind::Oc => plan.num_opens as f32,
            Kind::Add | Kind::Padd | Kind::Addr => {
                let reuse = self.kind == Kind::Addr;
                let domains = if !self.use_domains {
                    None
                } else if let Some(d) = &plan.domains {
                    Some(d.clone())
                } else {
                    match propagate_domains(ctx, plan) {
                        Some((_, d)) => Some(Rc::new(d)),
                        None => return f32::INFINITY,
                    }
                };
                let mut total = 0.0;
                for open in crate::chain::iter(&plan.opens) {
                    let value = self.open_value_in(ctx, plan, *open, domains.as_deref());
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
