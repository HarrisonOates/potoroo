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

use crate::formula::Atom;
use crate::planning_graph::hv_min;
use crate::terms::{Object, Term};

use super::binds::{ClassId, Resolved};
use super::plan::{reusable, Ctx, Plan};
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
    /// ADD plus value-token deficits (the ground planner's `TADD`).
    Tadd,
}

/// Largest product of narrowed domains enumerated per condition.
const ENUMERATION_LIMIT: usize = 512;

impl Kind {
    pub fn parse(name: &str) -> Result<Kind, String> {
        match name.to_ascii_uppercase().as_str() {
            "OC" => Ok(Kind::Oc),
            "ADD" => Ok(Kind::Add),
            "PADD" => Ok(Kind::Padd),
            "ADDR" => Ok(Kind::Addr),
            "TADD" => Ok(Kind::Tadd),
            _ => Err(format!(
                "unknown lifted FDR heuristic `{name}` (OC, ADD, PADD, ADDR, TADD)"
            )),
        }
    }
}

pub struct Estimator {
    kind: Kind,
    /// Evaluate conditions over propagated binding domains (not for PADD).
    use_domains: bool,
    /// Patterns are passed to the graph with bound terms substituted, so its
    /// binding-aware matching needs no constraints.
    empty: Rc<crate::bindings::Bindings>,
    graph: Option<Rc<PlanningGraph>>,
    /// A reusable atom buffer for evaluating conditions.
    scratch: std::cell::Cell<Atom>,
    /// Token tables for `TADD`, built on first use.
    tokens: std::cell::OnceCell<super::token::Tokens>,
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
            use_domains: matches!(kind, Kind::Add | Kind::Addr | Kind::Tadd),
            empty: crate::bindings::Bindings::empty(),
            scratch: std::cell::Cell::new(Atom {
                predicate: crate::predicates::Predicate(0),
                terms: Vec::new(),
            }),
            tokens: std::cell::OnceCell::new(),
        }
    }

    /// The planning-graph value of one open condition (infinite when no graph
    /// is built).
    pub fn open_value(&self, ctx: &Ctx, plan: &Plan, open: super::plan::Open) -> HeuristicValue {
        self.open_value_in(ctx, plan, open, false)
    }

    /// The planning-graph value of one open condition: the cheapest ground
    /// atom it admits. Bound terms are substituted; terms of one class share
    /// a variable. With `use_domains`, classes whose maintained domain is
    /// narrower than their type range over those objects only, enumerated
    /// when the product is small; other variables keep the graph's pattern
    /// minimum over type-compatible objects.
    pub fn open_value_in(
        &self,
        ctx: &Ctx,
        plan: &Plan,
        open: super::plan::Open,
        use_domains: bool,
    ) -> HeuristicValue {
        let Some(graph) = self.graph.as_ref() else {
            return HeuristicValue::ZERO;
        };
        let fact = ctx.condition(plan, open.consumer(), open.cond);
        let negated = fact.value == LValue::None;
        // Reuse one atom buffer across evaluations.
        let mut atom = self.scratch.replace(Atom {
            predicate: crate::predicates::Predicate(0),
            terms: Vec::new(),
        });
        atom.predicate = ctx.task.atom_terms_into(fact, &mut atom.terms);
        let value = self.atom_value(ctx, plan, open, use_domains, graph, negated, &mut atom);
        self.scratch.set(atom);
        value
    }

    #[allow(clippy::too_many_arguments)]
    fn atom_value(
        &self,
        ctx: &Ctx,
        plan: &Plan,
        open: super::plan::Open,
        use_domains: bool,
        graph: &PlanningGraph,
        negated: bool,
        atom: &mut Atom,
    ) -> HeuristicValue {
        let b = &plan.bindings;
        // Positions per unbound class, and the class's representative term.
        let mut classes: Vec<(ClassId, Vec<usize>, Term)> = Vec::new();
        for (i, t) in atom.terms.iter_mut().enumerate() {
            match b.resolve(*t, open.consumer()) {
                Resolved::Object(o) => *t = Term::Object(o),
                Resolved::Class(k) => match classes.iter_mut().find(|(c, _, _)| *c == k) {
                    Some((_, positions, first)) => {
                        positions.push(i);
                        *t = *first;
                    }
                    None => classes.push((k, vec![i], *t)),
                },
            }
        }
        let empty = &self.empty;
        let value_of = |atom: &Atom| {
            if negated {
                graph.heuristic_value_negation(atom, open.consumer(), Some((&ctx.types, empty)))
            } else {
                graph.heuristic_value_atom(atom, open.consumer(), Some((&ctx.types, empty)))
            }
        };
        if !use_domains {
            return value_of(atom);
        }
        let narrowed: Vec<(Vec<usize>, Vec<Object>)> = classes
            .iter()
            .filter_map(|(k, positions, first)| {
                let Term::Variable(v) = first else {
                    return None;
                };
                let domain = b.domain(*k);
                (domain.len() < ctx.type_set(*v).len())
                    .then(|| (positions.clone(), domain.iter().collect()))
            })
            .collect();
        let product = narrowed
            .iter()
            .try_fold(1usize, |acc, (_, d)| acc.checked_mul(d.len()));
        if narrowed.is_empty() || product.is_none_or(|p| p > ENUMERATION_LIMIT) {
            return value_of(atom);
        }
        if product == Some(0) {
            return HeuristicValue::INFINITE;
        }
        let mut best = HeuristicValue::INFINITE;
        let mut index = vec![0usize; narrowed.len()];
        let mut probe = atom.clone();
        loop {
            for (k, (positions, objects)) in narrowed.iter().enumerate() {
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
                if k == narrowed.len() {
                    return best;
                }
                index[k] += 1;
                if index[k] < narrowed[k].1.len() {
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
            Kind::Add | Kind::Padd | Kind::Addr | Kind::Tadd => {
                let reuse = self.kind == Kind::Addr;
                let tokens = self.kind == Kind::Tadd;
                let mut charged: Vec<(usize, u16)> = Vec::new();
                let mut total = 0.0;
                for open in crate::chain::iter(&plan.opens) {
                    let value = self.open_value_in(ctx, plan, *open, self.use_domains);
                    let cost = value.add_cost();
                    if cost == 0.0 {
                        continue;
                    }
                    if tokens {
                        charged.push((open.consumer(), open.cond));
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
                if tokens {
                    total += self
                        .tokens
                        .get_or_init(|| super::token::Tokens::new(ctx.task))
                        .deficit(ctx, plan, &charged);
                }
                total
            }
        }
    }
}
