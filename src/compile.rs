//! Causal-link compilation of a partial POCL plan into a classical STRIPS task.
//!
//! Implements the encoding of Bercher, Geier & Biundo (2013), "Using State-Based
//! Planning Heuristics for Partial-Order Causal-Link Planning" (§3), extended
//! with the *polynomial* causal-link protection of the position paper's
//! Proposition 1 (the paper's own `count(v)` link compilation is exponential —
//! "horrible" — and their evaluation simply ignored link protection).
//!
//! ## Base encoding (Bercher et al. 2013)
//! For a partial plan `P = (PS, ≺, CL)` and problem `π = (V, A, s_init, g)`, the
//! encoding `enc(P,π) = (V', A', s'_init, g')` introduces, for each plan step
//! `l:a` (excluding the artificial init `l_0` and goal `l_∞`), two indicator
//! propositions `l₋` and `l₊`:
//!
//! - `enc(l:(pre,add,del)) = (pre ∪ {l₋} ∪ {l'₊ | l' ≺ l, l' ≠ l_0},
//!                            add ∪ {l₊}, del ∪ {l₋})`
//! - `s'_init = s_init ∪ {l₋}`  (every step "not yet executed")
//! - `g' = g ∪ {l₊}`           (every step must be executed)
//!
//! `l₋` (precondition + delete of `l`) makes the step fire at most once; `l₊`
//! (add of `l`, goal) forces it to fire; the `l'₊` preconditions enforce the
//! partial order `≺`. The original goal `g` is the artificial goal step's
//! precondition; open conditions are *not* goals — they are forced via the step
//! preconditions plus the `l₊` flags.
//!
//! ## Causal-link protection (position paper, Prop 1 — polynomial)
//! One guard proposition `g_cl` per causal link `(p, v, c)`:
//! - true in `s'_init` iff `p` is a real step (which will delete it); for an
//!   init-produced link it starts false so the protected interval already blocks
//!   deleters from the start;
//! - the producer deletes `g_cl`, the consumer adds it back; a goal-consumed link
//!   never re-adds it, so deleters stay blocked to the end;
//! - every action deleting the protected literal `v` gets `g_cl` as a
//!   precondition, so it cannot fire inside the protected interval.
//! Guards are never goal requirements. This is `O(|CL|·|A|)` (Prop 1).
//!
//! The result is a [`CompiledProblem`] IR rendered to PDDL by [`emit_pddl`]; the
//! IR is the shared root for the FD heuristic (Phase 1) and the LP heuristic
//! (Phase 4, via FD's translator). Lifted partial plans are handled by leaving
//! unbound step variables as action parameters (FD grounds them) — per §4
//! "Ground Planning", ignoring designation constraints is a sound relaxation.

use std::collections::{BTreeSet, HashMap};
use std::fmt::Write;
use std::rc::Rc;

use crate::bindings::StepVarTypes;
use crate::chain;
use crate::effect::Effect;
use crate::external::FdHeuristic;
use crate::formula::{Atom, Formula, Literal};
use crate::orderings::StepTime;
use crate::plan::{Link, Plan, GOAL_ID, INIT_ID};
use crate::sas::{GroundEffect, GroundOp, GroundTask};
use crate::search::SearchContext;
use crate::terms::{Object, Term, Variable};
use crate::types::{Type, OBJECT};

/// A resolved literal: predicate, polarity, and argument terms (objects where
/// bound, variables otherwise).
#[derive(Debug, Clone)]
struct RLit {
    negative: bool,
    predicate: crate::predicates::Predicate,
    args: Vec<Term>,
}

/// A committed plan step compiled to a classical action.
#[derive(Debug)]
struct CompiledStep {
    /// Step id (used to name its indicator props `exec-pos-N`/`exec-neg-N`).
    id: usize,
    /// Unique action name, e.g. `step-3-puton`.
    name: String,
    /// Leftover unbound variables (index, type) → action parameters.
    params: Vec<(u32, Type)>,
    /// Substitution of bound step variables to objects.
    subst: HashMap<Variable, Term>,
    /// The step's (schema) precondition, rendered with `subst`.
    precondition: Rc<Formula>,
    /// The step's (schema) effects, rendered with `subst`.
    effects: Vec<Effect>,
    /// Variable types in the step's scope (for forall/param types).
    var_types: Vec<Type>,
    /// Committed steps `l'` with `l' ≺ l` (their `l'₊` are preconditions).
    predecessors: Vec<usize>,
    /// Guards this step must have true to fire (it deletes a protected literal).
    precond_guards: Vec<usize>,
    /// Guards this step deletes (producer).
    del_guards: Vec<usize>,
    /// Guards this step adds (consumer).
    add_guards: Vec<usize>,
}

/// A conditional guard precondition for an *original* (insertable) schema: the
/// instance needs guard `guard_id` true whenever its deleting effect's args equal
/// the protected literal's ground args.
#[derive(Debug)]
struct OriginalGuard {
    schema_index: usize,
    guard_id: usize,
    effect_args: Vec<Term>,
    protected_args: Vec<Object>,
}

/// The classical STRIPS task compiled from a partial plan. The shared IR.
pub struct CompiledProblem {
    /// Number of causal-link guard propositions (`guard-0..`).
    num_guards: usize,
    /// Guard ids true in the initial state (real-step producers).
    init_guards: BTreeSet<usize>,
    /// Committed steps as classical actions (carry their indicator ids).
    steps: Vec<CompiledStep>,
    /// Conditional guard preconditions for original schemas.
    original_guards: Vec<OriginalGuard>,
    /// Residual goal literals: the original problem goal (resolved). The `l₊`
    /// indicator goals are added from `steps` at emit time.
    goal: Vec<RLit>,
}

impl CompiledProblem {
    /// Compiles a partial plan into the classical task with causal-link
    /// protection (Prop 1) enabled.
    pub fn compile(plan: &Plan, ctx: &SearchContext) -> CompiledProblem {
        Self::compile_opts(plan, ctx, true)
    }

    /// Compiles with `link_guards` controlling whether the polynomial causal-link
    /// protection (Prop 1) is emitted. `false` yields the Bercher et al. (2013)
    /// base encoding (link protection relaxed away).
    pub fn compile_opts(plan: &Plan, ctx: &SearchContext, link_guards: bool) -> CompiledProblem {
        let links: Vec<Link> = chain::iter(&plan.links).cloned().collect();
        let num_guards = if link_guards { links.len() } else { 0 };

        // A guard is true initially iff its producer is a real step.
        let mut init_guards = BTreeSet::new();
        if link_guards {
            for (gid, link) in links.iter().enumerate() {
                if link.from_id != INIT_ID {
                    init_guards.insert(gid);
                }
            }
        }

        // Resolve each protected literal to ground args where possible.
        let resolved_links: Vec<(usize, RLit)> = links
            .iter()
            .enumerate()
            .map(|(gid, l)| (gid, resolve_literal(&l.condition, l.to_id, plan)))
            .collect();

        // Committed (non-synthetic) step ids, for predecessor computation.
        let committed: Vec<usize> = chain::iter(&plan.steps)
            .filter(|s| !s.action.synthetic())
            .map(|s| s.id)
            .collect();

        let mut steps = Vec::new();
        let mut original_guards = Vec::new();
        for step in chain::iter(&plan.steps) {
            if step.action.synthetic() {
                continue;
            }
            let sid = step.id;
            let action = &step.action;
            let name = format!("step-{sid}-{}", sanitize(&action.name));

            // Substitution: bound step variables → objects; leftover are params.
            let mut subst: HashMap<Variable, Term> = HashMap::new();
            let mut params: Vec<(u32, Type)> = Vec::new();
            for &p in &action.parameters {
                let bound = plan.bindings.binding(Term::Variable(p), sid);
                match bound {
                    Term::Object(_) => {
                        subst.insert(p, bound);
                    }
                    Term::Variable(v) => {
                        // Canonical representative may differ from p; declare the
                        // representative as the parameter and map p → it.
                        if v != p {
                            subst.insert(p, Term::Variable(v));
                        }
                        let ty = ctx.var_type(v, sid);
                        if !params.iter().any(|(i, _)| *i == v.0) {
                            params.push((v.0, ty));
                        }
                    }
                }
            }
            params.sort_by_key(|(i, _)| *i);

            // Predecessors l' ≺ l among committed steps (excluding init/self).
            let predecessors: Vec<usize> = committed
                .iter()
                .copied()
                .filter(|&lp| lp != sid && necessarily_before(plan, lp, sid))
                .collect();

            // Guard wiring: producer/consumer of links; threats by this step.
            let mut del_guards = Vec::new();
            let mut add_guards = Vec::new();
            let mut precond_guards = Vec::new();
            if link_guards {
                for (gid, link) in links.iter().enumerate() {
                    if link.from_id == sid {
                        del_guards.push(gid);
                    }
                    if link.to_id == sid {
                        add_guards.push(gid);
                    }
                }
                // Ground exact-match threat detection (both args resolved).
                let (add, del) = resolved_effects(action, sid, plan);
                for (gid, v) in &resolved_links {
                    let threats = if v.negative { &add } else { &del };
                    if threats.iter().any(|e| same_ground_atom(e, v)) {
                        let link = &links[*gid];
                        if link.from_id != sid && link.to_id != sid {
                            precond_guards.push(*gid);
                        }
                    }
                }
            }

            steps.push(CompiledStep {
                id: sid,
                name,
                params,
                subst,
                precondition: action.precondition.clone(),
                effects: action.effects.clone(),
                var_types: action.var_types.clone(),
                predecessors,
                precond_guards,
                del_guards,
                add_guards,
            });
        }

        // Conditional guard preconditions for original (insertable) schemas.
        if link_guards {
            for (schema_index, schema) in ctx.domain.actions.iter().enumerate() {
                for (gid, v) in &resolved_links {
                    let Some(protected_args) = all_objects(&v.args) else {
                        continue;
                    };
                    for eff in &schema.effects {
                        let eff_neg = eff.literal.negative();
                        let threatens = if v.negative { !eff_neg } else { eff_neg };
                        if !threatens || eff.literal.atom().predicate != v.predicate {
                            continue;
                        }
                        if eff.literal.atom().terms.len() != protected_args.len() {
                            continue;
                        }
                        original_guards.push(OriginalGuard {
                            schema_index,
                            guard_id: *gid,
                            effect_args: eff.literal.atom().terms.clone(),
                            protected_args: protected_args.clone(),
                        });
                    }
                }
            }
        }

        // Residual goal = the original problem goal (the artificial goal step's
        // precondition). Indicator (`l₊`) goals are added at emit time.
        let goal = resolve_conjunction(&ctx.problem.goal, GOAL_ID, plan);

        CompiledProblem {
            num_guards,
            init_guards,
            steps,
            original_guards,
            goal,
        }
    }

    /// Renders to a `(domain_pddl, problem_pddl)` pair for Fast Downward.
    pub fn emit_pddl(&self, ctx: &SearchContext) -> (String, String) {
        (self.emit_domain(ctx), self.emit_problem(ctx))
    }

    fn emit_domain(&self, ctx: &SearchContext) -> String {
        let preds = &ctx.domain.predicates;
        let types = &ctx.domain.types;
        let typed = !simple_type_names(types).is_empty();

        let mut s = String::new();
        let _ = writeln!(s, "(define (domain pocl-compiled)");
        let mut reqs = String::from("  (:requirements :strips :equality");
        if typed {
            reqs.push_str(" :typing");
        }
        reqs.push_str(" :disjunctive-preconditions :negative-preconditions :conditional-effects)");
        let _ = writeln!(s, "{reqs}");
        if typed {
            let _ = writeln!(s, "  (:types {})", simple_type_names(types).join(" "));
        }

        // Predicates: originals + indicator props + guard props.
        let _ = writeln!(s, "  (:predicates");
        for p in all_predicates(preds) {
            let mut line = format!("    ({}", preds.name(p));
            for (i, &ty) in preds.parameters(p).iter().enumerate() {
                let _ = write!(line, " ?a{i}");
                if typed {
                    let _ = write!(line, " - {}", types.name(ty));
                }
            }
            line.push(')');
            let _ = writeln!(s, "{line}");
        }
        for st in &self.steps {
            let _ = writeln!(s, "    (exec-pos-{0}) (exec-neg-{0})", st.id);
        }
        for gid in 0..self.num_guards {
            let _ = writeln!(s, "    (guard-{gid})");
        }
        let _ = writeln!(s, "  )");

        // Committed step actions.
        for st in &self.steps {
            let _ = writeln!(s, "  (:action {}", st.name);
            let _ = write!(s, "   :parameters (");
            for (i, (vi, ty)) in st.params.iter().enumerate() {
                if i > 0 {
                    s.push(' ');
                }
                let _ = write!(s, "?v{vi}");
                if typed {
                    let _ = write!(s, " - {}", types.name(*ty));
                }
            }
            let _ = writeln!(s, ")");

            // Precondition: schema precondition (subst) + l₋ + predecessors' l'₊
            // + threat guards.
            let _ = write!(s, "   :precondition (and");
            render_formula_into(&mut s, &st.precondition, &st.subst, ctx);
            let _ = write!(s, " (exec-neg-{})", st.id);
            for lp in &st.predecessors {
                let _ = write!(s, " (exec-pos-{lp})");
            }
            for g in &st.precond_guards {
                let _ = write!(s, " (guard-{g})");
            }
            let _ = writeln!(s, ")");

            // Effect: schema effects (subst) + add l₊, del l₋ + guard maintenance.
            let _ = write!(s, "   :effect (and");
            render_effects_into(&mut s, &st.effects, &st.subst, &st.var_types, ctx, typed);
            let _ = write!(s, " (exec-pos-{0}) (not (exec-neg-{0}))", st.id);
            for g in &st.del_guards {
                let _ = write!(s, " (not (guard-{g}))");
            }
            for g in &st.add_guards {
                let _ = write!(s, " (guard-{g})");
            }
            let _ = writeln!(s, ")");
            let _ = writeln!(s, "  )");
        }

        // Original (insertable) actions, with conditional guard preconditions.
        let empty = HashMap::new();
        for (schema_index, schema) in ctx.domain.actions.iter().enumerate() {
            let _ = writeln!(s, "  (:action {}", sanitize(&schema.name));
            let _ = write!(s, "   :parameters (");
            for (i, &p) in schema.parameters.iter().enumerate() {
                if i > 0 {
                    s.push(' ');
                }
                let _ = write!(s, "?v{}", p.0);
                if typed {
                    let _ = write!(s, " - {}", types.name(schema.var_types[p.0 as usize]));
                }
            }
            let _ = writeln!(s, ")");
            let _ = write!(s, "   :precondition (and");
            render_formula_into(&mut s, &schema.precondition, &empty, ctx);
            for og in self
                .original_guards
                .iter()
                .filter(|g| g.schema_index == schema_index)
            {
                let _ = write!(s, " (or (guard-{}) (not (and", og.guard_id);
                for (ea, &pa) in og.effect_args.iter().zip(&og.protected_args) {
                    let _ = write!(s, " (= {} {})", render_term(*ea, &empty, ctx), object_name(pa, ctx));
                }
                let _ = write!(s, ")))");
            }
            let _ = writeln!(s, ")");
            let _ = write!(s, "   :effect (and");
            render_effects_into(&mut s, &schema.effects, &empty, &schema.var_types, ctx, typed);
            let _ = writeln!(s, ")");
            let _ = writeln!(s, "  )");
        }

        let _ = writeln!(s, ")");
        s
    }

    fn emit_problem(&self, ctx: &SearchContext) -> String {
        let types = &ctx.domain.types;
        let typed = !simple_type_names(types).is_empty();

        let mut s = String::new();
        let _ = writeln!(s, "(define (problem pocl-compiled-prob)");
        let _ = writeln!(s, "  (:domain pocl-compiled)");

        let objs = all_objects_with_types(ctx);
        if !objs.is_empty() {
            let _ = write!(s, "  (:objects");
            for (o, ty) in &objs {
                let _ = write!(s, " {}", object_name(*o, ctx));
                if typed {
                    let _ = write!(s, " - {}", types.name(*ty));
                }
            }
            let _ = writeln!(s, ")");
        }

        // Init: problem init + every step's l₋ + guards true initially.
        let _ = write!(s, "  (:init");
        for atom in &ctx.problem.init_order {
            let _ = write!(s, " {}", render_atom(atom, ctx));
        }
        for st in &self.steps {
            let _ = write!(s, " (exec-neg-{})", st.id);
        }
        for gid in &self.init_guards {
            let _ = write!(s, " (guard-{gid})");
        }
        let _ = writeln!(s, ")");

        // Goal: problem goal + every step's l₊ (forces all steps to execute).
        let empty = HashMap::new();
        let _ = write!(s, "  (:goal (and");
        for l in &self.goal {
            let _ = write!(s, " {}", render_rlit(l, &empty, ctx));
        }
        for st in &self.steps {
            let _ = write!(s, " (exec-pos-{})", st.id);
        }
        let _ = writeln!(s, "))");
        let _ = writeln!(s, ")");
        s
    }
}

/// Parses a `COMPILE[_FF|_LMCUT|_HMAX|_HADD|_BLIND]` heuristic name into the FD
/// backend, or `None` if not a compile heuristic.
pub fn parse_backend(name: &str) -> Option<FdHeuristic> {
    match name.to_ascii_uppercase().as_str() {
        "COMPILE" | "COMPILE_FF" => Some(FdHeuristic::Ff),
        "COMPILE_LMCUT" => Some(FdHeuristic::LmCut),
        "COMPILE_HMAX" => Some(FdHeuristic::HMax),
        "COMPILE_HADD" => Some(FdHeuristic::HAdd),
        "COMPILE_BLIND" => Some(FdHeuristic::Blind),
        _ => None,
    }
}

// ==========================================================================
// Direct SAS⁺ grounding (Phase 1-opt fast path, ground search only).
//
// Grounds the same Bercher-2013 + Prop-1 encoding into an all-binary FDR task
// (`crate::sas::GroundTask`), so the heuristic is evaluated by the `downward`
// C++ binary directly — skipping Fast Downward's Python translator (~95% of the
// per-node cost). Restricted to ground search: committed steps and original
// actions are already ground, so there is no lifted-variable expansion. The
// polynomial causal-link guards collapse to plain ground preconditions here
// (the disjunctive `(or guard (not (= …)))` is decided once arguments are
// ground), which is the faithful Prop-1 encoding at the ground level.
// ==========================================================================

/// Interns ground facts (by canonical name) into a [`GroundTask`].
struct Interner<'a> {
    task: GroundTask,
    map: HashMap<String, usize>,
    ctx: &'a SearchContext<'a>,
}

impl<'a> Interner<'a> {
    fn new(ctx: &'a SearchContext<'a>) -> Self {
        Interner {
            task: GroundTask::new(),
            map: HashMap::new(),
            ctx,
        }
    }

    /// Interns a ground atom fact (initial truth = membership in the init state).
    fn atom_fact(&mut self, predicate: crate::predicates::Predicate, args: &[Object]) -> usize {
        let mut name = self.ctx.domain.predicates.name(predicate).to_string();
        name.push('(');
        for (i, &o) in args.iter().enumerate() {
            if i > 0 {
                name.push(',');
            }
            name.push_str(&object_name(o, self.ctx));
        }
        name.push(')');
        if let Some(&id) = self.map.get(&name) {
            return id;
        }
        let atom = Atom {
            predicate,
            terms: args.iter().map(|&o| Term::Object(o)).collect(),
        };
        let init = self.ctx.problem.init_atoms.contains(&atom);
        let id = self.task.add_fact(name.clone(), init);
        self.map.insert(name, id);
        id
    }

    /// Interns a named propositional fact (indicator / guard) with explicit init.
    fn named_fact(&mut self, name: String, init: bool) -> usize {
        if let Some(&id) = self.map.get(&name) {
            return id;
        }
        let id = self.task.add_fact(name.clone(), init);
        self.map.insert(name, id);
        id
    }
}

fn term_obj(t: Term) -> Option<Object> {
    match t {
        Term::Object(o) => Some(o),
        Term::Variable(_) => None,
    }
}

/// Flattens a ground precondition/condition formula into `(fact, truth)` pairs,
/// or `None` if it is statically false. Ground (in)equalities are evaluated.
fn flatten_pre(int: &mut Interner, f: &Rc<Formula>) -> Option<Vec<(usize, bool)>> {
    fn go(int: &mut Interner, f: &Rc<Formula>, out: &mut Vec<(usize, bool)>) -> bool {
        match f.as_ref() {
            Formula::True => true,
            Formula::False => false,
            Formula::Atom(a) => match all_objects(&a.terms) {
                Some(objs) => {
                    let id = int.atom_fact(a.predicate, &objs);
                    out.push((id, true));
                    true
                }
                None => true, // non-ground literal: ignore (relaxation)
            },
            Formula::Negation(a) => match all_objects(&a.terms) {
                Some(objs) => {
                    let id = int.atom_fact(a.predicate, &objs);
                    out.push((id, false));
                    true
                }
                None => true,
            },
            Formula::Equality { left, right, .. } => match (term_obj(*left), term_obj(*right)) {
                (Some(a), Some(b)) => a == b, // statically decided
                _ => true,                    // open: ignore
            },
            Formula::Inequality { left, right, .. } => match (term_obj(*left), term_obj(*right)) {
                (Some(a), Some(b)) => a != b,
                _ => true,
            },
            Formula::Conjunction(cs) => cs.iter().all(|c| go(int, c, out)),
            // Disjunctions / quantifiers do not occur in the ground benchmark
            // preconditions we target; treat as no constraint (a relaxation).
            _ => true,
        }
    }
    let mut out = Vec::new();
    if go(int, f, &mut out) {
        Some(out)
    } else {
        None
    }
}

/// Flattens ground effects into [`GroundEffect`]s (conditional `when` kept as
/// effect conditions; statically-false conditions drop the effect). Forall
/// effects are not expected in ground search and are skipped if present.
fn flatten_effects(int: &mut Interner, effects: &[Effect]) -> Vec<GroundEffect> {
    let mut out = Vec::new();
    for e in effects {
        if e.condition.contradiction() || !e.parameters.is_empty() {
            continue;
        }
        let Some(cond) = flatten_pre(int, &e.condition) else {
            continue; // condition statically false
        };
        let a = e.literal.atom();
        let Some(objs) = all_objects(&a.terms) else {
            continue;
        };
        let fact = int.atom_fact(a.predicate, &objs);
        out.push(GroundEffect {
            cond,
            fact,
            value: !e.literal.negative(),
        });
    }
    out
}

/// The constant base of the SAS⁺ compilation: the ground original (insertable)
/// actions and their facts, independent of any partial plan. Built once per
/// problem and reused across all search nodes (`SearchContext::compile_base`),
/// so each node only grounds its small delta (committed steps + indicators +
/// per-link guards). Carries the fact interner state so per-node facts share
/// ids with the base.
pub struct BaseGroundTask {
    task: GroundTask,
    map: HashMap<String, usize>,
    /// Number of operators that are original (insertable) actions; per-node guard
    /// folding scans exactly these.
    num_original_ops: usize,
}

/// Builds the constant base (ground original actions, no guards/indicators yet).
/// Originals are grounded by Fast Downward's translator (reachable set only),
/// keeping the SAS⁺ compact — which is what the per-node `downward` cost scales
/// with.
pub fn build_base(ctx: &SearchContext) -> BaseGroundTask {
    let mut int = Interner::new(ctx);
    for ga in ctx.fd_reachable_ground_actions() {
        let Some(pre) = flatten_pre(&mut int, &ga.precondition) else {
            continue; // statically inconsistent instance
        };
        let effects = flatten_effects(&mut int, &ga.effects);
        let name = ground_action_name(&ga, ctx);
        int.task.add_op(GroundOp { name, pre, effects });
    }
    let num_original_ops = int.task.num_ops();
    BaseGroundTask {
        task: int.task,
        map: int.map,
        num_original_ops,
    }
}

/// Grounds the causal-link compilation of `plan` into an all-binary FDR task,
/// reusing the cached constant base (ground originals). Requires ground search
/// (committed steps and original actions already ground).
pub fn ground_task(plan: &Plan, ctx: &SearchContext) -> GroundTask {
    let base = ctx.compile_base();
    let links: Vec<Link> = chain::iter(&plan.links).cloned().collect();
    let num_guards = links.len();
    let init_guards: BTreeSet<usize> = links
        .iter()
        .enumerate()
        .filter(|(_, l)| l.from_id != INIT_ID)
        .map(|(g, _)| g)
        .collect();
    let resolved_links: Vec<(usize, RLit)> = links
        .iter()
        .enumerate()
        .map(|(g, l)| (g, resolve_literal(&l.condition, l.to_id, plan)))
        .collect();

    let committed: Vec<usize> = chain::iter(&plan.steps)
        .filter(|s| !s.action.synthetic())
        .map(|s| s.id)
        .collect();

    // Start from a clone of the cached base (facts + original ops).
    let mut int = Interner {
        task: base.task.clone(),
        map: base.map.clone(),
        ctx,
    };

    // Pre-intern indicator and guard facts with their initial truth, so later
    // references (as preconditions) see the correct init value.
    for &sid in &committed {
        int.named_fact(format!("exec-neg-{sid}"), true);
        int.named_fact(format!("exec-pos-{sid}"), false);
    }
    for g in 0..num_guards {
        int.named_fact(format!("guard-{g}"), init_guards.contains(&g));
    }

    // Fold per-node causal-link guards into the cached original operators: a
    // fresh insertable action threatens link `g` if one of its effects sets the
    // protected literal's fact to its clobbering value; require `guard-g`.
    for (g, v) in &resolved_links {
        let Some(objs) = all_objects(&v.args) else { continue };
        let pf = int.atom_fact(v.predicate, &objs);
        let clobber_value = v.negative; // positive link clobbered by del (value=false)
        let guard = int.named_fact(format!("guard-{g}"), init_guards.contains(g));
        for op in int.task.ops_mut()[..base.num_original_ops].iter_mut() {
            if op
                .effects
                .iter()
                .any(|e| e.fact == pf && e.value == clobber_value)
            {
                op.pre.push((guard, true));
            }
        }
    }

    // Committed steps (already ground in ground search).
    for step in chain::iter(&plan.steps) {
        if step.action.synthetic() {
            continue;
        }
        let sid = step.id;
        let mut pre = match flatten_pre(&mut int, &step.action.precondition) {
            Some(p) => p,
            None => continue,
        };
        let mut effects = flatten_effects(&mut int, &step.action.effects);

        // Indicators: precondition exec-neg-l; add exec-pos-l, delete exec-neg-l.
        let neg = int.named_fact(format!("exec-neg-{sid}"), true);
        let pos = int.named_fact(format!("exec-pos-{sid}"), false);
        pre.push((neg, true));
        effects.push(GroundEffect { cond: vec![], fact: pos, value: true });
        effects.push(GroundEffect { cond: vec![], fact: neg, value: false });

        // Partial order: predecessors' exec-pos must hold.
        for &lp in &committed {
            if lp != sid && necessarily_before(plan, lp, sid) {
                let id = int.named_fact(format!("exec-pos-{lp}"), false);
                pre.push((id, true));
            }
        }

        // Causal-link guards: producer deletes, consumer adds; threats need it.
        let (sadd, sdel) = resolved_effects(&step.action, sid, plan);
        for (g, link) in links.iter().enumerate() {
            if link.from_id == sid {
                let id = int.named_fact(format!("guard-{g}"), init_guards.contains(&g));
                effects.push(GroundEffect { cond: vec![], fact: id, value: false });
            }
            if link.to_id == sid {
                let id = int.named_fact(format!("guard-{g}"), init_guards.contains(&g));
                effects.push(GroundEffect { cond: vec![], fact: id, value: true });
            }
        }
        for (g, v) in &resolved_links {
            let threats = if v.negative { &sadd } else { &sdel };
            let link = &links[*g];
            if link.from_id != sid
                && link.to_id != sid
                && threats.iter().any(|e| same_ground_atom(e, v))
            {
                let id = int.named_fact(format!("guard-{g}"), init_guards.contains(g));
                pre.push((id, true));
            }
        }

        int.task.add_op(GroundOp {
            name: format!("step-{sid}"),
            pre,
            effects,
        });
    }

    // Goal: problem goal (ground) + every step's exec-pos.
    if let Some(goal_lits) = flatten_pre(&mut int, &ctx.problem.goal) {
        for (f, t) in goal_lits {
            int.task.add_goal(f, t);
        }
    }
    for &sid in &committed {
        let id = int.named_fact(format!("exec-pos-{sid}"), false);
        int.task.add_goal(id, true);
    }

    int.task
}

fn ground_action_name(ga: &crate::plan::StepAction, ctx: &SearchContext) -> String {
    let mut name = sanitize(&ga.name);
    for &o in &ga.arguments {
        name.push('-');
        name.push_str(&object_name(o, ctx));
    }
    name
}

// ---- ordering / resolution helpers ---------------------------------------

/// Whether `lp` necessarily precedes `l` under the plan's orderings (`lp ≺ l`).
fn necessarily_before(plan: &Plan, lp: usize, l: usize) -> bool {
    // `lp` cannot be ordered at/after `l` ⇒ it is strictly before in every
    // linearization. Times collapse in the classical subset.
    !plan
        .orderings
        .possibly_after(lp, StepTime::AtEnd, l, StepTime::AtEnd)
}

fn resolve_literal(lit: &Literal, step_id: usize, plan: &Plan) -> RLit {
    let atom = lit.atom();
    RLit {
        negative: lit.negative(),
        predicate: atom.predicate,
        args: atom
            .terms
            .iter()
            .map(|&t| plan.bindings.binding(t, step_id))
            .collect(),
    }
}

fn resolve_conjunction(f: &Rc<Formula>, step_id: usize, plan: &Plan) -> Vec<RLit> {
    let mut out = Vec::new();
    collect_literals(f, step_id, plan, &mut out);
    out
}

fn collect_literals(f: &Rc<Formula>, step_id: usize, plan: &Plan, out: &mut Vec<RLit>) {
    match f.as_ref() {
        Formula::Atom(a) => out.push(resolve_literal(&Literal::Atom(a.clone()), step_id, plan)),
        Formula::Negation(a) => {
            out.push(resolve_literal(&Literal::Negation(a.clone()), step_id, plan))
        }
        Formula::Conjunction(cs) => {
            for c in cs {
                collect_literals(c, step_id, plan, out);
            }
        }
        _ => {}
    }
}

/// Resolved (add, del) literal lists for ground threat detection.
fn resolved_effects(
    action: &crate::plan::StepAction,
    step_id: usize,
    plan: &Plan,
) -> (Vec<RLit>, Vec<RLit>) {
    let mut add = Vec::new();
    let mut del = Vec::new();
    for e in &action.effects {
        let r = resolve_literal(&e.literal, step_id, plan);
        if e.literal.negative() {
            del.push(r);
        } else {
            add.push(r);
        }
    }
    (add, del)
}

fn all_objects(args: &[Term]) -> Option<Vec<Object>> {
    args.iter()
        .map(|t| match t {
            Term::Object(o) => Some(*o),
            Term::Variable(_) => None,
        })
        .collect()
}

fn same_ground_atom(a: &RLit, b: &RLit) -> bool {
    a.predicate == b.predicate
        && a.args.len() == b.args.len()
        && a.args.iter().zip(&b.args).all(|(x, y)| x == y)
}

// ---- rendering helpers (subst-aware) -------------------------------------

type Subst = HashMap<Variable, Term>;

fn render_term(t: Term, subst: &Subst, ctx: &SearchContext) -> String {
    let t = match t {
        Term::Variable(v) => subst.get(&v).copied().unwrap_or(t),
        Term::Object(_) => t,
    };
    match t {
        Term::Object(o) => object_name(o, ctx),
        Term::Variable(v) => format!("?v{}", v.0),
    }
}

fn render_rlit(l: &RLit, subst: &Subst, ctx: &SearchContext) -> String {
    let name = ctx.domain.predicates.name(l.predicate);
    let mut inner = format!("({name}");
    for &t in &l.args {
        let _ = write!(inner, " {}", render_term(t, subst, ctx));
    }
    inner.push(')');
    if l.negative {
        format!("(not {inner})")
    } else {
        inner
    }
}

fn render_atom(a: &Atom, ctx: &SearchContext) -> String {
    let empty = HashMap::new();
    let name = ctx.domain.predicates.name(a.predicate);
    let mut s = format!("({name}");
    for &t in &a.terms {
        let _ = write!(s, " {}", render_term(t, &empty, ctx));
    }
    s.push(')');
    s
}

fn render_atom_subst(a: &Atom, subst: &Subst, ctx: &SearchContext) -> String {
    let name = ctx.domain.predicates.name(a.predicate);
    let mut s = format!("({name}");
    for &t in &a.terms {
        let _ = write!(s, " {}", render_term(t, subst, ctx));
    }
    s.push(')');
    s
}

fn object_name(o: Object, ctx: &SearchContext) -> String {
    ctx.problem
        .objects
        .object_name(Some(&ctx.domain.constants), o)
        .to_string()
}

/// Appends a precondition/goal formula (space-prefixed sub-expressions) into the
/// surrounding `(and ...)`. Quantifiers are treated as no constraint.
fn render_formula_into(s: &mut String, f: &Rc<Formula>, subst: &Subst, ctx: &SearchContext) {
    match f.as_ref() {
        Formula::True => {}
        Formula::False => {
            let _ = write!(s, " (or)");
        }
        Formula::Atom(a) => {
            let _ = write!(s, " {}", render_atom_subst(a, subst, ctx));
        }
        Formula::Negation(a) => {
            let _ = write!(s, " (not {})", render_atom_subst(a, subst, ctx));
        }
        Formula::Equality { left, right, .. } => {
            let _ = write!(s, " (= {} {})", render_term(*left, subst, ctx), render_term(*right, subst, ctx));
        }
        Formula::Inequality { left, right, .. } => {
            let _ = write!(s, " (not (= {} {}))", render_term(*left, subst, ctx), render_term(*right, subst, ctx));
        }
        Formula::Conjunction(cs) => {
            for c in cs {
                render_formula_into(s, c, subst, ctx);
            }
        }
        Formula::Disjunction(ds) => {
            let _ = write!(s, " (or");
            for d in ds {
                render_formula_into(s, d, subst, ctx);
            }
            let _ = write!(s, ")");
        }
        Formula::Exists { .. } | Formula::Forall { .. } => {}
    }
}

/// A formula as a single well-formed expression (for `when`-conditions).
fn render_formula_expr(f: &Rc<Formula>, subst: &Subst, ctx: &SearchContext) -> String {
    match f.as_ref() {
        Formula::True => "(and)".to_string(),
        Formula::False => "(or)".to_string(),
        Formula::Atom(a) => render_atom_subst(a, subst, ctx),
        Formula::Negation(a) => format!("(not {})", render_atom_subst(a, subst, ctx)),
        Formula::Equality { left, right, .. } => {
            format!("(= {} {})", render_term(*left, subst, ctx), render_term(*right, subst, ctx))
        }
        Formula::Inequality { left, right, .. } => {
            format!("(not (= {} {}))", render_term(*left, subst, ctx), render_term(*right, subst, ctx))
        }
        Formula::Conjunction(cs) => {
            let mut s = String::from("(and");
            for c in cs {
                let _ = write!(s, " {}", render_formula_expr(c, subst, ctx));
            }
            s.push(')');
            s
        }
        Formula::Disjunction(ds) => {
            let mut s = String::from("(or");
            for d in ds {
                let _ = write!(s, " {}", render_formula_expr(d, subst, ctx));
            }
            s.push(')');
            s
        }
        Formula::Exists { .. } | Formula::Forall { .. } => "(and)".to_string(),
    }
}

/// Renders effects (conditional `when` and quantified `forall` faithfully) into
/// the surrounding `(and ...)`, applying `subst` to bound terms.
fn render_effects_into(
    s: &mut String,
    effects: &[Effect],
    subst: &Subst,
    var_types: &[Type],
    ctx: &SearchContext,
    typed: bool,
) {
    for e in effects {
        if e.condition.contradiction() {
            continue;
        }
        let a = e.literal.atom();
        let lit = if e.literal.negative() {
            format!("(not {})", render_atom_subst(a, subst, ctx))
        } else {
            render_atom_subst(a, subst, ctx)
        };
        let mut inner = if e.condition.tautology() {
            lit
        } else {
            format!("(when {} {})", render_formula_expr(&e.condition, subst, ctx), lit)
        };
        if !e.parameters.is_empty() {
            let mut params = String::new();
            for (i, &p) in e.parameters.iter().enumerate() {
                if i > 0 {
                    params.push(' ');
                }
                let _ = write!(params, "?v{}", p.0);
                if typed {
                    let ty = var_types.get(p.0 as usize).copied().unwrap_or(OBJECT);
                    let _ = write!(params, " - {}", ctx.domain.types.name(ty));
                }
            }
            inner = format!("(forall ({params}) {inner})");
        }
        let _ = write!(s, " {inner}");
    }
}

// ---- table helpers -------------------------------------------------------

fn all_predicates(preds: &crate::predicates::PredicateTable) -> Vec<crate::predicates::Predicate> {
    (0..preds.len() as u32)
        .map(crate::predicates::Predicate)
        .collect()
}

fn simple_type_names(types: &crate::types::Types) -> Vec<String> {
    let mut out = Vec::new();
    let mut i = 1i32; // skip object == 0
    while let Some(name) = types.name_opt(Type(i)) {
        out.push(name.to_string());
        i += 1;
    }
    out
}

fn all_objects_with_types(ctx: &SearchContext) -> Vec<(Object, Type)> {
    let mut out: Vec<(Object, Type)> = Vec::new();
    for (o, ty) in ctx.domain.constants.owned_objects() {
        out.push((o, ty));
    }
    for (o, ty) in ctx.problem.objects.owned_objects() {
        out.push((o, ty));
    }
    out
}

fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_alphanumeric() || c == '-' { c } else { '-' })
        .collect()
}
