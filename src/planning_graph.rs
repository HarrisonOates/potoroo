//! The relaxed planning graph and additive cost/work heuristic values.
//!
//! The graph is built once from the problem's init atoms (cost 0) and the
//! domain's instantiated action schemas, iterating to a fixpoint over the
//! additive cost/work values of every reachable ground literal.

use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

use crate::bindings::{Bindings, TypeContext};
use crate::chain;
use crate::effect::Effect;
use crate::formula::{Atom, Formula, Literal};
use crate::plan::{Plan, StepAction, INIT_ID};
use crate::predicates::{Predicate, PredicateTable};

pub const THRESHOLD: f32 = 0.01;

fn sum(n: i32, m: i32) -> i32 {
    if i32::MAX - n > m {
        n + m
    } else {
        i32::MAX
    }
}

/* ====================================================================== */
/* HeuristicValue */

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct HeuristicValue {
    add_cost: f32,
    add_work: i32,
    makespan: f32,
}

impl HeuristicValue {
    pub const ZERO: HeuristicValue = HeuristicValue {
        add_cost: 0.0,
        add_work: 0,
        makespan: THRESHOLD,
    };

    pub const ZERO_COST_UNIT_WORK: HeuristicValue = HeuristicValue {
        add_cost: 0.0,
        add_work: 1,
        makespan: THRESHOLD,
    };

    pub const INFINITE: HeuristicValue = HeuristicValue {
        add_cost: f32::INFINITY,
        add_work: i32::MAX,
        makespan: f32::INFINITY,
    };

    pub fn new(add_cost: f32, add_work: i32, makespan: f32) -> Self {
        HeuristicValue {
            add_cost,
            add_work,
            makespan,
        }
    }

    pub fn add_cost(&self) -> f32 {
        self.add_cost
    }

    pub fn add_work(&self) -> i32 {
        self.add_work
    }

    pub fn makespan(&self) -> f32 {
        self.makespan
    }

    pub fn zero(&self) -> bool {
        self.add_cost == 0.0
    }

    pub fn infinite(&self) -> bool {
        self.makespan == f32::INFINITY
    }

    pub fn add_assign(&mut self, v: &HeuristicValue) {
        self.add_cost += v.add_cost;
        self.add_work = sum(self.add_work, v.add_work);
        if self.makespan < v.makespan {
            self.makespan = v.makespan;
        }
    }

    pub fn increase_cost(&mut self, x: f32) {
        self.add_cost += x;
    }

    pub fn increment_work(&mut self) {
        self.add_work = sum(self.add_work, 1);
    }

    pub fn increase_makespan(&mut self, x: f32) {
        self.makespan += x;
    }
}

/// Componentwise minimum heuristic value.
pub fn hv_min(v1: HeuristicValue, v2: HeuristicValue) -> HeuristicValue {
    let (add_cost, add_work) = if v1.add_cost == v2.add_cost {
        (v1.add_cost, v1.add_work.min(v2.add_work))
    } else if v1.add_cost < v2.add_cost {
        (v1.add_cost, v1.add_work)
    } else {
        (v2.add_cost, v2.add_work)
    };
    HeuristicValue::new(add_cost, add_work, v1.makespan.min(v2.makespan))
}

/* ====================================================================== */
/* PlanningGraph */

pub struct PlanningGraph {
    atom_values: HashMap<Atom, HeuristicValue>,
    negation_values: HashMap<Atom, HeuristicValue>,
    predicate_atoms: HashMap<Predicate, Vec<Atom>>,
    predicate_negations: HashMap<Predicate, Vec<Atom>>,
    /// The ground actions the graph was built from (for relaxed-plan extraction
    /// by the Relax heuristic; unused by the additive heuristics).
    actions: Vec<Rc<StepAction>>,
    /// Predicate -> `(action index, effect index)` of every positive add effect,
    /// for finding achievers of a goal atom during relaxed-plan extraction.
    pos_achievers: HashMap<Predicate, Vec<(usize, usize)>>,
}

impl PlanningGraph {
    /// Builds the relaxed planning graph from `init_action` (which carries the
    /// init atoms as positive effects) and the ground action instantiations.
    pub fn build(
        predicates: &PredicateTable,
        init_action: &Rc<StepAction>,
        actions: &[Rc<StepAction>],
    ) -> PlanningGraph {
        let mut pg = PlanningGraph {
            atom_values: HashMap::new(),
            negation_values: HashMap::new(),
            predicate_atoms: HashMap::new(),
            predicate_negations: HashMap::new(),
            actions: Vec::new(),
            pos_achievers: HashMap::new(),
        };

        // Add initial conditions at level 0 (heuristics.cc:471-485).
        for effect in init_action.effects.iter() {
            let atom = effect.literal.atom().clone();
            if predicates.is_static(atom.predicate) {
                pg.atom_values
                    .entry(atom)
                    .or_insert(HeuristicValue::ZERO);
            } else {
                pg.atom_values
                    .entry(atom)
                    .or_insert(HeuristicValue::ZERO_COST_UNIT_WORK);
            }
        }

        // Generate the rest of the levels until no change occurs
        // (heuristics.cc:517-700).
        loop {
            let mut changed = false;
            let mut new_atom_values: HashMap<Atom, HeuristicValue> = HashMap::new();
            let mut new_negation_values: HashMap<Atom, HeuristicValue> = HashMap::new();

            for action in actions {
                // Precondition value at this level (bindings = NULL: ground).
                let (pre_value, _start_value) =
                    pg.ground_formula_value(predicates, &action.precondition);
                // start_value.infinite() == pre_value.infinite() in the
                // classical (instantaneous) case, so guard on pre_value.
                if pre_value.infinite() {
                    continue;
                }
                for effect in action.effects.iter() {
                    let (mut cond_value, _cvs) =
                        pg.ground_formula_value(predicates, &effect.condition);
                    if cond_value.infinite() {
                        continue;
                    }
                    // Effect condition achievable: add the precondition value.
                    cond_value.add_assign(&pre_value);
                    // makespan: threshold + min_duration (0 for classical) plus
                    // unit cost.
                    cond_value.increase_makespan(THRESHOLD);
                    cond_value.increase_cost(1.0); // UNIT_COST: d = 1.

                    let literal = &effect.literal;
                    match literal {
                        Literal::Atom(atom) => {
                            let existing = new_atom_values
                                .get(atom)
                                .or_else(|| pg.atom_values.get(atom))
                                .copied();
                            match existing {
                                None => {
                                    let mut new_value = cond_value;
                                    new_value.increment_work();
                                    new_atom_values.insert(atom.clone(), new_value);
                                    changed = true;
                                }
                                Some(old_value) => {
                                    let mut new_value = cond_value;
                                    new_value.increment_work();
                                    new_value = hv_min(new_value, old_value);
                                    if new_value != old_value {
                                        new_atom_values.insert(atom.clone(), new_value);
                                        changed = true;
                                    }
                                }
                            }
                        }
                        Literal::Negation(atom) => {
                            let existing = new_negation_values
                                .get(atom)
                                .or_else(|| pg.negation_values.get(atom))
                                .copied();
                            match existing {
                                None => {
                                    // Closed world: only achieve the negation if
                                    // the atom is not (yet) certainly present.
                                    if pg.heuristic_value_atom(atom, 0, None).zero() {
                                        let mut new_value = cond_value;
                                        new_value.increment_work();
                                        new_negation_values.insert(atom.clone(), new_value);
                                        changed = true;
                                    }
                                }
                                Some(old_value) => {
                                    let mut new_value = cond_value;
                                    new_value.increment_work();
                                    new_value = hv_min(new_value, old_value);
                                    if new_value != old_value {
                                        new_negation_values.insert(atom.clone(), new_value);
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            for (atom, value) in new_atom_values {
                pg.atom_values.insert(atom, value);
            }
            for (atom, value) in new_negation_values {
                pg.negation_values.insert(atom, value);
            }

            if !changed {
                break;
            }
        }

        // Map predicates to achievable ground atoms (heuristics.cc:702-718).
        for atom in pg.atom_values.keys() {
            pg.predicate_atoms
                .entry(atom.predicate)
                .or_default()
                .push(atom.clone());
        }
        for atom in pg.negation_values.keys() {
            pg.predicate_negations
                .entry(atom.predicate)
                .or_default()
                .push(atom.clone());
        }

        // Index positive add effects by predicate for relaxed-plan extraction.
        pg.actions = actions.to_vec();
        for (ai, action) in pg.actions.iter().enumerate() {
            for (ei, effect) in action.effects.iter().enumerate() {
                if let Literal::Atom(a) = &effect.literal {
                    pg.pos_achievers
                        .entry(a.predicate)
                        .or_default()
                        .push((ai, ei));
                }
            }
        }

        pg
    }

    pub fn heuristic_value_atom(
        &self,
        atom: &Atom,
        step_id: usize,
        bindings: Option<(&TypeContext, &Bindings)>,
    ) -> HeuristicValue {
        match bindings {
            None => self
                .atom_values
                .get(atom)
                .copied()
                .unwrap_or(HeuristicValue::INFINITE),
            Some((ctx, b)) => {
                // Take minimum value over ground atoms that unify.
                let mut value = HeuristicValue::INFINITE;
                if let Some(ground_atoms) = self.predicate_atoms.get(&atom.predicate) {
                    let lifted = Literal::Atom(atom.clone());
                    for a in ground_atoms {
                        if b.unify(ctx, &lifted, step_id, &Literal::Atom(a.clone()), 0) {
                            let v = self.heuristic_value_atom(a, 0, None);
                            value = hv_min(value, v);
                            if value.zero() {
                                return value;
                            }
                        }
                    }
                }
                value
            }
        }
    }

    pub fn heuristic_value_negation(
        &self,
        atom: &Atom,
        step_id: usize,
        bindings: Option<(&TypeContext, &Bindings)>,
    ) -> HeuristicValue {
        match bindings {
            None => {
                if let Some(v) = self.negation_values.get(atom) {
                    *v
                } else {
                    match self.atom_values.get(atom) {
                        None => HeuristicValue::ZERO_COST_UNIT_WORK,
                        Some(v) if !v.zero() => HeuristicValue::ZERO_COST_UNIT_WORK,
                        Some(_) => HeuristicValue::INFINITE,
                    }
                }
            }
            Some((ctx, b)) => {
                if !self.heuristic_value_atom(atom, step_id, bindings).zero() {
                    return HeuristicValue::ZERO;
                }
                let mut value = HeuristicValue::INFINITE;
                if let Some(ground_atoms) = self.predicate_negations.get(&atom.predicate) {
                    let lifted = Literal::Atom(atom.clone());
                    for a in ground_atoms {
                        if b.unify(ctx, &lifted, step_id, &Literal::Atom(a.clone()), 0) {
                            let v = self.heuristic_value_atom(a, 0, None);
                            value = hv_min(value, v);
                            if value.zero() {
                                return value;
                            }
                        }
                    }
                }
                value
            }
        }
    }

    /// Heuristic value of a ground formula (bindings = NULL), used during graph
    /// construction. Returns `(h, hs)`.
    fn ground_formula_value(
        &self,
        predicates: &PredicateTable,
        formula: &Formula,
    ) -> (HeuristicValue, HeuristicValue) {
        formula_heuristic_value(self, predicates, formula, 0, None)
    }
}

/* ====================================================================== */
/* Per-formula heuristic value. */

/// Computes `(h, hs)` for a formula, resolving atoms through `bindings` when
/// present. `hs` (the makespan companion) is computed identically in the
/// classical subset.
#[allow(clippy::only_used_in_recursion)]
pub fn formula_heuristic_value(
    pg: &PlanningGraph,
    predicates: &PredicateTable,
    formula: &Formula,
    step_id: usize,
    bindings: Option<(&TypeContext, &Bindings)>,
) -> (HeuristicValue, HeuristicValue) {
    match formula {
        // Constant::heuristic_value.
        Formula::True | Formula::False => (HeuristicValue::ZERO, HeuristicValue::ZERO),
        // Atom::heuristic_value.
        Formula::Atom(atom) => {
            let v = pg.heuristic_value_atom(atom, step_id, bindings);
            (v, v)
        }
        // Negation::heuristic_value.
        Formula::Negation(atom) => {
            let v = pg.heuristic_value_negation(atom, step_id, bindings);
            (v, v)
        }
        // Equality::heuristic_value / Inequality::heuristic_value.
        Formula::Equality { .. } | Formula::Inequality { .. } => {
            let consistent = match bindings {
                None => true,
                Some((ctx, b)) => binding_consistent(ctx, b, formula, step_id),
            };
            if consistent {
                (HeuristicValue::ZERO, HeuristicValue::ZERO)
            } else {
                (HeuristicValue::INFINITE, HeuristicValue::INFINITE)
            }
        }
        // Conjunction::heuristic_value (sum, short-circuit on infinite).
        Formula::Conjunction(cs) => {
            let mut h = HeuristicValue::ZERO;
            let mut hs = HeuristicValue::ZERO;
            for f in cs {
                if h.infinite() {
                    break;
                }
                let (hi, hsi) = formula_heuristic_value(pg, predicates, f, step_id, bindings);
                h.add_assign(&hi);
                hs.add_assign(&hsi);
            }
            (h, hs)
        }
        // Disjunction::heuristic_value (min, short-circuit on zero).
        Formula::Disjunction(ds) => {
            let mut h = HeuristicValue::INFINITE;
            let mut hs = HeuristicValue::INFINITE;
            for f in ds {
                if h.zero() {
                    break;
                }
                let (hi, hsi) = formula_heuristic_value(pg, predicates, f, step_id, bindings);
                h = hv_min(h, hi);
                hs = hv_min(hs, hsi);
            }
            (h, hs)
        }
        // Exists::heuristic_value.
        Formula::Exists { body, .. } => {
            formula_heuristic_value(pg, predicates, body, step_id, bindings)
        }
        // Forall::heuristic_value (universal base; classical subset never builds
        // quantified goal conditions, so evaluate the body directly).
        Formula::Forall { body, .. } => {
            formula_heuristic_value(pg, predicates, body, step_id, bindings)
        }
    }
}

/// The reuse-aware formula value used by `Heuristic::plan_rank`. When `reuse`
/// is set, a non-static literal that an existing ordered-before step already
/// achieves is valued at zero cost / unit work.
#[allow(clippy::too_many_arguments)]
pub fn formula_value(
    pg: &PlanningGraph,
    predicates: &PredicateTable,
    ctx: &TypeContext,
    plan: &Plan,
    formula: &Formula,
    step_id: usize,
    reuse: bool,
) -> (HeuristicValue, HeuristicValue) {
    let bindings = plan.bindings.clone();
    if reuse {
        match formula {
            Formula::Atom(_) | Formula::Negation(_) => {
                let literal = match formula {
                    Formula::Atom(a) => Literal::Atom(a.clone()),
                    Formula::Negation(a) => Literal::Negation(a.clone()),
                    _ => unreachable!(),
                };
                // when == AT_START for all classical open conditions.
                if let Some(v) = reuse_literal(predicates, ctx, plan, &literal, step_id) {
                    return v;
                }
                // Fall through to the planning-graph value.
            }
            Formula::Disjunction(ds) => {
                let mut h = HeuristicValue::INFINITE;
                let mut hs = HeuristicValue::INFINITE;
                for f in ds {
                    let (hi, hsi) = formula_value(pg, predicates, ctx, plan, f, step_id, true);
                    h = hv_min(h, hi);
                    hs = hv_min(hs, hsi);
                }
                return (h, hs);
            }
            Formula::Conjunction(cs) => {
                let mut h = HeuristicValue::ZERO;
                let mut hs = HeuristicValue::ZERO;
                for f in cs {
                    let (hi, hsi) = formula_value(pg, predicates, ctx, plan, f, step_id, true);
                    h.add_assign(&hi);
                    hs.add_assign(&hsi);
                }
                return (h, hs);
            }
            Formula::Exists { body, .. } => {
                return formula_value(pg, predicates, ctx, plan, body, step_id, true);
            }
            Formula::Forall { body, .. } => {
                return formula_value(pg, predicates, ctx, plan, body, step_id, true);
            }
            // Equality/Inequality/True/False: fall through to plain value.
            _ => {
                return formula_heuristic_value(
                    pg,
                    predicates,
                    formula,
                    step_id,
                    Some((ctx, &bindings)),
                );
            }
        }
    }
    formula_heuristic_value(pg, predicates, formula, step_id, Some((ctx, &bindings)))
}

impl PlanningGraph {
    /// Extracts a delete-relaxed plan achieving the partial plan's open
    /// conditions and returns the number of actions in it that are **not already
    /// in the partial plan** — the Relax / RePOP heuristic (after Nguyen &
    /// Kambhampati 2001, adapting FF to partial plans). Returns `None` if some
    /// open condition is unreachable in the relaxed graph (a dead end).
    ///
    /// Greedy extraction over the additive cost graph: process the highest-cost
    /// subgoal first, support it with its cheapest achiever, regress on that
    /// action's (positive) preconditions. Goals already true in the initial
    /// state, or — when `reuse` is set — already established by an existing plan
    /// step, are free and add no action. Negative subgoals are treated as free
    /// (a relaxation; the classical benchmark goals are positive).
    pub fn relaxed_plan_size(
        &self,
        ctx: &TypeContext,
        plan: &Plan,
        reuse: bool,
    ) -> Option<f32> {
        let bindings = plan.bindings.clone();
        let mut chosen: HashSet<usize> = HashSet::new();
        let mut achieved: HashSet<Atom> = HashSet::new();
        let mut worklist: VecDeque<Atom> = VecDeque::new();

        // Seed the worklist with the open conditions' positive goal atoms.
        for oc in chain::iter(plan.open_conds()) {
            if let Some(g) = self.goal_atom(&oc.condition, oc.step_id, ctx, &bindings) {
                worklist.push_back(g);
            }
        }

        while let Some(g) = worklist.pop_front() {
            if achieved.contains(&g) {
                continue;
            }
            // Free if already true in the initial state / static.
            if self.heuristic_value_atom(&g, 0, None).zero() {
                achieved.insert(g);
                continue;
            }
            // Reuse: an existing plan step already establishes it (RePOP reuse).
            if reuse && self.reusable_by_step(plan, &g) {
                achieved.insert(g);
                continue;
            }
            match self.cheapest_achiever(&g) {
                None => return None, // unreachable: relaxed dead end
                Some((ai, pre_atoms)) => {
                    achieved.insert(g);
                    chosen.insert(ai);
                    for p in pre_atoms {
                        if !achieved.contains(&p) {
                            worklist.push_back(p);
                        }
                    }
                }
            }
        }
        Some(chosen.len() as f32)
    }

    /// Resolves a (possibly lifted) atomic open condition to the cheapest ground
    /// goal atom under the planning graph. Returns `None` for non-atomic
    /// conditions (negations / (in)equalities / disjunctions are treated as free).
    fn goal_atom(
        &self,
        condition: &Rc<Formula>,
        step_id: usize,
        ctx: &TypeContext,
        bindings: &Bindings,
    ) -> Option<Atom> {
        let atom = match condition.as_ref() {
            Formula::Atom(a) => a,
            _ => return None,
        };
        // Resolve each term through the bindings.
        let resolved: Vec<crate::terms::Term> = atom
            .terms
            .iter()
            .map(|&t| bindings.binding(t, step_id))
            .collect();
        if resolved.iter().all(|t| t.object()) {
            return Some(Atom {
                predicate: atom.predicate,
                terms: resolved,
            });
        }
        // Lifted: pick the cheapest reachable ground atom that unifies.
        let mut best: Option<(Atom, f32)> = None;
        let lifted = Literal::Atom(atom.clone());
        for a in self.predicate_atoms.get(&atom.predicate)? {
            if bindings.unify(ctx, &lifted, step_id, &Literal::Atom(a.clone()), 0) {
                let c = self.heuristic_value_atom(a, 0, None).add_cost();
                if best.as_ref().map_or(true, |(_, bc)| c < *bc) {
                    best = Some((a.clone(), c));
                }
            }
        }
        best.map(|(a, _)| a)
    }

    /// The cheapest achiever of a ground goal atom: the `(action index, positive
    /// precondition atoms)` minimising the additive cost of the action's
    /// preconditions. `None` if no reachable achiever exists.
    fn cheapest_achiever(&self, g: &Atom) -> Option<(usize, Vec<Atom>)> {
        let mut best: Option<(usize, Vec<Atom>, f32)> = None;
        for &(ai, ei) in self.pos_achievers.get(&g.predicate).into_iter().flatten() {
            let action = &self.actions[ai];
            // This ground effect must produce exactly `g`.
            if action.effects[ei].literal.atom() != g {
                continue;
            }
            let pre_atoms = positive_precondition_atoms(&action.precondition);
            let mut cost = 0.0f32;
            let mut reachable = true;
            for p in &pre_atoms {
                let c = self.heuristic_value_atom(p, 0, None).add_cost();
                if c.is_infinite() {
                    reachable = false;
                    break;
                }
                cost += c;
            }
            if !reachable {
                continue;
            }
            if best.as_ref().map_or(true, |(_, _, bc)| cost < *bc) {
                best = Some((ai, pre_atoms, cost));
            }
        }
        best.map(|(ai, pre, _)| (ai, pre))
    }

    /// Whether some existing non-synthetic plan step has a positive effect that
    /// produces the ground atom `g` (RePOP-style reuse).
    fn reusable_by_step(&self, plan: &Plan, g: &Atom) -> bool {
        for step in chain::iter(&plan.steps) {
            if step.action.synthetic() {
                continue;
            }
            for effect in &step.action.effects {
                if let Literal::Atom(a) = &effect.literal {
                    if a == g {
                        return true;
                    }
                }
            }
        }
        false
    }
}

/// Collects the positive (atomic) conjuncts of a precondition formula as ground
/// atoms. Negative literals and (in)equalities are dropped (relaxed away).
fn positive_precondition_atoms(f: &Rc<Formula>) -> Vec<Atom> {
    fn go(f: &Rc<Formula>, out: &mut Vec<Atom>) {
        match f.as_ref() {
            Formula::Atom(a) => out.push(a.clone()),
            Formula::Conjunction(cs) => {
                for c in cs {
                    go(c, out);
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    go(f, &mut out);
    out
}

/// The reuse case for a literal: if a non-static literal is achieved by the
/// effect of some existing step possibly ordered before `step_id`, its value is
/// zero cost / unit work. Returns `None` if no such reusing step exists (the
/// caller then falls back to the graph value).
fn reuse_literal(
    predicates: &PredicateTable,
    ctx: &TypeContext,
    plan: &Plan,
    literal: &Literal,
    step_id: usize,
) -> Option<(HeuristicValue, HeuristicValue)> {
    use crate::orderings::StepTime;
    let gt = StepTime::AtStart; // start_time(AT_START)
    if predicates.is_static(literal.atom().predicate) {
        return None;
    }
    for sc in chain::iter(&plan.steps) {
        let step = sc;
        if step.id != INIT_ID
            && plan
                .orderings
                .possibly_before(step.id, StepTime::AtStart, step_id, gt)
        {
            for e in step.action.effects.iter() {
                let et = StepTime::AtEnd; // end_time(e) for classical AT_END
                if plan.orderings.possibly_before(step.id, et, step_id, gt) {
                    // typeid match: positive vs positive, negative vs negative.
                    if effect_same_sign(literal, e) {
                        let elit = Literal::from_effect(e);
                        if plan.bindings.unify(ctx, literal, step_id, &elit, step.id) {
                            // when == AT_START (!= AT_END): hs = ZERO_COST_UNIT_WORK.
                            return Some((
                                HeuristicValue::ZERO_COST_UNIT_WORK,
                                HeuristicValue::ZERO_COST_UNIT_WORK,
                            ));
                        }
                    }
                }
            }
        }
    }
    None
}

fn effect_same_sign(literal: &Literal, effect: &Effect) -> bool {
    literal.negative() == effect.literal.negative()
}

fn binding_consistent(
    ctx: &TypeContext,
    bindings: &Bindings,
    formula: &Formula,
    step_id: usize,
) -> bool {
    use crate::terms::Term;
    let (left, left_id, right, right_id, is_eq) = match formula {
        Formula::Equality {
            left,
            left_id,
            right,
            right_id,
        } => (*left, *left_id, *right, *right_id, true),
        Formula::Inequality {
            left,
            left_id,
            right,
            right_id,
        } => (*left, *left_id, *right, *right_id, false),
        _ => return true,
    };
    let lid = left_id.unwrap_or(step_id);
    let rid = right_id.unwrap_or(step_id);
    let lb = bindings.binding(left, lid);
    let rb = bindings.binding(right, rid);
    match (lb, rb) {
        // Both resolved to constants: decide directly.
        (Term::Object(a), Term::Object(b)) => {
            if is_eq {
                a == b
            } else {
                a != b
            }
        }
        // At least one variable: check domain overlap. For equality, the value
        // must be jointly achievable; for inequality, it is satisfiable unless
        // both are pinned to the same single constant (handled above).
        _ => {
            if is_eq {
                let dl = term_domain(ctx, bindings, left, lid);
                let dr = term_domain(ctx, bindings, right, rid);
                dl.iter().any(|o| dr.contains(o))
            } else {
                true
            }
        }
    }
}

fn term_domain(
    ctx: &TypeContext,
    bindings: &Bindings,
    term: crate::terms::Term,
    step_id: usize,
) -> std::collections::BTreeSet<crate::terms::Object> {
    use crate::terms::Term;
    match term {
        Term::Object(o) => {
            let mut s = std::collections::BTreeSet::new();
            s.insert(o);
            s
        }
        Term::Variable(v) => bindings.domain(ctx, v, step_id),
    }
}
