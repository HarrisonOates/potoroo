//! The relaxed planning graph and additive cost/work heuristic values.
//!
//! The graph is built once from the problem's init atoms (cost 0) and the
//! domain's instantiated action schemas, iterating to a fixpoint over the
//! additive cost/work values of every reachable ground literal.

use std::collections::VecDeque;
use std::rc::Rc;

use crate::action::ActionSchema;
use crate::bindings::{AtomPattern, Bindings, TypeContext};
use crate::chain;
use crate::effect::Effect;
use crate::fasthash::{FastMap, FastSet};
use crate::formula::{Atom, Formula, Literal};
use crate::instantiate::{
    instantiate_atom, instantiate_effect, instantiate_formula, precondition_consistent,
};
use crate::params::ActionCost;
use crate::plan::{Plan, StepAction, INIT_ID};
use crate::predicates::{Predicate, PredicateTable};
use crate::terms::{Object, Term, Variable};
use crate::types::Type;

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

/// Which of the graph's two relations a lookup reads: the atoms the relaxed
/// graph can achieve, or the ones it can negate.
#[derive(Debug, Clone, Copy)]
enum Relation {
    Positive,
    Negated,
}

/// A positional index over one predicate's reachable ground atoms:
/// `positions[argument]` maps an object to the atoms carrying it there, as
/// ascending indices into the predicate's atom list.
///
/// Lifted lookups resolve an open condition to an [`AtomPattern`] in which some
/// argument positions are fixed to objects. Probing the index on a fixed
/// position replaces a scan of the whole relation with a scan of one posting
/// list, which is what makes `at(truck1, ?loc)` cost the truck's locations
/// rather than every location of every truck.
#[derive(Debug, Default)]
struct AtomIndex {
    positions: Vec<FastMap<Object, Vec<u32>>>,
}

impl AtomIndex {
    fn build<'a>(atoms: impl Iterator<Item = &'a Atom>) -> AtomIndex {
        let mut positions: Vec<FastMap<Object, Vec<u32>>> = Vec::new();
        for (position, atom) in atoms.enumerate() {
            if positions.len() < atom.terms.len() {
                positions.resize_with(atom.terms.len(), FastMap::default);
            }
            for (argument, &term) in atom.terms.iter().enumerate() {
                if let Term::Object(object) = term {
                    positions[argument]
                        .entry(object)
                        .or_default()
                        .push(position as u32);
                }
            }
        }
        AtomIndex { positions }
    }

    /// The shortest posting list among the argument positions the caller has
    /// already fixed to an object, or `None` when nothing is fixed and the whole
    /// relation must be scanned. A fixed position whose object never occurs
    /// there yields an empty list, which decides the lookup outright.
    fn candidates(&self, bound: impl Iterator<Item = (usize, Object)>) -> Option<&[u32]> {
        const NONE: &[u32] = &[];
        let mut best: Option<&[u32]> = None;
        for (position, object) in bound {
            let posting = self
                .positions
                .get(position)
                .and_then(|by_object| by_object.get(&object))
                .map_or(NONE, |atoms| atoms.as_slice());
            if best.is_none_or(|shortest| posting.len() < shortest.len()) {
                best = Some(posting);
            }
            if best.is_some_and(<[u32]>::is_empty) {
                break;
            }
        }
        best
    }
}

/// The `Bindings::unify` oracle that [`PlanningGraph::for_each_match`] checks
/// [`AtomPattern::matches`] against in debug builds.
fn unifies(
    ctx: &TypeContext,
    bindings: &Bindings,
    atom: &Atom,
    step_id: usize,
    candidate: &Atom,
) -> bool {
    bindings.unify(
        ctx,
        &Literal::Atom(atom.clone()),
        step_id,
        &Literal::Atom(candidate.clone()),
        0,
    )
}

/// Groups ground atoms by predicate and indexes each resulting relation.
fn group_by_predicate<'a>(
    atoms: impl Iterator<Item = &'a Atom>,
) -> (FastMap<Predicate, Vec<Atom>>, FastMap<Predicate, AtomIndex>) {
    let mut table: FastMap<Predicate, Vec<Atom>> = FastMap::default();
    for atom in atoms {
        table.entry(atom.predicate).or_default().push(atom.clone());
    }
    let index = table
        .iter()
        .map(|(&predicate, atoms)| (predicate, AtomIndex::build(atoms.iter())))
        .collect();
    (table, index)
}

pub struct PlanningGraph {
    atom_values: FastMap<Atom, HeuristicValue>,
    negation_values: FastMap<Atom, HeuristicValue>,
    predicate_atoms: FastMap<Predicate, Vec<Atom>>,
    predicate_negations: FastMap<Predicate, Vec<Atom>>,
    /// The atoms true in the initial state, distinct from "reachable at zero
    /// cost" once zero-cost actions exist.
    init_atoms: FastSet<Atom>,
    /// Positional indexes over the two relations above, parallel to them.
    atom_index: FastMap<Predicate, AtomIndex>,
    negation_index: FastMap<Predicate, AtomIndex>,
    /// The ground actions the graph was built from (for relaxed-plan extraction
    /// by the Relax heuristic; unused by the additive heuristics).
    actions: Vec<Rc<StepAction>>,
    /// Predicate -> `(action index, effect index)` of every positive add effect,
    /// for finding achievers of a goal atom during relaxed-plan extraction.
    pos_achievers: FastMap<Predicate, Vec<(usize, usize)>>,
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
            atom_values: FastMap::default(),
            negation_values: FastMap::default(),
            predicate_atoms: FastMap::default(),
            predicate_negations: FastMap::default(),
            init_atoms: FastSet::default(),
            atom_index: FastMap::default(),
            negation_index: FastMap::default(),
            actions: Vec::new(),
            pos_achievers: FastMap::default(),
        };

        // Add initial conditions at level 0 (heuristics.cc:471-485).
        for effect in init_action.effects.iter() {
            let atom = effect.literal.atom().clone();
            if !effect.literal.negative() {
                pg.init_atoms.insert(atom.clone());
            }
            if predicates.is_static(atom.predicate) {
                pg.atom_values.entry(atom).or_insert(HeuristicValue::ZERO);
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
            let mut new_atom_values: FastMap<Atom, HeuristicValue> = FastMap::default();
            let mut new_negation_values: FastMap<Atom, HeuristicValue> = FastMap::default();

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
                    // Makespan remains a classical unit layer; additive cost
                    // uses the task's declared action cost.
                    cond_value.increase_makespan(THRESHOLD);
                    cond_value.increase_cost(action.cost as f32);

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
                                    // A negation is free unless the atom starts true.
                                    if pg.init_atoms.contains(atom) {
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
        let (atoms, atom_index) = group_by_predicate(pg.atom_values.keys());
        pg.predicate_atoms = atoms;
        pg.atom_index = atom_index;
        let (negations, negation_index) = group_by_predicate(pg.negation_values.keys());
        pg.predicate_negations = negations;
        pg.negation_index = negation_index;

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

    /// Builds the relaxed planning graph from `init_action` and a set of action
    /// `schemas`, without pre-grounding them. For each fixpoint iteration, each
    /// schema is applied to every type-compatible parameter tuple; only tuples
    /// whose precondition is achievable at the current level are processed. This
    /// avoids the O(n^m) upfront grounding cost while producing identical
    /// `atom_values` to `build`.
    ///
    /// `get_objects(ty)` must return all problem objects of (sub)type `ty`.
    pub fn build_from_schemas(
        predicates: &PredicateTable,
        init_action: &Rc<StepAction>,
        schemas: &[ActionSchema],
        get_objects: impl Fn(Type) -> Vec<Object>,
        cost_model: ActionCost,
        task_costs: bool,
    ) -> PlanningGraph {
        let mut pg = PlanningGraph {
            atom_values: FastMap::default(),
            negation_values: FastMap::default(),
            predicate_atoms: FastMap::default(),
            predicate_negations: FastMap::default(),
            init_atoms: FastSet::default(),
            atom_index: FastMap::default(),
            negation_index: FastMap::default(),
            actions: Vec::new(),
            pos_achievers: FastMap::default(),
        };

        // Initialise level 0 from the init atoms.
        for effect in init_action.effects.iter() {
            let atom = effect.literal.atom().clone();
            if !effect.literal.negative() {
                pg.init_atoms.insert(atom.clone());
            }
            if predicates.is_static(atom.predicate) {
                pg.atom_values.entry(atom).or_insert(HeuristicValue::ZERO);
            } else {
                pg.atom_values
                    .entry(atom)
                    .or_insert(HeuristicValue::ZERO_COST_UNIT_WORK);
            }
        }

        // Pre-compute the compatible-object lists for every type that appears
        // as a schema parameter, so `get_objects` is called at most once per type.
        let mut type_domains: FastMap<Type, Vec<Object>> = FastMap::default();
        for schema in schemas {
            // Quantified-effect variables are enumerated just like parameters,
            // so their types need a domain as well.
            let vars = schema
                .parameters
                .iter()
                .chain(schema.effects.iter().flat_map(|e| e.parameters.iter()));
            for &v in vars {
                let ty = schema.var_types[v.0 as usize];
                type_domains.entry(ty).or_insert_with(|| get_objects(ty));
            }
        }
        let type_sets: FastMap<Type, FastSet<Object>> = type_domains
            .iter()
            .map(|(ty, objs)| (*ty, objs.iter().copied().collect()))
            .collect();

        // Fixpoint.
        loop {
            let mut changed = false;
            let mut new_atom_values: FastMap<Atom, HeuristicValue> = FastMap::default();
            let mut new_negation_values: FastMap<Atom, HeuristicValue> = FastMap::default();
            let atoms_by_pred = atoms_by_predicate(&pg.atom_values, predicates.len());

            for schema in schemas {
                let action_cost = if task_costs {
                    cost_model.resolve(schema.cost)
                } else {
                    1
                };
                let mut je = JoinEnum::new(schema, &atoms_by_pred, &type_domains, &type_sets);
                je.run(&mut |subst, _tuple| {
                    apply_schema_tuple(
                        schema,
                        action_cost,
                        subst,
                        &pg,
                        predicates,
                        &atoms_by_pred,
                        &type_domains,
                        &type_sets,
                        &mut new_atom_values,
                        &mut new_negation_values,
                        &mut changed,
                    );
                });
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

        // Build predicate-to-atom indexes (same as `build`).
        let (atoms, atom_index) = group_by_predicate(pg.atom_values.keys());
        pg.predicate_atoms = atoms;
        pg.atom_index = atom_index;
        let (negations, negation_index) = group_by_predicate(pg.negation_values.keys());
        pg.predicate_negations = negations;
        pg.negation_index = negation_index;

        // Collect the reachable ground actions for relaxed-plan extraction.
        // Only tuples whose precondition has finite value at convergence are
        // included, which is the same subset that `cheapest_achiever` would
        // accept from a full ground-action list.
        let mut reachable_actions: Vec<Rc<StepAction>> = Vec::new();
        let atoms_by_pred = atoms_by_predicate(&pg.atom_values, predicates.len());
        for schema in schemas {
            let mut je = JoinEnum::new(schema, &atoms_by_pred, &type_domains, &type_sets);
            je.run(&mut |subst, tuple| {
                collect_reachable_tuple(
                    schema,
                    subst,
                    tuple,
                    &pg,
                    predicates,
                    &mut reachable_actions,
                );
            });
        }
        pg.actions = reachable_actions;

        // Index positive add effects for relaxed-plan extraction.
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

    /// Visits the reachable atoms of `predicate` that unify with `pattern`,
    /// narrowing the scan through the positional index whenever the pattern
    /// fixes an argument; `visit` returns `false` to stop early. Visit order
    /// matches a full relation scan, because posting lists are built in
    /// relation order, so callers that break ties by position are unaffected.
    ///
    /// Debug builds cross-check each visited candidate against `unifies`, and
    /// check that narrowing dropped no atom the full scan would have matched.
    fn for_each_match(
        &self,
        relation: Relation,
        predicate: Predicate,
        ctx: &TypeContext,
        pattern: &mut AtomPattern,
        unifies: impl Fn(&Atom) -> bool,
        mut visit: impl FnMut(&Atom) -> bool,
    ) {
        let (table, index) = match relation {
            Relation::Positive => (&self.predicate_atoms, &self.atom_index),
            Relation::Negated => (&self.predicate_negations, &self.negation_index),
        };
        let Some(atoms) = table.get(&predicate) else {
            return;
        };
        let candidates = index
            .get(&predicate)
            .and_then(|index| index.candidates(pattern.bound_positions()));

        #[cfg(debug_assertions)]
        if let Some(candidates) = candidates {
            for (position, atom) in atoms.iter().enumerate() {
                assert!(
                    !pattern.matches(ctx, &atom.terms) || candidates.contains(&(position as u32)),
                    "the positional index dropped a matching atom"
                );
            }
        }

        let mut scan = |atom: &Atom| {
            let matched = pattern.matches(ctx, &atom.terms);
            debug_assert_eq!(
                matched,
                unifies(atom),
                "AtomPattern::matches diverged from Bindings::unify"
            );
            !matched || visit(atom)
        };
        match candidates {
            Some(candidates) => {
                for &position in candidates {
                    if !scan(&atoms[position as usize]) {
                        return;
                    }
                }
            }
            None => {
                for atom in atoms {
                    if !scan(atom) {
                        return;
                    }
                }
            }
        }
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
                // Take minimum value over ground atoms that unify. The pattern
                // is resolved against the bindings once; per-candidate matching
                // is then cheap positional checks instead of full unification.
                let mut pattern = b.resolve_pattern(ctx, &atom.terms, step_id);
                self.positive_value_for(atom, step_id, ctx, b, &mut pattern)
            }
        }
    }

    /// Minimum value over the reachable ground atoms `pattern` admits. Split out
    /// of [`PlanningGraph::heuristic_value_atom`] so [`Self::heuristic_value_negation`]
    /// can reuse an already-resolved pattern instead of resolving it twice.
    fn positive_value_for(
        &self,
        atom: &Atom,
        step_id: usize,
        ctx: &TypeContext,
        b: &Bindings,
        pattern: &mut AtomPattern,
    ) -> HeuristicValue {
        if let Some(terms) = pattern.object_terms() {
            // Fully bound: a single hash lookup decides it.
            let ground = Atom {
                predicate: atom.predicate,
                terms,
            };
            return self.heuristic_value_atom(&ground, 0, None);
        }
        let mut value = HeuristicValue::INFINITE;
        self.for_each_match(
            Relation::Positive,
            atom.predicate,
            ctx,
            pattern,
            |candidate| unifies(ctx, b, atom, step_id, candidate),
            |candidate| {
                value = hv_min(value, self.heuristic_value_atom(candidate, 0, None));
                !value.zero()
            },
        );
        value
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
                } else if self.init_atoms.contains(atom) {
                    // True from the start and nothing achieves its negation.
                    HeuristicValue::INFINITE
                } else {
                    // False from the start: the negation costs nothing.
                    HeuristicValue::ZERO_COST_UNIT_WORK
                }
            }
            Some((ctx, b)) => {
                let mut pattern = b.resolve_pattern(ctx, &atom.terms, step_id);
                if !self
                    .positive_value_for(atom, step_id, ctx, b, &mut pattern)
                    .zero()
                {
                    return HeuristicValue::ZERO;
                }
                if let Some(terms) = pattern.object_terms() {
                    // Fully bound: decide membership in the negation table
                    // directly (the scan below values candidates through
                    // `heuristic_value_atom`, so mirror that here).
                    let ground = Atom {
                        predicate: atom.predicate,
                        terms,
                    };
                    return if self.negation_values.contains_key(&ground) {
                        self.heuristic_value_atom(&ground, 0, None)
                    } else if self.init_atoms.contains(&ground) {
                        HeuristicValue::INFINITE
                    } else {
                        HeuristicValue::ZERO_COST_UNIT_WORK
                    };
                }
                let mut value = HeuristicValue::INFINITE;
                self.for_each_match(
                    Relation::Negated,
                    atom.predicate,
                    ctx,
                    &mut pattern,
                    |candidate| unifies(ctx, b, atom, step_id, candidate),
                    |candidate| {
                        value = hv_min(value, self.heuristic_value_atom(candidate, 0, None));
                        !value.zero()
                    },
                );
                if value.zero() {
                    return value;
                }
                // No action achieves the negation, but a tuple simply absent
                // from the relation is free by the closed-world assumption. A
                // partially-bound pattern can't enumerate the complement, so
                // count matches that are true initially and compare against
                // the tuples the pattern admits: any surplus is a false atom.
                let mut initially_true = 0u64;
                self.for_each_match(
                    Relation::Positive,
                    atom.predicate,
                    ctx,
                    &mut pattern,
                    |candidate| unifies(ctx, b, atom, step_id, candidate),
                    |candidate| {
                        if self.init_atoms.contains(candidate) {
                            initially_true += 1;
                        }
                        true
                    },
                );
                if pattern.admitted_tuples(ctx) > initially_true {
                    value = hv_min(value, HeuristicValue::ZERO_COST_UNIT_WORK);
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
        search_ctx: &crate::search::SearchContext,
        plan: &Plan,
        reuse: bool,
    ) -> Option<f32> {
        let ctx = search_ctx.type_ctx();
        let bindings = plan.bindings.clone();
        let mut chosen: FastSet<usize> = FastSet::default();
        let mut achieved: FastSet<Atom> = FastSet::default();
        let mut worklist: VecDeque<Atom> = VecDeque::new();

        // Seed the worklist with the open conditions' positive goal atoms.
        for oc in chain::iter(plan.open_conds()) {
            if let Some(g) = self.goal_atom(&oc.condition, oc.step_id, &ctx, &bindings) {
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
            match self.cheapest_achiever(&g, search_ctx) {
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
        Some(
            chosen
                .into_iter()
                .map(|index| search_ctx.action_cost(&self.actions[index]) as f32)
                .sum(),
        )
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
        let mut pattern = bindings.resolve_pattern(ctx, &atom.terms, step_id);
        self.for_each_match(
            Relation::Positive,
            atom.predicate,
            ctx,
            &mut pattern,
            |candidate| unifies(ctx, bindings, atom, step_id, candidate),
            |candidate| {
                let cost = self.heuristic_value_atom(candidate, 0, None).add_cost();
                if best.as_ref().is_none_or(|(_, best_cost)| cost < *best_cost) {
                    best = Some((candidate.clone(), cost));
                }
                true
            },
        );
        best.map(|(a, _)| a)
    }

    /// The cheapest achiever of a ground goal atom: the `(action index, positive
    /// precondition atoms)` minimising the additive cost of the action's
    /// preconditions. `None` if no reachable achiever exists.
    fn cheapest_achiever(
        &self,
        g: &Atom,
        search_ctx: &crate::search::SearchContext,
    ) -> Option<(usize, Vec<Atom>)> {
        let mut best: Option<(usize, Vec<Atom>, f32)> = None;
        for &(ai, ei) in self.pos_achievers.get(&g.predicate).into_iter().flatten() {
            let action = &self.actions[ai];
            // This ground effect must produce exactly `g`.
            if action.effects[ei].literal.atom() != g {
                continue;
            }
            let pre_atoms = positive_precondition_atoms(&action.precondition);
            let mut cost = search_ctx.action_cost(action) as f32;
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

/// Collects the positive atomic conjuncts of a precondition reachable through
/// nested conjunctions: the join queries driving schema instantiation.
fn collect_join_atoms<'a>(f: &'a Formula, out: &mut Vec<&'a Atom>) {
    match f {
        Formula::Atom(a) => out.push(a),
        Formula::Conjunction(cs) => {
            for c in cs {
                collect_join_atoms(c, out);
            }
        }
        _ => {}
    }
}

/// Backtracking join enumerating every parameter tuple of a schema whose
/// positive precondition conjuncts all match currently-reachable ground atoms.
/// Tuples skipped by the join are exactly those with an unreachable positive
/// conjunct, whose precondition value is infinite — the per-tuple processing
/// discards them anyway — so replacing the Cartesian type-domain enumeration
/// with this join leaves the resulting planning graph unchanged while making
/// instantiation proportional to the number of matches.
struct JoinEnum<'a> {
    /// Types of every variable in the schema's scope, indexed by variable
    /// index. Covers schema parameters and quantified-effect variables alike.
    var_types: &'a [Type],
    /// The variables to enumerate: a schema's parameters, or one universally
    /// quantified effect's own parameters.
    params: &'a [Variable],
    /// Positive conjuncts of the formula being joined -- a schema's
    /// precondition, or a conditional effect's guard.
    join: Vec<&'a Atom>,
    used: Vec<bool>,
    /// Currently-reachable ground atoms, by predicate, with their indexes.
    atoms_by_pred: &'a [Option<JoinRelation<'a>>],
    /// Type-compatible objects per parameter type (for the membership check on
    /// join-bound objects, and for enumerating join-unconstrained parameters).
    type_domains: &'a FastMap<Type, Vec<Object>>,
    type_sets: &'a FastMap<Type, FastSet<Object>>,
    /// Dense substitution indexed by `Variable.0`: schema variable indices are
    /// small and contiguous, so an array beats a hash map for the per-candidate
    /// read/write this join does at every step.
    subst: Vec<Option<Object>>,
    /// Shared LIFO stack of variables newly bound by the in-progress
    /// `match_candidate` calls, one contiguous run per call (nested calls push
    /// and pop their own before returning, so it always nests correctly). A
    /// single growable buffer reused across every candidate probed, instead of
    /// a fresh `Vec` per call -- this join tries many candidates that fail
    /// after binding one or two variables.
    bound_stack: Vec<Variable>,
}

impl<'a> JoinEnum<'a> {
    fn new(
        schema: &'a ActionSchema,
        atoms_by_pred: &'a [Option<JoinRelation<'a>>],
        type_domains: &'a FastMap<Type, Vec<Object>>,
        type_sets: &'a FastMap<Type, FastSet<Object>>,
    ) -> Self {
        JoinEnum::over(
            &schema.var_types,
            &schema.parameters,
            &schema.precondition,
            atoms_by_pred,
            type_domains,
            type_sets,
        )
    }

    /// Enumerates `params` against the positive conjuncts of `join_source`: a
    /// schema's parameters against its precondition, or (with
    /// [`JoinEnum::seed`]) a quantified effect's variables against its guard.
    fn over(
        var_types: &'a [Type],
        params: &'a [Variable],
        join_source: &'a Formula,
        atoms_by_pred: &'a [Option<JoinRelation<'a>>],
        type_domains: &'a FastMap<Type, Vec<Object>>,
        type_sets: &'a FastMap<Type, FastSet<Object>>,
    ) -> Self {
        let mut join = Vec::new();
        collect_join_atoms(join_source, &mut join);
        let used = vec![false; join.len()];
        JoinEnum {
            var_types,
            params,
            join,
            used,
            atoms_by_pred,
            type_domains,
            type_sets,
            subst: vec![None; var_types.len()],
            bound_stack: Vec::new(),
        }
    }

    /// Pre-binds variables fixed by an enclosing scope. `subst` is always the
    /// same schema's dense substitution, so it's exactly as long as `self.subst`.
    fn seed(&mut self, subst: &[Option<Object>]) {
        self.subst.copy_from_slice(subst);
    }

    /// The declared type of a variable in the schema's scope.
    fn var_type(&self, v: Variable) -> Type {
        self.var_types[v.0 as usize]
    }

    fn run(&mut self, visit: &mut dyn FnMut(&[Option<Object>], &[Object])) {
        // Pick the unused join conjunct with the fewest unbound variables,
        // tie-broken by smallest candidate list.
        let mut pick: Option<(usize, (usize, usize))> = None;
        for (i, ja) in self.join.iter().enumerate() {
            if self.used[i] {
                continue;
            }
            let unbound = ja
                .terms
                .iter()
                .filter(|t| matches!(t, Term::Variable(v) if self.subst[v.0 as usize].is_none()))
                .count();
            let cands = self
                .atoms_by_pred
                .get(ja.predicate.0 as usize)
                .and_then(|r| r.as_ref())
                .map_or(0, |relation| relation.atoms.len());
            let key = (unbound, cands);
            if pick.map_or(true, |(_, k)| key < k) {
                pick = Some((i, key));
            }
        }
        let Some((i, _)) = pick else {
            // All conjuncts matched: enumerate any remaining unbound
            // parameters over their type domains, then emit the tuple.
            self.enumerate_rest(0, visit);
            return;
        };
        self.used[i] = true;
        let ja: &'a Atom = self.join[i];
        // `atoms_by_pred` outlives `self`, so copying the reference out lets the
        // candidate loop borrow the relation across the recursive call instead
        // of cloning it at every join step.
        let relations = self.atoms_by_pred;
        if let Some(relation) = relations
            .get(ja.predicate.0 as usize)
            .and_then(|r| r.as_ref())
        {
            // Probe the index with the conjunct's constants plus the variables
            // the partial substitution has already bound: the deeper the join
            // recursion, the more selective the probe. Positions still free stay
            // open and are matched candidate by candidate.
            let bound = ja.terms.iter().enumerate().filter_map(|(position, term)| {
                let object = match term {
                    Term::Object(object) => *object,
                    Term::Variable(variable) => self.subst[variable.0 as usize]?,
                };
                Some((position, object))
            });
            match relation.index.candidates(bound) {
                Some(candidates) => {
                    for &position in candidates {
                        self.match_candidate(ja, relation.atoms[position as usize], visit);
                    }
                }
                None => {
                    for &candidate in &relation.atoms {
                        self.match_candidate(ja, candidate, visit);
                    }
                }
            }
        }
        self.used[i] = false;
    }

    /// Matches one join conjunct against a ground candidate under the partial
    /// substitution, recursing when it unifies and undoing its bindings after.
    fn match_candidate(
        &mut self,
        conjunct: &'a Atom,
        candidate: &'a Atom,
        visit: &mut dyn FnMut(&[Option<Object>], &[Object]),
    ) {
        let mark = self.bound_stack.len();
        let mut ok = true;
        for (t, gt) in conjunct.terms.iter().zip(candidate.terms.iter()) {
            let Term::Object(o) = gt else {
                ok = false;
                break;
            };
            match t {
                Term::Object(p) => {
                    if p != o {
                        ok = false;
                        break;
                    }
                }
                Term::Variable(v) => match self.subst[v.0 as usize] {
                    Some(b) => {
                        if b != *o {
                            ok = false;
                            break;
                        }
                    }
                    None => {
                        // The Cartesian enumeration only ever tried objects
                        // from the parameter's type domain.
                        if !self.type_sets[&self.var_type(*v)].contains(o) {
                            for &v in &self.bound_stack[mark..] {
                                self.subst[v.0 as usize] = None;
                            }
                            self.bound_stack.truncate(mark);
                            return;
                        }
                        self.subst[v.0 as usize] = Some(*o);
                        self.bound_stack.push(*v);
                    }
                },
            }
        }
        if ok {
            self.run(visit);
        }
        for &v in &self.bound_stack[mark..] {
            self.subst[v.0 as usize] = None;
        }
        self.bound_stack.truncate(mark);
    }

    /// Enumerates parameters not bound by any join conjunct over their type
    /// domains, then emits the complete tuple.
    fn enumerate_rest(&mut self, from: usize, visit: &mut dyn FnMut(&[Option<Object>], &[Object])) {
        let params = self.params;
        let mut k = from;
        while k < params.len() && self.subst[params[k].0 as usize].is_some() {
            k += 1;
        }
        if k == params.len() {
            let tuple: Vec<Object> = params
                .iter()
                .map(|p| self.subst[p.0 as usize].expect("param bound by join or enumeration"))
                .collect();
            visit(&self.subst, &tuple);
            return;
        }
        let v = params[k];
        let ty = self.var_type(v);
        let domains = self.type_domains;
        for &obj in &domains[&ty] {
            self.subst[v.0 as usize] = Some(obj);
            self.enumerate_rest(k + 1, visit);
        }
        self.subst[v.0 as usize] = None;
    }
}

/// One predicate's currently-reachable atoms, with the positional index the
/// join probes with the variables its partial substitution has already bound.
struct JoinRelation<'a> {
    atoms: Vec<&'a Atom>,
    index: AtomIndex,
}

/// Groups the currently-reachable atoms by predicate for the join, indexing
/// each relation. Dense by predicate id (small and contiguous, like
/// `Variable`/`Object`), so the join's per-conjunct relation lookup is an
/// array index instead of a hash lookup.
fn atoms_by_predicate(
    atom_values: &FastMap<Atom, HeuristicValue>,
    num_predicates: usize,
) -> Vec<Option<JoinRelation<'_>>> {
    let mut grouped: Vec<Vec<&Atom>> = vec![Vec::new(); num_predicates];
    for atom in atom_values.keys() {
        grouped[atom.predicate.0 as usize].push(atom);
    }
    grouped
        .into_iter()
        .map(|atoms| {
            if atoms.is_empty() {
                return None;
            }
            let index = AtomIndex::build(atoms.iter().copied());
            Some(JoinRelation { atoms, index })
        })
        .collect()
}

/// Per-tuple processing of `apply_schema_tuples`: updates `new_atom_values` /
/// `new_negation_values` with the cost of each reachable effect of a
/// statically-consistent tuple whose precondition has a finite value in `pg`.
#[allow(clippy::too_many_arguments)]
fn apply_schema_tuple(
    schema: &ActionSchema,
    action_cost: usize,
    subst: &[Option<Object>],
    pg: &PlanningGraph,
    predicates: &PredicateTable,
    atoms_by_pred: &[Option<JoinRelation<'_>>],
    type_domains: &FastMap<Type, Vec<Object>>,
    type_sets: &FastMap<Type, FastSet<Object>>,
    new_atom_values: &mut FastMap<Atom, HeuristicValue>,
    new_negation_values: &mut FastMap<Atom, HeuristicValue>,
    changed: &mut bool,
) {
    if !precondition_consistent(&schema.precondition, subst) {
        return;
    }

    let ground_pre = instantiate_formula(&schema.precondition, subst);
    let (pre_value, _) = pg.ground_formula_value(predicates, &ground_pre);
    if pre_value.infinite() {
        return;
    }

    for effect in &schema.effects {
        if effect.parameters.is_empty() {
            apply_effect_tuple(
                effect,
                action_cost,
                subst,
                &pre_value,
                pg,
                predicates,
                new_atom_values,
                new_negation_values,
                changed,
            );
            continue;
        }
        // A quantified effect: join its guard for its own variables too, seeded
        // with the schema tuple's substitution.
        let mut je = JoinEnum::over(
            &schema.var_types,
            &effect.parameters,
            &effect.condition,
            atoms_by_pred,
            type_domains,
            type_sets,
        );
        je.seed(subst);
        je.run(&mut |effect_subst, _tuple| {
            apply_effect_tuple(
                effect,
                action_cost,
                effect_subst,
                &pre_value,
                pg,
                predicates,
                new_atom_values,
                new_negation_values,
                changed,
            );
        });
    }
}

/// Applies one effect of one fully-substituted schema tuple to the graph.
/// `subst` binds the schema's parameters and, for a quantified effect, its own
/// variables too.
#[allow(clippy::too_many_arguments)]
fn apply_effect_tuple(
    effect: &Effect,
    action_cost: usize,
    subst: &[Option<Object>],
    pre_value: &HeuristicValue,
    pg: &PlanningGraph,
    predicates: &PredicateTable,
    new_atom_values: &mut FastMap<Atom, HeuristicValue>,
    new_negation_values: &mut FastMap<Atom, HeuristicValue>,
    changed: &mut bool,
) {
    let ground_cond = instantiate_formula(&effect.condition, subst);
    let (mut cond_value, _) = pg.ground_formula_value(predicates, &ground_cond);
    if cond_value.infinite() {
        return;
    }
    cond_value.add_assign(pre_value);
    cond_value.increase_makespan(THRESHOLD);
    cond_value.increase_cost(action_cost as f32);

    let lit = match &effect.literal {
        Literal::Atom(a) => {
            let ga = instantiate_atom(a, subst);
            // A quantified variable the join left unbound cannot name a
            // ground atom; nothing to record.
            if ga.terms.iter().any(|t| t.variable()) {
                return;
            }
            Literal::Atom(ga)
        }
        Literal::Negation(a) => {
            let ga = instantiate_atom(a, subst);
            if ga.terms.iter().any(|t| t.variable()) {
                return;
            }
            Literal::Negation(ga)
        }
    };

    match lit {
        Literal::Atom(atom) => {
            let existing = new_atom_values
                .get(&atom)
                .or_else(|| pg.atom_values.get(&atom))
                .copied();
            let mut new_value = cond_value;
            new_value.increment_work();
            match existing {
                None => {
                    new_atom_values.insert(atom, new_value);
                    *changed = true;
                }
                Some(old_value) => {
                    let merged = hv_min(new_value, old_value);
                    if merged != old_value {
                        new_atom_values.insert(atom, merged);
                        *changed = true;
                    }
                }
            }
        }
        Literal::Negation(atom) => {
            let existing = new_negation_values
                .get(&atom)
                .or_else(|| pg.negation_values.get(&atom))
                .copied();
            match existing {
                None => {
                    // A negation is free unless the atom starts true.
                    if pg.init_atoms.contains(&atom) {
                        let mut new_value = cond_value;
                        new_value.increment_work();
                        new_negation_values.insert(atom, new_value);
                        *changed = true;
                    }
                }
                Some(old_value) => {
                    let mut new_value = cond_value;
                    new_value.increment_work();
                    let merged = hv_min(new_value, old_value);
                    if merged != old_value {
                        new_negation_values.insert(atom, merged);
                        *changed = true;
                    }
                }
            }
        }
    }
}

/// Per-tuple processing of `collect_reachable`: appends the ground
/// `StepAction` for a statically-consistent tuple whose precondition is
/// reachable at convergence. Only reachable actions need be stored for
/// relaxed-plan extraction.
fn collect_reachable_tuple(
    schema: &ActionSchema,
    subst: &[Option<Object>],
    tuple: &[Object],
    pg: &PlanningGraph,
    predicates: &PredicateTable,
    out: &mut Vec<Rc<StepAction>>,
) {
    if !precondition_consistent(&schema.precondition, subst) {
        return;
    }
    let ground_pre = instantiate_formula(&schema.precondition, subst);
    let (pre_value, _) = pg.ground_formula_value(predicates, &ground_pre);
    if pre_value.infinite() {
        return;
    }
    let effects: Vec<Effect> = schema
        .effects
        .iter()
        .map(|e| instantiate_effect(e, subst))
        .collect();
    out.push(Rc::new(StepAction {
        name: schema.name.clone(),
        parameters: Vec::new(),
        arguments: tuple.to_vec(),
        precondition: ground_pre,
        effects,
        cost: schema.cost,
        var_types: Vec::new(),
    }));
}
