//! Ground POCL search directly over a translated SAS+ task.
//!
//! Conditions and causal links protect [`Fact`](crate::fdr::Fact) equalities,
//! while effects are finite-domain assignments. Consequently, assigning *any
//! other value* to the same variable is a causal threat, even when there is no
//! explicit delete fact. The refinement semantics stay representation-specific,
//! while plan ranking, flaw-order configuration, search algorithms, limits, and
//! statistics follow the main search implementation.
//!
//! Threats from conditional assignments also admit *confrontation*, UCPOP's
//! resolver for conditional effects, which VHPOP folds into separation: the
//! effect only clobbers the link when all of its conditions hold, so committing
//! the threatening step to another value of a condition variable disarms it
//! without ordering the step out of the protected interval. Over a finite
//! domain the negated antecedent `y != c` is the disjunction over the remaining
//! values of `y`, so each alternative becomes a refinement of its own rather
//! than a disjunctive open condition. By the same reading, an effect whose
//! antecedent is already contradicted at its step can never fire and is not
//! reported as a threat.

use std::borrow::Cow;
use std::cmp::Ordering as CmpOrdering;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::rc::Rc;
use std::time::Instant;

use thiserror::Error;

use crate::external::FdError;
use crate::fdr::{Fact, ParseError, Task};
use crate::heuristics::{HVal, Heuristic, OrderType, SelectionCriterion};
use crate::lmcut::{BuildError as LmCutBuildError, FdrLmCut};
use crate::orderings::{BinaryOrderings, Ordering, StepTime};
use crate::params::{ActionCost, Parameters, SearchAlgorithm};
use crate::plan::{GOAL_ID, INIT_ID};
use crate::search::{SearchContext, SearchProgress};

/// A committed real step. Init and goal are represented by [`INIT_ID`] and
/// [`GOAL_ID`] and are not stored in this vector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Step {
    pub id: usize,
    pub operator: usize,
}

/// A finite-domain causal link `producer --(variable=value)--> consumer`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CausalLink {
    pub producer: usize,
    pub consumer: usize,
    pub condition: Fact,
    /// The producer's effect used to establish the link. `None` denotes the
    /// synthetic initial-state producer.
    pub effect: Option<usize>,
}

/// A finite-domain precondition not yet supported by a causal link.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenCondition {
    pub consumer: usize,
    pub condition: Fact,
}

/// A threat resolution posted as a constraint instead of split into two plans.
///
/// Nguyen & Kambhampati, IJCAI-01, §4.1:
///
/// > A problem with this premature splitting is that a single failing plan gets
/// > unnecessarily multiplied into many descendant plans poisoning the search
/// > queue significantly. A much better idea is to resolve the unsafe link by
/// > posting a disjunctive ordering constraint that captures both the promotion
/// > and demotion possibilities, and incrementally simplify these constraints by
/// > propagation techniques.
///
/// The disjunction is `(promote.0 ≺ promote.1) ∨ (demote.0 ≺ demote.1)`. It is
/// discharged by [`PartialPlan::propagate_disjunctions`] as soon as either
/// disjunct becomes entailed (satisfied) or impossible (the other is enforced),
/// and split into the search space only when nothing else is left to refine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrderingDisjunction {
    /// The threat this discharges, keyed as `(link, step, effect)`.
    pub threat: (usize, usize, usize),
    /// Promotion: the threatening step follows the link's consumer.
    pub promote: (usize, usize),
    /// Demotion: the threatening step precedes the link's producer.
    pub demote: (usize, usize),
}

/// A threat whose source is the step's *precondition* rather than one of its
/// effects: the step requires a fact mutex with the protected one, so it cannot
/// execute inside the interval at all. Only e-deletion produces these.
pub const NO_EFFECT: usize = usize::MAX;

/// An assignment that can occur inside a causal link's protected interval.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Threat {
    pub step: usize,
    /// Index of the clobbering effect, or [`NO_EFFECT`] for a precondition-based
    /// e-deletion threat.
    pub effect: usize,
    pub link: usize,
}

/// Copy-on-write append that allocates once instead of twice.
///
/// `Rc::make_mut(&mut v).push(x)` on a shared vector clones it at *exact*
/// capacity and then reallocates on the push, because the clone leaves
/// `len == capacity`. Every child plan appends to `steps`, `links` and
/// `open_conditions`, so that doubling showed up as the largest single source
/// of allocation traffic in the search. Building the replacement with room for
/// the new element costs one allocation and one copy.
#[inline]
fn push_cow<T: Clone>(slot: &mut Rc<Vec<T>>, value: T) {
    match Rc::get_mut(slot) {
        // Uniquely owned (an earlier refinement in this same child already
        // forced the copy): append in place.
        Some(vec) => vec.push(value),
        None => {
            let current = &**slot;
            let mut next = Vec::with_capacity(current.len() + 1);
            next.extend_from_slice(current);
            next.push(value);
            *slot = Rc::new(next);
        }
    }
}

/// Copy-on-write `swap_remove` that leaves room for `extra` later appends.
///
/// Every refinement removes the open condition it resolved and then pushes the
/// new step's preconditions. Cloning through `Rc::make_mut` leaves
/// `len == capacity`, so those pushes reallocate the vector that was just
/// cloned; sizing the clone for both at once costs a single allocation.
#[inline]
fn swap_remove_cow<T: Clone>(slot: &mut Rc<Vec<T>>, index: usize, extra: usize) {
    match Rc::get_mut(slot) {
        Some(vec) => {
            vec.swap_remove(index);
            vec.reserve(extra);
        }
        None => {
            let current = &**slot;
            let mut next = Vec::with_capacity(current.len() + extra);
            next.extend_from_slice(current);
            next.swap_remove(index);
            *slot = Rc::new(next);
        }
    }
}

/// Copy-on-write `extend` that allocates once, and not at all when there is
/// nothing to add -- most refinements introduce no new threat, and cloning the
/// threat list to append zero entries is pure waste.
#[inline]
fn extend_cow<T: Clone>(slot: &mut Rc<Vec<T>>, items: Vec<T>) {
    if items.is_empty() {
        return;
    }
    match Rc::get_mut(slot) {
        Some(vec) => vec.extend(items),
        None => {
            let current = &**slot;
            let mut next = Vec::with_capacity(current.len() + items.len());
            next.extend_from_slice(current);
            next.extend(items);
            *slot = Rc::new(next);
        }
    }
}

/// One immutable-by-convention finite-domain POCL search node.
#[derive(Debug, Clone)]
pub struct PartialPlan {
    pub steps: Rc<Vec<Step>>,
    pub links: Rc<Vec<CausalLink>>,
    pub open_conditions: Rc<Vec<OpenCondition>>,
    pub orderings: Rc<BinaryOrderings>,
    threats: Rc<Vec<Threat>>,
    /// Conditional effects `(step, effect)` that a confrontation refinement has
    /// committed never to fire. Sorted, so membership is a binary search.
    suppressed: Rc<Vec<(usize, usize)>>,
    /// Accumulated cost of committed operators.
    pub cost: usize,
    /// Threats resolved by posting a disjunctive ordering rather than by
    /// branching, still awaiting propagation or a split. Empty unless
    /// `-p disjunctive` is on.
    disjunctions: Rc<Vec<OrderingDisjunction>>,
    /// Mutex table enabling e-deletion, shared by every plan in the search.
    /// `None` leaves threat detection at the classical "assigns the protected
    /// variable another value" test. See [`crate::cutset::FactMutexes`] and
    /// `Planner::with_pruning`.
    edelete: Option<Rc<crate::cutset::FactMutexes>>,
    next_step_id: usize,
    id: usize,
}

impl PartialPlan {
    pub fn initial(task: &Task) -> Self {
        PartialPlan {
            steps: Rc::new(Vec::new()),
            links: Rc::new(Vec::new()),
            open_conditions: Rc::new(
                task.goals
                    .iter()
                    .copied()
                    .map(|condition| OpenCondition {
                        consumer: GOAL_ID,
                        condition,
                    })
                    .collect(),
            ),
            orderings: Rc::new(BinaryOrderings::new()),
            threats: Rc::new(Vec::new()),
            suppressed: Rc::new(Vec::new()),
            cost: 0,
            disjunctions: Rc::new(Vec::new()),
            edelete: None,
            next_step_id: 1,
            id: 0,
        }
    }

    pub fn complete(&self, _task: &Task) -> bool {
        self.open_conditions.is_empty() && self.threats.is_empty()
    }

    /// Cached threats, cloned for compatibility with callers that previously
    /// requested a freshly discovered threat vector.
    pub fn threats(&self, _task: &Task) -> Vec<Threat> {
        (*self.threats).clone()
    }

    #[cfg(test)]
    fn rediscover_threats(&self, task: &Task) -> Vec<Threat> {
        let mut threats = Vec::new();
        for (link_index, link) in self.links.iter().enumerate() {
            for step in self.steps.iter() {
                if step.id == link.producer
                    || step.id == link.consumer
                    || !self.can_be_inside(step.id, link)
                {
                    continue;
                }
                for (effect_index, effect) in
                    task.operators[step.operator].effects.iter().enumerate()
                {
                    if effect_e_deletes(effect, link.condition, self.edelete.as_deref())
                        && !self.effect_cannot_fire(task, step, effect_index)
                    {
                        threats.push(Threat {
                            step: step.id,
                            effect: effect_index,
                            link: link_index,
                        });
                    }
                }
                if let Some(mutexes) = self.edelete.as_deref() {
                    if precondition_e_deletes(
                        &task.operators[step.operator],
                        link.condition,
                        mutexes,
                    ) {
                        threats.push(Threat {
                            step: step.id,
                            effect: NO_EFFECT,
                            link: link_index,
                        });
                    }
                }
            }
        }
        threats
    }

    /// The committed step with the given id. Steps are only ever appended, so
    /// `id` doubles as a 1-based index into [`PartialPlan::steps`].
    fn step(&self, id: usize) -> Option<&Step> {
        id.checked_sub(1)
            .and_then(|index| self.steps.get(index))
            .filter(|step| step.id == id)
    }

    /// Whether `step` is already committed to a value of `fact`'s variable
    /// other than `fact.value`. Open conditions count as commitments: they are
    /// only ever discharged by a causal link carrying the very same equality,
    /// and a finite-domain variable holds one value at a time.
    fn step_excludes(&self, step: usize, fact: Fact) -> bool {
        let conflicts =
            |condition: Fact| condition.variable == fact.variable && condition.value != fact.value;
        self.open_conditions
            .iter()
            .any(|open| open.consumer == step && conflicts(open.condition))
            || self
                .links
                .iter()
                .any(|link| link.consumer == step && conflicts(link.condition))
    }

    /// Whether `effect` of `step` can never fire, and therefore neither
    /// threatens a link nor establishes one: a confrontation refinement
    /// suppressed it, or the step is already committed against one of the
    /// effect's conditions.
    fn effect_cannot_fire(&self, task: &Task, step: &Step, effect: usize) -> bool {
        if self.effect_suppressed(step.id, effect) {
            return true;
        }
        task.operators[step.operator].effects[effect]
            .conditions
            .iter()
            .any(|&condition| self.step_excludes(step.id, condition))
    }

    fn effect_suppressed(&self, step: usize, effect: usize) -> bool {
        !self.suppressed.is_empty() && self.suppressed.binary_search(&(step, effect)).is_ok()
    }

    fn suppress_effect(&mut self, step: usize, effect: usize) {
        let key = (step, effect);
        let suppressed = Rc::make_mut(&mut self.suppressed);
        if let Err(index) = suppressed.binary_search(&key) {
            suppressed.insert(index, key);
        }
    }

    /// Whether a threat already has a disjunction standing for it, so flaw
    /// selection must leave it alone.
    fn threat_covered(&self, threat: &Threat) -> bool {
        !self.disjunctions.is_empty()
            && self
                .disjunctions
                .iter()
                .any(|disjunction| disjunction.threat == threat_key(threat))
    }

    pub(crate) fn pending_disjunctions(&self) -> usize {
        self.disjunctions.len()
    }

    /// Propagates the pending disjunctions to a fixpoint.
    ///
    /// The three rules are RePOP's, minus the two that `BinaryOrderings`
    /// already enforces for itself (transitivity, and rejecting a cycle):
    ///
    /// * a disjunct that is **entailed** satisfies the disjunction — drop it;
    /// * a disjunct that is **impossible** leaves the other one forced — add it
    ///   (unit propagation) and drop the disjunction;
    /// * **both** impossible means the plan has no completion.
    ///
    /// Returns `false` when the plan is inconsistent and must be discarded.
    fn propagate_disjunctions(&mut self) -> bool {
        if self.disjunctions.is_empty() {
            return true;
        }
        loop {
            let mut forced: Option<(usize, usize)> = None;
            let mut discharged: Option<usize> = None;
            for (index, disjunction) in self.disjunctions.iter().enumerate() {
                let promote = self.ordering_status(disjunction.promote);
                let demote = self.ordering_status(disjunction.demote);
                match (promote, demote) {
                    (OrderingStatus::Entailed, _) | (_, OrderingStatus::Entailed) => {
                        discharged = Some(index);
                    }
                    (OrderingStatus::Impossible, OrderingStatus::Impossible) => return false,
                    (OrderingStatus::Impossible, _) => {
                        forced = Some(disjunction.demote);
                        discharged = Some(index);
                    }
                    (_, OrderingStatus::Impossible) => {
                        forced = Some(disjunction.promote);
                        discharged = Some(index);
                    }
                    _ => continue,
                }
                break;
            }
            let Some(index) = discharged else {
                return true;
            };
            let disjunctions = Rc::make_mut(&mut self.disjunctions);
            disjunctions.remove(index);
            if let Some((before, after)) = forced {
                let Some(orderings) = self.orderings.refine(Ordering::new(
                    before,
                    StepTime::AtEnd,
                    after,
                    StepTime::AtEnd,
                )) else {
                    return false;
                };
                self.orderings = orderings;
            }
        }
    }

    /// Where an ordering stands against the constraints already in the plan.
    fn ordering_status(&self, (before, after): (usize, usize)) -> OrderingStatus {
        if before == after || before == GOAL_ID || after == INIT_ID {
            return OrderingStatus::Impossible;
        }
        if is_ordered_before(&self.orderings, before, after) {
            return OrderingStatus::Entailed;
        }
        if is_ordered_before(&self.orderings, after, before) {
            return OrderingStatus::Impossible;
        }
        OrderingStatus::Undetermined
    }

    /// Drops disjunctions standing for threats that are no longer active. The
    /// constraint was only ever posted to disarm that threat, so keeping it
    /// would over-constrain the plan.
    fn retain_live_disjunctions(&mut self, task: &Task) {
        if self.disjunctions.is_empty() {
            return;
        }
        let live: Vec<OrderingDisjunction> = self
            .disjunctions
            .iter()
            .filter(|disjunction| {
                self.threats
                    .iter()
                    .any(|threat| threat_key(threat) == disjunction.threat)
                    && self.threat_active(
                        task,
                        &Threat {
                            link: disjunction.threat.0,
                            step: disjunction.threat.1,
                            effect: disjunction.threat.2,
                        },
                    )
            })
            .cloned()
            .collect();
        if live.len() != self.disjunctions.len() {
            self.disjunctions = Rc::new(live);
        }
    }

    fn can_be_inside(&self, step_id: usize, link: &CausalLink) -> bool {
        self.orderings
            .possibly_before(link.producer, StepTime::AtEnd, step_id, StepTime::AtEnd)
            && self.orderings.possibly_before(
                step_id,
                StepTime::AtEnd,
                link.consumer,
                StepTime::AtStart,
            )
    }

    fn push_open(&mut self, open: OpenCondition) {
        if !self.open_conditions.contains(&open) {
            push_cow(&mut self.open_conditions, open);
        }
    }

    fn threat_active(&self, task: &Task, threat: &Threat) -> bool {
        let Some(link) = self.links.get(threat.link) else {
            return false;
        };
        if threat.step == link.producer || threat.step == link.consumer {
            return false;
        }
        let Some(step) = self.step(threat.step) else {
            return false;
        };
        if threat.effect == NO_EFFECT {
            // A precondition-based e-deletion threat: it holds for as long as
            // the step can sit inside the interval, since a step's own
            // preconditions are not conditional on anything.
            let Some(mutexes) = self.edelete.as_deref() else {
                return false;
            };
            return self.can_be_inside(step.id, link)
                && precondition_e_deletes(&task.operators[step.operator], link.condition, mutexes);
        }
        let Some(effect) = task.operators[step.operator].effects.get(threat.effect) else {
            return false;
        };
        self.can_be_inside(step.id, link)
            && effect_e_deletes(effect, link.condition, self.edelete.as_deref())
            && !self.effect_cannot_fire(task, step, threat.effect)
    }

    /// Re-establishes the plan's cached invariants after a refinement: drop
    /// threats that are no longer live, drop the disjunctions standing for them,
    /// and propagate the rest. Returns `false` when propagation proves the plan
    /// inconsistent, in which case the caller must discard it.
    fn settle(&mut self, task: &Task) -> bool {
        self.retain_active_threats(task);
        if self.disjunctions.is_empty() {
            return true;
        }
        self.retain_live_disjunctions(task);
        if !self.propagate_disjunctions() {
            return false;
        }
        // Propagation can add orderings, which can in turn retire threats.
        self.retain_active_threats(task);
        self.retain_live_disjunctions(task);
        true
    }

    fn retain_active_threats(&mut self, task: &Task) {
        if self
            .threats
            .iter()
            .all(|threat| self.threat_active(task, threat))
        {
            return;
        }
        let active = self
            .threats
            .iter()
            .filter(|threat| self.threat_active(task, threat))
            .cloned()
            .collect();
        self.threats = Rc::new(active);
    }

    fn add_link_threats(&mut self, task: &Task, link_index: usize) {
        debug_assert_eq!(link_index + 1, self.links.len());
        let link = &self.links[link_index];
        let mut additions = Vec::new();
        for step in self.steps.iter() {
            if step.id == link.producer
                || step.id == link.consumer
                || !self.can_be_inside(step.id, link)
            {
                continue;
            }
            for (effect_index, effect) in task.operators[step.operator].effects.iter().enumerate() {
                if effect_e_deletes(effect, link.condition, self.edelete.as_deref())
                    && !self.effect_cannot_fire(task, step, effect_index)
                {
                    additions.push(Threat {
                        step: step.id,
                        effect: effect_index,
                        link: link_index,
                    });
                }
            }
            if let Some(mutexes) = self.edelete.as_deref() {
                if precondition_e_deletes(&task.operators[step.operator], link.condition, mutexes) {
                    additions.push(Threat {
                        step: step.id,
                        effect: NO_EFFECT,
                        link: link_index,
                    });
                }
            }
        }
        debug_assert!(self
            .threats
            .last()
            .zip(additions.first())
            .is_none_or(|(existing, addition)| threat_key(existing) < threat_key(addition)));
        extend_cow(&mut self.threats, additions);
    }

    fn add_step_threats(&mut self, task: &Task, step_id: usize) {
        let step = &self.steps[step_id - 1];
        let mut additions = Vec::new();
        for (link_index, link) in self.links.iter().enumerate() {
            if step.id == link.producer
                || step.id == link.consumer
                || !self.can_be_inside(step.id, link)
            {
                continue;
            }
            for (effect_index, effect) in task.operators[step.operator].effects.iter().enumerate() {
                if effect_e_deletes(effect, link.condition, self.edelete.as_deref())
                    && !self.effect_cannot_fire(task, step, effect_index)
                {
                    additions.push(Threat {
                        step: step.id,
                        effect: effect_index,
                        link: link_index,
                    });
                }
            }
            if let Some(mutexes) = self.edelete.as_deref() {
                if precondition_e_deletes(&task.operators[step.operator], link.condition, mutexes) {
                    additions.push(Threat {
                        step: step.id,
                        effect: NO_EFFECT,
                        link: link_index,
                    });
                }
            }
        }
        if additions.is_empty() {
            return;
        }

        // The brute-force discovery order is link, then step, then effect. A
        // newly added step can threaten old links, so merge those entries into
        // the cached order instead of simply appending them. Flaw-selection
        // tie-breaking therefore remains identical to full rediscovery.
        let existing = &self.threats;
        let mut merged = Vec::with_capacity(existing.len() + additions.len());
        let mut existing_index = 0;
        for addition in additions {
            while existing_index < existing.len()
                && threat_key(&existing[existing_index]) < threat_key(&addition)
            {
                merged.push(existing[existing_index].clone());
                existing_index += 1;
            }
            merged.push(addition);
        }
        merged.extend(existing[existing_index..].iter().cloned());
        self.threats = Rc::new(merged);
    }

    fn num_steps(&self) -> usize {
        self.steps.len()
    }

    pub fn cost(&self) -> usize {
        self.cost
    }

    fn num_open_conditions(&self) -> usize {
        self.open_conditions.len()
    }
}

/// A solved partial plan plus one valid topological linearization.
#[derive(Debug, Clone)]
pub struct Solution {
    pub plan: PartialPlan,
    pub operators: Vec<usize>,
}

impl Solution {
    pub fn format(&self, task: &Task) -> String {
        self.operators
            .iter()
            .enumerate()
            .map(|(time, &operator)| format!("{}:({})", time + 1, task.operators[operator].name))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SearchStats {
    pub nodes_generated: usize,
    pub nodes_visited: usize,
    pub h_evals: usize,
    pub h_eval_ms: u128,
    pub pruned: usize,
    pub max_steps: usize,
    pub max_open_conditions: usize,
    pub max_threats: usize,
    /// Peak number of ordering disjunctions held on a single plan. Zero unless
    /// `-p disjunctive` is on; a nonzero value is the evidence that threat
    /// resolution is being deferred rather than branched on.
    pub max_disjunctions: usize,
    pub max_queued: usize,
    h_eval_nanos: u128,
}

#[derive(Debug, Clone)]
pub enum Outcome {
    Solved(Solution),
    LimitReached,
    NoSolution,
}

/// Translates the original ground problem through Fast Downward and retains its
/// complete finite-domain representation.
pub fn translate(ctx: &SearchContext<'_>) -> Result<Task, Error> {
    let (domain_pddl, problem_pddl) = crate::pddl_emit::emit_original(ctx.domain, ctx.problem);
    let sas = crate::external::run_fd_translate(&domain_pddl, &problem_pddl)?;
    Ok(Task::parse(&sas)?)
}

/// Runs finite-domain POCL search with the default ranking and flaw order and a
/// single generated-node limit. This compatibility wrapper is convenient for
/// library callers that do not need the full [`Parameters`] surface.
pub fn solve(task: &Task, node_limit: usize) -> (Outcome, SearchStats) {
    let params = Parameters {
        // ADDR is the literal planner's default, but its reuse treatment forms
        // poor plateaus on FDR nodes. Plain ADD is the robust FDR default.
        heuristic: Heuristic::parse("ADD").expect("ADD is a valid heuristic"),
        search_limits: vec![node_limit],
        ..Parameters::default()
    };
    solve_with_params(task, &params).expect("default FDR search parameters are supported")
}

/// Runs finite-domain POCL search using the same algorithms, heuristic syntax,
/// flaw-selection orders, weights, limits, and statistics as the main planner.
pub fn solve_with_params(
    task: &Task,
    params: &Parameters,
) -> Result<(Outcome, SearchStats), Error> {
    solve_impl(task, params, None)
}

/// Like [`solve_with_params`], while also reporting a representation-neutral
/// snapshot after each node expansion.
pub fn solve_with_params_and_progress(
    task: &Task,
    params: &Parameters,
    progress: &mut dyn FnMut(SearchProgress),
) -> Result<(Outcome, SearchStats), Error> {
    solve_impl(task, params, Some(progress))
}

fn solve_impl(
    task: &Task,
    params: &Parameters,
    progress: Option<&mut dyn FnMut(SearchProgress)>,
) -> Result<(Outcome, SearchStats), Error> {
    let planner = Planner::with_action_cost(task, params.action_cost).with_pruning(params.prune);
    planner.validate_params(params)?;
    Ok(planner.solve(params, progress))
}

#[derive(Debug, Clone, Copy)]
struct Achiever {
    operator: usize,
    effect: usize,
}

struct Planner<'a> {
    task: &'a Task,
    achievers: HashMap<Fact, Vec<Achiever>>,
    variable_has_effect: Vec<bool>,
    operator_preconditions: Vec<Vec<Fact>>,
    effect_requirements: Vec<Vec<Vec<Fact>>>,
    derived_supports: HashMap<Fact, Vec<Vec<Fact>>>,
    base_relaxed: RelaxedValues,
    lmcut: Result<FdrLmCut, LmCutBuildError>,
    action_cost: ActionCost,
    /// Shared mutex table for e-deletion, installed on the initial plan.
    edelete: Option<Rc<crate::cutset::FactMutexes>>,
    /// Whether threats are resolved by posting a disjunction instead of by
    /// splitting the plan.
    disjunctive: bool,
    /// The task's operator graph over facts, for the recursion rule. Built only
    /// when `-p recursion` asks for it.
    fact_graph: Option<crate::fdr_pruning::FactGraph>,
    /// Whether non-minimality pruning is on.
    minimality: bool,
}

impl<'a> Planner<'a> {
    #[cfg(test)]
    fn new(task: &'a Task) -> Self {
        Self::with_action_cost(task, ActionCost::Task)
    }

    fn with_action_cost(task: &'a Task, action_cost: ActionCost) -> Self {
        let mut achievers: HashMap<Fact, Vec<Achiever>> = HashMap::new();
        let mut variable_has_effect = vec![false; task.variables.len()];
        let mut derived_supports = HashMap::new();
        for (variable, values) in task.variables.iter().enumerate() {
            if !task.is_derived_variable(variable) {
                continue;
            }
            variable_has_effect[variable] = true;
            for value in 0..values.values.len() {
                let fact = Fact::new(variable, value);
                derived_supports.insert(
                    fact,
                    task.derived_supports(fact)
                        .expect("derived variable has support expansion"),
                );
            }
        }
        let operator_preconditions = task
            .operators
            .iter()
            .map(|operator| operator.preconditions())
            .collect::<Vec<_>>();
        let effect_requirements = task
            .operators
            .iter()
            .zip(&operator_preconditions)
            .map(|(operator, preconditions)| {
                operator
                    .effects
                    .iter()
                    .map(|effect| {
                        let mut required = preconditions.clone();
                        for &condition in &effect.conditions {
                            if !required.contains(&condition) {
                                required.push(condition);
                            }
                        }
                        required
                    })
                    .collect()
            })
            .collect::<Vec<_>>();
        let base_relaxed =
            build_base_relaxed_values(task, &effect_requirements, &derived_supports, action_cost);
        let lmcut = FdrLmCut::new(task, action_cost);
        for (operator_index, operator) in task.operators.iter().enumerate() {
            for (effect_index, effect) in operator.effects.iter().enumerate() {
                variable_has_effect[effect.variable] = true;
                achievers
                    .entry(effect.assignment())
                    .or_default()
                    .push(Achiever {
                        operator: operator_index,
                        effect: effect_index,
                    });
            }
        }
        Planner {
            task,
            achievers,
            variable_has_effect,
            operator_preconditions,
            effect_requirements,
            derived_supports,
            base_relaxed,
            lmcut,
            action_cost,
            edelete: None,
            disjunctive: false,
            fact_graph: None,
            minimality: false,
        }
    }

    fn validate_params(&self, params: &Parameters) -> Result<(), Error> {
        if params.flaw_orders.is_empty() {
            return Err(Error::Unsupported(
                "at least one flaw-selection order is required".to_string(),
            ));
        }
        if params.search_limits.len() < params.flaw_orders.len() {
            return Err(Error::Unsupported(
                "one search limit is required per flaw-selection order".to_string(),
            ));
        }
        if matches!(
            params.action_cost,
            ActionCost::Duration | ActionCost::Relative
        ) {
            return Err(Error::Unsupported(
                "finite-domain POCL supports PDDL task costs or explicit unit costs".to_string(),
            ));
        }
        for term in params.heuristic.terms() {
            match term {
                HVal::Lifo
                | HVal::Fifo
                | HVal::Oc
                | HVal::Uc
                | HVal::Buc
                | HVal::SPlusOc
                | HVal::Ucpop
                | HVal::Add
                | HVal::AddCost
                | HVal::AddWork
                | HVal::Addr
                | HVal::AddrCost
                | HVal::AddrWork
                | HVal::Relax
                | HVal::RelaxR => {}
                HVal::LmCut | HVal::LmCutR => {
                    if let Err(error) = &self.lmcut {
                        return Err(Error::Unsupported(error.to_string()));
                    }
                }
                HVal::Landmarks
                | HVal::SampleFf(_)
                | HVal::Lplan(_)
                | HVal::Lpsas(_)
                | HVal::Compile(_) => {
                    return Err(Error::Unsupported(
                        "LM, SAMPLE_FF, LPLAN, and COMPILE heuristics operate on the literal plan representation"
                            .to_string(),
                    ));
                }
            }
        }
        Ok(())
    }

    /// Installs the mutex table e-deletion needs. Kept separate from
    /// construction so the cost is paid only when `-p edelete` asks for it.
    fn with_pruning(mut self, prune: crate::pruning::PruneOptions) -> Self {
        if prune.edelete {
            self.edelete = Some(Rc::new(crate::cutset::FactMutexes::new(self.task)));
        }
        self.disjunctive = prune.disjunctive;
        if prune.recursion {
            self.fact_graph = Some(crate::fdr_pruning::FactGraph::build(self.task));
        }
        self.minimality = prune.minimality;
        self
    }

    /// Whether an opt-in structural rule discards this refinement.
    ///
    /// The rules keep the staging their lifted counterparts use: each opens with
    /// an allocation-free applicability test, and only a plan that passes one
    /// pays for the graph searches behind it.
    fn structurally_pruned(&self, plan: &PartialPlan) -> bool {
        if self.minimality
            && crate::fdr_pruning::minimality_may_apply(plan)
            && crate::fdr_pruning::minimality_prunable(plan)
        {
            return true;
        }
        if let Some(graph) = &self.fact_graph {
            if crate::fdr_pruning::recursion_may_apply(plan, graph)
                && crate::fdr_pruning::recursion_prunable(plan, self.task, graph)
            {
                return true;
            }
        }
        false
    }

    fn solve(
        &self,
        params: &Parameters,
        mut progress: Option<&mut dyn FnMut(SearchProgress)>,
    ) -> (Outcome, SearchStats) {
        let search_started = Instant::now();
        let n_orders = params.flaw_orders.len();
        let inf = f32::INFINITY;
        let alg = params.search_algorithm;
        let is_ida = alg == SearchAlgorithm::Ida;
        let is_bfs = alg == SearchAlgorithm::Bfs;
        let is_gbfs = matches!(
            alg,
            SearchAlgorithm::Gbfs | SearchAlgorithm::LazyGbfs | SearchAlgorithm::LazyGbfsDual
        );
        let is_lazy = matches!(
            alg,
            SearchAlgorithm::LazyGbfs | SearchAlgorithm::LazyGbfsDual
        );
        let is_dual = alg == SearchAlgorithm::LazyGbfsDual;
        let is_alt = alg == SearchAlgorithm::Alt;

        // Cutset mutex pruning (`-p cutset`): Fast Downward's SAS+ variables and
        // declared mutex groups supply the mutexes this rule needs, so the
        // finite-domain representation gets it for free. See `crate::cutset`.
        let cutset_mutexes = params
            .prune
            .cutset
            .then(|| crate::cutset::FactMutexes::new(self.task));
        if let Some(mutexes) = &cutset_mutexes {
            // The goal step's pre-cutset is the task goals, and no link can span
            // the goal, so it is plan-independent: check it once.
            if crate::cutset::goals_inconsistent(self.task, mutexes) {
                return (Outcome::NoSolution, SearchStats::default());
            }
        }

        let mut initial_plan = PartialPlan::initial(self.task);
        initial_plan.edelete = self.edelete.clone();
        let initial = Rc::new(initial_plan);
        let mut queues: Vec<BinaryHeap<QueuedPlan>> =
            (0..n_orders).map(|_| BinaryHeap::new()).collect();
        let mut secondary_queues: Vec<BinaryHeap<QueuedPlan>> = if is_dual || is_alt {
            (0..n_orders).map(|_| BinaryHeap::new()).collect()
        } else {
            Vec::new()
        };
        let mut expanded_ids = HashSet::new();
        let mut generated_per_order = vec![0usize; n_orders];
        let mut stats = SearchStats::default();
        let mut current_order = 0usize;
        let mut orders_left = n_orders;
        let mut next_switch = 1_000usize;
        let mut limit_reached = false;
        let mut best_h = inf;
        let mut boost_budget = 0usize;
        let mut expand_count = 0usize;
        let mut current_rank0 = 0.0f32;

        generated_per_order[0] = 1;
        stats.nodes_generated = 1;
        let mut current_plan = Some(initial.clone());
        let mut f_limit = if is_ida {
            self.rank_both(&initial, params, &mut stats).0[0]
        } else {
            inf
        };

        loop {
            let mut next_f_limit = inf;
            while let Some(plan) = current_plan.clone() {
                if plan.complete(self.task) {
                    // A pending disjunction always keeps its threat in the
                    // threat list, so a complete plan can never carry one.
                    debug_assert_eq!(
                        plan.pending_disjunctions(),
                        0,
                        "a complete plan still holds an undischarged ordering disjunction"
                    );
                    if let Some(operators) = linearize_and_validate(&plan, self.task) {
                        return (
                            Outcome::Solved(Solution {
                                plan: (*plan).clone(),
                                operators,
                            }),
                            stats,
                        );
                    }
                    (current_plan, current_rank0) = self.pop_next(
                        &mut queues[current_order],
                        if is_dual || is_alt {
                            Some(&mut secondary_queues[current_order])
                        } else {
                            None
                        },
                        &expanded_ids,
                        params,
                        is_lazy,
                        is_gbfs,
                        is_dual,
                        is_alt,
                        &mut boost_budget,
                        &mut expand_count,
                        &mut stats,
                    );
                    continue;
                }

                stats.nodes_visited += 1;
                stats.max_steps = stats.max_steps.max(plan.steps.len());
                stats.max_open_conditions =
                    stats.max_open_conditions.max(plan.open_conditions.len());
                stats.max_threats = stats.max_threats.max(plan.threats.len());
                stats.max_disjunctions = stats.max_disjunctions.max(plan.pending_disjunctions());
                if is_dual || is_alt {
                    expanded_ids.insert(plan.id);
                }
                if is_dual {
                    if current_rank0 < best_h {
                        best_h = current_rank0;
                        boost_budget = boost_budget.saturating_add(10);
                    }
                    boost_budget = boost_budget.saturating_sub(1);
                }

                let children = self.refinements(&plan, &params.flaw_orders[current_order]);
                let order_index = current_order;
                for mut child in children {
                    if let Some(mutexes) = &cutset_mutexes {
                        if crate::cutset::has_inconsistent_cutset(&child, self.task, mutexes) {
                            stats.pruned += 1;
                            continue;
                        }
                    }
                    if self.structurally_pruned(&child) {
                        stats.pruned += 1;
                        continue;
                    }
                    child.id = stats.nodes_generated;
                    let child = Rc::new(child);
                    let mut alt_gbfs_rank = None;
                    let (rank, lazy_push) = if is_bfs {
                        (vec![child.num_steps() as f32, child.id as f32], false)
                    } else if is_lazy {
                        if params.heuristic.needs_planning_graph()
                            && !self.open_estimate(&child, false).cost.is_finite()
                        {
                            stats.pruned += 1;
                            continue;
                        }
                        (
                            vec![
                                current_rank0,
                                child.num_open_conditions() as f32,
                                -(child.id as f32),
                            ],
                            true,
                        )
                    } else if is_gbfs {
                        (self.rank_both(&child, params, &mut stats).1, false)
                    } else if is_alt {
                        let (a_rank, g_rank) = self.rank_both(&child, params, &mut stats);
                        alt_gbfs_rank = Some(g_rank);
                        (a_rank, false)
                    } else {
                        (self.rank_both(&child, params, &mut stats).0, false)
                    };

                    let primary = rank[0];
                    if primary.is_finite()
                        && generated_per_order[order_index] < params.search_limits[order_index]
                    {
                        if is_ida && primary > f_limit {
                            next_f_limit = next_f_limit.min(primary);
                            continue;
                        }
                        if is_dual {
                            secondary_queues[order_index].push(QueuedPlan {
                                plan: child.clone(),
                                rank: vec![child.id as f32],
                                is_lazy: lazy_push,
                            });
                        } else if is_alt {
                            secondary_queues[order_index].push(QueuedPlan {
                                plan: child.clone(),
                                rank: alt_gbfs_rank
                                    .take()
                                    .expect("ALT child has both rank vectors"),
                                is_lazy: false,
                            });
                        }
                        queues[order_index].push(QueuedPlan {
                            plan: child,
                            rank,
                            is_lazy: lazy_push,
                        });
                        generated_per_order[order_index] += 1;
                        stats.nodes_generated += 1;
                    }
                }

                let queued = queues.iter().map(BinaryHeap::len).sum();
                stats.max_queued = stats.max_queued.max(queued);
                if let Some(report) = progress.as_deref_mut() {
                    report(SearchProgress {
                        elapsed: search_started.elapsed(),
                        nodes_generated: stats.nodes_generated,
                        nodes_visited: stats.nodes_visited,
                        queued,
                        h_evals: stats.h_evals,
                        h_eval_ms: stats.h_eval_ms,
                        pruned: stats.pruned,
                        current_steps: plan.steps.len(),
                        current_open_conditions: plan.open_conditions.len(),
                        current_threats: plan.threats.len(),
                        flaw_order: current_order,
                    });
                }

                let order_limit =
                    generated_per_order[current_order] >= params.search_limits[current_order];
                if order_limit || generated_per_order[current_order] >= next_switch {
                    if order_limit {
                        limit_reached = true;
                        orders_left = orders_left.saturating_sub(1);
                        queues[current_order].clear();
                        if is_dual || is_alt {
                            secondary_queues[current_order].clear();
                        }
                    }
                    if orders_left > 0 {
                        loop {
                            current_order += 1;
                            if current_order >= n_orders {
                                current_order = 0;
                                next_switch = next_switch.saturating_mul(2);
                            }
                            if generated_per_order[current_order]
                                < params.search_limits[current_order]
                            {
                                break;
                            }
                        }
                    }
                }

                if orders_left == 0 {
                    break;
                }
                if generated_per_order[current_order] == 0 {
                    current_plan = Some(initial.clone());
                    current_rank0 = 0.0;
                    generated_per_order[current_order] = 1;
                    stats.nodes_generated += 1;
                } else {
                    (current_plan, current_rank0) = self.pop_next(
                        &mut queues[current_order],
                        if is_dual || is_alt {
                            Some(&mut secondary_queues[current_order])
                        } else {
                            None
                        },
                        &expanded_ids,
                        params,
                        is_lazy,
                        is_gbfs,
                        is_dual,
                        is_alt,
                        &mut boost_budget,
                        &mut expand_count,
                        &mut stats,
                    );
                }
            }

            if orders_left == 0 {
                break;
            }
            f_limit = next_f_limit;
            if is_ida && f_limit.is_finite() {
                current_plan = Some(initial.clone());
                current_rank0 = 0.0;
            } else {
                break;
            }
        }

        if limit_reached {
            (Outcome::LimitReached, stats)
        } else {
            (Outcome::NoSolution, stats)
        }
    }

    fn resolve_open(&self, plan: &PartialPlan, open_index: usize) -> Vec<PartialPlan> {
        let open = plan.open_conditions[open_index].clone();
        if let Some(supports) = self.derived_supports.get(&open.condition) {
            return supports
                .iter()
                .map(|support| {
                    let mut child = plan.clone();
                    swap_remove_cow(&mut child.open_conditions, open_index, support.len());
                    for &condition in support {
                        child.push_open(OpenCondition {
                            consumer: open.consumer,
                            condition,
                        });
                    }
                    child
                })
                .collect();
        }
        let mut children = Vec::new();

        if let Some(achievers) = self.achievers.get(&open.condition) {
            // Emit new steps before reuse. Search uses newest-generated plans as
            // its final GBFS tiebreaker, so this ordering makes reuse win equal
            // heuristic ranks instead of repeatedly inserting the same ground
            // operator.
            for achiever in achievers {
                if let Some(child) = self.add_step(plan, open_index, &open, achiever) {
                    children.push(child);
                }
            }

            // The regular plan representation stores steps newest-first and
            // emits reuse in that order. Reverse the insertion-ordered vector
            // to preserve the same deterministic preference.
            for step in plan.steps.iter().rev() {
                if !plan.orderings.possibly_before(
                    step.id,
                    StepTime::AtEnd,
                    open.consumer,
                    StepTime::AtStart,
                ) {
                    continue;
                }
                for achiever in achievers.iter().filter(|a| {
                    a.operator == step.operator
                        && !plan.effect_cannot_fire(self.task, step, a.effect)
                }) {
                    let effect = &self.task.operators[achiever.operator].effects[achiever.effect];
                    if let Some(child) = self.support(
                        plan,
                        open_index,
                        step.id,
                        Some(achiever.effect),
                        &effect.conditions,
                        open.consumer,
                    ) {
                        children.push(child);
                    }
                }
            }
        }

        // The initial state is the oldest reusable producer and is emitted
        // last, making it the preferred equal-rank child.
        if self.task.initial[open.condition.variable] == open.condition.value {
            if let Some(child) = self.support(plan, open_index, INIT_ID, None, &[], open.consumer) {
                children.push(child);
            }
        }
        children
    }

    fn support(
        &self,
        plan: &PartialPlan,
        open_index: usize,
        producer: usize,
        effect: Option<usize>,
        effect_conditions: &[Fact],
        consumer: usize,
    ) -> Option<PartialPlan> {
        let condition = plan.open_conditions[open_index].condition;
        let orderings = plan.orderings.refine(Ordering::new(
            producer,
            StepTime::AtEnd,
            consumer,
            StepTime::AtStart,
        ))?;
        let mut child = plan.clone();
        child.orderings = orderings;
        swap_remove_cow(
            &mut child.open_conditions,
            open_index,
            effect_conditions.len(),
        );
        let link_index = child.links.len();
        push_cow(
            &mut child.links,
            CausalLink {
                producer,
                consumer,
                condition,
                effect,
            },
        );
        for &effect_condition in effect_conditions {
            child.push_open(OpenCondition {
                consumer: producer,
                condition: effect_condition,
            });
        }
        if !child.settle(self.task) {
            return None;
        }
        child.add_link_threats(self.task, link_index);
        Some(child)
    }

    fn add_step(
        &self,
        plan: &PartialPlan,
        open_index: usize,
        open: &OpenCondition,
        achiever: &Achiever,
    ) -> Option<PartialPlan> {
        let new_id = plan.next_step_id;
        let orderings = plan.orderings.refine_with_step(
            Ordering::new(new_id, StepTime::AtEnd, open.consumer, StepTime::AtStart),
            new_id,
        )?;
        let operator = &self.task.operators[achiever.operator];
        let effect = &operator.effects[achiever.effect];

        let mut child = plan.clone();
        child.orderings = orderings;
        child.next_step_id += 1;
        child.cost = child
            .cost
            .saturating_add(self.action_cost.resolve(operator.cost));
        push_cow(
            &mut child.steps,
            Step {
                id: new_id,
                operator: achiever.operator,
            },
        );
        swap_remove_cow(
            &mut child.open_conditions,
            open_index,
            self.operator_preconditions[achiever.operator].len() + effect.conditions.len(),
        );
        let link_index = child.links.len();
        push_cow(
            &mut child.links,
            CausalLink {
                producer: new_id,
                consumer: open.consumer,
                condition: open.condition,
                effect: Some(achiever.effect),
            },
        );
        for &condition in &self.operator_preconditions[achiever.operator] {
            child.push_open(OpenCondition {
                consumer: new_id,
                condition,
            });
        }
        for &condition in &effect.conditions {
            child.push_open(OpenCondition {
                consumer: new_id,
                condition,
            });
        }
        if !child.settle(self.task) {
            return None;
        }
        child.add_link_threats(self.task, link_index);
        child.add_step_threats(self.task, new_id);
        Some(child)
    }

    /// The values confrontation can demand of the threatening step: the negated
    /// antecedent `y != c`, which over a finite domain is the disjunction over
    /// the remaining values of `y`, one refinement per alternative. Values the
    /// step is already committed against are skipped, since those children would
    /// be immediately inconsistent.
    fn confrontations(&self, plan: &PartialPlan, threat: &Threat) -> Vec<Fact> {
        // A precondition-based e-deletion threat has no effect to disarm: the
        // step requires the conflicting fact whenever it runs, so promotion and
        // demotion are its only resolvers.
        if threat.effect == NO_EFFECT {
            return Vec::new();
        }
        let Some(step) = plan.step(threat.step) else {
            return Vec::new();
        };
        let conditions = &self.task.operators[step.operator].effects[threat.effect].conditions;
        let mut alternatives: Vec<Fact> = Vec::new();
        for condition in conditions {
            for value in 0..self.task.variables[condition.variable].values.len() {
                let alternative = Fact::new(condition.variable, value);
                if value == condition.value
                    || alternatives.contains(&alternative)
                    || plan.step_excludes(threat.step, alternative)
                {
                    continue;
                }
                alternatives.push(alternative);
            }
        }
        alternatives
    }

    fn resolve_threat(&self, plan: &PartialPlan, threat: &Threat) -> Vec<PartialPlan> {
        let link = &plan.links[threat.link];
        let mut children = Vec::new();

        // Confrontation: UCPOP's resolver for conditional effects, which VHPOP
        // folds into separation. Committing the threatening step to another
        // value of one of its effect's condition variables disarms the
        // assignment without constraining where the step may be placed. Emitted
        // first so the newest-generated tiebreaker keeps preferring the ordering
        // resolvers.
        for alternative in self.confrontations(plan, threat) {
            let mut child = plan.clone();
            child.suppress_effect(threat.step, threat.effect);
            // An established link already commits the step to the alternative
            // value, so only an unsupported one needs a new open condition.
            let linked = plan
                .links
                .iter()
                .any(|link| link.consumer == threat.step && link.condition == alternative);
            if !linked {
                child.push_open(OpenCondition {
                    consumer: threat.step,
                    condition: alternative,
                });
            }
            if child.settle(self.task) {
                children.push(child);
            }
        }

        // With `-p disjunctive`, promotion and demotion are posted as one
        // constraint on a single child instead of splitting the plan in two.
        // Propagation then discharges it as soon as either disjunct becomes
        // entailed or impossible, so most threats never cost a branch at all.
        if self.disjunctive {
            if let Some(child) = self.post_disjunction(plan, threat) {
                children.push(child);
            }
            return children;
        }

        // Promotion: threatening step after the consumer. No step can follow the
        // synthetic goal. Emit promotion first so the newest-generated GBFS
        // tiebreaker prefers demotion when both refinements have equal rank,
        // matching the regular planner's deterministic ground-search order.
        if link.consumer != GOAL_ID {
            if let Some(orderings) = plan.orderings.refine(Ordering::new(
                link.consumer,
                StepTime::AtStart,
                threat.step,
                StepTime::AtEnd,
            )) {
                let mut child = plan.clone();
                child.orderings = orderings;
                if child.settle(self.task) {
                    children.push(child);
                }
            }
        }

        // Demotion: threatening step before the producer. No step can precede
        // the initial-state producer.
        if link.producer != INIT_ID {
            if let Some(orderings) = plan.orderings.refine(Ordering::new(
                threat.step,
                StepTime::AtEnd,
                link.producer,
                StepTime::AtEnd,
            )) {
                let mut child = plan.clone();
                child.orderings = orderings;
                if child.settle(self.task) {
                    children.push(child);
                }
            }
        }
        children
    }

    /// The single child carrying `(consumer ≺ step) ∨ (step ≺ producer)`.
    ///
    /// Unit propagation happens at posting time too: a disjunct the orderings
    /// already refute leaves the other forced, so the constraint is discharged
    /// straight into an ordering rather than stored. `None` means neither
    /// disjunct is possible and the threat cannot be resolved this way.
    fn post_disjunction(&self, plan: &PartialPlan, threat: &Threat) -> Option<PartialPlan> {
        let link = &plan.links[threat.link];
        // The goal follows everything and the initial state precedes it, so
        // those two cases rule the corresponding disjunct out up front.
        let promote = (link.consumer != GOAL_ID).then_some((link.consumer, threat.step));
        let demote = (link.producer != INIT_ID).then_some((threat.step, link.producer));

        let mut child = plan.clone();
        match (promote, demote) {
            (Some(promote), Some(demote)) => {
                let disjunctions = Rc::make_mut(&mut child.disjunctions);
                disjunctions.push(OrderingDisjunction {
                    threat: threat_key(threat),
                    promote,
                    demote,
                });
            }
            (Some((before, after)), None) | (None, Some((before, after))) => {
                child.orderings = child.orderings.refine(Ordering::new(
                    before,
                    StepTime::AtEnd,
                    after,
                    StepTime::AtEnd,
                ))?;
            }
            (None, None) => return None,
        }
        child.settle(self.task).then_some(child)
    }

    /// Splits a disjunction that propagation could not discharge: one child per
    /// disjunct. Reached only once nothing else in the plan is refinable.
    fn split_disjunction(&self, plan: &PartialPlan, index: usize) -> Vec<PartialPlan> {
        let disjunction = plan.disjunctions[index].clone();
        let mut children = Vec::new();
        for (before, after) in [disjunction.promote, disjunction.demote] {
            let mut child = plan.clone();
            let disjunctions = Rc::make_mut(&mut child.disjunctions);
            disjunctions.remove(index);
            let Some(orderings) = child.orderings.refine(Ordering::new(
                before,
                StepTime::AtEnd,
                after,
                StepTime::AtEnd,
            )) else {
                continue;
            };
            child.orderings = orderings;
            if child.settle(self.task) {
                children.push(child);
            }
        }
        children
    }

    fn refinements(
        &self,
        plan: &PartialPlan,
        order: &crate::heuristics::FlawSelectionOrder,
    ) -> Vec<PartialPlan> {
        let refinements = match self.select_flaw(plan, order) {
            SelectedFlaw::Threat(threat) => self.resolve_threat(plan, &threat),
            SelectedFlaw::Open(index) => self.resolve_open(plan, index),
            SelectedFlaw::Disjunction(index) => self.split_disjunction(plan, index),
        };

        #[cfg(test)]
        for child in &refinements {
            assert_eq!(
                child.threats(self.task),
                child.rediscover_threats(self.task),
                "incremental threat cache diverged"
            );
        }

        refinements
    }

    fn select_flaw(
        &self,
        plan: &PartialPlan,
        order: &crate::heuristics::FlawSelectionOrder,
    ) -> SelectedFlaw {
        let threats = &plan.threats;
        let local_consumer = plan.open_conditions.last().map(|open| open.consumer);

        for criterion in order.criteria() {
            let mut candidates = Vec::new();
            let relaxed = matches!(
                criterion.order,
                OrderType::Lc | OrderType::Mc | OrderType::Lw | OrderType::Mw
            )
            .then(|| self.relaxed_values(plan, criterion.reuse));
            if criterion.non_separable || criterion.separable {
                for (index, threat) in threats.iter().enumerate() {
                    // A threat already standing behind a posted disjunction is
                    // not a flaw to branch on: the constraint is doing the work.
                    if plan.threat_covered(threat) {
                        continue;
                    }
                    // A ground threat has no unifier to separate, so
                    // confrontability is all that remains of VHPOP's separation
                    // refinement and is what `{s}` selects here.
                    let confrontations = self.confrontations(plan, threat).len();
                    let applies = (criterion.non_separable && criterion.separable)
                        || (criterion.separable && confrontations > 0)
                        || (criterion.non_separable && confrontations == 0);
                    if !applies {
                        continue;
                    }
                    let refinements = self.threat_refinement_count(plan, threat, confrontations);
                    if refinements <= criterion.max_refinements {
                        candidates.push(FlawCandidate {
                            flaw: SelectedFlaw::Threat(threat.clone()),
                            is_threat: true,
                            refinements,
                            recency: index,
                            has_new: false,
                            has_reuse: false,
                            estimate: 0.0,
                        });
                    }
                }
            }
            for (index, open) in plan.open_conditions.iter().enumerate() {
                if !self.open_matches(criterion, plan, open, local_consumer) {
                    continue;
                }
                let refinements = self.open_refinement_count(plan, open);
                if refinements > criterion.max_refinements {
                    continue;
                }
                let has_new = self.achievers.contains_key(&open.condition)
                    || self.derived_supports.contains_key(&open.condition);
                let has_reuse = self.has_reuse(plan, open);
                let estimate = if let Some(estimates) = &relaxed {
                    match criterion.order {
                        OrderType::Lw | OrderType::Mw => {
                            estimates.work[open.condition.variable][open.condition.value] as f32
                        }
                        _ => estimates.cost[open.condition.variable][open.condition.value],
                    }
                } else {
                    0.0
                };
                candidates.push(FlawCandidate {
                    flaw: SelectedFlaw::Open(index),
                    is_threat: false,
                    refinements,
                    recency: index,
                    has_new,
                    has_reuse,
                    estimate,
                });
            }
            if let Some(candidate) = choose_candidate(candidates, criterion.order) {
                return candidate.flaw;
            }
        }

        // Every remaining threat stands behind a disjunction that propagation
        // could not discharge. Split the oldest one.
        if !plan.disjunctions.is_empty() {
            return SelectedFlaw::Disjunction(0);
        }

        panic!("finite-domain flaw order did not select an outstanding flaw")
    }

    fn open_matches(
        &self,
        criterion: &SelectionCriterion,
        plan: &PartialPlan,
        open: &OpenCondition,
        local_consumer: Option<usize>,
    ) -> bool {
        criterion.open_cond
            || (criterion.local_open_cond && Some(open.consumer) == local_consumer)
            || (criterion.static_open_cond && !self.variable_has_effect[open.condition.variable])
            || (criterion.unsafe_open_cond && self.unsafe_open_condition(plan, open))
    }

    fn unsafe_open_condition(&self, plan: &PartialPlan, open: &OpenCondition) -> bool {
        plan.steps.iter().any(|step| {
            plan.orderings.possibly_before(
                step.id,
                StepTime::AtEnd,
                open.consumer,
                StepTime::AtStart,
            ) && self.task.operators[step.operator]
                .effects
                .iter()
                .enumerate()
                .any(|(index, effect)| {
                    effect_clobbers(effect.variable, effect.post, open.condition)
                        && !plan.effect_cannot_fire(self.task, step, index)
                })
        })
    }

    fn threat_refinement_count(
        &self,
        plan: &PartialPlan,
        threat: &Threat,
        confrontations: usize,
    ) -> i32 {
        let link = &plan.links[threat.link];
        let demote = link.producer != INIT_ID
            && plan.orderings.possibly_before(
                threat.step,
                StepTime::AtEnd,
                link.producer,
                StepTime::AtEnd,
            );
        let promote = link.consumer != GOAL_ID
            && plan.orderings.possibly_before(
                link.consumer,
                StepTime::AtStart,
                threat.step,
                StepTime::AtEnd,
            );
        i32::from(demote)
            .saturating_add(i32::from(promote))
            .saturating_add(i32::try_from(confrontations).unwrap_or(i32::MAX))
    }

    fn open_refinement_count(&self, plan: &PartialPlan, open: &OpenCondition) -> i32 {
        if let Some(supports) = self.derived_supports.get(&open.condition) {
            return i32::try_from(supports.len()).unwrap_or(i32::MAX);
        }
        let mut count =
            i32::from(self.task.initial[open.condition.variable] == open.condition.value);
        if let Some(achievers) = self.achievers.get(&open.condition) {
            count = count.saturating_add(achievers.len() as i32);
            for step in plan.steps.iter() {
                if plan.orderings.possibly_before(
                    step.id,
                    StepTime::AtEnd,
                    open.consumer,
                    StepTime::AtStart,
                ) {
                    count = count.saturating_add(
                        achievers
                            .iter()
                            .filter(|achiever| {
                                achiever.operator == step.operator
                                    && !plan.effect_cannot_fire(self.task, step, achiever.effect)
                            })
                            .count() as i32,
                    );
                }
            }
        }
        count
    }

    fn has_reuse(&self, plan: &PartialPlan, open: &OpenCondition) -> bool {
        if self.task.initial[open.condition.variable] == open.condition.value {
            return true;
        }
        self.achievers
            .get(&open.condition)
            .is_some_and(|achievers| {
                plan.steps.iter().any(|step| {
                    plan.orderings.possibly_before(
                        step.id,
                        StepTime::AtEnd,
                        open.consumer,
                        StepTime::AtStart,
                    ) && achievers.iter().any(|achiever| {
                        achiever.operator == step.operator
                            && !plan.effect_cannot_fire(self.task, step, achiever.effect)
                    })
                })
            })
    }

    fn rank_both(
        &self,
        plan: &PartialPlan,
        params: &Parameters,
        stats: &mut SearchStats,
    ) -> (Vec<f32>, Vec<f32>) {
        // Only read the clock when `h_eval_ms` will be reported; see
        // `Parameters::time_h_evals`.
        let start = params.time_h_evals.then(Instant::now);
        let result = self.compute_rank_both(plan, params);
        stats.h_evals += 1;
        if let Some(start) = start {
            stats.h_eval_nanos += start.elapsed().as_nanos();
            stats.h_eval_ms = stats.h_eval_nanos / 1_000_000;
        }
        result
    }

    fn compute_rank_both(&self, plan: &PartialPlan, params: &Parameters) -> (Vec<f32>, Vec<f32>) {
        let g = plan.cost() as f32;
        let opens = plan.num_open_conditions();
        let threats = plan.threats.len();
        let mut rank = Vec::with_capacity(params.heuristic.terms().len());
        let mut grank = Vec::with_capacity(params.heuristic.terms().len() + 2);
        let mut add = None;
        let mut addr = None;
        let mut relax = None;
        let mut relaxr = None;
        let mut lmcut = None;
        let mut lmcutr = None;

        for term in params.heuristic.terms() {
            match term {
                HVal::Lifo => {
                    rank.push(-(plan.id as f32));
                    grank.push(-(plan.id as f32));
                }
                HVal::Fifo => {
                    rank.push(plan.id as f32);
                    grank.push(plan.id as f32);
                }
                HVal::Oc => {
                    rank.push(opens as f32);
                    grank.push(opens as f32);
                }
                HVal::Uc => {
                    rank.push(threats as f32);
                    grank.push(threats as f32);
                }
                HVal::Buc => {
                    let value = f32::from(threats > 0);
                    rank.push(value);
                    grank.push(value);
                }
                HVal::SPlusOc => {
                    let h = params.weight * opens as f32;
                    rank.push(g + h);
                    grank.push(h);
                }
                HVal::Ucpop => {
                    let h = params.weight * (opens + threats) as f32;
                    rank.push(g + h);
                    grank.push(h);
                }
                HVal::Add | HVal::AddCost | HVal::AddWork => {
                    let estimate = add.get_or_insert_with(|| self.open_estimate(plan, false));
                    push_add_rank(&mut rank, &mut grank, *term, *estimate, g, params.weight);
                }
                HVal::Addr | HVal::AddrCost | HVal::AddrWork => {
                    let estimate = addr.get_or_insert_with(|| self.open_estimate(plan, true));
                    push_add_rank(&mut rank, &mut grank, *term, *estimate, g, params.weight);
                }
                HVal::Relax | HVal::RelaxR => {
                    let reuse = matches!(term, HVal::RelaxR);
                    let estimate = if reuse {
                        *relaxr.get_or_insert_with(|| self.relaxed_plan_size(plan, true))
                    } else {
                        *relax.get_or_insert_with(|| self.relaxed_plan_size(plan, false))
                    };
                    let h = estimate.map_or(f32::INFINITY, |value| params.weight * value);
                    rank.push(if h.is_finite() { g + h } else { h });
                    grank.push(h);
                }
                HVal::LmCut | HVal::LmCutR => {
                    let reuse = matches!(term, HVal::LmCutR);
                    let estimate = if reuse {
                        *lmcutr.get_or_insert_with(|| self.lmcut_estimate(plan, true))
                    } else {
                        *lmcut.get_or_insert_with(|| self.lmcut_estimate(plan, false))
                    };
                    let h = estimate.map_or(f32::INFINITY, |value| params.weight * value);
                    rank.push(if h.is_finite() { g + h } else { h });
                    grank.push(h);
                }
                HVal::Landmarks
                | HVal::SampleFf(_)
                | HVal::Lplan(_)
                | HVal::Lpsas(_)
                | HVal::Compile(_) => {
                    unreachable!("unsupported FDR heuristic was rejected before search")
                }
            }
        }
        grank.push(opens as f32);
        grank.push(-(plan.id as f32));
        (rank, grank)
    }

    fn lmcut_estimate(&self, plan: &PartialPlan, reuse: bool) -> Option<f32> {
        let reusable = if reuse {
            plan.steps
                .iter()
                .flat_map(|step| {
                    self.task.operators[step.operator]
                        .effects
                        .iter()
                        .enumerate()
                        .filter(|&(index, _)| !plan.effect_cannot_fire(self.task, step, index))
                        .map(|(_, effect)| effect.assignment())
                })
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        let goals = plan
            .open_conditions
            .iter()
            .map(|open| open.condition)
            .collect::<Vec<_>>();
        self.lmcut
            .as_ref()
            .expect("native LM-cut was validated before search")
            .evaluate(reusable, goals)
            .map(|value| value as f32)
    }

    fn open_estimate(&self, plan: &PartialPlan, reuse: bool) -> AddEstimate {
        let values = self.relaxed_values(plan, reuse);
        let mut estimate = AddEstimate::default();
        for open in plan.open_conditions.iter() {
            let cost = values.cost[open.condition.variable][open.condition.value];
            let work = values.work[open.condition.variable][open.condition.value];
            estimate.cost += cost;
            estimate.work = estimate.work.saturating_add(work);
        }
        estimate
    }

    fn relaxed_values<'b>(&'b self, plan: &PartialPlan, reuse: bool) -> Cow<'b, RelaxedValues> {
        if !reuse {
            return Cow::Borrowed(&self.base_relaxed);
        }

        let mut values = self.base_relaxed.clone();
        let mut changed = false;
        for step in plan.steps.iter() {
            for (index, effect) in self.task.operators[step.operator]
                .effects
                .iter()
                .enumerate()
            {
                if plan.effect_cannot_fire(self.task, step, index) {
                    continue;
                }
                if values.cost[effect.variable][effect.post] != 0.0 {
                    values.cost[effect.variable][effect.post] = 0.0;
                    changed = true;
                }
                if values.work[effect.variable][effect.post] != 0 {
                    values.work[effect.variable][effect.post] = 0;
                    changed = true;
                }
            }
        }
        if changed {
            saturate_relaxed_values(
                self.task,
                &self.effect_requirements,
                &self.derived_supports,
                &mut values,
                self.action_cost,
            );
        }
        Cow::Owned(values)
    }

    /// Extracts one joint delete-relaxed support graph for every open
    /// finite-domain equality. Unlike `h_add`, an operator selected for several
    /// effects is counted once, exposing shared moves and other shared support.
    fn relaxed_plan_size(&self, plan: &PartialPlan, reuse: bool) -> Option<f32> {
        let reusable = if reuse {
            plan.steps
                .iter()
                .flat_map(|step| {
                    self.task.operators[step.operator]
                        .effects
                        .iter()
                        .enumerate()
                        .filter(|&(index, _)| !plan.effect_cannot_fire(self.task, step, index))
                        .map(|(_, effect)| effect.assignment())
                })
                .collect::<HashSet<_>>()
        } else {
            HashSet::new()
        };
        let mut chosen_operators = HashSet::new();
        let mut achieved = HashSet::new();
        let mut worklist = plan
            .open_conditions
            .iter()
            .map(|open| open.condition)
            .collect::<Vec<_>>();

        while let Some(goal) = worklist.pop() {
            if achieved.contains(&goal) {
                continue;
            }
            if (!self.task.is_derived_variable(goal.variable)
                && self.task.initial[goal.variable] == goal.value)
                || reusable.contains(&goal)
            {
                achieved.insert(goal);
                continue;
            }

            if let Some(supports) = self.derived_supports.get(&goal) {
                let support = supports.iter().min_by(|left, right| {
                    let cost = |clause: &&Vec<Fact>| {
                        clause
                            .iter()
                            .map(|fact| self.base_relaxed.cost[fact.variable][fact.value])
                            .sum::<f32>()
                    };
                    cost(left).total_cmp(&cost(right))
                })?;
                achieved.insert(goal);
                for &requirement in support.iter() {
                    if !achieved.contains(&requirement) {
                        worklist.push(requirement);
                    }
                }
                continue;
            }

            let achiever = self.base_relaxed.achiever[goal.variable][goal.value]?;
            achieved.insert(goal);
            chosen_operators.insert(achiever.operator);
            for &requirement in &self.effect_requirements[achiever.operator][achiever.effect] {
                if !achieved.contains(&requirement) {
                    worklist.push(requirement);
                }
            }
        }

        Some(
            chosen_operators
                .into_iter()
                .map(|operator| self.action_cost.resolve(self.task.operators[operator].cost) as f32)
                .sum(),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn pop_next(
        &self,
        primary: &mut BinaryHeap<QueuedPlan>,
        mut secondary: Option<&mut BinaryHeap<QueuedPlan>>,
        expanded_ids: &HashSet<usize>,
        params: &Parameters,
        is_lazy: bool,
        is_gbfs: bool,
        is_dual: bool,
        is_alt: bool,
        boost_budget: &mut usize,
        expand_count: &mut usize,
        stats: &mut SearchStats,
    ) -> (Option<Rc<PartialPlan>>, f32) {
        let alt_use_secondary = is_alt && {
            *expand_count += 1;
            (*expand_count).is_multiple_of(2)
        };
        loop {
            let use_secondary = alt_use_secondary
                || (is_dual && *boost_budget == 0 && {
                    *expand_count += 1;
                    (*expand_count).is_multiple_of(3)
                });
            let queued = if use_secondary {
                secondary
                    .as_deref_mut()
                    .and_then(BinaryHeap::pop)
                    .or_else(|| primary.pop())
            } else if is_alt {
                primary
                    .pop()
                    .or_else(|| secondary.as_deref_mut().and_then(BinaryHeap::pop))
            } else {
                primary.pop()
            };
            let Some(queued) = queued else {
                return (None, 0.0);
            };
            if (is_dual || is_alt) && expanded_ids.contains(&queued.plan.id) {
                continue;
            }
            if !is_lazy || !queued.is_lazy {
                return (Some(queued.plan), queued.rank[0]);
            }
            let rank = if is_gbfs {
                self.rank_both(&queued.plan, params, stats).1
            } else {
                self.rank_both(&queued.plan, params, stats).0
            };
            if rank[0].is_finite() {
                primary.push(QueuedPlan {
                    plan: queued.plan,
                    rank,
                    is_lazy: false,
                });
            }
        }
    }
}

fn effect_clobbers(variable: usize, post: usize, protected: Fact) -> bool {
    variable == protected.variable && post != protected.value
}

/// Whether an effect clobbers `protected`, extended by **e-deletion** when a
/// mutex table is supplied.
///
/// Nguyen & Kambhampati (IJCAI-01) generalise the classical threat test through
/// reachability: `aₖ` conflicts with a link on `p` when `Eff(aₖ) ∪ {p}` contains
/// a mutex, not only when `aₖ` deletes `p`. Vidal & Geffner (AAAI-04) state the
/// same rule action-wise as *e-deletion*.
///
/// Over one SAS⁺ variable the generalisation collapses to the classical test, so
/// what this adds is the cross-variable case: an assignment the translator has
/// proved cannot hold beside `protected`. Only an **unconditional** assignment
/// counts — a conditional one might not fire, and claiming a threat that cannot
/// happen would let threat resolution over-constrain a refinable plan.
fn effect_e_deletes(
    effect: &crate::fdr::Effect,
    protected: Fact,
    mutexes: Option<&crate::cutset::FactMutexes>,
) -> bool {
    if effect_clobbers(effect.variable, effect.post, protected) {
        return true;
    }
    match mutexes {
        Some(mutexes) => {
            effect.conditions.is_empty() && mutexes.mutex(effect.assignment(), protected)
        }
        None => false,
    }
}

/// Whether an operator's *precondition* e-deletes `protected`: it requires a
/// fact that cannot hold beside the protected one, and does not re-establish it.
///
/// This is CPT's third e-deletion case, and in a finite-domain task it is the
/// productive one — it needs no cross-variable invariant, only the exactly-one
/// semantics a SAS⁺ variable already has. A step requiring `location(truck) =
/// lyon` cannot run inside an interval protecting `location(truck) = paris`,
/// even though it assigns nothing.
///
/// The "does not re-establish `protected`" guard is kept from the published
/// rule. A step that requires a mutex fact already breaks the protection when it
/// *starts*, so the guard is not needed for soundness here, but it keeps the
/// implementation literally the published one and only ever suppresses threats.
fn precondition_e_deletes(
    operator: &crate::fdr::Operator,
    protected: Fact,
    mutexes: &crate::cutset::FactMutexes,
) -> bool {
    let reestablishes = operator
        .effects
        .iter()
        .any(|effect| effect.conditions.is_empty() && effect.assignment() == protected);
    if reestablishes {
        return false;
    }
    operator
        .prevail
        .iter()
        .copied()
        .chain(
            operator
                .effects
                .iter()
                .filter_map(|effect| effect.pre.map(|pre| Fact::new(effect.variable, pre))),
        )
        .any(|required| mutexes.mutex(required, protected))
}

fn threat_key(threat: &Threat) -> (usize, usize, usize) {
    (threat.link, threat.step, threat.effect)
}

/// Returns a deterministic topological linearization and independently executes
/// it against the SAS+ transition semantics. This is the search path's validity
/// oracle: representation/refinement mistakes cannot silently escape as plans.
fn linearize_and_validate(plan: &PartialPlan, task: &Task) -> Option<Vec<usize>> {
    // Build a topological order iteratively. `BinaryOrderings::schedule` is
    // recursive and is ideal for relatively shallow plans, but ground search
    // can generate very deep plans
    // before its node limit and must not overflow the process stack.
    let mut remaining = (*plan.steps).clone();
    remaining.sort_by_key(|step| step.id);
    let mut steps = Vec::with_capacity(remaining.len());
    while !remaining.is_empty() {
        let index = remaining.iter().position(|candidate| {
            remaining.iter().all(|other| {
                candidate.id == other.id
                    || !is_ordered_before(&plan.orderings, other.id, candidate.id)
            })
        })?;
        steps.push(remaining.remove(index));
    }

    let mut state = task.initial.clone();
    let mut operators = Vec::with_capacity(steps.len());
    for step in steps {
        task.close_axioms(&mut state);
        let operator = &task.operators[step.operator];
        if operator
            .preconditions()
            .iter()
            .any(|fact| state[fact.variable] != fact.value)
        {
            return None;
        }

        // Conditions are tested in the predecessor state; triggered assignments
        // are then applied together. Fast Downward canonicalizes conflicting
        // effects by post-value order, which the emitted effect order preserves.
        let old_state = state.clone();
        for effect in &operator.effects {
            if effect
                .conditions
                .iter()
                .all(|fact| old_state[fact.variable] == fact.value)
            {
                state[effect.variable] = effect.post;
            }
        }
        operators.push(step.operator);
    }

    task.close_axioms(&mut state);

    task.goals
        .iter()
        .all(|goal| state[goal.variable] == goal.value)
        .then_some(operators)
}

/// Whether an ordering already holds, cannot hold, or is still open.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OrderingStatus {
    Entailed,
    Impossible,
    Undetermined,
}

fn is_ordered_before(orderings: &BinaryOrderings, before: usize, after: usize) -> bool {
    before != after && !orderings.possibly_before(after, StepTime::AtEnd, before, StepTime::AtStart)
}

#[derive(Debug, Clone)]
enum SelectedFlaw {
    Threat(Threat),
    Open(usize),
    /// A pending ordering disjunction, split into one child per disjunct.
    Disjunction(usize),
}

struct FlawCandidate {
    flaw: SelectedFlaw,
    is_threat: bool,
    refinements: i32,
    recency: usize,
    has_new: bool,
    has_reuse: bool,
    estimate: f32,
}

fn choose_candidate(candidates: Vec<FlawCandidate>, order: OrderType) -> Option<FlawCandidate> {
    let prefer = |left: &FlawCandidate, right: &FlawCandidate| match order {
        // Threat selection runs before open-condition selection in the literal
        // planner. LIFO commits to a threat at the shared criterion; FIFO lets
        // the later open-condition pass replace it.
        OrderType::Lifo => (left.is_threat, left.recency) > (right.is_threat, right.recency),
        OrderType::Fifo => {
            if left.is_threat != right.is_threat {
                !left.is_threat
            } else {
                left.recency < right.recency
            }
        }
        OrderType::Random => left.recency > right.recency,
        OrderType::Lr => {
            left.refinements < right.refinements
                || (left.refinements == right.refinements
                    && (left.is_threat, left.recency) > (right.is_threat, right.recency))
        }
        OrderType::Mr => {
            left.refinements > right.refinements
                || (left.refinements == right.refinements
                    && (left.is_threat, left.recency) > (right.is_threat, right.recency))
        }
        OrderType::New => (left.has_new, left.recency) > (right.has_new, right.recency),
        OrderType::Reuse => (left.has_reuse, left.recency) > (right.has_reuse, right.recency),
        OrderType::Lc | OrderType::Lw => {
            left.estimate < right.estimate
                || (left.estimate == right.estimate && left.recency > right.recency)
        }
        OrderType::Mc | OrderType::Mw => {
            left.estimate > right.estimate
                || (left.estimate == right.estimate && left.recency > right.recency)
        }
    };
    let mut selected = None;
    for candidate in candidates {
        if selected
            .as_ref()
            .is_none_or(|current| prefer(&candidate, current))
        {
            selected = Some(candidate);
        }
    }
    selected
}

#[derive(Debug, Clone, Copy, Default)]
struct AddEstimate {
    cost: f32,
    work: i32,
}

#[derive(Clone)]
struct RelaxedValues {
    cost: Vec<Vec<f32>>,
    work: Vec<Vec<i32>>,
    achiever: Vec<Vec<Option<Achiever>>>,
}

fn build_base_relaxed_values(
    task: &Task,
    effect_requirements: &[Vec<Vec<Fact>>],
    derived_supports: &HashMap<Fact, Vec<Vec<Fact>>>,
    action_cost: ActionCost,
) -> RelaxedValues {
    let mut values = RelaxedValues {
        cost: task
            .variables
            .iter()
            .map(|variable| vec![f32::INFINITY; variable.values.len()])
            .collect(),
        work: task
            .variables
            .iter()
            .map(|variable| vec![i32::MAX; variable.values.len()])
            .collect(),
        achiever: task
            .variables
            .iter()
            .map(|variable| vec![None; variable.values.len()])
            .collect(),
    };
    for (variable, &value) in task.initial.iter().enumerate() {
        if task.is_derived_variable(variable) {
            continue;
        }
        values.cost[variable][value] = 0.0;
        values.work[variable][value] = 0;
    }
    saturate_relaxed_values(
        task,
        effect_requirements,
        derived_supports,
        &mut values,
        action_cost,
    );
    values
}

fn saturate_relaxed_values(
    task: &Task,
    effect_requirements: &[Vec<Vec<Fact>>],
    derived_supports: &HashMap<Fact, Vec<Vec<Fact>>>,
    values: &mut RelaxedValues,
    action_cost: ActionCost,
) {
    loop {
        let mut changed = false;
        for (operator_index, operator) in task.operators.iter().enumerate() {
            for (effect_index, effect) in operator.effects.iter().enumerate() {
                let mut cost = action_cost.resolve(operator.cost) as f32;
                let mut work = 1i32;
                for fact in &effect_requirements[operator_index][effect_index] {
                    cost += values.cost[fact.variable][fact.value];
                    work = work.saturating_add(values.work[fact.variable][fact.value]);
                }
                if cost < values.cost[effect.variable][effect.post] {
                    values.cost[effect.variable][effect.post] = cost;
                    values.achiever[effect.variable][effect.post] = Some(Achiever {
                        operator: operator_index,
                        effect: effect_index,
                    });
                    changed = true;
                }
                if work < values.work[effect.variable][effect.post] {
                    values.work[effect.variable][effect.post] = work;
                    changed = true;
                }
            }
        }
        for (&fact, supports) in derived_supports {
            for support in supports {
                let mut cost = 0.0f32;
                let mut work = 0i32;
                for condition in support {
                    cost += values.cost[condition.variable][condition.value];
                    work = work.saturating_add(values.work[condition.variable][condition.value]);
                }
                if cost < values.cost[fact.variable][fact.value] {
                    values.cost[fact.variable][fact.value] = cost;
                    changed = true;
                }
                if work < values.work[fact.variable][fact.value] {
                    values.work[fact.variable][fact.value] = work;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
}

fn push_add_rank(
    rank: &mut Vec<f32>,
    grank: &mut Vec<f32>,
    term: HVal,
    estimate: AddEstimate,
    steps: f32,
    weight: f32,
) {
    let cost_finite = estimate.cost.is_finite();
    let work_finite = estimate.work < i32::MAX;
    match term {
        HVal::Add | HVal::Addr => {
            let weighted = if cost_finite {
                weight * estimate.cost
            } else {
                f32::INFINITY
            };
            rank.push(if weighted.is_finite() {
                steps + weighted
            } else {
                weighted
            });
            grank.push(if cost_finite {
                estimate.cost
            } else {
                f32::INFINITY
            });
        }
        HVal::AddCost | HVal::AddrCost => {
            let value = if cost_finite {
                estimate.cost
            } else {
                f32::INFINITY
            };
            rank.push(value);
            grank.push(value);
        }
        HVal::AddWork | HVal::AddrWork => {
            let value = if work_finite {
                estimate.work as f32
            } else {
                f32::INFINITY
            };
            rank.push(value);
            grank.push(value);
        }
        _ => unreachable!("push_add_rank called for a non-additive term"),
    }
}

struct QueuedPlan {
    plan: Rc<PartialPlan>,
    rank: Vec<f32>,
    is_lazy: bool,
}

impl PartialEq for QueuedPlan {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == CmpOrdering::Equal
    }
}

impl Eq for QueuedPlan {}

impl PartialOrd for QueuedPlan {
    fn partial_cmp(&self, other: &Self) -> Option<CmpOrdering> {
        Some(self.cmp(other))
    }
}

impl Ord for QueuedPlan {
    fn cmp(&self, other: &Self) -> CmpOrdering {
        let n = self.rank.len().max(other.rank.len());
        for index in 0..n {
            let left = self.rank.get(index).copied().unwrap_or(0.0);
            let right = other.rank.get(index).copied().unwrap_or(0.0);
            if left < right {
                return CmpOrdering::Greater;
            }
            if left > right {
                return CmpOrdering::Less;
            }
        }
        CmpOrdering::Equal
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    FastDownward(#[from] FdError),
    #[error(transparent)]
    Parse(#[from] ParseError),
    #[error("unsupported FDR POCL feature: {0}")]
    Unsupported(String),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fdr::{Effect, Operator, Variable};
    use crate::heuristics::{FlawSelectionOrder, Heuristic};

    fn travel_task() -> Task {
        Task {
            variables: vec![Variable {
                name: "location".to_string(),
                values: vec![
                    "Atom at(truck,paris)".to_string(),
                    "Atom at(truck,lyon)".to_string(),
                    "Atom at(truck,nice)".to_string(),
                ],
            }],
            initial: vec![0],
            goals: vec![Fact::new(0, 2)],
            operators: vec![
                Operator {
                    name: "drive truck paris lyon".to_string(),
                    prevail: vec![],
                    effects: vec![Effect {
                        conditions: vec![],
                        variable: 0,
                        pre: Some(0),
                        post: 1,
                    }],
                    cost: 1,
                },
                Operator {
                    name: "drive truck lyon nice".to_string(),
                    prevail: vec![],
                    effects: vec![Effect {
                        conditions: vec![],
                        variable: 0,
                        pre: Some(1),
                        post: 2,
                    }],
                    cost: 1,
                },
            ],
            axioms: vec![],
            mutex_groups: vec![],
        }
    }

    fn conditional_task() -> Task {
        Task {
            variables: vec![
                Variable {
                    name: "location".to_string(),
                    values: vec!["at-a".to_string(), "at-b".to_string()],
                },
                Variable {
                    name: "switch".to_string(),
                    values: vec!["off".to_string(), "on".to_string()],
                },
            ],
            initial: vec![0, 0],
            goals: vec![Fact::new(0, 1)],
            operators: vec![
                Operator {
                    name: "turn-on".to_string(),
                    prevail: vec![],
                    effects: vec![Effect {
                        conditions: vec![],
                        variable: 1,
                        pre: Some(0),
                        post: 1,
                    }],
                    cost: 1,
                },
                Operator {
                    name: "move".to_string(),
                    prevail: vec![],
                    effects: vec![Effect {
                        conditions: vec![Fact::new(1, 1)],
                        variable: 0,
                        pre: Some(0),
                        post: 1,
                    }],
                    cost: 1,
                },
            ],
            axioms: vec![],
            mutex_groups: vec![],
        }
    }

    /// A task solvable only by confrontation. `run` must follow `power-on` to
    /// see `power = on`, so the conditional assignment that switches the power
    /// back off can be neither demoted nor promoted, and the spent fuse rules
    /// out establishing the goal with a second `power-on`. The single remaining
    /// resolver is to commit `run` to `mode = safe`.
    fn breaker_task() -> Task {
        let binary = |name: &str, off: &str, on: &str| Variable {
            name: name.to_string(),
            values: vec![off.to_string(), on.to_string()],
        };
        Task {
            variables: vec![
                binary("power", "off", "on"),
                binary("device", "idle", "done"),
                binary("mode", "unsafe", "safe"),
                binary("fuse", "intact", "spent"),
            ],
            initial: vec![0, 0, 0, 0],
            goals: vec![Fact::new(0, 1), Fact::new(1, 1)],
            operators: vec![
                Operator {
                    name: "power-on".to_string(),
                    prevail: vec![],
                    effects: vec![
                        Effect {
                            conditions: vec![],
                            variable: 0,
                            pre: Some(0),
                            post: 1,
                        },
                        Effect {
                            conditions: vec![],
                            variable: 3,
                            pre: Some(0),
                            post: 1,
                        },
                    ],
                    cost: 1,
                },
                Operator {
                    name: "run".to_string(),
                    prevail: vec![Fact::new(0, 1)],
                    effects: vec![
                        Effect {
                            conditions: vec![],
                            variable: 1,
                            pre: Some(0),
                            post: 1,
                        },
                        Effect {
                            conditions: vec![Fact::new(2, 0)],
                            variable: 0,
                            pre: None,
                            post: 0,
                        },
                    ],
                    cost: 1,
                },
                Operator {
                    name: "make-safe".to_string(),
                    prevail: vec![],
                    effects: vec![Effect {
                        conditions: vec![],
                        variable: 2,
                        pre: Some(0),
                        post: 1,
                    }],
                    cost: 1,
                },
            ],
            axioms: vec![],
            mutex_groups: vec![],
        }
    }

    /// The plan in which `power-on` (step 1) supports the goal's `power = on`
    /// and `run` (step 2) follows it, threatening that link.
    fn trapped_breaker_plan() -> (PartialPlan, Threat) {
        let orderings = Rc::new(BinaryOrderings::new())
            .refine_with_step(
                Ordering::new(1, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                1,
            )
            .unwrap()
            .refine_with_step(
                Ordering::new(2, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                2,
            )
            .unwrap()
            .refine(Ordering::new(1, StepTime::AtEnd, 2, StepTime::AtStart))
            .unwrap();
        let threat = Threat {
            step: 2,
            effect: 1,
            link: 0,
        };
        let plan = PartialPlan {
            steps: Rc::new(vec![
                Step { id: 1, operator: 0 },
                Step { id: 2, operator: 1 },
            ]),
            links: Rc::new(vec![CausalLink {
                producer: 1,
                consumer: GOAL_ID,
                condition: Fact::new(0, 1),
                effect: Some(0),
            }]),
            open_conditions: Rc::new(vec![]),
            orderings,
            threats: Rc::new(vec![threat.clone()]),
            suppressed: Rc::new(vec![]),
            disjunctions: Rc::new(Vec::new()),
            edelete: None,
            cost: 2,
            next_step_id: 3,
            id: 0,
        };
        (plan, threat)
    }

    fn shared_effect_task() -> Task {
        Task {
            variables: vec![
                Variable {
                    name: "left".to_string(),
                    values: vec!["off".to_string(), "on".to_string()],
                },
                Variable {
                    name: "right".to_string(),
                    values: vec!["off".to_string(), "on".to_string()],
                },
            ],
            initial: vec![0, 0],
            goals: vec![Fact::new(0, 1), Fact::new(1, 1)],
            operators: vec![Operator {
                name: "switch-both-on".to_string(),
                prevail: vec![],
                effects: vec![
                    Effect {
                        conditions: vec![],
                        variable: 0,
                        pre: Some(0),
                        post: 1,
                    },
                    Effect {
                        conditions: vec![],
                        variable: 1,
                        pre: Some(0),
                        post: 1,
                    },
                ],
                cost: 1,
            }],
            axioms: vec![],
            mutex_groups: vec![],
        }
    }

    #[test]
    fn solves_over_a_three_valued_variable() {
        let task = travel_task();
        let (outcome, stats) = solve(&task, 1_000);
        let Outcome::Solved(solution) = outcome else {
            panic!("expected a solution");
        };
        assert_eq!(solution.operators, vec![0, 1]);
        assert!(solution.plan.complete(&task));
        assert!(stats.nodes_visited > 0);
    }

    #[test]
    fn progress_callback_observes_fdr_expansions() {
        let task = travel_task();
        let params = Parameters {
            search_limits: vec![1_000],
            ..Parameters::default()
        };
        let mut updates = Vec::new();
        let mut report = |progress| updates.push(progress);
        let (outcome, stats) = solve_with_params_and_progress(&task, &params, &mut report).unwrap();

        assert!(matches!(outcome, Outcome::Solved(_)));
        assert!(!updates.is_empty());
        assert_eq!(updates[0].nodes_visited, 1);
        assert_eq!(updates.last().unwrap().nodes_visited, stats.nodes_visited);
        assert_eq!(
            updates.last().unwrap().nodes_generated,
            stats.nodes_generated
        );
        assert!(stats.max_queued > 0);
    }

    #[test]
    fn conditional_assignment_conditions_become_open_conditions() {
        let task = conditional_task();
        let params = Parameters {
            heuristic: Heuristic::parse("ADD").unwrap(),
            search_limits: vec![1_000],
            ..Parameters::default()
        };
        let (outcome, _) = solve_with_params(&task, &params).unwrap();
        let Outcome::Solved(solution) = outcome else {
            panic!("expected a solution");
        };
        assert_eq!(solution.operators, vec![0, 1]);
    }

    #[test]
    fn relaxed_plan_counts_a_shared_operator_once() {
        let task = shared_effect_task();
        let planner = Planner::new(&task);
        let plan = PartialPlan::initial(&task);
        assert_eq!(planner.open_estimate(&plan, false).cost, 2.0);
        assert_eq!(planner.relaxed_plan_size(&plan, false), Some(1.0));
        assert_eq!(planner.lmcut_estimate(&plan, false), Some(1.0));

        for heuristic in ["RELAX", "RELAXR", "LMCUT", "LMCUTR"] {
            let params = Parameters {
                search_algorithm: SearchAlgorithm::Gbfs,
                heuristic: Heuristic::parse(heuristic).unwrap(),
                search_limits: vec![100],
                ..Parameters::default()
            };
            let (outcome, _) = solve_with_params(&task, &params).unwrap();
            let Outcome::Solved(solution) = outcome else {
                panic!("{heuristic} did not solve the shared-effect task");
            };
            assert_eq!(solution.operators, vec![0]);
        }
    }

    #[test]
    fn lmcutr_reuses_committed_step_effects() {
        let task = travel_task();
        let planner = Planner::new(&task);
        let mut plan = PartialPlan::initial(&task);
        plan.steps = Rc::new(vec![Step { id: 1, operator: 0 }]);

        assert_eq!(planner.lmcut_estimate(&plan, false), Some(2.0));
        assert_eq!(planner.lmcut_estimate(&plan, true), Some(1.0));
    }

    #[test]
    fn native_lmcut_rejects_conditional_effects_only_when_selected() {
        let task = conditional_task();
        let params = Parameters {
            heuristic: Heuristic::parse("LMCUTR").unwrap(),
            search_limits: vec![100],
            ..Parameters::default()
        };
        let error = solve_with_params(&task, &params).unwrap_err();
        assert!(error.to_string().contains("conditional effects"));
    }

    #[test]
    fn production_search_algorithms_solve_the_same_fdr_task() {
        let task = travel_task();
        for algorithm in [
            SearchAlgorithm::A,
            SearchAlgorithm::Ida,
            SearchAlgorithm::Hc,
            SearchAlgorithm::Bfs,
            SearchAlgorithm::Gbfs,
            SearchAlgorithm::LazyGbfs,
            SearchAlgorithm::LazyGbfsDual,
            SearchAlgorithm::Alt,
        ] {
            let params = Parameters {
                search_algorithm: algorithm,
                heuristic: Heuristic::parse("ADD/UCPOP").unwrap(),
                search_limits: vec![1_000],
                ..Parameters::default()
            };
            let (outcome, stats) = solve_with_params(&task, &params).unwrap();
            let Outcome::Solved(solution) = outcome else {
                panic!("{algorithm:?} did not solve the finite-domain task");
            };
            assert_eq!(solution.operators, vec![0, 1]);
            if algorithm != SearchAlgorithm::Bfs {
                assert!(stats.h_evals > 0);
            }
        }
    }

    #[test]
    fn parsed_flaw_orders_drive_fdr_refinement() {
        let task = travel_task();
        for order in ["LCFR", "ZLIFO", "MC"] {
            let params = Parameters {
                flaw_orders: vec![FlawSelectionOrder::parse(order).unwrap()],
                search_limits: vec![1_000],
                ..Parameters::default()
            };
            let (outcome, _) = solve_with_params(&task, &params).unwrap();
            assert!(matches!(outcome, Outcome::Solved(_)), "order {order}");
        }
    }

    #[test]
    fn generated_node_limit_is_enforced() {
        let task = travel_task();
        let (outcome, stats) = solve(&task, 1);
        assert!(matches!(outcome, Outcome::LimitReached));
        assert_eq!(stats.nodes_generated, 1);
    }

    #[test]
    fn search_continues_with_the_next_flaw_order_after_a_limit() {
        let task = travel_task();
        let params = Parameters {
            flaw_orders: vec![
                FlawSelectionOrder::parse("UCPOP").unwrap(),
                FlawSelectionOrder::parse("LCFR").unwrap(),
            ],
            search_limits: vec![1, 1_000],
            ..Parameters::default()
        };
        let (outcome, stats) = solve_with_params(&task, &params).unwrap();
        assert!(matches!(outcome, Outcome::Solved(_)));
        assert!(stats.nodes_generated > 1);
    }

    #[test]
    fn different_assignment_is_an_implicit_threat() {
        assert!(effect_clobbers(0, 2, Fact::new(0, 1)));
        assert!(!effect_clobbers(0, 1, Fact::new(0, 1)));
        assert!(!effect_clobbers(1, 2, Fact::new(0, 1)));

        let task = travel_task();
        let orderings = Rc::new(BinaryOrderings::new());
        let orderings = orderings
            .refine_with_step(
                Ordering::new(1, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                1,
            )
            .unwrap();
        let orderings = orderings
            .refine_with_step(
                Ordering::new(2, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                2,
            )
            .unwrap();
        let plan = PartialPlan {
            steps: Rc::new(vec![
                Step { id: 1, operator: 0 },
                Step { id: 2, operator: 1 },
            ]),
            links: Rc::new(vec![CausalLink {
                producer: 1,
                consumer: GOAL_ID,
                condition: Fact::new(0, 1),
                effect: Some(0),
            }]),
            open_conditions: Rc::new(vec![]),
            orderings,
            threats: Rc::new(vec![Threat {
                step: 2,
                effect: 0,
                link: 0,
            }]),
            suppressed: Rc::new(vec![]),
            disjunctions: Rc::new(Vec::new()),
            edelete: None,
            cost: 2,
            next_step_id: 3,
            id: 0,
        };
        let threats = plan.threats(&task);
        assert_eq!(threats, plan.rediscover_threats(&task));
        assert_eq!(threats.len(), 1);
        assert_eq!(threats[0].step, 2);

        // Since the link runs to the goal, only demotion is possible: the
        // clobbering assignment must be ordered before the producer.
        let refinements = Planner::new(&task).resolve_threat(&plan, &threats[0]);
        assert_eq!(refinements.len(), 1);
        assert!(refinements[0].threats(&task).is_empty());
        assert_eq!(
            refinements[0].threats(&task),
            refinements[0].rediscover_threats(&task)
        );
        assert!(is_ordered_before(&refinements[0].orderings, 2, 1));
    }

    #[test]
    fn confrontation_resolves_a_threat_no_ordering_can_fix() {
        let task = breaker_task();
        for algorithm in [
            SearchAlgorithm::A,
            SearchAlgorithm::Gbfs,
            SearchAlgorithm::Bfs,
        ] {
            let params = Parameters {
                search_algorithm: algorithm,
                heuristic: Heuristic::parse("ADD").unwrap(),
                search_limits: vec![10_000],
                ..Parameters::default()
            };
            let (outcome, _) = solve_with_params(&task, &params).unwrap();
            let Outcome::Solved(solution) = outcome else {
                panic!("{algorithm:?} did not solve the breaker task");
            };
            let position = |operator: usize| {
                solution
                    .operators
                    .iter()
                    .position(|&chosen| chosen == operator)
                    .unwrap_or_else(|| panic!("{algorithm:?} omitted operator {operator}"))
            };
            // `make-safe` must precede `run`, or `run` trips the breaker.
            assert!(
                position(2) < position(1),
                "{algorithm:?} ran before making safe"
            );
            assert!(
                position(0) < position(1),
                "{algorithm:?} ran before powering on"
            );
            assert!(solution.plan.complete(&task));
        }
    }

    #[test]
    fn confrontation_is_the_only_resolver_of_a_trapped_conditional_effect() {
        let task = breaker_task();
        let planner = Planner::new(&task);
        let (plan, threat) = trapped_breaker_plan();
        assert_eq!(plan.threats(&task), plan.rediscover_threats(&task));

        // Promotion cannot follow the goal and demotion contradicts `run`'s own
        // ordering, so the only alternative value of `mode` is left.
        assert_eq!(
            planner.confrontations(&plan, &threat),
            vec![Fact::new(2, 1)]
        );
        let children = planner.resolve_threat(&plan, &threat);
        assert_eq!(children.len(), 1);
        let child = &children[0];
        assert_eq!(
            *child.open_conditions,
            vec![OpenCondition {
                consumer: 2,
                condition: Fact::new(2, 1),
            }]
        );
        assert!(child.threats(&task).is_empty());
        assert_eq!(child.threats(&task), child.rediscover_threats(&task));
        assert!(child.effect_cannot_fire(&task, &child.steps[1], 1));

        // The suppressed assignment is no longer available as a producer:
        // reusing `run` to switch the power off drops out of the refinement
        // count.
        let switch_off = OpenCondition {
            consumer: GOAL_ID,
            condition: Fact::new(0, 0),
        };
        assert_eq!(
            planner.open_refinement_count(child, &switch_off) + 1,
            planner.open_refinement_count(&plan, &switch_off)
        );
    }

    #[test]
    fn a_step_committed_to_a_condition_value_has_no_confrontation() {
        let task = breaker_task();
        let planner = Planner::new(&task);
        let (mut plan, threat) = trapped_breaker_plan();
        Rc::make_mut(&mut plan.open_conditions).push(OpenCondition {
            consumer: 2,
            condition: Fact::new(2, 0),
        });

        // `run` already requires `mode = unsafe`, so no alternative value is
        // consistent and the threat is a dead end.
        assert!(planner.confrontations(&plan, &threat).is_empty());
        assert!(planner.resolve_threat(&plan, &threat).is_empty());
        assert_eq!(plan.threats(&task), plan.rediscover_threats(&task));
    }

    #[test]
    fn a_contradicted_condition_is_never_a_threat() {
        let task = breaker_task();
        let (mut plan, _) = trapped_breaker_plan();
        Rc::make_mut(&mut plan.open_conditions).push(OpenCondition {
            consumer: 2,
            condition: Fact::new(2, 1),
        });
        plan.retain_active_threats(&task);

        // With `mode = safe` demanded at `run`, the conditional assignment can
        // never fire and is not reported as a threat at all.
        assert!(plan.threats(&task).is_empty());
        assert_eq!(plan.threats(&task), plan.rediscover_threats(&task));
    }

    #[test]
    fn adding_a_link_discovers_threats_incrementally() {
        let task = travel_task();
        let orderings = Rc::new(BinaryOrderings::new())
            .refine_with_step(
                Ordering::new(1, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                1,
            )
            .unwrap();
        let open = OpenCondition {
            consumer: GOAL_ID,
            condition: Fact::new(0, 1),
        };
        let plan = PartialPlan {
            steps: Rc::new(vec![Step { id: 1, operator: 1 }]),
            links: Rc::new(vec![]),
            open_conditions: Rc::new(vec![open.clone()]),
            orderings,
            threats: Rc::new(vec![]),
            suppressed: Rc::new(vec![]),
            disjunctions: Rc::new(Vec::new()),
            edelete: None,
            cost: 1,
            next_step_id: 2,
            id: 0,
        };
        let planner = Planner::new(&task);
        let child = planner
            .add_step(
                &plan,
                0,
                &open,
                &Achiever {
                    operator: 0,
                    effect: 0,
                },
            )
            .unwrap();
        assert_eq!(child.threats(&task), child.rediscover_threats(&task));
        assert_eq!(child.threats.len(), 1);
        assert_eq!(child.threats[0].step, 1);

        let resolved = planner.resolve_threat(&child, &child.threats[0]);
        assert_eq!(resolved.len(), 1);
        assert!(resolved[0].threats.is_empty());
        assert_eq!(
            resolved[0].threats(&task),
            resolved[0].rediscover_threats(&task)
        );
    }
}
