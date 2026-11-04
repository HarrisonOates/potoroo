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
use std::cell::Cell;
use std::cmp::Ordering as CmpOrdering;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::rc::Rc;
use std::time::Instant;

use thiserror::Error;

use crate::chain::{self, Chain};
use crate::external::FdError;
use crate::fasthash::{FastMap, FastSet};
use crate::fdr::{Fact, ParseError, Task};
use crate::heuristics::{HVal, Heuristic, OrderType, SelectionCriterion};
use crate::lmcut::{BuildError as LmCutBuildError, FdrLmCut};
use crate::orderings::{BinaryOrderings, Ordering, StepTime};
use crate::params::{ActionCost, Parameters, SearchAlgorithm};
use crate::plan::{GOAL_ID, INIT_ID};
use crate::rank::{Rank, RankTerm};
use crate::search::{SearchContext, SearchProgress};

/// A committed real step. Init and goal are represented by [`INIT_ID`] and
/// [`GOAL_ID`] and are not stored in this vector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Step {
    pub id: usize,
    pub operator: usize,
}

/// A finite-domain causal link `producer --(variable=value)--> consumer`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Threat {
    pub step: usize,
    /// Index of the clobbering effect, or [`NO_EFFECT`] for a precondition-based
    /// e-deletion threat.
    pub effect: usize,
    pub link: usize,
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

/// A finite-domain POCL search node.
///
/// Steps, links, and open conditions share persistent chains with ancestors.
/// Threats retain discovery order to preserve flaw-selection ties.
#[derive(Debug, Clone)]
pub struct PartialPlan {
    steps: Option<Rc<Chain<Step>>>,
    num_steps: usize,
    links: Option<Rc<Chain<CausalLink>>>,
    num_links: usize,
    open_conditions: Option<Rc<Chain<OpenCondition>>>,
    num_open_conditions: usize,
    pub orderings: Rc<BinaryOrderings>,
    /// Potential conflicts under the concrete orderings and effect guards.
    /// A posted disjunction leaves its source here until an ordering or guard
    /// commitment resolves it; `threat_covered` excludes that source from selection.
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
    /// Set once the search has expanded this plan; see `Plan::expanded`.
    expanded: Cell<bool>,
}

impl PartialPlan {
    pub fn initial(task: &Task) -> Self {
        let mut plan = PartialPlan {
            steps: None,
            num_steps: 0,
            links: None,
            num_links: 0,
            open_conditions: None,
            num_open_conditions: 0,
            orderings: Rc::new(BinaryOrderings::new()),
            threats: Rc::new(Vec::new()),
            suppressed: Rc::new(Vec::new()),
            cost: 0,
            disjunctions: Rc::new(Vec::new()),
            edelete: None,
            next_step_id: 1,
            id: 0,
            expanded: Cell::new(false),
        };
        for &condition in &task.goals {
            plan.push_open(OpenCondition {
                consumer: GOAL_ID,
                condition,
            });
        }
        plan
    }

    /// A plan assembled from its parts, in insertion order, for tests that
    /// need a specific shape without refining their way to it.
    #[cfg(test)]
    fn assemble(
        steps: Vec<Step>,
        links: Vec<CausalLink>,
        open_conditions: Vec<OpenCondition>,
        orderings: Rc<BinaryOrderings>,
        threats: Vec<Threat>,
        cost: usize,
        next_step_id: usize,
    ) -> Self {
        let mut plan = PartialPlan {
            steps: None,
            num_steps: 0,
            links: None,
            num_links: 0,
            open_conditions: None,
            num_open_conditions: 0,
            orderings,
            threats: Rc::new(threats),
            suppressed: Rc::new(Vec::new()),
            cost,
            disjunctions: Rc::new(Vec::new()),
            edelete: None,
            next_step_id,
            id: 0,
            expanded: Cell::new(false),
        };
        for step in steps {
            plan.push_step(step);
        }
        for link in links {
            plan.push_link(link);
        }
        for open in open_conditions {
            plan.push_open(open);
        }
        plan
    }

    pub fn complete(&self, _task: &Task) -> bool {
        // Covered threats still witness unresolved ordering disjunctions.
        self.num_open_conditions == 0 && self.threats.is_empty()
    }

    /// The committed steps, newest first.
    pub fn steps(&self) -> chain::Iter<'_, Step> {
        chain::iter(&self.steps)
    }

    /// The causal links, newest first. A link's index — the handle a
    /// [`Threat`] carries — counts from the oldest, so the newest link has
    /// index `num_links() - 1`.
    pub fn links(&self) -> chain::Iter<'_, CausalLink> {
        chain::iter(&self.links)
    }

    /// The open conditions, newest first.
    pub fn open_conditions(&self) -> chain::Iter<'_, OpenCondition> {
        chain::iter(&self.open_conditions)
    }

    pub fn num_links(&self) -> usize {
        self.num_links
    }

    /// The link with the given index, which is `num_links - 1 - index` hops
    /// from the newest. Threats mostly concern recent links, so the walk is
    /// short where it is frequent.
    pub fn link(&self, index: usize) -> Option<&CausalLink> {
        let hops = self.num_links.checked_sub(index + 1)?;
        self.links().nth(hops)
    }

    /// The link a threat stands against. Threats are only ever created from
    /// links of the same plan, and links are never removed.
    pub fn threatened_link(&self, threat: &Threat) -> &CausalLink {
        self.link(threat.link)
            .expect("a threat refers to a link of its own plan")
    }

    fn push_step(&mut self, step: Step) {
        self.steps = chain::cons(step, self.steps.take());
        self.num_steps += 1;
    }

    fn push_link(&mut self, link: CausalLink) {
        self.links = chain::cons(link, self.links.take());
        self.num_links += 1;
    }

    /// Discharges an open condition. Removal rebuilds the chain down to the
    /// element, so it is cheapest for the newest conditions — which is where
    /// the LIFO orders look first.
    fn remove_open(&mut self, open: &OpenCondition) {
        debug_assert!(chain::contains(&self.open_conditions, open));
        self.open_conditions = chain::remove(&self.open_conditions, open);
        self.num_open_conditions -= 1;
    }

    /// Cached threats, cloned for compatibility with callers that previously
    /// requested a freshly discovered threat vector.
    pub fn threats(&self, _task: &Task) -> Vec<Threat> {
        (*self.threats).clone()
    }

    #[cfg(test)]
    fn rediscover_threats(&self, task: &Task) -> Vec<Threat> {
        let mut threats = Vec::new();
        let links: Vec<&CausalLink> = self.links().collect();
        let steps: Vec<&Step> = self.steps().collect();
        for (link_index, link) in links.iter().rev().enumerate() {
            for &step in steps.iter().rev() {
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
        // Independent full discovery followed by dominance filtering, rather
        // than the incremental collector's early exits.
        let mut coalesced = Vec::new();
        for group in threats.chunk_by(|a, b| a.link == b.link && a.step == b.step) {
            let unavoidable = group.iter().find(|threat| {
                threat.effect == NO_EFFECT
                    || task.operators[self.step(threat.step).unwrap().operator].effects
                        [threat.effect]
                        .conditions
                        .is_empty()
            });
            if let Some(threat) = unavoidable {
                coalesced.push(*threat);
            } else {
                coalesced.extend_from_slice(group);
            }
        }
        coalesced
    }

    /// The committed step with the given id. Steps are only ever appended and
    /// ids are dense, so the step sits `num_steps - id` hops from the newest.
    fn step(&self, id: usize) -> Option<&Step> {
        let hops = self.num_steps.checked_sub(id)?;
        self.steps().nth(hops).filter(|step| step.id == id)
    }

    /// Whether `step` is already committed to a value of `fact`'s variable
    /// other than `fact.value`. Open conditions count as commitments: they are
    /// only ever discharged by a causal link carrying the very same equality,
    /// and a finite-domain variable holds one value at a time.
    fn step_excludes(&self, step: usize, fact: Fact) -> bool {
        let conflicts =
            |condition: Fact| condition.variable == fact.variable && condition.value != fact.value;
        self.open_conditions()
            .any(|open| open.consumer == step && conflicts(open.condition))
            || self
                .links()
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
    /// selection must leave it alone. All reasons involving the same step and
    /// link endpoints require the same ordering. The source threat stays in
    /// the cache: if its conditional guard is disabled, settling retires its
    /// disjunction and any remaining reasons become selectable again.
    fn threat_covered(&self, threat: &Threat) -> bool {
        self.disjunctions.iter().any(|disjunction| {
            if disjunction.threat.1 != threat.step {
                return false;
            }
            if disjunction.threat.0 == threat.link {
                return true;
            }
            let link = self.threatened_link(threat);
            disjunction.promote.0 == link.consumer && disjunction.demote.1 == link.producer
        })
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
    /// Returns whether propagation added an ordering, or `Err(())` when the
    /// plan is inconsistent and must be discarded.
    fn propagate_disjunctions(&mut self) -> Result<bool, ()> {
        let mut ordering_changed = false;
        if self.disjunctions.is_empty() {
            return Ok(ordering_changed);
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
                    (OrderingStatus::Impossible, OrderingStatus::Impossible) => return Err(()),
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
                return Ok(ordering_changed);
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
                    return Err(());
                };
                self.orderings = orderings;
                ordering_changed = true;
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
    /// would over-constrain the plan. Called only after retaining active threats,
    /// whose sorted cache already supplies the liveness test.
    fn retain_live_disjunctions(&mut self) {
        let live = |disjunction: &OrderingDisjunction| {
            self.threats
                .binary_search_by_key(&disjunction.threat, threat_key)
                .is_ok()
        };
        let Some(first_dead) = self.disjunctions.iter().position(|d| !live(d)) else {
            return;
        };
        let mut retained = Vec::with_capacity(self.disjunctions.len() - 1);
        retained.extend_from_slice(&self.disjunctions[..first_dead]);
        retained.extend(
            self.disjunctions[first_dead + 1..]
                .iter()
                .filter(|d| live(d))
                .cloned(),
        );
        self.disjunctions = Rc::new(retained);
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
        if !chain::contains(&self.open_conditions, &open) {
            self.open_conditions = chain::cons(open, self.open_conditions.take());
            self.num_open_conditions += 1;
        }
    }

    fn threat_active(&self, task: &Task, threat: &Threat) -> bool {
        let Some(link) = self.link(threat.link) else {
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
        self.retain_live_disjunctions();
        let Ok(ordering_changed) = self.propagate_disjunctions() else {
            return false;
        };
        // Guards and steps do not change during propagation. Only a new
        // ordering can invalidate the threats we just checked.
        if ordering_changed {
            self.retain_active_threats(task);
            self.retain_live_disjunctions();
        }
        true
    }

    fn retain_active_threats(&mut self, task: &Task) {
        let Some(first_dead) = self
            .threats
            .iter()
            .position(|threat| !self.threat_active(task, threat))
        else {
            return;
        };
        let mut active = Vec::with_capacity(self.threats.len() - 1);
        active.extend_from_slice(&self.threats[..first_dead]);
        active.extend(
            self.threats[first_dead + 1..]
                .iter()
                .filter(|threat| self.threat_active(task, threat))
                .copied(),
        );
        self.threats = Rc::new(active);
    }

    /// Collect threats for one step/link pair. An unconditional effect or
    /// conflicting precondition requires ordering the step outside the link,
    /// which also resolves every conditional reason in this pair. Otherwise
    /// retain each conditional effect's distinct guard-disabling alternative.
    fn collect_link_threats(
        &self,
        task: &Task,
        step: &Step,
        link: &CausalLink,
        link_index: usize,
        additions: &mut Vec<Threat>,
    ) {
        if step.id == link.producer
            || step.id == link.consumer
            || !self.can_be_inside(step.id, link)
        {
            return;
        }
        let start = additions.len();
        for (effect_index, effect) in task.operators[step.operator].effects.iter().enumerate() {
            if effect_e_deletes(effect, link.condition, self.edelete.as_deref())
                && !self.effect_cannot_fire(task, step, effect_index)
            {
                if effect.conditions.is_empty() {
                    additions.truncate(start);
                }
                additions.push(Threat {
                    step: step.id,
                    effect: effect_index,
                    link: link_index,
                });
                if effect.conditions.is_empty() {
                    return;
                }
            }
        }
        if self.edelete.as_deref().is_some_and(|mutexes| {
            precondition_e_deletes(&task.operators[step.operator], link.condition, mutexes)
        }) {
            additions.truncate(start);
            additions.push(Threat {
                step: step.id,
                effect: NO_EFFECT,
                link: link_index,
            });
        }
    }

    fn add_link_threats(&mut self, task: &Task, link_index: usize) {
        debug_assert_eq!(link_index + 1, self.num_links);
        let link = *self.threatened_link(&Threat {
            step: 0,
            effect: 0,
            link: link_index,
        });
        let link = &link;
        let mut additions = Vec::new();
        for step in self.steps() {
            self.collect_link_threats(task, step, link, link_index, &mut additions);
        }
        // Steps were visited newest first; the cache is kept in discovery
        // order, which is ascending `(link, step, effect)`.
        additions.sort_by_key(threat_key);
        debug_assert!(self
            .threats
            .last()
            .zip(additions.first())
            .is_none_or(|(existing, addition)| threat_key(existing) < threat_key(addition)));
        extend_cow(&mut self.threats, additions);
    }

    fn add_step_threats(&mut self, task: &Task, step_id: usize) {
        let step = *self.step(step_id).expect("the step was just added");
        let step = &step;
        let mut additions = Vec::new();
        let num_links = self.num_links;
        for (position, link) in self.links().enumerate() {
            let link_index = num_links - 1 - position;
            self.collect_link_threats(task, step, link, link_index, &mut additions);
        }
        if additions.is_empty() {
            return;
        }

        // The brute-force discovery order is link, then step, then effect. A
        // newly added step can threaten old links, so merge those entries into
        // the cached order instead of simply appending them. Flaw-selection
        // tie-breaking therefore remains identical to full rediscovery.
        additions.sort_by_key(threat_key);
        let existing = &self.threats;
        let mut merged = Vec::with_capacity(existing.len() + additions.len());
        let mut existing_index = 0;
        for addition in additions {
            while existing_index < existing.len()
                && threat_key(&existing[existing_index]) < threat_key(&addition)
            {
                merged.push(existing[existing_index]);
                existing_index += 1;
            }
            merged.push(addition);
        }
        merged.extend(existing[existing_index..].iter().cloned());
        self.threats = Rc::new(merged);
    }

    pub fn num_steps(&self) -> usize {
        self.num_steps
    }

    pub fn cost(&self) -> usize {
        self.cost
    }

    pub fn num_open_conditions(&self) -> usize {
        self.num_open_conditions
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
    /// Forced support refinements performed without allocating a queue entry.
    pub supporter_forced: usize,
    pub h2: crate::h2::Stats,
    pub max_steps: usize,
    pub max_open_conditions: usize,
    pub max_threats: usize,
    /// Peak number of ordering disjunctions held on a single plan. Zero unless
    /// `-p disjunctive` is on; a nonzero value is the evidence that threat
    /// resolution is being deferred rather than branched on.
    pub max_disjunctions: usize,
    pub max_queued: usize,
    /// Queued plans discarded by an open-list bound; see [`crate::memory`].
    pub dropped: usize,
    /// Why the search stopped short, when a budget rather than the search
    /// itself ended it. See [`crate::memory::SearchStop`].
    pub stopped: Option<crate::memory::StopReason>,
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
    solve_with_context(task, params, None, None)
}

/// Like [`solve_with_params`], while also reporting a representation-neutral
/// snapshot after each node expansion.
pub fn solve_with_params_and_progress(
    task: &Task,
    params: &Parameters,
    progress: &mut dyn FnMut(SearchProgress),
) -> Result<(Outcome, SearchStats), Error> {
    solve_with_context(task, params, None, Some(progress))
}

/// The general entry point: `symmetries` are the task's interchangeable
/// objects, consulted only under `-p symmetry`. The SAS+ task carries only
/// operator names, so the caller computes them from the lowered PDDL
/// (`SearchContext::object_symmetries`).
pub fn solve_with_context(
    task: &Task,
    params: &Parameters,
    symmetries: Option<&crate::symmetry::ObjectSymmetries>,
    progress: Option<&mut dyn FnMut(SearchProgress)>,
) -> Result<(Outcome, SearchStats), Error> {
    let planner = Planner::with_action_cost(task, params.action_cost);
    planner.validate_params(params)?;
    let planner = planner
        .with_pruning_params(params)
        .with_symmetries(params.prune.symmetry.then_some(symmetries).flatten());
    let (outcome, mut stats) = planner.solve(params, progress);
    stats.pruned += planner.symmetry_skipped.get();
    Ok((outcome, stats))
}

/// Whether the finite-domain representation can run this heuristic at all,
/// independently of any task.
///
/// The command line uses this to reject a configuration the moment it is
/// parsed, alongside the mirror-image [`Heuristic::requires_fdr_pocl`] check:
/// a `--stage` portfolio must not discover after its first stage has spent its
/// share of the clock that its second names a heuristic this representation
/// has never been able to evaluate.
pub fn supports_heuristic(heuristic: &Heuristic) -> Result<(), Error> {
    for term in heuristic.terms() {
        if matches!(
            term,
            HVal::SampleFf(_) | HVal::Lplan(_) | HVal::Lpsas(_) | HVal::Compile(_)
        ) {
            return Err(Error::Unsupported(
                "SAMPLE_FF, LPLAN, and COMPILE heuristics operate on the literal plan representation"
                    .to_string(),
            ));
        }
    }
    Ok(())
}

/// Checks that every one of these parameter sets can be searched over this
/// task, without searching any of them.
///
/// The rest of what [`Planner::validate_params`] looks at is task-dependent —
/// whether the LM-cut structure could be built at all, say — so a portfolio
/// runs its whole sequence through this before starting the first stage. The
/// tables a planner holds depend on the task, the action cost and the pruning
/// rules, every one of which a portfolio's stages share, so one planner
/// answers for all of them.
pub fn validate_all(task: &Task, stages: &[Parameters]) -> Result<(), Error> {
    let Some(first) = stages.first() else {
        return Ok(());
    };
    // Preflight checks configurations only. Do not spend a preprocessing
    // budget here; the stage that searches owns its time and memory limits.
    let planner = Planner::with_action_cost(task, first.action_cost);
    for params in stages {
        planner.validate_params(params)?;
    }
    Ok(())
}

#[derive(Debug, Clone, Copy)]
struct Achiever {
    operator: usize,
    effect: usize,
}

/// Open-condition prefixes shared only while producing new-step siblings.
/// Every sibling has the same new consumer and inherited tail. A node can be
/// reused exactly when both its fact and its tail match; the cache owns each
/// node, keeping the tail addresses used as keys valid until it is dropped.
struct NewStepOpenConditions {
    consumer: usize,
    tail: Option<Rc<Chain<OpenCondition>>>,
    inherited_count: usize,
    share: bool,
    prefixes: FastMap<(Fact, *const Chain<OpenCondition>), Rc<Chain<OpenCondition>>>,
}

impl NewStepOpenConditions {
    fn new(plan: &PartialPlan, open: &OpenCondition, share: bool) -> Self {
        let mut base = plan.clone();
        base.remove_open(open);
        Self {
            consumer: plan.next_step_id,
            tail: base.open_conditions,
            inherited_count: base.num_open_conditions,
            share,
            prefixes: FastMap::default(),
        }
    }

    /// Requirements are already deduplicated in their original insertion
    /// order. The consumer is fresh, so none can occur in the inherited tail.
    fn extend(&mut self, requirements: &[Fact]) -> (Option<Rc<Chain<OpenCondition>>>, usize) {
        let mut tail = self.tail.clone();
        for &condition in requirements {
            let make_node = || {
                Chain::new(
                    OpenCondition {
                        consumer: self.consumer,
                        condition,
                    },
                    tail.clone(),
                )
            };
            let node = if self.share {
                let address = tail.as_ref().map_or(std::ptr::null(), Rc::as_ptr);
                self.prefixes
                    .entry((condition, address))
                    .or_insert_with(make_node)
                    .clone()
            } else {
                make_node()
            };
            tail = Some(node);
        }
        (tail, self.inherited_count + requirements.len())
    }
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
    /// Feasibility checks for the optional supporter propagation rule.
    support_mutexes: Option<Rc<crate::cutset::FactMutexes>>,
    cutset_mutexes: Option<Rc<crate::cutset::FactMutexes>>,
    h2: crate::h2::Stats,
    /// Whether threats are resolved by posting a disjunction instead of by
    /// splitting the plan.
    disjunctive: bool,
    /// The task's operator graph over facts, for the recursion rule. Built only
    /// when `-p recursion` asks for it.
    fact_graph: Option<crate::fdr_pruning::FactGraph>,
    /// The compiled relaxation behind `CLADD`/`CLFF`; see [`crate::cl_relax`].
    compiled: crate::cl_relax::CompiledRelaxation,
    /// The task's fact landmarks, for `LM`; see
    /// [`crate::cl_relax::CompiledRelaxation::fact_landmarks`].
    landmarks: Vec<Fact>,
    /// Whether non-minimality pruning is on.
    minimality: bool,
    /// Interchangeable objects laid out over the operators, when `-p symmetry`
    /// is on and the task has any. See [`crate::symmetry`].
    symmetry: Option<crate::symmetry::SymmetryTable>,
    /// Achievers skipped as non-canonical, folded into `pruned` at the end.
    symmetry_skipped: Cell<usize>,
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
        let compiled =
            crate::cl_relax::CompiledRelaxation::new(task, &effect_requirements, action_cost);
        let landmarks = compiled.fact_landmarks();
        Planner {
            task,
            achievers,
            variable_has_effect,
            operator_preconditions,
            effect_requirements,
            compiled,
            landmarks,
            derived_supports,
            base_relaxed,
            lmcut,
            action_cost,
            edelete: None,
            support_mutexes: None,
            cutset_mutexes: None,
            h2: crate::h2::Stats::default(),
            disjunctive: false,
            fact_graph: None,
            minimality: false,
            symmetry: None,
            symmetry_skipped: Cell::new(0),
        }
    }

    /// Installs the interchangeable-object classes, indexed by the objects
    /// each operator's name lists: the translator writes an operator as its
    /// schema name followed by its arguments.
    fn with_symmetries(mut self, symmetries: Option<&crate::symmetry::ObjectSymmetries>) -> Self {
        if let Some(symmetries) = symmetries.filter(|s| !s.is_empty()) {
            let table = crate::symmetry::SymmetryTable::from_names(
                symmetries,
                self.task
                    .operators
                    .iter()
                    .map(|operator| operator.name.split_whitespace().skip(1)),
            );
            self.symmetry = Some(table);
        }
        self
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
                | HVal::RelaxR
                | HVal::ClAdd
                | HVal::ClFf
                | HVal::Landmarks { .. } => {}
                HVal::LmCut | HVal::LmCutR => {
                    if let Err(error) = &self.lmcut {
                        return Err(Error::Unsupported(error.to_string()));
                    }
                }
                HVal::SampleFf(_) | HVal::Lplan(_) | HVal::Lpsas(_) | HVal::Compile(_) => {
                    return Err(Error::Unsupported(
                        "SAMPLE_FF, LPLAN, and COMPILE heuristics operate on the literal plan representation"
                            .to_string(),
                    ));
                }
            }
        }
        Ok(())
    }

    #[cfg(test)]
    fn with_pruning(self, prune: crate::pruning::PruneOptions) -> Self {
        self.with_pruning_params(&Parameters {
            prune,
            ..Parameters::default()
        })
    }

    /// Build one shared table for cutsets, e-deletion and supporter checks.
    /// h² is optional and discards unfinished preprocessing results.
    fn with_pruning_params(mut self, params: &Parameters) -> Self {
        let prune = params.prune;
        if prune.cutset || prune.edelete || prune.supporters || prune.h2 {
            let table = if prune.h2 {
                let mut stop = crate::memory::SearchStop::new(params);
                let (table, stats) =
                    crate::h2::compute(self.task, crate::h2::Limits::default(), |work| {
                        stop.as_mut().and_then(|s| s.expired(work))
                    });
                self.h2 = stats;
                if stats.status.stopped().is_some() {
                    return self;
                }
                // A completed table that only rediscovers declared pairs adds
                // no pruning power. Keep its statistics, but avoid retaining
                // and querying a redundant matrix throughout the search.
                table.filter(|_| stats.new_mutex_pairs > 0 || stats.unreachable_facts > 0)
            } else {
                None
            };
            let mutexes = Rc::new(crate::cutset::FactMutexes::new(self.task).with_h2(table));
            if prune.cutset || prune.h2 {
                self.cutset_mutexes = Some(mutexes.clone());
            }
            if prune.edelete {
                self.edelete = Some(mutexes.clone());
            }
            if prune.supporters || prune.h2 {
                // All applicability conditions and the selected effect's guards
                // must coexist. Removing these templates preserves operator ids
                // and still permits any number of fresh action occurrences.
                for achievers in self.achievers.values_mut() {
                    let before = achievers.len();
                    achievers.retain(|achiever| {
                        let required: Vec<_> = self.effect_requirements[achiever.operator]
                            [achiever.effect]
                            .iter()
                            .copied()
                            .filter(|fact| !self.task.is_derived_variable(fact.variable))
                            .collect();
                        !mutexes.inconsistent(&required)
                    });
                    if prune.h2 {
                        self.h2.supporters_removed += before - achievers.len();
                    }
                }
                self.support_mutexes = Some(mutexes);
            }
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
        let mut progress_memory = crate::memory::ProgressMemory::default();
        let n_orders = params.flaw_orders.len();
        let inf = RankTerm::INFINITY;
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

        let mut stats = SearchStats {
            h2: self.h2,
            ..SearchStats::default()
        };
        if let Some(reason) = self.h2.status.stopped() {
            stats.stopped = Some(reason);
            return (Outcome::LimitReached, stats);
        }
        let cutset_mutexes = self.cutset_mutexes.as_deref();
        if let Some(mutexes) = &cutset_mutexes {
            // The goal step's pre-cutset is the task goals, and no link can span
            // the goal, so it is plan-independent: check it once.
            if crate::cutset::goals_inconsistent(self.task, mutexes) {
                return (Outcome::NoSolution, stats);
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
        let mut generated_per_order = vec![0usize; n_orders];
        let mut bound = crate::memory::OpenListBound::new(params);
        let mut stop = crate::memory::SearchStop::new(params);
        // Which budget ended the search, if one did. A stop is a restart, not
        // a prune: nothing queued has been discarded.
        let mut stopped: Option<crate::memory::StopReason> = None;
        // The stop is consulted wherever the loop takes another plan off a
        // queue, not only where it expands one: a complete plan that fails to
        // linearize pops its successor and goes round again without expanding
        // anything, and a search that spends its whole budget on such a run
        // must still honour it.
        macro_rules! stop_expired {
            () => {
                match stop.as_mut() {
                    Some(stop) => {
                        stop.expired(stats.nodes_visited.saturating_add(stats.supporter_forced))
                    }
                    None => None,
                }
            };
        }
        let mut current_order = 0usize;
        let mut orders_left = n_orders;
        let mut next_switch = 1_000usize;
        let mut limit_reached = false;
        let mut best_h = inf;
        let mut boost_budget = 0usize;
        let mut expand_count = 0usize;
        let mut current_rank0 = RankTerm::ZERO;

        generated_per_order[0] = 1;
        stats.nodes_generated = 1;
        let mut current_plan = Some(initial.clone());
        let mut f_limit = if is_ida {
            self.rank_both(&initial, params, &mut stats)
                .0
                .primary(initial.id)
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
                        params,
                        is_lazy,
                        is_gbfs,
                        is_dual,
                        is_alt,
                        &mut boost_budget,
                        &mut expand_count,
                        &mut stats,
                    );
                    if let Some(reason) = stop_expired!() {
                        stopped = Some(reason);
                        break;
                    }
                    continue;
                }

                if let Some(reason) = stop_expired!() {
                    stopped = Some(reason);
                    break;
                }
                stats.nodes_visited += 1;
                stats.max_steps = stats.max_steps.max(plan.num_steps());
                stats.max_open_conditions =
                    stats.max_open_conditions.max(plan.num_open_conditions());
                stats.max_threats = stats.max_threats.max(plan.threats.len());
                stats.max_disjunctions = stats.max_disjunctions.max(plan.pending_disjunctions());
                if is_dual || is_alt {
                    plan.expanded.set(true);
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
                    if params.prune.supporters {
                        if let Some(reason) = stop_expired!() {
                            stopped = Some(reason);
                            break;
                        }
                        let remaining = params.search_limits[order_index]
                            .saturating_sub(generated_per_order[order_index])
                            .saturating_sub(1);
                        let before = stats.supporter_forced;
                        let propagated =
                            self.propagate_supporters(child, params, remaining, &mut stats);
                        let forced = stats.supporter_forced - before;
                        // A refinement still consumes the node budget when its
                        // queue entry is elided. Otherwise a small node limit
                        // could hide thousands of recursive action insertions.
                        stats.nodes_generated += forced;
                        generated_per_order[order_index] += forced;
                        if let Some(reason) = stop_expired!() {
                            stopped = Some(reason);
                            break;
                        }
                        let Some(propagated) = propagated else {
                            stats.pruned += 1;
                            continue;
                        };
                        child = propagated;
                    }
                    if let Some(mutexes) = &cutset_mutexes {
                        if crate::cutset::has_inconsistent_cutset(&child, self.task, mutexes) {
                            stats.pruned += 1;
                            continue;
                        }
                    }
                    if self.has_unresolvable_threat(&child) {
                        stats.pruned += 1;
                        continue;
                    }
                    if self.structurally_pruned(&child) {
                        stats.pruned += 1;
                        continue;
                    }
                    child.id = stats.nodes_generated;
                    // A child is a clone of its parent, which is being
                    // expanded right now.
                    child.expanded = Cell::new(false);
                    let child = Rc::new(child);
                    let mut alt_gbfs_rank = None;
                    let (rank, lazy_push) = if is_bfs {
                        (Rank::bfs(child.num_steps(), child.id), false)
                    } else if is_lazy {
                        if params.heuristic.needs_planning_graph()
                            && !self.open_estimate(&child, false).cost.is_finite()
                        {
                            stats.pruned += 1;
                            continue;
                        }
                        (
                            Rank::lazy_proxy(current_rank0, child.num_open_conditions(), child.id),
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

                    let primary = rank.primary(child.id);
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
                                rank: Rank::fifo(child.id),
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

                if stopped.is_some() {
                    break;
                }
                let queued = queues.iter().map(BinaryHeap::len).sum();
                stats.max_queued = stats.max_queued.max(queued);
                if let Some(bound) = bound.as_mut() {
                    if let Some(keep) = bound.trim_target(stats.nodes_generated, queued) {
                        stats.dropped += crate::memory::trim_all(&mut queues, keep);
                        crate::memory::trim_all(&mut secondary_queues, keep);
                    }
                }
                if let Some(report) = progress.as_deref_mut() {
                    let elapsed = search_started.elapsed();
                    report(SearchProgress {
                        elapsed,
                        nodes_generated: stats.nodes_generated,
                        nodes_visited: stats.nodes_visited,
                        queued,
                        h_evals: stats.h_evals,
                        h_eval_ms: stats.h_eval_ms,
                        pruned: stats.pruned,
                        dropped: stats.dropped,
                        resident_kb: progress_memory.sample(elapsed),
                        current_steps: plan.num_steps(),
                        current_open_conditions: plan.num_open_conditions(),
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
                    current_rank0 = RankTerm::ZERO;
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

            if current_plan.is_none() && stopped.is_none() {
                stopped = stop_expired!();
            }
            if stopped.is_some() {
                break;
            }
            if orders_left == 0 {
                break;
            }
            f_limit = next_f_limit;
            if is_ida && f_limit.is_finite() {
                current_plan = Some(initial.clone());
                current_rank0 = RankTerm::ZERO;
            } else {
                break;
            }
        }

        // Queues emptied by an open-list bound say nothing about solvability,
        // and neither does a search stopped part-way for time or memory.
        stats.stopped = stopped;
        if stopped.is_some() || limit_reached || stats.dropped > 0 {
            (Outcome::LimitReached, stats)
        } else {
            (Outcome::NoSolution, stats)
        }
    }

    fn resolve_open(&self, plan: &PartialPlan, open: OpenCondition) -> Vec<PartialPlan> {
        if let Some(supports) = self.derived_supports.get(&open.condition) {
            return supports
                .iter()
                .filter_map(|support| {
                    if !self.support_requirements_possible(plan, open.consumer, support) {
                        return None;
                    }
                    let mut child = plan.clone();
                    child.remove_open(&open);
                    for &condition in support {
                        child.push_open(OpenCondition {
                            consumer: open.consumer,
                            condition,
                        });
                    }
                    Some(child)
                })
                .collect();
        }
        let mut children = Vec::new();

        if let Some(achievers) = self.achievers.get(&open.condition) {
            // Emit new steps before reuse. Search uses newest-generated plans as
            // its final GBFS tiebreaker, so this ordering makes reuse win equal
            // heuristic ranks instead of repeatedly inserting the same ground
            // operator.
            //
            // Under `-p symmetry`, a new step may introduce an interchangeable
            // object only if it is the first of its class the plan has not
            // used; the objects a plan uses are exactly its steps' arguments.
            let used = self.symmetry.as_ref().map(|table| {
                let mut used = vec![false; table.len()];
                for step in plan.steps() {
                    table.mark_used(step.operator, &mut used);
                }
                used
            });
            // Every new-step alternative adds the same step id before the
            // same consumer. Share that ordering refinement across siblings;
            // settling a child's disjunctions can still refine its own copy.
            let new_step_orderings = plan.orderings.refine_with_step(
                Ordering::new(
                    plan.next_step_id,
                    StepTime::AtEnd,
                    open.consumer,
                    StepTime::AtStart,
                ),
                plan.next_step_id,
            );
            let mut sibling_open = NewStepOpenConditions::new(plan, &open, achievers.len() > 1);
            let mut sibling_links: FastMap<usize, Rc<Chain<CausalLink>>> = FastMap::default();
            let mut sibling_threats: FastSet<Rc<Vec<Threat>>> = FastSet::default();
            for achiever in achievers {
                if let (Some(table), Some(used)) = (&self.symmetry, &used) {
                    if !table.canonical(achiever.operator, used) {
                        self.symmetry_skipped.set(self.symmetry_skipped.get() + 1);
                        continue;
                    }
                }
                if let Some(orderings) = &new_step_orderings {
                    // The producer id, consumer, fact and tail are identical
                    // across new-step siblings. Only the supporting effect's
                    // index varies; its operator lives in each child's steps.
                    let make_link = || {
                        Chain::new(
                            CausalLink {
                                producer: plan.next_step_id,
                                consumer: open.consumer,
                                condition: open.condition,
                                effect: Some(achiever.effect),
                            },
                            plan.links.clone(),
                        )
                    };
                    let link = if achievers.len() > 1 {
                        sibling_links
                            .entry(achiever.effect)
                            .or_insert_with(make_link)
                            .clone()
                    } else {
                        make_link()
                    };
                    if let Some(mut child) =
                        self.add_step(plan, achiever, orderings.clone(), link, &mut sibling_open)
                    {
                        // Different achievers often introduce the same conflicts.
                        // Keep one copy per sibling group, after independently
                        // computing each child's threats and their discovery order.
                        if achievers.len() > 1 && !child.threats.is_empty() {
                            if let Some(shared) = sibling_threats.get(&child.threats) {
                                child.threats = shared.clone();
                            } else {
                                sibling_threats.insert(child.threats.clone());
                            }
                        }
                        children.push(child);
                    }
                }
            }

            // The regular plan representation stores steps newest-first and
            // emits reuse in that order. Reverse the insertion-ordered vector
            // to preserve the same deterministic preference.
            for step in plan.steps() {
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
                        &open,
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
            if let Some(child) = self.support(plan, &open, INIT_ID, None, &[], open.consumer) {
                children.push(child);
            }
        }
        children
    }

    fn support(
        &self,
        plan: &PartialPlan,
        open: &OpenCondition,
        producer: usize,
        effect: Option<usize>,
        effect_conditions: &[Fact],
        consumer: usize,
    ) -> Option<PartialPlan> {
        let condition = open.condition;
        if !self.support_requirements_possible(plan, producer, effect_conditions) {
            return None;
        }
        let orderings = plan.orderings.refine(Ordering::new(
            producer,
            StepTime::AtEnd,
            consumer,
            StepTime::AtStart,
        ))?;
        let mut child = plan.clone();
        child.orderings = orderings;
        child.remove_open(open);
        let link_index = child.num_links;
        child.push_link(CausalLink {
            producer,
            consumer,
            condition,
            effect,
        });
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
        achiever: &Achiever,
        orderings: Rc<BinaryOrderings>,
        link: Rc<Chain<CausalLink>>,
        open_conditions: &mut NewStepOpenConditions,
    ) -> Option<PartialPlan> {
        let new_id = plan.next_step_id;
        let operator = &self.task.operators[achiever.operator];

        let mut child = plan.clone();
        child.orderings = orderings;
        child.next_step_id += 1;
        child.cost = child
            .cost
            .saturating_add(self.action_cost.resolve(operator.cost));
        child.push_step(Step {
            id: new_id,
            operator: achiever.operator,
        });
        let link_index = child.num_links;
        child.links = Some(link);
        child.num_links += 1;
        (child.open_conditions, child.num_open_conditions) =
            open_conditions.extend(&self.effect_requirements[achiever.operator][achiever.effect]);
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
        let link = plan.threatened_link(threat);
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
                .links()
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
        let link = plan.threatened_link(threat);
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
            SelectedFlaw::Open(open) => self.resolve_open(plan, open),
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
        // The chain is newest first, so the newest open condition is its head;
        // recency counts up from the oldest, as it does for threats.
        let local_consumer = plan.open_conditions().next().map(|open| open.consumer);
        let num_open = plan.num_open_conditions();

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
                            flaw: SelectedFlaw::Threat(*threat),
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
            for (position, open) in plan.open_conditions().enumerate() {
                let index = num_open - 1 - position;
                if !self.open_matches(criterion, plan, open, local_consumer) {
                    continue;
                }
                // Most criteria only need eligibility, not the exact count.
                // ZLIFO's zero/one tests can stop at one/two; unrestricted
                // LIFO needs no supporter walk at all.
                let refinements = if matches!(criterion.order, OrderType::Lr | OrderType::Mr) {
                    self.open_refinement_count(plan, open)
                } else if criterion.max_refinements < i32::MAX {
                    self.open_refinement_count_up_to(plan, open, criterion.max_refinements + 1)
                } else {
                    0
                };
                if refinements > criterion.max_refinements {
                    continue;
                }
                let has_new = criterion.order == OrderType::New
                    && (self.achievers.contains_key(&open.condition)
                        || self.derived_supports.contains_key(&open.condition));
                let has_reuse = criterion.order == OrderType::Reuse && self.has_reuse(plan, open);
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
                    flaw: SelectedFlaw::Open(open.clone()),
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
        plan.steps().any(|step| {
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

    /// A refinement cannot relax an existing ordering or a step's required
    /// facts. If a live threat has neither an ordering repair nor a possible
    /// confrontation, no descendant can complete this plan. Reject it before
    /// ranking and queueing, rather than waiting for flaw selection to find it.
    fn has_unresolvable_threat(&self, plan: &PartialPlan) -> bool {
        // Threats are sorted by link index; links are stored newest first.
        // Walk both backwards to avoid a chain lookup for every threat.
        let mut links = plan.links();
        let mut remaining_links = plan.num_links;
        let mut link = None;
        for threat in plan.threats.iter().rev() {
            while remaining_links > threat.link {
                link = links.next();
                remaining_links -= 1;
            }
            let link = link.expect("threat refers to an existing causal link");
            if self.threat_ordering_count(plan, threat, link) == 0
                && self.confrontations(plan, threat).is_empty()
            {
                return true;
            }
        }
        false
    }

    fn threat_refinement_count(
        &self,
        plan: &PartialPlan,
        threat: &Threat,
        confrontations: usize,
    ) -> i32 {
        self.threat_ordering_count(plan, threat, plan.threatened_link(threat))
            .saturating_add(i32::try_from(confrontations).unwrap_or(i32::MAX))
    }

    fn threat_ordering_count(&self, plan: &PartialPlan, threat: &Threat, link: &CausalLink) -> i32 {
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
        i32::from(demote) + i32::from(promote)
    }

    fn open_refinement_count(&self, plan: &PartialPlan, open: &OpenCondition) -> i32 {
        self.open_refinement_count_up_to(plan, open, i32::MAX)
    }

    /// Exactly min(full_count, cap). Every fresh template contributes even if
    /// later feasibility checks might reject its child, just as in the full
    /// count. Reaching the cap makes scanning reusable occurrences unnecessary.
    fn open_refinement_count_up_to(
        &self,
        plan: &PartialPlan,
        open: &OpenCondition,
        cap: i32,
    ) -> i32 {
        let count = self.count_open_supporters(plan, open, cap);
        #[cfg(test)]
        assert_eq!(
            count,
            self.open_refinement_count_reference(plan, open).min(cap)
        );
        count
    }

    fn count_open_supporters(&self, plan: &PartialPlan, open: &OpenCondition, cap: i32) -> i32 {
        debug_assert!(cap > 0);
        let mut count = 0;
        if let Some(supports) = self.derived_supports.get(&open.condition) {
            for support in supports {
                if self.support_requirements_possible(plan, open.consumer, support) {
                    count += 1;
                    if count == cap {
                        break;
                    }
                }
            }
            return count;
        }
        count = i32::from(self.task.initial[open.condition.variable] == open.condition.value);
        if let Some(achievers) = self.achievers.get(&open.condition) {
            count = count.saturating_add(i32::try_from(achievers.len()).unwrap_or(i32::MAX));
            if count >= cap {
                return cap;
            }
            for step in plan.steps() {
                if !plan.orderings.possibly_before(
                    step.id,
                    StepTime::AtEnd,
                    open.consumer,
                    StepTime::AtStart,
                ) {
                    continue;
                }
                for achiever in achievers {
                    if achiever.operator == step.operator
                        && !plan.effect_cannot_fire(self.task, step, achiever.effect)
                        && self.support_requirements_possible(
                            plan,
                            step.id,
                            &self.task.operators[step.operator].effects[achiever.effect].conditions,
                        )
                    {
                        count += 1;
                        if count == cap {
                            return cap;
                        }
                    }
                }
            }
        }
        count.min(cap)
    }

    #[cfg(test)]
    fn open_refinement_count_reference(&self, plan: &PartialPlan, open: &OpenCondition) -> i32 {
        if let Some(supports) = self.derived_supports.get(&open.condition) {
            return i32::try_from(
                supports
                    .iter()
                    .filter(|support| {
                        self.support_requirements_possible(plan, open.consumer, support)
                    })
                    .count(),
            )
            .unwrap_or(i32::MAX);
        }
        let mut count =
            i32::from(self.task.initial[open.condition.variable] == open.condition.value);
        if let Some(achievers) = self.achievers.get(&open.condition) {
            count = count.saturating_add(achievers.len() as i32);
            for step in plan.steps() {
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
                                    && self.support_requirements_possible(
                                        plan,
                                        step.id,
                                        &self.task.operators[step.operator].effects
                                            [achiever.effect]
                                            .conditions,
                                    )
                            })
                            .count() as i32,
                    );
                }
            }
        }
        count
    }

    /// A supporter's newly required guards cannot contradict the step's
    /// existing pre-state commitments. Derived facts are expanded separately;
    /// no claim about their truth is inferred from this base-fact test.
    fn support_requirements_possible(
        &self,
        plan: &PartialPlan,
        step: usize,
        required: &[Fact],
    ) -> bool {
        let Some(mutexes) = &self.support_mutexes else {
            return true;
        };
        for (i, &fact) in required.iter().enumerate() {
            if self.task.is_derived_variable(fact.variable) {
                continue;
            }
            if required[i + 1..].iter().any(|&other| {
                !self.task.is_derived_variable(other.variable) && mutexes.mutex(fact, other)
            }) {
                return false;
            }
            if plan
                .open_conditions()
                .filter(|open| open.consumer == step)
                .map(|open| open.condition)
                .chain(
                    plan.links()
                        .filter(|link| link.consumer == step)
                        .map(|link| link.condition),
                )
                .any(|other| {
                    !self.task.is_derived_variable(other.variable) && mutexes.mutex(fact, other)
                })
            {
                return false;
            }
        }
        true
    }

    /// Compress forced support choices into one queued refinement. The count
    /// includes every future action template as well as reusable occurrences,
    /// so "only one reusable step" never silently forbids a new occurrence.
    /// Counts are recomputed after each choice: adding a step can create new
    /// reuse alternatives for other conditions. A bounded batch and deadline
    /// check keep a recursive unique supporter from monopolizing the search.
    fn propagate_supporters(
        &self,
        mut plan: PartialPlan,
        params: &Parameters,
        remaining: usize,
        stats: &mut SearchStats,
    ) -> Option<PartialPlan> {
        for _ in 0..remaining.min(16) {
            if params
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
            {
                break;
            }
            let forced = plan.open_conditions().find_map(|open| {
                let count = self.open_refinement_count_up_to(&plan, open, 2);
                (count <= 1).then(|| (open.clone(), count))
            });
            let Some((open, count)) = forced else {
                break;
            };
            if count == 0 {
                return None;
            }
            let mut refinements = self.resolve_open(&plan, open);
            debug_assert!(refinements.len() <= 1, "support count missed a refinement");
            plan = refinements.pop()?;
            stats.supporter_forced += 1;
            #[cfg(test)]
            assert_eq!(plan.threats(self.task), plan.rediscover_threats(self.task));
        }
        Some(plan)
    }

    fn has_reuse(&self, plan: &PartialPlan, open: &OpenCondition) -> bool {
        if self.task.initial[open.condition.variable] == open.condition.value {
            return true;
        }
        self.achievers
            .get(&open.condition)
            .is_some_and(|achievers| {
                plan.steps().any(|step| {
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
    ) -> (Rank, Rank) {
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

    fn compute_rank_both(&self, plan: &PartialPlan, params: &Parameters) -> (Rank, Rank) {
        let g = plan.cost() as f32;
        let opens = plan.num_open_conditions();
        let threats = plan.threats.len();
        let mut rank = Rank::new();
        let mut grank = Rank::new();
        let mut add = None;
        let mut addr = None;
        let mut relax = None;
        let mut relaxr = None;
        let mut lmcut = None;
        let mut lmcutr = None;
        let mut compiled = None;
        let mut landmarks = None;

        for term in params.heuristic.terms() {
            match term {
                HVal::Lifo => {
                    rank.push_lifo(plan.id);
                    grank.push_lifo(plan.id);
                }
                HVal::Fifo => {
                    rank.push_fifo(plan.id);
                    grank.push_fifo(plan.id);
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
                HVal::ClAdd | HVal::ClFf => {
                    let estimate = *compiled.get_or_insert_with(|| self.compiled_estimate(plan));
                    let value = estimate.map(|e| match term {
                        HVal::ClFf => e.ff,
                        _ => e.add,
                    });
                    let h = value.map_or(f32::INFINITY, |v| params.weight * v);
                    rank.push(if h.is_finite() { g + h } else { h });
                    grank.push(h);
                }
                HVal::Landmarks { .. } => {
                    // The ground reading of the lifted count: a landmark is
                    // achieved when some step's effect produces it, or it
                    // holds initially. The FAM-cut and ordering variants
                    // coincide with the plain count here.
                    let count = *landmarks.get_or_insert_with(|| self.landmark_count(plan));
                    let h = params.weight * count as f32;
                    rank.push(g + h);
                    grank.push(h);
                }
                HVal::SampleFf(_) | HVal::Lplan(_) | HVal::Lpsas(_) | HVal::Compile(_) => {
                    unreachable!("unsupported FDR heuristic was rejected before search")
                }
            }
        }
        grank.push(opens as f32);
        grank.push_lifo(plan.id);
        (rank, grank)
    }

    /// The compiled relaxation's estimate for this plan; see [`crate::cl_relax`].
    /// Each committed step becomes a zero-cost action needing its
    /// preconditions and, for every causal link into it, the link's producer
    /// to have run. The producers are the orderings the plan's causal
    /// structure imposes; reading the immediate predecessors off the ordering
    /// closure instead is quadratic in the plan, and a greedy queue that dives
    /// into a four-hundred-step plan spent every millisecond there.
    fn compiled_estimate(&self, plan: &PartialPlan) -> Option<crate::cl_relax::Estimate> {
        use crate::cl_relax::CompiledStep;
        let mut compiled = vec![CompiledStep::default(); plan.num_steps()];
        for link in plan.links() {
            if link.producer != INIT_ID && link.consumer != GOAL_ID {
                let predecessors = &mut compiled[link.consumer - 1].predecessors;
                if !predecessors.contains(&(link.producer - 1)) {
                    predecessors.push(link.producer - 1);
                }
            }
        }
        for step in plan.steps() {
            let operator = &self.task.operators[step.operator];
            let entry = &mut compiled[step.id - 1];
            entry.preconditions = self.operator_preconditions[step.operator]
                .iter()
                .map(|&fact| self.compiled.encode(fact))
                .collect();
            for (effect_index, effect) in operator.effects.iter().enumerate() {
                if plan.effect_cannot_fire(self.task, step, effect_index) {
                    continue;
                }
                let assignment = self.compiled.encode(effect.assignment());
                if effect.conditions.is_empty() {
                    entry.effects.push(assignment);
                } else {
                    let conditions = effect
                        .conditions
                        .iter()
                        .map(|&fact| self.compiled.encode(fact))
                        .collect();
                    entry.conditional_effects.push((conditions, assignment));
                }
            }
        }
        self.compiled.evaluate(&compiled)
    }

    /// How many of the task's fact landmarks no step of the plan produces and
    /// the initial state does not hold; see `HVal::Landmarks`.
    fn landmark_count(&self, plan: &PartialPlan) -> usize {
        let produced: HashSet<Fact> = plan
            .steps()
            .flat_map(|step| {
                self.task.operators[step.operator]
                    .effects
                    .iter()
                    .enumerate()
                    .filter(|&(index, _)| !plan.effect_cannot_fire(self.task, step, index))
                    .map(|(_, effect)| effect.assignment())
            })
            .collect();
        self.landmarks
            .iter()
            .filter(|landmark| {
                self.task.initial[landmark.variable] != landmark.value
                    && !produced.contains(landmark)
            })
            .count()
    }

    fn lmcut_estimate(&self, plan: &PartialPlan, reuse: bool) -> Option<f32> {
        let reusable = if reuse {
            plan.steps()
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
            .open_conditions()
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
        for open in plan.open_conditions() {
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
        for step in plan.steps() {
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
            plan.steps()
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
            .open_conditions()
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
        params: &Parameters,
        is_lazy: bool,
        is_gbfs: bool,
        is_dual: bool,
        is_alt: bool,
        boost_budget: &mut usize,
        expand_count: &mut usize,
        stats: &mut SearchStats,
    ) -> (Option<Rc<PartialPlan>>, RankTerm) {
        let alt_use_secondary = is_alt && {
            *expand_count += 1;
            (*expand_count).is_multiple_of(2)
        };
        loop {
            if params
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
            {
                return (None, RankTerm::ZERO);
            }
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
                return (None, RankTerm::ZERO);
            };
            if (is_dual || is_alt) && queued.plan.expanded.get() {
                continue;
            }
            if !is_lazy || !queued.is_lazy {
                let primary = queued.rank.primary(queued.plan.id);
                return (Some(queued.plan), primary);
            }
            let rank = if is_gbfs {
                self.rank_both(&queued.plan, params, stats).1
            } else {
                self.rank_both(&queued.plan, params, stats).0
            };
            if rank.primary(queued.plan.id).is_finite() {
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
    let mut remaining: Vec<Step> = plan.steps().cloned().collect();
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
    Open(OpenCondition),
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
    rank: &mut Rank,
    grank: &mut Rank,
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
    rank: Rank,
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
        self.rank
            .better_first(&other.rank, || self.plan.id, || other.plan.id)
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

    #[test]
    fn new_step_open_prefixes_share_only_equal_tails_and_survive_removal() {
        let task = shared_effect_task();
        let parent = PartialPlan::initial(&task);
        // Remove the older goal, so the inherited prefix must be rebuilt.
        let open = parent.open_conditions().nth(1).unwrap().clone();
        let mut cache = NewStepOpenConditions::new(&parent, &open, true);
        let (first, count) = cache.extend(&[Fact::new(0, 0), Fact::new(1, 0)]);
        let (different, _) = cache.extend(&[Fact::new(0, 0), Fact::new(1, 1)]);
        let (identical, _) = cache.extend(&[Fact::new(0, 0), Fact::new(1, 0)]);
        let (shorter, shorter_count) = cache.extend(&[Fact::new(1, 0)]);
        let first = first.unwrap();
        let different = different.unwrap();
        assert_eq!(count, 3);
        assert_eq!(shorter_count, 2);
        assert!(Rc::ptr_eq(&first, identical.as_ref().unwrap()));
        assert!(Rc::ptr_eq(
            first.tail.as_ref().unwrap(),
            different.tail.as_ref().unwrap()
        ));
        assert!(!Rc::ptr_eq(&first, shorter.as_ref().unwrap()));
        assert_eq!(first.head, shorter.as_ref().unwrap().head);
        let (empty, empty_count) = cache.extend(&[]);
        assert_eq!(empty_count, 1);
        assert!(Rc::ptr_eq(
            empty.as_ref().unwrap(),
            first.tail.as_ref().unwrap().tail.as_ref().unwrap()
        ));
        assert_eq!(empty.as_ref().unwrap().head.consumer, GOAL_ID);
        // Releasing the expansion cache leaves every child's shared nodes live.
        drop(cache);
        let expected: Vec<_> = first.iter().cloned().collect();
        let mut child = parent.clone();
        child.open_conditions = Some(first.clone());
        child.num_open_conditions = count;
        child.remove_open(&OpenCondition {
            consumer: 1,
            condition: Fact::new(0, 0),
        });
        assert_eq!(child.num_open_conditions(), 2);
        assert_eq!(first.iter().cloned().collect::<Vec<_>>(), expected);
        assert_eq!(parent.num_open_conditions(), 2);
        assert_eq!(parent.open_conditions().nth(1), Some(&open));
    }

    #[test]
    fn new_step_conditions_preserve_guard_order_and_deduplicate_requirements() {
        let mut task = conditional_task();
        task.variables.push(Variable {
            name: "guard".into(),
            values: vec!["off".into(), "on".into()],
        });
        task.initial.push(1);
        task.operators[1].prevail.push(Fact::new(1, 1));
        task.operators[1].effects[0].conditions = vec![
            Fact::new(1, 1),
            Fact::new(2, 1),
            Fact::new(1, 1),
            Fact::new(2, 1),
        ];
        task.operators.push(task.operators[1].clone());
        let planner = Planner::new(&task);
        let parent = PartialPlan::initial(&task);
        let children =
            planner.resolve_open(&parent, parent.open_conditions().next().unwrap().clone());
        assert_eq!(children.len(), 2);
        for child in &children {
            assert_eq!(child.num_open_conditions(), 3);
            assert_eq!(
                child.open_conditions().cloned().collect::<Vec<_>>(),
                vec![
                    OpenCondition {
                        consumer: 1,
                        condition: Fact::new(2, 1)
                    },
                    OpenCondition {
                        consumer: 1,
                        condition: Fact::new(1, 1)
                    },
                    OpenCondition {
                        consumer: 1,
                        condition: Fact::new(0, 0)
                    },
                ]
            );
            assert_eq!(child.threats(&task), child.rediscover_threats(&task));
        }
        assert!(Rc::ptr_eq(
            children[0].open_conditions.as_ref().unwrap(),
            children[1].open_conditions.as_ref().unwrap()
        ));
    }

    #[test]
    fn new_step_siblings_share_storage_without_sharing_later_refinements() {
        let mut task = travel_task();
        // Three distinct achievers for the goal, each requiring location=1.
        task.operators.push(task.operators[1].clone());
        task.operators.push(task.operators[1].clone());
        let planner = Planner::new(&task);
        let parent = PartialPlan::initial(&task);
        let children =
            planner.resolve_open(&parent, parent.open_conditions().next().unwrap().clone());
        assert_eq!(children.len(), 3);
        for child in &children {
            assert!(Rc::ptr_eq(&child.orderings, &children[0].orderings));
            assert!(Rc::ptr_eq(
                child.links.as_ref().unwrap(),
                children[0].links.as_ref().unwrap()
            ));
            assert!(!Rc::ptr_eq(&child.orderings, &parent.orderings));
            assert_eq!(child.threats(&task), child.rediscover_threats(&task));
        }

        let next = planner.resolve_open(
            &children[0],
            children[0].open_conditions().next().unwrap().clone(),
        );
        assert_eq!(next.len(), 1);
        assert!(is_ordered_before(&next[0].orderings, 2, 1));
        assert!(!Rc::ptr_eq(&next[0].orderings, &children[0].orderings));
        assert_eq!(next[0].num_links(), 2);
        assert!(Rc::ptr_eq(
            next[0].links.as_ref().unwrap().tail.as_ref().unwrap(),
            children[0].links.as_ref().unwrap()
        ));
        for sibling in &children {
            assert_eq!(sibling.num_links(), 1);
            assert_eq!(sibling.num_steps(), 1);
            assert!(!is_ordered_before(&sibling.orderings, 2, 1));
        }
        assert_eq!(parent.num_steps(), 0);
    }

    #[test]
    fn sibling_links_share_across_operators_but_preserve_effect_indices() {
        let mut task = travel_task();
        task.variables.push(Variable {
            name: "flag".into(),
            values: vec!["off".into(), "on".into()],
        });
        task.initial.push(0);
        let mut alternate = task.operators[1].clone();
        alternate.effects.insert(
            0,
            Effect {
                conditions: vec![],
                variable: 1,
                pre: None,
                post: 1,
            },
        );
        task.operators.push(alternate);
        let mut direct = task.operators[1].clone();
        direct.effects[0].pre = Some(0);
        task.operators.push(direct);

        let planner = Planner::new(&task);
        let parent = PartialPlan::initial(&task);
        let children =
            planner.resolve_open(&parent, parent.open_conditions().next().unwrap().clone());
        assert_eq!(children.len(), 3);
        let links: Vec<_> = children
            .iter()
            .map(|child| child.links.as_ref().unwrap())
            .collect();
        assert!(Rc::ptr_eq(links[0], links[2]));
        assert!(!Rc::ptr_eq(links[0], links[1]));
        assert_eq!(links[0].head.effect, Some(0));
        assert_eq!(links[1].head.effect, Some(1));
        // Each shared link's producer is interpreted against its own plan's
        // operator and preconditions, which need not match its siblings'.
        for (index, child) in children.iter().enumerate() {
            assert_eq!(child.step(1).unwrap().operator, index + 1);
            let precondition = if index == 2 { 0 } else { 1 };
            assert_eq!(
                child.open_conditions().next().unwrap().condition,
                Fact::new(0, precondition)
            );
            assert_eq!(child.threats(&task), child.rediscover_threats(&task));
        }
        assert_eq!(parent.num_links(), 0);
    }

    #[test]
    fn siblings_share_only_equal_threat_caches_and_keep_them_immutable() {
        let mut task = travel_task();
        task.variables.push(Variable {
            name: "cargo".into(),
            values: vec!["intact".into(), "damaged".into()],
        });
        task.initial.push(0);
        task.operators.push(task.operators[0].clone());
        let mut damaging = task.operators[0].clone();
        damaging.effects.push(Effect {
            variable: 1,
            pre: None,
            post: 1,
            conditions: vec![],
        });
        task.operators.push(damaging);
        let open = OpenCondition {
            consumer: GOAL_ID,
            condition: Fact::new(0, 1),
        };
        let orderings = Rc::new(BinaryOrderings::new())
            .refine_with_step(
                Ordering::new(1, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                1,
            )
            .unwrap();
        let parent = PartialPlan::assemble(
            vec![Step { id: 1, operator: 1 }],
            vec![CausalLink {
                producer: INIT_ID,
                consumer: 1,
                condition: Fact::new(1, 0),
                effect: None,
            }],
            vec![open.clone()],
            orderings,
            vec![],
            1,
            2,
        );
        let planner = Planner::new(&task);
        let children = planner.resolve_open(&parent, open);
        assert_eq!(children.len(), 3);
        assert_eq!(children[0].threats.len(), 1);
        assert_eq!(children[2].threats.len(), 2);
        assert!(Rc::ptr_eq(&children[0].threats, &children[1].threats));
        assert!(!Rc::ptr_eq(&children[0].threats, &children[2].threats));
        for child in &children {
            assert_eq!(child.threats(&task), child.rediscover_threats(&task));
        }
        let resolved = planner.resolve_threat(&children[0], &children[0].threats[0]);
        assert!(!resolved.is_empty());
        assert!(resolved.iter().all(|p| p.threats.is_empty()));
        assert_eq!(children[0].threats.len(), 1);
        assert_eq!(children[1].threats.len(), 1);
        assert!(parent.threats.is_empty());
    }

    #[test]
    fn queue_rank_storage_does_not_allocate() {
        use crate::alloc_test::allocations_during;
        use std::hint::black_box;

        let task = travel_task();
        let planner = Planner::new(&task);
        let params = Parameters {
            // Four composed terms plus the two GBFS tiebreakers fill the rank.
            heuristic: Heuristic::parse("OC/FIFO/LIFO/UC").unwrap(),
            ..Parameters::default()
        };
        let mut plan = PartialPlan::initial(&task);
        plan.id = usize::MAX;
        let mut stats = SearchStats::default();
        let ((a, g), allocations) =
            allocations_during(|| black_box(planner.rank_both(&plan, &params, &mut stats)));
        assert_eq!(allocations, 0);
        assert_eq!(stats.h_evals, 1);
        let expected = [1.0, usize::MAX as f32, -(usize::MAX as f32), 0.0];
        assert_eq!(&*a, &expected);
        assert_eq!(&g[..4], &expected);
        assert_eq!(&g[4..], &[1.0, -(usize::MAX as f32)]);

        // Positive control: count the two allocations that the previous
        // implementation needed to hold its temporary numeric rank vectors.
        let ((av, gv), allocations) = allocations_during(|| black_box((a.to_vec(), g.to_vec())));
        assert_eq!(allocations, 2);
        assert_eq!(&*a, av);
        assert_eq!(&*g, gv);
    }

    #[test]
    fn queues_and_lazy_reranking_use_exact_plan_ids() {
        let task = travel_task();
        let planner = Planner::new(&task);
        for older in [1 << 24, usize::MAX - 1] {
            for (name, newest_first) in [
                ("OC/LIFO", true),
                ("OC/FIFO", false),
                ("LIFO/FIFO", true),
                ("FIFO/LIFO", false),
            ] {
                let params = Parameters {
                    heuristic: Heuristic::parse(name).unwrap(),
                    ..Parameters::default()
                };
                for (lazy, greedy) in [(false, false), (false, true), (true, true)] {
                    for ids in [[older, older + 1], [older + 1, older]] {
                        let mut queue = BinaryHeap::new();
                        let mut stats = SearchStats::default();
                        for id in ids {
                            let mut plan = PartialPlan::initial(&task);
                            plan.id = id;
                            let rank = if lazy {
                                Rank::lazy_proxy(RankTerm::ZERO, plan.num_open_conditions(), id)
                            } else {
                                let (a, g) = planner.rank_both(&plan, &params, &mut stats);
                                if greedy {
                                    g
                                } else {
                                    a
                                }
                            };
                            queue.push(QueuedPlan {
                                plan: Rc::new(plan),
                                rank,
                                is_lazy: lazy,
                            });
                        }
                        let first = if newest_first { older + 1 } else { older };
                        let second = if newest_first { older } else { older + 1 };
                        for expected in [first, second] {
                            let (next, _) = planner.pop_next(
                                &mut queue, None, &params, lazy, greedy, false, false, &mut 0,
                                &mut 0, &mut stats,
                            );
                            assert_eq!(next.unwrap().id, expected, "{name} lazy={lazy}");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn h2_strengthens_combined_pruning_and_preserves_reachable_goals() {
        let mut task = crate::h2::tests::resource_task();
        // A syntactic achiever of the resource whose prerequisites are jointly
        // impossible. Neither ordinary reachability nor declared mutexes see it.
        task.operators.push(Operator {
            name: "impossible-reset".into(),
            cost: 1,
            prevail: task.goals.clone(),
            effects: vec![Effect {
                conditions: vec![],
                variable: 0,
                pre: Some(0),
                post: 1,
            }],
        });
        for mask in 0..16 {
            let params = Parameters {
                search_algorithm: SearchAlgorithm::Bfs,
                search_limits: vec![200],
                prune: crate::pruning::PruneOptions {
                    h2: true,
                    cutset: mask & 1 != 0,
                    edelete: mask & 2 != 0,
                    disjunctive: mask & 4 != 0,
                    supporters: mask & 8 != 0,
                    ..Default::default()
                },
                ..Default::default()
            };
            task.goals = vec![Fact::new(1, 1), Fact::new(2, 1)];
            let (outcome, stats) = solve_with_params(&task, &params).unwrap();
            assert!(matches!(outcome, Outcome::NoSolution), "mask {mask}");
            assert_eq!(stats.nodes_generated, 0, "mutex goals rejected at root");
            assert_eq!(stats.h2.status, crate::h2::Status::Complete);
            assert!(stats.h2.mutex_pairs > 0);
            assert_eq!(stats.h2.supporters_removed, 1);

            for variable in 1..3 {
                task.goals = vec![Fact::new(variable, 1)];
                let (outcome, stats) = solve_with_params(&task, &params).unwrap();
                let Outcome::Solved(solution) = outcome else {
                    panic!("reachable goal lost, mask {mask}, variable {variable}")
                };
                assert_eq!(solution.operators, vec![variable - 1]);
                assert_eq!(solution.plan.cost(), 1);
                assert_eq!(stats.h2.supporters_removed, 1);
            }
        }
    }

    #[test]
    fn h2_axiom_projection_preserves_derived_goals_with_all_pruning_combinations() {
        let mut task = crate::h2::tests::axiom_resource_task();
        for mask in 0..16 {
            let params = Parameters {
                search_algorithm: SearchAlgorithm::Bfs,
                search_limits: vec![200],
                prune: crate::pruning::PruneOptions {
                    h2: true,
                    cutset: mask & 1 != 0,
                    edelete: mask & 2 != 0,
                    disjunctive: mask & 4 != 0,
                    supporters: mask & 8 != 0,
                    ..Default::default()
                },
                ..Default::default()
            };
            task.goals = vec![Fact::new(1, 1), Fact::new(2, 1)];
            let (outcome, stats) = solve_with_params(&task, &params).unwrap();
            assert!(matches!(outcome, Outcome::NoSolution), "mask {mask}");
            assert_eq!(stats.nodes_generated, 0);
            assert_eq!(stats.h2.status, crate::h2::Status::Complete);
            assert_eq!(stats.h2.projected_variables, 2);

            // Positive derived goal, already true after initial closure.
            task.goals = vec![Fact::new(4, 0)];
            let (outcome, _) = solve_with_params(&task, &params).unwrap();
            let Outcome::Solved(solution) = outcome else {
                panic!("initial derived goal lost, mask {mask}");
            };
            assert_eq!(solution.plan.cost(), 0);
            for variable in 1..3 {
                // The action needs the positive derived condition; afterward
                // both levels of the axiom chain must reset to their defaults.
                task.goals = vec![Fact::new(variable, 1), Fact::new(4, 1)];
                let (outcome, _) = solve_with_params(&task, &params).unwrap();
                let Outcome::Solved(solution) = outcome else {
                    panic!("derived reset goal lost, mask {mask}, variable {variable}");
                };
                assert_eq!(solution.operators, vec![variable - 1]);
                assert_eq!(solution.plan.cost(), 1);
            }
        }
    }

    #[test]
    fn h2_keeps_unreachable_fact_proofs_even_without_new_pairs() {
        let mut task = crate::h2::tests::resource_task();
        task.variables.truncate(1);
        task.initial = vec![0];
        task.goals = vec![Fact::new(0, 1)];
        task.operators.clear();
        let params = Parameters {
            prune: crate::pruning::PruneOptions::parse("h2").unwrap(),
            ..Default::default()
        };
        let (outcome, stats) = solve_with_params(&task, &params).unwrap();
        assert!(matches!(outcome, Outcome::NoSolution));
        assert_eq!(
            stats.nodes_generated, 0,
            "unreachable goal rejected before search"
        );
        assert_eq!(stats.h2.status, crate::h2::Status::Complete);
        assert_eq!(stats.h2.new_mutex_pairs, 0);
        assert_eq!(stats.h2.unreachable_facts, 1);
    }

    #[test]
    fn h2_deadline_is_a_search_stop_not_a_proof_of_no_solution() {
        let task = crate::h2::tests::resource_task();
        let params = Parameters {
            deadline: Some(Instant::now()),
            prune: crate::pruning::PruneOptions::parse("h2").unwrap(),
            ..Default::default()
        };
        let (outcome, stats) = solve_with_params(&task, &params).unwrap();
        assert!(matches!(outcome, Outcome::LimitReached));
        assert_eq!(stats.stopped, Some(crate::memory::StopReason::Deadline));
        assert_eq!(stats.h2.status, crate::h2::Status::Deadline);
        assert_eq!(stats.h2.mutex_pairs, 0);
        assert_eq!(stats.nodes_generated, 0);
    }

    #[test]
    fn supporter_propagation_preserves_the_only_route_and_its_cost() {
        let task = travel_task();
        let params = Parameters {
            prune: crate::pruning::PruneOptions::parse("supporters").unwrap(),
            ..Default::default()
        };
        let (outcome, stats) = solve_with_params(&task, &params).unwrap();
        let Outcome::Solved(solution) = outcome else {
            panic!("the two-drive route is reachable")
        };
        assert_eq!(solution.operators, vec![0, 1]);
        assert_eq!(solution.plan.cost(), 2);
        assert!(stats.supporter_forced > 0);
    }

    #[test]
    fn supporter_propagation_keeps_fresh_occurrences_as_alternatives_to_reuse() {
        let mut task = travel_task();
        task.goals = vec![Fact::new(0, 1)];
        let planner = Planner::new(&task)
            .with_pruning(crate::pruning::PruneOptions::parse("supporters").unwrap());
        let mut plan = PartialPlan::initial(&task);
        plan.orderings = plan
            .orderings
            .refine_with_step(
                Ordering::new(1, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                1,
            )
            .unwrap();
        plan.push_step(Step { id: 1, operator: 0 });
        plan.next_step_id = 2;
        // Both a fresh drive occurrence and the already committed one can
        // support the goal. Uniqueness of its action type does not force reuse.
        assert_eq!(
            planner.open_refinement_count(&plan, plan.open_conditions().next().unwrap()),
            2
        );
        let mut stats = SearchStats::default();
        let result = planner
            .propagate_supporters(plan, &Parameters::default(), 16, &mut stats)
            .unwrap();
        assert_eq!(result.num_links(), 0);
        assert_eq!(stats.supporter_forced, 0);
    }

    #[test]
    fn recursive_forced_support_yields_and_obeys_a_deadline() {
        let mut task = travel_task();
        task.goals = vec![Fact::new(0, 1)];
        task.operators.truncate(1);
        task.operators[0].effects[0].pre = Some(1);
        let planner = Planner::new(&task)
            .with_pruning(crate::pruning::PruneOptions::parse("supporters").unwrap());
        let mut stats = SearchStats::default();
        let plan = planner
            .propagate_supporters(
                PartialPlan::initial(&task),
                &Parameters::default(),
                16,
                &mut stats,
            )
            .unwrap();
        assert!(plan.num_steps() > 0 && plan.num_steps() <= 16);
        assert!(plan.num_open_conditions() > 0);
        let expired = Parameters {
            deadline: Some(Instant::now()),
            ..Default::default()
        };
        let mut stats = SearchStats::default();
        let result = planner
            .propagate_supporters(PartialPlan::initial(&task), &expired, 16, &mut stats)
            .unwrap();
        assert_eq!(result.num_steps(), 0);
        assert_eq!(stats.supporter_forced, 0);
    }

    #[test]
    fn forced_refinements_consume_the_search_node_budget() {
        let mut task = travel_task();
        task.goals = vec![Fact::new(0, 1)];
        task.operators.truncate(1);
        task.operators[0].effects[0].pre = Some(1);
        let params = Parameters {
            search_algorithm: SearchAlgorithm::Bfs,
            search_limits: vec![20],
            prune: crate::pruning::PruneOptions::parse("supporters").unwrap(),
            ..Default::default()
        };
        let (outcome, stats) = solve_with_params(&task, &params).unwrap();
        assert!(matches!(outcome, Outcome::LimitReached));
        assert!(stats.nodes_generated <= 20);
        assert!(stats.supporter_forced > 0);
    }

    #[test]
    fn forced_refinements_advance_memory_limit_sampling() {
        if crate::memory::resident_set_kb() < 1024 {
            return;
        }
        let mut task = travel_task();
        task.goals = vec![Fact::new(0, 1)];
        task.operators.truncate(1);
        task.operators[0].effects[0].pre = Some(1);
        let params = Parameters {
            search_algorithm: SearchAlgorithm::Bfs,
            search_limits: vec![2000],
            memory_stop_mb: Some(1),
            prune: crate::pruning::PruneOptions::parse("supporters").unwrap(),
            ..Default::default()
        };
        let (outcome, stats) = solve_with_params(&task, &params).unwrap();
        assert!(matches!(outcome, Outcome::LimitReached));
        assert_eq!(stats.stopped, Some(crate::memory::StopReason::Memory));
        assert!(stats.nodes_generated < 2000);
    }

    #[test]
    fn cutsets_include_committed_guards_without_spanning_links() {
        let task = conditional_task();
        let mutexes = crate::cutset::FactMutexes::new(&task);
        let mut plan = PartialPlan::initial(&task);
        plan.push_step(Step { id: 1, operator: 1 });
        plan.push_open(OpenCondition {
            consumer: 1,
            condition: Fact::new(1, 0),
        });
        // Supporting the other requirement does not stop it being a pre-state
        // commitment. Neither link spans any step in this partial plan.
        plan.push_link(CausalLink {
            producer: INIT_ID,
            consumer: 1,
            condition: Fact::new(1, 1),
            effect: None,
        });
        assert!(crate::cutset::has_inconsistent_cutset(
            &plan, &task, &mutexes
        ));
    }

    #[test]
    fn cutsets_check_cross_variable_commitments_but_separate_step_states() {
        let mut task = conditional_task();
        task.initial = vec![0, 1];
        task.mutex_groups = vec![vec![Fact::new(0, 0), Fact::new(1, 0)]];
        let mutexes = crate::cutset::FactMutexes::new(&task);
        let mut plan = PartialPlan::initial(&task);
        plan.push_step(Step { id: 1, operator: 1 });
        plan.push_open(OpenCondition {
            consumer: 1,
            condition: Fact::new(0, 0),
        });
        plan.push_open(OpenCondition {
            consumer: 1,
            condition: Fact::new(1, 0),
        });
        assert!(crate::cutset::has_inconsistent_cutset(
            &plan, &task, &mutexes
        ));
        // The same requirements at different action occurrences can coexist.
        plan.remove_open(&OpenCondition {
            consumer: 1,
            condition: Fact::new(1, 0),
        });
        plan.push_step(Step { id: 2, operator: 0 });
        plan.push_open(OpenCondition {
            consumer: 2,
            condition: Fact::new(1, 0),
        });
        assert!(!crate::cutset::has_inconsistent_cutset(
            &plan, &task, &mutexes
        ));
        // Requiring x=0 before an action that produces x=1 is also valid.
        plan.push_open(OpenCondition {
            consumer: 1,
            condition: Fact::new(1, 1),
        });
        assert!(!crate::cutset::has_inconsistent_cutset(
            &plan, &task, &mutexes
        ));
    }

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
        let plan = PartialPlan::assemble(
            vec![Step { id: 1, operator: 0 }, Step { id: 2, operator: 1 }],
            vec![CausalLink {
                producer: 1,
                consumer: GOAL_ID,
                condition: Fact::new(0, 1),
                effect: Some(0),
            }],
            vec![],
            orderings,
            vec![threat],
            2,
            3,
        );
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
        plan.push_step(Step { id: 1, operator: 0 });

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
        for order in [
            "STATIC",
            "LCFR",
            "ZLIFO",
            "MC",
            "MW",
            "UCPOP-LC",
            "{n,s}MR/{o}MR",
            "{n,s}LIFO/{o}REUSE",
            "DUNF-GEN",
        ] {
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
    fn unavoidable_threats_dominate_only_within_the_same_step_and_link() {
        let mut task = breaker_task();
        // A conditional threat precedes two unavoidable assignments in effect
        // order. The collector must discard it when it finds the first one.
        for _ in 0..2 {
            task.operators[1].effects.push(Effect {
                conditions: vec![],
                variable: 0,
                pre: None,
                post: 0,
            });
        }
        let (mut plan, _) = trapped_breaker_plan();
        plan.edelete = Some(Rc::new(crate::cutset::FactMutexes::new(&task)));
        plan.threats = Rc::new(Vec::new());
        let mut by_step = plan.clone();
        plan.add_link_threats(&task, 0);
        by_step.add_step_threats(&task, 2);
        let expected = vec![Threat {
            step: 2,
            effect: 2,
            link: 0,
        }];
        assert_eq!(*plan.threats, expected);
        assert_eq!(plan.threats, by_step.threats);
        assert_eq!(plan.threats(&task), plan.rediscover_threats(&task));
        assert!(Planner::new(&task)
            .confrontations(&plan, &expected[0])
            .is_empty());

        // A precondition threat also dominates conditional assignments, even
        // when there is no unconditional threatening effect.
        task.operators[1].effects.truncate(2);
        task.operators[1].prevail = vec![Fact::new(0, 0)];
        plan.threats = Rc::new(Vec::new());
        plan.add_link_threats(&task, 0);
        assert_eq!(
            *plan.threats,
            vec![Threat {
                step: 2,
                effect: NO_EFFECT,
                link: 0
            }]
        );
        assert_eq!(plan.threats(&task), plan.rediscover_threats(&task));

        // Without the unavoidable precondition conflict, the original
        // conditional effect and its confrontation alternative must survive.
        task.operators[1].prevail = vec![Fact::new(0, 1)];
        plan.threats = Rc::new(Vec::new());
        plan.add_link_threats(&task, 0);
        assert_eq!(plan.threats[0].effect, 1);
        let children = Planner::new(&task).resolve_threat(&plan, &plan.threats[0]);
        assert_eq!(children.len(), 1);
        assert!(children[0].effect_suppressed(2, 1));
    }

    #[test]
    fn ordering_repairs_retire_every_reason_for_the_same_threat() {
        let mut task = travel_task();
        // A protects location=lyon until B. T both requires paris and assigns
        // nice, giving two different reasons for the same ordering obligation.
        task.operators[1].name = "drive truck paris nice".into();
        task.operators[1].effects[0].pre = Some(0);
        task.operators.push(Operator {
            name: "consume-at-lyon".into(),
            prevail: vec![Fact::new(0, 1)],
            effects: vec![],
            cost: 1,
        });
        let mut orderings = Rc::new(BinaryOrderings::new());
        for step in 1..=3 {
            orderings = orderings
                .refine_with_step(
                    Ordering::new(step, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                    step,
                )
                .unwrap();
        }
        orderings = orderings
            .refine(Ordering::new(1, StepTime::AtEnd, 3, StepTime::AtStart))
            .unwrap();
        let mut plan = PartialPlan::assemble(
            (1..=3)
                .map(|id| Step {
                    id,
                    operator: id - 1,
                })
                .collect(),
            vec![CausalLink {
                producer: 1,
                consumer: 3,
                condition: Fact::new(0, 1),
                effect: Some(0),
            }],
            vec![],
            orderings,
            vec![],
            3,
            4,
        );
        plan.edelete = Some(Rc::new(crate::cutset::FactMutexes::new(&task)));
        plan.add_step_threats(&task, 2);
        assert_eq!(plan.threats(&task), plan.rediscover_threats(&task));
        assert_eq!(plan.threats.len(), 1);
        assert_eq!(plan.threats[0].effect, 0);

        let immediate = Planner::new(&task);
        let deferred = Planner::new(&task)
            .with_pruning(crate::pruning::PruneOptions::parse("disjunctive").unwrap());
        for threat in plan.threats.iter() {
            let posted = deferred.post_disjunction(&plan, threat).unwrap();
            assert!(!posted.complete(&task));
            assert_eq!(posted.pending_disjunctions(), 1);
            assert!(posted.threat_covered(threat));
            assert_eq!(posted.threats(&task), posted.rediscover_threats(&task));

            // Promotion and demotion, either immediate or deferred, retire
            // BOTH reasons regardless of which reason was selected.
            for children in [
                immediate.resolve_threat(&plan, threat),
                deferred.split_disjunction(&posted, 0),
            ] {
                assert_eq!(children.len(), 2);
                for child in children {
                    assert!(child.threats.is_empty());
                    assert_eq!(child.pending_disjunctions(), 0);
                    assert_eq!(child.threats(&task), child.rediscover_threats(&task));
                    assert!(
                        is_ordered_before(&child.orderings, 2, 1)
                            || is_ordered_before(&child.orderings, 3, 2)
                    );
                }
            }
        }
    }

    #[test]
    fn settling_retires_constraints_after_guard_and_ordering_changes() {
        let mut task = shared_effect_task();
        for name in ["guard-a", "guard-b"] {
            task.variables.push(Variable {
                name: name.into(),
                values: vec!["off".into(), "on".into()],
            });
            task.initial.push(0);
        }
        task.operators.push(Operator {
            name: "conditional-breaker".into(),
            cost: 1,
            prevail: vec![],
            effects: vec![
                Effect {
                    conditions: vec![Fact::new(2, 0)],
                    variable: 0,
                    pre: None,
                    post: 0,
                },
                Effect {
                    conditions: vec![Fact::new(3, 0)],
                    variable: 0,
                    pre: None,
                    post: 0,
                },
                Effect {
                    conditions: vec![Fact::new(3, 0)],
                    variable: 1,
                    pre: None,
                    post: 0,
                },
            ],
        });
        task.operators.push(Operator {
            name: "consume".into(),
            cost: 1,
            prevail: task.goals.clone(),
            effects: vec![],
        });
        let mut orderings = Rc::new(BinaryOrderings::new());
        for step in 1..=3 {
            orderings = orderings
                .refine_with_step(
                    Ordering::new(step, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                    step,
                )
                .unwrap();
        }
        orderings = orderings
            .refine(Ordering::new(1, StepTime::AtEnd, 3, StepTime::AtStart))
            .unwrap();
        let mut plan = PartialPlan::assemble(
            (1..=3)
                .map(|id| Step {
                    id,
                    operator: id - 1,
                })
                .collect(),
            (0..2)
                .map(|variable| CausalLink {
                    producer: 1,
                    consumer: 3,
                    condition: Fact::new(variable, 1),
                    effect: Some(variable),
                })
                .collect(),
            vec![],
            orderings,
            vec![],
            3,
            4,
        );
        plan.add_step_threats(&task, 2);
        assert_eq!(
            plan.threats.len(),
            3,
            "distinct conditional threats must survive"
        );
        assert_eq!(plan.threats(&task), plan.rediscover_threats(&task));
        let planner = Planner::new(&task)
            .with_pruning(crate::pruning::PruneOptions::parse("disjunctive").unwrap());
        let mut child = planner.post_disjunction(&plan, &plan.threats[0]).unwrap();
        assert_eq!(child.pending_disjunctions(), 1);
        assert_eq!(
            child
                .threats
                .iter()
                .filter(|t| child.threat_covered(t))
                .count(),
            3
        );
        // Forcing promotion must trigger a new threat sweep: all three
        // assignments are now outside both protected intervals.
        let mut forced = child.clone();
        forced.orderings = forced
            .orderings
            .refine(Ordering::new(1, StepTime::AtEnd, 2, StepTime::AtStart))
            .unwrap();
        assert!(forced.settle(&task));
        assert!(is_ordered_before(&forced.orderings, 3, 2));
        assert!(forced.threats.is_empty());
        assert_eq!(forced.pending_disjunctions(), 0);
        assert_eq!(forced.threats(&task), forced.rediscover_threats(&task));

        // A different protected interval is not covered by this constraint.
        let mut different_interval = child.clone();
        different_interval.push_link(CausalLink {
            producer: 1,
            consumer: GOAL_ID,
            condition: Fact::new(0, 1),
            effect: Some(0),
        });
        assert!(!different_interval.threat_covered(&Threat {
            step: 2,
            effect: 0,
            link: 2
        }));

        // A later commitment disables only the source effect. Keeping the
        // constraint would silently remove the other effects' valid
        // confrontation alternatives; dropping the other threats would miss
        // their still-live assignments.
        child.push_open(OpenCondition {
            consumer: 2,
            condition: Fact::new(2, 1),
        });
        assert!(child.settle(&task));
        assert_eq!(child.pending_disjunctions(), 0);
        assert_eq!(child.threats.len(), 2);
        assert!(child.threats.iter().all(|t| !child.threat_covered(t)));
        assert_eq!(child.threats(&task), child.rediscover_threats(&task));
        let alternatives = planner.resolve_threat(&child, &child.threats[0]);
        assert_eq!(
            alternatives.len(),
            2,
            "confrontation and a ordering remain possible"
        );
        assert!(
            alternatives[0].threats.is_empty(),
            "disabling guard-b resolves both remaining effects"
        );
        assert_eq!(alternatives[1].pending_disjunctions(), 1);
        let splits = planner.split_disjunction(&alternatives[1], 0);
        assert_eq!(splits.len(), 2);
        for resolved in splits {
            assert!(resolved.threats.is_empty());
            assert_eq!(resolved.pending_disjunctions(), 0);
            assert!(
                is_ordered_before(&resolved.orderings, 2, 1)
                    || is_ordered_before(&resolved.orderings, 3, 2)
            );
        }
    }

    #[test]
    fn two_conditional_threats_keep_both_confrontations_under_combined_pruning() {
        let mut task = breaker_task();
        task.variables.push(Variable {
            name: "second-mode".into(),
            values: vec!["unsafe".into(), "safe".into()],
        });
        task.initial.push(0);
        task.operators[1].effects.push(Effect {
            conditions: vec![Fact::new(4, 0)],
            variable: 0,
            pre: None,
            post: 0,
        });
        task.operators.push(Operator {
            name: "make-second-safe".into(),
            cost: 1,
            prevail: vec![],
            effects: vec![Effect {
                conditions: vec![],
                variable: 4,
                pre: Some(0),
                post: 1,
            }],
        });
        for order in ["STATIC", "ZLIFO"] {
            for mask in 0..32 {
                let params = Parameters {
                    search_algorithm: SearchAlgorithm::Bfs,
                    flaw_orders: vec![FlawSelectionOrder::parse(order).unwrap()],
                    search_limits: vec![2_000],
                    prune: crate::pruning::PruneOptions {
                        cutset: mask & 1 != 0,
                        edelete: mask & 2 != 0,
                        disjunctive: mask & 4 != 0,
                        supporters: mask & 8 != 0,
                        h2: mask & 16 != 0,
                        ..Default::default()
                    },
                    ..Default::default()
                };
                let (outcome, _) = solve_with_params(&task, &params).unwrap();
                let Outcome::Solved(solution) = outcome else {
                    panic!("lost a necessary confrontation: {order}, mask {mask}");
                };
                assert_eq!(solution.plan.cost(), 4, "{order}, mask {mask}");
                let run = solution.operators.iter().position(|&op| op == 1).unwrap();
                for preparation in [0, 2, 3] {
                    assert!(solution.operators[..run].contains(&preparation));
                }
            }
        }
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
        let plan = PartialPlan::assemble(
            vec![Step { id: 1, operator: 0 }, Step { id: 2, operator: 1 }],
            vec![CausalLink {
                producer: 1,
                consumer: GOAL_ID,
                condition: Fact::new(0, 1),
                effect: Some(0),
            }],
            vec![],
            orderings,
            vec![Threat {
                step: 2,
                effect: 0,
                link: 0,
            }],
            2,
            3,
        );
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
    fn dead_threat_check_preserves_confrontation_and_demotion() {
        let mut task = breaker_task();
        let (plan, _) = trapped_breaker_plan();
        assert!(!Planner::new(&task).has_unresolvable_threat(&plan));

        let mut committed = plan.clone();
        committed.push_open(OpenCondition {
            consumer: 2,
            condition: Fact::new(2, 0),
        });
        assert!(Planner::new(&task).has_unresolvable_threat(&committed));

        // An unconditional effect cannot be confronted, but moving the step
        // before the producer remains valid when their ordering permits it.
        task.operators[1].effects[1].conditions.clear();
        let planner = Planner::new(&task);
        assert!(planner.has_unresolvable_threat(&plan));
        let mut unordered = plan.clone();
        unordered.orderings = Rc::new(BinaryOrderings::new());
        for step in 1..=2 {
            unordered.orderings = unordered
                .orderings
                .refine_with_step(
                    Ordering::new(step, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                    step,
                )
                .unwrap();
        }
        assert!(!planner.has_unresolvable_threat(&unordered));
        assert_eq!(
            planner
                .resolve_threat(&unordered, &unordered.threats[0])
                .len(),
            1
        );
    }

    #[test]
    fn search_discards_dead_initial_links_but_keeps_later_achievers() {
        let mut task = shared_effect_task();
        task.initial[0] = 1;
        task.operators[0].effects[0].post = 0;
        task.operators[0].effects[0].pre = None;
        task.operators[0].cost = 3;
        // The only way to achieve right=on destroys left=on. An initial-state
        // link protecting left=on until the goal therefore cannot survive it.
        for restore in [false, true] {
            if restore {
                task.operators.push(Operator {
                    name: "restore-left".into(),
                    prevail: vec![],
                    effects: vec![Effect {
                        conditions: vec![],
                        variable: 0,
                        pre: Some(0),
                        post: 1,
                    }],
                    cost: 7,
                });
            }
            for algorithm in [
                SearchAlgorithm::A,
                SearchAlgorithm::Bfs,
                SearchAlgorithm::Gbfs,
                SearchAlgorithm::LazyGbfsDual,
                SearchAlgorithm::Alt,
            ] {
                let params = Parameters {
                    search_algorithm: algorithm,
                    flaw_orders: vec![FlawSelectionOrder::parse("ZLIFO").unwrap()],
                    heuristic: Heuristic::parse("ADD/LIFO").unwrap(),
                    search_limits: vec![1_000],
                    ..Parameters::default()
                };
                let (outcome, stats) = solve_with_params(&task, &params).unwrap();
                assert!(
                    stats.pruned > 0,
                    "{algorithm:?} must reject the dead initial link"
                );
                if restore {
                    let Outcome::Solved(solution) = outcome else {
                        panic!("{algorithm:?} lost the later achiever");
                    };
                    assert_eq!(solution.operators, vec![0, 1]);
                    assert_eq!(solution.plan.cost, 10);
                } else {
                    assert!(matches!(outcome, Outcome::NoSolution), "{algorithm:?}");
                }
            }
        }
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
            child.open_conditions().cloned().collect::<Vec<_>>(),
            vec![OpenCondition {
                consumer: 2,
                condition: Fact::new(2, 1),
            }]
        );
        assert!(child.threats(&task).is_empty());
        assert_eq!(child.threats(&task), child.rediscover_threats(&task));
        assert!(child.effect_cannot_fire(&task, child.step(2).unwrap(), 1));

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
        plan.push_open(OpenCondition {
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
        plan.push_open(OpenCondition {
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
        let plan = PartialPlan::assemble(
            vec![Step { id: 1, operator: 1 }],
            vec![],
            vec![open.clone()],
            orderings,
            vec![],
            1,
            2,
        );
        let planner = Planner::new(&task);
        let child = planner
            .add_step(
                &plan,
                &Achiever {
                    operator: 0,
                    effect: 0,
                },
                plan.orderings
                    .refine_with_step(
                        Ordering::new(
                            plan.next_step_id,
                            StepTime::AtEnd,
                            open.consumer,
                            StepTime::AtStart,
                        ),
                        plan.next_step_id,
                    )
                    .unwrap(),
                Chain::new(
                    CausalLink {
                        producer: plan.next_step_id,
                        consumer: open.consumer,
                        condition: open.condition,
                        effect: Some(0),
                    },
                    plan.links.clone(),
                ),
                &mut NewStepOpenConditions::new(&plan, &open, false),
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
