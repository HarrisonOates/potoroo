//! Ground POCL search directly over a translated SAS+ task.
//!
//! Conditions and causal links protect [`Fact`](crate::fdr::Fact) equalities,
//! while effects are finite-domain assignments. Consequently, assigning *any
//! other value* to the same variable is a causal threat, even when there is no
//! explicit delete fact. The refinement semantics stay representation-specific,
//! while plan ranking, flaw-order configuration, search algorithms, limits, and
//! statistics follow the main search implementation.

use std::borrow::Cow;
use std::cmp::Ordering as CmpOrdering;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::rc::Rc;
use std::time::Instant;

use thiserror::Error;

use crate::external::FdError;
use crate::fdr::{Fact, ParseError, Task};
use crate::heuristics::{HVal, OrderType, SelectionCriterion};
use crate::lmcut::{BuildError as LmCutBuildError, FdrLmCut};
use crate::orderings::{BinaryOrderings, Ordering, StepTime};
use crate::params::{ActionCost, Parameters, SearchAlgorithm};
use crate::plan::{GOAL_ID, INIT_ID};
use crate::search::SearchContext;

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

/// An assignment that can occur inside a causal link's protected interval.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Threat {
    pub step: usize,
    pub effect: usize,
    pub link: usize,
}

/// One immutable-by-convention finite-domain POCL search node.
#[derive(Debug, Clone)]
pub struct PartialPlan {
    pub steps: Rc<Vec<Step>>,
    pub links: Rc<Vec<CausalLink>>,
    pub open_conditions: Rc<Vec<OpenCondition>>,
    pub orderings: Rc<BinaryOrderings>,
    threats: Rc<Vec<Threat>>,
    /// Accumulated cost of committed operators.
    pub cost: usize,
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
            cost: 0,
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
                    if effect_clobbers(effect.variable, effect.post, link.condition) {
                        threats.push(Threat {
                            step: step.id,
                            effect: effect_index,
                            link: link_index,
                        });
                    }
                }
            }
        }
        threats
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
            Rc::make_mut(&mut self.open_conditions).push(open);
        }
    }

    fn threat_active(&self, task: &Task, threat: &Threat) -> bool {
        let Some(link) = self.links.get(threat.link) else {
            return false;
        };
        if threat.step == link.producer || threat.step == link.consumer {
            return false;
        }
        let Some(step) = threat
            .step
            .checked_sub(1)
            .and_then(|index| self.steps.get(index))
            .filter(|step| step.id == threat.step)
        else {
            return false;
        };
        let Some(effect) = task.operators[step.operator].effects.get(threat.effect) else {
            return false;
        };
        self.can_be_inside(step.id, link)
            && effect_clobbers(effect.variable, effect.post, link.condition)
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
                if effect_clobbers(effect.variable, effect.post, link.condition) {
                    additions.push(Threat {
                        step: step.id,
                        effect: effect_index,
                        link: link_index,
                    });
                }
            }
        }
        let threats = Rc::make_mut(&mut self.threats);
        debug_assert!(threats
            .last()
            .zip(additions.first())
            .is_none_or(|(existing, addition)| threat_key(existing) < threat_key(addition)));
        threats.extend(additions);
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
                if effect_clobbers(effect.variable, effect.post, link.condition) {
                    additions.push(Threat {
                        step: step.id,
                        effect: effect_index,
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
    let planner = Planner::with_action_cost(task, params.action_cost);
    planner.validate_params(params)?;
    Ok(planner.solve(params))
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
                HVal::SampleFf(_) | HVal::Lplan | HVal::Compile(_) => {
                    return Err(Error::Unsupported(
                        "SAMPLE_FF, LPLAN, and COMPILE heuristics operate on the literal plan representation"
                            .to_string(),
                    ));
                }
            }
        }
        Ok(())
    }

    fn solve(&self, params: &Parameters) -> (Outcome, SearchStats) {
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

        let initial = Rc::new(PartialPlan::initial(self.task));
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
                    Rc::make_mut(&mut child.open_conditions).swap_remove(open_index);
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
                for achiever in achievers.iter().filter(|a| a.operator == step.operator) {
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
        Rc::make_mut(&mut child.open_conditions).swap_remove(open_index);
        let link_index = child.links.len();
        Rc::make_mut(&mut child.links).push(CausalLink {
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
        child.retain_active_threats(self.task);
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
        Rc::make_mut(&mut child.steps).push(Step {
            id: new_id,
            operator: achiever.operator,
        });
        Rc::make_mut(&mut child.open_conditions).swap_remove(open_index);
        let link_index = child.links.len();
        Rc::make_mut(&mut child.links).push(CausalLink {
            producer: new_id,
            consumer: open.consumer,
            condition: open.condition,
            effect: Some(achiever.effect),
        });
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
        child.retain_active_threats(self.task);
        child.add_link_threats(self.task, link_index);
        child.add_step_threats(self.task, new_id);
        Some(child)
    }

    fn resolve_threat(&self, plan: &PartialPlan, threat: &Threat) -> Vec<PartialPlan> {
        let link = &plan.links[threat.link];
        let mut children = Vec::with_capacity(2);

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
                child.retain_active_threats(self.task);
                children.push(child);
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
                child.retain_active_threats(self.task);
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
            if criterion.non_separable {
                for (index, threat) in threats.iter().enumerate() {
                    let refinements = self.threat_refinement_count(plan, threat);
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
                .any(|effect| effect_clobbers(effect.variable, effect.post, open.condition))
        })
    }

    fn threat_refinement_count(&self, plan: &PartialPlan, threat: &Threat) -> i32 {
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
        i32::from(demote) + i32::from(promote)
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
                            .filter(|achiever| achiever.operator == step.operator)
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
                    ) && achievers
                        .iter()
                        .any(|achiever| achiever.operator == step.operator)
                })
            })
    }

    fn rank_both(
        &self,
        plan: &PartialPlan,
        params: &Parameters,
        stats: &mut SearchStats,
    ) -> (Vec<f32>, Vec<f32>) {
        let start = Instant::now();
        let result = self.compute_rank_both(plan, params);
        stats.h_evals += 1;
        stats.h_eval_nanos += start.elapsed().as_nanos();
        stats.h_eval_ms = stats.h_eval_nanos / 1_000_000;
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
                HVal::SampleFf(_) | HVal::Lplan | HVal::Compile(_) => {
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
                        .map(|effect| effect.assignment())
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
            for effect in &self.task.operators[step.operator].effects {
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
                        .map(|effect| effect.assignment())
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

fn is_ordered_before(orderings: &BinaryOrderings, before: usize, after: usize) -> bool {
    before != after && !orderings.possibly_before(after, StepTime::AtEnd, before, StepTime::AtStart)
}

#[derive(Debug, Clone)]
enum SelectedFlaw {
    Threat(Threat),
    Open(usize),
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
        }
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
