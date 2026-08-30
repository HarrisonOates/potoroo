//! Native landmark-cut evaluation over a delete-relaxed finite-domain task.
//!
//! Facts are propositionized finite-domain equalities. Different values of one
//! SAS+ variable may therefore coexist in the relaxed fact set, as usual for
//! delete-relaxation heuristics. The evaluator accepts node-specific initial
//! facts and goals so one preprocessed operator graph can serve every POCL node.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use thiserror::Error;

use crate::fdr::{Fact, Task};
use crate::params::ActionCost;

const UNREACHED: u32 = u32::MAX;

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub(crate) enum BuildError {
    #[error(
        "operator `{operator}` has conditional effects, which native LM-cut does not yet support"
    )]
    ConditionalEffects { operator: String },
    #[error("operator `{operator}` cost {cost} exceeds native LM-cut's u32 range")]
    ActionCostTooLarge { operator: String, cost: usize },
    #[error("LM-cut action references fact {fact}, but the task has only {num_facts} facts")]
    InvalidFact { fact: usize, num_facts: usize },
}

#[derive(Debug, Clone)]
pub(crate) struct RelaxedAction {
    preconditions: Vec<usize>,
    effects: Vec<usize>,
    cost: u32,
}

impl RelaxedAction {
    pub(crate) fn new(preconditions: Vec<usize>, effects: Vec<usize>, cost: u32) -> Self {
        RelaxedAction {
            preconditions,
            effects,
            cost,
        }
    }
}

/// A preprocessed relaxed operator graph. Initial facts and goals are supplied
/// to [`evaluate`](Self::evaluate), allowing a single graph to serve all nodes.
#[derive(Debug, Clone)]
pub(crate) struct RelaxedTask {
    num_facts: usize,
    actions: Vec<RelaxedAction>,
    precondition_of: Vec<Vec<usize>>,
    effect_of: Vec<Vec<usize>>,
    no_preconditions: Vec<usize>,
}

impl RelaxedTask {
    pub(crate) fn new(
        num_facts: usize,
        mut actions: Vec<RelaxedAction>,
    ) -> Result<Self, BuildError> {
        let mut precondition_of = vec![Vec::new(); num_facts];
        let mut effect_of = vec![Vec::new(); num_facts];
        let mut no_preconditions = Vec::new();

        for (action_id, action) in actions.iter_mut().enumerate() {
            action.preconditions.sort_unstable();
            action.preconditions.dedup();
            action.effects.sort_unstable();
            action.effects.dedup();

            for &fact in action.preconditions.iter().chain(&action.effects) {
                if fact >= num_facts {
                    return Err(BuildError::InvalidFact { fact, num_facts });
                }
            }
            if action.preconditions.is_empty() {
                no_preconditions.push(action_id);
            } else {
                for &fact in &action.preconditions {
                    precondition_of[fact].push(action_id);
                }
            }
            for &fact in &action.effects {
                effect_of[fact].push(action_id);
            }
        }

        Ok(RelaxedTask {
            num_facts,
            actions,
            precondition_of,
            effect_of,
            no_preconditions,
        })
    }

    /// Evaluates LM-cut. `None` denotes a relaxed-unreachable goal.
    pub(crate) fn evaluate(&self, initial: &[usize], goals: &[usize]) -> Option<u32> {
        if goals.is_empty() {
            return Some(0);
        }
        if initial
            .iter()
            .chain(goals)
            .any(|&fact| fact >= self.num_facts)
        {
            return None;
        }

        let mut residual_costs = self
            .actions
            .iter()
            .map(|action| action.cost)
            .collect::<Vec<_>>();
        let mut total = 0u32;

        loop {
            let hmax = self.hmax(initial, &residual_costs);
            let mut goal_supporter = None;
            let mut goal_cost = 0u32;
            for &goal in goals {
                let cost = hmax.fact_costs[goal];
                if cost == UNREACHED {
                    return None;
                }
                if goal_supporter.is_none() || cost > goal_cost {
                    goal_supporter = Some(goal);
                    goal_cost = cost;
                }
            }
            if goal_cost == 0 {
                return Some(total);
            }

            // The artificial zero-cost goal action selects one maximum-cost
            // goal as its h_max supporter. Follow zero-cost achievers backwards
            // to obtain the complete goal plateau.
            let mut goal_zone = vec![false; self.num_facts];
            let mut plateau = vec![goal_supporter.expect("non-empty goals have a supporter")];
            while let Some(fact) = plateau.pop() {
                if goal_zone[fact] {
                    continue;
                }
                goal_zone[fact] = true;
                for &action_id in &self.effect_of[fact] {
                    if residual_costs[action_id] != 0 || !hmax.reached[action_id] {
                        continue;
                    }
                    if let Some(supporter) = hmax.supporters[action_id] {
                        if !goal_zone[supporter] {
                            plateau.push(supporter);
                        }
                    }
                }
            }

            // Explore the justification graph from the relaxed initial state.
            // An action enters the cut when its selected h_max-support edge
            // crosses from the before-goal region into the goal plateau.
            let start = self.num_facts;
            let mut before = vec![false; self.num_facts + 1];
            let mut queue = Vec::with_capacity(self.num_facts + 1);
            before[start] = true;
            queue.push(start);
            for &fact in initial {
                if !goal_zone[fact] && !before[fact] {
                    before[fact] = true;
                    queue.push(fact);
                }
            }

            let mut in_cut = vec![false; self.actions.len()];
            let mut cut = Vec::new();
            while let Some(node) = queue.pop() {
                let action_ids: &[usize] = if node == start {
                    &self.no_preconditions
                } else {
                    &self.precondition_of[node]
                };
                for &action_id in action_ids {
                    let selected = match hmax.supporters[action_id] {
                        Some(supporter) => supporter == node,
                        None => node == start && hmax.reached[action_id],
                    };
                    if !selected {
                        continue;
                    }
                    if self.actions[action_id]
                        .effects
                        .iter()
                        .any(|&effect| goal_zone[effect])
                    {
                        if residual_costs[action_id] > 0 && !in_cut[action_id] {
                            in_cut[action_id] = true;
                            cut.push(action_id);
                        }
                        continue;
                    }
                    for &effect in &self.actions[action_id].effects {
                        if !before[effect] {
                            before[effect] = true;
                            queue.push(effect);
                        }
                    }
                }
            }

            let cut_cost = cut
                .iter()
                .map(|&action_id| residual_costs[action_id])
                .min()?;
            if cut_cost == 0 {
                return None;
            }
            total = total.saturating_add(cut_cost);
            for action_id in cut {
                residual_costs[action_id] -= cut_cost;
            }
        }
    }

    fn hmax(&self, initial: &[usize], residual_costs: &[u32]) -> HMaxValues {
        let mut fact_costs = vec![UNREACHED; self.num_facts];
        let mut unsatisfied = self
            .actions
            .iter()
            .map(|action| action.preconditions.len())
            .collect::<Vec<_>>();
        let mut supporters = vec![None; self.actions.len()];
        let mut reached = vec![false; self.actions.len()];
        let mut queue = BinaryHeap::new();

        let enqueue =
            |fact: usize,
             cost: u32,
             fact_costs: &mut [u32],
             queue: &mut BinaryHeap<(Reverse<u32>, Reverse<usize>)>| {
                if cost < fact_costs[fact] {
                    fact_costs[fact] = cost;
                    queue.push((Reverse(cost), Reverse(fact)));
                }
            };

        for &fact in initial {
            enqueue(fact, 0, &mut fact_costs, &mut queue);
        }
        for &action_id in &self.no_preconditions {
            reached[action_id] = true;
            let target = residual_costs[action_id];
            for &effect in &self.actions[action_id].effects {
                enqueue(effect, target, &mut fact_costs, &mut queue);
            }
        }

        while let Some((Reverse(popped_cost), Reverse(fact))) = queue.pop() {
            if popped_cost != fact_costs[fact] {
                continue;
            }
            for &action_id in &self.precondition_of[fact] {
                debug_assert!(unsatisfied[action_id] > 0);
                unsatisfied[action_id] -= 1;
                if unsatisfied[action_id] != 0 {
                    continue;
                }
                reached[action_id] = true;
                supporters[action_id] = Some(fact);
                let target = popped_cost.saturating_add(residual_costs[action_id]);
                for &effect in &self.actions[action_id].effects {
                    enqueue(effect, target, &mut fact_costs, &mut queue);
                }
            }
        }

        HMaxValues {
            fact_costs,
            supporters,
            reached,
        }
    }
}

struct HMaxValues {
    fact_costs: Vec<u32>,
    supporters: Vec<Option<usize>>,
    reached: Vec<bool>,
}

/// FDR-specific adapter used by ground POCL search. It propositionizes each
/// finite-domain equality while retaining multi-effect action labels.
pub(crate) struct FdrLmCut {
    relaxation: RelaxedTask,
    offsets: Vec<usize>,
    initial: Vec<usize>,
}

impl FdrLmCut {
    pub(crate) fn new(task: &Task, action_cost: ActionCost) -> Result<Self, BuildError> {
        let mut offsets = Vec::with_capacity(task.variables.len());
        let mut num_facts = 0usize;
        for variable in &task.variables {
            offsets.push(num_facts);
            num_facts += variable.values.len();
        }
        let encode = |fact: Fact| offsets[fact.variable] + fact.value;

        let mut actions = Vec::with_capacity(task.operators.len());
        for operator in &task.operators {
            if operator
                .effects
                .iter()
                .any(|effect| !effect.conditions.is_empty())
            {
                return Err(BuildError::ConditionalEffects {
                    operator: operator.name.clone(),
                });
            }
            let resolved_cost = action_cost.resolve(operator.cost);
            let cost =
                u32::try_from(resolved_cost).map_err(|_| BuildError::ActionCostTooLarge {
                    operator: operator.name.clone(),
                    cost: resolved_cost,
                })?;
            actions.push(RelaxedAction::new(
                operator.preconditions().into_iter().map(encode).collect(),
                operator
                    .effects
                    .iter()
                    .map(|effect| encode(effect.assignment()))
                    .collect(),
                cost,
            ));
        }
        for (variable, values) in task.variables.iter().enumerate() {
            if !task.is_derived_variable(variable) {
                continue;
            }
            for value in 0..values.values.len() {
                let fact = Fact::new(variable, value);
                for support in task
                    .derived_supports(fact)
                    .expect("derived variable has support clauses")
                {
                    actions.push(RelaxedAction::new(
                        support.into_iter().map(encode).collect(),
                        vec![encode(fact)],
                        0,
                    ));
                }
            }
        }
        let initial = task
            .initial
            .iter()
            .enumerate()
            .filter(|(variable, _)| !task.is_derived_variable(*variable))
            .map(|(variable, &value)| offsets[variable] + value)
            .collect();

        Ok(FdrLmCut {
            relaxation: RelaxedTask::new(num_facts, actions)?,
            offsets,
            initial,
        })
    }

    pub(crate) fn evaluate(
        &self,
        reusable: impl IntoIterator<Item = Fact>,
        goals: impl IntoIterator<Item = Fact>,
    ) -> Option<u32> {
        let mut initial = self.initial.clone();
        initial.extend(reusable.into_iter().map(|fact| self.encode(fact)));
        let goals = goals
            .into_iter()
            .map(|fact| self.encode(fact))
            .collect::<Vec<_>>();
        self.relaxation.evaluate(&initial, &goals)
    }

    fn encode(&self, fact: Fact) -> usize {
        self.offsets[fact.variable] + fact.value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn action(preconditions: &[usize], effects: &[usize]) -> RelaxedAction {
        RelaxedAction::new(preconditions.to_vec(), effects.to_vec(), 1)
    }

    #[test]
    fn satisfied_and_unreachable_goals() {
        let task = RelaxedTask::new(1, vec![]).unwrap();
        assert_eq!(task.evaluate(&[0], &[0]), Some(0));
        assert_eq!(task.evaluate(&[], &[0]), None);
        assert_eq!(task.evaluate(&[], &[]), Some(0));
    }

    #[test]
    fn serial_chain_costs_every_action() {
        let task = RelaxedTask::new(
            3,
            vec![action(&[], &[0]), action(&[0], &[1]), action(&[1], &[2])],
        )
        .unwrap();
        assert_eq!(task.evaluate(&[], &[2]), Some(3));
    }

    #[test]
    fn joint_cut_is_stronger_than_hmax_on_a_fork() {
        // make-p is shared, but reaching q and r still needs both branch actions:
        // h_max is 2 while LM-cut is 3.
        let task = RelaxedTask::new(
            3,
            vec![action(&[], &[0]), action(&[0], &[1]), action(&[0], &[2])],
        )
        .unwrap();
        assert_eq!(task.evaluate(&[], &[1, 2]), Some(3));
    }

    #[test]
    fn one_multi_effect_action_is_charged_once() {
        let task = RelaxedTask::new(2, vec![action(&[], &[0, 1])]).unwrap();
        assert_eq!(task.evaluate(&[], &[0, 1]), Some(1));
    }

    #[test]
    fn zero_cost_actions_extend_the_goal_plateau() {
        let task = RelaxedTask::new(
            2,
            vec![action(&[], &[0]), RelaxedAction::new(vec![0], vec![1], 0)],
        )
        .unwrap();
        assert_eq!(task.evaluate(&[], &[1]), Some(1));
    }
}
