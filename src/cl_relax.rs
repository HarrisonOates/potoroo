//! Native SAS+ evaluation of the causal-link relaxation
//! (Bercher, Geier & Biundo, KI 2013).
//!
//! Committed steps become zero-cost operators. Their preconditions and the
//! goal remain required; causal links require their producer's completion.
//! The relaxation does not enforce the full ordering closure. Conditional
//! effects retain their guards, suppressed effects are omitted, and axioms
//! provide zero-cost support. CLADD and CLFF are not admissible.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use crate::fdr::{Fact, Task};
use crate::params::ActionCost;

/// One relaxed action: the operators' effects, one action each, and the
/// axioms' support clauses.
#[derive(Debug, Clone)]
struct StaticAction {
    preconditions: Vec<usize>,
    effect: usize,
    cost: u32,
    /// The operator this effect belongs to, so a relaxed plan counts an
    /// operator once however many of its effects it uses. `None` for an
    /// axiom.
    operator: Option<usize>,
}

/// A committed step, as the caller describes it at each node.
#[derive(Debug, Clone, Default)]
pub struct CompiledStep {
    /// The step's preconditions, as [`CompiledRelaxation::encode`] facts.
    pub preconditions: Vec<usize>,
    /// Indices (into the step list) of the step's immediate necessary
    /// predecessors.
    pub predecessors: Vec<usize>,
    /// Unconditional effects the step can still produce.
    pub effects: Vec<usize>,
    /// Conditional effects the step can still produce: the conditions, then
    /// the assignment.
    pub conditional_effects: Vec<(Vec<usize>, usize)>,
}

/// Both estimates from one evaluation.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Estimate {
    /// `h_add`: the sum over goals of each goal's cheapest relaxed cost.
    pub add: f32,
    /// `h_FF`: the cost of one relaxed plan, each operator counted once.
    pub ff: f32,
}

/// The static half of the relaxed task: the operators and axioms, ready to be
/// joined by a node's steps.
#[derive(Debug, Clone)]
pub struct CompiledRelaxation {
    offsets: Vec<usize>,
    num_facts: usize,
    actions: Vec<StaticAction>,
    precondition_of: Vec<Vec<usize>>,
    no_preconditions: Vec<usize>,
    initial: Vec<usize>,
    goals: Vec<usize>,
    num_operators: usize,
}

const UNREACHED: u32 = u32::MAX;

impl CompiledRelaxation {
    /// `effect_requirements[o][e]` are the facts effect `e` of operator `o`
    /// needs: the operator's preconditions and the effect's conditions.
    pub fn new(
        task: &Task,
        effect_requirements: &[Vec<Vec<Fact>>],
        action_cost: ActionCost,
    ) -> Self {
        let mut offsets = Vec::with_capacity(task.variables.len());
        let mut num_facts = 0usize;
        for variable in &task.variables {
            offsets.push(num_facts);
            num_facts += variable.values.len();
        }
        let encode = |fact: Fact| offsets[fact.variable] + fact.value;

        let mut actions = Vec::new();
        for (operator_index, operator) in task.operators.iter().enumerate() {
            let cost = u32::try_from(action_cost.resolve(operator.cost)).unwrap_or(u32::MAX / 4);
            for (effect_index, effect) in operator.effects.iter().enumerate() {
                let mut preconditions: Vec<usize> = effect_requirements[operator_index]
                    [effect_index]
                    .iter()
                    .map(|&fact| encode(fact))
                    .collect();
                preconditions.sort_unstable();
                preconditions.dedup();
                actions.push(StaticAction {
                    preconditions,
                    effect: encode(effect.assignment()),
                    cost,
                    operator: Some(operator_index),
                });
            }
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
                    let mut preconditions: Vec<usize> = support.into_iter().map(encode).collect();
                    preconditions.sort_unstable();
                    preconditions.dedup();
                    actions.push(StaticAction {
                        preconditions,
                        effect: encode(fact),
                        cost: 0,
                        operator: None,
                    });
                }
            }
        }

        let mut precondition_of = vec![Vec::new(); num_facts];
        let mut no_preconditions = Vec::new();
        for (index, action) in actions.iter().enumerate() {
            if action.preconditions.is_empty() {
                no_preconditions.push(index);
            }
            for &fact in &action.preconditions {
                precondition_of[fact].push(index);
            }
        }
        let initial = task
            .initial
            .iter()
            .enumerate()
            .filter(|(variable, _)| !task.is_derived_variable(*variable))
            .map(|(variable, &value)| offsets[variable] + value)
            .collect();
        let goals = task.goals.iter().map(|&fact| encode(fact)).collect();

        CompiledRelaxation {
            offsets,
            num_facts,
            actions,
            precondition_of,
            no_preconditions,
            initial,
            goals,
            num_operators: task.operators.len(),
        }
    }

    pub fn encode(&self, fact: Fact) -> usize {
        self.offsets[fact.variable] + fact.value
    }

    pub fn decode(&self, fact: usize) -> Fact {
        let variable = self.offsets.partition_point(|&offset| offset <= fact) - 1;
        Fact::new(variable, fact - self.offsets[variable])
    }

    /// The task's fact landmarks, by backchaining over first achievers: a
    /// landmark's first achievers are the actions producing it that become
    /// applicable in a relaxed exploration in which it is never asserted, and
    /// a fact every first achiever requires is a landmark too (Richter,
    /// Helmert & Westphal 2008, without the disjunctive landmarks). The task
    /// goals seed it. Facts true initially are landmarks but are not chained
    /// from, since nothing need produce them.
    pub fn fact_landmarks(&self) -> Vec<Fact> {
        let mut initial = vec![false; self.num_facts];
        for &fact in &self.initial {
            initial[fact] = true;
        }
        let mut seen = vec![false; self.num_facts];
        let mut landmarks = Vec::new();
        let mut queue = Vec::new();
        for &goal in &self.goals {
            if !seen[goal] {
                seen[goal] = true;
                landmarks.push(goal);
                queue.push(goal);
            }
        }
        while let Some(landmark) = queue.pop() {
            if initial[landmark] {
                continue;
            }
            let achievers = self.first_achievers(landmark);
            let Some((&first, rest)) = achievers.split_first() else {
                continue;
            };
            let mut common: Vec<usize> = self.actions[first].preconditions.clone();
            for &achiever in rest {
                common.retain(|fact| self.actions[achiever].preconditions.contains(fact));
            }
            for fact in common {
                if !seen[fact] {
                    seen[fact] = true;
                    landmarks.push(fact);
                    queue.push(fact);
                }
            }
        }
        landmarks
            .into_iter()
            .map(|fact| self.decode(fact))
            .collect()
    }

    /// The actions producing `landmark` that become applicable when it is
    /// never asserted.
    fn first_achievers(&self, landmark: usize) -> Vec<usize> {
        let mut reached = vec![false; self.num_facts];
        let mut unsatisfied: Vec<usize> =
            self.actions.iter().map(|a| a.preconditions.len()).collect();
        let mut stack = Vec::new();
        let mut achievers = Vec::new();
        let settle = |action: usize,
                      reached: &mut [bool],
                      stack: &mut Vec<usize>,
                      achievers: &mut Vec<usize>| {
            let effect = self.actions[action].effect;
            if effect == landmark {
                achievers.push(action);
            } else if !reached[effect] {
                reached[effect] = true;
                stack.push(effect);
            }
        };
        for &fact in &self.initial {
            if fact != landmark && !reached[fact] {
                reached[fact] = true;
                stack.push(fact);
            }
        }
        for &action in &self.no_preconditions {
            settle(action, &mut reached, &mut stack, &mut achievers);
        }
        while let Some(fact) = stack.pop() {
            for &action in &self.precondition_of[fact] {
                unsatisfied[action] -= 1;
                if unsatisfied[action] == 0 {
                    settle(action, &mut reached, &mut stack, &mut achievers);
                }
            }
        }
        achievers
    }

    /// Evaluates the compiled task for a plan with these steps. `None` when
    /// some step can never run or some goal is unreachable — the plan has no
    /// completion.
    pub fn evaluate(&self, steps: &[CompiledStep]) -> Option<Estimate> {
        // Facts: the task's, then `done(s)` for each step. Actions: the
        // static ones, then per step one `run` action and one per conditional
        // effect, all zero-cost.
        let num_facts = self.num_facts + steps.len();
        let done = |step: usize| self.num_facts + step;
        let mut dynamic: Vec<(Vec<usize>, Vec<usize>)> = Vec::new();
        for (index, step) in steps.iter().enumerate() {
            let mut preconditions = step.preconditions.clone();
            preconditions.extend(step.predecessors.iter().map(|&p| done(p)));
            preconditions.sort_unstable();
            preconditions.dedup();
            let mut effects = step.effects.clone();
            effects.push(done(index));
            dynamic.push((preconditions, effects));
            for (conditions, effect) in &step.conditional_effects {
                let mut preconditions = conditions.clone();
                preconditions.push(done(index));
                preconditions.sort_unstable();
                preconditions.dedup();
                dynamic.push((preconditions, vec![*effect]));
            }
        }
        // Dynamic precondition index, as sorted pairs.
        let mut dynamic_pre: Vec<(usize, usize)> = dynamic
            .iter()
            .enumerate()
            .flat_map(|(a, (pre, _))| pre.iter().map(move |&f| (f, a)))
            .collect();
        dynamic_pre.sort_unstable();

        let num_static = self.actions.len();
        let mut fact_cost = vec![UNREACHED; num_facts];
        let mut achiever: Vec<Option<usize>> = vec![None; num_facts];
        let mut unsatisfied: Vec<usize> = self
            .actions
            .iter()
            .map(|a| a.preconditions.len())
            .chain(dynamic.iter().map(|(pre, _)| pre.len()))
            .collect();
        let mut pre_sum: Vec<u32> = vec![0; num_static + dynamic.len()];
        let mut queue: BinaryHeap<(Reverse<u32>, Reverse<usize>)> = BinaryHeap::new();

        let relax = |fact: usize,
                     cost: u32,
                     by: Option<usize>,
                     fact_cost: &mut [u32],
                     achiever: &mut [Option<usize>],
                     queue: &mut BinaryHeap<(Reverse<u32>, Reverse<usize>)>| {
            if cost < fact_cost[fact] {
                fact_cost[fact] = cost;
                achiever[fact] = by;
                queue.push((Reverse(cost), Reverse(fact)));
            }
        };
        for &fact in &self.initial {
            relax(fact, 0, None, &mut fact_cost, &mut achiever, &mut queue);
        }
        for &action in &self.no_preconditions {
            let a = &self.actions[action];
            relax(
                a.effect,
                a.cost,
                Some(action),
                &mut fact_cost,
                &mut achiever,
                &mut queue,
            );
        }
        for (index, (pre, effects)) in dynamic.iter().enumerate() {
            if pre.is_empty() {
                for &effect in effects {
                    relax(
                        effect,
                        0,
                        Some(num_static + index),
                        &mut fact_cost,
                        &mut achiever,
                        &mut queue,
                    );
                }
            }
        }

        while let Some((Reverse(cost), Reverse(fact))) = queue.pop() {
            if cost != fact_cost[fact] {
                continue;
            }
            let fire =
                |action: usize,
                 unsatisfied: &mut [usize],
                 pre_sum: &mut [u32],
                 fact_cost: &mut [u32],
                 achiever: &mut [Option<usize>],
                 queue: &mut BinaryHeap<(Reverse<u32>, Reverse<usize>)>| {
                    unsatisfied[action] -= 1;
                    pre_sum[action] = pre_sum[action].saturating_add(cost);
                    if unsatisfied[action] != 0 {
                        return;
                    }
                    if action < num_static {
                        let a = &self.actions[action];
                        let value = pre_sum[action].saturating_add(a.cost);
                        relax(a.effect, value, Some(action), fact_cost, achiever, queue);
                    } else {
                        let value = pre_sum[action];
                        for &effect in &dynamic[action - num_static].1 {
                            relax(effect, value, Some(action), fact_cost, achiever, queue);
                        }
                    }
                };
            if fact < self.num_facts {
                for &action in &self.precondition_of[fact] {
                    fire(
                        action,
                        &mut unsatisfied,
                        &mut pre_sum,
                        &mut fact_cost,
                        &mut achiever,
                        &mut queue,
                    );
                }
            }
            let start = dynamic_pre.partition_point(|&(f, _)| f < fact);
            for &(f, action) in &dynamic_pre[start..] {
                if f != fact {
                    break;
                }
                fire(
                    num_static + action,
                    &mut unsatisfied,
                    &mut pre_sum,
                    &mut fact_cost,
                    &mut achiever,
                    &mut queue,
                );
            }
        }

        // Goals: every step has run, and the task goals hold.
        let goals = (0..steps.len()).map(done).chain(self.goals.iter().copied());
        let mut add: u32 = 0;
        let mut stack: Vec<usize> = Vec::new();
        for goal in goals {
            let cost = fact_cost[goal];
            if cost == UNREACHED {
                return None;
            }
            add = add.saturating_add(cost);
            stack.push(goal);
        }

        // FF extraction: walk each goal back through its achiever, counting an
        // operator once.
        let mut marked = vec![false; num_facts];
        let mut chosen = vec![false; num_static + dynamic.len()];
        let mut operators_chosen: Vec<bool> = vec![false; self.num_operators];
        let mut ff: u32 = 0;
        while let Some(fact) = stack.pop() {
            if marked[fact] {
                continue;
            }
            marked[fact] = true;
            let Some(action) = achiever[fact] else {
                continue;
            };
            if chosen[action] {
                continue;
            }
            chosen[action] = true;
            if action < num_static {
                let a = &self.actions[action];
                if let Some(operator) = a.operator {
                    if !operators_chosen[operator] {
                        operators_chosen[operator] = true;
                        ff = ff.saturating_add(a.cost);
                    }
                }
                stack.extend(a.preconditions.iter().copied());
            } else {
                stack.extend(dynamic[action - num_static].0.iter().copied());
            }
        }

        Some(Estimate {
            add: add as f32,
            ff: ff as f32,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fdr::{Effect, Operator, Variable};

    /// Two binary variables `a`, `b`; `set-a` makes `a` true for 1; `set-b`
    /// needs `a` and makes `b` true for 2. Goal: `b`.
    fn task() -> Task {
        let binary = |name: &str| Variable {
            name: name.to_string(),
            values: vec!["false".to_string(), "true".to_string()],
        };
        Task {
            variables: vec![binary("a"), binary("b")],
            mutex_groups: vec![],
            initial: vec![0, 0],
            goals: vec![Fact::new(1, 1)],
            operators: vec![
                Operator {
                    name: "set-a".to_string(),
                    prevail: vec![],
                    effects: vec![Effect {
                        conditions: vec![],
                        variable: 0,
                        pre: None,
                        post: 1,
                    }],
                    cost: 1,
                },
                Operator {
                    name: "set-b".to_string(),
                    prevail: vec![Fact::new(0, 1)],
                    effects: vec![Effect {
                        conditions: vec![],
                        variable: 1,
                        pre: None,
                        post: 1,
                    }],
                    cost: 2,
                },
            ],
            axioms: vec![],
        }
    }

    fn relaxation(task: &Task) -> CompiledRelaxation {
        let requirements: Vec<Vec<Vec<Fact>>> = task
            .operators
            .iter()
            .map(|o| o.effects.iter().map(|_| o.preconditions()).collect())
            .collect();
        CompiledRelaxation::new(task, &requirements, ActionCost::Task)
    }

    #[test]
    fn the_empty_plan_is_charged_the_whole_relaxed_plan() {
        let task = task();
        let r = relaxation(&task);
        assert_eq!(r.evaluate(&[]), Some(Estimate { add: 3.0, ff: 3.0 }));
    }

    #[test]
    fn a_committed_step_is_free_once_it_can_run() {
        let task = task();
        let r = relaxation(&task);
        // `set-b` committed: its precondition `a` still costs 1; the step is free.
        let step = CompiledStep {
            preconditions: vec![r.encode(Fact::new(0, 1))],
            predecessors: vec![],
            effects: vec![r.encode(Fact::new(1, 1))],
            conditional_effects: vec![],
        };
        assert_eq!(r.evaluate(&[step]), Some(Estimate { add: 2.0, ff: 1.0 }));
        // Both committed and ordered: nothing left to pay.
        let set_a = CompiledStep {
            preconditions: vec![],
            predecessors: vec![],
            effects: vec![r.encode(Fact::new(0, 1))],
            conditional_effects: vec![],
        };
        let set_b = CompiledStep {
            preconditions: vec![r.encode(Fact::new(0, 1))],
            predecessors: vec![0],
            effects: vec![r.encode(Fact::new(1, 1))],
            conditional_effects: vec![],
        };
        assert_eq!(
            r.evaluate(&[set_a, set_b]),
            Some(Estimate { add: 0.0, ff: 0.0 })
        );
    }

    #[test]
    fn landmarks_chain_through_the_only_achiever() {
        let task = task();
        let r = relaxation(&task);
        // `b` is the goal; its only achiever needs `a`, so `a` is a landmark.
        let mut landmarks = r.fact_landmarks();
        landmarks.sort();
        assert_eq!(landmarks, vec![Fact::new(0, 1), Fact::new(1, 1)]);
    }

    #[test]
    fn a_step_that_can_never_run_is_a_dead_end() {
        let task = task();
        let r = relaxation(&task);
        let step = CompiledStep {
            preconditions: vec![r.encode(Fact::new(1, 0)) + 100],
            ..CompiledStep::default()
        };
        // An out-of-range precondition never appears, so the step never runs.
        assert_eq!(r.evaluate(&[step]), None);
    }
}
