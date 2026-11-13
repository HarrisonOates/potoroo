//! Nguyen & Kambhampati (IJCAI 2001), §3, Equation (1), over SAS+ facts.
//!
//! https://rakaposhi.eas.asu.edu/ucpop-revive.pdf
//!
//! This is the ranking heuristic, not the complete RePOP planner. Build a
//! serial planning graph from the initial state, including competing needs
//! and inconsistent support. Regress the highest-first-appearance goal through
//! an earliest-layer achiever, retaining its preconditions and removing *all*
//! its effects. Charge zero for committed operators, one for other selections.
//! There is no persistent achieved-fact set or global selected-action discount.
//!
//! The paper leaves ties unspecified. We use descending fact index for equal
//! levels, then prefer a committed earliest-layer achiever, then operator order.
//! Only unconditional, axiom-free, unit-cost tasks are supported.

use std::collections::BTreeSet;

use crate::fdr::{Fact, Task};
use crate::memory::{SearchStop, StopReason};
use crate::params::{ActionCost, Parameters};

pub(crate) fn validate(task: &Task, costs: ActionCost) -> Result<(), String> {
    if !task.axioms.is_empty()
        || task.operators.iter().any(|op| {
            op.effects
                .iter()
                .any(|effect| !effect.conditions.is_empty())
        })
    {
        return Err("REPOP requires unconditional effects and no axioms".into());
    }
    if task.operators.iter().any(|op| costs.resolve(op.cost) != 1) {
        return Err(
            "REPOP implements the paper's unit-action count; use unit costs (-a UNIT)".into(),
        );
    }
    for op in &task.operators {
        for (i, effect) in op.effects.iter().enumerate() {
            if op.effects[..i]
                .iter()
                .any(|other| other.variable == effect.variable && other.post != effect.post)
            {
                return Err("REPOP requires consistent unconditional effects".into());
            }
        }
    }
    Ok(())
}

#[derive(Clone)]
struct Pairs {
    size: usize,
    bits: Vec<u64>,
}

impl Pairs {
    fn new(size: usize) -> Result<Self, StopReason> {
        let cells = size.checked_mul(size).ok_or(StopReason::Memory)?;
        let mut bits = Vec::new();
        bits.try_reserve_exact(cells.div_ceil(64))
            .map_err(|_| StopReason::Memory)?;
        bits.resize(cells.div_ceil(64), 0);
        Ok(Self { size, bits })
    }

    fn contains(&self, a: usize, b: usize) -> bool {
        let index = a * self.size + b;
        self.bits[index / 64] & (1 << (index % 64)) != 0
    }

    fn insert(&mut self, a: usize, b: usize) {
        for index in [a * self.size + b, b * self.size + a] {
            self.bits[index / 64] |= 1 << (index % 64);
        }
    }

    fn possible(&self, preconditions: &[usize]) -> bool {
        preconditions
            .iter()
            .enumerate()
            .all(|(i, &a)| preconditions[i..].iter().all(|&b| self.contains(a, b)))
    }
}

pub(crate) struct Graph {
    offsets: Vec<usize>,
    levels: Vec<usize>,
    achievers: Vec<Vec<usize>>,
    preconditions: Vec<Vec<usize>>,
    effects: Vec<Vec<usize>>,
}

impl Graph {
    pub(crate) fn build(task: &Task, params: &Parameters) -> Result<Self, StopReason> {
        let mut stop = SearchStop::new(params);
        let mut work = 0;
        let mut check = || {
            work += 1;
            match stop.as_mut().and_then(|s| s.expired(work)) {
                Some(reason) => Err(reason),
                None => Ok(()),
            }
        };
        check()?;
        let mut offsets = vec![0];
        let mut facts = Vec::new();
        for (variable, v) in task.variables.iter().enumerate() {
            facts.extend((0..v.values.len()).map(|value| Fact::new(variable, value)));
            offsets.push(facts.len());
        }
        let encode = |fact: Fact| offsets[fact.variable] + fact.value;
        let initial: Vec<_> = task
            .initial
            .iter()
            .enumerate()
            .map(|(variable, &value)| encode(Fact::new(variable, value)))
            .collect();
        let preconditions: Vec<Vec<_>> = task
            .operators
            .iter()
            .map(|op| op.preconditions().into_iter().map(encode).collect())
            .collect();
        let effects: Vec<Vec<_>> = task
            .operators
            .iter()
            .map(|op| op.effects.iter().map(|e| encode(e.assignment())).collect())
            .collect();
        let mut levels = vec![usize::MAX; facts.len()];
        let mut achievers = vec![Vec::new(); facts.len()];
        let mut pairs = Pairs::new(facts.len())?;
        for &a in &initial {
            levels[a] = 0;
            for &b in &initial {
                pairs.insert(a, b);
            }
        }
        let mut layer = 0;
        loop {
            check()?;
            layer += 1;
            let mut next = pairs.clone(); // persistence/persistence supports
            for (op, required) in preconditions.iter().enumerate() {
                check()?;
                if !pairs.possible(required) {
                    continue;
                }
                for &effect in &effects[op] {
                    if levels[effect] == usize::MAX {
                        achievers[effect].push(op);
                    }
                    // Two effects of the SAME action can coexist. Distinct
                    // real actions are mutex in a serial planning graph.
                    for &other in &effects[op] {
                        next.insert(effect, other);
                    }
                }
                // Action/persistence supports: the fact must coexist with
                // every precondition and survive all assignments of the action.
                for (q, fact) in facts.iter().enumerate() {
                    if q % 128 == 0 {
                        check()?;
                    }
                    if !pairs.contains(q, q)
                        || effects[op]
                            .iter()
                            .any(|&e| facts[e].variable == fact.variable && e != q)
                        || required.iter().any(|&p| !pairs.contains(p, q))
                    {
                        continue;
                    }
                    for &effect in &effects[op] {
                        next.insert(effect, q);
                    }
                }
            }
            if next.bits == pairs.bits {
                break;
            }
            for (fact, level) in levels.iter_mut().enumerate() {
                if *level == usize::MAX && next.contains(fact, fact) {
                    *level = layer;
                }
            }
            pairs = next;
        }
        Ok(Self {
            offsets,
            levels,
            achievers,
            preconditions,
            effects,
        })
    }

    pub(crate) fn estimate(
        &self,
        goals: impl IntoIterator<Item = Fact>,
        committed: impl IntoIterator<Item = usize>,
    ) -> Option<f32> {
        let mut existing = vec![false; self.effects.len()];
        for op in committed {
            existing[op] = true;
        }
        let mut pending = BTreeSet::new();
        for fact in goals {
            let id = self.offsets[fact.variable] + fact.value;
            match self.levels[id] {
                usize::MAX => return None,
                0 => {}
                level => {
                    pending.insert((level, id));
                }
            }
        }
        let mut cost = 0;
        while let Some((level, fact)) = pending.pop_last() {
            let op = *self.achievers[fact]
                .iter()
                .min_by_key(|&&op| (!existing[op], op))?;
            cost += usize::from(!existing[op]);
            // Equation (1): (S union Prec(a)) minus Eff(a). An existing
            // action is free, but its preconditions still need achievement.
            for &pre in &self.preconditions[op] {
                debug_assert!(self.levels[pre] < level);
                if self.levels[pre] > 0 {
                    pending.insert((self.levels[pre], pre));
                }
            }
            for &effect in &self.effects[op] {
                pending.remove(&(self.levels[effect], effect));
            }
        }
        Some(cost as f32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fdr::{Effect, Operator, Variable};

    fn task(n: usize, actions: &[(Vec<Fact>, Vec<Fact>)]) -> Task {
        Task {
            variables: (0..n)
                .map(|i| Variable {
                    name: format!("v{i}"),
                    values: vec!["false".into(), "true".into()],
                })
                .collect(),
            initial: vec![0; n],
            goals: vec![],
            mutex_groups: vec![],
            axioms: vec![],
            operators: actions
                .iter()
                .enumerate()
                .map(|(i, (pre, post))| Operator {
                    name: format!("a{i}"),
                    prevail: pre.clone(),
                    cost: 1,
                    effects: post
                        .iter()
                        .map(|p| Effect {
                            conditions: vec![],
                            variable: p.variable,
                            pre: None,
                            post: p.value,
                        })
                        .collect(),
                })
                .collect(),
        }
    }

    #[test]
    fn shared_effects_and_committed_preconditions() {
        let [p, q, r] = [0, 1, 2].map(|v| Fact::new(v, 1));
        let t = task(3, &[(vec![], vec![p]), (vec![p], vec![q, r])]);
        let graph = Graph::build(&t, &Parameters::default()).unwrap();
        assert_eq!(graph.estimate([q, r], []), Some(2.0));
        assert_eq!(graph.estimate([q, r], [1]), Some(1.0));
        assert_eq!(graph.estimate([q, r], [0, 1]), Some(0.0));
        assert_eq!(graph.estimate([], []), Some(0.0));
    }

    #[test]
    fn competing_needs_delay_first_appearance() {
        let [p, q, g] = [0, 1, 2].map(|v| Fact::new(v, 1));
        let t = task(
            3,
            &[(vec![], vec![p]), (vec![], vec![q]), (vec![p, q], vec![g])],
        );
        let graph = Graph::build(&t, &Parameters::default()).unwrap();
        // p and q appear at layer 1, but their two distinct real achievers
        // are serially mutex. They first coexist at 2, so g appears at 3.
        assert_eq!(graph.levels[graph.offsets[2] + 1], 3);
        assert_eq!(graph.estimate([g], []), Some(3.0));
    }

    #[test]
    fn persistent_mutex_blocks_an_impossible_precondition() {
        let [p, q, g] = [0, 1, 2].map(|v| Fact::new(v, 1));
        let t = task(
            3,
            &[
                (vec![], vec![p, Fact::new(1, 0)]),
                (vec![], vec![q, Fact::new(0, 0)]),
                (vec![p, q], vec![g]),
            ],
        );
        let graph = Graph::build(&t, &Parameters::default()).unwrap();
        assert_eq!(graph.estimate([g], []), None);
        // Open conditions at different consumers are NOT required to coexist.
        assert_eq!(graph.estimate([p, q], []), Some(2.0));
    }

    #[test]
    fn earliest_layer_precedes_committed_achiever_preference() {
        let [p, g] = [0, 1].map(|v| Fact::new(v, 1));
        let t = task(
            2,
            &[
                (vec![], vec![p]),
                (vec![p], vec![g]),
                (vec![], vec![g]),
                (vec![], vec![g]),
            ],
        );
        let graph = Graph::build(&t, &Parameters::default()).unwrap();
        assert_eq!(graph.estimate([g], [1]), Some(1.0));
        assert_eq!(graph.estimate([g], [3]), Some(0.0));
    }

    #[test]
    fn unsupported_task_features_are_rejected() {
        let mut t = task(1, &[(vec![], vec![Fact::new(0, 1)])]);
        t.operators[0].cost = 2;
        assert!(validate(&t, ActionCost::Task).is_err());
        assert!(validate(&t, ActionCost::Unit).is_ok());
        t.operators[0].effects[0].conditions.push(Fact::new(0, 0));
        assert!(validate(&t, ActionCost::Unit).is_err());
    }

    #[test]
    fn preprocessing_honours_deadline() {
        let t = task(1, &[(vec![], vec![Fact::new(0, 1)])]);
        let params = Parameters {
            deadline: Some(std::time::Instant::now()),
            ..Parameters::default()
        };
        assert!(matches!(
            Graph::build(&t, &params),
            Err(StopReason::Deadline)
        ));
    }
}
