//! FF's relaxed planning graph and extraction (Hoffmann & Nebel 2001).
//!
//! https://arxiv.org/pdf/1106.0675
//! Marker lifetimes follow the author's FF-v2.3 `relax.c::achieve_goals`,
//! https://fai.cs.uni-saarland.de/hoffmann/ff.html: effects may support actions
//! selected later at the SAME layer, but cannot erase already regressed goals.
//!
//! POCL adaptation: extract jointly for the outstanding open conditions from
//! the task's initial state. Shared future actions are counted once. `FFR`
//! additionally filters open conditions with an order-compatible existing
//! supporter before calling this module (VHPOP's suggested combination).
//! This is neither FF's state-space search nor a causal-link compilation.

use std::cell::Cell;
use std::collections::BTreeSet;

use crate::fdr::{Fact, Task};
use crate::memory::{SearchStop, StopReason};
use crate::params::{ActionCost, Parameters};

pub(crate) fn validate(task: &Task, cost: ActionCost) -> Result<(), String> {
    if !task.axioms.is_empty()
        || task
            .operators
            .iter()
            .any(|op| op.effects.iter().any(|e| !e.conditions.is_empty()))
    {
        return Err(
            "FF/FFR/FFOC/FFOCR currently require unconditional effects and no axioms".into(),
        );
    }
    if task.operators.iter().any(|op| cost.resolve(op.cost) != 1) {
        return Err("FF/FFR/FFOC/FFOCR use unit-action counts; use unit costs (-a UNIT)".into());
    }
    Ok(())
}

pub(crate) struct Graph {
    offsets: Vec<usize>,
    levels: Vec<usize>,
    best: Vec<Option<usize>>,
    preconditions: Vec<Vec<usize>>,
    effects: Vec<Vec<usize>>,
    single_costs: Vec<Cell<Option<f32>>>,
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
        for v in &task.variables {
            offsets.push(offsets.last().unwrap() + v.values.len());
        }
        let nf = *offsets.last().unwrap();
        let encode = |f: Fact| offsets[f.variable] + f.value;
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
        let mut consumers = vec![Vec::new(); nf];
        let mut remaining = Vec::new();
        let mut scheduled = Vec::new();
        for (op, pre) in preconditions.iter().enumerate() {
            remaining.push(pre.len());
            if pre.is_empty() {
                scheduled.push(op);
            }
            for &f in pre {
                consumers[f].push(op);
            }
        }
        let mut levels = vec![usize::MAX; nf];
        let mut action_levels = vec![usize::MAX; task.operators.len()];
        let mut frontier = Vec::new();
        for (v, &value) in task.initial.iter().enumerate() {
            let f = offsets[v] + value;
            levels[f] = 0;
            frontier.push(f);
        }
        let mut layer = 0;
        loop {
            check()?;
            for fact in frontier.drain(..) {
                check()?;
                for &op in &consumers[fact] {
                    remaining[op] -= 1;
                    if remaining[op] == 0 {
                        scheduled.push(op);
                    }
                }
            }
            for op in scheduled.drain(..) {
                check()?;
                action_levels[op] = layer;
                for &effect in &effects[op] {
                    if levels[effect] == usize::MAX {
                        levels[effect] = layer + 1;
                        frontier.push(effect);
                    }
                }
            }
            if frontier.is_empty() {
                break;
            }
            layer += 1;
        }
        // FF's difficulty is the SUM OF FIRST FACT LEVELS, not h_add cost.
        let mut best = vec![None; nf];
        let mut best_key = vec![(usize::MAX, usize::MAX); nf];
        for (op, pre) in preconditions.iter().enumerate() {
            check()?;
            if action_levels[op] == usize::MAX {
                continue;
            }
            let difficulty: usize = pre.iter().map(|&f| levels[f]).sum();
            for &effect in &effects[op] {
                if action_levels[op] + 1 == levels[effect] && (difficulty, op) < best_key[effect] {
                    best[effect] = Some(op);
                    best_key[effect] = (difficulty, op);
                }
            }
        }
        Ok(Self {
            single_costs: vec![Cell::new(None); nf],
            offsets,
            levels,
            best,
            preconditions,
            effects,
        })
    }

    /// Cache one extraction per fact; sum at call sites without deduplicating
    /// occurrences. Sharing within a support plan is retained, sharing between
    /// distinct open-condition demands is deliberately relaxed away.
    pub(crate) fn single_cost(&self, fact: Fact) -> f32 {
        let cache = &self.single_costs[self.offsets[fact.variable] + fact.value];
        if let Some(cost) = cache.get() {
            return cost;
        }
        let cost = self
            .extract([fact])
            .map_or(f32::INFINITY, |p| p.len() as f32);
        cache.set(Some(cost));
        cost
    }

    /// Returns the relaxed actions in execution order. The graph is cached;
    /// only extraction depends on the current partial plan's open conditions.
    pub(crate) fn extract(&self, goals: impl IntoIterator<Item = Fact>) -> Option<Vec<usize>> {
        // Highest layer first; ascending fact id breaks ties deterministically.
        let mut pending = BTreeSet::new();
        for fact in goals {
            let f = self.offsets[fact.variable] + fact.value;
            match self.levels[f] {
                usize::MAX => return None,
                0 => {}
                level => {
                    pending.insert((std::cmp::Reverse(level), f));
                }
            }
        }
        // FF-v2.3 uses exact layer stamps for BOTH tests below. Retaining an
        // effect as true at the next lower layer can erase prerequisites of
        // an earlier selected action and create cyclic "support". A stamp
        // only permits reuse from actions already selected at this layer.
        let mut marked_at = vec![usize::MAX; self.levels.len()];
        let mut selected = Vec::new();
        while let Some((std::cmp::Reverse(layer), fact)) = pending.pop_first() {
            if marked_at[fact] == layer {
                continue;
            }
            let op = self.best[fact]?;
            selected.push((layer, op));
            for &pre in &self.preconditions[op] {
                if self.levels[pre] > 0 && marked_at[pre] != layer {
                    pending.insert((std::cmp::Reverse(self.levels[pre]), pre));
                }
            }
            for &effect in &self.effects[op] {
                marked_at[effect] = layer;
            }
        }
        // Stable sort preserves selection order for actions at the same layer.
        selected.sort_by_key(|&(layer, _)| layer);
        Some(selected.into_iter().map(|(_, op)| op).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fdr::{Effect, Operator, Variable};

    fn task(n: usize, actions: &[(Vec<usize>, Vec<usize>)]) -> Task {
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
                .map(|(i, (pre, add))| Operator {
                    name: format!("a{i}"),
                    prevail: pre.iter().map(|&v| Fact::new(v, 1)).collect(),
                    cost: 1,
                    effects: add
                        .iter()
                        .map(|&v| Effect {
                            conditions: vec![],
                            variable: v,
                            pre: None,
                            post: 1,
                        })
                        .collect(),
                })
                .collect(),
        }
    }

    fn extract_and_check(t: &Task, goals: &[usize]) -> Vec<usize> {
        let graph = Graph::build(t, &Parameters::default()).unwrap();
        let result = graph
            .extract(goals.iter().map(|&v| Fact::new(v, 1)))
            .unwrap();
        let mut reached: BTreeSet<_> = t
            .initial
            .iter()
            .enumerate()
            .map(|(v, &x)| Fact::new(v, x))
            .collect();
        let mut unique = BTreeSet::new();
        for &op in &result {
            assert!(
                unique.insert(op),
                "NOOPs-first should avoid repeated actions"
            );
            assert!(t.operators[op]
                .preconditions()
                .iter()
                .all(|p| reached.contains(p)));
            reached.extend(t.operators[op].effects.iter().map(|e| e.assignment()));
        }
        assert!(goals.iter().all(|&v| reached.contains(&Fact::new(v, 1))));
        result
    }

    #[test]
    fn single_goal_ff_shares_support_but_occurrences_remain_separate() {
        // p makes a and b jointly; c needs both. ADD(c)=3, FF(c)=2.
        let t = task(3, &[(vec![], vec![0, 1]), (vec![0, 1], vec![2])]);
        let graph = Graph::build(&t, &Parameters::default()).unwrap();
        let goal = Fact::new(2, 1);
        assert_eq!(graph.single_cost(goal), 2.0);
        assert_eq!(
            [goal, goal]
                .into_iter()
                .map(|g| graph.single_cost(g))
                .sum::<f32>(),
            4.0
        );
        assert_eq!(graph.extract([goal, goal]).unwrap().len(), 2);
    }

    #[test]
    fn potential_actions_share_a_future_producer() {
        let t = task(
            3,
            &[(vec![], vec![0]), (vec![0], vec![1]), (vec![0], vec![2])],
        );
        assert_eq!(extract_and_check(&t, &[1, 2]), vec![0, 1, 2]);
    }

    #[test]
    fn later_layer_effects_do_not_retroactively_remove_earlier_goals() {
        let t = task(
            3,
            &[(vec![], vec![0]), (vec![], vec![1]), (vec![0], vec![1, 2])],
        );
        assert_eq!(extract_and_check(&t, &[1, 2]), vec![0, 1, 2]);
    }

    #[test]
    fn later_effects_cannot_erase_an_earlier_actions_required_support() {
        let t = task(
            4,
            &[
                (vec![], vec![0]),
                (vec![], vec![1]),
                (vec![0], vec![1, 2]),
                (vec![1], vec![0, 3]),
            ],
        );
        assert_eq!(extract_and_check(&t, &[2, 3]), vec![0, 2, 3]);
    }

    #[test]
    fn generated_relaxations_have_executable_extractions() {
        // Check the semantic contract, independently of graph levels/markers:
        // every returned sequence is executable and establishes its goals.
        let mut seed = 0x5eed_u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            (seed >> 32) as usize
        };
        for _ in 0..4096 {
            let actions: Vec<_> = (0..12)
                .map(|_| {
                    let pre = (0..6).filter(|_| next() % 4 == 0).collect();
                    let add = (0..6).filter(|_| next() % 4 == 0).collect();
                    (pre, add)
                })
                .collect();
            let t = task(6, &actions);
            let goals: Vec<_> = (0..6).filter(|_| next() % 2 == 0).collect();
            let mut reachable = BTreeSet::<usize>::new();
            loop {
                let before = reachable.len();
                for (pre, add) in &actions {
                    if pre.iter().all(|p| reachable.contains(p)) {
                        reachable.extend(add.iter().copied());
                    }
                }
                if before == reachable.len() {
                    break;
                }
            }
            if goals.iter().all(|g| reachable.contains(g)) {
                extract_and_check(&t, &goals);
            } else {
                let graph = Graph::build(&t, &Parameters::default()).unwrap();
                assert_eq!(graph.extract(goals.iter().map(|&g| Fact::new(g, 1))), None);
            }
        }
    }

    #[test]
    fn parallel_levels_and_minimum_difficulty_choose_support() {
        let t = task(
            3,
            &[
                (vec![], vec![0]),
                (vec![], vec![1]),
                (vec![0, 1], vec![2]),
                (vec![0], vec![2]),
            ],
        );
        let graph = Graph::build(&t, &Parameters::default()).unwrap();
        assert_eq!(graph.levels[graph.offsets[2] + 1], 2);
        assert_eq!(extract_and_check(&t, &[2]), vec![0, 3]);
    }

    #[test]
    fn empty_unreachable_and_initial_goals() {
        let t = task(1, &[]);
        let graph = Graph::build(&t, &Parameters::default()).unwrap();
        assert_eq!(graph.extract([]), Some(vec![]));
        assert_eq!(graph.extract([Fact::new(0, 0)]), Some(vec![]));
        assert_eq!(graph.extract([Fact::new(0, 1)]), None);
    }

    #[test]
    fn unsupported_inputs_and_expired_preprocessing() {
        let mut t = task(1, &[(vec![], vec![0])]);
        t.operators[0].cost = 2;
        assert!(validate(&t, ActionCost::Task).is_err());
        assert!(validate(&t, ActionCost::Unit).is_ok());
        t.operators[0].effects[0].conditions.push(Fact::new(0, 0));
        assert!(validate(&t, ActionCost::Unit).is_err());
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
