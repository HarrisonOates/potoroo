//! Value-token deficits for FDR POCL plans.
//!
//! Every write to a variable ends the value it held. Between consecutive
//! writes, the variable keeps one value, so the history of a variable is a
//! sequence of *segments*: one started by the initial state, then one per
//! write. A step whose precondition `v = a` it overwrites needs a segment of
//! value `a` to end, and no other step can end that same segment. A goal
//! `v = a` needs the final segment to have value `a`, which no step ends.
//!
//! So in any completion of a partial plan, for each fact `v = a`,
//!
//! ```text
//! destroyers(a) + [goal(v) = a]  <=  [init(v) = a] + producers(a)
//! ```
//!
//! counting steps that will be in the plan. Additive costs see none of this:
//! a fact true initially costs nothing however many steps need to consume it.
//! The committed steps fix part of each side; a shortfall must be met by new
//! producers, each at least the fact's *reproduction* cost (an achiever's
//! cost plus additive costs of its preconditions on other variables).
//!
//! Causal-link view: two links from the same production of `v = a` to two
//! steps that both overwrite `v` threaten each other in both directions, so
//! no consistent ordering exists. Each destroyer needs its own production.

use std::cell::RefCell;

use crate::fdr::{Fact, Task};

/// Static per-task tables for the deficit count.
pub struct TokenTable {
    offset: Vec<usize>,
    /// Per operator: facts it requires and unconditionally overwrites.
    consumes: Vec<Vec<u32>>,
    /// Per operator: `(fact, effect index)` for every assignment it makes.
    produces: Vec<Vec<(u32, u32)>>,
    /// Per fact: `[init] - [goal]`, the slack before any step is counted.
    base: Vec<i32>,
    /// Per fact: cost of a fresh production.
    repro: Vec<f32>,
    /// Per fact: whether its additive cost is nonzero, i.e. whether an open
    /// occurrence is already charged a new producer by `h_add`.
    charged: Vec<bool>,
    /// Per operator: the variables it writes.
    writes: Vec<Vec<u32>>,
    /// Additive costs from the initial state, indexed by fact.
    add: Vec<f32>,
    initial: Vec<bool>,
    scratch: RefCell<Scratch>,
}

#[derive(Default)]
struct Scratch {
    /// Destroyers minus producers minus charged occurrences, per fact.
    need: Vec<i32>,
    demanded: Vec<bool>,
    touched: Vec<u32>,
    /// Facts a committed step may produce or already charged as a prevail
    /// need, with the indexes to reset.
    covered: Vec<bool>,
    marked: Vec<u32>,
}

impl TokenTable {
    /// `add` holds additive costs from the initial state; `requirements` the
    /// preconditions (with effect conditions) of each operator effect.
    pub fn new(
        task: &Task,
        add: &[Vec<f32>],
        requirements: &[Vec<Vec<Fact>>],
        costs: &[f32],
    ) -> Self {
        let mut offset = Vec::with_capacity(task.variables.len() + 1);
        let mut total = 0usize;
        for variable in &task.variables {
            offset.push(total);
            total += variable.values.len();
        }
        offset.push(total);
        let index = |fact: Fact| (offset[fact.variable] + fact.value) as u32;

        let writes = task
            .operators
            .iter()
            .map(|operator| {
                let mut vars: Vec<u32> =
                    operator.effects.iter().map(|e| e.variable as u32).collect();
                vars.sort_unstable();
                vars.dedup();
                vars
            })
            .collect();
        let mut add_flat = vec![f32::INFINITY; total];
        for (variable, costs) in add.iter().enumerate() {
            for (value, &cost) in costs.iter().enumerate() {
                add_flat[offset[variable] + value] = cost;
            }
        }
        let mut initial = vec![false; total];
        for (variable, &value) in task.initial.iter().enumerate() {
            if !task.is_derived_variable(variable) {
                initial[offset[variable] + value] = true;
            }
        }
        let mut consumes = Vec::with_capacity(task.operators.len());
        let mut produces = Vec::with_capacity(task.operators.len());
        let mut repro = vec![f32::INFINITY; total];
        for (o, operator) in task.operators.iter().enumerate() {
            let mut destroyed = Vec::new();
            let mut produced = Vec::new();
            for (e, effect) in operator.effects.iter().enumerate() {
                if task.is_derived_variable(effect.variable) {
                    continue;
                }
                let pre = effect.pre.or_else(|| {
                    operator
                        .prevail
                        .iter()
                        .find(|fact| fact.variable == effect.variable)
                        .map(|fact| fact.value)
                });
                if pre == Some(effect.post) {
                    continue;
                }
                if effect.conditions.is_empty() {
                    if let Some(value) = pre {
                        destroyed.push(index(Fact::new(effect.variable, value)));
                    }
                }
                let fact = Fact::new(effect.variable, effect.post);
                produced.push((index(fact), e as u32));
                let mut cost = costs[o];
                for requirement in &requirements[o][e] {
                    if requirement.variable != effect.variable {
                        cost += add[requirement.variable][requirement.value];
                    }
                }
                let slot = &mut repro[index(fact) as usize];
                if cost < *slot {
                    *slot = cost;
                }
            }
            destroyed.sort_unstable();
            destroyed.dedup();
            consumes.push(destroyed);
            produces.push(produced);
        }

        let mut base = vec![0i32; total];
        for (variable, &value) in task.initial.iter().enumerate() {
            if !task.is_derived_variable(variable) {
                base[offset[variable] + value] += 1;
            }
        }
        for &goal in &task.goals {
            if !task.is_derived_variable(goal.variable) {
                base[index(goal) as usize] -= 1;
            }
        }
        let mut charged = vec![false; total];
        for (variable, costs) in add.iter().enumerate() {
            for (value, &cost) in costs.iter().enumerate() {
                charged[offset[variable] + value] = cost > 0.0;
            }
        }
        TokenTable {
            offset,
            consumes,
            produces,
            base,
            repro,
            charged,
            writes,
            add: add_flat,
            initial,
            scratch: RefCell::new(Scratch {
                need: vec![0; total],
                demanded: vec![false; total],
                touched: Vec::new(),
                covered: vec![false; total],
                marked: Vec::new(),
            }),
        }
    }

    fn index(&self, fact: Fact) -> usize {
        self.offset[fact.variable] + fact.value
    }

    /// Total reproduction cost of every fact's shortfall, or infinity when a
    /// shortfall has no producer at all (then the plan has no completion).
    ///
    /// `operator` maps a committed step to its operator, `can_fire` tells
    /// whether that step's effect (by index) can still fire, and `opens`
    /// yields the open-condition facts.
    pub fn deficit<S: Copy>(
        &self,
        steps: impl Iterator<Item = S> + Clone,
        operator: impl Fn(S) -> usize,
        can_fire: impl Fn(S, usize) -> bool,
        opens: impl Iterator<Item = Fact>,
    ) -> f32 {
        let mut scratch = self.scratch.borrow_mut();
        let Scratch {
            need,
            demanded,
            touched,
            ..
        } = &mut *scratch;
        for step in steps.clone() {
            for &fact in &self.consumes[operator(step)] {
                let fact = fact as usize;
                if !demanded[fact] {
                    demanded[fact] = true;
                    touched.push(fact as u32);
                    need[fact] = -self.base[fact];
                }
                need[fact] += 1;
            }
        }
        let mut total = 0.0f32;
        if !touched.is_empty() {
            for step in steps {
                for &(fact, effect) in &self.produces[operator(step)] {
                    if demanded[fact as usize] && can_fire(step, effect as usize) {
                        need[fact as usize] -= 1;
                    }
                }
            }
            for open in opens {
                let fact = self.index(open);
                if demanded[fact] && self.charged[fact] {
                    need[fact] -= 1;
                }
            }
            for &fact in touched.iter() {
                let fact = fact as usize;
                if need[fact] > 0 {
                    total += need[fact] as f32 * self.repro[fact];
                }
                demanded[fact] = false;
            }
        }
        touched.clear();
        total
    }

    /// Additive open-condition cost that charges a *prevail* condition (one
    /// its consumer reads but does not overwrite) once per distinct fact, and
    /// not at all when a committed step can already produce it: one segment
    /// of the value can serve every reader. Conditions whose consumer
    /// overwrites the variable, and goals, are charged per occurrence as in
    /// `h_add`, since each needs its own production.
    pub fn open_cost<S: Copy>(
        &self,
        steps: impl Iterator<Item = S>,
        operator: impl Fn(S) -> usize,
        can_fire: impl Fn(S, usize) -> bool,
        opens: impl Iterator<Item = (Fact, Option<usize>)>,
    ) -> f32 {
        let mut scratch = self.scratch.borrow_mut();
        let Scratch {
            covered, marked, ..
        } = &mut *scratch;
        for step in steps {
            for &(fact, effect) in &self.produces[operator(step)] {
                if !covered[fact as usize] && can_fire(step, effect as usize) {
                    covered[fact as usize] = true;
                    marked.push(fact);
                }
            }
        }
        let mut total = 0.0f32;
        for (fact, consumer) in opens {
            let index = self.index(fact);
            let prevail = consumer.is_some_and(|op| {
                self.writes[op]
                    .binary_search(&(fact.variable as u32))
                    .is_err()
            });
            if !prevail {
                total += self.add[index];
                continue;
            }
            if self.initial[index] || covered[index] {
                continue;
            }
            covered[index] = true;
            marked.push(index as u32);
            total += self.add[index];
        }
        for &fact in marked.iter() {
            covered[fact as usize] = false;
        }
        marked.clear();
        total
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fdr::{Effect, Operator, Variable};

    /// One binary variable `p`, true initially and in the goal; `use` needs
    /// and clears it, `restore` sets it again.
    fn task() -> Task {
        let effect = |pre, post| Effect {
            conditions: vec![],
            variable: 0,
            pre,
            post,
        };
        Task {
            variables: vec![Variable {
                name: "p".into(),
                values: vec!["false".into(), "true".into()],
            }],
            mutex_groups: vec![],
            initial: vec![1],
            goals: vec![Fact::new(0, 1)],
            operators: vec![
                Operator {
                    name: "use".into(),
                    prevail: vec![],
                    effects: vec![effect(Some(1), 0)],
                    cost: 1,
                },
                Operator {
                    name: "restore".into(),
                    prevail: vec![],
                    effects: vec![effect(Some(0), 1)],
                    cost: 1,
                },
            ],
            axioms: vec![],
        }
    }

    #[test]
    fn each_destroyer_and_the_goal_need_their_own_production() {
        let task = task();
        let add = vec![vec![1.0, 0.0]];
        let requirements = vec![vec![vec![Fact::new(0, 1)]], vec![vec![Fact::new(0, 0)]]];
        let table = TokenTable::new(&task, &add, &requirements, &[1.0, 1.0]);
        let deficit = |steps: &[usize]| {
            table.deficit(
                steps.iter().copied(),
                |op| op,
                |_, _| true,
                std::iter::empty(),
            )
        };
        // The initial value serves either the goal or one use, not both.
        assert_eq!(deficit(&[]), 0.0);
        assert_eq!(deficit(&[0]), 1.0);
        assert_eq!(deficit(&[0, 0]), 2.0);
        // Each restore supplies one more.
        assert_eq!(deficit(&[0, 1]), 0.0);
        assert_eq!(deficit(&[0, 0, 1]), 1.0);
    }
}
