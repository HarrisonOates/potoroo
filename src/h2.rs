//! Bounded pair reachability for finite-domain tasks (a conservative h² test).
//!
//! A pair is reachable if initially true, jointly produced by an applicable
//! operator, or produced while the other fact can persist. Applicability and
//! effect guards are relaxed to pairwise compatibility. This over-approximates
//! real reachability: only pairs still absent at a fixed point are mutexes.
//! Conditional assignments can produce facts but only unconditional assignments
//! rule out persistence. Axiom tasks are projected onto ordinary facts: derived
//! requirements are dropped, and no pair involving a derived fact is disproved.
//! No incomplete fixed point is published.
//! Declared mutex groups constrain the relaxation itself, allowing their
//! consequences to propagate through operators as well as pruning search.

use crate::fdr::{Fact, Task};
use crate::memory::StopReason;
use std::time::Instant;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Status {
    #[default]
    Disabled,
    Complete,
    FactLimit,
    WorkLimit,
    /// Legacy status retained for callers; axiom tasks now use projection.
    Axioms,
    InvalidTask,
    Deadline,
    Memory,
}

impl Status {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Disabled => "disabled",
            Self::Complete => "complete",
            Self::FactLimit => "fact-limit",
            Self::WorkLimit => "work-limit",
            Self::Axioms => "axioms",
            Self::InvalidTask => "invalid-task",
            Self::Deadline => "deadline",
            Self::Memory => "memory",
        }
    }

    pub(crate) fn stopped(self) -> Option<StopReason> {
        match self {
            Self::Deadline => Some(StopReason::Deadline),
            Self::Memory => Some(StopReason::Memory),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Stats {
    pub status: Status,
    /// Charged table probes, fact processing and rule construction work.
    pub work: usize,
    pub elapsed_ms: u128,
    /// Proven cross-variable pairs, including any already declared by the task.
    pub mutex_pairs: usize,
    /// Proven cross-variable pairs not already in a declared mutex group.
    pub new_mutex_pairs: usize,
    /// Derived variables ignored by the conservative base-fact projection.
    pub projected_variables: usize,
    pub unreachable_facts: usize,
    pub supporters_removed: usize,
}

#[derive(Clone, Copy)]
pub(crate) struct Limits {
    pub facts: usize,
    pub work: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            facts: 2048,
            work: 5_000_000,
        }
    }
}

#[derive(Debug)]
pub(crate) struct Reachability {
    size: usize,
    bits: Vec<u64>,
}
impl Reachability {
    pub(crate) fn reachable(&self, a: usize, b: usize) -> bool {
        let i = a * self.size + b;
        self.bits[i / 64] & (1 << (i % 64)) != 0
    }
    fn insert(&mut self, a: usize, b: usize) -> bool {
        let fresh = !self.reachable(a, b);
        for i in [a * self.size + b, b * self.size + a] {
            self.bits[i / 64] |= 1 << (i % 64);
        }
        fresh
    }
}

struct Budget<F> {
    max: usize,
    used: usize,
    next_check: usize,
    stop: F,
}
impl<F: FnMut(usize) -> Option<StopReason>> Budget<F> {
    fn charge(&mut self, n: usize) -> Result<(), Status> {
        if n > self.max - self.used {
            return Err(Status::WorkLimit);
        }
        self.used += n;
        if self.used >= self.next_check {
            self.next_check = self.used.saturating_add(1024);
            if let Some(reason) = (self.stop)(self.used) {
                return Err(match reason {
                    StopReason::Deadline => Status::Deadline,
                    StopReason::Memory => Status::Memory,
                });
            }
        }
        Ok(())
    }
    fn reachable(&mut self, table: &Reachability, a: usize, b: usize) -> Result<bool, Status> {
        self.charge(1)?;
        Ok(table.reachable(a, b))
    }
    fn possible(&mut self, table: &Reachability, required: &[usize]) -> Result<bool, Status> {
        for (i, &a) in required.iter().enumerate() {
            for &b in &required[i..] {
                if !self.reachable(table, a, b)? {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }
}

struct Rule {
    required: Vec<usize>,
    post: usize,
}
struct Operator {
    rules: Vec<Rule>,
    unconditional: Vec<Fact>,
}

pub(crate) fn compute(
    task: &Task,
    limits: Limits,
    stop: impl FnMut(usize) -> Option<StopReason>,
) -> (Option<Reachability>, Stats) {
    let started = Instant::now();
    let mut budget = Budget {
        max: limits.work,
        used: 0,
        next_check: 0,
        stop,
    };
    let mut stats = Stats::default();
    let result = compute_inner(task, limits.facts, &mut budget, &mut stats);
    let table = match result {
        Ok(table) => {
            stats.status = Status::Complete;
            Some(table)
        }
        Err(status) => {
            stats.status = status;
            stats.mutex_pairs = 0;
            stats.new_mutex_pairs = 0;
            stats.unreachable_facts = 0;
            None
        }
    };
    stats.work = budget.used;
    stats.elapsed_ms = started.elapsed().as_millis();
    (table, stats)
}

fn compute_inner<F: FnMut(usize) -> Option<StopReason>>(
    task: &Task,
    max_facts: usize,
    budget: &mut Budget<F>,
    stats: &mut Stats,
) -> Result<Reachability, Status> {
    budget.charge(0)?;
    let mut offsets = vec![0usize];
    let mut facts = Vec::new();
    for (variable, v) in task.variables.iter().enumerate() {
        let next = facts
            .len()
            .checked_add(v.values.len())
            .ok_or(Status::FactLimit)?;
        if next > max_facts {
            return Err(Status::FactLimit);
        }
        if v.values.is_empty() {
            return Err(Status::InvalidTask);
        }
        budget.charge(v.values.len() + 1)?;
        facts.extend((0..v.values.len()).map(|value| Fact::new(variable, value)));
        offsets.push(next);
    }
    let index = |fact: Fact| -> Result<usize, Status> {
        let start = *offsets.get(fact.variable).ok_or(Status::InvalidTask)?;
        let end = *offsets.get(fact.variable + 1).ok_or(Status::InvalidTask)?;
        if fact.value >= end - start {
            return Err(Status::InvalidTask);
        }
        Ok(start + fact.value)
    };
    if task.initial.len() != task.variables.len() {
        return Err(Status::InvalidTask);
    }
    let mut derived = vec![false; task.variables.len()];
    for axiom in &task.axioms {
        budget.charge(2)?;
        index(Fact::new(axiom.variable, axiom.pre))?;
        index(Fact::new(axiom.variable, axiom.post))?;
        for &condition in &axiom.conditions {
            budget.charge(1)?;
            index(condition)?;
        }
        derived[axiom.variable] = true;
    }
    stats.projected_variables = derived.iter().filter(|&&d| d).count();
    let size = facts.len();
    let cells = size.checked_mul(size).ok_or(Status::FactLimit)?;
    budget.charge(2 * cells.div_ceil(64))?;
    let mut table = Reachability {
        size,
        bits: vec![0; cells.div_ceil(64)],
    };
    // Keep the existing global fact indices without adding a branch to every
    // search-time lookup. Any pair touching a derived variable is unknown:
    // closure can reset or establish its value independently of base effects.
    for (a, fact) in facts.iter().enumerate() {
        if derived[fact.variable] {
            for b in 0..size {
                budget.charge(1)?;
                table.insert(a, b);
            }
        }
    }
    // This scratch table is discarded before search. Charging every group
    // member/pair keeps dense or repeated groups inside the same work cap.
    let mut forbidden = Reachability {
        size,
        bits: vec![0; cells.div_ceil(64)],
    };
    for group in &task.mutex_groups {
        budget.charge(1)?;
        for (i, &left) in group.iter().enumerate() {
            budget.charge(1)?;
            let a = index(left)?;
            for &right in &group[i + 1..] {
                budget.charge(1)?;
                let b = index(right)?;
                if a != b && !derived[left.variable] && !derived[right.variable] {
                    forbidden.insert(a, b);
                }
            }
        }
    }
    for (v, &value) in task.initial.iter().enumerate() {
        let a = index(Fact::new(v, value))?;
        if derived[v] {
            continue;
        }
        for (w, &other) in task.initial[..=v].iter().enumerate() {
            budget.charge(1)?;
            let b = index(Fact::new(w, other))?;
            if derived[w] {
                continue;
            }
            if forbidden.reachable(a, b) {
                // A claimed mutex contradicted by the initial state cannot be
                // used to derive additional proofs.
                return Err(Status::InvalidTask);
            }
            table.insert(a, b);
        }
    }
    let mut operators = Vec::new();
    for op in &task.operators {
        budget.charge(8)?;
        let mut pre = Vec::new();
        for &fact in &op.prevail {
            budget.charge(1)?;
            let p = index(fact)?;
            if !derived[fact.variable] {
                pre.push(p);
            }
        }
        let mut unconditional = Vec::new();
        for effect in &op.effects {
            budget.charge(2)?;
            index(effect.assignment())?;
            if let Some(value) = effect.pre {
                let p = index(Fact::new(effect.variable, value))?;
                if !derived[effect.variable] {
                    pre.push(p);
                }
            }
            // Test the ORIGINAL guard. Dropping a derived guard must never
            // turn a conditional write into a guaranteed overwrite.
            if effect.conditions.is_empty() && !derived[effect.variable] {
                unconditional.push(effect.assignment());
            }
        }
        pre.sort_unstable();
        pre.dedup();
        let mut rules = Vec::new();
        for effect in &op.effects {
            budget.charge(8 + pre.len())?;
            let mut required = pre.clone();
            for &guard in &effect.conditions {
                budget.charge(1)?;
                let p = index(guard)?;
                if !derived[guard.variable] {
                    required.push(p);
                }
            }
            required.sort_unstable();
            required.dedup();
            if !derived[effect.variable] {
                rules.push(Rule {
                    required,
                    post: index(effect.assignment())?,
                });
            }
        }
        operators.push(Operator {
            rules,
            unconditional,
        });
    }
    loop {
        let mut changed = false;
        for op in &operators {
            budget.charge(1)?;
            for (i, a) in op.rules.iter().enumerate() {
                budget.charge(1)?;
                if !budget.possible(&table, &a.required)? {
                    continue;
                }
                changed |= table.insert(a.post, a.post);
                // Joint effects: each guard must be possible, and every pair
                // crossing the two guards must also be possible in the source.
                for b in &op.rules[i + 1..] {
                    budget.charge(1)?;
                    if facts[a.post].variable == facts[b.post].variable {
                        continue;
                    }
                    if table.reachable(a.post, b.post)
                        || forbidden.reachable(a.post, b.post)
                        || !budget.possible(&table, &b.required)?
                    {
                        continue;
                    }
                    let mut compatible = true;
                    'cross: for &p in &a.required {
                        for &q in &b.required {
                            if !budget.reachable(&table, p, q)? {
                                compatible = false;
                                break 'cross;
                            }
                        }
                    }
                    if compatible {
                        changed |= table.insert(a.post, b.post);
                    }
                }
                // Persistence: conditional writes cannot force a value away.
                for (c, fact) in facts.iter().enumerate() {
                    budget.charge(1)?;
                    if facts[a.post].variable == fact.variable
                        || table.reachable(a.post, c)
                        || forbidden.reachable(a.post, c)
                        || !table.reachable(c, c)
                    {
                        continue;
                    }
                    let mut overwritten = false;
                    for write in &op.unconditional {
                        budget.charge(1)?;
                        if write.variable == fact.variable && write.value != fact.value {
                            overwritten = true;
                            break;
                        }
                    }
                    if overwritten {
                        continue;
                    }
                    let mut compatible = true;
                    for &p in &a.required {
                        if !budget.reachable(&table, p, c)? {
                            compatible = false;
                            break;
                        }
                    }
                    if compatible {
                        changed |= table.insert(a.post, c);
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    // A fixed point is essential. On any earlier budget exit, discard the
    // entire table: "not reached yet" is not a proof of unreachability.
    for (a, fact) in facts.iter().enumerate() {
        budget.charge(1)?;
        stats.unreachable_facts += usize::from(!table.reachable(a, a));
        for (b, other) in facts[..a].iter().enumerate() {
            budget.charge(1)?;
            if fact.variable != other.variable && !table.reachable(a, b) {
                stats.mutex_pairs += 1;
                stats.new_mutex_pairs += usize::from(!forbidden.reachable(a, b));
            }
        }
    }
    Ok(table)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::fdr::{Effect, Operator, Variable};

    pub(crate) fn resource_task() -> Task {
        Task {
            variables: (0..3)
                .map(|i| Variable {
                    name: format!("v{i}"),
                    values: vec!["off".into(), "on".into()],
                })
                .collect(),
            initial: vec![1, 0, 0],
            goals: vec![Fact::new(1, 1), Fact::new(2, 1)],
            mutex_groups: vec![],
            axioms: vec![],
            operators: (1..3)
                .map(|v| Operator {
                    name: format!("use-for-{v}"),
                    cost: 1,
                    prevail: vec![],
                    effects: vec![
                        Effect {
                            conditions: vec![],
                            variable: 0,
                            pre: Some(1),
                            post: 0,
                        },
                        Effect {
                            conditions: vec![],
                            variable: v,
                            pre: None,
                            post: 1,
                        },
                    ],
                })
                .collect(),
        }
    }

    #[test]
    fn finds_a_resource_conflict_absent_from_declared_mutexes() {
        let task = resource_task();
        let base = crate::cutset::FactMutexes::new(&task);
        assert!(!base.inconsistent(&task.goals));
        let (table, stats) = compute(&task, Limits::default(), |_| None);
        assert_eq!(stats.status, Status::Complete);
        let table = table.unwrap();
        assert!(
            table.reachable(3, 3) && table.reachable(5, 5),
            "both goals are individually reachable"
        );
        assert!(
            !table.reachable(3, 5),
            "the same resource cannot be spent twice"
        );
        assert!(base.with_h2(Some(table)).inconsistent(&task.goals));
    }

    #[test]
    fn declared_mutexes_propagate_through_relaxed_conditional_effects() {
        let mut task = resource_task();
        task.variables.push(Variable {
            name: "done".into(),
            values: vec!["off".into(), "on".into()],
        });
        task.initial.push(0);
        task.goals = vec![Fact::new(3, 1)];
        // v0 is always on: each choice resets the other value. Conditional
        // persistence alone over-approximates this and permits both choices.
        task.operators = (1..3)
            .map(|variable| Operator {
                name: format!("choose-{variable}"),
                cost: 1,
                prevail: vec![],
                effects: vec![
                    Effect {
                        conditions: vec![],
                        variable,
                        pre: None,
                        post: 1,
                    },
                    Effect {
                        conditions: vec![Fact::new(0, 1)],
                        variable: 3 - variable,
                        pre: None,
                        post: 0,
                    },
                ],
            })
            .collect();
        task.operators.push(Operator {
            name: "requires-both".into(),
            cost: 1,
            prevail: vec![Fact::new(1, 1), Fact::new(2, 1)],
            effects: vec![Effect {
                conditions: vec![],
                variable: 3,
                pre: None,
                post: 1,
            }],
        });
        let (plain, _) = compute(&task, Limits::default(), |_| None);
        assert!(plain.unwrap().reachable(7, 7));
        task.mutex_groups = vec![vec![Fact::new(1, 1), Fact::new(2, 1)]];
        let (constrained, stats) = compute(&task, Limits::default(), |_| None);
        assert_eq!(stats.status, Status::Complete);
        assert!(!constrained.unwrap().reachable(7, 7));
        assert!(stats.new_mutex_pairs > 0);
        assert_eq!(stats.mutex_pairs, stats.new_mutex_pairs + 1);

        task.mutex_groups
            .push(vec![Fact::new(1, 0), Fact::new(2, 0)]);
        let (invalid, stats) = compute(&task, Limits::default(), |_| None);
        assert!(invalid.is_none());
        assert_eq!(stats.status, Status::InvalidTask);
        assert_eq!((stats.mutex_pairs, stats.new_mutex_pairs), (0, 0));
    }

    #[test]
    fn incomplete_tables_publish_no_mutexes() {
        let mut task = resource_task();
        let (_, complete) = compute(&task, Limits::default(), |_| None);
        for work in [0, 1, 10, complete.work / 2, complete.work - 1] {
            let (table, stats) = compute(&task, Limits { facts: 2048, work }, |_| None);
            assert!(table.is_none());
            assert_eq!(stats.status, Status::WorkLimit);
            assert!(stats.work <= work);
            assert_eq!((stats.mutex_pairs, stats.unreachable_facts), (0, 0));
            assert_eq!(stats.new_mutex_pairs, 0);
        }
        let (table, stats) = compute(
            &task,
            Limits {
                facts: 5,
                ..Limits::default()
            },
            |_| None,
        );
        assert!(table.is_none());
        assert_eq!(stats.status, Status::FactLimit);
        // Interrupt after work has started, rather than only at entry.
        for i in 3..64 {
            task.variables.push(Variable {
                name: format!("v{i}"),
                values: vec!["off".into(), "on".into()],
            });
            task.initial.push(0);
        }
        for reason in [StopReason::Deadline, StopReason::Memory] {
            let (table, stats) = compute(&task, Limits::default(), |work| {
                (work > 0).then_some(reason)
            });
            assert!(table.is_none());
            assert_eq!(stats.status.stopped(), Some(reason));
            assert!(stats.work >= 1024);
        }
    }

    pub(crate) fn axiom_resource_task() -> Task {
        let mut task = resource_task();
        for variable in 3..5 {
            task.variables.push(Variable {
                name: format!("derived-{variable}"),
                values: vec!["true".into(), "false".into()],
            });
            // The raw initial value is deliberately stale: closure makes both
            // variables true, then consuming the resource resets them to false.
            task.initial.push(1);
            task.axioms.push(crate::fdr::Axiom {
                conditions: vec![if variable == 3 {
                    Fact::new(0, 1)
                } else {
                    Fact::new(3, 0)
                }],
                variable,
                pre: 1,
                post: 0,
            });
        }
        for op in &mut task.operators {
            op.prevail.push(Fact::new(4, 0));
        }
        task
    }

    #[test]
    fn axiom_projection_proves_base_conflicts_and_never_derived_conflicts() {
        let task = axiom_resource_task();
        let (table, stats) = compute(&task, Limits::default(), |_| None);
        assert_eq!(stats.status, Status::Complete);
        assert_eq!(stats.projected_variables, 2);
        let table = table.unwrap();
        assert!(!table.reachable(3, 5));
        for derived in 6..10 {
            for other in 0..10 {
                assert!(table.reachable(derived, other));
                assert!(table.reachable(other, derived));
            }
        }
        let (_, base_stats) = compute(&resource_task(), Limits::default(), |_| None);
        assert_eq!(stats.mutex_pairs, base_stats.mutex_pairs);
        assert_eq!(stats.unreachable_facts, base_stats.unreachable_facts);
        // A resource stop or work cap must still discard ALL proofs, even
        // after completing the projection and most of the fixed point.
        for work in [0, 25, stats.work / 2, stats.work - 1] {
            let (table, partial) = compute(
                &task,
                Limits {
                    work,
                    ..Limits::default()
                },
                |_| None,
            );
            assert!(table.is_none());
            assert_eq!(partial.status, Status::WorkLimit);
            assert_eq!(
                (
                    partial.mutex_pairs,
                    partial.new_mutex_pairs,
                    partial.unreachable_facts
                ),
                (0, 0, 0)
            );
        }
        for reason in [StopReason::Deadline, StopReason::Memory] {
            let (table, stopped) = compute(&task, Limits::default(), |_| Some(reason));
            assert!(table.is_none());
            assert_eq!(stopped.status.stopped(), Some(reason));
        }
    }

    #[test]
    fn dropping_a_derived_guard_does_not_make_an_overwrite_unconditional() {
        let mut task = resource_task();
        task.initial = vec![0, 1, 1];
        task.axioms.push(crate::fdr::Axiom {
            conditions: vec![Fact::new(0, 1)],
            variable: 2,
            pre: 1,
            post: 0,
        });
        task.operators.truncate(1);
        task.operators[0].effects = vec![
            Effect {
                conditions: vec![],
                variable: 0,
                pre: None,
                post: 1,
            },
            Effect {
                conditions: vec![Fact::new(2, 0)],
                variable: 1,
                pre: None,
                post: 0,
            },
        ];
        // The derived guard is false in the source state. The real successor
        // is [1, 1, 0], so v1=1 MUST persist alongside the new v0=1.
        let (table, stats) = compute(&task, Limits::default(), |_| None);
        assert_eq!(stats.status, Status::Complete);
        assert!(table.unwrap().reachable(1, 3));
    }

    #[test]
    fn projected_pairs_survive_an_independent_axiom_reset_and_closure_oracle() {
        let mut rng = 419u64;
        let mut next = || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng as usize
        };
        for case in 0..128 {
            let mut task = axiom_resource_task();
            let definition: Vec<_> = (0..4).map(|_| next() % 2).collect();
            task.axioms[0].conditions =
                vec![Fact::new(0, definition[0]), Fact::new(1, definition[1])];
            task.axioms[1].conditions =
                vec![Fact::new(3, definition[2]), Fact::new(2, definition[3])];
            // Independent Boolean evaluation, deliberately not close_axioms:
            // both derived values are recomputed after EVERY base transition.
            let close = |state: &mut Vec<usize>| {
                state[3] = usize::from(!(state[0] == definition[0] && state[1] == definition[1]));
                state[4] = usize::from(!(state[3] == definition[2] && state[2] == definition[3]));
            };
            task.initial = (0..5).map(|_| next() % 2).collect();
            task.operators.clear();
            for op in 0..6 {
                let mut effects = vec![];
                for variable in 0..3 {
                    if next() % 2 == 0 {
                        effects.push(Effect {
                            conditions: (0..next() % 3)
                                .map(|_| Fact::new(next() % 5, next() % 2))
                                .collect(),
                            variable,
                            pre: (next() % 3 == 0).then(|| next() % 2),
                            post: next() % 2,
                        });
                    }
                }
                task.operators.push(Operator {
                    name: format!("a{op}"),
                    cost: 1,
                    effects,
                    prevail: (0..next() % 3)
                        .map(|_| Fact::new(next() % 5, next() % 2))
                        .collect(),
                });
            }
            let mut initial = task.initial.clone();
            close(&mut initial);
            let mut reached = std::collections::HashSet::from([initial.clone()]);
            let mut queue = std::collections::VecDeque::from([initial]);
            while let Some(state) = queue.pop_front() {
                for op in &task.operators {
                    if !op.prevail.iter().all(|p| state[p.variable] == p.value)
                        || !op
                            .effects
                            .iter()
                            .all(|e| e.pre.is_none_or(|p| state[e.variable] == p))
                    {
                        continue;
                    }
                    let mut successor = state.clone();
                    for e in &op.effects {
                        if e.conditions.iter().all(|p| state[p.variable] == p.value) {
                            successor[e.variable] = e.post;
                        }
                    }
                    close(&mut successor);
                    if reached.insert(successor.clone()) {
                        queue.push_back(successor);
                    }
                }
            }
            for declared in [false, true] {
                if declared {
                    // Include both base and derived facts in declared groups.
                    // Raw initial derived values may contradict valid groups;
                    // only their base-base pairs may constrain the projection.
                    task.mutex_groups = (0..10)
                        .flat_map(|a| (a + 1..10).map(move |b| (a, b)))
                        .filter(|&(a, b)| {
                            a / 2 != b / 2
                                && reached
                                    .iter()
                                    .all(|s| s[a / 2] != a % 2 || s[b / 2] != b % 2)
                        })
                        .map(|(a, b)| vec![Fact::new(a / 2, a % 2), Fact::new(b / 2, b % 2)])
                        .collect();
                }
                let (table, stats) = compute(&task, Limits::default(), |_| None);
                assert_eq!(
                    stats.status,
                    Status::Complete,
                    "case {case}, declared {declared}"
                );
                let table = table.unwrap();
                for state in &reached {
                    for a in 0..5 {
                        for b in 0..5 {
                            assert!(
                                table.reachable(a * 2 + state[a], b * 2 + state[b]),
                                "false mutex, case {case}, declared {declared}: {state:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn every_exactly_reachable_pair_survives_conditional_pair_relaxation() {
        let mut rng = 37u64;
        let mut next = || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng as usize
        };
        for case in 0..128 {
            let mut task = resource_task();
            task.initial = (0..3).map(|_| next() % 2).collect();
            task.operators.clear();
            for op in 0..4 {
                let mut pre = vec![];
                let mut effects = vec![];
                for variable in 0..3 {
                    let old = (next() % 3 == 0).then(|| next() % 2);
                    if next() % 2 == 0 {
                        let conditions = if next() % 2 == 0 {
                            vec![Fact::new(next() % 3, next() % 2)]
                        } else {
                            vec![]
                        };
                        effects.push(Effect {
                            conditions,
                            variable,
                            pre: old,
                            post: next() % 2,
                        });
                    } else if let Some(value) = old {
                        pre.push(Fact::new(variable, value));
                    }
                }
                task.operators.push(Operator {
                    name: format!("a{op}"),
                    prevail: pre,
                    effects,
                    cost: 1,
                });
            }
            let (table, stats) = compute(&task, Limits::default(), |_| None);
            assert_eq!(stats.status, Status::Complete, "case {case}");
            let table = table.unwrap();
            let mut reached = std::collections::HashSet::from([task.initial.clone()]);
            let mut queue = std::collections::VecDeque::from([task.initial.clone()]);
            while let Some(state) = queue.pop_front() {
                for a in 0..3 {
                    for b in 0..3 {
                        assert!(
                            table.reachable(a * 2 + state[a], b * 2 + state[b]),
                            "false mutex, case {case}: {state:?}"
                        );
                    }
                }
                for op in &task.operators {
                    if !op.prevail.iter().all(|p| state[p.variable] == p.value)
                        || !op
                            .effects
                            .iter()
                            .all(|e| e.pre.is_none_or(|p| state[e.variable] == p))
                    {
                        continue;
                    }
                    let mut successor = state.clone();
                    for e in &op.effects {
                        if e.conditions.iter().all(|p| state[p.variable] == p.value) {
                            successor[e.variable] = e.post;
                        }
                    }
                    if reached.insert(successor.clone()) {
                        queue.push_back(successor);
                    }
                }
            }
            // Supply a subset of independently proved mutexes. Constraining
            // the relaxation must still preserve every exactly reachable pair.
            task.mutex_groups = (0..6)
                .flat_map(|a| (a + 1..6).map(move |b| (a, b)))
                .filter(|&(a, b)| {
                    a / 2 != b / 2
                        && (a + b) % 2 == 0
                        && reached
                            .iter()
                            .all(|state| state[a / 2] != a % 2 || state[b / 2] != b % 2)
                })
                .map(|(a, b)| vec![Fact::new(a / 2, a % 2), Fact::new(b / 2, b % 2)])
                .collect();
            let (constrained, stats) = compute(&task, Limits::default(), |_| None);
            assert_eq!(stats.status, Status::Complete);
            let constrained = constrained.unwrap();
            for state in &reached {
                for a in 0..3 {
                    for b in 0..3 {
                        assert!(
                            constrained.reachable(a * 2 + state[a], b * 2 + state[b]),
                            "false mutex after seeding declared groups, case {case}: {state:?}"
                        );
                    }
                }
            }
        }
    }
}
