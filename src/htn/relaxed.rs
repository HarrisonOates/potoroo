//! Cost-aware delete relaxation for a partial HTN plan.
//!
//! Use h_max (Bonet and Geffner, 2001, equations 1 and 5) from the original
//! initial state, restricted to productive descendants of the active tasks.
//! https://doi.org/10.1016/S0004-3702(01)00108-4
//!
//! Adaptation to our plan space: committed primitive types cost zero, since
//! their occurrences are already paid in g. Other actions retain their costs.
//! Require the original goals and every committed action's preconditions.
//! Any real completion induces a relaxed execution achieving these facts at
//! no greater additional cost. Allowing free reuse of committed types and
//! ignoring multiplicity, ordering, deletes and support focus only relaxes it
//! further. Thus h_max lower-bounds the remaining cost; combine it with TDG
//! and necessary-support bounds by max, never addition.
//!
//! This is not the delete-and-ordering HTN relaxation: we retain only possible
//! descendant actions, not the requirement to realize a decomposition tree.
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::time::Instant;

use super::model::{FactId, Problem, TaskId};
use super::plan::Plan;
use super::search::Stats;
use super::tdg::{Recompute, Tdg, COST_CAP};
use super::tdg_cache::BoundCache;

const UNREACHABLE: u128 = u128::MAX;

pub(crate) struct RelaxedBound {
    cache: BoundCache,
    reachable: Vec<bool>,
    tasks: Vec<TaskId>,
    traversal: Vec<TaskId>,
    committed: Vec<bool>,
    consumers: Vec<Vec<TaskId>>,
    consumer_facts: Vec<FactId>,
    missing: Vec<usize>,
    costs: Vec<u128>,
    settled: Vec<bool>,
    touched: Vec<FactId>,
    ready: BinaryHeap<Reverse<(u128, FactId)>>,
    required: Vec<FactId>,
    closure_ready: bool,
}

impl RelaxedBound {
    pub(crate) fn new(problem: &Problem, deadline: Option<Instant>) -> Option<Self> {
        let expired = || deadline.is_some_and(|d| Instant::now() >= d);
        if expired() {
            return None;
        }
        let result = Self {
            cache: BoundCache::default(),
            reachable: vec![false; problem.tasks.len()],
            tasks: Vec::new(),
            traversal: Vec::new(),
            committed: vec![false; problem.actions.len()],
            consumers: vec![Vec::new(); problem.facts.len()],
            consumer_facts: Vec::new(),
            missing: vec![0; problem.actions.len()],
            costs: vec![UNREACHABLE; problem.facts.len()],
            settled: vec![false; problem.facts.len()],
            touched: Vec::new(),
            ready: BinaryHeap::new(),
            required: Vec::new(),
            closure_ready: false,
        };
        (!expired()).then_some(result)
    }

    /// Outer None is cancellation; inner None proves relaxed unreachability.
    pub(crate) fn remaining_cost(
        &mut self,
        problem: &Problem,
        plan: &Plan,
        tdg: &Tdg,
        deadline: Option<Instant>,
        stats: &mut Stats,
    ) -> Option<Option<u128>> {
        self.bound(problem, plan, tdg, None, deadline, stats)
    }

    /// Compute max(TDG, h_max), sharing hierarchy discovery and fact propagation
    /// on a cache miss. The h_max cache still stores only its own bound.
    pub(crate) fn with_tdg(
        &mut self,
        problem: &Problem,
        plan: &Plan,
        tdg: &Tdg,
        recompute: &mut Recompute,
        deadline: Option<Instant>,
        stats: &mut Stats,
    ) -> Option<Option<u128>> {
        self.bound(problem, plan, tdg, Some(recompute), deadline, stats)
    }

    fn bound(
        &mut self,
        problem: &Problem,
        plan: &Plan,
        tdg: &Tdg,
        recompute: Option<&mut Recompute>,
        deadline: Option<Instant>,
        stats: &mut Stats,
    ) -> Option<Option<u128>> {
        let expired = || deadline.is_some_and(|d| Instant::now() >= d);
        if expired() {
            return None;
        }
        let mut key = BoundCache::key(plan);
        // Multiplicity changes structural cost, but not this relaxation.
        key.dedup();
        if expired() {
            return None;
        }
        if let Some(bound) = self.cache.get(&key) {
            stats.relaxed_cache_hits += 1;
            // A scalar cache entry does not retain a closure. If TDG still
            // needs evaluation, use its cheaper Boolean reachability pass.
            return match (bound, recompute) {
                (Some(h), Some(index)) => Some(
                    index
                        .remaining_cost(problem, plan, tdg, deadline)?
                        .map(|c| c.max(h)),
                ),
                _ => Some(bound),
            };
        }
        stats.relaxed_evaluated += 1;
        let bound = self.propagate(problem, &key, tdg, expired)?;
        self.cache.insert(key, bound);
        match (bound, recompute) {
            (Some(h), Some(index)) => {
                let structural = if self.closure_ready {
                    stats.relaxed_shared += 1;
                    index.remaining_from_relaxed(
                        problem,
                        plan,
                        tdg,
                        (&self.tasks, &self.missing),
                        deadline,
                    )?
                } else {
                    // h_max is already zero when every required fact is
                    // initial. Keep TDG's cheaper Boolean propagation then.
                    index.remaining_cost(problem, plan, tdg, deadline)?
                };
                Some(structural.map(|c| c.max(h)))
            }
            _ => Some(bound),
        }
    }

    fn reset(&mut self) {
        for task in self.tasks.drain(..) {
            self.reachable[task] = false;
            if task < self.committed.len() {
                self.committed[task] = false;
            }
        }
        for fact in self.consumer_facts.drain(..) {
            self.consumers[fact].clear();
        }
        for fact in self.touched.drain(..) {
            self.costs[fact] = UNREACHABLE;
            self.settled[fact] = false;
        }
        self.traversal.clear();
        self.ready.clear();
        self.required.clear();
        self.closure_ready = false;
    }

    fn discover(&mut self, task: TaskId) {
        if !std::mem::replace(&mut self.reachable[task], true) {
            self.tasks.push(task);
            self.traversal.push(task);
        }
    }

    fn add_fact(&mut self, fact: FactId, cost: u128) {
        if cost < self.costs[fact] {
            if self.costs[fact] == UNREACHABLE {
                self.touched.push(fact);
            }
            self.costs[fact] = cost;
            self.ready.push(Reverse((cost, fact)));
        }
    }

    fn enable(&mut self, problem: &Problem, task: TaskId, pre_cost: u128) {
        let action = &problem.actions[task];
        let price = if self.committed[task] {
            0
        } else {
            action.cost as u128
        };
        let cost = (pre_cost + price).min(COST_CAP);
        for &fact in &action.add {
            self.add_fact(fact, cost);
        }
    }

    #[cfg(test)]
    fn evaluate(
        &mut self,
        problem: &Problem,
        active: &[TaskId],
        tdg: &Tdg,
        expired: impl FnMut() -> bool,
    ) -> Option<Option<u128>> {
        self.propagate(problem, active, tdg, expired)
    }

    fn propagate(
        &mut self,
        problem: &Problem,
        active: &[TaskId],
        tdg: &Tdg,
        mut expired: impl FnMut() -> bool,
    ) -> Option<Option<u128>> {
        if expired() {
            return None;
        }
        self.reset();
        self.required.extend(&problem.goal);
        for &task in active {
            if expired() {
                return None;
            }
            self.discover(task);
            if let Some(action) = problem.actions.get(task) {
                self.committed[task] = true;
                self.required.extend(&action.preconditions);
            }
        }
        if self
            .required
            .iter()
            .all(|f| problem.initial.binary_search(f).is_ok())
        {
            return (!expired()).then_some(Some(0));
        }
        while let Some(task) = self.traversal.pop() {
            if expired() {
                return None;
            }
            if let Some(action) = problem.actions.get(task) {
                self.missing[task] = action.preconditions.len();
                for &fact in &action.preconditions {
                    if expired() {
                        return None;
                    }
                    if self.consumers[fact].is_empty() {
                        self.consumer_facts.push(fact);
                    }
                    self.consumers[fact].push(task);
                }
            }
            for &method in &problem.methods_by_task[task] {
                if expired() {
                    return None;
                }
                if tdg.method_cost(method).is_some() {
                    for &child in &problem.methods[method].subtasks {
                        if expired() {
                            return None;
                        }
                        self.discover(child);
                    }
                }
            }
        }
        for &fact in &problem.initial {
            if expired() {
                return None;
            }
            self.add_fact(fact, 0);
        }
        for index in 0..self.tasks.len() {
            if expired() {
                return None;
            }
            let task = self.tasks[index];
            if task < problem.actions.len() && self.missing[task] == 0 {
                self.enable(problem, task, 0);
            }
        }
        while let Some(Reverse((cost, fact))) = self.ready.pop() {
            if expired() {
                return None;
            }
            if cost != self.costs[fact] || std::mem::replace(&mut self.settled[fact], true) {
                continue;
            }
            for index in 0..self.consumers[fact].len() {
                if expired() {
                    return None;
                }
                let task = self.consumers[fact][index];
                self.missing[task] -= 1;
                if self.missing[task] == 0 {
                    // Facts settle in increasing cost order: the last
                    // precondition supplies max, including zero-cost cycles.
                    self.enable(problem, task, cost);
                }
            }
        }
        self.closure_ready = true;
        let mut bound = 0;
        for &fact in &self.required {
            if expired() {
                return None;
            }
            if self.costs[fact] == UNREACHABLE {
                return Some(None);
            }
            bound = bound.max(self.costs[fact]);
        }
        Some(Some(bound))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::htn::{Action, Method, Task};

    fn action(cost: u64, pre: &[usize], add: &[usize]) -> Action {
        Action {
            cost,
            preconditions: pre.into(),
            add: add.into(),
            delete: vec![],
        }
    }

    fn problem(
        actions: Vec<Action>,
        compounds: usize,
        methods: &[(usize, Vec<usize>)],
        initial: &[usize],
        goal: &[usize],
    ) -> Problem {
        let tasks = (0..actions.len() + compounds)
            .map(|id| Task {
                name: format!("t{id}"),
                primitive: id < actions.len(),
            })
            .collect::<Vec<_>>();
        let root = tasks.len() - 1;
        Problem::new(
            vec!["p".into(), "q".into(), "r".into()],
            actions,
            tasks,
            methods
                .iter()
                .enumerate()
                .map(|(id, (task, children))| Method {
                    name: format!("m{id}"),
                    task: *task,
                    subtasks: children.clone(),
                    orderings: vec![],
                })
                .collect(),
            initial.into(),
            goal.into(),
            root,
        )
        .unwrap()
    }

    fn chain(cost: u64) -> Problem {
        problem(
            vec![action(cost, &[], &[0]), action(cost, &[0], &[1])],
            1,
            &[(2, vec![2, 2]), (2, vec![]), (2, vec![0]), (2, vec![1])],
            &[],
            &[1],
        )
    }

    #[test]
    fn chain_costs_move_into_g_and_duplicate_networks_share_a_cache_entry() {
        let p = chain(1);
        let tdg = Tdg::new(&p);
        let mut bound = RelaxedBound::new(&p, None).unwrap();
        let mut stats = Stats::default();
        let initial = Plan::initial(&p);
        assert_eq!(
            bound.remaining_cost(&p, &initial, &tdg, None, &mut stats),
            Some(Some(2))
        );
        let split = initial
            .decompose(&p, *initial.tasks().next().unwrap(), 0)
            .unwrap()
            .unwrap();
        assert_eq!(
            bound.remaining_cost(&p, &split, &tdg, None, &mut stats),
            Some(Some(2))
        );
        assert_eq!(stats.relaxed_evaluated, 1);
        assert_eq!(stats.relaxed_cache_hits, 1);
        let prepared = split
            .decompose(&p, *split.tasks().next().unwrap(), 2)
            .unwrap()
            .unwrap();
        assert_eq!(prepared.cost(), 1);
        assert_eq!(
            bound.remaining_cost(&p, &prepared, &tdg, None, &mut stats),
            Some(Some(1))
        );
        let finished = prepared
            .decompose(&p, *prepared.tasks().find(|t| t.task == 2).unwrap(), 3)
            .unwrap()
            .unwrap();
        assert_eq!(finished.cost(), 2);
        assert_eq!(
            bound.remaining_cost(&p, &finished, &tdg, None, &mut stats),
            Some(Some(0))
        );
        assert_eq!(
            bound.remaining_cost(&p, &initial, &tdg, None, &mut stats),
            Some(Some(2))
        );
    }

    #[test]
    fn unreachable_and_overflow_are_distinct_and_commitments_remain_required() {
        let p = chain(u64::MAX);
        let mut bound = RelaxedBound::new(&p, None).unwrap();
        let tdg = Tdg::new(&p);
        assert_eq!(
            bound.evaluate(&p, &[2], &tdg, || false),
            Some(Some(COST_CAP))
        );
        assert_eq!(
            bound.evaluate(&p, &[0, 2], &tdg, || false),
            Some(Some(u64::MAX as u128))
        );
        // The preparer exists in the model, but is outside this network.
        assert_eq!(bound.evaluate(&p, &[1], &tdg, || false), Some(None));
        let p = problem(vec![action(0, &[0], &[])], 0, &[], &[], &[]);
        let tdg = Tdg::new(&p);
        let mut bound = RelaxedBound::new(&p, None).unwrap();
        let mut stats = Stats::default();
        for _ in 0..2 {
            assert_eq!(
                bound.remaining_cost(&p, &Plan::initial(&p), &tdg, None, &mut stats),
                Some(None)
            );
        }
        assert_eq!(stats.relaxed_evaluated, 1);
        assert_eq!(stats.relaxed_cache_hits, 1);
    }

    // Independent exhaustive delete-relaxed state search on three facts.
    // This checks admissibility against exact conjunction costs, not another
    // implementation of h_max. Actions can be freely reused as in the bound.
    fn exact_relaxed(p: &Problem, active: &[usize], tdg: &Tdg) -> Option<u128> {
        let mut allowed = vec![false; p.tasks.len()];
        for &task in active {
            allowed[task] = true;
        }
        loop {
            let before = allowed.clone();
            for (id, m) in p.methods.iter().enumerate() {
                if allowed[m.task] && tdg.method_cost(id).is_some() {
                    for &child in &m.subtasks {
                        allowed[child] = true;
                    }
                }
            }
            if before == allowed {
                break;
            }
        }
        let mask = |facts: &[usize]| facts.iter().fold(0usize, |bits, f| bits | (1 << f));
        let goal = active
            .iter()
            .filter_map(|&t| p.actions.get(t))
            .fold(mask(&p.goal), |bits, a| bits | mask(&a.preconditions));
        let mut distance = [None; 8];
        distance[mask(&p.initial)] = Some(0u128);
        loop {
            let before = distance;
            for state in 0..8 {
                let Some(cost) = distance[state] else {
                    continue;
                };
                for (task, action) in p.actions.iter().enumerate() {
                    if !allowed[task]
                        || state & mask(&action.preconditions) != mask(&action.preconditions)
                    {
                        continue;
                    }
                    let next = state | mask(&action.add);
                    let price = if active.contains(&task) {
                        0
                    } else {
                        action.cost as u128
                    };
                    let candidate = (cost + price).min(COST_CAP);
                    if distance[next].is_none_or(|old| candidate < old) {
                        distance[next] = Some(candidate);
                    }
                }
            }
            if before == distance {
                break;
            }
        }
        distance
            .iter()
            .enumerate()
            .filter(|(state, _)| state & goal == goal)
            .filter_map(|(_, cost)| *cost)
            .min()
    }

    #[test]
    fn bound_is_admissible_against_exhaustive_relaxed_state_search() {
        let mut seed = 0x32ab_1987_a55bu64;
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed as usize
        };
        let facts = |mask: usize| (0..3).filter(|f| mask & (1 << f) != 0).collect::<Vec<_>>();
        for case in 0..512 {
            let actions = (0..3)
                .map(|_| {
                    action(
                        [0, 1, 7, u64::MAX][next() % 4],
                        &facts(next() % 8),
                        &facts(next() % 8),
                    )
                })
                .collect();
            let methods = (0..8)
                .map(|_| {
                    (
                        3 + next() % 3,
                        (0..next() % 4).map(|_| next() % 6).collect(),
                    )
                })
                .collect::<Vec<_>>();
            let p = problem(actions, 3, &methods, &facts(next() % 8), &facts(next() % 8));
            let tdg = Tdg::new(&p);
            let mut bound = RelaxedBound::new(&p, None).unwrap();
            for active in [
                vec![5],
                vec![0, 5],
                vec![1, 4, 5],
                vec![0, 1, 2],
                vec![5, 5],
                vec![],
            ] {
                let actual = bound.evaluate(&p, &active, &tdg, || false).unwrap();
                let expected = exact_relaxed(&p, &active, &tdg);
                assert_eq!(
                    actual.is_some(),
                    expected.is_some(),
                    "case {case} active {active:?}"
                );
                if let (Some(h), Some(optimal)) = (actual, expected) {
                    assert!(
                        h <= optimal,
                        "case {case} active {active:?}: {h} > {optimal}"
                    );
                }
            }
            // Compare the shared pass to two independent evaluations, on the
            // initial network and each representable first decomposition.
            let mut shared = RelaxedBound::new(&p, None).unwrap();
            let mut joined = Recompute::new(&p, None).unwrap();
            let mut separate = Recompute::new(&p, None).unwrap();
            let mut stats = Stats::default();
            let initial = Plan::initial(&p);
            let mut plans = vec![initial.clone()];
            for &method in &p.methods_by_task[p.root] {
                match initial.decompose(&p, *initial.tasks().next().unwrap(), method) {
                    Ok(Some(plan)) => plans.push(plan),
                    Err(error) if error.contains("overflow") => {}
                    other => panic!("unexpected decomposition: {other:?}"),
                }
            }
            for plan in plans {
                let h = bound
                    .remaining_cost(&p, &plan, &tdg, None, &mut Stats::default())
                    .unwrap();
                let structural = separate.remaining_cost(&p, &plan, &tdg, None).unwrap();
                let expected = structural.zip(h).map(|(a, b)| a.max(b));
                assert_eq!(
                    shared.with_tdg(&p, &plan, &tdg, &mut joined, None, &mut stats),
                    Some(expected),
                    "shared case {case}"
                );
                let reused = stats.relaxed_shared;
                let hits = stats.relaxed_cache_hits;
                assert_eq!(
                    shared.with_tdg(&p, &plan, &tdg, &mut joined, None, &mut stats),
                    Some(expected),
                    "cached case {case}"
                );
                assert_eq!(stats.relaxed_shared, reused);
                assert_eq!(stats.relaxed_cache_hits, hits + 1);
                assert_eq!(
                    shared.remaining_cost(&p, &plan, &tdg, None, &mut stats),
                    Some(h)
                );
            }
        }
    }

    #[test]
    fn sharing_keeps_zero_shortcuts_and_caches_only_the_hmax_bound() {
        for (goal, expected_h, shared) in [(0, 0, 0), (1, 7, 1)] {
            let p = problem(
                vec![action(7, &[0], &[1])],
                2,
                &[(1, vec![0]), (2, vec![1, 1])],
                &[0],
                &[goal],
            );
            let tdg = Tdg::new(&p);
            let mut bound = RelaxedBound::new(&p, None).unwrap();
            let mut recompute = Recompute::new(&p, None).unwrap();
            let mut stats = Stats::default();
            let plan = Plan::initial(&p);
            assert_eq!(
                bound.with_tdg(&p, &plan, &tdg, &mut recompute, None, &mut stats),
                Some(Some(14))
            );
            assert_eq!(stats.relaxed_shared, shared);
            // Initial goals need no weighted propagation. With a future goal,
            // h_max charges one achiever; TDG counts both required occurrences.
            assert_eq!(
                bound.remaining_cost(&p, &plan, &tdg, None, &mut stats),
                Some(Some(expected_h))
            );
            assert_eq!(
                bound.with_tdg(&p, &plan, &tdg, &mut recompute, None, &mut stats),
                Some(Some(14))
            );
            assert_eq!(stats.relaxed_shared, shared);
            assert!(bound
                .with_tdg(
                    &p,
                    &plan,
                    &tdg,
                    &mut recompute,
                    Some(Instant::now()),
                    &mut stats
                )
                .is_none());
            assert_eq!(
                bound.with_tdg(&p, &plan, &tdg, &mut recompute, None, &mut stats),
                Some(Some(14))
            );
        }
    }

    #[test]
    fn cancellation_at_each_checkpoint_does_not_poison_reused_buffers_or_cache() {
        let p = chain(1);
        let tdg = Tdg::new(&p);
        let mut bound = RelaxedBound::new(&p, None).unwrap();
        let mut checkpoints = 0;
        assert_eq!(
            bound.evaluate(&p, &[2], &tdg, || {
                checkpoints += 1;
                false
            }),
            Some(Some(2))
        );
        for stop in 1..=checkpoints {
            let mut ticks = 0;
            assert!(bound
                .evaluate(&p, &[2], &tdg, || {
                    ticks += 1;
                    ticks == stop
                })
                .is_none());
            assert_eq!(bound.evaluate(&p, &[0, 2], &tdg, || false), Some(Some(1)));
            assert_eq!(bound.evaluate(&p, &[2], &tdg, || false), Some(Some(2)));
        }
        let expired = Some(Instant::now());
        assert!(RelaxedBound::new(&p, expired).is_none());
        assert!(bound
            .remaining_cost(&p, &Plan::initial(&p), &tdg, expired, &mut Stats::default())
            .is_none());
        assert_eq!(bound.cache.get(&[2]), None);
        assert_eq!(
            bound.remaining_cost(&p, &Plan::initial(&p), &tdg, None, &mut Stats::default()),
            Some(Some(2))
        );
    }
}
