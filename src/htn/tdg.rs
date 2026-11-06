//! Task-decomposition graph relaxation. Methods are AND nodes and tasks are OR
//! nodes. The static bound ignores preconditions, deletes and orderings.
//!
//! A generalized Dijkstra traversal settles nonnegative minimum primitive costs;
//! repeated child occurrences contribute repeatedly. Pure recursion stays
//! unreachable, while empty methods and recursive exits seed finite costs.
//!
//! Structural cost recurrence: Bercher et al., "An Admissible HTN Planning
//! Heuristic" (IJCAI 2017), Definitions 2–3. Optional recomputation follows
//! section 5.1: restrict primitive tasks to descendants of the active network,
//! remove delete-relaxed unreachable actions, then recompute minimum costs.
//! Ordering and causal-link refinements do not change this relaxation.
//! https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.090/Publikationen/2017/Bercher17AdmissibleHTNHeuristic.pdf
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashSet, VecDeque};
use std::time::Instant;

use super::model::{FactId, MethodId, Problem, TaskId};
use super::plan::{Occurrence, Plan};

/// Bounds saturate one above the largest representable solution cost. This is
/// distinct from `None` (no finite decomposition), including for deep recursion.
pub const COST_CAP: u128 = u64::MAX as u128 + 1;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum TdgMode {
    /// Compute structural costs once, ignoring action preconditions.
    #[default]
    Static,
    /// Recompute costs using relaxed reachability after decomposition choices.
    Recompute,
    /// Defer reachability recomputation until a node is selected for expansion.
    Lazy,
    /// Lazy recomputation with a bounded cache of active-task multiset bounds.
    LazyCached,
}

#[derive(Debug)]
pub struct Tdg {
    task_costs: Vec<Option<u128>>,
    method_costs: Vec<Option<u128>>,
    may_add: Vec<HashSet<FactId>>,
}

impl Tdg {
    pub fn new(problem: &Problem) -> Self {
        Self::with_deadline(problem, None).expect("no deadline")
    }

    /// `None` means cancellation, not structural unreachability.
    pub(crate) fn with_deadline(problem: &Problem, deadline: Option<Instant>) -> Option<Self> {
        let expired = || deadline.is_some_and(|d| Instant::now() >= d);
        let parents = task_parents(problem, deadline)?;
        let costs = minimum_costs(problem, &parents, None, deadline)?;
        let task_costs = costs.task;
        let method_costs = costs.method;

        // Only productive methods can occur in a complete decomposition. These
        // edges propagate possible positive effects, never guaranteed effects.
        let mut productive_parents = vec![Vec::new(); problem.tasks.len()];
        for (id, method) in problem.methods.iter().enumerate() {
            if expired() {
                return None;
            }
            if method_costs[id].is_some() {
                for &task in &method.subtasks {
                    productive_parents[task].push(method.task);
                }
            }
        }
        for parents in &mut productive_parents {
            parents.sort_unstable();
            parents.dedup();
        }
        let mut may_add = vec![HashSet::new(); problem.tasks.len()];
        let mut effects = VecDeque::new();
        for (task, action) in problem.actions.iter().enumerate() {
            for &fact in &action.add {
                may_add[task].insert(fact);
                effects.push_back((task, fact));
            }
        }
        while let Some((task, fact)) = effects.pop_front() {
            if expired() {
                return None;
            }
            for &parent in &productive_parents[task] {
                if expired() {
                    return None;
                }
                if may_add[parent].insert(fact) {
                    effects.push_back((parent, fact));
                }
            }
        }
        if expired() {
            return None;
        }
        Some(Self {
            task_costs,
            method_costs,
            may_add,
        })
    }

    /// Minimum primitive cost of a decomposition, capped at `COST_CAP`.
    /// `None` proves there is no finite primitive decomposition.
    pub fn task_cost(&self, task: TaskId) -> Option<u128> {
        self.task_costs[task]
    }

    pub fn method_cost(&self, method: MethodId) -> Option<u128> {
        self.method_costs[method]
    }

    /// A conservative reachability test, not an abstract task's causal effect.
    pub fn may_add(&self, task: TaskId, fact: FactId) -> bool {
        self.may_add[task].contains(&fact)
    }

    pub(crate) fn method_may_add(&self, problem: &Problem, method: MethodId, fact: FactId) -> bool {
        self.method_cost(method).is_some()
            && problem.methods[method]
                .subtasks
                .iter()
                .any(|&task| self.may_add(task, fact))
    }

    /// Remaining primitive cost. Active primitives are already charged to g;
    /// only active compound *occurrences* contribute to h.
    pub fn remaining_cost(&self, problem: &Problem, plan: &Plan) -> Option<u128> {
        plan.tasks()
            .filter(|t| !problem.tasks[t.task].primitive)
            .try_fold(0u128, |sum, t| {
                self.task_cost(t.task).map(|c| (sum + c).min(COST_CAP))
            })
    }

    /// Check a method before allocating its children (which might overflow g).
    pub(crate) fn replacement_cost(
        &self,
        problem: &Problem,
        plan: &Plan,
        parent: Occurrence,
        method: MethodId,
    ) -> Option<u128> {
        let start = (plan.cost() as u128 + self.method_cost(method)?).min(COST_CAP);
        plan.tasks()
            .filter(|t| t.id != parent.id && !problem.tasks[t.task].primitive)
            .try_fold(start, |sum, t| {
                self.task_cost(t.task).map(|c| (sum + c).min(COST_CAP))
            })
    }
}

fn task_parents(problem: &Problem, deadline: Option<Instant>) -> Option<Vec<Vec<MethodId>>> {
    let mut parents = vec![Vec::new(); problem.tasks.len()];
    for (id, method) in problem.methods.iter().enumerate() {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        for &task in &method.subtasks {
            // One edge per occurrence: repeated children contribute repeatedly.
            parents[task].push(id);
        }
    }
    Some(parents)
}

struct Costs {
    task: Vec<Option<u128>>,
    method: Vec<Option<u128>>,
}

fn minimum_costs(
    problem: &Problem,
    parents: &[Vec<MethodId>],
    allowed: Option<&[bool]>,
    deadline: Option<Instant>,
) -> Option<Costs> {
    let expired = || deadline.is_some_and(|d| Instant::now() >= d);
    let mut pending = Vec::with_capacity(problem.methods.len());
    let mut sums = vec![0u128; problem.methods.len()];
    let mut ready = BinaryHeap::new();
    for (task, action) in problem.actions.iter().enumerate() {
        if expired() {
            return None;
        }
        if allowed.is_none_or(|a| a[task]) {
            ready.push(Reverse((action.cost as u128, task)));
        }
    }
    for method in &problem.methods {
        if expired() {
            return None;
        }
        pending.push(method.subtasks.len());
        if method.subtasks.is_empty() {
            ready.push(Reverse((0, method.task)));
        }
    }
    let mut task_costs = vec![None; problem.tasks.len()];
    while let Some(Reverse((cost, task))) = ready.pop() {
        if expired() {
            return None;
        }
        if task_costs[task].is_some() {
            continue;
        }
        task_costs[task] = Some(cost);
        for &method in &parents[task] {
            if expired() {
                return None;
            }
            sums[method] = (sums[method] + cost).min(COST_CAP);
            pending[method] -= 1;
            if pending[method] == 0 {
                ready.push(Reverse((sums[method], problem.methods[method].task)));
            }
        }
    }
    Some(Costs {
        task: task_costs,
        method: pending
            .iter()
            .zip(sums)
            .map(|(&left, sum)| (left == 0).then_some(sum))
            .collect(),
    })
}

/// Reusable scratch for the active hierarchy, scoped to one search. Only a
/// scalar bound enters OPEN. Reverse edges contain only the current subgraph;
/// touched-entry lists also make reuse safe after a cancelled evaluation.
pub(crate) struct Recompute {
    reachable: Vec<bool>,
    active_tasks: Vec<TaskId>,
    traversal: Vec<TaskId>,
    parents: Vec<Vec<MethodId>>,
    task_costs: Vec<Option<u128>>,
    pending: Vec<usize>,
    sums: Vec<u128>,
    ready: BinaryHeap<Reverse<(u128, TaskId)>>,
    consumers: Vec<Vec<TaskId>>,
    consumer_facts: Vec<FactId>,
    facts: Vec<bool>,
    fact_queue: Vec<FactId>,
    missing: Vec<usize>,
    executable: Vec<bool>,
}

impl Recompute {
    pub(crate) fn new(problem: &Problem, deadline: Option<Instant>) -> Option<Self> {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        let scratch = Self {
            reachable: vec![false; problem.tasks.len()],
            active_tasks: Vec::new(),
            traversal: Vec::new(),
            parents: vec![Vec::new(); problem.tasks.len()],
            task_costs: vec![None; problem.tasks.len()],
            pending: vec![0; problem.methods.len()],
            sums: vec![0; problem.methods.len()],
            ready: BinaryHeap::new(),
            consumers: vec![Vec::new(); problem.facts.len()],
            consumer_facts: Vec::new(),
            facts: vec![false; problem.facts.len()],
            fact_queue: Vec::new(),
            missing: vec![0; problem.actions.len()],
            executable: vec![false; problem.actions.len()],
        };
        (!deadline.is_some_and(|d| Instant::now() >= d)).then_some(scratch)
    }

    fn reset(&mut self) {
        for task in self.active_tasks.drain(..) {
            self.reachable[task] = false;
            self.parents[task].clear();
            self.task_costs[task] = None;
            if task < self.executable.len() {
                self.executable[task] = false;
            }
        }
        for fact in self.consumer_facts.drain(..) {
            self.consumers[fact].clear();
        }
        // Keep the whole fact queue until reset, including processed facts.
        for fact in self.fact_queue.drain(..) {
            self.facts[fact] = false;
        }
        self.traversal.clear();
        self.ready.clear();
    }

    fn discover(&mut self, task: TaskId) {
        if !std::mem::replace(&mut self.reachable[task], true) {
            // Record before any reverse edges are added, so cancellation before
            // visiting this task cannot leave edges behind for the next call.
            self.active_tasks.push(task);
            self.traversal.push(task);
        }
    }

    fn add_fact(&mut self, fact: FactId) {
        if !std::mem::replace(&mut self.facts[fact], true) {
            self.fact_queue.push(fact);
        }
    }

    fn enable(&mut self, problem: &Problem, task: TaskId) {
        self.executable[task] = true;
        self.ready
            .push(Reverse((problem.actions[task].cost as u128, task)));
        for &fact in &problem.actions[task].add {
            self.add_fact(fact);
        }
    }

    /// Outer `None` is cancellation; inner `None` proves no completion exists.
    /// Every real completion uses only active primitives and their descendants.
    /// Ignoring deletes, ordering and multiplicity overapproximates executable
    /// actions. Removing actions outside that closure therefore preserves every
    /// completion and makes the structural minimum cost an admissible bound.
    /// This is one hierarchy/reachability pass, not a joint pruning fixpoint.
    pub(crate) fn remaining_cost(
        &mut self,
        problem: &Problem,
        plan: &Plan,
        tdg: &Tdg,
        deadline: Option<Instant>,
    ) -> Option<Option<u128>> {
        self.evaluate(problem, plan, tdg, || {
            deadline.is_some_and(|d| Instant::now() >= d)
        })
    }

    fn evaluate(
        &mut self,
        problem: &Problem,
        plan: &Plan,
        tdg: &Tdg,
        mut expired: impl FnMut() -> bool,
    ) -> Option<Option<u128>> {
        if expired() {
            return None;
        }
        self.reset();
        for task in plan.tasks() {
            self.discover(task.task);
        }
        while let Some(task) = self.traversal.pop() {
            if expired() {
                return None;
            }
            if problem.tasks[task].primitive {
                let action = &problem.actions[task];
                self.missing[task] = action.preconditions.len();
                for &fact in &action.preconditions {
                    if self.consumers[fact].is_empty() {
                        self.consumer_facts.push(fact);
                    }
                    self.consumers[fact].push(task);
                }
            }
            for &id in &problem.methods_by_task[task] {
                if expired() {
                    return None;
                }
                if tdg.method_cost(id).is_none() {
                    continue;
                }
                let method = &problem.methods[id];
                self.pending[id] = method.subtasks.len();
                self.sums[id] = 0;
                if method.subtasks.is_empty() {
                    self.ready.push(Reverse((0, task)));
                }
                for &child in &method.subtasks {
                    self.discover(child);
                    // Keep one edge per occurrence, including repeated children.
                    self.parents[child].push(id);
                }
            }
        }
        // Build every consumer list before propagating facts. Initial facts and
        // zero-precondition actions can otherwise miss a not-yet-visited action.
        for &fact in &problem.initial {
            self.add_fact(fact);
        }
        for index in 0..self.active_tasks.len() {
            if expired() {
                return None;
            }
            let task = self.active_tasks[index];
            if problem.tasks[task].primitive && self.missing[task] == 0 {
                self.enable(problem, task);
            }
        }
        let mut next_fact = 0;
        while next_fact < self.fact_queue.len() {
            if expired() {
                return None;
            }
            let fact = self.fact_queue[next_fact];
            next_fact += 1;
            for index in 0..self.consumers[fact].len() {
                if expired() {
                    return None;
                }
                let task = self.consumers[fact][index];
                self.missing[task] -= 1;
                if self.missing[task] == 0 {
                    self.enable(problem, task);
                }
            }
        }
        if problem.goal.iter().any(|&f| !self.facts[f])
            || plan
                .tasks()
                .any(|t| problem.tasks[t.task].primitive && !self.executable[t.task])
        {
            return Some(None);
        }
        self.finish_costs(problem, plan, &mut expired)
    }

    /// Reuse h_max's complete productive closure and relaxed executability.
    /// A reachable primitive has zero missing preconditions iff executable.
    /// Goals and committed preconditions have already been checked by h_max.
    pub(crate) fn remaining_from_relaxed(
        &mut self,
        problem: &Problem,
        plan: &Plan,
        tdg: &Tdg,
        closure: (&[TaskId], &[usize]),
        deadline: Option<Instant>,
    ) -> Option<Option<u128>> {
        self.evaluate_relaxed(problem, plan, tdg, closure, || {
            deadline.is_some_and(|d| Instant::now() >= d)
        })
    }

    fn evaluate_relaxed(
        &mut self,
        problem: &Problem,
        plan: &Plan,
        tdg: &Tdg,
        closure: (&[TaskId], &[usize]),
        mut expired: impl FnMut() -> bool,
    ) -> Option<Option<u128>> {
        if expired() {
            return None;
        }
        self.reset();
        let (tasks, missing) = closure;
        // Register every touched task before building edges, including children
        // not visited yet if a deadline interrupts the following loop.
        for &task in tasks {
            if expired() {
                return None;
            }
            self.discover(task);
        }
        self.traversal.clear();
        for &task in tasks {
            if expired() {
                return None;
            }
            if task < problem.actions.len() && missing[task] == 0 {
                self.ready
                    .push(Reverse((problem.actions[task].cost as u128, task)));
            }
            for &id in &problem.methods_by_task[task] {
                if expired() {
                    return None;
                }
                if tdg.method_cost(id).is_none() {
                    continue;
                }
                let method = &problem.methods[id];
                self.pending[id] = method.subtasks.len();
                self.sums[id] = 0;
                if method.subtasks.is_empty() {
                    self.ready.push(Reverse((0, task)));
                }
                for &child in &method.subtasks {
                    if expired() {
                        return None;
                    }
                    self.parents[child].push(id);
                }
            }
        }
        self.finish_costs(problem, plan, &mut expired)
    }

    fn finish_costs(
        &mut self,
        problem: &Problem,
        plan: &Plan,
        expired: &mut impl FnMut() -> bool,
    ) -> Option<Option<u128>> {
        // Generalized Dijkstra on the induced productive hierarchy. An active
        // task includes all its productive methods and all their children, so
        // omitting the rest of the model cannot change any active task's cost.
        while let Some(Reverse((cost, task))) = self.ready.pop() {
            if expired() {
                return None;
            }
            if self.task_costs[task].is_some() {
                continue;
            }
            self.task_costs[task] = Some(cost);
            for &method in &self.parents[task] {
                if expired() {
                    return None;
                }
                self.sums[method] = (self.sums[method] + cost).min(COST_CAP);
                self.pending[method] -= 1;
                if self.pending[method] == 0 {
                    self.ready
                        .push(Reverse((self.sums[method], problem.methods[method].task)));
                }
            }
        }
        Some(
            plan.tasks()
                .filter(|t| !problem.tasks[t.task].primitive)
                .try_fold(0u128, |sum, t| {
                    self.task_costs[t.task].map(|c| (sum + c).min(COST_CAP))
                }),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::htn::{Action, Method, Task};

    // Independent relaxed reachability by repeated full-model scans, followed
    // by the original full-model cost traversal. No reusable state or active
    // reverse edges: this also checks that the optimization preserves the bound.
    fn reference_bound(p: &Problem, plan: &Plan, tdg: &Tdg) -> Option<u128> {
        let mut reachable = vec![false; p.tasks.len()];
        let mut tasks: Vec<_> = plan.tasks().map(|t| t.task).collect();
        while let Some(task) = tasks.pop() {
            if !std::mem::replace(&mut reachable[task], true) {
                for &method in &p.methods_by_task[task] {
                    if tdg.method_cost(method).is_some() {
                        tasks.extend(&p.methods[method].subtasks);
                    }
                }
            }
        }
        let mut facts: HashSet<_> = p.initial.iter().copied().collect();
        let mut executable = vec![false; p.actions.len()];
        loop {
            let mut changed = false;
            for (task, action) in p.actions.iter().enumerate() {
                if reachable[task]
                    && !executable[task]
                    && action.preconditions.iter().all(|f| facts.contains(f))
                {
                    executable[task] = true;
                    facts.extend(&action.add);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        if p.goal.iter().any(|f| !facts.contains(f))
            || plan
                .tasks()
                .any(|t| p.tasks[t.task].primitive && !executable[t.task])
        {
            return None;
        }
        let parents = task_parents(p, None).unwrap();
        let costs = minimum_costs(p, &parents, Some(&executable), None).unwrap();
        plan.tasks()
            .filter(|t| !p.tasks[t.task].primitive)
            .try_fold(0u128, |sum, t| {
                costs.task[t.task].map(|c| (sum + c).min(COST_CAP))
            })
    }

    #[test]
    fn active_bounds_match_full_model_across_recursive_networks_and_reuse() {
        for seed in 0..128u64 {
            let mut state = seed + 1;
            let mut draw = |n: usize| {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
                ((state >> 32) as usize) % n
            };
            let mut actions = Vec::new();
            for _ in 0..4 {
                actions.push(Action {
                    cost: [0, 1, 7, u64::MAX][draw(4)],
                    preconditions: (0..3).filter(|_| draw(3) == 0).collect(),
                    add: (0..3).filter(|_| draw(2) == 0).collect(),
                    delete: vec![],
                });
            }
            let mut methods = Vec::new();
            for task in 4..10 {
                for alternative in 0..3 {
                    methods.push(Method {
                        name: format!("m{task}-{alternative}"),
                        task,
                        subtasks: (0..draw(4)).map(|_| draw(10)).collect(),
                        orderings: vec![],
                    });
                }
            }
            let p = Problem::new(
                (0..3).map(|f| format!("f{f}")).collect(),
                actions,
                (0..10)
                    .map(|task| Task {
                        name: format!("t{task}"),
                        primitive: task < 4,
                    })
                    .collect(),
                methods,
                (0..3).filter(|_| draw(2) == 0).collect(),
                (0..3).filter(|_| draw(4) == 0).collect(),
                9,
            )
            .unwrap();
            let tdg = Tdg::new(&p);
            let mut scratch = Recompute::new(&p, None).unwrap();
            let mut plans = vec![Plan::initial(&p)];
            let mut next = 0;
            while next < plans.len() && plans.len() < 32 {
                if let Some(task) = plans[next].compound(&p) {
                    for &method in &p.methods_by_task[task.task] {
                        if let Ok(Some(child)) = plans[next].decompose(&p, task, method) {
                            plans.push(child);
                        }
                    }
                }
                next += 1;
            }
            // Backtracking across unrelated siblings must clear both reachable
            // facts and the reverse edges, not merely the accumulated costs.
            for plan in plans.iter().chain(plans.iter().rev()) {
                assert_eq!(
                    scratch.remaining_cost(&p, plan, &tdg, None),
                    Some(reference_bound(&p, plan, &tdg)),
                    "seed {seed}, depth {}",
                    plan.depth
                );
            }
        }
    }

    #[test]
    fn scratch_reuse_is_safe_after_every_cancellation_checkpoint() {
        let p = choice_problem();
        let tdg = Tdg::new(&p);
        let initial = Plan::initial(&p);
        let root = initial.compound(&p).unwrap();
        let expanded = initial.decompose(&p, root, 4).unwrap().unwrap();
        let choice = *expanded.tasks().find(|t| t.task == 4).unwrap();
        let without = expanded.decompose(&p, choice, 1).unwrap().unwrap();
        let mut scratch = Recompute::new(&p, None).unwrap();
        let mut checkpoints = 0;
        assert_eq!(
            scratch.evaluate(&p, &initial, &tdg, || {
                checkpoints += 1;
                false
            }),
            Some(Some(2))
        );
        for stop in 0..checkpoints {
            let mut visits = 0;
            assert_eq!(
                scratch.evaluate(&p, &initial, &tdg, || {
                    visits += 1;
                    visits > stop
                }),
                None
            );
            assert_eq!(
                scratch.remaining_cost(&p, &without, &tdg, None),
                Some(Some(14))
            );
            assert_eq!(
                scratch.remaining_cost(&p, &initial, &tdg, None),
                Some(Some(2))
            );
        }
    }

    fn choice_problem() -> Problem {
        let actions = vec![
            Action {
                cost: 0,
                preconditions: vec![],
                add: vec![0],
                delete: vec![],
            },
            Action {
                cost: 0,
                preconditions: vec![],
                add: vec![],
                delete: vec![],
            },
            Action {
                cost: 1,
                preconditions: vec![0],
                add: vec![],
                delete: vec![],
            },
            Action {
                cost: 7,
                preconditions: vec![],
                add: vec![],
                delete: vec![],
            },
        ];
        let methods = [
            (4, vec![0]),
            (4, vec![1]),
            (5, vec![2]),
            (5, vec![3]),
            (6, vec![4, 5, 5]),
        ]
        .into_iter()
        .enumerate()
        .map(|(id, (task, subtasks))| Method {
            name: format!("m{id}"),
            task,
            subtasks,
            orderings: vec![],
        })
        .collect();
        Problem::new(
            vec!["p".into()],
            actions,
            (0..7)
                .map(|i| Task {
                    name: format!("t{i}"),
                    primitive: i < 4,
                })
                .collect(),
            methods,
            vec![],
            vec![],
            6,
        )
        .unwrap()
    }

    #[test]
    fn recomputation_removes_lost_enablers_and_counts_repeated_tasks() {
        let p = choice_problem();
        let tdg = Tdg::new(&p);
        let mut index = Recompute::new(&p, None).unwrap();
        let initial = Plan::initial(&p);
        let root = initial.compound(&p).unwrap();
        let plan = initial.decompose(&p, root, 4).unwrap().unwrap();
        assert_eq!(index.remaining_cost(&p, &plan, &tdg, None), Some(Some(2)));
        let choice = *plan.tasks().find(|t| t.task == 4).unwrap();
        let without_enabler = plan.decompose(&p, choice, 1).unwrap().unwrap();
        assert_eq!(tdg.remaining_cost(&p, &without_enabler), Some(2));
        assert_eq!(
            index.remaining_cost(&p, &without_enabler, &tdg, None),
            Some(Some(14))
        );
        // A committed primitive is still available: plan-space search has not
        // executed it. It must enable both future cheap occurrences.
        let with_enabler = plan.decompose(&p, choice, 0).unwrap().unwrap();
        assert_eq!(
            index.remaining_cost(&p, &with_enabler, &tdg, None),
            Some(Some(2))
        );
        // Once a cheap primitive is required, losing its only enabler is a dead end.
        let cheap = *without_enabler.tasks().find(|t| t.task == 5).unwrap();
        let dead = without_enabler.decompose(&p, cheap, 2).unwrap().unwrap();
        assert_eq!(index.remaining_cost(&p, &dead, &tdg, None), Some(None));
        assert_eq!(
            index.remaining_cost(&p, &plan, &tdg, Some(Instant::now())),
            None
        );
    }

    #[test]
    fn relaxed_precondition_cycles_need_an_initial_seed() {
        for initial in [vec![], vec![0]] {
            let p = Problem::new(
                vec!["p".into(), "q".into()],
                vec![
                    Action {
                        cost: 0,
                        preconditions: vec![0],
                        add: vec![1],
                        delete: vec![0],
                    },
                    Action {
                        cost: 0,
                        preconditions: vec![1],
                        add: vec![0],
                        delete: vec![1],
                    },
                ],
                (0..3)
                    .map(|i| Task {
                        name: format!("t{i}"),
                        primitive: i < 2,
                    })
                    .collect(),
                vec![Method {
                    name: "cycle".into(),
                    task: 2,
                    subtasks: vec![0, 1],
                    orderings: vec![],
                }],
                initial.clone(),
                vec![0],
                2,
            )
            .unwrap();
            let tdg = Tdg::new(&p);
            assert_eq!(tdg.task_cost(p.root), Some(0));
            assert_eq!(
                Recompute::new(&p, None).unwrap().remaining_cost(
                    &p,
                    &Plan::initial(&p),
                    &tdg,
                    None
                ),
                Some((!initial.is_empty()).then_some(0))
            );
        }
    }

    #[test]
    fn shared_closure_reuse_survives_cancellation_at_every_checkpoint() {
        let p = choice_problem();
        let tdg = Tdg::new(&p);
        let initial = Plan::initial(&p);
        // Every task is a productive descendant; action 0 enables action 2.
        let tasks = (0..p.tasks.len()).collect::<Vec<_>>();
        let missing = vec![0; p.actions.len()];
        let closure = (tasks.as_slice(), missing.as_slice());
        let mut index = Recompute::new(&p, None).unwrap();
        let mut checks = 0;
        assert_eq!(
            index.evaluate_relaxed(&p, &initial, &tdg, closure, || {
                checks += 1;
                false
            }),
            Some(Some(2))
        );
        let root = initial
            .decompose(&p, initial.compound(&p).unwrap(), 4)
            .unwrap()
            .unwrap();
        let no_enabler = root
            .decompose(&p, *root.tasks().find(|t| t.task == 4).unwrap(), 1)
            .unwrap()
            .unwrap();
        for stop in 1..=checks {
            let mut ticks = 0;
            assert!(index
                .evaluate_relaxed(&p, &initial, &tdg, closure, || {
                    ticks += 1;
                    ticks == stop
                })
                .is_none());
            assert_eq!(
                index.remaining_cost(&p, &no_enabler, &tdg, None),
                Some(Some(14))
            );
            assert_eq!(
                index.evaluate_relaxed(&p, &initial, &tdg, closure, || false),
                Some(Some(2))
            );
        }
    }

    #[test]
    fn partial_plan_bound_counts_only_remaining_compound_occurrences() {
        let problem = Problem::new(
            vec![],
            [2, 3]
                .into_iter()
                .map(|cost| Action {
                    cost,
                    preconditions: vec![],
                    add: vec![],
                    delete: vec![],
                })
                .collect(),
            (0..4)
                .map(|id| Task {
                    name: format!("t{id}"),
                    primitive: id < 2,
                })
                .collect(),
            vec![
                Method {
                    name: "pair".into(),
                    task: 2,
                    subtasks: vec![1, 1],
                    orderings: vec![],
                },
                Method {
                    name: "root".into(),
                    task: 3,
                    subtasks: vec![0, 2, 2],
                    orderings: vec![],
                },
            ],
            vec![],
            vec![],
            3,
        )
        .unwrap();
        let tdg = Tdg::new(&problem);
        let mut plan = Plan::initial(&problem);
        for (g, h, method) in [(0, 14, 1), (2, 12, 0), (8, 6, 0)] {
            assert_eq!(plan.cost(), g);
            assert_eq!(tdg.remaining_cost(&problem, &plan), Some(h));
            let parent = plan.compound(&problem).unwrap();
            assert_eq!(
                tdg.replacement_cost(&problem, &plan, parent, method),
                Some(14)
            );
            plan = plan.decompose(&problem, parent, method).unwrap().unwrap();
        }
        assert_eq!(plan.cost(), 14);
        assert_eq!(tdg.remaining_cost(&problem, &plan), Some(0));
    }
}
