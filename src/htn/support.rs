//! Strengthen the structural TDG bound with necessary causal support.
//!
//! Let c(t) be the ordinary minimum decomposition cost, and c_p(t) the minimum
//! cost of a decomposition containing a primitive that adds p. Mark that leaf:
//! its path to the root pays for the leaf and the cheapest unmarked siblings.
//! Thus c_p is a shortest-path distance on reverse task edges weighted by the
//! sibling costs. This works with repeated children, empty methods and cycles.
//!
//! For each open condition lacking an eligible initial/committed supporter,
//! some eligible compound occurrence must supply the achiever. Its additional
//! cost above the structural sum is at least min_t(c_p(t) - c(t)). Add the
//! maximum such increment across open conditions, not their sum: a single
//! action may support several conditions. Focused support restricts candidates
//! for that condition only. Ignore future preconditions, deletes and internal
//! method orderings. This is a lower bound, not an executability test.
//!
//! This extension combines a necessary-support condition with the structural
//! costs of Bercher et al. (IJCAI 2017, Definitions 2–3); it is not their TDG
//! recomputation rule. https://www.ijcai.org/Proceedings/2017/0068.pdf
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, VecDeque};
use std::rc::Rc;
use std::time::Instant;

use super::model::{FactId, Problem, TaskId};
use super::plan::{OpenCondition, Plan};
use super::search::Stats;
use super::tdg::{Tdg, COST_CAP};

// Distances are capped at 2^64. A separate sentinel keeps zero, finite
// overflow and unreachable distinct without Option<u128>'s extra word.
const UNREACHABLE: u128 = u128::MAX;

struct CostTable {
    first_compound: TaskId,
    values: Box<[u128]>,
}

impl CostTable {
    fn get(&self, task: TaskId) -> Option<u128> {
        let index = task.checked_sub(self.first_compound)?;
        let cost = *self.values.get(index)?;
        (cost != UNREACHABLE).then_some(cost)
    }
}

type Costs = Rc<CostTable>;

pub(crate) struct SupportBound {
    parents: Vec<Vec<(TaskId, u128)>>,
    achievers: Vec<Vec<TaskId>>,
    cache: HashMap<FactId, Costs>,
    fifo: VecDeque<FactId>,
    max_entries: usize,
    first_compound: TaskId,
    // Reused per-query scratch. Only touched distances need resetting, even
    // when the previous computation was interrupted by a deadline.
    distances: Vec<u128>,
    touched: Vec<usize>,
    queue: BinaryHeap<Reverse<(u128, TaskId)>>,
    candidates: Vec<TaskId>,
}

impl SupportBound {
    pub(crate) fn new(problem: &Problem, tdg: &Tdg, deadline: Option<Instant>) -> Option<Self> {
        let expired = || deadline.is_some_and(|d| Instant::now() >= d);
        let mut parents = vec![Vec::new(); problem.tasks.len()];
        let mut suffix = Vec::new();
        for (id, method) in problem.methods.iter().enumerate() {
            if expired() {
                return None;
            }
            if tdg.method_cost(id).is_none() {
                continue;
            }
            // Capped prefix/suffix sums avoid subtracting from a saturated sum.
            suffix.clear();
            suffix.resize(method.subtasks.len() + 1, 0u128);
            for (i, &task) in method.subtasks.iter().enumerate().rev() {
                if expired() {
                    return None;
                }
                suffix[i] = (suffix[i + 1] + tdg.task_cost(task).unwrap()).min(COST_CAP);
            }
            let mut prefix = 0;
            for (i, &task) in method.subtasks.iter().enumerate() {
                if expired() {
                    return None;
                }
                parents[task].push((method.task, (prefix + suffix[i + 1]).min(COST_CAP)));
                prefix = (prefix + tdg.task_cost(task).unwrap()).min(COST_CAP);
            }
        }
        for edges in &mut parents {
            if expired() {
                return None;
            }
            // For a marked path, only the cheapest edge to each parent matters.
            edges.sort_unstable();
            edges.dedup_by_key(|edge| edge.0);
        }
        let mut achievers = vec![Vec::new(); problem.facts.len()];
        for (task, action) in problem.actions.iter().enumerate() {
            if expired() {
                return None;
            }
            for &fact in &action.add {
                achievers[fact].push(task);
            }
        }
        // Queries only concern future compound supporters. Primitive costs
        // are seeds, and committed primitive supporters have already paid g.
        // Bound cache payload to 8 MiB and 64 facts, excluding reusable scratch
        // and small container overhead. Oversized tables are not cached.
        let first_compound = problem.actions.len();
        let compounds = problem.tasks.len() - first_compound;
        let bytes = compounds.saturating_mul(std::mem::size_of::<u128>());
        let max_entries = ((8 * 1024 * 1024) / bytes.max(1)).min(64);
        Some(Self {
            parents,
            achievers,
            cache: HashMap::new(),
            fifo: VecDeque::new(),
            max_entries,
            first_compound,
            distances: vec![UNREACHABLE; compounds],
            touched: Vec::new(),
            queue: BinaryHeap::new(),
            candidates: Vec::new(),
        })
    }

    fn costs(
        &mut self,
        problem: &Problem,
        fact: FactId,
        deadline: Option<Instant>,
        stats: &mut Stats,
    ) -> Option<Costs> {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        if let Some(costs) = self.cache.get(&fact) {
            stats.support_cache_hits += 1;
            return Some(Rc::clone(costs));
        }
        stats.support_tables += 1;
        for index in self.touched.drain(..) {
            self.distances[index] = UNREACHABLE;
        }
        self.queue.clear();
        // Seed compound parents directly. Primitive tasks cannot be method
        // heads, so putting them in the queue/table would do redundant work.
        for &primitive in &self.achievers[fact] {
            if deadline.is_some_and(|d| Instant::now() >= d) {
                return None;
            }
            let cost = problem.actions[primitive].cost as u128;
            for &(parent, siblings) in &self.parents[primitive] {
                if deadline.is_some_and(|d| Instant::now() >= d) {
                    return None;
                }
                relax(
                    &mut self.distances,
                    &mut self.touched,
                    &mut self.queue,
                    self.first_compound,
                    parent,
                    (cost + siblings).min(COST_CAP),
                );
            }
        }
        while let Some(Reverse((cost, task))) = self.queue.pop() {
            if deadline.is_some_and(|d| Instant::now() >= d) {
                return None;
            }
            if self.distances[task - self.first_compound] != cost {
                continue;
            }
            for &(parent, siblings) in &self.parents[task] {
                if deadline.is_some_and(|d| Instant::now() >= d) {
                    return None;
                }
                let candidate = (cost + siblings).min(COST_CAP);
                relax(
                    &mut self.distances,
                    &mut self.touched,
                    &mut self.queue,
                    self.first_compound,
                    parent,
                    candidate,
                );
            }
        }
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        let costs = Rc::new(CostTable {
            first_compound: self.first_compound,
            values: self.distances.clone().into_boxed_slice(),
        });
        if self.max_entries > 0 {
            if self.cache.len() == self.max_entries {
                self.cache.remove(&self.fifo.pop_front().unwrap());
            }
            self.cache.insert(fact, Rc::clone(&costs));
            self.fifo.push_back(fact);
        }
        Some(costs)
    }

    /// The outer None is cancellation; the inner None proves missing support.
    pub(crate) fn remaining_cost(
        &mut self,
        problem: &Problem,
        plan: &Plan,
        tdg: &Tdg,
        deadline: Option<Instant>,
        stats: &mut Stats,
    ) -> Option<Option<u128>> {
        stats.support_evaluated += 1;
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        let mut structural = 0;
        for task in plan.tasks().filter(|t| !problem.tasks[t.task].primitive) {
            if deadline.is_some_and(|d| Instant::now() >= d) {
                return None;
            }
            let Some(cost) = tdg.task_cost(task.task) else {
                return Some(None);
            };
            structural = (structural + cost).min(COST_CAP);
        }
        if structural == COST_CAP {
            return Some(Some(COST_CAP));
        }
        let mut extra = 0;
        for &open in plan.open_conditions() {
            let Some(delta) = self.condition_cost(problem, plan, tdg, open, deadline, stats)?
            else {
                return Some(None);
            };
            extra = extra.max(delta);
        }
        Some(Some((structural + extra).min(COST_CAP)))
    }

    fn condition_cost(
        &mut self,
        problem: &Problem,
        plan: &Plan,
        tdg: &Tdg,
        open: OpenCondition,
        deadline: Option<Instant>,
        stats: &mut Stats,
    ) -> Option<Option<u128>> {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        let focus = plan
            .support_focus
            .as_ref()
            .filter(|focus| focus.open == open);
        if focus.is_none() && problem.initial.binary_search(&open.fact).is_ok() {
            return Some(Some(0));
        }
        self.candidates.clear();
        for task in plan.tasks() {
            if deadline.is_some_and(|d| Instant::now() >= d) {
                return None;
            }
            if focus.is_some_and(|f| !f.candidates.contains(task))
                || task.id == open.consumer
                || plan.ordered_before(open.consumer, task.id)
            {
                continue;
            }
            if let Some(action) = problem.actions.get(task.task) {
                if action.add.binary_search(&open.fact).is_ok() {
                    return Some(Some(0)); // Already paid in g.
                }
            } else if tdg.may_add(task.task, open.fact) {
                self.candidates.push(task.task);
            }
        }
        if self.candidates.is_empty() {
            return Some(None);
        }
        let costs = self.costs(problem, open.fact, deadline, stats)?;
        let mut best = None;
        for &task in &self.candidates {
            if deadline.is_some_and(|d| Instant::now() >= d) {
                return None;
            }
            if let Some(cost) = costs.get(task) {
                // structural < CAP ensures the subtracted cost is exact. If
                // c_p saturated, CAP - c is still a valid lower bound.
                let delta = cost - tdg.task_cost(task).unwrap();
                if delta == 0 {
                    return Some(Some(0)); // No smaller increment is possible.
                }
                best = Some(best.map_or(delta, |old: u128| old.min(delta)));
            }
        }
        Some(best)
    }
}

fn relax(
    distances: &mut [u128],
    touched: &mut Vec<usize>,
    queue: &mut BinaryHeap<Reverse<(u128, TaskId)>>,
    first_compound: TaskId,
    task: TaskId,
    cost: u128,
) {
    let index = task - first_compound;
    if cost < distances[index] {
        if distances[index] == UNREACHABLE {
            touched.push(index);
        }
        distances[index] = cost;
        queue.push(Reverse((cost, task)));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::htn::model::{Action, Method, Task};
    use crate::htn::refine::Refinement;
    use crate::plan::GOAL_ID;

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
        methods: &[(usize, &[usize])],
        initial: &[usize],
        goal: &[usize],
    ) -> Problem {
        let tasks = (0..actions.len() + compounds)
            .map(|i| Task {
                name: format!("t{i}"),
                primitive: i < actions.len(),
            })
            .collect::<Vec<_>>();
        let root = tasks.len() - 1;
        Problem::new(
            vec!["p".into(), "q".into()],
            actions,
            tasks,
            methods
                .iter()
                .enumerate()
                .map(|(i, &(task, subtasks))| Method {
                    name: format!("m{i}"),
                    task,
                    subtasks: subtasks.into(),
                    orderings: vec![],
                })
                .collect(),
            initial.into(),
            goal.into(),
            root,
        )
        .unwrap()
    }

    #[test]
    fn marked_leaf_costs_count_siblings_and_handle_cycles_empty_and_unproductive_methods() {
        let p = problem(
            vec![action(2, &[], &[0]), action(3, &[], &[1])],
            5,
            &[
                (2, &[2]),
                (2, &[]),
                (2, &[0, 0]),
                (2, &[3]),
                (3, &[2]),
                (3, &[1]),
                (4, &[4]),
                (4, &[0, 4]),
                (5, &[2, 2]),
                (6, &[5, 1]),
            ],
            &[],
            &[],
        );
        let tdg = Tdg::new(&p);
        let mut bound = SupportBound::new(&p, &tdg, None).unwrap();
        let mut stats = Stats::default();
        let costs = bound.costs(&p, 0, None, &mut stats).unwrap();
        assert_eq!(
            (2..7).map(|task| costs.get(task)).collect::<Vec<_>>(),
            [Some(4), Some(4), None, Some(4), Some(7)]
        );
        let costs = bound.costs(&p, 1, None, &mut stats).unwrap();
        assert_eq!(
            (2..7).map(|task| costs.get(task)).collect::<Vec<_>>(),
            [Some(3), Some(3), None, Some(3), Some(3)]
        );
        assert_eq!(tdg.task_cost(6), Some(3));
        // All tasks are in finite decompositions except the recursion-only 4.
        for fact in 0..2 {
            let costs = bound.costs(&p, fact, None, &mut stats).unwrap();
            for task in p.actions.len()..p.tasks.len() {
                let cost = costs.get(task);
                assert_eq!(cost.is_some(), tdg.may_add(task, fact));
                if let Some(cost) = cost {
                    assert!(cost >= tdg.task_cost(task).unwrap());
                }
            }
        }
    }

    #[test]
    fn support_focus_applies_to_its_condition_only_and_current_support_is_free() {
        let p = problem(
            vec![action(2, &[], &[0]), action(7, &[], &[0])],
            3,
            &[(2, &[3]), (3, &[]), (3, &[1]), (4, &[0, 2])],
            &[0, 1],
            &[0, 1],
        );
        let tdg = Tdg::new(&p);
        let mut bound = SupportBound::new(&p, &tdg, None).unwrap();
        let mut stats = Stats::default();
        let initial = Plan::initial(&p);
        let plan = initial
            .decompose(&p, *initial.tasks().next().unwrap(), 3)
            .unwrap()
            .unwrap();
        assert_eq!(
            bound.remaining_cost(&p, &plan, &tdg, None, &mut stats),
            Some(Some(0))
        );
        let parent = *plan.tasks().find(|t| t.task == 2).unwrap();
        let plan = Refinement::Decompose {
            parent,
            method: 0,
            for_support: true,
            focus: Some(OpenCondition {
                consumer: GOAL_ID,
                fact: 0,
            }),
        }
        .apply(&p, &plan)
        .unwrap()
        .unwrap();
        // p's initial and committed supporters are outside the selected subtree.
        // The unrelated goal q must still be allowed to use the initial state.
        assert_eq!(
            bound.remaining_cost(&p, &plan, &tdg, None, &mut stats),
            Some(Some(7))
        );
        let parent = *plan.tasks().find(|t| t.task == 3).unwrap();
        let plan = Refinement::Decompose {
            parent,
            method: 2,
            for_support: true,
            focus: Some(OpenCondition {
                consumer: GOAL_ID,
                fact: 0,
            }),
        }
        .apply(&p, &plan)
        .unwrap()
        .unwrap();
        assert_eq!(plan.cost(), 9);
        assert_eq!(
            bound.remaining_cost(&p, &plan, &tdg, None, &mut stats),
            Some(Some(0))
        );
    }

    #[test]
    fn self_support_and_future_support_after_consumer_are_excluded() {
        let p = problem(
            vec![action(2, &[0], &[0]), action(7, &[], &[0])],
            2,
            &[(2, &[]), (2, &[1]), (3, &[0, 2])],
            &[],
            &[],
        );
        let tdg = Tdg::new(&p);
        let mut bound = SupportBound::new(&p, &tdg, None).unwrap();
        let mut stats = Stats::default();
        let initial = Plan::initial(&p);
        let plan = initial
            .decompose(&p, *initial.tasks().next().unwrap(), 2)
            .unwrap()
            .unwrap();
        assert_eq!(
            bound.remaining_cost(&p, &plan, &tdg, None, &mut stats),
            Some(Some(7))
        );
        let consumer = plan.tasks().find(|t| t.task == 0).unwrap().id;
        let compound = plan.tasks().find(|t| t.task == 2).unwrap().id;
        let plan = plan.order(consumer, compound).unwrap();
        assert_eq!(
            bound.remaining_cost(&p, &plan, &tdg, None, &mut stats),
            Some(None)
        );
    }

    #[test]
    fn capped_costs_cache_eviction_and_cancellation_keep_their_meanings() {
        let p = problem(
            vec![
                action(u64::MAX, &[], &[0]),
                action(u64::MAX, &[], &[]),
                action(0, &[], &[1]),
            ],
            2,
            &[(3, &[0, 1]), (4, &[3, 2]), (4, &[])],
            &[],
            &[0, 1],
        );
        let tdg = Tdg::new(&p);
        let mut bound = SupportBound::new(&p, &tdg, None).unwrap();
        bound.max_entries = 1;
        let mut stats = Stats::default();
        assert_eq!(
            bound.costs(&p, 0, None, &mut stats).unwrap().get(4),
            Some(COST_CAP)
        );
        assert_eq!(
            bound.costs(&p, 0, None, &mut stats).unwrap().get(4),
            Some(COST_CAP)
        );
        assert_eq!(stats.support_tables, 1);
        assert_eq!(stats.support_cache_hits, 1);
        assert_eq!(
            bound.costs(&p, 1, None, &mut stats).unwrap().get(4),
            Some(COST_CAP)
        );
        assert!(!bound.cache.contains_key(&0));
        assert_eq!(
            bound.costs(&p, 0, None, &mut stats).unwrap().get(4),
            Some(COST_CAP)
        );
        assert_eq!(stats.support_tables, 3);
        assert_eq!(
            bound.remaining_cost(&p, &Plan::initial(&p), &tdg, None, &mut stats),
            Some(Some(COST_CAP))
        );
        let expired = Some(Instant::now());
        assert!(SupportBound::new(&p, &tdg, expired).is_none());
        assert!(bound.costs(&p, 1, expired, &mut stats).is_none());
        assert!(!bound.cache.contains_key(&1));
        assert!(bound
            .remaining_cost(&p, &Plan::initial(&p), &tdg, expired, &mut stats)
            .is_none());
        bound.cache.clear();
        bound.fifo.clear();
        bound.max_entries = 0;
        assert_eq!(
            bound.costs(&p, 0, None, &mut stats).unwrap().get(4),
            Some(COST_CAP)
        );
        assert!(bound.cache.is_empty());
    }

    // Independent tree recurrence: repeatedly combine complete child trees,
    // requiring one child to contain an achiever for the marked variant.
    // This does not use TDG costs, reverse edges, or shortest paths.
    fn tree_costs(problem: &Problem, fact: FactId) -> Vec<Option<u128>> {
        let mut plain = vec![None; problem.tasks.len()];
        let mut marked = plain.clone();
        for (task, action) in problem.actions.iter().enumerate() {
            plain[task] = Some(action.cost as u128);
            if action.add.contains(&fact) {
                marked[task] = plain[task];
            }
        }
        loop {
            let before = (plain.clone(), marked.clone());
            for method in &problem.methods {
                let cost = method.subtasks.iter().try_fold(0u128, |sum, &child| {
                    Some((sum + plain[child]?).min(COST_CAP))
                });
                if let Some(cost) = cost {
                    plain[method.task] = Some(plain[method.task].map_or(cost, |old| old.min(cost)));
                }
                for chosen in 0..method.subtasks.len() {
                    let cost = method.subtasks.iter().enumerate().try_fold(
                        0u128,
                        |sum, (index, &child)| {
                            let child_cost = if index == chosen {
                                marked[child]
                            } else {
                                plain[child]
                            };
                            Some((sum + child_cost?).min(COST_CAP))
                        },
                    );
                    if let Some(cost) = cost {
                        marked[method.task] =
                            Some(marked[method.task].map_or(cost, |old| old.min(cost)));
                    }
                }
            }
            if before == (plain.clone(), marked.clone()) {
                return marked;
            }
        }
    }

    #[test]
    fn compact_tables_match_tree_recurrence_with_and_without_caching() {
        let mut seed = 0x51a7_395b_193du64;
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed as usize
        };
        for case in 0..256 {
            let actions = (0..3)
                .map(|_| {
                    let cost = [0, 1, 7, u64::MAX][next() % 4];
                    let mask = next() % 4;
                    let add = (0..2)
                        .filter(|fact| mask & (1 << fact) != 0)
                        .collect::<Vec<_>>();
                    action(cost, &[], &add)
                })
                .collect();
            let methods = (0..12)
                .map(|_| {
                    let head = 3 + next() % 4;
                    let children = (0..next() % 5).map(|_| next() % 7).collect::<Vec<_>>();
                    (head, children)
                })
                .collect::<Vec<_>>();
            let methods = methods
                .iter()
                .map(|(head, children)| (*head, children.as_slice()))
                .collect::<Vec<_>>();
            let p = problem(actions, 4, &methods, &[], &[]);
            let tdg = Tdg::new(&p);
            let expected = [tree_costs(&p, 0), tree_costs(&p, 1)];
            for capacity in [0, 1, 64] {
                let mut bound = SupportBound::new(&p, &tdg, None).unwrap();
                bound.max_entries = capacity;
                for fact in [0, 1, 0, 1] {
                    let costs = bound.costs(&p, fact, None, &mut Stats::default()).unwrap();
                    for (task, &expected_cost) in expected[fact].iter().enumerate().skip(3) {
                        assert_eq!(
                            costs.get(task),
                            expected_cost,
                            "case {case}, cache {capacity}, fact {fact}, task {task}"
                        );
                    }
                    assert_eq!(costs.values.len(), 4);
                }
            }
        }
    }

    #[test]
    fn scratch_from_an_interrupted_query_cannot_leak_into_the_next_table() {
        let p = problem(
            vec![action(0, &[], &[0]), action(7, &[], &[1])],
            2,
            &[(2, &[0]), (3, &[1])],
            &[],
            &[],
        );
        let tdg = Tdg::new(&p);
        let mut bound = SupportBound::new(&p, &tdg, None).unwrap();
        let mut stats = Stats::default();
        // Reproduce a deadline interruption after relaxing one compound,
        // leaving both a reached distance and an unprocessed heap entry.
        relax(
            &mut bound.distances,
            &mut bound.touched,
            &mut bound.queue,
            2,
            2,
            0,
        );
        assert!(bound
            .costs(&p, 0, Some(Instant::now()), &mut stats)
            .is_none());
        assert!(bound.cache.is_empty());
        let q = bound.costs(&p, 1, None, &mut stats).unwrap();
        assert_eq!(q.get(2), None);
        assert_eq!(q.get(3), Some(7));
        let p = bound.costs(&p, 0, None, &mut stats).unwrap();
        assert_eq!(p.get(2), Some(0));
        assert_eq!(p.get(3), None);
        // Cached snapshots must survive subsequent changes to scratch.
        assert_eq!(q.get(2), None);
        assert_eq!(q.get(3), Some(7));
    }

    #[test]
    fn primitive_tasks_do_not_consume_table_payload_or_cache_capacity() {
        let p = problem(
            vec![action(1, &[], &[0]); 8192],
            1,
            &[(8192, &[0])],
            &[],
            &[],
        );
        let tdg = Tdg::new(&p);
        let mut bound = SupportBound::new(&p, &tdg, None).unwrap();
        assert_eq!(bound.max_entries, 64);
        let costs = bound.costs(&p, 0, None, &mut Stats::default()).unwrap();
        assert_eq!(costs.values.len(), 1);
        assert_eq!(costs.get(8192), Some(1));
        assert_eq!(costs.get(0), None);

        let p = problem(vec![action(1, &[], &[0])], 0, &[], &[], &[]);
        let mut bound = SupportBound::new(&p, &Tdg::new(&p), None).unwrap();
        assert!(bound
            .costs(&p, 0, None, &mut Stats::default())
            .unwrap()
            .values
            .is_empty());
    }
}
