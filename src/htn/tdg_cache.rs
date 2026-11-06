//! Memoize the relaxed bound by active task multiset, scoped to one search.
//!
//! The relaxation ignores occurrence IDs, ordering, causal links and history.
//! It depends only on the problem and active task types, including multiplicity.
//! All committed primitives remain active in plan-space search. Hence this key
//! also captures which primitive actions can enable the remaining compounds.
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

use super::model::TaskId;
use super::plan::Plan;

pub(crate) struct BoundCache {
    values: HashMap<Rc<[TaskId]>, Option<u128>>,
    fifo: VecDeque<Rc<[TaskId]>>,
    task_ids: usize,
    max_entries: usize,
    max_task_ids: usize,
}

impl Default for BoundCache {
    fn default() -> Self {
        Self::new(4096, (4 * 1024 * 1024) / std::mem::size_of::<TaskId>())
    }
}

impl BoundCache {
    // At most 4096 entries and 4 MiB of task-ID payload, plus bounded container
    // overhead. FIFO makes eviction deterministic without per-hit allocations.
    fn new(max_entries: usize, max_task_ids: usize) -> Self {
        Self {
            values: HashMap::new(),
            fifo: VecDeque::new(),
            task_ids: 0,
            max_entries,
            max_task_ids,
        }
    }

    pub(crate) fn key(plan: &Plan) -> Vec<TaskId> {
        let mut tasks: Vec<_> = plan.tasks().map(|t| t.task).collect();
        tasks.sort_unstable();
        tasks
    }

    // A cached None proves a dead end; outer None means cache miss.
    pub(crate) fn get(&self, key: &[TaskId]) -> Option<Option<u128>> {
        self.values.get(key).copied()
    }

    pub(crate) fn insert(&mut self, key: Vec<TaskId>, cost: Option<u128>) {
        if self.max_entries == 0
            || key.len() > self.max_task_ids
            || self.values.contains_key(key.as_slice())
        {
            return;
        }
        while self.values.len() >= self.max_entries || self.task_ids + key.len() > self.max_task_ids
        {
            let old = self
                .fifo
                .pop_front()
                .expect("cache accounting matches entries");
            self.task_ids -= old.len();
            self.values.remove(&old);
        }
        self.task_ids += key.len();
        let key: Rc<[TaskId]> = key.into();
        self.fifo.push_back(Rc::clone(&key));
        self.values.insert(key, cost);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cache_distinguishes_repetitions_dead_ends_and_zero_costs() {
        let mut cache = BoundCache::default();
        cache.insert(vec![1], Some(7));
        cache.insert(vec![1, 1], Some(14));
        cache.insert(vec![2], None);
        cache.insert(vec![], Some(0));
        assert_eq!(cache.get(&[1]), Some(Some(7)));
        assert_eq!(cache.get(&[1, 1]), Some(Some(14)));
        assert_eq!(cache.get(&[2]), Some(None));
        assert_eq!(cache.get(&[]), Some(Some(0)));
        assert_eq!(cache.get(&[3]), None);
    }

    #[test]
    fn cache_limits_both_entry_count_and_task_payload() {
        let mut cache = BoundCache::new(2, 4);
        cache.insert(vec![1], Some(1));
        cache.insert(vec![2], Some(2));
        cache.insert(vec![3], Some(3));
        assert_eq!(cache.get(&[1]), None);
        assert_eq!(cache.get(&[2]), Some(Some(2)));
        cache.insert(vec![4, 4, 4, 4], None);
        assert_eq!(cache.values.len(), 1);
        assert_eq!(cache.task_ids, 4);
        cache.insert(vec![5; 5], Some(5));
        assert_eq!(cache.get(&[5; 5]), None);
        assert_eq!(cache.get(&[4; 4]), Some(None));
        // Reinserting a cached key must not duplicate FIFO entries or accounting.
        cache.insert(vec![4; 4], None);
        assert_eq!(cache.fifo.len(), 1);
        assert_eq!(cache.task_ids, 4);
        cache.insert(vec![], Some(0));
        cache.insert(vec![6], Some(6));
        assert_eq!(cache.get(&[4; 4]), None);
        assert_eq!(cache.get(&[]), Some(Some(0)));
    }
}
