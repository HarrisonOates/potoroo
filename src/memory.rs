//! Queue limits and resident-memory accounting.
//!
//! Queue trimming discards the worst entries and makes search incomplete.
//! Exhausting a trimmed queue reports a resource limit, not unsolvability.
//! RSS-based capacity adjustments include a deadband because the allocator
//! may retain freed memory. These limits are disabled by default.

use std::collections::BinaryHeap;

use crate::params::Parameters;

/// Generated nodes between resident-set readings.
const CHECK_INTERVAL: usize = 1024;

/// How far the open list may overflow its capacity before it is trimmed
/// back, as a divisor: trimming a tenth at a time makes the cost amortised
/// constant per generated node.
const SLACK: usize = 10;

/// The resident set must have grown by this fraction of the limit since the
/// capacity was last tightened before it is tightened again, as a divisor.
const DEADBAND: u64 = 50;

/// The trigger state for one search.
#[derive(Debug)]
pub struct OpenListBound {
    max_queued: Option<usize>,
    memory_kb: Option<u64>,
    /// Capacity fixed by the memory bound, once it has fired.
    capacity: Option<usize>,
    /// Generated-node count at which the resident set is next read.
    next_check: usize,
    /// The resident set when the capacity was last tightened, to tell growth
    /// from the plateau that follows a trim.
    tightened_at_kb: u64,
}

impl OpenListBound {
    /// `None` when neither bound is set, so an unbounded search pays nothing.
    pub fn new(params: &Parameters) -> Option<Self> {
        if params.max_queued.is_none() && params.memory_limit_mb.is_none() {
            return None;
        }
        Some(OpenListBound {
            max_queued: params.max_queued,
            memory_kb: params.memory_limit_mb.map(|mb| mb as u64 * 1024),
            capacity: None,
            next_check: CHECK_INTERVAL,
            tightened_at_kb: 0,
        })
    }

    /// How many entries the open lists should be trimmed to, if they should
    /// be trimmed now. `generated` and `queued` are the running totals over
    /// every primary queue of the search.
    pub fn trim_target(&mut self, generated: usize, queued: usize) -> Option<usize> {
        if let Some(limit) = self.memory_kb {
            if generated >= self.next_check {
                self.next_check = generated + CHECK_INTERVAL;
                let rss = resident_set_kb();
                if rss > limit && rss > self.tightened_at_kb + limit / DEADBAND {
                    self.tightened_at_kb = rss;
                    let base = self.capacity.unwrap_or(queued).min(queued);
                    let tightened = (base - base / SLACK).max(1);
                    self.capacity = Some(tightened);
                    return Some(tightened);
                }
            }
        }
        let capacity = match (self.capacity, self.max_queued) {
            (Some(c), Some(m)) => c.min(m),
            (Some(c), None) => c,
            (None, Some(m)) => m,
            (None, None) => return None,
        };
        (queued > capacity + capacity / SLACK).then_some(capacity)
    }
}

/// Keeps the best `keep` entries of a heap and returns how many were dropped.
/// Linear in the heap: a selection rather than a sort, then a rebuild.
pub fn prune_heap<T: Ord>(heap: &mut BinaryHeap<T>, keep: usize) -> usize {
    if heap.len() <= keep {
        return 0;
    }
    let mut entries = std::mem::take(heap).into_vec();
    let dropped = entries.len() - keep;
    if keep > 0 {
        // `Ord` is arranged so the best entry is the greatest; the greatest
        // `keep` entries land in the tail after selecting on `dropped`.
        entries.select_nth_unstable_by(dropped, |a, b| a.cmp(b));
        entries.drain(..dropped);
    } else {
        entries.clear();
    }
    *heap = BinaryHeap::from(entries);
    dropped
}

/// Trims a family of queues to `keep` entries in total, each in proportion to
/// its size, and returns the number of entries dropped. A queue that is not
/// empty keeps at least one entry.
pub fn trim_all<T: Ord>(queues: &mut [BinaryHeap<T>], keep: usize) -> usize {
    let total: usize = queues.iter().map(BinaryHeap::len).sum();
    if total <= keep {
        return 0;
    }
    queues
        .iter_mut()
        .filter(|queue| !queue.is_empty())
        .map(|queue| {
            let share = ((queue.len() as u128 * keep as u128) / total as u128) as usize;
            prune_heap(queue, share.max(1))
        })
        .sum()
}

/// The resident set of this process in kilobytes, from `VmRSS` in
/// `/proc/self/status`; zero where that file does not exist, so a memory
/// bound never fires on a platform that cannot measure it.
pub fn resident_set_kb() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmRSS:"))
                .and_then(|l| l.split_whitespace().nth(1))
                .and_then(|kb| kb.parse().ok())
        })
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prune_keeps_the_greatest_entries() {
        let mut heap: BinaryHeap<u32> = (0..10).collect();
        assert_eq!(prune_heap(&mut heap, 4), 6);
        let mut kept = heap.into_sorted_vec();
        kept.sort_unstable();
        assert_eq!(kept, vec![6, 7, 8, 9]);
    }

    #[test]
    fn prune_is_a_no_op_within_the_bound() {
        let mut heap: BinaryHeap<u32> = (0..3).collect();
        assert_eq!(prune_heap(&mut heap, 3), 0);
        assert_eq!(heap.len(), 3);
        assert_eq!(prune_heap(&mut heap, 0), 3);
        assert!(heap.is_empty());
    }

    #[test]
    fn trimming_is_proportional_and_keeps_one_per_queue() {
        let mut queues = vec![
            BinaryHeap::from(vec![1u32]),
            BinaryHeap::from((0..30).collect::<Vec<u32>>()),
            BinaryHeap::new(),
        ];
        assert_eq!(trim_all(&mut queues, 10), 21);
        assert_eq!(queues[0].len(), 1);
        assert_eq!(queues[1].len(), 9);
        assert_eq!(queues[1].peek(), Some(&29));
        assert!(queues[2].is_empty());
        assert_eq!(trim_all(&mut queues, 10), 0);
    }

    #[test]
    fn count_bound_trims_only_past_the_slack() {
        let params = Parameters {
            max_queued: Some(100),
            ..Parameters::default()
        };
        let mut bound = OpenListBound::new(&params).unwrap();
        assert_eq!(bound.trim_target(5000, 100), None);
        assert_eq!(bound.trim_target(5000, 110), None);
        assert_eq!(bound.trim_target(5000, 111), Some(100));
        assert!(OpenListBound::new(&Parameters::default()).is_none());
    }
}
