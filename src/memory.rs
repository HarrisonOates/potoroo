//! Queue limits and resident-memory accounting.
//!
//! Queue trimming discards the worst entries and makes search incomplete.
//! Exhausting a trimmed queue reports a resource limit, not unsolvability.
//! RSS-based capacity adjustments include a deadband because the allocator
//! may retain freed memory. These limits are disabled by default.

use std::collections::BinaryHeap;
use std::time::Instant;

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

/// The stops a search honours at each expanded node: a wall-clock deadline
/// (`--time-limit`, or one stage's share of it) and a resident-set ceiling
/// (`--stage-mem-mb`).
///
/// Neither drops a node, which is what separates this from [`OpenListBound`]
/// above: the search simply ends where it stands and reports the limit
/// reached, so nothing it would have explored is silently discarded. That
/// makes a stop sound in a way trimming the open list is not, and it is what a
/// restart portfolio needs — a stage that ends has its queues freed for the
/// next one rather than taking the process down with it.
#[derive(Debug)]
pub struct SearchStop {
    deadline: Option<Instant>,
    memory_kb: Option<u64>,
    /// Expansion count at which the resident set is next read.
    next_check: usize,
}

impl SearchStop {
    /// `None` when neither stop is set, so an unbounded search never reads the
    /// clock or `/proc` at all.
    pub fn new(params: &Parameters) -> Option<Self> {
        if params.deadline.is_none() && params.memory_stop_mb.is_none() {
            return None;
        }
        Some(SearchStop {
            deadline: params.deadline,
            memory_kb: params.memory_stop_mb.map(|mb| mb as u64 * 1024),
            // The first reading is a whole interval in, not at the first
            // expansion: a stage always gets its first [`CHECK_INTERVAL`]
            // expansions, whatever the resident set happened to be when it
            // started.
            next_check: CHECK_INTERVAL,
        })
    }

    /// Whether the search should stop now, given how many nodes it has
    /// expanded. The clock is read every call, since a read is cheap beside an
    /// expansion and a late stop is a stage overrunning its share; the
    /// resident set comes from a file in `/proc` and is read only every
    /// [`CHECK_INTERVAL`] expansions.
    pub fn expired(&mut self, expansions: usize) -> bool {
        if let Some(deadline) = self.deadline {
            if Instant::now() >= deadline {
                return true;
            }
        }
        if let Some(limit) = self.memory_kb {
            if expansions >= self.next_check {
                self.next_check = expansions.saturating_add(CHECK_INTERVAL);
                if resident_set_kb() > limit {
                    return true;
                }
            }
        }
        false
    }
}

/// Returns the allocator's free arenas to the operating system.
///
/// Dropping a stage's queues frees them to glibc, not to the kernel: the
/// allocator keeps the arena for the next allocation, so `VmRSS` stays at the
/// stage's high-water mark and the stage that follows reads its predecessor's
/// peak as its own. Against [`SearchStop`]'s resident-set ceiling that is
/// fatal — every later stage stops at its first reading, having expanded
/// nothing — so the restart has to hand the pages back rather than merely drop
/// the references to them.
///
/// `malloc_trim` is what does that, and it has no portable equivalent: on any
/// other target this is a no-op and `--stage-mem-mb` degrades to bounding the
/// high-water mark of the run as a whole rather than of each stage.
#[cfg(target_os = "linux")]
pub fn release_free_memory() {
    extern "C" {
        fn malloc_trim(pad: usize) -> i32;
    }
    // SAFETY: `malloc_trim` takes no pointers and returns only unreachable
    // pages to the kernel, so the allocator stays valid whatever it reports.
    // It is advisory: the return value says whether anything was released.
    unsafe {
        malloc_trim(0);
    }
}

#[cfg(not(target_os = "linux"))]
pub fn release_free_memory() {}

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
    fn no_stop_is_built_without_a_time_or_memory_bound() {
        assert!(SearchStop::new(&Parameters::default()).is_none());
    }

    #[test]
    fn a_passed_deadline_stops_the_search() {
        let params = Parameters {
            deadline: Some(Instant::now() - std::time::Duration::from_secs(1)),
            ..Parameters::default()
        };
        let mut stop = SearchStop::new(&params).expect("a deadline builds a stop");
        assert!(stop.expired(0));

        let params = Parameters {
            deadline: Some(Instant::now() + std::time::Duration::from_secs(3600)),
            ..Parameters::default()
        };
        let mut stop = SearchStop::new(&params).expect("a deadline builds a stop");
        assert!(!stop.expired(0));
    }

    #[test]
    fn a_memory_stop_fires_once_the_resident_set_is_over_the_bound() {
        // One megabyte is below anything this process can be running in, so
        // the reading is over the bound whenever it can be taken at all.
        let params = Parameters {
            memory_stop_mb: Some(1),
            ..Parameters::default()
        };
        let mut stop = SearchStop::new(&params).expect("a memory stop builds a stop");
        // A stage gets its first interval of expansions before the resident
        // set is read at all, so a stage that starts above the bound still
        // searches rather than stopping where it stands.
        assert!(!stop.expired(0));
        assert!(!stop.expired(CHECK_INTERVAL - 1));
        assert_eq!(stop.expired(CHECK_INTERVAL), resident_set_kb() > 1024);
        // The next reading is a whole interval away again.
        assert!(!stop.expired(CHECK_INTERVAL + 1));
    }

    #[test]
    fn releasing_free_memory_is_safe_to_call() {
        // Check that the allocator-trim declaration links on this platform.
        release_free_memory();
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
