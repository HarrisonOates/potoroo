//! Step ordering constraints.
//!
//! A [`BinaryOrderings`] is the transitive closure of a strict partial order
//! over real step ids (1-based). Step 0 (the initial step) precedes everything
//! and the goal step ([`GOAL_ID`]) follows everything; those two are handled
//! specially rather than stored in the matrix.

use std::collections::HashMap;
use std::ops::{Index, IndexMut};
use std::rc::Rc;

use crate::plan::GOAL_ID;

/// A step time point. For non-durative planning only the start/end distinction
/// is carried; [`BinaryOrderings`] ignores it (it reasons purely about step ids).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepTime {
    AtStart,
    AtEnd,
}

/// An ordering constraint `before_id < after_id`.
#[derive(Debug, Clone, Copy)]
pub struct Ordering {
    pub before_id: usize,
    pub before_time: StepTime,
    pub after_id: usize,
    pub after_time: StepTime,
}

impl Ordering {
    pub fn new(
        before_id: usize,
        before_time: StepTime,
        after_id: usize,
        after_time: StepTime,
    ) -> Self {
        Ordering {
            before_id,
            before_time,
            after_id,
            after_time,
        }
    }
}

/// One row of the transitive-closure matrix, bit-packed into `u64` words.
///
/// Rows grow lazily: `get` past the end reads as `false`, and only `set` and
/// `or_with` extend the word vector. A step that never gains a high-numbered
/// successor therefore never pays for one, and adding a step to the plan does
/// not have to widen every existing row (which would clone them all and break
/// the sharing with the parent plan).
#[derive(Debug, Clone, Default)]
struct Row {
    words: Vec<u64>,
}

impl Row {
    #[inline]
    fn get(&self, i: usize) -> bool {
        match self.words.get(i >> 6) {
            Some(w) => (w >> (i & 63)) & 1 != 0,
            None => false,
        }
    }

    #[inline]
    fn set(&mut self, i: usize) {
        let w = i >> 6;
        if w >= self.words.len() {
            self.words.resize(w + 1, 0);
        }
        self.words[w] |= 1u64 << (i & 63);
    }

    /// True iff every bit of `other` is already set here, so an `or_with` would
    /// be a no-op. Checked before `Rc::make_mut` so untouched rows stay shared.
    #[inline]
    fn contains_all(&self, other: &Row) -> bool {
        for (k, &ow) in other.words.iter().enumerate() {
            if ow == 0 {
                continue;
            }
            match self.words.get(k) {
                Some(&sw) if sw & ow == ow => {}
                _ => return false,
            }
        }
        true
    }

    #[inline]
    fn or_with(&mut self, other: &Row) {
        if other.words.len() > self.words.len() {
            self.words.resize(other.words.len(), 0);
        }
        for (sw, &ow) in self.words.iter_mut().zip(other.words.iter()) {
            *sw |= ow;
        }
    }
}

/// Keep short plans flat; share blocks of row pointers once plans grow. The
/// rows themselves were already shared, but cloning the entire pointer table
/// for every child dominated retained memory on long plans (e.g. miconic).
/// A refinement now copies the directory and only the blocks it changes.
const ROW_BLOCK_SIZE: usize = 32;

#[derive(Debug, Clone)]
enum RowTable {
    Flat(Vec<Rc<Row>>),
    Blocked(Vec<Rc<Vec<Rc<Row>>>>),
}

impl Default for RowTable {
    fn default() -> Self {
        Self::Flat(Vec::new())
    }
}

impl RowTable {
    #[inline]
    fn get(&self, index: usize) -> Option<&Rc<Row>> {
        match self {
            Self::Flat(rows) => rows.get(index),
            Self::Blocked(blocks) => blocks
                .get(index / ROW_BLOCK_SIZE)?
                .get(index % ROW_BLOCK_SIZE),
        }
    }

    /// Extend a shared table without reallocating a freshly cloned tail.
    /// All blocks except the last are full; only that last block can grow.
    fn expanded(&self, new_len: usize) -> Self {
        let empty = Rc::new(Row::default());
        if let Self::Flat(rows) = self {
            if new_len <= ROW_BLOCK_SIZE {
                let mut next = Vec::with_capacity(new_len);
                next.extend(rows.iter().cloned());
                next.resize(new_len, empty);
                return Self::Flat(next);
            }
        }

        let mut blocks = Vec::with_capacity(new_len.div_ceil(ROW_BLOCK_SIZE));
        match self {
            Self::Flat(rows) if !rows.is_empty() => blocks.push(Rc::new(rows.clone())),
            Self::Flat(_) => {}
            Self::Blocked(old) => blocks.extend(old.iter().cloned()),
        }
        if let Some(last) = blocks.last() {
            let tail_len = (new_len - (blocks.len() - 1) * ROW_BLOCK_SIZE).min(ROW_BLOCK_SIZE);
            if last.len() < tail_len {
                let mut tail = Vec::with_capacity(tail_len);
                tail.extend(last.iter().cloned());
                tail.resize(tail_len, empty.clone());
                *blocks.last_mut().unwrap() = Rc::new(tail);
            }
        }
        while blocks.len() * ROW_BLOCK_SIZE < new_len {
            let len = (new_len - blocks.len() * ROW_BLOCK_SIZE).min(ROW_BLOCK_SIZE);
            blocks.push(Rc::new(vec![empty.clone(); len]));
        }
        Self::Blocked(blocks)
    }
}

impl Index<usize> for RowTable {
    type Output = Rc<Row>;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("step has an ordering row")
    }
}

impl IndexMut<usize> for RowTable {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        match self {
            Self::Flat(rows) => &mut rows[index],
            Self::Blocked(blocks) => {
                &mut Rc::make_mut(&mut blocks[index / ROW_BLOCK_SIZE])[index % ROW_BLOCK_SIZE]
            }
        }
    }
}

/// Transitive-closure boolean order over real step ids.
///
/// Successor-major: `succ[k - 1]` is the bit set of steps that step `k` is
/// ordered before, so `ordered_before(k, l)` is one bit test and propagating a
/// new constraint is a word-wise OR of two rows rather than a bit-at-a-time
/// double loop (`fill_transitive`).
///
/// Rows are shared across plans via `Rc` with copy-on-write at row granularity
/// (`Rc::make_mut`), so a refinement deep-copies only the rows it actually
/// changes and sibling plans share the rest.
#[derive(Debug, Clone, Default)]
pub struct BinaryOrderings {
    /// Highest real step id seen (0 means only init/goal). Real steps are
    /// `1..=high_id`.
    high_id: usize,
    /// Per-step successor rows; there are `high_id` entries.
    succ: RowTable,
}

impl BinaryOrderings {
    pub fn new() -> Self {
        BinaryOrderings::default()
    }

    /// Returns true iff real step `id1` is ordered before real step `id2`.
    /// Both ids must be real steps in `1..=high_id` (callers handle init/goal
    /// specially first).
    #[inline]
    fn ordered_before(&self, id1: usize, id2: usize) -> bool {
        if id1 == id2 {
            return false;
        }
        match self.succ.get(id1 - 1) {
            Some(row) => row.get(id2 - 1),
            None => false,
        }
    }

    pub fn possibly_before(&self, id1: usize, _t1: StepTime, id2: usize, _t2: StepTime) -> bool {
        if id1 == id2 {
            false
        } else if id1 == 0 || id2 == GOAL_ID {
            true
        } else if id1 == GOAL_ID || id2 == 0 {
            false
        } else {
            !self.ordered_before(id2, id1)
        }
    }

    // Two arms return the same value, mirroring VHPOP's `possibly_after`
    // (orderings.cc) case-for-case; keeping the shape makes the correspondence
    // checkable against the reference implementation.
    #[allow(clippy::if_same_then_else)]
    pub fn possibly_after(&self, id1: usize, _t1: StepTime, id2: usize, _t2: StepTime) -> bool {
        if id1 == id2 {
            false
        } else if id1 == 0 || id2 == GOAL_ID {
            false
        } else if id1 == GOAL_ID || id2 == 0 {
            true
        } else {
            !self.ordered_before(id1, id2)
        }
    }

    pub fn possibly_not_before(&self, id1: usize, t1: StepTime, id2: usize, t2: StepTime) -> bool {
        self.possibly_after(id1, t1, id2, t2)
    }

    pub fn possibly_not_after(&self, id1: usize, t1: StepTime, id2: usize, t2: StepTime) -> bool {
        self.possibly_before(id1, t1, id2, t2)
    }

    /// Returns the ordering collection with `new_ordering` added, or a clone of
    /// `self` when the ordering is already implied or trivially redundant.
    /// Returns `None` if the ordering is inconsistent (would create a cycle).
    pub fn refine(self: &Rc<Self>, new_ordering: Ordering) -> Option<Rc<BinaryOrderings>> {
        let before = new_ordering.before_id;
        let after = new_ordering.after_id;

        if before == after || before == GOAL_ID || after == 0 {
            return None;
        }
        if before == 0 || after == GOAL_ID || self.ordered_before(before, after) {
            return Some(self.clone());
        }
        if self.ordered_before(after, before) {
            return None;
        }

        let mut orderings = (**self).clone();
        orderings.fill_transitive(new_ordering);
        Some(Rc::new(orderings))
    }

    /// Returns the ordering collection accounting for a freshly added step plus
    /// the new ordering.
    pub fn refine_with_step(
        self: &Rc<Self>,
        new_ordering: Ordering,
        new_step_id: usize,
    ) -> Option<Rc<BinaryOrderings>> {
        if new_step_id != 0 && new_step_id != GOAL_ID {
            let mut orderings = if new_step_id > self.high_id {
                BinaryOrderings {
                    high_id: new_step_id,
                    succ: self.succ.expanded(new_step_id),
                }
            } else {
                (**self).clone()
            };
            if new_ordering.before_id != 0 && new_ordering.after_id != GOAL_ID {
                orderings.fill_transitive(new_ordering);
            }
            Some(Rc::new(orderings))
        } else {
            Some(self.clone())
        }
    }

    /// Marks `id1` before `id2`. The affected row is copied on first write via
    /// `Rc::make_mut`, giving copy-on-write behaviour.
    #[cfg(test)]
    fn set_before(&mut self, id1: usize, id2: usize) {
        if id1 != id2 {
            Rc::make_mut(&mut self.succ[id1 - 1]).set(id2 - 1);
        }
    }

    /// Updates the transitive closure given a new ordering constraint `i < j`.
    ///
    /// Every step at or before `i` gains every step at or after `j` as a
    /// successor. Both sides are bit sets, so the inner update is a word-wise
    /// OR: O(n^2 / 64) rather than the O(n^2) bit-at-a-time double loop this
    /// replaces.
    fn fill_transitive(&mut self, ordering: Ordering) {
        let i = ordering.before_id;
        let j = ordering.after_id;
        if i == j || self.ordered_before(i, j) {
            return;
        }
        let n = self.high_id;
        if i > n || j > n {
            return;
        }

        // Successors gained by everything at or before `i`: {j} + succ(j).
        let mut gained = (*self.succ[j - 1]).clone();
        gained.set(j - 1);

        for k in 1..=n {
            if k != i && !self.ordered_before(k, i) {
                continue;
            }
            // Leave rows that already imply the new edges shared with the parent.
            if self.succ[k - 1].contains_all(&gained) {
                continue;
            }
            Rc::make_mut(&mut self.succ[k - 1]).or_with(&gained);
        }
    }

    /// Fills `start_times` with each real step's integer start time and returns
    /// the makespan. The start time of a step is one plus the longest chain of
    /// predecessors; the initial step is not scheduled (it is implicitly at
    /// time 0).
    pub fn schedule(&self) -> (HashMap<usize, f32>, f32) {
        // In a transitive closure every predecessor has strictly more
        // successors than its descendant. Sorting by that count therefore
        // gives a topological order without recursion on the plan's depth.
        let mut order: Vec<_> = (1..=self.high_id).collect();
        order.sort_by_cached_key(|&id| {
            std::cmp::Reverse(
                self.succ[id - 1]
                    .words
                    .iter()
                    .map(|w| w.count_ones() as usize)
                    .sum::<usize>(),
            )
        });
        let mut distances = vec![1.0f32; self.high_id];
        let mut max_dist = 0.0f32;
        for &id in &order {
            let distance = distances[id - 1];
            max_dist = max_dist.max(distance);
            for next in 1..=self.high_id {
                if self.ordered_before(id, next) {
                    distances[next - 1] = distances[next - 1].max(distance + 1.0);
                }
            }
        }
        ((1..=self.high_id).zip(distances).collect(), max_dist)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refine_rejects_a_reverse_ordering() {
        let orderings = Rc::new(BinaryOrderings::new())
            .refine_with_step(
                Ordering::new(1, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                1,
            )
            .unwrap()
            .refine_with_step(Ordering::new(1, StepTime::AtEnd, 2, StepTime::AtStart), 2)
            .unwrap();

        assert!(orderings
            .refine(Ordering::new(2, StepTime::AtEnd, 1, StepTime::AtStart))
            .is_none());
    }

    #[test]
    fn refine_accepts_redundant_and_unordered_constraints() {
        let orderings = Rc::new(BinaryOrderings::new())
            .refine_with_step(
                Ordering::new(1, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                1,
            )
            .unwrap()
            .refine_with_step(
                Ordering::new(2, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                2,
            )
            .unwrap();
        let refined = orderings
            .refine(Ordering::new(1, StepTime::AtEnd, 2, StepTime::AtStart))
            .unwrap();
        let redundant = refined
            .refine(Ordering::new(1, StepTime::AtEnd, 2, StepTime::AtStart))
            .unwrap();

        assert!(Rc::ptr_eq(&refined, &redundant));
    }

    /// Naive reference closure: an n x n boolean matrix with an explicit
    /// Floyd-Warshall pass. Deliberately the dumbest correct implementation, so
    /// a disagreement indicts the bit-set version rather than the model.
    struct Reference {
        n: usize,
        before: Vec<bool>,
    }

    impl Reference {
        fn new(n: usize) -> Self {
            Reference {
                n,
                before: vec![false; n * n],
            }
        }
        fn get(&self, a: usize, b: usize) -> bool {
            self.before[(a - 1) * self.n + (b - 1)]
        }
        fn set(&mut self, a: usize, b: usize) {
            self.before[(a - 1) * self.n + (b - 1)] = true;
        }
        fn close(&mut self) {
            for k in 1..=self.n {
                for a in 1..=self.n {
                    if self.get(a, k) {
                        for b in 1..=self.n {
                            if self.get(k, b) {
                                self.set(a, b);
                            }
                        }
                    }
                }
            }
        }
        /// Applies `a < b`, returning false if it would close a cycle.
        fn refine(&mut self, a: usize, b: usize) -> bool {
            if a == b || self.get(b, a) {
                return false;
            }
            self.set(a, b);
            self.close();
            true
        }
    }

    fn xorshift(state: &mut u64) -> u64 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *state = x;
        x
    }

    #[test]
    fn closure_matches_a_naive_reference_on_random_orderings() {
        const N: usize = 40;
        for seed in 1..60u64 {
            let mut rng = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;

            // Introduce all N steps first, so both models share the same universe.
            let mut orderings = Rc::new(BinaryOrderings::new());
            for step in 1..=N {
                orderings = orderings
                    .refine_with_step(
                        Ordering::new(step, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                        step,
                    )
                    .expect("introducing a step is always consistent");
            }
            let mut reference = Reference::new(N);

            for _ in 0..(N * 3) {
                let a = (xorshift(&mut rng) as usize % N) + 1;
                let b = (xorshift(&mut rng) as usize % N) + 1;
                if a == b {
                    continue;
                }

                let accepted_ref = {
                    let mut probe = Reference {
                        n: reference.n,
                        before: reference.before.clone(),
                    };
                    probe.refine(a, b)
                };
                let refined =
                    orderings.refine(Ordering::new(a, StepTime::AtEnd, b, StepTime::AtStart));

                assert_eq!(
                    refined.is_some(),
                    accepted_ref,
                    "seed {seed}: disagreed on whether {a} < {b} is consistent"
                );
                if let Some(next) = refined {
                    reference.refine(a, b);
                    orderings = next;
                }

                for x in 1..=N {
                    for y in 1..=N {
                        assert_eq!(
                            orderings.ordered_before(x, y),
                            reference.get(x, y),
                            "seed {seed}: ordered_before({x}, {y}) diverged after {a} < {b}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn set_before_and_rows_grow_lazily() {
        let mut orderings = BinaryOrderings::new();
        orderings.high_id = 3;
        orderings.succ = orderings.succ.expanded(3);
        // An untouched row holds no words at all.
        assert!(orderings.succ[0].words.is_empty());
        assert!(!orderings.ordered_before(1, 3));
        orderings.set_before(1, 3);
        assert!(orderings.ordered_before(1, 3));
        assert!(!orderings.ordered_before(3, 1));
    }

    #[test]
    fn row_table_shares_unchanged_blocks_and_isolates_writes() {
        let flat = RowTable::default().expanded(ROW_BLOCK_SIZE);
        assert!(matches!(flat, RowTable::Flat(_)));
        let parent = flat.expanded(2 * ROW_BLOCK_SIZE + 1);
        let mut child = parent.expanded(2 * ROW_BLOCK_SIZE + 2);
        let (RowTable::Blocked(before), RowTable::Blocked(after)) = (&parent, &child) else {
            panic!("long tables should share blocks");
        };
        assert!(Rc::ptr_eq(&before[0], &after[0]));
        assert!(Rc::ptr_eq(&before[1], &after[1]));
        assert!(!Rc::ptr_eq(&before[2], &after[2]));
        // A row write must copy its containing block before testing whether
        // the row itself is shared, or the parent's row could be mutated.
        Rc::make_mut(&mut child[ROW_BLOCK_SIZE]).set(129);
        assert!(!parent[ROW_BLOCK_SIZE].get(129));
        assert!(child[ROW_BLOCK_SIZE].get(129));
        assert!(!child[ROW_BLOCK_SIZE + 1].get(129));
        let (RowTable::Blocked(before), RowTable::Blocked(after)) = (&parent, &child) else {
            unreachable!();
        };
        assert!(Rc::ptr_eq(&before[0], &after[0]));
        assert!(!Rc::ptr_eq(&before[1], &after[1]));
        assert!(parent.get(2 * ROW_BLOCK_SIZE + 1).is_none());
        assert!(child.get(2 * ROW_BLOCK_SIZE + 1).is_some());
    }

    #[test]
    fn closure_matches_reference_across_block_and_word_boundaries() {
        const N: usize = 130;
        let mut orderings = Rc::new(BinaryOrderings::new())
            .refine_with_step(
                Ordering::new(N, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                N,
            )
            .unwrap();
        let empty = orderings.clone();
        let mut reference = Reference::new(N);
        for (a, b) in [
            (1, 32),
            (32, 33),
            (33, 64),
            (64, 65),
            (65, 96),
            (96, 97),
            (97, 128),
            (128, 129),
            (129, 130),
            (1, 64),
            (128, 32),
        ] {
            let refined = orderings.refine(Ordering::new(a, StepTime::AtEnd, b, StepTime::AtStart));
            assert_eq!(refined.is_some(), reference.refine(a, b));
            if let Some(next) = refined {
                orderings = next;
            }
            for x in 1..=N {
                for y in 1..=N {
                    assert_eq!(orderings.ordered_before(x, y), reference.get(x, y));
                    assert!(!empty.ordered_before(x, y));
                }
            }
        }
    }

    #[test]
    fn a_deep_reverse_order_schedules_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let n = 2_000;
                let mut orderings = BinaryOrderings {
                    high_id: n,
                    succ: RowTable::default().expanded(n),
                };
                for id in 1..=n {
                    let mut row = Row::default();
                    for predecessor in 1..id {
                        row.set(predecessor - 1);
                    }
                    orderings.succ[id - 1] = Rc::new(row);
                }
                let (times, makespan) = orderings.schedule();
                assert_eq!(makespan, n as f32);
                for id in 1..=n {
                    assert_eq!(times[&id], (n + 1 - id) as f32);
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
