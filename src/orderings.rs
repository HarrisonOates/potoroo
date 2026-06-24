//! Step ordering constraints.
//!
//! A [`BinaryOrderings`] is the transitive closure of a strict partial order
//! over real step ids (1-based). Step 0 (the initial step) precedes everything
//! and the goal step ([`GOAL_ID`]) follows everything; those two are handled
//! specially rather than stored in the matrix.

use std::collections::HashMap;
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
    pub fn new(before_id: usize, before_time: StepTime, after_id: usize, after_time: StepTime) -> Self {
        Ordering {
            before_id,
            before_time,
            after_id,
            after_time,
        }
    }
}

/// One row of the transitive-closure matrix, bit-packed into `u64` words.
/// The row for step `m` (`m >= 2`) holds `2*m - 2` bits encoding `m`'s order
/// relation with every lower-numbered step in both directions (see [`BinaryOrderings`]).
#[derive(Debug, Clone, Default)]
struct Row {
    words: Vec<u64>,
}

impl Row {
    fn with_bits(nbits: usize) -> Self {
        Row {
            words: vec![0u64; nbits.div_ceil(64)],
        }
    }

    #[inline]
    fn get(&self, i: usize) -> bool {
        (self.words[i >> 6] >> (i & 63)) & 1 != 0
    }

    #[inline]
    fn set(&mut self, i: usize) {
        self.words[i >> 6] |= 1u64 << (i & 63);
    }
}

/// Transitive-closure boolean order over real step ids.
///
/// One bit-packed [`Row`] per step, shared across plans via `Rc` with
/// copy-on-write at row granularity (`Rc::make_mut`). A `refine` only
/// deep-copies the few rows it actually modifies; sibling plans share the rest.
/// `rows[m - 2]` is the row for step `m` (`m` in `2..=high_id`), so
/// `rows.len() == high_id - 1` (empty while `high_id <= 1`). Within step `m`'s
/// row of `2*m - 2` bits: bit `k - 1` is "step `k` before step `m`" and bit
/// `2*m - 2 - k` is "step `m` before step `k`", for each lower step `k` in
/// `1..m`.
#[derive(Debug, Clone, Default)]
pub struct BinaryOrderings {
    /// Highest real step id seen (0 means only init/goal). Real steps are
    /// `1..=high_id`.
    high_id: usize,
    /// Per-step transitive-closure rows; see the type doc for the layout.
    rows: Vec<Rc<Row>>,
}

impl BinaryOrderings {
    pub fn new() -> Self {
        BinaryOrderings::default()
    }

    /// Returns true iff real step `id1` is ordered before real step `id2`.
    /// Both ids must be real steps in `1..=high_id` (callers handle init/goal
    /// specially first).
    fn ordered_before(&self, id1: usize, id2: usize) -> bool {
        if id1 == id2 {
            false
        } else if id1 < id2 {
            self.rows[id2 - 2].get(id1 - 1)
        } else {
            self.rows[id1 - 2].get(2 * id1 - 2 - id2)
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
        if new_ordering.before_id != 0
            && new_ordering.after_id != GOAL_ID
            && self.possibly_not_before(
                new_ordering.before_id,
                new_ordering.before_time,
                new_ordering.after_id,
                new_ordering.after_time,
            )
        {
            let mut orderings = (**self).clone();
            orderings.fill_transitive(new_ordering);
            Some(Rc::new(orderings))
        } else {
            // Either trivially satisfied (init before / before goal), or already implied.
            Some(self.clone())
        }
    }

    /// Returns the ordering collection accounting for a freshly added step plus
    /// the new ordering.
    pub fn refine_with_step(
        self: &Rc<Self>,
        new_ordering: Ordering,
        new_step_id: usize,
    ) -> Option<Rc<BinaryOrderings>> {
        if new_step_id != 0 && new_step_id != GOAL_ID {
            let mut orderings = (**self).clone();
            if new_step_id > orderings.high_id {
                orderings.high_id = new_step_id;
                // Allocate the bit row for each newly introduced step. Step `m`
                // gets a row of `2*m - 2` bits at index `m - 2`; step 1 has no row.
                while orderings.rows.len() < new_step_id - 1 {
                    let m = orderings.rows.len() + 2;
                    orderings.rows.push(Rc::new(Row::with_bits(2 * m - 2)));
                }
            }
            if new_ordering.before_id != 0 && new_ordering.after_id != GOAL_ID {
                orderings.fill_transitive(new_ordering);
            }
            Some(Rc::new(orderings))
        } else {
            Some(self.clone())
        }
    }

    /// Marks `id1` before `id2`. The affected row is copied on first write via
    /// `Rc::make_mut`, giving copy-on-write behaviour (each row is cloned at
    /// most once per `refine`).
    fn set_before(&mut self, id1: usize, id2: usize) {
        if id1 != id2 {
            let i = id1.max(id2) - 2;
            let row = Rc::make_mut(&mut self.rows[i]);
            if id1 < id2 {
                row.set(id1 - 1);
            } else {
                row.set(2 * id1 - 2 - id2);
            }
        }
    }

    /// Updates the transitive closure given a new ordering constraint.
    fn fill_transitive(&mut self, ordering: Ordering) {
        let i = ordering.before_id;
        let j = ordering.after_id;
        if !self.ordered_before(i, j) {
            let n = self.high_id;
            // All steps ordered before i (and i itself) must precede j and all
            // steps ordered after j.
            for k in 1..=n {
                if (k == i || self.ordered_before(k, i)) && !self.ordered_before(k, j) {
                    for l in 1..=n {
                        if (j == l || self.ordered_before(j, l)) && !self.ordered_before(k, l) {
                            self.set_before(k, l);
                        }
                    }
                }
            }
        }
    }

    /// Fills `start_times` with each real step's integer start time and returns
    /// the makespan. The start time of a step is one plus the longest chain of
    /// predecessors; the initial step is not scheduled (it is implicitly at
    /// time 0).
    pub fn schedule(&self) -> (HashMap<usize, f32>, f32) {
        let mut start_times: HashMap<usize, f32> = HashMap::new();
        let mut max_dist = 0.0f32;
        for i in 1..=self.high_id {
            let ed = self.schedule_step(&mut start_times, i);
            if ed > max_dist {
                max_dist = ed;
            }
        }
        (start_times, max_dist)
    }

    fn schedule_step(&self, start_times: &mut HashMap<usize, f32>, step_id: usize) -> f32 {
        if let Some(&d) = start_times.get(&step_id) {
            return d;
        }
        let mut sd = 1.0f32;
        for j in 1..=self.high_id {
            if step_id != j && self.ordered_before(j, step_id) {
                let ed = 1.0 + self.schedule_step(start_times, j);
                if ed > sd {
                    sd = ed;
                }
            }
        }
        start_times.insert(step_id, sd);
        sd
    }
}
