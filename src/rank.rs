//! Inline lexicographic ranks for search queues.
//!
//! Each rank contains heuristic terms and search-specific tiebreakers.
//! [`MAX_TERMS`] covers every configuration accepted by the parser.

use std::cmp::Ordering;
use std::ops::Deref;

/// The most terms a rank can carry. `Heuristic::parse` caps composition at
/// [`MAX_HEURISTIC_TERMS`], and no search algorithm appends more than two
/// tiebreakers.
pub const MAX_TERMS: usize = 6;

/// The most heuristics that can be composed with `/`.
pub const MAX_HEURISTIC_TERMS: usize = MAX_TERMS - 2;

#[derive(Clone, Copy, Debug)]
pub struct Rank {
    len: u8,
    fifo: u8,
    lifo: u8,
    saved_primary: bool,
    terms: [f32; MAX_TERMS],
}

/// An exact rank component. Only live search state needs this expanded form;
/// queue entries keep compact tags and obtain IDs from their plans on demand.
#[derive(Clone, Copy, Debug)]
pub(crate) enum RankTerm {
    Score(f32),
    Fifo(usize),
    Lifo(usize),
}

impl RankTerm {
    pub const ZERO: Self = Self::Score(0.0);
    pub const INFINITY: Self = Self::Score(f32::INFINITY);

    pub fn is_finite(self) -> bool {
        match self {
            Self::Score(value) => value.is_finite(),
            _ => true,
        }
    }

    fn approximate(self) -> f32 {
        match self {
            Self::Score(value) => value,
            Self::Fifo(id) => id as f32,
            Self::Lifo(id) => -(id as f32),
        }
    }
}

/// Compare a nonnegative integer with an f32 without rounding the integer.
/// An f32 below 2^usize::BITS can safely be truncated to usize; if that ties,
/// its fractional part decides the comparison. NaN sorts after all numbers.
fn id_cmp_score(id: usize, score: f32) -> Ordering {
    if score.is_nan() || score >= 2.0f32.powi(usize::BITS as i32) {
        Ordering::Less
    } else if score < 0.0 {
        Ordering::Greater
    } else {
        id.cmp(&(score as usize)).then_with(|| {
            if score.fract() > 0.0 {
                Ordering::Less
            } else {
                Ordering::Equal
            }
        })
    }
}

impl Ord for RankTerm {
    fn cmp(&self, other: &Self) -> Ordering {
        use RankTerm::*;
        match (*self, *other) {
            (Score(a), Score(b)) => a
                .partial_cmp(&b)
                .unwrap_or_else(|| a.is_nan().cmp(&b.is_nan())),
            (Fifo(a), Fifo(b)) => a.cmp(&b),
            (Lifo(a), Lifo(b)) => b.cmp(&a),
            (Fifo(a), Lifo(b)) => (a != 0 || b != 0).cmp(&false),
            (Lifo(a), Fifo(b)) => false.cmp(&(a != 0 || b != 0)),
            (Fifo(id), Score(score)) => id_cmp_score(id, score),
            (Score(score), Fifo(id)) => id_cmp_score(id, score).reverse(),
            (Lifo(_), Score(score)) if score.is_nan() => Ordering::Less,
            (Score(score), Lifo(_)) if score.is_nan() => Ordering::Greater,
            (Lifo(id), Score(score)) => id_cmp_score(id, -score).reverse(),
            (Score(score), Lifo(id)) => id_cmp_score(id, -score),
        }
    }
}

impl PartialOrd for RankTerm {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for RankTerm {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for RankTerm {}

impl Rank {
    pub(crate) fn new() -> Self {
        Self::from_slice(&[])
    }

    /// Append directly to inline storage during heuristic evaluation. Proxy
    /// ranks with a saved parent ID are complete and must not be extended.
    pub(crate) fn push(&mut self, score: f32) {
        assert!(!self.saved_primary && (self.len as usize) < MAX_TERMS);
        self.terms[self.len as usize] = score;
        self.len += 1;
    }

    pub(crate) fn push_fifo(&mut self, id: usize) {
        self.push(id as f32);
        self.mark_fifo(self.len as usize - 1);
    }

    pub(crate) fn push_lifo(&mut self, id: usize) {
        self.push(-(id as f32));
        self.mark_lifo(self.len as usize - 1);
    }

    pub fn from_slice(terms: &[f32]) -> Rank {
        assert!(
            terms.len() <= MAX_TERMS,
            "a rank carries at most {MAX_TERMS} terms, got {}",
            terms.len()
        );
        let mut rank = Rank {
            len: terms.len() as u8,
            fifo: 0,
            lifo: 0,
            saved_primary: false,
            terms: [0.0; MAX_TERMS],
        };
        rank.terms[..terms.len()].copy_from_slice(terms);
        rank
    }

    pub(crate) fn mark_fifo(&mut self, index: usize) {
        assert!(index < self.len as usize);
        self.fifo |= 1 << index;
        self.lifo &= !(1 << index);
    }

    pub(crate) fn mark_lifo(&mut self, index: usize) {
        assert!(index < self.len as usize);
        self.lifo |= 1 << index;
        self.fifo &= !(1 << index);
    }

    pub(crate) fn fifo(id: usize) -> Self {
        let mut rank = Self::from_slice(&[id as f32]);
        rank.mark_fifo(0);
        rank
    }

    pub(crate) fn bfs(steps: usize, id: usize) -> Self {
        let mut rank = Self::from_slice(&[steps as f32, id as f32]);
        rank.mark_fifo(1);
        rank
    }

    pub(crate) fn lazy_proxy(primary: RankTerm, opens: usize, id: usize) -> Self {
        let mut rank = Self::from_slice(&[primary.approximate(), opens as f32, -(id as f32)]);
        rank.mark_lifo(2);
        let parent_id = match primary {
            RankTerm::Score(_) => return rank,
            RankTerm::Fifo(id) => {
                rank.mark_fifo(0);
                id
            }
            RankTerm::Lifo(id) => {
                rank.mark_lifo(0);
                id
            }
        };
        // A proxy has only three terms. Its unused final two words can hold
        // the parent's exact ID when the primary heuristic itself is FIFO or
        // LIFO. These are raw bits, never floating-point scores. This avoids
        // adding another usize to every entry for this uncommon configuration.
        rank.saved_primary = true;
        rank.terms[MAX_TERMS - 2] = f32::from_bits(parent_id as u32);
        rank.terms[MAX_TERMS - 1] = f32::from_bits(((parent_id as u64) >> 32) as u32);
        rank
    }

    fn term(&self, index: usize, plan_id: &impl Fn() -> usize) -> RankTerm {
        // Do not read the proxy's saved ID words as missing trailing scores.
        if index >= self.len as usize {
            return RankTerm::ZERO;
        }
        let bit = 1 << index;
        if (self.fifo | self.lifo) & bit == 0 {
            return RankTerm::Score(self.terms[index]);
        }
        let id = if self.saved_primary && index == 0 {
            (self.terms[MAX_TERMS - 2].to_bits() as u64
                | ((self.terms[MAX_TERMS - 1].to_bits() as u64) << 32)) as usize
        } else {
            plan_id()
        };
        if self.fifo & bit != 0 {
            RankTerm::Fifo(id)
        } else {
            RankTerm::Lifo(id)
        }
    }

    pub(crate) fn primary(&self, plan_id: usize) -> RankTerm {
        self.term(0, &|| plan_id)
    }

    /// Lexicographic comparison in which a *smaller* rank is the better plan
    /// and sorts as `Greater`, so a max-heap pops the best plan first. Missing
    /// trailing terms read as zero. IDs are loaded only when an ID term is
    /// reached, avoiding pointer chasing for comparisons decided by scores.
    /// NaN sorts after all numeric values, preserving a total queue ordering.
    pub fn better_first(
        &self,
        other: &Rank,
        self_id: impl Fn() -> usize,
        other_id: impl Fn() -> usize,
    ) -> Ordering {
        let n = self.len.max(other.len) as usize;
        for i in 0..n {
            let ordering = self.term(i, &self_id).cmp(&other.term(i, &other_id));
            if ordering != Ordering::Equal {
                return ordering.reverse();
            }
        }
        Ordering::Equal
    }
}

impl Deref for Rank {
    type Target = [f32];

    // Diagnostic score approximations, not the queue's exact ID ordering.
    fn deref(&self) -> &[f32] {
        &self.terms[..self.len as usize]
    }
}

impl From<Vec<f32>> for Rank {
    fn from(terms: Vec<f32>) -> Rank {
        Rank::from_slice(&terms)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::heuristics::Heuristic;

    #[test]
    fn integer_tags_do_not_enlarge_queue_ranks() {
        assert_eq!(std::mem::size_of::<Rank>(), 28);
    }

    #[test]
    fn exact_terms_have_a_consistent_numeric_order_including_mixed_types() {
        use RankTerm::*;
        let boundary = 1 << 24;
        // Groups are independently listed in increasing mathematical order.
        // In particular, +/-usize::MAX lie strictly inside +/-2^usize::BITS,
        // even on 64-bit targets where f64 cannot distinguish those values.
        let groups = vec![
            vec![Score(f32::NEG_INFINITY)],
            vec![Score(-(usize::MAX as f32))],
            vec![Lifo(usize::MAX)],
            vec![Lifo(usize::MAX - 1)],
            vec![Lifo(boundary + 1)],
            vec![Lifo(boundary), Score(-(boundary as f32))],
            vec![Lifo(1), Score(-1.0)],
            vec![Score(-0.5)],
            vec![Lifo(0), Fifo(0), Score(-0.0), Score(0.0)],
            vec![Score(0.5)],
            vec![Fifo(1), Score(1.0)],
            vec![Fifo(boundary), Score(boundary as f32)],
            vec![Fifo(boundary + 1)],
            vec![Fifo(usize::MAX - 1)],
            vec![Fifo(usize::MAX)],
            vec![Score(usize::MAX as f32)],
            vec![Score(f32::INFINITY)],
            vec![Score(f32::NAN), Score(-f32::NAN)],
        ];
        for (i, lefts) in groups.iter().enumerate() {
            for (j, rights) in groups.iter().enumerate() {
                for left in lefts {
                    for right in rights {
                        assert_eq!(left.cmp(right), i.cmp(&j), "{left:?} vs {right:?}");
                        assert_eq!(left == right, i == j);
                    }
                }
            }
        }
    }

    #[test]
    fn composed_id_terms_decide_before_later_scores_at_large_ids() {
        for older in [1 << 24, usize::MAX - 1] {
            let newer = older + 1;
            assert_eq!(older as f32, newer as f32, "this must exercise a float tie");
            for (name, sign, expected) in [
                ("ADD/FIFO/OC/LIFO", 1.0, Ordering::Greater),
                ("ADD/LIFO/OC/FIFO", -1.0, Ordering::Less),
            ] {
                let heuristic = Heuristic::parse(name).unwrap();
                // Later scores and the opposite ID term favor the wrong plan
                // if the first ID term is compared as a rounded float.
                let (old_oc, new_oc) = if sign > 0.0 { (9.0, 0.0) } else { (0.0, 9.0) };
                let a = heuristic.queue_rank(vec![
                    7.0,
                    sign * older as f32,
                    old_oc,
                    -sign * older as f32,
                ]);
                let b = heuristic.queue_rank(vec![
                    7.0,
                    sign * newer as f32,
                    new_oc,
                    -sign * newer as f32,
                ]);
                assert_eq!(a.better_first(&b, || older, || newer), expected);
                assert_eq!(b.better_first(&a, || newer, || older), expected.reverse());
            }
        }
    }

    #[test]
    fn scores_still_precede_ids_and_uncontrolled_ties_stay_equal() {
        let heuristic = Heuristic::parse("ADD/LIFO").unwrap();
        let a = heuristic.queue_rank(vec![1.0, -1.0]);
        let b = heuristic.queue_rank(vec![2.0, -2.0]);
        assert_eq!(
            a.better_first(&b, || panic!(), || panic!()),
            Ordering::Greater
        );
        let uncontrolled = Rank::from_slice(&[1.0]);
        assert_eq!(
            uncontrolled.better_first(&uncontrolled, || panic!(), || panic!()),
            Ordering::Equal
        );
    }

    #[test]
    fn algorithmic_fifo_and_lifo_terms_are_exact() {
        let old = usize::MAX - 1;
        let new = usize::MAX;
        let heuristic = Heuristic::parse("OC").unwrap();
        for (a, b, expected) in [
            (Rank::fifo(old), Rank::fifo(new), Ordering::Greater),
            (Rank::bfs(3, old), Rank::bfs(3, new), Ordering::Greater),
            (
                Rank::lazy_proxy(RankTerm::Score(7.0), 3, old),
                Rank::lazy_proxy(RankTerm::Score(7.0), 3, new),
                Ordering::Less,
            ),
            (
                heuristic.queue_rank(vec![7.0, 3.0, -(old as f32)]),
                heuristic.queue_rank(vec![7.0, 3.0, -(new as f32)]),
                Ordering::Less,
            ),
        ] {
            assert_eq!(a.better_first(&b, || old, || new), expected);
        }
        // BFS depth and GBFS open-condition preferences still come first.
        assert_eq!(
            Rank::bfs(2, new).better_first(&Rank::bfs(3, old), || panic!(), || panic!()),
            Ordering::Greater
        );
        assert_eq!(
            Rank::lazy_proxy(RankTerm::ZERO, 1, old).better_first(
                &Rank::lazy_proxy(RankTerm::ZERO, 2, new),
                || panic!(),
                || panic!()
            ),
            Ordering::Greater
        );
    }

    #[test]
    fn lazy_proxy_preserves_the_parents_exact_id_and_zero_pads_its_tail() {
        for primary in [
            RankTerm::Fifo(usize::MAX - 1),
            RankTerm::Lifo(usize::MAX - 1),
        ] {
            let proxy = Rank::lazy_proxy(primary, 0, usize::MAX);
            assert_eq!(proxy.primary(usize::MAX), primary);
            let real = Rank::fifo(usize::MAX);
            assert_eq!(
                proxy.better_first(&real, || usize::MAX, || usize::MAX),
                Ordering::Greater
            );
        }
        let proxy = Rank::lazy_proxy(RankTerm::Fifo(usize::MAX), 0, usize::MAX);
        let mut real =
            Rank::from_slice(&[usize::MAX as f32, 0.0, -(usize::MAX as f32), 0.0, 1.0, 0.0]);
        real.mark_fifo(0);
        real.mark_lifo(2);
        assert_eq!(
            proxy.better_first(&real, || usize::MAX, || usize::MAX),
            Ordering::Greater
        );
    }

    #[test]
    fn mixed_lazy_and_eager_comparisons_are_transitive() {
        let id = 1 << 24;
        let candidates = [
            (Rank::fifo(id + 1), id + 1),
            (Rank::fifo(id), id),
            (Rank::lazy_proxy(RankTerm::Fifo(id + 1), 0, id + 2), id + 2),
            (
                Rank::lazy_proxy(RankTerm::Score(id as f32), 0, id + 2),
                id + 2,
            ),
            (Rank::from_slice(&[id as f32, 1.0]), id + 3),
        ];
        let cmp = |a: &(Rank, usize), b: &(Rank, usize)| a.0.better_first(&b.0, || a.1, || b.1);
        for a in &candidates {
            for b in &candidates {
                assert_eq!(cmp(a, b), cmp(b, a).reverse());
                for c in &candidates {
                    if cmp(a, b).is_ge() && cmp(b, c).is_ge() {
                        assert!(cmp(a, c).is_ge(), "{a:?}, {b:?}, {c:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn smaller_rank_sorts_greater() {
        let a = Rank::from_slice(&[1.0, 5.0]);
        let b = Rank::from_slice(&[2.0, 0.0]);
        assert_eq!(
            a.better_first(&b, || panic!(), || panic!()),
            Ordering::Greater
        );
        assert_eq!(b.better_first(&a, || panic!(), || panic!()), Ordering::Less);
    }

    #[test]
    fn missing_terms_read_as_zero() {
        let short = Rank::from_slice(&[1.0]);
        let long = Rank::from_slice(&[1.0, 0.0, 0.0]);
        assert_eq!(
            short.better_first(&long, || panic!(), || panic!()),
            Ordering::Equal
        );
        let positive = Rank::from_slice(&[1.0, 1.0]);
        assert_eq!(
            short.better_first(&positive, || panic!(), || panic!()),
            Ordering::Greater
        );
    }

    #[test]
    fn derefs_to_its_terms() {
        let rank = Rank::from(vec![3.0, 4.0]);
        assert_eq!(&*rank, &[3.0, 4.0]);
        assert_eq!(rank[0], 3.0);
        assert_eq!(rank.len(), 2);
    }
}
