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
    terms: [f32; MAX_TERMS],
}

impl Rank {
    pub fn from_slice(terms: &[f32]) -> Rank {
        assert!(
            terms.len() <= MAX_TERMS,
            "a rank carries at most {MAX_TERMS} terms, got {}",
            terms.len()
        );
        let mut rank = Rank {
            len: terms.len() as u8,
            terms: [0.0; MAX_TERMS],
        };
        rank.terms[..terms.len()].copy_from_slice(terms);
        rank
    }

    /// Lexicographic comparison in which a *smaller* rank is the better plan
    /// and sorts as `Greater`, so a max-heap pops the best plan first. Missing
    /// trailing terms read as zero, and NaN compares equal.
    pub fn better_first(&self, other: &Rank) -> Ordering {
        let n = self.len.max(other.len) as usize;
        for i in 0..n {
            let a = self.terms[i];
            let b = other.terms[i];
            if a < b {
                return Ordering::Greater;
            } else if a > b {
                return Ordering::Less;
            }
        }
        Ordering::Equal
    }
}

impl Deref for Rank {
    type Target = [f32];

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

    #[test]
    fn smaller_rank_sorts_greater() {
        let a = Rank::from_slice(&[1.0, 5.0]);
        let b = Rank::from_slice(&[2.0, 0.0]);
        assert_eq!(a.better_first(&b), Ordering::Greater);
        assert_eq!(b.better_first(&a), Ordering::Less);
    }

    #[test]
    fn missing_terms_read_as_zero() {
        let short = Rank::from_slice(&[1.0]);
        let long = Rank::from_slice(&[1.0, 0.0, 0.0]);
        assert_eq!(short.better_first(&long), Ordering::Equal);
        let positive = Rank::from_slice(&[1.0, 1.0]);
        assert_eq!(short.better_first(&positive), Ordering::Greater);
    }

    #[test]
    fn derefs_to_its_terms() {
        let rank = Rank::from(vec![3.0, 4.0]);
        assert_eq!(&*rank, &[3.0, 4.0]);
        assert_eq!(rank[0], 3.0);
        assert_eq!(rank.len(), 2);
    }
}
