//! Dense sets of objects as bitsets. Object ids are small and contiguous
//! (domain constants, then problem objects), so domain intersection,
//! membership and counting are word operations. Sets over the first 128
//! objects are stored inline; a class domain is cloned whenever a plan
//! changes it, so avoiding the allocation matters.

use crate::terms::Object;

const INLINE: usize = 2;

#[derive(Debug, Clone)]
enum Words {
    Inline([u64; INLINE]),
    Heap(Box<[u64]>),
}

#[derive(Debug, Clone)]
pub struct ObjSet {
    words: Words,
}

impl Default for ObjSet {
    fn default() -> Self {
        ObjSet {
            words: Words::Inline([0; INLINE]),
        }
    }
}

impl PartialEq for ObjSet {
    fn eq(&self, other: &Self) -> bool {
        let (a, b) = (self.slice(), other.slice());
        let n = a.len().max(b.len());
        (0..n).all(|i| a.get(i).copied().unwrap_or(0) == b.get(i).copied().unwrap_or(0))
    }
}

impl Eq for ObjSet {}

impl ObjSet {
    /// An empty set with room for objects `0..capacity` without reallocating.
    pub fn new(capacity: usize) -> Self {
        let words = capacity.div_ceil(64);
        if words <= INLINE {
            ObjSet::default()
        } else {
            ObjSet {
                words: Words::Heap(vec![0; words].into_boxed_slice()),
            }
        }
    }

    #[inline]
    fn slice(&self) -> &[u64] {
        match &self.words {
            Words::Inline(w) => w,
            Words::Heap(w) => w,
        }
    }

    #[inline]
    fn slice_mut(&mut self) -> &mut [u64] {
        match &mut self.words {
            Words::Inline(w) => w,
            Words::Heap(w) => w,
        }
    }

    /// Makes room for at least `n` words.
    fn reserve_words(&mut self, n: usize) {
        if n <= self.slice().len() {
            return;
        }
        let mut words = self.slice().to_vec();
        words.resize(n, 0);
        self.words = Words::Heap(words.into_boxed_slice());
    }

    #[inline]
    pub fn insert(&mut self, o: Object) {
        let i = o.0 as usize;
        self.reserve_words(i / 64 + 1);
        self.slice_mut()[i / 64] |= 1 << (i % 64);
    }

    #[inline]
    pub fn remove(&mut self, o: Object) {
        let i = o.0 as usize;
        if let Some(word) = self.slice_mut().get_mut(i / 64) {
            *word &= !(1 << (i % 64));
        }
    }

    #[inline]
    pub fn contains(&self, o: Object) -> bool {
        let i = o.0 as usize;
        self.slice().get(i / 64).is_some_and(|w| w & (1 << (i % 64)) != 0)
    }

    pub fn len(&self) -> usize {
        self.slice().iter().map(|w| w.count_ones() as usize).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.slice().iter().all(|w| *w == 0)
    }

    pub fn clear(&mut self) {
        self.slice_mut().iter_mut().for_each(|w| *w = 0);
    }

    /// Keeps only members of `other`; whether anything was removed.
    pub fn intersect_with(&mut self, other: &ObjSet) -> bool {
        let theirs = other.slice();
        let mut changed = false;
        for (i, w) in self.slice_mut().iter_mut().enumerate() {
            let next = *w & theirs.get(i).copied().unwrap_or(0);
            changed |= next != *w;
            *w = next;
        }
        changed
    }

    /// Whether every member is also in `other`.
    pub fn is_subset(&self, other: &ObjSet) -> bool {
        let theirs = other.slice();
        self.slice()
            .iter()
            .enumerate()
            .all(|(i, w)| w & !theirs.get(i).copied().unwrap_or(0) == 0)
    }

    pub fn intersects(&self, other: &ObjSet) -> bool {
        self.slice().iter().zip(other.slice()).any(|(a, b)| a & b != 0)
    }

    pub fn union_with(&mut self, other: &ObjSet) {
        self.reserve_words(other.slice().len());
        let theirs = other.slice().to_vec();
        for (w, o) in self.slice_mut().iter_mut().zip(&theirs) {
            *w |= o;
        }
    }

    /// Members in increasing id order.
    pub fn iter(&self) -> impl Iterator<Item = Object> + '_ {
        self.slice().iter().enumerate().flat_map(|(i, &w)| {
            let mut bits = w;
            std::iter::from_fn(move || {
                if bits == 0 {
                    return None;
                }
                let b = bits.trailing_zeros();
                bits &= bits - 1;
                Some(Object((i * 64) as u32 + b))
            })
        })
    }

    /// The only member, if there is exactly one.
    pub fn single(&self) -> Option<Object> {
        let mut it = self.iter();
        let first = it.next()?;
        it.next().is_none().then_some(first)
    }
}

impl FromIterator<Object> for ObjSet {
    fn from_iter<I: IntoIterator<Item = Object>>(iter: I) -> Self {
        let mut set = ObjSet::default();
        for o in iter {
            set.insert(o);
        }
        set
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inline_and_heap_sets_agree() {
        let small: ObjSet = [1, 5, 100].into_iter().map(Object).collect();
        let large: ObjSet = [1, 5, 100, 300].into_iter().map(Object).collect();
        assert_eq!(small.len(), 3);
        assert!(large.contains(Object(300)));
        let mut a = large.clone();
        assert!(a.intersect_with(&small));
        assert_eq!(a, small);
        let mut b = small.clone();
        b.union_with(&large);
        assert_eq!(b, large);
        assert_eq!(large.iter().map(|o| o.0).collect::<Vec<_>>(), vec![1, 5, 100, 300]);
    }
}
