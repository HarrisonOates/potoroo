//! Dense sets of objects as bitsets. Object ids are small and contiguous
//! (domain constants, then problem objects), so domain intersection,
//! membership and counting are word operations.

use crate::terms::Object;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ObjSet {
    words: Vec<u64>,
}

impl ObjSet {
    pub fn new(capacity: usize) -> Self {
        ObjSet {
            words: vec![0; capacity.div_ceil(64)],
        }
    }

    #[inline]
    pub fn insert(&mut self, o: Object) {
        let i = o.0 as usize;
        if i / 64 >= self.words.len() {
            self.words.resize(i / 64 + 1, 0);
        }
        self.words[i / 64] |= 1 << (i % 64);
    }

    #[inline]
    pub fn remove(&mut self, o: Object) {
        let i = o.0 as usize;
        if let Some(word) = self.words.get_mut(i / 64) {
            *word &= !(1 << (i % 64));
        }
    }

    #[inline]
    pub fn contains(&self, o: Object) -> bool {
        let i = o.0 as usize;
        self.words.get(i / 64).is_some_and(|w| w & (1 << (i % 64)) != 0)
    }

    pub fn len(&self) -> usize {
        self.words.iter().map(|w| w.count_ones() as usize).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.words.iter().all(|w| *w == 0)
    }

    pub fn clear(&mut self) {
        self.words.iter_mut().for_each(|w| *w = 0);
    }

    /// Keeps only members of `other`; whether anything was removed.
    pub fn intersect_with(&mut self, other: &ObjSet) -> bool {
        let mut changed = false;
        for (i, w) in self.words.iter_mut().enumerate() {
            let next = *w & other.words.get(i).copied().unwrap_or(0);
            changed |= next != *w;
            *w = next;
        }
        changed
    }

    pub fn intersects(&self, other: &ObjSet) -> bool {
        self.words.iter().zip(&other.words).any(|(a, b)| a & b != 0)
    }

    pub fn union_with(&mut self, other: &ObjSet) {
        if other.words.len() > self.words.len() {
            self.words.resize(other.words.len(), 0);
        }
        for (w, o) in self.words.iter_mut().zip(&other.words) {
            *w |= o;
        }
    }

    /// Members in increasing id order.
    pub fn iter(&self) -> impl Iterator<Item = Object> + '_ {
        self.words.iter().enumerate().flat_map(|(i, &w)| {
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
