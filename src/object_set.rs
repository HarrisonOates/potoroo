//! Small object domains without per-value hashing. Larger object IDs remain
//! sparse, so a high ID never allocates an enormous dense bit vector.

use crate::fasthash::FastSet;
use crate::terms::Object;

#[derive(Clone, Default)]
pub(crate) struct ObjectSet {
    small: u128,
    large: FastSet<Object>,
}

impl ObjectSet {
    pub(crate) fn insert(&mut self, object: Object) {
        if object.0 < 128 {
            self.small |= 1u128 << object.0;
        } else {
            self.large.insert(object);
        }
    }

    pub(crate) fn contains(&self, object: Object) -> bool {
        if object.0 < 128 {
            self.small & (1u128 << object.0) != 0
        } else {
            self.large.contains(&object)
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.small.count_ones() as usize + self.large.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.small == 0 && self.large.is_empty()
    }

    pub(crate) fn intersect_with(&mut self, other: &Self) {
        self.small &= other.small;
        self.large.retain(|object| other.large.contains(object));
    }

    pub(crate) fn is_disjoint(&self, other: &Self) -> bool {
        self.small & other.small == 0
            && if self.large.len() <= other.large.len() {
                self.large
                    .iter()
                    .all(|object| !other.large.contains(object))
            } else {
                other
                    .large
                    .iter()
                    .all(|object| !self.large.contains(object))
            }
    }

    /// Conservative allowance for hash buckets and control bytes. The inline
    /// mask is counted by the containing ObjectSet allocation.
    pub(crate) fn heap_bytes(&self) -> usize {
        if self.large.capacity() == 0 {
            0
        } else {
            64 + self.large.capacity() * 8
        }
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = Object> + '_ {
        let mut bits = self.small;
        std::iter::from_fn(move || {
            if bits == 0 {
                return None;
            }
            let object = Object(bits.trailing_zeros());
            bits &= bits - 1;
            Some(object)
        })
        .chain(self.large.iter().copied())
    }
}

impl FromIterator<Object> for ObjectSet {
    fn from_iter<T: IntoIterator<Item = Object>>(iter: T) -> Self {
        let mut result = Self::default();
        for object in iter {
            result.insert(object);
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn masks_and_sparse_ids_agree_with_hash_sets() {
        let objects = [0, 1, 63, 64, 65, 127, 128, 129, 10000, u32::MAX];
        for mask in 0..1024 {
            let chosen: Vec<_> = objects
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, &o)| Object(o))
                .collect();
            let set: ObjectSet = chosen.iter().copied().collect();
            let reference: FastSet<_> = chosen.into_iter().collect();
            assert_eq!(set.len(), reference.len());
            assert_eq!(set.is_empty(), reference.is_empty());
            assert_eq!(set.iter().collect::<FastSet<_>>(), reference);
            for &o in &objects {
                assert_eq!(set.contains(Object(o)), reference.contains(&Object(o)));
            }
            let keep: ObjectSet = objects.iter().step_by(2).map(|&o| Object(o)).collect();
            let mut intersection = set.clone();
            intersection.intersect_with(&keep);
            let expected: FastSet<_> = reference
                .into_iter()
                .filter(|&o| keep.contains(o))
                .collect();
            assert_eq!(intersection.iter().collect::<FastSet<_>>(), expected);
            assert_eq!(set.is_disjoint(&keep), expected.is_empty());
            assert_eq!(keep.is_disjoint(&set), expected.is_empty());
        }
    }
}
