//! A persistent vector in fixed-size chunks behind `Rc`. Cloning copies one
//! pointer; changing an entry copies its chunk and the chunk list, so a child
//! plan that touches a few entries shares the rest with its parent.

use std::rc::Rc;

const CHUNK: usize = 16;

#[derive(Debug, Clone)]
pub struct PVec<T> {
    chunks: Rc<Vec<Rc<Vec<T>>>>,
    len: usize,
}

impl<T> Default for PVec<T> {
    fn default() -> Self {
        PVec {
            chunks: Rc::new(Vec::new()),
            len: 0,
        }
    }
}

impl<T: Clone> PVec<T> {
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn get(&self, i: usize) -> Option<&T> {
        (i < self.len).then(|| &self.chunks[i / CHUNK][i % CHUNK])
    }

    #[inline]
    pub fn get_mut(&mut self, i: usize) -> &mut T {
        assert!(i < self.len);
        let chunks = Rc::make_mut(&mut self.chunks);
        &mut Rc::make_mut(&mut chunks[i / CHUNK])[i % CHUNK]
    }

    pub fn push(&mut self, value: T) {
        let chunks = Rc::make_mut(&mut self.chunks);
        if self.len % CHUNK == 0 {
            chunks.push(Rc::new(Vec::with_capacity(CHUNK)));
        }
        Rc::make_mut(chunks.last_mut().expect("a chunk")).push(value);
        self.len += 1;
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> + '_ {
        self.chunks.iter().flat_map(|c| c.iter())
    }
}

impl<T: Clone> std::ops::Index<usize> for PVec<T> {
    type Output = T;
    #[inline]
    fn index(&self, i: usize) -> &T {
        self.get(i).expect("index in bounds")
    }
}

#[cfg(test)]
mod tests {
    use super::PVec;

    #[test]
    fn children_share_untouched_chunks() {
        let mut parent = PVec::default();
        for i in 0..100u32 {
            parent.push(i);
        }
        let mut child = parent.clone();
        *child.get_mut(70) = 7;
        child.push(100);
        assert_eq!(parent[70], 70);
        assert_eq!(child[70], 7);
        assert_eq!(child.len(), 101);
        assert_eq!(parent.len(), 100);
        assert_eq!(child.iter().copied().sum::<u32>(), (0..101).sum::<u32>() - 70 + 7);
    }
}
