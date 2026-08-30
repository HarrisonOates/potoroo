//! Persistent singly-linked list with structural sharing.
//!
//! The mutable collections of a plan (steps, links, unsafes, open conditions)
//! are immutable `Chain<T>` nodes shared across plan nodes via reference
//! counting. Refining a plan conses a new element onto the front (or removes
//! one), reusing the unchanged suffix. A chain is `Option<Rc<Chain<T>>>`, where
//! `None` is the empty chain and cloning the `Rc` shares the unchanged tail.

use std::rc::Rc;

/// A non-empty chain node. A full (possibly empty) chain is
/// `Option<Rc<Chain<T>>>`.
#[derive(Debug)]
pub struct Chain<T> {
    pub head: T,
    pub tail: Option<Rc<Chain<T>>>,
}

impl<T> Chain<T> {
    pub fn new(head: T, tail: Option<Rc<Chain<T>>>) -> Rc<Chain<T>> {
        Rc::new(Chain { head, tail })
    }

    /// Number of elements from this node to the end.
    pub fn len(&self) -> usize {
        let mut n = 0;
        let mut cur = Some(self);
        while let Some(node) = cur {
            n += 1;
            cur = node.tail.as_deref();
        }
        n
    }

    /// A non-empty chain node always holds at least its `head`, so this is
    /// always `false`; provided to satisfy the `len`/`is_empty` convention.
    /// The empty chain is represented by `None`, not by a `Chain` node.
    pub fn is_empty(&self) -> bool {
        false
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter { cur: Some(self) }
    }
}

impl<T: PartialEq> Chain<T> {
    pub fn contains(&self, x: &T) -> bool {
        self.iter().any(|h| h == x)
    }
}

impl<T: PartialEq + Clone> Chain<T> {
    /// Returns a chain with the first occurrence of `x` removed, sharing the
    /// suffix after the removed element. If `x` is not present the elements
    /// are unchanged (a fresh spine is built).
    pub fn remove(self: &Rc<Self>, x: &T) -> Option<Rc<Chain<T>>> {
        if self.head == *x {
            self.tail.clone()
        } else {
            match &self.tail {
                Some(t) => Some(Chain::new(self.head.clone(), t.remove(x))),
                None => Some(self.clone()),
            }
        }
    }
}

/// Borrowing iterator over a chain's elements.
pub struct Iter<'a, T> {
    cur: Option<&'a Chain<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let node = self.cur?;
        self.cur = node.tail.as_deref();
        Some(&node.head)
    }
}

pub fn cons<T>(head: T, tail: Option<Rc<Chain<T>>>) -> Option<Rc<Chain<T>>> {
    Some(Chain::new(head, tail))
}

pub fn len<T>(c: &Option<Rc<Chain<T>>>) -> usize {
    c.as_ref().map_or(0, |n| n.len())
}

pub fn contains<T: PartialEq>(c: &Option<Rc<Chain<T>>>, x: &T) -> bool {
    c.as_ref().is_some_and(|n| n.contains(x))
}

pub fn iter<T>(c: &Option<Rc<Chain<T>>>) -> Iter<'_, T> {
    Iter { cur: c.as_deref() }
}

pub fn remove<T: PartialEq + Clone>(c: &Option<Rc<Chain<T>>>, x: &T) -> Option<Rc<Chain<T>>> {
    match c {
        Some(n) => n.remove(x),
        None => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn from_vec(v: &[i32]) -> Option<Rc<Chain<i32>>> {
        let mut c = None;
        for &x in v.iter().rev() {
            c = cons(x, c);
        }
        c
    }

    fn to_vec(c: &Option<Rc<Chain<i32>>>) -> Vec<i32> {
        iter(c).copied().collect()
    }

    #[test]
    fn cons_prepends() {
        let c = from_vec(&[1, 2, 3]);
        assert_eq!(to_vec(&c), vec![1, 2, 3]);
        assert_eq!(len(&c), 3);
    }

    #[test]
    fn contains_works() {
        let c = from_vec(&[1, 2, 3]);
        assert!(contains(&c, &2));
        assert!(!contains(&c, &9));
    }

    #[test]
    fn remove_middle_shares_suffix() {
        let tail = from_vec(&[2, 3]);
        let c = cons(1, tail.clone());
        let removed = remove(&c, &1);
        // Removing the head returns exactly the shared tail Rc.
        assert!(Rc::ptr_eq(
            removed.as_ref().unwrap(),
            tail.as_ref().unwrap()
        ));
        assert_eq!(to_vec(&removed), vec![2, 3]);
    }

    #[test]
    fn remove_first_occurrence_only() {
        let c = from_vec(&[1, 2, 2, 3]);
        let removed = remove(&c, &2);
        assert_eq!(to_vec(&removed), vec![1, 2, 3]);
    }

    #[test]
    fn remove_absent_keeps_elements() {
        let c = from_vec(&[1, 2, 3]);
        let removed = remove(&c, &9);
        assert_eq!(to_vec(&removed), vec![1, 2, 3]);
    }
}
