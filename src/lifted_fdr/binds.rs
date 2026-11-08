//! Binding constraints for lifted FDR plans.
//!
//! Every step variable has a slot, and every slot belongs to an equality
//! class. A class records its constant (if bound), its domain (objects of
//! its type minus objects it must differ from), the classes it must differ
//! from, and its member slots. Resolution is two array reads, unlike the
//! chain of varsets in [`crate::bindings::Bindings`], whose lookups dominated
//! propagation.
//!
//! The structure is persistent: classes sit behind `Rc` individually, so a
//! child plan copies one vector of pointers and clones only the classes it
//! changes. Domains are maintained eagerly: binding a class removes its
//! object from every class it must differ from, and a class whose domain
//! becomes a single object is bound to it (forward checking).

use std::rc::Rc;

use crate::terms::{Object, Term, Variable};

use super::objset::ObjSet;
use super::pvec::PVec;

/// An equality class of step variables.
pub type ClassId = u32;

#[derive(Debug, Clone)]
struct Class {
    constant: Option<Object>,
    domain: ObjSet,
    distinct: Vec<ClassId>,
    /// The class this one was merged into (union-find without path
    /// compression; merges link the smaller class under the larger).
    forward: Option<ClassId>,
    /// Slots in the class, for union by size.
    size: u32,
}

/// A resolved term: an object, or an unbound class.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Resolved {
    Object(Object),
    Class(ClassId),
}

/// `(left, left step, right, right step, equal?)`.
pub type Constraint = (Term, usize, Term, usize, bool);

#[derive(Debug, Clone, Default)]
pub struct LBindings {
    /// For real step `id`, its first slot (index `id - 1`) and the schema's
    /// first global variable.
    steps: PVec<(u32, u32)>,
    class_of: PVec<ClassId>,
    classes: PVec<Rc<Class>>,
}

impl LBindings {
    /// Adds the next step's variables, each in its own class over `domains`
    /// (one per variable, in order).
    pub fn add_step(&mut self, var_base: u32, domains: impl IntoIterator<Item = ObjSet>) {
        let first_slot = self.class_of.len() as u32;
        self.steps.push((first_slot, var_base));
        for domain in domains {
            let id = self.classes.len() as ClassId;
            let constant = domain.single();
            self.class_of.push(id);
            self.classes.push(Rc::new(Class {
                constant,
                domain,
                distinct: Vec::new(),
                forward: None,
                size: 1,
            }));
        }
    }

    #[inline]
    fn slot(&self, v: Variable, step: usize) -> Option<u32> {
        let &(first, base) = self.steps.get(step.checked_sub(1)?)?;
        Some(first + v.0.checked_sub(base)?)
    }

    /// The class of a step variable.
    #[inline]
    pub fn class(&self, v: Variable, step: usize) -> ClassId {
        let mut c = self.class_of[self.slot(v, step).expect("a variable of a plan step") as usize];
        while let Some(next) = self.classes[c as usize].forward {
            c = next;
        }
        c
    }

    #[inline]
    pub fn resolve(&self, t: Term, step: usize) -> Resolved {
        match t {
            Term::Object(o) => Resolved::Object(o),
            Term::Variable(v) => {
                let c = self.class(v, step);
                match self.classes[c as usize].constant {
                    Some(o) => Resolved::Object(o),
                    None => Resolved::Class(c),
                }
            }
        }
    }

    /// The term with its object substituted when bound.
    #[inline]
    pub fn binding(&self, t: Term, step: usize) -> Term {
        match self.resolve(t, step) {
            Resolved::Object(o) => Term::Object(o),
            Resolved::Class(_) => t,
        }
    }

    pub fn domain(&self, c: ClassId) -> &ObjSet {
        &self.classes[c as usize].domain
    }

    pub fn distinct(&self, c: ClassId) -> &[ClassId] {
        &self.classes[c as usize].distinct
    }

    /// Unbound classes in creation order.
    pub fn unbound_classes(&self) -> impl Iterator<Item = ClassId> + '_ {
        self.classes
            .iter()
            .enumerate()
            .filter_map(|(i, c)| (c.constant.is_none() && c.forward.is_none()).then_some(i as ClassId))
    }

    /// Equality already entailed.
    pub fn terms_equal(&self, l: Term, ls: usize, r: Term, rs: usize) -> bool {
        match (self.resolve(l, ls), self.resolve(r, rs)) {
            (Resolved::Object(a), Resolved::Object(b)) => a == b,
            (Resolved::Class(a), Resolved::Class(b)) => a == b,
            _ => false,
        }
    }

    /// Whether equating the terms is consistent on its own.
    pub fn terms_can_equal(&self, l: Term, ls: usize, r: Term, rs: usize) -> bool {
        match (self.resolve(l, ls), self.resolve(r, rs)) {
            (Resolved::Object(a), Resolved::Object(b)) => a == b,
            (Resolved::Object(o), Resolved::Class(c)) | (Resolved::Class(c), Resolved::Object(o)) => {
                self.domain(c).contains(o)
            }
            (Resolved::Class(a), Resolved::Class(b)) => {
                a == b || (!self.distinct(a).contains(&b) && self.domain(a).intersects(self.domain(b)))
            }
        }
    }

    /// Adds (in)equalities, or `None` if inconsistent.
    pub fn add(&self, constraints: &[Constraint]) -> Option<LBindings> {
        let mut next = self.clone();
        for &(l, ls, r, rs, equal) in constraints {
            let (a, b) = (next.resolve(l, ls), next.resolve(r, rs));
            if !next.relate(a, b, equal) {
                return None;
            }
        }
        Some(next)
    }

    /// Binds a class to an object.
    pub fn bind(&self, c: ClassId, o: Object) -> Option<LBindings> {
        let mut next = self.clone();
        next.relate(Resolved::Class(c), Resolved::Object(o), true).then_some(next)
    }

    /// Restricts a class's domain; binds it when one object remains.
    pub fn restrict(&mut self, c: ClassId, domain: &ObjSet) -> bool {
        if !self.class_mut(c).domain.intersect_with(domain) {
            return true;
        }
        self.settle(c)
    }

    fn relate(&mut self, a: Resolved, b: Resolved, equal: bool) -> bool {
        match (a, b, equal) {
            (Resolved::Object(x), Resolved::Object(y), _) => (x == y) == equal,
            (Resolved::Class(c), Resolved::Object(o), true) | (Resolved::Object(o), Resolved::Class(c), true) => {
                self.assign(c, o)
            }
            (Resolved::Class(c), Resolved::Object(o), false) | (Resolved::Object(o), Resolved::Class(c), false) => {
                self.class_mut(c).domain.remove(o);
                self.settle(c)
            }
            (Resolved::Class(x), Resolved::Class(y), true) => self.merge(x, y),
            (Resolved::Class(x), Resolved::Class(y), false) => {
                if x == y {
                    return false;
                }
                if !self.classes[x as usize].distinct.contains(&y) {
                    self.class_mut(x).distinct.push(y);
                    self.class_mut(y).distinct.push(x);
                }
                true
            }
        }
    }

    fn class_mut(&mut self, c: ClassId) -> &mut Class {
        Rc::make_mut(self.classes.get_mut(c as usize))
    }

    /// Binds an unbound class, removing the object from its distinct classes.
    fn assign(&mut self, c: ClassId, o: Object) -> bool {
        if let Some(existing) = self.classes[c as usize].constant {
            return existing == o;
        }
        if !self.classes[c as usize].domain.contains(o) {
            return false;
        }
        let class = self.class_mut(c);
        class.constant = Some(o);
        class.domain = std::iter::once(o).collect();
        let distinct = class.distinct.clone();
        for d in distinct {
            if self.classes[d as usize].constant == Some(o) {
                return false;
            }
            if self.classes[d as usize].domain.contains(o) {
                self.class_mut(d).domain.remove(o);
                if !self.settle(d) {
                    return false;
                }
            }
        }
        true
    }

    /// After a domain shrank: empty fails, one object binds.
    fn settle(&mut self, c: ClassId) -> bool {
        let class = &self.classes[c as usize];
        if class.constant.is_some() {
            return !class.domain.is_empty();
        }
        match class.domain.single() {
            Some(o) => self.assign(c, o),
            None => !class.domain.is_empty(),
        }
    }

    fn merge(&mut self, x: ClassId, y: ClassId) -> bool {
        if x == y {
            return true;
        }
        if self.classes[x as usize].distinct.contains(&y) {
            return false;
        }
        // Keep the larger class.
        let (keep, gone) = if self.classes[x as usize].size >= self.classes[y as usize].size {
            (x, y)
        } else {
            (y, x)
        };
        let gone_class = (*self.classes[gone as usize]).clone();
        if let (Some(a), Some(b)) = (self.classes[keep as usize].constant, gone_class.constant) {
            if a != b {
                return false;
            }
        }
        for &d in &gone_class.distinct {
            let dc = self.class_mut(d);
            dc.distinct.retain(|&e| e != gone);
            if !dc.distinct.contains(&keep) {
                dc.distinct.push(keep);
            }
        }
        {
            let k = self.class_mut(keep);
            k.size += gone_class.size;
            k.domain.intersect_with(&gone_class.domain);
            for &d in &gone_class.distinct {
                if !k.distinct.contains(&d) {
                    k.distinct.push(d);
                }
            }
            if k.constant.is_none() {
                k.constant = gone_class.constant;
            }
        }
        {
            let g = self.class_mut(gone);
            g.forward = Some(keep);
            g.distinct.clear();
        }
        match self.classes[keep as usize].constant {
            Some(o) => {
                // Re-assert the constant against the merged distinct set.
                let k = self.class_mut(keep);
                k.constant = None;
                k.domain = std::iter::once(o).collect();
                self.assign(keep, o)
            }
            None => self.settle(keep),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(objects: &[u32]) -> ObjSet {
        objects.iter().map(|&o| Object(o)).collect()
    }

    fn two_steps() -> LBindings {
        let mut b = LBindings::default();
        b.add_step(0, [set(&[0, 1, 2]), set(&[0, 1, 2])]);
        b.add_step(0, [set(&[0, 1, 2]), set(&[0, 1])]);
        b
    }

    const X: Term = Term::Variable(Variable(0));
    const Y: Term = Term::Variable(Variable(1));

    #[test]
    fn equality_merges_and_intersects() {
        let b = two_steps().add(&[(Y, 1, Y, 2, true)]).unwrap();
        assert!(b.terms_equal(Y, 1, Y, 2));
        assert_eq!(b.domain(b.class(Variable(1), 1)), &set(&[0, 1]));
    }

    #[test]
    fn inequalities_force_and_fail() {
        let b = two_steps();
        let b = b
            .add(&[(X, 1, Term::Object(Object(0)), 1, false), (X, 1, Term::Object(Object(1)), 1, false)])
            .unwrap();
        assert_eq!(b.binding(X, 1), Term::Object(Object(2)));
        // Binding a class removes its object from distinct classes, which
        // binds a class left with one object.
        let b = two_steps().add(&[(Y, 2, X, 1, false)]).unwrap();
        let b = b.add(&[(X, 1, Term::Object(Object(0)), 1, true)]).unwrap();
        assert_eq!(b.binding(Y, 2), Term::Object(Object(1)));
        assert!(b.add(&[(Y, 2, Term::Object(Object(1)), 1, false)]).is_none());
        assert!(two_steps().add(&[(X, 1, Y, 1, false), (X, 1, Y, 1, true)]).is_none());
    }
}
