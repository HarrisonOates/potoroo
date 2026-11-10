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

/// A short, mostly empty list of class ids: no allocation when empty, one
/// shared slice otherwise (classes are cloned whenever a plan changes them).
#[derive(Debug, Clone, Default)]
struct IdList(Option<Rc<[ClassId]>>);

impl IdList {
    fn as_slice(&self) -> &[ClassId] {
        self.0.as_deref().unwrap_or(&[])
    }

    fn contains(&self, id: &ClassId) -> bool {
        self.as_slice().contains(id)
    }

    fn set(&mut self, ids: Vec<ClassId>) {
        self.0 = (!ids.is_empty()).then(|| ids.into());
    }

    fn push(&mut self, id: ClassId) {
        let mut ids = self.as_slice().to_vec();
        ids.push(id);
        self.set(ids);
    }

    fn retain(&mut self, keep: impl Fn(&ClassId) -> bool) {
        let ids: Vec<ClassId> = self
            .as_slice()
            .iter()
            .copied()
            .filter(|i| keep(i))
            .collect();
        self.set(ids);
    }

    fn clear(&mut self) {
        self.0 = None;
    }
}

#[derive(Debug, Clone)]
struct Class {
    constant: Option<Object>,
    domain: ObjSet,
    distinct: IdList,
    /// The class this one was merged into (union-find without path
    /// compression; merges link the newer class under the older).
    forward: Option<ClassId>,
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
    /// Classes changed since the last propagation: only constraints over
    /// them need revisiting. Empty in queued plans.
    dirty: Vec<ClassId>,
}

impl LBindings {
    /// Takes the classes changed since the last call.
    pub fn take_dirty(&mut self) -> Vec<ClassId> {
        std::mem::take(&mut self.dirty)
    }

    /// Marks a class as changed (a new constraint mentions it).
    pub fn touch(&mut self, c: ClassId) {
        self.dirty.push(c);
    }

    /// Adds the next step's variables, each in its own class over `domains`
    /// (one per variable, in order).
    pub fn add_step(&mut self, var_base: u32, domains: impl IntoIterator<Item = ObjSet>) {
        let first_slot = self.class_of.len() as u32;
        self.steps.push((first_slot, var_base));
        for domain in domains {
            let id = self.classes.len() as ClassId;
            self.dirty.push(id);
            let constant = domain.single();
            self.class_of.push(id);
            self.classes.push(Rc::new(Class {
                constant,
                domain,
                distinct: IdList::default(),
                forward: None,
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
        self.classes[c as usize].distinct.as_slice()
    }

    /// Number of class ids (merged ones included).
    pub fn num_classes(&self) -> usize {
        self.classes.len()
    }

    /// The class a class id was merged into (itself when not merged).
    pub fn representative(&self, mut c: ClassId) -> ClassId {
        while let Some(next) = self.classes[c as usize].forward {
            c = next;
        }
        c
    }

    /// The object a class (or the class it merged into) is bound to.
    pub fn value(&self, mut c: ClassId) -> Option<Object> {
        while let Some(next) = self.classes[c as usize].forward {
            c = next;
        }
        self.classes[c as usize].constant
    }

    /// Unbound classes in creation order.
    pub fn unbound_classes(&self) -> impl Iterator<Item = ClassId> + '_ {
        self.classes.iter().enumerate().filter_map(|(i, c)| {
            (c.constant.is_none() && c.forward.is_none()).then_some(i as ClassId)
        })
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
            (Resolved::Object(o), Resolved::Class(c))
            | (Resolved::Class(c), Resolved::Object(o)) => self.domain(c).contains(o),
            (Resolved::Class(a), Resolved::Class(b)) => {
                a == b
                    || (!self.distinct(a).contains(&b) && self.domain(a).intersects(self.domain(b)))
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
        next.relate(Resolved::Class(c), Resolved::Object(o), true)
            .then_some(next)
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
            (Resolved::Class(c), Resolved::Object(o), true)
            | (Resolved::Object(o), Resolved::Class(c), true) => self.assign(c, o),
            (Resolved::Class(c), Resolved::Object(o), false)
            | (Resolved::Object(o), Resolved::Class(c), false) => {
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
        self.dirty.push(c);
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
        let distinct = class.distinct.as_slice().to_vec();
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
        // Keep the older class. Linking a new step merges its fresh classes
        // into existing ones, which then usually need no change at all, so
        // they are not copied: only marked for propagation.
        let (keep, gone) = (x.min(y), x.max(y));
        let gone_class = (*self.classes[gone as usize]).clone();
        let kept = &self.classes[keep as usize];
        if let (Some(a), Some(b)) = (kept.constant, gone_class.constant) {
            if a != b {
                return false;
            }
        }
        let narrows = !kept.domain.is_subset(&gone_class.domain);
        let gains_constant = kept.constant.is_none() && gone_class.constant.is_some();
        let gains_distinct = !gone_class.distinct.as_slice().is_empty();
        for &d in gone_class.distinct.as_slice() {
            let dc = self.class_mut(d);
            dc.distinct.retain(|&e| e != gone);
            if !dc.distinct.contains(&keep) {
                dc.distinct.push(keep);
            }
        }
        if narrows || gains_constant || gains_distinct {
            let k = self.class_mut(keep);
            k.domain.intersect_with(&gone_class.domain);
            for &d in gone_class.distinct.as_slice() {
                if !k.distinct.contains(&d) {
                    k.distinct.push(d);
                }
            }
            if k.constant.is_none() {
                k.constant = gone_class.constant;
            }
        } else {
            self.touch(keep);
        }
        {
            let g = self.class_mut(gone);
            g.forward = Some(keep);
            g.distinct.clear();
        }
        match self.classes[keep as usize].constant {
            // Re-assert the constant against what the merge brought in.
            Some(o) if gains_constant || gains_distinct => {
                let k = self.class_mut(keep);
                k.constant = None;
                k.domain = std::iter::once(o).collect();
                self.assign(keep, o)
            }
            Some(_) => true,
            None if narrows => self.settle(keep),
            None => true,
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
            .add(&[
                (X, 1, Term::Object(Object(0)), 1, false),
                (X, 1, Term::Object(Object(1)), 1, false),
            ])
            .unwrap();
        assert_eq!(b.binding(X, 1), Term::Object(Object(2)));
        // Binding a class removes its object from distinct classes, which
        // binds a class left with one object.
        let b = two_steps().add(&[(Y, 2, X, 1, false)]).unwrap();
        let b = b.add(&[(X, 1, Term::Object(Object(0)), 1, true)]).unwrap();
        assert_eq!(b.binding(Y, 2), Term::Object(Object(1)));
        assert!(b
            .add(&[(Y, 2, Term::Object(Object(1)), 1, false)])
            .is_none());
        assert!(two_steps()
            .add(&[(X, 1, Y, 1, false), (X, 1, Y, 1, true)])
            .is_none());
    }
}

#[cfg(test)]
mod size_tests {
    #[test]
    fn classes_stay_small() {
        assert!(
            std::mem::size_of::<super::Class>() <= 64,
            "{}",
            std::mem::size_of::<super::Class>()
        );
    }
}
