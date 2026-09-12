//! PDDL predicates and the predicate table.

use std::collections::HashMap;

use crate::types::Type;

/// A predicate. Wraps an index into a [`PredicateTable`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Predicate(pub u32);

/// Owns predicate names, parameter types, and the static-predicate set.
#[derive(Debug, Default, Clone)]
pub struct PredicateTable {
    names: Vec<String>,
    parameters: Vec<Vec<Type>>,
    /// Whether each predicate appears in some effect, indexed by predicate id.
    /// Every predicate starts static until [`make_dynamic`](Self::make_dynamic).
    /// Dense rather than a set because `is_static` is asked per open condition
    /// by the flaw order and per atom by the planning graph, and a `Predicate`
    /// is already an index into `names`.
    dynamic: Vec<bool>,
    by_name: HashMap<String, Predicate>,
}

impl PredicateTable {
    pub fn new() -> Self {
        PredicateTable::default()
    }

    /// Adds a predicate with the given name (or returns the existing one).
    pub fn add_predicate(&mut self, name: &str) -> Predicate {
        if let Some(&p) = self.by_name.get(name) {
            return p;
        }
        let p = Predicate(self.names.len() as u32);
        self.names.push(name.to_string());
        self.parameters.push(Vec::new());
        self.dynamic.push(false);
        self.by_name.insert(name.to_string(), p);
        p
    }

    pub fn add_parameter(&mut self, p: Predicate, ty: Type) {
        self.parameters[p.0 as usize].push(ty);
    }

    /// Marks a predicate as dynamic (appearing in some effect).
    pub fn make_dynamic(&mut self, p: Predicate) {
        let idx = p.0 as usize;
        if idx >= self.dynamic.len() {
            self.dynamic.resize(idx + 1, false);
        }
        self.dynamic[idx] = true;
    }

    #[inline]
    pub fn is_static(&self, p: Predicate) -> bool {
        !self.dynamic.get(p.0 as usize).copied().unwrap_or(false)
    }

    pub fn name(&self, p: Predicate) -> &str {
        &self.names[p.0 as usize]
    }

    pub fn parameters(&self, p: Predicate) -> &[Type] {
        &self.parameters[p.0 as usize]
    }

    pub fn find_predicate(&self, name: &str) -> Option<Predicate> {
        self.by_name.get(name).copied()
    }

    /// Number of declared predicates (ids are dense from 0).
    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}
