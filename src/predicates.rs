//! PDDL predicates and the predicate table.

use std::collections::{HashMap, HashSet};

use crate::types::Type;

/// A predicate. Wraps an index into a [`PredicateTable`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Predicate(pub u32);

/// Owns predicate names, parameter types, and the static-predicate set.
#[derive(Debug, Default, Clone)]
pub struct PredicateTable {
    names: Vec<String>,
    parameters: Vec<Vec<Type>>,
    /// Predicates that never appear in an effect; every predicate starts static
    /// until [`make_dynamic`](Self::make_dynamic).
    dynamic: HashSet<Predicate>,
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
        self.by_name.insert(name.to_string(), p);
        p
    }

    pub fn add_parameter(&mut self, p: Predicate, ty: Type) {
        self.parameters[p.0 as usize].push(ty);
    }

    /// Marks a predicate as dynamic (appearing in some effect).
    pub fn make_dynamic(&mut self, p: Predicate) {
        self.dynamic.insert(p);
    }

    pub fn is_static(&self, p: Predicate) -> bool {
        !self.dynamic.contains(&p)
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
