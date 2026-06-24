//! PDDL terms: objects, variables, and the term table.
//!
//! A [`TermTable`] owns object names and their types plus the types of all
//! lifted variables. A problem's object table extends its domain's constant
//! table via an optional borrowed `parent` reference. Variable indices are local
//! to each table; schema lowering keeps every variable scope local.

use std::collections::HashMap;

use crate::types::{Type, Types};

/// An object (a ground term). Wraps an index into a [`TermTable`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Object(pub u32);

/// A variable (a lifted term). Wraps an index into a [`TermTable`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Variable(pub u32);

/// A term is either an object or a variable.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Term {
    Object(Object),
    Variable(Variable),
}

impl Term {
    pub fn object(self) -> bool {
        matches!(self, Term::Object(_))
    }

    pub fn variable(self) -> bool {
        matches!(self, Term::Variable(_))
    }

    pub fn as_object(self) -> Object {
        match self {
            Term::Object(o) => o,
            Term::Variable(_) => panic!("term is not an object"),
        }
    }

    pub fn as_variable(self) -> Variable {
        match self {
            Term::Variable(v) => v,
            Term::Object(_) => panic!("term is not a variable"),
        }
    }
}

impl From<Object> for Term {
    fn from(o: Object) -> Self {
        Term::Object(o)
    }
}

impl From<Variable> for Term {
    fn from(v: Variable) -> Self {
        Term::Variable(v)
    }
}

/// Owns object and variable declarations.
///
/// When `parent` is set (a problem's objects extending domain constants), object
/// indices in this table are offset by `parent_object_count` so that an
/// [`Object`] index is globally unique across the parent/child pair.
#[derive(Debug, Default)]
pub struct TermTable {
    /// Number of objects owned by the parent table (0 if no parent).
    parent_object_count: u32,
    /// Names of objects owned by *this* table.
    object_names: Vec<String>,
    /// Types of objects owned by *this* table (parallel to `object_names`).
    object_types: Vec<Type>,
    /// Types of variables allocated by this table.
    variable_types: Vec<Type>,
    /// Name -> object lookup for objects owned by this table.
    by_name: HashMap<String, Object>,
    /// Cache of compatible-object queries (`compatible_objects`).
    compatible_cache: HashMap<Type, Vec<Object>>,
}

impl TermTable {
    pub fn new() -> Self {
        TermTable::default()
    }

    /// Constructs a term table extending `parent`. Object indices in the new
    /// table start above the parent's objects so they never collide.
    pub fn with_parent(parent: &TermTable) -> Self {
        TermTable {
            parent_object_count: parent.total_object_count(),
            ..TermTable::default()
        }
    }

    /// Total number of objects visible through this table, including the parent.
    fn total_object_count(&self) -> u32 {
        self.parent_object_count + self.object_names.len() as u32
    }

    pub fn add_object(&mut self, name: &str, ty: Type) -> Object {
        if let Some(&o) = self.by_name.get(name) {
            return o;
        }
        let index = self.parent_object_count + self.object_names.len() as u32;
        let o = Object(index);
        self.object_names.push(name.to_string());
        self.object_types.push(ty);
        self.by_name.insert(name.to_string(), o);
        self.compatible_cache.clear();
        o
    }

    pub fn add_variable(&mut self, ty: Type) -> Variable {
        let index = self.variable_types.len() as u32;
        self.variable_types.push(ty);
        Variable(index)
    }

    /// Finds an object by name, searching this table then the parent.
    pub fn find_object(&self, parent: Option<&TermTable>, name: &str) -> Option<Object> {
        if let Some(&o) = self.by_name.get(name) {
            return Some(o);
        }
        parent.and_then(|p| p.find_object(None, name))
    }

    /// Returns the type of an object. The object must be owned by this table or
    /// the supplied parent.
    pub fn object_type(&self, parent: Option<&TermTable>, o: Object) -> Type {
        if o.0 < self.parent_object_count {
            let p = parent.expect("object belongs to a parent table not provided");
            return p.object_type(None, o);
        }
        self.object_types[(o.0 - self.parent_object_count) as usize]
    }

    pub fn variable_type(&self, v: Variable) -> Type {
        self.variable_types[v.0 as usize]
    }

    /// Returns all variable types allocated by this table, indexed by variable
    /// index. Used to snapshot a per-schema scope's variable types for later
    /// type reasoning during search.
    pub fn variable_types(&self) -> &[Type] {
        &self.variable_types
    }

    /// Returns all object types owned by *this* table (excluding the parent),
    /// paired with the global [`Object`] index.
    pub fn owned_objects(&self) -> impl Iterator<Item = (Object, Type)> + '_ {
        self.object_types
            .iter()
            .enumerate()
            .map(move |(i, &ty)| (Object(self.parent_object_count + i as u32), ty))
    }

    /// Number of objects owned by the parent table.
    pub fn parent_object_count(&self) -> u32 {
        self.parent_object_count
    }

    /// Returns the name of an object owned by this table or its parent.
    pub fn object_name<'a>(&'a self, parent: Option<&'a TermTable>, o: Object) -> &'a str {
        if o.0 < self.parent_object_count {
            let p = parent.expect("object belongs to a parent table not provided");
            return p.object_name(None, o);
        }
        &self.object_names[(o.0 - self.parent_object_count) as usize]
    }

    /// Returns all objects (this table's and the parent's) whose type is a
    /// subtype of `ty`. Results are cached.
    pub fn compatible_objects(
        &mut self,
        types: &Types,
        parent: Option<&TermTable>,
        ty: Type,
    ) -> Vec<Object> {
        if let Some(cached) = self.compatible_cache.get(&ty) {
            return cached.clone();
        }
        let mut result = Vec::new();
        if let Some(p) = parent {
            for i in 0..p.object_names.len() {
                let o = Object(i as u32);
                if types.subtype(p.object_types[i], ty) {
                    result.push(o);
                }
            }
        }
        for i in 0..self.object_names.len() {
            let o = Object(self.parent_object_count + i as u32);
            if types.subtype(self.object_types[i], ty) {
                result.push(o);
            }
        }
        self.compatible_cache.insert(ty, result.clone());
        result
    }
}
