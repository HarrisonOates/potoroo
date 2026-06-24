//! PDDL types and the type table.
//!
//! A [`Type`] is a small `Copy` newtype over an `i32`:
//!
//! * a non-negative value is a *simple* type whose index into
//!   [`Types::names`] is `index` (with `Type(0)` reserved for `object`);
//! * a negative value `-(i + 1)` encodes a *union* (`either`) type whose
//!   component set lives at `Types::unions[i]`.
//!
//! The subtype relation is stored as a dense transitive-closure boolean matrix
//! indexed directly by simple-type index.

use std::collections::BTreeSet;
use std::collections::HashMap;

/// A PDDL type. See the module docs for the index encoding.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Type(pub i32);

impl Type {
    pub fn simple(self) -> bool {
        self.0 >= 0
    }
}

/// The built-in `object` type, supertype of every simple type.
pub const OBJECT: Type = Type(0);

pub const OBJECT_NAME: &str = "object";
pub const NUMBER_NAME: &str = "number";

/// Owns the set of declared types and the subtype relation.
#[derive(Debug, Default, Clone)]
pub struct Types {
    /// Simple-type names, indexed by [`Type`] index. `names[0] == "object"`.
    names: Vec<String>,
    /// Transitive closure of the subtype relation over simple types.
    /// `subtype[a][b]` is true iff simple type `a` is a subtype of `b`.
    subtype: Vec<Vec<bool>>,
    /// Component sets of union types, indexed by `-(index) - 1`.
    unions: Vec<BTreeSet<Type>>,
    /// Name -> simple type lookup.
    by_name: HashMap<String, Type>,
}

impl Types {
    pub fn new() -> Self {
        let mut t = Types {
            names: Vec::new(),
            subtype: Vec::new(),
            unions: Vec::new(),
            by_name: HashMap::new(),
        };
        // Index 0 is reserved for `object`.
        t.names.push(OBJECT_NAME.to_string());
        t.subtype.push(vec![true]); // object <: object
        t.by_name.insert(OBJECT_NAME.to_string(), OBJECT);
        t
    }

    /// Adds a simple type with the given name (or returns the existing one).
    pub fn add_type(&mut self, name: &str) -> Type {
        if let Some(&t) = self.by_name.get(name) {
            return t;
        }
        let index = self.names.len() as i32;
        let ty = Type(index);
        self.names.push(name.to_string());
        // Grow the subtype matrix to a square (n+1) x (n+1), seeding the
        // reflexive entry and `<: object`.
        let n = self.names.len();
        for row in self.subtype.iter_mut() {
            row.resize(n, false);
        }
        let mut new_row = vec![false; n];
        new_row[index as usize] = true; // reflexive
        new_row[OBJECT.0 as usize] = true; // every type is a subtype of object
        self.subtype.push(new_row);
        self.by_name.insert(name.to_string(), ty);
        ty
    }

    /// Adds `type2` as a supertype of `type1`, maintaining transitive closure.
    /// Returns `false` if `type2` is already a proper subtype of `type1` (a
    /// cyclic declaration).
    pub fn add_supertype(&mut self, type1: Type, type2: Type) -> bool {
        if !type2.simple() {
            // Add each component of the union as a supertype.
            let components: Vec<Type> = self.unions[(-type2.0 - 1) as usize]
                .iter()
                .copied()
                .collect();
            for c in components {
                if !self.add_supertype(type1, c) {
                    return false;
                }
            }
            return true;
        }
        if self.subtype(type1, type2) {
            return true;
        }
        if self.subtype(type2, type1) {
            return false;
        }
        // Make every subtype of type1 a subtype of every supertype of type2.
        let n = self.names.len();
        let subs: Vec<usize> = (0..n).filter(|&k| self.subtype[k][type1.0 as usize]).collect();
        let supers: Vec<usize> =
            (0..n).filter(|&l| self.subtype[type2.0 as usize][l]).collect();
        for &k in &subs {
            for &l in &supers {
                self.subtype[k][l] = true;
            }
        }
        true
    }

    pub fn subtype(&self, type1: Type, type2: Type) -> bool {
        if type1 == type2 {
            return true;
        }
        if !type1.simple() {
            // Every component of the union must be a subtype of type2.
            return self.unions[(-type1.0 - 1) as usize]
                .iter()
                .all(|&c| self.subtype(c, type2));
        }
        if !type2.simple() {
            // type1 must be a subtype of some component of the union.
            return self.unions[(-type2.0 - 1) as usize]
                .iter()
                .any(|&c| self.subtype(type1, c));
        }
        self.subtype[type1.0 as usize][type2.0 as usize]
    }

    /// Tests if two types are compatible (one is a subtype of the other).
    pub fn compatible(&self, type1: Type, type2: Type) -> bool {
        self.subtype(type1, type2) || self.subtype(type2, type1)
    }

    /// Adds (or simplifies) a union of the given component types. A singleton
    /// set collapses to its sole member.
    pub fn union_type(&mut self, types: BTreeSet<Type>) -> Type {
        assert!(!types.is_empty(), "empty union type");
        if types.len() == 1 {
            return *types.iter().next().unwrap();
        }
        self.unions.push(types);
        Type(-(self.unions.len() as i32))
    }

    /// Fills `out` with the simple components of `ty` (the empty set for
    /// `object`).
    pub fn components(&self, out: &mut BTreeSet<Type>, ty: Type) {
        if !ty.simple() {
            out.clone_from(&self.unions[(-ty.0 - 1) as usize]);
        } else if ty != OBJECT {
            out.insert(ty);
        }
    }

    pub fn find_type(&self, name: &str) -> Option<Type> {
        self.by_name.get(name).copied()
    }

    /// Returns the printable name of a simple type. Panics for union types.
    pub fn name(&self, ty: Type) -> &str {
        assert!(ty.simple(), "name() called on a union type");
        &self.names[ty.0 as usize]
    }

    /// Returns the name of a simple type if it exists, else `None`. Used to
    /// enumerate the declared simple types (ids are dense from 0).
    pub fn name_opt(&self, ty: Type) -> Option<&str> {
        if ty.simple() && (ty.0 as usize) < self.names.len() {
            Some(&self.names[ty.0 as usize])
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subtype_chain() {
        let mut t = Types::new();
        let animal = t.add_type("animal");
        let dog = t.add_type("dog");
        let poodle = t.add_type("poodle");
        assert!(t.add_supertype(dog, animal));
        assert!(t.add_supertype(poodle, dog));
        assert!(t.subtype(poodle, animal)); // transitive
        assert!(t.subtype(dog, OBJECT));
        assert!(!t.subtype(animal, dog));
        assert!(t.compatible(animal, poodle));
    }

    #[test]
    fn union_type_membership() {
        let mut t = Types::new();
        let cat = t.add_type("cat");
        let dog = t.add_type("dog");
        let mut set = BTreeSet::new();
        set.insert(cat);
        set.insert(dog);
        let either = t.union_type(set);
        assert!(!either.simple());
        assert!(t.subtype(cat, either));
        assert!(t.subtype(dog, either));
    }
}
