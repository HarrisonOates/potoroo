//! PDDL functions (numeric fluents) and the function table.
//!
//! Functions are parsed and represented so numeric content can be surfaced and
//! rejected, but classical planning never evaluates them.

use std::collections::{HashMap, HashSet};

use crate::types::Type;

/// A function. Wraps an index into a [`FunctionTable`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Function(pub u32);

/// Owns function names, parameter types, and the static-function set.
#[derive(Debug, Default)]
pub struct FunctionTable {
    names: Vec<String>,
    parameters: Vec<Vec<Type>>,
    dynamic: HashSet<Function>,
    by_name: HashMap<String, Function>,
}

impl FunctionTable {
    pub fn new() -> Self {
        FunctionTable::default()
    }

    pub fn add_function(&mut self, name: &str) -> Function {
        if let Some(&f) = self.by_name.get(name) {
            return f;
        }
        let f = Function(self.names.len() as u32);
        self.names.push(name.to_string());
        self.parameters.push(Vec::new());
        self.by_name.insert(name.to_string(), f);
        f
    }

    pub fn add_parameter(&mut self, f: Function, ty: Type) {
        self.parameters[f.0 as usize].push(ty);
    }

    pub fn make_dynamic(&mut self, f: Function) {
        self.dynamic.insert(f);
    }

    pub fn is_static(&self, f: Function) -> bool {
        !self.dynamic.contains(&f)
    }

    pub fn name(&self, f: Function) -> &str {
        &self.names[f.0 as usize]
    }

    pub fn parameters(&self, f: Function) -> &[Type] {
        &self.parameters[f.0 as usize]
    }

    pub fn find_function(&self, name: &str) -> Option<Function> {
        self.by_name.get(name).copied()
    }
}
