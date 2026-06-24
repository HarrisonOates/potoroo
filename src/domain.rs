//! Lowered PDDL domains.

use std::collections::HashMap;

use crate::action::ActionSchema;
use crate::functions::FunctionTable;
use crate::predicates::PredicateTable;
use crate::requirements::Requirements;
use crate::terms::TermTable;
use crate::types::Types;

/// A lowered domain: name tables plus action schemas.
#[derive(Debug)]
pub struct Domain {
    pub name: String,
    pub requirements: Requirements,
    pub types: Types,
    pub predicates: PredicateTable,
    pub functions: FunctionTable,
    /// Domain constants. A problem's object table extends this one.
    pub constants: TermTable,
    pub actions: Vec<ActionSchema>,
    /// Action name -> index into `actions`.
    pub actions_by_name: HashMap<String, usize>,
}

impl Domain {
    pub fn find_action(&self, name: &str) -> Option<&ActionSchema> {
        self.actions_by_name.get(name).map(|&i| &self.actions[i])
    }
}
