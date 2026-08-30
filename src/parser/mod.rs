//! PDDL parsing front-end.
//!
//! The [`pddl`](https://crates.io/crates/pddl) crate produces a strongly-typed
//! AST, which is lowered into Potoroo's internal model in [`lower`].

pub mod lower;
pub mod read;

pub use lower::{lower_domain, lower_problem, LowerError};
pub use read::{read_pddl, ParsedUnit, ReadError};
