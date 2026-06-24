//! PDDL parsing front-end.
//!
//! Rather than porting VHPOP's bison/flex grammar (`pddl.yy`/`tokens.ll`), we use
//! the [`pddl`](https://crates.io/crates/pddl) crate to produce a strongly-typed
//! AST and lower it into our internal model in [`lower`].

pub mod lower;
pub mod read;

pub use lower::{lower_domain, lower_problem, LowerError};
pub use read::{read_pddl, ParsedUnit, ReadError};
