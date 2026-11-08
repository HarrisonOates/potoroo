//! Lifted finite-domain POCL planning.
//!
//! Steps are action schemas under binding constraints, as in the lifted
//! literal planner; conditions and effects are over schematic state variables
//! derived from lifted mutex groups ([`task`]), as in the ground FDR planner.
//! A writer of a possibly co-designating variable instance threatens a link
//! whenever its value may differ, so mutual exclusion is visible to threat
//! detection without e-deletion.

pub mod flaws;
pub mod heuristic;
pub mod invariants;
pub mod plan;
pub mod search;
pub mod task;

#[cfg(test)]
mod tests;

pub use search::{solve, Config, Lane, Outcome, Solution, Stats};
pub use task::{LiftedTask, Unsupported};
