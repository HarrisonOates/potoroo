//! Grounded, strict HTN planning by refinement in plan space.
//!
//! Decomposition and causal refinement can be interleaved, with optional TDG
//! guidance. It shares Potoroo's persistent chains and ordering engine,
//! without changing flat nodes or dispatch. pandaPIgrounder supplies grounded
//! input; negative preconditions and method tests must be compiled by the
//! frontend. Native conditional effects are rejected by the reader.
pub mod input;
pub mod model;
pub mod modification;
pub mod pipeline;
pub mod plan;
pub mod refine;
pub mod search;
mod support;
pub mod tdg;
mod tdg_cache;
mod unit_cycles;
pub mod validate;

#[cfg(test)]
mod systematic_tests;

pub use model::{Action, Method, Problem, Task};
pub use modification::ModificationTdg;
pub use refine::FlawSelection;
pub use search::{
    search, AStarTieBreak, Config, Outcome, SearchResult, SearchStrategy, Solution, Stats,
    StopReason,
};
pub use tdg::TdgMode;
pub use unit_cycles::UnitCyclePolicy;
