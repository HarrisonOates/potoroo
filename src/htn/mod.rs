//! Grounded, strict HTN planning by refinement in plan space.
//!
//! Decomposition and causal refinement can be interleaved, with optional TDG
//! guidance. It shares Potoroo's persistent chains and ordering engine,
//! without changing flat nodes or dispatch. pandaPIgrounder supplies grounded
//! input; negative preconditions and method tests must be compiled by the
//! frontend. Native conditional effects are rejected by the reader.
pub mod input;
pub mod model;
pub mod pipeline;
pub mod plan;
pub mod refine;
pub mod search;
pub mod tdg;
mod tdg_cache;
pub mod validate;

#[cfg(test)]
mod systematic_tests;

pub use model::{Action, Method, Problem, Task};
pub use refine::FlawSelection;
pub use search::{
    search, Config, Outcome, SearchResult, SearchStrategy, Solution, Stats, StopReason,
};
pub use tdg::TdgMode;
