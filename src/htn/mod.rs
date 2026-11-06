//! Grounded, strict HTN planning by refinement in plan space.
//!
//! This first kernel decomposes compound tasks before resolving primitive
//! causal flaws. It shares Potoroo's persistent chains and ordering engine,
//! without changing flat nodes or dispatch. Malleefowl supplies grounded PANDA
//! input; negative preconditions and method tests must be compiled by the
//! frontend. Native conditional effects are rejected by the reader.
pub mod input;
pub mod model;
pub mod pipeline;
pub mod plan;
pub mod search;
pub mod validate;

pub use model::{Action, Method, Problem, Task};
pub use search::{search, Config, Outcome, SearchResult, Solution, Stats, StopReason};
