//! Planning parameters.
//!
//! Only the classical-subset defaults are wired up: A* search, the `UCPOP`
//! plan-ranking heuristic, the `UCPOP` flaw-selection order, unit action cost,
//! weight 1, and lifted actions. IDA*/hill-climbing and ground-action toggling
//! exist as fields; only A* is exercised on the default path.

use crate::heuristics::{FlawSelectionOrder, Heuristic};

/// Search algorithm.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SearchAlgorithm {
    /// A* (the default): rank = g + w·h.
    A,
    /// IDA* (deferred).
    Ida,
    /// Hill climbing (deferred).
    Hc,
    /// Breadth-first search: rank = (steps, plan_id). No heuristic needed.
    Bfs,
    /// Greedy best-first search: rank = (h, steps, plan_id). Ignores the g
    /// component; the h value is still computed eagerly at generation time.
    Gbfs,
    /// Lazy GBFS: push refinements with the parent's h as a proxy rank; compute
    /// the real h only when a node is popped from the open list. Avoids h
    /// evaluation for nodes that are never expanded.
    LazyGbfs,
    /// Lazy GBFS with a boosted dual queue: a primary queue (h-ordered) and a
    /// secondary queue (FIFO). Both use lazy evaluation. The primary queue gets
    /// extra budget whenever a node improves the incumbent best-h (boost).
    LazyGbfsDual,
    /// LAMA-style queue alternation: every generated child is ranked eagerly
    /// under both the A* ordering (g + w·h) and the GBFS ordering (h) and
    /// pushed into two queues; expansions strictly alternate (1:1) between the
    /// A*-ordered and h-ordered queues. Bounds greedy search's worst case at
    /// roughly 2x A* while keeping greedy's wins.
    Alt,
}

/// Action cost model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActionCost {
    /// Every action costs one (the default).
    Unit,
    /// Durative cost (deferred).
    Duration,
    /// Relative cost (deferred).
    Relative,
}

/// Planning parameters.
#[derive(Debug, Clone)]
pub struct Parameters {
    pub search_algorithm: SearchAlgorithm,
    pub heuristic: Heuristic,
    pub action_cost: ActionCost,
    pub weight: f32,
    /// Flaw-selection orders, tried in round-robin.
    pub flaw_orders: Vec<FlawSelectionOrder>,
    /// Per-flaw-order generated-plan limits.
    pub search_limits: Vec<usize>,
    /// Whether to plan with fully ground actions. Ground instantiation is
    /// performed up front; the binding interface is otherwise identical.
    pub ground_actions: bool,
}

impl Default for Parameters {
    fn default() -> Self {
        Parameters {
            search_algorithm: SearchAlgorithm::A,
            heuristic: Heuristic::parse("UCPOP").expect("UCPOP is a valid heuristic"),
            action_cost: ActionCost::Unit,
            weight: 1.0,
            flaw_orders: vec![
                FlawSelectionOrder::parse("UCPOP").expect("UCPOP is a valid flaw order")
            ],
            search_limits: vec![usize::MAX],
            ground_actions: false,
        }
    }
}
