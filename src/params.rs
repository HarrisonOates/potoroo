//! Planning parameters and defaults.

use std::time::Instant;

use crate::heuristics::{FlawSelectionOrder, Heuristic};
use crate::pruning::PruneOptions;

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
    /// Use the PDDL/SAS+ operator cost (the default). Costless tasks supply one.
    Task,
    /// Every action costs one, ignoring declared task costs.
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
    /// Per-flaw-order ranking heuristics (FDR POCL only); `None` uses
    /// `heuristic`. Lets interleaved queues rank by different heuristics.
    pub order_heuristics: Vec<Option<Heuristic>>,
    /// Per-flaw-order heuristic weights; `None` uses `weight`.
    pub order_weights: Vec<Option<f32>>,
    /// Whether to plan with fully ground actions. Ground instantiation is
    /// performed up front; the binding interface is otherwise identical.
    pub ground_actions: bool,
    /// Whether to collect per-evaluation `h_eval_ms` timing.
    /// `h_evals` is counted regardless.
    pub time_h_evals: bool,
    /// Native FDR A*/GBFS only: give FF-supported refinements an additional
    /// queue, selected five times per ordinary-queue selection. All refinements
    /// remain in the ordinary queue. Off by default.
    pub preferred_operators: bool,
    /// Native FDR A* only: partial expansion (Yoshizumi, Miura & Ishida,
    /// AAAI 2000). An expansion queues only the children whose f-value equals
    /// the plan's current one, and re-queues the plan at its next child
    /// f-value. Same expansion order as A* up to ties; far fewer queue entries.
    pub partial_expansion: bool,
    /// With `partial_expansion`, plans with at most this many refinements are
    /// expanded fully: regenerating a few children saves little memory.
    pub partial_expansion_min: usize,
    /// Opt-in pruning rules from the POCL literature. All off by default; see
    /// [`PruneOptions`].
    pub prune: PruneOptions,
    /// Halve every open list once it holds more than this many plans in
    /// total. Incomplete; see [`crate::memory`].
    pub max_queued: Option<usize>,
    /// Halve every open list once the process's resident set exceeds this
    /// many megabytes. Incomplete; see [`crate::memory`].
    pub memory_limit_mb: Option<usize>,
    /// Wall-clock instant at which the search must give up and report the
    /// limit reached. Checked once per expanded node: a clock read costs a
    /// fraction of an expansion, and a node is the finest granularity a
    /// restart portfolio has any use for. `None` (the default) never reads the
    /// clock at all, so an unbounded run pays nothing for the field.
    pub deadline: Option<Instant>,
    /// Stop the search once the process's resident set exceeds this many
    /// megabytes. Unlike [`Parameters::memory_limit_mb`], which trims the open
    /// list and is therefore incomplete, this only *ends* the search: no node
    /// is dropped and the outcome is the same limit-reached that a deadline
    /// gives. That is what lets a memory-hungry stage of a `--stage` portfolio
    /// run before another one — its queues are freed at the restart instead of
    /// the process being killed under a hard address-space cap.
    pub memory_stop_mb: Option<usize>,
}

impl Default for Parameters {
    fn default() -> Self {
        Parameters {
            search_algorithm: SearchAlgorithm::A,
            heuristic: Heuristic::parse("ADD/LIFO").expect("ADD/LIFO is a valid heuristic"),
            action_cost: ActionCost::Task,
            weight: 1.0,
            flaw_orders: vec![
                FlawSelectionOrder::parse("STATIC").expect("STATIC is a valid flaw order")
            ],
            search_limits: vec![usize::MAX],
            order_heuristics: Vec::new(),
            order_weights: Vec::new(),
            ground_actions: false,
            time_h_evals: false,
            preferred_operators: false,
            partial_expansion: false,
            partial_expansion_min: 0,
            prune: PruneOptions::default(),
            max_queued: None,
            memory_limit_mb: None,
            deadline: None,
            memory_stop_mb: None,
        }
    }
}

impl ActionCost {
    /// Resolves a declared task cost under this command-line cost model.
    pub fn resolve(self, task_cost: usize) -> usize {
        match self {
            ActionCost::Task => task_cost,
            ActionCost::Unit => 1,
            ActionCost::Duration | ActionCost::Relative => task_cost,
        }
    }
}
