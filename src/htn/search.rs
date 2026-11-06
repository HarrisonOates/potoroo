//! Queue policies over HTN refinements. The original breadth-first baseline
//! remains available; TDG A* orders by committed plus remaining primitive cost.
use std::cmp::Ordering;
use std::collections::{BinaryHeap, VecDeque};
use std::rc::Rc;
use std::time::Instant;

use super::model::Problem;
use super::plan::Plan;
use super::refine::{self, FlawSelection, Refinement};
use super::tdg::{Recompute, Tdg, TdgMode, COST_CAP};
use super::tdg_cache::BoundCache;
use super::validate::{self, Certificate};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum SearchStrategy {
    /// Fair breadth-first search over refinement depth, ignoring action cost.
    #[default]
    #[value(name = "bfs")]
    BreadthFirst,
    /// TDG g+h. A returned solution is optimal unless depth cutoffs occurred.
    #[value(name = "astar")]
    AStar,
    /// TDG h only; satisficing, with no optimality guarantee.
    #[value(name = "gbfs")]
    Greedy,
}

#[derive(Clone, Debug, Default)]
pub struct Config {
    /// Maximum generated nodes, including the initial node.
    pub node_limit: Option<usize>,
    /// Optional incomplete depth bound. Exhaustion after a cutoff is a limit.
    pub max_depth: Option<usize>,
    pub deadline: Option<Instant>,
    pub strategy: SearchStrategy,
    pub flaws: FlawSelection,
    pub tdg: TdgMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StopReason {
    NodeLimit,
    DepthLimit,
    Deadline,
}

#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub generated: usize,
    pub expanded: usize,
    pub decompositions: usize,
    /// Decompositions requested to expose a future causal supporter.
    pub support_decompositions: usize,
    pub causal_links: usize,
    pub threat_orderings: usize,
    pub tdg_pruned: usize,
    pub tdg_recomputed: usize,
    /// Lazy evaluations whose stronger bound required another queue insertion.
    pub tdg_requeued: usize,
    pub tdg_cache_hits: usize,
    pub cost_bound_pruned: usize,
    pub max_queued: usize,
}

#[derive(Debug)]
pub struct Solution {
    pub plan: Rc<Plan>,
    pub certificate: Certificate,
    pub cost: u64,
    pub cost_optimal: bool,
}

#[derive(Debug)]
pub enum Outcome {
    Solved(Solution),
    NoSolution,
    Stopped(StopReason),
}

#[derive(Debug)]
pub struct SearchResult {
    pub outcome: Outcome,
    pub stats: Stats,
}

struct Evaluator {
    index: Recompute,
    cache: Option<BoundCache>,
}

impl Evaluator {
    fn bound(
        &mut self,
        problem: &Problem,
        plan: &Plan,
        tdg: &Tdg,
        deadline: Option<Instant>,
        stats: &mut Stats,
    ) -> Option<Option<u128>> {
        let key = self.cache.as_ref().map(|_| BoundCache::key(plan));
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        if let (Some(cache), Some(key)) = (&self.cache, &key) {
            if let Some(bound) = cache.get(key) {
                stats.tdg_cache_hits += 1;
                return Some(bound);
            }
        }
        stats.tdg_recomputed += 1;
        let bound = self.index.remaining_cost(problem, plan, tdg, deadline)?;
        // Cancellation is not a bound and is never cached.
        if let (Some(cache), Some(key)) = (&mut self.cache, key) {
            cache.insert(key, bound);
        }
        Some(bound)
    }
}

struct Node {
    plan: Rc<Plan>,
    h: u128,
    pending_tdg: bool,
}

struct Queued {
    // Increasing serial number gives FIFO tie-breaking on equal priorities.
    key: (u128, usize),
    node: Node,
}
impl PartialEq for Queued {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}
impl Eq for Queued {}
impl PartialOrd for Queued {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Queued {
    fn cmp(&self, other: &Self) -> Ordering {
        other.key.cmp(&self.key)
    }
}

enum Frontier {
    Fifo(VecDeque<Node>),
    Guided(BinaryHeap<Queued>),
}
impl Frontier {
    fn push(&mut self, node: Node, strategy: SearchStrategy, serial: usize) {
        match self {
            Self::Fifo(q) => q.push_back(node),
            Self::Guided(q) => {
                let score = if strategy == SearchStrategy::AStar {
                    node.plan.cost() as u128 + node.h
                } else {
                    node.h
                };
                q.push(Queued {
                    key: (score, serial),
                    node,
                });
            }
        }
    }
    fn pop(&mut self) -> Option<(Node, usize)> {
        match self {
            Self::Fifo(q) => q.pop_front().map(|node| (node, 0)),
            Self::Guided(q) => q.pop().map(|entry| (entry.node, entry.key.1)),
        }
    }
    fn len(&self) -> usize {
        match self {
            Self::Fifo(q) => q.len(),
            Self::Guided(q) => q.len(),
        }
    }
}

/// Returns an error for internal/cost failures, never an unsolvability claim.
/// A*/GBFS can starve higher-cost solutions behind infinite recursive plateaus;
/// breadth-first remains the fair finite-solution baseline.
/// See also Yousefi et al., ICAPS 2025, on zero-cost recursive cycles in HTNs:
/// https://yousefi.ai/static/papers/Yousefi2025Incompleteness.pdf
pub fn search(problem: &Problem, config: &Config) -> Result<SearchResult, String> {
    let mut stats = Stats::default();
    let expired = || config.deadline.is_some_and(|d| Instant::now() >= d);
    if expired() {
        return Ok(SearchResult {
            outcome: Outcome::Stopped(StopReason::Deadline),
            stats,
        });
    }
    if config.node_limit == Some(0) {
        return Ok(SearchResult {
            outcome: Outcome::Stopped(StopReason::NodeLimit),
            stats,
        });
    }
    // The original decomposition-first BFS needs neither TDG preprocessing nor
    // effect summaries, making it a useful independent research baseline.
    let tdg = if config.flaws != FlawSelection::DecompositionFirst
        || config.strategy != SearchStrategy::BreadthFirst
        || config.tdg != TdgMode::Static
    {
        let Some(graph) = Tdg::with_deadline(problem, config.deadline) else {
            return Ok(SearchResult {
                outcome: Outcome::Stopped(StopReason::Deadline),
                stats,
            });
        };
        Some(graph)
    } else {
        None
    };
    let mut recompute = if config.tdg != TdgMode::Static {
        let Some(index) = Recompute::new(problem, config.deadline) else {
            return Ok(SearchResult {
                outcome: Outcome::Stopped(StopReason::Deadline),
                stats,
            });
        };
        Some(Evaluator {
            index,
            cache: (config.tdg == TdgMode::LazyCached).then(BoundCache::default),
        })
    } else {
        None
    };
    let mut queue = if config.strategy == SearchStrategy::BreadthFirst {
        Frontier::Fifo(VecDeque::new())
    } else {
        Frontier::Guided(BinaryHeap::new())
    };
    let initial = Rc::new(Plan::initial(problem));
    stats.generated = 1;
    let h = if let Some(index) = &mut recompute {
        let Some(bound) = index.bound(
            problem,
            &initial,
            tdg.as_ref().unwrap(),
            config.deadline,
            &mut stats,
        ) else {
            return Ok(SearchResult {
                outcome: Outcome::Stopped(StopReason::Deadline),
                stats,
            });
        };
        bound
    } else {
        tdg.as_ref()
            .map_or(Some(0), |g| g.remaining_cost(problem, &initial))
    };
    let Some(h) = h else {
        stats.tdg_pruned += 1;
        return Ok(SearchResult {
            outcome: Outcome::NoSolution,
            stats,
        });
    };
    if initial.cost() as u128 + h >= COST_CAP {
        return Err("HTN plan cost overflow: TDG lower bound exceeds u64".into());
    }
    queue.push(
        Node {
            plan: initial,
            h,
            pending_tdg: false,
        },
        config.strategy,
        0,
    );
    stats.max_queued = 1;
    let mut depth_cut = false;
    let mut cost_cut = false;
    while let Some((mut node, serial)) = queue.pop() {
        if expired() {
            return Ok(SearchResult {
                outcome: Outcome::Stopped(StopReason::Deadline),
                stats,
            });
        }
        if node.pending_tdg {
            let Some(bound) = recompute.as_mut().unwrap().bound(
                problem,
                &node.plan,
                tdg.as_ref().unwrap(),
                config.deadline,
                &mut stats,
            ) else {
                return Ok(SearchResult {
                    outcome: Outcome::Stopped(StopReason::Deadline),
                    stats,
                });
            };
            let Some(bound) = bound else {
                stats.tdg_pruned += 1;
                continue;
            };
            if node.plan.cost() as u128 + bound >= COST_CAP {
                stats.cost_bound_pruned += 1;
                cost_cut = true;
                continue;
            }
            let previous = node.h;
            node.h = node.h.max(bound);
            node.pending_tdg = false;
            // OPEN always carries admissible lower bounds. A strengthened
            // priority must compete again before expansion or accepting a goal.
            // Keep the original serial, so equal-priority FIFO ties are stable.
            // BFS does not order by h and must not lose its refinement-depth order.
            if node.h > previous && config.strategy != SearchStrategy::BreadthFirst {
                stats.tdg_requeued += 1;
                queue.push(node, config.strategy, serial);
                continue;
            }
        }
        let Node {
            plan, h: parent_h, ..
        } = node;
        stats.expanded += 1;
        if plan.compound(problem).is_none()
            && plan.open.is_none()
            && plan.support_focus.is_none()
            && plan
                .threat(problem, config.flaws == FlawSelection::Systematic)
                .is_none()
        {
            let certificate = Certificate {
                root: 1,
                steps: plan.linearization(),
                decompositions: plan.decompositions().cloned().collect(),
            };
            let cost = validate::validate(problem, &certificate)
                .map_err(|e| format!("HTN solution failed independent validation: {e}"))?;
            if cost != plan.cost() {
                return Err("HTN committed cost disagrees with certificate".into());
            }
            return Ok(SearchResult {
                outcome: Outcome::Solved(Solution {
                    plan,
                    certificate,
                    cost,
                    cost_optimal: config.strategy == SearchStrategy::AStar && !depth_cut,
                }),
                stats,
            });
        }
        let Some(choices) =
            refine::choices(problem, &plan, config.flaws, tdg.as_ref(), config.deadline)
        else {
            return Ok(SearchResult {
                outcome: Outcome::Stopped(StopReason::Deadline),
                stats,
            });
        };
        for refinement in choices {
            if expired() {
                return Ok(SearchResult {
                    outcome: Outcome::Stopped(StopReason::Deadline),
                    stats,
                });
            }
            if let (Some(graph), Refinement::Decompose { parent, method, .. }) = (&tdg, refinement)
            {
                match graph.replacement_cost(problem, &plan, parent, method) {
                    None => {
                        stats.tdg_pruned += 1;
                        continue;
                    }
                    Some(cost) if cost >= COST_CAP => {
                        // These branches cannot beat a representable solution.
                        // If all search fails, report an error, not unsolvability.
                        stats.cost_bound_pruned += 1;
                        cost_cut = true;
                        continue;
                    }
                    _ => {}
                }
            }
            let Some(child) = refinement.apply(problem, &plan)? else {
                continue;
            };
            if config.max_depth.is_some_and(|d| child.depth > d) {
                depth_cut = true;
                continue;
            }
            if config.node_limit.is_some_and(|n| stats.generated >= n) {
                return Ok(SearchResult {
                    outcome: Outcome::Stopped(StopReason::NodeLimit),
                    stats,
                });
            }
            let mut pending_tdg = false;
            let h = if let Refinement::Decompose { parent, .. } = refinement {
                if let Some(index) = &mut recompute {
                    if problem.methods_by_task[parent.task].len() == 1 {
                        // The only method preserves the set of descendant actions.
                        // Its new primitive costs move from h into g (IJCAI 2017, §5.1).
                        parent_h
                            .checked_sub((child.cost() - plan.cost()) as u128)
                            .expect("single-method refinement preserves the relaxed total cost")
                    } else if matches!(config.tdg, TdgMode::Lazy | TdgMode::LazyCached) {
                        pending_tdg = true;
                        let structural = tdg
                            .as_ref()
                            .unwrap()
                            .remaining_cost(problem, &child)
                            .expect("productive method was checked before refinement");
                        // Any completion of the child also completes the parent.
                        // Preserve that total-cost lower bound while primitive
                        // costs move into g; never use an unchecked estimate as exact.
                        structural
                            .max(parent_h.saturating_sub((child.cost() - plan.cost()) as u128))
                    } else {
                        let Some(bound) = index.bound(
                            problem,
                            &child,
                            tdg.as_ref().unwrap(),
                            config.deadline,
                            &mut stats,
                        ) else {
                            return Ok(SearchResult {
                                outcome: Outcome::Stopped(StopReason::Deadline),
                                stats,
                            });
                        };
                        let Some(bound) = bound else {
                            stats.tdg_pruned += 1;
                            continue;
                        };
                        bound
                    }
                } else {
                    tdg.as_ref().map_or(0, |g| {
                        g.remaining_cost(problem, &child)
                            .expect("productive method was checked before refinement")
                    })
                }
            } else {
                // Links and ordering constraints do not change active tasks.
                parent_h
            };
            if child.cost() as u128 + h >= COST_CAP {
                stats.cost_bound_pruned += 1;
                cost_cut = true;
                continue;
            }
            stats.generated += 1;
            match refinement {
                Refinement::Decompose { for_support, .. } => {
                    stats.decompositions += 1;
                    stats.support_decompositions += usize::from(for_support);
                }
                Refinement::Support(..) => stats.causal_links += 1,
                Refinement::Order(..) => stats.threat_orderings += 1,
            }
            queue.push(
                Node {
                    plan: Rc::new(child),
                    h,
                    pending_tdg,
                },
                config.strategy,
                stats.generated,
            );
            stats.max_queued = stats.max_queued.max(queue.len());
        }
    }
    if cost_cut && !depth_cut {
        return Err("HTN plan cost overflow: unexplored decompositions exceed u64".into());
    }
    Ok(SearchResult {
        outcome: if depth_cut {
            Outcome::Stopped(StopReason::DepthLimit)
        } else {
            Outcome::NoSolution
        },
        stats,
    })
}
