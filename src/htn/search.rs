//! A fair breadth-first baseline over refinement depth. Every method application,
//! causal link, and threat ordering counts as one refinement, including empty
//! decompositions. This is a satisficing search, not action-cost optimisation.
use std::collections::VecDeque;
use std::rc::Rc;
use std::time::Instant;

use super::model::Problem;
use super::plan::Plan;
use super::validate::{self, Certificate};
use crate::plan::INIT_ID;

#[derive(Clone, Debug, Default)]
pub struct Config {
    /// Maximum generated nodes, including the initial node.
    pub node_limit: Option<usize>,
    /// Optional incomplete depth bound. Exhaustion after a cutoff is a limit.
    pub max_depth: Option<usize>,
    pub deadline: Option<Instant>,
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
    pub causal_links: usize,
    pub threat_orderings: usize,
    pub max_queued: usize,
}

#[derive(Debug)]
pub struct Solution {
    pub plan: Rc<Plan>,
    pub certificate: Certificate,
    pub cost: u64,
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

#[derive(Clone, Copy)]
enum Refinement {
    Decomposition,
    Link,
    Ordering,
}

/// Returns an error for internal/cost failures, never an unsolvability claim.
pub fn search(problem: &Problem, config: &Config) -> Result<SearchResult, String> {
    let mut stats = Stats::default();
    if config.deadline.is_some_and(|d| Instant::now() >= d) {
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
    let mut queue = VecDeque::from([Rc::new(Plan::initial(problem))]);
    stats.generated = 1;
    stats.max_queued = 1;
    let mut depth_cut = false;
    while let Some(plan) = queue.pop_front() {
        if config.deadline.is_some_and(|d| Instant::now() >= d) {
            return Ok(SearchResult {
                outcome: Outcome::Stopped(StopReason::Deadline),
                stats,
            });
        }
        stats.expanded += 1;
        let compound = plan.compound(problem);
        let threat = plan.threat(problem);
        if compound.is_none() && threat.is_none() && plan.open.is_none() {
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
                }),
                stats,
            });
        }
        let mut stopped = None;
        // Streaming successors allow limits to interrupt a wide method choice.
        let mut emit = |child: Plan, kind: Refinement| -> bool {
            if config.deadline.is_some_and(|d| Instant::now() >= d) {
                stopped = Some(StopReason::Deadline);
                return false;
            }
            if config.max_depth.is_some_and(|d| child.depth > d) {
                depth_cut = true;
                return true;
            }
            if config.node_limit.is_some_and(|n| stats.generated >= n) {
                stopped = Some(StopReason::NodeLimit);
                return false;
            }
            stats.generated += 1;
            match kind {
                Refinement::Decomposition => stats.decompositions += 1,
                Refinement::Link => stats.causal_links += 1,
                Refinement::Ordering => stats.threat_orderings += 1,
            }
            queue.push_back(Rc::new(child));
            stats.max_queued = stats.max_queued.max(queue.len());
            true
        };
        if let Some(parent) = compound {
            for &method in &problem.methods_by_task[parent.task] {
                if let Some(child) = plan.decompose(problem, parent, method)? {
                    if !emit(child, Refinement::Decomposition) {
                        break;
                    }
                }
            }
        } else if let Some(threat) = threat {
            for (a, b) in [
                (threat.step, threat.link.producer),
                (threat.link.consumer, threat.step),
            ] {
                if let Some(child) = plan.order(a, b) {
                    if !emit(child, Refinement::Ordering) {
                        break;
                    }
                }
            }
        } else if let Some(open) = plan.open_conditions().next().copied() {
            let initial = problem
                .initial
                .binary_search(&open.fact)
                .is_ok()
                .then_some(INIT_ID);
            let supporters = plan
                .tasks()
                .filter(|t| {
                    problem.actions[t.task]
                        .add
                        .binary_search(&open.fact)
                        .is_ok()
                })
                .map(|t| t.id);
            for producer in initial.into_iter().chain(supporters) {
                if let Some(child) = plan.support(open, producer) {
                    if !emit(child, Refinement::Link) {
                        break;
                    }
                }
            }
        }
        if let Some(reason) = stopped {
            return Ok(SearchResult {
                outcome: Outcome::Stopped(reason),
                stats,
            });
        }
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
