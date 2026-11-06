//! Persistent HTN partial plans. Compound occurrences are replaced atomically;
//! IDs are never reused within a branch. Retired ordering rows preserve closure.
use std::rc::Rc;

use crate::chain::{self, Chain};
use crate::orderings::{BinaryOrderings, Ordering, StepTime};
use crate::plan::{GOAL_ID, INIT_ID};

use super::model::{FactId, MethodId, Problem, TaskId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Occurrence {
    pub id: usize,
    pub task: TaskId,
}

#[derive(Clone, Debug)]
pub struct Decomposition {
    pub parent: Occurrence,
    pub method: MethodId,
    /// Child order is the method's storage order, not an execution order.
    pub children: Vec<Occurrence>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OpenCondition {
    pub consumer: usize,
    pub fact: FactId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Link {
    pub producer: usize,
    pub consumer: usize,
    pub fact: FactId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Threat {
    pub step: usize,
    pub link: Link,
}

/// While exposing a supporter, stay inside the chosen decomposition subtree.
/// Its immediate children are the only possible ancestors of that supporter.
#[derive(Clone, Debug)]
pub(crate) struct SupportFocus {
    pub open: OpenCondition,
    pub candidates: Vec<Occurrence>,
}

#[derive(Clone, Debug)]
pub struct Plan {
    pub(crate) tasks: Option<Rc<Chain<Occurrence>>>,
    pub(crate) orderings: Rc<BinaryOrderings>,
    pub(crate) links: Option<Rc<Chain<Link>>>,
    pub(crate) open: Option<Rc<Chain<OpenCondition>>>,
    pub(crate) history: Option<Rc<Chain<Decomposition>>>,
    pub(crate) support_focus: Option<Rc<SupportFocus>>,
    next_id: usize,
    pub(crate) cost: u64,
    pub(crate) depth: usize,
}

pub(crate) fn before(orderings: &BinaryOrderings, a: usize, b: usize) -> bool {
    a != b && !orderings.possibly_before(b, StepTime::AtStart, a, StepTime::AtStart)
}

fn edge(a: usize, b: usize) -> Ordering {
    Ordering::new(a, StepTime::AtEnd, b, StepTime::AtStart)
}

fn reserve(orderings: &Rc<BinaryOrderings>, id: usize) -> Rc<BinaryOrderings> {
    // Use a trivially consistent edge to grow the matrix; real edges go through
    // refine(), which checks for cycles. refine_with_step() alone does not.
    orderings.refine_with_step(edge(INIT_ID, id), id).unwrap()
}

impl Plan {
    pub(crate) fn initial(problem: &Problem) -> Self {
        let root = Occurrence {
            id: 1,
            task: problem.root,
        };
        let mut plan = Self {
            tasks: chain::cons(root, None),
            orderings: reserve(&Rc::new(BinaryOrderings::new()), root.id),
            links: None,
            open: None,
            history: None,
            support_focus: None,
            next_id: 2,
            cost: 0,
            depth: 0,
        };
        for &fact in &problem.goal {
            plan.open = chain::cons(
                OpenCondition {
                    consumer: GOAL_ID,
                    fact,
                },
                plan.open,
            );
        }
        if let Some(action) = problem.actions.get(root.task) {
            plan.cost = action.cost;
            for &fact in &action.preconditions {
                plan.open = chain::cons(
                    OpenCondition {
                        consumer: root.id,
                        fact,
                    },
                    plan.open,
                );
            }
        }
        plan
    }

    pub fn tasks(&self) -> impl Iterator<Item = &Occurrence> {
        chain::iter(&self.tasks)
    }
    pub fn links(&self) -> impl Iterator<Item = &Link> {
        chain::iter(&self.links)
    }
    pub fn open_conditions(&self) -> impl Iterator<Item = &OpenCondition> {
        chain::iter(&self.open)
    }
    pub fn decompositions(&self) -> impl Iterator<Item = &Decomposition> {
        chain::iter(&self.history)
    }
    pub fn cost(&self) -> u64 {
        self.cost
    }
    pub fn refinement_depth(&self) -> usize {
        self.depth
    }
    pub fn ordered_before(&self, a: usize, b: usize) -> bool {
        before(&self.orderings, a, b)
    }

    pub(crate) fn compound(&self, problem: &Problem) -> Option<Occurrence> {
        self.tasks()
            .copied()
            .find(|t| !problem.tasks[t.task].primitive)
    }

    pub(crate) fn decompose(
        &self,
        problem: &Problem,
        parent: Occurrence,
        method_id: MethodId,
    ) -> Result<Option<Self>, String> {
        let method = &problem.methods[method_id];
        debug_assert_eq!(method.task, parent.task);
        let next_id = self
            .next_id
            .checked_add(method.subtasks.len())
            .filter(|&id| id < GOAL_ID)
            .ok_or("HTN occurrence ID overflow")?;
        let children: Vec<_> = method
            .subtasks
            .iter()
            .enumerate()
            .map(|(i, &task)| Occurrence {
                id: self.next_id + i,
                task,
            })
            .collect();
        let mut child = self.clone();
        child.next_id = next_id;
        child.depth = self
            .depth
            .checked_add(1)
            .ok_or("HTN refinement depth overflow")?;
        child.tasks = chain::remove(&self.tasks, &parent);
        if let Some(last) = children.last() {
            child.orderings = reserve(&child.orderings, last.id);
        }
        for occurrence in &children {
            child.tasks = chain::cons(*occurrence, child.tasks);
            if let Some(action) = problem.actions.get(occurrence.task) {
                child.cost = child
                    .cost
                    .checked_add(action.cost)
                    .ok_or("HTN plan cost overflow")?;
                for &fact in &action.preconditions {
                    child.open = chain::cons(
                        OpenCondition {
                            consumer: occurrence.id,
                            fact,
                        },
                        child.open,
                    );
                }
            }
            // Inherit all implied external orderings, including paths through
            // previously removed empty tasks. Unordered siblings stay unordered.
            for other in self.tasks().filter(|t| t.id != parent.id) {
                let ordering = if before(&self.orderings, other.id, parent.id) {
                    Some(edge(other.id, occurrence.id))
                } else if before(&self.orderings, parent.id, other.id) {
                    Some(edge(occurrence.id, other.id))
                } else {
                    None
                };
                if let Some(ordering) = ordering {
                    let Some(orderings) = child.orderings.refine(ordering) else {
                        return Ok(None);
                    };
                    child.orderings = orderings;
                }
            }
        }
        for &(a, b) in &method.orderings {
            let Some(orderings) = child.orderings.refine(edge(children[a].id, children[b].id))
            else {
                return Ok(None);
            };
            child.orderings = orderings;
        }
        child.history = chain::cons(
            Decomposition {
                parent,
                method: method_id,
                children,
            },
            child.history,
        );
        Ok(Some(child))
    }

    pub(crate) fn support(&self, open: OpenCondition, producer: usize) -> Option<Self> {
        let orderings = self.orderings.refine(edge(producer, open.consumer))?;
        let mut child = self.clone();
        child.depth = self.depth.checked_add(1)?;
        child.orderings = orderings;
        child.open = chain::remove(&self.open, &open);
        debug_assert!(self.support_focus.as_ref().is_none_or(|f| f.open == open));
        child.support_focus = None;
        child.links = chain::cons(
            Link {
                producer,
                consumer: open.consumer,
                fact: open.fact,
            },
            child.links,
        );
        Some(child)
    }

    pub(crate) fn order(&self, a: usize, b: usize) -> Option<Self> {
        let orderings = self.orderings.refine(edge(a, b))?;
        let mut child = self.clone();
        child.depth = self.depth.checked_add(1)?;
        child.orderings = orderings;
        Some(child)
    }

    /// Recompute threats from actions and links. This baseline deliberately
    /// avoids an incremental flaw cache that could miss a batched insertion.
    /// With `last_achiever`, an intervening add also threatens the link: the
    /// producer must be the last achiever before the consumer (SNLP semantics).
    pub(crate) fn threat(&self, problem: &Problem, last_achiever: bool) -> Option<Threat> {
        for &link in self.links() {
            for occurrence in self.tasks() {
                let Some(action) = problem.actions.get(occurrence.task) else {
                    continue;
                };
                if occurrence.id != link.producer
                    && occurrence.id != link.consumer
                    && (action.delete.binary_search(&link.fact).is_ok()
                        || (last_achiever && action.add.binary_search(&link.fact).is_ok()))
                    && self.orderings.possibly_before(
                        link.producer,
                        StepTime::AtEnd,
                        occurrence.id,
                        StepTime::AtStart,
                    )
                    && self.orderings.possibly_before(
                        occurrence.id,
                        StepTime::AtEnd,
                        link.consumer,
                        StepTime::AtStart,
                    )
                {
                    return Some(Threat {
                        step: occurrence.id,
                        link,
                    });
                }
            }
        }
        None
    }

    pub(crate) fn linearization(&self) -> Vec<Occurrence> {
        let mut remaining: Vec<_> = self.tasks().copied().collect();
        remaining.sort_by_key(|t| t.id);
        let mut result = Vec::with_capacity(remaining.len());
        while !remaining.is_empty() {
            let i = remaining
                .iter()
                .position(|t| {
                    !remaining
                        .iter()
                        .any(|p| before(&self.orderings, p.id, t.id))
                })
                .expect("ordering engine maintains an acyclic partial order");
            result.push(remaining.remove(i));
        }
        result
    }
}
