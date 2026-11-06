//! Flaw selection and lazy refinement choices, independent of queue policy.
//!
//! Decomposition may expose a supporter even when an existing supporter is
//! available: cf. Bercher et al., SoCS 2014, Algorithm 1. Here only primitive
//! occurrences support links; hybrid abstract interfaces are not implemented.
//! https://ojs.aaai.org/index.php/SOCS/article/view/18323
//!
//! `Systematic` partitions witnesses identified by method IDs, child-slot paths,
//! and the execution order of primitive occurrences. When decomposition is used
//! to expose a supporter, the selected open condition stays focused on that
//! subtree until a primitive link is made. New preconditions wait; threats may
//! be repaired meanwhile. Without this commitment, different branches can
//! decompose the same tasks and then select a supporter from elsewhere.
//!
//! Links additionally require their producer to be the last achiever: both
//! adds and deletes threaten a link, following SNLP (McAllester/Rosenblitt 1991):
//! https://cdn.aaai.org/AAAI/1991/AAAI91-099.pdf
//! For a fixed executable witness, each open condition has one last achiever.
//! It is either present or lies below one active compound, fixing the support
//! branch and each method along its path. Threat repairs place an occurrence
//! before the producer or after the consumer, two disjoint execution cases.
//! Ordinary decomposition selects one compound and branches over its methods.
//! Thus sibling branches have disjoint witness sets; each valid witness retains
//! a branch. Primitive costs and the admissible TDG relaxation are unchanged.
//!
//! This is an occurrence-preserving adaptation, not PANDA's progression rule
//! or isomorphism-based symmetry reduction. Distinct method IDs and repeated
//! child slots remain distinct witnesses. See Hoeller et al. (2020), section
//! 4.2.3, for the distinction between search redundancy and model symmetry:
//! https://bercher.net/publications/2020/Hoeller2020HTNProgressionSearch.pdf
//! Systematicity does not make A*/GBFS fair on infinite recursive plateaus.
use std::rc::Rc;
use std::time::Instant;

use super::model::{MethodId, Problem};
use super::plan::{Occurrence, OpenCondition, Plan, SupportFocus};
use super::tdg::Tdg;
use crate::plan::INIT_ID;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum FlawSelection {
    /// Original baseline: fully decompose before resolving causal flaws.
    DecompositionFirst,
    /// Threats first, then the open condition with fewest possible refinements.
    Interleaved,
    /// Interleaved refinement with subtree support commitments and last-achiever links.
    #[default]
    Systematic,
}

#[derive(Clone, Copy)]
pub(crate) enum Refinement {
    Decompose {
        parent: Occurrence,
        method: MethodId,
        for_support: bool,
        focus: Option<OpenCondition>,
    },
    Support(OpenCondition, usize),
    Order(usize, usize),
}

impl Refinement {
    pub(crate) fn apply(self, problem: &Problem, plan: &Plan) -> Result<Option<Plan>, String> {
        match self {
            Self::Decompose {
                parent,
                method,
                focus,
                ..
            } => {
                let Some(mut child) = plan.decompose(problem, parent, method)? else {
                    return Ok(None);
                };
                if let Some(open) = focus {
                    debug_assert!(plan
                        .support_focus
                        .as_ref()
                        .is_none_or(|f| { f.open == open && f.candidates.contains(&parent) }));
                    let candidates = child.history.as_ref().unwrap().head.children.clone();
                    child.support_focus = Some(Rc::new(SupportFocus { open, candidates }));
                }
                Ok(Some(child))
            }
            Self::Support(open, producer) => Ok(plan.support(open, producer)),
            Self::Order(a, b) => Ok(plan.order(a, b)),
        }
    }
}

type Choices<'a> = Box<dyn Iterator<Item = Refinement> + 'a>;

fn decompositions(problem: &Problem, parent: Occurrence) -> Choices<'_> {
    Box::new(
        problem.methods_by_task[parent.task]
            .iter()
            .copied()
            .map(move |method| Refinement::Decompose {
                parent,
                method,
                for_support: false,
                focus: None,
            }),
    )
}

fn support_choices<'a>(
    problem: &'a Problem,
    plan: &'a Plan,
    open: OpenCondition,
    tdg: Option<&'a Tdg>,
    systematic: bool,
) -> Choices<'a> {
    let eligible = move |t: &Occurrence| {
        plan.support_focus
            .as_ref()
            .is_none_or(|focus| focus.candidates.contains(t))
    };
    let initial = (plan.support_focus.is_none()
        && problem.initial.binary_search(&open.fact).is_ok())
    .then_some(Refinement::Support(open, INIT_ID));
    let existing = plan.tasks().filter_map(move |t| {
        (eligible(t)
            && t.id != open.consumer
            && !plan.ordered_before(open.consumer, t.id)
            && problem
                .actions
                .get(t.task)
                .is_some_and(|a| a.add.binary_search(&open.fact).is_ok()))
        .then_some(Refinement::Support(open, t.id))
    });
    let future = plan
        .tasks()
        .filter(move |t| {
            eligible(t)
                && !problem.tasks[t.task].primitive
                && !plan.ordered_before(open.consumer, t.id)
                && tdg.is_some_and(|g| g.may_add(t.task, open.fact))
        })
        .flat_map(move |&parent| {
            problem.methods_by_task[parent.task]
                .iter()
                .copied()
                .filter(move |&m| tdg.is_some_and(|g| g.method_may_add(problem, m, open.fact)))
                .map(move |method| Refinement::Decompose {
                    parent,
                    method,
                    for_support: true,
                    focus: systematic.then_some(open),
                })
        });
    Box::new(initial.into_iter().chain(existing).chain(future))
}

/// `None` means deadline; an empty iterator is a dead end. Future support
/// branches leave the open condition unresolved until a primitive is available.
pub(crate) fn choices<'a>(
    problem: &'a Problem,
    plan: &'a Plan,
    selection: FlawSelection,
    tdg: Option<&'a Tdg>,
    deadline: Option<Instant>,
) -> Option<Choices<'a>> {
    let compound = plan.compound(problem);
    let systematic = selection == FlawSelection::Systematic;
    if selection == FlawSelection::DecompositionFirst {
        if let Some(parent) = compound {
            return Some(decompositions(problem, parent));
        }
    }
    if let Some(threat) = plan.threat(problem, systematic) {
        return Some(Box::new(
            [
                Refinement::Order(threat.step, threat.link.producer),
                Refinement::Order(threat.link.consumer, threat.step),
            ]
            .into_iter(),
        ));
    }
    if let Some(focus) = &plan.support_focus {
        debug_assert!(systematic);
        // Selecting another flaw here could decompose unrelated subtrees and
        // undo the partition established by the support choice.
        return Some(support_choices(problem, plan, focus.open, tdg, systematic));
    }
    let mut selected = None;
    let mut fewest = usize::MAX;
    for &open in plan.open_conditions() {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        if selection == FlawSelection::DecompositionFirst {
            selected = Some(open);
            break;
        }
        let mut count = 0;
        for _ in support_choices(problem, plan, open, tdg, systematic).take(fewest) {
            if deadline.is_some_and(|d| Instant::now() >= d) {
                return None;
            }
            count += 1;
        }
        if count < fewest {
            selected = Some(open);
            fewest = count;
        }
        if count == 0 {
            break;
        }
    }
    if let Some(open) = selected {
        return Some(support_choices(problem, plan, open, tdg, systematic));
    }
    Some(match compound {
        Some(parent) => decompositions(problem, parent),
        None => Box::new(std::iter::empty()),
    })
}
