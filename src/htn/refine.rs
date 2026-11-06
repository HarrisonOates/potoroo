//! Flaw selection and lazy refinement choices, independent of queue policy.
//!
//! Decomposition may expose a supporter even when an existing supporter is
//! available: cf. Bercher et al., SoCS 2014, Algorithm 1. Here only primitive
//! occurrences support links; hybrid abstract interfaces are not implemented.
//! https://ojs.aaai.org/index.php/SOCS/article/view/18323
use std::time::Instant;

use super::model::{MethodId, Problem};
use super::plan::{Occurrence, OpenCondition, Plan};
use super::tdg::Tdg;
use crate::plan::INIT_ID;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum FlawSelection {
    /// Original baseline: fully decompose before resolving causal flaws.
    #[default]
    DecompositionFirst,
    /// Threats first, then the open condition with fewest possible refinements.
    Interleaved,
}

#[derive(Clone, Copy)]
pub(crate) enum Refinement {
    Decompose {
        parent: Occurrence,
        method: MethodId,
        for_support: bool,
    },
    Support(OpenCondition, usize),
    Order(usize, usize),
}

impl Refinement {
    pub(crate) fn apply(self, problem: &Problem, plan: &Plan) -> Result<Option<Plan>, String> {
        match self {
            Self::Decompose { parent, method, .. } => plan.decompose(problem, parent, method),
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
            }),
    )
}

fn support_choices<'a>(
    problem: &'a Problem,
    plan: &'a Plan,
    open: OpenCondition,
    tdg: Option<&'a Tdg>,
) -> Choices<'a> {
    let initial = problem
        .initial
        .binary_search(&open.fact)
        .is_ok()
        .then_some(Refinement::Support(open, INIT_ID));
    let existing = plan.tasks().filter_map(move |t| {
        (t.id != open.consumer
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
            !problem.tasks[t.task].primitive
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
    if selection == FlawSelection::DecompositionFirst {
        if let Some(parent) = compound {
            return Some(decompositions(problem, parent));
        }
    }
    if let Some(threat) = plan.threat(problem) {
        return Some(Box::new(
            [
                Refinement::Order(threat.step, threat.link.producer),
                Refinement::Order(threat.link.consumer, threat.step),
            ]
            .into_iter(),
        ));
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
        for _ in support_choices(problem, plan, open, tdg).take(fewest) {
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
        return Some(support_choices(problem, plan, open, tdg));
    }
    Some(match compound {
        Some(parent) => decompositions(problem, parent),
        None => Box::new(std::iter::empty()),
    })
}
