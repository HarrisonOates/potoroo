//! Additional read-only measurements, requiring both diagnostic environment
//! switches. Each selected open belongs to exactly one bit-mask bucket; named
//! types overlap. Forced clobbers are conservative (unconditional effects only).
use super::*;
use std::collections::BTreeMap;

const LOCAL: u8 = 1;
const UNSAFE: u8 = 2;
const INITIAL: u8 = 4;
const GOAL: u8 = 8;
const STATIC: u8 = 16;
const BLOCKED_INITIAL: u8 = 32;
const REUSE: u8 = 64;
const BLOCKED_REUSE: u8 = 128;

#[derive(Default)]
struct Counts {
    selected: usize,
    children: usize,
    insertions: usize,
}

#[derive(Default)]
pub(super) struct FlawTypes {
    opens: BTreeMap<u8, Counts>,
    // (ordering/confrontation candidate count, has confrontation).
    threats: BTreeMap<(i32, bool), Counts>,
    disjunctions: usize,
}

fn open_mask(planner: &Planner<'_>, plan: &PartialPlan, open: &OpenCondition) -> u8 {
    let mut mask = 0;
    if plan
        .open_conditions()
        .next()
        .is_some_and(|o| o.consumer == open.consumer)
    {
        mask |= LOCAL;
    }
    if planner.unsafe_open_condition(plan, open) {
        mask |= UNSAFE;
    }
    if planner.task.initial[open.condition.variable] == open.condition.value {
        mask |= INITIAL;
    }
    if open.consumer == GOAL_ID {
        mask |= GOAL;
    }
    if !planner.variable_has_effect[open.condition.variable] {
        mask |= STATIC;
    }
    // A forced intervening unconditional deletion prevents a classical link
    // from that producer, even when another existing or future step restores
    // the fact. A consumer's own post-effects occur after its preconditions.
    let clobbers: Vec<_> = plan
        .steps()
        .filter(|step| {
            is_ordered_before(&plan.orderings, step.id, open.consumer)
                && planner.task.operators[step.operator]
                    .effects
                    .iter()
                    .enumerate()
                    .any(|(i, e)| {
                        e.conditions.is_empty()
                            && !plan.effect_suppressed(step.id, i)
                            && effect_clobbers(e.variable, e.post, open.condition)
                    })
        })
        .map(|step| step.id)
        .collect();
    if mask & INITIAL != 0 && !clobbers.is_empty() {
        mask |= BLOCKED_INITIAL;
    }
    // Mirror FFR's matching-producer/possible-order test. FFR itself rejects
    // conditional effects and axioms; interpret these reuse bins in that scope.
    let mut viable_reuse = false;
    for producer in plan.steps().filter(|step| {
        plan.orderings
            .possibly_before(step.id, StepTime::AtEnd, open.consumer, StepTime::AtStart)
            && planner.task.operators[step.operator]
                .effects
                .iter()
                .any(|e| e.assignment() == open.condition)
    }) {
        mask |= REUSE;
        if !clobbers
            .iter()
            .any(|&deleter| is_ordered_before(&plan.orderings, producer.id, deleter))
        {
            viable_reuse = true;
        }
    }
    if mask & REUSE != 0 && !viable_reuse {
        mask |= BLOCKED_REUSE;
    }
    mask
}

impl FlawTypes {
    pub(super) fn observe(
        &mut self,
        planner: &Planner<'_>,
        plan: &PartialPlan,
        flaw: &SelectedFlaw,
        children: &[PartialPlan],
    ) {
        let counts = match flaw {
            SelectedFlaw::Open(open) => self
                .opens
                .entry(open_mask(planner, plan, open))
                .or_default(),
            SelectedFlaw::Threat(threat) => {
                let confrontations = planner.confrontations(plan, threat).len();
                let repairs = planner.threat_refinement_count(plan, threat, confrontations);
                self.threats
                    .entry((repairs, confrontations > 0))
                    .or_default()
            }
            SelectedFlaw::Disjunction(_) => {
                self.disjunctions += 1;
                return;
            }
        };
        counts.selected += 1;
        counts.children += children.len();
        counts.insertions += children
            .iter()
            .filter(|child| child.num_steps() > plan.num_steps())
            .count();
    }

    pub(super) fn emit(&self) {
        eprintln!("FDR_DIAGNOSTIC_FLAW_TYPES {{\"version\":1,\"local\":1,\"unsafe\":2,\"initial\":4,\"goal\":8,\"static\":16,\"blocked_initial\":32,\"reuse\":64,\"blocked_reuse\":128,\"disjunctions\":{}}}", self.disjunctions);
        for (mask, counts) in &self.opens {
            eprintln!("FDR_DIAGNOSTIC_OPEN_TYPE {{\"mask\":{},\"selected\":{},\"children\":{},\"insertions\":{}}}", mask, counts.selected, counts.children, counts.insertions);
        }
        for ((repairs, confrontable), counts) in &self.threats {
            eprintln!("FDR_DIAGNOSTIC_THREAT_TYPE {{\"repairs\":{},\"confrontable\":{},\"selected\":{},\"children\":{}}}", repairs, confrontable, counts.selected, counts.children);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fdr::{Effect, Operator, Variable};
    use crate::heuristics::FlawSelectionOrder;

    fn fixture() -> (Task, PartialPlan) {
        let assign = |post| Effect {
            conditions: vec![],
            variable: 0,
            pre: None,
            post,
        };
        let task = Task {
            variables: vec![
                Variable {
                    name: "x".into(),
                    values: vec!["off".into(), "on".into()],
                },
                Variable {
                    name: "static".into(),
                    values: vec!["off".into(), "on".into()],
                },
            ],
            initial: vec![1, 1],
            goals: vec![Fact::new(0, 1)],
            mutex_groups: vec![],
            axioms: vec![],
            operators: vec![
                Operator {
                    name: "restore".into(),
                    prevail: vec![],
                    effects: vec![assign(1)],
                    cost: 1,
                },
                Operator {
                    name: "delete".into(),
                    prevail: vec![],
                    effects: vec![assign(0)],
                    cost: 1,
                },
                Operator {
                    name: "read".into(),
                    prevail: vec![Fact::new(0, 1)],
                    effects: vec![],
                    cost: 1,
                },
                Operator {
                    name: "static-read".into(),
                    prevail: vec![Fact::new(1, 1)],
                    effects: vec![],
                    cost: 1,
                },
            ],
        };
        let mut orders = Rc::new(BinaryOrderings::new());
        for id in 1..=4 {
            orders = orders
                .refine_with_step(
                    Ordering::new(id, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                    id,
                )
                .unwrap();
        }
        let plan = PartialPlan::assemble(
            (1..=4)
                .map(|id| Step {
                    id,
                    operator: id - 1,
                })
                .collect(),
            vec![],
            vec![
                OpenCondition {
                    consumer: GOAL_ID,
                    condition: Fact::new(0, 1),
                },
                OpenCondition {
                    consumer: 3,
                    condition: Fact::new(0, 1),
                },
                OpenCondition {
                    consumer: 4,
                    condition: Fact::new(1, 1),
                },
            ],
            orders,
            vec![],
            4,
            5,
        );
        (task, plan)
    }

    #[test]
    fn diagnostic_types_distinguish_possible_and_forced_clobbers() {
        let (task, mut plan) = fixture();
        let planner = Planner::new(&task);
        let open = OpenCondition {
            consumer: 3,
            condition: Fact::new(0, 1),
        };
        assert_eq!(open_mask(&planner, &plan, &open), INITIAL | UNSAFE | REUSE);
        plan.orderings = plan
            .orderings
            .refine(Ordering::new(2, StepTime::AtEnd, 3, StepTime::AtStart))
            .unwrap();
        // Reuse is still possible by putting the restorer after the deleter.
        assert_eq!(
            open_mask(&planner, &plan, &open),
            INITIAL | UNSAFE | REUSE | BLOCKED_INITIAL
        );
        plan.orderings = plan
            .orderings
            .refine(Ordering::new(1, StepTime::AtEnd, 2, StepTime::AtStart))
            .unwrap();
        assert_eq!(
            open_mask(&planner, &plan, &open),
            INITIAL | UNSAFE | REUSE | BLOCKED_INITIAL | BLOCKED_REUSE
        );
        plan.orderings = plan
            .orderings
            .refine_with_step(Ordering::new(5, StepTime::AtEnd, 3, StepTime::AtStart), 5)
            .unwrap();
        plan.orderings = plan
            .orderings
            .refine(Ordering::new(2, StepTime::AtEnd, 5, StepTime::AtStart))
            .unwrap();
        plan.push_step(Step { id: 5, operator: 0 });
        assert_eq!(
            open_mask(&planner, &plan, &open),
            INITIAL | UNSAFE | REUSE | BLOCKED_INITIAL
        );
        // INIT's link remains blocked even though a later producer can support it.
        let static_open = plan.open_conditions().next().unwrap();
        assert_eq!(
            open_mask(&planner, &plan, static_open),
            LOCAL | INITIAL | STATIC
        );
    }

    #[test]
    fn diagnostic_types_exclude_conditional_deletions_and_consumer_post_effects() {
        let (mut task, mut plan) = fixture();
        let open = OpenCondition {
            consumer: 3,
            condition: Fact::new(0, 1),
        };
        plan.orderings = plan
            .orderings
            .refine(Ordering::new(2, StepTime::AtEnd, 3, StepTime::AtStart))
            .unwrap();
        task.operators[1].effects[0]
            .conditions
            .push(Fact::new(1, 1));
        let planner = Planner::new(&task);
        assert_eq!(open_mask(&planner, &plan, &open) & BLOCKED_INITIAL, 0);
        drop(planner);
        task.operators[1].effects.clear();
        task.operators[2].effects.push(Effect {
            conditions: vec![],
            variable: 0,
            pre: None,
            post: 0,
        });
        let planner = Planner::new(&task);
        assert_eq!(
            open_mask(&planner, &plan, &open) & (UNSAFE | BLOCKED_INITIAL),
            0
        );
        let goal = OpenCondition {
            consumer: GOAL_ID,
            condition: Fact::new(0, 1),
        };
        assert_eq!(
            open_mask(&planner, &plan, &goal) & (GOAL | BLOCKED_INITIAL),
            GOAL | BLOCKED_INITIAL
        );
    }

    #[test]
    fn conflict_priority_can_override_local_focus_and_counts_partition_opens() {
        let (task, plan) = fixture();
        let planner = Planner::new(&task);
        let mut types = FlawTypes::default();
        for (order, consumer) in [
            ("LCFR", 4),
            ("LCFR-Loc", 4),
            ("LCFR-Conf", 3),
            ("LCFR-Loc-Conf", 3),
        ] {
            let flaw = planner.select_flaw(&plan, &FlawSelectionOrder::parse(order).unwrap());
            let SelectedFlaw::Open(open) = &flaw else {
                panic!("expected open condition")
            };
            assert_eq!(open.consumer, consumer, "{order}");
            types.observe(&planner, &plan, &flaw, std::slice::from_ref(&plan));
        }
        assert_eq!(types.opens.values().map(|c| c.selected).sum::<usize>(), 4);
        assert_eq!(types.opens.values().map(|c| c.children).sum::<usize>(), 4);
        assert_eq!(types.opens[&(LOCAL | INITIAL | STATIC)].selected, 2);
        assert_eq!(types.opens[&(UNSAFE | INITIAL | REUSE)].selected, 2);
        assert!(types.threats.is_empty());
    }
}
