//! Read-only search measurements, enabled by POTOROO_FDR_DIAGNOSTICS=1.
//! Counts describe expanded partial plans and children before pruning. Expensive
//! structure measurements use the first expansion and every 1024th thereafter,
//! at most 256 samples. Timing experiments should leave this disabled.
use super::*;

#[derive(Default)]
struct ConditionCounts {
    open_expansions: usize,
    open_children: usize,
    insertion_children: usize,
    goal_opens: usize,
    threat_expansions: usize,
    threat_children: usize,
    initial_link_threats: usize,
}

#[derive(Default)]
pub(super) struct Diagnostic {
    operators: usize,
    variables: usize,
    expanded: usize,
    open_expansions: usize,
    threat_expansions: usize,
    disjunction_expansions: usize,
    open_children: usize,
    threat_children: usize,
    open_sum: usize,
    threat_sum: usize,
    samples: usize,
    sample_steps: usize,
    repeated_steps: usize,
    pairs: usize,
    ordered_pairs: usize,
    structure_skipped: usize,
    insertion_children: usize,
    insertion_new_threats: usize,
    wk_checked: usize,
    wk_restored: usize,
    conditions: std::collections::BTreeMap<(usize, usize), ConditionCounts>,
    types: Option<super::flaw_type_diagnostic::FlawTypes>,
}

impl Diagnostic {
    pub(super) fn from_env(task: &Task) -> Option<Self> {
        (std::env::var_os("POTOROO_FDR_DIAGNOSTICS").as_deref() == Some(std::ffi::OsStr::new("1")))
            .then(|| {
                // Struct-update syntax would drop its temporary Default value
                // and emit an extra empty record because this type has Drop.
                let mut diagnostic = Self::default();
                diagnostic.operators = task.operators.len();
                diagnostic.variables = task.variables.len();
                if std::env::var_os("POTOROO_FDR_FLAW_TYPES").as_deref()
                    == Some(std::ffi::OsStr::new("1"))
                {
                    diagnostic.types = Some(Default::default());
                }
                diagnostic
            })
    }

    pub(super) fn observe(
        &mut self,
        planner: &Planner<'_>,
        plan: &PartialPlan,
        flaw: &SelectedFlaw,
        children: &[PartialPlan],
    ) {
        let task = planner.task;
        if let Some(types) = &mut self.types {
            types.observe(planner, plan, flaw, children);
        }
        self.expanded += 1;
        self.open_sum += plan.num_open_conditions();
        self.threat_sum += plan.threats.len();
        match flaw {
            SelectedFlaw::Open(open) => {
                self.open_expansions += 1;
                self.open_children += children.len();
                let counts = self
                    .conditions
                    .entry((open.condition.variable, open.condition.value))
                    .or_default();
                counts.open_expansions += 1;
                counts.open_children += children.len();
                counts.insertion_children += children
                    .iter()
                    .filter(|child| child.num_steps() > plan.num_steps())
                    .count();
                counts.goal_opens += usize::from(open.consumer == GOAL_ID);
            }
            SelectedFlaw::Threat(threat) => {
                self.threat_expansions += 1;
                self.threat_children += children.len();
                let link = plan.threatened_link(threat);
                let counts = self
                    .conditions
                    .entry((link.condition.variable, link.condition.value))
                    .or_default();
                counts.threat_expansions += 1;
                counts.threat_children += children.len();
                counts.initial_link_threats += usize::from(link.producer == INIT_ID);
            }
            SelectedFlaw::Disjunction(_) => self.disjunction_expansions += 1,
        }
        if self.samples >= 256 || !(self.expanded - 1).is_multiple_of(1024) {
            return;
        }
        self.samples += 1;
        let steps: Vec<_> = plan.steps().collect();
        self.sample_steps += steps.len();
        self.repeated_steps += steps.len()
            - steps
                .iter()
                .map(|s| s.operator)
                .collect::<FastSet<_>>()
                .len();
        // Bound quadratic observation work on deep failed searches. The count
        // of omitted samples is emitted; no omitted plan is treated as zero.
        if steps.len() > 256 || plan.threats.len() > 256 {
            self.structure_skipped += 1;
            return;
        }
        for (i, a) in steps.iter().enumerate() {
            for b in &steps[..i] {
                self.pairs += 1;
                self.ordered_pairs += usize::from(
                    is_ordered_before(&plan.orderings, a.id, b.id)
                        || is_ordered_before(&plan.orderings, b.id, a.id),
                );
            }
        }
        let old: FastSet<_> = plan.threats.iter().copied().collect();
        for child in children.iter().filter(|c| c.num_steps() > plan.num_steps()) {
            self.insertion_children += 1;
            self.insertion_new_threats +=
                child.threats.iter().filter(|t| !old.contains(*t)).count();
        }
        // A diagnostic opportunity only: search retains classical POCL threat
        // semantics. Count unconditional existing restorers forced after the
        // deleter and before the consumer. Conditional restorers are excluded.
        for threat in plan.threats.iter().filter(|t| t.effect != NO_EFFECT) {
            self.wk_checked += 1;
            self.wk_restored += usize::from(has_forced_restorer(task, plan, threat));
        }
    }
}

fn has_forced_restorer(task: &Task, plan: &PartialPlan, threat: &Threat) -> bool {
    let link = plan.threatened_link(threat);
    plan.steps().any(|s| {
        is_ordered_before(&plan.orderings, threat.step, s.id)
            && is_ordered_before(&plan.orderings, s.id, link.consumer)
            && task.operators[s.operator]
                .effects
                .iter()
                .enumerate()
                .any(|(i, e)| {
                    e.variable == link.condition.variable
                        && e.post == link.condition.value
                        && e.conditions.is_empty()
                        && !plan.effect_suppressed(s.id, i)
                })
    })
}

impl Drop for Diagnostic {
    fn drop(&mut self) {
        // Separate from STATS: one record per search stage, including early
        // returns. Integer totals let consumers choose the correct denominator.
        eprintln!(concat!("FDR_DIAGNOSTIC {{\"operators\":{},\"variables\":{},\"expanded\":{},",
            "\"open_expansions\":{},\"threat_expansions\":{},\"disjunction_expansions\":{},",
            "\"open_children\":{},\"threat_children\":{},\"open_sum\":{},\"threat_sum\":{},",
            "\"samples\":{},\"sample_steps\":{},\"repeated_steps\":{},\"pairs\":{},\"ordered_pairs\":{},",
            "\"structure_skipped\":{},\"insertion_children\":{},\"insertion_new_threats\":{},",
            "\"wk_checked\":{},\"wk_restored\":{}}}"),
            self.operators,self.variables,self.expanded,self.open_expansions,self.threat_expansions,
            self.disjunction_expansions,self.open_children,self.threat_children,self.open_sum,self.threat_sum,
            self.samples,self.sample_steps,self.repeated_steps,self.pairs,self.ordered_pairs,
            self.structure_skipped,self.insertion_children,self.insertion_new_threats,self.wk_checked,self.wk_restored);
        // IDs refer to this search stage's task. Mapping through captured SAS
        // is exact when no preprocessing remaps variables.
        for (&(variable, value), c) in &self.conditions {
            eprintln!(concat!("FDR_DIAGNOSTIC_CONDITION {{\"variable\":{},\"value\":{},",
                "\"open_expansions\":{},\"open_children\":{},\"insertion_children\":{},\"goal_opens\":{},",
                "\"threat_expansions\":{},\"threat_children\":{},\"initial_link_threats\":{}}}"),
                variable,value,c.open_expansions,c.open_children,c.insertion_children,c.goal_opens,
                c.threat_expansions,c.threat_children,c.initial_link_threats);
        }
        if let Some(types) = &self.types {
            types.emit();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fdr::{Effect, Operator, Variable};

    #[test]
    fn restoration_requires_forced_order_and_an_unconditional_effect() {
        let mut task = Task {
            variables: vec![Variable {
                name: "x".into(),
                values: vec!["off".into(), "on".into()],
            }],
            mutex_groups: vec![],
            initial: vec![1],
            goals: vec![Fact::new(0, 1)],
            axioms: vec![],
            operators: vec![
                Operator {
                    name: "delete".into(),
                    prevail: vec![],
                    cost: 1,
                    effects: vec![Effect {
                        conditions: vec![],
                        variable: 0,
                        pre: None,
                        post: 0,
                    }],
                },
                Operator {
                    name: "restore".into(),
                    prevail: vec![],
                    cost: 1,
                    effects: vec![Effect {
                        conditions: vec![],
                        variable: 0,
                        pre: None,
                        post: 1,
                    }],
                },
            ],
        };
        let orders = Rc::new(BinaryOrderings::new())
            .refine_with_step(
                Ordering::new(1, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                1,
            )
            .unwrap()
            .refine_with_step(
                Ordering::new(2, StepTime::AtEnd, GOAL_ID, StepTime::AtStart),
                2,
            )
            .unwrap();
        let t = Threat {
            step: 1,
            effect: 0,
            link: 0,
        };
        let mut plan = PartialPlan::assemble(
            vec![Step { id: 1, operator: 0 }, Step { id: 2, operator: 1 }],
            vec![CausalLink {
                producer: INIT_ID,
                consumer: GOAL_ID,
                condition: Fact::new(0, 1),
                effect: None,
            }],
            vec![],
            orders,
            vec![t],
            2,
            3,
        );
        assert!(!has_forced_restorer(&task, &plan, &t));
        plan.orderings = plan
            .orderings
            .refine(Ordering::new(1, StepTime::AtEnd, 2, StepTime::AtStart))
            .unwrap();
        assert!(has_forced_restorer(&task, &plan, &t));
        task.operators[1].effects[0]
            .conditions
            .push(Fact::new(0, 0));
        assert!(!has_forced_restorer(&task, &plan, &t));
        let mut d = Diagnostic::default();
        let planner = Planner::new(&task);
        d.observe(&planner, &plan, &SelectedFlaw::Threat(t), &[]);
        assert_eq!(
            (d.expanded, d.threat_expansions, d.wk_checked, d.wk_restored),
            (1, 1, 1, 0)
        );
        assert_eq!(
            (d.pairs, d.ordered_pairs, d.sample_steps, d.repeated_steps),
            (1, 1, 2, 0)
        );
        // A threat is attributed to its protected fact, not the deleter's effect.
        let protected = &d.conditions[&(0, 1)];
        assert_eq!(
            (protected.threat_expansions, protected.initial_link_threats),
            (1, 1)
        );
        assert!(!d.conditions.contains_key(&(0, 0)));
        let open = SelectedFlaw::Open(OpenCondition {
            consumer: GOAL_ID,
            condition: Fact::new(0, 0),
        });
        d.observe(&planner, &plan, &open, &[plan.clone()]);
        let counts = &d.conditions[&(0, 0)];
        assert_eq!(
            (
                counts.open_expansions,
                counts.open_children,
                counts.insertion_children,
                counts.goal_opens
            ),
            (1, 1, 0, 1)
        );
    }
}
