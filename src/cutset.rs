//! Mutex-based cutset pruning (Nguyen & Kambhampati, IJCAI 2001).
//!
//! A step's cutset contains its required facts, unconditional effects, and
//! facts from necessarily-spanning causal links. A mutex pair makes the
//! partial plan inconsistent.
//!
//! SAS effect pre-values are applicability conditions even for conditional
//! effects; only unconditional post-values enter cutsets. Exclude derived
//! facts and require established orderings on both sides of spanning links.

use crate::fdr::{Fact, Task};
use crate::fdr_pocl::PartialPlan;
use crate::orderings::{BinaryOrderings, StepTime};
use crate::plan::GOAL_ID;

/// Mutually exclusive fact pairs of a finite-domain task.
///
/// Same-variable pairs are implicit (a SAS⁺ variable holds one value), so only
/// the translator's declared `mutex_group`s need indexing.
#[derive(Debug, Default)]
pub struct FactMutexes {
    /// Group ids per fact, flattened: the groups containing fact `f` are
    /// `groups[offsets[i(f)]..offsets[i(f) + 1]]` for `i(f)` the fact's index.
    offsets: Vec<u32>,
    groups: Vec<u32>,
    /// First fact index of each variable, so `i(f) = var_base[f.variable] + f.value`.
    var_base: Vec<usize>,
    /// Whether any declared group spans more than one variable. When none does,
    /// the group index adds nothing the same-variable test does not already
    /// catch, and the per-pair group check is skipped entirely.
    cross_variable: bool,
}

impl FactMutexes {
    /// Indexes a task's declared mutex groups.
    pub fn new(task: &Task) -> Self {
        let mut var_base = Vec::with_capacity(task.variables.len() + 1);
        let mut total = 0usize;
        for variable in &task.variables {
            var_base.push(total);
            total += variable.values.len();
        }
        var_base.push(total);

        let mut per_fact: Vec<Vec<u32>> = vec![Vec::new(); total];
        let mut cross_variable = false;
        for (group_id, group) in task.mutex_groups.iter().enumerate() {
            if group.len() < 2 {
                continue;
            }
            let first = group[0].variable;
            if group.iter().any(|fact| fact.variable != first) {
                cross_variable = true;
            }
            for fact in group {
                if let Some(index) = index_of(&var_base, *fact) {
                    per_fact[index].push(group_id as u32);
                }
            }
        }

        let mut offsets = Vec::with_capacity(total + 1);
        let mut groups = Vec::new();
        for entry in &per_fact {
            offsets.push(groups.len() as u32);
            groups.extend_from_slice(entry);
        }
        offsets.push(groups.len() as u32);

        FactMutexes {
            offsets,
            groups,
            var_base,
            cross_variable,
        }
    }

    /// Whether two distinct facts can never hold in the same state.
    pub fn mutex(&self, left: Fact, right: Fact) -> bool {
        if left == right {
            return false;
        }
        if left.variable == right.variable {
            // One SAS⁺ variable, two values.
            return true;
        }
        if !self.cross_variable {
            return false;
        }
        let (Some(a), Some(b)) = (
            index_of(&self.var_base, left),
            index_of(&self.var_base, right),
        ) else {
            return false;
        };
        let a_groups = &self.groups[self.offsets[a] as usize..self.offsets[a + 1] as usize];
        let b_groups = &self.groups[self.offsets[b] as usize..self.offsets[b + 1] as usize];
        a_groups.iter().any(|g| b_groups.contains(g))
    }

    /// Whether a set of facts contains a mutex pair. `facts` is a cutset, which
    /// stays small, so the quadratic scan is cheaper than building a set.
    pub fn inconsistent(&self, facts: &[Fact]) -> bool {
        for (i, &left) in facts.iter().enumerate() {
            for &right in &facts[i + 1..] {
                if self.mutex(left, right) {
                    return true;
                }
            }
        }
        false
    }
}

fn index_of(var_base: &[usize], fact: Fact) -> Option<usize> {
    let base = *var_base.get(fact.variable)?;
    let end = *var_base.get(fact.variable + 1)?;
    let index = base + fact.value;
    (index < end).then_some(index)
}

/// Returns true iff `before` is *necessarily* before `after`.
///
/// `BinaryOrderings` stores the transitive closure, so this is a single lookup.
fn necessarily_before(orderings: &BinaryOrderings, before: usize, after: usize) -> bool {
    before != after && !orderings.possibly_after(before, StepTime::AtEnd, after, StepTime::AtStart)
}

/// Whether some cutset of `plan` contains a mutex pair — Proposition 1.
///
/// The plan is then provably unrefinable and the caller may discard it.
pub fn has_inconsistent_cutset(plan: &PartialPlan, task: &Task, mutexes: &FactMutexes) -> bool {
    // With no link there is no spanning condition, and a step's own
    // preconditions and effects are individually consistent by construction.
    if plan.num_links() == 0 {
        return false;
    }

    // Reused across steps so the scan allocates once per call rather than
    // twice per step.
    let mut spanning: Vec<Fact> = Vec::new();
    let mut cutset: Vec<Fact> = Vec::new();

    for step in plan.steps() {
        spanning.clear();
        for link in plan.links() {
            if link.producer == step.id || link.consumer == step.id {
                continue;
            }
            if !task.is_derived_variable(link.condition.variable)
                && necessarily_before(&plan.orderings, link.producer, step.id)
                && necessarily_before(&plan.orderings, step.id, link.consumer)
            {
                spanning.push(link.condition);
            }
        }
        if spanning.is_empty() {
            continue;
        }
        let Some(operator) = task.operators.get(step.operator) else {
            continue;
        };

        // C⁻(step) = Prec(step) ∪ L(step).
        cutset.clear();
        cutset.extend_from_slice(&spanning);
        cutset.extend(
            operator
                .prevail
                .iter()
                .copied()
                .filter(|fact| !task.is_derived_variable(fact.variable)),
        );
        for effect in &operator.effects {
            if let Some(pre) = effect.pre {
                if !task.is_derived_variable(effect.variable) {
                    cutset.push(Fact::new(effect.variable, pre));
                }
            }
        }
        if mutexes.inconsistent(&cutset) {
            return true;
        }

        // C⁺(step) = Eff(step) ∪ L(step). A link that spans the step protects
        // its condition across the step's own assignments too.
        cutset.clear();
        cutset.extend_from_slice(&spanning);
        for effect in &operator.effects {
            if effect.conditions.is_empty() && !task.is_derived_variable(effect.variable) {
                cutset.push(effect.assignment());
            }
        }
        if mutexes.inconsistent(&cutset) {
            return true;
        }
    }

    // The goal step's preconditions are the task goals; a link can never span
    // it, so its cutset is plan-independent and is checked once at setup
    // instead. Kept here as a comment rather than a loop iteration so the
    // correspondence with Definition 2 stays visible.
    let _ = GOAL_ID;
    false
}

/// Whether the task's goals are themselves mutually exclusive, making the task
/// unsolvable before search begins. This is the goal step's pre-cutset.
pub fn goals_inconsistent(task: &Task, mutexes: &FactMutexes) -> bool {
    mutexes.inconsistent(&task.goals)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fdr::{Effect, Operator, Variable};

    /// Two variables: `pos` over {a, b} and `holding` over {yes, no}, with a
    /// declared cross-variable group making `pos=b` and `holding=yes` mutex.
    fn task() -> Task {
        Task {
            variables: vec![
                Variable {
                    name: "pos".to_string(),
                    values: vec!["a".to_string(), "b".to_string()],
                },
                Variable {
                    name: "holding".to_string(),
                    values: vec!["yes".to_string(), "no".to_string()],
                },
            ],
            mutex_groups: vec![vec![Fact::new(0, 1), Fact::new(1, 0)]],
            initial: vec![0, 1],
            goals: vec![Fact::new(0, 1)],
            operators: vec![Operator {
                name: "grab".to_string(),
                prevail: vec![],
                effects: vec![Effect {
                    conditions: vec![],
                    variable: 1,
                    pre: Some(1),
                    post: 0,
                }],
                cost: 1,
            }],
            axioms: vec![],
        }
    }

    #[test]
    fn same_variable_values_are_mutex() {
        let task = task();
        let mutexes = FactMutexes::new(&task);
        assert!(mutexes.mutex(Fact::new(0, 0), Fact::new(0, 1)));
        assert!(!mutexes.mutex(Fact::new(0, 0), Fact::new(0, 0)));
    }

    #[test]
    fn declared_groups_give_cross_variable_mutexes() {
        let task = task();
        let mutexes = FactMutexes::new(&task);
        assert!(mutexes.mutex(Fact::new(0, 1), Fact::new(1, 0)));
        // Not in the group together.
        assert!(!mutexes.mutex(Fact::new(0, 0), Fact::new(1, 0)));
    }

    #[test]
    fn inconsistent_spots_a_pair_anywhere_in_the_set() {
        let task = task();
        let mutexes = FactMutexes::new(&task);
        assert!(!mutexes.inconsistent(&[Fact::new(0, 0), Fact::new(1, 1)]));
        assert!(mutexes.inconsistent(&[Fact::new(1, 1), Fact::new(0, 1), Fact::new(1, 0)]));
    }

    #[test]
    fn a_plan_with_no_links_is_never_pruned() {
        let task = task();
        let mutexes = FactMutexes::new(&task);
        let plan = PartialPlan::initial(&task);
        assert!(!has_inconsistent_cutset(&plan, &task, &mutexes));
    }
}

/// Cutset mutex pruning over the literal representation.
///
/// The rule is Proposition 1's, unchanged; what differs is where the mutexes
/// come from and how much of a condition is known. A finite-domain link carries
/// a `Fact`, always ground. A literal link carries terms that may still be
/// variables, so each condition is resolved through the plan's binding
/// constraints and contributes only when every term has reached an object.
/// A condition that is still open contributes nothing — which loses pruning,
/// never soundness.
///
/// See [`crate::lifted_mutex`] for where the mutexes come from without an h²
/// table and without grounding.
pub mod lifted {
    use crate::chain;
    use crate::formula::{Atom, Formula, Literal};
    use crate::lifted_mutex::{GroupKey, LiftedMutexes};
    use crate::orderings::{BinaryOrderings, StepTime};
    use crate::plan::{Link, Plan};
    use crate::search::SearchContext;

    fn necessarily_before(orderings: &BinaryOrderings, before: usize, after: usize) -> bool {
        before != after
            && !orderings.possibly_after(before, StepTime::AtEnd, after, StepTime::AtStart)
    }

    /// Resolves a literal through the bindings, keeping it only if it is
    /// positive and fully ground.
    fn ground_atom(plan: &Plan, literal: &Literal, step_id: usize) -> Option<Atom> {
        let Literal::Atom(atom) = literal else {
            // A negative condition says a fact is absent, which no lifted mutex
            // group constrains.
            return None;
        };
        crate::lifted_mutex::ground_atom(&plan.bindings, atom, step_id)
    }

    /// Where a fact enters the plan from, and therefore which steps' cutsets it
    /// belongs to.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Source {
        /// The condition of a causal link: it holds across every step the link
        /// necessarily spans, and at the link's consumer.
        Link(usize),
        /// An open condition of a step: any completion must establish it there.
        Open(usize),
        /// An unconditional effect of a step: it holds after the step runs.
        Effect(usize),
    }

    /// Whether the rule could fire at all.
    ///
    /// Allocation-free, and it asks the sharper question: not merely whether the
    /// plan has links, but whether any link carries a condition some group
    /// covers. On a domain whose groups touch none of the plan's conditions this
    /// rejects every node without resolving a single term.
    pub fn may_apply(plan: &Plan, mutexes: &LiftedMutexes) -> bool {
        if mutexes.is_empty() || plan.num_links == 0 || plan.num_steps() == 0 {
            return false;
        }
        chain::iter(&plan.links).any(|link| mutexes.covers(link.condition.atom().predicate))
    }

    /// Whether some cutset of the plan contains a mutex pair.
    ///
    /// Call [`may_apply`] first; this assumes it passed.
    ///
    /// # Why this is not the obvious loop
    ///
    /// Proposition 1 reads "for each step, gather the conditions spanning it and
    /// look for a mutex", and that is how this began. It costs
    /// `O(steps × links)` per node — on `logistics-a`, 35 million iterations
    /// across a search, and 90% of the rule's runtime.
    ///
    /// The loop is inverted instead. Two facts are mutex exactly when they are
    /// distinct members of the same *instance* of the same group, so bucketing
    /// the plan's facts by group instance finds every conflicting pair in one
    /// pass, without comparing anything to anything. Only then — and only for
    /// the pairs that actually conflict, which is almost always none — does the
    /// question of whether some step sees both of them get asked.
    ///
    /// So the common case costs a pass over the facts, and the spanning
    /// computation happens per *conflict* rather than per step.
    pub fn has_inconsistent_cutset(
        ctx: &SearchContext,
        plan: &Plan,
        mutexes: &LiftedMutexes,
    ) -> bool {
        // One pass over the links: keep those whose condition a group covers and
        // whose terms have all reached objects. Anything else can neither be a
        // mutex nor be compared to one.
        let mut links: Vec<&Link> = Vec::new();
        let mut facts: Vec<(Atom, Source)> = Vec::new();
        for link in chain::iter(&plan.links) {
            let index = links.len();
            links.push(link);
            if !mutexes.covers(link.condition.atom().predicate) {
                continue;
            }
            if let Some(atom) = ground_atom(plan, &link.condition, link.to_id) {
                facts.push((atom, Source::Link(index)));
            }
        }
        for open in chain::iter(&plan.open_conds) {
            if let Formula::Atom(atom) = open.condition.as_ref() {
                if !mutexes.covers(atom.predicate) {
                    continue;
                }
                if let Some(atom) =
                    crate::lifted_mutex::ground_atom(&plan.bindings, atom, open.step_id)
                {
                    facts.push((atom, Source::Open(open.step_id)));
                }
            }
        }
        for step in chain::iter(&plan.steps) {
            if step.action.synthetic() {
                continue;
            }
            for effect in step.action.effects.iter() {
                if effect.conditional() || !effect.parameters.is_empty() {
                    continue;
                }
                let Literal::Atom(added) = &effect.literal else {
                    continue;
                };
                if !mutexes.covers(added.predicate) {
                    continue;
                }
                if let Some(atom) = crate::lifted_mutex::ground_atom(&plan.bindings, added, step.id)
                {
                    facts.push((atom, Source::Effect(step.id)));
                }
            }
        }
        if facts.len() < 2 {
            return false;
        }

        // Bucket by group instance. Two facts in one bucket are mutex if they
        // differ, so every conflicting pair falls out without a comparison.
        // Sorting a flat vector beats hashing at these sizes, and the key is
        // `Copy`, so the whole pass costs two allocations.
        let mut tagged: Vec<(GroupKey, usize)> = Vec::with_capacity(facts.len());
        let mut keys: Vec<GroupKey> = Vec::new();
        for (index, (atom, _)) in facts.iter().enumerate() {
            keys.clear();
            mutexes.group_keys(atom, &mut keys);
            for key in keys.drain(..) {
                tagged.push((key, index));
            }
        }
        if tagged.len() < 2 {
            return false;
        }
        tagged.sort_unstable();

        let mut run_start = 0;
        while run_start < tagged.len() {
            let mut run_end = run_start + 1;
            while run_end < tagged.len() && tagged[run_end].0 == tagged[run_start].0 {
                run_end += 1;
            }
            for i in run_start..run_end {
                for j in (i + 1)..run_end {
                    let (left, right) = (tagged[i].1, tagged[j].1);
                    if facts[left].0 == facts[right].0 {
                        continue;
                    }
                    if shares_a_cutset(plan, &links, facts[left].1, facts[right].1) {
                        return true;
                    }
                }
            }
            run_start = run_end;
        }
        let _ = ctx;
        false
    }

    /// Whether the link necessarily spans the step, so its condition is held
    /// across it.
    fn spans(plan: &Plan, link: &Link, step: usize) -> bool {
        link.from_id != step
            && link.to_id != step
            && necessarily_before(&plan.orderings, link.from_id, step)
            && necessarily_before(&plan.orderings, step, link.to_id)
    }

    /// Whether two conflicting facts both belong to the cutset of some one step.
    ///
    /// A link's condition reaches every step it spans and its own consumer; an
    /// open condition and an effect reach only their own step, and they reach
    /// *different* cutsets — `C⁻` holds what a step relies on, `C⁺` what it
    /// asserts — so a pair drawn from both can never meet.
    fn shares_a_cutset(plan: &Plan, links: &[&Link], left: Source, right: Source) -> bool {
        match (left, right) {
            (Source::Link(a), Source::Link(b)) => {
                let (first, second) = (links[a], links[b]);
                if first.to_id == second.to_id {
                    return true;
                }
                if spans(plan, first, second.to_id) || spans(plan, second, first.to_id) {
                    return true;
                }
                chain::iter(&plan.steps)
                    .any(|step| spans(plan, first, step.id) && spans(plan, second, step.id))
            }
            (Source::Link(a), Source::Open(step)) | (Source::Open(step), Source::Link(a)) => {
                links[a].to_id == step || spans(plan, links[a], step)
            }
            (Source::Link(a), Source::Effect(step)) | (Source::Effect(step), Source::Link(a)) => {
                spans(plan, links[a], step)
            }
            (Source::Open(a), Source::Open(b)) => a == b,
            (Source::Effect(a), Source::Effect(b)) => a == b,
            // An open condition is what a step relies on and an effect is what
            // it asserts; the two never share a cutset.
            (Source::Open(_), Source::Effect(_)) | (Source::Effect(_), Source::Open(_)) => false,
        }
    }
}
