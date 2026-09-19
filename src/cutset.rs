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
/// the translator's declared `mutex_group`s need indexing. An optional completed
/// h² table adds proven unreachable facts and pairs.
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
    /// Only conditional effects and axiom expansion introduce step requirements
    /// beyond an operator's fixed preconditions. Keep the STRIPS fast path free
    /// of the extra commitment scan.
    additional_requirements: bool,
    h2: Option<crate::h2::Reachability>,
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
            h2: None,
            additional_requirements: !task.axioms.is_empty()
                || task.operators.iter().any(|operator| {
                    operator
                        .effects
                        .iter()
                        .any(|effect| !effect.conditions.is_empty())
                }),
        }
    }

    pub(crate) fn with_h2(mut self, table: Option<crate::h2::Reachability>) -> Self {
        self.h2 = table;
        self
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
        if !self.cross_variable && self.h2.is_none() {
            return false;
        }
        let (Some(a), Some(b)) = (
            index_of(&self.var_base, left),
            index_of(&self.var_base, right),
        ) else {
            return false;
        };
        if self.h2.as_ref().is_some_and(|table| !table.reachable(a, b)) {
            return true;
        }
        let a_groups = &self.groups[self.offsets[a] as usize..self.offsets[a + 1] as usize];
        let b_groups = &self.groups[self.offsets[b] as usize..self.offsets[b + 1] as usize];
        a_groups.iter().any(|g| b_groups.contains(g))
    }

    /// Whether a set contains an unreachable fact or a mutex pair. `facts` is a
    /// cutset, which stays small, so the quadratic scan avoids building a set.
    pub fn inconsistent(&self, facts: &[Fact]) -> bool {
        for (i, &left) in facts.iter().enumerate() {
            if self.h2.as_ref().is_some_and(|table| {
                index_of(&self.var_base, left).is_some_and(|a| !table.reachable(a, a))
            }) {
                return true;
            }
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
    if mutexes.additional_requirements && commitments_inconsistent(plan, task, mutexes) {
        return true;
    }
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

/// All conditions committed at a step hold in its pre-state, including guards
/// chosen to establish conditional effects and confrontation requirements.
/// Resolving an open condition merely moves its fact into an incoming link.
/// These facts need not occur in the operator's original preconditions, and
/// they can conflict even when no causal link spans the step.
fn commitments_inconsistent(plan: &PartialPlan, task: &Task, mutexes: &FactMutexes) -> bool {
    let mut facts: Vec<(usize, Fact)> = plan
        .open_conditions()
        .map(|open| (open.consumer, open.condition))
        .chain(plan.links().map(|link| (link.consumer, link.condition)))
        .filter(|(_, fact)| !task.is_derived_variable(fact.variable))
        .collect();
    facts.sort_unstable();
    facts.dedup();
    for (i, &(step, left)) in facts.iter().enumerate() {
        for &(other_step, right) in &facts[i + 1..] {
            if step != other_step {
                break;
            }
            if mutexes.mutex(left, right) {
                return true;
            }
        }
    }
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
    use std::rc::Rc;

    use crate::bindings::Bindings;
    use crate::chain::{self, Chain};
    use crate::formula::{Atom, Formula, Literal};
    use crate::lifted_mutex::{GroupKey, LiftedMutexes};
    use crate::orderings::{BinaryOrderings, StepTime};
    use crate::plan::{Link, Plan, Step};
    use crate::search::SearchContext;

    fn necessarily_before(orderings: &BinaryOrderings, before: usize, after: usize) -> bool {
        before != after
            && !orderings.possibly_after(before, StepTime::AtEnd, after, StepTime::AtStart)
    }

    /// Resolves a literal through the bindings, keeping it only if it is
    /// positive and fully ground.
    fn ground_literal(bindings: &Bindings, literal: &Literal, step_id: usize) -> Option<Atom> {
        let Literal::Atom(atom) = literal else {
            // A negative condition says a fact is absent, which no lifted mutex
            // group constrains.
            return None;
        };
        crate::lifted_mutex::ground_atom(bindings, atom, step_id)
    }

    /// Where a fact enters the plan from, and therefore which steps' cutsets it
    /// belongs to.
    ///
    /// A link is named by the two steps it runs between rather than by a
    /// position in the plan's link chain: those are the only two things the
    /// cutset test asks of it, and a pair of step ids stays meaningful in every
    /// descendant, where a chain position does not — the chain is consed onto,
    /// so a link's distance from the head grows as the plan is refined.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Source {
        /// The condition of a causal link: it holds across every step the link
        /// necessarily spans, and at the link's consumer.
        Link { from: usize, to: usize },
        /// An open condition of a step: any completion must establish it there.
        Open(usize),
        /// An unconditional effect of a step: it holds after the step runs.
        Effect(usize),
    }

    /// A link condition or step effect the bindings have not ground yet.
    ///
    /// Held as the chain node it lives in rather than as a copy of its atom:
    /// the plan already owns the node, so a candidate costs one reference
    /// count and no term vector.
    #[derive(Debug, Clone)]
    enum Candidate {
        Link(Rc<Chain<Link>>),
        /// A step together with the index of one of its effects.
        Effect(Rc<Chain<Step>>, u32),
    }

    impl Candidate {
        fn symbolic(&self) -> (&Atom, usize, Source) {
            match self {
                Candidate::Link(node) => {
                    let link = &node.head;
                    (
                        link.condition.atom(),
                        link.to_id,
                        Source::Link {
                            from: link.from_id,
                            to: link.to_id,
                        },
                    )
                }
                Candidate::Effect(node, index) => {
                    let step = &node.head;
                    (
                        step.action.effects[*index as usize].literal.atom(),
                        step.id,
                        Source::Effect(step.id),
                    )
                }
            }
        }

        fn resolve(&self, bindings: &Bindings) -> Option<(Atom, Source)> {
            match self {
                Candidate::Link(node) => {
                    let link = &node.head;
                    ground_literal(bindings, &link.condition, link.to_id).map(|atom| {
                        (
                            atom,
                            Source::Link {
                                from: link.from_id,
                                to: link.to_id,
                            },
                        )
                    })
                }
                Candidate::Effect(node, index) => {
                    let step = &node.head;
                    let effect = &step.action.effects[*index as usize];
                    ground_literal(bindings, &effect.literal, step.id)
                        .map(|atom| (atom, Source::Effect(step.id)))
                }
            }
        }
    }

    /// The ground facts one refinement contributed, sharing its parent's.
    ///
    /// A child differs from its parent by one refinement, and the two sets the
    /// cutset test reads are almost entirely inherited: links and steps are only
    /// ever consed on, and a term the bindings have resolved to an object stays
    /// that object in every descendant. So a node stores what it added and
    /// points at its parent for the rest, and the per-node cost of the rule
    /// falls from resolving every condition of the plan through the binding
    /// constraints to resolving the handful a refinement moved.
    ///
    /// Two things do not inherit. Open conditions *leave* a plan when they are
    /// linked, so they are gathered fresh on each call — they are a twentieth of
    /// the facts, and tracking removals through a shared chain would cost more
    /// than resolving them. And a condition that was not ground when its link
    /// was made may become ground later, so the ones still carrying variables
    /// are kept in `pending` and retried whenever the bindings change; the list
    /// is shared with the parent while they do not.
    struct Facts {
        parent: Option<Rc<Facts>>,
        depth: usize,
        /// The plan's link and step chains at this node. A child finds exactly
        /// what it added by walking its own chains down to these.
        links: Option<Rc<Chain<Link>>>,
        steps: Option<Rc<Chain<Step>>>,
        /// The bindings the facts here were resolved under. A child sharing
        /// them can ground nothing new.
        bindings: Rc<Bindings>,
        /// Facts that became ground at this node: conditions of links and
        /// unconditional effects of steps added here, plus any candidate the
        /// refinement's new bindings resolved.
        ground: Box<[(Atom, Source)]>,
        /// The group instances of `ground`, as `(instance id, index into
        /// ground)`. Computed once here rather than per node, because a fact's
        /// group instances are a property of the fact.
        keys: Box<[(u32, u32)]>,
        /// Candidates still carrying a variable, to retry when the bindings
        /// change.
        pending: Rc<[Candidate]>,
        /// Facts and keys in the whole chain up to here, so the scan below
        /// sizes its buffers once instead of growing them.
        total_ground: u32,
        total_keys: u32,
    }

    /// The chain nodes `chain` holds in front of `tail`, newest first.
    ///
    /// Returns false — leaving `out` meaningless — if `tail` is not a suffix of
    /// `chain`, which is a caller's cue to rebuild from scratch rather than
    /// assume a parentage the chains do not show.
    fn prefix<T>(
        chain: &Option<Rc<Chain<T>>>,
        tail: &Option<Rc<Chain<T>>>,
        out: &mut Vec<Rc<Chain<T>>>,
    ) -> bool {
        out.clear();
        let mut cur = chain.clone();
        while let Some(node) = cur {
            if let Some(stop) = tail {
                if Rc::ptr_eq(&node, stop) {
                    return true;
                }
            }
            cur = node.tail.clone();
            out.push(node);
        }
        tail.is_none()
    }

    /// Builds a plan's facts, extending its parent's where it can.
    const MAX_CACHE_DEPTH: usize = 16;
    const MAX_CACHE_ENTRIES: usize = 512;

    fn build(parent: Option<&Rc<Facts>>, plan: &Plan, mutexes: &LiftedMutexes) -> Rc<Facts> {
        let mut new_links: Vec<Rc<Chain<Link>>> = Vec::new();
        let mut new_steps: Vec<Rc<Chain<Step>>> = Vec::new();
        // Bound retained ancestry even when the oldest cache entries expire.
        let mut parent = parent.filter(|facts| facts.depth < MAX_CACHE_DEPTH);
        if let Some(inherited) = parent {
            if !prefix(&plan.links, &inherited.links, &mut new_links)
                || !prefix(&plan.steps, &inherited.steps, &mut new_steps)
            {
                parent = None;
            }
        }
        if parent.is_none() {
            prefix(&plan.links, &None, &mut new_links);
            prefix(&plan.steps, &None, &mut new_steps);
        }

        let mut ground: Vec<(Atom, Source)> = Vec::new();
        let mut fresh: Vec<Candidate> = Vec::new();
        // Whether the parent's own pending list still holds: it does exactly
        // when the bindings have not moved, since only a binding can ground a
        // term that was not ground before.
        let mut inherit_pending = false;
        if let Some(inherited) = parent {
            if Rc::ptr_eq(&inherited.bindings, &plan.bindings) {
                inherit_pending = true;
            } else {
                for candidate in inherited.pending.iter() {
                    match candidate.resolve(&plan.bindings) {
                        Some(fact) => ground.push(fact),
                        None => fresh.push(candidate.clone()),
                    }
                }
            }
        }

        for node in &new_links {
            let link = &node.head;
            if !mutexes.covers(link.condition.atom().predicate) {
                continue;
            }
            if !matches!(link.condition.as_ref(), Literal::Atom(_)) {
                // A negative condition never resolves into a group member, so
                // it is not worth carrying as a candidate either.
                continue;
            }
            match ground_literal(&plan.bindings, &link.condition, link.to_id) {
                Some(atom) => ground.push((
                    atom,
                    Source::Link {
                        from: link.from_id,
                        to: link.to_id,
                    },
                )),
                None => fresh.push(Candidate::Link(node.clone())),
            }
        }
        for node in &new_steps {
            let step = &node.head;
            if step.action.synthetic() {
                continue;
            }
            for (index, effect) in step.action.effects.iter().enumerate() {
                if effect.conditional() || !effect.parameters.is_empty() {
                    continue;
                }
                let Literal::Atom(added) = &effect.literal else {
                    continue;
                };
                if !mutexes.covers(added.predicate) {
                    continue;
                }
                match crate::lifted_mutex::ground_atom(&plan.bindings, added, step.id) {
                    Some(atom) => ground.push((atom, Source::Effect(step.id))),
                    None => fresh.push(Candidate::Effect(node.clone(), index as u32)),
                }
            }
        }

        if let Some(inherited) = parent {
            if inherit_pending && ground.is_empty() && fresh.is_empty() {
                // The refinement moved nothing this rule reads — an ordering,
                // or a link over a predicate no group covers. Share the
                // parent's node outright rather than allocate an empty delta:
                // its chains are still suffixes of this plan's, so a child of
                // this plan finds exactly what it added, and re-examining the
                // link this one skipped skips it again.
                return inherited.clone();
            }
        }

        let mut keys: Vec<(u32, u32)> = Vec::new();
        let mut scratch: Vec<GroupKey> = Vec::new();
        let mut ids: Vec<u32> = Vec::new();
        for (index, (atom, _)) in ground.iter().enumerate() {
            ids.clear();
            mutexes.group_key_ids(atom, &mut scratch, &mut ids);
            for id in ids.iter() {
                keys.push((*id, index as u32));
            }
        }

        let pending: Rc<[Candidate]> = match parent {
            Some(inherited) if inherit_pending && fresh.is_empty() => inherited.pending.clone(),
            Some(inherited) if inherit_pending => {
                let mut all: Vec<Candidate> = inherited.pending.to_vec();
                all.append(&mut fresh);
                Rc::from(all)
            }
            _ => Rc::from(fresh),
        };

        let (base_ground, base_keys) = parent.map_or((0, 0), |p| (p.total_ground, p.total_keys));
        Rc::new(Facts {
            depth: parent.map_or(1, |facts| facts.depth + 1),
            parent: parent.cloned(),
            links: plan.links.clone(),
            steps: plan.steps.clone(),
            bindings: plan.bindings.clone(),
            total_ground: base_ground + ground.len() as u32,
            total_keys: base_keys + keys.len() as u32,
            ground: ground.into_boxed_slice(),
            keys: keys.into_boxed_slice(),
            pending,
        })
    }

    /// A bounded, task-local acceleration cache. Entries are keyed by the
    /// immutable inputs to fact resolution, never by recyclable Plan addresses.
    /// Facts own those inputs, so a cached pointer key cannot alias a later one.
    /// Eviction only forces recomputation; it cannot remove a constraint.
    #[derive(Default)]
    pub(crate) struct Cache {
        entries: crate::fasthash::FastMap<(usize, usize, usize), Rc<Facts>>,
        fifo: std::collections::VecDeque<(usize, usize, usize)>,
    }

    impl std::fmt::Debug for Cache {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("Cache")
                .field("entries", &self.entries.len())
                .finish()
        }
    }

    fn key(
        links: &Option<Rc<Chain<Link>>>,
        steps: &Option<Rc<Chain<Step>>>,
        bindings: &Rc<Bindings>,
    ) -> (usize, usize, usize) {
        (
            links.as_ref().map_or(0, |p| Rc::as_ptr(p) as usize),
            steps.as_ref().map_or(0, |p| Rc::as_ptr(p) as usize),
            Rc::as_ptr(bindings) as usize,
        )
    }

    fn cached(plan: &Plan, parent: Option<&Plan>, mutexes: &LiftedMutexes) -> Rc<Facts> {
        let mut cache = mutexes.cutset_cache.borrow_mut();
        let plan_key = key(&plan.links, &plan.steps, &plan.bindings);
        if let Some(existing) = cache.entries.get(&plan_key) {
            return existing.clone();
        }
        let inherited = parent
            .and_then(|p| cache.entries.get(&key(&p.links, &p.steps, &p.bindings)))
            .cloned();
        let facts = build(inherited.as_ref(), plan, mutexes);
        if inherited.as_ref().is_some_and(|p| Rc::ptr_eq(p, &facts)) {
            return facts;
        }
        // A new fact set owns this plan's inputs, whose key was absent above.
        debug_assert_eq!(key(&facts.links, &facts.steps, &facts.bindings), plan_key);
        if cache.entries.len() >= MAX_CACHE_ENTRIES {
            let oldest = cache
                .fifo
                .pop_front()
                .expect("cache entry has an insertion key");
            cache.entries.remove(&oldest);
        }
        cache.fifo.push_back(plan_key);
        cache.entries.insert(plan_key, facts.clone());
        facts
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

    /// Whether a cutset contains a mutex pair. Requires [`may_apply`] to pass.
    /// `parent` is the plan this one extends.
    ///
    /// Bucket facts by mutex-group instance, then check whether a step sees both
    /// members of a conflicting pair. [`Facts`] caches resolved ground atoms
    /// across parent and child plans.
    pub fn has_inconsistent_cutset(
        ctx: &SearchContext,
        plan: &Plan,
        mutexes: &LiftedMutexes,
        parent: Option<&Plan>,
    ) -> bool {
        if mutexes.is_empty() {
            return false;
        }
        let cache = cached(plan, parent, mutexes);

        // Oldest delta first, so a fact's index is the one its keys were
        // recorded against.
        let mut deltas: Vec<&Facts> = Vec::new();
        let mut cursor = Some(cache.as_ref());
        while let Some(node) = cursor {
            deltas.push(node);
            cursor = node.parent.as_deref();
        }
        let mut facts: Vec<(&Atom, Source)> =
            Vec::with_capacity(cache.total_ground as usize + plan.num_open_conds);
        let mut tagged: Vec<(u32, u32)> =
            Vec::with_capacity(cache.total_keys as usize + plan.num_open_conds);
        for delta in deltas.iter().rev() {
            let base = facts.len() as u32;
            for (atom, source) in delta.ground.iter() {
                facts.push((atom, *source));
            }
            for (key, offset) in delta.keys.iter() {
                tagged.push((*key, base + offset));
            }
        }

        // Open conditions leave a plan when they are linked, so they are the one
        // part of the fact set that does not inherit.
        let mut opens: Vec<(Atom, Source)> = Vec::new();
        let mut symbolic = Vec::new();
        if ctx.params.prune.symbolic {
            symbolic.extend(cache.pending.iter().map(Candidate::symbolic));
        }
        for open in chain::iter(&plan.open_conds) {
            if let Formula::Atom(atom) = open.condition.as_ref() {
                if !mutexes.covers(atom.predicate) {
                    continue;
                }
                if let Some(resolved) =
                    crate::lifted_mutex::ground_atom(&plan.bindings, atom, open.step_id)
                {
                    opens.push((resolved, Source::Open(open.step_id)));
                } else if ctx.params.prune.symbolic {
                    symbolic.push((atom, open.step_id, Source::Open(open.step_id)));
                }
            }
        }
        let mut scratch: Vec<GroupKey> = Vec::new();
        let mut ids: Vec<u32> = Vec::new();
        for (atom, source) in opens.iter() {
            let index = facts.len() as u32;
            facts.push((atom, *source));
            ids.clear();
            mutexes.group_key_ids(atom, &mut scratch, &mut ids);
            for id in ids.iter() {
                tagged.push((*id, index));
            }
        }

        if !symbolic.is_empty() {
            let mut spanning = Spanning::new(plan, facts.len() + symbolic.len());
            let type_ctx = ctx.type_ctx();
            for (i, &(atom, step, source)) in symbolic.iter().enumerate() {
                let index = facts.len() + i;
                for (j, &(other, other_source)) in facts.iter().enumerate() {
                    if mutexes.may_pair(atom.predicate, other.predicate)
                        && spanning.shares_a_cutset(source, other_source, index, j)
                        && mutexes.symbolic_mutex(
                            &plan.bindings,
                            &type_ctx,
                            (atom, step),
                            (other, 0),
                        )
                    {
                        return true;
                    }
                }
                for (j, &(other, other_step, other_source)) in symbolic[..i].iter().enumerate() {
                    if mutexes.may_pair(atom.predicate, other.predicate)
                        && spanning.shares_a_cutset(source, other_source, index, facts.len() + j)
                        && mutexes.symbolic_mutex(
                            &plan.bindings,
                            &type_ctx,
                            (atom, step),
                            (other, other_step),
                        )
                    {
                        return true;
                    }
                }
            }
        }

        if facts.len() < 2 || tagged.len() < 2 {
            return false;
        }

        // Bucket by group instance. Two facts in one bucket are mutex if they
        // differ, so every conflicting pair falls out without a comparison.
        // Sorting a flat vector beats hashing at these sizes, and the key is
        // `Copy`.
        tagged.sort_unstable();
        let mut spanning: Option<Spanning> = None;
        let mut run_start = 0;
        while run_start < tagged.len() {
            let mut run_end = run_start + 1;
            while run_end < tagged.len() && tagged[run_end].0 == tagged[run_start].0 {
                run_end += 1;
            }
            for i in run_start..run_end {
                for j in (i + 1)..run_end {
                    let (left, right) = (tagged[i].1 as usize, tagged[j].1 as usize);
                    if facts[left].0 == facts[right].0 {
                        continue;
                    }
                    let spanning = spanning.get_or_insert_with(|| Spanning::new(plan, facts.len()));
                    if spanning.shares_a_cutset(facts[left].1, facts[right].1, left, right) {
                        return true;
                    }
                }
            }
            run_start = run_end;
        }
        false
    }

    /// Answers "do these two facts meet at some step" for one node's facts.
    ///
    /// The question is asked once per *conflicting pair*, and a domain whose
    /// facts fall into a few large group instances has far more conflicting
    /// pairs than links — 170 pairs over 24 facts on `grid`. Walking every step
    /// for every pair is then the rule's largest remaining cost, so the steps a
    /// link spans are computed once per link and kept as a bit per step; a pair
    /// meets exactly when the two sets intersect.
    ///
    /// Above 64 steps there is no room for the bitset and the direct walk is
    /// used, which is what the bitset is an exact restatement of.
    struct Spanning<'a> {
        plan: &'a Plan,
        /// Step ids in chain order, one bit position each. Empty when the plan
        /// has more steps than a bitset holds.
        steps: Vec<usize>,
        /// Span set per fact index, filled on first use.
        bits: Vec<Option<u64>>,
    }

    impl<'a> Spanning<'a> {
        fn new(plan: &'a Plan, facts: usize) -> Self {
            let steps: Vec<usize> = chain::iter(&plan.steps).map(|step| step.id).collect();
            let bits = if steps.len() <= 64 {
                vec![None; facts]
            } else {
                Vec::new()
            };
            Spanning { plan, steps, bits }
        }

        fn span_bits(&mut self, index: usize, from: usize, to: usize) -> u64 {
            if let Some(bits) = self.bits[index] {
                return bits;
            }
            let mut bits = 0u64;
            for (slot, step) in self.steps.iter().enumerate() {
                if spans(self.plan, from, to, *step) {
                    bits |= 1u64 << slot;
                }
            }
            self.bits[index] = Some(bits);
            bits
        }

        /// Whether two conflicting facts both belong to the cutset of some one
        /// step.
        ///
        /// A link's condition reaches every step it spans and its own consumer;
        /// an open condition and an effect reach only their own step, and they
        /// reach *different* cutsets — `C⁻` holds what a step relies on, `C⁺`
        /// what it asserts — so a pair drawn from both can never meet.
        fn shares_a_cutset(&mut self, left: Source, right: Source, li: usize, ri: usize) -> bool {
            match (left, right) {
                (
                    Source::Link {
                        from: first_from,
                        to: first_to,
                    },
                    Source::Link {
                        from: second_from,
                        to: second_to,
                    },
                ) => {
                    if first_to == second_to {
                        return true;
                    }
                    if spans(self.plan, first_from, first_to, second_to)
                        || spans(self.plan, second_from, second_to, first_to)
                    {
                        return true;
                    }
                    if self.bits.is_empty() {
                        return chain::iter(&self.plan.steps).any(|step| {
                            spans(self.plan, first_from, first_to, step.id)
                                && spans(self.plan, second_from, second_to, step.id)
                        });
                    }
                    let first = self.span_bits(li, first_from, first_to);
                    let second = self.span_bits(ri, second_from, second_to);
                    first & second != 0
                }
                (Source::Link { from, to }, Source::Open(step))
                | (Source::Open(step), Source::Link { from, to }) => {
                    to == step || spans(self.plan, from, to, step)
                }
                (Source::Link { from, to }, Source::Effect(step))
                | (Source::Effect(step), Source::Link { from, to }) => {
                    spans(self.plan, from, to, step)
                }
                (Source::Open(a), Source::Open(b)) => a == b,
                (Source::Effect(a), Source::Effect(b)) => a == b,
                // An open condition is what a step relies on and an effect is
                // what it asserts; the two never share a cutset.
                (Source::Open(_), Source::Effect(_)) | (Source::Effect(_), Source::Open(_)) => {
                    false
                }
            }
        }
    }

    /// Whether a link from `from` to `to` necessarily spans the step, so its
    /// condition is held across it.
    fn spans(plan: &Plan, from: usize, to: usize, step: usize) -> bool {
        from != step
            && to != step
            && necessarily_before(&plan.orderings, from, step)
            && necessarily_before(&plan.orderings, step, to)
    }

    /// The rule as it was written before [`Facts`]: one pass over the whole plan
    /// per node, resolving every condition through the bindings from scratch.
    ///
    /// Kept as the oracle the incremental form is tested against. The two must
    /// agree on every plan — a disagreement is either a lost prune or, worse, an
    /// invented one.
    #[cfg(test)]
    pub(crate) mod reference {
        use super::{spans, Source};
        use crate::chain;
        use crate::formula::{Atom, Formula, Literal};
        use crate::lifted_mutex::{GroupKey, LiftedMutexes};
        use crate::plan::Plan;

        /// The direct form: for a link/link pair, walk every step looking for
        /// one both links span.
        fn shares_a_cutset(plan: &Plan, left: Source, right: Source) -> bool {
            match (left, right) {
                (
                    Source::Link {
                        from: first_from,
                        to: first_to,
                    },
                    Source::Link {
                        from: second_from,
                        to: second_to,
                    },
                ) => {
                    if first_to == second_to {
                        return true;
                    }
                    if spans(plan, first_from, first_to, second_to)
                        || spans(plan, second_from, second_to, first_to)
                    {
                        return true;
                    }
                    chain::iter(&plan.steps).any(|step| {
                        spans(plan, first_from, first_to, step.id)
                            && spans(plan, second_from, second_to, step.id)
                    })
                }
                (Source::Link { from, to }, Source::Open(step))
                | (Source::Open(step), Source::Link { from, to }) => {
                    to == step || spans(plan, from, to, step)
                }
                (Source::Link { from, to }, Source::Effect(step))
                | (Source::Effect(step), Source::Link { from, to }) => spans(plan, from, to, step),
                (Source::Open(a), Source::Open(b)) => a == b,
                (Source::Effect(a), Source::Effect(b)) => a == b,
                (Source::Open(_), Source::Effect(_)) | (Source::Effect(_), Source::Open(_)) => {
                    false
                }
            }
        }

        fn ground_atom(plan: &Plan, literal: &Literal, step_id: usize) -> Option<Atom> {
            let Literal::Atom(atom) = literal else {
                return None;
            };
            crate::lifted_mutex::ground_atom(&plan.bindings, atom, step_id)
        }

        pub(crate) fn has_inconsistent_cutset(plan: &Plan, mutexes: &LiftedMutexes) -> bool {
            let mut facts: Vec<(Atom, Source)> = Vec::new();
            for link in chain::iter(&plan.links) {
                if !mutexes.covers(link.condition.atom().predicate) {
                    continue;
                }
                if let Some(atom) = ground_atom(plan, &link.condition, link.to_id) {
                    facts.push((
                        atom,
                        Source::Link {
                            from: link.from_id,
                            to: link.to_id,
                        },
                    ));
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
                    if let Some(atom) =
                        crate::lifted_mutex::ground_atom(&plan.bindings, added, step.id)
                    {
                        facts.push((atom, Source::Effect(step.id)));
                    }
                }
            }
            if facts.len() < 2 {
                return false;
            }

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
                        if shares_a_cutset(plan, facts[left].1, facts[right].1) {
                            return true;
                        }
                    }
                }
                run_start = run_end;
            }
            false
        }
    }
}

/// The incremental lifted rule against the one-pass form it replaced.
///
/// The rule's whole value is that it discards only plans it has *proved*
/// unrefinable, so the thing worth testing is not that the new form prunes but
/// that it prunes exactly what the old one did. `discarded_by_pruning` puts
/// every generated node to both implementations under `cfg(test)`; these tests
/// are the searches that generate the nodes, chosen so that the rule actually
/// fires — agreement where nothing is pruned proves nothing.
#[cfg(test)]
mod lifted_oracle {
    use crate::params::Parameters;
    use crate::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
    use crate::pruning::PruneOptions;
    use crate::search::{plan_with_stats, SearchContext};

    /// Runs a bounded search with `-p cutset` on, and returns how many nodes it
    /// discarded. The cross-check itself lives in `discarded_by_pruning`, which
    /// panics on a disagreement.
    fn pruned_over_a_search(domain_path: &str, problem_path: &str, limit: usize) -> usize {
        let domain_src = std::fs::read_to_string(domain_path).expect("read domain");
        let problem_src = std::fs::read_to_string(problem_path).expect("read problem");
        let domain = match read_pddl(&domain_src).expect("parse domain") {
            ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
            _ => panic!("expected a domain"),
        };
        let problem = match read_pddl(&problem_src).expect("parse problem") {
            ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
            _ => panic!("expected a problem"),
        };
        let params = Parameters {
            search_limits: vec![limit],
            prune: PruneOptions {
                cutset: true,
                ..PruneOptions::default()
            },
            ..Parameters::default()
        };
        let ctx = SearchContext::new(&domain, &problem, &params);
        let (_, stats) = plan_with_stats(&ctx);
        stats.pruned
    }

    #[test]
    fn the_incremental_rule_matches_the_one_pass_form_on_test_ferry() {
        let pruned = pruned_over_a_search(
            "examples/ferry-domain.pddl",
            "examples/test-ferry.pddl",
            3_000,
        );
        assert!(
            pruned > 0,
            "the rule never fired, so agreement proves little"
        );
    }

    #[test]
    fn the_incremental_rule_matches_the_one_pass_form_on_gripper() {
        let pruned = pruned_over_a_search(
            "examples/gripper-domain.pddl",
            "examples/gripper-6.pddl",
            3_000,
        );
        assert!(
            pruned > 0,
            "the rule never fired, so agreement proves little"
        );
    }

    #[test]
    fn the_incremental_rule_matches_the_one_pass_form_on_logistics_a() {
        let pruned = pruned_over_a_search(
            "examples/logistics-domain.pddl",
            "examples/logistics-a.pddl",
            3_000,
        );
        assert!(
            pruned > 0,
            "the rule never fired, so agreement proves little"
        );
    }

    /// Blocks world has mutex groups of its own shape, and a plan there carries
    /// more threats than links — a different mix of `Source`s reaching
    /// `shares_a_cutset`.
    #[test]
    fn the_incremental_rule_matches_the_one_pass_form_on_sussman_anomaly() {
        pruned_over_a_search(
            "examples/blocks-world-domain.pddl",
            "examples/sussman-anomaly.pddl",
            3_000,
        );
    }

    /// A plan whose parent carries no state — the initial plan's children, and
    /// any plan reached in a way the incremental path did not build — must give
    /// the same verdict as one whose state was inherited. This is the case the
    /// `prefix` guard and the `None` parent exist for, and it is not reached by
    /// a search, where every node has its parent to hand.
    #[test]
    fn a_plan_checked_without_its_parent_agrees_with_one_checked_with_it() {
        use crate::chain;
        use crate::plan::Plan;
        use std::rc::Rc;

        let domain_src =
            std::fs::read_to_string("examples/ferry-domain.pddl").expect("read domain");
        let problem_src =
            std::fs::read_to_string("examples/test-ferry.pddl").expect("read problem");
        let domain = match read_pddl(&domain_src).expect("parse domain") {
            ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
            _ => panic!("expected a domain"),
        };
        let problem = match read_pddl(&problem_src).expect("parse problem") {
            ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
            _ => panic!("expected a problem"),
        };
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let mutexes = ctx.lifted_mutexes();
        assert!(!mutexes.is_empty(), "no lifted mutex groups to test with");

        let initial = Plan::make_initial_plan(&ctx).expect("an initial plan");
        let mut stack: Vec<Rc<Plan>> = vec![initial];
        let mut checked = 0usize;
        while let Some(parent) = stack.pop() {
            if checked >= 300 {
                break;
            }
            for step in chain::iter(&parent.steps) {
                ctx.register_step(step.id, &step.action);
            }
            let mut children: Vec<Rc<Plan>> = Vec::new();
            parent.refinements_with(&ctx, 0, &mut children);
            for child in children {
                ctx.register_newest_step(&child, parent.num_steps);
                if !super::lifted::may_apply(&child, &mutexes) {
                    continue;
                }
                *mutexes.cutset_cache.borrow_mut() = Default::default();
                super::lifted::has_inconsistent_cutset(&ctx, &parent, &mutexes, None);
                let inherited =
                    super::lifted::has_inconsistent_cutset(&ctx, &child, &mutexes, Some(&parent));
                // Clear acceleration data to force a fresh build: its verdict
                // must be independent of cache residency and parent availability.
                *mutexes.cutset_cache.borrow_mut() = Default::default();
                let orphan = super::lifted::has_inconsistent_cutset(&ctx, &child, &mutexes, None);
                assert_eq!(
                    orphan, inherited,
                    "a plan's verdict depends on whether its parent was to hand"
                );
                assert_eq!(
                    orphan,
                    super::lifted::reference::has_inconsistent_cutset(&child, &mutexes),
                    "a parentless build disagrees with the one-pass form"
                );
                checked += 1;
                if !orphan && !child.complete() {
                    stack.push(child);
                }
            }
        }
        assert!(checked > 50, "only {checked} plans reached");
    }
}
