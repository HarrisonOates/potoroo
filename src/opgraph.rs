//! Recursion pruning (Smith & Peot, AIPS 1996, Theorems 1 and 4).
//!
//! The operator graph connects signed predicates to achieving schemas and
//! schemas to required predicates. Coarsening to predicates enlarges SCCs
//! and relevant-operator sets, so it can only weaken pruning.
//!
//! Exact recursion requires a syntactically repeated condition along every
//! causal-link path to the goal. Suspension is recomputed for each plan.
//! Prune when every open condition is suspended, or when a suspended
//! condition's root links cannot be threatened by remaining relevant operators.
//! Instance recursion and suspension-based flaw ordering are not implemented.

use std::collections::{HashMap, HashSet};

use crate::chain;
use crate::domain::Domain;
use crate::flaws::OpenCondition;
use crate::formula::{Formula, Literal};
use crate::orderings::StepTime;
use crate::plan::{Link, Plan, GOAL_ID, INIT_ID};
use crate::predicates::Predicate;
use crate::search::SearchContext;

/// A signed predicate: the node type standing for a precondition.
type SignedPredicate = (Predicate, bool);

/// The operator graph of a lowered domain, with its strongly connected
/// components and per-predicate relevant-operator sets.
#[derive(Debug)]
pub struct OperatorGraph {
    /// SCC id per signed predicate. Predicates in no cycle get their own
    /// singleton component.
    scc: HashMap<SignedPredicate, usize>,
    /// Schema ids belonging to each SCC.
    operators_by_scc: Vec<HashSet<usize>>,
    /// Schema ids reachable from each signed predicate: the operators that could
    /// take part in achieving it, transitively.
    relevant: HashMap<SignedPredicate, HashSet<usize>>,
    /// Whether the signed predicate's node lies on a cycle.
    cyclic: HashSet<SignedPredicate>,
}

/// Node ids in the bipartite graph: predicates first, then schemas.
fn build_nodes(domain: &Domain) -> (Vec<SignedPredicate>, HashMap<SignedPredicate, usize>) {
    let mut order: Vec<SignedPredicate> = Vec::new();
    let mut index: HashMap<SignedPredicate, usize> = HashMap::new();
    let note = |key: SignedPredicate,
                order: &mut Vec<SignedPredicate>,
                index: &mut HashMap<SignedPredicate, usize>| {
        index.entry(key).or_insert_with(|| {
            order.push(key);
            order.len() - 1
        });
    };
    for action in &domain.actions {
        let mut literals = Vec::new();
        collect_required_literals(&action.precondition, &mut literals);
        for literal in literals {
            note(signed(&literal), &mut order, &mut index);
        }
        for effect in &action.effects {
            note(signed(&effect.literal), &mut order, &mut index);
        }
    }
    (order, index)
}

fn signed(literal: &Literal) -> SignedPredicate {
    (literal.atom().predicate, literal.negative())
}

/// An open condition's signed predicate, without cloning its atom.
fn open_condition_predicate(open_cond: &OpenCondition) -> Option<SignedPredicate> {
    match open_cond.condition.as_ref() {
        Formula::Atom(atom) => Some((atom.predicate, false)),
        Formula::Negation(atom) => Some((atom.predicate, true)),
        _ => None,
    }
}

/// Collects the literals a precondition formula requires, over-approximating:
/// every atom that appears anywhere in the formula is treated as potentially
/// required. Over-approximating grows the graph, which is the safe direction
/// for both uses (see the module docs).
fn collect_required_literals(formula: &std::rc::Rc<Formula>, out: &mut Vec<Literal>) {
    match formula.as_ref() {
        Formula::Atom(atom) => out.push(Literal::Atom(atom.clone())),
        Formula::Negation(atom) => out.push(Literal::Negation(atom.clone())),
        Formula::Conjunction(parts) | Formula::Disjunction(parts) => {
            for part in parts {
                collect_required_literals(part, out);
            }
        }
        Formula::Exists { body, .. } | Formula::Forall { body, .. } => {
            collect_required_literals(body, out)
        }
        _ => {}
    }
}

impl OperatorGraph {
    /// Builds the graph, its SCCs and its relevant-operator sets.
    pub fn build(domain: &Domain) -> Self {
        let (predicates, predicate_index) = build_nodes(domain);
        let n_predicates = predicates.len();
        let n_schemas = domain.actions.len();
        let total = n_predicates + n_schemas;

        // Bipartite adjacency: predicate -> achieving schemas, schema -> its
        // required predicates.
        let mut adjacency: Vec<Vec<usize>> = vec![Vec::new(); total];
        for (schema_id, action) in domain.actions.iter().enumerate() {
            let schema_node = n_predicates + schema_id;
            let mut literals = Vec::new();
            collect_required_literals(&action.precondition, &mut literals);
            for literal in &literals {
                if let Some(&node) = predicate_index.get(&signed(literal)) {
                    adjacency[schema_node].push(node);
                }
            }
            for effect in &action.effects {
                if let Some(&node) = predicate_index.get(&signed(&effect.literal)) {
                    adjacency[node].push(schema_node);
                }
            }
        }
        for row in &mut adjacency {
            row.sort_unstable();
            row.dedup();
        }

        let components = tarjan(&adjacency);

        // A node is cyclic when its component has more than one node, or it has
        // a self-loop.
        let mut component_size = vec![0usize; total];
        for &component in &components {
            component_size[component] += 1;
        }

        let mut scc = HashMap::new();
        let mut cyclic = HashSet::new();
        let mut operators_by_scc: Vec<HashSet<usize>> = vec![HashSet::new(); total];
        for (schema_id, _) in domain.actions.iter().enumerate() {
            let node = n_predicates + schema_id;
            operators_by_scc[components[node]].insert(schema_id);
        }
        for (position, key) in predicates.iter().enumerate() {
            scc.insert(*key, components[position]);
            if component_size[components[position]] > 1 || adjacency[position].contains(&position) {
                cyclic.insert(*key);
            }
        }

        // Relevant operators: schemas reachable from each predicate node.
        let mut relevant = HashMap::new();
        for (position, key) in predicates.iter().enumerate() {
            let mut seen = vec![false; total];
            let mut stack = vec![position];
            seen[position] = true;
            let mut schemas = HashSet::new();
            while let Some(node) = stack.pop() {
                if node >= n_predicates {
                    schemas.insert(node - n_predicates);
                }
                for &next in &adjacency[node] {
                    if !seen[next] {
                        seen[next] = true;
                        stack.push(next);
                    }
                }
            }
            relevant.insert(*key, schemas);
        }

        OperatorGraph {
            scc,
            operators_by_scc,
            relevant,
            cyclic,
        }
    }

    /// Whether the literal's predicate node lies on a cycle — Theorem 2's
    /// filter. An open condition whose node is acyclic can never be recursive.
    pub fn may_recurse(&self, literal: &Literal) -> bool {
        self.cyclic.contains(&signed(literal))
    }

    /// Schema ids in the same SCC as the literal's predicate node.
    fn schemas_in_scc(&self, literal: &Literal) -> Option<&HashSet<usize>> {
        let component = self.scc.get(&signed(literal))?;
        self.operators_by_scc.get(*component)
    }

    /// Schema ids that could take part in achieving the literal.
    fn relevant_schemas(&self, literal: &Literal) -> Option<&HashSet<usize>> {
        self.relevant.get(&signed(literal))
    }
}

/// Iterative Tarjan, returning a component id per node. Iterative because a
/// domain's operator graph is small but a deep recursion here would be a silly
/// way to lose a run.
fn tarjan(adjacency: &[Vec<usize>]) -> Vec<usize> {
    let n = adjacency.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut component = vec![usize::MAX; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next_index = 0usize;
    let mut next_component = 0usize;

    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        // (node, next child position)
        let mut call_stack: Vec<(usize, usize)> = vec![(root, 0)];
        index[root] = next_index;
        low[root] = next_index;
        next_index += 1;
        stack.push(root);
        on_stack[root] = true;

        while let Some((node, child)) = call_stack.pop() {
            if child < adjacency[node].len() {
                call_stack.push((node, child + 1));
                let next = adjacency[node][child];
                if index[next] == usize::MAX {
                    index[next] = next_index;
                    low[next] = next_index;
                    next_index += 1;
                    stack.push(next);
                    on_stack[next] = true;
                    call_stack.push((next, 0));
                } else if on_stack[next] {
                    low[node] = low[node].min(index[next]);
                }
                continue;
            }
            // Finished `node`: fold its low-link into its parent and close the
            // component when it is a root.
            if let Some(&(parent, _)) = call_stack.last() {
                low[parent] = low[parent].min(low[node]);
            }
            if low[node] == index[node] {
                while let Some(member) = stack.pop() {
                    on_stack[member] = false;
                    component[member] = next_component;
                    if member == node {
                        break;
                    }
                }
                next_component += 1;
            }
        }
    }
    component
}

/// The links a recursion regresses through, plus the steps inside the loop.
#[derive(Debug, Clone)]
pub struct Recursion {
    /// The links `Sᵢ --C--> Sⱼ` every causal-link path to the goal must cross.
    pub root_links: Vec<Link>,
    /// Steps on a causal-link path from the open condition's step up to a root
    /// link's producer, inclusive: the loop region.
    pub region: HashSet<usize>,
}

/// Causal-link adjacency shared by the recursion tests for one plan.
/// Dense step IDs allow vector adjacency and bitmap reachability sets.
struct LinkIndex {
    /// Outgoing links per slot.
    forward: Vec<Vec<Link>>,
    /// Producer slots per consumer slot.
    backward: Vec<Vec<usize>>,
    /// Slots from which the goal is reachable along causal links.
    to_goal: Vec<bool>,
    /// Slot the goal step occupies.
    goal_slot: usize,
}

impl LinkIndex {
    fn build(plan: &Plan) -> Self {
        let goal_slot = plan.num_steps() + 1;
        let size = goal_slot + 1;
        let mut forward: Vec<Vec<Link>> = vec![Vec::new(); size];
        let mut backward: Vec<Vec<usize>> = vec![Vec::new(); size];
        for link in chain::iter(&plan.links) {
            let from = slot(link.from_id, goal_slot);
            let to = slot(link.to_id, goal_slot);
            if from >= size || to >= size {
                continue;
            }
            forward[from].push(link.clone());
            backward[to].push(from);
        }
        let to_goal = reachable_backward(&backward, [goal_slot]);
        LinkIndex {
            forward,
            backward,
            to_goal,
            goal_slot,
        }
    }

    fn slot(&self, id: usize) -> usize {
        slot(id, self.goal_slot)
    }

    fn out(&self, slot: usize) -> &[Link] {
        self.forward.get(slot).map_or(&[], Vec::as_slice)
    }
}

/// Maps a step id onto its dense slot. The goal sits just past the real steps.
fn slot(id: usize, goal_slot: usize) -> usize {
    if id == GOAL_ID {
        goal_slot
    } else {
        id
    }
}

/// Everything reachable by walking `backward` from the given seeds.
fn reachable_backward<I: IntoIterator<Item = usize>>(
    backward: &[Vec<usize>],
    seeds: I,
) -> Vec<bool> {
    let mut seen = vec![false; backward.len()];
    let mut stack: Vec<usize> = Vec::new();
    for seed in seeds {
        if seed < seen.len() && !seen[seed] {
            seen[seed] = true;
            stack.push(seed);
        }
    }
    while let Some(node) = stack.pop() {
        for &source in &backward[node] {
            if !seen[source] {
                seen[source] = true;
                stack.push(source);
            }
        }
    }
    seen
}

/// Everything reachable by walking `forward` from `start`.
fn reachable_forward(index: &LinkIndex, start: usize) -> Vec<bool> {
    let mut seen = vec![false; index.forward.len()];
    if start >= seen.len() {
        return seen;
    }
    seen[start] = true;
    let mut stack = vec![start];
    while let Some(node) = stack.pop() {
        for link in index.out(node) {
            let to = index.slot(link.to_id);
            if to < seen.len() && !seen[to] {
                seen[to] = true;
                stack.push(to);
            }
        }
    }
    seen
}

/// Whether the goal is reachable from `start` along causal links without
/// crossing a link whose condition equals `cut`.
fn goal_reachable_avoiding(index: &LinkIndex, start: usize, cut: &Literal) -> bool {
    let start = index.slot(start);
    let mut seen = vec![false; index.forward.len()];
    if start >= seen.len() {
        return false;
    }
    seen[start] = true;
    let mut stack = vec![start];
    while let Some(node) = stack.pop() {
        if node == index.goal_slot {
            return true;
        }
        for link in index.out(node) {
            if link.condition.as_ref() == cut {
                continue;
            }
            let to = index.slot(link.to_id);
            if to < seen.len() && !seen[to] {
                seen[to] = true;
                stack.push(to);
            }
        }
    }
    false
}

/// Identifies the recursion an open condition sits in, if it is exactly
/// recursive — Definition 1.
pub fn recursion_of(plan: &Plan, open_cond: &OpenCondition) -> Option<Recursion> {
    recursion_in(plan, &LinkIndex::build(plan), open_cond)
}

fn recursion_in(plan: &Plan, index: &LinkIndex, open_cond: &OpenCondition) -> Option<Recursion> {
    let condition = open_cond.literal()?;

    // Condition 1: every causal-link path from the open condition's step to the
    // goal crosses a link labelled with the same condition. Equivalently, the
    // goal is unreachable once those links are cut — and at least one such link
    // actually lies on a path to the goal.
    if goal_reachable_avoiding(index, open_cond.step_id, &condition) {
        return None;
    }
    let forward = reachable_forward(index, index.slot(open_cond.step_id));
    let root_links: Vec<Link> = chain::iter(&plan.links)
        .filter(|link| {
            let producer = index.slot(link.from_id);
            link.condition.as_ref() == &condition
                && index.to_goal.get(producer).copied().unwrap_or(false)
                && forward.get(producer).copied().unwrap_or(false)
        })
        .cloned()
        .collect();
    if root_links.is_empty() {
        return None;
    }

    // Condition 2: the root-link producers are mutually unordered.
    for (i, left) in root_links.iter().enumerate() {
        for right in &root_links[i + 1..] {
            if left.from_id == right.from_id {
                continue;
            }
            let ordered = !plan.orderings.possibly_after(
                left.from_id,
                StepTime::AtEnd,
                right.from_id,
                StepTime::AtStart,
            ) || !plan.orderings.possibly_after(
                right.from_id,
                StepTime::AtEnd,
                left.from_id,
                StepTime::AtStart,
            );
            if ordered {
                return None;
            }
        }
    }

    // The loop region: everything on a causal-link path from the open
    // condition's step up to a root-link producer. Two set operations rather
    // than a reachability query per candidate step.
    let reaches_producer = reachable_backward(
        &index.backward,
        root_links.iter().map(|link| index.slot(link.from_id)),
    );
    let region: HashSet<usize> = chain::iter(&plan.steps)
        .map(|step| step.id)
        .chain([INIT_ID, GOAL_ID])
        .filter(|&id| {
            let s = index.slot(id);
            forward.get(s).copied().unwrap_or(false)
                && reaches_producer.get(s).copied().unwrap_or(false)
        })
        .collect();

    Some(Recursion { root_links, region })
}

/// Whether some step in the plan is a *loop threat* for a recursion —
/// Definition 3, read generously.
///
/// A loop threat re-enables a suspended condition, so treating too many steps
/// as loop threats suspends less and prunes less; treating too few would prune
/// a plan that had to be kept. Any step with an effect that may clobber the
/// condition and that is not already ordered after the whole loop therefore
/// counts.
fn has_loop_threat(plan: &Plan, condition: &Literal, recursion: &Recursion) -> bool {
    for step in chain::iter(&plan.steps) {
        if recursion.region.contains(&step.id) {
            continue;
        }
        let threatens = step
            .action
            .effects
            .iter()
            .any(|effect| effect.literal.may_affect(condition));
        if !threatens {
            continue;
        }
        // Ordered strictly after every root link's consumer? Then it can never
        // land inside the loop.
        let after_everything = recursion.root_links.iter().all(|link| {
            !plan
                .orderings
                .possibly_before(step.id, StepTime::AtEnd, link.to_id, StepTime::AtStart)
        });
        if !after_everything {
            return true;
        }
    }
    false
}

/// Whether a causal link runs out of the loop region to a consumer outside it —
/// Smith & Peot's first re-enabling event ("a causal link is added from a step
/// between `C` and one of its root links to an open condition outside the
/// loop").
fn links_out_of_region(plan: &Plan, recursion: &Recursion) -> bool {
    let root_consumers: HashSet<usize> =
        recursion.root_links.iter().map(|link| link.to_id).collect();
    chain::iter(&plan.links).any(|link| {
        recursion.region.contains(&link.from_id)
            && !recursion.region.contains(&link.to_id)
            && !root_consumers.contains(&link.to_id)
    })
}

/// Whether an open condition is currently suspended.
pub fn is_suspended(ctx: &SearchContext, plan: &Plan, open_cond: &OpenCondition) -> bool {
    suspension_of(ctx, plan, open_cond).is_some()
}

/// The recursion suspending an open condition, if any.
pub fn suspension_of(
    ctx: &SearchContext,
    plan: &Plan,
    open_cond: &OpenCondition,
) -> Option<Recursion> {
    suspension_in(ctx, plan, &LinkIndex::build(plan), open_cond)
}

fn suspension_in(
    ctx: &SearchContext,
    plan: &Plan,
    index: &LinkIndex,
    open_cond: &OpenCondition,
) -> Option<Recursion> {
    let condition = open_cond.literal()?;
    if !ctx.operator_graph().may_recurse(&condition) {
        return None;
    }
    let recursion = recursion_in(plan, index, open_cond)?;
    if links_out_of_region(plan, &recursion) {
        return None;
    }
    if has_loop_threat(plan, &condition, &recursion) {
        return None;
    }
    Some(recursion)
}

/// Whether an open condition is a *loop predecessor* of a recursion —
/// Definition 2: every causal-link path from it to the goal crosses a root link.
fn is_loop_predecessor(
    index: &LinkIndex,
    open_cond: &OpenCondition,
    recursion: &Recursion,
) -> bool {
    let roots: HashSet<(usize, usize)> = recursion
        .root_links
        .iter()
        .map(|link| (link.from_id, link.to_id))
        .collect();
    let start = index.slot(open_cond.step_id);
    let mut seen = vec![false; index.forward.len()];
    if start >= seen.len() {
        return true;
    }
    seen[start] = true;
    let mut stack = vec![start];
    while let Some(node) = stack.pop() {
        if node == index.goal_slot {
            return false;
        }
        for link in index.out(node) {
            if roots.contains(&(link.from_id, link.to_id)) {
                continue;
            }
            let to = index.slot(link.to_id);
            if to < seen.len() && !seen[to] {
                seen[to] = true;
                stack.push(to);
            }
        }
    }
    true
}

/// Whether the plan can be discarded by Theorem 1 or Theorem 4.
pub fn prunable(ctx: &SearchContext, plan: &Plan) -> bool {
    // Theorem 2's filter, applied before anything is allocated: a recursion
    // needs a causal-link path to regress through, and an open condition whose
    // predicate node lies on no cycle can never be recursive. Most plans in
    // most domains stop here.
    if plan.num_links == 0 || plan.num_open_conds() == 0 {
        return false;
    }
    let graph = ctx.operator_graph();

    // A second filter, and the one that earns its keep: *exact* recursion
    // regresses an open condition through a link carrying the syntactically
    // same condition, so unless such a link is already in the plan there is no
    // root link and nothing to suspend. Checking that costs a scan over the
    // links; the alternative is building the link index and running a graph
    // search per open condition, which is what the rule used to do on every
    // node whether or not a recursion was possible.
    //
    // The predicate pass runs first because it compares two integers where the
    // structural pass compares a predicate and a term vector.
    let any_candidate = chain::iter(&plan.open_conds).any(|oc| {
        // Read the predicate off the formula rather than through
        // `OpenCondition::literal`, which clones the atom's term vector — this
        // runs for every open condition of every generated node.
        let Some(key) = open_condition_predicate(oc) else {
            return false;
        };
        if !graph.cyclic.contains(&key) {
            return false;
        }
        chain::iter(&plan.links).any(|link| {
            signed(&link.condition) == key
                && oc
                    .literal()
                    .is_some_and(|literal| link.condition.as_ref() == &literal)
        })
    });
    if !any_candidate {
        return false;
    }

    let index = LinkIndex::build(plan);
    let Some((anchor, recursion)) = chain::iter(&plan.open_conds).find_map(|oc| {
        suspension_in(ctx, plan, &index, oc).map(|recursion| (oc.clone(), recursion))
    }) else {
        return false;
    };

    // Theorem 1: all open conditions suspended (as recursions in their own
    // right, or as loop predecessors of one) and no unresolved threats.
    if plan.num_unsafes() == 0 {
        let all_suspended = chain::iter(&plan.open_conds).all(|oc| {
            oc == &anchor
                || is_loop_predecessor(&index, oc, &recursion)
                || suspension_in(ctx, plan, &index, oc).is_some()
        });
        if all_suspended {
            return true;
        }
    }

    theorem_four(ctx, plan, &anchor, &recursion)
}

/// Theorem 4: prune while open conditions remain, when none of them can reach
/// into the loop or threaten a root link.
fn theorem_four(
    ctx: &SearchContext,
    plan: &Plan,
    anchor: &OpenCondition,
    recursion: &Recursion,
) -> bool {
    let graph = ctx.operator_graph();
    let Some(anchor_literal) = anchor.literal() else {
        return false;
    };
    let Some(scc_schemas) = graph.schemas_in_scc(&anchor_literal) else {
        return false;
    };

    // R: operators relevant to the remaining open conditions.
    let mut relevant: HashSet<usize> = HashSet::new();
    for oc in chain::iter(&plan.open_conds) {
        if oc == anchor {
            continue;
        }
        let Some(literal) = oc.literal() else {
            // A disjunction or an inequality has no single predicate node; be
            // safe and decline to prune.
            return false;
        };
        match graph.relevant_schemas(&literal) {
            Some(schemas) => relevant.extend(schemas.iter().copied()),
            None => return false,
        }
    }

    // (1) No operator in R appears in the SCC of C.
    if relevant.iter().any(|schema| scc_schemas.contains(schema)) {
        return false;
    }

    // (2) No operator in R threatens any root link.
    for &schema_id in &relevant {
        let action = &ctx.domain.actions[schema_id];
        for effect in &action.effects {
            for link in &recursion.root_links {
                if effect.literal.may_affect(&link.condition) {
                    return false;
                }
            }
        }
    }

    // (3) No unresolved threat to a root link.
    for unsafe_ in chain::iter(&plan.unsafes) {
        if recursion
            .root_links
            .iter()
            .any(|link| link == &unsafe_.link)
        {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{lower_domain, read_pddl, ParsedUnit};

    const TRAVEL: &str = r#"
    (define (domain travel)
      (:requirements :strips :typing)
      (:types loc)
      (:predicates (at ?l - loc) (road ?a - loc ?b - loc) (rested))
      (:action drive
        :parameters (?from - loc ?to - loc)
        :precondition (and (at ?from) (road ?from ?to))
        :effect (and (not (at ?from)) (at ?to)))
      (:action sleep
        :parameters ()
        :precondition ()
        :effect (rested)))
    "#;

    fn domain(src: &str) -> Domain {
        match read_pddl(src).expect("parse domain") {
            ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
            _ => panic!("expected a domain"),
        }
    }

    #[test]
    fn drive_puts_at_on_a_cycle_and_leaves_rested_off_it() {
        let domain = domain(TRAVEL);
        let graph = OperatorGraph::build(&domain);
        let at = domain
            .predicates
            .find_predicate("at")
            .expect("predicate `at`");
        let rested = domain
            .predicates
            .find_predicate("rested")
            .expect("predicate `rested`");
        assert!(graph.may_recurse(&Literal::Atom(crate::formula::Atom {
            predicate: at,
            terms: vec![],
        })));
        assert!(!graph.may_recurse(&Literal::Atom(crate::formula::Atom {
            predicate: rested,
            terms: vec![],
        })));
    }

    #[test]
    fn a_static_predicate_is_never_cyclic() {
        let domain = domain(TRAVEL);
        let graph = OperatorGraph::build(&domain);
        let road = domain
            .predicates
            .find_predicate("road")
            .expect("predicate `road`");
        assert!(!graph.may_recurse(&Literal::Atom(crate::formula::Atom {
            predicate: road,
            terms: vec![],
        })));
    }
}
