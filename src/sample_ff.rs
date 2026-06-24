//! The Sample-FF heuristic for partial-order causal-link plans (Bercher, Geier,
//! Richter & Biundo, 2013: "On Delete Relaxation in Partial-Order Causal-Link
//! Planning"). Unlike the Relax heuristic — which delete-relaxes the *whole*
//! partial plan, ignoring the plan steps' negative effects and quantities —
//! Sample-FF keeps the committed plan steps non-relaxed and uses delete
//! relaxation only to fill the gaps between them.
//!
//! ## Algorithm (paper §IV)
//! For a partial plan `P = (PS, ≺, CL)`:
//! 1. **Sample** a constant `K` of total-order linearizations of the committed
//!    steps consistent with `≺` (the paper uses MCMC over the linearization
//!    graph for near-uniform sampling; we use randomized topological sort, which
//!    is cheaper and sufficient here).
//! 2. **Estimate** each linearization `z = init, a₁, …, aₙ, goal`. Build a
//!    saturated relaxed planning graph from `init`; its last (fixpoint) fact
//!    layer `F₀` must contain `pre(a₁)`, else `z` is infeasible. Apply `a₁`
//!    *non-relaxed* in that layer — `s₁ = (F₀ \ del(a₁)) ∪ add(a₁)` — and build
//!    `F₁` from `s₁`; and so on. `z` is feasible iff every `pre(aᵢ₊₁) ⊆ Fᵢ` and
//!    the goal `⊆ Fₙ`. The estimate is the total number of relaxed plan steps
//!    needed to fill all the gaps, computed by a back-to-front chained FF
//!    extraction: extract a relaxed plan for the goal in `Fₙ`; the base facts it
//!    bottoms out on that are *not* provided by `aₙ`'s adds — together with
//!    `pre(aₙ)` — become the goals for `Fₙ₋₁`; recurse to `F₀`.
//! 3. **Combine** by the minimum over the sampled linearizations. If *none* is
//!    feasible we cannot conclude the plan is dead (sampling is not exhaustive),
//!    so — like the paper — we fall back to the number of open conditions rather
//!    than `∞`.
//!
//! This first implementation targets the paper's best configuration: ground
//! representation, no causal-link filtering ("front: ⊥ end: ⊥"), `K = 10`
//! samples. Causal-link respecting (the `active`-links action filtering of §IV-D)
//! and lifted partial plans (the paper's stated future work) are not yet done; in
//! lifted search the heuristic falls back to the open-condition count.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::chain;
use crate::formula::{Atom, Formula};
use crate::orderings::StepTime;
use crate::plan::Plan;
use crate::search::SearchContext;
use crate::terms::{Object, Term};

/// Default number of sampled linearizations (the paper's best-performing `K`).
pub const DEFAULT_SAMPLES: usize = 10;

/// A delete-relaxed ground action effect: produce `add` when `pre` all hold.
/// One per positive (possibly conditional) effect of a ground domain action;
/// negative effects are dropped (delete relaxation), statically-false conditional
/// effects are omitted at build time, and a conditional effect's fluent
/// condition atoms are folded into `pre`.
#[derive(Debug)]
struct RAction {
    pre: Vec<usize>,
    add: usize,
}

/// A committed plan step resolved to ground facts for non-relaxed application.
#[derive(Debug)]
struct ResolvedStep {
    pre: Vec<usize>,
    add: Vec<usize>,
    del: Vec<usize>,
}

/// The problem-constant Sample-FF model: the interned ground facts, the initial
/// state and goal, the delete-relaxed ground action set used to fill gaps, and a
/// cached saturated reachability from the initial state (the paper's
/// "precomputing a fixed point for the initial state" optimization). Cached on
/// the [`SearchContext`]; rebuilt never within a run.
pub struct SampleFfModel {
    /// Ground fact id ↦ initial truth.
    init: Vec<bool>,
    /// `(predicate, args)` ↦ fact id.
    map: HashMap<(crate::predicates::Predicate, Vec<Object>), usize>,
    /// Positive goal facts.
    goal: Vec<usize>,
    /// Delete-relaxed ground actions (gap fillers).
    relaxed: Vec<RAction>,
    /// Saturated reachability from the initial state.
    init_reach: Reach,
}

/// Saturated relaxed reachability from some state: the reached fact set and, for
/// each reached fact, the index of a relaxed action achieving it (none for facts
/// already true in the seed state).
#[derive(Debug, Clone)]
struct Reach {
    reached: Vec<bool>,
    achiever: Vec<Option<usize>>,
}

impl SampleFfModel {
    /// Builds the model from the problem's ground actions (no external tools —
    /// Sample-FF is pure Rust). Uses the naive ground action set; reachability
    /// pruning falls out of the relaxed fixpoint anyway.
    pub fn build(ctx: &SearchContext) -> SampleFfModel {
        let mut map: HashMap<(crate::predicates::Predicate, Vec<Object>), usize> = HashMap::new();
        let mut init: Vec<bool> = Vec::new();
        let intern = |map: &mut HashMap<_, _>,
                          init: &mut Vec<bool>,
                          pred: crate::predicates::Predicate,
                          args: Vec<Object>| {
            let atom = Atom {
                predicate: pred,
                terms: args.iter().map(|&o| Term::Object(o)).collect(),
            };
            let key = (pred, args);
            if let Some(&id) = map.get(&key) {
                return id;
            }
            let id = init.len();
            init.push(ctx.problem.init_atoms.contains(&atom));
            map.insert(key, id);
            id
        };

        // Delete-relaxed ground actions: one RAction per positive effect.
        let mut relaxed: Vec<RAction> = Vec::new();
        for ga in ctx.ground_actions() {
            let Some(base_pre) = positive_atoms(&ga.precondition) else {
                continue; // statically inconsistent
            };
            let base_pre_ids: Vec<usize> = base_pre
                .into_iter()
                .map(|(p, a)| intern(&mut map, &mut init, p, a))
                .collect();
            for e in &ga.effects {
                if e.literal.negative() || !e.parameters.is_empty() {
                    continue;
                }
                let Some(cond) = static_eval_condition(&e.condition) else {
                    continue; // condition statically false
                };
                let Some(atom_args) = all_objects(&e.literal.atom().terms) else {
                    continue;
                };
                let mut pre = base_pre_ids.clone();
                for (p, a) in cond {
                    pre.push(intern(&mut map, &mut init, p, a));
                }
                let add = intern(&mut map, &mut init, e.literal.atom().predicate, atom_args);
                relaxed.push(RAction { pre, add });
            }
        }

        // Goal facts (positive; negatives relaxed away).
        let mut goal: Vec<usize> = Vec::new();
        if let Some(atoms) = positive_atoms(&ctx.problem.goal) {
            for (p, a) in atoms {
                goal.push(intern(&mut map, &mut init, p, a));
            }
        }

        let init_reach = saturate(&init, &relaxed, init.len());
        SampleFfModel {
            init,
            map,
            goal,
            relaxed,
            init_reach,
        }
    }
}

/// Computes the Sample-FF rank term `num_steps + weight * h` for `plan`. `h` is
/// the minimum relaxed-gap estimate over `k` sampled linearizations (or the open
/// condition count when no sample is feasible). Ground search only; lifted plans
/// fall back to `num_steps + weight * num_open_conds`.
pub fn sample_ff_rank(plan: &Plan, ctx: &SearchContext, weight: f32, k: usize) -> f32 {
    if !ctx.params.ground_actions {
        return plan.num_steps() as f32 + weight * plan.num_open_conds() as f32;
    }
    let model = ctx.sample_ff_model();

    // Resolve committed steps (skip init/goal) and their ordering relation.
    let committed: Vec<&crate::plan::Step> = chain::iter(&plan.steps)
        .filter(|s| !s.action.synthetic())
        .collect();

    // Intern committed-step facts against a clone of the model map (committed
    // steps are ground domain-action instances, so this almost never extends the
    // fact set; when it does, init reachability is recomputed for the new size).
    let mut map = model.map.clone();
    let mut init = model.init.clone();
    let resolved: Vec<ResolvedStep> = committed
        .iter()
        .map(|s| resolve_step(&s.action, &mut map, &mut init))
        .collect();
    let nfacts = init.len();
    let init_reach = if nfacts == model.init.len() {
        // No new facts: reuse the cached init fixed point.
        std::borrow::Cow::Borrowed(&model.init_reach)
    } else {
        std::borrow::Cow::Owned(saturate(&init, &model.relaxed, nfacts))
    };

    let order: Vec<usize> = committed.iter().map(|s| s.id).collect();
    let n = order.len();

    // No committed steps: the estimate is the relaxed plan straight from init.
    if n == 0 {
        let h = match extract(&init_reach, &init, &model.goal, &model.relaxed) {
            Some((count, _)) => count as f32,
            None => plan.num_open_conds() as f32,
        };
        return plan.num_steps() as f32 + weight * h;
    }

    // Step id ↦ index into `committed`/`resolved`, for mapping a sampled
    // linearization (a sequence of ids) back to resolved steps in O(1).
    let pos_of: HashMap<usize, usize> =
        committed.iter().enumerate().map(|(i, s)| (s.id, i)).collect();

    let mut rng = Rng::seed(plan);
    let mut best: Option<usize> = None;
    for _ in 0..k {
        let lin = sample_linearization(plan, &order, &mut rng);
        let steps: Vec<&ResolvedStep> = lin.iter().map(|&id| &resolved[pos_of[&id]]).collect();
        if let Some(est) =
            estimate_linearization(&init, &init_reach, &steps, &model.goal, &model.relaxed, nfacts)
        {
            best = Some(best.map_or(est, |b| b.min(est)));
        }
    }

    let h = match best {
        Some(est) => est as f32,
        // No feasible sample: not provably dead, fall back to #open-conditions.
        None => plan.num_open_conds() as f32,
    };
    plan.num_steps() as f32 + weight * h
}

/// Estimates one linearization (paper §IV-B): the total relaxed plan steps to
/// fill the gaps between the non-relaxed steps. `None` if infeasible (some step's
/// precondition or the goal is unreachable in the relevant fixpoint).
fn estimate_linearization(
    init: &[bool],
    init_reach: &Reach,
    steps: &[&ResolvedStep],
    goal: &[usize],
    relaxed: &[RAction],
    nfacts: usize,
) -> Option<usize> {
    let n = steps.len();

    // Forward pass: states s₀..sₙ and their saturated fixpoints F₀..Fₙ.
    let mut states: Vec<Vec<bool>> = Vec::with_capacity(n + 1);
    let mut reaches: Vec<Reach> = Vec::with_capacity(n + 1);
    states.push(init.to_vec());
    reaches.push(init_reach.clone());
    for (i, step) in steps.iter().enumerate() {
        // pre(aᵢ₊₁) must hold in the current fixpoint Fᵢ.
        if !step.pre.iter().all(|&p| reaches[i].reached[p]) {
            return None;
        }
        // sᵢ₊₁ = (Fᵢ \ del) ∪ add, applied in the saturated layer.
        let mut s = reaches[i].reached.clone();
        for &d in &step.del {
            s[d] = false;
        }
        for &a in &step.add {
            s[a] = true;
        }
        let r = saturate(&s, relaxed, nfacts);
        states.push(s);
        reaches.push(r);
    }

    // Goal must be reachable in the last fixpoint.
    if !goal.iter().all(|&g| reaches[n].reached[g]) {
        return None;
    }

    // Backward chained extraction.
    let mut total = 0usize;
    let mut goals: Vec<usize> = goal.to_vec();
    for i in (0..=n).rev() {
        let (count, base_reqs) = extract(&reaches[i], &states[i], &goals, relaxed)?;
        total += count;
        if i > 0 {
            // sᵢ was produced by step i-1 from Fᵢ₋₁. Base facts provided by that
            // step's adds are free; the rest must be re-achieved in Fᵢ₋₁, along
            // with the step's own precondition.
            let step = steps[i - 1];
            let add: HashSet<usize> = step.add.iter().copied().collect();
            let mut next: HashSet<usize> = base_reqs
                .into_iter()
                .filter(|r| !add.contains(r))
                .collect();
            next.extend(step.pre.iter().copied());
            goals = next.into_iter().collect();
        }
    }
    Some(total)
}

/// Greedy FF relaxed-plan extraction in one fixpoint. Returns the number of
/// distinct relaxed actions chosen and the set of seed-state facts the plan
/// bottoms out on. `None` if a goal is unreachable (no achiever and not in the
/// seed state).
fn extract(
    reach: &Reach,
    state: &[bool],
    goals: &[usize],
    relaxed: &[RAction],
) -> Option<(usize, HashSet<usize>)> {
    let mut chosen: HashSet<usize> = HashSet::new();
    let mut base_reqs: HashSet<usize> = HashSet::new();
    let mut done: HashSet<usize> = HashSet::new();
    let mut queue: Vec<usize> = goals.to_vec();
    while let Some(g) = queue.pop() {
        if !done.insert(g) {
            continue;
        }
        if state[g] {
            base_reqs.insert(g);
            continue;
        }
        match reach.achiever[g] {
            Some(a) => {
                if chosen.insert(a) {
                    for &p in &relaxed[a].pre {
                        if !done.contains(&p) {
                            queue.push(p);
                        }
                    }
                }
            }
            None => return None, // unreachable subgoal
        }
    }
    Some((chosen.len(), base_reqs))
}

/// Saturated relaxed reachability from `state` over `relaxed`, recording the
/// first achiever of each newly reached fact. Facts true in `state` have no
/// achiever.
fn saturate(state: &[bool], relaxed: &[RAction], nfacts: usize) -> Reach {
    let mut reached = vec![false; nfacts];
    let achiever = vec![None; nfacts];
    for (i, &t) in state.iter().enumerate() {
        if t {
            reached[i] = true;
        }
    }
    let mut reach = Reach { reached, achiever };
    let mut changed = true;
    while changed {
        changed = false;
        for (ai, action) in relaxed.iter().enumerate() {
            if reach.reached[action.add] {
                continue;
            }
            if action.pre.iter().all(|&p| reach.reached[p]) {
                reach.reached[action.add] = true;
                reach.achiever[action.add] = Some(ai);
                changed = true;
            }
        }
    }
    reach
}

/// Samples a single linearization: a randomized topological sort of the committed
/// step ids respecting the plan's orderings.
fn sample_linearization(plan: &Plan, order: &[usize], rng: &mut Rng) -> Vec<usize> {
    let n = order.len();
    // indegree[i] = number of committed steps that must precede order[i].
    let mut indeg = vec![0usize; n];
    let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n];
    for a in 0..n {
        for b in 0..n {
            if a != b && necessarily_before(plan, order[a], order[b]) {
                succ[a].push(b);
                indeg[b] += 1;
            }
        }
    }
    let mut ready: Vec<usize> = (0..n).filter(|&i| indeg[i] == 0).collect();
    let mut out: Vec<usize> = Vec::with_capacity(n);
    while !ready.is_empty() {
        let pick = rng.below(ready.len());
        let i = ready.swap_remove(pick);
        out.push(order[i]);
        for &j in &succ[i] {
            indeg[j] -= 1;
            if indeg[j] == 0 {
                ready.push(j);
            }
        }
    }
    out
}

/// Whether `lp` necessarily precedes `l` under the plan's orderings (`lp ≺ l`).
fn necessarily_before(plan: &Plan, lp: usize, l: usize) -> bool {
    !plan
        .orderings
        .possibly_after(lp, StepTime::AtEnd, l, StepTime::AtEnd)
}

/// Resolves a ground committed step into ground fact ids: positive preconditions,
/// and the add/delete sets with statically-evaluated conditional effects applied.
/// Interns any not-yet-seen facts into `map`/`init`.
fn resolve_step(
    action: &crate::plan::StepAction,
    map: &mut HashMap<(crate::predicates::Predicate, Vec<Object>), usize>,
    init: &mut Vec<bool>,
) -> ResolvedStep {
    let intern = |map: &mut HashMap<_, _>,
                      init: &mut Vec<bool>,
                      pred: crate::predicates::Predicate,
                      args: Vec<Object>| {
        let key = (pred, args);
        if let Some(&id) = map.get(&key) {
            return id;
        }
        let id = init.len();
        init.push(false); // not interned during model build ⇒ not in initial state
        map.insert(key, id);
        id
    };

    let pre = positive_atoms(&action.precondition)
        .map(|v| {
            v.into_iter()
                .map(|(p, a)| intern(map, init, p, a))
                .collect()
        })
        .unwrap_or_default();

    let mut add = Vec::new();
    let mut del = Vec::new();
    for e in &action.effects {
        if !e.parameters.is_empty() {
            continue; // no quantified effects in the ground classical subset
        }
        // Ground conditional effects in the target domains carry only static
        // (in)equalities; a statically-false condition drops the effect.
        if static_eval_condition(&e.condition).is_none() {
            continue;
        }
        let Some(args) = all_objects(&e.literal.atom().terms) else {
            continue;
        };
        let id = intern(map, init, e.literal.atom().predicate, args);
        if e.literal.negative() {
            del.push(id);
        } else {
            add.push(id);
        }
    }
    ResolvedStep { pre, add, del }
}

/// Collects the positive ground atoms of a precondition/goal conjunction as
/// `(predicate, args)`. Negative literals and satisfied (in)equalities are
/// dropped (relaxation); a violated ground (in)equality makes the whole formula
/// statically false, returning `None`.
fn positive_atoms(f: &Rc<Formula>) -> Option<Vec<(crate::predicates::Predicate, Vec<Object>)>> {
    fn go(
        f: &Rc<Formula>,
        out: &mut Vec<(crate::predicates::Predicate, Vec<Object>)>,
    ) -> bool {
        match f.as_ref() {
            Formula::True => true,
            Formula::False => false,
            Formula::Atom(a) => {
                if let Some(args) = all_objects(&a.terms) {
                    out.push((a.predicate, args));
                }
                true
            }
            Formula::Negation(_) => true, // relaxed away
            Formula::Equality { left, right, .. } => match (obj(*left), obj(*right)) {
                (Some(a), Some(b)) => a == b,
                _ => true,
            },
            Formula::Inequality { left, right, .. } => match (obj(*left), obj(*right)) {
                (Some(a), Some(b)) => a != b,
                _ => true,
            },
            Formula::Conjunction(cs) => cs.iter().all(|c| go(c, out)),
            _ => true, // disjunctions/quantifiers: no constraint (relaxation)
        }
    }
    let mut out = Vec::new();
    if go(f, &mut out) {
        Some(out)
    } else {
        None
    }
}

/// Evaluates an effect condition's static (in)equalities, returning its positive
/// fluent condition atoms (to fold into a relaxed action's precondition), or
/// `None` if the condition is statically false. Negative fluent conditions are
/// relaxed away.
fn static_eval_condition(
    f: &Rc<Formula>,
) -> Option<Vec<(crate::predicates::Predicate, Vec<Object>)>> {
    positive_atoms(f)
}

fn all_objects(args: &[Term]) -> Option<Vec<Object>> {
    args.iter()
        .map(|t| match t {
            Term::Object(o) => Some(*o),
            Term::Variable(_) => None,
        })
        .collect()
}

fn obj(t: Term) -> Option<Object> {
    match t {
        Term::Object(o) => Some(o),
        Term::Variable(_) => None,
    }
}

/// A small deterministic SplitMix64 PRNG. Sample-FF needs randomized
/// linearizations but reproducible runs/tests, so the seed is derived from the
/// plan's shape rather than wall-clock entropy.
struct Rng(u64);

impl Rng {
    fn seed(plan: &Plan) -> Rng {
        let s = 0x9E37_79B9_7F4A_7C15u64
            ^ (plan.num_steps() as u64)
            ^ ((plan.num_open_conds() as u64) << 17)
            ^ ((plan.serial_no() as u64) << 33);
        Rng(s)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// p false in init, one relaxed action with no preconditions adds it. The
    /// saturated layer reaches p, with that action as its achiever.
    #[test]
    fn saturate_reaches_via_action() {
        let init = vec![false]; // fact 0 = p
        let relaxed = vec![RAction { pre: vec![], add: 0 }];
        let r = saturate(&init, &relaxed, 1);
        assert!(r.reached[0]);
        assert_eq!(r.achiever[0], Some(0));
    }

    /// Two-step chain q ← a1 ← a0: extracting a relaxed plan for q from the empty
    /// state picks both actions (count 2); facts already true cost nothing.
    #[test]
    fn extract_counts_chain() {
        // facts: 0 = p, 1 = q. a0: {} -> p ; a1: {p} -> q.
        let init = vec![false, false];
        let relaxed = vec![
            RAction { pre: vec![], add: 0 },
            RAction { pre: vec![0], add: 1 },
        ];
        let reach = saturate(&init, &relaxed, 2);
        let (count, base) = extract(&reach, &init, &[1], &relaxed).unwrap();
        assert_eq!(count, 2);
        assert!(base.is_empty());

        // With p already in the state, only a1 is needed and p is a base req.
        let state = vec![true, false];
        let reach2 = saturate(&state, &relaxed, 2);
        let (count2, base2) = extract(&reach2, &state, &[1], &relaxed).unwrap();
        assert_eq!(count2, 1);
        assert_eq!(base2.into_iter().collect::<Vec<_>>(), vec![0]);
    }

    /// An unreachable goal yields `None` from extraction (a relaxed dead end).
    #[test]
    fn extract_unreachable_is_none() {
        let init = vec![false, false];
        let relaxed = vec![RAction { pre: vec![], add: 0 }];
        let reach = saturate(&init, &relaxed, 2);
        assert!(extract(&reach, &init, &[1], &relaxed).is_none());
    }
}
