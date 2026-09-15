//! The Lplan linear-programming heuristic (Bylander, AAAI 1997: "A Linear
//! Programming Heuristic for Optimal Planning") applied to our causal-link
//! compilation.
//!
//! Bylander translates a propositional STRIPS instance with a plan-length bound
//! `l` into a time-indexed 0-1 integer program — conditions `p(t)` and operators
//! `op(t)` at each time point, with precondition, frame-axiom and "at most one
//! operator per step" constraints — and *relaxes* it to a linear program over
//! `[0,1]`. If the relaxed LP at length `l` is infeasible then no plan of length
//! `≤ l` exists, so the smallest `l` whose relaxed LP is feasible is an
//! **admissible** lower bound on the plan length. This was the first non-trivial
//! admissible heuristic for partial-order planning.
//!
//! ## Using our causal-link compilation
//! Rather than re-deriving Bylander's separate partial-order ordering-constraint
//! LP, we feed his *state-based* encoding the **ground causal-link compilation**
//! (`crate::compile::ground_task`). That compilation already bakes the partial
//! plan into a classical task: the committed steps become forced operators (their
//! `exec-pos` indicators are goals), the partial order becomes predecessor
//! preconditions, and the causal links become guard preconditions. So the
//! smallest horizon `l` for which the compiled task's relaxed LP reaches the
//! goal `g'` is an admissible estimate of the *total* length of any completion of
//! the partial plan — exactly the position paper's "Lplan with our causal-link
//! compilation".
//!
//! The smallest feasible horizon `l*` is normally close to the committed-step
//! count (a completion adds only a few new steps), so we scan `l` upward from
//! that lower bound — building the smallest LPs first — and stop at the first
//! feasible one. Ground search only (the compilation's fast ground path); lifted
//! falls back to the open-condition count.

use good_lp::constraint::{eq, geq, leq};
#[cfg(feature = "highs-lp")]
use good_lp::solvers::highs::highs as lp_solver;
#[cfg(not(feature = "highs-lp"))]
use good_lp::solvers::microlp::microlp as lp_solver;
use good_lp::{Expression, ProblemVariables, ResolutionError, SolverModel, Variable};

use crate::plan::Plan;
use crate::sas::GroundTask;
use crate::search::SearchContext;

/// How many time steps beyond the committed-step lower bound to search for a
/// feasible horizon before giving up (and returning the cap as an admissible
/// underestimate). Bounds the largest LP we build per node — and, crucially, the
/// work spent on a node whose partial plan cannot complete (its scan runs to the
/// cap). Kept small: the optimum is normally within a few steps of the bound.
/// Above this many facts the pair table is not worth building; the tightenings
/// then simply contribute nothing.
const MAX_MUTEX_FACTS: usize = 512;

const HORIZON_EXTRA: usize = 6;

/// Computes the Lplan rank for `plan`: the smallest horizon whose relaxed LP over
/// the causal-link compilation reaches the goal. Admissible lower bound on the
/// total completion length (so `weight` is intentionally *not* applied). Ground
/// search only; lifted falls back to `num_steps + weight * num_open_conds`.
/// Which tightenings of Bylander's relaxation to apply.
///
/// [`Tightenings::NONE`] is the paper's encoding exactly, and is what `LPLAN`
/// uses. Each flag adds inequalities that every *integer* feasible solution
/// already satisfies, so the integer program's feasible set is unchanged and the
/// smallest feasible horizon stays an admissible lower bound; the relaxation
/// only gets tighter. Any new flag must carry that argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Tightenings {
    /// Forbid pairs of facts that hold together in no reachable state.
    ///
    /// This is the cut that attacks Bylander's "superposition": his `Σ op(t) ≤ 1`
    /// already forbids two operators summing above one at a time point, so a
    /// pairwise *operator* mutex adds nothing — his own worked example has two
    /// operators at 0.5 summing to exactly 1. The looseness is in the *facts*,
    /// which take convex combinations that correspond to no real state.
    pub fact_mutexes: bool,
    /// Add negative preconditions where sound, suppressing delete-correction
    /// variables. Bylander's own suggestion: "often, negative preconditions are
    /// added to operators if possible to avoid the creation of additional
    /// variables."
    pub negative_preconditions: bool,
    /// Encode the partial order with the paper's step variables rather than
    /// leaving it to the causal-link compilation.
    pub step_variables: bool,
    /// Sum the operators sharing a precondition into one inequality instead of
    /// posting the paper's one-per-operator form.
    ///
    /// At most one operator fires per time point, so
    /// `Σ_{i requiring f} o(t,i) ≤ p(t,f)` holds in every integer solution and
    /// dominates the individual `o(t,i) ≤ p(t,f)`, every `o` being
    /// non-negative. It also replaces one constraint per operator-precondition
    /// with one per fact, so the model shrinks as it tightens.
    pub aggregated_preconditions: bool,
}

impl Tightenings {
    /// Bylander's encoding as published.
    pub const NONE: Self = Self {
        fact_mutexes: false,
        negative_preconditions: false,
        step_variables: false,
        aggregated_preconditions: false,
    };

    /// Every tightening.
    /// Every implemented tightening. `step_variables` is not among them yet.
    pub const ALL: Self = Self {
        fact_mutexes: true,
        negative_preconditions: true,
        step_variables: false,
        aggregated_preconditions: true,
    };

    /// Parses a `+`-separated feature list, for ablation: `mutex+negpre`.
    /// An empty spec means [`Tightenings::ALL`].
    pub fn parse(spec: &str) -> Result<Self, String> {
        if spec.is_empty() {
            return Ok(Self::ALL);
        }
        let mut t = Self::NONE;
        for feature in spec.split('+') {
            match feature.to_ascii_lowercase().as_str() {
                "none" => {}
                "mutex" => t.fact_mutexes = true,
                "aggpre" => t.aggregated_preconditions = true,
                "negpre" => t.negative_preconditions = true,
                "steps" => {
                    return Err(
                        "Lplan tightening `steps` (Bylander's step-variable encoding of the \
                         partial order) is not implemented yet"
                            .to_string(),
                    )
                }
                "all" => t = Self::ALL,
                other => {
                    return Err(format!(
                        "unknown Lplan tightening `{other}` (expected none, mutex, negpre, aggpre, steps or all)"
                    ))
                }
            }
        }
        Ok(t)
    }
}

pub fn lplan_rank(plan: &Plan, ctx: &SearchContext, weight: f32, tightenings: Tightenings) -> f32 {
    if !ctx.params.ground_actions {
        return plan.num_steps() as f32 + weight * plan.num_open_conds() as f32;
    }
    let task = crate::compile::ground_task(plan, ctx);

    // Every committed step is a forced operator (its exec-pos is a goal) and at
    // most one operator fires per step, so the horizon is at least the number of
    // committed steps — a sound lower bound to start the scan from.
    let l0 = plan.num_steps();
    let cap = l0 + HORIZON_EXTRA;

    // The task is the same at every horizon, so the pair analysis is done once.
    let mutexes = if tightenings.fact_mutexes || tightenings.negative_preconditions {
        fact_mutexes(&task)
    } else {
        Vec::new()
    };
    // A fact mutex with one of an operator's positive preconditions is a
    // negative precondition that operator can be given for free — Bylander's
    // own suggestion for avoiding correction variables.
    let implied_false: Vec<Vec<usize>> = if tightenings.negative_preconditions {
        task.ops()
            .iter()
            .map(|op| {
                let pos: Vec<usize> = op
                    .pre
                    .iter()
                    .filter(|(_, v)| *v)
                    .map(|(fct, _)| *fct)
                    .collect();
                let mut out: Vec<usize> = mutexes
                    .iter()
                    .filter_map(|&(a, b)| {
                        if pos.contains(&a) {
                            Some(b)
                        } else if pos.contains(&b) {
                            Some(a)
                        } else {
                            None
                        }
                    })
                    .collect();
                out.sort_unstable();
                out.dedup();
                out
            })
            .collect()
    } else {
        Vec::new()
    };

    // Scan upward (smallest LP first); feasibility is monotone in `l`, so the
    // first feasible horizon is the minimum. If even `cap` is infeasible the true
    // minimum exceeds it, and returning `cap` stays an admissible underestimate.
    for l in l0..=cap {
        if solve_horizon(&task, l, tightenings, &mutexes, &implied_false) {
            return l as f32;
        }
    }
    cap as f32
}

/// A zero expression plus the single variable `v`.
fn var(v: Variable) -> Expression {
    let mut e = Expression::default();
    e += v;
    e
}

/// The expression `1 - v`.
fn one_minus(v: Variable) -> Expression {
    let mut e = Expression::default();
    e += 1.0;
    e -= v;
    e
}

/// Builds Bylander's relaxed LP for the ground task at the given horizon and
/// returns whether the goal is reachable (the LP is feasible). The LP relaxation
/// keeps all variables in `[0,1]` rather than `{0,1}`.
fn solve_horizon(
    task: &GroundTask,
    l: usize,
    tightenings: Tightenings,
    mutexes: &[(usize, usize)],
    implied_false: &[Vec<usize>],
) -> bool {
    let f = task.num_facts();
    let ops = task.ops();
    let m = ops.len();
    let init = task.init();

    let mut vars = ProblemVariables::new();
    // Condition variables p(t) for t in 0..=l; operator variables op(t) for
    // t in 0..l. All in [0,1].
    let p: Vec<Vec<Variable>> = (0..=l)
        .map(|_| (0..f).map(|_| vars.add(unit())).collect())
        .collect();
    let o: Vec<Vec<Variable>> = (0..l)
        .map(|_| (0..m).map(|_| vars.add(unit())).collect())
        .collect();

    let mut cons: Vec<good_lp::Constraint> = Vec::new();

    // Per operator, classify preconditions once.
    let pos_pre: Vec<Vec<usize>> = ops
        .iter()
        .map(|op| {
            op.pre
                .iter()
                .filter(|(_, v)| *v)
                .map(|(fct, _)| *fct)
                .collect()
        })
        .collect();
    let neg_pre: Vec<Vec<usize>> = ops
        .iter()
        .map(|op| {
            op.pre
                .iter()
                .filter(|(_, v)| !*v)
                .map(|(fct, _)| *fct)
                .collect()
        })
        .collect();

    // Initial state: p(0) fixed.
    for fct in 0..f {
        cons.push(eq(var(p[0][fct]), if init[fct] { 1.0 } else { 0.0 }));
    }

    for t in 0..l {
        // At most one operator per time point.
        let mut one = Expression::default();
        for &variable in &o[t][..m] {
            one += variable;
        }
        cons.push(leq(one, 1.0));

        // Frame-axiom deltas: p(t+1) = p(t) + Σ adds − Σ dels, with "already
        // true/false" correction variables. Accumulate per fact.
        let mut delta: Vec<Expression> = (0..f).map(|_| Expression::default()).collect();

        // Preconditions: op ⇒ condition holds. Posted per operator this is
        // weaker than it needs to be. At most one operator fires per time point,
        // so the operators sharing a precondition can be summed,
        //
        //     sum over operators requiring `fct` of o(t,i)  ≤  p(t,fct)
        //
        // which dominates the individual inequalities — every `o` is
        // non-negative — and costs one constraint per fact rather than one per
        // operator-precondition.
        if tightenings.aggregated_preconditions {
            let mut requiring_true: Vec<Expression> =
                (0..f).map(|_| Expression::default()).collect();
            let mut requiring_false: Vec<Expression> =
                (0..f).map(|_| Expression::default()).collect();
            for oi in 0..m {
                for &fct in &pos_pre[oi] {
                    requiring_true[fct] += o[t][oi];
                }
                for &fct in &neg_pre[oi] {
                    requiring_false[fct] += o[t][oi];
                }
            }
            for fct in 0..f {
                cons.push(leq(
                    std::mem::take(&mut requiring_true[fct]),
                    var(p[t][fct]),
                ));
                cons.push(leq(
                    std::mem::take(&mut requiring_false[fct]),
                    one_minus(p[t][fct]),
                ));
            }
        } else {
            for oi in 0..m {
                for &fct in &pos_pre[oi] {
                    cons.push(leq(var(o[t][oi]), var(p[t][fct])));
                }
                for &fct in &neg_pre[oi] {
                    cons.push(leq(var(o[t][oi]), one_minus(p[t][fct])));
                }
            }
        }

        for (oi, op) in ops.iter().enumerate() {
            let trig = o[t][oi];

            for e in &op.effects {
                let fct = e.fact;
                // The trigger for this effect's contribution: the operator
                // variable, or — for a conditional effect — a fresh `fire`
                // variable pinned to (op ∧ condition).
                let etrig = if e.cond.is_empty() {
                    trig
                } else {
                    let fire = vars.add(unit());
                    cons.push(leq(var(fire), var(trig)));
                    // fire ≤ each condition literal; fire ≥ op + Σcond − |cond|.
                    let mut lower = var(trig);
                    for &(cf, cv) in &e.cond {
                        if cv {
                            cons.push(leq(var(fire), var(p[t][cf])));
                            lower += p[t][cf];
                            lower -= 1.0;
                        } else {
                            cons.push(leq(var(fire), one_minus(p[t][cf])));
                            lower -= p[t][cf];
                        }
                    }
                    cons.push(geq(var(fire), lower));
                    fire
                };

                if e.value {
                    // Add effect. If the op already requires `fct` true, it is a
                    // no-op on `fct` (skip). Otherwise introduce the "already
                    // true" correction `a`: net contribution `etrig − a`.
                    if pos_pre[oi].contains(&fct) {
                        continue;
                    }
                    // A fact this operator cannot see true needs no "already
                    // true" correction: the inequality below *is* the negative
                    // precondition, and the correction would be zero anyway.
                    if tightenings.negative_preconditions
                        && implied_false
                            .get(oi)
                            .is_some_and(|facts| facts.binary_search(&fct).is_ok())
                    {
                        cons.push(leq(var(etrig), one_minus(p[t][fct])));
                        delta[fct] += etrig;
                        continue;
                    }
                    let a = vars.add(unit());
                    cons.push(leq(var(a), var(etrig)));
                    cons.push(leq(var(a), var(p[t][fct])));
                    cons.push(leq(sub(etrig, a), one_minus(p[t][fct])));
                    delta[fct] += etrig;
                    delta[fct] -= a;
                } else {
                    // Delete effect. If the op already requires `fct` false it is a
                    // no-op. Otherwise the "already false" correction `d`.
                    if neg_pre[oi].contains(&fct) {
                        continue;
                    }
                    let d = vars.add(unit());
                    cons.push(leq(var(d), var(etrig)));
                    cons.push(leq(var(d), one_minus(p[t][fct])));
                    cons.push(leq(sub(etrig, d), var(p[t][fct])));
                    delta[fct] -= etrig;
                    delta[fct] += d;
                }
            }
        }

        // p(t+1) = p(t) + delta.
        for fct in 0..f {
            let mut rhs = var(p[t][fct]);
            rhs += std::mem::take(&mut delta[fct]);
            cons.push(eq(var(p[t + 1][fct]), rhs));
        }
    }

    // Mutex cuts. Every integer solution assigns `p(t)` a real reachable state,
    // so a pair that holds in no reachable state cannot hold here either. This
    // is what stops two operators half-firing and superposing their effects.
    if tightenings.fact_mutexes {
        for row in p.iter().take(l + 1) {
            for &(a, b) in mutexes {
                let mut both = var(row[a]);
                both += row[b];
                cons.push(leq(both, 1.0));
            }
        }
    }

    // Goal at the final time point.
    for &(fct, value) in task.goal() {
        cons.push(eq(var(p[l][fct]), if value { 1.0 } else { 0.0 }));
    }

    // Objective: minimise total operator usage (feasibility is what matters; a
    // bounded objective keeps the solver well-posed).
    let mut obj = Expression::default();
    for row in o.iter().take(l) {
        for &variable in &row[..m] {
            obj += variable;
        }
    }

    let model = vars.minimise(obj).using(lp_solver).with_all(cons);
    // These LPs are small — a few hundred variables — and one horizon is solved
    // per node, so HiGHS's parallel task executor spends more time scheduling
    // than solving: its worker spin was 67% of the profile, and pinning to one
    // thread is worth ~1.2x. Presolve is left on: it is what makes HiGHS fast
    // here, and turning it off costs 4x.
    #[cfg(feature = "highs-lp")]
    let model = model
        .set_parallel(good_lp::solvers::highs::HighsParallelType::Off)
        .set_threads(1);
    match model.solve() {
        Ok(_) => true,
        Err(ResolutionError::Infeasible) => false,
        // Unbounded cannot occur (all variables are bounded); any other solver
        // error is treated conservatively as "not feasible".
        Err(_) => false,
    }
}

/// `etrig − v` as an expression.
fn sub(etrig: Variable, v: Variable) -> Expression {
    let mut e = var(etrig);
    e -= v;
    e
}

/// A fresh continuous variable clamped to `[0,1]` (the LP relaxation of a binary).
fn unit() -> good_lp::variable::VariableDefinition {
    good_lp::variable().min(0.0).max(1.0)
}

/// Fact pairs that hold together in no state reachable from the initial one.
///
/// A standard `h²`-style fixpoint over pairs, and the source of both
/// tightenings: the pairs become `p(t) + q(t) ≤ 1` cuts, and a fact mutex with
/// one of an operator's preconditions is a negative precondition that operator
/// may be given for free.
///
/// **Soundness rests on over-approximating what is reachable.** Claiming a pair
/// reachable when it is not only costs a mutex we could have had; claiming a
/// mutex that does not hold would cut off integer solutions and break
/// admissibility. So every uncertainty is resolved towards "reachable":
/// negative preconditions and conditional-effect guards are ignored when
/// deciding applicability, a conditionally added fact counts as possibly added,
/// and a conditionally deleted fact counts as possibly surviving.
pub(crate) fn fact_mutexes(task: &GroundTask) -> Vec<(usize, usize)> {
    let f = task.num_facts();
    // Bail out on tasks where the pair table would be large; the caller then
    // simply gets no cuts.
    if f == 0 || f > MAX_MUTEX_FACTS {
        return Vec::new();
    }
    let init = task.init();
    let idx = |a: usize, b: usize| a * f + b;

    // `single[p]`: p can be true. `pair[a*f+b]`: a and b can be true together.
    let mut single = vec![false; f];
    let mut pair = vec![false; f * f];
    for a in 0..f {
        if init[a] {
            single[a] = true;
            for b in 0..f {
                if init[b] {
                    pair[idx(a, b)] = true;
                }
            }
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for op in task.ops() {
            // Applicability, over-approximated: positive preconditions must be
            // pairwise reachable; negative ones are ignored.
            let pos: Vec<usize> = op
                .pre
                .iter()
                .filter(|(_, v)| *v)
                .map(|(fct, _)| *fct)
                .collect();
            if pos.iter().any(|&p| !single[p]) {
                continue;
            }
            if pos
                .iter()
                .enumerate()
                .any(|(i, &p)| pos[i + 1..].iter().any(|&q| !pair[idx(p, q)]))
            {
                continue;
            }

            // Facts this operator may make true, and those it definitely makes
            // false. A conditional effect only *may* fire, so it adds to the
            // first set and never to the second.
            let mut adds: Vec<usize> = Vec::new();
            let mut deletes: Vec<usize> = Vec::new();
            for e in &op.effects {
                if e.value {
                    adds.push(e.fact);
                } else if e.cond.is_empty() {
                    deletes.push(e.fact);
                }
            }
            // An unconditionally deleted fact that is also added stays possible.
            deletes.retain(|d| !adds.contains(d));

            for &a in &adds {
                if !single[a] {
                    single[a] = true;
                    changed = true;
                }
                // Added facts are mutually reachable.
                for &b in &adds {
                    if !pair[idx(a, b)] {
                        pair[idx(a, b)] = true;
                        pair[idx(b, a)] = true;
                        changed = true;
                    }
                }
                // An added fact joins anything that could already hold alongside
                // every precondition and that this operator does not delete.
                for c in 0..f {
                    if !single[c] || deletes.contains(&c) || pair[idx(a, c)] {
                        continue;
                    }
                    let survives = pos.iter().all(|&p| pair[idx(p, c)]);
                    if survives {
                        pair[idx(a, c)] = true;
                        pair[idx(c, a)] = true;
                        changed = true;
                    }
                }
            }
        }
    }

    let mut mutexes = Vec::new();
    for a in 0..f {
        for b in (a + 1)..f {
            // Only a pair of individually reachable facts is a useful mutex; an
            // unreachable fact is handled by the rest of the encoding.
            if single[a] && single[b] && !pair[idx(a, b)] {
                mutexes.push((a, b));
            }
        }
    }
    mutexes
}

#[cfg(test)]
mod mutex_tests {
    use super::*;
    use crate::params::Parameters;
    use crate::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
    use crate::plan::Plan;
    use crate::search::SearchContext;

    pub(super) fn task_for(domain_file: &str, problem_file: &str) -> GroundTask {
        let domain_src = std::fs::read_to_string(format!("examples/{domain_file}")).unwrap();
        let problem_src = std::fs::read_to_string(format!("examples/{problem_file}")).unwrap();
        let domain = match read_pddl(&domain_src).unwrap() {
            ParsedUnit::Domain(d) => lower_domain(&d).unwrap(),
            _ => panic!("expected a domain"),
        };
        let problem = match read_pddl(&problem_src).unwrap() {
            ParsedUnit::Problem(p) => lower_problem(&p, &domain).unwrap(),
            _ => panic!("expected a problem"),
        };
        let params = Parameters {
            ground_actions: true,
            ..Parameters::default()
        };
        let ctx = SearchContext::new(&domain, &problem, &params);
        let plan = Plan::make_initial_plan(&ctx).expect("initial plan");
        crate::compile::ground_task(&plan, &ctx)
    }

    /// Exhaustively reachable states, up to a cap. Exact: unlike the analysis,
    /// this honours negative preconditions and conditional-effect guards.
    fn reachable_states(task: &GroundTask, cap: usize) -> Vec<Vec<bool>> {
        let init: Vec<bool> = task.init().to_vec();
        let mut seen = std::collections::HashSet::new();
        let mut queue = std::collections::VecDeque::new();
        seen.insert(init.clone());
        queue.push_back(init);
        let mut out = Vec::new();
        while let Some(state) = queue.pop_front() {
            out.push(state.clone());
            if out.len() >= cap {
                break;
            }
            for op in task.ops() {
                if !op.pre.iter().all(|&(fct, v)| state[fct] == v) {
                    continue;
                }
                // Every guard is read against the pre-state.
                let firing: Vec<&crate::sas::GroundEffect> = op
                    .effects
                    .iter()
                    .filter(|e| e.cond.iter().all(|&(cf, cv)| state[cf] == cv))
                    .collect();
                let mut next = state.clone();
                for e in firing {
                    next[e.fact] = e.value;
                }
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
        }
        out
    }

    /// Every pair the analysis calls mutex must genuinely hold in no reachable
    /// state. A false mutex would cut integer solutions out of the LP and make
    /// the heuristic inadmissible, so this is the load-bearing check.
    #[test]
    fn no_claimed_mutex_holds_in_any_reachable_state() {
        for (domain_file, problem_file) in [
            ("blocks-world-domain.pddl", "sussman-anomaly.pddl"),
            ("ferry-domain.pddl", "test-ferry.pddl"),
            ("hanoi-domain.pddl", "hanoi-3.pddl"),
            ("gripper-domain.pddl", "gripper-4.pddl"),
        ] {
            let task = task_for(domain_file, problem_file);
            let mutexes = fact_mutexes(&task);
            let states = reachable_states(&task, 20_000);
            assert!(!states.is_empty(), "{problem_file}: no states explored");
            for &(a, b) in &mutexes {
                for state in &states {
                    assert!(
                        !(state[a] && state[b]),
                        "{problem_file}: facts {a} and {b} were called mutex \
                         but hold together in a reachable state"
                    );
                }
            }
            eprintln!(
                "  {problem_file}: {} facts, {} mutex pairs, {} states checked",
                task.num_facts(),
                mutexes.len(),
                states.len()
            );
        }
    }
}
