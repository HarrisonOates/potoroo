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
use good_lp::solvers::microlp::microlp;
use good_lp::{Expression, ProblemVariables, ResolutionError, SolverModel, Variable};

use crate::plan::Plan;
use crate::sas::GroundTask;
use crate::search::SearchContext;

/// How many time steps beyond the committed-step lower bound to search for a
/// feasible horizon before giving up (and returning the cap as an admissible
/// underestimate). Bounds the largest LP we build per node — and, crucially, the
/// work spent on a node whose partial plan cannot complete (its scan runs to the
/// cap). Kept small: the optimum is normally within a few steps of the bound.
const HORIZON_EXTRA: usize = 6;

/// Computes the Lplan rank for `plan`: the smallest horizon whose relaxed LP over
/// the causal-link compilation reaches the goal. Admissible lower bound on the
/// total completion length (so `weight` is intentionally *not* applied). Ground
/// search only; lifted falls back to `num_steps + weight * num_open_conds`.
pub fn lplan_rank(plan: &Plan, ctx: &SearchContext, weight: f32) -> f32 {
    if !ctx.params.ground_actions {
        return plan.num_steps() as f32 + weight * plan.num_open_conds() as f32;
    }
    let task = crate::compile::ground_task(plan, ctx);

    // Every committed step is a forced operator (its exec-pos is a goal) and at
    // most one operator fires per step, so the horizon is at least the number of
    // committed steps — a sound lower bound to start the scan from.
    let l0 = plan.num_steps();
    let cap = l0 + HORIZON_EXTRA;

    // Scan upward (smallest LP first); feasibility is monotone in `l`, so the
    // first feasible horizon is the minimum. If even `cap` is infeasible the true
    // minimum exceeds it, and returning `cap` stays an admissible underestimate.
    for l in l0..=cap {
        if solve_horizon(&task, l) {
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
fn solve_horizon(task: &GroundTask, l: usize) -> bool {
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
        .map(|op| op.pre.iter().filter(|(_, v)| *v).map(|(fct, _)| *fct).collect())
        .collect();
    let neg_pre: Vec<Vec<usize>> = ops
        .iter()
        .map(|op| op.pre.iter().filter(|(_, v)| !*v).map(|(fct, _)| *fct).collect())
        .collect();

    // Initial state: p(0) fixed.
    for fct in 0..f {
        cons.push(eq(var(p[0][fct]), if init[fct] { 1.0 } else { 0.0 }));
    }

    for t in 0..l {
        // At most one operator per time point.
        let mut one = Expression::default();
        for op in 0..m {
            one += o[t][op];
        }
        cons.push(leq(one, 1.0));

        // Frame-axiom deltas: p(t+1) = p(t) + Σ adds − Σ dels, with "already
        // true/false" correction variables. Accumulate per fact.
        let mut delta: Vec<Expression> = (0..f).map(|_| Expression::default()).collect();

        for (oi, op) in ops.iter().enumerate() {
            let trig = o[t][oi];

            // Preconditions: op ⇒ condition holds.
            for &fct in &pos_pre[oi] {
                cons.push(leq(var(trig), var(p[t][fct])));
            }
            for &fct in &neg_pre[oi] {
                cons.push(leq(var(trig), one_minus(p[t][fct])));
            }

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

    // Goal at the final time point.
    for &(fct, value) in task.goal() {
        cons.push(eq(var(p[l][fct]), if value { 1.0 } else { 0.0 }));
    }

    // Objective: minimise total operator usage (feasibility is what matters; a
    // bounded objective keeps the solver well-posed).
    let mut obj = Expression::default();
    for t in 0..l {
        for op in 0..m {
            obj += o[t][op];
        }
    }

    let model = vars.minimise(obj).using(microlp).with_all(cons);
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
