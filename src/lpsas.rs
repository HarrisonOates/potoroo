//! Bylander's LP relaxation over Fast Downward's finite-domain (SAS⁺) task.
//!
//! [`crate::lplan`] encodes the relaxation over a task of boolean facts, which
//! is the form Bylander's paper uses. Fast Downward's translator instead
//! produces multi-valued variables, and encoding over those changes the model in
//! three ways that all pull in the same direction:
//!
//! 1. **Invariants come for free.** A SAS⁺ variable *is* an exactly-one group,
//!    so `Σ_d x(t,v,d) = 1` replaces the pairwise mutex cuts `lplan` has to
//!    derive with its own `h²` fixpoint — and it is the clique-strength version
//!    of them.
//! 2. **The state is smaller.** Tower of Hanoi is 8 variables here against 33
//!    boolean facts in the compiled task, over an operator set the translator
//!    has already pruned for reachability.
//! 3. **The correction variables disappear.** Bylander needs an auxiliary
//!    variable per operator-effect per time step to represent "the postcondition
//!    was already true", because a boolean add tells you nothing about the prior
//!    value. Here the transition is expressed by two inequalities per
//!    `(time, variable, value)` and needs no auxiliaries at all:
//!
//!    ```text
//!    x(t+1,v,d) ≤ x(t,v,d) + Σ  o(t,i)     over operators i setting v := d
//!    x(t+1,v,d) ≥ x(t,v,d) − Σ  o(t,i)     over operators i setting v := d' ≠ d
//!    ```
//!
//!    A value can only hold at `t+1` if it held at `t` or an operator set it,
//!    and it survives unless an operator moved the variable elsewhere. Both hold
//!    in every integer solution, so the integer program is unchanged and the
//!    smallest feasible horizon stays an admissible bound.
//!
//! A conditional effect only *may* fire. It is therefore counted in both sums:
//! among the operators that may set `d` (which relaxes the upper bound) and
//! among those that may move the variable away (which relaxes the lower bound).
//! Relaxing in both directions keeps every integer solution feasible.
//!
//! ## Status
//!
//! This encodes the distance from the task's initial state, so it is a *task*
//! bound rather than a per-node completion bound: it does not yet represent a
//! partial plan. Bylander's step variables are what would close that gap, and
//! they are the natural fit here because the causal-link compilation
//! (`crate::compile::ground_task`) produces a boolean task with no SAS⁺
//! counterpart. Until then this exists to measure the encoding against
//! `crate::lplan` on equal terms.

use good_lp::constraint::{eq, geq, leq};
#[cfg(feature = "highs-lp")]
use good_lp::solvers::highs::highs as lp_solver;
#[cfg(not(feature = "highs-lp"))]
use good_lp::solvers::microlp::microlp as lp_solver;
use good_lp::{Expression, ProblemVariables, ResolutionError, SolverModel, Variable};

use crate::fdr::Task;

/// A `[0,1]` variable.
fn unit() -> good_lp::variable::VariableDefinition {
    good_lp::variable().min(0.0).max(1.0)
}

fn var(v: Variable) -> Expression {
    let mut e = Expression::default();
    e += v;
    e
}

/// The smallest horizon in `0..=cap` whose relaxed LP reaches the goal, or
/// `None` when even `cap` is infeasible or the task is outside the fragment
/// this encodes.
///
/// Feasibility is monotone in the horizon, so the first feasible one is the
/// minimum and an admissible lower bound on the number of operators any plan
/// needs.
pub fn horizon_bound(task: &Task, cap: usize) -> Option<usize> {
    // Axioms would need their closure modelled inside each time step; a task
    // carrying them is simply not estimated here.
    if !task.axioms.is_empty() {
        return None;
    }
    (0..=cap).find(|&l| feasible(task, l))
}

/// Whether the relaxation admits reaching the goal within `l` operators.
fn feasible(task: &Task, l: usize) -> bool {
    let num_variables = task.variables.len();
    let mut vars = ProblemVariables::new();

    // x[t][v][d]: variable `v` takes value `d` at time `t`.
    let x: Vec<Vec<Vec<Variable>>> = (0..=l)
        .map(|_| {
            task.variables
                .iter()
                .map(|variable| variable.values.iter().map(|_| vars.add(unit())).collect())
                .collect()
        })
        .collect();
    // o[t][i]: operator `i` is applied at time `t`.
    let o: Vec<Vec<Variable>> = (0..l)
        .map(|_| task.operators.iter().map(|_| vars.add(unit())).collect())
        .collect();

    let mut cons: Vec<good_lp::Constraint> = Vec::new();

    // Each variable takes exactly one value at each time point. This is the
    // invariant the boolean encoding has to rediscover as mutexes.
    for row in x.iter().take(l + 1) {
        for values in row.iter().take(num_variables) {
            let mut total = Expression::default();
            for &value in values {
                total += value;
            }
            cons.push(eq(total, 1.0));
        }
    }

    // The translator's invariant groups, as cuts. A SAS+ variable already
    // carries exactly-one over its own values, so these add what that cannot:
    // the *cross*-variable invariants. They hold in every reachable state, hence
    // in every integer solution, so admissibility is untouched.
    for row in x.iter().take(l + 1) {
        for group in &task.mutex_groups {
            let mut total = Expression::default();
            for fact in group {
                total += row[fact.variable][fact.value];
            }
            cons.push(leq(total, 1.0));
        }
    }

    // Initial state, and the goal at the final time point.
    for (v, &value) in task.initial.iter().enumerate() {
        cons.push(eq(var(x[0][v][value]), 1.0));
    }
    for goal in &task.goals {
        cons.push(eq(var(x[l][goal.variable][goal.value]), 1.0));
    }

    for t in 0..l {
        // At most one operator per time point, as in the paper.
        let mut applied = Expression::default();
        for &operator in &o[t] {
            applied += operator;
        }
        cons.push(leq(applied, 1.0));

        // An operator may only be applied where its preconditions hold.
        for (i, operator) in task.operators.iter().enumerate() {
            for fact in operator.preconditions() {
                cons.push(leq(var(o[t][i]), var(x[t][fact.variable][fact.value])));
            }
        }

        // Transitions. `sets[v][d]` accumulates the operators that may give `v`
        // the value `d`; `moves[v]` those that may change `v` at all.
        let mut sets: Vec<Vec<Expression>> = task
            .variables
            .iter()
            .map(|variable| {
                variable
                    .values
                    .iter()
                    .map(|_| Expression::default())
                    .collect()
            })
            .collect();
        let mut moves: Vec<Vec<Expression>> = task
            .variables
            .iter()
            .map(|variable| {
                variable
                    .values
                    .iter()
                    .map(|_| Expression::default())
                    .collect()
            })
            .collect();
        for (i, operator) in task.operators.iter().enumerate() {
            for effect in &operator.effects {
                sets[effect.variable][effect.post] += o[t][i];
                // Every other value of this variable may be displaced.
                for (d, displaced) in moves[effect.variable].iter_mut().enumerate() {
                    if d != effect.post {
                        *displaced += o[t][i];
                    }
                }
            }
        }

        // An unconditional effect is not optional: if the operator fires, the
        // variable *has* the post value afterwards. Without this the two
        // inequalities below only bound how far the value may drift, and an
        // operator could fire without moving it, which is what made this
        // encoding weaker than the boolean one's frame equalities. A
        // conditional effect is excluded: it may not fire.
        for (i, operator) in task.operators.iter().enumerate() {
            for effect in &operator.effects {
                if effect.conditions.is_empty() {
                    cons.push(leq(
                        var(o[t][i]),
                        var(x[t + 1][effect.variable][effect.post]),
                    ));
                }
            }
        }

        for v in 0..num_variables {
            for d in 0..task.variables[v].values.len() {
                // A value holds next only if it held, or an operator set it.
                let mut upper = var(x[t][v][d]);
                upper += std::mem::take(&mut sets[v][d]);
                cons.push(leq(var(x[t + 1][v][d]), upper));

                // And it survives unless an operator moved the variable away.
                let mut lower = var(x[t][v][d]);
                lower -= std::mem::take(&mut moves[v][d]);
                cons.push(geq(var(x[t + 1][v][d]), lower));
            }
        }
    }

    // Feasibility is the question; the objective only has to be bounded.
    let model = vars
        .minimise(Expression::default())
        .using(lp_solver)
        .with_all(cons);
    #[cfg(feature = "highs-lp")]
    let model = model
        .set_parallel(good_lp::solvers::highs::HighsParallelType::Off)
        .set_threads(1);
    match model.solve() {
        Ok(_) => true,
        Err(ResolutionError::Infeasible) => false,
        // Any other solver outcome is treated conservatively as infeasible,
        // which can only make the bound weaker, never inadmissible.
        Err(_) => false,
    }
}
