//! Bylander's time-indexed LP relaxation over finite-domain SAS+ tasks.
//!
//! Exactly-one constraints encode each variable's values. Transition bounds
//! allow a value to appear only if it persisted or an operator set it, and
//! to disappear only if an operator may change it. Conditional effects relax
//! both bounds, preserving feasibility of integer plans.

use good_lp::constraint::{eq, geq, leq};
#[cfg(feature = "highs-lp")]
use good_lp::solvers::highs::highs as lp_solver;
#[cfg(not(feature = "highs-lp"))]
use good_lp::solvers::microlp::microlp as lp_solver;
use good_lp::{Expression, ProblemVariables, ResolutionError, SolverModel, Variable};

use crate::fdr::Task;
use crate::orderings::StepTime;
use crate::plan::{Plan, GOAL_ID, INIT_ID};
use crate::search::SearchContext;

/// Whether operator variables are relaxed or integral.
///
/// With integral operators and unconditional effects, exactly-one constraints
/// make state values integral by induction from the initial state.
/// Conditional effects can still leave fractional values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operators {
    /// Bylander's relaxation: operator variables range over `[0,1]`.
    Fractional,
    /// Operator variables are binary.
    Integral,
}

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
pub fn horizon_bound(task: &Task, cap: usize, operators: Operators) -> Option<usize> {
    // Axioms would need their closure modelled inside each time step; a task
    // carrying them is simply not estimated here.
    if !task.axioms.is_empty() {
        return None;
    }
    (0..=cap).find(|&l| feasible_with(task, l, &[], operators))
}

/// One committed step: the operator it instantiates, and the steps that must
/// precede it.
struct CommittedStep {
    operator: usize,
    /// Indices into the step list, not plan step ids.
    predecessors: Vec<usize>,
}

/// Maps each committed step of `plan` onto a SAS+ operator, by the name Fast
/// Downward gives it. `None` if any step has no counterpart, in which case the
/// caller has no business estimating with this encoding.
fn committed_steps(task: &Task, plan: &Plan, ctx: &SearchContext) -> Option<Vec<CommittedStep>> {
    let mut by_name: std::collections::HashMap<&str, usize> =
        std::collections::HashMap::with_capacity(task.operators.len());
    for (index, operator) in task.operators.iter().enumerate() {
        by_name.insert(operator.name.as_str(), index);
    }

    let mut ids = Vec::new();
    let mut operators = Vec::new();
    for step in crate::chain::iter(&plan.steps) {
        if step.id == INIT_ID || step.id == GOAL_ID || step.action.synthetic() {
            continue;
        }
        // The translator names an operator "<action> <arg> <arg>", lowercased.
        let mut name = step.action.name.to_ascii_lowercase();
        for &object in &step.action.arguments {
            name.push(' ');
            name.push_str(
                &ctx.problem
                    .objects
                    .object_name(Some(&ctx.domain.constants), object)
                    .to_ascii_lowercase(),
            );
        }
        operators.push(*by_name.get(name.as_str())?);
        ids.push(step.id);
    }

    Some(
        ids.iter()
            .enumerate()
            .map(|(j, &id)| CommittedStep {
                operator: operators[j],
                predecessors: ids
                    .iter()
                    .enumerate()
                    .filter(|&(k, &other)| {
                        k != j
                            && !plan.orderings.possibly_after(
                                other,
                                StepTime::AtEnd,
                                id,
                                StepTime::AtEnd,
                            )
                    })
                    .map(|(k, _)| k)
                    .collect(),
            })
            .collect(),
    )
}

/// The smallest horizon that completes `plan`: an admissible lower bound on the
/// total length of any completion, as [`horizon_bound`] is for the bare task.
///
/// The partial plan enters the LP through Bylander's step variables rather than
/// through a compilation. `s(j,i)` means "step `j` has been applied at or before
/// time `i`", tied to the operator variables by
/// `Σ_{j on operator a} (s(j,i) − s(j,i−1)) ≤ o(i,a)`, and an ordering `p ≺ q`
/// becomes `s(q,i) ≤ s(p,i−1)`. Every committed step must be applied by the
/// horizon, so the bound is over the whole completion.
pub fn completion_bound(
    task: &Task,
    plan: &Plan,
    ctx: &SearchContext,
    extra: usize,
    operators: Operators,
) -> Option<usize> {
    if !task.axioms.is_empty() {
        return None;
    }
    let steps = committed_steps(task, plan, ctx)?;
    // At most one operator fires per time point, so the horizon is at least the
    // number of committed steps.
    let l0 = steps.len();
    (l0..=l0 + extra).find(|&l| feasible_with(task, l, &steps, operators))
}

fn feasible_with(task: &Task, l: usize, steps: &[CommittedStep], operators: Operators) -> bool {
    // Every committed step needs a time point of its own.
    if steps.len() > l {
        return false;
    }
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
        .map(|_| {
            task.operators
                .iter()
                .map(|_| match operators {
                    Operators::Fractional => vars.add(unit()),
                    Operators::Integral => vars.add(good_lp::variable().binary()),
                })
                .collect()
        })
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

    // Bylander's step variables: `s[j][i]` is "step `j` has been applied at or
    // before time `i`". They are what puts the partial plan into the LP without
    // compiling it into the task.
    if !steps.is_empty() {
        let s: Vec<Vec<Variable>> = steps
            .iter()
            .map(|_| (0..l).map(|_| vars.add(unit())).collect())
            .collect();

        for (j, step) in steps.iter().enumerate() {
            // Applied at some point within the horizon, and never un-applied.
            cons.push(eq(var(s[j][l - 1]), 1.0));
            for i in 1..l {
                cons.push(geq(var(s[j][i]), var(s[j][i - 1])));
            }
            // Ordering: a step cannot have been applied before its predecessor.
            for &p in &step.predecessors {
                cons.push(eq(var(s[j][0]), 0.0));
                for i in 1..l {
                    cons.push(leq(var(s[j][i]), var(s[p][i - 1])));
                }
            }
        }

        // The step only becomes applied at a time its operator actually fires.
        // Steps sharing an operator are summed, as the paper requires.
        for (i, row) in o.iter().enumerate().take(l) {
            let mut used: Vec<Expression> = task
                .operators
                .iter()
                .map(|_| Expression::default())
                .collect();
            for (j, step) in steps.iter().enumerate() {
                if i == 0 {
                    used[step.operator] += s[j][0];
                } else {
                    used[step.operator] += s[j][i];
                    used[step.operator] -= s[j][i - 1];
                }
            }
            for (a, total) in used.into_iter().enumerate() {
                cons.push(leq(total, var(row[a])));
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
