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
use crate::orderings::StepTime;
use crate::plan::{Plan, GOAL_ID, INIT_ID};
use crate::search::SearchContext;

/// Whether the operator variables are relaxed or held integral.
///
/// [`Operators::Integral`] removes Bylander's "superposition": with at most one
/// operator per time point and that choice integral, an unconditional effect
/// forces its post value to 1 and exactly-one zeroes the rest, so — starting
/// from an integral initial state — the whole solution is integral by induction
/// and the relaxation becomes exact. Exact means no longer a relaxation: each
/// probe is a mixed-integer program, i.e. the planning problem itself. Offered
/// to measure what superposition is actually costing, not as a default.
///
/// Conditional effects are the exception: one may decline to fire, so the
/// variable it writes can still take a fractional value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operators {
    /// Bylander's relaxation: operator variables range over `[0,1]`.
    Fractional,
    /// Operator variables are binary.
    Integral,
    /// Binary, but each probe is given at most this many milliseconds. A probe
    /// that does not finish counts as feasible, which stops the scan early and
    /// so underestimates — weaker, never inadmissible. This trades tightness
    /// against the cost of exactness, which on gripper-4 is 309x.
    IntegralWithin(u64),
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
    scan_from(task, &[], cap, operators)
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
    scan_from(task, &steps, l0 + extra, operators)
}

/// The smallest horizon up to `cap` that admits a solution.
///
/// Under an integral mode the scan starts from the relaxation's answer rather
/// than from zero. Holding the operators integral only ever removes solutions,
/// so every horizon the relaxation rejects the integer program rejects too, and
/// beginning below that answer can only re-prove what is already known. It also
/// keeps an integral mode from ever returning *less* than the relaxation would,
/// which a budgeted probe could otherwise do by running out of time low in the
/// scan.
fn scan_from(
    task: &Task,
    steps: &[CommittedStep],
    cap: usize,
    operators: Operators,
) -> Option<usize> {
    let floor = match operators {
        Operators::Fractional => steps.len(),
        // The relaxation rejecting every horizon means the task does too.
        Operators::Integral | Operators::IntegralWithin(_) => {
            scan_from(task, steps, cap, Operators::Fractional)?
        }
    };
    (floor..=cap).find(|&l| solve_at(task, l, steps, operators).is_some())
}

/// Values of `v` that some operator forced to fire demands.
///
/// An operator is forced when it is the only one writing a goal value that is
/// not already established: no plan can reach the goal without it, so every
/// precondition it carries must hold at some point, and the variables those
/// preconditions name must *visit* those values. That turns the transition
/// bound from a shortest path into a shortest walk.
fn forced_values(task: &Task, v: usize) -> Vec<usize> {
    let mut required = Vec::new();
    for goal in &task.goals {
        if task.initial[goal.variable] == goal.value {
            continue;
        }
        // Every way of achieving this goal is a disjunctive landmark: one of
        // them must fire. Where they all demand the same value of `v`, that
        // value is visited whichever is chosen. Insisting on a *single*
        // achiever is far too strict -- a goal value usually has several, such
        // as dropping a ball with either gripper -- and finds almost nothing.
        let achievers: Vec<_> = task
            .operators
            .iter()
            .filter(|operator| {
                operator
                    .effects
                    .iter()
                    .any(|e| e.variable == goal.variable && e.post == goal.value)
            })
            .collect();
        let Some(first) = achievers.first() else {
            continue;
        };
        for fact in first.preconditions() {
            if fact.variable != v || required.contains(&fact.value) {
                continue;
            }
            let demanded_by_all = achievers.iter().all(|operator| {
                operator
                    .preconditions()
                    .iter()
                    .any(|other| other.variable == v && other.value == fact.value)
            });
            if demanded_by_all {
                required.push(fact.value);
            }
        }
    }
    required
}

/// Shortest walk from `start` through every value of `through`, ending at
/// `goal`. Domains are small, so the orders are simply enumerated.
fn shortest_walk(
    distance: &dyn Fn(usize, usize) -> Option<usize>,
    start: usize,
    through: &[usize],
    goal: usize,
) -> Option<usize> {
    if through.is_empty() {
        return distance(start, goal);
    }
    // More than a handful of required values is not worth enumerating, and
    // dropping them only weakens the bound.
    if through.len() > 4 {
        return distance(start, goal);
    }
    let mut order: Vec<usize> = (0..through.len()).collect();
    let mut best: Option<usize> = None;
    permute(&mut order, 0, &mut |perm| {
        let mut total = 0usize;
        let mut at = start;
        for &index in perm {
            let Some(step) = distance(at, through[index]) else {
                return;
            };
            total += step;
            at = through[index];
        }
        let Some(last) = distance(at, goal) else {
            return;
        };
        total += last;
        best = Some(best.map_or(total, |b: usize| b.min(total)));
    });
    best
}

fn permute(order: &mut Vec<usize>, k: usize, visit: &mut dyn FnMut(&[usize])) {
    if k == order.len() {
        visit(order);
        return;
    }
    for i in k..order.len() {
        order.swap(k, i);
        permute(order, k + 1, visit);
        order.swap(k, i);
    }
}

/// Whether two facts hold together in no reachable state.
///
/// Two values of the same variable are mutex by exactly-one; across variables it
/// takes one of the translator's invariant groups.
fn mutex(task: &Task, a: crate::fdr::Fact, b: crate::fdr::Fact) -> bool {
    if a.variable == b.variable {
        return a.value != b.value;
    }
    task.mutex_groups
        .iter()
        .any(|group| group.contains(&a) && group.contains(&b))
}

/// The fewest value changes variable `v` must undergo: the shortest path in its
/// domain transition graph from its initial to its goal value. `None` when `v`
/// has no goal, or the goal is already its initial value.
///
/// Every edge of that path costs one operator application that writes `v`, so
/// this bounds from below how often such operators fire — a *counting* bound on
/// the operator variables, which is the class that bites here, rather than
/// another constraint on the state.
///
/// Edges are over-approximated: a conditional effect that might not fire still
/// contributes one, and an effect with no required old value contributes an
/// edge from every value. More edges mean shorter paths and a weaker bound,
/// never an inadmissible one.
fn dtg_distance(task: &Task, v: usize) -> Option<usize> {
    let start = task.initial[v];
    let through = forced_values(task, v);
    // With no goal of its own a variable is still obliged to visit whatever the
    // landmarks demand; it just has nowhere particular to end up.
    let goal = match task.goals.iter().find(|g| g.variable == v) {
        Some(g) => g.value,
        None if through.is_empty() => return None,
        None => *through.last().expect("checked non-empty"),
    };
    let size = task.variables[v].values.len();
    let mut edges: Vec<Vec<usize>> = vec![Vec::new(); size];
    for operator in &task.operators {
        for effect in &operator.effects {
            if effect.variable != v {
                continue;
            }
            match effect.pre {
                Some(from) => edges[from].push(effect.post),
                // No required old value recorded, which does not mean the
                // operator is applicable whatever `v` holds: the condition that
                // pins `v` may live in another variable. `drop ball roomb left`
                // is the case in point — it writes `at(ball, roomb)` with no
                // recorded old value, but requires `carry(ball, left)`, which is
                // mutex with the ball being in either room. Edges out of values
                // the preconditions exclude are dropped, which lengthens the
                // path and so strengthens the bound; only a genuine mutex may
                // prune, or a real transition would be lost.
                None => {
                    let preconditions = operator.preconditions();
                    for (from, out) in edges.iter_mut().enumerate() {
                        let excluded = preconditions
                            .iter()
                            .any(|&fact| mutex(task, fact, crate::fdr::Fact::new(v, from)));
                        if !excluded {
                            out.push(effect.post);
                        }
                    }
                }
            }
        }
    }

    // All-pairs distances over a domain this small.
    let hop = |from: usize, to: usize| -> Option<usize> {
        if from == to {
            return Some(0);
        }
        let mut seen = vec![false; size];
        seen[from] = true;
        let mut queue = std::collections::VecDeque::from([(from, 0usize)]);
        while let Some((value, steps)) = queue.pop_front() {
            for &next in &edges[value] {
                if next == to {
                    return Some(steps + 1);
                }
                if !seen[next] {
                    seen[next] = true;
                    queue.push_back((next, steps + 1));
                }
            }
        }
        None
    };

    // A value some forced operator demands has to be visited on the way, which
    // can make the journey longer than the direct path — a variable may have to
    // leave its goal value and come back.
    shortest_walk(&hop, start, &through, goal)
}

/// Solves the model at horizon `l`, minimising total operator usage, and
/// returns that usage. `None` when the horizon admits no solution at all.
///
/// The scan over horizons is deliberate. Building one model at the cap and
/// rounding up its cheapest operator usage looks like it should replace the
/// scan with a single solve, and it is admissible, but it is both weaker and
/// slower: measured against the scan it gave 3/2/4/2 where the scan gave
/// 4/4/5/5 on test-ferry, Hanoi, gripper-4 and monkey. The horizon is itself
/// the constraint that bites — at horizon `l` with one operator per time point
/// the relaxation can spend at most `l` of them, and it is infeasibility at
/// `l - 1` that carries the information. Minimising at a distant horizon
/// removes that pressure and the optimum simply drops.
fn solve_at(task: &Task, l: usize, steps: &[CommittedStep], operators: Operators) -> Option<f64> {
    // Every committed step needs a time point of its own.
    if steps.len() > l {
        return None;
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
                    Operators::Integral | Operators::IntegralWithin(_) => {
                        vars.add(good_lp::variable().binary())
                    }
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

        // An operator may only be applied where its preconditions hold. Posting
        // this per operator as `o(t,i) <= x(t,v,d)` is weaker than it needs to
        // be: at most one operator fires per time point, so the operators that
        // *share* a precondition can be summed,
        //
        //     sum over i requiring v = d of o(t,i)  <=  x(t,v,d)
        //
        // which dominates the individual constraints, since every `o` is
        // non-negative, and replaces one constraint per operator-precondition
        // with one per fact. Stronger and smaller at once.
        let mut requiring: Vec<Vec<Expression>> = task
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
            for fact in operator.preconditions() {
                requiring[fact.variable][fact.value] += o[t][i];
            }
        }
        for (v, values) in requiring.into_iter().enumerate() {
            for (d, total) in values.into_iter().enumerate() {
                cons.push(leq(total, var(x[t][v][d])));
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
        // Aggregated the same way as the preconditions: at most one operator
        // fires, so the operators that unconditionally write the same value can
        // be summed against it. Dominates the per-operator form.
        let mut writing: Vec<Vec<Expression>> = task
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
                if effect.conditions.is_empty() {
                    writing[effect.variable][effect.post] += o[t][i];
                }
            }
        }
        for (v, values) in writing.into_iter().enumerate() {
            for (d, total) in values.into_iter().enumerate() {
                cons.push(leq(total, var(x[t + 1][v][d])));
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

    // Domain-transition counting. Independent of the per-step constraints: it
    // bounds how often the operators writing a variable fire across the whole
    // horizon, which the telescoped transitions cannot express — they only force
    // the goal value to be written once.
    for v in 0..num_variables {
        if let Some(distance) = dtg_distance(task, v) {
            let mut writes = Expression::default();
            for row in o.iter().take(l) {
                for (i, operator) in task.operators.iter().enumerate() {
                    if operator.effects.iter().any(|e| e.variable == v) {
                        writes += row[i];
                    }
                }
            }
            cons.push(geq(writes, distance as f64));
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

    // Minimise how many operators are used across the horizon.
    let mut usage = Expression::default();
    for row in o.iter().take(l) {
        for &operator in row {
            usage += operator;
        }
    }
    let model = vars.minimise(usage.clone()).using(lp_solver).with_all(cons);
    #[cfg(feature = "highs-lp")]
    let model = {
        let model = model
            .set_parallel(good_lp::solvers::highs::HighsParallelType::Off)
            .set_threads(1);
        match operators {
            Operators::IntegralWithin(millis) => model.set_time_limit(millis as f64 / 1000.0),
            _ => model,
        }
    };
    match model.solve() {
        Ok(solution) => Some(usage.eval_with(&solution)),
        Err(ResolutionError::Infeasible) => None,
        // Anything else is "don't know", and the safe direction is *feasible*.
        // The scan moves to a larger horizon only when a probe is infeasible, so
        // reporting infeasible on an inconclusive solve pushes the estimate up
        // and can overestimate. Reporting feasible stops the scan early, which
        // underestimates and stays admissible.
        Err(_) => Some(l as f64),
    }
}
