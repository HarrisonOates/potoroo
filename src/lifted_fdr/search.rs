//! Best-first search over lifted FDR partial plans, completion grounding, and
//! an independent STRIPS check of every returned plan.

use std::collections::{BinaryHeap, HashSet};
use std::rc::Rc;
use std::time::{Duration, Instant};

use crate::bindings::TypeContext;
use crate::chain;
use crate::domain::Domain;
use crate::formula::{Atom, Formula, Literal};
use crate::orderings::StepTime;
use crate::problem::Problem;
use crate::terms::{Object, Term};

use super::heuristic::Estimator;
use super::plan::{refine_open, refine_threat, Ctx, GlobalTypes, Plan};
use super::task::{LiftedTask, Unsupported};

/// The lanes run when none are given: ZLIFO and MW-Loc with domain-aware
/// and pattern ADD, with and without degree binding where the development
/// panel showed each to matter (`investigation/lifted-fdr/findings.md`).
pub const DEFAULT_LANES: [&str; 5] = [
    "ZLIFO@ADD",
    "ZLIFO@ADD+deg",
    "MW-Loc@ADD+deg",
    "ZLIFO@PADD",
    "MW-Loc@PADD+deg",
];

/// One independent best-first search: a flaw order and a ranking heuristic.
#[derive(Debug, Clone)]
pub struct Lane {
    pub name: String,
    pub flaw_order: crate::heuristics::FlawSelectionOrder,
    pub heuristic: super::heuristic::Kind,
    /// Bind any class whose surviving domain is no larger than the number of
    /// separable threats it touches (`+deg`).
    pub degree_binding: bool,
}

impl Lane {
    /// Parses `ORDER[@HEUR][+deg]`; the heuristic defaults to `ADD`.
    pub fn parse(spec: &str) -> Result<Lane, String> {
        let (rest, degree_binding) = match spec.strip_suffix("+deg") {
            Some(rest) => (rest, true),
            None => (spec, false),
        };
        let (order, heuristic) = match rest.rsplit_once('@') {
            Some((order, heuristic)) => (order, heuristic),
            None => (rest, "ADD"),
        };
        Ok(Lane {
            name: spec.to_string(),
            flaw_order: crate::heuristics::FlawSelectionOrder::parse(order)?,
            heuristic: super::heuristic::Kind::parse(heuristic)?,
            degree_binding,
        })
    }
}

/// Search configuration.
#[derive(Debug, Clone)]
pub struct Config {
    /// Lanes expanded round-robin, one node each per round; the first plan
    /// found by any lane is returned. Empty selects [`DEFAULT_LANES`].
    pub lanes: Vec<Lane>,
    pub weight: f32,
    /// Limit on nodes generated across all lanes.
    pub node_limit: usize,
    pub time_limit: Option<Duration>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            lanes: Vec::new(),
            weight: 1.0,
            node_limit: usize::MAX,
            time_limit: None,
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct Stats {
    /// Time in heuristic evaluation, flaw selection, binding choice and
    /// refinement (with propagation), for profiling.
    pub phase: [Duration; 4],
    pub generated: usize,
    pub expanded: usize,
    pub dead: usize,
    pub max_steps: usize,
    /// The lane that found the plan.
    pub solved_by: Option<String>,
}

/// A validated, totally ordered plan: schema names and arguments.
#[derive(Debug, Clone)]
pub struct Solution {
    pub actions: Vec<(usize, Vec<Object>)>,
    pub cost: usize,
}

impl Solution {
    pub fn format(&self, domain: &Domain, problem: &Problem) -> String {
        let mut out = String::new();
        for (time, (action, args)) in self.actions.iter().enumerate() {
            let names: Vec<&str> = args
                .iter()
                .map(|o| problem.objects.object_name(Some(&domain.constants), *o))
                .collect();
            out.push_str(&format!(
                "{time}: ({} {})\n",
                domain.actions[*action].name,
                names.join(" ")
            ));
        }
        out
    }
}

pub enum Outcome {
    Solved(Solution),
    NoSolution,
    LimitReached,
}

struct Node {
    f: f32,
    h: f32,
    id: usize,
    plan: Rc<Plan>,
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == std::cmp::Ordering::Equal
    }
}
impl Eq for Node {}
impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Node {
    /// Max-heap: lower f, then lower h, then newer id first.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other
            .f
            .total_cmp(&self.f)
            .then(other.h.total_cmp(&self.h))
            .then(self.id.cmp(&other.id))
    }
}

/// Compiles and solves. Unsupported tasks are reported, not attempted.
pub fn solve(domain: &Domain, problem: &Problem, config: &Config) -> Result<(Outcome, Stats), Unsupported> {
    let task = LiftedTask::compile(domain, problem)?;
    Ok(solve_task(domain, problem, &task, config))
}

/// A lane's open list and heuristic.
struct Running<'a> {
    lane: &'a Lane,
    estimator: Estimator,
    queue: BinaryHeap<Node>,
    exhausted: bool,
}

/// Shared search state and knobs.
struct Search<'a, 'c> {
    ctx: &'c Ctx<'a>,
    domain: &'a Domain,
    problem: &'a Problem,
    weight: f32,
    bind_policy: BindPolicy,
    mac_budget: usize,
    trace: usize,
}

impl Search<'_, '_> {
    fn push(&self, lane: &mut Running, mut plan: Plan, stats: &mut Stats) {
        stats.generated += 1;
        if self.mac_budget > 0 && !bindings_feasible(self.ctx, &plan, self.mac_budget) {
            stats.dead += 1;
            return;
        }
        let started = Instant::now();
        let h = lane.estimator.estimate(self.ctx, &plan);
        stats.phase[0] += started.elapsed();
        plan.domains = None;
        if !h.is_finite() {
            stats.dead += 1;
            return;
        }
        lane.queue.push(Node {
            f: plan.cost as f32 + self.weight * h,
            h,
            id: stats.generated,
            plan: Rc::new(plan),
        });
    }

    /// Expands the lane's best node: a solution, or `None`.
    fn expand(&self, lane: &mut Running, stats: &mut Stats) -> Option<Solution> {
        let Some(node) = lane.queue.pop() else {
            lane.exhausted = true;
            return None;
        };
        let ctx = self.ctx;
        stats.expanded += 1;
        let plan = node.plan.clone();
        stats.max_steps = stats.max_steps.max(plan.num_steps());
        if plan.complete() {
            if let Some(solution) = complete(ctx, self.domain, self.problem, &plan) {
                return Some(solution);
            }
            stats.dead += 1;
            return None;
        }
        let started = Instant::now();
        let selected = super::flaws::select(ctx, &plan, &lane.lane.flaw_order, &lane.estimator);
        stats.phase[1] += started.elapsed();
        let started = Instant::now();
        let binding = choose_binding(ctx, &plan, &selected, self.bind_policy, lane.lane.degree_binding);
        stats.phase[2] += started.elapsed();
        if stats.expanded <= self.trace {
            self.trace_node(lane, &node, &plan, &selected, &binding);
        }
        let started = Instant::now();
        let children = match binding {
            Some((class, objects)) => super::plan::refine_bind(ctx, &plan, class, &objects),
            None => match selected {
                super::flaws::Flaw::Threat(t) => refine_threat(ctx, &plan, t),
                super::flaws::Flaw::Open(o) => refine_open(ctx, &plan, o),
                super::flaws::Flaw::Dead => Vec::new(),
            },
        };
        stats.phase[3] += started.elapsed();
        for child in children {
            self.push(lane, child, stats);
        }
        None
    }

    fn trace_node(
        &self,
        lane: &Running,
        node: &Node,
        plan: &Plan,
        selected: &super::flaws::Flaw,
        binding: &Option<(crate::bindings::StepVariable, Vec<Object>)>,
    ) {
        let ctx = self.ctx;
        let describe = |consumer: usize, f: &super::task::LFact| {
            let resolve = |t: &Term| plan.bindings.binding(*t, consumer);
            let resolved = super::task::LFact {
                var: f.var,
                inv: f.inv.iter().map(resolve).collect(),
                value: match &f.value {
                    super::task::LValue::None => super::task::LValue::None,
                    super::task::LValue::Part { part, args } => super::task::LValue::Part {
                        part: *part,
                        args: args.iter().map(resolve).collect(),
                    },
                },
            };
            ctx.task.fact_name(self.domain, self.problem, &resolved)
        };
        let flaw = match (binding, selected) {
            (Some((class, objects)), _) => format!("bind ?{}@{} over {} objects", class.0 .0, class.1, objects.len()),
            (None, super::flaws::Flaw::Open(o)) => {
                let name = if o.consumer == super::plan::GOAL_ID {
                    "goal".to_string()
                } else {
                    ctx.schema_of(plan, o.consumer).name.clone()
                };
                format!("open {} for {}@{}", describe(o.consumer, ctx.condition(plan, o.consumer, o.cond)), name, o.consumer)
            }
            (None, super::flaws::Flaw::Threat(t)) => format!(
                "threat step {} ({}) on {}",
                t.step,
                ctx.schema_of(plan, t.step).name,
                describe(t.link.consumer, ctx.condition(plan, t.link.consumer, t.link.cond))
            ),
            (None, super::flaws::Flaw::Dead) => "dead".to_string(),
        };
        eprintln!(
            "expand [{}] f={} h={} cost={} steps={} opens={} threats={} | {}",
            lane.lane.name,
            node.f,
            node.h,
            plan.cost,
            plan.num_steps(),
            plan.num_opens,
            plan.num_threats,
            flaw
        );
    }
}

pub fn solve_task(domain: &Domain, problem: &Problem, task: &LiftedTask, config: &Config) -> (Outcome, Stats) {
    let global = GlobalTypes(task.var_types.clone());
    let types = TypeContext {
        types: &domain.types,
        objects: &problem.objects,
        constants: &domain.constants,
        step_vars: &global,
    };
    let mut ctx = Ctx::new(task, types);
    if std::env::var("POTOROO_LFDR_SYM").map_or(true, |v| v != "0") {
        let symmetries = crate::symmetry::ObjectSymmetries::compute(domain, problem);
        if !symmetries.is_empty() {
            ctx.symmetries = Some(Rc::new(symmetries));
        }
    }
    let ctx = ctx;
    let mut stats = Stats::default();
    if task.unsolvable {
        return (Outcome::NoSolution, stats);
    }
    let Some(root) = Plan::initial(&ctx) else {
        return (Outcome::NoSolution, stats);
    };
    let defaults: Vec<Lane>;
    let lanes: &[Lane] = if config.lanes.is_empty() {
        defaults = DEFAULT_LANES.iter().map(|l| Lane::parse(l).expect("valid default lane")).collect();
        &defaults
    } else {
        &config.lanes
    };
    let search = Search {
        ctx: &ctx,
        domain,
        problem,
        weight: config.weight,
        bind_policy: BindPolicy::from_env(),
        mac_budget: std::env::var("POTOROO_LFDR_MAC").ok().and_then(|v| v.parse().ok()).unwrap_or(0),
        trace: std::env::var("POTOROO_TRACE").ok().and_then(|v| v.parse().ok()).unwrap_or(0),
    };
    // One planning graph serves every lane.
    let mut graph = None;
    let mut running: Vec<Running> = lanes
        .iter()
        .map(|lane| {
            let estimator = Estimator::new_shared(domain, problem, lane.heuristic, &mut graph);
            Running {
                lane,
                estimator,
                queue: BinaryHeap::new(),
                exhausted: false,
            }
        })
        .collect();
    for lane in &mut running {
        search.push(lane, root.clone(), &mut stats);
    }
    let start = Instant::now();
    loop {
        if running.iter().all(|l| l.exhausted) {
            return (Outcome::NoSolution, stats);
        }
        for lane in &mut running {
            if lane.exhausted {
                continue;
            }
            if stats.generated >= config.node_limit || config.time_limit.is_some_and(|limit| start.elapsed() > limit) {
                return (Outcome::LimitReached, stats);
            }
            if let Some(solution) = search.expand(lane, &mut stats) {
                stats.solved_by = Some(lane.lane.name.clone());
                return (Outcome::Solved(solution), stats);
            }
        }
    }
}

/// When an unbound variable is the flaw to refine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindPolicy {
    /// Never: variables are ground only at completion.
    Never,
    /// Once no open condition remains, before separable threats.
    End,
    /// As `End`, restricted to classes in the remaining threats.
    Threat,
    /// Whenever its domain is smaller than the selected flaw's repairs.
    Lr,
}

impl BindPolicy {
    fn from_env() -> Self {
        match std::env::var("POTOROO_LFDR_BINDFLAW").as_deref() {
            Ok("never") => BindPolicy::Never,
            Ok("end") => BindPolicy::End,
            Ok("lr") => BindPolicy::Lr,
            _ => BindPolicy::Threat,
        }
    }
}

fn choose_binding(
    ctx: &Ctx,
    plan: &Plan,
    selected: &super::flaws::Flaw,
    policy: BindPolicy,
    degree_binding: bool,
) -> Option<(crate::bindings::StepVariable, Vec<Object>)> {
    use super::flaws::Flaw;
    match policy {
        BindPolicy::Never => None,
        BindPolicy::End => {
            if plan.num_opens > 0 || matches!(selected, Flaw::Dead) {
                return None;
            }
            if let Flaw::Threat(t) = selected {
                if super::plan::definite(ctx, plan, t) {
                    return None;
                }
            }
            super::plan::binding_candidates(ctx, plan).into_iter().next().map(|(c, _, d)| (c, d))
        }
        BindPolicy::Threat => threat_binding(ctx, plan, selected, degree_binding),
        BindPolicy::Lr => {
            let (class, _, objects) = super::plan::binding_candidates(ctx, plan).into_iter().next()?;
            let repairs = match selected {
                Flaw::Dead => return None,
                Flaw::Threat(t) => super::plan::count_threat_options(ctx, plan, t).unwrap_or(0),
                Flaw::Open(o) => super::plan::count_refinements(ctx, plan, *o, objects.len() + 1),
            };
            (objects.len() < repairs).then_some((class, objects))
        }
    }
}

/// Bindings chosen to force threats (dom/deg with forward checking). Over
/// the classes in separable threats: prune objects that leave some threat
/// without a repair; an empty domain kills the plan and a single survivor is
/// a forced binding taken at once. Otherwise, once no open condition remains
/// or the surviving domain undercuts the selected flaw's repairs, bind the
/// class minimising domain size over threat degree, trying first the objects
/// that remove the most threats.
fn threat_binding(
    ctx: &Ctx,
    plan: &Plan,
    selected: &super::flaws::Flaw,
    degree_rule: bool,
) -> Option<(crate::bindings::StepVariable, Vec<Object>)> {
    use super::flaws::Flaw;
    if matches!(selected, Flaw::Dead) || plan.num_threats == 0 {
        return None;
    }
    if let Flaw::Threat(t) = selected {
        if super::plan::definite(ctx, plan, t) {
            return None;
        }
    }
    let mut touching: std::collections::HashMap<crate::bindings::StepVariable, Vec<super::plan::Threat>> =
        Default::default();
    for t in chain::iter(&plan.threats) {
        if super::plan::definite(ctx, plan, t) {
            continue;
        }
        let mut classes = super::plan::threat_classes(ctx, plan, t);
        classes.sort();
        classes.dedup();
        for c in classes {
            touching.entry(c).or_default().push(*t);
        }
    }
    if touching.is_empty() {
        return None;
    }
    let mut best: Option<(f32, usize, crate::bindings::StepVariable, Vec<Object>)> = None;
    for (class, full, domain) in super::plan::binding_candidates(ctx, plan) {
        let Some(threats) = touching.get(&class) else {
            continue;
        };
        if domain.len() > 16 {
            continue;
        }
        let mut viable = super::plan::viable_values(ctx, plan, class, &domain, threats);
        // Symmetric objects stand or fall together, so no viable
        // representative means none at all. One representative is forced only
        // when symmetry did not remove its alternatives.
        let forced = viable.len() == 1
            && (full.len() == domain.len()
                || super::plan::viable_values(ctx, plan, class, &full, threats).len() == 1);
        if viable.is_empty() || forced {
            let objects = viable.into_iter().map(|(o, _)| o).collect();
            return Some((class, objects));
        }
        // Decide on the unreduced size: symmetry shrinks a binding's
        // children, not its commitment (pruned objects stay possible for
        // other classes), so it must not make binding look cheaper.
        let size = viable.len() + (full.len() - domain.len());
        if size <= 1 {
            continue;
        }
        viable.sort_by_key(|(o, removed)| (std::cmp::Reverse(*removed), *o));
        let score = size as f32 / threats.len() as f32;
        if best.as_ref().is_none_or(|(s, _, _, _)| score < *s) {
            best = Some((score, size, class, viable.into_iter().map(|(o, _)| o).collect()));
        }
    }
    let (score, size, class, objects) = best?;
    // A class whose surviving domain is no larger than the number of
    // separable threats it touches settles at least as many threats as it
    // creates children: bind it whatever the selected flaw.
    if plan.num_opens == 0 || (degree_rule && score <= 1.0) {
        return Some((class, objects));
    }
    let repairs = match selected {
        Flaw::Threat(t) => super::plan::count_threat_options(ctx, plan, t).unwrap_or(0),
        Flaw::Open(o) => super::plan::count_refinements(ctx, plan, *o, size + 1),
        Flaw::Dead => return None,
    };
    (size < repairs).then_some((class, objects))
}

/// Grounds every step variable consistently with bindings and static
/// constraints, linearises, and validates against the STRIPS semantics.
fn complete(ctx: &Ctx, domain: &Domain, problem: &Problem, plan: &Plan) -> Option<Solution> {
    let mut variables = Vec::new();
    for step in 1..=plan.num_steps() {
        for v in &ctx.schema_of(plan, step).parameters {
            variables.push((*v, step));
        }
    }
    let mut bindings = plan.bindings.clone();
    if !ground(ctx, plan, &variables, 0, &mut bindings) {
        if std::env::var_os("POTOROO_TRACE").is_some() {
            eprintln!("  (grounding search exhausted)");
        }
        return None;
    }
    // Topological order from the transitive orderings.
    let n = plan.num_steps();
    let mut placed = vec![false; n + 1];
    let mut order = Vec::with_capacity(n);
    while order.len() < n {
        let next = (1..=n).find(|&s| {
            !placed[s]
                && (1..=n).all(|p| {
                    placed[p] || p == s || plan.orderings.possibly_before(s, StepTime::AtEnd, p, StepTime::AtStart)
                })
        });
        let Some(next) = next else {
            if std::env::var_os("POTOROO_TRACE").is_some() {
                eprintln!("  (no topological order)");
            }
            return None;
        };
        placed[next] = true;
        order.push(next);
    }
    let mut actions = Vec::with_capacity(n);
    for step in order {
        let schema = ctx.schema_of(plan, step);
        let args: Vec<Object> = schema
            .parameters
            .iter()
            .map(|v| bindings.binding(Term::Variable(*v), step).as_object())
            .collect();
        actions.push((schema.action, args));
    }
    let solution = Solution {
        actions,
        cost: plan.cost,
    };
    match validate(domain, problem, &solution) {
        Ok(()) => Some(solution),
        Err(e) => panic!("lifted FDR produced an invalid plan: {e}\n{}", solution.format(domain, problem)),
    }
}

fn ground(
    ctx: &Ctx,
    plan: &Plan,
    variables: &[(crate::terms::Variable, usize)],
    i: usize,
    bindings: &mut Rc<crate::bindings::Bindings>,
) -> bool {
    let mut budget = usize::MAX;
    ground_within(ctx, plan, variables, i, bindings, &mut budget) == Some(true)
}

/// Depth-first grounding with arc consistency at each assignment (MAC).
/// `None` when the assignment budget runs out before an answer.
fn ground_within(
    ctx: &Ctx,
    plan: &Plan,
    variables: &[(crate::terms::Variable, usize)],
    i: usize,
    bindings: &mut Rc<crate::bindings::Bindings>,
    budget: &mut usize,
) -> Option<bool> {
    if i == variables.len() {
        return Some(true);
    }
    let (v, step) = variables[i];
    if let Term::Object(_) = bindings.binding(Term::Variable(v), step) {
        return ground_within(ctx, plan, variables, i + 1, bindings, budget);
    }
    for o in bindings.domain(&ctx.types, v, step) {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        let saved = bindings.clone();
        let Some(next) = bindings.add(
            &ctx.types,
            &[crate::bindings::Binding::new(v, step, Term::Object(o), step, true)],
            false,
        ) else {
            continue;
        };
        let mut probe = plan.clone();
        probe.bindings = next;
        let Some(propagated) = super::plan::propagate_statics(ctx, &probe) else {
            continue;
        };
        *bindings = propagated;
        match ground_within(ctx, plan, variables, i + 1, bindings, budget) {
            Some(true) => return Some(true),
            None => return None,
            Some(false) => {}
        }
        *bindings = saved;
    }
    Some(false)
}

/// Whether the plan's binding constraints have a solution, searched within
/// `budget` assignments; an exhausted budget counts as feasible.
pub fn bindings_feasible(ctx: &Ctx, plan: &Plan, budget: usize) -> bool {
    let mut variables = Vec::new();
    for step in 1..=plan.num_steps() {
        for v in &ctx.schema_of(plan, step).parameters {
            variables.push((*v, step));
        }
    }
    let mut bindings = plan.bindings.clone();
    let mut budget = budget;
    ground_within(ctx, plan, &variables, 0, &mut bindings, &mut budget) != Some(false)
}

/// Simulates the plan under STRIPS semantics (deletes before adds).
pub fn validate(domain: &Domain, problem: &Problem, solution: &Solution) -> Result<(), String> {
    let mut state: HashSet<Atom> = problem.init_atoms.clone();
    for (time, (action, args)) in solution.actions.iter().enumerate() {
        let schema = &domain.actions[*action];
        let mut s: Vec<Option<Object>> = vec![None; schema.var_types.len()];
        for (v, o) in schema.parameters.iter().zip(args) {
            s[v.0 as usize] = Some(*o);
        }
        if !holds(&schema.precondition, &s, &state) {
            return Err(format!("step {time} ({}) is not applicable", schema.name));
        }
        let mut next = state.clone();
        for e in &schema.effects {
            if let Literal::Negation(a) = &e.literal {
                next.remove(&ground_atom(a, &s));
            }
        }
        for e in &schema.effects {
            if let Literal::Atom(a) = &e.literal {
                next.insert(ground_atom(a, &s));
            }
        }
        state = next;
    }
    if holds(&problem.goal, &[], &state) {
        Ok(())
    } else {
        Err("goal not reached".into())
    }
}

fn subst(t: Term, s: &[Option<Object>]) -> Object {
    match t {
        Term::Object(o) => o,
        Term::Variable(v) => s[v.0 as usize].expect("bound parameter"),
    }
}

fn ground_atom(a: &Atom, s: &[Option<Object>]) -> Atom {
    Atom {
        predicate: a.predicate,
        terms: a.terms.iter().map(|t| Term::Object(subst(*t, s))).collect(),
    }
}

fn holds(f: &Formula, s: &[Option<Object>], state: &HashSet<Atom>) -> bool {
    match f {
        Formula::True => true,
        Formula::False => false,
        Formula::Atom(a) => state.contains(&ground_atom(a, s)),
        Formula::Negation(a) => !state.contains(&ground_atom(a, s)),
        Formula::Equality { left, right, .. } => subst(*left, s) == subst(*right, s),
        Formula::Inequality { left, right, .. } => subst(*left, s) != subst(*right, s),
        Formula::Conjunction(fs) => fs.iter().all(|f| holds(f, s, state)),
        Formula::Disjunction(fs) => fs.iter().any(|f| holds(f, s, state)),
        Formula::Exists { .. } | Formula::Forall { .. } => panic!("quantifier in a supported task"),
    }
}
