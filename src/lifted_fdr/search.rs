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

/// VHPOP's MW-Loc: threats by fewest refinements, then the newest step's open
/// conditions by most estimated work. Best on the development panel among
/// ZLIFO, LCFR, LCFR-DSep, DSep-LC, LCFR-Loc-Conf, MW-Loc and MC-Loc
/// (`investigation/lifted-fdr/findings.md`).
pub const DEFAULT_FLAW_ORDER: &str = "MW-Loc";

/// Search configuration.
#[derive(Debug, Clone)]
pub struct Config {
    pub heuristic: super::heuristic::Kind,
    pub weight: f32,
    pub node_limit: usize,
    pub time_limit: Option<Duration>,
    /// Flaw-selection order (`-f`); `None` selects [`DEFAULT_FLAW_ORDER`].
    pub flaw_order: Option<crate::heuristics::FlawSelectionOrder>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            heuristic: super::heuristic::Kind::Add,
            weight: 1.0,
            node_limit: usize::MAX,
            time_limit: None,
            flaw_order: None,
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

pub fn solve_task(domain: &Domain, problem: &Problem, task: &LiftedTask, config: &Config) -> (Outcome, Stats) {
    let global = GlobalTypes(task.var_types.clone());
    let types = TypeContext {
        types: &domain.types,
        objects: &problem.objects,
        constants: &domain.constants,
        step_vars: &global,
    };
    let ctx = Ctx::new(task, types);
    let estimator = Estimator::new(&ctx, domain, problem, config.heuristic);
    let mut stats = Stats::default();
    let Some(root) = Plan::initial(&ctx) else {
        return (Outcome::NoSolution, stats);
    };
    let flaw_order = config.flaw_order.clone().unwrap_or_else(|| {
        crate::heuristics::FlawSelectionOrder::parse(DEFAULT_FLAW_ORDER).expect("valid default")
    });
    let trace: usize = std::env::var("POTOROO_TRACE").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let start = Instant::now();
    let mut queue = BinaryHeap::new();
    let bind_policy = BindPolicy::from_env();
    let mac_budget: usize = std::env::var("POTOROO_LFDR_MAC")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(0);
    let push = |queue: &mut BinaryHeap<Node>, mut plan: Plan, stats: &mut Stats| {
        stats.generated += 1;
        if mac_budget > 0 && !bindings_feasible(&ctx, &plan, mac_budget) {
            stats.dead += 1;
            return;
        }
        let started = Instant::now();
        let h = estimator.estimate(&ctx, &plan);
        stats.phase[0] += started.elapsed();
        plan.domains = None;
        if !h.is_finite() {
            stats.dead += 1;
            return;
        }
        queue.push(Node {
            f: plan.cost as f32 + config.weight * h,
            h,
            id: stats.generated,
            plan: Rc::new(plan),
        });
    };
    push(&mut queue, root, &mut stats);
    while let Some(node) = queue.pop() {
        if stats.generated >= config.node_limit
            || config.time_limit.is_some_and(|limit| start.elapsed() > limit)
        {
            return (Outcome::LimitReached, stats);
        }
        stats.expanded += 1;
        let plan = node.plan;
        if stats.expanded <= trace {
            eprintln!(
                "expand f={} h={} cost={} steps={} opens={} threats={}",
                node.f,
                node.h,
                plan.cost,
                plan.num_steps(),
                plan.num_opens,
                plan.num_threats
            );
            if let Some(open) = chain::iter(&plan.opens).next() {
                if plan.num_threats == 0 {
                    let f = ctx.condition(&plan, open.consumer, open.cond);
                    let resolved = super::task::LFact {
                        var: f.var,
                        inv: f.inv.iter().map(|t| plan.bindings.binding(*t, open.consumer)).collect(),
                        value: match &f.value {
                            super::task::LValue::None => super::task::LValue::None,
                            super::task::LValue::Part { part, args } => super::task::LValue::Part {
                                part: *part,
                                args: args.iter().map(|t| plan.bindings.binding(*t, open.consumer)).collect(),
                            },
                        },
                    };
                    eprintln!("   newest open @{}: {}", open.consumer, ctx.task.fact_name(domain, problem, &resolved));
                }
            }
        }
        stats.max_steps = stats.max_steps.max(plan.num_steps());
        if plan.complete() {
            if let Some(solution) = complete(&ctx, domain, problem, &plan) {
                return (Outcome::Solved(solution), stats);
            }
            if stats.dead < 3 && trace > 0 {
                eprintln!(
                    "grounding failed for a complete plan (propagation {}):",
                    if super::plan::propagate_statics(&ctx, &plan).is_some() { "consistent" } else { "INCONSISTENT" }
                );
                for link in chain::iter(&plan.links) {
                    for w in 1..=plan.num_steps() {
                        for a in 0..ctx.schema_of(&plan, w).assigns.len() {
                            if super::plan::threatens(&ctx, &plan, w, a as u16, link) {
                                eprintln!("  MISSED THREAT: step {w} assign {a} on link {:?}", link);
                            }
                        }
                    }
                }
                for link in chain::iter(&plan.links) {
                    if link.producer == super::plan::INIT_ID {
                        let f = ctx.condition(&plan, link.consumer, link.cond);
                        let resolved = super::task::LFact {
                            var: f.var,
                            inv: f.inv.iter().map(|t| plan.bindings.binding(*t, link.consumer)).collect(),
                            value: match &f.value {
                                super::task::LValue::None => super::task::LValue::None,
                                super::task::LValue::Part { part, args } => super::task::LValue::Part {
                                    part: *part,
                                    args: args.iter().map(|t| plan.bindings.binding(*t, link.consumer)).collect(),
                                },
                            },
                        };
                        eprintln!("  init -> {}: {}", link.consumer, ctx.task.fact_name(domain, problem, &resolved));
                    }
                }
                for step in 1..=plan.num_steps() {
                    let schema = ctx.schema_of(&plan, step);
                    let args: Vec<String> = schema
                        .parameters
                        .iter()
                        .map(|v| match plan.bindings.binding(Term::Variable(*v), step) {
                            Term::Object(o) => problem.objects.object_name(Some(&domain.constants), o).to_string(),
                            Term::Variable(v) => {
                                let rep = plan.bindings.representative(v, step);
                                let ncd = plan.bindings.non_codesignated(v, step).len();
                                format!("?{}@{}#{}!{}", rep.0 .0, rep.1, plan.bindings.domain(&ctx.types, v, step).len(), ncd)
                            }
                        })
                        .collect();
                    let statics: Vec<String> = schema.statics.iter().map(|a| domain.predicates.name(a.predicate).to_string()).collect();
                    eprintln!("  {step}: {} {} statics {:?} ok={}", schema.name, args.join(" "), statics, super::plan::step_statics_possible(&ctx, &plan, step));
                }
            }
            stats.dead += 1;
            continue;
        }
        let started = Instant::now();
        let selected = super::flaws::select(&ctx, &plan, &flaw_order, &estimator);
        stats.phase[1] += started.elapsed();
        let started = Instant::now();
        let binding = choose_binding(&ctx, &plan, &selected, bind_policy);
        stats.phase[2] += started.elapsed();
        if stats.expanded <= trace {
            let describe = |consumer: usize, f: &super::task::LFact| {
                let resolved = super::task::LFact {
                    var: f.var,
                    inv: f.inv.iter().map(|t| plan.bindings.binding(*t, consumer)).collect(),
                    value: match &f.value {
                        super::task::LValue::None => super::task::LValue::None,
                        super::task::LValue::Part { part, args } => super::task::LValue::Part {
                            part: *part,
                            args: args.iter().map(|t| plan.bindings.binding(*t, consumer)).collect(),
                        },
                    },
                };
                ctx.task.fact_name(domain, problem, &resolved)
            };
            match (&binding, &selected) {
                (Some((class, objects)), _) => eprintln!("   flaw: bind ?{}@{} over {} objects", class.0 .0, class.1, objects.len()),
                (None, super::flaws::Flaw::Open(o)) => {
                    let name = if o.consumer == super::plan::GOAL_ID { "goal".to_string() } else { ctx.schema_of(&plan, o.consumer).name.clone() };
                    eprintln!("   flaw: open {} for {}@{}", describe(o.consumer, ctx.condition(&plan, o.consumer, o.cond)), name, o.consumer)
                }
                (None, super::flaws::Flaw::Threat(t)) => eprintln!(
                    "   flaw: threat step {} ({}) on {}",
                    t.step,
                    ctx.schema_of(&plan, t.step).name,
                    describe(t.link.consumer, ctx.condition(&plan, t.link.consumer, t.link.cond))
                ),
                (None, super::flaws::Flaw::Dead) => eprintln!("   flaw: dead"),
            }
        }
        let started = Instant::now();
        let children = match binding {
            Some((class, objects)) => super::plan::refine_bind(&ctx, &plan, class, &objects),
            None => match selected {
                super::flaws::Flaw::Threat(t) => refine_threat(&ctx, &plan, t),
                super::flaws::Flaw::Open(o) => refine_open(&ctx, &plan, o),
                super::flaws::Flaw::Dead => Vec::new(),
            },
        };
        stats.phase[3] += started.elapsed();
        for child in children {
            push(&mut queue, child, &mut stats);
        }
    }
    (Outcome::NoSolution, stats)
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
            super::plan::binding_candidates(ctx, plan).into_iter().next()
        }
        BindPolicy::Threat => threat_binding(ctx, plan, selected),
        BindPolicy::Lr => {
            let (class, objects) = super::plan::binding_candidates(ctx, plan).into_iter().next()?;
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
    let mut best: Option<(f32, crate::bindings::StepVariable, Vec<Object>)> = None;
    for (class, domain) in super::plan::binding_candidates(ctx, plan) {
        let Some(threats) = touching.get(&class) else {
            continue;
        };
        if domain.len() > 16 {
            continue;
        }
        let mut viable = super::plan::viable_values(ctx, plan, class, &domain, threats);
        if viable.len() <= 1 {
            // Dead (no object) or forced (one object): take it now.
            let objects = viable.into_iter().map(|(o, _)| o).collect();
            return Some((class, objects));
        }
        viable.sort_by_key(|(o, removed)| (std::cmp::Reverse(*removed), *o));
        let score = viable.len() as f32 / threats.len() as f32;
        if best.as_ref().is_none_or(|(s, _, _)| score < *s) {
            best = Some((score, class, viable.into_iter().map(|(o, _)| o).collect()));
        }
    }
    let (_, class, objects) = best?;
    let repairs = match selected {
        Flaw::Threat(t) => super::plan::count_threat_options(ctx, plan, t).unwrap_or(0),
        Flaw::Open(o) => super::plan::count_refinements(ctx, plan, *o, objects.len() + 1),
        Flaw::Dead => return None,
    };
    (plan.num_opens == 0 || objects.len() < repairs).then_some((class, objects))
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
