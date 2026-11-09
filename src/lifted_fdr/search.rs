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
    /// Time in heuristic evaluation, flaw selection, binding choice,
    /// refinement (with propagation), forced threats and binding
    /// feasibility, for profiling.
    pub phase: [Duration; 6],
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

/// The flaw a queued child refined, to rebuild it from its parent.
#[derive(Clone, Copy)]
enum Refined {
    Open(super::plan::Open),
    Threat(super::plan::Threat),
    Bind(super::binds::ClassId),
}

/// A queued plan: built, or a recipe rebuilt on pop. Recipes keep only the
/// parent (shared with siblings) and which refinement made the child; the
/// child is ranked when generated and then dropped, as the ground FDR
/// planner does for new steps. At the cluster's time/memory ratio searches
/// run out of memory long before time, so the rebuild is worth its cost.
enum Entry {
    Built(Rc<Plan>),
    Recipe {
        base: Rc<Expansion>,
        choice: super::plan::Choice,
    },
}

/// What siblings share: their parent and the flaw it refined.
struct Expansion {
    parent: Rc<Plan>,
    flaw: Refined,
    /// A grounding of the parent's bindings, tried first for its children.
    witness: Option<Witness>,
}

pub use super::plan::Witness;

/// The outcome of a bounded joint check of a plan's binding constraints.
pub enum Feasibility {
    Witness(Witness),
    /// The budget ran out: assumed feasible.
    Unknown,
    Infeasible,
}

struct Node {
    f: f32,
    h: f32,
    id: u32,
    entry: Entry,
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
    /// Lowest h popped so far, for `POTOROO_LFDR_PROGRESS`.
    best_f: std::cell::Cell<f32>,
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
    /// Queue children as recipes (`POTOROO_LFDR_DEFER=0` stores them built).
    defer: bool,
    /// Keep each expansion's first-ranked child built (`POTOROO_LFDR_DEFER=best`):
    /// cheaper when that child is popped next, but in round-robin lanes it
    /// often is not, and keeping it built costs memory.
    keep_best: bool,
    /// Report each lane's f layers (`POTOROO_LFDR_PROGRESS`).
    progress: bool,
    /// Drop resolved threats at expansion (`POTOROO_LFDR_STALE=0` keeps them
    /// as one-child refinements).
    drop_stale: bool,
    force_rounds: usize,
    /// Drop children whose new threats include one with no resolution
    /// (`POTOROO_LFDR_NEWDEAD=0` disables).
    dead_new_threats: bool,
    /// Plans with `h` at most this get a bounded joint check of their
    /// bindings (`POTOROO_LFDR_FEAS=H[:BUDGET]`).
    feasibility_h: f32,
    feasibility_budget: usize,
    /// Check plans when popped for expansion (default) rather than every
    /// child when generated (`POTOROO_LFDR_FEASPOP=0`).
    feasibility_at_pop: bool,
    /// Expansions whose plan is printed in full (`POTOROO_LFDR_DUMP`).
    dump: Vec<usize>,
}

impl Search<'_, '_> {
    /// Ranks a generated plan: `(f, h, id)`, or `None` when it is dead.
    fn evaluate(
        &self,
        lane: &Running,
        plan: &Plan,
        hint: Option<&Witness>,
        same_bindings: bool,
        stats: &mut Stats,
    ) -> Option<(f32, f32, u32)> {
        stats.generated += 1;
        if self.mac_budget > 0 && !bindings_feasible(self.ctx, plan, self.mac_budget) {
            stats.dead += 1;
            return None;
        }
        let started = Instant::now();
        let h = lane.estimator.estimate(self.ctx, plan);
        stats.phase[0] += started.elapsed();
        if !h.is_finite() {
            stats.dead += 1;
            return None;
        }
        if h <= self.feasibility_h
            && !self.feasibility_at_pop
            && !(same_bindings && hint.is_some())
            && matches!(
                find_witness(self.ctx, plan, hint, self.feasibility_budget),
                Feasibility::Infeasible
            )
        {
            stats.dead += 1;
            return None;
        }
        Some((plan.cost as f32 + self.weight * h, h, stats.generated as u32))
    }

    fn enqueue(lane: &mut Running, (f, h, id): (f32, f32, u32), entry: Entry) {
        // Grow a large queue by an eighth rather than doubling it.
        if lane.queue.len() == lane.queue.capacity() && lane.queue.capacity() >= 1 << 16 {
            lane.queue.reserve_exact(lane.queue.capacity() / 8);
        }
        lane.queue.push(Node { f, h, id, entry });
    }

    fn push(&self, lane: &mut Running, plan: Plan, stats: &mut Stats) {
        if let Some(rank) = self.evaluate(lane, &plan, None, false, stats) {
            Self::enqueue(lane, rank, Entry::Built(Rc::new(plan)));
        }
    }

    /// Expands the lane's best node: a solution, or `None`.
    fn expand(&self, lane: &mut Running, stats: &mut Stats) -> Option<Solution> {
        let Some(node) = lane.queue.pop() else {
            lane.exhausted = true;
            return None;
        };
        let ctx = self.ctx;
        stats.expanded += 1;
        if self.progress && node.h < lane.best_f.get() {
            lane.best_f.set(node.h);
            eprintln!(
                "progress [{}] f={} h={} expanded={} generated={} queued={}",
                lane.lane.name,
                node.f,
                node.h,
                stats.expanded,
                stats.generated,
                lane.queue.len()
            );
        }
        // A child that only added an ordering keeps its parent's bindings,
        // and so its solution.
        let (parent_witness, same_bindings) = match &node.entry {
            Entry::Recipe { base, choice } => (
                base.witness.clone(),
                matches!(
                    choice,
                    super::plan::Choice::Demote | super::plan::Choice::Promote | super::plan::Choice::Drop
                ),
            ),
            Entry::Built(_) => (None, false),
        };
        let plan = match &node.entry {
            Entry::Built(plan) => plan.clone(),
            Entry::Recipe { base, choice } => {
                let started = Instant::now();
                let rebuilt = rebuild(ctx, &base.parent, base.flaw, *choice);
                stats.phase[3] += started.elapsed();
                match rebuilt {
                    Some(plan) => Rc::new(plan),
                    None => {
                        debug_assert!(false, "a queued recipe must rebuild");
                        return None;
                    }
                }
            }
        };
        // Threats that orderings or bindings have since resolved are dropped
        // here in one pass, rather than each costing a search node.
        // (Forcing drops stale threats too.)
        let plan = if self.drop_stale && self.force_rounds == 0 {
            super::plan::without_stale_threats(ctx, plan)
        } else {
            plan
        };
        // Forced threats are resolved in place (`POTOROO_LFDR_FORCE=N` rounds,
        // 0 to keep them as search nodes).
        let plan = if self.force_rounds > 0 {
            let started = Instant::now();
            let forced = super::plan::force_threats(ctx, plan, self.force_rounds);
            stats.phase[4] += started.elapsed();
            match forced {
                Some(plan) => plan,
                None => {
                    stats.dead += 1;
                    return None;
                }
            }
        } else {
            plan
        };
        stats.max_steps = stats.max_steps.max(plan.num_steps());
        if plan.complete() {
            if let Some(solution) = complete(ctx, self.domain, self.problem, &plan) {
                return Some(solution);
            }
            stats.dead += 1;
            return None;
        }
        // The plan's binding solution, for its children to start from; with
        // `feasibility_at_pop` a plan without one is dead.
        let started = Instant::now();
        let witness = if self.feasibility_h >= 0.0 && node.h <= self.feasibility_h {
            if same_bindings && parent_witness.is_some() {
                parent_witness
            } else {
                match find_witness(ctx, &plan, parent_witness.as_ref(), self.feasibility_budget) {
                    Feasibility::Witness(w) => Some(w),
                    Feasibility::Unknown => None,
                    Feasibility::Infeasible => {
                        if self.feasibility_at_pop {
                            stats.dead += 1;
                            return None;
                        }
                        None
                    }
                }
            }
        } else {
            None
        };
        stats.phase[5] += started.elapsed();
        let started = Instant::now();
        let selected = super::flaws::select(ctx, &plan, &lane.lane.flaw_order, &lane.estimator);
        stats.phase[1] += started.elapsed();
        let started = Instant::now();
        let binding = choose_binding(ctx, &plan, &selected, self.bind_policy, lane.lane.degree_binding);
        stats.phase[2] += started.elapsed();
        if stats.expanded <= self.trace {
            self.trace_node(lane, &node, &plan, &selected, &binding);
            if self.dump.contains(&stats.expanded) {
                self.dump_plan(&plan);
                if let super::flaws::Flaw::Threat(t) = &selected {
                    let b = &plan.bindings;
                    let g = ctx.assignment(&plan, t.step(), t.assign);
                    let f = ctx.condition(&plan, t.link.consumer(), t.link.cond);
                    eprintln!(
                        "  threat: writer inv {:?} vs link inv {:?}; definite={}",
                        g.inv.iter().map(|x| b.resolve(*x, t.step())).collect::<Vec<_>>(),
                        f.inv.iter().map(|x| b.resolve(*x, t.link.consumer())).collect::<Vec<_>>(),
                        super::plan::definite(ctx, &plan, t)
                    );
                }
            }
        }
        let started = Instant::now();
        let (refined, children) = match binding {
            Some((class, objects)) => (Refined::Bind(class), super::plan::refine_bind(ctx, &plan, class, &objects)),
            None => match selected {
                super::flaws::Flaw::Threat(t) => (Refined::Threat(t), refine_threat(ctx, &plan, t, None)),
                super::flaws::Flaw::Open(o) => (Refined::Open(o), refine_open(ctx, &plan, o, None)),
                super::flaws::Flaw::Dead => (Refined::Bind(0), Vec::new()),
            },
        };
        stats.phase[3] += started.elapsed();
        let base = Rc::new(Expansion {
            parent: plan.clone(),
            flaw: refined,
            witness,
        });
        let ranked: Vec<((f32, f32, u32), super::plan::Choice, Plan)> = children
            .into_iter()
            .filter_map(|(choice, child)| {
                if self.dead_new_threats && super::plan::new_threat_dead(ctx, &child, &plan, 64) {
                    stats.generated += 1;
                    stats.dead += 1;
                    return None;
                }
                let same = matches!(
                    choice,
                    super::plan::Choice::Demote | super::plan::Choice::Promote | super::plan::Choice::Drop
                );
                let rank = self.evaluate(lane, &child, base.witness.as_ref(), same, stats);
                if stats.expanded <= self.trace {
                    eprintln!("  child {:?}: {}", choice, rank.map_or("dead".to_string(), |r| format!("f={} h={}", r.0, r.1)));
                }
                Some((rank?, choice, child))
            })
            .collect();
        // The child the queue would pop first among these may be popped next:
        // optionally keep it built, and only the rest as recipes.
        let first = ranked
            .iter()
            .enumerate()
            .min_by(|(_, (a, _, _)), (_, (b, _, _))| {
                a.0.total_cmp(&b.0).then(a.1.total_cmp(&b.1)).then(b.2.cmp(&a.2))
            })
            .map(|(i, _)| i);
        for (i, (rank, choice, child)) in ranked.into_iter().enumerate() {
            let entry = if self.defer && !(self.keep_best && Some(i) == first) {
                Entry::Recipe {
                    base: base.clone(),
                    choice,
                }
            } else {
                Entry::Built(Rc::new(child))
            };
            Self::enqueue(lane, rank, entry);
        }
        None
    }

    /// Prints a plan's steps with resolved arguments, its links and the
    /// steps' order (`POTOROO_LFDR_DUMP=N,M` with `POTOROO_TRACE`).
    fn dump_plan(&self, plan: &Plan) {
        let ctx = self.ctx;
        let name = |t: Term| match t {
            Term::Object(o) => self.problem.objects.object_name(Some(&self.domain.constants), o).to_string(),
            Term::Variable(v) => format!("?{}", v.0),
        };
        for s in 1..=plan.num_steps() {
            let schema = ctx.schema_of(plan, s);
            let args: Vec<String> = schema
                .parameters
                .iter()
                .map(|v| {
                    let t = Term::Variable(*v);
                    match plan.bindings.resolve(t, s) {
                        super::binds::Resolved::Object(o) => name(Term::Object(o)),
                        super::binds::Resolved::Class(k) => {
                            format!("c{}{{{}}}", k, plan.bindings.domain(k).len())
                        }
                    }
                })
                .collect();
            let after: Vec<usize> = (1..=plan.num_steps())
                .filter(|&p| p != s && !plan.orderings.possibly_before(s, StepTime::AtEnd, p, StepTime::AtStart))
                .collect();
            eprintln!("  step {s}: {}({}) after {:?}", schema.name, args.join(" "), after);
        }
        for link in chain::iter(&plan.links) {
            eprintln!("  link {} -> {} cond {}", link.producer(), link.consumer(), link.cond);
        }
    }

    fn trace_node(
        &self,
        lane: &Running,
        node: &Node,
        plan: &Plan,
        selected: &super::flaws::Flaw,
        binding: &Option<(super::binds::ClassId, Vec<Object>)>,
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
            (Some((class, objects)), _) => format!("bind class {} over {} objects", class, objects.len()),
            (None, super::flaws::Flaw::Open(o)) => {
                let name = if o.consumer() == super::plan::GOAL_ID {
                    "goal".to_string()
                } else {
                    ctx.schema_of(plan, o.consumer()).name.clone()
                };
                format!("open {} for {}@{}", describe(o.consumer(), ctx.condition(plan, o.consumer(), o.cond)), name, o.consumer())
            }
            (None, super::flaws::Flaw::Threat(t)) => format!(
                "threat step {} ({}) on {}",
                t.step(),
                ctx.schema_of(plan, t.step()).name,
                describe(t.link.consumer(), ctx.condition(plan, t.link.consumer(), t.link.cond))
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
    // Joint binding feasibility: on by default for every plan expanded;
    // `POTOROO_LFDR_FEAS=off` disables it, `=H[:BUDGET]` limits it to plans
    // with `h <= H`.
    let feas: (f32, usize) = match std::env::var("POTOROO_LFDR_FEAS").as_deref() {
        Ok("off") => (-1.0, 0),
        Ok(v) => {
            let (h, budget) = v.split_once(':').unwrap_or((v, "1000"));
            (h.parse().unwrap_or(f32::INFINITY), budget.parse().unwrap_or(1000))
        }
        Err(_) => (f32::INFINITY, 1000),
    };
    let search = Search {
        ctx: &ctx,
        domain,
        problem,
        weight: config.weight,
        bind_policy: BindPolicy::from_env(),
        mac_budget: std::env::var("POTOROO_LFDR_MAC").ok().and_then(|v| v.parse().ok()).unwrap_or(0),
        trace: std::env::var("POTOROO_TRACE").ok().and_then(|v| v.parse().ok()).unwrap_or(0),
        defer: std::env::var("POTOROO_LFDR_DEFER").map_or(true, |v| v != "0"),
        keep_best: std::env::var("POTOROO_LFDR_DEFER").is_ok_and(|v| v == "best"),
        progress: std::env::var_os("POTOROO_LFDR_PROGRESS").is_some(),
        drop_stale: std::env::var("POTOROO_LFDR_STALE").map_or(true, |v| v != "0"),
        dead_new_threats: std::env::var("POTOROO_LFDR_NEWDEAD").map_or(true, |v| v != "0"),
        force_rounds: std::env::var("POTOROO_LFDR_FORCE").ok().and_then(|v| v.parse().ok()).unwrap_or(4),
        feasibility_h: feas.0,
        feasibility_budget: feas.1,
        feasibility_at_pop: std::env::var("POTOROO_LFDR_FEASPOP").map_or(true, |v| v != "0"),
        dump: std::env::var("POTOROO_LFDR_DUMP")
            .map(|v| v.split(',').filter_map(|n| n.parse().ok()).collect())
            .unwrap_or_default(),
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
                best_f: std::cell::Cell::new(f32::INFINITY),
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

/// Rebuilds the child that `choice` names from `parent`.
fn rebuild(ctx: &Ctx, parent: &Plan, flaw: Refined, choice: super::plan::Choice) -> Option<Plan> {
    let mut children = match (flaw, choice) {
        (Refined::Open(o), _) => refine_open(ctx, parent, o, Some(choice)),
        (Refined::Threat(t), _) => refine_threat(ctx, parent, t, Some(choice)),
        (Refined::Bind(class), super::plan::Choice::Bind(o)) => super::plan::refine_bind(ctx, parent, class, &[o]),
        (Refined::Bind(_), _) => Vec::new(),
    };
    debug_assert!(children.len() <= 1);
    children.pop().map(|(_, plan)| plan)
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
) -> Option<(super::binds::ClassId, Vec<Object>)> {
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
) -> Option<(super::binds::ClassId, Vec<Object>)> {
    use super::flaws::Flaw;
    if matches!(selected, Flaw::Dead) || plan.num_threats == 0 {
        return None;
    }
    if let Flaw::Threat(t) = selected {
        if super::plan::definite(ctx, plan, t) {
            return None;
        }
    }
    let mut touching: std::collections::HashMap<super::binds::ClassId, Vec<super::plan::Threat>> =
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
    let mut best: Option<(f32, usize, super::binds::ClassId, Vec<Object>)> = None;
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
    let mut bindings = plan.bindings.clone();
    let mut budget = usize::MAX;
    if ground_within(ctx, plan, &mut bindings, &mut budget) != Some(true) {
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

/// Depth-first grounding of the unbound classes, smallest domain first,
/// with arc consistency at each assignment (MAC). `None` when the assignment
/// budget runs out before an answer.
fn ground_within(ctx: &Ctx, plan: &Plan, bindings: &mut super::binds::LBindings, budget: &mut usize) -> Option<bool> {
    let Some(class) = bindings.unbound_classes().min_by_key(|&c| (bindings.domain(c).len(), c)) else {
        return Some(true);
    };
    let objects: Vec<Object> = bindings.domain(class).iter().collect();
    for o in objects {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        let Some(next) = bindings.bind(class, o) else {
            continue;
        };
        let mut probe = plan.clone();
        probe.bindings = next;
        let Some(mut propagated) = super::plan::propagate_statics(ctx, &probe) else {
            continue;
        };
        match ground_within(ctx, plan, &mut propagated, budget) {
            Some(true) => {
                *bindings = propagated;
                return Some(true);
            }
            None => return None,
            Some(false) => {}
        }
    }
    Some(false)
}

/// A solution of the plan's binding constraints within `budget` assignments,
/// trying `hint` (a solution for the parent) first: its values are bound at
/// once and checked by one propagation, and only the classes it does not
/// settle are searched.
pub fn find_witness(ctx: &Ctx, plan: &Plan, hint: Option<&Witness>, budget: usize) -> Feasibility {
    let extract = |b: &super::binds::LBindings| -> Feasibility {
        let mut w = Witness::default();
        for c in plan.bindings.unbound_classes() {
            w.set(c, b.value(c));
        }
        Feasibility::Witness(w)
    };
    // The parent's solution, repaired where this plan departs from it; then
    // a fresh search by table lookups; then search with propagation, which
    // can prove infeasibility within the budget.
    if let Some(hint) = hint {
        if let Some(w) = super::plan::extend_witness(ctx, plan, hint, 256) {
            return Feasibility::Witness(w);
        }
    }
    if let Some(w) = super::plan::extend_witness(ctx, plan, &Witness::default(), 2048) {
        return Feasibility::Witness(w);
    }
    let mut bindings = plan.bindings.clone();
    let mut budget = budget;
    match ground_within(ctx, plan, &mut bindings, &mut budget) {
        Some(true) => extract(&bindings),
        Some(false) => Feasibility::Infeasible,
        None => Feasibility::Unknown,
    }
}

/// Whether the plan's binding constraints have a solution, searched within
/// `budget` assignments; an exhausted budget counts as feasible.
pub fn bindings_feasible(ctx: &Ctx, plan: &Plan, budget: usize) -> bool {
    let mut bindings = plan.bindings.clone();
    let mut budget = budget;
    ground_within(ctx, plan, &mut bindings, &mut budget) != Some(false)
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

#[cfg(test)]
mod tests {
    #[test]
    fn queue_entries_stay_small() {
        // A queued child is a recipe: ranks, id, shared expansion, choice.
        assert!(std::mem::size_of::<super::Node>() <= 40, "{}", std::mem::size_of::<super::Node>());
    }
}
