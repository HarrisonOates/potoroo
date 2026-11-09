//! Potoroo command-line entry point. Outputs per-problem: `;name`, the scheduled
//! step lines or a `no plan` message, and a `Time:` line. The classical subset
//! supports A*/IDA*/hill-climbing (HC behaves like A* in this version), the
//! cheap and additive (ADD/ADDR) heuristics, and the full flaw-selection DSL
//! with round-robin over multiple `-f`/`-l`. Truly deferred features
//! (durative/numeric) report a clear error.

use std::collections::BTreeMap;
use std::io::Read;
use std::process::ExitCode;
use std::time::{Duration, Instant};

use potoroo::domain::Domain;
use potoroo::heuristics::{FlawSelectionOrder, Heuristic};
use potoroo::params::{ActionCost, Parameters, SearchAlgorithm};
use potoroo::parser::{bind_action_costs, lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::problem::Problem;
use potoroo::search::{
    format_steps, plan_with_progress, plan_with_stats, Outcome, SearchContext, SearchProgress,
};

const PACKAGE: &str = "potoroo";
const VERSION: &str = env!("CARGO_PKG_VERSION");

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(e) => {
            eprintln!("{PACKAGE}: {e}");
            ExitCode::FAILURE
        }
    }
}

/// Parsed command-line configuration.
struct Cli {
    params: Parameters,
    /// Selects ground POCL over Fast Downward's multi-valued SAS+ task. Search
    /// algorithms, heuristics, flaw orders, weights, and limits still come from
    /// `params`.
    fdr_pocl: bool,
    lifted_fdr: bool,
    /// `--lane=ORDER[@HEUR]` for `--lifted-fdr`, repeatable.
    lanes: Vec<String>,
    verbosity: u32,
    files: Vec<String>,
    /// Effective flaw-order names, retained for readable telemetry.
    flaw_order_names: Vec<String>,
    /// Effective `-h` value (default `ADD/LIFO`). Used to label telemetry and the
    /// optional `POTOROO_STATS_JSON` output.
    heuristic_name: String,
    /// Raw `-s` value as given on the command line (default `A`). Included in the
    /// `POTOROO_STATS_JSON` output so different algorithms are distinguishable.
    algorithm_name: String,
    /// The `--stage` restart portfolio, in the order it was given. Empty for a
    /// plain run, which is then a portfolio of one implicit stage; see
    /// [`Cli::portfolio`].
    stages: Vec<Stage>,
    /// Wall-clock budget for one problem, from `--time-limit` or `-T`.
    time_limit: Option<Duration>,
    /// Resident-set ceiling at which a stage gives way to the next
    /// (`--stage-mem-mb`).
    stage_mem_mb: Option<usize>,
}

/// One stage of the `--stage` restart portfolio: `HEURISTIC[@SEARCH][=SECS]`.
///
/// A stage is a whole search, restarted from the initial plan with a different
/// heuristic. It is not a pruning device: a stage that ends leaves its part of
/// the search space unexplored rather than excluded, which is why the outcome
/// it reports is the limit reached and why an exhausted search space ends the
/// portfolio outright.
#[derive(Clone)]
struct Stage {
    /// The spec exactly as written, for the STATS label and the `-v` lines.
    spec: String,
    heuristic: Heuristic,
    /// `None` inherits the command line's `-s`.
    search_algorithm: Option<SearchAlgorithm>,
    /// How long this stage may run for. `None` runs to `--time-limit`, or
    /// without a bound at all when there is none, and is therefore only
    /// allowed on the last stage — anything after it would never start.
    share: Option<Duration>,
}

impl Cli {
    /// The stages to run for one problem. Without `--stage` this is a single
    /// stage carrying the command line's own heuristic and search algorithm,
    /// so a plain run goes through exactly the same loop as a portfolio and
    /// the two cannot drift apart.
    fn portfolio(&self) -> Vec<Stage> {
        if self.stages.is_empty() {
            vec![Stage {
                spec: format!("{}@{}", self.heuristic_name, self.algorithm_name),
                heuristic: self.params.heuristic.clone(),
                search_algorithm: Some(self.params.search_algorithm),
                share: None,
            }]
        } else {
            self.stages.clone()
        }
    }

    /// The STATS `heuristic` field: `ALG(HEUR)` for a plain run, so different
    /// algorithms on the same heuristic stay distinct columns, and
    /// `portfolio(SPEC;SPEC)` for a `--stage` run, so a portfolio row can
    /// never be mistaken for one of its stages run alone.
    fn stats_label(&self) -> String {
        if self.stages.is_empty() {
            format!("{}({})", self.algorithm_name, self.heuristic_name)
        } else {
            let specs: Vec<&str> = self
                .stages
                .iter()
                .map(|stage| stage.spec.as_str())
                .collect();
            format!("portfolio({})", specs.join(";"))
        }
    }
}

/// Search statistics summed over the stages of one problem: counters add up
/// and peaks take a maximum, so a STATS row says what the whole problem cost
/// rather than what its last stage cost. Also the single shape the STATS line
/// is written from, since the two representations keep their own.
#[derive(Clone, Copy, Debug, Default)]
struct RunStats {
    nodes_generated: usize,
    nodes_visited: usize,
    h_evals: usize,
    h_eval_ms: u128,
    pruned: usize,
    supporter_forced: usize,
    // Preprocessing work/time/removals sum across stages; proof counts are
    // maxima because stages can rediscover the same pairs. Status is the last
    // enabled stage's, with run/completion counts showing partial completion.
    h2: potoroo::h2::Stats,
    h2_runs: usize,
    h2_completed: usize,
    max_steps: usize,
    max_open_conditions: usize,
    max_threats: usize,
    max_disjunctions: usize,
    max_queued: usize,
    dropped: usize,
}

impl RunStats {
    /// Folds one stage's statistics into the running total.
    fn add(&mut self, stage: &RunStats) {
        self.nodes_generated += stage.nodes_generated;
        self.nodes_visited += stage.nodes_visited;
        self.h_evals += stage.h_evals;
        self.h_eval_ms += stage.h_eval_ms;
        self.pruned += stage.pruned;
        self.supporter_forced += stage.supporter_forced;
        self.h2_runs += stage.h2_runs;
        self.h2_completed += stage.h2_completed;
        if stage.h2_runs > 0 {
            self.h2.status = stage.h2.status;
        }
        self.h2.work += stage.h2.work;
        self.h2.elapsed_ms += stage.h2.elapsed_ms;
        self.h2.mutex_pairs = self.h2.mutex_pairs.max(stage.h2.mutex_pairs);
        self.h2.new_mutex_pairs = self.h2.new_mutex_pairs.max(stage.h2.new_mutex_pairs);
        self.h2.projected_variables = self
            .h2
            .projected_variables
            .max(stage.h2.projected_variables);
        self.h2.unreachable_facts = self.h2.unreachable_facts.max(stage.h2.unreachable_facts);
        self.h2.supporters_removed += stage.h2.supporters_removed;
        self.max_steps = self.max_steps.max(stage.max_steps);
        self.max_open_conditions = self.max_open_conditions.max(stage.max_open_conditions);
        self.max_threats = self.max_threats.max(stage.max_threats);
        self.max_disjunctions = self.max_disjunctions.max(stage.max_disjunctions);
        self.max_queued = self.max_queued.max(stage.max_queued);
        self.dropped += stage.dropped;
    }
}

impl From<potoroo::search::SearchStats> for RunStats {
    fn from(stats: potoroo::search::SearchStats) -> Self {
        RunStats {
            nodes_generated: stats.nodes_generated,
            nodes_visited: stats.nodes_visited,
            h_evals: stats.h_evals,
            h_eval_ms: stats.h_eval_ms,
            pruned: stats.pruned,
            supporter_forced: 0,
            h2: Default::default(),
            h2_runs: 0,
            h2_completed: 0,
            max_steps: stats.max_steps,
            max_open_conditions: stats.max_open_conditions,
            max_threats: stats.max_threats,
            // Ordering disjunctions only exist on finite-domain plans.
            max_disjunctions: 0,
            max_queued: stats.max_queued,
            dropped: stats.dropped,
        }
    }
}

impl From<potoroo::fdr_pocl::SearchStats> for RunStats {
    fn from(stats: potoroo::fdr_pocl::SearchStats) -> Self {
        RunStats {
            nodes_generated: stats.nodes_generated,
            nodes_visited: stats.nodes_visited,
            h_evals: stats.h_evals,
            h_eval_ms: stats.h_eval_ms,
            pruned: stats.pruned,
            supporter_forced: stats.supporter_forced,
            h2: stats.h2,
            h2_runs: usize::from(stats.h2.status != potoroo::h2::Status::Disabled),
            h2_completed: usize::from(stats.h2.status == potoroo::h2::Status::Complete),
            max_steps: stats.max_steps,
            max_open_conditions: stats.max_open_conditions,
            max_threats: stats.max_threats,
            max_disjunctions: stats.max_disjunctions,
            max_queued: stats.max_queued,
            dropped: stats.dropped,
        }
    }
}

/// What one search returned, with the two representations' outcomes folded
/// into one shape. The plan is already rendered: a stage's search context is
/// dropped before the next stage starts, so it cannot be formatted later.
enum RunOutcome {
    Solved {
        plan: String,
        steps: usize,
        cost: usize,
    },
    /// The node limit (`-l`) was reached.
    LimitReached,
    /// The wall-clock deadline was reached.
    TimedOut,
    /// The resident-set ceiling (`--stage-mem-mb`) was reached.
    MemoryStopped,
    /// The search space was exhausted without finding a plan.
    NoSolution,
}

impl RunOutcome {
    /// Reads a limit-reached search's own account of why it stopped. The node
    /// limit is the case where no budget fired.
    fn stopped_short(reason: Option<potoroo::memory::StopReason>) -> Self {
        match reason {
            Some(potoroo::memory::StopReason::Deadline) => RunOutcome::TimedOut,
            Some(potoroo::memory::StopReason::Memory) => RunOutcome::MemoryStopped,
            None => RunOutcome::LimitReached,
        }
    }

    /// Whether this ends the whole portfolio rather than handing over to the
    /// next stage. A plan obviously does; so does an exhausted search space,
    /// which is exact and says the problem is unsolvable however it is
    /// searched. Running out of time or of nodes says nothing of the kind.
    fn ends_the_portfolio(&self) -> bool {
        matches!(self, RunOutcome::Solved { .. } | RunOutcome::NoSolution)
    }

    /// The word the `-v` summary and the STATS `outcome` field are derived from.
    fn status(&self) -> &'static str {
        match self {
            RunOutcome::Solved { .. } => "solved",
            RunOutcome::LimitReached => "limit reached",
            RunOutcome::TimedOut => "time limit reached",
            RunOutcome::MemoryStopped => "memory bound reached",
            RunOutcome::NoSolution => "no solution",
        }
    }
}

fn run() -> Result<ExitCode, String> {
    let cli = match parse_args(std::env::args().skip(1))? {
        // `-H`/`-V` already produced their output; exit successfully.
        None => return Ok(ExitCode::SUCCESS),
        Some(cli) => cli,
    };

    // Read all input (files, or stdin when none given) into domains/problems.
    let mut domains: BTreeMap<String, Domain> = BTreeMap::new();
    // Problems are solved in name order, matching the C++ `std::map` iteration.
    let mut problems: BTreeMap<String, Problem> = BTreeMap::new();

    // Each buffer may hold several `(define ...)` forms — the documented stdin
    // workflow pipes a domain and a problem together — and the parser reads only
    // the first form in a string, so split before parsing.
    let sources: Vec<String> = if cli.files.is_empty() {
        let mut buf = String::new();
        std::io::stdin()
            .read_to_string(&mut buf)
            .map_err(|e| format!("error reading stdin: {e}"))?;
        potoroo::parser::split_units(&buf)
    } else {
        let mut v = Vec::new();
        for f in &cli.files {
            let source =
                std::fs::read_to_string(f).map_err(|e| format!("error reading {f}: {e}"))?;
            v.extend(potoroo::parser::split_units(&source));
        }
        v
    };

    // First pass: lower all domains so problems can reference them.
    let mut problem_units: Vec<pddl::Problem> = Vec::new();
    for src in &sources {
        match read_pddl(src).map_err(|e| e.to_string())? {
            ParsedUnit::Domain(d) => {
                let dom = lower_domain(&d).map_err(|e| e.to_string())?;
                domains.insert(dom.name.clone(), dom);
            }
            ParsedUnit::Problem(p) => problem_units.push(p),
        }
    }
    for p in &problem_units {
        let dom_name = p.domain().as_ref();
        let domain = domains
            .get(dom_name)
            .ok_or_else(|| format!("undeclared domain `{dom_name}`"))?;
        let prob = lower_problem(p, domain).map_err(|e| e.to_string())?;
        problems.insert(prob.name.clone(), prob);
    }

    // Solve each problem in name order.
    for problem in problems.values() {
        // Cost functions read the problem's `:init`, so resolve per problem.
        bind_action_costs(
            domains
                .get_mut(&problem.domain_name)
                .expect("domain was looked up during lowering"),
            problem,
        )
        .map_err(|e| e.to_string())?;
        let domain = domains
            .get(&problem.domain_name)
            .expect("domain was looked up during lowering");
        println!(";{}", problem.name);
        if cli.verbosity > 0 {
            print_search_configuration(&cli);
        }
        let timer = Instant::now();
        // Include translation and grounding in the wall-clock deadline.
        let deadline = cli.time_limit.map(|limit| timer + limit);
        let portfolio = cli.portfolio();
        let (outcome, stats) = if cli.lifted_fdr {
            run_lifted_fdr(&cli, domain, problem, deadline)?
        } else if cli.fdr_pocl {
            run_fdr_portfolio(&cli, domain, problem, &portfolio, deadline)?
        } else {
            run_lifted_portfolio(&cli, domain, problem, &portfolio, deadline)?
        };

        let (solved, plan_len, plan_cost) = match &outcome {
            RunOutcome::Solved { plan, steps, cost } => {
                if cli.verbosity > 0 {
                    eprintln!("Plan: {steps} steps | cost {cost}");
                }
                println!("{plan}");
                (true, *steps, *cost)
            }
            RunOutcome::LimitReached => {
                println!("no plan");
                println!(";Search limit reached.");
                (false, 0, 0)
            }
            RunOutcome::TimedOut => {
                println!("no plan");
                println!(";Time limit reached.");
                (false, 0, 0)
            }
            RunOutcome::MemoryStopped => {
                println!("no plan");
                println!(";Memory bound reached.");
                (false, 0, 0)
            }
            RunOutcome::NoSolution => {
                println!("no plan");
                println!(";Problem has no solution.");
                (false, 0, 0)
            }
        };
        let status = outcome.status();
        let ms = timer.elapsed().as_millis();
        println!("Time: {ms}");
        if cli.verbosity > 0 {
            print_search_summary(status, ms, &stats);
        }

        // Machine-readable benchmark line (stderr, opt-in). Kept off stdout so
        // the differential tests still diff stdout byte-for-byte.
        if std::env::var_os("POTOROO_STATS_JSON").is_some() {
            if cli.fdr_pocl {
                let label = format!("FDR:{}", cli.stats_label());
                eprintln!(
                    "STATS {{\"problem\":\"{}\",\"heuristic\":\"{}\",\"ground\":true,\
                     \"solved\":{},\"plan_len\":{},\"plan_cost\":{},\"nodes_generated\":{},\"nodes_visited\":{},\
                     \"wall_ms\":{},\"h_evals\":{},\"h_eval_ms\":{},\"pruned\":{},\
                     \"max_steps\":{},\"max_open_conditions\":{},\"max_threats\":{},\
                     \"supporter_forced\":{},\"max_disjunctions\":{},\"max_queued\":{},\"dropped\":{},\
                     \"h2_status\":\"{}\",\"h2_runs\":{},\"h2_completed\":{},\"h2_work\":{},\"h2_ms\":{},\
                     \"h2_max_mutex_pairs\":{},\"h2_max_new_mutex_pairs\":{},\"h2_max_projected_variables\":{},\"h2_max_unreachable_facts\":{},\"h2_supporters_removed\":{},\
                     \"outcome\":\"{}\",\"peak_rss_kb\":{}}}",
                    json_escape(&problem.name),
                    json_escape(&label),
                    solved,
                    plan_len,
                    plan_cost,
                    stats.nodes_generated,
                    stats.nodes_visited,
                    ms,
                    stats.h_evals,
                    stats.h_eval_ms,
                    stats.pruned,
                    stats.max_steps,
                    stats.max_open_conditions,
                    stats.max_threats,
                    stats.supporter_forced,
                    stats.max_disjunctions,
                    stats.max_queued,
                    stats.dropped,
                    stats.h2.status.as_str(),
                    stats.h2_runs,
                    stats.h2_completed,
                    stats.h2.work,
                    stats.h2.elapsed_ms,
                    stats.h2.mutex_pairs,
                    stats.h2.new_mutex_pairs,
                    stats.h2.projected_variables,
                    stats.h2.unreachable_facts,
                    stats.h2.supporters_removed,
                    outcome_label(status),
                    peak_rss_kb(),
                );
            } else {
                // Label: "ALG(HEUR)" so different algorithms on the same
                // heuristic appear as distinct columns in the benchmark table.
                let label = cli.stats_label();
                eprintln!(
                    "STATS {{\"problem\":\"{}\",\"heuristic\":\"{}\",\"ground\":{},\"solved\":{},\
                     \"plan_len\":{},\"plan_cost\":{},\"nodes_generated\":{},\"nodes_visited\":{},\"wall_ms\":{},\
                     \"h_evals\":{},\"h_eval_ms\":{},\"pruned\":{},\"max_steps\":{},\
                     \"max_open_conditions\":{},\"max_threats\":{},\"max_queued\":{},\
                     \"dropped\":{},\"outcome\":\"{}\",\"peak_rss_kb\":{}}}",
                    json_escape(&problem.name),
                    json_escape(&label),
                    cli.params.ground_actions,
                    solved,
                    plan_len,
                    plan_cost,
                    stats.nodes_generated,
                    stats.nodes_visited,
                    ms,
                    stats.h_evals,
                    stats.h_eval_ms,
                    stats.pruned,
                    stats.max_steps,
                    stats.max_open_conditions,
                    stats.max_threats,
                    stats.max_queued,
                    stats.dropped,
                    outcome_label(status),
                    peak_rss_kb(),
                );
            }
        }
    }

    Ok(ExitCode::SUCCESS)
}

/// One stage's `Parameters`: the command line's, with the heuristic, the search
/// algorithm and the deadline replaced. Everything else — flaw orders, node
/// limits, weight, pruning rules, action cost — is shared, so the stages of a
/// portfolio differ only in what a portfolio is there to vary.
///
/// The deadline is the earlier of this stage's own share, counted from now, and
/// the problem's global `--time-limit`: a stage never outlives the problem's
/// budget, and a share that is left off simply runs to that budget.
fn stage_parameters(cli: &Cli, stage: &Stage, deadline: Option<Instant>) -> Parameters {
    let mut params = cli.params.clone();
    params.heuristic = stage.heuristic.clone();
    if let Some(algorithm) = stage.search_algorithm {
        params.search_algorithm = algorithm;
    }
    params.deadline = match (stage.share, deadline) {
        (Some(share), Some(global)) => Some((Instant::now() + share).min(global)),
        (Some(share), None) => Some(Instant::now() + share),
        (None, global) => global,
    };
    params.memory_stop_mb = cli.stage_mem_mb;
    params
}

/// Runs the stages in order and returns the last one's outcome together with
/// the statistics summed over all of them. `run_stage` performs one search; the
/// sequencing policy around it lives here, once, for every representation.
///
/// That policy: a stage that solves the problem or exhausts the search space
/// ends the portfolio, and a stage that runs out of time, memory or nodes hands
/// over to the next. Between two stages — and only between them, so a plain run
/// pays nothing — the pages the finished stage freed go back to the kernel,
/// because the allocator holds on to them otherwise and the next stage would
/// read its predecessor's peak as its own resident set.
fn run_portfolio(
    cli: &Cli,
    portfolio: &[Stage],
    deadline: Option<Instant>,
    mut run_stage: impl FnMut(&Stage, &Parameters) -> Result<(RunOutcome, RunStats), String>,
) -> Result<(RunOutcome, RunStats), String> {
    let mut total = RunStats::default();
    let mut last = RunOutcome::NoSolution;
    for (index, stage) in portfolio.iter().enumerate() {
        let params = stage_parameters(cli, stage, deadline);
        announce_stage(cli, index, portfolio.len(), stage);
        let (outcome, stats) = run_stage(stage, &params)?;
        total.add(&stats);
        report_stage(cli, index, portfolio.len(), &outcome, stats.nodes_generated);
        last = outcome;
        if last.ends_the_portfolio() {
            break;
        }
        if index + 1 < portfolio.len() {
            potoroo::memory::release_free_memory();
        }
    }
    Ok((last, total))
}

/// Runs the portfolio over the lifted or `-g` representation.
///
/// A fresh [`SearchContext`] per stage. Nothing in a context depends on *which*
/// heuristic asked for it — the planning graph, the compiled relaxation, the
/// Sample-FF model and the landmark sets are all functions of the domain and
/// the problem alone — but they are exactly the memory a stage should hand back
/// before the next one starts, which is the point of `--stage-mem-mb`. The
/// price is re-grounding under `-g`, one Fast Downward call a stage.
fn run_lifted_portfolio(
    cli: &Cli,
    domain: &Domain,
    problem: &Problem,
    portfolio: &[Stage],
    deadline: Option<Instant>,
) -> Result<(RunOutcome, RunStats), String> {
    run_portfolio(cli, portfolio, deadline, |_stage, params| {
        // Scoped so the queues and the context are gone before the stage ends,
        // which is what the next stage's memory bound is measured against.
        let ctx = SearchContext::new(domain, problem, params);
        let (outcome, stats) = if cli.verbosity > 0 {
            let mut printer = ProgressPrinter::new(cli.verbosity);
            let mut report = |progress| printer.report(progress);
            plan_with_progress(&ctx, &mut report)
        } else {
            plan_with_stats(&ctx)
        };
        let outcome = match outcome {
            Outcome::Solved(plan) => RunOutcome::Solved {
                plan: format_steps(&ctx, &plan),
                steps: plan.num_steps(),
                cost: plan.cost(),
            },
            Outcome::LimitReached => RunOutcome::stopped_short(stats.stopped),
            Outcome::NoSolution => RunOutcome::NoSolution,
        };
        Ok((outcome, RunStats::from(stats)))
    })
}

/// Runs lifted finite-domain POCL search (`--lifted-fdr`).
fn run_lifted_fdr(
    cli: &Cli,
    domain: &Domain,
    problem: &Problem,
    deadline: Option<Instant>,
) -> Result<(RunOutcome, RunStats), String> {
    use potoroo::lifted_fdr::{Config, Lane, Outcome};
    let lanes = cli
        .lanes
        .iter()
        .map(|spec| Lane::parse(spec))
        .collect::<Result<Vec<_>, _>>()?;
    let config = Config {
        lanes,
        weight: cli.params.weight,
        node_limit: cli.params.search_limits.first().copied().unwrap_or(usize::MAX),
        time_limit: deadline.map(|d| d.saturating_duration_since(Instant::now())),
    };
    let start = Instant::now();
    let (outcome, stats) = potoroo::lifted_fdr::solve(domain, problem, &config).map_err(|e| e.to_string())?;
    let run_stats = RunStats {
        nodes_generated: stats.generated,
        nodes_visited: stats.expanded,
        pruned: stats.dead,
        max_steps: stats.max_steps,
        ..RunStats::default()
    };
    if cli.verbosity > 0 {
        eprintln!(
            "Search finished: lifted FDR in {:.2}s | visited {} | generated {} | pruned {} | largest plan steps={}",
            start.elapsed().as_secs_f64(),
            stats.expanded,
            stats.generated,
            stats.dead,
            stats.max_steps
        );
        if let Some(lane) = &stats.solved_by {
            eprintln!("Lifted FDR lane: {lane}");
        }
        if stats.frontier_keys + stats.frontier_no_key.iter().sum::<usize>() > 0 {
            eprintln!(
                "Lifted FDR frontier: keys {} | dominated {} | no key (threats, goal open, nothing settled, shared class, distinct) {:?}",
                stats.frontier_keys, stats.frontier_dominated, stats.frontier_no_key
            );
        }
        if stats.non_minimal > 0 {
            eprintln!("Lifted FDR non-minimal plans discarded: {}", stats.non_minimal);
        }
        let [h, select, bind, refine, force, feasible] = stats.phase;
        eprintln!(
            "Lifted FDR time: heuristic {:.2}s | flaw selection {:.2}s | binding choice {:.2}s | refinement {:.2}s | forced threats {:.2}s | feasibility {:.2}s",
            h.as_secs_f64(),
            select.as_secs_f64(),
            bind.as_secs_f64(),
            refine.as_secs_f64(),
            force.as_secs_f64(),
            feasible.as_secs_f64()
        );
    }
    let outcome = match outcome {
        Outcome::Solved(solution) => RunOutcome::Solved {
            plan: solution.format(domain, problem),
            steps: solution.actions.len(),
            cost: solution.cost,
        },
        Outcome::LimitReached => RunOutcome::LimitReached,
        Outcome::NoSolution => RunOutcome::NoSolution,
    };
    Ok((outcome, run_stats))
}

/// Runs the portfolio over the finite-domain representation.
///
/// The SAS+ translation reads only the domain and the problem, so it is done
/// once for the whole portfolio: it costs a Fast Downward invocation, which a
/// restart has no reason to pay again. Each stage still builds its own planner,
/// so the heuristic's tables are freed at the stage boundary.
fn run_fdr_portfolio(
    cli: &Cli,
    domain: &Domain,
    problem: &Problem,
    portfolio: &[Stage],
    deadline: Option<Instant>,
) -> Result<(RunOutcome, RunStats), String> {
    let ctx = SearchContext::new(domain, problem, &cli.params);
    let task = potoroo::fdr_pocl::translate(&ctx).map_err(|e| e.to_string())?;
    if cli.verbosity > 0 {
        eprintln!(
            "SAS+ task: {} variables ({} multi-valued), {} facts, {} operators",
            task.variables.len(),
            task.multi_valued_variables(),
            task.num_facts(),
            task.operators.len()
        );
    }
    let symmetries = cli.params.prune.symmetry.then(|| ctx.object_symmetries());
    if let (Some(symmetries), true) = (&symmetries, cli.verbosity > 0) {
        eprintln!("Symmetry: {}", symmetries.summary());
    }
    // The lifted context has served its purpose; the SAS+ task and the symmetry
    // table do not borrow from it, and a portfolio has no use for its memory.
    drop(ctx);

    // Whether the task can be searched under each stage's parameters is settled
    // before any of them runs. The command line has already rejected the
    // heuristics this representation can never evaluate; what is left is
    // task-dependent, and a portfolio that discovered it after its first stage
    // had spent its share of the clock would abort with no plan, no `Time:` and
    // no statistics. One planner answers for every stage, so this costs a
    // single extra construction, and only where there is more than one stage.
    if portfolio.len() > 1 {
        // The deadlines in these copies are not the ones the stages will run
        // under — they are counted from now rather than from each stage's start
        // — but validation does not look at them.
        let staged: Vec<Parameters> = portfolio
            .iter()
            .map(|stage| stage_parameters(cli, stage, deadline))
            .collect();
        potoroo::fdr_pocl::validate_all(&task, &staged).map_err(|e| e.to_string())?;
    }

    run_portfolio(cli, portfolio, deadline, |_stage, params| {
        let search_result = if cli.verbosity > 0 {
            let mut printer = ProgressPrinter::new(cli.verbosity);
            let mut report = |progress| printer.report(progress);
            potoroo::fdr_pocl::solve_with_context(
                &task,
                params,
                symmetries.as_deref(),
                Some(&mut report),
            )
        } else {
            potoroo::fdr_pocl::solve_with_context(&task, params, symmetries.as_deref(), None)
        };
        let (outcome, stats) = search_result.map_err(|e| e.to_string())?;
        let outcome = match outcome {
            potoroo::fdr_pocl::Outcome::Solved(solution) => RunOutcome::Solved {
                plan: solution.format(&task),
                steps: solution.operators.len(),
                cost: solution.plan.cost(),
            },
            potoroo::fdr_pocl::Outcome::LimitReached => RunOutcome::stopped_short(stats.stopped),
            potoroo::fdr_pocl::Outcome::NoSolution => RunOutcome::NoSolution,
        };
        Ok((outcome, RunStats::from(stats)))
    })
}

/// The `-v` line at the start of a stage. Silent for a plain run, whose single
/// implicit stage is the whole search: saying so would only be noise.
fn announce_stage(cli: &Cli, index: usize, stages: usize, stage: &Stage) {
    if cli.verbosity > 0 && !cli.stages.is_empty() {
        eprintln!("Stage {}/{} started: {}", index + 1, stages, stage.spec);
    }
}

/// The `-v` line at the end of a stage, saying why it stopped and how much of
/// the search space it had covered when it did.
fn report_stage(cli: &Cli, index: usize, stages: usize, outcome: &RunOutcome, generated: usize) {
    if cli.verbosity > 0 && !cli.stages.is_empty() {
        eprintln!(
            "Stage {}/{} finished: {} | generated {}",
            index + 1,
            stages,
            outcome.status(),
            generated,
        );
    }
}

/// Throttles the per-expansion callback into compact, line-oriented telemetry.
/// Level 1 reports at most once a second, level 2 four times a second, and level
/// 3 reports every expanded node for detailed debugging. The first expansion is
/// always shown so short searches still explain what happened.
struct ProgressPrinter {
    interval: Duration,
    last_report: Option<Duration>,
}

impl ProgressPrinter {
    fn new(verbosity: u32) -> Self {
        let interval = match verbosity {
            0 | 1 => Duration::from_secs(1),
            2 => Duration::from_millis(250),
            _ => Duration::ZERO,
        };
        Self {
            interval,
            last_report: None,
        }
    }

    fn report(&mut self, progress: SearchProgress) {
        if self
            .last_report
            .is_some_and(|last| progress.elapsed.saturating_sub(last) < self.interval)
        {
            return;
        }
        self.last_report = Some(progress.elapsed);
        eprintln!(
            "Search [{:>7.2}s] visited {} | generated {} | queued {} | h {} evals / {} ms | pruned {} | dropped {} | rss {} MB | current steps={} open={} threats={} order={}",
            progress.elapsed.as_secs_f64(),
            progress.nodes_visited,
            progress.nodes_generated,
            progress.queued,
            progress.h_evals,
            progress.h_eval_ms,
            progress.pruned,
            progress.dropped,
            progress.resident_kb / 1024,
            progress.current_steps,
            progress.current_open_conditions,
            progress.current_threats,
            progress.flaw_order + 1,
        );
    }
}

fn print_search_configuration(cli: &Cli) {
    let representation = if cli.fdr_pocl {
        "finite-domain POCL"
    } else if cli.params.ground_actions {
        "ground literal POCL"
    } else {
        "lifted POCL"
    };
    let limits = cli
        .params
        .search_limits
        .iter()
        .map(|&limit| {
            if limit == usize::MAX {
                "unlimited".to_string()
            } else {
                limit.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join(",");
    let limit_label = if cli.params.flaw_orders.len() == 1 {
        "node limit"
    } else {
        "node limits"
    };
    eprintln!(
        "Search: {} | {}({}) | flaws {} | cost {} | weight {} | {} {}",
        representation,
        cli.algorithm_name,
        cli.heuristic_name,
        cli.flaw_order_names.join(","),
        action_cost_name(cli.params.action_cost),
        cli.params.weight,
        limit_label,
        limits,
    );

    if let Some(limit) = cli.time_limit {
        eprintln!(
            "Time limit: {:.3}s per problem, counted from before translation",
            limit.as_secs_f64()
        );
    }
    if !cli.stages.is_empty() {
        let specs: Vec<&str> = cli.stages.iter().map(|stage| stage.spec.as_str()).collect();
        eprintln!(
            "Portfolio: {} stages | {}",
            cli.stages.len(),
            specs.join(" ; ")
        );
    }
    if let Some(mb) = cli.stage_mem_mb {
        eprintln!("Stage memory: a stage ends once the process holds {mb} MB resident");
    }

    let prune = cli.params.prune.names();
    if !prune.is_empty() {
        eprintln!("Pruning: {}", prune.join(","));
        if !cli.fdr_pocl && !cli.params.ground_actions {
            let inert = cli.params.prune.ground_only();
            if !inert.is_empty() {
                eprintln!(
                    "  {} cannot fire: lifted steps have no arguments yet (use -g or --fdr-pocl)",
                    inert.join(",")
                );
            }
        }
        let inert = if cli.fdr_pocl {
            cli.params.prune.lifted_only()
        } else {
            cli.params.prune.finite_domain_only()
        };
        if !inert.is_empty() {
            let reason = if cli.fdr_pocl {
                "have nothing to say about an already-ground SAS+ task"
            } else {
                "need finite-domain facts and do nothing without --fdr-pocl"
            };
            eprintln!("Pruning: {} {reason}", inert.join(","));
        }
    }

    if cli.fdr_pocl
        || cli.params.ground_actions
        || cli.heuristic_name.to_ascii_uppercase().contains("COMPILE")
    {
        eprintln!(
            "Fast Downward: driver {} | search {}",
            potoroo::external::fd_path(),
            potoroo::external::downward_path(),
        );
    }
}

fn action_cost_name(cost: ActionCost) -> &'static str {
    match cost {
        ActionCost::Task => "TASK",
        ActionCost::Unit => "UNIT",
        ActionCost::Duration => "DURATION",
        ActionCost::Relative => "RELATIVE",
    }
}

fn print_search_summary(status: &str, wall_ms: u128, stats: &RunStats) {
    eprintln!(
        "Search finished: {} in {:.2}s | visited {} | generated {} | max queued {} | h {} evals / {} ms | pruned {} | largest plan steps={} open={} threats={}",
        status,
        wall_ms as f64 / 1000.0,
        stats.nodes_visited,
        stats.nodes_generated,
        stats.max_queued,
        stats.h_evals,
        stats.h_eval_ms,
        stats.pruned,
        stats.max_steps,
        stats.max_open_conditions,
        stats.max_threats,
    );
    if stats.h2_runs > 0 {
        eprintln!(
            "Pair reachability: {} | completed {}/{} stages | {} ms | {} work | at most {} mutex pairs ({} beyond declared groups), {} unreachable facts, {} projected derived variables per stage | {} supporter templates removed across stages",
            stats.h2.status.as_str(), stats.h2_completed, stats.h2_runs,
            stats.h2.elapsed_ms, stats.h2.work, stats.h2.mutex_pairs,
            stats.h2.new_mutex_pairs,
            stats.h2.unreachable_facts, stats.h2.projected_variables, stats.h2.supporters_removed,
        );
    }
}

/// Peak resident set size in kilobytes from `/proc/self/status`.
/// Returns zero when the file is unavailable.
fn peak_rss_kb() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmHWM:"))
                .and_then(|l| l.split_whitespace().nth(1))
                .and_then(|kb| kb.parse().ok())
        })
        .unwrap_or(0)
}

/// The STATS outcome reported by the search.
fn outcome_label(status: &str) -> &'static str {
    match status {
        "solved" => "solved",
        "limit reached" => "limit",
        // Both time and stage-memory stops report `timeout` in STATS.
        // The external runner reserves `oom` for processes killed before reporting.
        "time limit reached" | "memory bound reached" => "timeout",
        _ => "noplan",
    }
}

/// Minimal JSON string escaping for the opt-in `POTOROO_STATS_JSON` line. Problem
/// and heuristic names are normally plain identifiers, but escape the
/// JSON-significant characters defensively.
fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            _ => out.push(c),
        }
    }
    out
}

/// Hand-rolled getopt-style parser for Potoroo's command-line options. Returns
/// `None` if `-H`/`-V` handled output and the program should exit.
fn parse_args(args: impl Iterator<Item = String>) -> Result<Option<Cli>, String> {
    let mut params = Parameters::default();
    let mut verbosity = 0u32;
    let mut fdr_pocl = false;
    let mut lifted_fdr = false;
    let mut lanes = Vec::new();
    let mut files = Vec::new();
    let mut heuristic_name = String::from("ADD/LIFO");
    let mut algorithm_name = String::from("A");
    // Track whether the user set these so repeated flags replace the defaults.
    let mut flaw_orders: Vec<FlawSelectionOrder> = Vec::new();
    let mut flaw_order_names: Vec<String> = Vec::new();
    let mut search_limits: Vec<usize> = Vec::new();
    let mut stages: Vec<Stage> = Vec::new();
    let mut time_limit: Option<Duration> = None;
    let mut stage_mem_mb: Option<usize> = None;

    let args: Vec<String> = args.collect();
    let mut i = 0;
    // After `--`, everything is a file.
    let mut only_files = false;
    while i < args.len() {
        let arg = &args[i];
        if only_files || !arg.starts_with('-') || arg == "-" {
            files.push(arg.clone());
            i += 1;
            continue;
        }
        if arg == "--" {
            only_files = true;
            i += 1;
            continue;
        }

        // Normalize: support `--long`, `-x`, and `-xVALUE`. `flag` is the option
        // letter/name; `inline` is any attached value.
        let (flag, inline): (String, Option<String>) = if let Some(long) = arg.strip_prefix("--") {
            match long.split_once('=') {
                Some((k, v)) => (long_to_short(k)?, Some(v.to_string())),
                None => (long_to_short(long)?, None),
            }
        } else {
            let body = &arg[1..];
            let (letter, rest) = body.split_at(1);
            (
                letter.to_string(),
                if rest.is_empty() {
                    None
                } else {
                    Some(rest.to_string())
                },
            )
        };

        // Helper closures cannot borrow `args`/`i` mutably easily, so inline the
        // "take a required value" logic.
        macro_rules! required_value {
            () => {{
                match inline.clone() {
                    Some(v) => v,
                    None => {
                        i += 1;
                        args.get(i)
                            .cloned()
                            .ok_or_else(|| format!("option -{flag} requires an argument"))?
                    }
                }
            }};
        }

        match flag.as_str() {
            "a" => {
                let v = required_value!();
                params.action_cost = parse_action_cost(&v)?;
            }
            "d" => {
                // Domain constraints (optional 0|1) — deferred; accepted as a no-op.
                let _ = inline;
            }
            "f" => {
                let v = required_value!();
                flaw_orders.push(FlawSelectionOrder::parse(&v)?);
                flaw_order_names.push(v);
            }
            "P" => fdr_pocl = true,
            "lifted-fdr" => lifted_fdr = true,
            "lane" => lanes.push(required_value!()),
            "g" => params.ground_actions = true,
            "h" => {
                let v = required_value!();
                params.heuristic = Heuristic::parse(&v)?;
                heuristic_name = v;
            }
            "H" => {
                print_help();
                return Ok(None);
            }
            "l" => {
                let v = required_value!();
                search_limits.push(parse_limit(&v)?);
            }
            "p" => {
                let v = required_value!();
                params.prune = potoroo::pruning::PruneOptions::parse(&v)?;
            }
            "max-queued" => {
                let v = required_value!();
                params.max_queued = Some(parse_count(&flag, &v)?);
            }
            "mem-mb" => {
                let v = required_value!();
                params.memory_limit_mb = Some(parse_count(&flag, &v)?);
            }
            "stage" => {
                let v = required_value!();
                stages.push(parse_stage(&v)?);
            }
            "stage-mem-mb" => {
                let v = required_value!();
                stage_mem_mb = Some(parse_count(&flag, &v)?);
            }
            "r" => return Err("-r (random open conditions) is not yet supported".to_string()),
            "S" => {
                let _ = required_value!(); // seed; only relevant with -r
            }
            "s" => {
                let v = required_value!();
                params.search_algorithm = parse_search_algorithm(&v)?;
                algorithm_name = v.to_ascii_uppercase();
            }
            "T" => {
                // VHPOP spells the wall-clock limit in minutes; `--time-limit`
                // spells the same limit in seconds.
                let v = required_value!();
                time_limit = Some(parse_time_limit(&v, 60.0)?);
            }
            "time-limit" => {
                let v = required_value!();
                time_limit = Some(parse_time_limit(&v, 1.0)?);
            }
            "t" => {
                let _ = required_value!(); // durative tolerance — deferred
            }
            "v" => {
                verbosity = match inline {
                    Some(v) if v.chars().all(|c| c == 'v') => {
                        verbosity.saturating_add(1).saturating_add(v.len() as u32)
                    }
                    Some(v) => v.parse().map_err(|_| format!("invalid verbosity `{v}`"))?,
                    None => verbosity.saturating_add(1),
                };
            }
            "V" => {
                println!("{PACKAGE} {VERSION}");
                return Ok(None);
            }
            "W" => {
                let _ = inline; // warning level — accepted, not acted upon
            }
            "w" => {
                let v = required_value!();
                params.weight = v.parse().map_err(|_| format!("invalid weight `{v}`"))?;
                if !params.weight.is_finite() || params.weight < 0.0 {
                    return Err(format!(
                        "invalid weight `{v}`: expected a finite non-negative number"
                    ));
                }
            }
            other => return Err(format!("unknown option `-{other}`")),
        }
        i += 1;
    }

    if !flaw_orders.is_empty() {
        params.flaw_orders = flaw_orders;
    } else {
        flaw_order_names.push("STATIC".to_string());
    }
    if !search_limits.is_empty() {
        params.search_limits = search_limits;
    }
    // One search limit per flaw order; pad with the last (or unlimited).
    while params.search_limits.len() < params.flaw_orders.len() {
        let pad = params.search_limits.last().copied().unwrap_or(usize::MAX);
        params.search_limits.push(pad);
    }
    // Every heuristic a run could reach is checked against its representation
    // here rather than when search reaches it: a portfolio that only found out
    // at its second stage would already have spent the first stage's share of
    // the clock, and would then abort with no plan and no statistics.
    let heuristics = std::iter::once(&params.heuristic).chain(stages.iter().map(|s| &s.heuristic));
    for heuristic in heuristics {
        if !fdr_pocl && heuristic.requires_fdr_pocl() {
            return Err("LMCUT and LMCUTR require --fdr-pocl".to_string());
        }
        if fdr_pocl {
            potoroo::fdr_pocl::supports_heuristic(heuristic).map_err(|e| e.to_string())?;
        }
    }

    // Only the last stage may run without a share of the clock: one before it
    // that never gives up would starve every stage after it, which is a
    // configuration nobody means to write.
    if let Some(position) = stages
        .iter()
        .take(stages.len().saturating_sub(1))
        .position(|stage| stage.share.is_none())
    {
        return Err(format!(
            "stage `{}` has no time limit, so no stage after it would ever run: \
             give every stage but the last one an `=SECS`",
            stages[position].spec
        ));
    }

    // Per-evaluation timing is only worth its two clock reads per generated
    // node where `h_eval_ms` is actually printed: the verbose summary and live
    // progress line, and the opt-in STATS row.
    params.time_h_evals = verbosity > 0 || std::env::var_os("POTOROO_STATS_JSON").is_some();

    Ok(Some(Cli {
        params,
        fdr_pocl,
        lifted_fdr,
        lanes,
        verbosity,
        files,
        flaw_order_names,
        heuristic_name,
        algorithm_name,
        stages,
        time_limit,
        stage_mem_mb,
    }))
}

/// Parses one `--stage` value: `HEURISTIC[@SEARCH][=SECS]`. The heuristic is
/// required; the search algorithm and the time share fall back to `-s` and
/// `--time-limit`. No heuristic or algorithm name contains `@` or `=`, so the
/// spec splits unambiguously left to right.
fn parse_stage(spec: &str) -> Result<Stage, String> {
    let (head, share) = match spec.split_once('=') {
        Some((head, share)) => (
            head,
            Some(
                parse_time_limit(share, 1.0)
                    .map_err(|_| format!("invalid stage time limit `{share}` in `{spec}`"))?,
            ),
        ),
        None => (spec, None),
    };
    let (heuristic_name, algorithm_name) = match head.split_once('@') {
        Some((heuristic, algorithm)) => (heuristic, Some(algorithm)),
        None => (head, None),
    };
    if heuristic_name.is_empty() {
        return Err(format!("stage `{spec}` names no heuristic"));
    }
    Ok(Stage {
        spec: spec.to_string(),
        heuristic: Heuristic::parse(heuristic_name)?,
        search_algorithm: algorithm_name.map(parse_search_algorithm).transpose()?,
        share,
    })
}

/// Maps a long option name to its short letter.
fn long_to_short(name: &str) -> Result<String, String> {
    let short = match name {
        "action-cost" => "a",
        "domain-constraints" => "d",
        "flaw-order" => "f",
        "fdr-pocl" => "P",
        "lifted-fdr" => "lifted-fdr",
        "lane" => "lane",
        "ground-actions" => "g",
        "heuristic" => "h",
        "help" => "H",
        "limit" => "l",
        "max-queued" => "max-queued",
        "mem-mb" => "mem-mb",
        "prune" => "p",
        "random-open-conditions" => "r",
        "seed" => "S",
        "search-algorithm" => "s",
        "stage" => "stage",
        "stage-mem-mb" => "stage-mem-mb",
        "time-limit" => "time-limit",
        "tolerance" => "t",
        "verbose" => "v",
        "version" => "V",
        "warnings" => "W",
        "weight" => "w",
        other => return Err(format!("unknown option `--{other}`")),
    };
    Ok(short.to_string())
}

/// A positive integer option value.
fn parse_count(flag: &str, v: &str) -> Result<usize, String> {
    match v.parse::<usize>() {
        Ok(n) if n > 0 => Ok(n),
        _ => Err(format!(
            "option --{flag} requires a positive integer, got `{v}`"
        )),
    }
}

/// The longest time limit accepted, in seconds: about thirty years. The point
/// is not the length but the arithmetic — beyond roughly this,
/// `Duration::from_secs_f64` and adding the result to an `Instant` overflow and
/// panic, and a planner run that meant `1e20` seconds meant something else.
const MAX_LIMIT_SECONDS: f64 = 1e9;

/// A positive, finite time limit, written in units of `unit_seconds` seconds:
/// one for `--time-limit` and a stage's share, sixty for `-T`, which VHPOP
/// spells in minutes. The bound rejects rather than saturates, since a value
/// this far out is a mistake and silently reinterpreting it would hide it.
fn parse_time_limit(v: &str, unit_seconds: f64) -> Result<Duration, String> {
    match v.parse::<f64>() {
        // Excludes infinities and NaN, both of which fail the comparison.
        Ok(value) if value > 0.0 && value * unit_seconds <= MAX_LIMIT_SECONDS => {
            Ok(Duration::from_secs_f64(value * unit_seconds))
        }
        _ => Err(format!("invalid time limit `{v}`")),
    }
}

fn parse_action_cost(v: &str) -> Result<ActionCost, String> {
    match v.to_ascii_uppercase().as_str() {
        "TASK" | "PDDL" => Ok(ActionCost::Task),
        "UNIT" => Ok(ActionCost::Unit),
        "DURATION" => Ok(ActionCost::Duration),
        "RELATIVE" => Ok(ActionCost::Relative),
        other => Err(format!("invalid action cost `{other}`")),
    }
}

fn parse_search_algorithm(v: &str) -> Result<SearchAlgorithm, String> {
    match v.to_ascii_uppercase().as_str() {
        "A" => Ok(SearchAlgorithm::A),
        "IDA" => Ok(SearchAlgorithm::Ida),
        "HC" => Ok(SearchAlgorithm::Hc),
        "BFS" => Ok(SearchAlgorithm::Bfs),
        "GBFS" => Ok(SearchAlgorithm::Gbfs),
        "LGBFS" => Ok(SearchAlgorithm::LazyGbfs),
        "LGBFS-D" => Ok(SearchAlgorithm::LazyGbfsDual),
        "ALT" => Ok(SearchAlgorithm::Alt),
        other => Err(format!("invalid search algorithm `{other}`")),
    }
}

fn parse_limit(v: &str) -> Result<usize, String> {
    if v.eq_ignore_ascii_case("unlimited") {
        Ok(usize::MAX)
    } else {
        v.parse().map_err(|_| format!("invalid search limit `{v}`"))
    }
}

fn print_help() {
    println!(
        "usage: {PACKAGE} [options] [file ...]\n\
         \n\
         Options (classical subset):\n\
         \x20 -a, --action-cost=COST     action cost: TASK, UNIT, DURATION, RELATIVE\n\
         \x20 -f, --flaw-order=ORDER     flaw-selection order (default STATIC)\n\
         \x20     --fdr-pocl             ground POCL search over SAS+ variables\n\
         \x20     --lifted-fdr           lifted POCL search over schematic SAS+ variables\n\
         \x20     --lane=ORDER[@HEUR][+deg]  a --lifted-fdr search lane (repeatable;\n\
         \x20                            HEUR is ADD, PADD, ADDR or OC; +deg binds\n\
         \x20                            threat-heavy variables); lanes run round-robin\n\
         \x20 -g, --ground-actions       plan with ground actions\n\
         \x20 -h, --heuristic=HEUR       plan-ranking heuristic (default ADD/LIFO)\n\
         \x20 -l, --limit=N              search-node limit (or `unlimited`)\n\
         \x20     --max-queued=N         halve the open lists above N queued plans (incomplete)\n\
         \x20     --mem-mb=M             halve the open lists above M MB resident (incomplete)\n\
         \x20 -p, --prune=RULES          opt-in pruning: cutset, symbolic, supporters, h2, edelete,\n\
         \x20                            disjunctive, params, joint, recursion, minimality, symmetry, all, none\n\
         \x20                            (default none)\n\
         \x20 -s, --search-algorithm=A   search algorithm: A, IDA, HC, BFS, GBFS, LGBFS, LGBFS-D, ALT\n\
         \x20     --stage=SPEC           restart-portfolio stage HEURISTIC[@SEARCH][=SECS];\n\
         \x20                            repeatable, run in order, @SEARCH defaults to -s and\n\
         \x20                            =SECS to the remaining --time-limit; only the last\n\
         \x20                            stage may leave =SECS off\n\
         \x20     --stage-mem-mb=M       end a stage once the process holds M MB resident, so\n\
         \x20                            the next one starts with the memory back\n\
         \x20 -T, --time-limit=SECS      wall-clock limit per problem, counted from before\n\
         \x20                            translation and grounding; -T takes minutes,\n\
         \x20                            --time-limit takes seconds\n\
         \x20 -v, --verbose[=N]          live search telemetry (repeat for more frequent updates)\n\
         \x20 -w, --weight=W             heuristic weight (default 1)\n\
         \x20 -H, --help                 display this help and exit\n\
         \x20 -V, --version              display version and exit"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pair_preprocessing_stats_preserve_work_and_proof_counts_across_stages() {
        use potoroo::h2::{Stats, Status};
        let stage = |h2| {
            let mut stats = potoroo::fdr_pocl::SearchStats::default();
            stats.h2 = h2;
            RunStats::from(stats)
        };
        let mut total = RunStats::default();
        total.add(&stage(Stats {
            status: Status::Complete,
            work: 100,
            elapsed_ms: 2,
            mutex_pairs: 7,
            new_mutex_pairs: 2,
            projected_variables: 4,
            unreachable_facts: 3,
            supporters_removed: 4,
        }));
        total.add(&stage(Stats {
            status: Status::Complete,
            work: 100,
            elapsed_ms: 3,
            mutex_pairs: 7,
            new_mutex_pairs: 2,
            projected_variables: 1,
            unreachable_facts: 3,
            supporters_removed: 4,
        }));
        total.add(&stage(Stats {
            status: Status::WorkLimit,
            work: 50,
            elapsed_ms: 1,
            ..Default::default()
        }));
        total.add(&RunStats::from(potoroo::search::SearchStats::default()));
        assert_eq!((total.h2_runs, total.h2_completed), (3, 2));
        assert_eq!(total.h2.status, Status::WorkLimit);
        assert_eq!((total.h2.work, total.h2.elapsed_ms), (250, 6));
        assert_eq!((total.h2.mutex_pairs, total.h2.unreachable_facts), (7, 3));
        assert_eq!(total.h2.new_mutex_pairs, 2);
        assert_eq!(total.h2.projected_variables, 4);
        assert_eq!(total.h2.supporters_removed, 8);
        let parsed = cli(&["--fdr-pocl", "-p", "all,no-h2"]);
        assert!(!parsed.params.prune.h2);
        assert!(cli(&["--fdr-pocl", "-p", "h2"]).params.prune.h2);
    }

    fn cli(args: &[&str]) -> Cli {
        parse_args(args.iter().map(|arg| (*arg).to_string()))
            .expect("arguments parse")
            .expect("arguments do not request an early exit")
    }

    #[test]
    fn literal_cli_uses_the_add_lifo_static_profile() {
        let cli = cli(&[]);
        assert_eq!(cli.heuristic_name, "ADD/LIFO");
        assert_eq!(cli.flaw_order_names, ["STATIC"]);
        assert_eq!(cli.params.search_algorithm, SearchAlgorithm::A);
        assert_eq!(cli.params.action_cost, ActionCost::Task);
        assert_eq!(cli.params.weight, 1.0);
    }

    #[test]
    fn every_representation_defaults_to_add_lifo() {
        assert_eq!(cli(&[]).heuristic_name, "ADD/LIFO");
        assert_eq!(cli(&["-g"]).heuristic_name, "ADD/LIFO");
        assert_eq!(cli(&["--fdr-pocl"]).heuristic_name, "ADD/LIFO");
    }

    #[test]
    fn an_explicit_heuristic_still_wins() {
        for heuristic in ["ADDR", "ADD", "ADD/FIFO", "ADD/OC/LIFO"] {
            assert_eq!(cli(&["-h", heuristic]).heuristic_name, heuristic);
            assert_eq!(
                cli(&["--fdr-pocl", "-h", heuristic]).heuristic_name,
                heuristic
            );
        }
    }

    fn rejects(args: &[&str]) -> String {
        match parse_args(args.iter().map(|arg| (*arg).to_string())) {
            Err(message) => message,
            Ok(_) => panic!("arguments {args:?} were accepted"),
        }
    }

    #[test]
    fn a_stage_spec_takes_a_heuristic_a_search_and_a_time_share() {
        let cli = cli(&[
            "--fdr-pocl",
            "--stage",
            "CLFF@ALT=10",
            "--stage=ADD=2.5",
            "--stage",
            "ADDR",
        ]);
        assert_eq!(cli.stages.len(), 3);

        assert_eq!(cli.stages[0].spec, "CLFF@ALT=10");
        assert_eq!(cli.stages[0].search_algorithm, Some(SearchAlgorithm::Alt));
        assert_eq!(cli.stages[0].share, Some(Duration::from_secs(10)));

        // `@SEARCH` omitted: the stage inherits `-s`, which the runner supplies
        // rather than the parser, so the stage itself records nothing.
        assert_eq!(cli.stages[1].spec, "ADD=2.5");
        assert_eq!(cli.stages[1].search_algorithm, None);
        assert_eq!(cli.stages[1].share, Some(Duration::from_millis(2500)));

        // `=SECS` omitted on the last stage: it runs to the global limit, or
        // forever.
        assert_eq!(cli.stages[2].spec, "ADDR");
        assert_eq!(cli.stages[2].search_algorithm, None);
        assert_eq!(cli.stages[2].share, None);
    }

    #[test]
    fn a_stage_spec_rejects_what_it_cannot_run() {
        assert!(rejects(&["--stage", "ADD=0"]).contains("invalid stage time limit `0`"));
        assert!(rejects(&["--stage", "ADD=x"]).contains("invalid stage time limit `x`"));
        assert!(rejects(&["--stage", "ADD=-1"]).contains("invalid stage time limit `-1`"));
        assert!(rejects(&["--stage", "NOPE"]).contains("invalid heuristic `NOPE`"));
        assert!(rejects(&["--stage", "ADD@NOPE"]).contains("invalid search algorithm `NOPE`"));
        assert!(rejects(&["--stage", "=10"]).contains("names no heuristic"));
        // The same rejection `-h` gives, so a portfolio cannot smuggle an FDR
        // heuristic into a representation that has no facts for it.
        assert!(rejects(&["--stage", "LMCUT"]).contains("require --fdr-pocl"));
        assert!(rejects(&["--stage", "ADD", "--stage", "CLFF"]).contains("require --fdr-pocl"));
    }

    #[test]
    fn a_stage_the_representation_cannot_evaluate_is_rejected_before_any_search() {
        // The mirror image: a literal-plan heuristic under --fdr-pocl. Caught
        // at parse time rather than when the second stage starts, which is
        // after the first has spent its share of the clock.
        for args in [
            &["--fdr-pocl", "-h", "LPSAS"][..],
            &["--fdr-pocl", "--stage", "LPSAS"][..],
            &["--fdr-pocl", "--stage", "CLFF@ALT=10", "--stage", "LPSAS"][..],
            &["--fdr-pocl", "--stage", "ADD=10", "--stage", "SAMPLE_FF"][..],
        ] {
            assert!(
                rejects(args).contains("literal plan representation"),
                "{args:?} was not rejected for its representation"
            );
        }
        // And the same heuristics are fine where they do belong.
        assert_eq!(cli(&["-g", "--stage", "LPSAS"]).stages.len(), 1);
    }

    #[test]
    fn only_the_last_stage_may_run_without_a_time_share() {
        assert_eq!(cli(&["--stage", "ADD"]).stages.len(), 1);
        assert_eq!(
            cli(&["--stage", "ADD=10", "--stage", "ADDR"]).stages.len(),
            2
        );
        let message = rejects(&["--stage", "ADD", "--stage", "ADDR"]);
        assert!(
            message.contains("stage `ADD` has no time limit"),
            "{message}"
        );
        assert!(
            message.contains("no stage after it would ever run"),
            "{message}"
        );
        // The offending stage named is the first one without a share, not the
        // last stage, which is allowed to have none.
        let message = rejects(&["--stage", "ADD=1", "--stage", "ADDR", "--stage", "ADD"]);
        assert!(
            message.contains("stage `ADDR` has no time limit"),
            "{message}"
        );
    }

    #[test]
    fn the_time_limit_is_seconds_and_dash_t_is_minutes() {
        assert_eq!(cli(&[]).time_limit, None);
        assert_eq!(
            cli(&["--time-limit", "2.5"]).time_limit,
            Some(Duration::from_millis(2500))
        );
        assert_eq!(
            cli(&["--time-limit=0.001"]).time_limit,
            Some(Duration::from_micros(1000))
        );
        assert_eq!(cli(&["-T", "2"]).time_limit, Some(Duration::from_secs(120)));
        assert!(rejects(&["--time-limit", "0"]).contains("invalid time limit `0`"));
        assert!(rejects(&["-T", "later"]).contains("invalid time limit `later`"));
    }

    #[test]
    fn an_absurd_time_limit_is_an_error_rather_than_a_panic() {
        // `Duration::from_secs_f64` panics past its range, and so does adding
        // the result to an `Instant`; the bound is checked before either.
        for value in ["1e20", "inf", "NaN", "1e300"] {
            assert!(
                rejects(&["--time-limit", value]).contains("invalid time limit"),
                "--time-limit {value} was accepted"
            );
            assert!(
                rejects(&["--stage", &format!("ADD={value}")]).contains("invalid stage time limit"),
                "--stage ADD={value} was accepted"
            );
        }
        // `-T` is in minutes, so the bound bites sixty times sooner.
        assert!(rejects(&["-T", "1e9"]).contains("invalid time limit"));
        assert_eq!(
            cli(&["--time-limit", "1e9"]).time_limit,
            Some(Duration::from_secs(1_000_000_000))
        );
    }

    #[test]
    fn a_plain_run_is_a_portfolio_of_one_stage() {
        let cli = cli(&["-h", "ADDR", "-s", "GBFS"]);
        assert!(cli.stages.is_empty());
        let portfolio = cli.portfolio();
        assert_eq!(portfolio.len(), 1);
        assert_eq!(portfolio[0].search_algorithm, Some(SearchAlgorithm::Gbfs));
        assert_eq!(portfolio[0].share, None);
        assert_eq!(cli.stats_label(), "GBFS(ADDR)");
    }

    #[test]
    fn a_portfolio_is_labelled_apart_from_any_stage_run_alone() {
        let cli = cli(&["--stage", "ADD=10", "--stage", "ADDR@ALT"]);
        assert_eq!(cli.stats_label(), "portfolio(ADD=10;ADDR@ALT)");
        assert_eq!(cli.portfolio().len(), 2);
    }

    #[test]
    fn a_stage_inherits_every_parameter_it_does_not_name() {
        let cli = cli(&[
            "--stage",
            "ADDR@GBFS=10",
            "-s",
            "ALT",
            "-w",
            "3",
            "-l",
            "500",
            "-p",
            "cutset",
            "--stage-mem-mb",
            "600",
        ]);
        let stage = cli.portfolio()[0].clone();
        let stage = &stage;
        let params = stage_parameters(&cli, stage, None);
        assert_eq!(params.search_algorithm, SearchAlgorithm::Gbfs);
        assert_eq!(params.weight, 3.0);
        assert_eq!(params.search_limits, vec![500]);
        assert!(params.prune.cutset);
        assert_eq!(params.memory_stop_mb, Some(600));
        assert!(params.deadline.is_some());

        // A stage with no share of its own runs to the global deadline.
        let unbounded = Stage {
            share: None,
            ..stage.clone()
        };
        assert!(stage_parameters(&cli, &unbounded, None).deadline.is_none());
        let global = Instant::now() + Duration::from_secs(60);
        assert_eq!(
            stage_parameters(&cli, &unbounded, Some(global)).deadline,
            Some(global)
        );
        // A share longer than what is left of the global limit is cut to it.
        let near = Instant::now() + Duration::from_millis(1);
        assert_eq!(
            stage_parameters(&cli, stage, Some(near)).deadline,
            Some(near)
        );
    }
}
