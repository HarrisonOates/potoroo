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
    verbosity: u32,
    files: Vec<String>,
    /// Effective flaw-order names, retained for readable telemetry.
    flaw_order_names: Vec<String>,
    /// Effective `-h` value (default `ADDR`, or `ADD` with `--fdr-pocl`). Used
    /// to label telemetry and the optional `POTOROO_STATS_JSON` output.
    heuristic_name: String,
    /// Raw `-s` value as given on the command line (default `A`). Included in the
    /// `POTOROO_STATS_JSON` output so different algorithms are distinguishable.
    algorithm_name: String,
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

    let sources: Vec<String> = if cli.files.is_empty() {
        let mut buf = String::new();
        std::io::stdin()
            .read_to_string(&mut buf)
            .map_err(|e| format!("error reading stdin: {e}"))?;
        vec![buf]
    } else {
        let mut v = Vec::new();
        for f in &cli.files {
            v.push(std::fs::read_to_string(f).map_err(|e| format!("error reading {f}: {e}"))?);
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
        let ctx = SearchContext::new(domain, problem, &cli.params);
        if cli.fdr_pocl {
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
            let search_result = if cli.verbosity > 0 {
                let mut printer = ProgressPrinter::new(cli.verbosity);
                let mut report = |progress| printer.report(progress);
                potoroo::fdr_pocl::solve_with_params_and_progress(&task, &cli.params, &mut report)
            } else {
                potoroo::fdr_pocl::solve_with_params(&task, &cli.params)
            };
            let (outcome, stats) = search_result.map_err(|e| e.to_string())?;
            let (solved, plan_len, plan_cost, status) = match outcome {
                potoroo::fdr_pocl::Outcome::Solved(solution) => {
                    if cli.verbosity > 0 {
                        eprintln!(
                            "Plan: {} steps | cost {}",
                            solution.operators.len(),
                            solution.plan.cost()
                        );
                    }
                    println!("{}", solution.format(&task));
                    (
                        true,
                        solution.operators.len(),
                        solution.plan.cost(),
                        "solved",
                    )
                }
                potoroo::fdr_pocl::Outcome::LimitReached => {
                    println!("no plan");
                    println!(";Search limit reached.");
                    (false, 0, 0, "limit reached")
                }
                potoroo::fdr_pocl::Outcome::NoSolution => {
                    println!("no plan");
                    println!(";Problem has no solution.");
                    (false, 0, 0, "no solution")
                }
            };
            let ms = timer.elapsed().as_millis();
            println!("Time: {ms}");
            if cli.verbosity > 0 {
                print_search_summary(
                    status,
                    ms,
                    stats.nodes_generated,
                    stats.nodes_visited,
                    stats.max_queued,
                    stats.h_evals,
                    stats.h_eval_ms,
                    stats.pruned,
                    stats.max_steps,
                    stats.max_open_conditions,
                    stats.max_threats,
                );
            }
            if std::env::var_os("POTOROO_STATS_JSON").is_some() {
                let label = format!("FDR:{}({})", cli.algorithm_name, cli.heuristic_name);
                eprintln!(
                    "STATS {{\"problem\":\"{}\",\"heuristic\":\"{}\",\"ground\":true,\
                     \"solved\":{},\"plan_len\":{},\"plan_cost\":{},\"nodes_generated\":{},\"nodes_visited\":{},\
                     \"wall_ms\":{},\"h_evals\":{},\"h_eval_ms\":{},\"pruned\":{},\
                     \"max_steps\":{},\"max_open_conditions\":{},\"max_threats\":{},\"max_queued\":{}}}",
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
                    stats.max_queued,
                );
            }
            continue;
        }
        let (outcome, stats) = if cli.verbosity > 0 {
            let mut printer = ProgressPrinter::new(cli.verbosity);
            let mut report = |progress| printer.report(progress);
            plan_with_progress(&ctx, &mut report)
        } else {
            plan_with_stats(&ctx)
        };
        let (solved, plan_len, plan_cost, status) = match &outcome {
            Outcome::Solved(p) => {
                if cli.verbosity > 0 {
                    eprintln!("Plan: {} steps | cost {}", p.num_steps(), p.cost());
                }
                println!("{}", format_steps(&ctx, &p));
                (true, p.num_steps(), p.cost(), "solved")
            }
            Outcome::LimitReached => {
                println!("no plan");
                println!(";Search limit reached.");
                (false, 0, 0, "limit reached")
            }
            Outcome::NoSolution => {
                println!("no plan");
                println!(";Problem has no solution.");
                (false, 0, 0, "no solution")
            }
        };
        let ms = timer.elapsed().as_millis();
        println!("Time: {ms}");
        if cli.verbosity > 0 {
            print_search_summary(
                status,
                ms,
                stats.nodes_generated,
                stats.nodes_visited,
                stats.max_queued,
                stats.h_evals,
                stats.h_eval_ms,
                stats.pruned,
                stats.max_steps,
                stats.max_open_conditions,
                stats.max_threats,
            );
        }

        // Machine-readable benchmark line (stderr, opt-in). Kept off stdout so
        // the differential tests still diff stdout byte-for-byte.
        if std::env::var_os("POTOROO_STATS_JSON").is_some() {
            // Label: "ALG(HEUR)" so different algorithms on the same heuristic
            // appear as distinct columns in the benchmark table.
            let label = format!("{}({})", cli.algorithm_name, cli.heuristic_name);
            eprintln!(
                "STATS {{\"problem\":\"{}\",\"heuristic\":\"{}\",\"ground\":{},\"solved\":{},\
                 \"plan_len\":{},\"plan_cost\":{},\"nodes_generated\":{},\"nodes_visited\":{},\"wall_ms\":{},\
                 \"h_evals\":{},\"h_eval_ms\":{},\"pruned\":{},\"max_steps\":{},\
                 \"max_open_conditions\":{},\"max_threats\":{},\"max_queued\":{}}}",
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
            );
        }
    }

    Ok(ExitCode::SUCCESS)
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
            "Search [{:>7.2}s] visited {} | generated {} | queued {} | h {} evals / {} ms | pruned {} | current steps={} open={} threats={} order={}",
            progress.elapsed.as_secs_f64(),
            progress.nodes_visited,
            progress.nodes_generated,
            progress.queued,
            progress.h_evals,
            progress.h_eval_ms,
            progress.pruned,
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

#[allow(clippy::too_many_arguments)]
fn print_search_summary(
    status: &str,
    wall_ms: u128,
    generated: usize,
    visited: usize,
    max_queued: usize,
    h_evals: usize,
    h_eval_ms: u128,
    pruned: usize,
    max_steps: usize,
    max_open: usize,
    max_threats: usize,
) {
    eprintln!(
        "Search finished: {} in {:.2}s | visited {} | generated {} | max queued {} | h {} evals / {} ms | pruned {} | largest plan steps={} open={} threats={}",
        status,
        wall_ms as f64 / 1000.0,
        visited,
        generated,
        max_queued,
        h_evals,
        h_eval_ms,
        pruned,
        max_steps,
        max_open,
        max_threats,
    );
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
    let mut files = Vec::new();
    let mut heuristic_name = String::from("ADDR");
    let mut algorithm_name = String::from("A");
    let mut heuristic_explicit = false;
    // Track whether the user set these so repeated flags replace the defaults.
    let mut flaw_orders: Vec<FlawSelectionOrder> = Vec::new();
    let mut flaw_order_names: Vec<String> = Vec::new();
    let mut search_limits: Vec<usize> = Vec::new();

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
            "g" => params.ground_actions = true,
            "h" => {
                let v = required_value!();
                params.heuristic = Heuristic::parse(&v)?;
                heuristic_name = v;
                heuristic_explicit = true;
            }
            "H" => {
                print_help();
                return Ok(None);
            }
            "l" => {
                let v = required_value!();
                search_limits.push(parse_limit(&v)?);
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
                let _ = required_value!(); // time limit (minutes) — accepted, not enforced
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
            }
            other => return Err(format!("unknown option `-{other}`")),
        }
        i += 1;
    }

    // Reuse-aware ADDR is strongest on literal partial plans, but creates deep
    // plateaus on the finite-domain representation. Plain ADD is the robust FDR
    // default. An explicit `-h` always wins.
    if fdr_pocl && !heuristic_explicit {
        params.heuristic = Heuristic::parse("ADD").expect("ADD is a valid heuristic");
        heuristic_name = "ADD".to_string();
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
    if !fdr_pocl && params.heuristic.requires_fdr_pocl() {
        return Err("LMCUT and LMCUTR require --fdr-pocl".to_string());
    }

    Ok(Some(Cli {
        params,
        fdr_pocl,
        verbosity,
        files,
        flaw_order_names,
        heuristic_name,
        algorithm_name,
    }))
}

/// Maps a long option name to its short letter.
fn long_to_short(name: &str) -> Result<String, String> {
    let short = match name {
        "action-cost" => "a",
        "domain-constraints" => "d",
        "flaw-order" => "f",
        "fdr-pocl" => "P",
        "ground-actions" => "g",
        "heuristic" => "h",
        "help" => "H",
        "limit" => "l",
        "random-open-conditions" => "r",
        "seed" => "S",
        "search-algorithm" => "s",
        "time-limit" => "T",
        "tolerance" => "t",
        "verbose" => "v",
        "version" => "V",
        "warnings" => "W",
        "weight" => "w",
        other => return Err(format!("unknown option `--{other}`")),
    };
    Ok(short.to_string())
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
         \x20 -g, --ground-actions       plan with ground actions\n\
         \x20 -h, --heuristic=HEUR       plan-ranking heuristic (default ADDR; ADD for FDR)\n\
         \x20 -l, --limit=N              search-node limit (or `unlimited`)\n\
         \x20 -s, --search-algorithm=A   search algorithm: A, IDA, HC, BFS, GBFS, LGBFS, LGBFS-D, ALT\n\
         \x20 -v, --verbose[=N]          live search telemetry (repeat for more frequent updates)\n\
         \x20 -w, --weight=W             heuristic weight (default 1)\n\
         \x20 -H, --help                 display this help and exit\n\
         \x20 -V, --version              display version and exit"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cli(args: &[&str]) -> Cli {
        parse_args(args.iter().map(|arg| (*arg).to_string()))
            .expect("arguments parse")
            .expect("arguments do not request an early exit")
    }

    #[test]
    fn literal_cli_uses_the_addr_static_profile() {
        let cli = cli(&[]);
        assert_eq!(cli.heuristic_name, "ADDR");
        assert_eq!(cli.flaw_order_names, ["STATIC"]);
        assert_eq!(cli.params.search_algorithm, SearchAlgorithm::A);
        assert_eq!(cli.params.action_cost, ActionCost::Task);
        assert_eq!(cli.params.weight, 1.0);
    }

    #[test]
    fn fdr_cli_uses_add_unless_the_heuristic_is_explicit() {
        assert_eq!(cli(&["--fdr-pocl"]).heuristic_name, "ADD");
        assert_eq!(cli(&["--fdr-pocl", "-h", "ADDR"]).heuristic_name, "ADDR");
    }
}
