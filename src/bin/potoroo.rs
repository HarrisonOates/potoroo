//! Potoroo command-line entry point. Outputs per-problem: `;name`, the scheduled
//! step lines or a `no plan` message, and a `Time:` line. The classical subset
//! supports A*/IDA*/hill-climbing (HC behaves like A* in this version), the
//! cheap and additive (ADD/ADDR) heuristics, and the full flaw-selection DSL
//! with round-robin over multiple `-f`/`-l`. Truly deferred features
//! (durative/numeric) report a clear error.

use std::collections::BTreeMap;
use std::io::Read;
use std::process::ExitCode;
use std::time::Instant;

use potoroo::domain::Domain;
use potoroo::params::{ActionCost, Parameters, SearchAlgorithm};
use potoroo::heuristics::{FlawSelectionOrder, Heuristic};
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use potoroo::problem::Problem;
use potoroo::search::{format_steps, plan_with_stats, Outcome, SearchContext};

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
    verbosity: u32,
    files: Vec<String>,
    /// Raw `-h` value as given on the command line (default `UCPOP`). Only used
    /// to label the optional `POTOROO_STATS_JSON` benchmark output.
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
            v.push(
                std::fs::read_to_string(f)
                    .map_err(|e| format!("error reading {f}: {e}"))?,
            );
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
        let domain = domains
            .get(&problem.domain_name)
            .expect("domain was looked up during lowering");
        println!(";{}", problem.name);
        let timer = Instant::now();
        let ctx = SearchContext::new(domain, problem, &cli.params);
        let (outcome, stats) = plan_with_stats(&ctx);
        let (solved, plan_len) = match &outcome {
            Outcome::Solved(p) => {
                if cli.verbosity > 0 {
                    eprintln!("Number of steps: {}", p.num_steps());
                }
                println!("{}", format_steps(&ctx, &p));
                (true, p.num_steps())
            }
            Outcome::LimitReached => {
                println!("no plan");
                println!(";Search limit reached.");
                (false, 0)
            }
            Outcome::NoSolution => {
                println!("no plan");
                println!(";Problem has no solution.");
                (false, 0)
            }
        };
        let ms = timer.elapsed().as_millis();
        println!("Time: {ms}");

        // Machine-readable benchmark line (stderr, opt-in). Kept off stdout so
        // the differential tests still diff stdout byte-for-byte.
        if std::env::var_os("POTOROO_STATS_JSON").is_some() {
            // Label: "ALG(HEUR)" so different algorithms on the same heuristic
            // appear as distinct columns in the benchmark table.
            let label = format!("{}({})", cli.algorithm_name, cli.heuristic_name);
            eprintln!(
                "STATS {{\"problem\":\"{}\",\"heuristic\":\"{}\",\"ground\":{},\"solved\":{},\
                 \"plan_len\":{},\"nodes_generated\":{},\"nodes_visited\":{},\"wall_ms\":{},\
                 \"h_evals\":{},\"h_eval_ms\":{},\"pruned\":{}}}",
                json_escape(&problem.name),
                json_escape(&label),
                cli.params.ground_actions,
                solved,
                plan_len,
                stats.nodes_generated,
                stats.nodes_visited,
                ms,
                stats.h_evals,
                stats.h_eval_ms,
                stats.pruned,
            );
        }
    }

    Ok(ExitCode::SUCCESS)
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

/// Hand-rolled getopt-style parser matching `vhpop.cc`'s option set. Returns
/// `None` if `-H`/`-V` handled output and the program should exit.
fn parse_args(args: impl Iterator<Item = String>) -> Result<Option<Cli>, String> {
    let mut params = Parameters::default();
    let mut verbosity = 0u32;
    let mut files = Vec::new();
    let mut heuristic_name = String::from("UCPOP");
    let mut algorithm_name = String::from("A");
    // Track whether the user set these so repeated flags replace the defaults.
    let mut flaw_orders: Vec<FlawSelectionOrder> = Vec::new();
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
            }
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
            "r" => {
                return Err("-r (random open conditions) is not yet supported".to_string())
            }
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
                    Some(v) => v
                        .parse()
                        .map_err(|_| format!("invalid verbosity `{v}`"))?,
                    None => 1,
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
                params.weight = v
                    .parse()
                    .map_err(|_| format!("invalid weight `{v}`"))?;
            }
            other => return Err(format!("unknown option `-{other}`")),
        }
        i += 1;
    }

    if !flaw_orders.is_empty() {
        params.flaw_orders = flaw_orders;
    } else if !params.ground_actions && params.heuristic.needs_planning_graph() {
        // Lifted planning-graph runs: resolve static open conditions first.
        // Statics only link to init, so handling them early commits variable
        // bindings cheaply and makes the planning-graph heuristic informative
        // (unbound atoms are otherwise valued by their most optimistic
        // instantiation). Big measured win on logistics/hanoi; overridable
        // with an explicit -f. The library default stays UCPOP.
        params.flaw_orders =
            vec![FlawSelectionOrder::parse("static").expect("static alias parses")];
    }
    if !search_limits.is_empty() {
        params.search_limits = search_limits;
    }
    // One search limit per flaw order; pad with the last (or unlimited).
    while params.search_limits.len() < params.flaw_orders.len() {
        let pad = params.search_limits.last().copied().unwrap_or(usize::MAX);
        params.search_limits.push(pad);
    }

    Ok(Some(Cli {
        params,
        verbosity,
        files,
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
        v.parse()
            .map_err(|_| format!("invalid search limit `{v}`"))
    }
}

fn print_help() {
    println!(
        "usage: {PACKAGE} [options] [file ...]\n\
         \n\
         Options (classical subset):\n\
         \x20 -a, --action-cost=COST     action cost: UNIT, DURATION, RELATIVE\n\
         \x20 -f, --flaw-order=ORDER     flaw-selection order (default UCPOP)\n\
         \x20 -g, --ground-actions       plan with ground actions\n\
         \x20 -h, --heuristic=HEUR       plan-ranking heuristic (default UCPOP)\n\
         \x20 -l, --limit=N              search-node limit (or `unlimited`)\n\
         \x20 -s, --search-algorithm=A   search algorithm: A, IDA, HC, BFS, GBFS, LGBFS, LGBFS-D, ALT\n\
         \x20 -v, --verbose[=N]          verbosity level\n\
         \x20 -w, --weight=W             heuristic weight (default 1)\n\
         \x20 -H, --help                 display this help and exit\n\
         \x20 -V, --version              display version and exit"
    );
}
