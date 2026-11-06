//! Feature-gated HTN entry point; classical CLI and search are independent.
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{Duration, Instant};

use clap::Parser;
use potoroo::htn::{pipeline, search, Config, Outcome, StopReason};

#[derive(Parser)]
#[command(
    name = "potoroo-htn",
    version,
    about = "Strict HTN planning by decomposition and causal-link refinement"
)]
struct Cli {
    /// HDDL domain and problem; one file with --lifted or --grounded.
    #[arg(required = true, num_args = 1..=2, value_name = "INPUT")]
    files: Vec<PathBuf>,
    /// Read Malleefowl's grounded PANDA .sas directly (not Fast Downward SAS+).
    #[arg(long, conflicts_with = "lifted")]
    grounded: bool,
    /// Ground a parser-produced lifted .htn with Malleefowl.
    #[arg(long)]
    lifted: bool,
    /// HDDL parser executable (default POTOROO_HTN_PARSER or pandaPIparser).
    #[arg(long)]
    parser: Option<PathBuf>,
    /// Malleefowl executable (default POTOROO_MALLEEFOWL or malleefowl).
    #[arg(long)]
    grounder: Option<PathBuf>,
    /// Generated-node limit, including the initial node.
    #[arg(short = 'l', long)]
    limit: Option<usize>,
    /// Optional refinement-depth bound; reaching it is not unsolvability.
    #[arg(long)]
    max_depth: Option<usize>,
    /// Wall seconds for parsing, grounding and search.
    #[arg(long, value_parser = seconds)]
    time_limit: Option<Duration>,
}

fn seconds(value: &str) -> Result<Duration, String> {
    let seconds = value
        .parse::<f64>()
        .map_err(|_| "expected nonnegative seconds")?;
    Duration::try_from_secs_f64(seconds)
        .map_err(|_| "time limit must be finite, nonnegative and representable".into())
}

fn main() -> ExitCode {
    match run(Cli::parse()) {
        Ok(code) => code,
        Err(error) => {
            eprintln!("potoroo-htn: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run(cli: Cli) -> Result<ExitCode, String> {
    let start = Instant::now();
    let deadline = cli
        .time_limit
        .map(|duration| start.checked_add(duration).ok_or("time limit is too large"))
        .transpose()?;
    let input = if cli.grounded || cli.lifted {
        if cli.files.len() != 1 {
            return Err("--grounded/--lifted requires exactly one input file".into());
        }
        if cli.grounded {
            pipeline::Input::Grounded(&cli.files[0])
        } else {
            pipeline::Input::Lifted(&cli.files[0])
        }
    } else {
        if cli.files.len() != 2 {
            return Err("expected HDDL domain and problem, or --grounded/--lifted FILE".into());
        }
        pipeline::Input::Hddl {
            domain: &cli.files[0],
            problem: &cli.files[1],
        }
    };
    let defaults = pipeline::Tools::default();
    let tools = pipeline::Tools {
        parser: cli.parser.unwrap_or(defaults.parser),
        grounder: cli.grounder.unwrap_or(defaults.grounder),
    };
    let problem = match pipeline::load(input, &tools, deadline) {
        Ok(problem) => problem,
        Err(pipeline::Error::Deadline) => {
            println!("no plan: time limit reached");
            return Ok(ExitCode::from(2));
        }
        Err(error) => return Err(error.to_string()),
    };
    let result = search(
        &problem,
        &Config {
            node_limit: cli.limit,
            max_depth: cli.max_depth,
            deadline,
        },
    )?;
    eprintln!("HTN: generated={} expanded={} decompositions={} links={} threat_orderings={} max_queued={} elapsed={:.3}s",
        result.stats.generated, result.stats.expanded, result.stats.decompositions,
        result.stats.causal_links, result.stats.threat_orderings, result.stats.max_queued,
        start.elapsed().as_secs_f64());
    match result.outcome {
        Outcome::Solved(solution) => {
            print!("{}", solution.certificate.to_panda(&problem)?);
            eprintln!(
                "HTN: primitive_occurrences={} cost={} refinement_depth={}",
                solution.certificate.steps.len(),
                solution.cost,
                solution.plan.refinement_depth()
            );
            Ok(ExitCode::SUCCESS)
        }
        Outcome::NoSolution => {
            println!("no plan: search exhausted");
            Ok(ExitCode::SUCCESS)
        }
        Outcome::Stopped(reason) => {
            let reason = match reason {
                StopReason::NodeLimit => "node limit",
                StopReason::DepthLimit => "refinement depth limit",
                StopReason::Deadline => "time limit",
            };
            println!("no plan: {reason} reached");
            Ok(ExitCode::from(2))
        }
    }
}
