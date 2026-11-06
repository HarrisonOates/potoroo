//! Feature-gated HTN entry point; classical CLI and search are independent.
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{Duration, Instant};

use clap::Parser;
use potoroo::htn::{
    pipeline, search, AStarTieBreak, Config, FlawSelection, Outcome, SearchStrategy, StopReason,
    TdgMode,
};

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
    /// Read grounded PANDA .sas directly (not Fast Downward SAS+).
    #[arg(long, conflicts_with = "lifted")]
    grounded: bool,
    /// Ground a parser-produced lifted .htn with pandaPIgrounder.
    #[arg(long)]
    lifted: bool,
    /// HDDL parser executable (default POTOROO_HTN_PARSER or pandaPIparser).
    #[arg(long)]
    parser: Option<PathBuf>,
    /// Grounder executable (default POTOROO_HTN_GROUNDER or pandaPIgrounder).
    #[arg(long)]
    grounder: Option<PathBuf>,
    /// Queue policy; astar/gbfs use the TDG primitive-cost bound.
    #[arg(long, value_enum, default_value = "bfs")]
    search: SearchStrategy,
    /// Flaw policy; systematic commits support subtrees and uses last-achiever links.
    #[arg(long, value_enum, default_value_t = FlawSelection::default())]
    flaws: FlawSelection,
    /// TDG evaluation; recompute eagerly or lazily after decomposition choices.
    #[arg(long, value_enum, default_value_t = TdgMode::default())]
    tdg: TdgMode,
    /// A* tie policy; ignored by bfs/gbfs. Action cost remains the primary key.
    #[arg(long, value_enum, default_value_t = AStarTieBreak::default())]
    astar_tie: AStarTieBreak,
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
            strategy: cli.search,
            flaws: cli.flaws,
            tdg: cli.tdg,
            astar_tie: cli.astar_tie,
        },
    )?;
    eprintln!("HTN: generated={} expanded={} decompositions={} links={} threat_orderings={} max_queued={} support_decompositions={} tdg_pruned={} cost_bound_pruned={} tdg_recomputed={} tdg_requeued={} tdg_cache_hits={} equal_f_expanded={} max_f_plateau={} elapsed={:.3}s",
        result.stats.generated, result.stats.expanded, result.stats.decompositions,
        result.stats.causal_links, result.stats.threat_orderings, result.stats.max_queued,
        result.stats.support_decompositions, result.stats.tdg_pruned, result.stats.cost_bound_pruned,
        result.stats.tdg_recomputed, result.stats.tdg_requeued, result.stats.tdg_cache_hits,
        result.stats.equal_f_expanded, result.stats.max_f_plateau,
        start.elapsed().as_secs_f64());
    match result.outcome {
        Outcome::Solved(solution) => {
            print!("{}", solution.certificate.to_panda(&problem)?);
            eprintln!(
                "HTN: primitive_occurrences={} cost={} refinement_depth={} cost_optimal={}",
                solution.certificate.steps.len(),
                solution.cost,
                solution.plan.refinement_depth(),
                solution.cost_optimal
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
