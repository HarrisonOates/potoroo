//! CLI coverage for deadlines and restart portfolios.
//!
//! Exact node counts check stage accounting and independent restarts.

use std::io::Write;
use std::process::{Command, Stdio};

/// Runs the planner with the STATS line on, since every claim here is about a
/// field of it.
fn run(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_potoroo"))
        .args(args)
        .env_remove("POTOROO_STATS")
        .env("POTOROO_STATS_JSON", "1")
        .output()
        .expect("run potoroo")
}

/// The value of one integer field of the STATS line.
fn stat(stderr: &str, field: &str) -> i64 {
    let key = format!("\"{field}\":");
    let rest = stderr
        .split_once(&key)
        .unwrap_or_else(|| panic!("STATS line has no `{field}` field in:\n{stderr}"))
        .1;
    let end = rest
        .find(|c: char| !c.is_ascii_digit() && c != '-')
        .unwrap_or(rest.len());
    rest[..end].parse().expect("a numeric STATS field")
}

/// The `generated N` count from a `Stage n/m finished:` line.
fn stage_generated(stderr: &str, prefix: &str) -> i64 {
    let line = stderr
        .lines()
        .find(|line| line.starts_with(prefix))
        .unwrap_or_else(|| panic!("no `{prefix}` line in:\n{stderr}"));
    line.rsplit_once("generated ")
        .expect("a stage line reports its generated nodes")
        .1
        .trim()
        .parse()
        .expect("a numeric node count")
}

/// The baseline this whole task must not move: the default configuration on
/// `sussman-anomaly`, measured with the binary as it stood before the time
/// limit and the portfolio were added.
const SUSSMAN_GENERATED: i64 = 64;

#[test]
fn the_default_configuration_still_generates_the_same_nodes() {
    let output = run(&[
        "examples/blocks-world-domain.pddl",
        "examples/sussman-anomaly.pddl",
    ]);
    assert!(output.status.success());
    let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
    assert_eq!(stat(&stderr, "nodes_generated"), SUSSMAN_GENERATED);
    assert_eq!(stat(&stderr, "nodes_visited"), 40);
    assert!(stderr.contains("\"outcome\":\"solved\""));
}

#[test]
fn a_time_limit_stops_a_search_that_needs_longer() {
    // `gripper-20` takes a quarter of a second under the default
    // configuration, so a millisecond is short by more than two orders of
    // magnitude however fast the machine is.
    let output = run(&[
        "--time-limit",
        "0.001",
        "examples/gripper-domain.pddl",
        "examples/gripper-20.pddl",
    ]);
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
    assert!(stdout.contains("no plan"), "{stdout}");
    assert!(stdout.contains(";Time limit reached."), "{stdout}");
    assert!(
        !stdout.contains(";Search limit reached."),
        "a time limit is not a node limit:\n{stdout}"
    );

    let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
    assert!(
        stderr.contains("\"outcome\":\"timeout\""),
        "the sweep tells a timeout from a node limit by this field:\n{stderr}"
    );
    assert!(stderr.contains("\"solved\":false"), "{stderr}");
}

#[test]
fn the_verbose_summary_names_the_time_limit() {
    let output = run(&[
        "-v",
        "--time-limit",
        "0.001",
        "examples/gripper-domain.pddl",
        "examples/gripper-20.pddl",
    ]);
    assert!(output.status.success());
    let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
    assert!(
        stderr.contains("Search finished: time limit reached"),
        "{stderr}"
    );
    assert!(
        stderr.contains("Time limit: 0.001s per problem"),
        "{stderr}"
    );
}

#[test]
fn a_later_stage_solves_what_the_first_had_no_time_for() {
    // A microsecond has always passed by the time the first node is expanded,
    // so the first stage contributes its initial plan and nothing else, and
    // the second searches exactly as a plain run would.
    let output = run(&[
        "--stage",
        "ADD=0.000001",
        "--stage",
        "ADD",
        "examples/blocks-world-domain.pddl",
        "examples/sussman-anomaly.pddl",
    ]);
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
    assert!(stdout.contains("(puton a b table)"), "{stdout}");

    let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
    assert!(stderr.contains("\"outcome\":\"solved\""), "{stderr}");
    assert_eq!(
        stat(&stderr, "nodes_generated"),
        SUSSMAN_GENERATED + 1,
        "the STATS line sums the stages:\n{stderr}"
    );
    assert_eq!(stat(&stderr, "nodes_visited"), 40);
    assert!(
        stderr.contains("\"heuristic\":\"portfolio(ADD=0.000001;ADD)\""),
        "a portfolio row must not look like one of its stages run alone:\n{stderr}"
    );
}

#[test]
fn the_verbose_output_reports_each_stage() {
    let output = run(&[
        "-v",
        "--stage",
        "ADD=0.000001",
        "--stage",
        "ADD",
        "examples/blocks-world-domain.pddl",
        "examples/sussman-anomaly.pddl",
    ]);
    assert!(output.status.success());
    let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
    assert!(stderr.contains("Portfolio: 2 stages | ADD=0.000001 ; ADD"));
    assert!(
        stderr.contains("Stage 1/2 started: ADD=0.000001"),
        "{stderr}"
    );
    assert!(
        stderr.contains("Stage 1/2 finished: time limit reached | generated 1"),
        "{stderr}"
    );
    assert!(stderr.contains("Stage 2/2 started: ADD"), "{stderr}");
    assert!(
        stderr.contains("Stage 2/2 finished: solved | generated 64"),
        "{stderr}"
    );
}

/// Read an unsolvable domain and problem together from stdin.
const UNSOLVABLE: &str = "\
(define (domain stuck) (:requirements :strips) (:predicates (waited) (done))
 (:action wait :parameters () :precondition (and) :effect (waited)))
(define (problem stuck-problem) (:domain stuck) (:init) (:goal (done)))";

#[test]
fn an_exhausted_search_space_ends_the_portfolio() {
    // An exhausted search space is an exact verdict: a second stage would only
    // search the same space again, so the first one is the last.
    let mut child = Command::new(env!("CARGO_BIN_EXE_potoroo"))
        .args(["-v", "--stage", "ADD", "--stage", "ADDR"])
        .env_remove("POTOROO_STATS")
        .env("POTOROO_STATS_JSON", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run potoroo");
    child
        .stdin
        .take()
        .expect("stdin is piped")
        .write_all(UNSOLVABLE.as_bytes())
        .expect("write the task");
    let output = child.wait_with_output().expect("potoroo exits");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
    assert!(stdout.contains(";Problem has no solution."), "{stdout}");
    let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
    assert!(
        stderr.contains("Stage 1/2 finished: no solution"),
        "{stderr}"
    );
    assert!(
        !stderr.contains("Stage 2/2 started"),
        "an exact verdict should not be re-searched:\n{stderr}"
    );
}

#[test]
fn a_stage_hands_its_memory_back_to_the_one_after_it() {
    // The regression this pins: dropping a stage's queues returns them to the
    // allocator, not to the kernel, so without an explicit release the second
    // stage reads the first stage's peak as its own resident set and stops
    // having expanded nothing. Thirty megabytes is well under what the first
    // stage reaches on `gripper-20` and well over the process baseline, so the
    // first stage must hit the bound and the second must survive it.
    let output = run(&[
        "-v",
        "--stage-mem-mb",
        "30",
        "--stage",
        "ADD",
        "--stage",
        "ADD",
        "examples/gripper-domain.pddl",
        "examples/gripper-20.pddl",
    ]);
    assert!(output.status.success());
    let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
    assert!(
        stderr.contains("Stage 1/2 finished: time limit reached"),
        "the first stage should have hit the memory bound:\n{stderr}"
    );
    assert!(stderr.contains("Stage 2/2 started: ADD"), "{stderr}");

    // Both stages run the same configuration under the same bound, so the
    // second should get as far as the first; anything near a single node means
    // it was stopped by its predecessor's memory rather than by its own.
    let generated = stage_generated(&stderr, "Stage 2/2 finished:");
    assert!(
        generated > 1000,
        "the second stage expanded almost nothing, so the memory was never \
         handed back: it generated {generated}\n{stderr}"
    );
}

#[test]
fn a_global_time_limit_caps_a_stage_that_asks_for_longer() {
    // The stage asks for an hour; the problem has a millisecond. The stage
    // deadline is the earlier of the two, so the run still ends promptly.
    let output = run(&[
        "--time-limit",
        "0.001",
        "--stage",
        "ADD=3600",
        "examples/gripper-domain.pddl",
        "examples/gripper-20.pddl",
    ]);
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
    assert!(stdout.contains(";Time limit reached."), "{stdout}");
}
