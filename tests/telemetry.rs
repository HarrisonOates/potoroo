//! CLI coverage for the human-readable, opt-in search telemetry.

use std::process::Command;

fn run(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_potoroo"))
        .args(args)
        .env_remove("POTOROO_STATS")
        .env_remove("POTOROO_STATS_JSON")
        .output()
        .expect("run potoroo")
}

#[test]
fn verbose_mode_reports_live_and_final_search_state() {
    let output = run(&[
        "-v",
        "examples/blocks-world-domain.pddl",
        "examples/sussman-anomaly.pddl",
    ]);
    assert!(output.status.success());

    let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
    assert!(stderr.contains(
        "Search: lifted POCL | A(ADDR) | flaws STATIC | cost TASK | weight 1 | node limit unlimited"
    ));
    assert!(stderr.contains("visited 1 | generated"));
    assert!(stderr.contains("| queued "));
    assert!(stderr.contains("| current steps=0 open=2 threats=0 order=1"));
    assert!(stderr.contains("Search finished: solved"));
    assert!(stderr.contains("largest plan"));
}

#[test]
fn telemetry_stays_off_stderr_by_default() {
    let output = run(&[
        "examples/blocks-world-domain.pddl",
        "examples/sussman-anomaly.pddl",
    ]);
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
}

#[test]
fn compact_repeated_verbose_flag_is_accepted() {
    let output = run(&[
        "-vv",
        "examples/blocks-world-domain.pddl",
        "examples/sussman-anomaly.pddl",
    ]);
    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("Search finished: solved"));
}
