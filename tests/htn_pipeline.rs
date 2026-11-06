#![cfg(feature = "htn")]

use potoroo::htn::{pipeline, search, Config, Outcome};
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{Duration, Instant};

#[test]
fn grounded_cli_requires_no_external_tools() {
    let path = std::env::temp_dir().join(format!("potoroo-htn-cli-{}.sas", std::process::id()));
    // Zero facts/actions; root has a genuinely empty decomposition.
    fs::write(
        &path,
        "0\n0\n0\n0\n0\n0\n-1\n-1\n1\n1 root[]\n0\n1\nempty\n0\n-1\n-1\n",
    )
    .unwrap();
    let run = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_potoroo-htn"))
            .args(args)
            .arg(&path)
            .env("POTOROO_MALLEEFOWL", "/missing/grounder")
            .env("POTOROO_HTN_PARSER", "/missing/parser")
            .output()
            .unwrap()
    };
    let solved = run(&["--grounded"]);
    assert!(
        solved.status.success(),
        "{}",
        String::from_utf8_lossy(&solved.stderr)
    );
    assert!(String::from_utf8_lossy(&solved.stdout).contains("==>\nroot 1\n1 root[] -> empty\n<=="));
    for strategy in ["bfs", "astar", "gbfs"] {
        for flaws in ["decomposition-first", "interleaved"] {
            let output = run(&["--grounded", "--search", strategy, "--flaws", flaws]);
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let expected = format!("cost_optimal={}", strategy == "astar");
            assert!(String::from_utf8_lossy(&output.stderr).contains(&expected));
            let bounded = run(&[
                "--grounded",
                "--search",
                strategy,
                "--flaws",
                flaws,
                "--max-depth",
                "0",
            ]);
            assert_eq!(bounded.status.code(), Some(2));
        }
    }
    assert!(!run(&["--grounded", "--search", "unknown"]).status.success());
    let limited = run(&["--grounded", "--limit", "0"]);
    assert_eq!(limited.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&limited.stdout).contains("node limit"));
    let timed = run(&["--grounded", "--time-limit", "0"]);
    assert_eq!(timed.status.code(), Some(2));
    let bad = run(&["--grounded", "--time-limit", "NaN"]);
    assert!(!bad.status.success());
    fs::remove_file(path).unwrap();
}

#[test]
fn malleefowl_pipeline_certificate_verifies_against_original_hddl() {
    let (Some(parser), Some(grounder)) = (
        std::env::var_os("POTOROO_HTN_PARSER"),
        std::env::var_os("POTOROO_MALLEEFOWL"),
    ) else {
        eprintln!(
            "skipping external HTN integration: set POTOROO_HTN_PARSER and POTOROO_MALLEEFOWL"
        );
        return;
    };
    let tools = pipeline::Tools {
        parser: parser.into(),
        grounder: grounder.into(),
    };
    let domain = PathBuf::from("examples/htn/interleave-domain.hddl");
    let problem = PathBuf::from("examples/htn/interleave-problem.hddl");
    let deadline = Some(Instant::now() + Duration::from_secs(30));
    let model = pipeline::load(
        pipeline::Input::Hddl {
            domain: &domain,
            problem: &problem,
        },
        &tools,
        deadline,
    )
    .unwrap();
    let result = search(
        &model,
        &Config {
            node_limit: Some(10_000),
            deadline,
            strategy: potoroo::htn::SearchStrategy::AStar,
            flaws: potoroo::htn::FlawSelection::Interleaved,
            ..Config::default()
        },
    )
    .unwrap();
    let Outcome::Solved(solution) = result.outcome else {
        panic!("expected solution")
    };
    let names: Vec<_> = solution
        .certificate
        .steps
        .iter()
        .map(|s| model.tasks()[s.task].name.as_str())
        .collect();
    assert_eq!(names, ["prepare[]", "consume[]", "finish[]"]);
    let root = std::env::temp_dir().join(format!("potoroo-htn-verify-{}", std::process::id()));
    fs::create_dir(&root).unwrap();
    let raw = root.join("raw.plan");
    let converted = root.join("converted.plan");
    fs::write(&raw, solution.certificate.to_panda(&model).unwrap()).unwrap();
    let conversion = Command::new(&tools.parser)
        .arg("--panda-converter")
        .arg(&raw)
        .arg(&converted)
        .output()
        .unwrap();
    assert!(
        conversion.status.success(),
        "{}",
        String::from_utf8_lossy(&conversion.stderr)
    );
    let checked = Command::new(&tools.parser)
        .args(["--verify=0", "--no-colour"])
        .arg(domain)
        .arg(problem)
        .arg(converted)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&checked.stdout);
    assert!(
        checked.status.success() && stdout.contains("Plan verification result: true"),
        "{stdout}\n{}",
        String::from_utf8_lossy(&checked.stderr)
    );
    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn external_failures_and_deadlines_are_distinct_from_search_exhaustion() {
    use std::os::unix::fs::PermissionsExt;
    let root = std::env::temp_dir().join(format!("potoroo htn tools {}", std::process::id()));
    fs::create_dir(&root).unwrap();
    let grounder = root.join("fake grounder");
    fs::write(
        &grounder,
        "#!/bin/sh\nprintf 'sentinel grounding failure\\n' >&2\nexit 9\n",
    )
    .unwrap();
    fs::set_permissions(&grounder, fs::Permissions::from_mode(0o700)).unwrap();
    let tools = pipeline::Tools {
        parser: root.join("absent"),
        grounder: grounder.clone(),
    };
    let lifted = root.join("input.htn");
    let failure = pipeline::load(pipeline::Input::Lifted(&lifted), &tools, None).unwrap_err();
    assert!(
        matches!(failure, pipeline::Error::Failed(ref text) if text.contains("sentinel grounding failure"))
    );
    fs::write(&grounder, "#!/bin/sh\nexec sleep 5\n").unwrap();
    let start = Instant::now();
    let timed = pipeline::load(
        pipeline::Input::Lifted(&lifted),
        &tools,
        Some(start + Duration::from_millis(50)),
    )
    .unwrap_err();
    assert!(matches!(timed, pipeline::Error::Deadline));
    assert!(start.elapsed() < Duration::from_secs(3));
    fs::remove_file(&grounder).unwrap();
    let missing = pipeline::load(pipeline::Input::Lifted(&lifted), &tools, None).unwrap_err();
    assert!(
        matches!(missing, pipeline::Error::Failed(ref text) if text.contains("could not run Malleefowl"))
    );
    fs::remove_dir_all(root).unwrap();
}
