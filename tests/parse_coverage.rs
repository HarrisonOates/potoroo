//! Parse-coverage smoke test: every classical `.pddl` file under `../examples`
//! must parse with the `pddl` crate. Files using deferred features (durative
//! actions, numeric fluents) are skipped — they are out of scope for the
//! classical subset.

use std::fs;
use std::path::{Path, PathBuf};

use potoroo::parser::read_pddl;

fn examples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("examples")
}

/// Requirements that put a file outside the classical subset.
fn is_deferred(src: &str) -> bool {
    let lower = src.to_ascii_lowercase();
    [
        ":durative-actions",
        ":duration-inequalities",
        ":timed-initial-literals",
        ":fluents",
        ":continuous-effects",
    ]
    .iter()
    .any(|r| lower.contains(r))
}

#[test]
fn all_classical_examples_parse() {
    let dir = examples_dir();
    let mut checked = 0usize;
    let mut skipped = Vec::new();
    let mut failures = Vec::new();

    for entry in fs::read_dir(&dir).expect("examples dir readable") {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("pddl") {
            continue;
        }
        let src = fs::read_to_string(&path).unwrap();
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        if is_deferred(&src) {
            skipped.push(name);
            continue;
        }
        match read_pddl(&src) {
            Ok(_) => checked += 1,
            Err(e) => failures.push(format!("{name}: {e}")),
        }
    }

    eprintln!("parsed {checked} classical files, skipped {} deferred", skipped.len());
    assert!(
        failures.is_empty(),
        "the following classical example files failed to parse:\n{}",
        failures.join("\n")
    );
    assert!(checked > 0, "expected to parse at least one example");
}
