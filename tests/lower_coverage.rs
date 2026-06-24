//! Lowering-coverage test: every classical `.pddl` file under `../examples`
//! must lower without error. Domains lower with `lower_domain`; problems lower
//! against their referenced domain with `lower_problem`.
//!
//! Files using deferred features (durative actions, numeric fluents, timed
//! initial literals, ...) are skipped, mirroring `parse_coverage.rs`. A problem
//! whose `:domain X` was not among the successfully-lowered classical domains is
//! skipped rather than failed.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use potoroo::domain::Domain;
use potoroo::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};

fn examples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("examples")
}

/// Requirements that put a file outside the classical subset (same skip logic
/// style as `parse_coverage.rs`).
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
fn all_classical_examples_lower() {
    let dir = examples_dir();

    // Gather classical .pddl files, partitioned into parsed domains and
    // parsed problems.
    let mut parsed_domains: Vec<(String, pddl::Domain)> = Vec::new();
    let mut parsed_problems: Vec<(String, pddl::Problem)> = Vec::new();
    let mut skipped = 0usize;
    let mut parse_failures = Vec::new();

    for entry in fs::read_dir(&dir).expect("examples dir readable") {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("pddl") {
            continue;
        }
        let src = fs::read_to_string(&path).unwrap();
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        if is_deferred(&src) {
            skipped += 1;
            continue;
        }
        match read_pddl(&src) {
            Ok(ParsedUnit::Domain(d)) => parsed_domains.push((name, d)),
            Ok(ParsedUnit::Problem(p)) => parsed_problems.push((name, p)),
            Err(e) => parse_failures.push(format!("{name}: {e}")),
        }
    }

    assert!(
        parse_failures.is_empty(),
        "classical files failed to parse (fix parse_coverage first):\n{}",
        parse_failures.join("\n")
    );

    // Lower domains, indexing successfully-lowered ones by their PDDL name.
    let mut lower_failures = Vec::new();
    let mut domains_by_name: HashMap<String, Domain> = HashMap::new();
    let mut lowered_domains = 0usize;
    for (file, d) in &parsed_domains {
        match lower_domain(d) {
            Ok(dom) => {
                lowered_domains += 1;
                domains_by_name.insert(dom.name.clone(), dom);
            }
            Err(e) => lower_failures.push(format!("domain {file}: {e}")),
        }
    }

    // Lower problems against their referenced domain.
    let mut lowered_problems = 0usize;
    let mut skipped_problems = 0usize;
    for (file, p) in &parsed_problems {
        let dom_name = p.domain().as_ref().to_string();
        match domains_by_name.get(&dom_name) {
            Some(dom) => match lower_problem(p, dom) {
                Ok(_) => lowered_problems += 1,
                Err(e) => lower_failures.push(format!("problem {file} (domain {dom_name}): {e}")),
            },
            // The referenced domain wasn't in the classical set; skip.
            None => skipped_problems += 1,
        }
    }

    eprintln!(
        "lowered {lowered_domains} domains, {lowered_problems} problems; \
         skipped {skipped} deferred files, {skipped_problems} problems without a matching domain"
    );

    assert!(
        lower_failures.is_empty(),
        "the following classical example files failed to lower:\n{}",
        lower_failures.join("\n")
    );
    assert!(lowered_domains > 0, "expected to lower at least one domain");
    assert!(lowered_problems > 0, "expected to lower at least one problem");
}
