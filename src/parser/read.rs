//! Thin wrapper over the `pddl` crate that classifies and parses a PDDL source
//! string into either a domain or a problem AST.

use pddl::parsers::Parser;
use pddl::{Domain, PddlFile, Problem};

/// A successfully parsed PDDL compilation unit.
pub enum ParsedUnit {
    Domain(Domain),
    Problem(Problem),
}

/// Error produced while reading PDDL source.
#[derive(Debug)]
pub enum ReadError {
    /// The source could not be parsed as either a domain or a problem.
    Parse(String),
}

impl std::fmt::Display for ReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReadError::Parse(msg) => write!(f, "parse error: {msg}"),
        }
    }
}

impl std::error::Error for ReadError {}

/// Parse exactly one domain or problem, letting the upstream parser determine
/// its kind. Use [`read_pddl_file`] for buffers containing several definitions.
pub fn read_pddl(src: &str) -> Result<ParsedUnit, ReadError> {
    let file = read_pddl_file(src)?;
    match (file.domains.len(), file.problems.len()) {
        (1, 0) => Ok(ParsedUnit::Domain(file.domains.into_iter().next().unwrap())),
        (0, 1) => Ok(ParsedUnit::Problem(file.problems.into_iter().next().unwrap())),
        (domains, problems) => Err(ReadError::Parse(format!(
            "expected exactly one domain or problem, found {domains} domains and {problems} problems"
        ))),
    }
}

/// Parse a buffer holding any number of `(define ...)` forms, such as a domain
/// and a problem piped together on stdin.
pub fn read_pddl_file(src: &str) -> Result<PddlFile, ReadError> {
    PddlFile::from_str(&fold_case(src)).map_err(|e| ReadError::Parse(e.to_string()))
}

/// Folds names to lower case. PDDL names are case-insensitive, and `pddl` keeps
/// the spelling as written (comparing case-insensitively), but potoroo's symbol
/// tables key on the string, so `NEXT`/`next` would otherwise become two
/// predicates. ASCII folding keeps byte offsets, so error positions still match.
fn fold_case(src: &str) -> String {
    src.to_ascii_lowercase()
}

#[cfg(test)]
mod tests {
    use super::*;

    const DOMAIN: &str = "(define (domain d) (:predicates (p)))";
    const PROBLEM: &str = "(define (problem q) (:domain d) (:init) (:goal (p)))";

    #[test]
    fn comments_cannot_change_the_definition_kind() {
        for comment in [
            "; Uses (domain d)\n",
            "; Example (problem q)\n",
            "; (define (domain fake))\n",
        ] {
            assert!(matches!(
                read_pddl(&format!("{comment}{DOMAIN}")),
                Ok(ParsedUnit::Domain(_))
            ));
            assert!(matches!(
                read_pddl(&format!("{comment}{PROBLEM}")),
                Ok(ParsedUnit::Problem(_))
            ));
        }
    }

    #[test]
    fn single_unit_reader_rejects_empty_or_multiple_definitions() {
        for src in [
            String::new(),
            "; comment only\n".into(),
            format!("{DOMAIN}\n{PROBLEM}"),
            format!("{DOMAIN}\n{DOMAIN}"),
            format!("{PROBLEM}\n{PROBLEM}"),
        ] {
            assert!(read_pddl(&src).is_err(), "accepted {src}");
        }
    }

    #[test]
    fn readers_reject_trailing_garbage_and_incomplete_definitions() {
        for src in [
            format!("{DOMAIN}\ngarbage"),
            format!("{DOMAIN}\n(define (problem"),
            "(define (domain".into(),
        ] {
            assert!(read_pddl(&src).is_err(), "accepted {src}");
            assert!(read_pddl_file(&src).is_err(), "accepted {src}");
        }
    }

    #[test]
    fn a_buffer_holding_a_domain_and_a_problem_reads_as_two_units() {
        let src = "(define (domain d) (:predicates (p)))\n(define (problem q) (:domain d) (:init) (:goal (p)))";
        let file = read_pddl_file(src).expect("parse");
        assert_eq!(file.domains.len(), 1);
        assert_eq!(file.problems.len(), 1);
    }

    #[test]
    fn names_are_folded_to_lower_case() {
        let Ok(ParsedUnit::Domain(d)) = read_pddl("(DEFINE (DOMAIN D) (:PREDICATES (NEXT)))")
        else {
            panic!("upper-case domain must parse");
        };
        assert_eq!(d.name().as_ref() as &str, "d");
    }
}
