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

/// Parse a PDDL source string, auto-detecting whether it declares a domain or a
/// problem from the leading `(define (domain ...))` / `(define (problem ...))`.
pub fn read_pddl(src: &str) -> Result<ParsedUnit, ReadError> {
    let src = fold_case(src);
    if looks_like_problem(&src) {
        Problem::from_str(&src).map(ParsedUnit::Problem)
    } else {
        Domain::from_str(&src).map(ParsedUnit::Domain)
    }
    .map_err(|e| ReadError::Parse(e.to_string()))
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

/// Heuristic classification: scan for `(define (problem` ignoring whitespace and
/// comments is overkill; the first occurrence of the `problem`/`domain` keyword
/// after `(define (` is sufficient for well-formed PDDL. Expects folded source.
fn looks_like_problem(src: &str) -> bool {
    match (
        src.find("(define"),
        src.find("(problem"),
        src.find("(domain"),
    ) {
        (Some(_), Some(p), Some(d)) => p < d,
        (Some(_), Some(_), None) => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
