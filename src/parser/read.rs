//! Thin wrapper over the `pddl` crate that classifies and parses a PDDL source
//! string into either a domain or a problem AST.

use pddl::parsers::Parser;
use pddl::{Domain, Problem};

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
    let src = normalize(src);
    let src = src.as_str();
    if looks_like_problem(src) {
        Problem::from_str(src)
            .map(ParsedUnit::Problem)
            .map_err(|e| ReadError::Parse(format!("{e}")))
    } else {
        Domain::from_str(src)
            .map(ParsedUnit::Domain)
            .map_err(|e| ReadError::Parse(format!("{e}")))
    }
}

/// Normalize source so the `pddl` crate's whitespace-separated list parsers
/// accept VHPOP-permissive input. VHPOP (and the PDDL spec) treat `(` and `)`
/// as self-delimiting tokens, so adjacent forms like `(a ?x)(b ?y)` are legal;
/// the `pddl` crate's `nom` lists require a separator. PDDL has no string
/// literals, so a `)(` sequence is always a token boundary and inserting a space
/// there is semantically harmless (including inside `;` comments).
fn normalize(src: &str) -> String {
    src.replace(")(", ") (")
}

/// Heuristic classification: scan for `(define (problem` ignoring whitespace and
/// comments is overkill; the first occurrence of the `problem`/`domain` keyword
/// after `(define (` is sufficient for well-formed PDDL.
fn looks_like_problem(src: &str) -> bool {
    let lower = src.to_ascii_lowercase();
    match (lower.find("(define"), lower.find("(problem"), lower.find("(domain")) {
        (Some(_), Some(p), Some(d)) => p < d,
        (Some(_), Some(_), None) => true,
        _ => false,
    }
}
