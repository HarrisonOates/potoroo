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

/// Normalizes source for the `pddl` crate's stricter-than-spec parsers: folds
/// identifiers to lower case (PDDL names are case-insensitive; the symbol
/// tables downstream are not, so `NEXT`/`next` would otherwise become two
/// predicates), inserts a space before a `(` with no preceding separator
/// (`:parameters(...)`), and drops space before a `)` (`(at ?x ?y )`). Comments
/// are stripped first so a dangling `)` can't get pulled onto a comment line.
fn normalize(src: &str) -> String {
    let uncommented = strip_comments(&src.to_ascii_lowercase());
    let mut out = String::with_capacity(uncommented.len());
    let mut prev = '(';
    for c in uncommented.chars() {
        match c {
            '(' if prev != '(' && !prev.is_whitespace() => out.push(' '),
            ')' => while out.ends_with(char::is_whitespace) {
                out.pop();
            },
            _ => {}
        }
        out.push(c);
        prev = c;
    }
    out
}

/// Removes `;`-to-end-of-line comments, preserving the newlines so line numbers
/// in parse errors still line up with the input.
fn strip_comments(src: &str) -> String {
    let mut out = String::with_capacity(src.len());
    let mut in_comment = false;
    for c in src.chars() {
        match c {
            ';' => in_comment = true,
            '\n' => in_comment = false,
            _ => {}
        }
        if !in_comment {
            out.push(c);
        }
    }
    out
}

/// Heuristic classification: scan for `(define (problem` ignoring whitespace and
/// comments is overkill; the first occurrence of the `problem`/`domain` keyword
/// after `(define (` is sufficient for well-formed PDDL.
fn looks_like_problem(src: &str) -> bool {
    let lower = src.to_ascii_lowercase();
    match (
        lower.find("(define"),
        lower.find("(problem"),
        lower.find("(domain"),
    ) {
        (Some(_), Some(p), Some(d)) => p < d,
        (Some(_), Some(_), None) => true,
        _ => false,
    }
}
