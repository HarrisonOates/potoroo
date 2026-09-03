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

/// Normalize source so the `pddl` crate's parsers accept permissive PDDL input.
///
/// The spec treats `(` and `)` as self-delimiting tokens, so a token boundary
/// needs no whitespace and stray whitespace at one is insignificant. The `pddl`
/// crate's `nom` parsers are stricter: they require a separator between
/// adjacent forms and reject padding before a closing paren. IPC 2023 exercises
/// both — labyrinth writes `:parameters(...)` and `(card-at ?cm ?x ?y )`.
///
/// So this inserts a space before any `(` that is not already preceded by
/// whitespace or `(`, and drops whitespace before any `)`. PDDL has no string
/// literals, so no parenthesis can occur inside a token and both rewrites are
/// semantically inert.
///
/// Names are also folded to lower case. PDDL identifiers -- types, constants,
/// predicates, functions, variables, and action names alike -- are
/// case-insensitive, but the symbol tables downstream key on the exact string,
/// so `(NEXT ?p1 ?p2)` declared and `(next ?x ?y)` used would silently become
/// two predicates. IPC 2023's labyrinth does exactly that. Folding here is
/// total, which is what makes it safe: no lookup path can be missed. Nothing
/// else in PDDL is case-sensitive, so only the spelling of names in output
/// changes, and every mainstream planner and VAL fold the same way.
///
/// Comments are deleted first (keeping their terminating newline). They must
/// not survive: deleting the whitespace before a `)` could otherwise pull the
/// paren onto the end of a comment line and swallow it.
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
