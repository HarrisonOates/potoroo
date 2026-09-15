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
    let normalized = normalize(src);
    match parse_unit(&normalized) {
        Ok(unit) => Ok(unit),
        Err(original) => {
            // Retry on a repaired copy. Input that already parses never reaches
            // here, so the repair cannot regress a domain that works today.
            let repaired = repair(&normalized);
            if repaired == normalized {
                return Err(original);
            }
            // Report the original failure, not the repaired source's: the user
            // never saw the rewrite, so its offsets would be meaningless.
            parse_unit(&repaired).map_err(|_| original)
        }
    }
}

fn parse_unit(src: &str) -> Result<ParsedUnit, ReadError> {
    if looks_like_problem(src) {
        Problem::from_str(src)
            .map(ParsedUnit::Problem)
            .map_err(|e| parse_error(src, e))
    } else {
        Domain::from_str(src)
            .map(ParsedUnit::Domain)
            .map_err(|e| parse_error(src, e))
    }
}

/// Renders a `nom` failure as a line/column and a bounded excerpt.
///
/// `nom::error::Error`'s own `Display` prints an internal combinator name
/// followed by the entire unconsumed input, which for an IPC problem file is
/// megabytes of PDDL.
fn parse_error(src: &str, error: nom::Err<pddl::parsers::ParseError<'_>>) -> ReadError {
    let remainder = match &error {
        nom::Err::Error(e) | nom::Err::Failure(e) => Some(*e.input.fragment()),
        nom::Err::Incomplete(_) => None,
    };
    let Some(remainder) = remainder else {
        return ReadError::Parse("input ended before the form was complete".to_string());
    };
    let consumed = src.len().saturating_sub(remainder.len());
    let line = src[..consumed].matches('\n').count() + 1;
    let column = consumed - src[..consumed].rfind('\n').map_or(0, |i| i + 1) + 1;
    let excerpt: String = remainder.chars().take(60).collect();
    let excerpt = excerpt.replace('\n', " ");
    let ellipsis = if remainder.chars().count() > 60 {
        "..."
    } else {
        ""
    };
    ReadError::Parse(format!(
        "line {line}, column {column}: unexpected `{}{ellipsis}`",
        excerpt.trim_start()
    ))
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
            ')' => {
                while out.ends_with(char::is_whitespace) {
                    out.pop();
                }
            }
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

/// The `:require-key`s the `pddl` crate's grammar accepts. Any other tag fails
/// the whole `(:requirements ...)` form, and with it the file.
const KNOWN_REQUIREMENTS: &[&str] = &[
    ":strips",
    ":typing",
    ":negative-preconditions",
    ":disjunctive-preconditions",
    ":equality",
    ":existential-preconditions",
    ":universal-preconditions",
    ":quantified-preconditions",
    ":conditional-effects",
    ":fluents",
    ":numeric-fluents",
    ":object-fluents",
    ":adl",
    ":durative-actions",
    ":duration-inequalities",
    ":continuous-effects",
    ":derived-predicates",
    ":timed-initial-literals",
    ":preferences",
    ":constraints",
    ":action-costs",
];

/// The order the crate's domain grammar expects its sections in. It is
/// positional rather than free-form, so a domain that declares `:functions`
/// before `:predicates` fails to parse.
const DOMAIN_SECTIONS: &[&str] = &[
    "(:extends",
    "(:requirements",
    "(:types",
    "(:constants",
    "(:predicates",
    "(:functions",
    "(:constraints",
    "(:timeless",
];

/// The same for problems.
const PROBLEM_SECTIONS: &[&str] = &[
    "(:domain",
    "(:requirements",
    "(:objects",
    "(:init",
    "(:goal",
    "(:constraints",
    "(:metric",
    "(:length",
];

/// Splits a buffer into its top-level `(define ...)` units by paren balance.
///
/// The `pddl` crate's `from_str` discards whatever follows the form it parsed,
/// so a concatenated domain-then-problem stream silently yields only the
/// domain. Splitting first is what makes the documented stdin workflow work.
/// Returns one element (the whole input) when no complete form is found, so
/// malformed input still reaches the parser and produces its error.
pub fn split_units(src: &str) -> Vec<String> {
    let mut units = Vec::new();
    let stripped = strip_comments(src);
    let bytes: Vec<char> = stripped.chars().collect();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != '(' {
            index += 1;
            continue;
        }
        let start = index;
        let mut depth = 0usize;
        while index < bytes.len() {
            match bytes[index] {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        units.push(bytes[start..=index].iter().collect());
                        break;
                    }
                }
                _ => {}
            }
            index += 1;
        }
        if depth != 0 {
            // Unbalanced: leave the remainder to the parser's error reporting.
            break;
        }
        index += 1;
    }
    if units.is_empty() {
        vec![src.to_string()]
    } else {
        units
    }
}

/// Rewrites source the crate's grammar would reject but the PDDL spec allows:
/// drops unrecognised `:require-key`s, and puts the top-level sections into the
/// order the grammar expects. Applied only after a first parse attempt has
/// failed, so input that already parses is never touched.
fn repair(src: &str) -> String {
    reorder_sections(&drop_unknown_requirements(src))
}

/// Removes `:require-key`s outside [`KNOWN_REQUIREMENTS`]. An unknown tag would
/// otherwise fail the whole file; potoroo rejects features at their use site
/// anyway, so a tag it does not model is better ignored than fatal.
fn drop_unknown_requirements(src: &str) -> String {
    let Some(start) = src.find("(:requirements") else {
        return src.to_string();
    };
    let Some(length) = form_length(&src[start..]) else {
        return src.to_string();
    };
    let form = &src[start..start + length];
    let inner = &form["(:requirements".len()..form.len() - 1];
    let kept: Vec<&str> = inner
        .split_whitespace()
        .filter(|tag| KNOWN_REQUIREMENTS.contains(tag))
        .collect();
    let mut out = String::with_capacity(src.len());
    out.push_str(&src[..start]);
    out.push_str("(:requirements ");
    out.push_str(&kept.join(" "));
    out.push(')');
    out.push_str(&src[start + length..]);
    out
}

/// Reorders the top-level sections of a `(define ...)` form into the order the
/// crate's positional grammar expects, leaving the leading `(domain x)` /
/// `(problem x)` and every unrecognised form (actions, and anything else) in
/// their original relative positions after the sections.
fn reorder_sections(src: &str) -> String {
    let Some(open) = src.find("(define") else {
        return src.to_string();
    };
    let Some(length) = form_length(&src[open..]) else {
        return src.to_string();
    };
    let body = &src[open + "(define".len()..open + length - 1];
    let Some(forms) = top_level_forms(body) else {
        return src.to_string();
    };
    let Some((name, rest)) = forms.split_first() else {
        return src.to_string();
    };
    let sections = if looks_like_problem(src) {
        PROBLEM_SECTIONS
    } else {
        DOMAIN_SECTIONS
    };
    let key = |form: &str| {
        sections
            .iter()
            .position(|section| starts_section(form, section))
    };
    // A stable sort by section index keeps unrecognised forms (which sort last,
    // together) in their original order, so action order is preserved.
    let mut ordered: Vec<&str> = rest.to_vec();
    ordered.sort_by_key(|form| key(form).unwrap_or(sections.len()));

    let mut out = String::with_capacity(src.len());
    out.push_str(&src[..open]);
    out.push_str("(define ");
    out.push_str(name);
    for form in ordered {
        out.push('\n');
        out.push_str(form);
    }
    out.push_str("\n)");
    out.push_str(&src[open + length..]);
    out
}

/// Whether `form` opens with `section`, allowing space after the keyword only
/// at a token boundary (so `(:type` does not match `(:types`).
fn starts_section(form: &str, section: &str) -> bool {
    form.strip_prefix(section).is_some_and(|rest| {
        rest.is_empty() || rest.starts_with(|c: char| c.is_whitespace() || c == '(' || c == ')')
    })
}

/// The byte length of the parenthesised form starting at the front of `src`.
fn form_length(src: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (offset, c) in src.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(offset + c.len_utf8());
                }
            }
            _ => {}
        }
    }
    None
}

/// Splits a form's body into its top-level parenthesised forms. `None` when the
/// body holds anything but whitespace between them.
fn top_level_forms(body: &str) -> Option<Vec<&str>> {
    let mut forms = Vec::new();
    let mut rest = body.trim();
    while !rest.is_empty() {
        if !rest.starts_with('(') {
            return None;
        }
        let length = form_length(rest)?;
        forms.push(&rest[..length]);
        rest = rest[length..].trim();
    }
    Some(forms)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_buffer_holding_a_domain_and_a_problem_splits_into_two_units() {
        let src = "(define (domain d) (:predicates (p)))\n(define (problem q) (:domain d))";
        let units = split_units(src);
        assert_eq!(units.len(), 2);
        assert!(units[0].contains("domain d"));
        assert!(units[1].contains("problem q"));
    }

    #[test]
    fn splitting_leaves_unbalanced_input_to_the_parser() {
        // No complete form: the whole string comes back so the parse error is
        // reported against what the user actually wrote.
        let units = split_units("(define (domain d)");
        assert_eq!(units.len(), 1);
    }

    #[test]
    fn an_unknown_requirement_key_is_dropped_rather_than_failing_the_file() {
        let repaired =
            drop_unknown_requirements("(:requirements :strips :some-future-tag :typing)");
        assert_eq!(repaired, "(:requirements :strips :typing)");
    }

    #[test]
    fn domain_sections_are_reordered_into_the_grammar_order() {
        let src = "(define (domain d)\n(:functions (total-cost))\n(:predicates (p))\n)";
        let repaired = reorder_sections(src);
        let predicates = repaired.find("(:predicates").expect("predicates kept");
        let functions = repaired.find("(:functions").expect("functions kept");
        assert!(
            predicates < functions,
            "`:predicates` must precede `:functions`"
        );
    }

    #[test]
    fn reordering_preserves_the_order_of_the_actions() {
        let src = "(define (domain d)\n(:action b :parameters ())\n(:predicates (p))\n\
                   (:action a :parameters ())\n)";
        let repaired = reorder_sections(src);
        let first = repaired.find(":action b").expect("action b kept");
        let second = repaired.find(":action a").expect("action a kept");
        assert!(first < second, "actions must keep their declaration order");
    }

    #[test]
    fn a_domain_that_already_parses_is_left_alone() {
        let src = normalize("(define (domain d) (:requirements :strips) (:predicates (p)))");
        assert!(matches!(read_pddl(&src), Ok(ParsedUnit::Domain(_))));
    }
}
