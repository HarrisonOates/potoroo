//! Lifted fact-alternating mutex groups
//! (Fišer, AAAI 2020; Helmert, Artificial Intelligence 2009).
//!
//! Each group allows at most one member per invariant-parameter assignment.
//! Candidates must hold initially, and every add must be balanced by a
//! required delete under the same assignment.
//!
//! Reject groups with conditional or quantified effects, multiple adds,
//! unbound invariant parameters, unmatched deletes, or non-entailed
//! preconditions. Candidate and group-size limits safely weaken pruning
//! by omitting groups.

use std::collections::HashMap;
use std::rc::Rc;

use crate::action::ActionSchema;
use crate::domain::Domain;
use crate::effect::Effect;
use crate::formula::{Atom, Formula, Literal};
use crate::predicates::Predicate;
use crate::problem::Problem;
use crate::terms::Term;

/// A predicate with one counted argument position: for each assignment of the
/// other positions, at most one instance holds in any reachable state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LiftedMutexGroup {
    pub predicate: Predicate,
    pub counted: usize,
}

/// The lifted mutex groups of a domain and problem.
#[derive(Debug, Default)]
pub struct LiftedMutexes {
    /// Counted positions per predicate. A predicate with no valid candidate is
    /// absent, so the common case is one lookup that misses.
    by_predicate: HashMap<Predicate, Vec<usize>>,
    groups: Vec<LiftedMutexGroup>,
}

impl LiftedMutexes {
    /// Synthesises every single-predicate group the schemas and initial state
    /// admit.
    pub fn synthesise(domain: &Domain, problem: &Problem) -> Self {
        let mut groups = Vec::new();
        let mut by_predicate: HashMap<Predicate, Vec<usize>> = HashMap::new();

        for index in 0..domain.predicates.len() {
            let predicate = Predicate(index as u32);
            let arity = domain.predicates.parameters(predicate).len();
            for counted in 0..arity {
                let candidate = LiftedMutexGroup { predicate, counted };
                if !initially_true(candidate, problem) {
                    continue;
                }
                if !domain
                    .actions
                    .iter()
                    .all(|schema| preserved_by(candidate, schema))
                {
                    continue;
                }
                groups.push(candidate);
                by_predicate.entry(predicate).or_default().push(counted);
            }
        }

        LiftedMutexes {
            by_predicate,
            groups,
        }
    }

    /// Every group found, for tests and reporting.
    pub fn groups(&self) -> &[LiftedMutexGroup] {
        &self.groups
    }

    /// Whether two atoms can never hold in the same reachable state.
    ///
    /// Both must be ground at every position the comparison reads; a term still
    /// carrying a variable makes the answer "not known to be mutex", which is
    /// the safe direction.
    pub fn mutex(&self, left: &Atom, right: &Atom) -> bool {
        if left.predicate != right.predicate || left.terms.len() != right.terms.len() {
            return false;
        }
        let Some(counted_positions) = self.by_predicate.get(&left.predicate) else {
            return false;
        };
        counted_positions.iter().any(|&counted| {
            // Differ where the group counts...
            let differs = match (left.terms.get(counted), right.terms.get(counted)) {
                (Some(Term::Object(a)), Some(Term::Object(b))) => a != b,
                _ => false,
            };
            if !differs {
                return false;
            }
            // ...and agree everywhere it does not.
            left.terms
                .iter()
                .zip(&right.terms)
                .enumerate()
                .all(|(position, (a, b))| {
                    if position == counted {
                        return true;
                    }
                    matches!((a, b), (Term::Object(x), Term::Object(y)) if x == y)
                })
        })
    }

    /// Whether two literals are mutex. Only two positive literals can be: a
    /// negative one is a statement about a fact's absence, which no group
    /// constrains.
    pub fn literals_mutex(&self, left: &Literal, right: &Literal) -> bool {
        match (left, right) {
            (Literal::Atom(a), Literal::Atom(b)) => self.mutex(a, b),
            _ => false,
        }
    }

    /// Whether a set of ground atoms contains a mutex pair. Cutsets stay small,
    /// so the quadratic scan beats building an index.
    pub fn inconsistent(&self, atoms: &[Atom]) -> bool {
        if self.groups.is_empty() {
            return false;
        }
        for (i, left) in atoms.iter().enumerate() {
            for right in &atoms[i + 1..] {
                if self.mutex(left, right) {
                    return true;
                }
            }
        }
        false
    }

    pub fn is_empty(&self) -> bool {
        self.groups.is_empty()
    }
}

/// Whether at most one instance per fixed-argument tuple holds initially.
fn initially_true(candidate: LiftedMutexGroup, problem: &Problem) -> bool {
    let instances: Vec<&Atom> = problem
        .init_order
        .iter()
        .filter(|atom| atom.predicate == candidate.predicate)
        .collect();
    for (i, left) in instances.iter().enumerate() {
        for right in &instances[i + 1..] {
            if left.terms.len() != right.terms.len() {
                continue;
            }
            let same_fixed = left
                .terms
                .iter()
                .zip(&right.terms)
                .enumerate()
                .all(|(position, (a, b))| position == candidate.counted || a == b);
            let differs = left.terms.get(candidate.counted) != right.terms.get(candidate.counted);
            if same_fixed && differs {
                return false;
            }
        }
    }
    true
}

/// Whether a schema preserves the candidate — the fact-alternating check.
fn preserved_by(candidate: LiftedMutexGroup, schema: &ActionSchema) -> bool {
    let touching: Vec<&Rc<Effect>> = schema
        .effects
        .iter()
        .filter(|effect| effect.literal.atom().predicate == candidate.predicate)
        .collect();
    if touching.is_empty() {
        return true;
    }
    // A conditional or quantified effect on the predicate may fire without its
    // partner, or fire many times. Decline rather than reason about it.
    if touching
        .iter()
        .any(|effect| effect.conditional() || !effect.parameters.is_empty())
    {
        return false;
    }

    let adds: Vec<&Atom> = touching
        .iter()
        .filter_map(|effect| match &effect.literal {
            Literal::Atom(atom) => Some(atom),
            Literal::Negation(_) => None,
        })
        .collect();
    if adds.is_empty() {
        // Deletes only: the count can fall but never rise.
        return true;
    }
    if adds.len() > 1 {
        // Two adds might land in the same group under some binding.
        return false;
    }
    let added = adds[0];

    let deletes: Vec<&Atom> = touching
        .iter()
        .filter_map(|effect| match &effect.literal {
            Literal::Negation(atom) => Some(atom),
            Literal::Atom(_) => None,
        })
        .collect();

    let mut entailed = Vec::new();
    collect_entailed_atoms(&schema.precondition, &mut entailed);

    deletes.iter().any(|deleted| {
        same_fixed_arguments(candidate, added, deleted)
            && entailed.iter().any(|required| {
                required.predicate == deleted.predicate && required.terms == deleted.terms
            })
    })
}

/// Whether two atoms carry syntactically identical terms at every fixed
/// position of the group, so they always belong to the same instance of it.
fn same_fixed_arguments(candidate: LiftedMutexGroup, added: &Atom, deleted: &Atom) -> bool {
    added.terms.len() == deleted.terms.len()
        && added
            .terms
            .iter()
            .zip(&deleted.terms)
            .enumerate()
            .all(|(position, (a, b))| position == candidate.counted || a == b)
}

/// Collects the positive atoms a precondition entails: the top-level
/// conjunction, and existential bodies. A disjunct or a negated atom is not
/// guaranteed and contributes nothing.
fn collect_entailed_atoms(formula: &Rc<Formula>, out: &mut Vec<Atom>) {
    match formula.as_ref() {
        Formula::Atom(atom) => out.push(atom.clone()),
        Formula::Conjunction(parts) => {
            for part in parts {
                collect_entailed_atoms(part, out);
            }
        }
        Formula::Exists { body, .. } => collect_entailed_atoms(body, out),
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};

    struct Fixture {
        domain: Domain,
        problem: Problem,
    }

    impl Fixture {
        fn new(domain_src: &str, problem_src: &str) -> Self {
            let domain = match read_pddl(domain_src).expect("parse domain") {
                ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
                _ => panic!("expected a domain"),
            };
            let problem = match read_pddl(problem_src).expect("parse problem") {
                ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
                _ => panic!("expected a problem"),
            };
            Fixture { domain, problem }
        }

        fn mutexes(&self) -> LiftedMutexes {
            LiftedMutexes::synthesise(&self.domain, &self.problem)
        }

        fn object(&self, name: &str) -> Term {
            Term::Object(
                self.problem
                    .objects
                    .find_object(Some(&self.domain.constants), name)
                    .unwrap_or_else(|| panic!("object `{name}` is declared")),
            )
        }

        fn atom(&self, predicate: &str, args: &[&str]) -> Atom {
            Atom {
                predicate: self
                    .domain
                    .predicates
                    .find_predicate(predicate)
                    .unwrap_or_else(|| panic!("predicate `{predicate}` is declared")),
                terms: args.iter().map(|name| self.object(name)).collect(),
            }
        }
    }

    const TRAVEL_DOMAIN: &str = r#"
    (define (domain travel)
      (:requirements :strips :typing)
      (:types loc vehicle)
      (:predicates (at ?v - vehicle ?l - loc)
                   (road ?a - loc ?b - loc)
                   (visited ?l - loc))
      (:action drive
        :parameters (?v - vehicle ?from - loc ?to - loc)
        :precondition (and (at ?v ?from) (road ?from ?to))
        :effect (and (not (at ?v ?from)) (at ?v ?to) (visited ?to))))
    "#;

    const TRAVEL_PROBLEM: &str = r#"
    (define (problem t1)
      (:domain travel)
      (:objects a b c - loc truck van - vehicle)
      (:init (at truck a) (at van b) (road a b) (road b c))
      (:goal (at truck c)))
    "#;

    #[test]
    fn a_vehicle_is_at_one_location() {
        let fixture = Fixture::new(TRAVEL_DOMAIN, TRAVEL_PROBLEM);
        let mutexes = fixture.mutexes();
        // `drive` deletes (at ?v ?from), which is a precondition, and adds
        // (at ?v ?to) with the same vehicle: the group is preserved.
        assert!(mutexes.mutex(
            &fixture.atom("at", &["truck", "a"]),
            &fixture.atom("at", &["truck", "b"])
        ));
    }

    #[test]
    fn two_vehicles_at_different_places_are_not_mutex() {
        let fixture = Fixture::new(TRAVEL_DOMAIN, TRAVEL_PROBLEM);
        let mutexes = fixture.mutexes();
        assert!(!mutexes.mutex(
            &fixture.atom("at", &["truck", "a"]),
            &fixture.atom("at", &["van", "b"])
        ));
        // Same atom twice is not a mutex either.
        assert!(!mutexes.mutex(
            &fixture.atom("at", &["truck", "a"]),
            &fixture.atom("at", &["truck", "a"])
        ));
    }

    #[test]
    fn counting_the_vehicle_is_rejected_by_the_initial_state() {
        let fixture = Fixture::new(TRAVEL_DOMAIN, TRAVEL_PROBLEM);
        let mutexes = fixture.mutexes();
        // Counting position 0 would claim one vehicle per location, which the
        // initial state does not refute here — but `drive` adds (at ?v ?to)
        // while deleting (at ?v ?from), whose *fixed* position under that
        // reading is ?to vs ?from. They are different terms, so the candidate
        // is rejected, and two vehicles may share a location.
        assert!(!mutexes.mutex(
            &fixture.atom("at", &["truck", "a"]),
            &fixture.atom("at", &["van", "a"])
        ));
    }

    #[test]
    fn a_monotone_predicate_yields_no_group() {
        let fixture = Fixture::new(TRAVEL_DOMAIN, TRAVEL_PROBLEM);
        let mutexes = fixture.mutexes();
        // `visited` is only ever added, so nothing bounds how many hold.
        assert!(!mutexes.mutex(
            &fixture.atom("visited", &["a"]),
            &fixture.atom("visited", &["b"])
        ));
    }

    #[test]
    fn an_unpaired_delete_rejects_the_candidate() {
        // `teleport` adds (at ?v ?to) without deleting anything, so two
        // locations could hold at once and the group must be refused.
        let domain_src = r#"
        (define (domain leaky)
          (:requirements :strips :typing)
          (:types loc vehicle)
          (:predicates (at ?v - vehicle ?l - loc))
          (:action teleport
            :parameters (?v - vehicle ?to - loc)
            :precondition ()
            :effect (at ?v ?to)))
        "#;
        let problem_src = r#"
        (define (problem p1)
          (:domain leaky)
          (:objects a b - loc truck - vehicle)
          (:init (at truck a))
          (:goal (at truck b)))
        "#;
        let fixture = Fixture::new(domain_src, problem_src);
        let mutexes = fixture.mutexes();
        assert!(!mutexes.mutex(
            &fixture.atom("at", &["truck", "a"]),
            &fixture.atom("at", &["truck", "b"])
        ));
    }

    #[test]
    fn a_delete_that_is_not_a_precondition_rejects_the_candidate() {
        // `jump` deletes (at ?v ?from) but never required it, so it can add a
        // second location while the first survives.
        let domain_src = r#"
        (define (domain leaky2)
          (:requirements :strips :typing)
          (:types loc vehicle)
          (:predicates (at ?v - vehicle ?l - loc) (ready ?v - vehicle))
          (:action jump
            :parameters (?v - vehicle ?from - loc ?to - loc)
            :precondition (ready ?v)
            :effect (and (not (at ?v ?from)) (at ?v ?to))))
        "#;
        let problem_src = r#"
        (define (problem p1)
          (:domain leaky2)
          (:objects a b - loc truck - vehicle)
          (:init (at truck a) (ready truck))
          (:goal (at truck b)))
        "#;
        let fixture = Fixture::new(domain_src, problem_src);
        let mutexes = fixture.mutexes();
        assert!(!mutexes.mutex(
            &fixture.atom("at", &["truck", "a"]),
            &fixture.atom("at", &["truck", "b"])
        ));
    }

    #[test]
    fn a_contradictory_initial_state_rejects_the_candidate() {
        let problem_src = r#"
        (define (problem t2)
          (:domain travel)
          (:objects a b - loc truck - vehicle)
          (:init (at truck a) (at truck b) (road a b))
          (:goal (at truck b)))
        "#;
        let fixture = Fixture::new(TRAVEL_DOMAIN, problem_src);
        let mutexes = fixture.mutexes();
        assert!(!mutexes.mutex(
            &fixture.atom("at", &["truck", "a"]),
            &fixture.atom("at", &["truck", "b"])
        ));
    }

    /// A static predicate with a single initial instance is a genuine invariant
    /// — nothing ever adds a second — and the synthesis finds it. Sound, and
    /// occasionally useful: it makes a plan that needs two different roads out
    /// of the same location provably unrefinable.
    #[test]
    fn a_static_predicate_can_carry_a_group() {
        let problem_src = r#"
        (define (problem t3)
          (:domain travel)
          (:objects a b c - loc truck - vehicle)
          (:init (at truck a) (road a b))
          (:goal (at truck b)))
        "#;
        let fixture = Fixture::new(TRAVEL_DOMAIN, problem_src);
        let mutexes = fixture.mutexes();
        assert!(mutexes.mutex(
            &fixture.atom("road", &["a", "b"]),
            &fixture.atom("road", &["a", "c"])
        ));
    }
}
