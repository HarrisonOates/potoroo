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

use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

use crate::action::ActionSchema;
use crate::domain::Domain;
use crate::formula::{Atom, Formula, Literal};
use crate::predicates::Predicate;
use crate::problem::Problem;
use crate::terms::{Object, Term};

/// Most parts one group may grow to. Three covers the published invariants
/// (`at`/`in`, `at`/`on`); beyond that the candidate space grows faster than
/// the groups justify.
const MAX_PARTS: usize = 3;

/// Most candidates the refinement loop will test, over the whole synthesis.
const MAX_CANDIDATES: usize = 4_000;

/// What one argument position of a part holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Slot {
    /// An invariant parameter, shared across the group's parts.
    Param(usize),
    /// A fixed object.
    Const(Object),
    /// Unconstrained: a position the group counts over.
    Counted,
}

/// One lifted atom of a group.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Part {
    predicate: Predicate,
    slots: Vec<Slot>,
}

/// A set of lifted atoms of which at most one holds, per assignment of the
/// invariant parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MutexGroup {
    arity: usize,
    parts: Vec<Part>,
}

impl MutexGroup {
    /// Number of lifted atoms in the group.
    pub fn len(&self) -> usize {
        self.parts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.parts.is_empty()
    }

    /// The predicates the group covers, sorted, for tests and reporting.
    pub fn predicates(&self) -> Vec<Predicate> {
        let mut seen: Vec<Predicate> = self.parts.iter().map(|part| part.predicate).collect();
        seen.sort_by_key(|predicate| predicate.0);
        seen.dedup();
        seen
    }

    /// A canonical key for deduplicating candidates.
    fn key(&self) -> (usize, Vec<Part>) {
        let mut parts = self.parts.clone();
        parts.sort();
        (self.arity, parts)
    }
}

/// The lifted mutex groups of a domain and problem.
#[derive(Debug, Default)]
pub struct LiftedMutexes {
    groups: Vec<MutexGroup>,
    /// `(group index, part index)` pairs per predicate, so a query only looks at
    /// groups that could cover the atom.
    by_predicate: HashMap<Predicate, Vec<(usize, usize)>>,
}

impl LiftedMutexes {
    /// Synthesises the groups the schemas and initial state admit.
    pub fn synthesise(domain: &Domain, problem: &Problem) -> Self {
        let schemas: Vec<SchemaFacts> = domain.actions.iter().map(SchemaFacts::new).collect();

        let mut queue: VecDeque<MutexGroup> = VecDeque::new();
        let mut seen: HashSet<(usize, Vec<Part>)> = HashSet::new();
        for index in 0..domain.predicates.len() {
            let predicate = Predicate(index as u32);
            let arity = domain.predicates.parameters(predicate).len();
            for counted in 0..arity {
                let mut slots = Vec::with_capacity(arity);
                let mut next_param = 0;
                for position in 0..arity {
                    if position == counted {
                        slots.push(Slot::Counted);
                    } else {
                        slots.push(Slot::Param(next_param));
                        next_param += 1;
                    }
                }
                let candidate = MutexGroup {
                    arity: next_param,
                    parts: vec![Part { predicate, slots }],
                };
                if seen.insert(candidate.key()) {
                    queue.push_back(candidate);
                }
            }
        }

        let mut groups: Vec<MutexGroup> = Vec::new();
        let mut tested = 0usize;
        while let Some(candidate) = queue.pop_front() {
            tested += 1;
            if tested > MAX_CANDIDATES {
                break;
            }
            if !initially_true(&candidate, problem) {
                continue;
            }
            match balance(&candidate, &schemas) {
                Balance::Preserved => groups.push(candidate),
                Balance::Rejected => {}
                Balance::Unbalanced { refinements } => {
                    if candidate.parts.len() >= MAX_PARTS {
                        continue;
                    }
                    for part in refinements {
                        if candidate.parts.contains(&part) {
                            continue;
                        }
                        let mut refined = candidate.clone();
                        refined.parts.push(part);
                        if seen.insert(refined.key()) {
                            queue.push_back(refined);
                        }
                    }
                }
            }
        }

        // Smallest first: a query that succeeds tends to succeed on the
        // cheapest group.
        groups.sort_by_key(MutexGroup::len);

        let mut by_predicate: HashMap<Predicate, Vec<(usize, usize)>> = HashMap::new();
        for (group_index, group) in groups.iter().enumerate() {
            for (part_index, part) in group.parts.iter().enumerate() {
                by_predicate
                    .entry(part.predicate)
                    .or_default()
                    .push((group_index, part_index));
            }
        }

        LiftedMutexes {
            groups,
            by_predicate,
        }
    }

    /// Every group found, for tests and reporting.
    pub fn groups(&self) -> &[MutexGroup] {
        &self.groups
    }

    pub fn is_empty(&self) -> bool {
        self.groups.is_empty()
    }

    /// Whether two atoms can never hold in the same reachable state.
    ///
    /// Both must be ground where the comparison reads them; a term still
    /// carrying a variable makes the answer "not known to be mutex", which is
    /// the safe direction.
    pub fn mutex(&self, left: &Atom, right: &Atom) -> bool {
        if left == right {
            return false;
        }
        let (Some(left_parts), Some(right_parts)) = (
            self.by_predicate.get(&left.predicate),
            self.by_predicate.get(&right.predicate),
        ) else {
            return false;
        };
        for &(group_index, left_part) in left_parts {
            for &(other_group, right_part) in right_parts {
                if other_group != group_index {
                    continue;
                }
                let group = &self.groups[group_index];
                let mut binding: Vec<Option<Object>> = vec![None; group.arity];
                if match_ground(&group.parts[left_part], left, &mut binding)
                    && match_ground(&group.parts[right_part], right, &mut binding)
                {
                    return true;
                }
            }
        }
        false
    }

    /// Whether two literals are mutex. Only two positive literals can be: a
    /// negative one asserts a fact's absence, which no group constrains.
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
}

/// Resolves an atom's terms through a plan's binding constraints, returning it
/// only once every term has reached an object.
///
/// A lifted mutex group compares objects, so an atom still carrying a variable
/// cannot be asked about — the answer is "not known to be mutex", which is the
/// safe direction for every caller.
pub fn ground_atom(
    bindings: &crate::bindings::Bindings,
    atom: &Atom,
    step_id: usize,
) -> Option<Atom> {
    let mut terms = Vec::with_capacity(atom.terms.len());
    for &term in &atom.terms {
        match bindings.binding(term, step_id) {
            Term::Object(object) => terms.push(Term::Object(object)),
            Term::Variable(_) => return None,
        }
    }
    Some(Atom {
        predicate: atom.predicate,
        terms,
    })
}

/// Matches a ground atom against a part, extending `binding`.
///
/// `binding` is left modified on failure, so a caller that tries several parts
/// must start each attempt from a fresh one.
fn match_ground(part: &Part, atom: &Atom, binding: &mut [Option<Object>]) -> bool {
    if part.predicate != atom.predicate || part.slots.len() != atom.terms.len() {
        return false;
    }
    for (slot, term) in part.slots.iter().zip(&atom.terms) {
        match slot {
            Slot::Counted => {}
            Slot::Const(expected) => {
                if *term != Term::Object(*expected) {
                    return false;
                }
            }
            Slot::Param(index) => {
                let Term::Object(object) = term else {
                    return false;
                };
                match binding[*index] {
                    Some(bound) if bound != *object => return false,
                    Some(_) => {}
                    None => binding[*index] = Some(*object),
                }
            }
        }
    }
    true
}

/// Matches a schema's atom — whose terms may be variables — against a part,
/// extending the lifted assignment `sigma`.
fn match_lifted(part: &Part, atom: &Atom, sigma: &mut [Option<Term>]) -> bool {
    if part.predicate != atom.predicate || part.slots.len() != atom.terms.len() {
        return false;
    }
    for (slot, term) in part.slots.iter().zip(&atom.terms) {
        match slot {
            Slot::Counted => {}
            Slot::Const(expected) => {
                if *term != Term::Object(*expected) {
                    return false;
                }
            }
            Slot::Param(index) => match sigma[*index] {
                Some(bound) if bound != *term => return false,
                Some(_) => {}
                None => sigma[*index] = Some(*term),
            },
        }
    }
    true
}

/// Whether at most one atom of the group holds initially, for every assignment.
fn initially_true(group: &MutexGroup, problem: &Problem) -> bool {
    let relevant: Vec<&Atom> = problem
        .init_order
        .iter()
        .filter(|atom| {
            group
                .parts
                .iter()
                .any(|part| part.predicate == atom.predicate)
        })
        .collect();
    for (i, left) in relevant.iter().enumerate() {
        for right in &relevant[i + 1..] {
            if left == right {
                continue;
            }
            for left_part in &group.parts {
                for right_part in &group.parts {
                    let mut binding: Vec<Option<Object>> = vec![None; group.arity];
                    if match_ground(left_part, left, &mut binding)
                        && match_ground(right_part, right, &mut binding)
                    {
                        return false;
                    }
                }
            }
        }
    }
    true
}

/// The outcome of testing a candidate against every schema.
enum Balance {
    /// Every schema preserves the group.
    Preserved,
    /// Some schema rules the candidate out outright; refining cannot help.
    Rejected,
    /// A schema adds into the group with nothing to pair against. Each listed
    /// part would account for that add if the group contained it.
    Unbalanced { refinements: Vec<Part> },
}

/// The pieces of a schema the balance check reads, extracted once.
struct SchemaFacts {
    /// Unconditional, unquantified positive effect atoms.
    adds: Vec<Atom>,
    /// Unconditional, unquantified negative effect atoms.
    deletes: Vec<Atom>,
    /// Predicates touched by a conditional or quantified effect, either polarity.
    uncertain: HashSet<Predicate>,
    /// Positive atoms the precondition entails.
    required: Vec<Atom>,
}

impl SchemaFacts {
    fn new(schema: &ActionSchema) -> Self {
        let mut adds = Vec::new();
        let mut deletes = Vec::new();
        let mut uncertain = HashSet::new();
        for effect in &schema.effects {
            let atom = effect.literal.atom().clone();
            if effect.conditional() || !effect.parameters.is_empty() {
                uncertain.insert(atom.predicate);
                continue;
            }
            match &effect.literal {
                Literal::Atom(_) => adds.push(atom),
                Literal::Negation(_) => deletes.push(atom),
            }
        }
        let mut required = Vec::new();
        collect_entailed_atoms(&schema.precondition, &mut required);
        SchemaFacts {
            adds,
            deletes,
            uncertain,
            required,
        }
    }
}

fn balance(group: &MutexGroup, schemas: &[SchemaFacts]) -> Balance {
    let mut refinements: Vec<Part> = Vec::new();
    let mut unbalanced = false;

    for schema in schemas {
        if group
            .parts
            .iter()
            .any(|part| schema.uncertain.contains(&part.predicate))
        {
            return Balance::Rejected;
        }

        // The ways this schema adds into the group, and the assignment each
        // lands under.
        let mut entering: Vec<Vec<Option<Term>>> = Vec::new();
        for added in &schema.adds {
            for part in &group.parts {
                let mut sigma: Vec<Option<Term>> = vec![None; group.arity];
                if match_lifted(part, added, &mut sigma) {
                    entering.push(sigma);
                }
            }
        }
        if entering.is_empty() {
            continue;
        }
        if entering.len() > 1 {
            // Two ways into the group at once. Rather than prove they land
            // under different assignments, decline.
            return Balance::Rejected;
        }
        let sigma = &entering[0];
        if sigma.iter().any(Option::is_none) {
            // The atom enters the group for every value of some parameter; no
            // single delete balances that.
            return Balance::Rejected;
        }

        // A delete from the group under the same assignment, which the schema
        // also required.
        let paired = schema.deletes.iter().any(|deleted| {
            if !schema.required.contains(deleted) {
                return false;
            }
            group.parts.iter().any(|part| {
                let mut check = sigma.clone();
                match_lifted(part, deleted, &mut check) && check == *sigma
            })
        });
        if paired {
            continue;
        }

        unbalanced = true;
        for deleted in &schema.deletes {
            if !schema.required.contains(deleted) {
                continue;
            }
            refinements.push(derive_part(deleted, sigma));
        }
    }

    if unbalanced {
        Balance::Unbalanced { refinements }
    } else {
        Balance::Preserved
    }
}

/// Builds the part that would let `deleted` account for an add under `sigma`.
///
/// A term the assignment binds becomes that invariant parameter, an object
/// becomes a constant, and anything else is counted.
fn derive_part(deleted: &Atom, sigma: &[Option<Term>]) -> Part {
    let slots = deleted
        .terms
        .iter()
        .map(|term| {
            if let Some(index) = sigma.iter().position(|bound| bound.as_ref() == Some(term)) {
                Slot::Param(index)
            } else if let Term::Object(object) = term {
                Slot::Const(*object)
            } else {
                Slot::Counted
            }
        })
        .collect();
    Part {
        predicate: deleted.predicate,
        slots,
    }
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

        fn from_files(domain_path: &str, problem_path: &str) -> Self {
            let domain_src = std::fs::read_to_string(domain_path).expect("read domain");
            let problem_src = std::fs::read_to_string(problem_path).expect("read problem");
            Fixture::new(&domain_src, &problem_src)
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

        fn predicate(&self, name: &str) -> Predicate {
            self.domain
                .predicates
                .find_predicate(name)
                .unwrap_or_else(|| panic!("predicate `{name}` is declared"))
        }

        fn atom(&self, predicate: &str, args: &[&str]) -> Atom {
            Atom {
                predicate: self.predicate(predicate),
                terms: args.iter().map(|name| self.object(name)).collect(),
            }
        }

        /// Whether some multi-part group covers exactly these predicates.
        fn has_group_over(&self, names: &[&str]) -> bool {
            let mut want: Vec<Predicate> = names.iter().map(|n| self.predicate(n)).collect();
            want.sort_by_key(|predicate| predicate.0);
            self.mutexes()
                .groups()
                .iter()
                .any(|group| group.len() > 1 && group.predicates() == want)
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

    // -- the single-part case ----------------------------------------------

    #[test]
    fn a_vehicle_is_at_one_location() {
        let fixture = Fixture::new(TRAVEL_DOMAIN, TRAVEL_PROBLEM);
        let mutexes = fixture.mutexes();
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
        assert!(!mutexes.mutex(
            &fixture.atom("at", &["truck", "a"]),
            &fixture.atom("at", &["truck", "a"])
        ));
    }

    #[test]
    fn a_monotone_predicate_yields_no_group() {
        let fixture = Fixture::new(TRAVEL_DOMAIN, TRAVEL_PROBLEM);
        let mutexes = fixture.mutexes();
        assert!(!mutexes.mutex(
            &fixture.atom("visited", &["a"]),
            &fixture.atom("visited", &["b"])
        ));
    }

    #[test]
    fn an_unpaired_delete_rejects_the_candidate() {
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
        assert!(!fixture.mutexes().mutex(
            &fixture.atom("at", &["truck", "a"]),
            &fixture.atom("at", &["truck", "b"])
        ));
    }

    #[test]
    fn a_delete_that_is_not_a_precondition_rejects_the_candidate() {
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
        assert!(!fixture.mutexes().mutex(
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
        assert!(!fixture.mutexes().mutex(
            &fixture.atom("at", &["truck", "a"]),
            &fixture.atom("at", &["truck", "b"])
        ));
    }

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
        assert!(fixture.mutexes().mutex(
            &fixture.atom("road", &["a", "b"]),
            &fixture.atom("road", &["a", "c"])
        ));
    }

    // -- refinement, the multi-part case ------------------------------------

    /// The flagship. `load-truck` adds `in(?o, ?truck)` and unbalances the
    /// single-part `in` candidate; refinement grows it into
    /// `⟨at(v₀, ·), in(v₀, ·)⟩` from the `at(?o, ?loc)` that `load-truck`
    /// deletes and required.
    #[test]
    fn a_package_is_at_a_place_or_in_a_vehicle_but_not_both() {
        let fixture = Fixture::from_files(
            "examples/logistics-domain.pddl",
            "examples/logistics-a.pddl",
        );
        assert!(
            fixture.has_group_over(&["at", "in"]),
            "no at/in group; found {:?}",
            fixture
                .mutexes()
                .groups()
                .iter()
                .map(|group| (group.len(), group.predicates()))
                .collect::<Vec<_>>()
        );
    }

    /// Ferry's version of the same shape, and the one with a constant in it:
    /// `debark` adds `at(?x, ?y)` and deletes `on(?x, ferry)`, so the derived
    /// part pins the second position to the `ferry` constant.
    #[test]
    fn a_car_is_ashore_or_aboard_the_ferry() {
        let fixture = Fixture::from_files("examples/ferry-domain.pddl", "examples/test-ferry.pddl");
        assert!(
            fixture.has_group_over(&["at", "on"]),
            "no at/on group; found {:?}",
            fixture
                .mutexes()
                .groups()
                .iter()
                .map(|group| (group.len(), group.predicates()))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn refinement_never_pairs_a_monotone_predicate() {
        let fixture = Fixture::new(TRAVEL_DOMAIN, TRAVEL_PROBLEM);
        // `visited` is only ever added, so no group may contain it beside `at`.
        assert!(!fixture.mutexes().mutex(
            &fixture.atom("at", &["truck", "a"]),
            &fixture.atom("visited", &["b"])
        ));
    }
}
