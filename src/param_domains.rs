//! Operator parameter domains (Gerevini & Schubert, JAIR 5, 1996, §4).
//!
//! Propagate positive atoms from the initial state to a fixpoint. Each schema
//! parameter's domain intersects the values supported at its precondition
//! occurrences; effects then propagate those domains.
//!
//! Only entailed positive preconditions constrain domains. Disjunction,
//! negation, universal preconditions, and equality add no restrictions.
//! Propagate all positive effects, including conditional and quantified ones.
//! Unknown terms and unconstrained parameters use [`ArgDomain::Any`] to keep
//! the result an over-approximation.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::domain::Domain;
use crate::formula::{Atom, Formula};
use crate::predicates::Predicate;
use crate::problem::Problem;
use crate::terms::{Object, Term};

/// The constants an argument position may take. [`Any`](ArgDomain::Any) is the
/// top element: no constraint is known.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgDomain {
    Any,
    Only(HashSet<Object>),
}

impl ArgDomain {
    fn empty() -> Self {
        ArgDomain::Only(HashSet::new())
    }

    fn is_empty(&self) -> bool {
        matches!(self, ArgDomain::Only(set) if set.is_empty())
    }

    fn contains(&self, object: Object) -> bool {
        match self {
            ArgDomain::Any => true,
            ArgDomain::Only(set) => set.contains(&object),
        }
    }

    /// Unions `other` into `self`, returning whether `self` grew.
    fn union_with(&mut self, other: &ArgDomain) -> bool {
        match (&mut *self, other) {
            (ArgDomain::Any, _) => false,
            (_, ArgDomain::Any) => {
                *self = ArgDomain::Any;
                true
            }
            (ArgDomain::Only(set), ArgDomain::Only(add)) => {
                let before = set.len();
                set.extend(add.iter().copied());
                set.len() != before
            }
        }
    }

    /// Intersects `other` into `self`.
    fn intersect_with(&mut self, other: &ArgDomain) {
        match (&mut *self, other) {
            (_, ArgDomain::Any) => {}
            (ArgDomain::Any, ArgDomain::Only(keep)) => *self = ArgDomain::Only(keep.clone()),
            (ArgDomain::Only(set), ArgDomain::Only(keep)) => set.retain(|o| keep.contains(o)),
        }
    }
}

/// What a precondition occurrence holds at one argument position.
#[derive(Debug, Clone, Copy)]
enum Slot {
    /// The schema's parameter at this index.
    Param(usize),
    /// A domain constant.
    Const(Object),
    /// Anything else — a quantified variable, say. Matches without constraining.
    Other,
}

/// One entailed positive precondition atom of a schema.
#[derive(Debug, Clone)]
struct Occurrence {
    predicate: Predicate,
    slots: Vec<Slot>,
}

/// A positive atom a schema's effects (or the initial state) can produce, with
/// a domain per argument position.
#[derive(Debug, Clone)]
struct Production {
    predicate: Predicate,
    positions: Vec<ArgDomain>,
}

#[derive(Debug)]
struct SchemaDomains {
    /// Entailed positive precondition atoms.
    occurrences: Vec<Occurrence>,
    /// `individual[occurrence][parameter]`, tracked only where the parameter
    /// occurs; elsewhere it stays `None`.
    individual: Vec<Vec<Option<ArgDomain>>>,
    /// Intersection of the individual domains, per parameter.
    intersected: Vec<ArgDomain>,
    /// Positive effect literals, as slots over the schema's scope.
    effects: Vec<Occurrence>,
}

/// Per-schema parameter domains for a lowered domain and problem.
#[derive(Debug)]
pub struct ParameterDomains {
    schemas: Vec<SchemaDomains>,
    by_name: HashMap<String, usize>,
}

impl ParameterDomains {
    /// Runs `find-parameter-domains` to a fixpoint.
    pub fn compute(domain: &Domain, problem: &Problem) -> Self {
        let mut schemas: Vec<SchemaDomains> = Vec::with_capacity(domain.actions.len());
        let mut by_name = HashMap::with_capacity(domain.actions.len());

        for (index, action) in domain.actions.iter().enumerate() {
            let param_index: HashMap<u32, usize> = action
                .parameters
                .iter()
                .enumerate()
                .map(|(i, v)| (v.0, i))
                .collect();

            let mut occurrences = Vec::new();
            collect_entailed_atoms(&action.precondition, &param_index, &mut occurrences);

            let mut effects = Vec::new();
            for effect in &action.effects {
                if let crate::formula::Literal::Atom(atom) = &effect.literal {
                    effects.push(occurrence_of(atom, &param_index));
                }
            }

            let individual = occurrences
                .iter()
                .map(|occ| {
                    let mut row = vec![None; action.parameters.len()];
                    for slot in &occ.slots {
                        if let Slot::Param(p) = slot {
                            row[*p] = Some(ArgDomain::empty());
                        }
                    }
                    row
                })
                .collect();

            schemas.push(SchemaDomains {
                occurrences,
                individual,
                intersected: vec![ArgDomain::Any; action.parameters.len()],
                effects,
            });
            by_name.insert(action.name.clone(), index);
        }

        let mut domains = ParameterDomains { schemas, by_name };
        domains.saturate(initial_productions(problem));
        domains
    }

    /// Propagates until no individual domain grows.
    fn saturate(&mut self, initial: Vec<Production>) {
        loop {
            // Rebuild the production set from the initial state plus every
            // schema whose parameters are all currently satisfiable. A schema
            // with an empty intersected domain has no instance at all, so it
            // produces nothing.
            let mut productions = initial.clone();
            for schema in &self.schemas {
                if schema.intersected.iter().any(ArgDomain::is_empty) {
                    continue;
                }
                for effect in &schema.effects {
                    productions.push(Production {
                        predicate: effect.predicate,
                        positions: effect
                            .slots
                            .iter()
                            .map(|slot| match slot {
                                Slot::Param(p) => schema.intersected[*p].clone(),
                                Slot::Const(o) => ArgDomain::Only(HashSet::from([*o])),
                                Slot::Other => ArgDomain::Any,
                            })
                            .collect(),
                    });
                }
            }

            let mut changed = false;
            for schema in &mut self.schemas {
                for (occ_index, occurrence) in schema.occurrences.iter().enumerate() {
                    for production in &productions {
                        if production.predicate != occurrence.predicate
                            || production.positions.len() != occurrence.slots.len()
                        {
                            continue;
                        }
                        // A constant in the occurrence must be producible here.
                        let compatible = occurrence.slots.iter().zip(&production.positions).all(
                            |(slot, position)| match slot {
                                Slot::Const(o) => position.contains(*o),
                                _ => !position.is_empty(),
                            },
                        );
                        if !compatible {
                            continue;
                        }
                        for (slot, position) in occurrence.slots.iter().zip(&production.positions) {
                            if let Slot::Param(p) = slot {
                                if let Some(individual) = &mut schema.individual[occ_index][*p] {
                                    changed |= individual.union_with(position);
                                }
                            }
                        }
                    }
                }
                schema.recompute_intersected();
            }

            if !changed {
                return;
            }
        }
    }

    /// Whether `object` can reach parameter `position` of the named schema.
    /// Unknown schema names (the synthetic init and goal actions, or a ground
    /// action whose schema was renamed) answer `true`.
    pub fn permits(&self, action_name: &str, position: usize, object: Object) -> bool {
        let Some(&index) = self.by_name.get(action_name) else {
            return true;
        };
        match self.schemas[index].intersected.get(position) {
            Some(domain) => domain.contains(object),
            None => true,
        }
    }

    /// Whether a fully ground argument tuple is viable.
    pub fn permits_arguments(&self, action_name: &str, arguments: &[Object]) -> bool {
        let Some(&index) = self.by_name.get(action_name) else {
            return true;
        };
        let intersected = &self.schemas[index].intersected;
        arguments
            .iter()
            .enumerate()
            .all(|(position, object)| match intersected.get(position) {
                Some(domain) => domain.contains(*object),
                None => true,
            })
    }

    /// Whether the named schema has any viable instance at all. A schema with an
    /// empty parameter domain can never apply and need not be instantiated.
    pub fn schema_viable(&self, action_name: &str) -> bool {
        match self.by_name.get(action_name) {
            Some(&index) => !self.schemas[index]
                .intersected
                .iter()
                .any(ArgDomain::is_empty),
            None => true,
        }
    }

    /// Parameter domains of one schema, for tests and `-v` reporting. `None` at
    /// a position means unconstrained.
    pub fn domain_of(&self, action_name: &str, position: usize) -> Option<Vec<Object>> {
        let index = *self.by_name.get(action_name)?;
        match self.schemas[index].intersected.get(position)? {
            ArgDomain::Any => None,
            ArgDomain::Only(set) => {
                let mut objects: Vec<Object> = set.iter().copied().collect();
                objects.sort_by_key(|o| o.0);
                Some(objects)
            }
        }
    }
}

impl SchemaDomains {
    fn recompute_intersected(&mut self) {
        for (parameter, intersected) in self.intersected.iter_mut().enumerate() {
            let mut combined: Option<ArgDomain> = None;
            for row in &self.individual {
                if let Some(individual) = &row[parameter] {
                    match &mut combined {
                        None => combined = Some(individual.clone()),
                        Some(current) => current.intersect_with(individual),
                    }
                }
            }
            *intersected = combined.unwrap_or(ArgDomain::Any);
        }
    }
}

fn occurrence_of(atom: &Atom, param_index: &HashMap<u32, usize>) -> Occurrence {
    Occurrence {
        predicate: atom.predicate,
        slots: atom
            .terms
            .iter()
            .map(|term| match term {
                Term::Object(o) => Slot::Const(*o),
                Term::Variable(v) => match param_index.get(&v.0) {
                    Some(p) => Slot::Param(*p),
                    None => Slot::Other,
                },
            })
            .collect(),
    }
}

/// Collects the positive atoms a precondition entails. Descends only through
/// conjunction and existential quantification; a disjunct, a negated atom or a
/// universally quantified body constrains nothing.
fn collect_entailed_atoms(
    formula: &Rc<Formula>,
    param_index: &HashMap<u32, usize>,
    out: &mut Vec<Occurrence>,
) {
    match formula.as_ref() {
        Formula::Atom(atom) => out.push(occurrence_of(atom, param_index)),
        Formula::Conjunction(parts) => {
            for part in parts {
                collect_entailed_atoms(part, param_index, out);
            }
        }
        Formula::Exists { body, .. } => collect_entailed_atoms(body, param_index, out),
        _ => {}
    }
}

fn initial_productions(problem: &Problem) -> Vec<Production> {
    problem
        .init_order
        .iter()
        .map(|atom| Production {
            predicate: atom.predicate,
            positions: atom
                .terms
                .iter()
                .map(|term| match term {
                    Term::Object(o) => ArgDomain::Only(HashSet::from([*o])),
                    Term::Variable(_) => ArgDomain::Any,
                })
                .collect(),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};

    const TRANSPORT_DOMAIN: &str = r#"
    (define (domain transport)
      (:requirements :strips :typing)
      (:types loc vehicle package)
      (:predicates (at ?v - vehicle ?l - loc)
                   (in ?p - package ?v - vehicle)
                   (road ?a - loc ?b - loc))
      (:action drive
        :parameters (?v - vehicle ?from - loc ?to - loc)
        :precondition (and (at ?v ?from) (road ?from ?to))
        :effect (and (not (at ?v ?from)) (at ?v ?to)))
      (:action load
        :parameters (?p - package ?v - vehicle ?l - loc)
        :precondition (and (at ?v ?l))
        :effect (in ?p ?v)))
    "#;

    const TRANSPORT_PROBLEM: &str = r#"
    (define (problem t1)
      (:domain transport)
      (:objects a b c - loc truck - vehicle box - package)
      (:init (at truck a) (road a b))
      (:goal (in box truck)))
    "#;

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

        fn domains(&self) -> ParameterDomains {
            ParameterDomains::compute(&self.domain, &self.problem)
        }

        fn object(&self, name: &str) -> Object {
            self.problem
                .objects
                .find_object(Some(&self.domain.constants), name)
                .unwrap_or_else(|| panic!("object `{name}` is declared"))
        }
    }

    #[test]
    fn a_parameter_is_limited_to_the_constants_that_reach_it() {
        let fixture = Fixture::new(TRANSPORT_DOMAIN, TRANSPORT_PROBLEM);
        let domains = fixture.domains();

        // `?from` must satisfy both (at ?v ?from) and (road ?from ?to). The
        // truck starts at `a` and can drive to `b`; the only road leaves `a`,
        // so the intersection over both preconditions is {a}.
        assert_eq!(
            domains.domain_of("drive", 1),
            Some(vec![fixture.object("a")])
        );
        // `?to` is produced only by the single road a -> b.
        assert_eq!(
            domains.domain_of("drive", 2),
            Some(vec![fixture.object("b")])
        );
    }

    #[test]
    fn an_instance_outside_the_domain_is_rejected() {
        let fixture = Fixture::new(TRANSPORT_DOMAIN, TRANSPORT_PROBLEM);
        let domains = fixture.domains();
        let (truck, a, b, c) = (
            fixture.object("truck"),
            fixture.object("a"),
            fixture.object("b"),
            fixture.object("c"),
        );
        assert!(domains.permits_arguments("drive", &[truck, a, b]));
        // `c` appears in no road fact, so no drive instance may mention it.
        assert!(!domains.permits_arguments("drive", &[truck, a, c]));
        assert!(!domains.permits_arguments("drive", &[truck, c, b]));
    }

    #[test]
    fn an_unconstrained_parameter_stays_unconstrained() {
        let fixture = Fixture::new(TRANSPORT_DOMAIN, TRANSPORT_PROBLEM);
        let domains = fixture.domains();
        // `?p` appears in no precondition of `load`, so nothing constrains it;
        // an empty domain here would prune every way of loading the package.
        assert_eq!(domains.domain_of("load", 0), None);
        assert!(domains.permits("load", 0, fixture.object("box")));
    }

    #[test]
    fn a_disjunctive_precondition_constrains_nothing() {
        let domain_src = r#"
        (define (domain d)
          (:requirements :strips :typing :disjunctive-preconditions)
          (:types thing)
          (:predicates (p ?x - thing) (q ?x - thing) (goal ?x - thing))
          (:action act
            :parameters (?x - thing)
            :precondition (or (p ?x) (q ?x))
            :effect (goal ?x)))
        "#;
        let problem_src = r#"
        (define (problem p1)
          (:domain d)
          (:objects u v - thing)
          (:init (p u))
          (:goal (goal v)))
        "#;
        let fixture = Fixture::new(domain_src, problem_src);
        let domains = fixture.domains();
        // `v` satisfies neither disjunct from the initial state, but a
        // disjunction is not an entailed atom, so the rule must not claim it.
        assert_eq!(domains.domain_of("act", 0), None);
        assert!(domains.permits_arguments("act", &[fixture.object("v")]));
    }

    #[test]
    fn a_negative_precondition_constrains_nothing() {
        let domain_src = r#"
        (define (domain d)
          (:requirements :strips :typing :negative-preconditions)
          (:types thing)
          (:predicates (blocked ?x - thing) (done ?x - thing))
          (:action act
            :parameters (?x - thing)
            :precondition (not (blocked ?x))
            :effect (done ?x)))
        "#;
        let problem_src = r#"
        (define (problem p1)
          (:domain d)
          (:objects u v - thing)
          (:init (blocked u))
          (:goal (done v)))
        "#;
        let fixture = Fixture::new(domain_src, problem_src);
        let domains = fixture.domains();
        assert_eq!(domains.domain_of("act", 0), None);
        assert!(domains.permits_arguments("act", &[fixture.object("v")]));
    }

    #[test]
    fn unknown_schemas_are_permitted() {
        let fixture = Fixture::new(TRANSPORT_DOMAIN, TRANSPORT_PROBLEM);
        let domains = fixture.domains();
        assert!(domains.permits("<init 0>", 0, fixture.object("a")));
        assert!(domains.schema_viable("<init 0>"));
    }
}
