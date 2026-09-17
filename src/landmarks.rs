//! Lifted necessary-subgoal landmarks
//! (Wichlacz, Höller & Hoffmann, IJCAI 2022, §3.1).
//!
//! Backchain through achievers and intersect their entailed positive
//! preconditions by predicate. Keep object bindings only when all achievers
//! agree. An empty achiever set supplies no intersection.
//! Only unconditional, unquantified positive effects establish landmarks;
//! multiple occurrences must agree at every retained argument position.

use std::collections::HashSet;
use std::rc::Rc;

use crate::action::ActionSchema;
use crate::domain::Domain;
use crate::formula::{Atom, Formula, Literal};
use crate::predicates::Predicate;
use crate::problem::Problem;
use crate::terms::{Object, Term, Variable};

/// Most landmarks to extract, and most backchaining rounds. Running out drops
/// landmarks, which weakens the heuristic and never makes it claim more.
const MAX_LANDMARKS: usize = 512;
const MAX_ROUNDS: usize = 64;

/// A predicate with each argument either pinned to an object or left free: the
/// partially grounded predicate of Definition 1.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PartialAtom {
    pub predicate: Predicate,
    /// `Some(o)` pins the position to that object; `None` leaves it free.
    pub args: Vec<Option<Object>>,
}

impl PartialAtom {
    /// Whether a ground atom is an instance of this partially grounded one.
    pub fn matches_ground(&self, atom: &Atom) -> bool {
        self.predicate == atom.predicate
            && self.args.len() == atom.terms.len()
            && self
                .args
                .iter()
                .zip(&atom.terms)
                .all(|(pinned, term)| match (pinned, term) {
                    (None, _) => true,
                    (Some(object), Term::Object(other)) => object == other,
                    (Some(_), Term::Variable(_)) => false,
                })
    }

    /// Whether some instance of this landmark *could* be the given literal, once
    /// its terms are resolved as far as the bindings go.
    ///
    /// Optimistic on purpose: an unbound term might still become the object the
    /// landmark wants, so it counts as a possible match. That makes the
    /// heuristic count fewer outstanding landmarks rather than more.
    pub fn could_match(&self, atom: &Atom, resolve: impl Fn(Term) -> Term) -> bool {
        self.predicate == atom.predicate
            && self.args.len() == atom.terms.len()
            && self
                .args
                .iter()
                .zip(&atom.terms)
                .all(|(pinned, &term)| match pinned {
                    None => true,
                    Some(object) => match resolve(term) {
                        Term::Object(other) => *object == other,
                        Term::Variable(_) => true,
                    },
                })
    }
}

/// The lifted landmarks of a task.
#[derive(Debug, Default)]
pub struct LiftedLandmarks {
    landmarks: Vec<PartialAtom>,
}

impl LiftedLandmarks {
    pub fn landmarks(&self) -> &[PartialAtom] {
        &self.landmarks
    }

    pub fn len(&self) -> usize {
        self.landmarks.len()
    }

    pub fn is_empty(&self) -> bool {
        self.landmarks.is_empty()
    }

    /// Backchains from the goal to a fixpoint.
    pub fn extract(domain: &Domain, problem: &Problem) -> Self {
        let mut seeds = Vec::new();
        collect_entailed_atoms(&problem.goal, &mut seeds);

        let mut found: Vec<PartialAtom> = Vec::new();
        let mut seen: HashSet<PartialAtom> = HashSet::new();
        let mut frontier: Vec<PartialAtom> = Vec::new();
        for atom in seeds {
            let landmark = PartialAtom {
                predicate: atom.predicate,
                args: atom
                    .terms
                    .iter()
                    .map(|term| match term {
                        Term::Object(object) => Some(*object),
                        Term::Variable(_) => None,
                    })
                    .collect(),
            };
            if seen.insert(landmark.clone()) {
                found.push(landmark.clone());
                frontier.push(landmark);
            }
        }

        let schemas: Vec<SchemaFacts> = domain.actions.iter().map(SchemaFacts::new).collect();

        for _ in 0..MAX_ROUNDS {
            if frontier.is_empty() || found.len() >= MAX_LANDMARKS {
                break;
            }
            let mut next = Vec::new();
            for subgoal in &frontier {
                for candidate in necessary_subgoals(subgoal, &schemas) {
                    if found.len() >= MAX_LANDMARKS {
                        break;
                    }
                    if seen.insert(candidate.clone()) {
                        found.push(candidate.clone());
                        next.push(candidate);
                    }
                }
            }
            frontier = next;
        }

        LiftedLandmarks { landmarks: found }
    }
}

impl LiftedLandmarks {
    /// How many landmarks no step of the partial plan achieves.
    ///
    /// A landmark counts as achieved when the initial state already makes it
    /// true, or when some committed step has an effect that could produce it
    /// under the plan's current bindings. What is left is work the plan has
    /// still to do, which is the estimate — the plan-space reading of LAMA's
    /// landmark count, where "the state has accepted it" becomes "a step in the
    /// plan produces it".
    ///
    /// "Could produce" is deliberately optimistic: a step whose parameter is
    /// still unbound might yet be bound to the object the landmark wants, so it
    /// counts. The estimate is therefore a lower bound on the landmarks a
    /// completion must still achieve, never an over-count.
    pub fn outstanding(&self, plan: &crate::plan::Plan) -> usize {
        self.landmarks
            .iter()
            .filter(|landmark| !self.achieved(landmark, plan))
            .count()
    }

    fn achieved(&self, landmark: &PartialAtom, plan: &crate::plan::Plan) -> bool {
        for step in crate::chain::iter(&plan.steps) {
            for effect in step.action.effects.iter() {
                if effect.conditional() || !effect.parameters.is_empty() {
                    continue;
                }
                let Literal::Atom(added) = &effect.literal else {
                    continue;
                };
                // The initial step carries the initial atoms as its effects, so
                // a landmark true to begin with is caught here too.
                if landmark.could_match(added, |term| plan.bindings.binding(term, step.id)) {
                    return true;
                }
            }
        }
        false
    }
}

/// One schema, reduced to what backchaining reads.
struct SchemaFacts {
    /// Positive, unconditional, unquantified effect atoms.
    adds: Vec<Atom>,
    /// Positive atoms the precondition entails.
    required: Vec<Atom>,
}

impl SchemaFacts {
    fn new(schema: &ActionSchema) -> Self {
        let adds = schema
            .effects
            .iter()
            .filter(|effect| !effect.conditional() && effect.parameters.is_empty())
            .filter_map(|effect| match &effect.literal {
                Literal::Atom(atom) => Some(atom.clone()),
                Literal::Negation(_) => None,
            })
            .collect();
        let mut required = Vec::new();
        collect_entailed_atoms(&schema.precondition, &mut required);
        SchemaFacts { adds, required }
    }
}

/// The new subgoals a landmark backchains to: predicates required by *every*
/// schema that could have produced it.
fn necessary_subgoals(subgoal: &PartialAtom, schemas: &[SchemaFacts]) -> Vec<PartialAtom> {
    // Each candidate is one schema partially ground so that it produces the
    // subgoal, reduced to the preconditions under that grounding.
    let mut candidates: Vec<Vec<Atom>> = Vec::new();
    for schema in schemas {
        for added in &schema.adds {
            let Some(binding) = match_add(subgoal, added) else {
                continue;
            };
            candidates.push(
                schema
                    .required
                    .iter()
                    .map(|atom| apply(atom, &binding))
                    .collect(),
            );
        }
    }
    // No schema adds it: the subgoal has to hold initially, and intersecting
    // over nothing would admit every predicate.
    if candidates.is_empty() {
        return Vec::new();
    }

    // Predicates every candidate requires.
    let mut shared: Vec<Predicate> = candidates[0]
        .iter()
        .map(|atom| atom.predicate)
        .collect::<HashSet<_>>()
        .into_iter()
        .collect();
    shared.retain(|predicate| {
        candidates
            .iter()
            .all(|required| required.iter().any(|atom| atom.predicate == *predicate))
    });
    shared.sort_by_key(|predicate| predicate.0);

    // For each such predicate, pin the positions every occurrence agrees on.
    shared
        .into_iter()
        .filter_map(|predicate| {
            let mut args: Option<Vec<Option<Object>>> = None;
            for required in &candidates {
                for atom in required.iter().filter(|atom| atom.predicate == predicate) {
                    let here: Vec<Option<Object>> = atom
                        .terms
                        .iter()
                        .map(|term| match term {
                            Term::Object(object) => Some(*object),
                            Term::Variable(_) => None,
                        })
                        .collect();
                    args = Some(match args {
                        None => here,
                        Some(previous) => {
                            if previous.len() != here.len() {
                                return None;
                            }
                            previous
                                .into_iter()
                                .zip(here)
                                .map(|(a, b)| if a == b { a } else { None })
                                .collect()
                        }
                    });
                }
            }
            args.map(|args| PartialAtom { predicate, args })
        })
        .collect()
}

/// Partially grounds a schema so that `added` produces `subgoal`, returning the
/// variable bindings that forces. `None` when it cannot.
fn match_add(subgoal: &PartialAtom, added: &Atom) -> Option<Vec<(Variable, Object)>> {
    if subgoal.predicate != added.predicate || subgoal.args.len() != added.terms.len() {
        return None;
    }
    let mut binding: Vec<(Variable, Object)> = Vec::new();
    for (pinned, term) in subgoal.args.iter().zip(&added.terms) {
        let Some(object) = pinned else { continue };
        match term {
            Term::Object(other) => {
                if other != object {
                    return None;
                }
            }
            Term::Variable(variable) => match binding.iter().find(|(bound, _)| bound == variable) {
                Some((_, already)) if already != object => return None,
                Some(_) => {}
                None => binding.push((*variable, *object)),
            },
        }
    }
    Some(binding)
}

fn apply(atom: &Atom, binding: &[(Variable, Object)]) -> Atom {
    Atom {
        predicate: atom.predicate,
        terms: atom
            .terms
            .iter()
            .map(|term| match term {
                Term::Variable(variable) => binding
                    .iter()
                    .find(|(bound, _)| bound == variable)
                    .map(|(_, object)| Term::Object(*object))
                    .unwrap_or(*term),
                Term::Object(_) => *term,
            })
            .collect(),
    }
}

/// Collects the positive atoms a formula entails: its top-level conjunction and
/// existential bodies. A disjunct or a negated atom is not required.
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

    fn fixture(domain_path: &str, problem_path: &str) -> (Domain, Problem) {
        let domain_src = std::fs::read_to_string(domain_path).expect("read domain");
        let problem_src = std::fs::read_to_string(problem_path).expect("read problem");
        let domain = match read_pddl(&domain_src).expect("parse domain") {
            ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
            _ => panic!("expected a domain"),
        };
        let problem = match read_pddl(&problem_src).expect("parse problem") {
            ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
            _ => panic!("expected a problem"),
        };
        (domain, problem)
    }

    #[test]
    fn the_goal_atoms_are_landmarks() {
        let (domain, problem) = fixture(
            "examples/blocks-world-domain.pddl",
            "examples/sussman-anomaly.pddl",
        );
        let landmarks = LiftedLandmarks::extract(&domain, &problem);
        let mut goals = Vec::new();
        collect_entailed_atoms(&problem.goal, &mut goals);
        assert!(!goals.is_empty(), "the test problem has conjunctive goals");
        for goal in &goals {
            assert!(
                landmarks.landmarks().iter().any(|l| l.matches_ground(goal)),
                "goal atom {goal:?} is not among the landmarks"
            );
        }
    }

    #[test]
    fn backchaining_finds_more_than_the_goal() {
        let (domain, problem) = fixture(
            "examples/blocks-world-domain.pddl",
            "examples/sussman-anomaly.pddl",
        );
        let landmarks = LiftedLandmarks::extract(&domain, &problem);
        let mut goals = Vec::new();
        collect_entailed_atoms(&problem.goal, &mut goals);
        assert!(
            landmarks.len() > goals.len(),
            "backchaining produced nothing beyond the goal: {:?}",
            landmarks.landmarks()
        );
    }

    #[test]
    fn a_landmark_may_be_only_partly_ground() {
        // Logistics: a package must be *in* something, but which vehicle is not
        // agreed on by the actions that could put it there, so the position is
        // left free — the compact disjunction of Definition 1.
        let (domain, problem) = fixture(
            "examples/logistics-domain.pddl",
            "examples/logistics-a.pddl",
        );
        let landmarks = LiftedLandmarks::extract(&domain, &problem);
        assert!(
            landmarks.landmarks().iter().any(|l| l.args.contains(&None)),
            "no partially grounded landmark found"
        );
    }

    #[test]
    fn extraction_terminates_on_every_example_domain() {
        for (domain_path, problem_path) in [
            ("examples/ferry-domain.pddl", "examples/test-ferry.pddl"),
            ("examples/gripper-domain.pddl", "examples/gripper-6.pddl"),
            ("examples/hanoi-domain.pddl", "examples/hanoi-3.pddl"),
            ("examples/flat-tire-domain.pddl", "examples/fixit.pddl"),
        ] {
            let (domain, problem) = fixture(domain_path, problem_path);
            let landmarks = LiftedLandmarks::extract(&domain, &problem);
            assert!(
                landmarks.len() <= MAX_LANDMARKS,
                "{problem_path}: extraction exceeded its budget"
            );
        }
    }
}
