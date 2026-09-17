//! Lifted necessary-subgoal landmarks
//! (Wichlacz, Höller & Hoffmann, IJCAI 2022, §3.1).
//!
//! Backchain through achievers and intersect their entailed positive
//! preconditions by predicate. Keep object bindings only when all achievers
//! agree. An empty achiever set supplies no intersection.
//! Only unconditional, unquantified positive effects establish landmarks;
//! multiple occurrences must agree at every retained argument position.

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::action::ActionSchema;
use crate::domain::Domain;
use crate::fam_cut::{self, ActionInstance, DisjunctiveActionLandmark};
use crate::formula::{Atom, Formula, Literal};
use crate::lifted_mutex::LiftedMutexes;
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
    /// `(before, after)` index pairs into `landmarks`: `before` →D `after`, the
    /// direct ordering backchaining hands out as a side effect (§3.3).
    orderings: Vec<(usize, usize)>,
    /// Disjunctive action landmarks from the FAM cuts, empty unless extraction
    /// was given the mutex groups.
    actions: Vec<DisjunctiveActionLandmark>,
    /// `(before, after)` index pairs into `actions`: the weaker → ordering
    /// between successive cuts of one group instance.
    action_orderings: Vec<(usize, usize)>,
}

impl LiftedLandmarks {
    pub fn landmarks(&self) -> &[PartialAtom] {
        &self.landmarks
    }

    /// The disjunctive action landmarks, one entry per cut.
    pub fn actions(&self) -> &[DisjunctiveActionLandmark] {
        &self.actions
    }

    /// The →D orderings between fact landmarks, as index pairs.
    pub fn orderings(&self) -> &[(usize, usize)] {
        &self.orderings
    }

    pub fn len(&self) -> usize {
        self.landmarks.len()
    }

    pub fn is_empty(&self) -> bool {
        self.landmarks.is_empty() && self.actions.is_empty()
    }

    /// Backchains from the goal to a fixpoint over necessary subgoals alone.
    pub fn extract(domain: &Domain, problem: &Problem) -> Self {
        Self::extract_with(domain, problem, None)
    }

    /// Backchains as [`Self::extract`] does, and additionally cuts the
    /// transition graph of every landmark's mutex group ([`crate::fam_cut`]).
    pub fn extract_with_mutexes(
        domain: &Domain,
        problem: &Problem,
        mutexes: &LiftedMutexes,
    ) -> Self {
        Self::extract_with(domain, problem, Some(mutexes))
    }

    /// The two extraction methods run together, because each feeds the other:
    /// backchaining turns a fact landmark into more fact landmarks, and a FAM
    /// cut turns one into a disjunctive action landmark whose shared
    /// preconditions are fact landmarks again. The paper runs this to a
    /// fixpoint; the round and size budgets stop it earlier on tasks where it
    /// would not converge cheaply.
    fn extract_with(domain: &Domain, problem: &Problem, mutexes: Option<&LiftedMutexes>) -> Self {
        let mut goals = Vec::new();
        collect_entailed_atoms(&problem.goal, &mut goals);

        let mut out = LiftedLandmarks::default();
        let mut seen: HashMap<PartialAtom, usize> = HashMap::new();
        let mut frontier: Vec<usize> = Vec::new();
        for atom in goals {
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
            if let Entry::Vacant(slot) = seen.entry(landmark.clone()) {
                slot.insert(out.landmarks.len());
                out.landmarks.push(landmark);
                frontier.push(out.landmarks.len() - 1);
            }
        }

        let schemas: Vec<SchemaFacts> = domain.actions.iter().map(SchemaFacts::new).collect();

        for _ in 0..MAX_ROUNDS {
            if frontier.is_empty() || out.landmarks.len() >= MAX_LANDMARKS {
                break;
            }
            let mut next = Vec::new();
            for index in frontier {
                let subgoal = out.landmarks[index].clone();

                // Backchaining: every new subgoal is ordered directly before
                // the landmark it was extracted from.
                for candidate in necessary_subgoals(&subgoal, &schemas) {
                    if let Some(found) = out.admit(candidate, &mut seen, &mut next) {
                        out.orderings.push((found, index));
                    }
                }

                let Some(mutexes) = mutexes else { continue };
                if out.actions.len() >= MAX_LANDMARKS {
                    continue;
                }
                // FAM cuts: the cuts come back goal-end first, so consecutive
                // pairs are ordered later-cut after earlier-cut.
                let mut previous: Option<usize> = None;
                for cut in fam_cut::cuts(domain, problem, mutexes, &subgoal) {
                    for candidate in shared_preconditions(domain, &schemas, &cut) {
                        out.admit(candidate, &mut seen, &mut next);
                    }
                    let here = match out.actions.iter().position(|known| *known == cut) {
                        Some(known) => known,
                        None => {
                            out.actions.push(cut);
                            out.actions.len() - 1
                        }
                    };
                    if let Some(earlier) = previous {
                        // `here` is the earlier cut in plan order: the cut
                        // sequence walks backwards from the goal.
                        out.action_orderings.push((here, earlier));
                    }
                    previous = Some(here);
                }
            }
            frontier = next;
        }

        out
    }

    /// Records a new landmark, returning its index when it was not already
    /// known. Dropping a landmark at the budget weakens the heuristic and never
    /// makes it claim more.
    fn admit(
        &mut self,
        candidate: PartialAtom,
        seen: &mut HashMap<PartialAtom, usize>,
        next: &mut Vec<usize>,
    ) -> Option<usize> {
        if let Some(known) = seen.get(&candidate) {
            return Some(*known);
        }
        if self.landmarks.len() >= MAX_LANDMARKS {
            return None;
        }
        let index = self.landmarks.len();
        seen.insert(candidate.clone(), index);
        self.landmarks.push(candidate);
        next.push(index);
        Some(index)
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
        self.count(plan, false)
    }

    /// The landmark count, optionally sharpened by the ordering relations.
    ///
    /// Without orderings this is the plain count of landmarks — fact landmarks
    /// and FAM cuts alike — that nothing in the plan achieves.
    ///
    /// With orderings it applies §3.3's rule. A lifted landmark is a
    /// disjunction, so a plan may well contain a step producing *some* instance
    /// of `P` without producing the instance the goal needs. When `Q` →D `P`
    /// and nothing achieves `Q`, the instance of `P` that the plan will
    /// eventually use has not been produced either, so `P` still counts. The
    /// same propagation runs over the weaker → between successive cuts.
    pub fn count(&self, plan: &crate::plan::Plan, orderings: bool) -> usize {
        let mut facts: Vec<bool> = self
            .landmarks
            .iter()
            .map(|landmark| !self.achieved(landmark, plan))
            .collect();
        let mut actions: Vec<bool> = self
            .actions
            .iter()
            .map(|landmark| !achieved_action(landmark, plan))
            .collect();
        if orderings {
            propagate(&self.orderings, &mut facts);
            propagate(&self.action_orderings, &mut actions);
        }
        facts.iter().filter(|open| **open).count() + actions.iter().filter(|open| **open).count()
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

/// Carries "still outstanding" forward along an ordering: when the earlier
/// landmark is open, so is the later one.
fn propagate(orderings: &[(usize, usize)], open: &mut [bool]) {
    for _ in 0..orderings.len() {
        let mut changed = false;
        for &(before, after) in orderings {
            if open[before] && !open[after] {
                open[after] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

/// Whether some step of the plan could be one of a disjunctive action
/// landmark's alternatives.
///
/// Optimistic in the same way as [`PartialAtom::could_match`]: a step whose
/// argument is still unbound might yet be bound to what the landmark wants, so
/// it counts as achieving it.
fn achieved_action(landmark: &DisjunctiveActionLandmark, plan: &crate::plan::Plan) -> bool {
    crate::chain::iter(&plan.steps).any(|step| {
        landmark
            .alternatives
            .iter()
            .any(|alternative| matches_step(alternative, step, plan))
    })
}

fn matches_step(
    alternative: &ActionInstance,
    step: &crate::plan::Step,
    plan: &crate::plan::Plan,
) -> bool {
    if step.action.name != alternative.name {
        return false;
    }
    let ground = &step.action.arguments;
    let lifted = &step.action.parameters;
    alternative
        .args
        .iter()
        .enumerate()
        .all(|(position, wanted)| {
            let Some(wanted) = wanted else { return true };
            if let Some(object) = ground.get(position) {
                return object == wanted;
            }
            match lifted.get(position) {
                Some(variable) => match plan.bindings.binding(Term::Variable(*variable), step.id) {
                    Term::Object(object) => object == *wanted,
                    Term::Variable(_) => true,
                },
                None => true,
            }
        })
}

/// The fact landmarks a disjunctive action landmark yields: predicates every
/// alternative requires, pinned wherever the alternatives agree. The same
/// intersection backchaining uses, over a set of actions the cut chose rather
/// than over the actions that could add a subgoal.
fn shared_preconditions(
    domain: &Domain,
    schemas: &[SchemaFacts],
    cut: &DisjunctiveActionLandmark,
) -> Vec<PartialAtom> {
    let candidates: Vec<Vec<Atom>> = cut
        .alternatives
        .iter()
        .map(|alternative| {
            let binding: Vec<(Variable, Object)> = domain.actions[alternative.schema]
                .parameters
                .iter()
                .zip(&alternative.args)
                .filter_map(|(variable, object)| object.map(|object| (*variable, object)))
                .collect();
            schemas[alternative.schema]
                .required
                .iter()
                .map(|atom| apply(atom, &binding))
                .collect()
        })
        .collect();
    intersect(&candidates)
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
    intersect(&candidates)
}

/// The partially ground atoms a set of requirement lists all share: a predicate
/// every list mentions, with an object at each position on which every
/// occurrence in every list agrees.
///
/// This is what keeps a lifted landmark sound where the candidates disagree —
/// disagreement widens the landmark into the disjunction over that position
/// rather than committing to one candidate's choice.
fn intersect(candidates: &[Vec<Atom>]) -> Vec<PartialAtom> {
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
            for required in candidates {
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
