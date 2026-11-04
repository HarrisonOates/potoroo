//! FAM-cut action landmarks (Wichlacz, Höller & Hoffmann, IJCAI 2022, §3.2).
//!
//! Cuts in a lifted mutex group's transition graph yield disjunctive action
//! landmarks between its initial value and known fact landmarks.
//!
//! Over-approximate transitions with all covered delete/add pairs and minimal
//! bindings. Abandon groups with conditional or quantified effects, unbalanced
//! adds, or excessive construction cost. Targets include every node that can
//! unify with the landmark.

use crate::domain::Domain;
use crate::formula::{Atom, Literal};
use crate::landmarks::PartialAtom;
use crate::lifted_mutex::{LiftedMutexes, MutexGroup, Slot};
use crate::predicates::Predicate;
use crate::problem::Problem;
use crate::terms::{Object, Term, Variable};

/// Most nodes one group's transition graph may hold, and most cuts to take from
/// it. Exhausting either abandons the group, which loses landmarks and never
/// invents one.
const MAX_NODES: usize = 256;
const MAX_CUTS: usize = 16;

/// One alternative of a disjunctive action landmark: a schema with as many
/// arguments pinned as the cut forces.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ActionInstance {
    /// Index into `domain.actions`.
    pub schema: usize,
    /// The schema's name, so a plan step can be matched without the domain.
    pub name: String,
    /// One entry per schema parameter; `None` where the cut leaves it free.
    pub args: Vec<Option<Object>>,
}

/// A set of partially ground actions, one of which every plan must execute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DisjunctiveActionLandmark {
    pub alternatives: Vec<ActionInstance>,
}

/// One group with its invariant parameters pinned: a lifted "variable".
struct Instance<'a> {
    group: &'a MutexGroup,
    params: Vec<Object>,
}

impl Instance<'_> {
    fn covers(&self, predicate: Predicate) -> bool {
        self.group
            .parts()
            .iter()
            .any(|part| part.predicate() == predicate)
    }

    /// Whether a partially ground atom is a value of this instance.
    fn holds(&self, atom: &PartialAtom) -> bool {
        self.group.parts().iter().any(|part| {
            part.predicate() == atom.predicate
                && part.slots().len() == atom.args.len()
                && part
                    .slots()
                    .iter()
                    .zip(&atom.args)
                    .all(|(slot, arg)| match slot {
                        Slot::Counted => true,
                        Slot::Const(constant) => *arg == Some(*constant),
                        Slot::Param(index) => *arg == Some(self.params[*index]),
                    })
        })
    }

    /// Every way of extending `sigma` so that a schema's atom becomes a value
    /// of this instance — one per part that admits it, because a group may hold
    /// the same predicate at more than one shape and each is a distinct value.
    fn bind(&self, atom: &Atom, sigma: &[(Variable, Object)]) -> Vec<Vec<(Variable, Object)>> {
        let mut out = Vec::new();
        for part in self.group.parts() {
            if part.predicate() != atom.predicate || part.slots().len() != atom.terms.len() {
                continue;
            }
            let mut trial = sigma.to_vec();
            let mut ok = true;
            for (slot, term) in part.slots().iter().zip(&atom.terms) {
                let wanted = match slot {
                    Slot::Counted => continue,
                    Slot::Const(constant) => *constant,
                    Slot::Param(index) => self.params[*index],
                };
                if !bind_term(term, wanted, &mut trial) {
                    ok = false;
                    break;
                }
            }
            if ok && !out.contains(&trial) {
                out.push(trial);
            }
        }
        out
    }
}

/// Forces a schema term to an object, extending `sigma`. False on a clash.
fn bind_term(term: &Term, wanted: Object, sigma: &mut Vec<(Variable, Object)>) -> bool {
    match term {
        Term::Object(object) => *object == wanted,
        Term::Variable(variable) => match sigma.iter().find(|(bound, _)| bound == variable) {
            Some((_, already)) => *already == wanted,
            None => {
                sigma.push((*variable, wanted));
                true
            }
        },
    }
}

/// A schema reduced to the group atoms it adds and deletes.
struct Transitions {
    schema: usize,
    name: String,
    /// The schema's parameters, in order, so an edge can record how far the
    /// binding pins them.
    parameters: Vec<Variable>,
    adds: Vec<Atom>,
    deletes: Vec<Atom>,
}

/// The disjunctive action landmarks cutting `landmark` off from the initial
/// value of its group instance, ordered from the goal end backwards.
pub fn cuts(
    domain: &Domain,
    problem: &Problem,
    mutexes: &LiftedMutexes,
    landmark: &PartialAtom,
) -> Vec<DisjunctiveActionLandmark> {
    let Some(instance) = instance_of(mutexes, landmark) else {
        return Vec::new();
    };
    let Some(transitions) = transitions(domain, &instance) else {
        return Vec::new();
    };
    let Some(initial) = initial_value(problem, &instance) else {
        return Vec::new();
    };
    let Some(graph) = build(&instance, &transitions, initial) else {
        return Vec::new();
    };
    cut(&graph, landmark)
}

/// The group instance a partially ground landmark identifies, if its invariant
/// positions are all pinned.
fn instance_of<'a>(mutexes: &'a LiftedMutexes, landmark: &PartialAtom) -> Option<Instance<'a>> {
    for group in mutexes.groups() {
        for part in group.parts() {
            if part.predicate() != landmark.predicate || part.slots().len() != landmark.args.len() {
                continue;
            }
            let mut params: Vec<Option<Object>> = vec![None; group.arity()];
            let mut ok = true;
            for (slot, arg) in part.slots().iter().zip(&landmark.args) {
                match slot {
                    Slot::Counted => {}
                    Slot::Const(constant) => {
                        if *arg != Some(*constant) {
                            ok = false;
                        }
                    }
                    Slot::Param(index) => match arg {
                        Some(object) => match params[*index] {
                            Some(bound) if bound != *object => ok = false,
                            _ => params[*index] = Some(*object),
                        },
                        None => ok = false,
                    },
                }
                if !ok {
                    break;
                }
            }
            if !ok {
                continue;
            }
            if let Some(params) = params.into_iter().collect::<Option<Vec<_>>>() {
                return Some(Instance { group, params });
            }
        }
    }
    None
}

/// The value the initial state gives this instance. `None` when it has none,
/// which leaves nothing to cut from.
fn initial_value(problem: &Problem, instance: &Instance) -> Option<PartialAtom> {
    problem
        .init_order
        .iter()
        .map(ground_partial)
        .find(|atom| instance.holds(atom))
}

fn ground_partial(atom: &Atom) -> PartialAtom {
    PartialAtom {
        predicate: atom.predicate,
        args: atom
            .terms
            .iter()
            .map(|term| match term {
                Term::Object(object) => Some(*object),
                Term::Variable(_) => None,
            })
            .collect(),
    }
}

/// Reduces every schema to its group-covered adds and deletes, or `None` when
/// some schema breaks the case analysis the cuts rely on.
fn transitions(domain: &Domain, instance: &Instance) -> Option<Vec<Transitions>> {
    let mut out = Vec::new();
    for (index, schema) in domain.actions.iter().enumerate() {
        let mut adds = Vec::new();
        let mut deletes = Vec::new();
        for effect in &schema.effects {
            let (atom, positive) = match &effect.literal {
                Literal::Atom(atom) => (atom, true),
                Literal::Negation(atom) => (atom, false),
            };
            if !instance.covers(atom.predicate) {
                continue;
            }
            // A conditional or quantified effect over a group predicate may fire
            // or not, so it is neither reliably a transition nor reliably not
            // one. Abandon the group rather than guess.
            if effect.conditional() || !effect.parameters.is_empty() {
                return None;
            }
            if positive {
                adds.push(atom.clone());
            } else {
                deletes.push(atom.clone());
            }
        }
        // Adding a group atom without deleting one would let two values of the
        // same variable hold, so the group is not fact-alternating after all.
        if !adds.is_empty() && deletes.is_empty() {
            return None;
        }
        if !adds.is_empty() {
            out.push(Transitions {
                schema: index,
                name: schema.name.clone(),
                parameters: schema.parameters.clone(),
                adds,
                deletes,
            });
        }
    }
    Some(out)
}

struct Graph {
    nodes: Vec<PartialAtom>,
    edges: Vec<(usize, usize, ActionInstance)>,
}

/// Explores the instance's values forward from its initial one.
fn build(instance: &Instance, transitions: &[Transitions], initial: PartialAtom) -> Option<Graph> {
    let mut graph = Graph {
        nodes: vec![initial],
        edges: Vec::new(),
    };
    let mut frontier = vec![0usize];
    while let Some(index) = frontier.pop() {
        let from = graph.nodes[index].clone();
        for transition in transitions {
            for deleted in &transition.deletes {
                for sigma in instance.bind(deleted, &[]) {
                    let Some(sigma) = unify(deleted, &from, sigma) else {
                        continue;
                    };
                    for added in &transition.adds {
                        for sigma in instance.bind(added, &sigma) {
                            let target = specialise(added, &sigma);
                            let to = match graph.nodes.iter().position(|node| *node == target) {
                                Some(existing) => existing,
                                None => {
                                    if graph.nodes.len() >= MAX_NODES {
                                        return None;
                                    }
                                    graph.nodes.push(target);
                                    frontier.push(graph.nodes.len() - 1);
                                    graph.nodes.len() - 1
                                }
                            };
                            let edge = (index, to, instantiate(transition, &sigma));
                            if !graph.edges.contains(&edge) {
                                graph.edges.push(edge);
                            }
                        }
                    }
                }
            }
        }
    }
    Some(graph)
}

/// Specialises `sigma` so that a schema atom denotes the node's value.
fn unify(
    atom: &Atom,
    node: &PartialAtom,
    mut sigma: Vec<(Variable, Object)>,
) -> Option<Vec<(Variable, Object)>> {
    if atom.predicate != node.predicate || atom.terms.len() != node.args.len() {
        return None;
    }
    for (term, arg) in atom.terms.iter().zip(&node.args) {
        let Some(wanted) = arg else { continue };
        if !bind_term(term, *wanted, &mut sigma) {
            return None;
        }
    }
    Some(sigma)
}

fn specialise(atom: &Atom, sigma: &[(Variable, Object)]) -> PartialAtom {
    PartialAtom {
        predicate: atom.predicate,
        args: atom
            .terms
            .iter()
            .map(|term| match term {
                Term::Object(object) => Some(*object),
                Term::Variable(variable) => sigma
                    .iter()
                    .find(|(bound, _)| bound == variable)
                    .map(|(_, object)| *object),
            })
            .collect(),
    }
}

/// The edge's action, with every parameter the binding reached pinned.
fn instantiate(transition: &Transitions, sigma: &[(Variable, Object)]) -> ActionInstance {
    ActionInstance {
        schema: transition.schema,
        name: transition.name.clone(),
        args: transition
            .parameters
            .iter()
            .map(|parameter| {
                sigma
                    .iter()
                    .find(|(bound, _)| bound == parameter)
                    .map(|(_, object)| *object)
            })
            .collect(),
    }
}

/// Whether two partially ground atoms have a common instance.
fn unifiable(left: &PartialAtom, right: &PartialAtom) -> bool {
    left.predicate == right.predicate
        && left.args.len() == right.args.len()
        && left
            .args
            .iter()
            .zip(&right.args)
            .all(|(a, b)| match (a, b) {
                (Some(x), Some(y)) => x == y,
                _ => true,
            })
}

/// Peels cuts off the graph, from the goal end back towards the initial value.
fn cut(graph: &Graph, landmark: &PartialAtom) -> Vec<DisjunctiveActionLandmark> {
    let mut blocked: Vec<bool> = graph
        .nodes
        .iter()
        .map(|node| unifiable(node, landmark))
        .collect();
    let mut out = Vec::new();
    for _ in 0..MAX_CUTS {
        // The initial value is itself a possible goal value: nothing left.
        if blocked[0] {
            break;
        }
        let reach = reachable(graph, &blocked);
        let mut alternatives: Vec<ActionInstance> = Vec::new();
        let mut sources: Vec<usize> = Vec::new();
        for (from, to, action) in &graph.edges {
            if !reach[*from] || !blocked[*to] {
                continue;
            }
            if !alternatives.contains(action) {
                alternatives.push(action.clone());
            }
            if !sources.contains(from) {
                sources.push(*from);
            }
        }
        // No edge crosses into the target set: it is unreachable in this graph,
        // and there is nothing sound left to say.
        if alternatives.is_empty() {
            break;
        }
        out.push(DisjunctiveActionLandmark { alternatives });
        for source in sources {
            blocked[source] = true;
        }
    }
    out
}

/// Nodes reachable from the initial value without entering the target set.
fn reachable(graph: &Graph, blocked: &[bool]) -> Vec<bool> {
    let mut seen = vec![false; graph.nodes.len()];
    seen[0] = true;
    let mut frontier = vec![0usize];
    while let Some(node) = frontier.pop() {
        for (from, to, _) in &graph.edges {
            if *from == node && !seen[*to] && !blocked[*to] {
                seen[*to] = true;
                frontier.push(*to);
            }
        }
    }
    seen
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

    /// A landmark the initial state already satisfies needs no action at all, so
    /// there is nothing to cut. This is the `blocked[0]` exit, and getting it
    /// wrong would invent a landmark out of an empty graph.
    #[test]
    fn a_landmark_the_initial_state_holds_yields_no_cut() {
        let (domain, problem) = fixture("examples/ferry-domain.pddl", "examples/test-ferry.pddl");
        let mutexes = LiftedMutexes::synthesise(&domain, &problem);
        let mut tested = 0;
        for atom in &problem.init_order {
            let landmark = ground_partial(atom);
            if instance_of(&mutexes, &landmark).is_none() {
                continue;
            }
            tested += 1;
            assert!(
                cuts(&domain, &problem, &mutexes, &landmark).is_empty(),
                "cut an initial value off from itself: {landmark:?}"
            );
        }
        assert!(tested > 0, "no initial atom belonged to a mutex group");
    }

    /// The cuts come back goal-end first, which is what makes consecutive pairs
    /// an ordering. Ferry's last cut is the one against the car's own starting
    /// location, so it is the one with every argument pinned, while the cut
    /// nearest the goal cannot know where the car will be put down.
    #[test]
    fn the_cuts_run_backwards_from_the_goal() {
        let (domain, problem) = fixture("examples/ferry-domain.pddl", "examples/test-ferry.pddl");
        let mutexes = LiftedMutexes::synthesise(&domain, &problem);
        let landmarks = crate::landmarks::LiftedLandmarks::extract(&domain, &problem);
        let sequence = landmarks
            .landmarks()
            .iter()
            .map(|landmark| cuts(&domain, &problem, &mutexes, landmark))
            .find(|found| found.len() > 1)
            .expect("no landmark produced more than one cut");

        let first_free = sequence[0]
            .alternatives
            .iter()
            .any(|action| action.args.iter().any(|argument| argument.is_none()));
        let last_pinned = sequence[sequence.len() - 1]
            .alternatives
            .iter()
            .all(|action| action.args.iter().all(|argument| argument.is_some()));
        assert!(
            first_free && last_pinned,
            "the cut order is not goal-end first: {sequence:?}"
        );
    }
}
