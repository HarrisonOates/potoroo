//! Object-symmetry pruning of achievers (Fox & Long, IJCAI 1999).
//!
//! Objects are interchangeable when their transposition preserves the initial
//! state and action costs and neither is named in the goal. A refinement may
//! introduce only the first unused objects of each equivalence class. Other
//! candidates have equivalent siblings under renaming.
//!
//! Classes use PDDL object names so literal and finite-domain search can share
//! the same checks.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::domain::Domain;
use crate::expressions::Fluent;
use crate::formula::{Atom, Formula};
use crate::problem::Problem;
use crate::terms::{Object, Term};

/// The task's interchangeable objects, grouped into classes.
#[derive(Debug, Clone, Default)]
pub struct ObjectSymmetries {
    /// Each class in its canonical order — declaration order of the objects —
    /// as lower-case names. Only classes of two or more.
    classes: Vec<Vec<String>>,
    /// Lower-case object name to `(class, rank)`.
    by_name: HashMap<String, (usize, usize)>,
    /// The same, by object id, for the literal representation.
    by_object: HashMap<Object, (usize, usize)>,
    /// Each class in canonical order, by object id.
    members: Vec<Vec<Object>>,
}

impl ObjectSymmetries {
    #[allow(clippy::needless_range_loop)]
    pub fn compute(domain: &Domain, problem: &Problem) -> Self {
        let constants = Some(&domain.constants);

        // Objects the goal names are told apart by the goal itself.
        let mut fixed: HashSet<Object> = HashSet::new();
        collect_objects(&problem.goal, &mut fixed);

        // Domain constants are named by the schemas, which the transposition
        // does not touch, so only the problem's own objects are candidates.
        let candidates: Vec<Object> = problem
            .objects
            .owned_objects()
            .map(|(object, _)| object)
            .filter(|object| !fixed.contains(object))
            .collect();

        // The atoms and cost assignments each candidate appears in.
        let atoms: Vec<&Atom> = problem.init_atoms.iter().collect();
        let mut atom_mentions: HashMap<Object, Vec<usize>> = HashMap::new();
        for (index, atom) in atoms.iter().enumerate() {
            for term in &atom.terms {
                if let Term::Object(object) = term {
                    atom_mentions.entry(*object).or_default().push(index);
                }
            }
        }
        let mut value_mentions: HashMap<Object, Vec<usize>> = HashMap::new();
        for (index, (fluent, _)) in problem.init_values.iter().enumerate() {
            for term in &fluent.terms {
                if let Term::Object(object) = term {
                    value_mentions.entry(*object).or_default().push(index);
                }
            }
        }

        // A cheap signature cuts the pairs to test: two interchangeable objects
        // have the same type and appear in the same predicates at the same
        // positions the same number of times.
        let signature = |object: Object| {
            let mut shape: Vec<(u32, usize)> = atom_mentions
                .get(&object)
                .into_iter()
                .flatten()
                .flat_map(|&index| {
                    let atom = atoms[index];
                    atom.terms
                        .iter()
                        .enumerate()
                        .filter(move |(_, term)| **term == Term::Object(object))
                        .map(move |(position, _)| (atom.predicate.0, position))
                })
                .collect();
            shape.sort_unstable();
            let values = value_mentions.get(&object).map_or(0, Vec::len);
            (
                problem.objects.object_type(constants, object),
                shape,
                values,
            )
        };
        let signatures: Vec<_> = candidates.iter().map(|&object| signature(object)).collect();

        let mut parent: Vec<usize> = (0..candidates.len()).collect();
        fn find(parent: &mut [usize], i: usize) -> usize {
            let mut root = i;
            while parent[root] != root {
                root = parent[root];
            }
            let mut walk = i;
            while parent[walk] != root {
                let next = parent[walk];
                parent[walk] = root;
                walk = next;
            }
            root
        }
        for i in 0..candidates.len() {
            for j in i + 1..candidates.len() {
                if signatures[i] != signatures[j] {
                    continue;
                }
                let (a, b) = (candidates[i], candidates[j]);
                if find(&mut parent, i) == find(&mut parent, j) {
                    continue;
                }
                if interchangeable(problem, &atoms, &atom_mentions, &value_mentions, a, b) {
                    let (ra, rb) = (find(&mut parent, i), find(&mut parent, j));
                    parent[ra] = rb;
                }
            }
        }

        // Classes in declaration order, which is also the canonical order.
        let mut members: HashMap<usize, Vec<Object>> = HashMap::new();
        for i in 0..candidates.len() {
            let root = find(&mut parent, i);
            members.entry(root).or_default().push(candidates[i]);
        }
        let mut classes: Vec<Vec<Object>> = members
            .into_values()
            .filter(|class| class.len() >= 2)
            .collect();
        for class in &mut classes {
            class.sort_by_key(|object| object.0);
        }
        classes.sort_by_key(|class| class[0].0);

        let mut by_name = HashMap::new();
        let mut by_object = HashMap::new();
        let named: Vec<Vec<String>> = classes
            .iter()
            .enumerate()
            .map(|(class_index, class)| {
                class
                    .iter()
                    .enumerate()
                    .map(|(rank, &object)| {
                        let name = problem
                            .objects
                            .object_name(constants, object)
                            .to_ascii_lowercase();
                        by_name.insert(name.clone(), (class_index, rank));
                        by_object.insert(object, (class_index, rank));
                        name
                    })
                    .collect()
            })
            .collect();
        ObjectSymmetries {
            classes: named,
            by_name,
            by_object,
            members: classes,
        }
    }

    /// Whether a step with these arguments is the canonical choice for a plan
    /// whose used objects `used` recognises: in every class, the objects the
    /// step introduces are the first ones the plan has not used. The ground
    /// literal representation's reading of [`SymmetryTable::canonical`].
    pub fn canonical_arguments(&self, arguments: &[Object], used: impl Fn(Object) -> bool) -> bool {
        for &argument in arguments {
            let Some((class, rank)) = self.by_object(argument) else {
                continue;
            };
            if used(argument) {
                continue;
            }
            // Every earlier member of the class must be used already or be
            // introduced by this same step.
            let earlier = &self.members[class][..rank];
            if earlier
                .iter()
                .any(|&other| !used(other) && !arguments.contains(&other))
            {
                return false;
            }
        }
        true
    }

    pub fn is_empty(&self) -> bool {
        self.classes.is_empty()
    }

    /// The classes, each in canonical order.
    pub fn classes(&self) -> &[Vec<String>] {
        &self.classes
    }

    /// The class and rank of an object, by (case-insensitive) name.
    pub fn by_name(&self, name: &str) -> Option<(usize, usize)> {
        self.by_name
            .get(name)
            .or_else(|| self.by_name.get(&name.to_ascii_lowercase()))
            .copied()
    }

    /// The class and rank of an object, by id.
    pub fn by_object(&self, object: Object) -> Option<(usize, usize)> {
        self.by_object.get(&object).copied()
    }

    /// One line for the telemetry: how many classes, of what sizes.
    pub fn summary(&self) -> String {
        let sizes: Vec<String> = self
            .classes
            .iter()
            .map(|class| class.len().to_string())
            .collect();
        format!(
            "{} interchangeable-object class(es) of size {}",
            self.classes.len(),
            sizes.join(", ")
        )
    }
}

/// Whether the transposition `(a b)` maps the initial state and the cost
/// assignments onto themselves. Atoms mentioning neither object are fixed, and
/// a transposition is its own inverse, so it suffices that every atom
/// mentioning either has its image in the initial state.
fn interchangeable(
    problem: &Problem,
    atoms: &[&Atom],
    atom_mentions: &HashMap<Object, Vec<usize>>,
    value_mentions: &HashMap<Object, Vec<usize>>,
    a: Object,
    b: Object,
) -> bool {
    let swap = |term: &Term| match term {
        Term::Object(o) if *o == a => Term::Object(b),
        Term::Object(o) if *o == b => Term::Object(a),
        other => *other,
    };
    let mentioned = |mentions: &HashMap<Object, Vec<usize>>| -> Vec<usize> {
        let mut all: Vec<usize> = mentions
            .get(&a)
            .into_iter()
            .chain(mentions.get(&b))
            .flatten()
            .copied()
            .collect();
        all.sort_unstable();
        all.dedup();
        all
    };
    for index in mentioned(atom_mentions) {
        let atom = atoms[index];
        let image = Atom {
            predicate: atom.predicate,
            terms: atom.terms.iter().map(swap).collect(),
        };
        if !problem.init_atoms.contains(&image) {
            return false;
        }
    }
    for index in mentioned(value_mentions) {
        let (fluent, value) = &problem.init_values[index];
        let image = Fluent {
            function: fluent.function,
            terms: fluent.terms.iter().map(swap).collect(),
        };
        let matched = problem
            .init_values
            .iter()
            .any(|(other, other_value)| *other == image && other_value == value);
        if !matched {
            return false;
        }
    }
    true
}

/// Every object a formula names, anywhere.
fn collect_objects(formula: &Rc<Formula>, out: &mut HashSet<Object>) {
    match &**formula {
        Formula::True | Formula::False => {}
        Formula::Atom(atom) | Formula::Negation(atom) => {
            for term in &atom.terms {
                if let Term::Object(object) = term {
                    out.insert(*object);
                }
            }
        }
        Formula::Equality { left, right, .. } | Formula::Inequality { left, right, .. } => {
            for term in [left, right] {
                if let Term::Object(object) = term {
                    out.insert(*object);
                }
            }
        }
        Formula::Conjunction(parts) | Formula::Disjunction(parts) => {
            for part in parts {
                collect_objects(part, out);
            }
        }
        Formula::Exists { body, .. } | Formula::Forall { body, .. } => collect_objects(body, out),
    }
}

/// The classes laid out for a ground task: every symmetric object gets one
/// index, classes are contiguous, and each operator knows which indices it
/// mentions. The candidate test then needs no names.
#[derive(Debug, Clone)]
pub struct SymmetryTable {
    /// First index of each class.
    offsets: Vec<usize>,
    /// Size of each class.
    sizes: Vec<usize>,
    /// The symmetric objects each operator mentions, as sorted indices.
    per_operator: Vec<Vec<usize>>,
    total: usize,
}

impl SymmetryTable {
    /// Lays the classes out over operators given by their argument names.
    pub fn from_names<'n>(
        symmetries: &ObjectSymmetries,
        operators: impl Iterator<Item = impl Iterator<Item = &'n str>>,
    ) -> Self {
        Self::build(
            symmetries,
            operators.map(|arguments| {
                arguments
                    .filter_map(|name| symmetries.by_name(name))
                    .collect()
            }),
        )
    }

    /// Lays the classes out over operators given by their argument objects.
    pub fn from_objects<'o>(
        symmetries: &ObjectSymmetries,
        operators: impl Iterator<Item = &'o [Object]>,
    ) -> Self {
        Self::build(
            symmetries,
            operators.map(|arguments| {
                arguments
                    .iter()
                    .filter_map(|&object| symmetries.by_object(object))
                    .collect()
            }),
        )
    }

    fn build(
        symmetries: &ObjectSymmetries,
        operators: impl Iterator<Item = Vec<(usize, usize)>>,
    ) -> Self {
        let sizes: Vec<usize> = symmetries.classes.iter().map(Vec::len).collect();
        let mut offsets = Vec::with_capacity(sizes.len());
        let mut total = 0;
        for &size in &sizes {
            offsets.push(total);
            total += size;
        }
        let per_operator = operators
            .map(|mentions| {
                let mut indices: Vec<usize> = mentions
                    .into_iter()
                    .map(|(class, rank)| offsets[class] + rank)
                    .collect();
                indices.sort_unstable();
                indices.dedup();
                indices
            })
            .collect();
        SymmetryTable {
            offsets,
            sizes,
            per_operator,
            total,
        }
    }

    /// Number of symmetric objects; the length of a `used` slice.
    pub fn len(&self) -> usize {
        self.total
    }

    pub fn is_empty(&self) -> bool {
        self.total == 0
    }

    /// Marks the symmetric objects `operator` mentions as used by the plan.
    pub fn mark_used(&self, operator: usize, used: &mut [bool]) {
        for &index in &self.per_operator[operator] {
            used[index] = true;
        }
    }

    /// Whether adding a step of `operator` to a plan using exactly the objects
    /// marked in `used` is the canonical choice: in every class, the objects
    /// it introduces are the first ones the plan has not used.
    #[allow(clippy::needless_range_loop)]
    pub fn canonical(&self, operator: usize, used: &[bool]) -> bool {
        let mentions = &self.per_operator[operator];
        let mut at = 0;
        while at < mentions.len() {
            // One class at a time: the mentions are sorted and classes are
            // contiguous, so a class's mentions are a run.
            let class = self
                .offsets
                .partition_point(|&offset| offset <= mentions[at])
                - 1;
            let (start, end) = (self.offsets[class], self.offsets[class] + self.sizes[class]);
            let run_end = at + mentions[at..].partition_point(|&index| index < end);
            let mut wanted = mentions[at..run_end].iter().filter(|&&index| !used[index]);
            let mut next = wanted.next();
            for index in start..end {
                let Some(&want) = next else { break };
                if used[index] {
                    continue;
                }
                if index != want {
                    return false;
                }
                next = wanted.next();
            }
            at = run_end;
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn table(classes: &[&[&str]], operators: &[&[&str]]) -> SymmetryTable {
        let mut symmetries = ObjectSymmetries::default();
        for (class_index, class) in classes.iter().enumerate() {
            symmetries
                .classes
                .push(class.iter().map(|s| s.to_string()).collect());
            for (rank, name) in class.iter().enumerate() {
                symmetries
                    .by_name
                    .insert(name.to_string(), (class_index, rank));
            }
        }
        SymmetryTable::from_names(
            &symmetries,
            operators.iter().map(|arguments| arguments.iter().copied()),
        )
    }

    #[test]
    fn the_first_unused_object_of_a_class_is_canonical() {
        let t = table(
            &[&["t1", "t2", "t3"]],
            &[&["t1", "a"], &["t2", "a"], &["t3", "a"]],
        );
        let mut used = vec![false; t.len()];
        assert!(t.canonical(0, &used));
        assert!(!t.canonical(1, &used));
        assert!(!t.canonical(2, &used));
        t.mark_used(0, &mut used);
        assert!(t.canonical(0, &used));
        assert!(t.canonical(1, &used));
        assert!(!t.canonical(2, &used));
    }

    #[test]
    fn two_new_objects_must_be_the_first_two() {
        let t = table(
            &[&["a", "b", "c"]],
            &[&["a", "b"], &["a", "c"], &["b", "c"]],
        );
        let used = vec![false; t.len()];
        assert!(t.canonical(0, &used));
        assert!(!t.canonical(1, &used));
        assert!(!t.canonical(2, &used));
        // With `a` used, `b` is the first unused: `[a, c]` skips it.
        let used = vec![true, false, false];
        assert!(t.canonical(2, &used));
        assert!(!t.canonical(1, &used));
    }

    #[test]
    fn classes_are_independent() {
        let t = table(
            &[&["t1", "t2"], &["p1", "p2"]],
            &[&["t2", "p1"], &["t1", "p2"], &["t1", "p1"]],
        );
        let used = vec![false; t.len()];
        assert!(!t.canonical(0, &used));
        assert!(!t.canonical(1, &used));
        assert!(t.canonical(2, &used));
    }

    #[test]
    fn an_operator_naming_no_symmetric_object_is_always_canonical() {
        let t = table(&[&["a", "b"]], &[&["x", "y"]]);
        assert!(t.canonical(0, &[false, false]));
    }
}
