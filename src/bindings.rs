//! Variable binding constraints.
//!
//! A [`Bindings`] is a chain of [`Varset`]s. Each varset is an equality class
//! of step-variables (`(Variable, step_id)`) optionally pinned to a constant
//! object, with a non-codesignation list and a most-specific type. Adding
//! equality/inequality bindings merges or separates varsets, returning a fresh
//! `Bindings` (`None` when inconsistent). For ground actions every term is
//! already an object, so the same interface degenerates to constant equality
//! checks.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::chain::{self, Chain};
use crate::fasthash::{FastMap, FastSet};
use crate::formula::{Formula, Literal};
use crate::terms::{Object, Term, TermTable, Variable};
use crate::types::{Type, Types};

/// A variable scoped to a step.
pub type StepVariable = (Variable, usize);

/// A single variable binding (equality or inequality).
#[derive(Debug, Clone, Copy)]
pub struct Binding {
    pub var: Variable,
    pub var_id: usize,
    pub term: Term,
    pub term_id: usize,
    pub equality: bool,
}

impl Binding {
    pub fn new(var: Variable, var_id: usize, term: Term, term_id: usize, equality: bool) -> Self {
        Binding {
            var,
            var_id,
            term,
            term_id,
            equality,
        }
    }
}

/// Resolver for the variable types in effect at a given step. Each step's
/// action carries its own `var_types`. Implemented by the search context.
pub trait StepVarTypes {
    fn var_type(&self, var: Variable, step_id: usize) -> Type;
}

/// Helper bundling the type tables and the problem objects needed for type
/// reasoning and grounding.
#[derive(Clone, Copy)]
pub struct TypeContext<'a> {
    pub types: &'a Types,
    /// Problem objects table (extends the domain constants).
    pub objects: &'a TermTable,
    /// Domain constants table (parent of `objects`).
    pub constants: &'a TermTable,
    /// Per-step variable-type resolver.
    pub step_vars: &'a dyn StepVarTypes,
}

impl<'a> TypeContext<'a> {
    fn term_type(&self, term: Term, step_id: usize) -> Type {
        match term {
            Term::Object(o) => self.object_type(o),
            Term::Variable(v) => self.step_vars.var_type(v, step_id),
        }
    }

    fn variable_type(&self, v: Variable, step_id: usize) -> Type {
        self.step_vars.var_type(v, step_id)
    }

    fn object_type(&self, o: Object) -> Type {
        self.objects.object_type(Some(self.constants), o)
    }

    /// Most specific common subtype, or `None` if incompatible.
    fn most_specific(&self, t1: Type, t2: Type) -> Option<Type> {
        if self.types.subtype(t1, t2) {
            Some(t1)
        } else if self.types.subtype(t2, t1) {
            Some(t2)
        } else {
            None
        }
    }

    /// How many objects are compatible with `ty` and not in `excluded`.
    /// The counting counterpart of [`TypeContext::compatible_objects`], for
    /// callers that only need the cardinality and should not allocate.
    pub(crate) fn count_compatible_objects(&self, ty: Type, excluded: &[Object]) -> usize {
        self.constants
            .owned_objects()
            .chain(self.objects.owned_objects())
            .filter(|(o, oty)| self.types.subtype(*oty, ty) && !excluded.contains(o))
            .count()
    }

    /// Objects compatible with `ty` (type-subtype), from objects + constants.
    pub(crate) fn compatible_objects(&self, ty: Type) -> Vec<Object> {
        let mut result = Vec::new();
        for (o, oty) in self.constants.owned_objects() {
            if self.types.subtype(oty, ty) {
                result.push(o);
            }
        }
        for (o, oty) in self.objects.owned_objects() {
            if self.types.subtype(oty, ty) {
                result.push(o);
            }
        }
        result
    }
}

/// A variable codesignation / non-codesignation class.
#[derive(Debug)]
struct Varset {
    /// The constant this class is pinned to, if any.
    constant: Option<Object>,
    /// Codesignated step-variables.
    cd_set: Option<Rc<Chain<StepVariable>>>,
    /// Non-codesignated step-variables.
    ncd_set: Option<Rc<Chain<StepVariable>>>,
    /// Most specific type of any member.
    ty: Type,
}

impl Varset {
    fn includes_object(&self, obj: Object) -> bool {
        self.constant == Some(obj)
    }

    fn includes_var(&self, var: Variable, step_id: usize) -> bool {
        chain::iter(&self.cd_set).any(|sv| sv.0 == var && sv.1 == step_id)
    }

    fn excludes_var(&self, var: Variable, step_id: usize) -> bool {
        chain::iter(&self.ncd_set).any(|sv| sv.0 == var && sv.1 == step_id)
    }

    /// Adds an object to this varset, or `None` if excluded.
    fn add_object(&self, ctx: &TypeContext, obj: Object) -> Option<Varset> {
        if let Some(c) = self.constant {
            if c == obj {
                Some(self.clone_shallow())
            } else {
                None
            }
        } else {
            let ot = ctx.object_type(obj);
            if ctx.types.subtype(ot, self.ty) {
                Some(Varset {
                    constant: Some(obj),
                    cd_set: self.cd_set.clone(),
                    ncd_set: self.ncd_set.clone(),
                    ty: ot,
                })
            } else {
                None
            }
        }
    }

    /// Adds a variable to this varset, or `None` if excluded/incompatible.
    fn add_var(&self, ctx: &TypeContext, var: Variable, step_id: usize) -> Option<Varset> {
        if self.excludes_var(var, step_id) {
            return None;
        }
        let var_ty = ctx.variable_type(var, step_id);
        let tt = if self.constant.is_some() {
            if !ctx.types.subtype(self.ty, var_ty) {
                return None;
            }
            self.ty
        } else {
            ctx.most_specific(self.ty, var_ty)?
        };
        let new_cd = chain::cons((var, step_id), self.cd_set.clone());
        Some(Varset {
            constant: self.constant,
            cd_set: new_cd,
            ncd_set: self.ncd_set.clone(),
            ty: tt,
        })
    }

    fn add_term(&self, ctx: &TypeContext, term: Term, step_id: usize) -> Option<Varset> {
        match term {
            Term::Object(o) => self.add_object(ctx, o),
            Term::Variable(v) => self.add_var(ctx, v, step_id),
        }
    }

    /// Adds a variable to the non-codesignation list.
    fn restrict(&self, var: Variable, step_id: usize) -> Varset {
        let new_ncd = chain::cons((var, step_id), self.ncd_set.clone());
        Varset {
            constant: self.constant,
            cd_set: self.cd_set.clone(),
            ncd_set: new_ncd,
            ty: self.ty,
        }
    }

    fn clone_shallow(&self) -> Varset {
        Varset {
            constant: self.constant,
            cd_set: self.cd_set.clone(),
            ncd_set: self.ncd_set.clone(),
            ty: self.ty,
        }
    }

    /// Combines two varsets, or `None` if inconsistent.
    fn combine(&self, ctx: &TypeContext, vs: &Varset) -> Option<Varset> {
        let comb_obj;
        let tt;
        if let Some(c1) = self.constant {
            if let Some(c2) = vs.constant {
                if c1 != c2 {
                    return None;
                }
            } else if !ctx.types.subtype(self.ty, vs.ty) {
                return None;
            }
            comb_obj = Some(c1);
            tt = self.ty;
        } else if let Some(c2) = vs.constant {
            if !ctx.types.subtype(vs.ty, self.ty) {
                return None;
            }
            comb_obj = Some(c2);
            tt = vs.ty;
        } else {
            comb_obj = None;
            tt = ctx.most_specific(self.ty, vs.ty)?;
        }
        // Combined codesignation list: self.cd ++ vs.cd, rejecting any vs.cd
        // member that self excludes.
        let mut comb_cd = self.cd_set.clone();
        for sv in chain::iter(&vs.cd_set) {
            if self.excludes_var(sv.0, sv.1) {
                return None;
            }
            comb_cd = chain::cons(*sv, comb_cd);
        }
        // Combined non-codesignation list: self.ncd ++ (vs.ncd not already
        // included/excluded by self), rejecting any vs.ncd member self includes.
        let mut comb_ncd = self.ncd_set.clone();
        for sv in chain::iter(&vs.ncd_set) {
            if self.includes_var(sv.0, sv.1) {
                return None;
            } else if !self.excludes_var(sv.0, sv.1) {
                comb_ncd = chain::cons(*sv, comb_ncd);
            }
        }
        Some(Varset {
            constant: comb_obj,
            cd_set: comb_cd,
            ncd_set: comb_ncd,
            ty: tt,
        })
    }

    /// Builds the varset representing a single binding.
    fn make(ctx: &TypeContext, b: &Binding, reverse: bool) -> Option<Varset> {
        if b.equality {
            let cd0 = chain::cons((b.var, b.var_id), None);
            match b.term {
                Term::Object(obj) => Some(Varset {
                    constant: Some(obj),
                    cd_set: cd0,
                    ncd_set: None,
                    ty: ctx.object_type(obj),
                }),
                Term::Variable(tv) => {
                    let tt = ctx.most_specific(
                        ctx.variable_type(b.var, b.var_id),
                        ctx.variable_type(tv, b.term_id),
                    )?;
                    let cd = chain::cons((tv, b.term_id), cd0);
                    Some(Varset {
                        constant: None,
                        cd_set: cd,
                        ncd_set: None,
                        ty: tt,
                    })
                }
            }
        } else if reverse {
            let ncd = chain::cons((b.var, b.var_id), None);
            match b.term {
                Term::Object(obj) => Some(Varset {
                    constant: Some(obj),
                    cd_set: None,
                    ncd_set: ncd,
                    ty: ctx.object_type(obj),
                }),
                Term::Variable(tv) => {
                    let cd = chain::cons((tv, b.term_id), None);
                    Some(Varset {
                        constant: None,
                        cd_set: cd,
                        ncd_set: ncd,
                        ty: ctx.variable_type(tv, b.term_id),
                    })
                }
            }
        } else {
            match b.term {
                Term::Object(_) => None,
                Term::Variable(tv) => {
                    let cd = chain::cons((b.var, b.var_id), None);
                    let ncd = chain::cons((tv, b.term_id), None);
                    Some(Varset {
                        constant: None,
                        cd_set: cd,
                        ncd_set: ncd,
                        ty: ctx.variable_type(b.var, b.var_id),
                    })
                }
            }
        }
    }
}

/// An index key and its class ID in one hash-table entry. Equality and hashing
/// use only the step-variable: inserting an older occurrence must preserve the
/// class already recorded for the newest one. Keeping the ID beside the u32
/// variable uses the padding a `(Variable, usize)` key would otherwise need.
#[derive(Debug)]
struct IndexedVariable {
    var: Variable,
    class: u32,
    step_id: usize,
}

impl PartialEq for IndexedVariable {
    fn eq(&self, other: &Self) -> bool {
        self.var == other.var && self.step_id == other.step_id
    }
}

impl Eq for IndexedVariable {}

impl Hash for IndexedVariable {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.var, self.step_id).hash(state);
    }
}

/// Lazily-built lookup index over an immutable varset chain: the authoritative
/// (newest) varset node per step-variable and per pinned constant, plus the
/// constants excluded per step-variable through pinned classes'
/// non-codesignation lists. Replaces the O(chain) linear scans on the hot
/// lookup paths; positions are relative to the chain head so shadowed (stale)
/// entries never win.
#[derive(Debug, Default)]
struct VarsetIndex {
    vars: FastSet<IndexedVariable>,
    objs: FastMap<Object, u32>,
    /// Store a position and node reference once per authoritative class rather
    /// than repeating them for every variable and constant in that class.
    classes: Box<[(usize, Rc<Chain<Varset>>)]>,
    ncd_constants: FastMap<StepVariable, Vec<Object>>,
}

/// Chains shorter than this are scanned linearly: for them the hash-map build
/// costs more than the scans it replaces. Above it an index is built on first
/// use — children then inherit it (see [`Bindings::add`]), so the build is
/// amortised over a whole subtree rather than repeated per node.
const INDEX_THRESHOLD: usize = 8;

/// Longest prefix of not-yet-indexed varsets tolerated in front of an
/// inherited index before the chain is re-indexed from scratch. Bounds the
/// per-`resolve_pattern` exclusion scan, while amortising the O(chain)
/// rebuild over at least this many generations of child bindings.
const MAX_INDEX_PREFIX: usize = 32;

/// Maximum number of variables and constants in the unindexed prefix.
/// Bounds lookup work even when a prefix contains large equality classes.
const MAX_PREFIX_MEMBERS: usize = 96;

/// Whether a chain is worth indexing (cached alongside the index itself).
#[derive(Debug, Clone)]
enum IndexState {
    /// Scan directly: short chains, or an index too large for u32 class IDs.
    Small,
    /// Index over a suffix of the chain. The first `prefix` (newest) varsets
    /// are scanned directly before the index answers for the rest. Reusing
    /// the varsets avoids allocating a second chain of lookup entries for
    /// their members. Index positions are relative to the indexed suffix,
    /// so `prefix` is added on the way out.
    Built {
        prefix: usize,
        prefix_members: usize,
        ix: Rc<VarsetIndex>,
    },
}

/// Indexed lookup for a step-variable: scans the unindexed prefix (newest
/// first), then the index with head-relative positions. Resolution order is
/// identical to a full `scan_var`.
fn lookup_var_in(
    state: &IndexState,
    varsets: &Option<Rc<Chain<Varset>>>,
    var: Variable,
    step_id: usize,
) -> Option<(usize, Rc<Chain<Varset>>)> {
    match state {
        IndexState::Small => scan_var(varsets, var, step_id, usize::MAX),
        IndexState::Built { prefix, ix, .. } => {
            scan_var(varsets, var, step_id, *prefix).or_else(|| {
                ix.vars
                    .get(&IndexedVariable {
                        var,
                        class: 0,
                        step_id,
                    })
                    .map(|entry| {
                        let (p, n) = &ix.classes[entry.class as usize];
                        (p + prefix, n.clone())
                    })
            })
        }
    }
}

/// Indexed lookup for a pinned constant; see [`lookup_var_in`].
fn lookup_obj_in(
    state: &IndexState,
    varsets: &Option<Rc<Chain<Varset>>>,
    obj: Object,
) -> Option<(usize, Rc<Chain<Varset>>)> {
    match state {
        IndexState::Small => scan_obj(varsets, obj, usize::MAX),
        IndexState::Built { prefix, ix, .. } => scan_obj(varsets, obj, *prefix).or_else(|| {
            ix.objs.get(&obj).map(|&class| {
                let (p, n) = &ix.classes[class as usize];
                (p + prefix, n.clone())
            })
        }),
    }
}

/// Head-first scan of up to `limit` varsets for a step-variable.
fn scan_var(
    varsets: &Option<Rc<Chain<Varset>>>,
    var: Variable,
    step_id: usize,
    limit: usize,
) -> Option<(usize, Rc<Chain<Varset>>)> {
    let mut cur = varsets;
    for p in 0..limit {
        let node = cur.as_ref()?;
        if node.head.includes_var(var, step_id) {
            return Some((p, node.clone()));
        }
        cur = &node.tail;
    }
    None
}

/// Head-first scan of up to `limit` varsets for a pinned constant.
fn scan_obj(
    varsets: &Option<Rc<Chain<Varset>>>,
    obj: Object,
    limit: usize,
) -> Option<(usize, Rc<Chain<Varset>>)> {
    let mut cur = varsets;
    for p in 0..limit {
        let node = cur.as_ref()?;
        if node.head.includes_object(obj) {
            return Some((p, node.clone()));
        }
        cur = &node.tail;
    }
    None
}

/// A collection of variable bindings.
#[derive(Debug, Default)]
pub struct Bindings {
    /// Varsets; the head is the most recently added.
    varsets: Option<Rc<Chain<Varset>>>,
    /// Highest step id mentioned in any varset.
    high_step: usize,
    /// Chain length, maintained incrementally so the index/scan decision is
    /// O(1) — short chains never touch the cache below.
    num_varsets: usize,
    /// Lookup index, built on first use once the chain reaches
    /// [`INDEX_THRESHOLD`] and thereafter inherited by descendants, so parked
    /// plans share one table rather than each holding their own.
    index: RefCell<Option<IndexState>>,
}

/// The varset chain, high step, and chain length that adding a set of bindings
/// would produce. See [`Bindings::try_add`].
type AddedVarsets = (Option<Rc<Chain<Varset>>>, usize, usize);

impl Bindings {
    /// Variables participating in constraints, including witnesses that occur
    /// only in (in)equalities rather than in an action's parameter list.
    pub(crate) fn constrained_variables(&self) -> Vec<StepVariable> {
        let mut variables = Vec::new();
        for varset in chain::iter(&self.varsets) {
            variables.extend(chain::iter(&varset.cd_set).copied());
            variables.extend(chain::iter(&varset.ncd_set).copied());
        }
        variables.sort_unstable();
        variables.dedup();
        variables
    }

    pub fn empty() -> Rc<Bindings> {
        Rc::new(Bindings::default())
    }

    /// The lookup state, building the index on first use for long chains. The
    /// varset chain is immutable once the `Bindings` exists, so the cached
    /// state never goes stale.
    fn index_state(&self) -> IndexState {
        self.with_index_state(|state| state.clone())
    }

    /// Runs `f` against the cached lookup state without cloning it out of the
    /// cell.
    ///
    /// [`Bindings::index_state`] hands back an owned `IndexState`, which bumps
    /// and then drops an `Rc`. That is fine for callers that take it once and
    /// use it across a region, but `find_var_node` and `find_obj_node` ask per
    /// lookup, so borrowing avoids repeated reference-count updates.
    fn with_index_state<R>(&self, f: impl FnOnce(&IndexState) -> R) -> R {
        if self.num_varsets < INDEX_THRESHOLD {
            return f(&IndexState::Small);
        }
        if self.index.borrow().is_none() {
            // Built outside the borrow: construction reads `self.varsets`, and
            // holding the cell across it would risk a double borrow.
            let state = self.build_index();
            *self.index.borrow_mut() = Some(state);
        }
        let cell = self.index.borrow();
        f(cell.as_ref().expect("index built or present above"))
    }

    /// Builds the index for a long chain. The varset chain is immutable once
    /// the `Bindings` exists, so the result never goes stale.
    fn build_index(&self) -> IndexState {
        {
            let mut ix = VarsetIndex::default();
            let mut classes = Vec::new();
            let mut pos = 0usize;
            let mut cur = self.varsets.clone();
            while let Some(node) = cur {
                let Ok(class) = u32::try_from(classes.len()) else {
                    // Preserve correctness even for histories too large to
                    // index compactly; never truncate a class or a step ID.
                    return IndexState::Small;
                };
                let vs = &node.head;
                let mut used = false;
                for &(var, step_id) in chain::iter(&vs.cd_set) {
                    // First (newest) entry wins: it is the authoritative class.
                    used |= ix.vars.insert(IndexedVariable {
                        var,
                        class,
                        step_id,
                    });
                }
                if let Some(c) = vs.constant {
                    if let std::collections::hash_map::Entry::Vacant(entry) = ix.objs.entry(c) {
                        entry.insert(class);
                        used = true;
                    }
                    // Record the pinned constant against every step-variable
                    // its class non-codesignates (stale entries carry subsets
                    // of the authoritative lists, so duplicates are the only
                    // artifact).
                    for sv in chain::iter(&vs.ncd_set) {
                        let e = ix.ncd_constants.entry(*sv).or_default();
                        if !e.contains(&c) {
                            e.push(c);
                        }
                    }
                }
                if used {
                    classes.push((pos, node.clone()));
                }
                pos += 1;
                cur = node.tail.clone();
            }
            ix.classes = classes.into_boxed_slice();
            IndexState::Built {
                prefix: 0,
                prefix_members: 0,
                ix: Rc::new(ix),
            }
        }
    }

    /// Finds the authoritative varset node (and its head-relative position)
    /// for a step-variable.
    fn find_var_node(&self, var: Variable, step_id: usize) -> Option<(usize, Rc<Chain<Varset>>)> {
        let found =
            self.with_index_state(|state| lookup_var_in(state, &self.varsets, var, step_id));
        debug_assert!(
            {
                let scanned = scan_var(&self.varsets, var, step_id, usize::MAX);
                match (&found, &scanned) {
                    (None, None) => true,
                    (Some((p1, n1)), Some((p2, n2))) => p1 == p2 && Rc::ptr_eq(n1, n2),
                    _ => false,
                }
            },
            "indexed var lookup diverged from head-first scan"
        );
        found
    }

    /// Finds the authoritative varset node (and its head-relative position)
    /// for a pinned constant.
    fn find_obj_node(&self, obj: Object) -> Option<(usize, Rc<Chain<Varset>>)> {
        let found = self.with_index_state(|state| lookup_obj_in(state, &self.varsets, obj));
        debug_assert!(
            {
                let scanned = scan_obj(&self.varsets, obj, usize::MAX);
                match (&found, &scanned) {
                    (None, None) => true,
                    (Some((p1, n1)), Some((p2, n2))) => p1 == p2 && Rc::ptr_eq(n1, n2),
                    _ => false,
                }
            },
            "indexed obj lookup diverged from head-first scan"
        );
        found
    }

    /// Historically dropped the lookup index after a plan ranking so parked
    /// plans didn't each retain an O(chain) side table. The index is now
    /// `Rc`-shared down the refinement tree (see [`Bindings::add`]), so a
    /// parked plan holds one refcount, not its own table — and dropping the
    /// reference would force every descendant to rebuild from scratch, which
    /// profiling showed dominated lifted-search time. Deliberately a no-op;
    /// kept so call sites document where eviction *would* go.
    pub fn clear_index(&self) {}

    /// Returns the constant bound to `term` at `step_id`, or `term` itself when
    /// unbound.
    pub fn binding(&self, term: Term, step_id: usize) -> Term {
        if let Term::Variable(v) = term {
            if step_id <= self.high_step {
                if let Some((_, node)) = self.find_var_node(v, step_id) {
                    if let Some(c) = node.head.constant {
                        return Term::Object(c);
                    }
                }
            }
        }
        term
    }

    /// Equality already entailed by the bindings, rather than equality that
    /// could be imposed by a future refinement. Variable scope is essential:
    /// the same schema variable in two occurrences need not denote one object.
    pub(crate) fn terms_equal(
        &self,
        left: Term,
        left_step: usize,
        right: Term,
        right_step: usize,
    ) -> bool {
        let left = self.binding(left, left_step);
        let right = self.binding(right, right_step);
        match (left, right) {
            (Term::Object(a), Term::Object(b)) => a == b,
            (Term::Variable(a), Term::Variable(b)) => {
                (a == b && left_step == right_step)
                    || self
                        .find_var_node(a, left_step)
                        .is_some_and(|(_, node)| node.head.includes_var(b, right_step))
            }
            _ => false,
        }
    }

    /// A conservative proof that a scoped formula is false in this binding
    /// snapshot. Unknown literals and quantified bodies remain possible.
    pub(crate) fn contradicts(&self, formula: &Formula, step: usize) -> bool {
        match formula {
            Formula::False => true,
            Formula::Inequality {
                left,
                left_id,
                right,
                right_id,
            } => self.terms_equal(
                *left,
                left_id.unwrap_or(step),
                *right,
                right_id.unwrap_or(step),
            ),
            Formula::Equality {
                left,
                left_id,
                right,
                right_id,
            } => {
                match (
                    self.binding(*left, left_id.unwrap_or(step)),
                    self.binding(*right, right_id.unwrap_or(step)),
                ) {
                    (Term::Object(a), Term::Object(b)) => a != b,
                    _ => false,
                }
            }
            Formula::Conjunction(parts) => parts.iter().any(|p| self.contradicts(p, step)),
            Formula::Disjunction(parts) => parts.iter().all(|p| self.contradicts(p, step)),
            _ => false,
        }
    }

    /// Whether equating two terms is consistent. Used to prove that two
    /// symbolic invariant members must be distinct, including explicit
    /// inequalities and disjoint types, without assigning either variable.
    pub(crate) fn terms_can_equal(
        &self,
        ctx: &TypeContext,
        left: Term,
        left_step: usize,
        right: Term,
        right_step: usize,
    ) -> bool {
        let left = self.binding(left, left_step);
        let right = self.binding(right, right_step);
        let binding = match (left, right) {
            (Term::Object(a), Term::Object(b)) => return a == b,
            (Term::Variable(v), term) => Binding::new(v, left_step, term, right_step, true),
            (term, Term::Variable(v)) => Binding::new(v, right_step, term, left_step, true),
        };
        self.try_add(ctx, &[binding]).is_some()
    }

    /// Returns the possible objects for a step variable (its type-compatible
    /// objects minus any object excluded via non-codesignation).
    pub fn domain(&self, ctx: &TypeContext, var: Variable, step_id: usize) -> BTreeSet<Object> {
        let ty = ctx.variable_type(var, step_id);
        let mut names: BTreeSet<Object> = ctx.compatible_objects(ty).into_iter().collect();
        if step_id <= self.high_step {
            if let Some((_, node)) = self.find_var_node(var, step_id) {
                for sv in chain::iter(&node.head.ncd_set) {
                    if let Some((_, node2)) = self.find_var_node(sv.0, sv.1) {
                        if let Some(c) = node2.head.constant {
                            names.remove(&c);
                        }
                    }
                }
            }
        }
        names
    }

    /// Checks if `l1` is the negation of `l2` and the atoms unify.
    pub fn affects(
        &self,
        ctx: &TypeContext,
        l1: &Literal,
        id1: usize,
        l2: &Literal,
        id2: usize,
    ) -> bool {
        let mut mgu = Vec::new();
        self.affects_mgu(ctx, &mut mgu, l1, id1, l2, id2)
    }

    /// `affects`, collecting the unifier.
    pub fn affects_mgu(
        &self,
        ctx: &TypeContext,
        mgu: &mut Vec<Binding>,
        l1: &Literal,
        id1: usize,
        l2: &Literal,
        id2: usize,
    ) -> bool {
        match (l1, l2) {
            (Literal::Negation(a), Literal::Atom(b)) => self.unify_atoms(ctx, mgu, b, id2, a, id1),
            (Literal::Atom(a), Literal::Negation(b)) => self.unify_atoms(ctx, mgu, b, id2, a, id1),
            _ => false,
        }
    }

    /// Checks if two literals can be unified.
    pub fn unify(
        &self,
        ctx: &TypeContext,
        l1: &Literal,
        id1: usize,
        l2: &Literal,
        id2: usize,
    ) -> bool {
        let mut mgu = Vec::new();
        self.unify_mgu(ctx, &mut mgu, l1, id1, l2, id2)
    }

    /// `unify`, collecting the most general unifier.
    pub fn unify_mgu(
        &self,
        ctx: &TypeContext,
        mgu: &mut Vec<Binding>,
        l1: &Literal,
        id1: usize,
        l2: &Literal,
        id2: usize,
    ) -> bool {
        if l1.negative() != l2.negative() {
            return false;
        }
        self.unify_atoms(ctx, mgu, l1.atom(), id1, l2.atom(), id2)
    }

    /// Unification of two atoms, with no opinion about the literals' signs.
    ///
    /// Split out of [`Bindings::unify_mgu`] so `affects_mgu`, which pairs a
    /// negation's atom against a positive literal, can call it directly. It
    /// previously cloned the atom purely to wrap it in a `Literal::Atom` that
    /// would satisfy the sign check -- 703,380 allocations over a 20,000-node
    /// lifted search.
    #[allow(clippy::too_many_arguments)]
    fn unify_atoms(
        &self,
        ctx: &TypeContext,
        mgu: &mut Vec<Binding>,
        a1: &crate::formula::Atom,
        id1: usize,
        a2: &crate::formula::Atom,
        id2: usize,
    ) -> bool {
        if a1.predicate != a2.predicate {
            return false;
        }
        let g1 = is_ground(a1);
        let g2 = is_ground(a2);
        if g1 && g2 {
            // Both fully instantiated: equal iff identical terms.
            return a1.terms == a2.terms;
        } else if g1 || g2 {
            // One literal is fully instantiated.
            let (ll, lg, idl) = if g1 { (a2, a1, id2) } else { (a1, a2, id1) };
            let mut bind: Vec<(Variable, Object)> = Vec::new();
            for i in 0..ll.terms.len() {
                let term1 = ll.terms[i];
                let obj2 = lg.terms[i].as_object();
                match term1 {
                    Term::Object(o) => {
                        if o != obj2 {
                            return false;
                        }
                    }
                    Term::Variable(var1) => {
                        if let Some(&(_, bound)) = bind.iter().find(|(v, _)| *v == var1) {
                            if bound != obj2 {
                                return false;
                            }
                        } else {
                            let bt = self.binding(term1, idl);
                            match bt {
                                Term::Object(bo) => {
                                    if bo != obj2 {
                                        return false;
                                    }
                                }
                                Term::Variable(_) => {
                                    if !ctx.types.subtype(
                                        ctx.object_type(obj2),
                                        ctx.variable_type(var1, idl),
                                    ) {
                                        return false;
                                    }
                                    mgu.push(Binding::new(var1, idl, Term::Object(obj2), 0, true));
                                }
                            }
                            bind.push((var1, obj2));
                        }
                    }
                }
            }
        } else {
            // Neither literal is fully instantiated.
            for i in 0..a1.terms.len() {
                let term1 = a1.terms[i];
                let term2 = a2.terms[i];
                match (term1, term2) {
                    (Term::Object(o1), Term::Object(o2)) => {
                        if o1 != o2 {
                            return false;
                        }
                    }
                    (Term::Object(_), Term::Variable(v2)) => {
                        if !ctx
                            .types
                            .subtype(ctx.term_type(term1, id1), ctx.variable_type(v2, id2))
                        {
                            return false;
                        }
                        mgu.push(Binding::new(v2, id2, term1, 0, true));
                    }
                    (Term::Variable(v1), Term::Object(_)) => {
                        if !ctx
                            .types
                            .subtype(ctx.term_type(term2, id2), ctx.variable_type(v1, id1))
                        {
                            return false;
                        }
                        mgu.push(Binding::new(v1, id1, term2, id2, true));
                    }
                    (Term::Variable(v1), Term::Variable(v2)) => {
                        if !ctx
                            .types
                            .compatible(ctx.variable_type(v1, id1), ctx.variable_type(v2, id2))
                        {
                            return false;
                        }
                        mgu.push(Binding::new(v1, id1, term2, id2, true));
                    }
                }
            }
        }
        // Unification must be consistent with current bindings.
        self.try_add(ctx, mgu).is_some()
    }

    /// Adds `new_bindings`, returning the resulting collection or `None` if
    /// inconsistent. When `test_only` is set, the result is `Some(self)` on
    /// success (no new collection is materialized).
    pub fn add(
        self: &Rc<Self>,
        ctx: &TypeContext,
        new_bindings: &[Binding],
        test_only: bool,
    ) -> Option<Rc<Bindings>> {
        if new_bindings.is_empty() || test_only {
            // Consistency-only: confirm the bindings are consistent, but reuse
            // the existing collection.
            return self.try_add(ctx, new_bindings).map(|_| self.clone());
        }
        self.try_add(ctx, new_bindings)
            .map(|(varsets, high_step, num_varsets)| {
                // Reasserting constraints already entailed by this collection
                // changes neither its history nor its lookup index. Keep the
                // collection shared instead of allocating a wrapper per child.
                if num_varsets == self.num_varsets && high_step == self.high_step {
                    return self.clone();
                }
                // Inherit the parent's index: the child chain is the parent chain
                // plus a few consed varsets, so the parent's table stays valid
                // behind a scan of the new varsets. Once the prefix's length or
                // member count would exceed its cap the child starts
                // unindexed and the usual promotion path re-indexes from scratch,
                // resetting both to empty for its own descendants.
                let index = match self.index.borrow().as_ref() {
                    Some(IndexState::Built {
                        prefix,
                        prefix_members,
                        ix,
                    }) => {
                        let added = num_varsets - self.num_varsets;
                        let p = prefix + added;
                        if p <= MAX_INDEX_PREFIX {
                            let members = prefix_members
                                + chain::iter(&varsets)
                                    .take(added)
                                    .map(|vs| {
                                        chain::iter(&vs.cd_set).count()
                                            + usize::from(vs.constant.is_some())
                                    })
                                    .sum::<usize>();
                            (members <= MAX_PREFIX_MEMBERS).then(|| IndexState::Built {
                                prefix: p,
                                prefix_members: members,
                                ix: ix.clone(),
                            })
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                Rc::new(Bindings {
                    varsets,
                    high_step,
                    num_varsets,
                    index: RefCell::new(index),
                })
            })
    }

    /// Computes the varsets/high-step/length that would result from adding
    /// `new_bindings`, or `None` if inconsistent. Shared by [`Bindings::add`]
    /// (which wraps the result in an `Rc`) and the consistency checks in
    /// `unify`/`affects`.
    fn try_add(&self, ctx: &TypeContext, new_bindings: &[Binding]) -> Option<AddedVarsets> {
        if new_bindings.is_empty() {
            return Some((self.varsets.clone(), self.high_step, self.num_varsets));
        }
        let mut varsets = self.varsets.clone();
        let mut high_step = self.high_step;
        // Entries cons'ed onto `varsets` within this call. They shadow the
        // original chain, so lookups scan this prefix first (newest first) and
        // fall back to the (possibly indexed) rest — the same resolution
        // order as a plain head-first linear scan. Variables above the old
        // high step can only appear in the prefix, so the `self.high_step`
        // guard on the fallback is exact.
        let mut delta = 0usize;
        let state = self.index_state();

        let find_var = |varsets: &Option<Rc<Chain<Varset>>>,
                        delta: usize,
                        var: Variable,
                        step_id: usize|
         -> Option<(usize, Rc<Chain<Varset>>)> {
            let mut cur = varsets;
            for p in 0..delta {
                let node = cur.as_ref().expect("delta exceeds chain length");
                if node.head.includes_var(var, step_id) {
                    return Some((p, node.clone()));
                }
                cur = &node.tail;
            }
            if step_id <= self.high_step {
                if let Some((p, node)) = lookup_var_in(&state, &self.varsets, var, step_id) {
                    return Some((p + delta, node));
                }
            }
            None
        };
        let find_obj = |varsets: &Option<Rc<Chain<Varset>>>,
                        delta: usize,
                        obj: Object|
         -> Option<(usize, Rc<Chain<Varset>>)> {
            let mut cur = varsets;
            for p in 0..delta {
                let node = cur.as_ref().expect("delta exceeds chain length");
                if node.head.includes_object(obj) {
                    return Some((p, node.clone()));
                }
                cur = &node.tail;
            }
            if let Some((p, node)) = lookup_obj_in(&state, &self.varsets, obj) {
                return Some((p + delta, node));
            }
            None
        };

        for bind in new_bindings.iter() {
            // Resolve the varsets of the variable and the term.
            let vs1 = find_var(&varsets, delta, bind.var, bind.var_id);
            if bind.var_id > high_step {
                high_step = bind.var_id;
            }
            let vs2 = match bind.term {
                Term::Object(o) => find_obj(&varsets, delta, o),
                Term::Variable(tv) => {
                    let found = find_var(&varsets, delta, tv, bind.term_id);
                    if bind.term_id > high_step {
                        high_step = bind.term_id;
                    }
                    found
                }
            };

            if bind.equality {
                let comb = match (&vs1, &vs2) {
                    (None, None) => Varset::make(ctx, bind, false),
                    (Some((i1, _)), Some((i2, _))) if i1 == i2 => {
                        // Already in the same equality class. Consing an
                        // identical varset would only lengthen the history and
                        // consume the inherited index's prefix budget.
                        continue;
                    }
                    (Some((_, n1)), Some((_, n2))) => n1.head.combine(ctx, &n2.head),
                    (None, Some((_, n2))) => n2.head.add_var(ctx, bind.var, bind.var_id),
                    (Some((_, n1)), None) => n1.head.add_term(ctx, bind.term, bind.term_id),
                };
                // Push the combined varset; the resolver searches the head
                // first, so the most recent class wins.
                varsets = chain::cons(comb?, varsets);
                delta += 1;
            } else {
                // Inequality binding.
                if let (Some((i1, _)), Some((i2, _))) = (&vs1, &vs2) {
                    if i1 == i2 {
                        // Already bound to each other: inconsistent.
                        return None;
                    }
                }
                // Separate the second term from the first. When the variable
                // side has no varset yet, `Varset::make(.., false)` returns
                // `None` for an object term — that is NOT a failure (the
                // separation is recorded in the object's varset, `new_vs2`), so
                // we keep it as `None` rather than propagating it.
                let new_vs1 = match &vs1 {
                    None => Varset::make(ctx, bind, false),
                    Some((_, n1)) => {
                        let vs1 = &n1.head;
                        match bind.term {
                            Term::Variable(tv) => {
                                if vs1.excludes_var(tv, bind.term_id) {
                                    None
                                } else {
                                    Some(vs1.restrict(tv, bind.term_id))
                                }
                            }
                            // Term is an object: separation recorded in the
                            // object's varset instead.
                            Term::Object(_) => None,
                        }
                    }
                };
                // Separate the first term from the second.
                let new_vs2 = match &vs2 {
                    None => Varset::make(ctx, bind, true),
                    Some((_, n2)) => {
                        let vs2 = &n2.head;
                        if vs2.excludes_var(bind.var, bind.var_id) {
                            None
                        } else {
                            Some(vs2.restrict(bind.var, bind.var_id))
                        }
                    }
                };
                if let Some(v1) = new_vs1 {
                    varsets = chain::cons(v1, varsets);
                    delta += 1;
                }
                if let Some(v2) = new_vs2 {
                    varsets = chain::cons(v2, varsets);
                    delta += 1;
                }
            }
        }

        Some((varsets, high_step, self.num_varsets + delta))
    }

    /// Checks consistency of an inequality `var != term`.
    pub fn consistent_with_inequality(
        &self,
        var: Variable,
        var_id: usize,
        term: Term,
        term_id: usize,
    ) -> bool {
        let node = if term_id <= self.high_step {
            match term {
                Term::Object(o) => self.find_obj_node(o).map(|(_, n)| n),
                Term::Variable(tv) => self.find_var_node(tv, term_id).map(|(_, n)| n),
            }
        } else {
            None
        };
        match node {
            None => true,
            Some(n) => {
                let vs = &n.head;
                !vs.includes_var(var, var_id) || vs.excludes_var(var, var_id)
            }
        }
    }
}

/* ====================================================================== */
/* Resolved atom patterns: fast lifted-vs-ground matching. */

/// One position of an [`AtomPattern`]: a term resolved through the bindings.
#[derive(Debug, Clone, Copy)]
pub enum PatTerm {
    /// Resolved to a constant object.
    Obj(Object),
    /// Unbound variable: its equality class (pattern-local index) and the
    /// most-specific type the class admits.
    Var { class: u8, ty: Type },
}

/// A lifted atom's argument list resolved once against a [`Bindings`], plus
/// the binding constraints relevant to matching it against ground atoms.
/// [`AtomPattern::matches`] then decides unification per ground candidate with
/// cheap per-position checks instead of re-walking the varset chain; it
/// returns exactly what [`Bindings::unify`] returns for that candidate (see
/// the debug assertions at the call sites).
#[derive(Debug)]
pub struct AtomPattern {
    /// Pattern positions, parallel to the atom's term list.
    terms: Vec<PatTerm>,
    /// Per-class constants excluded by non-codesignation constraints.
    excluded: Vec<Vec<Object>>,
    /// Class pairs that must not be assigned the same object.
    ncd_pairs: Vec<(u8, u8)>,
    /// Scratch class assignment reused across candidates.
    assignment: Vec<Option<Object>>,
}

impl AtomPattern {
    /// True iff every position is already fixed to an object. Allocation-free,
    /// so callers can test before paying for [`AtomPattern::object_terms`].
    #[inline]
    pub fn is_fully_bound(&self) -> bool {
        self.terms.iter().all(|pt| matches!(pt, PatTerm::Obj(_)))
    }

    /// The fully-resolved term list, or `None` if any position is unbound.
    ///
    /// The emptiness test comes first because `collect()` into an `Option<Vec>`
    /// allocates the vector before it reaches the unbound position that makes it
    /// `None` -- and in lifted search most patterns are unbound, so that
    /// allocation was being made and thrown away on the common path.
    pub fn object_terms(&self) -> Option<Vec<Term>> {
        if !self.is_fully_bound() {
            return None;
        }
        Some(
            self.terms
                .iter()
                .map(|pt| match pt {
                    PatTerm::Obj(o) => Term::Object(*o),
                    PatTerm::Var { .. } => unreachable!("checked fully bound above"),
                })
                .collect(),
        )
    }

    /// The argument positions the pattern fixes to an object. These are the
    /// positions a relation index can probe; the remaining positions still need
    /// [`AtomPattern::matches`] for their type, equality-class and
    /// non-codesignation constraints.
    pub fn bound_positions(&self) -> impl Iterator<Item = (usize, Object)> + '_ {
        self.terms
            .iter()
            .enumerate()
            .filter_map(|(position, term)| match term {
                PatTerm::Obj(object) => Some((position, *object)),
                PatTerm::Var { .. } => None,
            })
    }

    /// An upper bound on the number of ground term tuples this pattern admits:
    /// each distinct variable class contributes its type's object count minus
    /// its exclusions. Ignores non-codesignation pairs, so it can overcount
    /// relative to [`AtomPattern::matches`] — harmless for callers using it as
    /// a bound.
    pub fn admitted_tuples(&self, ctx: &TypeContext) -> u64 {
        // Classes are numbered by first appearance.
        let mut class_types: Vec<Type> = Vec::new();
        for term in &self.terms {
            if let PatTerm::Var { class, ty } = term {
                if *class as usize == class_types.len() {
                    class_types.push(*ty);
                }
            }
        }
        let mut total: u64 = 1;
        for (class, ty) in class_types.iter().enumerate() {
            let n = ctx.count_compatible_objects(*ty, &self.excluded[class]);
            total = total.saturating_mul(n as u64);
            if total == 0 {
                return 0;
            }
        }
        total
    }

    /// Whether a ground candidate's terms unify with the pattern under the
    /// bindings it was resolved against.
    pub fn matches(&mut self, ctx: &TypeContext, ground_terms: &[Term]) -> bool {
        debug_assert_eq!(ground_terms.len(), self.terms.len());
        self.assignment.iter_mut().for_each(|a| *a = None);
        for (pt, gt) in self.terms.iter().zip(ground_terms) {
            let o = match gt {
                Term::Object(o) => *o,
                Term::Variable(_) => return false,
            };
            match pt {
                PatTerm::Obj(p) => {
                    if *p != o {
                        return false;
                    }
                }
                PatTerm::Var { class, ty } => {
                    let c = *class as usize;
                    match self.assignment[c] {
                        // A repeated class must resolve to one object; the
                        // type/exclusion checks were done on first occurrence.
                        Some(prev) => {
                            if prev != o {
                                return false;
                            }
                        }
                        None => {
                            if !ctx.types.subtype(ctx.object_type(o), *ty)
                                || self.excluded[c].contains(&o)
                            {
                                return false;
                            }
                            self.assignment[c] = Some(o);
                        }
                    }
                }
            }
        }
        for &(a, b) in &self.ncd_pairs {
            if self.assignment[a as usize] == self.assignment[b as usize] {
                return false;
            }
        }
        true
    }
}

impl Bindings {
    /// Resolves a lifted atom's terms into an [`AtomPattern`] for repeated
    /// matching against ground atoms (the planning-graph heuristic lookups).
    pub fn resolve_pattern(
        &self,
        ctx: &TypeContext,
        terms: &[Term],
        step_id: usize,
    ) -> AtomPattern {
        // Pattern-local equality classes: the varset when the variable has
        // one, otherwise the variable itself (all positions share `step_id`).
        #[derive(PartialEq, Clone, Copy)]
        enum ClassKey {
            Set(usize),
            Fresh(Variable),
        }
        let state = self.index_state();
        let mut pat_terms = Vec::with_capacity(terms.len());
        let mut classes: Vec<ClassKey> = Vec::new();
        let mut class_nodes: Vec<Option<Rc<Chain<Varset>>>> = Vec::new();
        for &t in terms {
            match self.binding(t, step_id) {
                Term::Object(o) => pat_terms.push(PatTerm::Obj(o)),
                Term::Variable(v) => {
                    let found = if step_id <= self.high_step {
                        self.find_var_node(v, step_id)
                    } else {
                        None
                    };
                    let key = match &found {
                        Some((p, _)) => ClassKey::Set(*p),
                        None => ClassKey::Fresh(v),
                    };
                    let class = classes.iter().position(|k| *k == key).unwrap_or_else(|| {
                        classes.push(key);
                        class_nodes.push(found.map(|(_, n)| n));
                        classes.len() - 1
                    });
                    // An unbound variable's varset carries the most-specific
                    // type of its whole equality class.
                    let ty = match &class_nodes[class] {
                        Some(n) => n.head.ty,
                        None => ctx.variable_type(v, step_id),
                    };
                    pat_terms.push(PatTerm::Var {
                        class: class as u8,
                        ty,
                    });
                }
            }
        }
        // Excluded constants: a constant is excluded for a class when some
        // chain entry pinned to it non-codesignates a member of the class.
        // Inequalities always restrict both sides, so this direction alone is
        // complete — including `separate()`'s var≠var goals and var≠object
        // inequalities, which are recorded only on the object's class. Long
        // chains answer through the index's `ncd_constants` table; short ones
        // scan the (few) chain entries directly. Stale (shadowed) entries
        // carry subsets of the authoritative lists, so both are sound.
        let mut excluded: Vec<Vec<Object>> = vec![Vec::new(); classes.len()];
        // Direct scan of pinned chain entries against the classes; `limit`
        // restricts it to the newest `limit` varsets (unindexed prefix), or the
        // whole chain for `usize::MAX`. Exclusions are a union over entries, so
        // combining scan and index contributions in any order is sound.
        let mut scan_excluded = |limit: usize| {
            if classes.is_empty() {
                return;
            }
            for vs in chain::iter(&self.varsets).take(limit) {
                let Some(c) = vs.constant else { continue };
                for (ci, key) in classes.iter().enumerate() {
                    if excluded[ci].contains(&c) {
                        continue;
                    }
                    let hit = chain::iter(&vs.ncd_set).any(|sv| match key {
                        ClassKey::Fresh(v) => sv.0 == *v && sv.1 == step_id,
                        ClassKey::Set(_) => class_nodes[ci]
                            .as_ref()
                            .unwrap()
                            .head
                            .includes_var(sv.0, sv.1),
                    });
                    if hit {
                        excluded[ci].push(c);
                    }
                }
            }
        };
        match &state {
            IndexState::Built { prefix, ix, .. } => {
                // Entries newer than the index answer by scan…
                scan_excluded(*prefix);
                // …the indexed rest through the `ncd_constants` table.
                for (ci, key) in classes.iter().enumerate() {
                    match key {
                        ClassKey::Fresh(v) => {
                            if let Some(cs) = ix.ncd_constants.get(&(*v, step_id)) {
                                for c in cs {
                                    if !excluded[ci].contains(c) {
                                        excluded[ci].push(*c);
                                    }
                                }
                            }
                        }
                        ClassKey::Set(_) => {
                            let node = class_nodes[ci].as_ref().unwrap();
                            for sv in chain::iter(&node.head.cd_set) {
                                if let Some(cs) = ix.ncd_constants.get(sv) {
                                    for c in cs {
                                        if !excluded[ci].contains(c) {
                                            excluded[ci].push(*c);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            IndexState::Small => scan_excluded(usize::MAX),
        }
        // Pairwise non-codesignation between the atom's classes: a candidate
        // may not assign such a pair the same object.
        let mut ncd_pairs: Vec<(u8, u8)> = Vec::new();
        for (ci, _) in classes.iter().enumerate() {
            let Some(n_i) = &class_nodes[ci] else {
                continue;
            };
            for (cj, _) in classes.iter().enumerate().skip(ci + 1) {
                let Some(n_j) = &class_nodes[cj] else {
                    continue;
                };
                let ncd = chain::iter(&n_i.head.ncd_set)
                    .any(|sv| n_j.head.includes_var(sv.0, sv.1))
                    || chain::iter(&n_j.head.ncd_set).any(|sv| n_i.head.includes_var(sv.0, sv.1));
                if ncd {
                    ncd_pairs.push((ci as u8, cj as u8));
                }
            }
        }
        let num_classes = classes.len();
        AtomPattern {
            terms: pat_terms,
            excluded,
            ncd_pairs,
            assignment: vec![None; num_classes],
        }
    }
}

impl Clone for Varset {
    fn clone(&self) -> Self {
        self.clone_shallow()
    }
}

/// Whether all of an atom's terms are objects (fully instantiated).
fn is_ground(a: &crate::formula::Atom) -> bool {
    a.terms.iter().all(|t| t.object())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::OBJECT;

    struct ObjectVariables;
    impl StepVarTypes for ObjectVariables {
        fn var_type(&self, _: Variable, _: usize) -> Type {
            OBJECT
        }
    }

    fn with_context(f: impl FnOnce(&TypeContext)) {
        let types = Types::new();
        let constants = TermTable::new();
        let mut objects = TermTable::with_parent(&constants);
        for name in ["a", "b", "c"] {
            objects.add_object(name, OBJECT);
        }
        f(&TypeContext {
            types: &types,
            objects: &objects,
            constants: &constants,
            step_vars: &ObjectVariables,
        });
    }

    fn indexed_bindings(ctx: &TypeContext) -> Rc<Bindings> {
        let bindings: Vec<_> = (1..=INDEX_THRESHOLD)
            .map(|step| Binding::new(Variable(0), step, Term::Variable(Variable(1)), step, true))
            .collect();
        let result = Bindings::empty().add(ctx, &bindings, false).unwrap();
        assert!(matches!(
            result.index_state(),
            IndexState::Built { prefix: 0, .. }
        ));
        result
    }

    #[test]
    fn compact_index_shares_one_record_for_a_large_equality_class() {
        with_context(|ctx| {
            let constraints: Vec<_> = (1..=64)
                .map(|step| Binding::new(Variable(0), step, Term::Object(Object(0)), 0, true))
                .collect();
            let bindings = Bindings::empty().add(ctx, &constraints, false).unwrap();
            let IndexState::Built { ix, .. } = bindings.index_state() else {
                panic!("long binding history should be indexed");
            };
            // All 64 variables and their constant share the newest node; the
            // older, shadowed classes must not consume additional records.
            assert_eq!(ix.classes.len(), 1);
            assert_eq!(ix.vars.len(), 64);
            assert_eq!(ix.objs.len(), 1);
            assert_lookups(&bindings);
            for step in 1..=64 {
                assert_eq!(
                    bindings.binding(Term::Variable(Variable(0)), step),
                    Term::Object(Object(0))
                );
            }
        });
    }

    #[test]
    fn compact_index_preserves_full_width_step_and_variable_ids() {
        with_context(|ctx| {
            let mut constraints: Vec<_> = (1..=INDEX_THRESHOLD)
                .map(|step| Binding::new(Variable(0), step, Term::Object(Object(0)), 0, true))
                .collect();
            let mut cases = vec![
                (Variable(0), 1, Object(0)),
                (Variable(0), crate::plan::GOAL_ID, Object(1)),
                (Variable(u32::MAX), usize::MAX - 1, Object(2)),
                (Variable(u32::MAX), 1, Object(1)),
            ];
            if usize::BITS > 32 {
                cases.push((Variable(0), u32::MAX as usize, Object(2)));
            }
            for &(var, step, obj) in &cases {
                constraints.push(Binding::new(var, step, Term::Object(obj), 0, true));
            }
            let bindings = Bindings::empty().add(ctx, &constraints, false).unwrap();
            assert!(matches!(bindings.index_state(), IndexState::Built { .. }));
            for (var, step, obj) in cases {
                assert_eq!(
                    bindings.binding(Term::Variable(var), step),
                    Term::Object(obj)
                );
                let (p, node) = bindings.find_var_node(var, step).unwrap();
                let (q, scanned) = scan_var(&bindings.varsets, var, step, usize::MAX).unwrap();
                assert_eq!(p, q);
                assert!(Rc::ptr_eq(&node, &scanned));
                assert!(bindings
                    .add(
                        ctx,
                        &[Binding::new(var, step, Term::Object(obj), 0, false)],
                        true
                    )
                    .is_none());
            }
            assert!(bindings
                .find_var_node(Variable(1), crate::plan::GOAL_ID)
                .is_none());
        });
    }

    #[test]
    fn entailed_equalities_share_bindings_without_allocating() {
        with_context(|ctx| {
            let parent = indexed_bindings(ctx)
                .add(
                    ctx,
                    &[Binding::new(
                        Variable(0),
                        1,
                        Term::Object(Object(0)),
                        0,
                        true,
                    )],
                    false,
                )
                .unwrap();
            let repeated = [
                Binding::new(Variable(1), 1, Term::Variable(Variable(0)), 1, true),
                Binding::new(Variable(1), 1, Term::Object(Object(0)), 0, true),
            ];
            let (child, allocations) = crate::alloc_test::allocations_during(|| {
                let mut child = parent.clone();
                for _ in 0..MAX_INDEX_PREFIX + 1 {
                    child = child.add(ctx, &repeated, false).unwrap();
                }
                child
            });
            assert!(Rc::ptr_eq(&parent, &child));
            assert_eq!(allocations, 0);
            assert_lookups(&child);

            // Equality is scoped to a step: this is a real merge even though
            // the schema variable has the same name in both occurrences.
            let mut extended = repeated.to_vec();
            extended.push(Binding::new(
                Variable(0),
                2,
                Term::Variable(Variable(0)),
                1,
                true,
            ));
            let merged = child.add(ctx, &extended, false).unwrap();
            assert_eq!(merged.num_varsets, parent.num_varsets + 1);
            assert_eq!(
                merged.binding(Term::Variable(Variable(1)), 2),
                Term::Object(Object(0))
            );
            assert!(parent.binding(Term::Variable(Variable(0)), 2).variable());
            assert_lookups(&merged);

            // A later contradiction in the same batch must still be checked.
            extended.push(Binding::new(
                Variable(1),
                2,
                Term::Object(Object(0)),
                0,
                false,
            ));
            for test_only in [false, true] {
                assert!(parent.add(ctx, &extended, test_only).is_none());
            }
        });
    }

    // Compare positions and node identity, including misses, against a full
    // head-first scan independent of the inherited index and its prefix.
    fn assert_lookups(bindings: &Bindings) {
        let same = |found: Option<(usize, Rc<Chain<Varset>>)>,
                    scanned: Option<(usize, Rc<Chain<Varset>>)>| {
            match (found, scanned) {
                (Some((p, n)), Some((q, m))) => assert!(p == q && Rc::ptr_eq(&n, &m)),
                (None, None) => {}
                _ => panic!("indexed lookup disagrees with full scan"),
            }
        };
        for step in 0..=bindings.high_step + 1 {
            for var in [Variable(0), Variable(1), Variable(2)] {
                same(
                    bindings.find_var_node(var, step),
                    scan_var(&bindings.varsets, var, step, usize::MAX),
                );
            }
        }
        for obj in [Object(0), Object(1), Object(2)] {
            same(
                bindings.find_obj_node(obj),
                scan_obj(&bindings.varsets, obj, usize::MAX),
            );
        }
    }

    #[test]
    fn inherited_prefix_shadows_classes_and_preserves_siblings() {
        with_context(|ctx| {
            let parent = indexed_bindings(ctx);
            let child = parent
                .add(
                    ctx,
                    &[
                        Binding::new(Variable(0), 1, Term::Object(Object(0)), 0, true),
                        Binding::new(Variable(0), 2, Term::Variable(Variable(0)), 1, true),
                    ],
                    false,
                )
                .unwrap();
            let sibling = parent
                .add(
                    ctx,
                    &[Binding::new(
                        Variable(0),
                        1,
                        Term::Object(Object(1)),
                        0,
                        true,
                    )],
                    false,
                )
                .unwrap();
            let IndexState::Built { ix, .. } = parent.index_state() else {
                panic!()
            };
            for bindings in [&parent, &child, &sibling] {
                assert_lookups(bindings);
                let IndexState::Built { ix: shared, .. } = bindings.index_state() else {
                    panic!()
                };
                assert!(Rc::ptr_eq(&ix, &shared));
            }
            for step in [1, 2] {
                for var in [Variable(0), Variable(1)] {
                    assert_eq!(
                        child.binding(Term::Variable(var), step),
                        Term::Object(Object(0))
                    );
                    assert_eq!(child.find_var_node(var, step).unwrap().0, 0);
                    assert!(parent.binding(Term::Variable(var), step).variable());
                }
            }
            assert_eq!(child.find_obj_node(Object(0)).unwrap().0, 0);
            assert_eq!(
                sibling.binding(Term::Variable(Variable(1)), 1),
                Term::Object(Object(1))
            );
            assert!(child
                .add(
                    ctx,
                    &[Binding::new(
                        Variable(1),
                        2,
                        Term::Object(Object(1)),
                        0,
                        true
                    ),],
                    false
                )
                .is_none());
        });
    }

    #[test]
    fn inherited_index_rebuilds_at_both_prefix_limits() {
        with_context(|ctx| {
            for grow_class in [false, true] {
                let parent = indexed_bindings(ctx);
                let mut bindings = parent.clone();
                let mut prefix = 0;
                let mut members = 0;
                let mut rebuilds = 0;
                for added in 1..=MAX_INDEX_PREFIX + 1 {
                    let step = INDEX_THRESHOLD + added;
                    let (term, term_step, class_size) = if grow_class {
                        (Variable(0), 1, 2 + added)
                    } else {
                        (Variable(1), step, 2)
                    };
                    bindings = bindings
                        .add(
                            ctx,
                            &[Binding::new(
                                Variable(0),
                                step,
                                Term::Variable(term),
                                term_step,
                                true,
                            )],
                            false,
                        )
                        .unwrap();
                    prefix += 1;
                    members += class_size;
                    if prefix > MAX_INDEX_PREFIX || members > MAX_PREFIX_MEMBERS {
                        assert!(bindings.index.borrow().is_none());
                        prefix = 0;
                        members = 0;
                        rebuilds += 1;
                    }
                    assert_lookups(&bindings);
                    assert!(matches!(bindings.index_state(), IndexState::Built {
                        prefix: p, prefix_members: m, ..
                    } if p == prefix && m == members));
                }
                assert!(rebuilds > 0);
                assert_lookups(&parent);
            }
        });
    }

    #[test]
    fn pattern_exclusions_combine_index_and_prefix() {
        with_context(|ctx| {
            let mut initial: Vec<_> = (1..=INDEX_THRESHOLD)
                .map(|step| {
                    Binding::new(Variable(0), step, Term::Variable(Variable(1)), step, true)
                })
                .collect();
            initial.push(Binding::new(
                Variable(0),
                1,
                Term::Object(Object(0)),
                0,
                false,
            ));
            let parent = Bindings::empty().add(ctx, &initial, false).unwrap();
            assert_lookups(&parent); // Index the first exclusion.
            let child = parent
                .add(
                    ctx,
                    &[Binding::new(
                        Variable(1),
                        1,
                        Term::Object(Object(1)),
                        0,
                        false,
                    )],
                    false,
                )
                .unwrap();
            assert_lookups(&child);
            let terms = [Term::Variable(Variable(0)), Term::Variable(Variable(1))];
            let mut parent_pattern = parent.resolve_pattern(ctx, &terms, 1);
            let mut child_pattern = child.resolve_pattern(ctx, &terms, 1);
            for (obj, parent_ok, child_ok) in [(0, false, false), (1, true, false), (2, true, true)]
            {
                let tuple = [Term::Object(Object(obj)); 2];
                assert_eq!(parent_pattern.matches(ctx, &tuple), parent_ok);
                assert_eq!(child_pattern.matches(ctx, &tuple), child_ok);
                let pin = [Binding::new(Variable(0), 1, tuple[0], 0, true)];
                assert_eq!(child.add(ctx, &pin, true).is_some(), child_ok);
            }
        });
    }
}
