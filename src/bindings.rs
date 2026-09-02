//! Variable binding constraints.
//!
//! A [`Bindings`] is a chain of [`Varset`]s. Each varset is an equality class
//! of step-variables (`(Variable, step_id)`) optionally pinned to a constant
//! object, with a non-codesignation list and a most-specific type. Adding
//! equality/inequality bindings merges or separates varsets, returning a fresh
//! `Bindings` (`None` when inconsistent). For ground actions every term is
//! already an object, so the same interface degenerates to constant equality
//! checks.

use std::cell::{Cell, RefCell};
use std::collections::BTreeSet;
use std::rc::Rc;

use crate::chain::{self, Chain};
use crate::fasthash::FastMap;
use crate::formula::Literal;
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

/// Lazily-built lookup index over an immutable varset chain: the authoritative
/// (newest) varset node per step-variable and per pinned constant, plus the
/// constants excluded per step-variable through pinned classes'
/// non-codesignation lists. Replaces the O(chain) linear scans on the hot
/// lookup paths; positions are relative to the chain head so shadowed (stale)
/// entries never win.
#[derive(Debug, Default)]
struct VarsetIndex {
    vars: FastMap<StepVariable, (usize, Rc<Chain<Varset>>)>,
    objs: FastMap<Object, (usize, Rc<Chain<Varset>>)>,
    ncd_constants: FastMap<StepVariable, Vec<Object>>,
}

/// Chains shorter than this are scanned linearly: for them the hash-map
/// builds cost more than the scans they replace.
const INDEX_THRESHOLD: usize = 64;

/// Number of lookups on one `Bindings` before its chain is worth indexing.
/// Plans that are ranked once and parked (or expanded with few unifications)
/// stay on linear scans; lookup-heavy evaluations (e.g. the reuse-aware
/// heuristics probing every step effect per open condition) promote quickly
/// and amortise the build.
const PROMOTE_AFTER: u32 = 48;

/// Longest prefix of not-yet-indexed varsets tolerated in front of an
/// inherited index before the chain is re-indexed from scratch. Bounds the
/// per-`resolve_pattern` exclusion scan, while amortising the O(chain)
/// rebuild over at least this many generations of child bindings.
const MAX_INDEX_PREFIX: usize = 32;

/// Overlay entry cap; entries are class members, so the overlay can outgrow
/// the node prefix. Bounds the linear pass every indexed lookup makes before
/// the hash maps.
const MAX_OVERLAY: usize = 96;

/// Flat lookup entries for the varsets newer than a shared [`VarsetIndex`],
/// ordered oldest→newest (lookups iterate in reverse so the newest class
/// wins, matching a head-first scan). `depth` is the node's distance from the
/// chain tail — stable as children cons more varsets on — and converts to a
/// head-relative position as `num_varsets - 1 - depth`.
#[derive(Debug, Default, Clone)]
struct Overlay {
    vars: Vec<(StepVariable, u32, Rc<Chain<Varset>>)>,
    objs: Vec<(Object, u32, Rc<Chain<Varset>>)>,
}

/// Whether a chain is worth indexing (cached alongside the index itself).
#[derive(Debug, Clone)]
enum IndexState {
    /// Short chain: linear scans win.
    Small,
    /// Index over a suffix of the chain. The first `prefix` (newest) varsets
    /// are answered by the flat `overlay` before the index answers for the
    /// rest; a fresh build has an empty overlay, and children extend it with
    /// the varsets they cons on (see `Bindings::add`). Index positions are
    /// relative to the indexed suffix, so `prefix` is added on the way out.
    Built {
        prefix: usize,
        overlay: Rc<Overlay>,
        ix: Rc<VarsetIndex>,
    },
}

/// Indexed lookup for a step-variable: checks the overlay (newest first),
/// then the index with head-relative positions. `num_varsets` is the chain
/// length of the `Bindings` the state was taken from. Resolution order is
/// identical to a plain `scan_var`.
fn lookup_var_in(
    state: &IndexState,
    varsets: &Option<Rc<Chain<Varset>>>,
    num_varsets: usize,
    var: Variable,
    step_id: usize,
) -> Option<(usize, Rc<Chain<Varset>>)> {
    match state {
        IndexState::Small => scan_var(varsets, var, step_id),
        IndexState::Built {
            prefix,
            overlay,
            ix,
        } => {
            for (sv, depth, node) in overlay.vars.iter().rev() {
                if sv.0 == var && sv.1 == step_id {
                    return Some((num_varsets - 1 - *depth as usize, node.clone()));
                }
            }
            ix.vars
                .get(&(var, step_id))
                .map(|(p, n)| (p + prefix, n.clone()))
        }
    }
}

/// Indexed lookup for a pinned constant; see [`lookup_var_in`].
fn lookup_obj_in(
    state: &IndexState,
    varsets: &Option<Rc<Chain<Varset>>>,
    num_varsets: usize,
    obj: Object,
) -> Option<(usize, Rc<Chain<Varset>>)> {
    match state {
        IndexState::Small => scan_obj(varsets, obj),
        IndexState::Built {
            prefix,
            overlay,
            ix,
        } => {
            for (o, depth, node) in overlay.objs.iter().rev() {
                if *o == obj {
                    return Some((num_varsets - 1 - *depth as usize, node.clone()));
                }
            }
            ix.objs.get(&obj).map(|(p, n)| (p + prefix, n.clone()))
        }
    }
}

/// Head-first linear scan for the authoritative varset of a step-variable.
fn scan_var(
    varsets: &Option<Rc<Chain<Varset>>>,
    var: Variable,
    step_id: usize,
) -> Option<(usize, Rc<Chain<Varset>>)> {
    let mut cur = varsets;
    let mut p = 0usize;
    while let Some(node) = cur {
        if node.head.includes_var(var, step_id) {
            return Some((p, node.clone()));
        }
        p += 1;
        cur = &node.tail;
    }
    None
}

/// Head-first linear scan for the authoritative varset of a pinned constant.
fn scan_obj(
    varsets: &Option<Rc<Chain<Varset>>>,
    obj: Object,
) -> Option<(usize, Rc<Chain<Varset>>)> {
    let mut cur = varsets;
    let mut p = 0usize;
    while let Some(node) = cur {
        if node.head.includes_object(obj) {
            return Some((p, node.clone()));
        }
        p += 1;
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
    /// Lookups performed so far; long chains promote to an index only after
    /// `PROMOTE_AFTER` of them (see `index_state`).
    probes: Cell<u32>,
    /// Lookup index, built after enough lookups on a long chain. Dropped after
    /// each plan ranking (see `clear_index`) so the many queued-but-never-
    /// expanded plans don't retain an O(chain) side table each.
    index: RefCell<Option<IndexState>>,
}

impl Bindings {
    pub fn empty() -> Rc<Bindings> {
        Rc::new(Bindings::default())
    }

    /// The lookup state, building the index on first use for long chains. The
    /// varset chain is immutable once the `Bindings` exists, so the cached
    /// state never goes stale.
    fn index_state(&self) -> IndexState {
        if self.num_varsets < INDEX_THRESHOLD {
            return IndexState::Small;
        }
        if let Some(s) = self.index.borrow().as_ref() {
            return s.clone();
        }
        // Long chain, no index yet: only build one once this instance has
        // seen enough lookups to amortise the build.
        let probes = self.probes.get();
        if probes < PROMOTE_AFTER {
            self.probes.set(probes + 1);
            return IndexState::Small;
        }
        let state = {
            let mut ix = VarsetIndex::default();
            let mut pos = 0usize;
            let mut cur = self.varsets.clone();
            while let Some(node) = cur {
                let vs = &node.head;
                for sv in chain::iter(&vs.cd_set) {
                    // First (newest) entry wins: it is the authoritative class.
                    ix.vars.entry(*sv).or_insert_with(|| (pos, node.clone()));
                }
                if let Some(c) = vs.constant {
                    ix.objs.entry(c).or_insert_with(|| (pos, node.clone()));
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
                pos += 1;
                cur = node.tail.clone();
            }
            IndexState::Built {
                prefix: 0,
                overlay: Rc::new(Overlay::default()),
                ix: Rc::new(ix),
            }
        };
        *self.index.borrow_mut() = Some(state.clone());
        state
    }

    /// Finds the authoritative varset node (and its head-relative position)
    /// for a step-variable.
    fn find_var_node(&self, var: Variable, step_id: usize) -> Option<(usize, Rc<Chain<Varset>>)> {
        let found = lookup_var_in(
            &self.index_state(),
            &self.varsets,
            self.num_varsets,
            var,
            step_id,
        );
        debug_assert!(
            {
                let scanned = scan_var(&self.varsets, var, step_id);
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
        let found = lookup_obj_in(&self.index_state(), &self.varsets, self.num_varsets, obj);
        debug_assert!(
            {
                let scanned = scan_obj(&self.varsets, obj);
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
    pub fn affects(&self, ctx: &TypeContext, l1: &Literal, id1: usize, l2: &Literal, id2: usize) -> bool {
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
        match l1 {
            Literal::Negation(a) => self.unify_mgu(
                ctx,
                mgu,
                l2,
                id2,
                &Literal::Atom(a.clone()),
                id1,
            ),
            Literal::Atom(_) => match l2 {
                Literal::Negation(a) => self.unify_mgu(
                    ctx,
                    mgu,
                    &Literal::Atom(a.clone()),
                    id2,
                    l1,
                    id1,
                ),
                Literal::Atom(_) => false,
            },
        }
    }

    /// Checks if two literals can be unified.
    pub fn unify(&self, ctx: &TypeContext, l1: &Literal, id1: usize, l2: &Literal, id2: usize) -> bool {
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
        let a1 = l1.atom();
        let a2 = l2.atom();
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
                                    mgu.push(Binding::new(
                                        var1,
                                        idl,
                                        Term::Object(obj2),
                                        0,
                                        true,
                                    ));
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
        self.try_add(ctx, new_bindings).map(|(varsets, high_step, num_varsets)| {
            // Inherit the parent's index: the child chain is the parent chain
            // plus a few consed varsets, so the parent's table stays valid
            // behind an overlay extended with the new varsets' members. Once
            // the prefix or overlay would exceed its cap the child starts
            // unindexed and the usual promotion path re-indexes from scratch,
            // resetting both to empty for its own descendants.
            let index = match self.index.borrow().as_ref() {
                Some(IndexState::Built {
                    prefix,
                    overlay,
                    ix,
                }) => {
                    let added = num_varsets - self.num_varsets;
                    let p = prefix + added;
                    if p <= MAX_INDEX_PREFIX {
                        let mut ov = (**overlay).clone();
                        // The added nodes are the first `added` of the child
                        // chain; append oldest-first so reverse iteration in
                        // the lookups sees the newest class first.
                        let mut nodes: Vec<Rc<Chain<Varset>>> = Vec::with_capacity(added);
                        let mut cur = &varsets;
                        for _ in 0..added {
                            let n = cur.as_ref().expect("added exceeds chain length");
                            nodes.push(n.clone());
                            cur = &n.tail;
                        }
                        for (i, n) in nodes.iter().enumerate().rev() {
                            let depth = (num_varsets - 1 - i) as u32;
                            for sv in chain::iter(&n.head.cd_set) {
                                ov.vars.push((*sv, depth, n.clone()));
                            }
                            if let Some(c) = n.head.constant {
                                ov.objs.push((c, depth, n.clone()));
                            }
                        }
                        (ov.vars.len() + ov.objs.len() <= MAX_OVERLAY).then(|| {
                            IndexState::Built {
                                prefix: p,
                                overlay: Rc::new(ov),
                                ix: ix.clone(),
                            }
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
                probes: Cell::new(0),
                index: RefCell::new(index),
            })
        })
    }

    /// Computes the varsets/high-step/length that would result from adding
    /// `new_bindings`, or `None` if inconsistent. Shared by [`Bindings::add`]
    /// (which wraps the result in an `Rc`) and the consistency checks in
    /// `unify`/`affects`.
    fn try_add(
        &self,
        ctx: &TypeContext,
        new_bindings: &[Binding],
    ) -> Option<(Option<Rc<Chain<Varset>>>, usize, usize)> {
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
                if let Some((p, node)) =
                    lookup_var_in(&state, &self.varsets, self.num_varsets, var, step_id)
                {
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
            if let Some((p, node)) = lookup_obj_in(&state, &self.varsets, self.num_varsets, obj) {
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
                    (Some((i1, n1)), Some((i2, _))) if i1 == i2 => {
                        // Already bound to each other: reuse existing varset.
                        Some(n1.head.clone_shallow())
                    }
                    (Some((_, n1)), Some((_, n2))) => n1.head.combine(ctx, &n2.head),
                    (None, Some((_, n2))) => n2.head.add_var(ctx, bind.var, bind.var_id),
                    (Some((_, n1)), None) => n1.head.add_term(ctx, bind.term, bind.term_id),
                };
                match comb {
                    None => return None,
                    Some(new_vs) => {
                        // Push the combined varset; the resolver searches the
                        // head first, so the most recent class wins.
                        varsets = chain::cons(new_vs, varsets);
                        delta += 1;
                    }
                }
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
    /// The fully-resolved term list, or `None` if any position is unbound.
    pub fn object_terms(&self) -> Option<Vec<Term>> {
        self.terms
            .iter()
            .map(|pt| match pt {
                PatTerm::Obj(o) => Some(Term::Object(*o)),
                PatTerm::Var { .. } => None,
            })
            .collect()
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
                    let class = classes
                        .iter()
                        .position(|k| *k == key)
                        .unwrap_or_else(|| {
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
            let Some(n_i) = &class_nodes[ci] else { continue };
            for (cj, _) in classes.iter().enumerate().skip(ci + 1) {
                let Some(n_j) = &class_nodes[cj] else { continue };
                let ncd = chain::iter(&n_i.head.ncd_set)
                    .any(|sv| n_j.head.includes_var(sv.0, sv.1))
                    || chain::iter(&n_j.head.ncd_set)
                        .any(|sv| n_i.head.includes_var(sv.0, sv.1));
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
