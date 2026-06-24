//! Variable binding constraints.
//!
//! A [`Bindings`] is a chain of [`Varset`]s. Each varset is an equality class
//! of step-variables (`(Variable, step_id)`) optionally pinned to a constant
//! object, with a non-codesignation list and a most-specific type. Adding
//! equality/inequality bindings merges or separates varsets, returning a fresh
//! `Bindings` (`None` when inconsistent). For ground actions every term is
//! already an object, so the same interface degenerates to constant equality
//! checks.

use std::collections::BTreeSet;
use std::rc::Rc;

use crate::chain::{self, Chain};
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

fn find_varset_object(varsets: &Option<Rc<Chain<Varset>>>, obj: Object) -> Option<usize> {
    chain::iter(varsets).position(|vs| vs.includes_object(obj))
}

fn find_varset_var(
    varsets: &Option<Rc<Chain<Varset>>>,
    var: Variable,
    step_id: usize,
) -> Option<usize> {
    chain::iter(varsets).position(|vs| vs.includes_var(var, step_id))
}

/// A collection of variable bindings.
#[derive(Debug, Default)]
pub struct Bindings {
    /// Varsets; the head is the most recently added.
    varsets: Option<Rc<Chain<Varset>>>,
    /// Highest step id mentioned in any varset.
    high_step: usize,
}

impl Bindings {
    pub fn empty() -> Rc<Bindings> {
        Rc::new(Bindings::default())
    }

    /// Returns the constant bound to `term` at `step_id`, or `term` itself when
    /// unbound.
    pub fn binding(&self, term: Term, step_id: usize) -> Term {
        if let Term::Variable(v) = term {
            if step_id <= self.high_step {
                if let Some(i) = find_varset_var(&self.varsets, v, step_id) {
                    let vs = chain::iter(&self.varsets).nth(i).unwrap();
                    if let Some(c) = vs.constant {
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
            if let Some(i) = find_varset_var(&self.varsets, var, step_id) {
                let vs = chain::iter(&self.varsets).nth(i).unwrap();
                for sv in chain::iter(&vs.ncd_set) {
                    if sv.1 <= self.high_step {
                        if let Some(j) = find_varset_var(&self.varsets, sv.0, sv.1) {
                            let vs2 = chain::iter(&self.varsets).nth(j).unwrap();
                            if let Some(c) = vs2.constant {
                                names.remove(&c);
                            }
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
        self.try_add(ctx, new_bindings).map(|(varsets, high_step)| Rc::new(Bindings { varsets, high_step }))
    }

    /// Computes the varsets/high-step that would result from adding
    /// `new_bindings`, or `None` if inconsistent. Shared by [`Bindings::add`]
    /// (which wraps the result in an `Rc`) and the consistency checks in
    /// `unify`/`affects`.
    fn try_add(
        &self,
        ctx: &TypeContext,
        new_bindings: &[Binding],
    ) -> Option<(Option<Rc<Chain<Varset>>>, usize)> {
        if new_bindings.is_empty() {
            return Some((self.varsets.clone(), self.high_step));
        }
        let mut varsets = self.varsets.clone();
        let mut high_step = self.high_step;
        // Variables introduced above the previous high step.
        let mut high_step_vars: BTreeSet<StepVariable> = BTreeSet::new();

        for bind in new_bindings.iter() {
            // Resolve the varset of the variable.
            let vs1_idx;
            {
                let sv = (bind.var, bind.var_id);
                if bind.var_id <= self.high_step || high_step_vars.contains(&sv) {
                    vs1_idx = find_varset_var(&varsets, bind.var, bind.var_id);
                } else {
                    if bind.var_id > high_step {
                        high_step = bind.var_id;
                    }
                    high_step_vars.insert(sv);
                    vs1_idx = None;
                }
            }
            // Resolve the varset of the term.
            let vs2_idx;
            match bind.term {
                Term::Object(o) => {
                    vs2_idx = find_varset_object(&varsets, o);
                }
                Term::Variable(tv) => {
                    let sv = (tv, bind.term_id);
                    if bind.term_id <= self.high_step || high_step_vars.contains(&sv) {
                        vs2_idx = find_varset_var(&varsets, tv, bind.term_id);
                    } else {
                        if bind.term_id > high_step {
                            high_step = bind.term_id;
                        }
                        high_step_vars.insert(sv);
                        vs2_idx = None;
                    }
                }
            }

            if bind.equality {
                let comb = if vs1_idx.is_some() || vs2_idx.is_some() {
                    if vs1_idx != vs2_idx {
                        if vs1_idx.is_none() {
                            let vs2 = varset_at(&varsets, vs2_idx.unwrap());
                            vs2.add_var(ctx, bind.var, bind.var_id)
                        } else if vs2_idx.is_none() {
                            let vs1 = varset_at(&varsets, vs1_idx.unwrap());
                            vs1.add_term(ctx, bind.term, bind.term_id)
                        } else {
                            let vs1 = varset_at(&varsets, vs1_idx.unwrap());
                            let vs2 = varset_at(&varsets, vs2_idx.unwrap());
                            vs1.combine(ctx, vs2)
                        }
                    } else {
                        // Already bound to each other: reuse existing varset.
                        Some(varset_at(&varsets, vs1_idx.unwrap()).clone_shallow())
                    }
                } else {
                    Varset::make(ctx, bind, false)
                };
                match comb {
                    None => return None,
                    Some(new_vs) => {
                        // Push the combined varset; the resolver searches the
                        // head first, so the most recent class wins.
                        varsets = chain::cons(new_vs, varsets);
                    }
                }
            } else {
                // Inequality binding.
                if vs1_idx.is_some() && vs1_idx == vs2_idx {
                    // Already bound to each other: inconsistent.
                    return None;
                }
                // Separate the second term from the first. When the variable
                // side has no varset yet, `Varset::make(.., false)` returns
                // `None` for an object term — that is NOT a failure (the
                // separation is recorded in the object's varset, `new_vs2`), so
                // we keep it as `None` rather than propagating it.
                let new_vs1 = match vs1_idx {
                    None => Varset::make(ctx, bind, false),
                    Some(i) => {
                        let vs1 = varset_at(&varsets, i);
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
                let new_vs2 = match vs2_idx {
                    None => Varset::make(ctx, bind, true),
                    Some(i) => {
                        let vs2 = varset_at(&varsets, i);
                        if vs2.excludes_var(bind.var, bind.var_id) {
                            None
                        } else {
                            Some(vs2.restrict(bind.var, bind.var_id))
                        }
                    }
                };
                if let Some(v1) = new_vs1 {
                    varsets = chain::cons(v1, varsets);
                }
                if let Some(v2) = new_vs2 {
                    varsets = chain::cons(v2, varsets);
                }
            }
        }

        Some((varsets, high_step))
    }

    /// Checks consistency of an inequality `var != term`.
    pub fn consistent_with_inequality(
        &self,
        var: Variable,
        var_id: usize,
        term: Term,
        term_id: usize,
    ) -> bool {
        let idx = if term_id <= self.high_step {
            match term {
                Term::Object(o) => find_varset_object(&self.varsets, o),
                Term::Variable(tv) => find_varset_var(&self.varsets, tv, term_id),
            }
        } else {
            None
        };
        match idx {
            None => true,
            Some(i) => {
                let vs = chain::iter(&self.varsets).nth(i).unwrap();
                !vs.includes_var(var, var_id) || vs.excludes_var(var, var_id)
            }
        }
    }
}

fn varset_at(varsets: &Option<Rc<Chain<Varset>>>, idx: usize) -> &Varset {
    chain::iter(varsets).nth(idx).unwrap()
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
