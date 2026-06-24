//! Lowering from the `pddl` crate AST to the owned data model in this crate.
//!
//! * Requirements are collected, ADL is expanded, and deferred (temporal /
//!   numeric) requirements are rejected up front.
//! * Types are declared, then supertypes wired with transitive closure.
//! * Atoms over an undeclared predicate auto-declare that predicate.
//! * `=` becomes [`Formula::Equality`]; `(not (= ..))` becomes
//!   [`Formula::Inequality`]; `imply a b` becomes `or (not a) b`.
//! * Each action schema gets a fresh variable scope mapping PDDL variable names
//!   to freshly allocated [`Variable`]s.

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use pddl::{
    AtomicFormula, ConditionalEffect, Domain as PddlDomain, EffectCondition, GoalDefinition,
    InitElement, Literal as PddlLiteral, PreconditionGoalDefinition, PreferenceGoalDefinition,
    PrimitiveEffect, Problem as PddlProblem, Requirement, Term as PddlTerm, Type as PddlType,
    TypedList,
};

use crate::action::ActionSchema;
use crate::domain::Domain;
use crate::effect::{Effect, EffectTime};
use crate::formula::{Atom, Formula, Literal};
use crate::functions::FunctionTable;
use crate::predicates::PredicateTable;
use crate::problem::{Optimization, Problem};
use crate::requirements::Requirements;
use crate::terms::{Object, Term, TermTable, Variable};
use crate::types::{Type, Types, OBJECT};

/// Errors produced during lowering.
#[derive(Debug, thiserror::Error)]
pub enum LowerError {
    #[error("unsupported requirement: :{0}")]
    UnsupportedRequirement(String),
    #[error("unknown type: {0}")]
    UnknownType(String),
    #[error("unknown object or constant: {0}")]
    UnknownObject(String),
    #[error("unbound variable: ?{0}")]
    UnboundVariable(String),
    #[error("numeric/object fluent content is not supported in the classical subset: {0}")]
    UnsupportedFluent(String),
    #[error("function terms are not supported in the classical subset")]
    FunctionTerm,
    #[error("preferences are not supported in the classical subset")]
    Preference,
    #[error("derived predicates are not supported in the classical subset")]
    DerivedPredicate,
    #[error("durative actions are not supported in the classical subset")]
    DurativeAction,
    #[error("equality term must be a variable or object")]
    BadEqualityTerm,
}

/// Disambiguating `&str` view for symbol newtypes that implement both
/// `AsRef<str>` and `AsRef<Name>` (`Variable`, `ActionSymbol`, ...).
fn s<T: AsRef<str>>(v: &T) -> &str {
    v.as_ref()
}

/// A per-action variable scope mapping PDDL variable names to allocated
/// [`Variable`]s, supporting nested quantifier scopes.
struct VarScope<'a> {
    terms: &'a mut TermTable,
    /// Stack of name -> variable frames (innermost last).
    frames: Vec<HashMap<String, Variable>>,
}

impl<'a> VarScope<'a> {
    fn new(terms: &'a mut TermTable) -> Self {
        VarScope {
            terms,
            frames: vec![HashMap::new()],
        }
    }

    fn push(&mut self) {
        self.frames.push(HashMap::new());
    }

    fn pop(&mut self) {
        self.frames.pop();
    }

    /// Declares a variable in the innermost frame, allocating a fresh
    /// [`Variable`] of the given type.
    fn declare(&mut self, name: &str, ty: Type) -> Variable {
        let v = self.terms.add_variable(ty);
        self.frames
            .last_mut()
            .unwrap()
            .insert(name.to_string(), v);
        v
    }

    /// Resolves a variable name, searching innermost-to-outermost.
    fn lookup(&self, name: &str) -> Option<Variable> {
        self.frames.iter().rev().find_map(|f| f.get(name).copied())
    }
}

// ---------------------------------------------------------------------------
// Requirements
// ---------------------------------------------------------------------------

fn lower_requirements(reqs: &pddl::Requirements) -> Requirements {
    let mut r = Requirements::new();
    for req in reqs.iter() {
        match req {
            Requirement::Strips => {}
            Requirement::Typing => r.typing = true,
            Requirement::NegativePreconditions => r.negative_preconditions = true,
            Requirement::DisjunctivePreconditions => r.disjunctive_preconditions = true,
            Requirement::Equality => r.equality = true,
            Requirement::ExistentialPreconditions => r.existential_preconditions = true,
            Requirement::UniversalPreconditions => r.universal_preconditions = true,
            Requirement::QuantifiedPreconditions => r.enable_quantified_preconditions(),
            Requirement::ConditionalEffects => r.conditional_effects = true,
            Requirement::Adl => r.enable_adl(),
            // Numeric/object fluents.
            Requirement::Fluents | Requirement::NumericFluents | Requirement::ObjectFluents => {
                r.fluents = true
            }
            Requirement::DurativeActions => r.durative_actions = true,
            Requirement::DurationInequalities => r.duration_inequalities = true,
            Requirement::ContinuousEffects => r.continuous_effects = true,
            Requirement::TimedInitialLiterals => r.timed_initial_literals = true,
            // Action costs use numeric fluents under the hood.
            Requirement::ActionCosts => r.fluents = true,
            // Everything else (preferences, constraints, derived predicates,
            // ...) is not part of the classical subset but does not in itself
            // make a domain temporal/numeric; it is rejected lazily if used.
            _ => {}
        }
    }
    r
}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Resolves a `pddl` type AST node into a [`Type`], declaring simple types as
/// needed and building union types for `(either ...)`.
fn lower_type(types: &mut Types, ty: &PddlType) -> Result<Type, LowerError> {
    match ty {
        PddlType::Exactly(prim) => Ok(types.add_type(prim.as_ref())),
        PddlType::EitherOf(prims) => {
            let mut set = BTreeSet::new();
            for p in prims {
                set.insert(types.add_type(p.as_ref()));
            }
            if set.is_empty() {
                return Ok(OBJECT);
            }
            Ok(types.union_type(set))
        }
    }
}

/// Declares the domain's type hierarchy. Two passes: first declare every simple
/// type name, then wire supertypes.
fn lower_types(types: &mut Types, decls: &TypedList<pddl::Name>) -> Result<(), LowerError> {
    // Pass 1: declare every subtype and (simple) supertype name.
    for entry in decls.iter() {
        types.add_type(entry.value().as_ref());
    }
    // Pass 2: wire supertypes.
    for entry in decls.iter() {
        let sub = types.add_type(entry.value().as_ref());
        let sup = lower_type(types, entry.type_())?;
        types.add_supertype(sub, sup);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

/// Lowers a PDDL term appearing inside a schema body to a [`Term`], resolving
/// variables against the scope and objects/constants against the term tables.
fn lower_term(
    term: &PddlTerm,
    scope: &VarScope,
    consts: &TermTable,
    objects: Option<&TermTable>,
) -> Result<Term, LowerError> {
    match term {
        PddlTerm::Variable(v) => scope
            .lookup(s(v))
            .map(Term::Variable)
            .ok_or_else(|| LowerError::UnboundVariable(s(v).to_string())),
        PddlTerm::Name(n) => {
            // Objects (problem) take precedence over constants (domain), but
            // both share an index space via the parent link.
            if let Some(objs) = objects {
                if let Some(o) = objs.find_object(Some(consts), n.as_ref()) {
                    return Ok(Term::Object(o));
                }
            } else if let Some(o) = consts.find_object(None, n.as_ref()) {
                return Ok(Term::Object(o));
            }
            Err(LowerError::UnknownObject(n.as_ref().to_string()))
        }
        PddlTerm::Function(_) => Err(LowerError::FunctionTerm),
    }
}

// ---------------------------------------------------------------------------
// Formulas (goal descriptions)
// ---------------------------------------------------------------------------

fn predicate_for(preds: &mut PredicateTable, name: &str) -> crate::predicates::Predicate {
    if let Some(p) = preds.find_predicate(name) {
        p
    } else {
        preds.add_predicate(name)
    }
}

/// Lowers an `AtomicFormula<Term>` into either an [`Atom`] (for predicates) or an
/// equality/inequality pair of terms.
enum LoweredAtomic {
    Atom(Atom),
    Equality(Term, Term),
}

fn lower_atomic(
    af: &AtomicFormula<PddlTerm>,
    preds: &mut PredicateTable,
    scope: &VarScope,
    consts: &TermTable,
    objects: Option<&TermTable>,
) -> Result<LoweredAtomic, LowerError> {
    match af {
        AtomicFormula::Equality(eq) => {
            let l = lower_term(eq.first(), scope, consts, objects)?;
            let r = lower_term(eq.second(), scope, consts, objects)?;
            Ok(LoweredAtomic::Equality(l, r))
        }
        AtomicFormula::Predicate(pa) => {
            let pred = predicate_for(preds, s(pa.predicate()));
            let mut terms = Vec::with_capacity(pa.values().len());
            for t in pa.values() {
                terms.push(lower_term(t, scope, consts, objects)?);
            }
            Ok(LoweredAtomic::Atom(Atom {
                predicate: pred,
                terms,
            }))
        }
    }
}

fn lower_goal(
    gd: &GoalDefinition,
    preds: &mut PredicateTable,
    types: &mut Types,
    scope: &mut VarScope,
    consts: &TermTable,
    objects: Option<&TermTable>,
) -> Result<Rc<Formula>, LowerError> {
    match gd {
        GoalDefinition::AtomicFormula(af) => match lower_atomic(af, preds, scope, consts, objects)? {
            LoweredAtomic::Atom(a) => Ok(Rc::new(Formula::Atom(a))),
            LoweredAtomic::Equality(l, r) => Ok(Formula::equality(l, r)),
        },
        GoalDefinition::Literal(lit) => match lit {
            PddlLiteral::AtomicFormula(af) => {
                match lower_atomic(af, preds, scope, consts, objects)? {
                    LoweredAtomic::Atom(a) => Ok(Rc::new(Formula::Atom(a))),
                    LoweredAtomic::Equality(l, r) => {
                        Ok(Formula::equality(l, r))
                    }
                }
            }
            PddlLiteral::NotAtomicFormula(af) => {
                match lower_atomic(af, preds, scope, consts, objects)? {
                    LoweredAtomic::Atom(a) => Ok(Rc::new(Formula::Negation(a))),
                    LoweredAtomic::Equality(l, r) => {
                        Ok(Formula::inequality(l, r))
                    }
                }
            }
        },
        GoalDefinition::And(gs) => {
            let mut acc = Rc::new(Formula::True);
            for g in gs {
                let f = lower_goal(g, preds, types, scope, consts, objects)?;
                acc = Formula::and(acc, f);
            }
            Ok(acc)
        }
        GoalDefinition::Or(gs) => {
            let mut acc = Rc::new(Formula::False);
            for g in gs {
                let f = lower_goal(g, preds, types, scope, consts, objects)?;
                acc = Formula::or(acc, f);
            }
            Ok(acc)
        }
        GoalDefinition::Not(g) => {
            let f = lower_goal(g, preds, types, scope, consts, objects)?;
            Ok(f.negation())
        }
        // imply a b == (not a) or b.
        GoalDefinition::Imply(a, b) => {
            let fa = lower_goal(a, preds, types, scope, consts, objects)?;
            let fb = lower_goal(b, preds, types, scope, consts, objects)?;
            Ok(Formula::or(fa.negation(), fb))
        }
        GoalDefinition::Exists(vars, body) => {
            scope.push();
            let params = declare_typed_variables(vars, types, scope)?;
            let f = lower_goal(body, preds, types, scope, consts, objects)?;
            scope.pop();
            Ok(Rc::new(Formula::Exists { params, body: f }))
        }
        GoalDefinition::ForAll(vars, body) => {
            scope.push();
            let params = declare_typed_variables(vars, types, scope)?;
            let f = lower_goal(body, preds, types, scope, consts, objects)?;
            scope.pop();
            Ok(Rc::new(Formula::Forall { params, body: f }))
        }
        GoalDefinition::FluentComparison(_) => {
            Err(LowerError::UnsupportedFluent("fluent comparison".to_string()))
        }
    }
}

/// Declares a typed-variable list into the current (already-pushed) scope frame,
/// returning the allocated variables in order. Used for quantifiers and forall
/// effects.
fn declare_typed_variables(
    vars: &TypedList<pddl::Variable>,
    types: &mut Types,
    scope: &mut VarScope,
) -> Result<Vec<Variable>, LowerError> {
    let mut params = Vec::new();
    for entry in vars.iter() {
        let ty = lower_type(types, entry.type_())?;
        let v = scope.declare(s(entry.value()), ty);
        params.push(v);
    }
    Ok(params)
}

// ---------------------------------------------------------------------------
// Effects
// ---------------------------------------------------------------------------

/// Lowers a primitive effect (an add/delete literal). Numeric/object fluent
/// assignments are rejected. Marks the predicate dynamic.
fn lower_primitive_effect(
    pe: &PrimitiveEffect,
    preds: &mut PredicateTable,
    scope: &VarScope,
    consts: &TermTable,
    objects: Option<&TermTable>,
) -> Result<Literal, LowerError> {
    match pe {
        PrimitiveEffect::AtomicFormula(af) => {
            match lower_atomic(af, preds, scope, consts, objects)? {
                LoweredAtomic::Atom(a) => {
                    preds.make_dynamic(a.predicate);
                    Ok(Literal::Atom(a))
                }
                LoweredAtomic::Equality(..) => Err(LowerError::BadEqualityTerm),
            }
        }
        PrimitiveEffect::NotAtomicFormula(af) => {
            match lower_atomic(af, preds, scope, consts, objects)? {
                LoweredAtomic::Atom(a) => {
                    preds.make_dynamic(a.predicate);
                    Ok(Literal::Negation(a))
                }
                LoweredAtomic::Equality(..) => Err(LowerError::BadEqualityTerm),
            }
        }
        PrimitiveEffect::AssignNumericFluent(..) => {
            Err(LowerError::UnsupportedFluent("numeric assignment".to_string()))
        }
        PrimitiveEffect::AssignObjectFluent(..) => {
            Err(LowerError::UnsupportedFluent("object assignment".to_string()))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_conditional_effect(
    ce: &ConditionalEffect,
    out: &mut Vec<Effect>,
    preds: &mut PredicateTable,
    types: &mut Types,
    scope: &mut VarScope,
    consts: &TermTable,
    objects: Option<&TermTable>,
    parameters: &[Variable],
    condition: &Rc<Formula>,
) -> Result<(), LowerError> {
    match ce {
        ConditionalEffect::Effect(pe) => {
            let literal = lower_primitive_effect(pe, preds, scope, consts, objects)?;
            out.push(Effect {
                parameters: parameters.to_vec(),
                condition: condition.clone(),
                literal,
                when: EffectTime::AtEnd,
                link_condition: Rc::new(Formula::True),
            });
            Ok(())
        }
        ConditionalEffect::Forall(fa) => {
            scope.push();
            let mut params = parameters.to_vec();
            params.extend(declare_typed_variables(&fa.variables, types, scope)?);
            for inner in fa.effects.iter() {
                lower_conditional_effect(
                    inner, out, preds, types, scope, consts, objects, &params, condition,
                )?;
            }
            scope.pop();
            Ok(())
        }
        ConditionalEffect::When(w) => {
            // The guard is evaluated in the current scope.
            let guard = lower_goal(&w.condition, preds, types, scope, consts, objects)?;
            let combined = Formula::and(condition.clone(), guard);
            match &w.effect {
                EffectCondition::Single(pe) => {
                    let literal = lower_primitive_effect(pe, preds, scope, consts, objects)?;
                    out.push(Effect {
                        parameters: parameters.to_vec(),
                        condition: combined,
                        literal,
                        when: EffectTime::AtEnd,
                        link_condition: Rc::new(Formula::True),
                    });
                }
                EffectCondition::All(pes) => {
                    for pe in pes {
                        let literal = lower_primitive_effect(pe, preds, scope, consts, objects)?;
                        out.push(Effect {
                            parameters: parameters.to_vec(),
                            condition: combined.clone(),
                            literal,
                            when: EffectTime::AtEnd,
                            link_condition: Rc::new(Formula::True),
                        });
                    }
                }
            }
            Ok(())
        }
    }
}

// ---------------------------------------------------------------------------
// Precondition goal definitions
// ---------------------------------------------------------------------------

/// Lowers a `PreconditionGoalDefinition` (the top-level precondition / goal
/// wrapper that may contain a `forall` or a plain goal description).
fn lower_precondition(
    pgd: &PreconditionGoalDefinition,
    preds: &mut PredicateTable,
    types: &mut Types,
    scope: &mut VarScope,
    consts: &TermTable,
    objects: Option<&TermTable>,
) -> Result<Rc<Formula>, LowerError> {
    match pgd {
        PreconditionGoalDefinition::Preference(pref) => match pref {
            PreferenceGoalDefinition::Goal(gd) => {
                lower_goal(gd, preds, types, scope, consts, objects)
            }
            PreferenceGoalDefinition::Preference(_) => Err(LowerError::Preference),
        },
        PreconditionGoalDefinition::Forall(vars, body) => {
            scope.push();
            let params = declare_typed_variables(vars, types, scope)?;
            let f = lower_preconditions(body, preds, types, scope, consts, objects)?;
            scope.pop();
            Ok(Rc::new(Formula::Forall { params, body: f }))
        }
    }
}

/// Lowers a list of precondition goal definitions, conjoining them.
fn lower_preconditions(
    pgds: &pddl::PreconditionGoalDefinitions,
    preds: &mut PredicateTable,
    types: &mut Types,
    scope: &mut VarScope,
    consts: &TermTable,
    objects: Option<&TermTable>,
) -> Result<Rc<Formula>, LowerError> {
    let mut acc = Rc::new(Formula::True);
    for pgd in pgds.iter() {
        let f = lower_precondition(pgd, preds, types, scope, consts, objects)?;
        acc = Formula::and(acc, f);
    }
    Ok(acc)
}

// ---------------------------------------------------------------------------
// Domain lowering
// ---------------------------------------------------------------------------

/// Lowers a parsed PDDL domain into the owned [`Domain`] model.
pub fn lower_domain(d: &PddlDomain) -> Result<Domain, LowerError> {
    // 1. Requirements.
    let requirements = lower_requirements(d.requirements());
    requirements.reject_deferred()?;

    // 2. Types (+ supertypes).
    let mut types = Types::new();
    lower_types(&mut types, d.types())?;

    // 3. Constants.
    let mut constants = TermTable::new();
    lower_objects_into(&mut constants, None, &mut types, d.constants())?;

    // 4. Predicates.
    let mut predicates = PredicateTable::new();
    for skel in d.predicates().values() {
        let p = predicates.add_predicate(skel.name().as_ref());
        for entry in skel.variables().iter() {
            let ty = lower_type(&mut types, entry.type_())?;
            predicates.add_parameter(p, ty);
        }
    }

    // 5. Functions (declared so they can be referenced and rejected).
    let mut functions = FunctionTable::new();
    for ft in d.functions().values().values() {
        let skel = ft.value_ref();
        let f = functions.add_function(s(skel.symbol()));
        for entry in skel.variables().iter() {
            let ty = lower_type(&mut types, entry.type_())?;
            functions.add_parameter(f, ty);
        }
    }

    // 6. Action schemas.
    let mut actions = Vec::new();
    let mut actions_by_name = HashMap::new();
    for sdef in d.structure().iter() {
        let action = match sdef {
            pddl::StructureDef::Action(a) => a,
            pddl::StructureDef::DurativeAction(_) => return Err(LowerError::DurativeAction),
            pddl::StructureDef::Derived(_) => return Err(LowerError::DerivedPredicate),
        };
        let id = actions.len();
        let name = s(action.symbol()).to_string();

        // Each schema gets its own variable scope.
        let mut term_table = TermTable::new();
        let (parameters, precondition, effects) = {
            let mut scope = VarScope::new(&mut term_table);
            // Declare schema parameters in the base frame.
            let parameters = declare_typed_variables(action.parameters(), &mut types, &mut scope)?;

            let precondition = lower_preconditions(
                action.precondition(),
                &mut predicates,
                &mut types,
                &mut scope,
                &constants,
                None,
            )?;

            let mut effects = Vec::new();
            if let Some(effs) = action.effect() {
                let no_params: Vec<Variable> = Vec::new();
                let truth = Rc::new(Formula::True);
                for ce in effs.iter() {
                    lower_conditional_effect(
                        ce,
                        &mut effects,
                        &mut predicates,
                        &mut types,
                        &mut scope,
                        &constants,
                        None,
                        &no_params,
                        &truth,
                    )?;
                }
            }
            // Compute effect link conditions (e.g. move's (not (= ?from ?to))).
            crate::effect::strengthen_effects(&mut effects, &precondition);
            (parameters, precondition, effects)
        };

        let schema = ActionSchema {
            id,
            name: name.clone(),
            parameters,
            var_types: term_table.variable_types().to_vec(),
            precondition,
            effects,
        };
        actions_by_name.insert(name, id);
        actions.push(schema);
    }

    Ok(Domain {
        name: d.name().as_ref().to_string(),
        requirements,
        types,
        predicates,
        functions,
        constants,
        actions,
        actions_by_name,
    })
}

fn lower_objects_into(
    table: &mut TermTable,
    _parent: Option<&TermTable>,
    types: &mut Types,
    decls: &TypedList<pddl::Name>,
) -> Result<(), LowerError> {
    for entry in decls.iter() {
        let ty = lower_type(types, entry.type_())?;
        table.add_object(entry.value().as_ref(), ty);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Problem lowering
// ---------------------------------------------------------------------------

/// Lowers a parsed PDDL problem against an already-lowered [`Domain`].
///
/// The problem's predicate/type/function tables are derived from a *clone-free*
/// view: we mutate fresh copies seeded from the domain so undeclared predicates
/// in the goal/init can be auto-declared without disturbing the domain. Since
/// later phases re-derive ground structure from the domain, the problem only
/// needs its objects, init, goal, and metric.
pub fn lower_problem(p: &PddlProblem, domain: &Domain) -> Result<Problem, LowerError> {
    let requirements = lower_requirements(p.requirements());
    requirements.reject_deferred()?;

    // Working copies of the mutable tables. The domain stays immutable; we copy
    // the parts we may extend (types for object types, predicates for
    // auto-declaration).
    let mut types = clone_types(&domain.types);
    let mut predicates = clone_predicates(&domain.predicates);

    // Objects extend the domain constants.
    let mut objects = TermTable::with_parent(&domain.constants);
    for entry in p.objects().values().iter() {
        let ty = lower_type(&mut types, entry.type_())?;
        objects.add_object(entry.value().as_ref(), ty);
    }

    // Init: ground atoms / fluent values.
    let mut init_atoms = std::collections::HashSet::new();
    let mut init_order = Vec::new();
    let mut init_values = Vec::new();
    for el in p.init().values() {
        lower_init_element(
            el,
            &mut init_atoms,
            &mut init_order,
            &mut init_values,
            &mut predicates,
            &domain.constants,
            &objects,
        )?;
    }

    // Goal.
    let mut goal_term_table = TermTable::new();
    let goal = {
        let mut scope = VarScope::new(&mut goal_term_table);
        lower_preconditions(
            p.goals(),
            &mut predicates,
            &mut types,
            &mut scope,
            &domain.constants,
            Some(&objects),
        )?
    };
    let goal_var_types = goal_term_table.variable_types().to_vec();

    // Metric (recorded only).
    let metric = p.metric_spec().as_ref().map(|m| match m.optimization() {
        pddl::Optimization::Minimize => Optimization::Minimize,
        pddl::Optimization::Maximize => Optimization::Maximize,
    });

    Ok(Problem {
        name: p.name().as_ref().to_string(),
        domain_name: p.domain().as_ref().to_string(),
        objects,
        init_atoms,
        init_order,
        init_values,
        goal,
        goal_var_types,
        metric,
    })
}

/// Lowers a single init element into a ground atom or fluent value.
fn lower_init_element(
    el: &InitElement,
    atoms: &mut std::collections::HashSet<Atom>,
    order: &mut Vec<Atom>,
    _values: &mut Vec<(crate::expressions::Fluent, f64)>,
    preds: &mut PredicateTable,
    consts: &TermTable,
    objects: &TermTable,
) -> Result<(), LowerError> {
    match el {
        InitElement::Literal(lit) => {
            // NameLiteral = Literal<Name>: ground literals.
            let (af, _negated) = match lit {
                PddlLiteral::AtomicFormula(af) => (af, false),
                PddlLiteral::NotAtomicFormula(af) => (af, true),
            };
            // Negated init literals (closed-world) are dropped: absence already
            // means false.
            match af {
                AtomicFormula::Predicate(pa) => {
                    let pred = predicate_for(preds, s(pa.predicate()));
                    let mut terms = Vec::with_capacity(pa.values().len());
                    for n in pa.values() {
                        let o = resolve_object(n.as_ref(), consts, objects)?;
                        terms.push(Term::Object(o));
                    }
                    if !_negated {
                        let atom = Atom {
                            predicate: pred,
                            terms,
                        };
                        if atoms.insert(atom.clone()) {
                            order.push(atom);
                        }
                    }
                }
                AtomicFormula::Equality(_) => {
                    // (= a b) in init is meaningless for the classical subset.
                }
            }
            Ok(())
        }
        // Timed initial literals and fluent value assignments are deferred. They
        // only appear with deferred requirements, which were already rejected;
        // reaching here means malformed input for the classical subset.
        InitElement::At(..) => Err(LowerError::UnsupportedRequirement(
            "timed-initial-literals".to_string(),
        )),
        InitElement::IsValue(..) | InitElement::IsObject(..) => {
            Err(LowerError::UnsupportedFluent("init fluent value".to_string()))
        }
    }
}

/// Resolves a ground object name against problem objects then domain constants.
fn resolve_object(name: &str, consts: &TermTable, objects: &TermTable) -> Result<Object, LowerError> {
    objects
        .find_object(Some(consts), name)
        .ok_or_else(|| LowerError::UnknownObject(name.to_string()))
}

// ---------------------------------------------------------------------------
// Cheap table copies for problem lowering
// ---------------------------------------------------------------------------
//
// The `Types` and `PredicateTable` structs do not derive `Clone` (they are owned
// by exactly one domain in normal use). For problem lowering we need a private,
// extendable view, so we rebuild them by replaying their public construction.
// This keeps the domain immutable and avoids global state.

fn clone_types(src: &Types) -> Types {
    src.clone()
}

fn clone_predicates(src: &PredicateTable) -> PredicateTable {
    src.clone()
}
