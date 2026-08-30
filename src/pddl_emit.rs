//! Faithful PDDL emission of the original lowered classical task.
//!
//! This is deliberately separate from the partial-plan compilation heuristic:
//! translating an empty compiled plan used to relax away quantified formulas
//! and non-conjunctive goals. The FDR grounder and reachability grounder use this
//! module so Fast Downward sees the original task semantics.

use std::collections::BTreeSet;
use std::fmt::Write;
use std::rc::Rc;

use crate::action::ActionSchema;
use crate::domain::Domain;
use crate::effect::Effect;
use crate::formula::{Atom, Formula, Literal};
use crate::problem::{Metric, Problem};
use crate::terms::{Term, TermTable, Variable};
use crate::types::{Type, Types, OBJECT};

/// Emits the original lowered `(domain, problem)` pair without compiling a
/// partial plan or relaxing formulas.
pub fn emit_original(domain: &Domain, problem: &Problem) -> (String, String) {
    (emit_domain(domain), emit_problem(domain, problem))
}

fn emit_domain(domain: &Domain) -> String {
    let mut out = String::new();
    let typed = domain.types.simple_types().count() > 1 || domain.requirements.typing;
    let _ = writeln!(out, "(define (domain {})", domain.name);
    let _ = write!(out, "  (:requirements :strips");
    let requirements = domain.requirements;
    for (enabled, name) in [
        (typed, ":typing"),
        (
            requirements.negative_preconditions,
            ":negative-preconditions",
        ),
        (
            requirements.disjunctive_preconditions,
            ":disjunctive-preconditions",
        ),
        (requirements.equality, ":equality"),
        (
            requirements.existential_preconditions,
            ":existential-preconditions",
        ),
        (
            requirements.universal_preconditions,
            ":universal-preconditions",
        ),
        (requirements.conditional_effects, ":conditional-effects"),
        (requirements.action_costs, ":action-costs"),
    ] {
        if enabled {
            let _ = write!(out, " {name}");
        }
    }
    let _ = writeln!(out, ")");

    let declared_types = domain
        .types
        .simple_types()
        .filter(|&ty| ty != OBJECT)
        .collect::<Vec<_>>();
    if !declared_types.is_empty() {
        let _ = write!(out, "  (:types");
        for ty in declared_types {
            let parents = domain.types.direct_supertypes(ty);
            let _ = write!(
                out,
                " {} - {}",
                domain.types.name(ty),
                render_parents(&domain.types, &parents)
            );
        }
        let _ = writeln!(out, ")");
    }

    let constants = domain.constants.owned_objects().collect::<Vec<_>>();
    if !constants.is_empty() {
        let _ = write!(out, "  (:constants");
        for (object, ty) in constants {
            let _ = write!(
                out,
                " {} - {}",
                domain.constants.object_name(None, object),
                render_type(&domain.types, ty)
            );
        }
        let _ = writeln!(out, ")");
    }

    let _ = writeln!(out, "  (:predicates");
    for index in 0..domain.predicates.len() {
        let predicate = crate::predicates::Predicate(index as u32);
        let _ = write!(out, "    ({0}", domain.predicates.name(predicate));
        for (parameter, ty) in domain.predicates.parameters(predicate).iter().enumerate() {
            let _ = write!(out, " ?p{parameter} - {}", render_type(&domain.types, *ty));
        }
        let _ = writeln!(out, ")");
    }
    let _ = writeln!(out, "  )");

    if requirements.action_costs {
        let _ = writeln!(out, "  (:functions (total-cost) - number)");
    }

    for action in &domain.actions {
        emit_action(&mut out, domain, action);
    }
    let _ = writeln!(out, ")");
    out
}

fn emit_action(out: &mut String, domain: &Domain, action: &ActionSchema) {
    let _ = writeln!(out, "  (:action {}", action.name);
    let _ = write!(out, "    :parameters (");
    for (index, parameter) in action.parameters.iter().enumerate() {
        if index > 0 {
            out.push(' ');
        }
        let ty = action.var_types[parameter.0 as usize];
        let _ = write!(
            out,
            "?v{} - {}",
            parameter.0,
            render_type(&domain.types, ty)
        );
    }
    let _ = writeln!(out, ")");
    let _ = writeln!(
        out,
        "    :precondition {}",
        render_formula(
            &action.precondition,
            &domain.predicates,
            &action.var_types,
            &domain.types,
            &domain.constants,
            None,
        )
    );
    let _ = write!(out, "    :effect (and");
    for effect in &action.effects {
        let _ = write!(
            out,
            " {}",
            render_effect(
                effect,
                &domain.predicates,
                &action.var_types,
                &domain.types,
                &domain.constants,
                None,
            )
        );
    }
    if domain.requirements.action_costs {
        let _ = write!(out, " (increase (total-cost) {})", action.cost);
    }
    let _ = writeln!(out, ")");
    let _ = writeln!(out, "  )");
}

fn emit_problem(domain: &Domain, problem: &Problem) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "(define (problem {})", problem.name);
    let _ = writeln!(out, "  (:domain {})", domain.name);
    let objects = problem.objects.owned_objects().collect::<Vec<_>>();
    if !objects.is_empty() {
        let _ = write!(out, "  (:objects");
        for (object, ty) in objects {
            let _ = write!(
                out,
                " {} - {}",
                problem.objects.object_name(Some(&domain.constants), object),
                render_type(&domain.types, ty)
            );
        }
        let _ = writeln!(out, ")");
    }
    let _ = write!(out, "  (:init");
    for atom in &problem.init_order {
        let _ = write!(
            out,
            " {}",
            render_atom(
                atom,
                &domain.predicates,
                &problem.objects,
                Some(&domain.constants)
            )
        );
    }
    if domain.requirements.action_costs {
        let _ = write!(out, " (= (total-cost) 0)");
    }
    let _ = writeln!(out, ")");
    let _ = writeln!(
        out,
        "  (:goal {})",
        render_formula(
            &problem.goal,
            &domain.predicates,
            &problem.goal_var_types,
            &domain.types,
            &problem.objects,
            Some(&domain.constants),
        )
    );
    if problem.metric == Some(Metric::MinimizeTotalCost) {
        let _ = writeln!(out, "  (:metric minimize (total-cost))");
    }
    let _ = writeln!(out, ")");
    out
}

fn render_effect(
    effect: &Effect,
    predicates: &crate::predicates::PredicateTable,
    var_types: &[Type],
    types: &Types,
    objects: &TermTable,
    parent: Option<&TermTable>,
) -> String {
    let literal = render_literal(&effect.literal, predicates, objects, parent);
    let mut inner = if effect.condition.tautology() {
        literal
    } else {
        format!(
            "(when {} {})",
            render_formula(
                &effect.condition,
                predicates,
                var_types,
                types,
                objects,
                parent,
            ),
            literal
        )
    };
    if !effect.parameters.is_empty() {
        let params = render_parameters(&effect.parameters, var_types, types);
        inner = format!("(forall ({params}) {inner})");
    }
    inner
}

fn render_formula(
    formula: &Rc<Formula>,
    predicates: &crate::predicates::PredicateTable,
    var_types: &[Type],
    types: &Types,
    objects: &TermTable,
    parent: Option<&TermTable>,
) -> String {
    match formula.as_ref() {
        Formula::True => "(and)".to_string(),
        Formula::False => "(or)".to_string(),
        Formula::Atom(atom) => render_atom(atom, predicates, objects, parent),
        Formula::Negation(atom) => {
            format!("(not {})", render_atom(atom, predicates, objects, parent))
        }
        Formula::Equality { left, right, .. } => format!(
            "(= {} {})",
            render_term(*left, objects, parent),
            render_term(*right, objects, parent)
        ),
        Formula::Inequality { left, right, .. } => format!(
            "(not (= {} {}))",
            render_term(*left, objects, parent),
            render_term(*right, objects, parent)
        ),
        Formula::Conjunction(parts) => {
            render_parts("and", parts, predicates, var_types, types, objects, parent)
        }
        Formula::Disjunction(parts) => {
            render_parts("or", parts, predicates, var_types, types, objects, parent)
        }
        Formula::Exists { params, body } => format!(
            "(exists ({}) {})",
            render_parameters(params, var_types, types),
            render_formula(body, predicates, var_types, types, objects, parent)
        ),
        Formula::Forall { params, body } => format!(
            "(forall ({}) {})",
            render_parameters(params, var_types, types),
            render_formula(body, predicates, var_types, types, objects, parent)
        ),
    }
}

fn render_parts(
    connective: &str,
    parts: &[Rc<Formula>],
    predicates: &crate::predicates::PredicateTable,
    var_types: &[Type],
    types: &Types,
    objects: &TermTable,
    parent: Option<&TermTable>,
) -> String {
    let mut out = format!("({connective}");
    for part in parts {
        let _ = write!(
            out,
            " {}",
            render_formula(part, predicates, var_types, types, objects, parent)
        );
    }
    out.push(')');
    out
}

fn render_parameters(params: &[Variable], var_types: &[Type], types: &Types) -> String {
    params
        .iter()
        .map(|parameter| {
            let ty = var_types
                .get(parameter.0 as usize)
                .copied()
                .unwrap_or(OBJECT);
            format!("?v{} - {}", parameter.0, render_type(types, ty))
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn render_literal(
    literal: &Literal,
    predicates: &crate::predicates::PredicateTable,
    objects: &TermTable,
    parent: Option<&TermTable>,
) -> String {
    match literal {
        Literal::Atom(atom) => render_atom(atom, predicates, objects, parent),
        Literal::Negation(atom) => {
            format!("(not {})", render_atom(atom, predicates, objects, parent))
        }
    }
}

fn render_atom(
    atom: &Atom,
    predicates: &crate::predicates::PredicateTable,
    objects: &TermTable,
    parent: Option<&TermTable>,
) -> String {
    render_atom_named(atom, predicates.name(atom.predicate), objects, parent)
}

fn render_atom_named(
    atom: &Atom,
    name: &str,
    objects: &TermTable,
    parent: Option<&TermTable>,
) -> String {
    let mut out = format!("({name}");
    for &term in &atom.terms {
        let _ = write!(out, " {}", render_term(term, objects, parent));
    }
    out.push(')');
    out
}

fn render_term(term: Term, objects: &TermTable, parent: Option<&TermTable>) -> String {
    match term {
        Term::Variable(variable) => format!("?v{}", variable.0),
        Term::Object(object) => objects.object_name(parent, object).to_string(),
    }
}

fn render_type(types: &Types, ty: Type) -> String {
    if ty.simple() {
        return types.name(ty).to_string();
    }
    let mut components = BTreeSet::new();
    types.components(&mut components, ty);
    format!(
        "(either {})",
        components
            .into_iter()
            .map(|component| types.name(component).to_string())
            .collect::<Vec<_>>()
            .join(" ")
    )
}

fn render_parents(types: &Types, parents: &[Type]) -> String {
    match parents {
        [] => types.name(OBJECT).to_string(),
        [parent] => types.name(*parent).to_string(),
        _ => format!(
            "(either {})",
            parents
                .iter()
                .map(|parent| types.name(*parent).to_string())
                .collect::<Vec<_>>()
                .join(" ")
        ),
    }
}
