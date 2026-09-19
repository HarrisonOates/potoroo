//! Independent POCL plan-validity checks.
//!
//! Recompute causal-link support and threats, then replay the emitted
//! linearization against actual states to check preconditions and the goal.
//! Replay is independent of the planner's flaw bookkeeping.

use crate::chain;
use crate::formula::Literal;
use crate::formula::{Atom, Formula};
use crate::orderings::StepTime;
use crate::plan::{Link, Plan, Step, INIT_ID};
use crate::search::SearchContext;
use crate::terms::{Object, Term, Variable};
use crate::types::Type;
use std::collections::{HashMap, HashSet};

/// Checks that `plan` is a valid POCL solution. Returns `Ok(())` if so, or
/// `Err(reason)` describing the first violation found.
///
/// Four checks:
/// 1. No open conditions remain in the stored flaw list.
/// 2. Each causal link is *supported*: its producer step has an effect whose
///    literal unifies with the link condition under the plan's bindings.
/// 3. Each causal link is *unthreatened*: no step with a clobbering effect can be
///    ordered into the protected interval (recomputed, not read from `unsafes`).
/// 4. The emitted sequence is executable and reaches the goal.
pub fn is_valid_solution(plan: &Plan, ctx: &SearchContext) -> Result<(), String> {
    ctx.register_plan(plan);
    // (1) No open conditions.
    if plan.num_open_conds != 0 || plan.open_conds.is_some() {
        return Err(format!(
            "plan has {} open condition(s); not a complete solution",
            plan.num_open_conds
        ));
    }

    // (2) Every causal link is supported by an effect of its producer.
    for link in chain::iter(&plan.links) {
        if !link_supported(plan, ctx, link) {
            return Err(format!(
                "causal link {} --{:?}--> {} is unsupported: producer has no effect \
                 unifying with the link condition",
                link.from_id, link.condition, link.to_id
            ));
        }
    }

    // (3) No causal link is threatened.
    for link in chain::iter(&plan.links) {
        if let Some(threat_id) = link_threatened_by(plan, ctx, link) {
            return Err(format!(
                "causal link {} --{:?}--> {} is threatened by step {}",
                link.from_id, link.condition, link.to_id, threat_id
            ));
        }
    }

    is_executable_solution(plan, ctx)
}

/// Replays the printed linearization from the actual initial state. This does
/// not trust links or the flaw counters: every action precondition, conditional
/// effect, quantified formula and final goal is evaluated independently.
/// Used in release search as well as by the structural checker above.
pub fn is_executable_solution(plan: &Plan, ctx: &SearchContext) -> Result<(), String> {
    let (times, _) = plan.orderings.schedule();
    let mut steps: Vec<_> = chain::iter(&plan.steps)
        .filter(|step| step.id != INIT_ID && step.id != crate::plan::GOAL_ID)
        .collect();
    // Match format_steps, including the stable tie order.
    steps.sort_by(|a, b| {
        times
            .get(&a.id)
            .unwrap_or(&0.0)
            .total_cmp(times.get(&b.id).unwrap_or(&0.0))
    });
    let mut state = ctx.problem.init_atoms.clone();
    for step in steps {
        let mut substitution = HashMap::new();
        for &variable in &step.action.parameters {
            let Term::Object(object) = plan.bindings.binding(Term::Variable(variable), step.id)
            else {
                return Err(format!("step {} has an unbound argument", step.id));
            };
            if !ctx.domain.types.subtype(
                ctx.problem
                    .objects
                    .object_type(Some(&ctx.domain.constants), object),
                step.action.var_types[variable.0 as usize],
            ) {
                return Err(format!(
                    "step {} has an argument of the wrong type",
                    step.id
                ));
            }
            substitution.insert(variable, object);
        }
        let types = &step.action.var_types;
        if !holds(
            &step.action.precondition,
            &state,
            ctx,
            types,
            &mut substitution,
        )? {
            return Err(format!(
                "step {} ({}) has a false precondition",
                step.id, step.action.name
            ));
        }
        let mut adds = Vec::new();
        let mut deletes = Vec::new();
        for effect in &step.action.effects {
            quantify(
                &effect.parameters,
                ctx,
                types,
                &mut substitution,
                false,
                &mut |subst| {
                    if holds(&effect.condition, &state, ctx, types, subst)? {
                        let atom = ground_atom(effect.literal.atom(), subst)?;
                        if effect.literal.negative() {
                            deletes.push(atom);
                        } else {
                            adds.push(atom);
                        }
                    }
                    Ok(true)
                },
            )?;
        }
        // All guards read the predecessor state; simultaneous adds win over
        // deletes, independent of the order effects were declared in.
        for atom in deletes {
            state.remove(&atom);
        }
        state.extend(adds);
    }
    if holds(
        &ctx.problem.goal,
        &state,
        ctx,
        &ctx.problem.goal_var_types,
        &mut HashMap::new(),
    )? {
        Ok(())
    } else {
        Err("the final state does not satisfy the goal".to_string())
    }
}

fn ground_term(term: Term, subst: &HashMap<Variable, Object>) -> Result<Object, String> {
    match term {
        Term::Object(o) => Ok(o),
        Term::Variable(v) => subst
            .get(&v)
            .copied()
            .ok_or_else(|| format!("unbound variable {:?} in replay", v)),
    }
}

fn ground_atom(atom: &Atom, subst: &HashMap<Variable, Object>) -> Result<Atom, String> {
    Ok(Atom {
        predicate: atom.predicate,
        terms: atom
            .terms
            .iter()
            .map(|&term| ground_term(term, subst).map(Term::Object))
            .collect::<Result<_, _>>()?,
    })
}

fn holds(
    formula: &Formula,
    state: &HashSet<Atom>,
    ctx: &SearchContext,
    types: &[Type],
    subst: &mut HashMap<Variable, Object>,
) -> Result<bool, String> {
    match formula {
        Formula::True => Ok(true),
        Formula::False => Ok(false),
        Formula::Atom(a) => Ok(state.contains(&ground_atom(a, subst)?)),
        Formula::Negation(a) => Ok(!state.contains(&ground_atom(a, subst)?)),
        Formula::Equality { left, right, .. } => {
            Ok(ground_term(*left, subst)? == ground_term(*right, subst)?)
        }
        Formula::Inequality { left, right, .. } => {
            Ok(ground_term(*left, subst)? != ground_term(*right, subst)?)
        }
        Formula::Conjunction(parts) => {
            for part in parts {
                if !holds(part, state, ctx, types, subst)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Formula::Disjunction(parts) => {
            for part in parts {
                if holds(part, state, ctx, types, subst)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Formula::Exists { params, body } | Formula::Forall { params, body } => quantify(
            params,
            ctx,
            types,
            subst,
            matches!(formula, Formula::Exists { .. }),
            &mut |subst| holds(body, state, ctx, types, subst),
        ),
    }
}

fn quantify<F: FnMut(&mut HashMap<Variable, Object>) -> Result<bool, String>>(
    params: &[Variable],
    ctx: &SearchContext,
    types: &[Type],
    subst: &mut HashMap<Variable, Object>,
    existential: bool,
    evaluate: &mut F,
) -> Result<bool, String> {
    let Some((&variable, rest)) = params.split_first() else {
        return evaluate(subst);
    };
    let ty = *types
        .get(variable.0 as usize)
        .ok_or_else(|| "missing quantified variable type".to_string())?;
    let saved = subst.get(&variable).copied();
    let mut result = Ok(!existential);
    for object in ctx.compatible_objects(ty) {
        subst.insert(variable, object);
        match quantify(rest, ctx, types, subst, existential, evaluate) {
            Ok(value) if value != existential => {}
            other => {
                result = other;
                break;
            }
        }
    }
    if let Some(value) = saved {
        subst.insert(variable, value);
    } else {
        subst.remove(&variable);
    }
    result
}

fn find_step(plan: &Plan, id: usize) -> Option<Step> {
    chain::iter(&plan.steps).find(|s| s.id == id).cloned()
}

/// Whether the producer of `link` has an effect whose literal positively unifies
/// with the link's protected condition under the plan's bindings.
///
/// A negative link from `INIT_ID` is the closed-world case: [`Plan::new_cw_link`]
/// supports it by the *absence* of a matching init atom, not by any actual
/// effect, so it needs its own check below rather than `unify`.
fn link_supported(plan: &Plan, ctx: &SearchContext, link: &Link) -> bool {
    let Some(producer) = find_step(plan, link.from_id) else {
        return false;
    };
    let type_ctx = ctx.type_ctx();
    if link.from_id == INIT_ID && link.condition.negative() {
        let atom = Literal::Atom(link.condition.atom().clone());
        return producer.action.effects.iter().all(|e| {
            !plan
                .bindings
                .unify(&type_ctx, &e.literal, link.from_id, &atom, link.to_id)
        });
    }
    producer.action.effects.iter().any(|e| {
        plan.bindings.unify(
            &type_ctx,
            &e.literal,
            link.from_id,
            &link.condition,
            link.to_id,
        )
    })
}

/// Recomputes whether any step threatens `link`, returning the threatening step
/// id if so. Reports rather than records, and does not consult the plan's stored
/// `unsafes`.
/// Whether the plan has committed against `effect`'s guard at `step_id`, so the
/// effect cannot fire there and threatens nothing.
///
/// This is UCPOP's *confrontation*, which potoroo folds into its separation
/// refinement: rather than ordering the threatening step out of the protected
/// interval, the refinement adds the negated guard as an open condition on that
/// step, and a complete plan closes it with a causal link. A guard literal whose
/// negation is linked into the step is therefore proof that the effect is dead
/// there.
///
/// Without this, every confronted conditional effect reads as an unresolved
/// threat and valid plans are reported invalid — `briefcase-world` resolves
/// `(when (in p) ...)` exactly this way.
fn effect_confronted(plan: &Plan, effect: &crate::effect::Effect, step_id: usize) -> bool {
    fn disproved(plan: &Plan, formula: &crate::formula::Formula, step: usize) -> bool {
        use crate::formula::Formula;
        if plan.bindings.contradicts(formula, step) {
            return true;
        }
        match formula {
            Formula::Conjunction(parts) => parts.iter().any(|p| disproved(plan, p, step)),
            Formula::Disjunction(parts) => parts.iter().all(|p| disproved(plan, p, step)),
            Formula::Atom(atom) | Formula::Negation(atom) => {
                let negative = matches!(formula, Formula::Negation(_));
                chain::iter(&plan.links).any(|link| {
                    let other = link.condition.atom();
                    link.to_id == step
                        && link.condition.negative() != negative
                        && atom.predicate == other.predicate
                        && atom.terms.len() == other.terms.len()
                        && atom
                            .terms
                            .iter()
                            .zip(&other.terms)
                            .all(|(&a, &b)| plan.bindings.terms_equal(a, step, b, link.to_id))
                })
            }
            // Quantified guards require instance-wise evidence.
            _ => false,
        }
    }
    disproved(plan, &effect.condition, step_id) || disproved(plan, &effect.link_condition, step_id)
}

fn link_threatened_by(plan: &Plan, ctx: &SearchContext, link: &Link) -> Option<usize> {
    let orderings = &plan.orderings;
    let bindings = &plan.bindings;
    let type_ctx = ctx.type_ctx();
    let lt1 = link.effect_time;
    let lt2 = link.condition_time.end_time();

    for s in chain::iter(&plan.steps) {
        // Cheap window prune: the step must be orderable strictly between the
        // link's producer and consumer.
        if !(orderings.possibly_not_after(link.from_id, lt1, s.id, StepTime::AtEnd)
            && orderings.possibly_not_before(link.to_id, lt2, s.id, StepTime::AtStart))
        {
            continue;
        }
        for e in s.action.effects.iter() {
            // A contradictory link condition means the effect can never fire in a
            // way that clobbers, so it is not a real threat.
            if !e.threat_possible(bindings, s.id) {
                continue;
            }
            // Nor is a conditional effect the plan has already committed
            // against: confrontation resolves the threat without ordering the
            // step anywhere.
            if effect_confronted(plan, e, s.id) {
                continue;
            }
            let et = StepTime::AtEnd;
            if (s.id != link.to_id)
                && orderings.possibly_not_after(link.from_id, lt1, s.id, et)
                && orderings.possibly_not_before(link.to_id, lt2, s.id, et)
            {
                let neg_condition = link.condition.negative();
                if (neg_condition || (link.from_id != s.id))
                    && bindings.affects(&type_ctx, &e.literal, s.id, &link.condition, link.to_id)
                {
                    return Some(s.id);
                }
            }
        }
    }
    None
}
