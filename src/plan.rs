//! Partial plans and their refinement for the classical (non-temporal,
//! non-numeric) subset. Mutex threats are temporal-only and kept as an
//! always-empty placeholder.
//!
//! A [`Plan`] is an immutable node sharing its step/link/unsafe/open-condition
//! collections (persistent [`Chain`]s) with its parent, plus an
//! [`Rc<BinaryOrderings>`] and [`Rc<Bindings>`]. Refinement selects one flaw and
//! produces zero or more child plans. The refinement order and plan-id
//! assignment are kept identical to VHPOP's, because they determine which
//! optimal plan A* returns.

use std::collections::HashMap;
use std::rc::Rc;

use crate::bindings::{Binding, Bindings, StepVarTypes};
use crate::chain::{self, Chain};
use crate::effect::Effect;
use crate::flaws::{Flaw, FormulaTime, OpenCondition, Unsafe};
use crate::formula::{Atom, Formula, Literal};
use crate::orderings::{BinaryOrderings, Ordering, StepTime};
use crate::search::SearchContext;
use crate::terms::{Term, Variable};

pub const GOAL_ID: usize = usize::MAX;
/// Id of the initial step.
pub const INIT_ID: usize = 0;

/// An action a step is instantiated from — an action schema (lifted), a ground
/// action, or the synthetic init/goal action.
#[derive(Debug)]
pub struct StepAction {
    /// Action name. `<init 0>` for the init step, empty for the goal step.
    pub name: String,
    /// Schema parameters, in order (lifted steps). Empty for ground/init/goal.
    pub parameters: Vec<Variable>,
    /// Ground arguments, in order (ground steps). Empty for lifted/init/goal.
    pub arguments: Vec<crate::terms::Object>,
    /// Precondition formula (the goal formula for the goal step).
    pub precondition: Rc<Formula>,
    /// Effects (the init atoms for the init step; empty for the goal step).
    pub effects: Vec<Effect>,
    /// Variable types in this action's scope, indexed by variable index.
    pub var_types: Vec<crate::types::Type>,
}

impl StepAction {
    /// Whether this is a synthetic action (name begins with `<` or is empty),
    /// skipped in add/reuse-step and in plan output. The goal action's empty
    /// name is never an achiever and prints nothing.
    pub fn synthetic(&self) -> bool {
        self.name.starts_with('<') || self.name.is_empty()
    }
}

#[derive(Debug, Clone)]
pub struct Step {
    pub id: usize,
    pub action: Rc<StepAction>,
}

impl PartialEq for Step {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && Rc::ptr_eq(&self.action, &other.action)
    }
}

/// A causal link `from_id --condition--> to_id`.
#[derive(Debug, Clone)]
pub struct Link {
    pub from_id: usize,
    pub effect_time: StepTime,
    pub to_id: usize,
    pub condition: Literal,
    pub condition_time: FormulaTime,
}

impl PartialEq for Link {
    fn eq(&self, other: &Self) -> bool {
        self.from_id == other.from_id
            && self.to_id == other.to_id
            && self.condition == other.condition
            && self.condition_time == other.condition_time
    }
}

pub struct Plan {
    pub steps: Option<Rc<Chain<Step>>>,
    pub num_steps: usize,
    pub links: Option<Rc<Chain<Link>>>,
    pub num_links: usize,
    pub orderings: Rc<BinaryOrderings>,
    pub bindings: Rc<Bindings>,
    pub unsafes: Option<Rc<Chain<Unsafe>>>,
    pub num_unsafes: usize,
    pub open_conds: Option<Rc<Chain<OpenCondition>>>,
    pub num_open_conds: usize,
    /// Serial number (set before rank is computed).
    pub id: std::cell::Cell<usize>,
}

impl Plan {
    pub fn num_steps(&self) -> usize {
        self.num_steps
    }
    pub fn num_open_conds(&self) -> usize {
        self.num_open_conds
    }
    pub fn num_unsafes(&self) -> usize {
        self.num_unsafes
    }
    pub fn serial_no(&self) -> usize {
        self.id.get()
    }
    pub fn unsafes(&self) -> &Option<Rc<Chain<Unsafe>>> {
        &self.unsafes
    }
    pub fn open_conds(&self) -> &Option<Rc<Chain<OpenCondition>>> {
        &self.open_conds
    }

    pub fn complete(&self) -> bool {
        self.unsafes.is_none() && self.open_conds.is_none()
    }

    pub fn primary_rank(&self, ctx: &SearchContext) -> f32 {
        self.rank(ctx)[0]
    }

    /// Full rank vector. Each generated plan is ranked exactly once (the result
    /// is carried by its queue entry), so no caching is kept on the plan itself
    /// — that just duplicated the vector for millions of queued plans.
    pub fn rank(&self, ctx: &SearchContext) -> Vec<f32> {
        let type_ctx = ctx.type_ctx();
        // Build the planning graph on demand for the additive heuristics.
        let pg = if ctx.params.heuristic.needs_planning_graph() {
            Some(ctx.planning_graph())
        } else {
            None
        };
        ctx.params.heuristic.plan_rank(
            self,
            ctx.params.weight,
            &ctx.domain.predicates,
            &type_ctx,
            pg.as_deref(),
            ctx,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn new(
        steps: Option<Rc<Chain<Step>>>,
        num_steps: usize,
        links: Option<Rc<Chain<Link>>>,
        num_links: usize,
        orderings: Rc<BinaryOrderings>,
        bindings: Rc<Bindings>,
        unsafes: Option<Rc<Chain<Unsafe>>>,
        num_unsafes: usize,
        open_conds: Option<Rc<Chain<OpenCondition>>>,
        num_open_conds: usize,
    ) -> Rc<Plan> {
        Rc::new(Plan {
            steps,
            num_steps,
            links,
            num_links,
            orderings,
            bindings,
            unsafes,
            num_unsafes,
            open_conds,
            num_open_conds,
            id: std::cell::Cell::new(0),
        })
    }

    /// Returns the initial plan, or `None` if the goal is inconsistent.
    pub fn make_initial_plan(ctx: &SearchContext) -> Option<Rc<Plan>> {
        let mut open_conds: Option<Rc<Chain<OpenCondition>>> = None;
        let mut num_open_conds = 0;
        let mut new_bindings: Vec<Binding> = Vec::new();
        if !add_goal(
            ctx,
            &mut open_conds,
            &mut num_open_conds,
            &mut new_bindings,
            ctx.goal_action.precondition.clone(),
            GOAL_ID,
            false,
        ) {
            return None;
        }
        // Steps: init (id 0) and goal (GOAL_ID).
        let steps = chain::cons(
            Step {
                id: INIT_ID,
                action: ctx.init_action.clone(),
            },
            chain::cons(
                Step {
                    id: GOAL_ID,
                    action: ctx.goal_action.clone(),
                },
                None,
            ),
        );
        let orderings = Rc::new(BinaryOrderings::new());
        let bindings = Bindings::empty();
        // new_bindings from the goal (equalities/inequalities) — none for the
        // classical goal of conjoined literals, but handle generally.
        let bindings = bindings.add(&ctx.type_ctx(), &new_bindings, false)?;
        Some(Plan::new(
            steps,
            0,
            None,
            0,
            orderings,
            bindings,
            None,
            0,
            open_conds,
            num_open_conds,
        ))
    }

    fn get_flaw(&self, ctx: &SearchContext) -> Flaw {
        self.get_flaw_with(ctx, 0)
    }

    pub fn get_flaw_with(&self, ctx: &SearchContext, order_index: usize) -> Flaw {
        let order = &ctx.params.flaw_orders[order_index];
        if order.needs_planning_graph() {
            let pg = ctx.planning_graph();
            order.select(self, ctx, Some(pg.as_ref()))
        } else {
            order.select(self, ctx, None)
        }
    }

    pub fn refinements_with(
        &self,
        ctx: &SearchContext,
        order_index: usize,
        plans: &mut Vec<Rc<Plan>>,
    ) {
        let flaw = self.get_flaw_with(ctx, order_index);
        match flaw {
            Flaw::Unsafe(u) => self.handle_unsafe(ctx, plans, &u),
            Flaw::OpenCondition(oc) => self.handle_open_condition(ctx, plans, &oc),
        }
    }

    pub fn refinements(&self, ctx: &SearchContext, plans: &mut Vec<Rc<Plan>>) {
        let flaw = self.get_flaw(ctx);
        match flaw {
            Flaw::Unsafe(u) => self.handle_unsafe(ctx, plans, &u),
            Flaw::OpenCondition(oc) => self.handle_open_condition(ctx, plans, &oc),
        }
    }

    // -- Unsafe link handling -------------------------------------------------

    fn handle_unsafe(&self, ctx: &SearchContext, plans: &mut Vec<Rc<Plan>>, unsafe_: &Unsafe) {
        let link = &unsafe_.link;
        let mut unifier: Vec<Binding> = Vec::new();
        let affected = self.orderings.possibly_not_after(
            link.from_id,
            link.effect_time,
            unsafe_.step_id,
            StepTime::AtEnd,
        ) && self.orderings.possibly_not_before(
            link.to_id,
            link.condition_time.end_time(),
            unsafe_.step_id,
            StepTime::AtEnd,
        ) && self.bindings.affects_mgu(
            &ctx.type_ctx(),
            &mut unifier,
            &unsafe_.effect.literal,
            unsafe_.step_id,
            &link.condition,
            link.to_id,
        );
        if affected {
            self.separate(ctx, plans, unsafe_, &unifier);
            self.promote(ctx, plans, unsafe_);
            self.demote(ctx, plans, unsafe_);
        } else {
            // Bogus flaw: just drop it.
            plans.push(Plan::new(
                self.steps.clone(),
                self.num_steps,
                self.links.clone(),
                self.num_links,
                self.orderings.clone(),
                self.bindings.clone(),
                chain::remove(&self.unsafes, unsafe_),
                self.num_unsafes - 1,
                self.open_conds.clone(),
                self.num_open_conds,
            ));
        }
    }

    fn separate(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        unsafe_: &Unsafe,
        unifier: &[Binding],
    ) {
        // Build the disjunction of inequalities that would separate the threat.
        let mut goal = Rc::new(Formula::False);
        for subst in unifier {
            if !unsafe_.effect.parameters.contains(&subst.var) {
                let g = make_inequality(subst.var, subst.var_id, subst.term, subst.term_id);
                // For variable!=variable the C++ checks consistency; objects are
                // always consistent to add as a separation goal.
                let consistent = match g.as_ref() {
                    Formula::Inequality { .. } => self.bindings.consistent_with_inequality(
                        subst.var,
                        subst.var_id,
                        subst.term,
                        subst.term_id,
                    ),
                    _ => true,
                };
                if consistent {
                    goal = Formula::or(goal, g);
                }
            }
        }
        // Conditional effect condition (negated) — only when the effect is
        // conditional. For a universally-quantified effect, wrap the negated
        // condition in a fresh-variable `forall` so that *no* instance of the
        // effect fires.
        let effect_cond = &unsafe_.effect.condition;
        if !effect_cond.tautology() {
            let cond_goal = if unsafe_.effect.parameters.is_empty() {
                effect_cond.negation()
            } else {
                let mut subst: HashMap<Variable, Term> = HashMap::new();
                let mut params = Vec::with_capacity(unsafe_.effect.parameters.len());
                for &p in &unsafe_.effect.parameters {
                    params.push(fresh_for(ctx, &mut subst, p, unsafe_.step_id));
                }
                let body = effect_cond.substitute(&subst).negation();
                Rc::new(Formula::Forall { params, body })
            };
            goal = Formula::or(goal, cond_goal);
        }

        let mut new_open_conds = self.open_conds.clone();
        let mut new_num_open_conds = self.num_open_conds;
        let mut new_bindings: Vec<Binding> = Vec::new();
        let added = add_goal(
            ctx,
            &mut new_open_conds,
            &mut new_num_open_conds,
            &mut new_bindings,
            goal,
            unsafe_.step_id,
            false,
        );
        if added {
            if let Some(bindings) = self.bindings.add(&ctx.type_ctx(), &new_bindings, false) {
                plans.push(Plan::new(
                    self.steps.clone(),
                    self.num_steps,
                    self.links.clone(),
                    self.num_links,
                    self.orderings.clone(),
                    bindings,
                    chain::remove(&self.unsafes, unsafe_),
                    self.num_unsafes - 1,
                    new_open_conds,
                    new_num_open_conds,
                ));
            }
        }
    }

    fn demote(&self, ctx: &SearchContext, plans: &mut Vec<Rc<Plan>>, unsafe_: &Unsafe) {
        let link = &unsafe_.link;
        if self.orderings.possibly_before(
            unsafe_.step_id,
            StepTime::AtEnd,
            link.from_id,
            link.effect_time,
        ) {
            self.new_ordering(
                ctx,
                plans,
                unsafe_.step_id,
                StepTime::AtEnd,
                link.from_id,
                link.effect_time,
                unsafe_,
            );
        }
    }

    fn promote(&self, ctx: &SearchContext, plans: &mut Vec<Rc<Plan>>, unsafe_: &Unsafe) {
        let link = &unsafe_.link;
        if self.orderings.possibly_before(
            link.to_id,
            link.condition_time.end_time(),
            unsafe_.step_id,
            StepTime::AtEnd,
        ) {
            self.new_ordering(
                ctx,
                plans,
                link.to_id,
                link.condition_time.end_time(),
                unsafe_.step_id,
                StepTime::AtEnd,
                unsafe_,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn new_ordering(
        &self,
        _ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        before_id: usize,
        before_time: StepTime,
        after_id: usize,
        after_time: StepTime,
        unsafe_: &Unsafe,
    ) {
        if let Some(new_orderings) = self
            .orderings
            .refine(Ordering::new(before_id, before_time, after_id, after_time))
        {
            plans.push(Plan::new(
                self.steps.clone(),
                self.num_steps,
                self.links.clone(),
                self.num_links,
                new_orderings,
                self.bindings.clone(),
                chain::remove(&self.unsafes, unsafe_),
                self.num_unsafes - 1,
                self.open_conds.clone(),
                self.num_open_conds,
            ));
        }
    }

    // -- Open condition handling ---------------------------------------------

    fn handle_open_condition(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        open_cond: &OpenCondition,
    ) {
        if let Some(literal) = open_cond.literal() {
            if let Some(achievers) = ctx.literal_achievers(&literal) {
                self.add_step(ctx, plans, &literal, open_cond, achievers);
                self.reuse_step(ctx, plans, &literal, open_cond, achievers);
            }
            if let Literal::Negation(atom) = &literal {
                self.new_cw_link(ctx, plans, atom, open_cond);
            }
        } else if let Some((left, right)) = open_cond.inequality() {
            self.handle_inequality(ctx, plans, left, right, open_cond);
        } else if open_cond.disjunction().is_some() {
            self.handle_disjunction(ctx, plans, open_cond);
        } else {
            panic!("unknown kind of open condition");
        }
    }

    fn handle_disjunction(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        open_cond: &OpenCondition,
    ) {
        let disjuncts = open_cond.disjunction().unwrap().to_vec();
        for f in disjuncts {
            let mut new_open_conds = chain::remove(&self.open_conds, open_cond);
            let mut new_num_open_conds = self.num_open_conds - 1;
            let mut new_bindings: Vec<Binding> = Vec::new();
            let added = add_goal(
                ctx,
                &mut new_open_conds,
                &mut new_num_open_conds,
                &mut new_bindings,
                f,
                open_cond.step_id,
                false,
            );
            if added {
                if let Some(bindings) = self.bindings.add(&ctx.type_ctx(), &new_bindings, false) {
                    plans.push(Plan::new(
                        self.steps.clone(),
                        self.num_steps,
                        self.links.clone(),
                        self.num_links,
                        self.orderings.clone(),
                        bindings,
                        self.unsafes.clone(),
                        self.num_unsafes,
                        new_open_conds,
                        new_num_open_conds,
                    ));
                }
            }
        }
    }

    fn handle_inequality(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        left: Term,
        right: Term,
        open_cond: &OpenCondition,
    ) {
        let step_id = open_cond.step_id;
        // Both terms are variables (the only inequality open condition produced).
        let var1 = left.as_variable();
        let var2 = right.as_variable();
        let d1 = self.bindings.domain(&ctx.type_ctx(), var1, step_id);
        let d2 = self.bindings.domain(&ctx.type_ctx(), var2, step_id);
        let (bvar1, id1, bvar2, id2, var_domain) = if d1.len() < d2.len() {
            (var1, step_id, var2, step_id, d1)
        } else {
            (var2, step_id, var1, step_id, d2)
        };
        for name in var_domain {
            let new_bindings = vec![
                Binding::new(bvar1, id1, Term::Object(name), 0, true),
                Binding::new(bvar2, id2, Term::Object(name), 0, false),
            ];
            if let Some(bindings) = self.bindings.add(&ctx.type_ctx(), &new_bindings, false) {
                plans.push(Plan::new(
                    self.steps.clone(),
                    self.num_steps,
                    self.links.clone(),
                    self.num_links,
                    self.orderings.clone(),
                    bindings,
                    self.unsafes.clone(),
                    self.num_unsafes,
                    chain::remove(&self.open_conds, open_cond),
                    self.num_open_conds - 1,
                ));
            }
        }
    }

    fn add_step(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        literal: &Literal,
        open_cond: &OpenCondition,
        achievers: &[(Rc<StepAction>, usize)],
    ) {
        for (action, effect_idx) in achievers {
            if !action.synthetic() {
                let step = Step {
                    id: self.num_steps + 1,
                    action: action.clone(),
                };
                // Register the new step's action so binding/type lookups for its
                // variables resolve correctly.
                ctx.register_step(step.id, action);
                let effect = action.effects[*effect_idx].clone();
                self.new_link(ctx, plans, &step, &effect, literal, open_cond);
            }
        }
    }

    fn reuse_step(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        literal: &Literal,
        open_cond: &OpenCondition,
        achievers: &[(Rc<StepAction>, usize)],
    ) {
        let gt = open_cond.when.start_time();
        for sc in chain::iter(&self.steps) {
            let step = sc.clone();
            if self.orderings.possibly_before(
                step.id,
                StepTime::AtStart,
                open_cond.step_id,
                gt,
            ) {
                for (action, effect_idx) in achievers {
                    if Rc::ptr_eq(action, &step.action) {
                        let effect = action.effects[*effect_idx].clone();
                        let et = StepTime::AtEnd;
                        if self
                            .orderings
                            .possibly_before(step.id, et, open_cond.step_id, gt)
                        {
                            self.new_link(ctx, plans, &step, &effect, literal, open_cond);
                        }
                    }
                }
            }
        }
    }

    fn new_link(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        step: &Step,
        effect: &Effect,
        literal: &Literal,
        open_cond: &OpenCondition,
    ) {
        let mut mgu: Vec<Binding> = Vec::new();
        if self.bindings.unify_mgu(
            &ctx.type_ctx(),
            &mut mgu,
            &effect.literal,
            step.id,
            literal,
            open_cond.step_id,
        ) {
            self.make_link(ctx, plans, step, effect, open_cond, &mgu);
        }
    }

    /// Adds a child plan with a closed-world link for a negative literal.
    fn new_cw_link(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        negation_atom: &Atom,
        open_cond: &OpenCondition,
    ) {
        // The init action's effects are the only effects considered (closed
        // world over the initial state).
        let mut goals = Rc::new(Formula::True);
        for effect in ctx.init_action.effects.iter() {
            let mut mgu: Vec<Binding> = Vec::new();
            if self.bindings.unify_mgu(
                &ctx.type_ctx(),
                &mut mgu,
                &effect.literal,
                INIT_ID,
                &Literal::Atom(negation_atom.clone()),
                open_cond.step_id,
            ) {
                if mgu.is_empty() {
                    // Impossible to separate goal from init: no cw link.
                    return;
                }
                let mut binds = Rc::new(Formula::False);
                for subst in &mgu {
                    binds = Formula::or(
                        binds,
                        make_inequality(subst.var, subst.var_id, subst.term, subst.term_id),
                    );
                }
                goals = Formula::and(goals, binds);
            }
        }
        let mut new_open_conds = chain::remove(&self.open_conds, open_cond);
        let mut new_num_open_conds = self.num_open_conds - 1;
        let mut new_bindings: Vec<Binding> = Vec::new();
        let added = add_goal(
            ctx,
            &mut new_open_conds,
            &mut new_num_open_conds,
            &mut new_bindings,
            goals,
            INIT_ID,
            false,
        );
        if added {
            if let Some(bindings) = self.bindings.add(&ctx.type_ctx(), &new_bindings, false) {
                // New link from init (id 0).
                let link = Link {
                    from_id: INIT_ID,
                    effect_time: StepTime::AtEnd,
                    to_id: open_cond.step_id,
                    condition: open_cond.literal().unwrap(),
                    condition_time: open_cond.when,
                };
                let new_links = chain::cons(link.clone(), self.links.clone());
                let mut new_unsafes = self.unsafes.clone();
                let mut new_num_unsafes = self.num_unsafes;
                link_threats(
                    ctx,
                    &mut new_unsafes,
                    &mut new_num_unsafes,
                    &link,
                    &self.steps,
                    &self.orderings,
                    &bindings,
                );
                plans.push(Plan::new(
                    self.steps.clone(),
                    self.num_steps,
                    new_links,
                    self.num_links + 1,
                    self.orderings.clone(),
                    bindings,
                    new_unsafes,
                    new_num_unsafes,
                    new_open_conds,
                    new_num_open_conds,
                ));
            }
        }
    }

    fn make_link(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        step: &Step,
        effect: &Effect,
        open_cond: &OpenCondition,
        unifier: &[Binding],
    ) {
        // Rename universally-quantified effect parameters to fresh per-step
        // variables, so binding one instance (to establish this link) leaves the
        // original parameter free for other instances and for threat detection.
        let mut new_bindings: Vec<Binding> = Vec::with_capacity(unifier.len());
        let mut forall_subst: HashMap<Variable, Term> = HashMap::new();
        if effect.parameters.is_empty() {
            new_bindings.extend_from_slice(unifier);
        } else {
            for subst in unifier {
                if effect.parameters.contains(&subst.var) {
                    let fresh = fresh_for(ctx, &mut forall_subst, subst.var, step.id);
                    new_bindings.push(Binding::new(
                        fresh,
                        subst.var_id,
                        subst.term,
                        subst.term_id,
                        true,
                    ));
                } else {
                    new_bindings.push(subst.clone());
                }
            }
        }

        let mut new_open_conds = chain::remove(&self.open_conds, open_cond);
        let mut new_num_open_conds = self.num_open_conds - 1;

        // Conditional effect: add its condition together with the synthesised
        // link condition (with forall parameters renamed to the fresh
        // variables) as a goal.
        let mut cond_goal = Formula::and(effect.condition.clone(), effect.link_condition.clone());
        if !cond_goal.tautology() {
            if !effect.parameters.is_empty() {
                for &p in &effect.parameters {
                    fresh_for(ctx, &mut forall_subst, p, step.id);
                }
                cond_goal = cond_goal.substitute(&forall_subst);
            }
            if !add_goal(
                ctx,
                &mut new_open_conds,
                &mut new_num_open_conds,
                &mut new_bindings,
                cond_goal,
                step.id,
                false,
            ) {
                return;
            }
        }

        // New step? Add its precondition as goals.
        let is_new_step = step.id > self.num_steps;
        let mut new_steps = self.steps.clone();
        let mut new_num_steps = self.num_steps;
        if is_new_step {
            if !add_goal(
                ctx,
                &mut new_open_conds,
                &mut new_num_open_conds,
                &mut new_bindings,
                step.action.precondition.clone(),
                step.id,
                false,
            ) {
                return;
            }
            new_steps = chain::cons(step.clone(), new_steps);
            new_num_steps += 1;
        }

        let bindings = match self.bindings.add(&ctx.type_ctx(), &new_bindings, false) {
            Some(b) => b,
            None => return,
        };

        let new_orderings = match self.orderings.refine_with_step(
            Ordering::new(
                step.id,
                StepTime::AtEnd,
                open_cond.step_id,
                open_cond.when.start_time(),
            ),
            step.id,
        ) {
            Some(o) => o,
            None => return,
        };

        // Add the new link.
        let link = Link {
            from_id: step.id,
            effect_time: StepTime::AtEnd,
            to_id: open_cond.step_id,
            condition: open_cond.literal().unwrap(),
            condition_time: open_cond.when,
        };
        let new_links = chain::cons(link.clone(), self.links.clone());

        // Threats to the new link.
        let mut new_unsafes = self.unsafes.clone();
        let mut new_num_unsafes = self.num_unsafes;
        link_threats(
            ctx,
            &mut new_unsafes,
            &mut new_num_unsafes,
            &link,
            &new_steps,
            &new_orderings,
            &bindings,
        );

        // If this is a new step, find the links it threatens.
        if is_new_step {
            step_threats(
                ctx,
                &mut new_unsafes,
                &mut new_num_unsafes,
                step,
                &self.links,
                &new_orderings,
                &bindings,
            );
        }

        plans.push(Plan::new(
            new_steps,
            new_num_steps,
            new_links,
            self.num_links + 1,
            new_orderings,
            bindings,
            new_unsafes,
            new_num_unsafes,
            new_open_conds,
            new_num_open_conds,
        ));
    }
}

// -- Refinement counting (test-only) -----------------------------------------
//
// Count how many child plans a flaw would produce without allocating them.
// These feed the LR/MR/NEW/REUSE flaw orders and the `max_refinements` limits.
impl Plan {
    /// Returns the separate-refinement count for `unsafe_` (0 or 1): whether the
    /// threat's effect can be separated from the link condition by an inequality.
    pub fn separable(&self, ctx: &SearchContext, unsafe_: &Unsafe) -> i32 {
        let link = &unsafe_.link;
        let lt1 = link.effect_time;
        let lt2 = link.condition_time.end_time();
        let et = StepTime::AtEnd;
        let mut unifier: Vec<Binding> = Vec::new();
        if self
            .orderings
            .possibly_not_after(link.from_id, lt1, unsafe_.step_id, et)
            && self
                .orderings
                .possibly_not_before(link.to_id, lt2, unsafe_.step_id, et)
            && self.bindings.affects_mgu(
                &ctx.type_ctx(),
                &mut unifier,
                &unsafe_.effect.literal,
                unsafe_.step_id,
                &link.condition,
                link.to_id,
            )
        {
            self.separate_count(ctx, unsafe_, &unifier)
        } else {
            0
        }
    }

    fn separate_count(&self, ctx: &SearchContext, unsafe_: &Unsafe, unifier: &[Binding]) -> i32 {
        let mut goal = Rc::new(Formula::False);
        for subst in unifier {
            if !unsafe_.effect.parameters.contains(&subst.var) {
                let g = make_inequality(subst.var, subst.var_id, subst.term, subst.term_id);
                let consistent = match g.as_ref() {
                    Formula::Inequality { .. } => self.bindings.consistent_with_inequality(
                        subst.var,
                        subst.var_id,
                        subst.term,
                        subst.term_id,
                    ),
                    _ => true,
                };
                if consistent {
                    goal = Formula::or(goal, g);
                }
            }
        }
        let effect_cond = &unsafe_.effect.condition;
        if !effect_cond.tautology() {
            goal = Formula::or(goal, effect_cond.negation());
        }
        let mut dummy_oc: Option<Rc<Chain<OpenCondition>>> = None;
        let mut dummy_n = 0usize;
        let mut new_bindings: Vec<Binding> = Vec::new();
        let added = add_goal(
            ctx,
            &mut dummy_oc,
            &mut dummy_n,
            &mut new_bindings,
            goal,
            unsafe_.step_id,
            true,
        );
        if added && self.bindings.add(&ctx.type_ctx(), &new_bindings, true).is_some() {
            1
        } else {
            0
        }
    }

    fn demotable(&self, unsafe_: &Unsafe) -> i32 {
        let link = &unsafe_.link;
        if self.orderings.possibly_before(
            unsafe_.step_id,
            StepTime::AtEnd,
            link.from_id,
            link.effect_time,
        ) {
            1
        } else {
            0
        }
    }

    fn promotable(&self, unsafe_: &Unsafe) -> i32 {
        let link = &unsafe_.link;
        if self.orderings.possibly_before(
            link.to_id,
            link.condition_time.end_time(),
            unsafe_.step_id,
            StepTime::AtEnd,
        ) {
            1
        } else {
            0
        }
    }

    /// Counts the refinements for `unsafe_`, returning whether the count is
    /// within `limit`. The `*` parameters cache the sub-counts across calls
    /// (-1 = "not yet computed").
    #[allow(clippy::too_many_arguments)]
    pub fn unsafe_refinements(
        &self,
        ctx: &SearchContext,
        refinements: &mut i32,
        separable: &mut i32,
        promotable: &mut i32,
        demotable: &mut i32,
        unsafe_: &Unsafe,
        limit: i32,
    ) -> bool {
        if *refinements >= 0 {
            return *refinements <= limit;
        }
        let link = &unsafe_.link;
        let lt1 = link.effect_time;
        let lt2 = link.condition_time.end_time();
        let et = StepTime::AtEnd;
        let mut unifier: Vec<Binding> = Vec::new();
        let affected = self
            .orderings
            .possibly_not_after(link.from_id, lt1, unsafe_.step_id, et)
            && self
                .orderings
                .possibly_not_before(link.to_id, lt2, unsafe_.step_id, et)
            && self.bindings.affects_mgu(
                &ctx.type_ctx(),
                &mut unifier,
                &unsafe_.effect.literal,
                unsafe_.step_id,
                &link.condition,
                link.to_id,
            );
        if affected {
            let mut r = 0;
            if *separable < 0 {
                *separable = self.separate_count(ctx, unsafe_, &unifier);
            }
            r += *separable;
            if r <= limit {
                if *promotable < 0 {
                    *promotable = self.promotable(unsafe_);
                }
                r += *promotable;
                if r <= limit {
                    if *demotable < 0 {
                        *demotable = self.demotable(unsafe_);
                    }
                    *refinements = r + *demotable;
                    return *refinements <= limit;
                }
            }
            false
        } else {
            // Bogus threat: the single refinement is to drop it.
            *separable = 0;
            *promotable = 0;
            *demotable = 0;
            *refinements = 1;
            *refinements <= limit
        }
    }

    /// Whether the given open condition is threatened by some effect of an
    /// existing step (i.e. selecting it could resolve a threat).
    pub fn unsafe_open_condition(&self, ctx: &SearchContext, open_cond: &OpenCondition) -> bool {
        let literal = match open_cond.literal() {
            Some(l) => l,
            None => return false,
        };
        let gt = open_cond.when.end_time();
        for s in chain::iter(&self.steps) {
            if self.orderings.possibly_not_before(
                open_cond.step_id,
                gt,
                s.id,
                StepTime::AtStart,
            ) {
                for effect in s.action.effects.iter() {
                    let et = StepTime::AtEnd;
                    if self.orderings.possibly_not_before(open_cond.step_id, gt, s.id, et)
                        && self.bindings.affects(
                            &ctx.type_ctx(),
                            &effect.literal,
                            s.id,
                            &literal,
                            open_cond.step_id,
                        )
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Counts the refinements for the given open condition, returning whether the
    /// count is within `limit`. The `*` parameters cache the sub-counts across
    /// calls (-1 = "not yet computed").
    pub fn open_cond_refinements(
        &self,
        ctx: &SearchContext,
        refinements: &mut i32,
        addable: &mut i32,
        reusable: &mut i32,
        open_cond: &OpenCondition,
        limit: i32,
    ) -> bool {
        if *refinements >= 0 {
            return *refinements <= limit;
        }
        if let Some(literal) = open_cond.literal() {
            let mut r = 0;
            if *addable < 0 && !self.addable_steps(ctx, addable, &literal, open_cond, limit) {
                return false;
            }
            r += *addable;
            if r <= limit {
                if *reusable < 0
                    && !self.reusable_steps(ctx, reusable, &literal, open_cond, limit)
                {
                    return false;
                }
                *refinements = r + *reusable;
                return *refinements <= limit;
            }
            false
        } else {
            // Disjunction / inequality open conditions: count via the real
            // refinement methods into a throwaway list (the classical subset has
            // no quantified-effect blowup, so this is cheap).
            let mut dummy: Vec<Rc<Plan>> = Vec::new();
            if open_cond.disjunction().is_some() {
                self.handle_disjunction(ctx, &mut dummy, open_cond);
            } else if let Some((left, right)) = open_cond.inequality() {
                self.handle_inequality(ctx, &mut dummy, left, right, open_cond);
            } else {
                panic!("unknown kind of open condition");
            }
            *refinements = dummy.len() as i32;
            *refinements <= limit
        }
    }

    pub fn addable_steps(
        &self,
        ctx: &SearchContext,
        refinements: &mut i32,
        literal: &Literal,
        open_cond: &OpenCondition,
        limit: i32,
    ) -> bool {
        let mut dummy: Vec<Rc<Plan>> = Vec::new();
        if let Some(achievers) = ctx.literal_achievers(literal) {
            for (action, effect_idx) in achievers {
                if !action.synthetic() {
                    let step = Step {
                        id: self.num_steps + 1,
                        action: action.clone(),
                    };
                    ctx.register_step(step.id, action);
                    let effect = action.effects[*effect_idx].clone();
                    self.new_link(ctx, &mut dummy, &step, &effect, literal, open_cond);
                    if dummy.len() as i32 > limit {
                        return false;
                    }
                }
            }
        }
        *refinements = dummy.len() as i32;
        *refinements <= limit
    }

    pub fn reusable_steps(
        &self,
        ctx: &SearchContext,
        refinements: &mut i32,
        literal: &Literal,
        open_cond: &OpenCondition,
        limit: i32,
    ) -> bool {
        let mut dummy: Vec<Rc<Plan>> = Vec::new();
        let gt = open_cond.when.start_time();
        for step in chain::iter(&self.steps) {
            if self
                .orderings
                .possibly_before(step.id, StepTime::AtStart, open_cond.step_id, gt)
            {
                if let Some(achievers) = ctx.literal_achievers(literal) {
                    for (action, effect_idx) in achievers {
                        if Rc::ptr_eq(action, &step.action) {
                            let et = StepTime::AtEnd;
                            if self
                                .orderings
                                .possibly_before(step.id, et, open_cond.step_id, gt)
                            {
                                let effect = action.effects[*effect_idx].clone();
                                self.new_link(ctx, &mut dummy, step, &effect, literal, open_cond);
                                if dummy.len() as i32 > limit {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
        }
        if let Literal::Negation(atom) = literal {
            self.new_cw_link(ctx, &mut dummy, atom, open_cond);
            if dummy.len() as i32 > limit {
                return false;
            }
        }
        *refinements = dummy.len() as i32;
        *refinements <= limit
    }
}

impl Literal {
    /// The literal asserted by an effect.
    pub fn from_effect(effect: &Effect) -> Literal {
        effect.literal.clone()
    }
}

/// Builds a separation inequality `var@var_id != term@term_id`. The left side
/// is always a variable, so constant/constant cases cannot arise.
fn make_inequality(var: Variable, var_id: usize, term: Term, term_id: usize) -> Rc<Formula> {
    Rc::new(Formula::Inequality {
        left: Term::Variable(var),
        left_id: Some(var_id),
        right: term,
        right_id: Some(term_id),
    })
}

/// Returns the fresh per-step variable substituting the quantified effect
/// parameter `param`, allocating it on first use.
fn fresh_for(
    ctx: &SearchContext,
    forall_subst: &mut HashMap<Variable, Term>,
    param: Variable,
    step_id: usize,
) -> Variable {
    if let Some(Term::Variable(v)) = forall_subst.get(&param) {
        return *v;
    }
    let ty = ctx.var_type(param, step_id);
    let v = ctx.fresh_forall_var(step_id, ty);
    forall_subst.insert(param, Term::Variable(v));
    v
}

/// Adds a goal formula to the open-condition chain, accumulating binding
/// constraints from equality/inequality literals. Returns false if the goal is
/// a contradiction.
fn add_goal(
    ctx: &SearchContext,
    open_conds: &mut Option<Rc<Chain<OpenCondition>>>,
    num_open_conds: &mut usize,
    new_bindings: &mut Vec<Binding>,
    goal: Rc<Formula>,
    step_id: usize,
    test_only: bool,
) -> bool {
    if goal.tautology() {
        return true;
    }
    if goal.contradiction() {
        return false;
    }
    let mut goals: Vec<Rc<Formula>> = vec![goal];
    while let Some(g) = goals.pop() {
        match g.as_ref() {
            Formula::Atom(_) | Formula::Negation(_) => {
                let l = match g.as_ref() {
                    Formula::Atom(a) => Literal::Atom(a.clone()),
                    Formula::Negation(a) => Literal::Negation(a.clone()),
                    _ => unreachable!(),
                };
                if !test_only {
                    *open_conds = chain::cons(
                        OpenCondition {
                            step_id,
                            condition: l.to_formula(),
                            when: FormulaTime::AtStart,
                        },
                        open_conds.clone(),
                    );
                }
                *num_open_conds += 1;
            }
            Formula::Conjunction(cs) => {
                for c in cs {
                    goals.push(c.clone());
                }
            }
            Formula::Disjunction(_) => {
                if !test_only {
                    *open_conds = chain::cons(
                        OpenCondition {
                            step_id,
                            condition: g.clone(),
                            when: FormulaTime::AtStart,
                        },
                        open_conds.clone(),
                    );
                }
                *num_open_conds += 1;
            }
            Formula::Equality {
                left,
                left_id,
                right,
                right_id,
            }
            | Formula::Inequality {
                left,
                left_id,
                right,
                right_id,
            } => {
                let is_eq = matches!(g.as_ref(), Formula::Equality { .. });
                // Unscoped terms default to the goal's step id; separation
                // (in)equalities carry their own per-term ids.
                let lid = left_id.unwrap_or(step_id);
                let rid = right_id.unwrap_or(step_id);
                // Constant-vs-constant (in)equalities are decided immediately
                // (they simplify to TRUE/FALSE). They arise pervasively from
                // ground action preconditions such as `(not (= a table))`. A
                // violated literal makes the whole goal a contradiction.
                if let (Term::Object(a), Term::Object(b)) = (*left, *right) {
                    let holds = if is_eq { a == b } else { a != b };
                    if !holds {
                        return false;
                    }
                } else {
                    let (var, var_id, term, term_id) = binding_of(*left, lid, *right, rid);
                    new_bindings.push(Binding::new(var, var_id, term, term_id, is_eq));
                }
            }
            Formula::Exists { body, .. } => {
                goals.push(body.clone());
            }
            Formula::Forall { params, body } => {
                // Universal base: instantiate the body over all type-compatible
                // object tuples for the quantified parameters.
                let expanded = ctx.universal_base(params, body, step_id);
                goals.push(expanded);
            }
            Formula::True | Formula::False => {}
        }
    }
    true
}

fn binding_of(
    left: Term,
    left_id: usize,
    right: Term,
    right_id: usize,
) -> (Variable, usize, Term, usize) {
    match left {
        Term::Variable(v) => (v, left_id, right, right_id),
        Term::Object(_) => match right {
            Term::Variable(v) => (v, right_id, left, left_id),
            // Two objects are handled before reaching here (see `add_goal`).
            Term::Object(_) => (Variable(0), left_id, right, right_id),
        },
    }
}

#[allow(clippy::too_many_arguments)]
pub fn link_threats(
    ctx: &SearchContext,
    unsafes: &mut Option<Rc<Chain<Unsafe>>>,
    num_unsafes: &mut usize,
    link: &Link,
    steps: &Option<Rc<Chain<Step>>>,
    orderings: &BinaryOrderings,
    bindings: &Bindings,
) {
    let lt1 = link.effect_time;
    let lt2 = link.condition_time.end_time();
    for s in chain::iter(steps) {
        if orderings.possibly_not_after(link.from_id, lt1, s.id, StepTime::AtEnd)
            && orderings.possibly_not_before(link.to_id, lt2, s.id, StepTime::AtStart)
        {
            for e in s.action.effects.iter() {
                if e.link_condition.contradiction() {
                    continue;
                }
                let et = StepTime::AtEnd;
                if (s.id != link.to_id)
                    && orderings.possibly_not_after(link.from_id, lt1, s.id, et)
                    && orderings.possibly_not_before(link.to_id, lt2, s.id, et)
                {
                    let neg_condition = link.condition.negative();
                    if (neg_condition || (link.from_id != s.id))
                        && bindings.affects(
                            &ctx.type_ctx(),
                            &e.literal,
                            s.id,
                            &link.condition,
                            link.to_id,
                        ) {
                            *unsafes = chain::cons(
                                Unsafe {
                                    link: link.clone(),
                                    step_id: s.id,
                                    effect: e.clone(),
                                },
                                unsafes.clone(),
                            );
                            *num_unsafes += 1;
                        }
                }
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub fn step_threats(
    ctx: &SearchContext,
    unsafes: &mut Option<Rc<Chain<Unsafe>>>,
    num_unsafes: &mut usize,
    step: &Step,
    links: &Option<Rc<Chain<Link>>>,
    orderings: &BinaryOrderings,
    bindings: &Bindings,
) {
    for l in chain::iter(links) {
        let lt1 = l.effect_time;
        let lt2 = l.condition_time.end_time();
        if orderings.possibly_not_after(l.from_id, lt1, step.id, StepTime::AtEnd)
            && orderings.possibly_not_before(l.to_id, lt2, step.id, StepTime::AtStart)
        {
            for e in step.action.effects.iter() {
                if e.link_condition.contradiction() {
                    continue;
                }
                let et = StepTime::AtEnd;
                if (step.id != l.to_id)
                    && orderings.possibly_not_after(l.from_id, lt1, step.id, et)
                    && orderings.possibly_not_before(l.to_id, lt2, step.id, et)
                {
                    let neg_condition = l.condition.negative();
                    if (neg_condition || (l.from_id != step.id))
                        && bindings.affects(
                            &ctx.type_ctx(),
                            &e.literal,
                            step.id,
                            &l.condition,
                            l.to_id,
                        ) {
                            *unsafes = chain::cons(
                                Unsafe {
                                    link: l.clone(),
                                    step_id: step.id,
                                    effect: e.clone(),
                                },
                                unsafes.clone(),
                            );
                            *num_unsafes += 1;
                        }
                }
            }
        }
    }
}
