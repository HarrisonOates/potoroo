//! Partial plans and their refinement for the classical (non-temporal,
//! non-numeric) subset. Mutex threats are temporal-only and kept as an
//! always-empty placeholder.
//!
//! A [`Plan`] is an immutable node sharing its step/link/unsafe/open-condition
//! collections (persistent [`Chain`]s) with its parent, plus an
//! [`Rc<BinaryOrderings>`] and [`Rc<Bindings>`]. Refinement selects one flaw and
//! produces zero or more child plans. Refinement order and plan-id assignment
//! are deterministic because they determine which optimal plan A* returns.

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
    pub effects: Vec<Rc<Effect>>,
    /// Declared task cost. Synthetic init/goal actions have zero cost.
    pub cost: usize,
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
///
/// The condition is shared rather than owned because a `Link` is copied far
/// more often than it is created: every threat against it holds one, and
/// removing a resolved threat from the chain clones each `Unsafe` ahead of it.
/// Owning the literal made each of those copies allocate the condition atom's
/// term vector.
#[derive(Debug, Clone)]
pub struct Link {
    pub from_id: usize,
    pub effect_time: StepTime,
    pub to_id: usize,
    pub condition: Rc<Literal>,
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
    /// Accumulated cost of committed real steps.
    pub cost: usize,
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
    /// Set once the search has expanded this plan. Dual-queue algorithms
    /// queue a plan twice and skip the second entry by this flag, which costs
    /// nothing per plan where a set of expanded ids grew with the search.
    pub expanded: std::cell::Cell<bool>,
}

impl Plan {
    pub fn num_steps(&self) -> usize {
        self.num_steps
    }
    pub fn cost(&self) -> usize {
        self.cost
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
        let pg = if ctx.params.heuristic.needs_planning_graph() {
            Some(ctx.planning_graph())
        } else {
            None
        };
        let start = ctx.h_eval_start();
        let rank = ctx.params.heuristic.plan_rank(
            self,
            ctx.params.weight,
            &ctx.domain.predicates,
            &type_ctx,
            pg.as_deref(),
            ctx,
        );
        ctx.record_h_eval(start);
        // Most generated plans are ranked once and then parked in a queue;
        // don't let each retain its bindings lookup index.
        self.bindings.clear_index();
        rank
    }

    /// Both rank vectors — A* ([`rank`](Self::rank)) and GBFS
    /// ([`rank_gbfs`](Self::rank_gbfs)) — from a single heuristic evaluation.
    /// Used by `ALT`, which queues every child under both orderings; counts as
    /// one h evaluation since the underlying work is done once.
    pub fn rank_both(&self, ctx: &SearchContext) -> (Vec<f32>, Vec<f32>) {
        let type_ctx = ctx.type_ctx();
        let pg = if ctx.params.heuristic.needs_planning_graph() {
            Some(ctx.planning_graph())
        } else {
            None
        };
        let start = ctx.h_eval_start();
        let ranks = ctx.params.heuristic.plan_rank_both(
            self,
            ctx.params.weight,
            &ctx.domain.predicates,
            &type_ctx,
            pg.as_deref(),
            ctx,
        );
        ctx.record_h_eval(start);
        self.bindings.clear_index();
        ranks
    }

    /// Greedy-BFS rank vector: h-only (no g component), with steps and
    /// plan_id appended as tiebreakers. Used by GBFS, LGBFS, and LGBFS-D.
    pub fn rank_gbfs(&self, ctx: &SearchContext) -> Vec<f32> {
        let type_ctx = ctx.type_ctx();
        let pg = if ctx.params.heuristic.needs_planning_graph() {
            Some(ctx.planning_graph())
        } else {
            None
        };
        let start = ctx.h_eval_start();
        let rank = ctx.params.heuristic.plan_rank_gbfs(
            self,
            ctx.params.weight,
            &ctx.domain.predicates,
            &type_ctx,
            pg.as_deref(),
            ctx,
        );
        ctx.record_h_eval(start);
        // Most generated plans are ranked once and then parked in a queue;
        // don't let each retain its bindings lookup index.
        self.bindings.clear_index();
        rank
    }

    #[allow(clippy::too_many_arguments)]
    fn new(
        steps: Option<Rc<Chain<Step>>>,
        num_steps: usize,
        cost: usize,
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
            cost,
            links,
            num_links,
            orderings,
            bindings,
            unsafes,
            num_unsafes,
            open_conds,
            num_open_conds,
            id: std::cell::Cell::new(0),
            expanded: std::cell::Cell::new(false),
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
        let placement_admits = unsafe_
            .effect
            .threat_possible(&self.bindings, unsafe_.step_id)
            && self.orderings.possibly_not_after(
                link.from_id,
                link.effect_time,
                unsafe_.step_id,
                StepTime::AtEnd,
            )
            && self.orderings.possibly_not_before(
                link.to_id,
                link.condition_time.end_time(),
                unsafe_.step_id,
                StepTime::AtEnd,
            );
        let affected = placement_admits
            && self.bindings.affects_mgu(
                &ctx.type_ctx(),
                &mut unifier,
                &unsafe_.effect.literal,
                unsafe_.step_id,
                &link.condition,
                link.to_id,
            );
        // With `-p params`, a threat whose unifier the parameter domains rule out
        // is not a flaw: dropping it here saves the two or three children that
        // resolving it would have cost.
        let affected = affected
            && !(ctx.params.prune.params
                && crate::search::threat_unifier_impossible(ctx, &unifier));

        if affected {
            self.separate(ctx, plans, unsafe_, &unifier);
            self.promote(ctx, plans, unsafe_);
            self.demote(ctx, plans, unsafe_);
        } else if placement_admits
            && effect_e_deletes(ctx, &self.bindings, &unsafe_.effect, unsafe_.step_id, link)
        {
            // An e-deletion threat has no unifier to separate: the two atoms
            // are already ground and a mutex group rules them out together, so
            // the only resolvers are ordering ones. If neither is consistent
            // the conflict is unavoidable and the plan has no children, which
            // is the correct outcome.
            self.promote(ctx, plans, unsafe_);
            self.demote(ctx, plans, unsafe_);
        } else {
            // Bogus flaw: just drop it.
            plans.push(Plan::new(
                self.steps.clone(),
                self.num_steps,
                self.cost,
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

    /// The goal whose achievement separates `unsafe_`: the disjunction of the
    /// inequalities that would break the threatening unifier, plus the
    /// negation of its strengthened guard (confrontation).
    ///
    /// Shared by [`Self::separate`] and [`Self::separate_count`] so a refinement
    /// is never counted on a different formula from the one it produces. The
    /// two used to build this separately, and only `separate` wrapped a
    /// quantified effect's negated guard in a fresh-variable `forall`, so the
    /// `LR`/`MR` flaw orders ranked forall-conditional effects by a count that
    /// did not match the refinements available.
    fn separation_goal(
        &self,
        ctx: &SearchContext,
        unsafe_: &Unsafe,
        unifier: &[Binding],
    ) -> Rc<Formula> {
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
        // The strengthened guard includes cancellation by a same-step add.
        // Confrontation may therefore resolve a delete by equating its arguments
        // with that add, or by establishing the restoring add's condition.
        // For a universally-quantified effect, wrap the negated guard in a
        // fresh-variable `forall` so that no instance of the effect fires.
        let effect_cond = Formula::and(
            unsafe_.effect.condition.clone(),
            unsafe_.effect.link_condition.clone(),
        );
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
        goal
    }

    fn separate(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        unsafe_: &Unsafe,
        unifier: &[Binding],
    ) {
        let goal = self.separation_goal(ctx, unsafe_, unifier);

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
                    self.cost,
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
        if let Some(new_orderings) =
            self.orderings
                .refine(Ordering::new(before_id, before_time, after_id, after_time))
        {
            plans.push(Plan::new(
                self.steps.clone(),
                self.num_steps,
                self.cost,
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
                self.new_cw_link(ctx, plans, atom, open_cond, false);
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
                        self.cost,
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
                    self.cost,
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
        // Under `-p symmetry`, a ground step may introduce an interchangeable
        // object only if it is the first of its class the plan has not used;
        // the objects a plan uses are exactly its steps' arguments. Lifted
        // steps carry no arguments yet and pass through. See `crate::symmetry`.
        let symmetries = ctx
            .params
            .prune
            .symmetry
            .then(|| ctx.object_symmetries())
            .filter(|symmetries| !symmetries.is_empty());
        let used: Option<crate::fasthash::FastSet<crate::terms::Object>> =
            symmetries.as_ref().map(|_| {
                chain::iter(&self.steps)
                    .flat_map(|step| step.action.arguments.iter().copied())
                    .collect()
            });
        for (action, effect_idx) in achievers {
            if !action.synthetic() {
                if let (Some(symmetries), Some(used)) = (&symmetries, &used) {
                    if !symmetries.canonical_arguments(&action.arguments, |o| used.contains(&o)) {
                        ctx.pruned.set(ctx.pruned.get() + 1);
                        continue;
                    }
                }
                let step = Step {
                    id: self.num_steps + 1,
                    action: action.clone(),
                };
                // Register the new step's action so binding/type lookups for its
                // variables resolve correctly.
                ctx.register_step(step.id, action);
                let effect = action.effects[*effect_idx].clone();
                self.new_link(ctx, plans, &step, &effect, literal, open_cond, false);
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
            if self
                .orderings
                .possibly_before(step.id, StepTime::AtStart, open_cond.step_id, gt)
            {
                for (action, effect_idx) in achievers {
                    if Rc::ptr_eq(action, &step.action) {
                        let effect = action.effects[*effect_idx].clone();
                        let et = StepTime::AtEnd;
                        if self
                            .orderings
                            .possibly_before(step.id, et, open_cond.step_id, gt)
                        {
                            self.new_link(ctx, plans, &step, &effect, literal, open_cond, false);
                        }
                    }
                }
            }
        }
    }

    /// Supports `open_cond` with `effect` of `step`. Returns whether the link is
    /// feasible; see [`Plan::make_link`] for what `test_only` skips.
    #[allow(clippy::too_many_arguments)]
    fn new_link(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        step: &Step,
        effect: &Effect,
        literal: &Literal,
        open_cond: &OpenCondition,
        test_only: bool,
    ) -> bool {
        let mut mgu: Vec<Binding> = Vec::new();
        if self.bindings.unify_mgu(
            &ctx.type_ctx(),
            &mut mgu,
            &effect.literal,
            step.id,
            literal,
            open_cond.step_id,
        ) {
            self.make_link(ctx, plans, step, effect, open_cond, &mgu, test_only)
        } else {
            false
        }
    }

    /// Supports a negative literal from the closed world. Test-only calls run
    /// the same feasibility gates without constructing a child or its threats.
    fn new_cw_link(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        negation_atom: &Atom,
        open_cond: &OpenCondition,
        test_only: bool,
    ) -> bool {
        // The init action's effects are the only effects considered (closed
        // world over the initial state).
        let mut goals = Rc::new(Formula::True);
        let positive = Literal::Atom(negation_atom.clone());
        for effect in ctx.init_action.effects.iter() {
            let mut mgu: Vec<Binding> = Vec::new();
            if self.bindings.unify_mgu(
                &ctx.type_ctx(),
                &mut mgu,
                &effect.literal,
                INIT_ID,
                &positive,
                open_cond.step_id,
            ) {
                if mgu.is_empty() {
                    // Impossible to separate goal from init: no cw link.
                    return false;
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
        let mut new_open_conds = if test_only {
            None
        } else {
            chain::remove(&self.open_conds, open_cond)
        };
        let mut new_num_open_conds = self.num_open_conds - 1;
        let mut new_bindings: Vec<Binding> = Vec::new();
        let added = add_goal(
            ctx,
            &mut new_open_conds,
            &mut new_num_open_conds,
            &mut new_bindings,
            goals,
            INIT_ID,
            test_only,
        );
        if added {
            if let Some(bindings) = self.bindings.add(&ctx.type_ctx(), &new_bindings, test_only) {
                if test_only {
                    return true;
                }
                // New link from init (id 0).
                let link = Link {
                    from_id: INIT_ID,
                    effect_time: StepTime::AtEnd,
                    to_id: open_cond.step_id,
                    condition: Rc::new(open_cond.literal().unwrap()),
                    condition_time: open_cond.when,
                };
                let new_links = chain::cons(link, self.links.clone());
                let link = &new_links
                    .as_ref()
                    .expect("cons yields a non-empty chain")
                    .head;
                let mut new_unsafes = self.unsafes.clone();
                let mut new_num_unsafes = self.num_unsafes;
                link_threats(
                    ctx,
                    &mut new_unsafes,
                    &mut new_num_unsafes,
                    link,
                    &self.steps,
                    &self.orderings,
                    &bindings,
                );
                plans.push(Plan::new(
                    self.steps.clone(),
                    self.num_steps,
                    self.cost,
                    new_links,
                    self.num_links + 1,
                    self.orderings.clone(),
                    bindings,
                    new_unsafes,
                    new_num_unsafes,
                    new_open_conds,
                    new_num_open_conds,
                ));
                return true;
            }
        }
        false
    }

    /// Builds the child plan that supports `open_cond` with `effect` of `step`,
    /// pushing it onto `plans`. Returns whether the link is feasible at all.
    ///
    /// Under `test_only` every feasibility gate still runs — the unifier, the
    /// conditional-effect and precondition goals, binding consistency and the
    /// ordering cycle check — but none of the bookkeeping that only a real child
    /// needs: no chain is extended, no threats are recomputed, no `Plan` is
    /// allocated. The refinement counts behind the `LR`/`MR` flaw orders and the
    /// `max_refinements` caps used to build a whole plan and throw it away.
    /// Sharing one path keeps a count from ever disagreeing with the refinement
    /// it counts.
    #[allow(clippy::too_many_arguments)]
    fn make_link(
        &self,
        ctx: &SearchContext,
        plans: &mut Vec<Rc<Plan>>,
        step: &Step,
        effect: &Effect,
        open_cond: &OpenCondition,
        unifier: &[Binding],
        test_only: bool,
    ) -> bool {
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
                    new_bindings.push(*subst);
                }
            }
        }

        let mut new_open_conds = if test_only {
            None
        } else {
            chain::remove(&self.open_conds, open_cond)
        };
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
                test_only,
            ) {
                return false;
            }
        }

        // New step? Add its precondition as goals.
        let is_new_step = step.id > self.num_steps;
        let mut new_steps = self.steps.clone();
        let mut new_num_steps = self.num_steps;
        let mut new_cost = self.cost;
        if is_new_step {
            if !add_goal(
                ctx,
                &mut new_open_conds,
                &mut new_num_open_conds,
                &mut new_bindings,
                step.action.precondition.clone(),
                step.id,
                test_only,
            ) {
                return false;
            }
            if !test_only {
                new_steps = chain::cons(step.clone(), new_steps);
            }
            new_num_steps += 1;
            new_cost = new_cost.saturating_add(ctx.action_cost(&step.action));
        }

        let bindings = match self.bindings.add(&ctx.type_ctx(), &new_bindings, test_only) {
            Some(b) => b,
            None => return false,
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
            None => return false,
        };

        if test_only {
            // Feasible. The link, its threats and the child plan itself matter
            // only to a caller that is going to search the child.
            return true;
        }

        // Add the new link.
        let link = Link {
            from_id: step.id,
            effect_time: StepTime::AtEnd,
            to_id: open_cond.step_id,
            condition: Rc::new(open_cond.literal().unwrap()),
            condition_time: open_cond.when,
        };
        // Cons first, then borrow the link back out of the node just built.
        // Cloning it for `link_threats` instead would copy the condition atom's
        // term vector on every link the search creates.
        let new_links = chain::cons(link, self.links.clone());
        let link = &new_links
            .as_ref()
            .expect("cons yields a non-empty chain")
            .head;

        // Threats to the new link.
        let mut new_unsafes = self.unsafes.clone();
        let mut new_num_unsafes = self.num_unsafes;
        link_threats(
            ctx,
            &mut new_unsafes,
            &mut new_num_unsafes,
            link,
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
            new_cost,
            new_links,
            self.num_links + 1,
            new_orderings,
            bindings,
            new_unsafes,
            new_num_unsafes,
            new_open_conds,
            new_num_open_conds,
        ));
        true
    }
}

/// Resumable counts for one flaw in one immutable plan. Kept only during flaw
/// selection, never shared between plans or after their bindings change.
/// Construct lazily: unrestricted LIFO/FIFO criteria need no counting at all.
pub(crate) struct OpenConditionCounts<'a> {
    plan: &'a Plan,
    open: &'a OpenCondition,
    literal: Option<Literal>,
    new_cursor: usize,
    new_count: i32,
    reuse_step: Option<&'a Chain<Step>>,
    reuse_cursor: usize,
    reuse_count: i32,
    cw_done: bool,
    formula_count: Option<i32>,
    #[cfg(test)]
    tested_candidates: usize,
}

impl<'a> OpenConditionCounts<'a> {
    pub(crate) fn new(plan: &'a Plan, open: &'a OpenCondition) -> Self {
        Self {
            plan,
            open,
            literal: open.literal(),
            new_cursor: 0,
            new_count: 0,
            reuse_step: plan.steps.as_deref(),
            reuse_cursor: 0,
            reuse_count: 0,
            cw_done: false,
            formula_count: None,
            #[cfg(test)]
            tested_candidates: 0,
        }
    }

    fn new_up_to(&mut self, ctx: &SearchContext, cap: i32) -> i32 {
        let Some(literal) = &self.literal else {
            return 0;
        };
        let achievers = ctx.literal_achievers(literal).unwrap_or(&[]);
        let mut unused = Vec::new();
        while self.new_count < cap && self.new_cursor < achievers.len() {
            let (action, index) = &achievers[self.new_cursor];
            self.new_cursor += 1;
            if action.synthetic() {
                continue;
            }
            let step = Step {
                id: self.plan.num_steps + 1,
                action: action.clone(),
            };
            ctx.register_step(step.id, action);
            #[cfg(test)]
            {
                self.tested_candidates += 1;
            }
            if self.plan.new_link(
                ctx,
                &mut unused,
                &step,
                &action.effects[*index],
                literal,
                self.open,
                true,
            ) {
                self.new_count += 1;
            }
        }
        self.new_count
    }

    fn reuse_up_to(&mut self, ctx: &SearchContext, cap: i32) -> i32 {
        let Some(literal) = &self.literal else {
            return 0;
        };
        let achievers = ctx.literal_achievers(literal).unwrap_or(&[]);
        let mut unused = Vec::new();
        while self.reuse_count < cap {
            let Some(node) = self.reuse_step else {
                break;
            };
            let step = &node.head;
            if !self.plan.orderings.possibly_before(
                step.id,
                StepTime::AtEnd,
                self.open.step_id,
                self.open.when.start_time(),
            ) {
                self.reuse_step = node.tail.as_deref();
                self.reuse_cursor = 0;
                continue;
            }
            while self.reuse_cursor < achievers.len() && self.reuse_count < cap {
                let (action, index) = &achievers[self.reuse_cursor];
                self.reuse_cursor += 1;
                if !Rc::ptr_eq(action, &step.action) {
                    continue;
                }
                #[cfg(test)]
                {
                    self.tested_candidates += 1;
                }
                if self.plan.new_link(
                    ctx,
                    &mut unused,
                    step,
                    &action.effects[*index],
                    literal,
                    self.open,
                    true,
                ) {
                    self.reuse_count += 1;
                }
            }
            if self.reuse_cursor == achievers.len() {
                self.reuse_step = node.tail.as_deref();
                self.reuse_cursor = 0;
            }
        }
        if self.reuse_count < cap && !self.cw_done {
            self.cw_done = true;
            if let Literal::Negation(atom) = literal {
                #[cfg(test)]
                {
                    self.tested_candidates += 1;
                }
                if self
                    .plan
                    .new_cw_link(ctx, &mut unused, atom, self.open, true)
                {
                    self.reuse_count += 1;
                }
            }
        }
        self.reuse_count
    }

    pub(crate) fn within(&mut self, ctx: &SearchContext, limit: i32) -> bool {
        if limit < 0 {
            return false;
        }
        if self.literal.is_none() {
            return self.exact(ctx) <= limit;
        }
        let added = self.new_up_to(ctx, limit.saturating_add(1));
        added <= limit && self.reuse_up_to(ctx, (limit - added).saturating_add(1)) <= limit - added
    }

    pub(crate) fn exact(&mut self, ctx: &SearchContext) -> i32 {
        if self.literal.is_some() {
            return self
                .new_up_to(ctx, i32::MAX)
                .saturating_add(self.reuse_up_to(ctx, i32::MAX));
        }
        *self.formula_count.get_or_insert_with(|| {
            let mut plans = Vec::new();
            if self.open.disjunction().is_some() {
                self.plan.handle_disjunction(ctx, &mut plans, self.open);
            } else if let Some((left, right)) = self.open.inequality() {
                self.plan
                    .handle_inequality(ctx, &mut plans, left, right, self.open);
            } else {
                panic!("unknown kind of open condition");
            }
            i32::try_from(plans.len()).unwrap_or(i32::MAX)
        })
    }

    pub(crate) fn has_new(&mut self, ctx: &SearchContext) -> bool {
        self.new_up_to(ctx, 1) > 0
    }

    pub(crate) fn has_reuse(&mut self, ctx: &SearchContext) -> bool {
        self.reuse_up_to(ctx, 1) > 0
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
        if unsafe_
            .effect
            .threat_possible(&self.bindings, unsafe_.step_id)
            && self
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
        let goal = self.separation_goal(ctx, unsafe_, unifier);
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
        if added
            && self
                .bindings
                .add(&ctx.type_ctx(), &new_bindings, true)
                .is_some()
        {
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
        let possible = unsafe_
            .effect
            .threat_possible(&self.bindings, unsafe_.step_id);
        let affected = possible
            && self
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
        let e_deleting = possible
            && !affected
            && self
                .orderings
                .possibly_not_after(link.from_id, lt1, unsafe_.step_id, et)
            && self
                .orderings
                .possibly_not_before(link.to_id, lt2, unsafe_.step_id, et)
            && effect_e_deletes(ctx, &self.bindings, &unsafe_.effect, unsafe_.step_id, link);
        if e_deleting {
            // No separation, but promotion and demotion still apply, so the
            // flaw order must not read this as an irremediable zero.
            let mut r = 0;
            if *promotable < 0 {
                *promotable = self.promotable(unsafe_);
            }
            r += *promotable;
            if *demotable < 0 {
                *demotable = self.demotable(unsafe_);
            }
            r += *demotable;
            *refinements = r;
            return r <= limit;
        }
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
            if self
                .orderings
                .possibly_not_before(open_cond.step_id, gt, s.id, StepTime::AtStart)
            {
                for effect in s.action.effects.iter() {
                    let et = StepTime::AtEnd;
                    if self
                        .orderings
                        .possibly_not_before(open_cond.step_id, gt, s.id, et)
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
                if *reusable < 0 && !self.reusable_steps(ctx, reusable, &literal, open_cond, limit)
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
        let mut plans: Vec<Rc<Plan>> = Vec::new();
        let mut found = 0;
        if let Some(achievers) = ctx.literal_achievers(literal) {
            for (action, effect_idx) in achievers {
                if !action.synthetic() {
                    let step = Step {
                        id: self.num_steps + 1,
                        action: action.clone(),
                    };
                    ctx.register_step(step.id, action);
                    let effect = action.effects[*effect_idx].clone();
                    if self.new_link(ctx, &mut plans, &step, &effect, literal, open_cond, true) {
                        found += 1;
                        if found > limit {
                            return false;
                        }
                    }
                }
            }
        }
        *refinements = found;
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
        let mut plans: Vec<Rc<Plan>> = Vec::new();
        let mut found = 0;
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
                                if self.new_link(
                                    ctx, &mut plans, step, &effect, literal, open_cond, true,
                                ) {
                                    found += 1;
                                    if found > limit {
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        if let Literal::Negation(atom) = literal {
            // Keep this legacy counting API as a construction-based reference
            // for the feasibility-only closed-world path in OpenConditionCounts.
            self.new_cw_link(ctx, &mut plans, atom, open_cond, false);
            found += plans.len() as i32;
            if found > limit {
                return false;
            }
        }
        *refinements = found;
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
                if !test_only {
                    // Rebuild the formula directly rather than by way of a
                    // `Literal`, which cloned the atom once to be made and
                    // again in `to_formula`. The `Rc` is still fresh: open
                    // conditions are identified by pointer, so sharing `g`
                    // here would make distinct ones compare equal.
                    let condition = match g.as_ref() {
                        Formula::Atom(a) => Rc::new(Formula::Atom(a.clone())),
                        Formula::Negation(a) => Rc::new(Formula::Negation(a.clone())),
                        _ => unreachable!("matched an atom or a negation above"),
                    };
                    *open_conds = chain::cons(
                        OpenCondition {
                            step_id,
                            condition,
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
            Formula::Exists { params, body } => {
                // Each occurrence needs its own witnesses, including copies
                // made by a surrounding forall. Record even unused witnesses:
                // an empty type or inconsistent inequalities must not pass as
                // a complete plan simply because no literal mentions them.
                let mut subst = HashMap::new();
                for &param in params {
                    let ty = ctx.var_type(param, step_id);
                    if ctx.compatible_objects(ty).is_empty() {
                        return false;
                    }
                    let var = fresh_for(ctx, &mut subst, param, step_id);
                    new_bindings.push(Binding::new(
                        var,
                        step_id,
                        Term::Variable(var),
                        step_id,
                        true,
                    ));
                }
                goals.push(body.substitute(&subst));
            }
            Formula::Forall { params, body } => {
                // Universal base: instantiate the body over all type-compatible
                // object tuples for the quantified parameters.
                let expanded = ctx.universal_base(params, body, step_id);
                goals.push(expanded);
            }
            Formula::True => {}
            Formula::False => return false,
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

/// Whether an effect **e-deletes** a link's condition: it asserts something the
/// lifted mutex groups say cannot hold beside the protected fact.
///
/// Nguyen & Kambhampati (IJCAI-01, Def. 3) widen a threat from "deletes `p`" to
/// "cannot hold beside `p`". On the literal representation the widening needs
/// two things the classical test does not: mutexes, which
/// [`crate::lifted_mutex`] supplies without grounding, and both atoms resolved
/// to objects through the binding constraints. A condition still carrying a
/// variable yields `false` — no threat claimed, which is the safe direction,
/// since a threat claimed wrongly could force an ordering that loses a plan.
///
/// Only an **unconditional, unquantified positive** effect counts. A
/// conditional add may never fire, and a `forall` add is not one atom.
///
/// The precondition case of e-deletion — a step whose *precondition* is mutex
/// with the protected fact — is not a threat here, because there is no effect
/// to hang an [`Unsafe`] on. `-p cutset` catches those once the orderings put
/// the step inside the interval; see [`crate::cutset::lifted`].
pub(crate) fn effect_e_deletes(
    ctx: &SearchContext,
    bindings: &Bindings,
    effect: &Effect,
    step_id: usize,
    link: &Link,
) -> bool {
    if !ctx.params.prune.edelete || effect.conditional() || !effect.parameters.is_empty() {
        return false;
    }
    let Literal::Atom(added) = &effect.literal else {
        return false;
    };
    let Literal::Atom(protected) = link.condition.as_ref() else {
        return false;
    };
    let mutexes = ctx.lifted_mutexes();
    if mutexes.is_empty() {
        return false;
    }
    let (Some(added), Some(protected)) = (
        crate::lifted_mutex::ground_atom(bindings, added, step_id),
        crate::lifted_mutex::ground_atom(bindings, protected, link.to_id),
    ) else {
        return false;
    };
    mutexes.mutex(&added, &protected)
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
            // Nothing below depends on which effect is being examined: the step,
            // the link and `et` are all fixed across the loop. Deciding it once
            // per step keeps the ordering matrix out of the per-effect path,
            // which is where the threat scan spends its time on a long plan.
            let et = StepTime::AtEnd;
            let placement_admits_threat = (s.id != link.to_id)
                && orderings.possibly_not_after(link.from_id, lt1, s.id, et)
                && orderings.possibly_not_before(link.to_id, lt2, s.id, et)
                && (link.condition.negative() || (link.from_id != s.id));
            if !placement_admits_threat {
                continue;
            }
            for e in s.action.effects.iter() {
                // Cheapest test first: it reads the effect literal alone, and
                // rules out most effects before the second `Rc` hop into the
                // link condition and the unification below.
                let classical = e.literal.may_affect(&link.condition);
                if !classical && !effect_e_deletes(ctx, bindings, e, s.id, link) {
                    continue;
                }
                if !e.threat_possible(bindings, s.id) {
                    continue;
                }
                if !classical
                    || bindings.affects(
                        &ctx.type_ctx(),
                        &e.literal,
                        s.id,
                        &link.condition,
                        link.to_id,
                    )
                {
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
            // Loop-invariant across the step's effects; see `link_threats`.
            let et = StepTime::AtEnd;
            let placement_admits_threat = (step.id != l.to_id)
                && orderings.possibly_not_after(l.from_id, lt1, step.id, et)
                && orderings.possibly_not_before(l.to_id, lt2, step.id, et)
                && (l.condition.negative() || (l.from_id != step.id));
            if !placement_admits_threat {
                continue;
            }
            for e in step.action.effects.iter() {
                // See `link_threats`.
                let classical = e.literal.may_affect(&l.condition);
                if !classical && !effect_e_deletes(ctx, bindings, e, step.id, l) {
                    continue;
                }
                if !e.threat_possible(bindings, step.id) {
                    continue;
                }
                if !classical
                    || bindings.affects(&ctx.type_ctx(), &e.literal, step.id, &l.condition, l.to_id)
                {
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

#[cfg(test)]
mod counting_tests {
    use super::*;
    use crate::heuristics::FlawSelectionOrder;
    use crate::params::Parameters;
    use crate::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};

    #[test]
    fn zero_then_one_queries_resume_at_the_next_achiever() {
        let ParsedUnit::Domain(d) = read_pddl(
            "(define (domain counts) (:requirements :strips) (:predicates (p))
            (:action a :parameters () :precondition (and) :effect (p))
            (:action b :parameters () :precondition (and) :effect (p))
            (:action c :parameters () :precondition (and) :effect (p)))",
        )
        .unwrap() else {
            panic!()
        };
        let domain = lower_domain(&d).unwrap();
        let ParsedUnit::Problem(p) =
            read_pddl("(define (problem p) (:domain counts) (:init) (:goal (p)))").unwrap()
        else {
            panic!()
        };
        let problem = lower_problem(&p, &domain).unwrap();
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let plan = Plan::make_initial_plan(&ctx).unwrap();
        ctx.register_plan(&plan);
        let oc = chain::iter(plan.open_conds()).next().unwrap();
        let mut counts = OpenConditionCounts::new(&plan, oc);
        assert!(!counts.within(&ctx, 0));
        assert_eq!(counts.tested_candidates, 1);
        assert!(!counts.within(&ctx, 1));
        assert_eq!(counts.tested_candidates, 2);
        assert!(counts.has_new(&ctx));
        assert_eq!(counts.tested_candidates, 2);
        assert_eq!(counts.exact(&ctx), 3);
        assert_eq!(counts.tested_candidates, 3);
    }

    #[test]
    fn resumed_counts_match_actual_children_and_never_retest_candidates() {
        let ParsedUnit::Domain(d) = read_pddl(
            "(define (domain counts)
            (:requirements :adl :typing) (:types item)
            (:predicates (p ?x - item) (q ?x - item) (r ?x - item))
            (:action first :parameters (?x - item) :precondition (q ?x) :effect (p ?x))
            (:action second :parameters (?x - item) :precondition (not (r ?x)) :effect (p ?x))
            (:action many :parameters () :precondition (and)
                :effect (forall (?x - item) (when (q ?x) (p ?x)))))",
        )
        .unwrap() else {
            panic!()
        };
        let domain = lower_domain(&d).unwrap();
        let mut checked = 0;
        let mut reused = 0;
        let mut closed_world = 0;
        for goal in [
            "(and (p a) (not (r b)))",
            "(exists (?x - item) (and (p ?x) (not (q ?x))))",
            "(or (p a) (p b))",
        ] {
            let ParsedUnit::Problem(p) = read_pddl(&format!(
                "(define (problem p) (:domain counts)
                (:objects a b - item) (:init (p b) (q a)) (:goal {goal}))"
            ))
            .unwrap() else {
                panic!()
            };
            let problem = lower_problem(&p, &domain).unwrap();
            for ground_actions in [false, true] {
                let params = Parameters {
                    ground_actions,
                    flaw_orders: vec![FlawSelectionOrder::parse("ZLIFO").unwrap()],
                    ..Parameters::default()
                };
                let ctx = SearchContext::new(&domain, &problem, &params);
                let mut queue =
                    std::collections::VecDeque::from([Plan::make_initial_plan(&ctx).unwrap()]);
                for _ in 0..24 {
                    let Some(plan) = queue.pop_front() else {
                        break;
                    };
                    ctx.register_plan(&plan);
                    for oc in chain::iter(plan.open_conds()) {
                        let mut counts = OpenConditionCounts::new(&plan, oc);
                        for limit in [0, 0, 1, 0, 2, 1, i32::MAX, 0] {
                            let before = counts.tested_candidates;
                            let within = counts.within(&ctx, limit);
                            let mut exact = -1;
                            let (mut addable, mut reusable) = (-1, -1);
                            let reference = plan.open_cond_refinements(
                                &ctx,
                                &mut exact,
                                &mut addable,
                                &mut reusable,
                                oc,
                                limit,
                            );
                            assert_eq!(within, reference);
                            let after = counts.tested_candidates;
                            assert!(after >= before);
                            assert_eq!(counts.within(&ctx, limit), within);
                            assert_eq!(
                                counts.tested_candidates, after,
                                "an identical query rescanned candidates"
                            );
                        }
                        let count = counts.exact(&ctx);
                        let after = counts.tested_candidates;
                        let mut children = Vec::new();
                        plan.handle_open_condition(&ctx, &mut children, oc);
                        assert_eq!(count as usize, children.len());
                        counts.has_new(&ctx);
                        counts.has_reuse(&ctx);
                        assert_eq!(
                            counts.tested_candidates, after,
                            "exact count did not finish the scans"
                        );
                        // NEW/REUSE can precede threshold and ranking criteria.
                        let mut availability = OpenConditionCounts::new(&plan, oc);
                        assert_eq!(availability.has_reuse(&ctx), counts.reuse_count > 0);
                        assert_eq!(availability.has_new(&ctx), counts.new_count > 0);
                        assert_eq!(availability.within(&ctx, 1), count <= 1);
                        assert_eq!(availability.exact(&ctx), count);
                        reused += usize::from(counts.reuse_count > 0);
                        closed_world += usize::from(
                            matches!(counts.literal, Some(Literal::Negation(_))) && counts.cw_done,
                        );
                        checked += 1;
                    }
                    if !plan.complete() {
                        let mut children = Vec::new();
                        plan.refinements(&ctx, &mut children);
                        queue.extend(children);
                    }
                }
            }
        }
        assert!(
            checked > 20 && reused > 0 && closed_world > 0,
            "insufficient coverage: {checked} flaws, {reused} reuse cases, {closed_world} closed-world cases"
        );
    }
}
