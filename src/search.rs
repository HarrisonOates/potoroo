//! The A* search loop and the search context (problem, parameters, achiever
//! maps, and per-step variable-type registry) shared across all search nodes.

use std::cell::{Cell, RefCell};
use std::cmp::Ordering as CmpOrdering;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::time::{Duration, Instant};

use crate::fasthash::FastMap;
use std::rc::Rc;

use crate::action::ActionSchema;
use crate::bindings::{Binding, Bindings, StepVarTypes, TypeContext};
use crate::chain;
use crate::domain::Domain;
use crate::effect::Effect;
use crate::formula::{Atom, Formula, Literal};
use crate::instantiate::{instantiate_effect, instantiate_formula, precondition_consistent};
use crate::params::{Parameters, SearchAlgorithm};
use crate::plan::{Plan, StepAction, GOAL_ID, INIT_ID};
use crate::problem::Metric;
use crate::problem::Problem;
use crate::terms::{Object, Term, Variable};
use crate::types::{Type, OBJECT};

/// Holds the immutable context threaded through search: the problem/domain,
/// parameters, the synthetic init/goal actions, the achiever maps, and the
/// per-step variable-type registry. Replaces the C++ globals in `plans.cc`.
/// An achiever index: for each key, the actions that achieve it paired with the
/// index of the achieving effect. Keyed by predicate id for the lifted indexes
/// and by ground atom for the exact ones.
type AchieverIndex<K> = FastMap<K, Vec<(Rc<StepAction>, usize)>>;

pub struct SearchContext<'a> {
    pub domain: &'a Domain,
    pub problem: &'a Problem,
    pub params: &'a Parameters,
    pub init_action: Rc<StepAction>,
    pub goal_action: Rc<StepAction>,
    /// Achievers of positive literals, keyed by predicate id. Each entry is the
    /// achieving action plus the index of the achieving effect.
    achieves_pred: AchieverIndex<u32>,
    /// Achievers of negative literals, keyed by predicate id.
    achieves_neg_pred: AchieverIndex<u32>,
    /// Exact achiever index for a fully ground task: the same entries as the
    /// two predicate maps, keyed by the effect literal's atom rather than by its
    /// predicate alone. `None` when any effect literal carries a variable (every
    /// lifted run, and any forall effect), in which case the predicate maps are
    /// the only index. See [`SearchContext::literal_achievers`].
    achieves_atom: Option<AchieverIndex<Atom>>,
    /// Exact achiever index for negative literals; see `achieves_atom`.
    achieves_neg_atom: Option<AchieverIndex<Atom>>,
    /// Step-id -> action variable-type registry; populated as steps are created.
    step_var_types: RefCell<FastMap<usize, Rc<StepAction>>>,
    /// The relaxed planning graph, built lazily on first use when the configured
    /// heuristic needs it.
    planning_graph: RefCell<Option<Rc<crate::planning_graph::PlanningGraph>>>,
    /// Types of fresh variables allocated per step for universally-quantified
    /// effect instances (the renamed forall parameters in `make_link`/`separate`).
    /// Keyed by step id; each fresh variable has index `action.var_types.len() +
    /// position`.
    fresh_vars: RefCell<FastMap<usize, Vec<Type>>>,
    /// The constant base of the SAS⁺ causal-link compilation (the ground original
    /// actions + their facts), built lazily on first use. Reused across every
    /// search node so the `COMPILE` heuristic only re-grounds the per-node delta
    /// (committed steps + indicators + guards). See `crate::compile`.
    compile_base: RefCell<Option<Rc<crate::compile::BaseGroundTask>>>,
    /// The translated finite-domain task, for the SAS+ LP heuristic. Built once
    /// per search: translating runs Fast Downward, which costs far more than a
    /// node. The inner `None` records that translation failed, so it is not
    /// retried at every node.
    fdr_task: RefCell<Option<Option<Rc<crate::fdr::Task>>>>,
    /// The problem-constant Sample-FF model (interned ground facts, delete-relaxed
    /// ground actions, cached initial-state fixpoint), built lazily on first use
    /// and reused across every search node. See `crate::sample_ff`.
    sample_ff_model: RefCell<Option<Rc<crate::sample_ff::SampleFfModel>>>,
    /// Every ground cost-function value the problem's `:init` assigns, keyed by
    /// the function and its arguments. Lets a ground instance be priced exactly
    /// where the schema only carries a lower bound over instances.
    pub(crate) cost_values: HashMap<(crate::functions::Function, Vec<Object>), f64>,
    /// Number of heuristic (rank) evaluations performed during search.
    pub(crate) h_evals: Cell<usize>,
    /// Total wall time spent in heuristic (rank) evaluations.
    pub(crate) h_eval_nanos: Cell<u128>,
    /// Children discarded by relaxed-reachability pruning at generation time.
    pub(crate) pruned: Cell<usize>,
    /// Operator parameter domains, built on first use when `-p params` is on.
    /// See [`crate::param_domains`].
    param_domains: RefCell<Option<Rc<crate::param_domains::ParameterDomains>>>,
    /// The domain's operator graph and its SCCs, built on first use when
    /// `-p recursion` is on. See [`crate::opgraph`].
    operator_graph: RefCell<Option<Rc<crate::opgraph::OperatorGraph>>>,
    /// The task's lifted landmarks, extracted on first use by `-h LM`.
    landmarks: RefCell<Option<Rc<crate::landmarks::LiftedLandmarks>>>,
    /// Landmarks extracted with the FAM cuts as well, cached apart because the
    /// two extractions produce different landmark sets.
    landmarks_fam: RefCell<Option<Rc<crate::landmarks::LiftedLandmarks>>>,
    /// Lifted mutex groups, synthesised on first use when `-p cutset` is on.
    /// See [`crate::lifted_mutex`].
    lifted_mutexes: RefCell<Option<Rc<crate::lifted_mutex::LiftedMutexes>>>,
}

impl<'a> StepVarTypes for SearchContext<'a> {
    fn var_type(&self, var: Variable, step_id: usize) -> Type {
        let map = self.step_var_types.borrow();
        if let Some(action) = map.get(&step_id) {
            let idx = var.0 as usize;
            let base = action.var_types.len();
            if idx < base {
                return action.var_types[idx];
            }
            // A fresh forall-instance variable (index past the action's params).
            if let Some(types) = self.fresh_vars.borrow().get(&step_id) {
                if let Some(ty) = types.get(idx - base) {
                    return *ty;
                }
            }
        }
        OBJECT
    }
}

impl<'a> SearchContext<'a> {
    pub fn new(domain: &'a Domain, problem: &'a Problem, params: &'a Parameters) -> Self {
        // Goal action.
        let goal_action = Rc::new(StepAction {
            name: String::new(),
            parameters: Vec::new(),
            arguments: Vec::new(),
            precondition: problem.goal.clone(),
            effects: Vec::new(),
            cost: 0,
            var_types: problem.goal_var_types.clone(),
        });
        // Init action: effects = init atoms (positive), in declaration order.
        let init_effects: Vec<Rc<Effect>> = problem
            .init_order
            .iter()
            .map(|a| Rc::new(Effect::new(Literal::Atom(a.clone()))))
            .collect();
        let init_action = Rc::new(StepAction {
            name: "<init 0>".to_string(),
            parameters: Vec::new(),
            arguments: Vec::new(),
            precondition: Rc::new(Formula::True),
            effects: init_effects,
            cost: 0,
            var_types: Vec::new(),
        });

        let mut ctx = SearchContext {
            domain,
            problem,
            params,
            init_action: init_action.clone(),
            goal_action: goal_action.clone(),
            achieves_pred: FastMap::default(),
            achieves_neg_pred: FastMap::default(),
            achieves_atom: None,
            achieves_neg_atom: None,
            step_var_types: RefCell::new(FastMap::default()),
            planning_graph: RefCell::new(None),
            fresh_vars: RefCell::new(FastMap::default()),
            compile_base: RefCell::new(None),
            fdr_task: RefCell::new(None),
            sample_ff_model: RefCell::new(None),
            cost_values: crate::parser::lower::cost_function_values(problem),
            h_evals: Cell::new(0),
            h_eval_nanos: Cell::new(0),
            pruned: Cell::new(0),
            param_domains: RefCell::new(None),
            operator_graph: RefCell::new(None),
            lifted_mutexes: RefCell::new(None),
            landmarks: RefCell::new(None),
            landmarks_fam: RefCell::new(None),
        };
        ctx.step_var_types
            .borrow_mut()
            .insert(GOAL_ID, goal_action.clone());
        ctx.step_var_types
            .borrow_mut()
            .insert(INIT_ID, init_action.clone());
        ctx.build_achievers();
        ctx
    }

    /// Builds the predicate -> achievers maps. In ground mode, uses FD's
    /// reachability-based grounder when available, falling back to naive
    /// Cartesian instantiation otherwise.
    fn build_achievers(&mut self) {
        let mut actions: Vec<Rc<StepAction>> = if self.params.ground_actions {
            self.fd_reachable_ground_actions()
        } else {
            self.domain
                .actions
                .iter()
                .map(|a| Rc::new(schema_to_action(a)))
                .collect()
        };
        // With `-p params`, drop action instances whose arguments lie outside
        // their parameter domains before they ever become achievers. In ground
        // mode this removes them from every open condition's candidate set at
        // once, for a single up-front cost; in lifted mode it removes whole
        // schemas that have no viable instance at all.
        if self.params.prune.params {
            let domains = self.param_domains();
            actions.retain(|action| {
                if action.arguments.is_empty() {
                    domains.schema_viable(&action.name)
                } else {
                    domains.permits_arguments(&action.name, &action.arguments)
                }
            });
        }
        for action in &actions {
            for (idx, effect) in action.effects.iter().enumerate() {
                let pred = effect.literal.atom().predicate.0;
                let map = if effect.literal.negative() {
                    &mut self.achieves_neg_pred
                } else {
                    &mut self.achieves_pred
                };
                map.entry(pred).or_default().push((action.clone(), idx));
            }
        }
        // Init action achieves positive literals.
        for (idx, effect) in self.init_action.effects.iter().enumerate() {
            let pred = effect.literal.atom().predicate.0;
            self.achieves_pred
                .entry(pred)
                .or_default()
                .push((self.init_action.clone(), idx));
        }
        self.build_atom_achievers();
    }

    /// Builds the exact, atom-keyed achiever index from the predicate-keyed
    /// ones. A ground open condition otherwise scans every effect sharing its
    /// predicate and unifies each: on gripper-20 that is every `drop` in the
    /// task for one `(at ball_i room_j)`, of which two can match.
    ///
    /// Only a wholly ground task can be indexed this way -- one variable in one
    /// effect literal (a forall parameter, or any lifted run) makes the atom an
    /// unsound key, because that effect can achieve atoms it is not equal to.
    /// Giving up on the whole index then, rather than per predicate, keeps the
    /// lookup a single branch on the hot path.
    fn build_atom_achievers(&mut self) {
        let ground = |m: &FastMap<u32, Vec<(Rc<StepAction>, usize)>>| {
            m.values().flatten().all(|(action, idx)| {
                let effect = &action.effects[*idx];
                effect.parameters.is_empty() && effect.literal.atom().ground()
            })
        };
        if !ground(&self.achieves_pred) || !ground(&self.achieves_neg_pred) {
            return;
        }
        // Preserve each predicate bucket's order within its atom buckets: the
        // achiever order decides the order refinements are generated in, and
        // that decides which optimal plan A* returns.
        let index = |m: &FastMap<u32, Vec<(Rc<StepAction>, usize)>>| {
            let mut out: FastMap<Atom, Vec<(Rc<StepAction>, usize)>> = FastMap::default();
            for entry in m.values().flatten() {
                let atom = entry.1;
                let key = entry.0.effects[atom].literal.atom().clone();
                out.entry(key).or_default().push(entry.clone());
            }
            out
        };
        self.achieves_atom = Some(index(&self.achieves_pred));
        self.achieves_neg_atom = Some(index(&self.achieves_neg_pred));
    }

    /// Naively instantiates every schema over all type-compatible argument
    /// tuples (no planning graph). Used in ground mode and by the SAS⁺
    /// compilation grounder (`crate::compile::ground_task`).
    pub(crate) fn ground_actions(&self) -> Vec<Rc<StepAction>> {
        let mut out = Vec::new();
        for schema in &self.domain.actions {
            let domains: Vec<Vec<Object>> = schema
                .parameters
                .iter()
                .map(|&p| {
                    let ty = schema.var_types[p.0 as usize];
                    self.compatible_objects(ty)
                })
                .collect();
            let mut tuple: Vec<Object> = Vec::with_capacity(schema.parameters.len());
            self.instantiate(schema, &domains, 0, &mut tuple, &mut out);
        }
        out
    }

    fn instantiate(
        &self,
        schema: &ActionSchema,
        domains: &[Vec<Object>],
        depth: usize,
        tuple: &mut Vec<Object>,
        out: &mut Vec<Rc<StepAction>>,
    ) {
        if depth == schema.parameters.len() {
            if let Some(a) = self.instantiate_tuple(schema, tuple) {
                out.push(a);
            }
            return;
        }
        for &obj in &domains[depth] {
            tuple.push(obj);
            self.instantiate(schema, domains, depth + 1, tuple, out);
            tuple.pop();
        }
    }

    /// Instantiates a schema with a concrete object tuple, returning the ground
    /// action, or `None` if its static (in)equality preconditions are violated.
    pub(crate) fn instantiate_tuple(
        &self,
        schema: &ActionSchema,
        tuple: &[Object],
    ) -> Option<Rc<StepAction>> {
        let mut subst: Vec<Option<Object>> = vec![None; schema.var_types.len()];
        for (i, &p) in schema.parameters.iter().enumerate() {
            subst[p.0 as usize] = Some(tuple[i]);
        }
        if !precondition_consistent(&schema.precondition, &subst) {
            return None;
        }
        let precondition = instantiate_formula(&schema.precondition, &subst);
        let effects: Vec<Rc<Effect>> = schema
            .effects
            .iter()
            .map(|e| Rc::new(instantiate_effect(e, &subst)))
            .collect();
        Some(Rc::new(StepAction {
            name: schema.name.clone(),
            parameters: Vec::new(),
            arguments: tuple.to_vec(),
            precondition,
            effects,
            // A ground instance knows its own cost arguments, so a
            // parameterised cost resolves exactly here rather than staying at
            // the schema's minimum-over-instances bound.
            cost: schema
                .instance_cost(tuple, &self.cost_values)
                .unwrap_or(schema.cost),
            var_types: Vec::new(),
        }))
    }

    /// The set of **reachable** ground actions, grounded by Fast Downward's
    /// (heavily optimised) translator rather than naive Cartesian instantiation.
    /// We translate the original problem once, read the reachable ground operator
    /// names from the SAS⁺ output, and re-instantiate them from our schemas. Used
    /// to build the compact base of the `COMPILE` heuristic's SAS⁺ task; falls
    /// back to `ground_actions` if FD is unavailable or the output is unusable.
    pub(crate) fn fd_reachable_ground_actions(&self) -> Vec<Rc<StepAction>> {
        match self.try_fd_reachable_ground_actions() {
            Some(actions) if !actions.is_empty() => actions,
            _ => self.ground_actions(),
        }
    }

    fn try_fd_reachable_ground_actions(&self) -> Option<Vec<Rc<StepAction>>> {
        let (domain_pddl, problem_pddl) =
            crate::pddl_emit::emit_original(self.domain, self.problem);
        let sas = crate::external::run_fd_translate(&domain_pddl, &problem_pddl).ok()?;

        // Build case-insensitive name lookups for schemas and objects.
        let schema_by_name: HashMap<String, &ActionSchema> = self
            .domain
            .actions
            .iter()
            .map(|a| (a.name.to_ascii_lowercase(), a))
            .collect();
        let mut object_by_name: HashMap<String, Object> = HashMap::new();
        for (o, _) in self.domain.constants.owned_objects() {
            let n = self
                .domain
                .constants
                .object_name(None, o)
                .to_ascii_lowercase();
            object_by_name.insert(n, o);
        }
        for (o, _) in self.problem.objects.owned_objects() {
            let n = self
                .problem
                .objects
                .object_name(Some(&self.domain.constants), o)
                .to_ascii_lowercase();
            object_by_name.insert(n, o);
        }

        // Parse operator names (the line following each `begin_operator`).
        let mut out = Vec::new();
        let mut lines = sas.lines();
        while let Some(line) = lines.next() {
            if line.trim() != "begin_operator" {
                continue;
            }
            let Some(name) = lines.next() else { break };
            let mut toks = name.split_whitespace();
            let Some(action) = toks.next() else { continue };
            let Some(schema) = schema_by_name.get(action) else {
                continue;
            };
            let args: Option<Vec<Object>> = toks.map(|t| object_by_name.get(t).copied()).collect();
            let Some(args) = args else { continue };
            if args.len() != schema.parameters.len() {
                continue;
            }
            if let Some(a) = self.instantiate_tuple(schema, &args) {
                out.push(a);
            }
        }
        Some(out)
    }

    /// Objects compatible with a type (objects + domain constants).
    pub fn compatible_objects(&self, ty: Type) -> Vec<Object> {
        let mut result = Vec::new();
        for (o, oty) in self.domain.constants.owned_objects() {
            if self.domain.types.subtype(oty, ty) {
                result.push(o);
            }
        }
        for (o, oty) in self.problem.objects.owned_objects() {
            if self.domain.types.subtype(oty, ty) {
                result.push(o);
            }
        }
        result
    }

    pub fn planning_graph(&self) -> Rc<crate::planning_graph::PlanningGraph> {
        if self.planning_graph.borrow().is_none() {
            let pg = crate::planning_graph::PlanningGraph::build_from_schemas(
                &self.domain.predicates,
                &self.init_action,
                &self.domain.actions,
                |ty| self.compatible_objects(ty),
                self.params.action_cost,
                self.problem.metric == Some(Metric::MinimizeTotalCost),
            );
            *self.planning_graph.borrow_mut() = Some(Rc::new(pg));
        }
        self.planning_graph.borrow().clone().unwrap()
    }

    /// Operator parameter domains, computed once per search.
    pub fn param_domains(&self) -> Rc<crate::param_domains::ParameterDomains> {
        if self.param_domains.borrow().is_none() {
            let domains =
                crate::param_domains::ParameterDomains::compute(self.domain, self.problem);
            *self.param_domains.borrow_mut() = Some(Rc::new(domains));
        }
        self.param_domains.borrow().clone().unwrap()
    }

    /// The task's lifted landmarks, extracted once per search. `fam` also cuts
    /// the mutex groups' transition graphs, which needs those groups and so
    /// costs a synthesis on top of the backchaining.
    pub fn landmarks(&self, fam: bool) -> Rc<crate::landmarks::LiftedLandmarks> {
        let cache = if fam {
            &self.landmarks_fam
        } else {
            &self.landmarks
        };
        if cache.borrow().is_none() {
            let extracted = if fam {
                let mutexes = self.lifted_mutexes();
                crate::landmarks::LiftedLandmarks::extract_with_mutexes(
                    self.domain,
                    self.problem,
                    &mutexes,
                )
            } else {
                crate::landmarks::LiftedLandmarks::extract(self.domain, self.problem)
            };
            *cache.borrow_mut() = Some(Rc::new(extracted));
        }
        cache.borrow().clone().unwrap()
    }

    /// The domain's lifted mutex groups, synthesised once per search.
    pub fn lifted_mutexes(&self) -> Rc<crate::lifted_mutex::LiftedMutexes> {
        if self.lifted_mutexes.borrow().is_none() {
            let mutexes = crate::lifted_mutex::LiftedMutexes::synthesise(self.domain, self.problem);
            *self.lifted_mutexes.borrow_mut() = Some(Rc::new(mutexes));
        }
        self.lifted_mutexes.borrow().clone().unwrap()
    }

    /// The domain's operator graph, computed once per search.
    pub fn operator_graph(&self) -> Rc<crate::opgraph::OperatorGraph> {
        if self.operator_graph.borrow().is_none() {
            let graph = crate::opgraph::OperatorGraph::build(self.domain);
            *self.operator_graph.borrow_mut() = Some(Rc::new(graph));
        }
        self.operator_graph.borrow().clone().unwrap()
    }

    /// Effective cost of inserting an action under the selected cost model.
    pub fn action_cost(&self, action: &StepAction) -> usize {
        let declared = if self.problem.metric == Some(Metric::MinimizeTotalCost) {
            action.cost
        } else {
            1
        };
        self.params.action_cost.resolve(declared)
    }

    /// Returns the constant base of the SAS⁺ causal-link compilation (ground
    /// original actions + their facts), building it on first use. Shared across
    /// all search nodes by the `COMPILE` heuristic's fast path.
    pub fn compile_base(&self) -> Rc<crate::compile::BaseGroundTask> {
        if self.compile_base.borrow().is_none() {
            let base = crate::compile::build_base(self);
            *self.compile_base.borrow_mut() = Some(Rc::new(base));
        }
        self.compile_base.borrow().clone().unwrap()
    }

    /// The translated finite-domain task, or `None` if translation failed.
    /// Translation runs Fast Downward, so it happens once per search.
    pub fn fdr_task(&self) -> Option<Rc<crate::fdr::Task>> {
        if self.fdr_task.borrow().is_none() {
            let translated = crate::fdr_pocl::translate(self).ok().map(Rc::new);
            *self.fdr_task.borrow_mut() = Some(translated);
        }
        self.fdr_task.borrow().clone().flatten()
    }

    /// Returns the problem-constant Sample-FF model (interned facts, delete-relaxed
    /// ground actions, cached initial fixpoint), building it on first use. Shared
    /// across all search nodes by the `SAMPLE_FF` heuristic.
    pub fn sample_ff_model(&self) -> Rc<crate::sample_ff::SampleFfModel> {
        if self.sample_ff_model.borrow().is_none() {
            let model = crate::sample_ff::SampleFfModel::build(self);
            *self.sample_ff_model.borrow_mut() = Some(Rc::new(model));
        }
        self.sample_ff_model.borrow().clone().unwrap()
    }

    pub fn literal_achievers(&self, literal: &Literal) -> Option<&[(Rc<StepAction>, usize)]> {
        let atom = literal.atom();
        // A ground condition against a ground task: answer exactly. The
        // achievers dropped here are precisely those `new_link` would have
        // unified against and rejected, so the refinements produced -- and
        // their order -- are unchanged.
        let exact = if literal.negative() {
            &self.achieves_neg_atom
        } else {
            &self.achieves_atom
        };
        if let Some(map) = exact {
            if atom.ground() {
                return map.get(atom).map(|v| v.as_slice());
            }
        }
        let pred = atom.predicate.0;
        let map = if literal.negative() {
            &self.achieves_neg_pred
        } else {
            &self.achieves_pred
        };
        map.get(&pred).map(|v| v.as_slice())
    }

    /// Builds a [`TypeContext`] over the current tables.
    pub fn type_ctx(&self) -> TypeContext<'_> {
        TypeContext {
            types: &self.domain.types,
            objects: &self.problem.objects,
            constants: &self.domain.constants,
            step_vars: self,
        }
    }

    /// Reads the clock, but only when `h_eval_ms` will be reported. See
    /// [`Parameters::time_h_evals`].
    #[inline]
    pub(crate) fn h_eval_start(&self) -> Option<Instant> {
        self.params.time_h_evals.then(Instant::now)
    }

    /// Accumulates one heuristic (rank) evaluation into the search stats,
    /// adding its duration when [`Self::h_eval_start`] took a reading.
    #[inline]
    pub(crate) fn record_h_eval(&self, started: Option<Instant>) {
        self.h_evals.set(self.h_evals.get() + 1);
        if let Some(started) = started {
            self.h_eval_nanos
                .set(self.h_eval_nanos.get() + started.elapsed().as_nanos());
        }
    }

    /// Registers a step's action for variable-type lookups.
    /// The action currently registered for a step id, if any. Step ids repeat
    /// across sibling plans, so this answers for the plan most recently
    /// registered — which is the one being refined.
    pub fn step_action(&self, step_id: usize) -> Option<Rc<StepAction>> {
        self.step_var_types.borrow().get(&step_id).cloned()
    }

    pub fn register_step(&self, step_id: usize, action: &Rc<StepAction>) {
        self.step_var_types
            .borrow_mut()
            .insert(step_id, action.clone());
    }

    /// Re-points the step-action map at `plan`'s own newest step.
    ///
    /// `step_var_types` is keyed by step id alone, but ids repeat across a
    /// parent's sibling refinements, so without this the last sibling
    /// registered would decide the parameter types used to rank all of them.
    /// A refinement adds at most one step, consed onto the chain's head.
    pub fn register_newest_step(&self, plan: &Plan, parent_num_steps: usize) {
        if plan.num_steps > parent_num_steps {
            if let Some(chain) = &plan.steps {
                self.register_step(chain.head.id, &chain.head.action);
            }
        }
    }

    /// Allocates a fresh variable scoped to `step_id` with type `ty`, used for a
    /// universally-quantified effect instance (the renamed forall parameter).
    /// Its index lies past the step's action parameters; [`var_type`] resolves it
    /// via `fresh_vars`.
    pub fn fresh_forall_var(&self, step_id: usize, ty: Type) -> Variable {
        let base = self
            .step_var_types
            .borrow()
            .get(&step_id)
            .map(|a| a.var_types.len())
            .unwrap_or(0);
        let mut fresh = self.fresh_vars.borrow_mut();
        let v = fresh.entry(step_id).or_default();
        let idx = base + v.len();
        v.push(ty);
        Variable(idx as u32)
    }

    /// Universal-base expansion of a forall body: conjoins the body over the
    /// cartesian product of all type-compatible objects for each parameter.
    pub fn universal_base(
        &self,
        params: &[Variable],
        body: &Rc<Formula>,
        step_id: usize,
    ) -> Rc<Formula> {
        let tctx = self.type_ctx();
        let obj_lists: Vec<Vec<Object>> = params
            .iter()
            .map(|&p| tctx.compatible_objects(self.var_type(p, step_id)))
            .collect();
        // Cartesian product of object choices for the parameters.
        let mut combos: Vec<HashMap<Variable, Term>> = vec![HashMap::new()];
        for (i, &p) in params.iter().enumerate() {
            let mut next = Vec::new();
            for combo in &combos {
                for &o in &obj_lists[i] {
                    let mut c = combo.clone();
                    c.insert(p, Term::Object(o));
                    next.push(c);
                }
            }
            combos = next;
        }
        let mut result = Rc::new(Formula::True);
        for combo in &combos {
            result = Formula::and(result, body.substitute(combo));
        }
        result
    }
}

/// Converts a schema into a `StepAction` (lifted). Registers nothing; the schema
/// id maps the step to its var_types via the registry.
fn schema_to_action(schema: &ActionSchema) -> StepAction {
    StepAction {
        name: schema.name.clone(),
        parameters: schema.parameters.clone(),
        arguments: Vec::new(),
        precondition: schema.precondition.clone(),
        effects: schema.effects.clone(),
        cost: schema.cost,
        var_types: schema.var_types.clone(),
    }
}

/// A plan wrapped for the priority queue. Lower rank is better; ties broken by
/// subsequent rank elements. Ordered so the best plan is greatest (Rust's
/// `BinaryHeap` is a max-heap; the best plan must sort largest to be popped).
struct QueuedPlan {
    plan: Rc<Plan>,
    rank: Vec<f32>,
    /// When true the rank is a cheap proxy (parent's h + structural tiebreakers)
    /// and the real h must be computed when this plan is popped. Used by
    /// `LazyGbfs` and `LazyGbfsDual`.
    is_lazy: bool,
}

impl PartialEq for QueuedPlan {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == CmpOrdering::Equal
    }
}
impl Eq for QueuedPlan {}
impl PartialOrd for QueuedPlan {
    fn partial_cmp(&self, other: &Self) -> Option<CmpOrdering> {
        Some(self.cmp(other))
    }
}
impl Ord for QueuedPlan {
    fn cmp(&self, other: &Self) -> CmpOrdering {
        // Greater = better, so the heap pops the best plan. Smaller rank is better.
        let n = self.rank.len().max(other.rank.len());
        for i in 0..n {
            let a = self.rank.get(i).copied().unwrap_or(0.0);
            let b = other.rank.get(i).copied().unwrap_or(0.0);
            if a < b {
                return CmpOrdering::Greater; // self better
            } else if a > b {
                return CmpOrdering::Less;
            }
        }
        CmpOrdering::Equal
    }
}

pub enum Outcome {
    /// A complete (and, for lifted mode, fully instantiated) plan was found.
    Solved(Rc<Plan>),
    /// The search-node limit was reached before a solution was found.
    LimitReached,
    /// The search space was exhausted without finding a solution.
    NoSolution,
}

/// Search-space statistics for one `plan` invocation. Exposed so benchmarking
/// harnesses can record per-run node counts without scraping stderr.
#[derive(Clone, Copy, Debug, Default)]
pub struct SearchStats {
    /// Plans pushed onto a search queue (search nodes generated).
    pub nodes_generated: usize,
    /// Plans dequeued and refined (search nodes visited/expanded).
    pub nodes_visited: usize,
    /// Heuristic (rank) evaluations performed.
    pub h_evals: usize,
    /// Total milliseconds spent in heuristic (rank) evaluations.
    pub h_eval_ms: u128,
    /// Children discarded by relaxed-reachability pruning at generation time.
    pub pruned: usize,
    /// Largest number of real steps seen in an expanded partial plan.
    pub max_steps: usize,
    /// Largest number of open conditions seen in an expanded partial plan.
    pub max_open_conditions: usize,
    /// Largest number of threats seen in an expanded partial plan.
    pub max_threats: usize,
    /// Largest primary open-list size observed during search.
    pub max_queued: usize,
}

/// A point-in-time view of an active search, delivered after an expansion.
///
/// The callback APIs expose this representation-neutral snapshot so command-line
/// clients can render useful progress without coupling either search engine to
/// stderr, a terminal UI, or a particular logging framework.
#[derive(Clone, Copy, Debug)]
pub struct SearchProgress {
    /// Time spent in the search loop (task construction/translation excluded).
    pub elapsed: Duration,
    pub nodes_generated: usize,
    pub nodes_visited: usize,
    /// Number of nodes waiting in the primary open lists. Secondary queue
    /// duplicates used by dual-queue algorithms are deliberately excluded.
    pub queued: usize,
    pub h_evals: usize,
    pub h_eval_ms: u128,
    pub pruned: usize,
    /// Shape of the partial plan expanded for this update.
    pub current_steps: usize,
    pub current_open_conditions: usize,
    pub current_threats: usize,
    /// Zero-based index of the active flaw-selection order.
    pub flaw_order: usize,
}

pub fn plan(ctx: &SearchContext) -> Outcome {
    plan_with_stats(ctx).0
}

/// Like [`plan_with_stats`], while also reporting a snapshot after each node
/// expansion. The callback decides how often to render or persist snapshots;
/// the search engine itself remains silent.
pub fn plan_with_progress(
    ctx: &SearchContext,
    progress: &mut dyn FnMut(SearchProgress),
) -> (Outcome, SearchStats) {
    plan_impl(ctx, Some(progress))
}

/// Pops the next plan to expand from the primary queue (and optionally the
/// secondary FIFO queue for dual-queue mode), handling lazy h-evaluation.
///
/// Returns `(Some(plan), rank0)` where `rank0` is the plan's primary rank
/// component (used as the lazy proxy for its children), or `(None, 0.0)` if
/// all queues are empty.
///
/// Lazy plans: their rank is a proxy; the real h is computed here. If the real
/// rank is finite the plan is re-pushed with the correct rank (not expanded
/// this call). Dead-end plans (real rank = ∞) are silently dropped. Neither
/// case counts as a visited plan.
#[allow(clippy::too_many_arguments)]
fn pop_next(
    primary: &mut BinaryHeap<QueuedPlan>,
    mut secondary: Option<&mut BinaryHeap<QueuedPlan>>,
    expanded_ids: &HashSet<usize>,
    ctx: &SearchContext,
    is_lazy: bool,
    is_gbfs: bool,
    is_dual: bool,
    is_alt: bool,
    boost_budget: &mut usize,
    expand_count: &mut usize,
) -> (Option<Rc<Plan>>, f32) {
    // ALT: strict 1:1 alternation between the A*-ordered primary queue and the
    // h-ordered secondary queue. The queue is chosen once per call (i.e. per
    // expansion) so skipping stale entries inside the loop below does not
    // perturb the alternation. Odd expansions pop the A* queue, even the GBFS
    // queue.
    let alt_use_secondary = is_alt && {
        *expand_count += 1;
        (*expand_count).is_multiple_of(2)
    };
    loop {
        // In dual-queue mode, decide which queue to pop from.
        let use_secondary = alt_use_secondary
            || (is_dual && *boost_budget == 0 && {
                *expand_count += 1;
                (*expand_count).is_multiple_of(3) // pop secondary every 3rd expansion (2:1 ratio)
            });

        let q = if use_secondary {
            if let Some(sec) = secondary.as_deref_mut() {
                sec.pop().or_else(|| primary.pop())
            } else {
                primary.pop()
            }
        } else if is_alt {
            // Both queues hold the same plans (modulo stale entries), so fall
            // back to the secondary queue when the primary drains first.
            primary
                .pop()
                .or_else(|| secondary.as_deref_mut().and_then(|sec| sec.pop()))
        } else {
            primary.pop()
        };

        let q = match q {
            Some(q) => q,
            None => return (None, 0.0),
        };

        // Skip plans already expanded (stale secondary-queue duplicates).
        if (is_dual || is_alt) && expanded_ids.contains(&q.plan.id.get()) {
            continue;
        }

        if !is_lazy || !q.is_lazy {
            let r0 = q.rank[0];
            return (Some(q.plan), r0);
        }

        // Lazy: compute the real rank now.
        let real_rank = if is_gbfs {
            q.plan.rank_gbfs(ctx)
        } else {
            q.plan.rank(ctx)
        };
        if real_rank[0].is_finite() {
            primary.push(QueuedPlan {
                plan: q.plan,
                rank: real_rank,
                is_lazy: false,
            });
        }
        // Do not expand; loop to pop the next candidate.
    }
}

/// Whether an opt-in pruning rule discards this refinement.
///
/// The rules are checked cheapest first, so an expensive one only runs on plans
/// the cheap ones kept. Each is sound on its own terms; see `crate::pruning`.
fn discarded_by_pruning(ctx: &SearchContext, plan: &Plan) -> bool {
    let options = ctx.params.prune;
    if options.params && violates_parameter_domains(ctx, plan) {
        return true;
    }
    if options.cutset {
        let mutexes = ctx.lifted_mutexes();
        if crate::cutset::lifted::may_apply(plan, &mutexes)
            && crate::cutset::lifted::has_inconsistent_cutset(ctx, plan, &mutexes)
        {
            return true;
        }
    }
    if options.minimality && crate::minimality::prunable(plan) {
        return true;
    }
    if options.recursion && crate::opgraph::prunable(ctx, plan) {
        return true;
    }
    false
}

/// Whether parameter domains rule out a threat's unifier
/// (Gerevini & Schubert, JAIR 5, 1996, §5).
///
/// Reject a parameter/object equality outside the parameter's domain or a
/// parameter/parameter equality whose domains are disjoint.
pub(crate) fn threat_unifier_impossible(ctx: &SearchContext, unifier: &[Binding]) -> bool {
    if unifier.is_empty() {
        return false;
    }
    let domains = ctx.param_domains();
    for binding in unifier {
        if !binding.equality {
            continue;
        }
        let Some((action, position)) = parameter_position(ctx, binding.var, binding.var_id) else {
            continue;
        };
        match binding.term {
            Term::Object(object) => {
                if !domains.permits(&action.name, position, object) {
                    return true;
                }
            }
            Term::Variable(other) => {
                let Some((other_action, other_position)) =
                    parameter_position(ctx, other, binding.term_id)
                else {
                    continue;
                };
                if !domains.positions_can_agree(
                    &action.name,
                    position,
                    &other_action.name,
                    other_position,
                ) {
                    return true;
                }
            }
        }
    }
    false
}

/// The action a step was instantiated from, and the index of `var` among its
/// parameters. `None` for a synthetic step, or a variable that is not one of the
/// action's own parameters (a `forall` instance variable, say).
fn parameter_position(
    ctx: &SearchContext,
    var: Variable,
    step_id: usize,
) -> Option<(Rc<StepAction>, usize)> {
    let action = ctx.step_action(step_id)?;
    if action.synthetic() {
        return None;
    }
    let position = action.parameters.iter().position(|p| *p == var)?;
    Some((action, position))
}

/// Whether any step of the plan binds a parameter to an object outside the
/// constants that can reach it (Gerevini & Schubert 1996).
///
/// Every step is checked, not only the newest: a binding added anywhere in the
/// plan — by a link, or by a separation — can be what first pins an older
/// step's parameter to an impossible object.
fn violates_parameter_domains(ctx: &SearchContext, plan: &Plan) -> bool {
    let domains = ctx.param_domains();
    for step in chain::iter(&plan.steps) {
        let action = &step.action;
        if action.synthetic() {
            continue;
        }
        // A ground step carries its arguments directly.
        if !action.arguments.is_empty() {
            if !domains.permits_arguments(&action.name, &action.arguments) {
                return true;
            }
            continue;
        }
        for (position, variable) in action.parameters.iter().enumerate() {
            if let Term::Object(object) = plan.bindings.binding(Term::Variable(*variable), step.id)
            {
                if !domains.permits(&action.name, position, object) {
                    return true;
                }
            }
        }
    }
    false
}

/// Whether some open condition introduced by `child`'s newly added step is
/// relaxed-unreachable under `child`'s bindings. Such a child can never be
/// completed: this is the same ∞-value that would make an eager rank discard
/// it, checked over only the new step's conditions (not the full open-condition
/// list) so it stays much cheaper than a full h evaluation.
///
/// Refinements that add no step (reuse, separation, ordering) return false —
/// their open conditions were already checked when first introduced. Binding
/// changes can in principle turn an *old* open condition unreachable; those
/// dead ends are still caught at pop time by the real h evaluation.
fn has_unreachable_new_open_cond(ctx: &SearchContext, parent: &Plan, child: &Plan) -> bool {
    if child.num_steps() <= parent.num_steps() {
        return false;
    }
    let Some(new_step) = chain::iter(&child.steps).next() else {
        return false;
    };
    let new_step_id = new_step.id;
    let pg = ctx.planning_graph();
    let type_ctx = ctx.type_ctx();
    let mut unreachable = false;
    for oc in chain::iter(child.open_conds()) {
        if oc.step_id != new_step_id {
            continue;
        }
        let (v, _) = crate::planning_graph::formula_value(
            &pg,
            &ctx.domain.predicates,
            &type_ctx,
            child,
            &oc.condition,
            oc.step_id,
            false,
        );
        if v.infinite() {
            unreachable = true;
            break;
        }
    }
    // Don't let a parked (or discarded) child retain its bindings lookup
    // index, mirroring `Plan::rank`.
    child.bindings.clear_index();
    unreachable
}

/// Like [`plan`], but also returns the [`SearchStats`] gathered during the
/// search. `plan` delegates here, so the two never diverge.
pub fn plan_with_stats(ctx: &SearchContext) -> (Outcome, SearchStats) {
    plan_impl(ctx, None)
}

fn plan_impl(
    ctx: &SearchContext,
    mut progress: Option<&mut dyn FnMut(SearchProgress)>,
) -> (Outcome, SearchStats) {
    let search_started = Instant::now();
    let n_orders = ctx.params.flaw_orders.len();
    let inf = f32::INFINITY;

    let initial_plan = match Plan::make_initial_plan(ctx) {
        Some(p) => p,
        None => return (Outcome::NoSolution, SearchStats::default()),
    };
    initial_plan.id.set(0);

    // Algorithm flags derived once.
    let alg = ctx.params.search_algorithm;
    let is_ida = alg == SearchAlgorithm::Ida;
    let is_bfs = alg == SearchAlgorithm::Bfs;
    let is_gbfs = matches!(
        alg,
        SearchAlgorithm::Gbfs | SearchAlgorithm::LazyGbfs | SearchAlgorithm::LazyGbfsDual
    );
    let is_lazy = matches!(
        alg,
        SearchAlgorithm::LazyGbfs | SearchAlgorithm::LazyGbfsDual
    );
    let is_dual = alg == SearchAlgorithm::LazyGbfsDual;
    // ALT: eager dual-queue alternation. Children are ranked under both the A*
    // ordering (primary queue) and the GBFS ordering (secondary queue);
    // expansions strictly alternate 1:1 between the two queues.
    let is_alt = alg == SearchAlgorithm::Alt;
    // Lazy modes skip ranking at generation time, so dead-end children are only
    // detected (and dropped) when popped, after paying a queue slot and a full
    // h evaluation. When a planning-graph heuristic is active, check just the
    // refinement's *new* open conditions for relaxed reachability at generation
    // time instead. Eager modes already get this from the ∞-rank discard.
    let prune_unreachable = is_lazy && ctx.params.heuristic.needs_planning_graph();
    let prune_options = ctx.params.prune;

    // One pending-plan queue and generated-plan counter per flaw order.
    let mut queues: Vec<BinaryHeap<QueuedPlan>> =
        (0..n_orders).map(|_| BinaryHeap::new()).collect();
    // Secondary queues (only allocated for dual-queue modes): FIFO for
    // LGBFS-D, h-ordered (GBFS rank) for ALT.
    let mut secondary_queues: Vec<BinaryHeap<QueuedPlan>> = if is_dual || is_alt {
        (0..n_orders).map(|_| BinaryHeap::new()).collect()
    } else {
        Vec::new()
    };
    // Plan IDs already expanded; used to skip stale secondary-queue entries.
    let mut expanded_ids: HashSet<usize> = HashSet::new();

    // Dual-queue boost state.
    let mut best_h: f32 = inf;
    let mut boost_budget: usize = 0;
    let mut expand_count: usize = 0; // for 2:1 primary:secondary ratio

    let mut generated_plans: Vec<usize> = vec![0; n_orders];
    let mut num_generated_plans: usize = 0;
    let mut num_visited_plans: usize = 0;
    let mut max_steps: usize = 0;
    let mut max_open_conditions: usize = 0;
    let mut max_threats: usize = 0;
    let mut max_queued: usize = 0;
    let stats = std::env::var_os("POTOROO_STATS").is_some();

    let mut current_flaw_order: usize = 0;
    let mut flaw_orders_left: usize = n_orders;
    let mut next_switch: usize = 1000;

    // The rank[0] of the plan currently being expanded. Used as the lazy proxy
    // for its children in lazy-evaluation modes.
    let mut current_rank0: f32 = 0.0;

    let mut current_plan: Option<Rc<Plan>> = Some(initial_plan.clone());
    generated_plans[current_flaw_order] += 1;
    num_generated_plans += 1;
    // Whether any flaw order exhausted its search limit (vs. ran out of plans).
    let mut limit_reached = false;

    let mut f_limit = if is_ida {
        initial_plan.primary_rank(ctx)
    } else {
        inf
    };

    loop {
        let mut next_f_limit = inf;
        while let Some(plan) = current_plan.clone() {
            if plan.complete() {
                break;
            }
            num_visited_plans += 1;
            max_steps = max_steps.max(plan.num_steps());
            max_open_conditions = max_open_conditions.max(plan.num_open_conds());
            max_threats = max_threats.max(plan.num_unsafes());
            if is_dual || is_alt {
                expanded_ids.insert(plan.id.get());
            }
            if is_dual {
                // Update boost when this plan's h improves the incumbent.
                if current_rank0 < best_h {
                    best_h = current_rank0;
                    boost_budget = boost_budget.saturating_add(10);
                }
                boost_budget = boost_budget.saturating_sub(1);
            }
            // Register step actions referenced by this plan for type lookups.
            for s in chain::iter(&plan.steps) {
                ctx.register_step(s.id, &s.action);
            }
            // Refine the current plan under the current flaw order.
            let mut refinements: Vec<Rc<Plan>> = Vec::new();
            plan.refinements_with(ctx, current_flaw_order, &mut refinements);

            let cfo = current_flaw_order;
            for new_plan in refinements {
                // N.B. id must be set before rank is computed (rank uses serial_no).
                new_plan.id.set(num_generated_plans);
                // Siblings share step ids, so claim the map before this child's
                // variables are typed by anything below.
                ctx.register_newest_step(&new_plan, plan.num_steps);

                // Opt-in literature pruning rules (`-p`). Each discards a plan
                // it has proved unrefinable or provably non-minimal; all are
                // off unless asked for. See `crate::pruning`.
                if prune_options.any() && discarded_by_pruning(ctx, &new_plan) {
                    ctx.pruned.set(ctx.pruned.get() + 1);
                    continue;
                }

                // ALT: GBFS-ordered rank from the shared evaluation, consumed
                // by the secondary-queue push below.
                let mut alt_gbfs_rank: Option<Vec<f32>> = None;

                // Compute rank and determine whether to push eagerly or lazily.
                let (rank, is_lazy_push) = if is_bfs {
                    // BFS: rank by step count, then plan id (FIFO tiebreak).
                    (
                        vec![new_plan.num_steps() as f32, new_plan.id.get() as f32],
                        false,
                    )
                } else if is_lazy {
                    if prune_unreachable && has_unreachable_new_open_cond(ctx, &plan, &new_plan) {
                        ctx.pruned.set(ctx.pruned.get() + 1);
                        continue;
                    }
                    // Lazy: use parent's rank[0] as a cheap h proxy, with the
                    // same tiebreakers as `plan_rank_gbfs`: fewer remaining
                    // flaws, then newest-generated (LIFO). Ascending plan ids
                    // would sweep proxy-plateaus breadth-first — exactly where
                    // lazy GBFS stalls.
                    (
                        vec![
                            current_rank0,
                            new_plan.num_open_conds() as f32,
                            -(new_plan.id.get() as f32),
                        ],
                        true,
                    )
                } else if is_gbfs {
                    (new_plan.rank_gbfs(ctx), false)
                } else if is_alt {
                    // ALT queues the child under both orderings; one shared
                    // evaluation produces the A* rank (primary queue) and the
                    // GBFS rank (secondary queue, pushed below).
                    let (a_rank, g_rank) = new_plan.rank_both(ctx);
                    alt_gbfs_rank = Some(g_rank);
                    (a_rank, false)
                } else {
                    (new_plan.rank(ctx), false)
                };

                let primary = rank[0];
                if primary.is_finite() && generated_plans[cfo] < ctx.params.search_limits[cfo] {
                    if is_ida && primary > f_limit {
                        next_f_limit = next_f_limit.min(primary);
                        continue;
                    }
                    if is_dual {
                        // Secondary queue: pure FIFO ordered by plan id.
                        secondary_queues[cfo].push(QueuedPlan {
                            plan: new_plan.clone(),
                            rank: vec![new_plan.id.get() as f32],
                            is_lazy: is_lazy_push,
                        });
                    } else if is_alt {
                        // ALT secondary queue: the GBFS (h-ordered) rank from
                        // the shared evaluation above.
                        secondary_queues[cfo].push(QueuedPlan {
                            plan: new_plan.clone(),
                            rank: alt_gbfs_rank
                                .take()
                                .expect("ALT child ranked without GBFS rank"),
                            is_lazy: false,
                        });
                    }
                    queues[cfo].push(QueuedPlan {
                        plan: new_plan,
                        rank,
                        is_lazy: is_lazy_push,
                    });
                    generated_plans[cfo] += 1;
                    num_generated_plans += 1;
                }
            }

            let queued = queues.iter().map(BinaryHeap::len).sum();
            max_queued = max_queued.max(queued);
            if let Some(report) = progress.as_deref_mut() {
                report(SearchProgress {
                    elapsed: search_started.elapsed(),
                    nodes_generated: num_generated_plans,
                    nodes_visited: num_visited_plans,
                    queued,
                    h_evals: ctx.h_evals.get(),
                    h_eval_ms: ctx.h_eval_nanos.get() / 1_000_000,
                    pruned: ctx.pruned.get(),
                    current_steps: plan.num_steps(),
                    current_open_conditions: plan.num_open_conds(),
                    current_threats: plan.num_unsafes(),
                    flaw_order: current_flaw_order,
                });
            }

            // Time to switch flaw orders? (limit reached, or this order has had
            // its turn of `next_switch` generated plans).
            let order_limit_reached =
                generated_plans[current_flaw_order] >= ctx.params.search_limits[current_flaw_order];
            if order_limit_reached || generated_plans[current_flaw_order] >= next_switch {
                if order_limit_reached {
                    limit_reached = true;
                    flaw_orders_left = flaw_orders_left.saturating_sub(1);
                    queues[current_flaw_order].clear();
                    if is_dual || is_alt {
                        secondary_queues[current_flaw_order].clear();
                    }
                }
                if flaw_orders_left > 0 {
                    loop {
                        current_flaw_order += 1;
                        if current_flaw_order >= n_orders {
                            current_flaw_order = 0;
                            next_switch *= 2;
                        }
                        if generated_plans[current_flaw_order]
                            < ctx.params.search_limits[current_flaw_order]
                        {
                            break;
                        }
                    }
                }
            }

            if flaw_orders_left > 0 {
                if generated_plans[current_flaw_order] == 0 {
                    // First visit to this flaw order: start from the initial plan.
                    current_plan = Some(initial_plan.clone());
                    current_rank0 = 0.0;
                    generated_plans[current_flaw_order] += 1;
                    num_generated_plans += 1;
                } else {
                    (current_plan, current_rank0) = pop_next(
                        &mut queues[current_flaw_order],
                        if is_dual || is_alt {
                            Some(&mut secondary_queues[current_flaw_order])
                        } else {
                            None
                        },
                        &expanded_ids,
                        ctx,
                        is_lazy,
                        is_gbfs,
                        is_dual,
                        is_alt,
                        &mut boost_budget,
                        &mut expand_count,
                    );
                }

                // Instantiate all actions if the plan is otherwise complete
                // (lifted mode only).
                if !ctx.params.ground_actions {
                    let correct_costs = has_parameterised_costs(ctx);
                    loop {
                        match &current_plan {
                            Some(p) if p.complete() => match step_instantiation(ctx, p) {
                                Some(inst) => {
                                    // A step whose cost depends on its arguments
                                    // was priced at the schema's lower bound when
                                    // it was added. Now that instantiation has
                                    // bound every argument the real cost is known;
                                    // if it is higher this plan is worse than its
                                    // `g` claimed, so requeue it at its true cost
                                    // rather than return it as the best found.
                                    let exact = if correct_costs {
                                        exact_plan_cost(ctx, &inst)
                                    } else {
                                        inst.cost
                                    };
                                    if exact > inst.cost {
                                        num_generated_plans += 1;
                                        let corrected = Rc::new(Plan {
                                            steps: inst.steps.clone(),
                                            num_steps: inst.num_steps,
                                            cost: exact,
                                            links: inst.links.clone(),
                                            num_links: inst.num_links,
                                            orderings: inst.orderings.clone(),
                                            bindings: inst.bindings.clone(),
                                            unsafes: inst.unsafes.clone(),
                                            num_unsafes: inst.num_unsafes,
                                            open_conds: inst.open_conds.clone(),
                                            num_open_conds: inst.num_open_conds,
                                            id: std::cell::Cell::new(num_generated_plans),
                                        });
                                        let rank = corrected.rank(ctx);
                                        if rank[0].is_finite() {
                                            queues[current_flaw_order].push(QueuedPlan {
                                                plan: corrected,
                                                rank,
                                                is_lazy: false,
                                            });
                                        }
                                        (current_plan, current_rank0) = pop_next(
                                            &mut queues[current_flaw_order],
                                            if is_dual || is_alt {
                                                Some(&mut secondary_queues[current_flaw_order])
                                            } else {
                                                None
                                            },
                                            &expanded_ids,
                                            ctx,
                                            is_lazy,
                                            is_gbfs,
                                            is_dual,
                                            is_alt,
                                            &mut boost_budget,
                                            &mut expand_count,
                                        );
                                        continue;
                                    }
                                    current_plan = Some(inst);
                                    break;
                                }
                                None => {
                                    (current_plan, current_rank0) = pop_next(
                                        &mut queues[current_flaw_order],
                                        if is_dual || is_alt {
                                            Some(&mut secondary_queues[current_flaw_order])
                                        } else {
                                            None
                                        },
                                        &expanded_ids,
                                        ctx,
                                        is_lazy,
                                        is_gbfs,
                                        is_dual,
                                        is_alt,
                                        &mut boost_budget,
                                        &mut expand_count,
                                    );
                                }
                            },
                            _ => break,
                        }
                    }
                }
            } else {
                if next_f_limit != inf {
                    current_plan = None;
                }
                break;
            }
        }

        if matches!(&current_plan, Some(p) if p.complete()) {
            break;
        }
        f_limit = next_f_limit;
        if f_limit != inf {
            // Restart the IDA* search with the relaxed f-limit.
            current_plan = Some(initial_plan.clone());
            current_rank0 = 0.0;
        } else {
            break;
        }
    }

    if stats {
        eprintln!("Plans generated: {num_generated_plans}\nPlans visited: {num_visited_plans}");
    }

    let search_stats = SearchStats {
        nodes_generated: num_generated_plans,
        nodes_visited: num_visited_plans,
        h_evals: ctx.h_evals.get(),
        h_eval_ms: ctx.h_eval_nanos.get() / 1_000_000,
        pruned: ctx.pruned.get(),
        max_steps,
        max_open_conditions,
        max_threats,
        max_queued,
    };
    let outcome = match current_plan {
        Some(p) if p.complete() => {
            // Independent correctness oracle: recompute the POCL solution
            // invariants (Definition 1) rather than trusting the planner's own
            // flaw bookkeeping. Catches silently-emitted invalid plans, the
            // historical bug class here. Debug-only so release search is unaffected.
            debug_assert!(
                match crate::validate::is_valid_solution(&p, ctx) {
                    Ok(()) => true,
                    Err(e) => {
                        eprintln!("INVALID SOLUTION emitted by search: {e}");
                        false
                    }
                },
                "search::plan returned a plan that is not a valid POCL solution"
            );
            Outcome::Solved(p)
        }
        _ if limit_reached => Outcome::LimitReached,
        _ => Outcome::NoSolution,
    };
    (outcome, search_stats)
}

/// The plan's cost with every parameterised step priced by the objects its
/// parameters are actually bound to, rather than by the schema's
/// minimum-over-instances bound.
///
/// A lifted step is added to a plan before its arguments are fully bound, so a
/// cost that depends on those arguments can only be bounded from below at that
/// point. Once the plan is complete and instantiated every argument is known,
/// and this recovers the real cost.
fn exact_plan_cost(ctx: &SearchContext, plan: &Plan) -> usize {
    let mut total: usize = 0;
    for step in chain::iter(&plan.steps) {
        if step.id == INIT_ID || step.id == GOAL_ID {
            continue;
        }
        total = total.saturating_add(exact_step_cost(ctx, plan, step));
    }
    total
}

/// One step's cost, resolved through the plan's bindings where the schema's
/// number is only a bound. Falls back to the recorded cost whenever the step is
/// already ground, the schema has no parameterised cost, or a parameter is
/// still unbound.
fn exact_step_cost(ctx: &SearchContext, plan: &Plan, step: &crate::plan::Step) -> usize {
    let recorded = ctx.action_cost(&step.action);
    if !step.action.arguments.is_empty() || step.action.parameters.is_empty() {
        return recorded;
    }
    let Some(schema) = ctx.domain.find_action(&step.action.name) else {
        return recorded;
    };
    if schema.cost_specs.iter().all(|s| s.is_argument_free()) {
        return recorded;
    }
    let mut arguments = Vec::with_capacity(step.action.parameters.len());
    for &v in &step.action.parameters {
        match plan.bindings.binding(Term::Variable(v), step.id) {
            Term::Object(o) => arguments.push(o),
            Term::Variable(_) => return recorded,
        }
    }
    match schema.instance_cost(&arguments, &ctx.cost_values) {
        Some(exact) => {
            if ctx.problem.metric == Some(Metric::MinimizeTotalCost) {
                ctx.params.action_cost.resolve(exact)
            } else {
                recorded
            }
        }
        None => recorded,
    }
}

/// Whether any schema prices an action by a function of its parameters, so a
/// complete plan's cost has to be recomputed once its steps are bound.
fn has_parameterised_costs(ctx: &SearchContext) -> bool {
    ctx.problem.metric == Some(Metric::MinimizeTotalCost)
        && ctx
            .domain
            .actions
            .iter()
            .any(|a| a.cost_specs.iter().any(|s| !s.is_argument_free()))
}

/// Returns a fully-instantiated copy of a complete plan, or `None` if its steps
/// cannot all be ground consistently.
fn step_instantiation(ctx: &SearchContext, plan: &Rc<Plan>) -> Option<Rc<Plan>> {
    let bindings = instantiate_steps(ctx, &plan.steps, plan.bindings.clone())?;
    if Rc::ptr_eq(&bindings, &plan.bindings) {
        return Some(plan.clone());
    }
    Some(Rc::new(Plan {
        steps: plan.steps.clone(),
        num_steps: plan.num_steps,
        cost: plan.cost,
        links: plan.links.clone(),
        num_links: plan.num_links,
        orderings: plan.orderings.clone(),
        bindings,
        unsafes: None,
        num_unsafes: 0,
        open_conds: None,
        num_open_conds: 0,
        id: std::cell::Cell::new(plan.id.get()),
    }))
}

/// Recursively binds each unbound schema parameter to a compatible object.
fn instantiate_steps(
    ctx: &SearchContext,
    steps: &Option<Rc<chain::Chain<crate::plan::Step>>>,
    bindings: Rc<Bindings>,
) -> Option<Rc<Bindings>> {
    let step_vec: Vec<crate::plan::Step> = chain::iter(steps).cloned().collect();
    instantiate_step_list(ctx, &step_vec, 0, 0, bindings)
}

fn instantiate_step_list(
    ctx: &SearchContext,
    steps: &[crate::plan::Step],
    step_idx: usize,
    param_idx: usize,
    bindings: Rc<Bindings>,
) -> Option<Rc<Bindings>> {
    if step_idx >= steps.len() {
        return Some(bindings);
    }
    let step = &steps[step_idx];
    let params = &step.action.parameters;
    if params.len() <= param_idx {
        return instantiate_step_list(ctx, steps, step_idx + 1, 0, bindings);
    }
    let v = params[param_idx];
    // Already bound to an object?
    if let Term::Object(_) = bindings.binding(Term::Variable(v), step.id) {
        return instantiate_step_list(ctx, steps, step_idx, param_idx + 1, bindings);
    }
    let ty = step.action.var_types[v.0 as usize];
    for obj in ctx.compatible_objects(ty) {
        let bl = vec![crate::bindings::Binding::new(
            v,
            step.id,
            Term::Object(obj),
            0,
            true,
        )];
        if let Some(nb) = bindings.add(&ctx.type_ctx(), &bl, false) {
            if let Some(result) = instantiate_step_list(ctx, steps, step_idx, param_idx + 1, nb) {
                return Some(result);
            }
        }
    }
    None
}

/// Formats the plan body: the problem header comment, then the scheduled step
/// lines.
pub fn format_plan_body(ctx: &SearchContext, plan: &Plan) -> String {
    let steps = format_steps(ctx, plan);
    if steps.is_empty() {
        format!(";{}", ctx.problem.name)
    } else {
        format!(";{}\n{}", ctx.problem.name, steps)
    }
}

/// Formats just the step lines (no `;name` header): one `START:(action args...)`
/// line per real step in scheduled order. Steps whose action name begins with
/// `<` (or is empty) are skipped.
pub fn format_steps(ctx: &SearchContext, plan: &Plan) -> String {
    let (start_times, _makespan) = plan.orderings.schedule();
    // Collect real steps with their start times.
    let mut ordered: Vec<(&crate::plan::Step, f32)> = Vec::new();
    for s in chain::iter(&plan.steps) {
        if s.id == INIT_ID || s.id == GOAL_ID {
            continue;
        }
        let t = start_times.get(&s.id).copied().unwrap_or(0.0);
        ordered.push((s, t));
    }
    // Stable sort by start time (matches std::stable behaviour closely enough;
    // ties retain chain order which the C++ `sort` does not guarantee, but for
    // the classical totally-ordered solutions there are no ties).
    ordered.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(CmpOrdering::Equal));

    let mut lines: Vec<String> = Vec::new();
    for (s, t) in ordered {
        if s.action.synthetic() {
            continue;
        }
        lines.push(format!("{}:{}", format_float(t), format_step(ctx, plan, s)));
    }
    lines.join("\n")
}

fn format_step(ctx: &SearchContext, plan: &Plan, step: &crate::plan::Step) -> String {
    let mut s = String::new();
    s.push('(');
    s.push_str(&step.action.name);
    if !step.action.arguments.is_empty() {
        // Ground action: print arguments directly.
        for &obj in &step.action.arguments {
            s.push(' ');
            s.push_str(object_name(ctx, obj));
        }
    } else {
        // Lifted action: print each parameter's bound object.
        for &v in &step.action.parameters {
            s.push(' ');
            let t = plan.bindings.binding(Term::Variable(v), step.id);
            match t {
                Term::Object(o) => s.push_str(object_name(ctx, o)),
                Term::Variable(_) => s.push('?'),
            }
        }
    }
    s.push(')');
    s
}

fn object_name<'a>(ctx: &'a SearchContext, o: Object) -> &'a str {
    ctx.problem
        .objects
        .object_name(Some(&ctx.domain.constants), o)
}

/// Formats a float the way C++ `ostream << float` does: integers without a
/// decimal point.
fn format_float(f: f32) -> String {
    if f.fract() == 0.0 {
        format!("{}", f as i64)
    } else {
        format!("{f}")
    }
}
