//! Plan-ranking heuristics and flaw-selection orders.

use crate::bindings::TypeContext;
use crate::chain;
use crate::compile::CompiledProblem;
use crate::external::{self, FdHeuristic, HResult};
use crate::flaws::Flaw;
use crate::plan::Plan;
use crate::planning_graph::{formula_value, PlanningGraph};
use crate::predicates::PredicateTable;
use crate::search::SearchContext;

/// A plan-ranking heuristic value. `MAKESPAN` (temporal) is deferred.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HVal {
    Lifo,
    Fifo,
    Oc,
    Uc,
    Buc,
    SPlusOc,
    Ucpop,
    Add,
    AddCost,
    AddWork,
    Addr,
    AddrCost,
    AddrWork,
    /// Relax / RePOP heuristic: size of a delete-relaxed plan for the open
    /// conditions (FF-style joint extraction). `Relax` counts every relaxed-plan
    /// action; `RelaxR` reuses existing plan steps (counts only new actions).
    Relax,
    RelaxR,
    /// Native LM-cut over the FDR POCL open-condition relaxation. `LmCut`
    /// starts from the problem initial state; `LmCutR` also treats effects of
    /// committed steps as initially available. FDR POCL search only.
    LmCut,
    LmCutR,
    /// Sample-FF heuristic (Bercher et al. 2013): keep the committed plan steps
    /// non-relaxed and fill the gaps between them with delete relaxation, over
    /// `usize` sampled linearizations of the partial order. Ground search only.
    SampleFf(usize),
    /// Lplan LP heuristic (Bylander 1997): the smallest horizon whose relaxed LP
    /// over the causal-link compilation reaches the goal — an admissible lower
    /// bound on the completion length. Ground search only.
    Lplan,
    /// Causal-link compilation heuristic: rank by a state-based heuristic
    /// (computed by Fast Downward) on the initial state of the classical problem
    /// the partial plan compiles to (`crate::compile`). The `FdHeuristic` is the
    /// backend (FF / LM-cut / hmax / ...).
    Compile(FdHeuristic),
}

/// A plan-ranking heuristic (a sequence of ranking terms).
#[derive(Debug, Clone)]
pub struct Heuristic {
    h: Vec<HVal>,
    needs_pg: bool,
}

impl Heuristic {
    pub fn parse(name: &str) -> Result<Heuristic, String> {
        let mut h = Vec::new();
        let mut needs_pg = false;
        for part in name.split('/') {
            // Causal-link compilation heuristics (COMPILE / COMPILE_FF / ...).
            if let Some(backend) = crate::compile::parse_backend(part) {
                h.push(HVal::Compile(backend));
                continue;
            }
            // Sample-FF (SAMPLE_FF or SAMPLE_FF:k for k samples).
            let upper = part.to_ascii_uppercase();
            if upper == "SAMPLE_FF" || upper.starts_with("SAMPLE_FF:") {
                let k = match upper.strip_prefix("SAMPLE_FF:") {
                    Some(n) => n
                        .parse::<usize>()
                        .map_err(|_| format!("invalid SAMPLE_FF sample count `{n}`"))?,
                    None => crate::sample_ff::DEFAULT_SAMPLES,
                };
                if k == 0 {
                    return Err("SAMPLE_FF sample count must be positive".to_string());
                }
                h.push(HVal::SampleFf(k));
                continue;
            }
            let v = match part.to_ascii_uppercase().as_str() {
                "LIFO" => HVal::Lifo,
                "FIFO" => HVal::Fifo,
                "OC" => HVal::Oc,
                "UC" => HVal::Uc,
                "BUC" => HVal::Buc,
                "S+OC" => HVal::SPlusOc,
                "UCPOP" => HVal::Ucpop,
                "ADD" => {
                    needs_pg = true;
                    HVal::Add
                }
                "ADD_COST" => {
                    needs_pg = true;
                    HVal::AddCost
                }
                "ADD_WORK" => {
                    needs_pg = true;
                    HVal::AddWork
                }
                "ADDR" => {
                    needs_pg = true;
                    HVal::Addr
                }
                "ADDR_COST" => {
                    needs_pg = true;
                    HVal::AddrCost
                }
                "ADDR_WORK" => {
                    needs_pg = true;
                    HVal::AddrWork
                }
                "RELAX" => {
                    needs_pg = true;
                    HVal::Relax
                }
                "RELAXR" => {
                    needs_pg = true;
                    HVal::RelaxR
                }
                "LMCUT" | "LM-CUT" => HVal::LmCut,
                "LMCUTR" | "LM-CUTR" => HVal::LmCutR,
                "LPLAN" => HVal::Lplan,
                "MAKESPAN" => {
                    return Err("heuristic `MAKESPAN` is temporal and not yet supported".to_string())
                }
                other => return Err(format!("invalid heuristic `{other}`")),
            };
            h.push(v);
        }
        Ok(Heuristic { h, needs_pg })
    }

    pub fn needs_planning_graph(&self) -> bool {
        self.needs_pg
    }

    /// Whether this ranking contains a heuristic defined only for native FDR
    /// POCL nodes rather than the literal partial-plan representation.
    pub fn requires_fdr_pocl(&self) -> bool {
        self.h
            .iter()
            .any(|term| matches!(term, HVal::LmCut | HVal::LmCutR))
    }

    /// Parsed ranking terms for alternate plan representations. Keeping the
    /// syntax in one place lets ground finite-domain search consume exactly the
    /// same `-h` configuration without translating SAS+ facts back to literals.
    pub(crate) fn terms(&self) -> &[HVal] {
        &self.h
    }

    /// Fills `rank` with the heuristic ranks for `plan`. Lower is better.
    pub fn plan_rank(
        &self,
        plan: &Plan,
        weight: f32,
        predicates: &PredicateTable,
        ctx: &TypeContext,
        pg: Option<&PlanningGraph>,
        search_ctx: &SearchContext,
    ) -> Vec<f32> {
        self.plan_rank_both(plan, weight, predicates, ctx, pg, search_ctx)
            .0
    }

    /// Computes the A* rank ([`plan_rank`](Self::plan_rank)) and the GBFS rank
    /// ([`plan_rank_gbfs`](Self::plan_rank_gbfs)) in one pass, sharing every
    /// heuristic evaluation between them. The two ranks differ only in the
    /// g-component (step count) mixed into some entries and the trailing GBFS
    /// tiebreakers, so algorithms that need both orderings of the same plan
    /// (`ALT`) pay one evaluation instead of two.
    pub fn plan_rank_both(
        &self,
        plan: &Plan,
        weight: f32,
        predicates: &PredicateTable,
        ctx: &TypeContext,
        pg: Option<&PlanningGraph>,
        search_ctx: &SearchContext,
    ) -> (Vec<f32>, Vec<f32>) {
        let mut rank = Vec::with_capacity(self.h.len());
        let mut grank = Vec::with_capacity(self.h.len() + 2);
        // Cache the ADD / ADDR sums across the (single) ADD* / ADDR* terms.
        let mut add_done = false;
        let mut add_cost = 0.0f32;
        let mut add_work = 0i32;
        let mut addr_done = false;
        let mut addr_cost = 0.0f32;
        let mut addr_work = 0i32;
        // i32::MAX as f32 (the C++ `std::numeric_limits<int>::max()` comparison).
        let int_max_f = i32::MAX as f32;
        let steps = plan.num_steps() as f32;

        for &h in &self.h {
            match h {
                // No g component: both ranks carry the same value.
                HVal::Lifo => {
                    rank.push(-(plan.serial_no() as f32));
                    grank.push(-(plan.serial_no() as f32));
                }
                HVal::Fifo => {
                    rank.push(plan.serial_no() as f32);
                    grank.push(plan.serial_no() as f32);
                }
                HVal::Oc => {
                    rank.push(plan.num_open_conds() as f32);
                    grank.push(plan.num_open_conds() as f32);
                }
                HVal::Uc => {
                    rank.push(plan.num_unsafes() as f32);
                    grank.push(plan.num_unsafes() as f32);
                }
                HVal::Buc => {
                    let v = if plan.num_unsafes() > 0 { 1.0 } else { 0.0 };
                    rank.push(v);
                    grank.push(v);
                }
                HVal::SPlusOc => {
                    let hterm = weight * plan.num_open_conds() as f32;
                    rank.push(steps + hterm);
                    grank.push(hterm);
                }
                HVal::Ucpop => {
                    let hterm = weight * (plan.num_open_conds() + plan.num_unsafes()) as f32;
                    rank.push(steps + hterm);
                    grank.push(hterm);
                }
                HVal::Add | HVal::AddCost | HVal::AddWork => {
                    let pg = pg.expect("ADD heuristic requires a planning graph");
                    if !add_done {
                        add_done = true;
                        for oc in chain::iter(plan.open_conds()) {
                            let (v, _vs) = formula_value(
                                pg,
                                predicates,
                                ctx,
                                plan,
                                &oc.condition,
                                oc.step_id,
                                false,
                            );
                            add_cost += v.add_cost();
                            add_work = saturating_sum(add_work, v.add_work());
                            // Both accumulators pegged: every downstream value
                            // is already decided (cost ranks read only the
                            // `< int_max_f` threshold, work is saturated), so
                            // skip the remaining open conditions. Dead-end
                            // children hit this on their first unreachable
                            // condition — the newest, scanned first.
                            if add_cost >= int_max_f && add_work == i32::MAX {
                                break;
                            }
                        }
                    }
                    let cost_fin = add_cost < int_max_f;
                    let work_fin = add_work < i32::MAX;
                    match h {
                        HVal::Add => {
                            rank.push(if cost_fin {
                                steps + weight * add_cost
                            } else {
                                f32::INFINITY
                            });
                            grank.push(if cost_fin { add_cost } else { f32::INFINITY });
                        }
                        HVal::AddCost => {
                            let v = if cost_fin { add_cost } else { f32::INFINITY };
                            rank.push(v);
                            grank.push(v);
                        }
                        _ => {
                            let v = if work_fin {
                                add_work as f32
                            } else {
                                f32::INFINITY
                            };
                            rank.push(v);
                            grank.push(v);
                        }
                    }
                }
                HVal::Addr | HVal::AddrCost | HVal::AddrWork => {
                    let pg = pg.expect("ADDR heuristic requires a planning graph");
                    if !addr_done {
                        addr_done = true;
                        for oc in chain::iter(plan.open_conds()) {
                            let (v, _vs) = formula_value(
                                pg,
                                predicates,
                                ctx,
                                plan,
                                &oc.condition,
                                oc.step_id,
                                true,
                            );
                            addr_cost += v.add_cost();
                            addr_work = saturating_sum(addr_work, v.add_work());
                            // See the ADD loop: pegged accumulators decide
                            // every downstream value; skip the rest.
                            if addr_cost >= int_max_f && addr_work == i32::MAX {
                                break;
                            }
                        }
                    }
                    let cost_fin = addr_cost < int_max_f;
                    let work_fin = addr_work < i32::MAX;
                    match h {
                        HVal::Addr => {
                            rank.push(if cost_fin {
                                steps + weight * addr_cost
                            } else {
                                f32::INFINITY
                            });
                            grank.push(if cost_fin { addr_cost } else { f32::INFINITY });
                        }
                        HVal::AddrCost => {
                            let v = if cost_fin { addr_cost } else { f32::INFINITY };
                            rank.push(v);
                            grank.push(v);
                        }
                        _ => {
                            let v = if work_fin {
                                addr_work as f32
                            } else {
                                f32::INFINITY
                            };
                            rank.push(v);
                            grank.push(v);
                        }
                    }
                }
                HVal::Relax | HVal::RelaxR => {
                    let pg = pg.expect("RELAX heuristic requires a planning graph");
                    let reuse = matches!(h, HVal::RelaxR);
                    match pg.relaxed_plan_size(ctx, plan, reuse) {
                        Some(v) => {
                            rank.push(steps + weight * v);
                            grank.push(weight * v);
                        }
                        None => {
                            rank.push(f32::INFINITY);
                            grank.push(f32::INFINITY);
                        }
                    }
                }
                HVal::LmCut | HVal::LmCutR => {
                    unreachable!("native LMCUT/LMCUTR requires FDR POCL search")
                }
                // Delegating heuristics carry no separable g component; both
                // ranks use the same value, computed once.
                HVal::SampleFf(k) => {
                    let v = crate::sample_ff::sample_ff_rank(plan, search_ctx, weight, k);
                    rank.push(v);
                    grank.push(v);
                }
                HVal::Lplan => {
                    let v = crate::lplan::lplan_rank(plan, search_ctx, weight);
                    rank.push(v);
                    grank.push(v);
                }
                HVal::Compile(backend) => {
                    let v = compile_rank(plan, search_ctx, weight, backend);
                    rank.push(v);
                    grank.push(v);
                }
            }
        }
        // GBFS tiebreakers: prefer fewer remaining flaws (progress towards
        // completion), then newest-generated (LIFO). Ascending serial numbers
        // would sweep h-plateaus breadth-first, which is exactly where greedy
        // search stalls; diving on the newest plan escapes them.
        grank.push(plan.num_open_conds() as f32);
        grank.push(-(plan.serial_no() as f32));
        (rank, grank)
    }

    /// Greedy-BFS variant of [`plan_rank`]: strips the g-component (step count)
    /// from each `HVal` so the primary sort criterion is pure h. After the
    /// h-components, `steps` and `plan_id` are appended as tiebreakers so the
    /// ordering remains deterministic. Heuristics that already have no g
    /// component (e.g. `AddCost`, `Oc`, `Fifo`) are returned unchanged.
    pub fn plan_rank_gbfs(
        &self,
        plan: &Plan,
        weight: f32,
        predicates: &PredicateTable,
        ctx: &TypeContext,
        pg: Option<&PlanningGraph>,
        search_ctx: &SearchContext,
    ) -> Vec<f32> {
        self.plan_rank_both(plan, weight, predicates, ctx, pg, search_ctx)
            .1
    }
}

/// Ranks a partial plan by the causal-link compilation heuristic: compile to a
/// classical task, ask Fast Downward for the chosen state-based heuristic on its
/// initial state, and combine as `g + weight*h` (`num_steps` committed plus the
/// estimated remaining cost), matching the additive heuristic's shape.
///
/// An unreachable compiled goal (FD reports infinite) or an FD error sinks the
/// plan to `INFINITY` (it won't be expanded unless nothing better remains),
/// matching how the ADD heuristic treats unreachable open conditions. Note: this
/// spawns an FD subprocess per evaluation — the dominant cost, as the paper
/// notes; identical compiled problems are memoized in `crate::external`.
fn compile_rank(plan: &Plan, ctx: &SearchContext, weight: f32, backend: FdHeuristic) -> f32 {
    // Ground search: take the fast path — ground the task ourselves into FDR and
    // invoke only the `downward` C++ binary, skipping FD's Python translator
    // (~95% of the per-node cost). Lifted search: emit PDDL and run the full
    // driver (the translator is needed to ground the lifted task).
    let result = if ctx.params.ground_actions {
        crate::compile::ground_task(plan, ctx).heuristic(backend)
    } else {
        let compiled = CompiledProblem::compile(plan, ctx);
        let (domain_pddl, problem_pddl) = compiled.emit_pddl(ctx);
        external::run_fd_heuristic(&domain_pddl, &problem_pddl, backend)
    };
    match result {
        Ok(HResult::Finite(h)) => plan.num_steps() as f32 + weight * h,
        Ok(HResult::Infinite) => f32::INFINITY,
        Err(e) => {
            eprintln!("COMPILE heuristic: Fast Downward error: {e}");
            f32::INFINITY
        }
    }
}

fn saturating_sum(n: i32, m: i32) -> i32 {
    if i32::MAX - n > m {
        n + m
    } else {
        i32::MAX
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OrderType {
    Lifo,
    Fifo,
    Random,
    /// Least refinements.
    Lr,
    /// Most refinements.
    Mr,
    /// Prefer open conditions with a new-step achiever.
    New,
    /// Prefer open conditions with a reuse achiever.
    Reuse,
    /// Least heuristic cost.
    Lc,
    /// Most heuristic cost.
    Mc,
    /// Least heuristic work.
    Lw,
    /// Most heuristic work.
    Mw,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RankHeuristic {
    Add,
}

#[derive(Debug, Clone)]
pub(crate) struct SelectionCriterion {
    pub(crate) non_separable: bool,
    pub(crate) separable: bool,
    pub(crate) open_cond: bool,
    pub(crate) local_open_cond: bool,
    pub(crate) static_open_cond: bool,
    pub(crate) unsafe_open_cond: bool,
    /// `i32::MAX` means unlimited.
    pub(crate) max_refinements: i32,
    pub(crate) order: OrderType,
    heuristic: RankHeuristic,
    pub(crate) reuse: bool,
}

/// A flaw-selection order: a sequence of selection criteria.
#[derive(Debug, Clone)]
pub struct FlawSelectionOrder {
    selection_criteria: Vec<SelectionCriterion>,
    needs_pg: bool,
    /// Stored as i64 so the `first > last` "empty" sentinel (i32::MAX vs 0)
    /// can be represented without wrapping.
    first_unsafe_criterion: i64,
    last_unsafe_criterion: i64,
    first_open_cond_criterion: i64,
    last_open_cond_criterion: i64,
}

struct FlawSelection {
    flaw: Option<Flaw>,
    /// Index of the criterion that selected `flaw`. `i32::MAX` = none yet.
    criterion: i64,
    /// Rank of the selected flaw (for ranking criteria).
    rank: f32,
    /// Streak length, for the random order.
    streak: i32,
}

impl FlawSelectionOrder {
    /// Parses a flaw-selection-order name: expands predefined aliases to their
    /// criteria strings, then parses the `{flaws}[max]ORDER` grammar.
    pub fn parse(name: &str) -> Result<FlawSelectionOrder, String> {
        // Predefined aliases.
        let lower = name.to_ascii_lowercase();
        let expanded: Option<&str> = match lower.as_str() {
            "ucpop" => Some("{n,s}LIFO/{o}LIFO"),
            "ucpop-lc" => Some("{n,s}LIFO/{o}LR"),
            "dsep-lifo" => Some("{n}LIFO/{o}LIFO/{s}LIFO"),
            "dsep-fifo" => Some("{n}LIFO/{o}FIFO/{s}LIFO"),
            "dsep-lc" => Some("{n}LIFO/{o}LR/{s}LIFO"),
            "dunf-lifo" => Some("{n,s}0LIFO/{n,s}1LIFO/{o}LIFO/{n,s}LIFO"),
            "dunf-fifo" => Some("{n,s}0LIFO/{n,s}1LIFO/{o}FIFO/{n,s}LIFO"),
            "dunf-lc" => Some("{n,s}0LIFO/{n,s}1LIFO/{o}LR/{n,s}LIFO"),
            "dunf-gen" => Some("{n,s,o}0LIFO/{n,s,o}1LIFO/{n,s,o}LIFO"),
            "dres-lifo" => Some("{n,s}0LIFO/{o}LIFO/{n,s}LIFO"),
            "dres-fifo" => Some("{n,s}0LIFO/{o}FIFO/{n,s}LIFO"),
            "dres-lc" => Some("{n,s}0LIFO/{o}LR/{n,s}LIFO"),
            "dend-lifo" => Some("{o}LIFO/{n,s}LIFO"),
            "dend-fifo" => Some("{o}FIFO/{n,s}LIFO"),
            "dend-lc" => Some("{o}LR/{n,s}LIFO"),
            "lcfr" => Some("{n,s,o}LR"),
            "lcfr-dsep" => Some("{n,o}LR/{s}LR"),
            "zlifo" => Some("{n}LIFO/{o}0LIFO/{o}1NEW/{o}LIFO/{s}LIFO"),
            "zlifo*" => Some("{o}0LIFO/{n,s}LIFO/{o}1NEW/{o}LIFO"),
            "static" => Some("{t}LIFO/{n,s}LIFO/{o}LIFO"),
            "lcfr-loc" => Some("{n,s,l}LR"),
            "lcfr-conf" => Some("{n,s,u}LR/{o}LR"),
            "lcfr-loc-conf" => Some("{n,s,u}LR/{l}LR"),
            "mc" => Some("{n,s}LR/{o}MC_add"),
            "mc-loc" => Some("{n,s}LR/{l}MC_add"),
            // N.B. the upstream source has a typo here (`[u}` instead of `{u}`);
            // we implement the intended order so `MC-Loc-Conf` is usable.
            "mc-loc-conf" => Some("{n,s}LR/{u}MC_add/{l}MC_add"),
            "mw" => Some("{n,s}LR/{o}MW_add"),
            "mw-loc" => Some("{n,s}LR/{l}MW_add"),
            "mw-loc-conf" => Some("{n,s}LR/{u}MW_add/{l}MW_add"),
            _ => None,
        };
        if let Some(s) = expanded {
            return Self::parse(s);
        }
        Self::parse_criteria(name)
    }

    fn parse_criteria(name: &str) -> Result<FlawSelectionOrder, String> {
        let err = || format!("invalid flaw selection order `{name}'");
        let bytes = name.as_bytes();
        let mut order = FlawSelectionOrder {
            selection_criteria: Vec::new(),
            needs_pg: false,
            first_unsafe_criterion: i32::MAX as i64,
            last_unsafe_criterion: 0,
            first_open_cond_criterion: i32::MAX as i64,
            last_open_cond_criterion: 0,
        };
        let mut non_separable_max_refinements: i32 = -1;
        let mut separable_max_refinements: i32 = -1;
        let mut open_cond_max_refinements: i32 = -1;

        // Returns the byte at `p`, or NUL when past the end. The grammar tests
        // against ',' and '}' which never match NUL, so out-of-bounds silently
        // fails the next grammar check.
        let at = |p: usize| -> u8 { bytes.get(p).copied().unwrap_or(0) };

        let mut pos = 0usize;
        while pos < name.len() {
            if at(pos) != b'{' {
                return Err(err());
            }
            pos += 1;
            let mut c = SelectionCriterion {
                non_separable: false,
                separable: false,
                open_cond: false,
                local_open_cond: false,
                static_open_cond: false,
                unsafe_open_cond: false,
                max_refinements: i32::MAX,
                order: OrderType::Lifo,
                heuristic: RankHeuristic::Add,
                reuse: false,
            };
            let idx = order.selection_criteria.len() as i64;
            // Flaw-type letters.
            loop {
                match at(pos) {
                    b'n' => {
                        pos += 1;
                        if at(pos) == b',' || at(pos) == b'}' {
                            c.non_separable = true;
                            if order.first_unsafe_criterion > order.last_unsafe_criterion {
                                order.first_unsafe_criterion = idx;
                            }
                            order.last_unsafe_criterion = idx;
                        } else {
                            return Err(err());
                        }
                    }
                    b's' => {
                        pos += 1;
                        if at(pos) == b',' || at(pos) == b'}' {
                            c.separable = true;
                            if order.first_unsafe_criterion > order.last_unsafe_criterion {
                                order.first_unsafe_criterion = idx;
                            }
                            order.last_unsafe_criterion = idx;
                        } else {
                            return Err(err());
                        }
                    }
                    b'o' => {
                        pos += 1;
                        if at(pos) == b',' || at(pos) == b'}' {
                            c.open_cond = true;
                            c.local_open_cond = false;
                            c.static_open_cond = false;
                            c.unsafe_open_cond = false;
                            if order.first_open_cond_criterion > order.last_open_cond_criterion {
                                order.first_open_cond_criterion = idx;
                            }
                            order.last_open_cond_criterion = idx;
                        } else {
                            return Err(err());
                        }
                    }
                    b'l' => {
                        pos += 1;
                        if at(pos) == b',' || at(pos) == b'}' {
                            if !c.open_cond {
                                c.local_open_cond = true;
                                if order.first_open_cond_criterion > order.last_open_cond_criterion
                                {
                                    order.first_open_cond_criterion = idx;
                                }
                                order.last_open_cond_criterion = idx;
                            }
                        } else {
                            return Err(err());
                        }
                    }
                    b't' => {
                        pos += 1;
                        if at(pos) == b',' || at(pos) == b'}' {
                            if !c.open_cond {
                                c.static_open_cond = true;
                                if order.first_open_cond_criterion > order.last_open_cond_criterion
                                {
                                    order.first_open_cond_criterion = idx;
                                }
                                order.last_open_cond_criterion = idx;
                            }
                        } else {
                            return Err(err());
                        }
                    }
                    b'u' => {
                        pos += 1;
                        if at(pos) == b',' || at(pos) == b'}' {
                            if !c.open_cond {
                                c.unsafe_open_cond = true;
                                if order.first_open_cond_criterion > order.last_open_cond_criterion
                                {
                                    order.first_open_cond_criterion = idx;
                                }
                                order.last_open_cond_criterion = idx;
                            }
                        } else {
                            return Err(err());
                        }
                    }
                    _ => return Err(err()),
                }
                if at(pos) == b',' {
                    pos += 1;
                    if at(pos) == b'}' {
                        return Err(err());
                    }
                }
                if at(pos) == b'}' {
                    break;
                }
            }
            pos += 1; // consume '}'
                      // Optional max-refinements integer.
            let mut next_pos = pos;
            while at(next_pos).is_ascii_digit() {
                next_pos += 1;
            }
            if next_pos > pos {
                c.max_refinements = name[pos..next_pos].parse().map_err(|_| err())?;
                pos = next_pos;
            } else {
                c.max_refinements = i32::MAX;
            }
            // The order key runs up to the next '/' (or end).
            let key_end = name[pos..].find('/').map(|d| pos + d).unwrap_or(name.len());
            let key = &name[pos..key_end];
            let kl = key.to_ascii_lowercase();
            if kl == "lifo" {
                c.order = OrderType::Lifo;
            } else if kl == "fifo" {
                c.order = OrderType::Fifo;
            } else if kl == "r" {
                c.order = OrderType::Random;
            } else if kl == "lr" {
                c.order = OrderType::Lr;
            } else if kl == "mr" {
                c.order = OrderType::Mr;
            } else {
                if c.non_separable || c.separable {
                    // No other orders can be used with threats.
                    return Err(err());
                }
                if kl == "new" {
                    c.order = OrderType::New;
                } else if kl == "reuse" {
                    c.order = OrderType::Reuse;
                } else if let Some(rest) = strip_ci(&kl, "lc_") {
                    c.order = OrderType::Lc;
                    order.needs_pg = true;
                    parse_rank_heuristic(rest, &mut c, true).ok_or_else(err)?;
                } else if let Some(rest) = strip_ci(&kl, "mc_") {
                    c.order = OrderType::Mc;
                    order.needs_pg = true;
                    parse_rank_heuristic(rest, &mut c, true).ok_or_else(err)?;
                } else if let Some(rest) = strip_ci(&kl, "lw_") {
                    c.order = OrderType::Lw;
                    order.needs_pg = true;
                    parse_rank_heuristic(rest, &mut c, false).ok_or_else(err)?;
                } else if let Some(rest) = strip_ci(&kl, "mw_") {
                    c.order = OrderType::Mw;
                    order.needs_pg = true;
                    parse_rank_heuristic(rest, &mut c, false).ok_or_else(err)?;
                } else {
                    return Err(err());
                }
            }
            if c.non_separable {
                non_separable_max_refinements =
                    non_separable_max_refinements.max(c.max_refinements);
            }
            if c.separable {
                separable_max_refinements = separable_max_refinements.max(c.max_refinements);
            }
            if c.open_cond || c.local_open_cond {
                open_cond_max_refinements = open_cond_max_refinements.max(c.max_refinements);
            }
            order.selection_criteria.push(c);
            pos = key_end;
            if at(pos) == b'/' {
                pos += 1;
                if pos >= name.len() {
                    return Err(err());
                }
            }
        }
        // An incomplete flaw selection order (a flaw type whose every criterion
        // imposes a refinement limit) is rejected.
        if non_separable_max_refinements < i32::MAX
            || separable_max_refinements < i32::MAX
            || open_cond_max_refinements < i32::MAX
        {
            return Err(err());
        }
        Ok(order)
    }

    pub fn needs_planning_graph(&self) -> bool {
        self.needs_pg
    }

    /// Parsed criteria for search representations that implement their own
    /// flaw objects. SAS+ threats are ground and therefore non-separable, but
    /// the ordering and refinement-count rules are otherwise shared.
    pub(crate) fn criteria(&self) -> &[SelectionCriterion] {
        &self.selection_criteria
    }

    pub fn select(&self, plan: &Plan, ctx: &SearchContext, pg: Option<&PlanningGraph>) -> Flaw {
        let mut selection = FlawSelection {
            flaw: None,
            criterion: i32::MAX as i64,
            rank: 0.0,
            streak: 0,
        };
        let last_criterion = self.select_unsafe(
            &mut selection,
            plan,
            ctx,
            self.first_unsafe_criterion,
            self.last_unsafe_criterion,
        );
        self.select_open_cond(
            &mut selection,
            plan,
            ctx,
            pg,
            self.first_open_cond_criterion,
            self.last_open_cond_criterion.min(last_criterion),
        );
        selection
            .flaw
            .expect("select called on a plan with no selectable flaw")
    }

    /// Searches threats for a flaw to select. Returns the updated `last_criterion`.
    fn select_unsafe(
        &self,
        selection: &mut FlawSelection,
        plan: &Plan,
        ctx: &SearchContext,
        first_criterion: i64,
        mut last_criterion: i64,
    ) -> i64 {
        if first_criterion > last_criterion || plan.unsafes().is_none() {
            return i32::MAX as i64;
        }
        for u in chain::iter(plan.unsafes()) {
            if first_criterion > last_criterion {
                break;
            }
            // Cached per-flaw refinement counts (-1 = "not yet computed").
            let mut refinements: i32 = -1;
            let mut separable: i32 = -1;
            let mut promotable: i32 = -1;
            let mut demotable: i32 = -1;
            let mut c = first_criterion;
            while c <= last_criterion {
                let crit = &self.selection_criteria[c as usize];
                if crit.non_separable != crit.separable && separable < 0 {
                    separable = plan.separable(ctx, u);
                    if separable < 0 {
                        refinements = 0;
                        separable = 0;
                    }
                }
                let applies = (crit.non_separable && crit.separable)
                    || (crit.separable && separable > 0)
                    || (crit.non_separable && separable == 0);
                if applies {
                    let within = crit.max_refinements >= 3
                        || plan.unsafe_refinements(
                            ctx,
                            &mut refinements,
                            &mut separable,
                            &mut promotable,
                            &mut demotable,
                            u,
                            crit.max_refinements,
                        );
                    if within {
                        match crit.order {
                            OrderType::Lifo => {
                                selection.flaw = Some(Flaw::Unsafe(u.clone()));
                                selection.criterion = c;
                                last_criterion = c - 1;
                            }
                            OrderType::Fifo => {
                                selection.flaw = Some(Flaw::Unsafe(u.clone()));
                                selection.criterion = c;
                                last_criterion = c;
                            }
                            OrderType::Random => {
                                if c == selection.criterion {
                                    selection.streak += 1;
                                } else {
                                    selection.streak = 1;
                                }
                                if rand01ex() < 1.0 / selection.streak as f64 {
                                    selection.flaw = Some(Flaw::Unsafe(u.clone()));
                                    selection.criterion = c;
                                    last_criterion = c;
                                }
                            }
                            OrderType::Lr => {
                                let better = c < selection.criterion || {
                                    plan.unsafe_refinements(
                                        ctx,
                                        &mut refinements,
                                        &mut separable,
                                        &mut promotable,
                                        &mut demotable,
                                        u,
                                        (selection.rank + 0.5) as i32 - 1,
                                    )
                                };
                                if better {
                                    selection.flaw = Some(Flaw::Unsafe(u.clone()));
                                    selection.criterion = c;
                                    plan.unsafe_refinements(
                                        ctx,
                                        &mut refinements,
                                        &mut separable,
                                        &mut promotable,
                                        &mut demotable,
                                        u,
                                        i32::MAX,
                                    );
                                    selection.rank = refinements as f32;
                                    last_criterion = if refinements == 0 { c - 1 } else { c };
                                }
                            }
                            OrderType::Mr => {
                                plan.unsafe_refinements(
                                    ctx,
                                    &mut refinements,
                                    &mut separable,
                                    &mut promotable,
                                    &mut demotable,
                                    u,
                                    i32::MAX,
                                );
                                if c < selection.criterion || refinements as f32 > selection.rank {
                                    selection.flaw = Some(Flaw::Unsafe(u.clone()));
                                    selection.criterion = c;
                                    selection.rank = refinements as f32;
                                    last_criterion = if refinements == 3 { c - 1 } else { c };
                                }
                            }
                            _ => {}
                        }
                    }
                }
                c += 1;
            }
        }
        last_criterion
    }

    #[allow(clippy::too_many_arguments)]
    fn select_open_cond(
        &self,
        selection: &mut FlawSelection,
        plan: &Plan,
        ctx: &SearchContext,
        pg: Option<&PlanningGraph>,
        first_criterion: i64,
        mut last_criterion: i64,
    ) -> i64 {
        if first_criterion > last_criterion || plan.open_conds().is_none() {
            return i32::MAX as i64;
        }
        let predicates = &ctx.domain.predicates;
        let tctx = ctx.type_ctx();
        let mut local_id: usize = 0;
        for oc in chain::iter(plan.open_conds()) {
            if first_criterion > last_criterion {
                break;
            }
            if local_id == 0 {
                local_id = oc.step_id;
            }
            let local = oc.step_id == local_id;
            let mut is_static: i32 = -1;
            let mut is_unsafe: i32 = -1;
            let mut refinements: i32 = -1;
            let mut addable: i32 = -1;
            let mut reusable: i32 = -1;
            let mut c = first_criterion;
            while c <= last_criterion {
                let crit = &self.selection_criteria[c as usize];
                if crit.local_open_cond
                    && !local
                    && !crit.static_open_cond
                    && !crit.unsafe_open_cond
                {
                    if c == last_criterion {
                        last_criterion -= 1;
                    }
                    c += 1;
                    continue;
                }
                if crit.static_open_cond && is_static < 0 {
                    is_static = if oc.is_static(predicates) { 1 } else { 0 };
                }
                if crit.unsafe_open_cond && is_unsafe < 0 {
                    is_unsafe = if plan.unsafe_open_condition(ctx, oc) {
                        1
                    } else {
                        0
                    };
                }
                let applies = crit.open_cond
                    || (crit.local_open_cond && local)
                    || (crit.static_open_cond && is_static > 0)
                    || (crit.unsafe_open_cond && is_unsafe > 0);
                if applies {
                    let within = crit.max_refinements == i32::MAX
                        || plan.open_cond_refinements(
                            ctx,
                            &mut refinements,
                            &mut addable,
                            &mut reusable,
                            oc,
                            crit.max_refinements,
                        );
                    if within {
                        match crit.order {
                            OrderType::Lifo => {
                                selection.flaw = Some(Flaw::OpenCondition(oc.clone()));
                                selection.criterion = c;
                                last_criterion = c - 1;
                            }
                            OrderType::Fifo => {
                                selection.flaw = Some(Flaw::OpenCondition(oc.clone()));
                                selection.criterion = c;
                                last_criterion = c;
                            }
                            OrderType::Random => {
                                if c == selection.criterion {
                                    selection.streak += 1;
                                } else {
                                    selection.streak = 1;
                                }
                                if rand01ex() < 1.0 / selection.streak as f64 {
                                    selection.flaw = Some(Flaw::OpenCondition(oc.clone()));
                                    selection.criterion = c;
                                    last_criterion = c;
                                }
                            }
                            OrderType::Lr => {
                                let better = c < selection.criterion || {
                                    plan.open_cond_refinements(
                                        ctx,
                                        &mut refinements,
                                        &mut addable,
                                        &mut reusable,
                                        oc,
                                        (selection.rank + 0.5) as i32 - 1,
                                    )
                                };
                                if better {
                                    selection.flaw = Some(Flaw::OpenCondition(oc.clone()));
                                    selection.criterion = c;
                                    plan.open_cond_refinements(
                                        ctx,
                                        &mut refinements,
                                        &mut addable,
                                        &mut reusable,
                                        oc,
                                        i32::MAX,
                                    );
                                    selection.rank = refinements as f32;
                                    last_criterion = if refinements == 0 { c - 1 } else { c };
                                }
                            }
                            OrderType::Mr => {
                                plan.open_cond_refinements(
                                    ctx,
                                    &mut refinements,
                                    &mut addable,
                                    &mut reusable,
                                    oc,
                                    i32::MAX,
                                );
                                if c < selection.criterion || refinements as f32 > selection.rank {
                                    selection.flaw = Some(Flaw::OpenCondition(oc.clone()));
                                    selection.criterion = c;
                                    selection.rank = refinements as f32;
                                    last_criterion = c;
                                }
                            }
                            OrderType::New => {
                                let has_new = if addable < 0 {
                                    match oc.literal() {
                                        Some(literal) => {
                                            !plan.addable_steps(ctx, &mut addable, &literal, oc, 0)
                                        }
                                        None => false,
                                    }
                                } else {
                                    addable > 0
                                };
                                if has_new || c < selection.criterion {
                                    selection.flaw = Some(Flaw::OpenCondition(oc.clone()));
                                    selection.criterion = c;
                                    last_criterion = if has_new { c - 1 } else { c };
                                }
                            }
                            OrderType::Reuse => {
                                let has_reuse = if reusable < 0 {
                                    match oc.literal() {
                                        Some(literal) => !plan.reusable_steps(
                                            ctx,
                                            &mut reusable,
                                            &literal,
                                            oc,
                                            0,
                                        ),
                                        None => false,
                                    }
                                } else {
                                    reusable > 0
                                };
                                if has_reuse || c < selection.criterion {
                                    selection.flaw = Some(Flaw::OpenCondition(oc.clone()));
                                    selection.criterion = c;
                                    last_criterion = if has_reuse { c - 1 } else { c };
                                }
                            }
                            OrderType::Lc | OrderType::Mc | OrderType::Lw | OrderType::Mw => {
                                let pg = pg.expect("cost/work flaw order needs a planning graph");
                                let (h, _hs) = formula_value(
                                    pg,
                                    predicates,
                                    &tctx,
                                    plan,
                                    &oc.condition,
                                    oc.step_id,
                                    crit.reuse,
                                );
                                match crit.order {
                                    OrderType::Lc => {
                                        let rank = h.add_cost();
                                        if c < selection.criterion || rank < selection.rank {
                                            selection.flaw = Some(Flaw::OpenCondition(oc.clone()));
                                            selection.criterion = c;
                                            selection.rank = rank;
                                            last_criterion = if rank == 0.0 { c - 1 } else { c };
                                        }
                                    }
                                    OrderType::Mc => {
                                        let rank = h.add_cost();
                                        if c < selection.criterion || rank > selection.rank {
                                            selection.flaw = Some(Flaw::OpenCondition(oc.clone()));
                                            selection.criterion = c;
                                            selection.rank = rank;
                                            last_criterion = c;
                                        }
                                    }
                                    OrderType::Lw => {
                                        let rank = h.add_work() as f32;
                                        if c < selection.criterion || rank < selection.rank {
                                            selection.flaw = Some(Flaw::OpenCondition(oc.clone()));
                                            selection.criterion = c;
                                            selection.rank = rank;
                                            last_criterion = if rank == 0.0 { c - 1 } else { c };
                                        }
                                    }
                                    OrderType::Mw => {
                                        let rank = h.add_work() as f32;
                                        if c < selection.criterion || rank > selection.rank {
                                            selection.flaw = Some(Flaw::OpenCondition(oc.clone()));
                                            selection.criterion = c;
                                            selection.rank = rank;
                                            last_criterion = c;
                                        }
                                    }
                                    _ => unreachable!(),
                                }
                            }
                        }
                    }
                }
                c += 1;
            }
        }
        last_criterion
    }
}

/// Parses the heuristic suffix of an `LC_`/`MC_`/`LW_`/`MW_` order key.
/// `allow_makespan` is true for LC/MC but
/// false for LW/MW. Returns `None` on an invalid suffix.
fn parse_rank_heuristic(
    suffix: &str,
    c: &mut SelectionCriterion,
    allow_makespan: bool,
) -> Option<()> {
    let s = suffix.to_ascii_lowercase();
    if s == "add" {
        c.heuristic = RankHeuristic::Add;
        c.reuse = false;
        Some(())
    } else if s == "addr" {
        c.heuristic = RankHeuristic::Add;
        c.reuse = true;
        Some(())
    } else if allow_makespan && s == "makespan" {
        // Temporal; not supported in the classical subset.
        None
    } else {
        None
    }
}

/// Case-insensitive prefix strip. Returns the remainder if `s` (already
/// lowercased) starts with `prefix` (lowercase).
fn strip_ci<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
    s.strip_prefix(prefix)
}

/// Stub for the RANDOM order. Exact parity with any external RNG is not
/// required; returning a fixed value degenerates RANDOM to a stable LIFO-like
/// pick (streak logic always keeps the first match), which still yields valid plans.
fn rand01ex() -> f64 {
    0.5
}
