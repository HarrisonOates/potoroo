# Lifted FDR POCL: phases 1–3 findings

November 2026, branch `investigate/relax-vs-add`. Design:
`docs/superpowers/specs/2026-11-08-lifted-fdr-pocl-design.md`. Opt-in as
`--lifted-fdr`. No existing planner is modified.

## Built

* **Task compiler** (`src/lifted_fdr/task.rs`, `invariants.rs`). It uses its own
  Helmert-style invariant synthesis. Unlike `lifted_mutex`, one schema may
  add into several instances that cannot co-designate, so sokoban's
  `at(?thing,·)` becomes a variable. Schemas are rewritten to conditions and
  assignments: deletes come before adds, and a delete paired with an add on
  the same instance is dropped. Schema variables are renumbered into disjoint
  global ranges, so `Bindings` types need no per-step registry.
  * **41/42 agile domains compile.** Pathways is rejected for a disjunctive
    precondition.
  * **Random walks** (applicability and successors) **agree with STRIPS** on
    every compiled p01.
  * **Variable covers are comparable to FD's translator.** Sometimes ours is
    larger: parking folds `curb-clear` in.
* **Plan model and refinements** (`plan.rs`).
  * **Threats** use the SAS⁺ clobbering test, made lifted.
  * **Resolutions:** demotion, promotion, disjoint separation, or agreement
    (bind the write to the protected value).
  * **Generalised arc consistency over static atoms**, per equality class,
    binding singletons. Without it, childsnack's plans co-designate one place
    for several children and fail only at grounding.
* **Search** (`search.rs`): A*. Every returned plan is grounded and then
  checked by an independent STRIPS simulation. The check has caught one
  grounding bug: co-designated variables in other steps were not re-checked.
* **ADD/ADDR** (`heuristic.rs`) through the lifted planner's planning graph.
  * **ADD has no reuse**, matching FDR `ADD`.
  * **ADDR reuse needs an entailed match.** Mere unifiability let one
    unbound `drop` discount every gripper goal (h 51 → 0).
* **Flaw selection** (`flaws.rs`) interprets Potoroo's flaw-order language,
  counting refinements as VHPOP does (separation counts once).

## Development panel: p01, 15 s, 2 GiB, `-h ADD`

Nodes generated (– = not solved):

| | gripper | childsnack | logistics | blocks | miconic | satellite | elevators | sokoban | rovers | zeno |
|---|---|---|---|---|---|---|---|---|---|---|
| ground FDR ZLIFO ADD | 3,083 | 5,859 | 4,107 | – | 2,650 | 851 | 754 | – | 2.15M | 176,869 |
| lifted ZLIFO | – | 5,260 | – | – | 2,119 | – | – | – | – | – |
| lifted LCFR | – | – | – | – | – | 404,565 | – | – | – | – |
| lifted forced-first LCFR-DSep | – | – | – | – | – | 406 | – | – | – | – |
| lifted DSep-LC | – | – | – | – | – | 727 | – | – | – | – |
| lifted LCFR-Loc-Conf | 838,259 | – | – | – | 2,047 | 145 | – | – | – | – |
| **lifted MW-Loc / MC-Loc** | 12,429 | 123,600 | – | – | 932 | 159 | – | – | – | 3,440 |

MW-Loc is now the default. Lifted beats ground FDR on satellite and on
zenotravel (51× fewer nodes). It loses gripper and childsnack by 4× and 21×.

## What mattered, in order

1. **Static arc consistency** (childsnack: unsolvable → 690 nodes under the
   old ZLIFO variant).
2. **ADD without reuse**, as FDR does (miconic: timeout → 2k nodes).
3. **Flaw selection.** Lifted goals look forced to ZLIFO because their single
   achiever has unbound parameters, so ZLIFO works breadth-first across goals.
   That leaves 100+ postponed threats whose CSP the heuristic cannot see
   (gripper, satellite). Local strategies (VHPOP `{l}`) fix this, as Younes &
   Simmons report for lifted VHPOP.
4. **Binding on insertion** (`POTOROO_LFDR_BIND=k`, default off): no gain at any
   k. Even fully ground, gripper did not solve under ZLIFO, so binding was
   not the problem.

## Open problems

* **Plateaus without threats** (logistics, elevators, rovers): thousands of
  plans of one shape at one f with few flaws. The likely cause is
  initial-state support for unbound conditions: there is one child per
  matching initial fact, and the heuristic cannot rank them. Diagnose next.
* **Throughput.** Static propagation recomputes domains per child, so logistics
  runs at about 10k nodes/s.
* **Not implemented yet:** PEA, per-queue portfolios, TADD/FLOW, forced-flaw
  propagation as a separate pass, and conditional effects.

## Update: initial-state tables, distinctness, binding as a flaw

* **Initial-state support is one child.** It carries a table constraint (the
  tuple must be an initial fact) inside the static arc consistency, instead
  of one child per matching fact. With ZLIFO, childsnack takes 546 nodes and
  elevators solves (72k nodes).
* **Hall check over non-codesignation.** Pairwise separations can be jointly
  unsatisfiable, e.g. six `turn_to` steps separated over two satellites. A
  greedy all-different check prunes these. It needs a read-only
  `Bindings::non_codesignated` accessor.
* **Bounded MAC feasibility** (`POTOROO_LFDR_MAC=n`, default 0) catches
  cross-step joint constraints that arc consistency misses (two satellites'
  images sharing one instrument variable). It solves satellite but costs
  3–12× per node, and it is unnecessary once bindings are flaws.
* **Binding as a flaw** (`POTOROO_LFDR_BINDFLAW`, default `threat`). Over the
  classes in separable threats, forward checking removes objects that leave
  some threat without a repair:
  * no object left: the plan dies;
  * one object left: the binding is forced and applied at once;
  * otherwise, once no open condition remains or the domain undercuts the
    selected flaw's repairs, the class minimising domain/threat-degree is
    bound, values that remove the most threats first.

| p01, nodes generated | ground FDR | lifted ZLIFO + threat | lifted MW-Loc + threat |
|---|---|---|---|
| gripper | 3,083 | 4,080 | 6,307 |
| childsnack | 5,859 | 491 | 15,454 |
| miconic | 2,650 | 2,119 | 932 |
| satellite | 851 | – | 159 |
| elevators | 754 | 5,006 | – |
| zenotravel | 176,869 | – | 3,426 |
| logistics | 4,107 | – | – |
| rovers | 2,152,095 | – | – |

Policies `never`, `end` and `lr` are each dominated by `threat`. The two orders
are complementary: the union covers 6/10, against ground FDR's 8/10.

## Update: why the panel stalled, and fixes

Diagnosed with `POTOROO_TRACE=N`, which now also prints the selected flaw.

1. **The heuristic ignored binding domains.** `at(rover0, ?w)` costs 0
   under a pattern minimum over all waypoints, even when `visible_from` has
   narrowed `?w` to distant ones. ADD now evaluates each condition over the
   classes' propagated domains, enumerating up to 512 combinations
   (`POTOROO_LFDR_HDOM=0` disables this).
   * Logistics solves for the first time (ZLIFO, 2,468 nodes; ground FDR
     4,107), and zenotravel improves under MW-Loc (3,426 → 2,009).
   * Elevators under ZLIFO regresses (5,006 → >3M nodes): a search-direction
     change, not cost.
2. **Throughput.** Phase timers (shown with `-v`) showed propagation
   dominating refinement and heuristic time.
   * Tables now have per-position indexes and a worklist.
   * Domains computed in refinement are handed to the heuristic once and
     dropped before queuing.
   * Speed-up 2–5×: elevators 30k nodes 18.5 s → 3.5 s; rovers 3.1 s → 1.4 s.
3. **Rovers remains.** The stall is ordering many consumers of
   `at(rover0)` against a chain of `navigate` steps. Ground FDR also needs
   2.15M nodes there, at about 800k nodes/s; we run at about 20k/s.

| p01 | hdom=0 MW-Loc | hdom=0 ZLIFO | hdom=1 MW-Loc | hdom=1 ZLIFO |
|---|---|---|---|---|
| gripper | 6,307 | 4,080 | 6,307 | 4,080 |
| childsnack | 15,454 | 491 | 15,454 | 491 |
| logistics | – | – | – | 2,468 |
| miconic | 932 | 2,119 | 1,495 | 4,116 |
| satellite | 159 | – | 159 | – |
| elevators | – | 4,952 | – | – |
| zenotravel | 3,426 | – | 2,009 | 550,540 |

The union is 7/10, against ground FDR's 8/10 (rovers). Blocksworld and
sokoban are unsolved by both.

## First screens: 420-task panel (p01–p10), 30 s / 2 GiB, 8 parallel

Baselines from `investigation/pocl-heuristic/` at the same budget: ground FDR
ZLIFO ADD/LIFO solves 88, FD A*/FF 118.

| build | solved | change |
|---|---|---|
| `6e8025a` (4 lanes) | 66 | first screen; 14 errors (pathways disjunctions, organic static goals) |
| `+` degree binding, static goals, DNF schemas | 80 | satellite 2 → 8, pathways 0 → 8 |
| `054231a` (5 lanes, per-lane `+deg`, symmetry) | 78 | childsnack 6 → 9; airport, gripper, logistics and visitall each lose 1–2 |

* All failures are timeouts (342 at `054231a`), none memouts: the opposite
  of ground FDR. Each extra lane divides the budget, and per-node cost is
  roughly 20–80× ground FDR's.
* **Complementary to ground FDR.** Lifted or ground solves 101/420, against
  FD's 118. Lifted-only tasks: zenotravel p04–p07 and p09, pathways p06–p08,
  depots p02, nomystery p01, pegsol p08, pipesworld-notankage p01, tpp p03.
* **Largest losses:** elevators 2 vs 6 (moves with unbound floors threaten
  every `lift-at` link of their lift), logistics, rovers, airport.

Per-domain levers found so far:

* **Degree binding** (bind a class whose domain is no larger than the
  separable threats it touches) is essential on satellite and fatal on
  childsnack, whose sandwiches must stay unbound. It is therefore a lane
  option.
* **Value-symmetry breaking must only prune children.** Letting it shrink the
  domain used for the binding decision made bindings look cheap and broke
  childsnack.

## Per-node speed (callgrind; `perf` is unavailable on this machine)

* **Before:** `propagate_domains` was over 60% of instructions, mostly SipHash
  on `HashSet<Object>` domains and support sets, plus malloc.
* **Changes:**
  * Domains are dense object bitsets in Fx maps.
  * Each class's initial domain comes from a cached per-type bitset minus
    its non-codesignated constants.
  * Term resolution is memoised per propagation.
  * Only negated statics are re-checked afterwards; the positive ones had
    been about 20% on their own.
  * Heuristic enumeration substitutes bound terms first.
* **Results:** same search, 1.4–2.3× faster (p03 at 30k nodes: elevators
  1.77 → 0.92 s, logistics 2.16 → 0.94 s). The search is also deterministic
  now.
* **Panel at `0b44576`:** 83/420, up from 78. Gained driverlog p01, gripper
  p09, logistics p03–p04, mprime p04, tetris p03 and visitall p01; lost
  airport p01 and childsnack p07. Lifted or ground FDR: 103.
* **What remains:** propagation is still about 58%, now dominated by
  `Bindings::find_var_node`: about 200 lookups per propagation at about 500
  instructions each, scanning the unindexed varset prefix. Further gains need
  either a cheaper class lookup or propagation that reuses the parent's
  resolution and domains.

## Local class-based bindings (`2346c5a`)

* **The change.** The shared VHPOP-style `Bindings` in lifted FDR plans is
  replaced by `LBindings`, a persistent slot/class structure.
  * Each step variable has a slot.
  * Each class keeps its constant, its domain as a bitset, the classes it
    must differ from, and its members.
  * Resolution is two array reads.
  * Binding a class forward-checks its distinct classes, and a class left
    with one object is bound.
  * Propagation writes narrowed domains back, so later propagation starts
    from them, and binding flaws and the heuristic read domains directly.
  * `src/bindings.rs` is back to its pre-branch state.
* **Per node:** 2–3× faster (p03 at 30k nodes: elevators 0.96 → 0.48 s,
  rovers 0.77 → 0.41 s, gripper 0.36 → 0.11 s). The search changes slightly
  because domain maintenance is now eager.
* **Panel, 30 s / 2 GiB:**
  * **98/420**, ahead of ground FDR ZLIFO ADD (88). FD A*/FF: 118.
  * Gained 17: airport p01, p02 and p04; childsnack p07; data-network p01;
    depots p07; driverlog p05; gripper p10; nomystery p04, p06 and p09;
    openstacks p02; pipesworld-tankage p03; storage p06; tpp p07;
    zenotravel p02 and p08.
  * Lost satellite p04 and p07.
* **Lifted or ground FDR: 116/420**, against FD's 118.
* **Memory now matters.** There are 33 memouts, up from 3, so the faster
  search now reaches the 2 GiB limit.

## Memory: compaction (`17dc876`) and the calibrated ratio

* **Compaction, profiled with massif.**
  * Plan steps and the binding tables are persistent chunked vectors
    (16-entry chunks behind `Rc`).
  * Classes link to the class they merged into instead of listing members.
  * Small object sets are stored inline.
  * Links, opens and threats use `u32` step ids.
  * Same search, 18–21% less peak memory. What remains: class clones from
    forward checking (36%) and threat-chain prefix copies on removal (23%).
* **Calibrated ratio, 225 s / 1 GiB** (the cluster's 1,800 s / 8 GiB; 420
  tasks, 6 parallel):
  * Lifted FDR solves **105**, against ground FDR ZLIFO ADD 90 and the
    `port3c` FDR portfolio 121. Lifted or `port3c`: **143**.
  * Lifted is **memory-bound**: 295 memouts at a median of **29 s** of 225,
    with 266 before 112 s. Time is mostly unused, so time-for-memory
    trades (rebuilding queued children from recipes) pay at this ratio,
    though at 30 s / 2 GiB they would not.
  * Lifted wins nomystery 7–0, zenotravel 7–1, driverlog 4–1, tpp and
    openstacks. `port3c` wins elevators 10–2, depots, rovers, satellite and
    pathways.

## Recipes, speed and memory (to `8c9d79f`)

* **Recipes** (`bf4e828`). Queued children are kept as (parent expansion,
  choice) and rebuilt on pop.
  * Identical search, 40–68% less memory.
  * 375-task calibrated fragment (225 s / 1 GiB): **108 solved**, against 96
    without recipes. 169 memouts and 98 timeouts, against 266 and 13.
* **Incremental, allocation-free propagation** (`b2d6000`).
  * Recipes now cost about what the build without them did.
  * Same fragment: **109** (gained logistics p08). Faster runs reach the
    memory limit sooner: 203 memouts, 63 timeouts.
  * With `port3c` (117 alone): 142.
* **Copy-free class merges** (`8c9d79f`): −3 to −9% memory, identical
  searches.
* **Measured and dropped:**
  * *Threat-list compaction.* Removals copy only 2–6 nodes on average.
  * *Queue entries.* Already 32 bytes.
  * *Allocator overhead.* RSS minus the binary's footprint matches the live
    heap.
* **Chained recipes with a plan cache: rejected.**
  * Each expansion recorded its origin, and built parents were kept only
    while cached (fixed size, or evicted under address-space pressure).
  * A fixed cache cuts memory 3–4× but rebuilds 20–74% of expansions; at
    1024 plans nomystery needed 59M rebuilds.
  * Chain records add 9–22% even with nothing evicted.
  * Under 300 MB: logistics p06 still solves (55 s against 51 s), but
    **nomystery p05 times out where `8c9d79f` solves in 71 s**, and
    elevators p03 only turns a memout into a timeout.
  * Non-local pops make rebuild chains too expensive, and the overhead
    triggers eviction in runs that would have fit.

## Regressions, elevators and memory (November 9, `e132009`–`b556868`)

New screen: 420-task panel at **10 s / 1 GiB**, 6 parallel
(`target/lfdr/screen/s10.sh`). The reference is the `65d2ac9` search: 89.

| build | solved | change |
|---|---|---|
| `65d2ac9` | 89 | reference |
| + stale threats dropped, joint binding feasibility (child check) | 85 | satellite +4, but 1.31× time |
| + feasibility at expansion with inherited witnesses (`e132009`, v2) | 100 | time 0.55× |
| + forced threats in place (v3) | 110 | elevators, data-network, visitall |
| + batched forcing, pairwise option counts (`ffae936`, v5) | 111 | openstacks p02 back |
| + dead new threats dropped on generation (`b556868`, v6) | **113** | no losses against `65d2ac9`; time 0.42× |

* **The satellite regression was not a bug.** `LBindings` correctly rules out
  a reuse that the old `Bindings` counted, so ZLIFO picks a different flaw.
  The real failure is a **jointly infeasible binding CSP**.
  * Classes of different steps (satellite, instrument, direction) pass
    arc consistency and Hall's check but have no common solution.
  * A plan with no flaws left then fails grounding. Its `NewStep` sibling
    keeps the same core and adds a `turn_to`, so the subtree is infinite.
  * In p04 there were 64k expansions at f=33 with h=0.
* **Joint feasibility check.** Every expanded plan gets a bounded check of
  its binding constraints. It relaxes threats and orderings, so it is sound.
  * The parent's solution (a persistent `Witness`) is repaired first, by
    table lookups over the classes it no longer fits.
  * If that fails: a fresh search by table lookups, then MAC, which can
    prove infeasibility.
  * Results: satellite p04 0.02 s, p07 0.09 s, p08 0.10 s, p10 0.33 s, all
    unsolved before. Overhead is 2–8%.
  * Checking every generated child instead costs 12–30%, with the same
    coverage.
* **Stale threats were most of the nodes.**
  * In elevators p03, 992k of 1.24M expansions refined a threat that
    orderings or bindings had already removed, giving one `Drop` child.
  * Dropping them at expansion cuts wall time 2–3× on the same search.
* **Forced threats.** A threat with at most one resolution is applied in
  place at expansion; one with none kills the plan.
  * This mostly fixes elevators. Binding the passenger of a
    `board(?p, lift, …)`, added for the lift's passenger count, to an
    already-served passenger leaves threats that each have one ordering
    and are jointly impossible. Before, each cost a search node.
  * Elevators p03 under ZLIFO@ADD: 472k → 56k nodes (ground FDR: 22k);
    p04 12.8 → 3.3 s.
  * Forced orderings are applied directly and the threat list is rebuilt
    once per round: openstacks plans carry up to 856 threats.
* **Dead new threats.** A child whose newly added threats include one with
  no resolution is dropped before ranking: elevators p04 (5 lanes)
  18.1 → 10.7 s, nomystery p04 5.9 → 4.2 s.
* **Memory.** Witnesses were 49% of peak heap. As chunked persistent `u32`
  vectors shared with the parent's, rovers p01 at 3M generated nodes drops
  from 1.16 GB to 0.64 GB.
* **Systematic threat resolution (measured, dropped).** Ordering separation
  and agreement children between the link's ends would make threat children
  disjoint. In practice no separation or agreement child is ever generated:
  separable threats are settled by binding flaws, and definite ones only
  have demote/promote, which are already disjoint.
* **Still open.** Depots p04–p06 stall at h≈20 early: ADD gives too little
  guidance, where ground `port3c` has TADD/FLOW and deferral. Rovers, and
  pathways p09–p10, are unchanged.

Diagnostics: `POTOROO_LFDR_PROGRESS` (each lane's new lowest h),
`POTOROO_LFDR_DUMP=N,…` with `POTOROO_TRACE` (full plan at expansion N),
per-child rank lines in the trace, and `-v` timers for forcing and
feasibility. Knobs: `POTOROO_LFDR_FEAS=off|H[:BUDGET]`, `POTOROO_LFDR_FEASPOP=0`,
`POTOROO_LFDR_FORCE=N`, `POTOROO_LFDR_STALE=0`, `POTOROO_LFDR_NEWDEAD=0`.

### Calibrated result for v6 (`b556868`)

* **123/375** at 225 s / 1 GiB, against 109 for `b2d6000` and 117 for the
  ground `port3c` portfolio. Lifted or `port3c`: 147.
* **Gained 15:** satellite p04, p07, p08 and p10; elevators p04, p07, p09
  and p10 (now 9/10); data-network p02, p04 and p05; driverlog p07;
  nomystery p08; pathways p10; pipesworld-notankage p08.
* **Lost 1:** pegsol p03.
* **`port3c` still leads** on depots (4–9), rovers (1–7), parcprinter
  (4–7), pegsol (4–6), and by one each on elevators, mprime, pathways,
  storage, freecell and sokoban.
* Failures are still mostly memory: 209 memouts, 43 timeouts.

## Lifted TADD (`508da7f`, `2d7c686`)

* **What it counts.** A committed step that requires and overwrites an
  instance's value needs its own segment of that value; so does a goal on
  that variable.
* **Lifted version: bipartite matching.** Supplies are initial values and
  committed writes that may unify with a demand and may precede it.
  * Demands left unmatched by a maximum matching cost their variable's
    cheapest writer.
  * Ground TADD's per-fact counts are the special case with every fact
    known. The matching also uses orderings, which ground TADD ignores.
  * Sound as a lower bound: orderings, bindings and the other variables are
    relaxed.
* **Grouping is too weak.** First tried: grouping destroyers only when their
  resolved terms are identical, as the per-fact ground counts would. It
  almost never fires (depots: mean child h 29.81 vs ADD's 29.84).
* **Matching, ZLIFO@TADD vs ZLIFO@ADD:**

  | task | ZLIFO@ADD | ZLIFO@TADD |
  |---|---|---|
  | elevators p03 | 55,579 nodes | 5,537 nodes |
  | elevators p04 | 123,669 nodes | 7,349 nodes |
  | elevators p06 | fail | 1.8 s |
  | pegsol p05 | 400,688 nodes | 172,624 nodes |

  * Ground FDR needs 22k nodes on elevators p03.
  * Depots, rovers, sokoban and logistics are unchanged. Per-node overhead
    is about 20% after indexing supplies by variable, value and first
    instance object.
* **Lane screen, 10 s.** Default lanes with ZLIFO@TADD in place of
  ZLIFO@PADD: 114 vs 113. Gains elevators p04 and p06, loses nomystery p09.
* **Depots needs FLOW.** On the ground side, depots p04 is solved by the
  deferred-ZLIFO@FLOW queue (9 s) and the LC20@HYB queue (1.4 s), not by
  TADD queues. Counting matching initial facts as refinements, so that
  `{o}20` deferral applies to lifted conditions, did not help (dropped).
  * Porting FLOW needs ground domain-transition distances per variable
    instance. With unbound steps relaxed away, its infeasibility pruning
    would no longer be sound.
