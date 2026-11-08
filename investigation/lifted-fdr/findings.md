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
