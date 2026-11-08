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
