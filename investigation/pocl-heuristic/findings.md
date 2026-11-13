# Closing the gap to Fast Downward: token-aware plan ranking

Branch `investigate/relax-vs-add`, November 2026. Goal: a plan-selection
heuristic (and flaw selection if needed) bringing FDR POCL coverage within
40–50 solves of Fast Downward A*/FF (cluster: FD 278, FDR ADD/LIFO 193 of 1,260).

RESULTS_PLACEHOLDER

## Diagnosis

Cluster FDR ADD/LIFO failures are almost all allocation failures after
60–90 M generated plans. On the 420-task panel (p01–p10 of every domain) the
cluster gap is FD 168 vs ADD 97: 71 of the 85-solve suite gap. FD solves many
of these with tiny searches (pegsol p13: 50 expansions; parcprinter: plan length
+ 1; data-network p01: 10), so the POCL failures are guidance and memory
failures, not hardness. Traces (`POTOROO_TRACE=N`) show three mechanisms:

1. **Consumed values are free to ADD.** A precondition true initially costs 0
   however many steps overwrite it. In pegsol every jump consumes `move-ended`
   and two pegs; in sokoban the player position; in organic synthesis the
   `procnone` lock. ADD cannot see that a second consumer needs a new producer.
2. **Overcounting of shared support.** Initial ADD for parcprinter p05 is 152
   against a 25-step plan (every `Available` precondition re-charges
   `initialize`); organic synthesis p20: 188 vs 22; thoughtful p13: 409 vs 93.
3. **Wrong commitment order.** ZLIFO develops each parcprinter sheet's route to
   the feeder before ever looking at the `hasimage` goal, so routes are
   committed blind and the print step later cannot be fitted.

Plus the memory mechanism: each expansion queues every refinement (253 for
pipesworld's `normal(s12)` lock), and A* touches few of them.

## What was built

All opt-in; defaults and published configurations are unchanged.

* **Value tokens (`src/token.rs`, `-h TADD`).** Each write to a variable ends
  one segment of its history, and a step that requires `v = a` and overwrites
  it needs its own segment of `a`; two links from one production of `a` to two
  such steps threaten each other both ways. Per fact, counted over committed
  steps: `destroyers + [goal] <= [init] + producers`. TADD adds to ADD the
  shortfall times the fact's reproduction cost (cheapest achiever plus additive
  costs of its other-variable preconditions), not double-charging open
  occurrences ADD already prices. Infinite when a shortfall has no producer.
* **Token flow (`src/flow.rs`, `-h FLOW`).** The same segment view per variable
  as a transportation problem: committed steps, the initial state and the goal
  fix each value's surplus or deficit; new steps move tokens along domain
  transition graph edges priced at operator cost plus additive costs of other
  preconditions. Min-cost flow per variable (successive shortest paths), summed;
  prevail conditions are charged once per distinct fact when no committed step
  produces them. No feasible flow proves the plan has no completion (orderings
  and other variables relaxed), so such plans are pruned soundly.
* **`HYB` = TADD + ½ FLOW** (`POTOROO_HYB` selects other mixes for experiments).
* **Per-queue heuristics (`-f ORDER@HEURISTIC`).** Interleaved flaw-order queues
  (existing round-robin with doubling budgets) can each rank by their own
  heuristic: an alternation portfolio within one search and memory budget.
  Queues whose heuristic does not support the task are dropped.
* **Partial-expansion A\* (`--pea`).** Yoshizumi, Miura & Ishida (AAAI 2000):
  queue only the children whose f equals the plan's current f, re-queue the plan
  at its next child f. Same expansion order as A* up to ties (the test checks
  optimal costs with LM-cut); 3–100× fewer queued plans at similar wall time.

* **Deferred high-branching open conditions (flaw selection).** Counter and
  lock facts (freecell's `colspace`/`cellspace`, pipesworld's `normal(s)`,
  depots' hoists, organic synthesis' `procnone`) have 200–390 achievers, and
  ZLIFO or least-cost-first selection commits to one early. Selecting first
  among open conditions with at most 20 refinements, and only then the rest
  (`{o}20LIFO/{o}LIFO` or `{o}20LC_add/{o}LC_add` in the existing flaw DSL),
  keeps those choices until the plan's structure constrains them. This solves
  pipesworld p01 and depots p04–p10, which nothing else did.

The recommended configuration (`port3c`):

```
--fdr-pocl -s A --pea \
  -f 'ZLIFO@TADD/LIFO' \
  -f '{n}LIFO/{o}0LIFO/{o}1NEW/{o}20LIFO/{o}LIFO/{s}LIFO@FLOW/LIFO' \
  -f '{n}LIFO/{o}0LIFO/{o}1NEW/{o}20LC_add/{o}LC_add/{s}LIFO@HYB/LIFO'
```

The TADD queue keeps plain ZLIFO, which the ADD-friendly domains need
(elevators loses with deferral). The third queue uses least-cost open
condition first, which fixes the parcprinter commitment order (p05: 3k nodes)
and helps freecell, pathways and rovers.

## Things that did not work

* `TADD2` (prevail conditions charged once per fact): loses miconic and
  logistics — ADD's repeated charges for e.g. truck locations reflect real
  repeated visits.
* `HYB` alone and FLOW alone: strong on pegsol/pathways/visitall/childsnack, but
  lose airport and elevators (FLOW's edge costs inflate airport's f to 306 vs
  101 and drive a wrong greedy dive).
* `FLOW0` (edges at operator cost): initial estimates collapse (sokoban 2 vs
  33). `FLOWM` (h_max edge costs): estimates much closer to plan lengths but
  search no better than FLOW.
* Tie-breaking by h or open-condition count; LCFR, LR and MC flaw orders on
  lock-heavy domains (pipesworld, sokoban, snake, tidybot, parking, grid).
* Fourth queues (FFR, weight-3 TADD, ZLIFO20@TADD): neutral at 10 s and at the
  calibrated budget. Per-queue weights (`ORDER@H*W`) remain available.
* LAMA-style boosting of a queue that reaches a new best h, and FF
  preferred-achiever tie-breaking: no gain; removed.
* Weight 2–3 on the whole portfolio: collapses some rovers/logistics searches
  but gives nothing on the FD-only domains.
* `-p cutset,edelete,disjunctive` on top of the portfolio: mixed.

## Remaining gap

Domains where FD wins by state-space duplicate detection under weak or
misleading h remain out of reach: sokoban (initial f 6 vs 33), pipesworld (lock
variables with ~250 achievers), thoughtful, snake, tidybot, parking, and
counter-heavy data-network. POCL partial plans have no duplicate detection, so
an underestimating A* must exhaust a far larger space than FD's state space.

## Reproduction

`run.py` (one config, JSONL), `spot.py` (side-by-side), `summarize.py`.
Panel: `panel10.txt`. Cluster references: `cluster-solved.json`.
Calibrated protocol: 1 GiB / 225 s per run (the cluster's 1,800 s / 8 GiB
ratio); see `calib.sh`. Screens: `screen*.sh` at 10 s / 1 GiB.
