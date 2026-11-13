# Testing the published Relax recurrence

Follow-up on branch `investigate/relax-vs-add`, 7 November 2026.

The new `REPOP` heuristic fixes the committed-producer witness, but changing
the recurrence alone does not recover the six selected cluster failures.
Combining it with weight 5 and LIFO open-condition selection recovers both
Miconic cases. The old RELAX still fails those cases with the same settings.
The recovered plans are longer than ADD's plans. These results support a
configuration-dependent improvement, not a general replacement for ADD.

## Implementation and scope

[src/repop.rs](../../src/repop.rs) implements the §3 recurrence from
[Nguyen and Kambhampati (2001)](https://rakaposhi.eas.asu.edu/ucpop-revive.pdf#page=3)
over native FDR facts:

- Build a serial planning graph from the initial state. Synchronous pair
  reachability layers account for competing needs, inconsistent support,
  action/persistence interference, and mutual exclusion of distinct real actions.
- Select an outstanding fact with greatest first-appearance level, and an
  achiever present at that first layer.
- Regress with `(S union preconditions(action)) minus effects(action)`.
- Charge zero for an operator already committed to the partial plan, one
  otherwise. Still regress through committed actions' preconditions.

The implementation does not use RELAX's cached additive achievers, permanently
mark requested facts achieved, or make every committed effect initially true.
The committed-producer test now gives `g+h = 3, 3, 3`; the legacy RELAX witness
remains `3, 3, 4`.

The paper leaves ties unspecified. This implementation chooses descending fact
index for equal levels, then prefers committed earliest-layer achievers, then
translator operator order. It rejects conditional effects, axioms, and non-unit
resolved action costs. All selected inputs satisfy these restrictions without
changing their costs.

This is a native FDR implementation of the published heuristic recurrence,
not an exact reproduction of the original Lisp planner. Grounding, the FDR
encoding, unspecified ties, and refinement ordering can affect search. `REPOP`
is opt-in; `RELAX`, `RELAXR`, and the ADD default retain their previous behavior.
The label names the heuristic, not the entire RePOP system.

## Controlled comparison

Six targets were selected from the frozen snapshot's **ADD-only FDR solves**:
Gripper p01/p03, Miconic p01/p02, Childsnack p01, and Elevators p02. Parcprinter
p03 is a separate control where both cluster configurations solved and RELAX
generated fewer nodes. Local PDDL hashes match both cluster records for each
case. Selection is deliberate, not a random benchmark sample.

The main and control sweeps use one binary, serial execution, A* ranking,
`/LIFO` queue ties, 200,000 generated nodes, a 10-second planner deadline,
15-second external watchdog, and a 1 GiB per-process address-space cap.
Compilation finished before measurements started. `UCPOP` flaw selection means
`{n,s}LIFO/{o}LIFO`; its open-condition selection matches the paper's LIFO
choice. It is separate from the queue's `/LIFO` tie-breaker.

`CE` below is Potoroo's existing `-p cutset,edelete,disjunctive,h2`. The h2
preprocessing completed in every CE run; no incomplete mutex table was used.
This tests the existing consistency machinery alongside the recurrence rather
than reproducing every implementation detail of the original planner.

Entries are generated nodes on successful runs; a dash is a resource-limited
failure. `Z` means ZLIFO and `U` means UCPOP/LIFO open-condition selection.

| Problem | ADD, w1 Z | RELAX, w1 Z | REPOP, w1 Z | REPOP, w5 U | REPOP, w5 U + CE |
|---|---:|---:|---:|---:|---:|
| Gripper p01 | 3,083 | — | — | — | — |
| Gripper p03 | 6,553 | — | — | — | — |
| Miconic p01 | 2,650 | — | — | 2,078 | 2,871 |
| Miconic p02 | 5,991 | — | — | 3,836 | 4,970 |
| Childsnack p01 | 5,859 | — | — | — | — |
| Elevators p02 | 8,449 | — | — | — | — |
| Parcprinter p03 (control) | — | 64,299 | 5,216 | — | 119,356 |

Important controls:

- REPOP with **ZLIFO** solves none of the six targets at either weight 1 or 5.
- REPOP with **LIFO at weight 1** also solves none. The Miconic gains require
  both the higher weight and changed flaw order in this tested matrix.
- Old RELAX at weight 5 still fails both Miconic cases with ZLIFO, LIFO, and
  LIFO plus CE. Its Gripper solves are already recovered by weight 5 alone,
  whereas REPOP fails those cases under the tested settings.
- Miconic solution costs are **61 vs ADD's 56** on p01 and **79 vs 70** on p02.
  CE preserves those REPOP costs and increases generated nodes on these cases.
- ADD with weight 5, LIFO, and CE solves all six targets, and also solves the
  Parcprinter control in 751 generated nodes. The CE/control settings therefore
  do not themselves prevent solutions.
- Parcprinter benefits from REPOP at weight 1: 5,216 nodes with ZLIFO, or 1,893
  with LIFO, versus 64,299 for baseline RELAX, all with cost 17. Raising the
  weight to 5 loses this solve under the same limits until CE is enabled.

These are node-count and outcome comparisons. A single run per configuration
does not estimate timing variance. Capped runs do not establish eventual
failure under the cluster's larger budget.

## Extended budgets

The four still-unsolved targets were rerun with REPOP, weight 5, UCPOP/LIFO,
and CE, allowing 2,000,000 generated nodes, 60 seconds inside the planner,
a 65-second watchdog, and 2 GiB per-process address space. None solved:

| Problem | Outcome | Generated nodes | Wall seconds |
|---|---|---:|---:|
| Gripper p01 | Time limit | 849,637 | 60.178 |
| Gripper p03 | Time limit | 353,594 | 60.067 |
| Childsnack p01 | Node limit | 2,000,000 | 8.602 |
| Elevators p02 | Node limit | 2,000,000 | 30.824 |

These runs establish that the remaining deficit is not just a marginal miss
at the initial 200,000-node cap. They still do not reproduce the original
RePOP planner's reported coverage, nor prove that a larger run or different
unspecified achiever ties cannot solve these tasks.

## Reproduction and validation

```sh
cargo test --release --lib
cargo test --release --bin potoroo
cargo build --release --bin potoroo
python3 investigation/relax-vs-add/repop_probe.py --run
python3 investigation/relax-vs-add/repop_probe.py --suite controls --run
python3 investigation/relax-vs-add/repop_probe.py --suite extended --run
python3 investigation/relax-vs-add/summarize_repop.py
```

The library suite passed **222 tests, with 1 diagnostic ignored**; the binary
suite passed **13 tests**. New coverage checks shared effects, free committed
actions with outstanding preconditions, serial mutex delays, permanently
incompatible preconditions, earliest-layer achievers, unsupported inputs,
preprocessing deadlines, and the previous committed-support witness. The
production search validates each returned plan by linearization and execution.

All **81 runs** produced final statistics with no setup errors. The six
baseline ADD runs reproduced the frozen cluster's generated-node counts.

See [main results](repop.csv), [matched controls](repop-controls.csv),
[extended runs](repop-extended.csv), and [summary](repop-summary.json).
Manifests record every command and budget; the three provenance JSON files
record source and binary hashes and cluster-matching input hashes. Full logs
are under `target/relax-investigation/repop*`; their hashes are in the summary.

The exact tested source and binary were frozen before subsequent FF work;
[archive references and hashes](repop-frozen.json) preserve their identity.
The result-to-claim reviewer independently checked the recurrence, all 81 final
statistics records, and artifact/input hashes. The scoped conclusions are
supported; no additional RePOP experiments were requested. Assurance remains
provisional (same-family review, serving identity unverified; no formal integrity
audit). See the [review](../../.aris/traces/result-to-claim/2026-11-07_run02/001-review.response.md).
