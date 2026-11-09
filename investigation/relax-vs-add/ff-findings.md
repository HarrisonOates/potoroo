# FF with potential action reuse in POCL

Investigation on `investigate/relax-vs-add`, 7 November 2026.

The corrected controlled comparison does not support replacing ADD with FF. Joint
FF extraction does, however, give a useful result on Parcprinter when combined
with ordering-aware reuse of existing steps. RePOP's previous source, binary,
and results are preserved; this investigation shifts to a separate FF baseline.

## What VHPOP proposes

[VHPOP §3.1.2](https://www.cs.cmu.edu/afs/cs/project/jair/pub/volume20/younes03a-html/node6.html)
distinguishes **existing actions** already in the partial plan from **potential
actions** that might be added later. Its modified additive heuristic considers
the former. FF's joint extraction can share the latter across subgoals. The
paper suggests evaluating FF in plan-space search; it does not supply a complete
POCL FF algorithm. It also explicitly cautions that possible existing reuse can
be overly optimistic.

Two opt-in native FDR rankings now make that comparison possible:

- `FF`: extract one relaxed plan for all outstanding open conditions, sharing
  potential future actions. The graph starts from the task's initial state.
- `FFR`: first omit each open-condition occurrence that an existing step could
  support under the current orderings, then perform the same joint extraction.
  This combines VHPOP's top-level existing-support check with FF extraction.
  A supporter eligible for one consumer does not make every occurrence free.

Both use parallel first-appearance levels, NOOPs first, and minimum summed
precondition levels for supporter choice, as described by
[Hoffmann and Nebel](https://arxiv.org/pdf/1106.0675), §§4.2–4.3. Effect marking
follows the author's [released FF-v2.3 source](https://fai.cs.uni-saarland.de/hoffmann/ff.html),
`relax.c::achieve_goals`: mark at the current layer and test equality with that
layer for both goals and preconditions. This allows support from an action
selected earlier at the same layer, while preserving already-regressed lower
requirements. Equal-level facts and tied operators use ascending indices. This differs from RELAX's additive-cost
achievers and RePOP's serial graph. Existing `CLFF` evaluates a causal-link
compilation using additive achievers; it is another relevant baseline.

The local [Fast Downward FF implementation](../../downward/src/search/heuristics/ff_heuristic.cc)
uses additive-cost propagation, recursively follows `reached_by` supporters,
and sums costs once per selected operator. It is therefore closer to our
existing RELAX's extraction than to the original FF level/difficulty selection.
It never removes previously regressed requirements through cross-layer effect
marking. This code comparison is not a claim that the two planners have
identical heuristic values or search behavior. The inspected revision and
source hashes are recorded in [ff-reference-code.json](ff-reference-code.json).
On the four-action support fixture below, the local FD binary reports initial
`h_FF=4`, while our corrected original-FF-style extraction selects three actions.
Both are executable estimates; supporter selection and sharing differ.

The first prototype incorrectly interpreted adjacent-layer markers so that a
later selected action could erase support needed by an earlier action. The
review found a four-action counterexample returning an unexecutable relaxed
plan. The correction follows FF-v2.3's explicit marker-lifetime distinction;
the counterexample now extracts an executable three-action plan. All original
90 measurements are marked [superseded](ff-initial-status.json) and preserved.
The tables below use a complete rerun with the corrected binary.

Implementation: [src/ff.rs](../../src/ff.rs), integrated in
[src/fdr_pocl.rs](../../src/fdr_pocl.rs). It currently supports unconditional,
axiom-free tasks with unit resolved action costs. It adds neither FF's
helpful-action pruning nor enforced hill climbing. `FFR` is an explicit
experimental adaptation, not an algorithm claimed to have been implemented
in VHPOP. Native `ADDR` also differs from VHPOP's formula: it seeds committed
effects at zero cost and propagates, without the per-consumer ordering check.

## Matched comparison on the original targets

All profiles use ZLIFO flaw selection, `/LIFO` ties, no optional pruning, one
release binary, and serial execution after compilation. Limits are 200,000
generated nodes, 10 seconds in the planner, a 15-second external watchdog, and
a 1 GiB per-process address-space cap. `w1` and `w5` use `g + w*h`; GBFS uses
the existing planner's greedy ranking and secondary ties.

The six targets are Gripper p01/p03, Miconic p01/p02, Childsnack p01, and
Elevators p02. They are deliberately selected ADD-only cases in the frozen
cluster snapshot. Both input hashes match the snapshot. Parcprinter p03 is
a separate control where cluster ADD and RELAX both solved.

| Profile | Six targets solved | Parcprinter p03 |
|---|---:|---:|
| ADD, w1 | 6/6 | node cap |
| ADDR, w1 | 0/6 | node cap |
| CLFF, w1 | 0/6 | node cap |
| FF, w1 | 0/6 | 70,933 nodes, cost 17 |
| FF, w5 | 2/6 | 32,441 nodes, cost 17 |
| FF, GBFS | 2/6 | time limit |
| FFR, w1 | 0/6 | **332 nodes, cost 17** |
| FFR, w5 | 0/6 | node cap |
| FFR, GBFS | 0/6 | time limit |

FF's two recoveries are both Gripper. Weight 5 generates 1,971/4,306 nodes,
with costs 77/117; ADD generates 3,083/6,553 with costs 59/89. Greedy FF generates
2,068/4,453 nodes, with costs 79/119. The weight-5 counts and costs match the
earlier RELAX experiment, so this Gripper recovery is not a new advantage
attributable to the paper-faithful extraction rules.

At weight 1, the FF-to-FFR comparison on Parcprinter reduces generated nodes
by about 214 times while preserving cost 17. It is a matched comparison of
the added existing-support filter. Raising the weight loses that benefit.
There is no evidence here that lower estimates or more reuse consistently
produce better search guidance.

## Probe in the domains discussed by VHPOP

To reduce dependence on the ADD-only selection, a second matrix uses the first
autoscale agile instance, p01, in each domain from VHPOP Table 1. These are
modern benchmark instances, not the paper's IPC3 problems. The nine profiles
and limits are unchanged; input hashes match available frozen cluster records.
The ZenoTravel RELAX record is absent from that snapshot, so its input check
uses ADD's record only.

| Domain p01 | ADD w1 | ADDR w1 | CLFF w1 | FF w1 | FFR w1 |
|---|---:|---:|---:|---:|---:|
| Driverlog | cap | timeout | cap | cap | cap |
| ZenoTravel | 176,869 / 28 | timeout | timeout | cap | cap |
| Satellite | 851 / 14 | 461 / 14 | 461 / 14 | 137,685 / 14 | 1,344 / 14 |

Cells with numbers are generated nodes / plan cost. Neither higher weight nor
GBFS solves Driverlog or ZenoTravel with FF/FFR. On Satellite, only FFR with
weight 5 additionally solves (1,315 nodes, cost 15); the remaining FF/FFR
weight-5 and GBFS profiles fail within the limits.

Existing-step reuse helps FF substantially on Satellite, but ADD and the two
existing reuse/compilation baselines still generate fewer nodes. Parcprinter
is the only tested case where FFR w1 wins against all three baseline profiles.

## Why a more accurate action count can still guide poorly

The original small witness is useful here: two goal actions both need `p`,
and a third action establishes `p`. Joint extraction correctly shares that
future producer. But after committing it for one goal, the estimate can charge
for it again as a prerequisite of the other, still-potential goal action.

The regression test now checks the same three partial plans:

| Ranking, weight 1 | Root | First goal action committed | Its producer committed |
|---|---:|---:|---:|
| ADD, `g+h` | 4 | 4 | 4 |
| RELAX, `g+h` | 3 | 3 | 4 |
| FF, `g+h` | 3 | 3 | 4 |
| FFR, `g+h` | 3 | 3 | 4 |
| REPOP, `g+h` | 3 | 3 | 3 |

`FFR` checks existing support only for current open conditions. It does not
make existing effects globally true during recursive extraction. Consequently,
it does not fix the committed-producer barrier when reuse occurs below the
current open-condition frontier. Conversely, a free existing supporter for a
current open condition may be optimistic about other threats and commitments.
The ordering check alone does not guarantee jointly usable support.

The witness proves a specific limitation of this adaptation; it does not prove
that the barrier caused every benchmark failure. The measured outcomes support
keeping ADD as the default and retaining FF/FFR as experimental comparisons.
A next investigation should test a relaxation that represents committed-step
support throughout extraction, while keeping consumer/order information, with
`CLFF` as a comparator. It should first pass this witness and preserve the
Parcprinter gain. Simply tuning weights further is not established as a remedy.

## Scope and evidence

These are deterministic, bounded probes, not a broad coverage study or timing
distribution. Input selection favours ADD on the six targets. Exact search
trajectories can depend on translator order, fact/operator ties, flaw selection,
and FDR encoding. A node or time limit is not proof that a heuristic cannot
solve an instance. These runs do not reproduce the original FF planner or
VHPOP's lifted search and flaw strategies.

All 90 corrected benchmark runs have final statistics and recorded provenance.
A transparent interpreter wrapper saves the actual translated SAS output for
all runs. Translator revision and Python-file hashes are recorded; all nine
profiles for a case must receive identical SAS hashes. The wrapper adds an
extra Python invocation equally to all profiles, so timings should not be
compared directly with the superseded matrix. The
initial validation passed 231 library tests (one diagnostic ignored),
13 CLI tests, the release build, and `git diff --check`. New tests cover shared
future producers, layer-local effect sharing, parallel levels,
difficulty-based support selection, unreachable goals, rejected task features,
preprocessing deadlines, order-incompatible reuse, self-support, per-occurrence
reuse filtering, and retention of committed steps' open preconditions. An additional deterministic
check executes extracted plans for 4,096 generated relaxed tasks and checks
their goals/reachability independently of graph markers.

Reproduction and audit artifacts:

- [ff_probe.py](ff_probe.py), [ff-corrected-manifest.json](ff-corrected-manifest.json),
  [ff-corrected.csv](ff-corrected.csv), [ff-corrected-provenance.json](ff-corrected-provenance.json).
- [summarize_ff.py](summarize_ff.py), [ff-corrected-summary.json](ff-corrected-summary.json),
  [ff-corrected-validation.json](ff-corrected-validation.json). The summary checks every row
  against its final log, source and binary hashes, limits, and input hashes.
- [ff-corrected-vhpop-domains.csv](ff-corrected-vhpop-domains.csv),
  [ff-corrected-vhpop-domains-provenance.json](ff-corrected-vhpop-domains-provenance.json).
- [ff-corrected-frozen.json](ff-corrected-frozen.json) records the archived measurement source and
  binary. The archived and recorded source snapshots agree for the corrected measurements.
- Raw process logs are under `target/relax-investigation/ff-corrected/` and
  `target/relax-investigation/ff-corrected-vhpop-domains/`.

Run `python3 investigation/relax-vs-add/ff_probe.py --run` after building the
release binary to reproduce the first matrix; add `--suite vhpop-domains` for
the second. Preserve the existing artifacts before rerunning. Defaults remain
ADD; `FF` and `FFR` are experimental options.

The fresh result-to-claim review accepted all seven scoped conclusions with high
confidence and found no remaining extraction defect in the supported task class.
Its read-only audit reported 1,691 checks, including all 378 artifact hashes.
Semantic acceptance remains provisional (same model family; exact serving
identity unknown); no formal `EXPERIMENT_AUDIT.json` exists. Full review:
[run04](../../.aris/traces/result-to-claim/2026-11-07_run04/001-review.response.md).
