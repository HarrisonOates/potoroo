# Full compilation and occurrence-sensitive FF

7 November 2026, `investigate/relax-vs-add`.

**Historical first batch.** Review found finite u32 cost saturation was treated
as unreachable in native compiled FF and, for large costs, LM-cut. The 80-run
batch and archive below are preserved; corrected reruns supersede compilation
interpretation. FFOC itself was unaffected. See [the corrected follow-up report](compiled-ff-corrected-findings.md).

`FFOC` recovers all six selected ADD-only failures of joint FF. It does not
outperform ADD on the ten-case panel. Full compilation, after correcting cost
accounting, fails on the six targets with either FF or LM-cut under these limits.
Both compiled backends solve Parcprinter, especially efficiently with LM-cut.

## Implementation and mechanism

`FFOC` sums a separate FF relaxed-plan size for **each open-condition occurrence**.
The same fact required by two consumers contributes twice. Within each support
plan, actions still share their effects in the FF extraction. Single-fact costs
are cached because the graph still starts from the original initial state.
This is an experimental POCL adaptation, not original FF search or a claim that
VHPOP implemented it. It accepts unconditional, axiom-free, unit-cost tasks.

The original `FF` extracts jointly across all open facts. This can merge repeated
support demands and share actions between consumers without representing all
compatibility constraints. ADD preserves separate contributions. The recovery
with FFOC supports retaining that distinction, but does not isolate duplicate
fact merging from other cross-demand sharing or explain every failure. The
initial-state graph itself remains unchanged; replacing it is not necessary for
the observed recovery. A unit fixture has `{} -> {a,b}` and `{a,b} -> c`:
ADD(c)=3 and FF(c)=2; two occurrences of c contribute 4 in FFOC, but 2 in joint FF.

`COMPILE_FF` and `COMPILE_LMCUT` now support native FDR POCL. Each evaluation
builds a task with separate mandatory occurrences, execution markers, full
committed ordering closure, and causal-link protection guards. Original actions
remain available for insertion. The compiled task starts from the original world
state, since POCL commitments have not yet been executed. Native compiled FF
uses additive-cost supporters through `cl_relax`; LM-cut uses the existing native
evaluator. FF supporter ties need not match FD's binary, and this is not a
bit-for-bit FD comparison or a reproduction of the paper's experiments.

Both native and literal compiled rankings use
`g + w * max(h_compiled - g, 0)`; greedy ranking omits g. Literal SAS and PDDL
output now carries resolved action costs, including zero costs, instead of
forcing every action to cost one. Ground instances use exact costs. Lifted
parameterized costs retain the planner's schema lower-bound convention. Native
compilation currently rejects conditional effects and axioms.

The [earlier diagnostic](compilation-findings.md) records the original bug.
Its original test/output are preserved as `initial-compile_diagnostic.rs` and
`initial-compile-accounting.log`; historical production source is in the
preferred investigation's frozen archive. The current diagnostic asserts the
corrected A*/greedy weight accounting. Subtracting g does not guarantee useful
FF guidance: its two-action example still has a constant remaining FF value,
while LM-cut decreases to zero. That example uses the literal FD-backed path.

## Controlled results

Eighty serial runs use one frozen release binary and identical captured SAS
inputs for each case: ZLIFO flaws, LIFO ties, no optional pruning or preferences,
200,000 generated nodes, 10 seconds planner time, 15 seconds watchdog, and 1 GiB
address space. Six selected ADD-only cases plus Parcprinter and three VHPOP-domain
controls are the same panel as earlier. Inputs match the frozen cluster snapshot.
These are selected cases and single runs, not a general coverage or timing claim.

| Profile | Six targets | All ten |
|---|---:|---:|
| ADD, w1 | 6 | 8 |
| FF, w1 | 0 | 2 |
| CLFF, w1 | 0 | 1 |
| FFOC, w1 | 6 | 8 |
| FFOC, w5 | 5 | 6 |
| FFOC, greedy | 2 | 2 |
| COMPILE_FF, w1 | 0 | 1 |
| COMPILE_LMCUT, w1 | 0 | 1 |

FFOC exactly matches ADD's generated-node counts and costs on Gripper p01/p03,
Miconic p01/p02, Childsnack p01, ZenoTravel p01 and Satellite p01. Both hit the node
cap on Driverlog and Parcprinter. Elevators is the exception: ADD uses 8,449 nodes
at cost 43; FFOC uses 99,689 at cost 42. Thus restoring coverage does not establish
an efficiency gain. Weight/greedy variants are exploratory; matched ADD profiles
at those settings were not measured in this batch.

Parcprinter: ADD and FFOC hit the cap; ordinary FF uses 70,933 nodes, compiled FF
12,201, and compiled LM-cut 123, all successful plans costing 17. Compilation
failed on every other case. The compiled backends spend most of their capped
search time evaluating heuristics, so both guidance and evaluation overhead
matter. Smaller node counts at timeout are not evidence of greater efficiency.

## Evidence and validation

- `ff-compiled-summary.json`: all 80 outcomes, nodes, costs, timing and artifact hashes.
- `ff-compiled-frozen.json`: source/tests archive and release executable hashes.
- `ff-compiled-baseline-check.json`: all 30 ADD/FF/CLFF outcomes reproduce the
  corrected investigation; solved/node-capped node counts and costs also match.
- `ff-compiled-plan-validation.json`: all 29 printed solutions independently
  replayed against the captured SAS tasks, including preconditions and goals.
- `ff-compiled-validation.json`: library 237 passed/one ignored, CLI 14 passed,
  six compilation integration tests, corrected accounting diagnostic, and final
  FFOC ranking test passed. The slow full lifted search test was excluded.
- `compiled_probe.py`, `summarize_compiled.py`, `validate_compiled_plans.py`
  preserve preparation, verification, and replay procedures. Logs/SAS/source/binary
  live under `target/relax-investigation/ff-compiled*`.

Native compilation tests use independent concrete Dijkstra search to check
non-unit costs, mandatory occurrences, ordering restrictions and initial-to-goal
link protection. Literal compilation is checked with zero/non-unit costs in both
SAS and emitted PDDL, including committed plans and unit-cost override.

## Next test

Retain FFOC (or ADD) as the primary occurrence-sensitive rank and use joint FF or
FFR only to break ties. This asks whether potential/existing reuse can help when
it cannot override the primary support-demand estimate. The three prepared
profiles are `FFOC/FF/LIFO`, `FFOC/FFR/LIFO`, and `ADD/FFR/LIFO`, all w1.
Their performance is not claimed here before measurement.

Review run06: partial, same-family/provisional, formal integrity audit unavailable.
The reviewer independently verified outcomes and replayed plans, but required
fixing finite-cost reachability before interpreting compiled failures. Two new
regressions fail before and pass after separating reachability from cost; the
unit chain triggers the old bug at 32 mandatory steps. Corrected reruns follow.
