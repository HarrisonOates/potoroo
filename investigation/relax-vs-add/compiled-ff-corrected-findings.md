# Corrected compiled FF and occurrence-sensitive FF

7 November 2026, `investigate/relax-vs-add`.

Occurrence-sensitive FF (`FFOC`) recovers all six selected ADD-only failures and
matches ADD's 8/10 coverage. It has not overtaken ADD. Corrected full compilation
solves only Parcprinter under these limits; FF-based secondary ranks reduce
coverage. ADD remains the default.

## Numerical correction

The first compiled matrix is preserved in [the initial report](compiled-ff-findings.md).
Independent review found that finite additive costs could collide with the
unreachable sentinel. Full ordering closure gives a unit-cost mandatory chain
marker estimates `2^i-1`, so 32 actions suffice to reach `u32::MAX` despite a
concrete completion of cost 32. The old evaluator incorrectly returned infinity.
An analogous aggregate-cost issue affected LM-cut for sufficiently large costs.

`cl_relax` and `lmcut` now represent unreachable separately (`None`), keeping
saturated finite costs reachable. Numeric estimates still cap at `u32::MAX`;
this is not arbitrary-precision arithmetic. Both native regressions fail before
and pass after the fix. The mandatory-chain test checks lengths 31, 32 and 40
against concrete Dijkstra; a second test checks two large accepted action costs.
Further tests cover repeated occurrences of the same operator and link protection
between real steps, including a consumer that deletes the consumed fact.

The code and test archive is `ff-compiled-v2-frozen.json`. All corrected and tie
measurements use that one release executable. FFOC implementation is unchanged.

## Tie-profile design

The adaptive follow-up compares `FFOC/FF/LIFO`, `FFOC/FFR/LIFO`, and `ADD/FFR/LIFO`
against the matched w1 ADD/FFOC runs. Their exact ranks are
`(g+h_primary, g+h_secondary, LIFO)`: the second term includes g, and is not a
pure-h tie-break. The shared original FF graph is unchanged; FFR filters
order-compatible existing support at the current open-condition frontier.

This is an exploratory selected panel, not held-out evaluation. It tests whether
joint sharing can help when it cannot override the primary support-demand rank.

## Adaptations

`FFOC` sums one original-FF-style relaxed-plan size per open-condition occurrence.
It preserves repeated demands across consumers while allowing actions to share
effects within each individual support plan. Costs are cached per fact, since
the underlying graph still starts from the original initial state. The cached
graph is therefore compatible with the observed recovery; this does not isolate
duplicate-fact merging from other sharing across different demands. FFOC currently
requires unit-cost, unconditional, axiom-free tasks. It is an experimental POCL
adaptation, not an algorithm claimed to appear in the VHPOP paper.

Native `COMPILE_FF` and `COMPILE_LMCUT` represent distinct mandatory action
occurrences, full committed ordering closure, and causal-link guards. The
remaining estimate is `max(h_compiled-g,0)` before weighting. Original actions
remain available for insertion. Native FF uses additive-cost supporters through
`cl_relax`; its choices need not match FD. Literal SAS/PDDL compilation now carries
resolved costs, including zero costs; ground instances use exact costs, while
lifted parameterized costs retain the planner's schema lower-bound convention.
Native compilation requires unconditional effects and no axioms.

## Corrected comparisons

One frozen release binary, identical captured SAS per case, serial execution,
ZLIFO flaws, LIFO final ties, no optional pruning or preferences. Limits:
200,000 generated nodes, 10 seconds planner time, 15 seconds external watchdog,
and 1 GiB address space. The six targets are the same selected ADD-only cases
from the frozen cluster snapshot. Four controls complete the ten-case panel.
These are single runs on an adaptively selected panel, not a broad or statistical
performance claim. Weighted and greedy FFOC are exploratory; matched ADD profiles
at those settings were not measured here.

| Profile | Six targets solved | Ten-case panel solved |
|---|---:|---:|
| ADD, w1 | 6 | 8 |
| FF, w1 | 0 | 2 |
| CLFF, w1 | 0 | 1 |
| FFOC, w1 | 6 | 8 |
| FFOC, w5 | 5 | 6 |
| FFOC, greedy | 2 | 2 |
| COMPILE_FF, w1 | 0 | 1 |
| COMPILE_LMCUT, w1 | 0 | 1 |
| FFOC/FF/LIFO, w1 | 2 | 3 |
| FFOC/FFR/LIFO, w1 | 2 | 3 |
| ADD/FFR/LIFO, w1 | 4 | 5 |

FFOC matches ADD's generated-node counts and costs on seven solved cases:
Gripper p01/p03, Miconic p01/p02, Childsnack p01, ZenoTravel p01 and Satellite p01.
Both hit the cap on Driverlog and Parcprinter. Elevators differs: ADD generates
8,449 nodes at cost 43; FFOC generates 99,689 at cost 42. Equal counts on the other
cases do not prove their heuristic values or search trees are identical.

Parcprinter is the sole success for each full compiled backend: FF uses 12,201
nodes and 1,658 ms; LM-cut uses 123 nodes and 105 ms, both cost 17. Ordinary FF
uses 70,933 nodes and 241 ms, also cost 17. Compiled FF's node reduction is not a runtime
improvement. Every other compiled run times out; much of the time is spent in
heuristic evaluation. The numerical fix preserves coverage and solved counts,
but no telemetry attributes a particular original timeout to saturation.

Secondary FF/FFR ranks lose both Grippers and ZenoTravel, among other regressions.
There are local gains: ADD/FFR solves Childsnack in 4,541 rather than 5,859 nodes,
and both FFR tie profiles solve Satellite in 604 rather than ADD's 851. These do
not compensate for the lost coverage. The tested secondary terms include g;
this is not evidence that every possible pure-h or sharing-aware tie rule fails.

## Verification and preserved evidence

The corrected 80-run and tie 30-run summaries verify 110 CSV/final-STATS records,
commands, limits, input hashes, archived source/binary, and identical actual SAS
across profiles. All 40 printed successful plans were independently replayed
against their captured SAS inputs, checking preconditions, goals and costs.
All 30 ADD/FF/CLFF baseline outcomes reproduce the earlier corrected FF batch;
solved and node-limited counts/costs also match. The 80 pre-overflow-fix runs are
preserved separately and are not used as the corrected matrix.

- `ff-compiled-v2-summary.json`, `ff-ties-summary.json`: outcomes and artifact hashes.
- `ff-compiled-v2-frozen.json`, `ff-ties-frozen.json`: same corrected source/tests archive and binary.
- `ff-compiled-v2-plan-validation.json`, `ff-ties-plan-validation.json`: 29 + 11 executable plan replays.
- `ff-compiled-v2-baseline-check.json`: 30 matched baseline comparisons.
- `ff-compiled-v2-validation.json`: 242 library tests passed, one ignored; 14 CLI
  tests passed. Earlier six literal compilation integration tests and the corrected
  accounting diagnostic remain applicable to their unchanged source paths.
- `compiled_v2_probe.py`, `compiled_ties_probe.py`, `summarize_compiled_v2.py`,
  `summarize_compiled_ties.py`, `validate_compiled_plans.py`,
  `finish_compiled_analysis.py`: preparation, verification and replay procedures.

Raw logs/SAS/plans/source/binary are under `target/relax-investigation/` with
`ff-compiled-v2` and `ff-ties` prefixes. The original numerical counterexamples
have explicit failing-before and passing-after logs there as well.

## Decision

Keep ADD as default and retain `--fdr-pocl -h FFOC/LIFO` as the promising FF
baseline for further work. Global FF sharing and these secondary rank rules do
not improve the selected panel. A stronger adaptation needs a way to preserve
useful demand information while sharing support only when that sharing helps
search; that is a future hypothesis, not a result established by these runs.


## Result-to-claim review

The secondary reviewer supports the bounded implementation and descriptive claims
with high confidence, finds the overflow blocker resolved, and identifies no
remaining blocking correctness or measurement defect. Overall verdict remains
**partial** because overtaking ADD is not supported. It independently verified
110 records and replayed all 40 solutions. Review is same-family/provisional,
with exact serving identity unknown and no formal EXPERIMENT_AUDIT. The final
review continued the originally fresh run06 session after a new fresh-agent
attempt hit the tool's thread limit. Full requests, responses and parsed verdicts
are preserved under `.aris/traces/result-to-claim/2026-11-07_run06` and `run07`.

No additional measurement is required for these bounded findings. Before wider
tuning, inspect rank disagreements and plateau decisions; any promising change
then needs held-out evaluation and matched baselines.
