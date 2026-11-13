# Targeted support selection and forced threat propagation

Branch: `investigate/relax-vs-add`. This round tests interventions motivated by
[the condition attribution](memory-and-domain-findings.md#condition-level-attribution).
ADD and all default settings remain unchanged.

## Methods fixed before the screen

The support-selection intervention retains ZLIFO's threat priority and its
zero/one-supporter rules, then selects the newest open condition with at most
eight candidate supports. If none qualify, it selects the open condition with
the fewest candidates. The threshold eight was chosen before this round's
results, not tuned per domain. This uses existing flaw-selection machinery:

```
{n}LIFO/{o}0LIFO/{o}1NEW/{o}8LIFO/{o}LR/{s}LIFO
```

Counts include fresh templates, INIT support and eligible existing occurrences;
they are candidate counts, before all refinement feasibility checks. No predicate
names or domain-specific exclusions are used. All achievers of the selected
condition remain available. This differs from global LR by keeping LIFO among
qualifying low-count open conditions. The report calls this policy B8.

The independent `-p threats` intervention compresses chains of forced classical
ordering repairs after a threat or ordering disjunction is selected. It only
propagates uncovered threats with at most one possible ordering repair and no
conditional-effect confrontation alternative. Ambiguous threats remain pending;
a zero-repair threat is rejected. It uses the existing resolver and threat cache.

Propagation deliberately does not run on every new-action candidate: those
candidates retain the planner's compact deferred queue representation. Batches
are capped at 16 repairs and check deadlines. Compressed refinements still count
against generated-node limits and advance memory-stop sampling. `threat_forced`
counts explicit resolutions whose queue entries were omitted, not individual
ordering edges. This changes search order, while retaining classical causal-link
semantics. It does not implement white knights, route macros, or order-aware
initial-state heuristic evaluation.

## Evaluation protocol

The first panel reuses the seven diagnosed instances. The second panel is also
previously studied; neither panel is unseen heldout data. The first matrix is
fully crossed: ADD/FFR × ZLIFO/B8 × propagation off/on, plus ADD/LR and FFR/LR
controls (70 runs). All use A with weight one and LIFO queue ties. No other
pruning or preferences are enabled. The same new frozen binary runs every profile.

Limits match the earlier local performance screen: 15 seconds including
translation, 20-second watchdog, 512 MiB soft parent RSS stop, 1,536 MiB per-process
address space, unlimited generated nodes. Runs are serial, with diagnostics off.
Inputs and actual SAS are captured and hashed; every solution is independently
replayed. Failed-task times are censoring limits, not solution runtimes. Generated
node comparisons include forced refinements and must not be mistaken for queue
insertions. These experiments do not change the historical cluster results.

Tests include 96 generated three-variable tasks checked against exhaustive
state-space reachability, optimal BFS costs and executable plan replay, with
propagation both off and on. Searches have a 200-node cap: limit outcomes are
allowed, so this checks returned solutions and no false `NoSolution`, not
complete reachability agreement for every generated task. They also cover preserved action occurrences/support
links, retained ambiguous and
conditional choices, inconsistent links, bounded batches/deadlines, and a
multi-consumer forced-ordering task across five search algorithms with plan
replay and node budgets. A separate fixture distinguishes B8 from both standard
ZLIFO and global LR.

## First-panel results

All 70 runs completed; 11 returned plans pass independent SAS replay. Coverage
below is out of the seven previously studied cases. `+T` enables forced repairs.

| Ranking | ZLIFO | ZLIFO +T | B8 | B8 +T | LR |
| --- | ---: | ---: | ---: | ---: | ---: |
| ADD | 0 | 0 | 1 | 1 | 1 |
| FFR | 1 | 1 | 2 | 2 | 2 |

Every ADD solution is NoTankage p01. FFR/ZLIFO solves Parcprinter p05; FFR/B8
and FFR/LR solve both. All profiles fail on Thoughtful p01, Tankage p01,
Sokoban p02, Pegsol p01 and Freecell p02. There is no new union coverage over
the earlier configurations. The B8 result is a potentially useful compromise
between ZLIFO and global LR, not evidence that it is universally superior.

Without propagation, B8 and LR give identical generated/visited counts and
plan costs on NoTankage: ADD generates 284,215 nodes (cost 14, 555/579 ms),
while FFR generates 1,620,539 (cost 14, 3,325/3,381 ms). On Parcprinter,
FFR/ZLIFO generates 602 nodes, B8 6,118, and LR 118,886; all cost 25.
The respective times are 83, 97 and 409 ms. These are single measurements;
the small timing differences do not establish speedups.

Forced repairs change coverage in none of the 28 matched pairs. They do
compress real work: Sokoban ADD/ZLIFO records 650,293 forced repairs and
671,851 queue visits versus 1,314,816 visits without propagation. Both hit
the RSS limit, and their maximum queues remain approximately 2.39 million.
Parcprinter ADD/ZLIFO compresses 3,612,300 repairs but still hits the RSS
limit with approximately 433,000 queued plans. Thus reducing the number of
queued intermediate ordering refinements does not resolve these frontier
memory failures. Different stop points mean these failed-run counts are not
a controlled comparison of equal search prefixes or total CPU work.

## Adaptive confirmation

After seeing the first panel, the planned second panel is narrowed to six
profiles: ADD/ZLIFO, ADD/LR, FFR/ZLIFO, FFR/LR, FFR/B8 and FFR/B8+T (42 runs).
Six previously used ADD-success controls additionally compare ADD/ZLIFO,
FFR/ZLIFO, FFR/B8 and FFR/B8+T (24 runs). This tests whether B8 retains
ZLIFO's Parcprinter behavior and LR's NoTankage/Pegsol behavior without losing
the controls. No threshold is retuned. The full 70-run second-panel manifest
was prepared before the screen but is not executed.

All 42 second-panel runs completed, with eight executable plans independently
replayed. Combining the two seven-case target panels gives:

| Profile | First seven | Second seven | Total /14 |
| --- | ---: | ---: | ---: |
| ADD/ZLIFO | 0 | 0 | 0 |
| ADD/LR | 1 | 1 | 2 |
| FFR/ZLIFO | 1 | 2 | 3 |
| FFR/LR | 2 | 1 | 3 |
| FFR/B8 | 2 | 2 | 4 |
| FFR/B8+T | 2 | 2 | 4 |

The four FFR/B8 solutions are NoTankage p01, Parcprinter p05/p07 and Pegsol p02.
This combines the solved sets of FFR/ZLIFO and FFR/LR on these cases without
running a portfolio. It adds no case to their union. It does not establish a
general advantage, and its resource tradeoffs are substantial:

* On Parcprinter p07, B8 solves where LR hits the RSS limit, but generates
  688,091 nodes versus ZLIFO's 714, both cost 33. Their measured times are
  2,563 versus 87 ms. B8+T generates 704,515 nodes including 405,492 forced
  repairs and returns in 1,843 ms; its peak planner RSS is 87,888 versus
  B8's 92,156 KiB. These single-run differences need repetition before a
  stable speed claim.
* On Pegsol p02, B8 generates 785,685 nodes and returns a 12-action plan;
  ZLIFO generates 1,573,929 with cost 13, and LR 1,492,700 with cost 13.
  However, B8's peak planner RSS is 403,452 KiB versus ZLIFO's 258,448 KiB.
  Fewer generated nodes do not imply less memory. ADD/LR is much cheaper
  computationally (7,458 nodes, 102 ms, 6,240 KiB planner RSS) but returns
  a longer 18-action plan. These plans are validated, not proven optimal.

FFR/B8+T adds no solution on the second panel. All configurations still fail
on the second Thoughtful, Tankage, NoTankage, Sokoban and Freecell cases.

The 24 control runs also completed. ADD/ZLIFO solves all six (Childsnack p01,
Elevators p02, Gripper p01/p03, Miconic p01/p02), in 78–117 ms each. FFR/ZLIFO,
FFR/B8 and FFR/B8+T each solve zero. The six ADD plans pass independent replay.
For the profiles tested on all 20 cases, ADD/ZLIFO therefore solves six,
FFR/ZLIFO three, and FFR/B8 with or without propagation four. ADD/LR was
not run on these six controls; combining its target results with ADD/ZLIFO's
controls would not describe a single tested configuration.

Across this round there are 136 runs and 25 independently replayed solutions.
All 41 matched propagation pairs retain the same solved/failed status.

## Decision

Keep the default unchanged. B8 is an experimental configuration that combines
two existing FFR coverage patterns on this selected target set. It still fails
the ADD controls, and can be much more expensive than ZLIFO on Parcprinter.
Neither it nor propagation establishes an overall improvement over ADD.

Stop expanding the forced-repair experiment for now. It removes intermediate
queue visits but does not add coverage or resolve these memory failures. The
single Parcprinter p07 timing improvement is a candidate for a narrowly scoped
speed study, not grounds for a general performance claim or default change.

The remaining research priority is heuristic guidance about support that has
to be re-established, particularly the initially true mode/resource facts
identified in the condition analysis. In the current implementation, the FF
graph still seeds the original initial state and the FFR reuse filter only
checks whether a producer could precede its consumer. These interventions do
not change either assumption. A useful next diagnostic would count initially
true open conditions whose INIT support is blocked by a forced intervening
deletion, and reused producers separated from consumers by such deletions.
That would measure whether a cheaper order-aware correction is worth testing;
this round does not show that such a correction would improve coverage.

The B8 configuration is reproducible with the frozen binary:

```sh
target/relax-investigation/ff-target-frozen/potoroo --fdr-pocl -s A -w 1 -h FFR/LIFO -f '{n}LIFO/{o}0LIFO/{o}1NEW/{o}8LIFO/{o}LR/{s}LIFO' -p none --time-limit 15 --stage-mem-mb 512 -l unlimited DOMAIN PROBLEM
```

## Validation and artifacts

Validation scope: 251 library, 14 CLI, 15 pruning integration and 11 review
regression tests pass (291 total; one diagnostic ignored). The broader pruning run was
interrupted during the unrelated lifted LPLAN optimality test after it exceeded
60 seconds; it had reported no failure. The integration rerun passes all 15 other pruning tests and all 11 review
regressions, with only `lifted_cutset_preserves_optimal_ground_plans` excluded. This round does
not claim a completed full-repository test run.

The frozen binary/source archive and their SHA-256 hashes are recorded in
`ff-target-frozen.json`. `ff-target-validation.json` records validation logs.
`ff-target-{screen,confirm,controls}-summary.json` record raw-artifact hashes and
plan replay; the corresponding `-interventions.json` files add the forced-repair
counters. `targeted_refinement_probe.py` defines the original screen, and
`targeted_refinement_confirm.py` records the adaptive confirmation selection. The
checkpoint reviewer found no implementation blocker, subject to the bounded
validation scope above. Its same-family judgment is provisional; see
`.aris/traces/result-to-claim/2026-11-07_run11/` at the repository root.
The screen review supported proceeding with this bounded confirmation, while
rejecting a coverage-breakthrough claim. The final review supports the narrow
B8 configuration gain and the negative propagation result, with a **partial**
verdict for the broader coverage/memory objective. It independently checked all
136 runs, 601 artifact-hash entries, the frozen/current source snapshots and
replayed all 25 plans. No further experiments are required for these scoped
claims. Acceptance remains provisional and same-family; no formal experiment
integrity audit was run. The next action is the narrower diagnostic direction
above, with no default change or further expansion of this propagation screen.
See the [final review](../../.aris/traces/result-to-claim/2026-11-07_run11/003-final-review.response.md)
and [structured verdict](../../.aris/traces/result-to-claim/2026-11-07_run11/final-verdict.json).
