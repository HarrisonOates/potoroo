# Why RELAX underperforms ADD

Investigation dated 7 November 2026, branch `investigate/relax-vs-add`, based on
commit `2b7bf40`. The earlier LP changes and HTN validation files are preserved
in the stash named `HTN validation and LP work before Relax investigation`.

**Follow-up:** [Testing the published Relax recurrence](repop-findings.md)
adds a separate native `REPOP` implementation and controlled comparisons.
The evidence below describes the original RELAX investigation and its binary.

**Current direction:** [FF with potential action reuse](ff-findings.md) adds
native `FF`/`FFR` prototypes and 90 bounded comparisons. Further RePOP tuning
is parked. The FF follow-up records both a Parcprinter gain and the remaining
support-reuse limitation.

**Preferred refinements:** [150 further runs](preferred-findings.md) test
preferred queues, FIFO ties and local Fast Downward on identical SAS inputs.
The option helps Parcprinter but does not close the native FF gap.

RELAX has two measured disadvantages: it explores much larger searches on
important domains, and each estimate costs more to compute. The code and
diagnostics identify a specific ranking mechanism: extracting one shared
support graph from the initial state loses the cost of repeated support needs,
while committing a useful step can leave that same operator charged in the
remaining estimate. ADD's separate charge for each open condition provides
more useful guidance on these cases. The evidence establishes these mechanisms
and their presence in representative cases; it does not assign a percentage of
the suite-wide coverage loss to each one.

## Matched cluster results

Source: `../potoroo-cluster/results/cluster-memory-2026-11-07-0836`, frozen image
`91c1408` with dirty-source tree hash beginning `0239ba3f`. All comparisons use
A*, ZLIFO, `/LIFO`, 1,800 seconds and 8,192 MiB per-process address space. The
newer local memory image is not used in this cluster snapshot.

RELAX is only partially run. Comparing its solved count with ADD's full 1,260
tasks would be misleading. On the exact completed intersection:

| Representation | Same tasks | ADD solved | RELAX solved | Both | ADD only | RELAX only |
|---|---:|---:|---:|---:|---:|---:|
| FDR | 725 | 117 | 32 | 31 | 86 | 1 |
| Lifted | 180 | 15 | 6 | 4 | 11 | 2 |

There are no ground-propositional RELAX results in this snapshot. Completed
subsets are not random samples; these are observed matched results, not
predictions of final full-suite coverage. Input hashes, image identity, budgets,
and flags agree within pairs. The snapshot has no repeated attempts.

Among the 31 jointly solved FDR tasks, RELAX generates 6.65 times as many nodes
and visits 6.69 times as many, using geometric means of paired ratios. The
elapsed-time ratio is 3.05. These ratios exclude failures.

The lost FDR solves include 23 Childsnack, 22 Gripper, 16 Miconic, and 8 Elevators
tasks. Gripper/p01 is the clearest example: ADD solves after 3,083 generated
nodes; RELAX's last progress report already contains 42,705,704 generated nodes
before an allocation failure. Miconic/p01 is 2,650 versus at least 42,157,964.
Those failed-run counts are lower bounds, not final totals. These differences
cannot be explained by evaluator speed alone.

RELAX also has real wins: Parcprinter/p16 is its only additional FDR solve,
and on jointly solved Parcprinter/p03 it generates 64,299 nodes against ADD's
1,198,598. This is not universal dominance by ADD.

Reproduce the comparison with [compare_cluster.py](compare_cluster.py); the
full matched evidence and source hashes are in [cluster-comparison.json](cluster-comparison.json).

## What the ranking loses

FDR RELAX is a native Rust SAS+ implementation. Fast Downward translates the
input once; heuristic evaluation uses the in-process `Planner` and its cached
initial-state cost/achiever tables. It does not invoke Fast Downward per node.
The `COMPILE_FF` family is separate, as is native FDR `CLFF`.

In [FDR relaxed_plan_size](../../src/fdr_pocl.rs), open conditions are reduced
to facts, `achieved` deduplicates facts, and `chosen_operators` deduplicates
ground operator identities. Achievers come from the task's initial-state cost
table. The standard RELAX estimate has no consumer-specific support accounting,
does not subtract a committed operator that still appears in the support graph,
and does not price threats or ordering conflicts. Repeated executions needed
after deletes can all be represented by one operator in that graph.

ADD instead sums the static relaxed cost of *every open-condition occurrence*.
Its overcounting can reward resolving an obligation even when another consumer
needs the same fact. Both estimates remain approximations; RELAX is not an
admissible heuristic and a smaller estimate is not automatically a better one.

The committed-support test in
[relax_diagnostic.rs](../../src/fdr_pocl/relax_diagnostic.rs) provides a minimal
witness. One action establishes `p`; two goal actions both require `p`. With
ZLIFO, insert a goal action, then its producer:

| Partial plan | ADD g+h | RELAX g+h |
|---|---:|---:|
| Initial | 4 | 3 |
| One goal action committed | 4 | 3 |
| Its required producer committed | 4 | 4 |

RELAX still charges the producer for the other goal, despite paying for its
committed occurrence in g. A* therefore sees a score increase on a useful
refinement. This is a reproducible ranking barrier, not a planner correctness
failure. Treating every committed effect as free introduces different losses
of information; the RELAXR probes below do not generally recover ADD's results.

On actual Gripper/p01 partial plans selected by the diagnostic's ADD search,
the initial estimates are ADD=60 and RELAX=41. The first support insertion
raises RELAX's g+h from 41 to 42 while ADD stays at 60. The diagnostic reaches
a valid 59-step solution. On Miconic/p01 the root estimates are 73 and 48, with
many more open-condition occurrences than distinct facts later in the search.
These traces show the same kind of information loss in benchmark tasks. They
are diagnostic searches, not exact replays of the production search queue.

See [Gripper trace](fdr-gripper-diagnostic.txt) and
[Miconic trace](fdr-miconic-diagnostic.txt).

## Evaluation overhead

FDR ADD sums cached numeric values; RELAX allocates sets and a worklist and
walks the shared support graph on every evaluation. In literal lifted/ground
planning, [cheapest_achiever](../../src/planning_graph.rs) also scans the
predicate's entire achiever list and recomputes candidate precondition sums for
each requested ground atom. That choice is static for a fixed ground atom and
graph but is recalculated repeatedly.

Identical-plan diagnostics separate this overhead from different search paths.
FDR measurements repeat each evaluator 1,000 times; literal measurements repeat
100 times. Each row below is the median of per-plan batch averages, except p29,
which measures only the root. Literal ADD includes rank construction while
literal RELAX times extraction alone. These are local microbenchmarks, not
end-to-end speedup estimates or measurements of the frozen cluster binary.

| Sample | ADD microseconds | RELAX microseconds | Median paired ratio |
|---|---:|---:|---:|
| FDR Gripper/p01, 60 nonempty plans | 0.017 | 3.273 | 197x |
| FDR Miconic/p01, 57 nonempty plans | 0.035 | 2.170 | 53x |
| Ground Miconic/p01, 55 nonempty plans | 0.337 | 9.176 | 22x |
| Lifted Miconic/p01, 55 nonempty plans | 2.713 | 15.188 | 3.2x |
| Lifted Miconic/p29, initial plan only | 1.687 | 8,453.987 | about 5,000x |

The large lifted case makes evaluator optimization a substantial performance
target. Repeated achiever scanning is a concrete candidate from code inspection;
these timings measure the whole evaluator and do not isolate scanning from
matching, allocation, or other extraction work. Its cluster run generates only
51,806 nodes in 30 minutes; ADD solves
after 908,726 generated nodes in about 25 seconds. Different trajectories
prevent treating that comparison as a per-evaluation ratio; the same-plan
measurement supplies the direct evidence of overhead.

All six inspected heuristic function bodies are identical between the archived
cluster source and this checkout. Other code has changed, including memory
management and lifted graph construction. Hashes and comparisons are in
[local-summary.json](local-summary.json) and [local-provenance.json](local-provenance.json).

## Controlled local probes

The small diagnostic set uses seven deliberately selected FDR problems, all
with cluster-matching input hashes. Each run has a 200,000 generated-node cap,
10-second planner limit, 15-second watchdog, and 1 GiB address-space cap.
Production defaults are unchanged. Six cases have strong ADD results; the
seventh, Parcprinter/p03, is a RELAX advantage control.

The table reports generated nodes on solved runs. `limit` and `timeout` are
censored outcomes under these local limits, not predictions of 30-minute
cluster results. Every row is p01 except Parcprinter/p03.

| Domain | ADD A* | RELAX A* | RELAX then ADD A* | RELAX weight 3 | RELAX GBFS |
|---|---:|---:|---:|---:|---:|
| Gripper | 3,083 | limit | limit | 1,971 | 2,068 |
| Miconic | 2,650 | limit | limit | limit | timeout |
| Childsnack | 5,859 | limit | limit | limit | timeout |
| Elevators | 754 | limit | limit | limit | timeout |
| Logistics | 4,107 | limit | 89,384 | 103,954 | timeout |
| Satellite | 851 | 137,685 | 22,340 | 26,946 | timeout |
| Parcprinter | limit | 64,299 | not measured | not measured | not measured |

Increasing the weight recovers Gripper, but the plan costs 77 instead of ADD's
59; GBFS costs 79. An ADD tie-breaker substantially helps Satellite and Logistics
without matching ADD. GBFS with ADD or OC tie-breakers still fails the other
six selected tasks within these limits. RELAXR A* solves Satellite and
Parcprinter but hits the node cap on the other five. None of these tested
adjustments recovers ADD's results across the selected cases. Other weights,
tie-breakers, and combinations remain untested.

Additional ground and lifted probes reproduce the gap on Miconic and
Childsnack. Ground Gripper is solved by ADD and capped with RELAX; both lifted
Gripper runs hit the cap. Raw outcomes are in [probe.csv](probe.csv),
[followup.csv](followup.csv), and [representations.csv](representations.csv).
The first five Parcprinter attempts used a missing generic domain filename;
they are retained as errors and excluded from conclusions. Corrected runs use
`domain-p03.pddl` in followup.csv. Some early probes overlapped compilation, so
the comparison above uses node counts and outcomes rather than runtime ratios.

## Next changes worth testing

1. Cache literal cheapest achievers by ground fact, or cache their support
   closures. Replace repeated FDR set construction with indexed scratch storage
   where useful. Verify score equivalence on identical partial plans. This
   addresses evaluator overhead; it cannot repair the observed search order.
2. Preserve useful per-consumer obligations when accounting for shared support.
   Evaluate this against the committed-support witness and repeated-resource
   tasks before proposing a replacement RELAX. More unconditional free reuse
   alone is not supported by these probes.
3. Keep ADD as the performance baseline and retain RELAX-favourable controls.
   A larger, matched run is needed before selecting any new default.

The literal implementation also treats negative and non-atomic open conditions
as free, ignores conditional-effect guards during this extraction, and uses
FIFO processing despite the comment claiming highest-cost-first processing.
Those are separate semantic/documentation limitations. They cannot explain the
shared FDR failure by themselves: FDR supports finite-domain values and effect
requirements. The subsequent [paper-to-code comparison and tests](repop-findings.md)
distinguish these legacy implementations from the published recurrence.

## Reproduction and checks

Run from the repository root:

```sh
python3 investigation/relax-vs-add/compare_cluster.py \
  ../potoroo-cluster/results/cluster-memory-2026-11-07-0836 \
  --output investigation/relax-vs-add/cluster-comparison.json
cargo build --release --bin potoroo
POTOROO_FD=../downward/fast-downward.py python3 \
  ../potoroo-cluster/scripts/potoroo/pocl_probe.py \
  investigation/relax-vs-add/probe-manifest.json \
  --output /tmp/relax-probe.csv --logs /tmp/relax-probe-logs \
  --seconds 15 --memory-mb 1024 --node-limit 200000
python3 investigation/relax-vs-add/run_diagnostics.py
python3 investigation/relax-vs-add/summarize.py
cargo test --release --lib
```

Repeat the probe command with `followup-manifest.json` and
`representations-manifest.json` for the remaining configurations. Manifests
record the local absolute binary/input paths; adjust them when moving the
checkout. Full local planner logs are under `target/relax-investigation`.

The library suite passes: 216 passed, 1 diagnostic ignored. Both ignored FDR
diagnostics and all three literal diagnostic runs pass when explicitly invoked.
The only planner-source edit includes a test module; runtime heuristic and
search behavior have not been changed by this investigation.

Result-to-claim review: **supported for this scoped investigation**, with the
wording above limited to tested settings and total evaluator overhead. The
fresh reviewer independently reproduced the matched comparison and checked
the local evidence and implementation. Confidence is high for the observed
deficit and ranking barriers, moderate for their contribution across the suite.
Assurance remains provisional (native Codex review; serving model identity not
independently verified). No separate experiment-integrity audit was run.
See the [full review](../../.aris/traces/result-to-claim/2026-11-07_run01/001-review.response.md).


## FF compilation and occurrence-sensitive follow-up

See [the corrected report](compiled-ff-corrected-findings.md). The 110 corrected
runs recover ADD's six selected target solutions and 8/10 panel coverage using
FFOC, which sums independent FF support plans per open occurrence. This is a
recovery, not an overall gain over ADD. Full compiled FF and LM-cut solve only
Parcprinter; three FF/FFR secondary-rank profiles reduce coverage to 3/3/5 of ten.
Keep ADD default and FFOC experimental.

Review found and then confirmed correction of finite-cost saturation being
misclassified as unreachable in cl_relax/LM-cut. The 80 original compiled runs
remain historical; corrected source, binary, 110 runs and 40 replayed solutions
are frozen separately. Final result-to-claim verdict is partial for the broader
aspiration, with the bounded report supported and no remaining blocking defect
identified (same-family/provisional, formal integrity audit unavailable).

## Memory failures and the FD coverage gap

The [latest report](memory-and-domain-findings.md) records complementary FFR
recoveries, particularly four of nine historical Parcprinter ADD memory
failures, and targeted flaw-selection experiments in the seven requested
domains. On the 14 selected FD-gap tasks, standard ADD solves zero, ADD/LR two,
and FFR with either standard ZLIFO or LR three; FD solves 11 with A*/FF and 13
with preferred greedy FF under the stated budget differences. These selected
local results do not establish broad superiority over ADD or FD.

Paired diagnostic runs distinguish high supporter branching in Pipesworld and
Freecell from predominantly unary threat-resolution work in Sokoban and
Parcprinter. They also observe existing forced restorers without changing
classical threat semantics. The detailed report gives counters, sample bounds,
superseded diagnostic output, raw evidence, and the run10 review status.

Run10's final review supports the scoped descriptive results with a partial
verdict for the broader FF ambition (same-family/provisional): 224 runs, 971
artifact-hash entries and 47 successful plan replays verified. A separate
condition-attribution addendum verifies another 21 runs, 97 artifact hashes and
two successful replays. It localizes much of the sampled work to pipe mode
flags, solitaire capacity/playability facts, player/sheet locations and Pegsol
move-control facts. These identify concrete targets; runtime causation and
coverage gains from changing them are not yet demonstrated.

## Targeted refinement follow-up

The [136-run follow-up](targeted-refinement-findings.md) tests a fixed bounded
support-selection policy and forced classical threat repairs. FFR with the
bounded policy solves four of the 14 selected hard cases, versus three for
either previous FFR policy and two for ADD/LR. It combines the existing FFR
solved sets; it adds no new case to their union. All three tested FFR variants
fail the six ADD-success controls, which ADD solves again. Across the 20 cases,
the bounded FFR configuration therefore still trails standard ADD, four versus
six. It is not a replacement for the default.

Forced propagation adds no solve in 41 matched pairs. It can remove substantial
intermediate queue work without resolving the memory failures. All 25 returned
plans pass independent replay. The detailed report records the Pegsol plan-cost
gain alongside its higher memory use, the Parcprinter tradeoffs, validation
scope, and the final run11 review status.

Run11's final review supports the scoped configuration gain and negative
propagation result, with a partial verdict for the broader objective
(same-family/provisional). It independently verifies all 136 runs, 601
artifact-hash entries and 25 executable plans; no further experiments are
required for those scoped conclusions.
