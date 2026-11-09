# FF reuse, preferred refinements, and the FD coverage gap

Investigation branch: `investigate/relax-vs-add`. These are bounded local
experiments, not a replacement cluster coverage result. ADD remains the default.

## Findings supported by completed memory experiments

FFR has useful complementary strengths. It does not dominate ADD.

* On all **nine Parcprinter search-memory failures** from the historical ADD
  run, FFR with A/LIFO solves **four**, versus **zero** for matched ADD, FF and
  ADDR. The successes are p05, p07, p09 and p13: respectively 602, 714, 972 and
  1,444 generated nodes, costs 25, 33, 49 and 57, and planner times 87–112 ms.
  All four plans were independently replayed against their actual SAS tasks.
* Under GBFS/FIFO, FFR solves Rovers p02 and p04; enabling preferred refinements
  additionally solves Logistics p05 and p07. On Rovers, preferences reduce
  generated nodes from 10,800 to 4,616 and from 25,777 to 4,081, while also
  reducing plan costs from 63 to 51 and from 51 to 47.
* Preferred ADD has different strengths: it solves the same two Logistics
  cases and Elevators p13/p14. Preferred FFR fails on those Elevators cases.
  On Logistics p07, preferred ADD is considerably better: 131,411 nodes,
  cost 235, 1.88 s versus FFR's 485,839 nodes, cost 241, 10.83 s.
* The new FFOCR experiment sums separate FF support costs for every open
  occurrence after discounting compatible existing support. On its 14-case
  panel, ADD solves six, FFOCR two, and preferred FFOCR one. FFOCR recovers
  Driverlog p01 (1,525,845 generated nodes, cost 71, 5.97 s), but retains only
  Childsnack of the six earlier ADD-success controls. It does not combine the
  strengths of FFOC and FFR as hoped.

The two initial memory panels each contain one prespecified search-memory
failure from eight domains. The second instance was selected before the first
panel finished. Parcprinter was subsequently extended to all nine eligible
failures; that extension is adaptive domain exploration. The greedy confirmation
retains all eight second instances but drops unsuccessful FF/FFOC profiles.

| Completed suite | Runs | Cases | Profiles / successful runs |
|---|---:|---:|---|
| `ff-memory-screen` | 48 | 8 | ADD±pref 0/0; FFOC±pref 0/0; FFR±pref 1/1 |
| `ff-memory-heldout` | 48 | 8 | ADD±pref 0/0; FFOC±pref 0/0; FFR±pref 1/1 |
| `ff-memory-greedy-screen` | 64 | 8 | ADD±pref 1/2; FF±pref 0/0; FFR±pref 1/2; FFOC±pref 1/2 |
| `ff-memory-greedy-confirm` | 32 | 8 | ADD±pref 1/2; FFR±pref 1/2 |
| `ff-memory-parcprinter` | 36 | 9 | ADD 0; FF 0; ADDR 0; FFR 4 |
| `ff-ffocr-screen` | 42 | 14 | ADD 6; FFOCR 2; FFOCR+pref 1 |

The table contains overlapping instances and repeated profiles; adding its
success counts would not give unique coverage. Likewise, the union of successes
across profiles is not the performance of an actual shared-budget portfolio.
The prepared `ff-memory-portfolio` and `ff-memory-greedy-heldout` manifests are
not measurements; the latter was superseded by `ff-memory-greedy-confirm`.

## Protocol and evidence

Each local planner run receives 15 seconds including translation, a 20-second
watchdog, a 512 MiB soft planner RSS stop and a 1,536 MiB per-process address-space
limit. Performance runs have unlimited node counts; diagnostics use the fixed
budgets below. Runs are serial, with pruning disabled unless
explicitly identified. STATS calls both RSS and time stops `timeout`; the
summaries classify them using the explicit final stop message.

`planner_ms` includes translation, not just search. Parent RSS is distinct from
GNU time's peak individual-process RSS accounting across descendants; the latter
is not simultaneous total tree memory. Historical ADD used a different image,
1,800 seconds and 8 GiB address space. Its failures select cases; they do not
provide controlled local speed or memory ratios.

Every suite has a manifest, provenance record, raw logs, captured normalized
inputs/SAS, CSV and verified summary. `summarize_memory.py` verifies hashes,
commands and metrics, checks identical SAS across configurations of a case,
and independently replays each solution. The original memory experiments use
`ff-compiled-v2-frozen.json`; FFOCR and the FD-gap timing screen use
`ff-ffocr-frozen.json`. New diagnostic source/binary are separately frozen in
`ff-gap-diagnostic-v2-frozen.json`. The original diagnostic freeze is
retained as a superseded output-format run; see the diagnostic validation below.

The run09 result-to-claim review independently checked 228 memory runs, 996
artifact-hash entries and 23 successful plan replays. Verdict: **partial**,
same-family/provisional continuation, no correctness or measurement blocker.
It supports the scoped recoveries above, not broad dominance. FFOCR and the
subsequent FD-gap experiments were outside that review's completed scope.

## The seven priority domains

The latest coverage snapshot is `cluster-memory-2026-11-07-1248`; its FD baseline
comes from `cluster-2026-11-04-final-old`, using `astar(ff())`. That comparison
uses separate submissions/images; the old FD harness did not enforce the current
FDR run's physical-core affinity. Historical FD rows lack per-input hashes.
Local FD controls therefore consume the exact captured SAS used by local POCL.

Screen cases are the first lexicographic FD-solved/ADD-unsolved instance in
Thoughtful, Pipesworld Tankage, Pipesworld NoTankage, Sokoban, Parcprinter,
Pegsol and Freecell: p01, p01, p01, p02, p05, p01, p02. Second instances were
reserved before screening: p02, p02, p02, p03, p07, p02, p03. Parcprinter's pair
was already studied and is a replication control, not unseen evidence.

The fixed-ADD flaw ablation changes only ZLIFO's final unrestricted open-condition
tier to FIFO, fewest refinements (LR), or highest ADD cost (MC_add). Threat
priority and the zero/one-achiever tiers stay fixed. Queue scoring remains
ADD/LIFO with A. This separates flaw selection from the unrelated LIFO search
tie-break. Additional profiles are FFR/A, FFOCR/A, and preferred ADD/FFR GBFS/FIFO.

The diagnostic observer is opt-in and read-only. It counts actual children of
selected flaws before outer search pruning (after internal refinement checks),
with bounded samples of ordered step pairs,
repeated grounded operators, and new threats in action-insertion children.
These describe the visited search trajectory, not intrinsic domain properties
or duplicate-state counts. A separate paired on/off run compares the tracked
outcomes and search-count summaries at a fixed generated-node budget; it does
not compare complete expansion traces.

## White knights

The [IJCAI paper](https://ijcai.org/proceedings/2026/688) establishes the
representation result and evaluates MaxSAT reordering of fixed action sets.
Its standard IPC comparison solves 64/81 in both methods with equal ordering
counts; the ordering reductions occur in the synthetic resource-borrowing
benchmarks. This motivates investigation, but does not establish that relaxing
threat semantics improves generative planning coverage.

The observer counts a narrow existing-restorer opportunity: an unconditional
effect restoring the protected equality, forced after the deleter and before
the consumer. It does not resolve those threats or add restoration branches.
Zero observations would not rule out white-knight benefits: classical search
may prune a useful partial plan before it is sampled, and future restorers are
not represented by this counter. A correct search implementation would need
consistent changes to threat caching, pruning, refinement and solution checks.

## Initial seven-domain screen

The completed 56-run screen has three successful runs, all independently
replayed. Standard ADD/ZLIFO solves none. ADD with the final open tier set to
LR solves Pipesworld NoTankage p01 in 580 ms (284,215 generated nodes, cost 14).
ADD with that tier set to MC_add solves Parcprinter p05 in 104 ms (8,778 nodes,
cost 31). FFR with ordinary ZLIFO solves the same Parcprinter case in 84 ms
(602 nodes, cost 25). The other profiles solve none on this screen. These are
local outcomes; the second-instance results are reported separately.

Thus the four-of-nine Parcprinter FFR result is a comparison against fixed
ZLIFO baselines, not all possible ADD configurations. Changing ADD's flaw
selection removes the coverage difference on p05, although FFR still generates
fewer nodes and returns the shorter plan in this comparison.

FD controls use the local pinned revision `acc6438c7c927ac4de45c2baf263956bfba189e0`
and the exact same captured SAS. A*/FF solves six of seven; greedy FF with
preferred operators solves all seven. Thoughtful p01 is the A* failure, but
greedy preferred FF solves it in 251 ms with cost 96. Both FD variants solve
all other screen tasks, and all 13 successful plans were independently replayed.
FD receives 15 seconds of search, whereas POCL's 15 seconds includes translation.
FD RSS is externally sampled and killed above 512 MiB; POCL uses its own soft
stop. These differences preclude claiming perfectly equal end-to-end budgets.
The harness's 50 ms polling also rounds small FD external times upward.

Captured translation takes 49–754 ms on these seven tasks. Grounded operator
counts range from 87 (Pegsol) to 8,270 (Thoughtful). The sampled failures occur
in search. This does not establish the failure phase on larger tasks or on
Organic Synthesis, which is outside this sample.

Preferred FFR/GBFS is not uniformly useful here. Its maximum expanded-plan
sizes reach 612 steps in Thoughtful, 728 in Sokoban and 446 in Parcprinter,
versus ADD/A's 48, 15 and 42. This is evidence of very different trajectories,
not proof of duplicate states or of a particular cause. The structural observer below samples repeated grounded operators and counts
the prevalence of threats for the A/LIFO profiles; it does not instrument these
preferred-GBFS trajectories.

## Second-instance confirmation and applying LR to FFR

The seven-case FFR/LR follow-up solves NoTankage p01 in 3.40 s (1,620,539 nodes,
cost 14) and Parcprinter p05 in 416 ms (118,886 nodes, cost 25). This is slower
than ADD/LR on NoTankage and standard FFR on Parcprinter, but covers both with
one configuration. Both plans pass replay.

The 35-run confirmation uses all seven reserved second cases with five profiles.
It produces four verified plans: standard FFR solves Parcprinter p07 in 93 ms
(714 nodes, cost 33) and Pegsol p02 in 3.99 s (1,573,929 nodes, cost 13).
ADD/LR solves Pegsol p02 in 98 ms (7,458 nodes, cost 18), and FFR/LR solves it
in 5.00 s (1,492,700 nodes, cost 13). NoTankage p02 fails under every tested
profile. The MC and FFR/LR Parcprinter gains do not repeat on p07.

| Profile, all A/LIFO | First seven | Second seven | Total solved / 14 |
|---|---:|---:|---:|
| ADD, standard ZLIFO | 0 | 0 | 0 |
| ADD, final open tier LR | 1 | 1 | 2 |
| ADD, final open tier MC_add | 1 | 0 | 1 |
| FFR, standard ZLIFO | 1 | 2 | 3 |
| FFR, final open tier LR | 2 | 1 | 3 |

These are selected FD-gap cases, not a balanced benchmark. FFR/LR was chosen
adaptively after the NoTankage ADD/LR result; the second cases were already
reserved. The one-case coverage advantage over ADD/LR does not establish broad
superiority, and the solved sets differ. The initial preferred-queue profiles
solve none of the first seven and were not carried into this confirmation.

FD's confirmation solves five of seven with A*/FF and six with preferred
greedy FF. Thoughtful p02 and Tankage p02 are the A* timeouts; NoTankage p02 is
the preferred-greedy timeout. Across both panels, FD solves **11/14** with
A*/FF and **13/14** with preferred greedy FF. Their union covers all 14, but
this is not a shared-budget portfolio result. All 24 successful FD runs pass
independent SAS replay.

## Existing pruning controls

The 14-run pruning comparison enables `h2,supporters,edelete` jointly on the
first seven cases with ADD/ZLIFO and FFR/ZLIFO. It adds no solves: ADD remains
0/7 and FFR 1/7, retaining Parcprinter p05 (759 generated nodes, cost 25,
100 ms). That plan passes independent SAS replay.

The pairwise-reachability preprocessing reaches its 5,000,000-work limit on
Thoughtful and both Pipesworld tasks, so no completed h2 table is available
there. On these cases the result is not a test of fully computed h2 pruning.
The package also does not isolate the contributions of its individual rules,
and its failure does not rule out stronger resource or geometric dead-end
reasoning.

## Diagnostic validation

All 21 paired on/off comparisons pass: recorded outcomes, generated/visited
counts, plan cost, maximum queue size and preferred counters agree exactly.
No run stops on time or RSS; all use identical per-case SAS and the same binary.
Enabled runs emit exactly one diagnostic record and disabled runs emit none.
Four returned plans pass independent replay. This establishes agreement of the
tracked summaries, not identical expansion traces or negligible runtime cost.

The first diagnostic binary
emitted an extra empty record because Rust struct-update syntax dropped a
`Default` temporary of a type with a reporting `Drop` implementation. The
strict one-record parser caught this. The constructor is corrected; the
original raw logs and search summaries are preserved, with an explicit
supersession record in `ff-gap-diagnostic-v1-issue.json`.

The corrected v2 checks use 500,000 generated nodes instead of 50,000. This
lets high-branching Pipesworld searches reach non-root structural samples;
the earlier budget sampled only their empty initial plan. The budget change
applies equally to diagnostics on and off, using the same new frozen binary.
Performance comparisons above retain their original frozen binaries and budgets.


## Measured search structure

The following counters use ADD with standard ZLIFO and a 500,000-generated-node
budget. Child counts describe the selected flaw's emitted refinements after
internal checks and before outer pruning. Pair comparability is transitive and
excludes INIT/GOAL; it is pooled over sampled plans, not a domain-wide estimate.

| Case | Children / selected open | Threat expansions | Children / selected threat | Ordered sampled pairs | Structural samples |
|---|---:|---:|---:|---:|---:|
| thoughtful-p01 | 35.1 | 56.3% | 1.069 | 93.6% | 94 |
| pipesworld-tankage-p01 | 173.8 | 21.0% | 1.007 | 92.7% | 5 |
| pipesworld-notankage-p01 | 97.2 | 14.2% | 1.009 | 95.8% | 7 |
| sokoban-p02 | 9.5 | 72.9% | 1.019 | 95.3% | 163 |
| parcprinter-p05 | 2.6 | 84.2% | 1.003 | 50.9% | 256 |
| pegsol-p01 | 7.8 | 50.1% | 1.111 | 94.5% | 146 |
| freecell-p02 | 58.2 | 37.3% | 1.070 | 77.4% | 20 |

These observations sharpen the proposed explanations:

* **Supporter branching is prominent in Pipesworld and Freecell.** LR reduces
  emitted children per selected open from 174 to 23 in Tankage, 97 to 14 in
  NoTankage, and 58 to 8 in Freecell. These are different search trajectories,
  not matched partial plans. NoTankage p01 is the associated coverage recovery;
  the branching reductions alone do not solve Tankage or Freecell.
* **Threat processing dominates expansions in Sokoban and Parcprinter, with
  about one emitted child per selected threat.** Their means of 1.019 and 1.003 children per selected threat
  show repeated ordering work; they do not demonstrate a binary
  promotion/demotion explosion.
  These averages do not give the fraction of zero-, one- and two-child threats,
  or the fraction of runtime spent handling them. A bounded closure of forced
  classical threat resolutions is a concrete next experiment. Existing
  disjunctive-order propagation is not this experiment: a selected new threat
  still emits a queued refinement.
* **Much of the sampled ordering is already fixed.** ADD's Sokoban and Pegsol
  pair comparability is about 95% and 94%. Parcprinter is about 51%, so a single
  explanation based on almost-total orders does not fit all seven cases.
  Tankage/NoTankage have only five/seven structural samples and 41/71 pairs;
  their high ratios are especially weak evidence about typical plans.
* **Repeated operators do not demonstrate equivalent partial plans.** Sampled
  repeat fractions are about 12% in Sokoban and 7% in Pegsol, but zero in
  Tankage and Freecell under this profile. These measure repeated grounded
  actions within a sampled plan, not duplicate states across plans.

All v2 structural samples meet the size bounds, so none are skipped. Sampling
is deterministic, not random. Parcprinter ADD reaches the 256-sample ceiling;
its structural counts therefore cover an earlier prefix than the all-expansion
counts. FFR solves Parcprinter in 283 expansions and samples only the empty
root, so its comparability and repeat ratios are undefined, not zero. The JSON
summary retains denominators and all 21 profile/case records.

Existing forced restorers occur in these classical trajectories: 59 of 730
sampled threat occurrences in Sokoban/ADD, 15 of 1,275 in Parcprinter/ADD,
18 of 486 in Thoughtful/ADD, and 16 of 290 in Pegsol/ADD. These are repeated
observations, not distinct rescue opportunities or successful white-knight
refinements. They justify a small semantics-correct white-knight pilot; they
do not yet show that this will improve coverage, and the paper's post-hoc
optimization results cannot supply that missing generative-search evidence.

## Configurations and next direction

The current useful candidates are FFR with standard ZLIFO for Parcprinter,
ADD with LR for cheap NoTankage/Pegsol solutions, and FFR with LR for a different
combination of solved cases. None warrants replacing the default. The tested
preferred refinement queue adds no solutions on the first seven FD-gap cases,
although it remains helpful on the earlier Rovers/Logistics memory cases.

Reproduce the ranking and flaw settings below, replacing DOMAIN and PROBLEM
with the paths in the corresponding manifest. These commands apply the planner's
15-second and 512-MiB soft RSS stops; use the recorded Python harness for the
20-second watchdog, 1,536-MiB process address-space cap, provenance and replay.

```sh
target/release/potoroo --fdr-pocl -s A -w 1 -h FFR/LIFO -f ZLIFO -p none --time-limit 15 --stage-mem-mb 512 -l unlimited DOMAIN PROBLEM
target/release/potoroo --fdr-pocl -s A -w 1 -h ADD/LIFO -f '{n}LIFO/{o}0LIFO/{o}1NEW/{o}LR/{s}LIFO' -p none --time-limit 15 --stage-mem-mb 512 -l unlimited DOMAIN PROBLEM
```

Changing the second command's heuristic to `FFR/LIFO` gives the FFR/LR profile.
For exact performance reproduction use the archived `ff-ffocr-frozen/potoroo`
binary named in each manifest. `target/release/potoroo` contains the later
read-only diagnostic observer and constructor fix.

The next implementation priority is to reduce forced threat-resolution nodes
and measure their runtime contribution, while retaining LR as a separate
supporter-branching control. A white-knight pilot needs coordinated threat,
pruning and solution-validation changes and should follow explicit soundness
fixtures. Neither full state progression, deadlock-specific reasoning nor
canonicalization has been implemented or validated in this round.

## Review and validation

The final run10 review is **partial, same-family/provisional**. It independently
verified 224 included runs, 971 artifact-hash entries and 47 successful SAS
replays, including all 21 corrected diagnostic pairs. The 42 superseded v1
runs and the earlier run09 suites are outside those totals. No remaining
measurement blocker was found for the scoped results. Broad FF superiority,
causal bottleneck explanations and white-knight performance gains remain
unsupported. The review explicitly corrects its earlier missed constructor
output defect.

Relevant library and CLI tests pass (245 + 14, one diagnostic test ignored);
release build, formatting and diff checks pass. The raw review, structured
verdict and audit are in `.aris/traces/result-to-claim/2026-11-07_run10/`.
No formal `EXPERIMENT_AUDIT.json` exists. The next route is to retain the local
claims and investigate the measured mechanisms, not to claim general coverage
improvement. The subsequent per-condition attribution is reviewed separately.


## Condition-level attribution

The observer now also counts the exact FDR fact of every selected open condition
and the protected fact of every selected threat. This is an all-expansion count,
not the earlier structural sample. The new 21-run follow-up uses the same seven
cases, three profiles and 500,000-generated-node budget. All tracked search
summaries and every earlier aggregate diagnostic counter match the frozen v2
runs. Both returned plans pass independent SAS replay. Variables are mapped
back to their exact captured SAS labels, with pruning disabled so indices are
unchanged. Predicate totals reconcile with the per-fact and global counters.

For **ADD/ZLIFO**, the main conditions are:

| Task | Observed condition | Share of work in this trajectory |
|---|---|---|
| Thoughtful p01 | `talonplayable(card)` | 45.5% of open-condition children; 80.6% of threat expansions |
| Pipesworld Tankage p01 | `normal(pipe)` | 70.4% of open-condition children; about 521 children each time selected |
| Pipesworld NoTankage p01 | `normal(pipe)` | 76.7% of open-condition children; about 253 children each time selected |
| Freecell p02 | `colspace(n)` and `cellspace(n)` | 87.8% of open-condition children; 90.6% of threat expansions |
| Sokoban p02 | `at(player-01, location)` | 84.4% of open-condition children; 89.0% of threat expansions |
| Parcprinter p05 | `location(sheet, location)` | 85.8% of open-condition children; 99.0% of threat expansions |
| Pegsol p01 | `move-ended` and `last-visited(location)` | 94.5% of threat expansions; `free`/`occupied` still produce 63.3% of open-condition children |

“Open-condition children” means all emitted children of selected open flaws,
after internal refinement checks and before outer pruning or the generated-node
stop. These totals can exceed the generated-node budget. “Threat expansions”
counts selected threats, not every threat present and not CPU time. Repeated
visits to the same fact are counted repeatedly. These are seven individual task
trajectories, not domain-wide causal estimates.

The condition meanings materially refine the earlier hypotheses:

* **Pipesworld is spending much of its supporter branching on a transaction
  control flag.** `normal(pipe)` holds outside a split push/pop operation;
  `push-updating` and `pop-updating` mark the intermediate phases. In Tankage,
  each observed `normal` fact has 520 grounded achievers: 360 `pop-end` and 160
  `push-end` actions. NoTankage's `normal(s12)` has 252 (126 of each). Many batch
  choices can therefore support the same mode fact. The observed children are
  overwhelmingly fresh action insertions. Tank occupancy adds branching in
  Tankage, but does not explain the common dominant condition in both variants.
* **Freecell branches on exact free-space counts.** `colspace(coln2)`, for
  example, has 124 grounded achievers; `cellspace(celln1)` has 252. Their action
  families move many different cards while producing the same capacity count.
  This is consistent with capacity-related supporter ambiguity, not just
  ambiguity about which card should sit on another.
* **Thoughtful concentrates on which talon card is playable.** A selected
  `talonplayable` condition emits about 499 children on average. For example,
  `talonplayable(s7)` has 658 grounded achievers across talon-to-column,
  talon-to-home and deck-turning actions. `clear` is the next largest contributor
  to emitted children, at 19.6%.
* **Sokoban is dominated by player routing in these counters.** Stone-location
  threats account for fewer than 1% of all selected threats under ADD/ZLIFO;
  player location accounts for 89%. This does not establish that box deadlocks
  are unimportant to solving the task, but it identifies the main observed
  causal-link maintenance burden more precisely.
* **Parcprinter is routing-dominated, not equipment-availability-threat
  dominated in this encoding.** `available` has zero selected threats. Static
  SAS inspection confirms its only assignments are the 14 positive effects of
  `initialize`; the routing operators preserve availability. Their PDDL add and
  delete effects on availability cancel in the atomic transition semantics.
* **Pegsol's move-control sequence is particularly visible.** `move-ended`
  permits a fresh jump; `last-visited` connects a continued jump and the
  `end-move` action. Together they account for almost all selected threats,
  although occupancy facts still dominate open-condition children.

This pattern is configuration dependent. ADD/LR shifts the dominant open-child
predicate to `last` in Tankage and `first` in NoTankage, while Freecell shifts
from capacity counters to `clear`/`incell`. With FFR/ZLIFO, `normal` still
contributes 46.7%/59.5% of open children in Tankage/NoTankage, and Freecell's two
space counters contribute 73.1%. Sokoban player location remains the largest
threat contributor in ADD/LR (87.0%) and FFR (71.8%). FFR's successful
Parcprinter run has only 92 selected threats, so comparing its percentages to
ADD's 384,035 must retain those denominators.

Links whose producer is INIT account for only 7.6% of selected threats in
Sokoban and 2.9% in Parcprinter under ADD/ZLIFO. Thus the measured threat work
mostly concerns links protecting facts established by inserted actions; their
consumers can include GOAL. This does not test how optimistic initial
facts affect heuristic ranking, so it cannot rule out that separate guidance
issue.

All observed Pipesworld `normal` facts are true in the initial state. The
native ADD table and FF graph seed these facts at zero individual support cost
from that original state (`build_base_relaxed_values` and `ff::Graph::build`).
That connects this attribution to the earlier initial-state guidance concern:
a control condition can add no relaxed support cost while actual refinement
still considers hundreds of ways to establish it at a particular consumer.
It is a concrete target for order-aware initial support, not evidence that this
change would by itself solve Pipesworld.

The new implementation direction suggested by these measurements is to delay or
constrain supporter selection for high-achiever control/resource conditions,
using the selected operation's other preconditions to narrow the alternatives.
For Sokoban/Parcprinter, the corresponding target is coherent player/sheet
routing and forced ordering work. Pairing split pipe operations or introducing
route macros requires a separate soundness and coverage experiment; neither has
been implemented here. The evidence does not justify pruning supporters solely
because their effect predicate is frequent.

Artifacts: `ff-gap-condition-summary.json`, `ff-gap-condition-attribution.json`
(per-fact counts and exact labels), `ff-gap-condition-static.json` (grounded
achiever families and availability assignments), and the frozen source/binary
and validation metadata with the same prefix. Relevant tests, release build,
formatting and diff checks pass. The separate condition-attribution review
supports these scoped descriptive claims (same-family/provisional). It verified
21 runs, 97 artifact-hash entries, two successful plan replays, all predicate
and first-argument mappings, and 28 static achiever examples across seven SAS
tasks. No blocker was found. Runtime causation and improvement from the proposed
changes remain untested. See run10's `004-conditions.response.md` and
`condition-verdict.json`; the completed v2 verdict remains separately scoped.

## Testing the condition-driven targets

The subsequent [targeted refinement report](targeted-refinement-findings.md)
records 136 runs testing bounded support selection (B8) and opt-in forced
classical threat propagation. B8/FFR combines the ZLIFO and LR solved sets on
the 14 hard cases: four solves, compared with three for either old FFR policy
and two for ADD/LR. It does not add a new case to their union. The three FFR
variants tested on the six ADD-success controls fail all six; standard ADD
solves all six.
The broader objective of improving over ADD remains unmet.

Propagation changes none of the 41 matched solved/failed outcomes. It reduces
queue visits but leaves large frontiers and memory failures. The report records
the positive Pegsol plan-cost result, higher Pegsol memory use, substantial
Parcprinter policy tradeoffs, verified plan replay, and the decision to keep
defaults unchanged and stop expanding this propagation experiment.
