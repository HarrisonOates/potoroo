# Preferred refinements for native FF

Follow-up on `investigate/relax-vs-add`, 7 November 2026. The question is whether
FF's poor POCL performance is caused by omitting preferred operators or a related
search policy. The earlier corrected extraction and its measurements remain in
[ff-findings.md](ff-findings.md); their source/binary snapshot is preserved.

## What is implemented

`--preferred` is an optional native FDR feature for A/weighted A and GBFS. It
adds a preferred queue with the same ranking as the ordinary queue. Five queue
selections favour the preferred queue, then one uses the ordinary queue;
either falls back when empty. All admitted children enter the ordinary queue,
and both entries share materialization and expansion state. The option changes
A's expansion order and does not preserve A* ordering or promise optimality.
Defaults remain unchanged.

For each expanded parent, extract the joint FF relaxed plan for its open
conditions. Prefer a refinement if it inserts one of the extracted operators,
or if it adds no action (an existing/initial support link or ordering refinement).
Classification precedes optional forced-support propagation. With FFR ranking,
use FFR's existing-support filter; otherwise use FF, including with ADD ranking.
The supported task class is unconditional, axiom-free, unit resolved cost.

This is a POCL adaptation. Fast Downward's
[FF implementation](../../downward/src/search/heuristics/ff_heuristic.cc)
prefers extracted actions whose prerequisites hold in the **current state**.
POCL has no single current state; an action introduced to support a flaw can
itself require additional producers. Consequently this implementation considers
all extracted operators, and preserves the existing flaw-selection policy.
It is not original FF's helpful-action pruning or enforced hill climbing.

The additional STATS fields are `preferred_generated` (admitted preferred
children) and `preferred_selected` (unexpanded entries popped from that queue,
including terminal plans). Preference extraction is extra wall time outside
`h_eval_ms`. Ordinary queue occupancy includes entries already expanded through
the other queue until they are popped; it is not a unique-live-plan count.

## Controlled comparisons

The main matrix has ten profiles on each of ten previously tested problems:
ADD, FF, weighted FF (w5), greedy FF, and FFR, each with preferred off/on.
All use ZLIFO flaw selection, `/LIFO` ranking ties, no optional pruning,
200,000 generated-plan limit, 10-second planner deadline, 15-second external
watchdog, and 1 GiB address-space cap. Runs are serial, after the release build.
The same binary is used for all profiles; actual translated SAS is archived and
checked for equality within each problem.

A supplementary twenty-run matrix changes greedy FF's ranking ties to `/FIFO`,
with preferred off/on. This is motivated by Fast Downward's
[FIFO tie-breaking](../../downward/src/search/open_lists/best_first_open_list.h),
whereas our prior experiments used LIFO. It is an adaptive follow-up prompted
by greedy preferred search growing partial plans past 1,600 actions on Gripper.

Thirty Fast Downward controls use exactly the same captured SAS problems with
`astar(ff())`, `eager_greedy([ff()])`, and greedy FF with an additional preferred
queue. The latter uses FD's default boost=0 (queue alternation), not the POCL
5:1 schedule. Each has a 10-second search deadline, 15-second watchdog and 1 GiB
address-space cap, with no FD node cap. Translation is excluded from FD timing.
Generated state nodes and generated POCL partial plans are different work units;
these are implementation controls, not equal-algorithm speed comparisons.

## Results

On the six preselected ADD-only failures:

| Ranking/search | Preferred off | Preferred on |
|---|---:|---:|
| ADD, A (w1) | 6/6 | 6/6 |
| FF, A (w1) | 0/6 | 0/6 |
| FF, weighted A (w5) | 2/6 | 2/6 |
| FF, GBFS with LIFO ties | 2/6 | 0/6 |
| FFR, A (w1) | 0/6 | 0/6 |
| FF, GBFS with FIFO ties | 2/6 | 2/6 |

Every 2/6 result is the same two Gripper instances. Neither preferences nor
FIFO recover Miconic, Childsnack or Elevators under these limits. Preference
counters are nonzero in every enabled run and zero in every disabled run.
All 50 disabled main-matrix runs reproduce the earlier corrected outcomes;
solved and node-limited runs also reproduce generated counts and solution costs.
Timeout node counts vary with runtime. See [baseline checks](ff-preferred-baseline-check.json).

The controls show tradeoffs rather than a generally beneficial queue change:

| Case/profile | Preferred off: generated / cost | Preferred on: generated / cost |
|---|---:|---:|
| Parcprinter, ADD A | 200,000 limit | 152,041 / 17 |
| Parcprinter, FF A | 70,933 / 17 | 26,744 / 17 |
| Parcprinter, FFR A | 332 / 17 | 766 / 17 |
| ZenoTravel, ADD A | 176,869 / 28 | 200,000 limit |
| Satellite, ADD A | 851 / 14 | 1,915 / 14 |
| Satellite, FF A | 137,685 / 14 | 194,823 / 14 |
| Satellite, FFR A | 1,344 / 14 | 1,517 / 14 |

FF's Parcprinter improvement is about 2.65× fewer generated partial plans at the
same solution cost. ADD gains Parcprinter but loses ZenoTravel: its total remains
8/10. No tested POCL profile gains total coverage from preferences. This is a
small, deliberately selected panel, not a coverage estimate for the benchmark suite.

The LIFO/FIFO effect is concrete. On Gripper p01, greedy FF without preferences
solves in 2,068 generated plans (cost 79). Preferred LIFO times out after 6,575
plans, having reached 1,602 committed steps and 2,414 opens. Preferred FIFO solves
in 44,527 plans (cost 77); FIFO without preferences takes 42,603. On Gripper p03,
FIFO takes 139,753 off / 152,485 on (both cost 117). FIFO avoids the observed
preferred-LIFO behaviour here, but both FIFO runs need more generated plans than
ordinary LIFO's successful runs. This does not prove that every deep trajectory
is a cycle or identify a unique cause of the plateau.

The state-space controls are much stronger on this panel:

| Local Fast Downward profile | Solved / 10 |
|---|---:|
| A with FF | 5 |
| Greedy FF | 9 |
| Greedy FF + preferred | 10 |

Greedy FF **without preferences** solves Miconic p01/p02 in 1,034/1,695 generated
states; enabling preferences gives exactly the same counts and costs there.
Thus missing preferred operators alone cannot explain the native POCL failures.
The extra FD recovery is Childsnack: ordinary greedy FF times out after
30,317,280 generated states; preferred greedy FF solves in 231,888 (cost 21).
That successful FD run exceeds the POCL 200,000-node cap, which is an additional
reason not to present these results as an equal-budget coverage comparison.
Every other successful greedy FD run is below 23,000 generated states. FD's
successful plans were independently replayed against the captured SAS tasks.
These are local implementation controls, not a reproduction of the original FF
or VHPOP experimental suite.

## Interpretation

The estimates are already different algorithms. Native FF uses the released
original FF's layer/difficulty extraction; local Fast Downward uses additive
supporters and operator deduplication. More fundamentally, native extraction
starts from a cached graph rooted at the original initial facts and queries the
outstanding open conditions. Fast Downward recomputes its relaxed reachability
from each current concrete state. The native FF/FFR adaptation also merges fact
requirements across consumers; FFR discounts existing support only at the
current open-condition frontier. Adding a preferred queue does not change any
of those estimate properties.

A follow-up [compilation diagnostic](compilation-findings.md) sharpens this
point: a compiled problem may legitimately start at the original world state
while encoding all current plan commitments in its actions, goals and guards.
The representational information retained by the estimate is the issue.

These code differences establish why equal performance cannot be assumed. They
do not identify a single cause for every failed problem. A global relaxed
operator set may guide POCL poorly when consumer order and repeated action
occurrences matter. The bounded comparisons below test queue preference and
FIFO ties; they do not exhaust consumer-sensitive guidance, different flaw
selection, other queue schedules, or complete reuse-aware extraction.

## Reproduction and evidence

- `preferred_probe.py --run` and `--suite vhpop-domains`: main 100-run matrix.
- `preferred_fifo_probe.py --run` and `--suite vhpop-domains`: 20 FIFO controls.
- `preferred_fd_probe.py`: 30 state-space controls and independent SAS plan replay.
- `summarize_preferred.py`, `summarize_preferred_fifo.py`, and
  `validate_preferred_fd.py`: verify logs, hashes, commands, limits, source,
  actual SAS, preference counters and executable FD solutions.
- `ff-preferred-frozen.json`: archived source and release binary.
- `ff-preferred-validation.json`: library/CLI tests and release build logs.

The harness scripts refuse to overwrite an existing measurement CSV/JSON.
Preserve artifacts before reproducing. All 150 measurements completed. The main
summary verifies 418 artifact hashes; FIFO verifies 98. The FD validator checks
all 30 controls, sequential timestamps, executable solutions and SAS equality
with the POCL inputs. Library tests: 234 passed, one ignored diagnostic; CLI
checks: 14 passed. The tests cover ordinary-queue turns, duplicate expansion,
nonpreferred solutions, storage equivalence, and unsupported configurations.

Keep ADD as default and `--preferred` experimental. The option helps particular
cases but does not close the FF/FFR gap. A useful next investigation is guidance
that retains consumer/order information and handles committed support throughout
extraction. The present results do not establish that this extension will work.


## Review

The fresh result-to-claim reviewer confirmed the seven scoped implementation and
descriptive claims with high confidence, identifying no correctness or measurement
bug in this change. It independently checked all 516 main/FIFO hashes, 50 baseline
comparisons and the 30 FD controls with executable solution replay. Full
[review](../../.aris/traces/result-to-claim/2026-11-07_run05/001-review.response.md).
Acceptance remains provisional (same family; exact serving identity unknown),
and formal integrity-audit status is unavailable. This review excludes the
subsequent [compilation diagnostic](compilation-findings.md).
