> SUPERSEDED: review found invalid relaxed extraction on cyclic support. These initial FF/FFR measurements must not support final performance claims. See ff-findings.md for corrected results.

# FF with potential action reuse in POCL

Investigation on `investigate/relax-vs-add`, 7 November 2026.

The first controlled comparison does not support replacing ADD with FF. Joint
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

Both use [Hoffmann and Nebel's FF extraction](https://arxiv.org/pdf/1106.0675),
§§4.2–4.3/Figure 2: parallel first-appearance levels, NOOPs first, minimum summed
precondition levels for supporter choice, and marking all selected effects at
the current and preceding extraction layer. Equal-level facts and tied
operators use ascending indices. This differs from RELAX's additive-cost
achievers and RePOP's serial graph. Existing `CLFF` evaluates a causal-link
compilation using additive achievers; it is another relevant baseline.

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
| FF, w1 | 0/6 | 57,379 nodes, cost 17 |
| FF, w5 | 2/6 | 22,499 nodes, cost 17 |
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
by about 173 times while preserving cost 17. It is a matched comparison of
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

All 90 benchmark runs have final statistics and recorded provenance. The
initial validation passed 229 library tests (one diagnostic ignored),
13 CLI tests, the release build, and `git diff --check`. New tests cover shared
future producers, effects shared across extraction layers, parallel levels,
difficulty-based support selection, unreachable goals, rejected task features,
preprocessing deadlines, order-incompatible reuse, self-support, per-occurrence
reuse filtering, and retention of committed steps' open preconditions.

Reproduction and audit artifacts:

- [ff_probe.py](ff_probe.py), [ff-manifest.json](ff-manifest.json),
  [ff.csv](ff.csv), [ff-provenance.json](ff-provenance.json).
- [summarize_ff.py](summarize_ff.py), [ff-summary.json](ff-summary.json),
  [ff-validation.json](ff-validation.json). The summary checks every row
  against its final log, source and binary hashes, limits, and input hashes.
- [ff-vhpop-domains.csv](ff-vhpop-domains.csv),
  [ff-vhpop-domains-provenance.json](ff-vhpop-domains-provenance.json).
- [ff-frozen.json](ff-frozen.json) records the archived measurement source and
  binary. The subsequent source change only extends the test witness above.
- Raw process logs are under `target/relax-investigation/ff/` and
  `target/relax-investigation/ff-vhpop-domains/`.

Run `python3 investigation/relax-vs-add/ff_probe.py --run` after building the
release binary to reproduce the first matrix; add `--suite vhpop-domains` for
the second. Preserve the existing artifacts before rerunning. Defaults remain
ADD; `FF` and `FFR` are experimental options.
