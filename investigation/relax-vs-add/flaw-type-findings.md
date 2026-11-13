# Flaw types, goal focus and early conflict exposure

This follow-up tests the user's hypothesis that treating different flaw types
uniformly contributes to the weak FFR results. Branch: `investigate/relax-vs-add`.
Defaults remain unchanged.

## Protocol fixed before the screen

The screen uses eight existing orders: LCFR, LCFR-Loc, LCFR-Conf,
LCFR-Loc-Conf, MC-Loc, MW-Loc, MW-Loc-Conf and DUnf-LIFO. Every run uses
FFR/LIFO, A, weight one, no pruning and no preferred queue. Seven previously
diagnosed hard cases and six ADD-success controls give 104 runs. The binary
is the unchanged `ff-target-frozen` binary from the previous round. Its
ADD/ZLIFO and FFR/ZLIFO/B8 baseline records on these cases are reused;
cross-round single timings will not be presented as speed improvements.

Limits remain 15 seconds including translation, 20-second watchdog, 512 MiB
soft planner RSS and 1,536 MiB per-process address space, unlimited generated
nodes. Runs are serial, diagnostics disabled, with captured input/SAS hashes
and independent replay of all returned plans. No compiler or tests run during
the serial performance screen. These cases have all been seen previously.

At most two policies will advance if they add target solves or recover ADD
controls. Follow-up will use matched ADD and second instances to distinguish
a flaw-order gain from an FF-specific advantage. Selection is adaptive and
will be documented. No new numerical threshold is tuned in this round.

## Meaning of the types

In native FDR search, `o` is any open condition; `l` belongs to the newest
unfinished action (identified by the head of the outstanding-open chain);
`u` has a possible preceding step whose active effect can overwrite its fact;
`t` is on a variable no operator changes. The `u` predicate is potential
interference, not proof that every possible supporter is threatened.

`n` and `s` select non-confrontable and confrontable threats in the ground
representation. On this unconditional, axiom-free FF panel there are no
conditional-effect confrontation alternatives and no unbound variables, so
all threats are `n`. Separating `n` from `s` cannot explain differences here.
The local/conflict orders and delay of multiply repairable threats are the
useful distinctions to test.

LCFR's four variants cross all versus local open conditions with unsafe-first
versus no unsafe priority. MC/MW select higher additive estimated cost/work
within their eligible open conditions. These are flaw-order estimates even
though whole plans are ranked with FFR. DUnf-LIFO selects threats with zero or
one repair first, then opens, then remaining threats.

The definitions and motivation follow VHPOP's
[local flaw selection](https://www.cs.cmu.edu/afs/cs/project/jair/pub/volume20/younes03a-html/node12.html)
and [conflict-driven flaw selection](https://www.cs.cmu.edu/afs/cs/project/jair/pub/volume20/younes03a-html/node14.html).
These sources motivate the policies; their reported results are not evidence
that they improve this planner on the current domains.

## Results

The old-code screen completed all 104 runs and independently replayed ten
returned plans. LCFR and LCFR-Loc each solve NoTankage p01 and Parcprinter p05;
the other six policies solve only Parcprinter p05. Every policy fails all six
ADD-success controls. Thus these policies add no coverage to the previous
FFR/ZLIFO/B8 solved-set union on this panel.

On Parcprinter, local LCFR generates 4,662 nodes versus global LCFR's 112,557;
unsafe-first LCFR generates 404 (434 with local fallback), versus standard
FFR/ZLIFO's 602 from the matched frozen baseline. All cost 25. The unsafe-first
orders fail NoTankage, where LCFR and LCFR-Loc succeed. These measurements show
a case-specific policy tradeoff, not a universally better flaw type. The
corrected-work screen below must be evaluated separately.

## Implementation mismatch found during the audit

The original native FDR implementation seeds initial and reused facts with
zero work, and minimizes work independently of additive cost. For unit-cost
operators without axioms this collapses work to additive action cost, apart
from numeric limits. Thus the old screen's MW policies do not test VHPOP's
distinct effort estimate faithfully.

VHPOP's [effort definition](https://www.cs.cmu.edu/afs/cs/project/jair/pub/volume20/younes03a-html/node7.html)
charges one refinement for an initial causal link and propagates effort along
cost-minimizing support. The literal planner already distinguishes zero cost
and unit work. The native correction now charges initial/reused support
one link, makes effort follow minimum additive cost with minimum effort on
cost ties, and keeps large finite effort distinct from the unreachable
sentinel. Derived-support expansion also counts one refinement; that is the
native axiom extension, not a claim about the paper's axiom-free setting.
Existing additive costs and RELAX's achiever tie policy are preserved.

The corrected follow-up is fixed before its results: on the same 13 cases,
test FFR/MW-Loc, FFR/MW-Loc-Conf, FFR with ADD_WORK as a tie-breaker and ZLIFO,
FFR with that tie-breaker and MW-Loc, and ADD with that tie-breaker and MW-Loc
(65 runs). All retain A, weight one and trailing LIFO. The first two have
matched old-code profiles in the original screen; the other profiles are
combined configurations and will not isolate the work correction by themselves.
The ADD comparison distinguishes an FFR-specific advantage from a general
search-control gain. The original 104 runs remain an old-code screen.

Separately, a new read-only diagnostic records selected open conditions as
local, unsafe, initially true, goal, static, blocked INIT support, potential
FFR reuse and reuse blocked for every eligible producer. A forced blocker is
an unconditional non-suppressed deletion necessarily between producer and
consumer; the consumer's own post-effects are excluded. Passing this check
does not prove a support link feasible. Counts use disjoint bitmask buckets,
while named types overlap. We compare the old binary, corrected binary with observers off, and corrected
binary with observers on at 100,000 generated nodes: four fixed profiles over
13 cases, or 52 triples (156 runs). Time/memory stops invalidate a triple.
Agreement covers recorded outcomes and counters, not complete traces or
zero timing overhead. This is separate from timed performance runs.

The release build succeeds. Selected validation passes 259 library tests,
14 CLI tests and 19 additive/FDR/review integration tests (292 total, one
ignored library test). Eight new tests exercise effort propagation, finite
saturation, selected-flaw categories and conservative clobber classification.
This is not a full repository test run. The new binary and 108-file source
archive are frozen in `ff-types-diagnostic-frozen.json`; validation logs and
hashes are recorded in `ff-types-validation.json`.

## Selected-flaw diagnostics

All 52 old/off/on triples completed without time or memory stops. The old and
corrected binaries, with observers disabled/enabled, agree on all 18 recorded
outcome/search fields on these cost-only profiles. The counters partition
selected opens and threats exactly; all 27 returned plans across the three
modes pass independent replay. This supports unchanged recorded behaviour for
these runs, not exact trace equivalence or zero observer overhead.

The following percentages weight selected open conditions by their emitted
children, before outer pruning, under FFR/ZLIFO. Named types overlap. Each
unsolved run ends at 100,000 generated nodes; the solved Parcprinter run ends
earlier. These are neither CPU shares nor proportions of every flaw in the
frontier. The full dataset of 52 case/profile observations from four profiles is
`ff-types-diagnostic-analysis.json`.

| Case | Unsafe | INIT link blocked | Every eligible reuse producer blocked |
|---|---:|---:|---:|
| Thoughtful p01 | 0.0% | 0.0% | 0.0% |
| Pipesworld Tankage p01 | 19.0% | 18.8% | 0.0% |
| Pipesworld NoTankage p01 | 11.4% | 9.7% | 3.8% |
| Sokoban p02 | 53.7% | 32.0% | 7.8% |
| Parcprinter p05 | 19.6% | 4.2% | 10.8% |
| Pegsol p01 | 28.7% | 24.9% | 5.0% |
| Freecell p02 | 0.9% | 0.7% | 0.1% |
| Miconic p01 | 90.7% | 7.6% | 56.0% |
| Miconic p02 | 76.1% | 4.8% | 57.2% |

These separate several failure patterns. Thoughtful's FFR prefix expands
1,523 open conditions and no threats: a threat-type priority cannot explain
that sampled search's cost. Freecell's sampled FFR search also spends almost
all of its open-child generation on conditions classified safe. Sokoban,
Pegsol and the pipe tasks expose more blocked initial support. Miconic exposes
a separate reuse problem: FFR may discount an open-condition occurrence merely
because an existing producer can precede its consumer, although a mandatory
intervening deletion prevents that classical causal link. This is overly
permissive occurrence-level reuse eligibility. It does not establish that the
whole heuristic value changes: another unfiltered occurrence of the same fact
or another extraction requirement may still retain that fact. The diagnostic
does not show that correcting this will recover any failed case.

Blocked INIT alone is not a failure classifier. Successful ADD on Gripper has
69.4–72.6% of its open children in that category; failing FFR has 85.3–89.4%,
but only 2.8–3.9% of all FFR open children lack an existing producer that passes the conservative
no-forced-clobber check. Passing that check does not establish link feasibility.
Successful ADD on Miconic also has substantial blocked support. The heuristic,
selected paths and need to restore a fact must be considered together.

No selected open is static on this panel. Every selected threat is
non-confrontable; there are no disjunctions. Under FFR/ZLIFO, 10,315 of Sokoban's
11,137 selected threats have one repair; all 92 Parcprinter threats and all
239 Freecell threats have one repair. Ground threat confrontation is therefore
not the useful distinction here. This is consistent with the previous
negative coverage result for forced unary-threat propagation, while not
claiming that threat processing is free.

The checkpoint review supports the old-code findings and correction, with no
implementation blocker, and routes to the fixed corrected-effort screen. It
is same-family/provisional; no formal integrity audit has been run. Diagnostic
and corrected-performance conclusions are being reviewed separately.
