# Bylander's Lplan: what he left for future work, and where it stands

Reading notes on Tom Bylander, *A Linear Programming Heuristic for Optimal
Planning*, AAAI-97, pp. 694–699, against Potoroo's implementation in
`src/lplan.rs`.

## What the paper does

A propositional STRIPS instance plus a plan-length bound `l` is translated into
a 0–1 integer program; relaxing the variables to `[0,1]` gives an LP. Feasibility
is monotone in `l`, so the smallest feasible `l` is an **admissible** lower bound
on plan length — "to my knowledge, this is the first non-trivial admissible
heuristic for partial-order planning."

The encoding is the one Potoroo implements:

- condition variables `p(0)…p(l)`, operator variables `op(0)…op(l-1)`;
- at most one operator per time point, `1 ≥ Σ op(t)`;
- precondition inequalities, in both polarities;
- frame axioms with **correction variables** (`op2_a(0)`, `op1_d(0)` in his
  notation) for "the postcondition was already true/false before the operator
  applied", each bounded by its operator variable.

Those correction variables are the `a`/`d` variables in `solve_horizon`, and
they dominate the model: three constraints per operator-effect per time step.

Bylander notes an optimisation Potoroo does not currently apply: *"Often,
negative preconditions are added to operators if possible to avoid the creation
of additional variables."* An operator that already requires `fct` false needs
no `d` correction for deleting it — `solve_horizon` has exactly this check
(`if neg_pre[oi].contains(&fct) { continue; }`), but nothing *adds* such
preconditions where they would be sound.

### Where Potoroo deliberately diverges

The paper's "Partial-Order Planning" section encodes ordering constraints with
step variables `s1(i)`, `s2(i)` meaning "step applied at or before time `i`",
tied to the operator variables and to each other (`s2(i) ≤ s1(i-1)` for
`s1 ≺ s2`). Potoroo does not implement that. It instead feeds the state-based
encoding the ground **causal-link compilation**, which bakes the partial plan
into a classical task. `src/lplan.rs` documents this choice. It is worth
revisiting: the step-variable encoding is the author's own and may be tighter or
cheaper than compiling, and nobody has compared them.

## The stated future work

Four statements, verbatim:

1. *"Furthermore, because linear programming variables are not restricted to
   binary values, I believe that this approach has great potential for
   incorporating utility, probabilistic operators, and lack of knowledge about
   the environment. However, the results in this paper are restricted to
   propositional STRIPS planning. Future research will consider these more
   general problems."*
2. *"Often, Lplan expanded a small number of nodes. Future research will attempt
   to find more efficient versions of this heuristic."*
3. *"In the future, I intend to obtain results for larger random planning
   instances."*
4. Conclusion: *"Future research will focus on more efficient use of the linear
   programming heuristic and more efficient versions of the heuristic."*

So: **(a)** make it cheaper, **(b)** make it stronger, **(c)** evaluate at
larger scale, **(d)** generalise beyond propositional STRIPS.

## Where each stands in Potoroo

### (a) More efficient use — largely achieved

Bylander solved with the CPLEX barrier solver and reports *"each heuristic value
required around a second of CPU time"* on a Sun UltraSparc. Potoroo with the
`highs-lp` backend evaluates a node in **~6 ms** on the Sussman anomaly (264 ms
across 42 nodes). Hardware confounds the comparison, but the gap is two orders
of magnitude and the paper's own framing — Lplan visits few nodes but each node
is too expensive — no longer bites as hard.

Measured on this branch's parent:

| | per node |
|---|---|
| microlp (default backend) | ~33 ms |
| HiGHS, one thread, presolve on | ~6 ms |
| Bylander 1997, CPLEX barrier | ~1000 ms |

Remaining cost is structural rather than solver-bound: ~28% HiGHS presolve, ~18%
model construction, ~10% simplex. Two cheap-looking fixes were measured and
rejected — reordering the horizon scan is a regression (143 → 158 probes), and
building once at the cap to warm-start needs a 9–62% saving just to break even,
because early probes are 4–29× cheaper than cap-sized ones.

### (b) More efficient *versions* — untouched, and the real gap

This is where the heuristic actually loses, and the paper diagnoses it itself.
Because operator variables may be fractional, conflicting operators can each
half-fire and their effects superpose:

> This "superposition" of operators in relaxed solutions is a major reason why
> the heuristic can lead to poor results.

Tower of Hanoi is his stated pathological case: the heuristic returns `2n` where
the optimal plan is `2^n − 1`, "exponentially bad for this domain".

`tests/lplan_superposition.rs` pins this in Potoroo. On `hanoi-3` (optimal 7),
`h(init) = 4` — *below* the horizon cap of 6, so this is the relaxation being
loose, not the scan being truncated, and it is weaker than the `2n = 6` the paper
predicts for its own encoding. On Sussman, `h(init) = 3`, exactly optimal.

That weakness has downstream consequences measured on the parent branch: a
frequently-capped, uninformative bound makes A\* explore *more*, not less. On
`test-ferry`, Lplan visits 720 nodes against `ADD`'s 251, and Lplan solves 2 of 5
benchmark instances where the default solves 5.

### (c) Larger instances — easy, and now affordable

The paper stops at 14 blocks and 10 goals. `scripts/gen_instances.py` already
generates scaled logistics and gripper instances, and at ~6 ms/node rather than
~1 s/node the original experiment is cheaply repeatable at larger sizes.

### (d) Utility, probabilistic operators, incomplete knowledge — out of scope

Potoroo targets the classical IPC 2027 fragment. Noted for completeness; not a
direction for this planner.

## Directions worth pursuing, ranked

1. **Tighten the relaxation against superposition.** The single thing that would
   change Lplan's standing. The obvious lever is that `Σ op(t) ≤ 1` bounds the
   *sum* but not the *support* — his own example has two operators at 0.5 each,
   summing to exactly 1. Candidate tightenings: mutex constraints between
   operator pairs whose preconditions and postconditions conflict, in the spirit
   of Graphplan mutexes; or integrality cuts on such pairs. Each must be checked
   to preserve admissibility — a cut valid for every integer solution is safe.
2. **Compare the step-variable encoding against the causal-link compilation.**
   The author's own partial-order encoding has never been measured against
   Potoroo's substitute. It may be smaller (no compilation indicator facts) and
   it keeps the partial order explicit rather than compiling it away.
3. **Add negative preconditions where sound**, the paper's own suggestion, to
   suppress `d` correction variables. Mechanical, and it attacks the part of the
   model that dominates its size.
4. **Repeat the paper's scaling study** at sizes it could not reach.

Direction 1 is the research contribution; 3 is the cheap engineering win; 2
answers a question the codebase explicitly leaves open.

## Context worth knowing

Bylander's "more efficient versions of the heuristic" was, in effect, answered by
later work he could not have cited: the operator-counting LP framework
(Pommerening, Röger, Helmert & Bonet, ICAPS 2014) and the state-equation
heuristic (Bonet 2013) drop time-indexing entirely — one LP with a variable per
operator and a constraint per fact, no horizon and therefore no scan. They are
strictly cheaper than a time-indexed encoding and admit landmark and flow
constraints that address exactly the superposition looseness. Adopting that
framing would no longer be "Lplan" as the paper defines it, so it belongs
alongside the heuristic rather than replacing it — but it is the honest answer to
what the paper asked for.
