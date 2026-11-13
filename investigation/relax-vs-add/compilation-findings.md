# Can causal-link compilation address the initial-state issue?

Historical diagnostic, before the cost correction and native full compilation.
See [the corrected follow-up experiments](compiled-ff-corrected-findings.md) for the implemented changes.

Yes, by making the **evaluated problem depend on the partial plan**. Keeping the
original world state as the compiled task's starting state is appropriate: POCL
steps are commitments to future execution, not an already-executed prefix.
Progress must appear through the committed occurrences, their execution markers,
preconditions, ordering constraints and causal links. A single concrete current
state is generally unavailable without choosing a linearization.

This sharpens the wording in the preferred-queue investigation. The cached native
FF graph and the evolving state in forward search differ materially, but the
original initial state alone is not a diagnosis. A per-node compilation can keep
those original facts while still representing the current partial plan.

## What the current code provides

| Path | Information represented | Remaining limitation |
|---|---|---|
| Native `FF`/`FFR` | Joint current open facts; FFR filters immediately reusable support | Cached original graph; facts merged across consumers; FFR reuse stops at the open frontier |
| Native `CLFF` | Rebuilds zero-cost committed actions with preconditions and completion facts; causal-link producers become predecessor requirements | Deletes relaxed; full ordering closure and link-protection guards omitted |
| Full `COMPILE_FF` | Separate committed occurrences, execution markers, full committed ordering requirements and per-link protection guards | FD FF then relaxes that encoding; cost-accounting discrepancy below |

The native path is in [cl_relax.rs](../../src/cl_relax.rs) and
[Planner::compiled_estimate](../../src/fdr_pocl.rs). The full compilation is in
[compile.rs](../../src/compile.rs), with its scalar FD evaluation in
[heuristics.rs](../../src/heuristics.rs). `COMPILE_FF` is currently a literal-plan
option (`-g` supplies the direct SAS fast path), not a native FDR POCL option.
The interface returns an estimate, not a compiled relaxed plan/preferred action
mapping. Transferring preferred actions back would require mapping them to action
insertions or reuse/support refinements.

`CLFF` already handles committed support deeper in the relaxed graph. Its existing
unit test, `a_committed_step_is_free_once_it_can_run`, checks that committing the
whole necessary chain leaves zero remaining cost. Nevertheless, it solved 0/6 of
the selected ADD-only cases in the corrected w1 matrix. That finding applies to
this relaxed native approximation, not every full compilation or backend.

## What the paper says

[Bercher, Geier and Biundo (KI 2013), Sections 3–4](https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.090/Publikationen/2013/Bercher13POCLHeuristics.pdf)
evaluate the encoded problem's initial state and define the remaining estimate as
`max(h_state(encoded_problem) - cost(partial_plan), 0)`. They explicitly report
that FF became uninformative in their experiments because relaxation affected
the actions encoding progress. Their experiments instead used LM-cut and merge
and shrink; the evaluated encoding omitted causal-link protection. This supports
testing the compilation with a suitable backend, not assuming FF transfers
unchanged.

## A concrete diagnostic

The existing full compiled path currently evaluates `g + w*h_compiled`, without
subtracting committed cost. Its SAS encoding also assigns unit cost to every
operator, including the mandatory committed copies. This disagrees with the
paper's remaining-cost convention even on unit-cost tasks. Cost handling for
non-unit original tasks additionally needs attention before a general correction.

An explicitly run [original diagnostic](initial-compile_diagnostic.rs) uses the chain
`make-p: {} -> p`, `make-q: p -> q`, goal `q`. It records the root, the partial
plan committing `make-q`, and the complete plan also committing `make-p`.
The original and committed copies are separate compiled operators.

| Committed cost g | Raw compiled FF | Current FF rank, w1 | FF remaining, subtract g | LM-cut remaining, subtract g |
|---:|---:|---:|---:|---:|
| 0 | 2 | 2 | 2 | 2 |
| 1 | 3 | 4 | 2 | 1 |
| 2 | 4 | 6 | 2 | 0 |

There are two distinct problems in this witness. Current ranking charges the
compiled cost in addition to `g`. Correcting that accounting alone still leaves
FF's remaining estimate constant at 2, even on the completed plan. Raw compiled
LM-cut stays at 2 and its remaining estimate falls to zero after subtracting `g`.
This is a two-action sanity example, not a benchmark claim about LM-cut.

Evidence: [record and hashes](compile-accounting.json), raw output in
`target/relax-investigation/compile-accounting.log`, and all three compiled SAS
tasks in `target/relax-investigation/compile-accounting/`. The diagnostic passes
and invokes the local FD FF and LM-cut evaluators. Production compilation and
cost accounting have **not** been changed by this follow-up; the preferred-queue
measurements are unaffected and never used `COMPILE_FF`.

The useful next comparison is a cost-correct full compilation with FF and LM-cut,
alongside native `CLFF`. Its promise is a more informative representation of the
partial plan. The FF relaxation can still discard that information, so the
backend is part of the research question.
