# Potoroo

A modern partial-order causal-link (POCL) planner written in Rust.

The aim is to provide a correct, fast, and well-documented POCL planner that
brings together heuristics from across the literature, including approaches
whose original source code has been lost. Potoroo is intended as a platform for
future POCL planning research.

Potoroo supports lifted, ground, and finite-domain planning, with classical POCL
heuristics, causal-link relaxations, landmarks, and optional pruning rules.
The name comes from the [potoroo](https://en.wikipedia.org/wiki/Potoroo), a small
Australian marsupial.

## Build

Install stable [Rust](https://rustup.rs), then:

```bash
git clone https://github.com/HarrisonOates/potoroo.git
cd potoroo
cargo build --release
cargo test
```

The executable is `target/release/potoroo`. The default build is pure Rust.
For a faster Lplan LP backend, use `cargo build --release --features highs-lp`;
this also requires CMake and a C++ compiler.

### Fast Downward

[Fast Downward](https://github.com/aibasel/downward) is required for finite-domain
search (`--fdr-pocl`), `LPSAS`, and `COMPILE*` heuristics. Ground mode (`-g`) uses
its reachability-based grounder when available and otherwise falls back to naive
instantiation.

```bash
git clone https://github.com/aibasel/downward.git
cd downward
python build.py
export POTOROO_FD="$PWD/fast-downward.py"
export POTOROO_DOWNWARD="$PWD/builds/release/bin/downward"
cd ..
```

Alternatively, put `fast-downward.py` on `PATH`. `POTOROO_DOWNWARD` selects the
C++ executable used to evaluate compiled tasks. Tests requiring Fast Downward
skip automatically when it is unavailable.

## Run

```bash
# Lifted POCL with the default ADD/LIFO ranking
./target/release/potoroo examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl

# Greedy search
./target/release/potoroo -s GBFS -h ADD examples/gripper-domain.pddl examples/gripper-4.pddl

# Ground actions with the Lplan LP heuristic
./target/release/potoroo -g -h LPLAN examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl

# Finite-domain POCL, with progress on stderr
./target/release/potoroo --fdr-pocl -v examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl
```

Input files may appear in either order; a single file or stdin may contain both
domain and problem. Plans go to stdout. `-v` reports search progress on stderr;
`POTOROO_STATS_JSON=1` adds machine-readable statistics. An unsolved problem prints
`no plan` and a reason; a nonzero exit status indicates an error.

Defaults: lifted representation, A* search, `ADD/LIFO`, `STATIC` flaw selection,
task action costs, weight 1, and no optional pruning. Explicit `-h` replaces the
whole ranking: `-h ADD` omits the default LIFO tie preference.

## Command reference

Use `-H` for help (`-h` selects a heuristic) and `-V` for the version.

| Option | Purpose |
|---|---|
| `-g`, `--ground-actions` | Instantiate actions before literal POCL search. |
| `--fdr-pocl` | Search over Fast Downward's multi-valued SAS+ variables. |
| `-h`, `--heuristic HEUR` | Rank plans; compose up to four heuristics with `/`. |
| `-f`, `--flaw-order ORDER` | Select the flaw to refine within a plan. |
| `-s`, `--search-algorithm ALG` | Select a search algorithm; see below. |
| `-w`, `--weight W` | Heuristic weight; default `1.0`. |
| `-a`, `--action-cost TASK\|UNIT` | Use declared action costs or unit costs. |
| `-p`, `--prune RULES` | Comma-separated optional pruning rules. |
| `-l`, `--limit N` | Generated-node limit; default `unlimited`. Repeat with `-f` for search tiers. |
| `--time-limit SECS` | Wall-clock limit, including translation. The short form `-T` uses **minutes**. |
| `--max-queued N` | Cap queued plans by discarding the worst. |
| `--mem-mb M` | Trim queues toward an RSS budget. |
| `--stage HEUR[@ALG][=SECS]` | Add a restart stage; repeat for a portfolio. |
| `--stage-mem-mb M` | Stop a stage at its RSS limit and advance to the next. |
| `-v`, `--verbose` | Progress reporting; repeat for more frequent updates. |

`--max-queued` and `--mem-mb` discard search states and make search incomplete.
RSS limits are sampled, so the process can exceed them between checks.

Finite-domain search stores deferred new-step recipes directly in eager
single-queue entries. Alternating queues share recipes so they can recognize
already-expanded plans; lazy search retains materialized plan pointers.
Large finite-domain queues grow their capacity in smaller increments. These
storage changes preserve search order and retain all admitted alternatives.

### Search algorithms

| `-s` | Behaviour |
|---|---|
| `A` | A* / weighted best-first search; default. |
| `IDA` | Iterative-deepening A*. |
| `HC` | Hill climbing. |
| `BFS` | Breadth-first search. |
| `GBFS` | Greedy best-first search. |
| `LGBFS` | Lazy GBFS: score children when popped. |
| `LGBFS-D` | Lazy GBFS with a secondary FIFO queue. |
| `ALT` | Alternate A* and GBFS queues. |

### Heuristics

Compose rankings lexicographically, e.g. `-h ADD/OC/LIFO`. FIFO/LIFO terms compare
exact integer plan IDs. In the table, “literal” means lifted or `-g` search;
“FD” means Fast Downward must be installed.

| Heuristic | Representation / requirement | Estimate |
|---|---|---|
| `OC`, `UC`, `BUC`, `UCPOP` | Any | Open conditions, threats, or structural combinations. |
| `FIFO`, `LIFO` | Any | Oldest/newest generated plan first. |
| `ADD`, `ADD_COST`, `ADD_WORK` | Any | Additive relaxed cost or work. |
| `ADDR`, `ADDR_COST`, `ADDR_WORK` | Any | Additive estimates with committed-action reuse. |
| `RELAX`, `RELAXR` | Any | Joint relaxed-plan cost, without/with reuse. |
| `REPOP` | `--fdr-pocl`; unconditional, axiom-free unit-cost tasks | Published §3 regression recurrence using serial planning-graph levels. |
| `FF`, `FFR` | `--fdr-pocl`; unconditional, axiom-free unit-cost tasks | Joint parallel FF extraction sharing future actions, without/with order-compatible existing-step reuse. |
| `FFOC`, `FFOCR` | `--fdr-pocl`; unconditional, axiom-free unit-cost tasks | Sum a separate FF support-plan size for every open-condition occurrence; `FFOCR` first discounts order-compatible existing support. |
| `TADD`, `TADD_H` | `--fdr-pocl` | `ADD` plus value-token shortfalls: each committed step that overwrites a value it requires needs its own production of that value. `_H` omits the plan cost (tie-breaking). |
| `FLOW`, `FLOW_H` | `--fdr-pocl` | Per-variable min-cost token flow over domain transition graphs; plans with no feasible flow are pruned. |
| `HYB` | `--fdr-pocl` | `TADD` + ½ `FLOW`. |
| `CLADD`, `CLFF` | `--fdr-pocl` | Causal-link compilation evaluated natively. |
| `LMCUT`, `LMCUTR` | `--fdr-pocl`; unconditional SAS+ effects | LM-cut, without/with reuse. |
| `LM` | Any | Unachieved landmarks: lifted or ground according to representation. |
| `LMO`, `LMF`, `LMFO` | Literal | Landmark ordering, FAM cuts, or both. |
| `LPLAN` | `-g` | Bylander's time-indexed LP relaxation. |
| `LPSAS`, `LPSAS:MIP`, `LPSAS:MIP50` | `-g`, FD | SAS+ LP, integral operators, or a per-probe MIP budget in milliseconds. |
| `SAMPLE_FF`, `SAMPLE_FF:k` | `-g` | Sample-FF over `k` linearisations; default 10. |
| `COMPILE_FF`, `COMPILE_LMCUT` | Native `--fdr-pocl` on unconditional, axiom-free tasks; literal search with FD (`-g` is faster) | Full occurrence, ordering and causal-link compilation. Subtract committed cost before weighting. `COMPILE` aliases `COMPILE_FF`. |
| `COMPILE_HMAX`, `COMPILE_HADD`, `COMPILE_BLIND` | Literal search with FD (`-g` is faster) | Full compilation with another FD backend. |

Heuristics differ in cost and suitability; no single configuration dominates
across domains. Optimality requires an admissible ranking and a compatible search
configuration.

In native FDR search, `ADD_WORK`/`ADDR_WORK` estimate remaining causal-link
refinements: initially true or reusable facts cost one link, and other facts
inherit the effort of cost-minimizing support plus one. Equal-cost alternatives
use minimum effort. `MW`/`LW` use these work estimates for flaw selection;
`MC`/`LC` use additive action cost. A composition such as `FFR/ADD_WORK/LIFO`
uses work only to break equal FFR ranks. The
[flaw-type investigation](investigation/relax-vs-add/flaw-type-findings.md)
records the native effort correction and its evaluation.

`FF` adapts Hoffmann and Nebel's [relaxed-plan extraction](https://arxiv.org/pdf/1106.0675)
to the joint outstanding open conditions. It uses parallel first-appearance
levels, NOOPs first, minimum summed precondition levels, and all selected effects.
Effect marks are restricted to the current extraction layer, following the
author's released FF-v2.3 implementation, to preserve already-required support.
Ties use ascending fact/operator indices. `FFR` first removes each open condition
that a committed step could support under the current orderings, following the
existing-action reuse check discussed in [VHPOP §3.1.2](https://www.cs.cmu.edu/afs/cs/project/jair/pub/volume20/younes03a-html/node6.html).
The reuse test checks possible producer-before-consumer ordering; it does not
reject a producer whose fact is necessarily overwritten between those steps.
The [flaw-type diagnostics](investigation/relax-vs-add/flaw-type-findings.md)
measure this optimistic occurrence-level eligibility.
Both share potential future actions; `FFR` additionally considers existing steps.
This is an experimental POCL adaptation, without FF's helpful-action pruning or
enforced hill climbing. It retains outstanding preconditions of committed steps.
It differs from `CLFF`'s causal-link compilation and `RELAX`'s additive achievers.
The `FFR` reuse filter applies to current open conditions; it does not discount
existing support needed recursively by a potential future action. See the
[FF investigation](investigation/relax-vs-add/ff-findings.md) for results and scope.
The [memory and FD-gap follow-up](investigation/relax-vs-add/memory-and-domain-findings.md)
compares reuse, preferred refinements, alternative flaw selection, and measured
search structure on the difficult cluster cases.
The [targeted-refinement follow-up](investigation/relax-vs-add/targeted-refinement-findings.md)
tests bounded supporter counts and opt-in forced threat repairs against the
conditions identified by those diagnostics.

`TADD`, `FLOW` and `HYB` count *value tokens*. A variable's history is a chain
of segments, one per write; a step that requires `v = a` and overwrites it ends
one segment of value `a`, and no other step can end the same segment. `TADD`
charges each shortfall of productions at the value's cheapest reproduction cost
on top of `ADD`; `FLOW` solves the per-variable transportation problem from
surplus to deficit values over the domain transition graph. See the
[token heuristic investigation](investigation/pocl-heuristic/findings.md).

In native FDR search, `-f ORDER@HEURISTIC[*WEIGHT]` gives an interleaved
flaw-order queue its own ranking (and weight), so one search alternates between
heuristics; a queue whose heuristic cannot handle the task is dropped.
`--pea` turns native FDR A* into partial-expansion A* (Yoshizumi, Miura &
Ishida 2000): a plan queues only its children at its current f-value and is
re-queued at its next one, which keeps the queue far smaller.
The recommended token configuration is

```sh
potoroo --fdr-pocl -s A --pea -f 'ZLIFO@TADD/LIFO' -f 'ZLIFO@FLOW/LIFO' \
  -f '{n}LIFO/{o}0LIFO/{o}1NEW/{o}LC_add/{s}LIFO@HYB/LIFO' domain.pddl problem.pddl
```

`--preferred` adds an experimental preferred-refinement queue to native FDR
`A` or `GBFS` search. It favours new actions selected by the parent's FF relaxed
plan, links to existing steps, and ordering refinements. With `FFR` or `FFOCR` it uses the
same existing-support filter as the estimate; other rankings, including `ADD`,
use ordinary FF extraction for preferences. Five selections use the preferred
queue for every ordinary-queue selection, with fallback when either is empty.
Every refinement remains in the ordinary queue and shared entries expand once.
This changes expansion order even with `A`; it does not preserve A*'s ordering.
It requires unconditional, axiom-free unit-cost tasks, regardless of the ranking
heuristic. `preferred_generated` and `preferred_selected` appear in FDR STATS;
preference extraction contributes to wall time but not `h_eval_ms`.
See the [preferred-refinement investigation](investigation/relax-vs-add/preferred-findings.md).

`POTOROO_FDR_DIAGNOSTICS=1` emits a separate `FDR_DIAGNOSTIC` JSON record per
native FDR search stage. It counts selected open/threat refinements and their
emitted children before outer search pruning (internal refinement checks have
already run). Bounded samples measure repeated action occurrences,
ordered pairs of real steps, new threats in insertion children, and existing
unconditional restorers forced between a deleter and a link's consumer. This
last counter measures possible white-knight support; it does not change threat
semantics. Sampling starts at expansion 1, repeats every 1024 expansions, and
stops after 256 samples; structure checks omit plans with over 256 steps or
threats and report the omissions. Keep diagnostics off for timing comparisons.
Additional `FDR_DIAGNOSTIC_CONDITION` records attribute selected open conditions
and threatened links to `(variable, value)` facts, including emitted children,
new-step children and links from INIT. IDs refer to the current search task;
mapping them to captured SAS labels requires unchanged variable indices.
Also setting `POTOROO_FDR_FLAW_TYPES=1` emits selected-flaw type counts,
including local/unsafe opens, initially true facts, and support blocked by a
forced intervening unconditional deletion. Bitmask buckets partition selected
opens; named types overlap. These observations do not prune or rerank plans.

`FFOC` preserves separate support demands across open conditions while using FF
sharing inside each demand. `FFOCR` adds FFR's per-consumer existing-support
filter to this sum; it keeps the outstanding preconditions of committed steps.
Both are experimental adaptations. Native `COMPILE_FF` uses additive supporters; its
tie choices need not match FD. Native `COMPILE_LMCUT` uses the existing LM-cut
evaluator. Both rebuild the full compiled task at each evaluation. See the
[compiled FF investigation](investigation/relax-vs-add/compiled-ff-corrected-findings.md).

`REPOP` implements the ranking recurrence in Nguyen and Kambhampati (2001),
[§3](https://rakaposhi.eas.asu.edu/ucpop-revive.pdf), over native finite-domain
facts. It chooses a highest-level goal, regresses through an earliest-layer
achiever, removes all its effects, and charges zero for committed operators.
Equal levels use descending fact index; tied achievers prefer committed actions,
then translator order. Those tie choices are unspecified in the paper.
Use `-w 5` for the paper's heuristic weight. The flag alone does not enable
RePOP's consistency enforcement or change flaw selection. Existing `RELAX`
and `RELAXR` retain their previous semantics for comparisons.

### Flaw selection and pruning

`-f` chooses a flaw *within* a partial plan; `-h` chooses a plan from the queue.
Predefined flaw orders include `STATIC`, `UCPOP`, `UCPOP-LC`, `UCPOP-MC`,
`UCPOP-LC-MC`, `DSEP-LIFO`, `DSEP-LC`, `ZLIFO`, `LCFR`, `LCFR-LOC`, `LCFR-CONF`,
`MC`, `MW`, and the `LC_ADD`, `MC_ADD`, `LW_ADD`, `MW_ADD` variants.

Custom orders use `/`-separated tiers: `{flaws}[max]ORDER`. For example, ZLIFO is
`{n}LIFO/{o}0LIFO/{o}1NEW/{o}LIFO/{s}LIFO`. Here `n` and `s` are non-separable
and separable threats, `o` denotes open conditions, and the optional number caps
refinements. Orders include `LIFO`, `FIFO`, `LR`, `MR`, `NEW`, `REUSE`, and
cost/work variants.

Pruning is off by default. Select rules with `-p cutset,edelete`, use `all` or
`none`, and disable individual rules with `no-`, e.g. `all,no-recursion`.

| Rules | Where they apply |
|---|---|
| `cutset`, `edelete`, `recursion`, `minimality` | All representations. |
| `params`, `joint` | Literal representations. |
| `symbolic` | Lifted cutset checks. |
| `supporters`, `threats`, `h2`, `disjunctive` | Finite-domain search. |
| `symmetry` | Ground literal and finite-domain search. |

Rules have different costs and can change the returned plan.

`threats` compresses chains of forced classical ordering repairs after a threat
is selected. It leaves ambiguous promotion/demotion choices and conditional
confrontations open, and preserves compact storage for newly inserted action
candidates. Each batch performs at most 16 repairs, checks the deadline, and
counts the omitted queue entries against the generated-node budget. FDR STATS
reports `threat_forced` separately from `supporter_forced`. This changes search
order, but retains classical causal-link protection semantics.

`params` uses independent parameter domains. `joint` instead filters complete
relaxed-reachable argument tuples, propagates their supports through shared
variables, and binds singleton domains. For example, use `-f ZLIFO -p joint`.
Tuple tables are shared across the search. During expansion, sibling refinements
reuse unaffected domains and propagate changes through a constraint worklist.
Small value domains use bitsets, and a bounded shared cache reuses table filters
across expansions (at most 512 entries, with a 4 MiB payload allowance).
Independent groups in simple conjunctive preconditions are enumerated separately.
Large Cartesian tables are deferred until bindings connect groups; small tables
and other formulas retain complete-table construction. Further exact factor
discovery has a bounded work budget. The original full-product storage budget
still decides which schemas are included, and retained projections add at most
the original tables' tuple and posting storage.
Queued plans retain only forced bindings; non-singleton domains are reconstructed
when a plan is expanded, and the temporary cache is released after its children.
Tables exceeding the storage budget are omitted in full, weakening pruning
without excluding solutions. `joint` is experimental and off by default.

### Restart portfolios

Stages restart from the initial plan and release their search state when finished:

```bash
./target/release/potoroo --fdr-pocl \
  --stage 'CLFF@ALT=10' --stage ADD/LIFO \
  --time-limit 20 --stage-mem-mb 600 domain.pddl problem.pddl
```

This gives CLFF/ALT up to ten seconds, then ADD/LIFO the remaining time.
Only the final stage may omit its duration. Each stage inherits other command-line
options; stage heuristics are used exactly as written.

## PDDL support

Supports STRIPS, typing (including hierarchies and `either`), equality, negative
and disjunctive preconditions, existential and universal quantification,
conditional effects, and the `total-cost` action-cost fragment. Action costs may
be constants or functions of action parameters.

Durative actions, general numeric fluents, timed initial literals, preferences,
constraints, and explicit derived predicates are rejected. Translator-generated
axioms are handled by finite-domain search. State-dependent cost increases nested
inside `when` or `forall` are accepted but currently contribute zero.

## HTN

Potoroo includes a work-in-progress HTN layer for future plan-space HTN research.

## References

Potoroo draws on the following work. References for individual pruning rules
also appear beside their implementations.

- **VHPOP:** Håkan L. S. Younes and Reid G. Simmons. [*VHPOP: Versatile Heuristic Partial Order Planner*](https://www.cs.cmu.edu/afs/cs.cmu.edu/project/jair/pub/volume20/younes03a.pdf). JAIR, 2003.
- **Lplan:** Tom Bylander. [*A Linear Programming Heuristic for Optimal Planning*](https://cdn.aaai.org/AAAI/1997/AAAI97-108.pdf). AAAI, 1997.
- **RePOP:** XuanLong Nguyen and Subbarao Kambhampati. [*Reviving Partial Order Planning*](https://ijcai.org/proceedings/2001/0064.pdf). IJCAI, 2001.
- **Causal-link compilation:** Pascal Bercher, Thomas Geier, and Susanne Biundo. [*Using State-Based Planning Heuristics for Partial-Order Causal-Link Planning*](https://doi.org/10.1007/978-3-642-40942-4_1). KI, 2013.
- **Sample-FF:** Pascal Bercher, Thomas Geier, Felix Richter, and Susanne Biundo. [*On Delete Relaxation in Partial-Order Causal-Link Planning*](https://bercher.net/publications/2013/Bercher2013POCL-DeleteRelaxation.pdf). ICTAI, 2013.
- **Fast Downward:** Malte Helmert. [*The Fast Downward Planning System*](https://www.jair.org/index.php/jair/article/view/10457). JAIR, 2006.
- **Lifted mutex groups:** Daniel Fišer. [*Lifted Fact-Alternating Mutex Groups and Pruned Grounding of Classical Planning Problems*](https://ojs.aaai.org/index.php/AAAI/article/view/6536). AAAI, 2020.
- **Lifted landmarks:** Julia Wichlacz, Daniel Höller, and Jörg Hoffmann. [*Landmark Heuristics for Lifted Classical Planning*](https://www.ijcai.org/proceedings/2022/647). IJCAI, 2022.
- **Position paper and heuristic survey:** Scott Howsam, Harrison Oates, and Pascal Bercher. [*Reviving Partial Order Causal Link (POCL) Planning: Is It Possible? Is It Worth It?*](https://icaps26.icaps-conference.org/files/workshops/hsdip/ICAPS_HSDIP_2026_paper_8.pdf). HSDIP, 2026.

## License

Copyright 2026 Harrison Oates. Licensed under the [Apache License 2.0](LICENSE).
See [NOTICE](NOTICE) for the copyright and license notice.
