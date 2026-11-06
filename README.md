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
| `CLADD`, `CLFF` | `--fdr-pocl` | Causal-link compilation evaluated natively. |
| `LMCUT`, `LMCUTR` | `--fdr-pocl`; unconditional SAS+ effects | LM-cut, without/with reuse. |
| `LM` | Any | Unachieved landmarks: lifted or ground according to representation. |
| `LMO`, `LMF`, `LMFO` | Literal | Landmark ordering, FAM cuts, or both. |
| `LPLAN` | `-g` | Bylander's time-indexed LP relaxation. |
| `LPSAS`, `LPSAS:MIP`, `LPSAS:MIP50` | `-g`, FD | SAS+ LP, integral operators, or a per-probe MIP budget in milliseconds. |
| `SAMPLE_FF`, `SAMPLE_FF:k` | `-g` | Sample-FF over `k` linearisations; default 10. |
| `COMPILE_FF`, `COMPILE_LMCUT`, `COMPILE_HMAX`, `COMPILE_HADD`, `COMPILE_BLIND` | `-g`, FD | Evaluate a compiled classical task using FD. `COMPILE` aliases `COMPILE_FF`. |

Heuristics differ in cost and suitability; no single configuration dominates
across domains. Optimality requires an admissible ranking and a compatible search
configuration.

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
| `supporters`, `h2`, `disjunctive` | Finite-domain search. |
| `symmetry` | Ground literal and finite-domain search. |

Rules have different costs and can change the returned plan.

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

## HTN prototype

The optional `htn` feature adds a separate decomposition-based, plan-space
planner. The existing `potoroo` executable, flat plan types, and flat search
remain independent of this backend.

```bash
cargo build --release --features htn --bin potoroo-htn

# Use explicit executable paths, or put pandaPIparser and pandaPIgrounder on PATH.
export POTOROO_HTN_PARSER=/path/to/pandaPIparser
export POTOROO_HTN_GROUNDER=/path/to/pandaPIgrounder

./target/release/potoroo-htn --time-limit 30 \
  examples/htn/interleave-domain.hddl examples/htn/interleave-problem.hddl

# Existing PANDA parser or grounder output can also be used directly.
./target/release/potoroo-htn --lifted input.htn
./target/release/potoroo-htn --grounded output.sas
```

[pandaPIgrounder](https://github.com/panda-planner-dev/pandaPIgrounder) grounds the lifted PANDA
format produced by [pandaPIparser](https://github.com/panda-planner-dev/pandaPIparser).
`--parser` and `--grounder` override the environment variables. The pipeline uses
`--no-abstract-expansion --as-input-sas-deletes` so that method expansion remains
a search decision and delete effects remain explicit. Use the same flags when
preparing grounded input separately. Grounded PANDA `.sas` is a different format
from Fast Downward SAS+. No additional Cargo dependencies are needed.

The HTN backend supports ground STRIPS actions with nonnegative integer
costs, partially ordered methods, repeated task occurrences, recursive methods,
and empty methods. Negative preconditions and method preconditions use the
frontend's compiled facts and check actions. Native conditional effects and
nonempty additional mutex/invariant sections are rejected explicitly.

Every primitive occurrence must belong to the hierarchy; arbitrary action
insertion is disallowed. Queue policy and flaw selection are independent:

| Option | Behaviour |
| --- | --- |
| `--search bfs` (default) | Breadth-first over refinement depth; satisficing. |
| `--search astar` | TDG A*: committed primitive cost plus a lower bound on remaining cost. |
| `--search gbfs` | Greedy search on the TDG remaining-cost bound; satisficing. |
| `--flaws decomposition-first` (default) | Expand all compounds before resolving causal flaws. |
| `--flaws interleaved` | Resolve threats first, then the open condition with fewest possible refinements; expand remaining compounds when no causal flaws remain. |

```bash
./target/release/potoroo-htn --flaws interleaved --search astar --time-limit 30 \
  examples/htn/interleave-domain.hddl examples/htn/interleave-problem.hddl
```

Interleaved search considers both existing primitive supporters and methods
that could introduce a future supporter. It uses conservative descendant-effect
reachability to identify those methods, retains the open condition until a
primitive can support it, and checks for new threats after decomposition.
Compound tasks do not directly supply causal links.

The task-decomposition graph (TDG) gives primitive tasks their action costs,
methods the sum of their children's costs **with occurrence multiplicity**,
and compound tasks the minimum over their methods. Empty methods cost zero.
A nonnegative AND/OR traversal handles recursive exits and proves tasks with no
finite decomposition dead. The node bound sums only active compound occurrences;
active primitive occurrences are already charged to the committed cost. This
relaxation ignores preconditions, deletes, and ordering. Bounds saturate above
`u64::MAX` separately from unproductive tasks; overflow cannot become a false
unsolvability result. TDG preprocessing runs only for interleaved or guided
search, leaving the default baseline independent of the relaxation.

`cost_optimal=true` means A* returned a minimum-cost solution without dropping
branches at a depth bound. Equal priorities use FIFO ties, but A*/GBFS can still
starve solutions behind infinite recursive plateaus of lower priority.
Breadth-first remains fair for finite solutions; recursive unsolvable problems
can run indefinitely. `--limit N`, `--max-depth N`, and `--time-limit SECONDS`
report incomplete termination distinctly from exhausted search; limits exit
with status 2, input/internal errors with status 1. The time limit includes TDG
preprocessing. A depth cutoff disables the optimality claim for any later solution.

Successful output is a grounded PANDA decomposition certificate on stdout;
statistics and primitive cost go to stderr. Generated guard and noop occurrences
are retained for certificate conversion. Every solution is independently checked
for legal decomposition, occurrence multiplicity, inherited ordering,
executability, and final goals before emission. To check against the original
HDDL as well:

```bash
./target/release/potoroo-htn domain.hddl problem.hddl > plan.raw
"$POTOROO_HTN_PARSER" --panda-converter plan.raw plan.converted
"$POTOROO_HTN_PARSER" --verify=0 --no-colour domain.hddl problem.hddl plan.converted
```

Run `cargo test --features htn --test htn --test htn_guidance --test htn_pipeline`
for semantic and CLI checks. Independent exhaustive oracles cover 1,024 fixed
task networks and 512 hierarchical problems with alternative methods; the latter
checks all six queue/flaw combinations and A* cost optimality. Setting both
external tool environment variables also enables a PANDA parser/grounder integration
test of interleaved A* with original-HDDL certificate verification.

The modules separate immutable schemas (`model`), persistent partial plans
(`plan`), flaw selection/refinements (`refine`), static hierarchy analysis (`tdg`),
queue policies (`search`), and independent certificate checking (`validate`).
All are behind the `htn` feature; flat nodes and search dispatch remain separate.
This is still a strict HTN backend, not a full hybrid PANDA-3 replacement.

### HTN research coverage and next increments

Literature review updated **2026-11-06**. The algorithm and applicability review
below guides implementation; it is not a claim of exhaustive coverage or planner
parity. [PANDA's overview](https://panda-planner-dev.github.io/) distinguishes its
POCL backend from progression, SAT, and BDD planners. Our immediate comparison
target is PANDA's decomposition-based POCL search. Techniques evaluated with
progression or totally ordered networks need a separate justification here.

| Work reviewed | Consequence for this backend |
| --- | --- |
| [Hybrid Planning Heuristics Based on Task Decomposition Graphs (SoCS 2014)](https://ojs.aaai.org/index.php/SOCS/article/view/18323) | Basis for interleaving decomposition and causal refinement. Abstract interfaces and causal-link inheritance remain absent; possible descendant effects are only used to enumerate refinements. |
| [An Admissible HTN Planning Heuristic (IJCAI 2017)](https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.090/Publikationen/2017/Bercher17AdmissibleHTNHeuristic.pdf) | The static structural cost recurrence is implemented. Modification-effort guidance, delete-relaxed reachability pruning, and node-specific TDG recomputation remain to be added. Current search does not reproduce the full published heuristic suite. |
| [Classical heuristic guidance (IJCAI 2019)](https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.090/Publikationen/2019/Hoeller2019ProgressionHeuristics.pdf) and [delete- and ordering-relaxation (IJCAI 2020)](https://ijcai.org/proceedings/2020/564) | Investigate relaxed-composition and LP/ILP alternatives after the TDG baselines. A POCL adaptation must account for committed occurrences, causal commitments, and repeated mandatory tasks. |
| [Landmark Generation in HTN Planning (AAAI 2021)](https://ojs.aaai.org/index.php/AAAI/article/view/17405) and [Landmark Generation in HTN Planning Revisited (ICAPS 2025)](https://ojs.aaai.org/index.php/ICAPS/article/view/36123) | Bidirectional landmark extraction is a promising next heuristic. Design occurrence-aware progress tracking for partial plans; a raw landmark count is not automatically an admissible cost bound. |
| [Inevitable task refinements (SoCS 2023)](https://ojs.aaai.org/index.php/SOCS/article/download/27284/27057/31328) and [optimal total-order ILP guidance (ECAI 2024)](https://journals.sagepub.com/doi/pdf/10.3233/FAIA241005) | Reviewed summary-based pruning and heuristic construction. Their total-order assumptions need explicit guards; arbitrary POCL frontiers do not supply a single progression state. |
| [How Good is Perfect? On the Incompleteness of A* for Total-Order HTN Planning (ICAPS 2025)](https://yousefi.ai/static/papers/Yousefi2025Incompleteness.pdf) | Zero-cost recursion can defeat A*, including graph search. Keep fairness tests and distinguish conditional cost optimality from completeness. The paper's total-order transformation is not a ready-made partial-order preprocessing rule. |
| [Learning Heuristic Functions for HTN Planning (AAAI 2026)](https://nsp.cs.uni-saarland.de/papers/HoellerAAAI26.pdf) | Reviewed representation and evaluation: learned lifted guidance is interesting, but its total-order evaluation does not establish gains for this ground POCL backend. Keep learning optional after reproducible symbolic baselines. |

Additional screening, with no implementation claim: [PANDA loop detection
(2021)](https://ojs.aaai.org/index.php/ICAPS/article/view/15959),
[redundant PO decompositions (HPlan 2024)](https://icaps24.icaps-conference.org/program/workshops/hplan/HPlan2024_paper_9.pdf),
[LLM-generated heuristics (May 2026 preprint)](https://arxiv.org/abs/2605.07707),
[hierarchy-preserving deordering (September 2026 preprint)](https://arxiv.org/abs/2609.03912),
and [risk-aware HTN planning (2026)](https://link.springer.com/article/10.1007/s10489-026-07450-4).
These warrant further algorithm review before adoption. Stochastic objectives
and learned domain-specific guidance are separate extensions.

Planned order: modification-effort guidance; restricted reachability and cached
node-specific TDG updates; bidirectional landmarks and sound duplicate detection;
then RC/LP alternatives and explicit hybrid interfaces. Duplicate keys must
respect occurrence multiplicity, ordering, open conditions, and causal links,
while retaining a certificate witness. Abstract effects cannot simply be inferred
from the union of descendant effects and used as causal supporters.

Before promoting a configuration, compare pinned PANDA baselines on IPC partial-
and total-order problems, verify certificates against original HDDL, and report
coverage, primitive cost, grounding/preprocessing/search time, and peak memory.
Ablate each heuristic and pruning rule. Small exhaustive tests establish semantic
coverage, not competitive performance. Continue matched feature-on/off flat
benchmarks; HTN analysis and per-node data stay within the optional backend.

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
