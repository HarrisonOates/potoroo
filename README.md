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
./target/release/potoroo -s GBFS examples/gripper-domain.pddl examples/gripper-20.pddl

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
| `params` | Literal representations. |
| `symbolic` | Lifted cutset checks. |
| `supporters`, `h2`, `disjunctive` | Finite-domain search. |
| `symmetry` | Ground literal and finite-domain search. |

Rules have different costs and can change the returned plan.

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
