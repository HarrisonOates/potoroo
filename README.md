# Potoroo

A modern **partial-order causal-link (POCL) planner** written in Rust.

Potoroo is based on [VHPOP](http://www.tempastic.org/vhpop/) (Younes & Simmons 2003).
The aim is to provide a correct, fast, and well-documented POCL planner that implements all known POCL heuristics — including those whose original source code has been lost to time — and serves as a jumping-off point for future POCL planning research.

The name comes from the [potoroo](https://en.wikipedia.org/wiki/Potoroo), a small Australian marsupial.

---

## Features

- **Full POCL search** with lifted, ground, and finite-domain representations
- **All historical heuristics** discussed in the position paper by Howsam, Oates and Bercher (HSDIP 2026)
- **Flaw-selection DSL** covering every order from the VHPOP and UCPOP literature
- **Composable heuristics** — combine any two with `/`
- **PDDL action costs** end-to-end, including cost functions of an action's parameters
- **Reachability-based grounding** via Fast Downward's translator, with a naive fallback
- Pure Rust, no C/C++ build-time dependencies (Fast Downward is optional at runtime)

---

## Building

**Prerequisites:** [Rust](https://rustup.rs) (stable, 1.75+). No other build-time dependencies.

```bash
git clone https://github.com/harrisonoates/potoroo
cd potoroo
cargo build --release
```

The binary is at `target/release/potoroo`.

**Run tests:**

```bash
cargo test
```

Most tests run without Fast Downward. Tests that require it are skipped automatically if it is not available.

### Optional features

| Feature | Effect |
|---------|--------|
| `highs-lp` | Solve the `LPLAN` LP with [HiGHS](https://highs.dev) instead of the pure-Rust `microlp`. Roughly 5× faster per evaluation, and turns some timeouts into solutions. HiGHS is a C++ library built from source, so this needs `cmake` and a C++ compiler; off by default so the core stays buildable with no system dependencies. |

```bash
cargo build --release --features highs-lp
```

---

## Fast Downward (optional)

Fast Downward is required for the `COMPILE*` heuristics, for `--fdr-pocl`, and for
reachability-based grounding. Everything else works without it.

```bash
git clone https://github.com/aibasel/downward.git
cd downward
python build.py
```

**Tell Potoroo where to find it** (choose one):

```bash
# Option 1: put fast-downward.py on PATH
export PATH="/path/to/downward:$PATH"

# Option 2: set the environment variable
export POTOROO_FD=/path/to/downward/fast-downward.py

# Option 3 (ground-mode COMPILE* only): point directly at the C++ binary,
# which skips the Python translator and is ~10× faster per node
export POTOROO_DOWNWARD=/path/to/downward/builds/release/bin/downward
```

For a checkout at `./downward`, a project-local `.cargo/config.toml` can make both
paths automatic for every `cargo run` and `cargo test`:

```toml
[env]
POTOROO_FD = { value = "downward/fast-downward.py", relative = true }
POTOROO_DOWNWARD = { value = "downward/builds/release/bin/downward", relative = true }
```

The local config is gitignored, so machine-specific paths do not leak into commits.
Explicit shell environment variables override these defaults.

---

## Usage

```
potoroo [options] domain.pddl problem.pddl
```

Files may be given in either order — each is classified by its contents. A single
file may hold both, and input can be piped on stdin instead.

```bash
# Default configuration: lifted POCL, A*, the ADD heuristic
potoroo examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl

# Ground actions with the admissible Lplan LP heuristic
potoroo -g -h LPLAN examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl

# Greedy best-first search, which is usually the fastest satisficing setting
potoroo -s GBFS examples/gripper-domain.pddl examples/gripper-20.pddl

# Compose two heuristics: rank by UCPOP, break ties by ADD
potoroo -h "UCPOP/ADD" examples/gripper-domain.pddl examples/gripper-4.pddl

# Finite-domain ground POCL over Fast Downward's SAS+ variables
potoroo --fdr-pocl examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl
```

---

## Options reference

| Flag | Long form | Argument | Description | Default |
|------|-----------|----------|-------------|---------|
| `-a` | `--action-cost` | `TASK`\|`UNIT`\|`DURATION`\|`RELATIVE` | Action cost model. `TASK` uses the PDDL `total-cost`; `UNIT` makes every action cost 1. `DURATION` and `RELATIVE` are accepted and fall back to `TASK`. | `TASK` |
| `-f` | `--flaw-order` | ORDER | Flaw-selection order; see [Flaw-selection orders](#flaw-selection-orders). Repeatable, one per search tier. | `STATIC` |
| `-g` | `--ground-actions` | — | Plan with fully ground actions. Required by `LPLAN`, `SAMPLE_FF` and `COMPILE*`. | lifted |
| `-h` | `--heuristic` | HEUR | Plan-ranking heuristic; see [Heuristics](#heuristics). | `ADD` |
| `-l` | `--limit` | N \| `unlimited` | Cap on generated search nodes. Repeatable, one per `-f` tier. | `unlimited` |
| `-s` | `--search-algorithm` | `A`\|`IDA`\|`HC`\|`BFS`\|`GBFS`\|`LGBFS`\|`LGBFS-D`\|`ALT` | Search algorithm; see the table below. | `A` |
| `-v` | `--verbose` | `[N]` | Live telemetry on stderr. Repeat for faster updates: `-vv` is 250 ms, `-vvv` prints every expansion. | off |
| `-w` | `--weight` | W | Multiplier on the heuristic term of the rank. | `1.0` |
| — | `--fdr-pocl` | — | Search over Fast Downward's multi-valued SAS+ variables; see [Representations](#representations). | off |
| `-H` | `--help` | — | Print usage and exit. | |
| `-V` | `--version` | — | Print version and exit. | |

Accepted for VHPOP compatibility but inert: `-d`, `-S`, `-T`, `-t`, `-W`.
`-r` (random open conditions) is rejected.

### Search algorithms (`-s`)

| Name | Description |
|------|-------------|
| `A` | Best-first A\* on `g + w × h`. Returns optimal-length plans with an admissible heuristic. **Default.** |
| `IDA` | Iterative-deepening A\*, re-searching under a rising `f`-limit. |
| `HC` | Hill climbing. |
| `BFS` | Breadth-first search. |
| `GBFS` | Greedy best-first: ranks on `h` alone. Usually much faster than `A` when any plan will do. |
| `LGBFS` | Lazy GBFS — children are queued on the parent's estimate and re-ranked when popped. |
| `LGBFS-D` | Lazy GBFS with a dual queue. |
| `ALT` | LAMA-style 1:1 alternation between an A\*-ordered and a GBFS-ordered queue. |

---

## Heuristics

Set with `-h NAME`. Two heuristics compose with `/` for lexicographic
tie-breaking: `-h "UCPOP/ADD"` ranks by `UCPOP` and breaks ties with `ADD`.

The **Needs** column gives the representation a heuristic requires: `—` means any,
`-g` means ground actions, `--fdr-pocl` means the finite-domain representation, and
`FD` means Fast Downward must be installed.

### Structural

No planning graph; `O(|plan|)` per node.

| Name | Needs | Description |
|------|-------|-------------|
| `UCPOP` | — | `committed-cost + w × (open conditions + unsafe links)`, from the original UCPOP planner |
| `OC` | — | Open-condition count |
| `UC` | — | Unsafe-link (threat) count |
| `BUC` | — | Binary unsafe count: 0 with no threats, 1 otherwise |
| `LIFO` | — | Newest plan first |
| `FIFO` | — | Oldest plan first |

### Planning graph

Built incrementally, Graphplan-style. Ground mode is not required but resolves more
bindings and so gives sharper estimates.

| Name | Needs | Description |
|------|-------|-------------|
| `ADD` | — | Additive heuristic: `committed-cost + w × h_add` over all open conditions. **Default.** |
| `ADD_COST` | — | The `ADD` cost term alone, without the step count |
| `ADD_WORK` | — | Operator count in the `ADD` relaxed plan |
| `ADDR` | — | `ADD` with action reuse (VHPOP's `h^r_add`): only new operators count |
| `ADDR_COST` | — | The `ADDR` cost term alone |
| `ADDR_WORK` | — | Operator count in the `ADDR` relaxed plan |
| `RELAX` | — | Delete-relaxed plan cost, FF-style joint extraction |
| `RELAXR` | — | `RELAX` counting only operators not already in the plan |

### Admissible

| Name | Needs | Description |
|------|-------|-------------|
| `LPLAN` | `-g` | Bylander's (1997) LP relaxation over the causal-link compilation: the smallest horizon whose time-indexed LP is feasible. A lower bound on total completion length. Build with `--features highs-lp` for a much faster solver. |
| `LMCUT` | `--fdr-pocl` | Joint LM-cut estimate for all open conditions, from the problem's initial state. Requires unconditional SAS+ effects. |
| `LMCUTR` | `--fdr-pocl` | Reuse-aware LM-cut: effects of committed steps are free |

### Delegating

These evaluate a transformed task, so each node costs far more than a planning-graph
evaluation.

| Name | Needs | Description |
|------|-------|-------------|
| `SAMPLE_FF` | `-g` | Sample-FF (Bercher et al. 2013): committed steps stay unrelaxed, open conditions are filled by delete relaxation over `k` sampled linearisations. `k` defaults to 10. |
| `SAMPLE_FF:k` | `-g` | As above with an explicit sample count, e.g. `SAMPLE_FF:5` |
| `COMPILE_FF` | `-g`, FD | Compile the partial plan to a classical task (Bercher, Geier & Biundo 2013) and evaluate it with FD's `ff()`. The most useful of these in practice. |
| `COMPILE_LMCUT` | `-g`, FD | As above with `lmcut()` — a tight admissible bound, slower |
| `COMPILE_HMAX` | `-g`, FD | As above with `hmax()` |
| `COMPILE_HADD` | `-g`, FD | As above with `add()` |
| `COMPILE_BLIND` | `-g`, FD | As above with `blind()`, for baselines |
| `COMPILE` | `-g`, FD | Alias for `COMPILE_FF` |

`LMCUT`/`LMCUTR` are open-condition relaxations computed directly over finite-domain
facts, and are distinct from `COMPILE_LMCUT`, which runs LM-cut on the compiled task.

---

## Flaw-selection orders

Set with `-f`. The order decides which flaw the planner resolves at each step, and
is a major factor in POCL search efficiency — it was studied extensively in the
UCPOP and VHPOP literature.

### Predefined

| Name | Expansion | Description |
|------|-----------|-------------|
| `STATIC` | — | Static open conditions first, then LIFO for threats and the rest. **Default.** |
| `UCPOP` | `{n,s}LIFO/{o}LIFO` | Threats LIFO (non-separable then separable), then open conditions LIFO |
| `UCPOP-LC` | `{n,s}LIFO/{o}LR` | Threats LIFO, open conditions by fewest refinements |
| `UCPOP-MC` | `{n,s}LIFO/{o}MR` | Threats LIFO, open conditions by most refinements |
| `UCPOP-LC-MC` | `{n,s}LIFO/{o}LR/{o}MR` | Both, in that order |
| `DSEP-LIFO` | `{n}LIFO/{o}LIFO/{s}LIFO` | Non-separable threats, then open conditions, then separable threats |
| `DSEP-LC` | `{n}LIFO/{o}LR/{s}LIFO` | As above with least-refinements open conditions |
| `ZLIFO` | `{n}LIFO/{o}0LIFO/{o}1NEW/{o}LIFO/{s}LIFO` | Zero-commitment LIFO (Haslum & Geffner 2000): dead ends first, then single-refinement conditions |
| `LCFR` | — | Least-cost-first with reuse |
| `LCFR-LOC` | — | `LCFR` preferring open conditions |
| `LCFR-CONF` | — | `LCFR` preferring threatened conditions |
| `MC` | — | Most-cost first |
| `MW` | — | Most-work first |
| `LC_ADD`, `MC_ADD`, `LW_ADD`, `MW_ADD` | — | Cost and work variants ranked by the `ADD` heuristic |

### DSL

Custom orders are written as `/`-separated tiers, evaluated lexicographically:

```
{flaws}[max]ORDER / {flaws}[max]ORDER / ...
```

| Part | Meaning |
|------|---------|
| `{n}` | Non-separable threats |
| `{s}` | Separable threats |
| `{o}` | Open conditions |
| `[max]` | Optional cap on refinements considered, e.g. `{o}0LIFO` selects only flaws with no refinement |
| `ORDER` | `LIFO`, `FIFO`, `R` (random), `LR` (fewest refinements), `MR` (most), `NEW`, `REUSE`, `LC_add`, `MC_add`, `LW_add`, `MW_add` |

---

## Representations

The same search configuration — algorithms, weights, limits, flaw orders — applies
to all three.

| Flag | Representation |
|------|----------------|
| *(none)* | **Lifted.** Actions stay partially instantiated and variables are resolved by binding constraints. |
| `-g` | **Ground.** Actions are fully instantiated up front, by Fast Downward's translator where available and by naive instantiation otherwise. Required by `LPLAN`, `SAMPLE_FF` and `COMPILE*`. |
| `--fdr-pocl` | **Finite-domain.** Fast Downward's multi-valued SAS+ variables are kept throughout. Causal links protect equalities such as `location(truck) = paris`, so any effect assigning another value is a threat without needing an explicit delete. |

Structural heuristics, `ADD`/`ADDR`, `RELAX`/`RELAXR` and the native `LMCUT`/`LMCUTR`
work on finite-domain nodes; `SAMPLE_FF`, `LPLAN` and `COMPILE*` do not.

---

## Supported PDDL

Potoroo targets the **IPC 2027 fragment** of PDDL 3.1: STRIPS, action costs,
negative preconditions, and conditional effects (including in combination with
`forall`), plus the two features the competition lists as under consideration —
disjunctive preconditions and existential quantifiers.

| Feature | Support |
|---|---|
| STRIPS | Full. |
| `:typing` (`:types`, `:constants`, hierarchies, `either`) | Full, including multi-level hierarchies and union types. |
| `:negative-preconditions` | Full and native — no `not-p` compilation. Negative open conditions may be closed against the initial state. |
| `:disjunctive-preconditions` (`or`, `imply`) | Full and native: a disjunction is a first-class flaw, refined into one child plan per disjunct rather than split into separate actions. |
| `:existential-preconditions` (`exists`) | Full, in preconditions and goals. The binder is eliminated and its variables are resolved by the binding constraints. |
| `:universal-preconditions` (`forall`) | Full, by expansion over the type-compatible objects. |
| `:conditional-effects` (`when`, `forall`) | Full, including `(forall … (when …))` and nested `forall`. Threats from conditional effects are resolved by confrontation as well as by promotion and demotion. |
| `:action-costs` | Full for the `total-cost` fragment: constants, nullary cost functions, and functions of an action's parameters such as `(increase (total-cost) (road-length ?a ?b))`. An increase guarded by `when`/`forall` is accepted but contributes zero — see below. |
| `:equality` | Full, through the binding constraints rather than as a fact. |

Deliberately rejected, with a diagnostic naming the construct: durative actions,
general numeric fluents, timed initial literals, preferences, constraints, and
derived predicates. `:fluents`/`:numeric-fluents` may be *declared* alongside
`:action-costs` — many IPC domains do — and is rejected only if numeric content
outside the `total-cost` fragment is actually used. Declaring `(total-cost)` in
`:functions` is enough to enable action costs, whether or not `:action-costs`
appears in `:requirements`.

Against the 147 domain families in
[`downward-benchmarks`](https://github.com/aibasel/downward-benchmarks), 143
parse and lower; the 4 that do not are the derived-predicate domains. Reproduce
with `scripts/fragment_survey.sh <benchmark-dir>`.

### Action costs and the lifted representation

A cost that depends on an action's arguments has no single value at the schema
level, and a lifted POCL step joins the plan before its arguments are bound. Such
a step is therefore priced at the **minimum over the instances its parameter
types admit** — a lower bound, so `g` never over-estimates and A* stays
admissible — and the exact cost is recovered once the plan is complete and its
steps are instantiated. Ground (`-g`) and finite-domain (`--fdr-pocl`) search
price every instance exactly from the outset. All three representations agree on
the cost of a finished plan.

An `(increase (total-cost) …)` nested inside a `when` or `forall` is accepted and
recorded, but contributes zero: whether its guard holds is a property of the
state the step is applied in, which a partial order does not fix. No IPC
benchmark family uses that form.

---

## Output

On success the plan goes to stdout:

```
;problem-name
1:(puton c table a)
2:(puton b c table)
Time: 42
```

On failure, `no plan` followed by the reason. Exit status is non-zero only for bad
input, not for an unsolved problem.

`-v` adds the chosen configuration, live progress, and a closing summary on stderr:

```text
Search [   1.00s] visited 1824 | generated 5931 | queued 4107 | h 5930 evals / 712 ms | pruned 38 | current steps=7 open=4 threats=1 order=1
```

Set `POTOROO_STATS_JSON=1` for one machine-readable line per problem on stderr:

```json
STATS {"problem":"...","heuristic":"...","ground":false,"solved":true,"plan_len":6,"plan_cost":11,"nodes_generated":142,"nodes_visited":38,"wall_ms":12}
```

---

## Design notes

**Threat resolution.** Threats are resolved by promotion, demotion and separation.
Separation also covers *confrontation*, UCPOP's resolver for conditional effects: an
effect only clobbers a link when its guard holds, so the threatening step can be
committed against the guard instead of being ordered out of the protected interval.
Over finite domains the negated guard is exact — `mode != unsafe` is the disjunction
over the remaining values of `mode` — so each alternative is a refinement of its own
rather than a disjunctive open condition, and a threat disappears once the step is
already committed against one of the guard's conditions. A ground threat has no
unifier to separate, so `{s}` selects the confrontable threats and `{n}` the rest.

**Action costs.** Declared costs are used by default; `-a UNIT` overrides them. A cost
that depends on an action's arguments has no single value at the schema level, so a
lifted step whose arguments are still unbound is priced at the minimum over the
instances its parameter types admit. That is a lower bound, so `g` never
over-estimates and A\* stays admissible, and the exact cost is recovered once the plan
is complete and its steps are instantiated. Ground and finite-domain search price
every instance exactly from the outset.

**Axioms.** Axiom variables that Fast Downward introduces when normalising quantified
and disjunctive formulas are expanded into base-fact support clauses where they are
consumed.

---
## Acknowledgements

Potoroo builds on the following work:

- **VHPOP** — Håkan L. S. Younes and Reid G. Simmons, *VHPOP: Versatile Heuristic Partial Order Planner*, JAIR 2003. The original planner this reimplements.
- **Lplan** — Tom Bylander, *A Linear Programming Heuristic for Optimal Planning*, AAAI 1997.
- **Causal-link compilation** — Pascal Bercher, Tobias Geier, and Susanne Biundo, *Using State-Based Planning Heuristics for Partial-Order Causal-Link Planning*, KI 2013.
- **Sample-FF** — Pascal Bercher, Tobias Geier, Florian Richter, and Susanne Biundo, *On Delete Relaxation in Partial-Order Causal-Link Planning*, ICTAI 2013.
- **Fast Downward** — Malte Helmert, *The Fast Downward Planning System*, JAIR 2006.
- **Position paper & heuristic survey** — Scott Howsam, Harrison Oates, and Pascal Bercher, *Reviving Partial Order Causal Link (POCL) Planning: Is It Possible? Is It Worth It?*, HSDIP 2026. ([PDF](https://icaps26.icaps-conference.org/files/workshops/hsdip/ICAPS_HSDIP_2026_paper_8.pdf))

---

## License

This project is licensed under the [Apache License 2.0](LICENSE.MD).
