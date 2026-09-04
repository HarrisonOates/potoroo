# Potoroo

A modern **partial-order causal-link (POCL) planner** written in Rust.

Potoroo is based on [VHPOP](http://www.tempastic.org/vhpop/) (Younes & Simmons 2003).
The aim is to provide a correct, fast, and well-documented POCL planner that implements all known POCL heuristics — including those whose original source code has been lost to time — and serves as a jumping-off point for future POCL planning research.

The name comes from the [potoroo](https://en.wikipedia.org/wiki/Potoroo), a small Australian marsupial.

---

## Features

- **Full POCL search** with lifted and grounded action modes
- **Reachability-based grounder** via Fast Downward's translator when in ground mode (`-g`), with fallback to naive instantiation
- **PDDL action costs** end-to-end in lifted and finite-domain search
- **All historical heuristics** discussed in the position paper by Howsam, Oates and Bercher (HSDIP 2026)
- **Flaw-selection DSL** with all orders from the VHPOP and UCPOP literature
- **Composable heuristics** — combine any two with `/`
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

Most tests run without Fast Downward. Tests that require FD are skipped automatically if it is not available.

---

## Fast Downward (optional)

Fast Downward is required for the `COMPILE*` family of heuristics and for efficient grounding. All other heuristics work without it.

**Install Fast Downward:**

```bash
# Clone and build
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

# Option 3 (ground-mode COMPILE* only): point directly at the C++ binary
# for maximum speed (skips the Python translator, ~10× faster per node)
export POTOROO_DOWNWARD=/path/to/downward/builds/release/bin/downward
```

For a checkout at `./downward`, a project-local `.cargo/config.toml` can make
both paths automatic for every `cargo run` and `cargo test`:

```toml
[env]
POTOROO_FD = { value = "downward/fast-downward.py", relative = true }
POTOROO_DOWNWARD = { value = "downward/builds/release/bin/downward", relative = true }
```

The local config is gitignored, so machine-specific planner paths do not leak
into commits. Explicit shell environment variables override these defaults.

---

## Usage

```
potoroo [options] domain.pddl problem.pddl
```

Input files can also be piped via stdin (domain first, then problem).

### Quick examples

```bash
# Solve the Sussman anomaly with the default ADDR heuristic
potoroo examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl

# Use the additive heuristic
potoroo -h ADD examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl

# Use the Lplan LP heuristic (admissible) with ground actions
potoroo -h LPLAN -g examples/blocks-world-domain.pddl examples/bw-large-a.pddl

# Compile to classical planning and evaluate with LM-cut (requires Fast Downward)
potoroo -h COMPILE_LMCUT -g examples/gripper-domain.pddl examples/gripper-4.pddl

# Compose two heuristics (lexicographic tiebreaking)
potoroo -h "UCPOP/ADD" examples/logistics-domain.pddl examples/logistics-a.pddl

# Ground POCL search directly over Fast Downward's SAS+ variables
potoroo --fdr-pocl -v examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl
```

### Default search profile

Potoroo defaults to lifted POCL, A* search, task action costs, weight 1, and the
`STATIC` flaw order. Literal POCL uses the reuse-aware `ADDR` heuristic. With
`--fdr-pocl`, Potoroo selects plain `ADD` instead: empirical sweeps found its
finite-domain search substantially more robust than `ADDR`. Any explicit
`-h`, `-f`, `-s`, `-a`, or `-w` option overrides the corresponding default.

### Finite-domain ground POCL

`--fdr-pocl` translates the original problem with Fast Downward and retains its
multi-valued SAS+ variables throughout ground POCL refinement.
Causal links protect equalities such as `location(truck) = paris`; every effect
assigning another value to `location(truck)` is treated as a threat, without
requiring an explicit delete proposition. With `-v`, Potoroo reports how many
translated variables are genuinely multi-valued.

Threats from conditional assignments are resolved by *confrontation* as well as
by promotion and demotion. Confrontation is UCPOP's threat resolver for
conditional effects, which VHPOP folds into its separation refinement: the
effect only clobbers the link when all of its conditions hold, so the
threatening step is committed to another value of a condition variable instead
of being ordered out of the protected interval. Finite domains make the negated
antecedent exact — `mode != unsafe` is the disjunction over the remaining values
of `mode`, so each alternative is a refinement of its own rather than a
disjunctive open condition — and by the same reading a threat is dropped
outright once the step is already committed against one of the effect's
conditions. A ground threat has no unifier to separate, so `{s}` selects the
confrontable threats and `{n}` the rest.

The finite-domain path consumes the normal search configuration: A*/IDA*/HC,
BFS, GBFS, lazy/dual-queue GBFS, ALT, search weights and limits, and the
flaw-order DSL. Cheap structural heuristics, `ADD`/`ADDR`, joint FF-style
`RELAX`/`RELAXR` extraction, and native `LMCUT`/`LMCUTR` (including composed
ranks) are implemented directly over finite-domain facts. Declared PDDL/SAS+
operator costs are used by default, with `-a UNIT` available as an override.
Fast Downward-generated axiom variables (used when normalizing quantified and
disjunctive formulas) are expanded into base-fact support clauses at the
consumer. The representation-specific `SAMPLE_FF`, `LPLAN`, and `COMPILE*`
heuristics remain unavailable on FDR nodes. Native LM-cut currently requires
unconditional SAS+ effects.

| Native FDR heuristic | Description |
|------|-------------|
| `LMCUT` | Joint LM-cut estimate for all open conditions, starting from the problem initial state |
| `LMCUTR` | Reuse-aware LM-cut: committed-step effects are free; an admissible lower bound on additional task cost |

These are direct POCL open-condition relaxations and are distinct from
`COMPILE_LMCUT`, which evaluates LM-cut on the causal-link compilation.

For resource-shuttling problems, `-s ALT -h ADD` is generally more robust than
pure GBFS: ALT interleaves greedy `h_add` guidance with total estimated plan
cost, avoiding low-heuristic plateaus caused by repeated vehicle transitions.

### Output

On success, Potoroo prints the plan to stdout:

```
;problem-name
(action1 arg1 arg2)
(action2 arg1)
...
Time: 42
```

On failure: `no plan` followed by the reason.

Pass `-v` to see the selected search configuration, live progress on stderr,
and a final human-readable summary. Progress includes generated, visited, and
queued nodes; heuristic evaluations and time; pruned nodes; and the current
partial plan's steps, open conditions, and threats. The first expansion is
always printed, followed by updates at most once per second. Use `-vv` for
250 ms updates or `-vvv` to print every expansion.

```text
Search [   1.00s] visited 1824 | generated 5931 | queued 4107 | h 5930 evals / 712 ms | pruned 38 | current steps=7 open=4 threats=1 order=1
```

Set `POTOROO_STATS_JSON=1` to emit a machine-readable JSON line on stderr:

```json
STATS {"problem":"...","heuristic":"...","ground":false,"solved":true,"plan_len":6,"plan_cost":11,"nodes_generated":142,"nodes_visited":38,"wall_ms":12}
```

---

## Options reference

| Flag | Long form | Argument | Description | Default |
|------|-----------|----------|-------------|---------|
| `-a` | `--action-cost` | `TASK`\|`UNIT`\|`DURATION`\|`RELATIVE` | Action cost model (`TASK` respects PDDL `total-cost`) | `TASK` |
| `-f` | `--flaw-order` | ORDER | Flaw-selection order (see [Flaw orders](#flaw-selection-orders)) | `STATIC` |
| — | `--fdr-pocl` | — | Ground POCL search over translated multi-valued SAS+ variables | off |
| `-g` | `--ground-actions` | — | Plan with fully ground actions (required for `LPLAN`, `SAMPLE_FF`, `COMPILE*`) | lifted |
| `-h` | `--heuristic` | HEUR | Plan-ranking heuristic (see [Heuristics](#heuristics)) | `ADDR` (`ADD` with `--fdr-pocl`) |
| `-l` | `--limit` | N or `unlimited` | Search-node expansion limit | unlimited |
| `-s` | `--search-algorithm` | `A`\|`IDA`\|`HC`\|`BFS`\|`GBFS`\|`LGBFS`\|`LGBFS-D`\|`ALT` | Search algorithm (`A` = best-first A\*; `ALT` = LAMA-style 1:1 alternation between A\*- and GBFS-ordered queues) | `A` |
| `-v` | `--verbose` | [N] | Live telemetry; repeat for faster updates (`-vv`, `-vvv`) | 0 |
| `-w` | `--weight` | W | Heuristic weight multiplier on the h-term | 1.0 |
| `-H` | `--help` | — | Display help and exit | |
| `-V` | `--version` | — | Display version and exit | |

---

## Heuristics

Heuristics are specified with `-h NAME`. Two heuristics can be composed with `/` for lexicographic tiebreaking: `-h "UCPOP/ADD"` ranks by UCPOP first, breaking ties by ADD.

### Cheap heuristics

These run in O(|plan|) time with no planning graph.

| Name | Description |
|------|-------------|
| `UCPOP` | `committed-cost + weight × (open-conditions + unsafe-links)` — the heuristic from the original UCPOP planner |
| `OC` | Open-condition count |
| `UC` | Unsafe-link (threat) count |
| `BUC` | Binary unsafe count (0 if no threats, 1 otherwise) |
| `LIFO` | Last-in-first-out ordering (newest plan first) |
| `FIFO` | First-in-first-out ordering (oldest plan first) |

### Planning-graph heuristics

These build an incremental Graphplan-style planning graph. Ground mode (`-g`) is not required but may give better estimates by resolving more bindings.

| Name | Description |
|------|-------------|
| `ADD` | Additive heuristic: sum of cost-aware ADD values for all open conditions. `committed-cost + weight × h_add`. **FDR default.** |
| `ADD_COST` | ADD cost term only (no step count) |
| `ADD_WORK` | ADD work: total operator count in the ADD relaxed plan |
| `ADDR` | Additive heuristic with action reuse: only new operators count toward the estimate. **Literal-POCL default.** |
| `ADDR_COST` | ADDR cost only |
| `ADDR_WORK` | ADDR work |
| `RELAX` | Delete-relaxed plan cost (FF-style joint extraction): `committed-cost + weight × cost(π_relax)` |
| `RELAXR` | RELAX with reuse (only new operators in the extracted relaxed plan) |

### Lplan LP heuristic

Requires ground actions (`-g`). An **admissible** lower bound on the total number of steps needed to complete the plan, based on Bylander's (1997) LP relaxation applied to the causal-link compilation of the current partial plan.

| Name | Description |
|------|-------------|
| `LPLAN` | Smallest feasible horizon h such that a time-indexed LP relaxation of the ground causal-link compilation admits a solution. Admissible. |

### Sample-FF heuristic

Requires ground actions (`-g`).

| Name | Description |
|------|-------------|
| `SAMPLE_FF` | Sample-FF (Bercher et al. 2013): keeps committed steps non-relaxed and fills open conditions with delete relaxation over k sampled linearizations. Default k=10. |
| `SAMPLE_FF:k` | As above with explicit sample count k (e.g. `SAMPLE_FF:5`). |

### Causal-link compilation heuristics

Require ground actions (`-g`) and Fast Downward. The partial plan is compiled to a classical STRIPS task (Bercher, Geier & Biundo 2013), and the initial-state heuristic value of that task estimates the remaining completion cost.

| Name | FD evaluator | Description |
|------|-------------|-------------|
| `COMPILE_FF` | `ff()` | FF heuristic (delete relaxation, most useful in practice) |
| `COMPILE_LMCUT` | `lmcut()` | Landmark-cut (tight admissible bound, slower) |
| `COMPILE_HMAX` | `hmax()` | h^max (admissible, less informed than LM-cut) |
| `COMPILE_HADD` | `add()` | Additive heuristic via FD |
| `COMPILE_BLIND` | `blind()` | Goal-count (for baseline comparison) |
| `COMPILE` | `ff()` | Alias for `COMPILE_FF` |

**Performance note:** The ground-mode path (`-g`) bypasses the Python translator and communicates with the `downward` C++ binary directly, reducing per-node overhead by ~10×. Set `POTOROO_DOWNWARD` to the binary path for this fast path.

---

## Flaw-selection orders

The flaw-selection order (`-f`) controls which open flaw the planner chooses to resolve at each step. This is a major factor in search efficiency for POCL planning and was extensively studied in the UCPOP/VHPOP literature.

### Predefined orders

| Name | Description |
|------|-------------|
| `STATIC` | Resolve static open conditions first, then use LIFO for threats and remaining open conditions. **Default.** |
| `UCPOP` | `{n,s}LIFO/{o}LIFO` — threats (non-separable then separable) LIFO, then open conditions LIFO |
| `UCPOP-LC` | `{n,s}LIFO/{o}LR` — threats LIFO, open conditions by least-refinements |
| `UCPOP-MC` | `{n,s}LIFO/{o}MR` — threats LIFO, open conditions by most-refinements |
| `UCPOP-LC-MC` | `{n,s}LIFO/{o}LR/{o}MR` |
| `DSEP-LIFO` | `{n}LIFO/{o}LIFO/{s}LIFO` — non-separable threats, then open conditions, then separable threats |
| `DSEP-LC` | `{n}LIFO/{o}LR/{s}LIFO` |
| `ZLIFO` | Complex ZLIFO order (Haslum & Geffner 2000) |
| `LCFR` | Least-cost-first with reuse |
| `LCFR-LOC` | LCFR, prefer open conditions |
| `LCFR-CONF` | LCFR, prefer threatened conditions |
| `MC` | Most-cost first |
| `MW` | Most-work first |
| `LC_ADD`, `MC_ADD`, `LW_ADD`, `MW_ADD` | Cost/work variants using the ADD heuristic |

### DSL syntax

Custom orders can be written in the flaw-selection DSL:

```
{flaws}[max]ORDER / {flaws}[max]ORDER / ...
```

- `{n}` — non-separable threats, `{s}` — separable threats, `{o}` — open conditions
- `[max]` — optional integer cap on refinements considered (e.g. `{n}0LIFO`)
- Ordering keywords: `LIFO`, `FIFO`, `R` (random), `LR` (least refinements), `MR` (most refinements), `NEW`, `REUSE`, `LC_add`, `MC_add`, `LW_add`, `MW_add`
- Tiers are separated by `/` and evaluated lexicographically

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

This project is licensed under the [Apache License 2.0](LICENSE).
