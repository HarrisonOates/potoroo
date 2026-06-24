# Potoroo

A modern **partial-order causal-link (POCL) planner** written in Rust.

Potoroo is based on [VHPOP](http://www.tempastic.org/vhpop/) (Younes & Simmons 2003).
The aim is to provide a correct, fast, and well-documented POCL planner that implements all known POCL heuristics — including those whose original source code has been lost to time — and serves as a jumping-off point for future POCL planning research.

The name comes from the [potoroo](https://en.wikipedia.org/wiki/Potoroo), a small Australian marsupial.

---

## Features

- **Full POCL search** with lifted and grounded action modes
- **Reachability-based grounder** via Fast Downward's translator when in ground mode (`-g`), with fallback to naive instantiation
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

---

## Usage

```
potoroo [options] domain.pddl problem.pddl
```

Input files can also be piped via stdin (domain first, then problem).

### Quick examples

```bash
# Solve the Sussman anomaly with the default UCPOP heuristic
potoroo examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl

# Use the additive heuristic
potoroo -h ADD examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl

# Use the Lplan LP heuristic (admissible) with ground actions
potoroo -h LPLAN -g examples/blocks-world-domain.pddl examples/bw-large-a.pddl

# Compile to classical planning and evaluate with LM-cut (requires Fast Downward)
potoroo -h COMPILE_LMCUT -g examples/gripper-domain.pddl examples/gripper-4.pddl

# Compose two heuristics (lexicographic tiebreaking)
potoroo -h "UCPOP/ADD" examples/logistics-domain.pddl examples/logistics-a.pddl
```

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

Set `POTOROO_STATS_JSON=1` to emit a machine-readable JSON line on stderr:

```json
STATS {"problem":"...","heuristic":"...","ground":false,"solved":true,"plan_len":6,"nodes_generated":142,"nodes_visited":38,"wall_ms":12}
```

---

## Options reference

| Flag | Long form | Argument | Description | Default |
|------|-----------|----------|-------------|---------|
| `-a` | `--action-cost` | `UNIT`\|`DURATION`\|`RELATIVE` | Action cost model | `UNIT` |
| `-f` | `--flaw-order` | ORDER | Flaw-selection order (see [Flaw orders](#flaw-selection-orders)) | `UCPOP` |
| `-g` | `--ground-actions` | — | Plan with fully ground actions (required for `LPLAN`, `SAMPLE_FF`, `COMPILE*`) | lifted |
| `-h` | `--heuristic` | HEUR | Plan-ranking heuristic (see [Heuristics](#heuristics)) | `UCPOP` |
| `-l` | `--limit` | N or `unlimited` | Search-node expansion limit | unlimited |
| `-s` | `--search-algorithm` | `A` | Search algorithm (`A` = best-first A\*) | `A` |
| `-v` | `--verbose` | [N] | Verbosity level (0–3) | 0 |
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
| `UCPOP` | `steps + weight × (open-conditions + unsafe-links)` — the heuristic from the original UCPOP planner. **Default.** |
| `OC` | Open-condition count |
| `UC` | Unsafe-link (threat) count |
| `BUC` | Binary unsafe count (0 if no threats, 1 otherwise) |
| `LIFO` | Last-in-first-out ordering (newest plan first) |
| `FIFO` | First-in-first-out ordering (oldest plan first) |

### Planning-graph heuristics

These build an incremental Graphplan-style planning graph. Ground mode (`-g`) is not required but may give better estimates by resolving more bindings.

| Name | Description |
|------|-------------|
| `ADD` | Additive heuristic: sum of ADD-layer costs for all open conditions. `steps + weight × h_add` |
| `ADD_COST` | ADD cost term only (no step count) |
| `ADD_WORK` | ADD work: total operator count in the ADD relaxed plan |
| `ADDR` | Additive heuristic with action reuse: only new operators count toward the estimate |
| `ADDR_COST` | ADDR cost only |
| `ADDR_WORK` | ADDR work |
| `RELAX` | Delete-relaxed plan size (FF-style joint extraction): `steps + weight × |π_relax|` |
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
| `UCPOP` | `{n,s}LIFO/{o}LIFO` — threats (non-separable then separable) LIFO, then open conditions LIFO. **Default.** |
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

