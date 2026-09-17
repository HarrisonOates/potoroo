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

## Usage

```
potoroo [options] domain.pddl problem.pddl
```

Input files can also be piped via stdin (domain first, then problem).

### Quick examples

```bash
# Solve the Sussman anomaly with the default ADD heuristic
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

Potoroo defaults to lifted POCL, A* search, the additive `ADD` heuristic, task
action costs, weight 1, and the `STATIC` flaw order. The same defaults apply to
every representation. Any explicit `-h`, `-f`, `-s`, `-a`, or `-w` option
overrides the corresponding default.

`ADD` rather than VHPOP's reuse-aware `ADDR`: the reuse check scans every step
and effect for every open condition, so its cost grows with plan size, and on
several domains it buys very little for that. On Gripper it is catastrophic, and
not only here — VHPOP 3.0 itself needs 101,595 nodes with `ADDR` against 886
with `ADD` on `gripper-6`, and times out on `gripper-8`. `ADDR` remains
available with `-h ADDR`.

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
| `-h` | `--heuristic` | HEUR | Plan-ranking heuristic (see [Heuristics](#heuristics)) | `ADD` |
| `-l` | `--limit` | N or `unlimited` | Search-node expansion limit | unlimited |
| `-p` | `--prune` | RULES | Opt-in pruning rules (see [Pruning rules](#pruning-rules)) | none |
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
| `ADD` | Additive heuristic: sum of cost-aware ADD values for all open conditions. `committed-cost + weight × h_add`. **Default.** |
| `ADD_COST` | ADD cost term only (no step count) |
| `ADD_WORK` | ADD work: total operator count in the ADD relaxed plan |
| `ADDR` | Additive heuristic with action reuse (VHPOP's `h^r_add`): only new operators count toward the estimate. Evaluation cost grows with plan size; see the note on defaults above. |
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

## Pruning rules

VHPOP discards a partial plan only when its ordering constraints cycle or its
binding constraints become unsatisfiable, and Potoroo inherited that. Four
further rules from the plan-space literature are implemented and selected with
`-p`, as a comma-separated list; `all` enables everything and a leading `no-`
turns one off, so `-p all,no-minimality` is the three cheap rules.

| Rule | Source | Representation | What it discards |
|---|---|---|---|
| `cutset` | Nguyen & Kambhampati, IJCAI-01, Prop. 1 | every representation | A plan whose pre- or post-cutset — a step's own conditions plus every link condition the orderings force to span it — contains a mutex pair. No linearisation of such a plan is executable. Finite-domain search takes its mutexes from the translator; lifted and ground search synthesise **lifted mutex groups** from the schemas (see below). |
| `edelete` | Nguyen & Kambhampati, IJCAI-01, Def. 3 | every representation | Extends threats from "deletes the protected fact" to "cannot hold beside it". A step needing `location(truck) = lyon` threatens a link protecting `location(truck) = paris` even though it assigns nothing. Sound and it fires, but see the note below before enabling it. |
| `disjunctive` | Nguyen & Kambhampati, IJCAI-01, §4.1 | `--fdr-pocl` | Not a pruning rule but a branching one: a threat is resolved by posting `(consumer ≺ step) ∨ (step ≺ producer)` on a single child and propagating, rather than splitting the plan in two. Remaining disjunctions are split only once nothing else is refinable. |
| `params` | Gerevini & Schubert, JAIR 5 (1996), §§4–5 | lifted and ground | Two things. An action instance binding a parameter to a constant that cannot reach it, computed by propagating the initial conditions through the operator graph — this is the half that fires. And a *spurious threat*, whose unifier would have to put a parameter outside its domain or identify two parameters with disjoint domains; implemented, but no domain in `examples/` has parameter domains uneven enough to trigger it. |
| `recursion` | Smith & Peot, AIPS-96, Thms. 1 and 4 | every representation | A plan whose remaining open conditions are all suspended inside a regression loop, so every completion is non-minimal. |
| `minimality` | Kambhampati, IJCAI-95, Strategy 2 | every representation | A plan with steps `s′ ≺ s″` where everything `s″` might rely on is already guaranteed at `s′`, making the steps between them removable. |

```bash
# The three finite-domain rules, which are also the three cheapest
potoroo --fdr-pocl -p cutset,edelete,disjunctive -h LMCUT domain.pddl problem.pddl

# Everything, on the default lifted search
potoroo -p all domain.pddl problem.pddl

# Everything except the two expensive rules
potoroo -p all,no-recursion,no-minimality domain.pddl problem.pddl
```

`-v` reports the active rules, and says which of them cannot fire for the chosen
representation: `edelete` and `disjunctive` need finite-domain facts,
and `params` has nothing to say about an already-ground SAS+ task. So `-p all`
is `-p cutset,params,recursion,minimality` in lifted and ground mode, and
`-p cutset,edelete,disjunctive,recursion,minimality` under `--fdr-pocl`.
The `pruned` counter in the telemetry line
and in `POTOROO_STATS_JSON` counts the plans they discard. `max_disjunctions` in
the finite-domain JSON reports the peak number of deferred threat resolutions,
and is zero unless `disjunctive` is on.

### Runtime cost

Measured at a fixed generated-node budget, so every configuration does the same
amount of search and the difference is the rule's own price. Median of seven
runs; `us/node` is per generated node.

| Rule | `hanoi-3` | `fixit` | `logistics-a` | `gripper-6` |
|---|---|---|---|---|
| **baseline** (lifted, `ADD`) | 2.1 us/node | 1.6 us/node | 5.1 us/node | — |
| `params` | +29% | +56% | +33% | — |
| `recursion` | +119% | +138% | +71% | — |
| `minimality` | +86% | +356% | +128% | — |
| all applicable | +233% | +544% | +214% | — |
| **baseline** (`--fdr-pocl`, `LMCUT`) | 7.4 us/node | — | 119 us/node | 11.4 us/node |
| `cutset` | +14% | — | +1% | +15% |
| `edelete` | +7% | — | −1% | +4% |
| `disjunctive` | +3% | — | −1% | +3% |
| `recursion` | +32% | — | **−9%** | +12% |
| `minimality` | +7% | — | 0% | +5% |
| all applicable | +60% | — | **−6%** | +29% |

The same two structural rules cost between three and ten times less on the
finite-domain representation than on the lifted one, and fire far more often
there. A finite-domain link condition is a `Fact` — two `usize`s compared by
equality — where a literal condition is an `Rc<Literal>` whose comparison walks a
predicate and a term vector; and because a SAS+ task is ground, exact recursion
is the only kind there is. On `hanoi-3`, `minimality` rejects 3224 plans under
`--fdr-pocl` against 15 on the lifted representation, and on `logistics-a`
`recursion` prunes enough to pay for itself twice over.

The three finite-domain rules are close to free: they share one mutex table built
at setup and test a handful of facts per step, and where the heuristic dominates
(`logistics-a`, at 120 us/node under `LMCUT`) they are inside the noise. `params`
partly pays for itself by skipping the heuristic evaluation on every instance it
rejects — 17% fewer `h` evaluations on `logistics-a`.

`recursion` and `minimality` are the expensive pair, because both walk the plan's
causal-link structure on every generated node. They were 4-7x worse still before
being rewritten around a per-plan link index with dense step slots (`recursion`
on `logistics-a`: 68 us/node, now 8.8); what is left is the work the rules
actually are. Enable them where a domain loops or where plans grow redundant
tails, not by reflex.

### Lifted mutex groups

`cutset` needs sound mutexes, and the literal representation has none to hand.
An h² table would supply them, but it is quadratic in the reachable atoms.
Instead Potoroo synthesises **lifted mutex groups** from the action schemas: a
predicate together with one *counted* argument position, asserting that for each
assignment of the other positions at most one instance holds in any reachable
state. `⟨at(?v, ?l), counted = 1⟩` says a vehicle is at one location, which is
exactly the invariant a SAS+ variable encodes.

A group may have **several parts**, which is what makes two *different*
predicates mutex: `⟨at(v₀, ·), in(v₀, ·)⟩` says a package is at a location or in
a vehicle and never both, and `⟨at(v₀, ·), on(v₀, ferry)⟩` says a car is ashore
or aboard.

A candidate survives if at most one of its atoms holds initially per assignment,
and if every schema that adds an atom into the group also deletes one from it
under the *same* assignment *and* required that deleted atom as a precondition —
the fact-alternating condition. A schema that unbalances a candidate does not
discard it: each atom the schema deletes and required derives a **new part**, and
the enlarged candidate is re-tested from scratch. That is how `⟨in(v₀, ·)⟩`,
which `load-truck` unbalances by adding `in(?o, ?truck)`, grows the part
`at(v₀, ·)` from the `at(?o, ?loc)` that `load-truck` deletes.

Conditional effects, quantified effects, two adds into one group, an add whose
assignment leaves a parameter unbound, and a delete that only maybe matches the
add all reject the candidate, because a mutex claimed wrongly would let the rule
discard a refinable plan. Refinement is bounded at three parts.

This is Fišer's lifted fact-alternating mutex groups (AAAI 2020) in the shape of
Helmert's invariant synthesis (AIJ 2009).

It is the one rule that makes lifted search explore less rather than reject what
the heuristic was rejecting anyway. Under `-g -h LPLAN`, which is genuinely
cost-optimal:

| generated nodes | default | `-p cutset` |
|---|---|---|
| `test-ferry` (lifted) | 254 | **74** |
| `logistics-a` (lifted) | 13081 | **10458** |
| `gripper-4` (lifted) | 231 | **203** |
| `test-ferry` (`-g -h LPLAN`) | 720 | **344** |
| `sussman-anomaly` (`-g -h LPLAN`) | 43 | **37** |

Costs are unchanged in every row. Multi-part groups are most of that: with
single-predicate groups alone, `test-ferry` stopped at 190 and `logistics-a` did
not move at all.

But fewer nodes is not the same as less time, and here the two part company. The
check walks every step against every link, so its cost per node is
`O(steps × links)` and grows with plan length — while whether it fires at all is
a property of the domain, not of the plan's size. Measured on problems that
solve, so that node counts mean something:

| | longest plan | generated | | wall ms | |
|---|---|---|---|---|---|
| | | default | `-p cutset` | default | `-p cutset` |
| `get-paid` | 2 | 17 | 17 | 0 | 0 |
| `road-test` | 4 | 21 | 21 | 0 | 0 |
| `test-ferry` | 7 | 254 | **74** | 0 | 0 |
| `gripper-4` | 9 | 231 | **203** | 0 | 0 |
| `gripper-6` | 15 | 835 | **330** | 1 | 3 |
| `logistics-a` | 52 | 13081 | **10458** | 78 | **666** |

So: a clear win where plans stay short and the domain has state-variable
structure, and a clear loss where plans get long. `logistics-a` explores a fifth
fewer nodes and takes eight times as long to do it.

That is worth stating plainly, because it is not a fixable constant. Any
plan-space pruning rule that inspects the whole partial plan pays a price that
grows with plan length — which is exactly where POCL search is already in
trouble, and the same tension the HSDIP position paper raises about node growth.
Hoisting the binding resolution out of the inner loop cut this cost five-fold
(`logistics-a`: 2781 ms to 666 ms) and the shape did not change.

### A note on `edelete` outside `--fdr-pocl`

e-deletion works on the literal representation too — an effect asserting
something a group rules out beside the protected fact is a threat, even though
it deletes nothing named in the link. It is sound and it fires. It also does not
pay, and combining it with `cutset` is worse than `cutset` alone:

| `test-ferry`, generated | |
|---|---|
| default | 254 |
| `-p edelete` | 125 |
| `-p cutset` | **74** |
| `-p cutset,edelete` | 91 |

The extra threats cost more branching than the early ordering commitments save,
and forcing orderings sooner moves plans out of the state where `cutset` would
have rejected them outright. The same shape shows up under `--fdr-pocl`. Enable
it to study it, not to go faster.

### Does the rest of it pay, in lifted mode?

Not on this example set, and they add nothing on top of `cutset` either. Holding
`cutset` fixed and adding one rule at a time, generated nodes do not move at all:

| `logistics-a`, generated | |
|---|---|
| default | 13081 |
| `-p cutset` | 10458 |
| `-p cutset,params` | 10458 |
| `-p cutset,recursion` | 10458 |
| `-p cutset,minimality` | 10458 |
| `-p cutset,edelete` | 13345 |
| `-p all` | 13345 |

`params` does raise the `pruned` counter (1376 to 5272) without changing a
single node, which is the clearest demonstration that what it rejects is what
the `∞`-rank guard was about to reject anyway. `edelete` is the only one of the
four that changes the search, and it changes it for the worse — so `-p all` is
exactly `-p cutset,edelete`, and strictly worse than `-p cutset`.

The reason is worth recording rather than rediscovering.

Measured end-to-end with no node cap, `-p params` and `-p all` generate
**exactly** the same number of nodes as the bare default on every lifted problem
that solves, under both `ADD` and the planning-graph-free `UCPOP`. The rules are
sound and they do fire (`params` reports 3484 discards on `logistics-a`), but
every node they discard is one the search was going to throw away anyway: the
non-viable instances are already gone from the achiever index before search
starts, and what the per-node check catches later is a plan the `∞`-rank guard
would have dropped a moment afterwards. All that is saved is the heuristic
evaluation, and the check costs more than the evaluation does.

| `logistics-a`, time to solve | generated | ms |
|---|---|---|
| default | 13081 | 74 |
| `-p params` | 13081 | 107 |
| `-p all` | 13081 | 317 |

So the honest recommendation for lifted and ground search is `-p cutset` and
nothing else — not `-p all`. The finite-domain rules are a different story — `cutset` cuts visited
nodes on `gripper-4` from 184 to 170 and on `sussman-anomaly` from 13 to 12
under admissible `LMCUT`, because it discards plans on structural grounds the
heuristic cannot see.

That contrast is the whole point: a pruning rule earns its keep only by catching
plans the heuristic does not. Giving lifted mode a rule of that kind means
porting `cutset` and `edelete` to the planner's own literal space, which needs an
h² mutex table over ground atoms and a cutset test that resolves link conditions
through the binding constraints and skipping the ones still carrying variables.
That is the open work.

The obvious objection is that an h² table means grounding, which is the thing
lifted search exists to avoid. It mostly does not, because **lifted mode already
grounds**. Every planning-graph heuristic — `ADD` (the default), `ADDR`,
`RELAX`, `RELAXR` and their variants — builds `PlanningGraph` from the schemas
by a Datalog-style join, and that join materialises both the reachable ground
atom set and, for relaxed-plan extraction, the reachable ground action list.
It is lifted *evaluation*, never a Cartesian product, but the result is the same
reachable set a grounder produces, computed once per search and cached. An h²
fixpoint over it adds a pair table and a pass over actions that already exist;
it does not add grounding.

The exceptions are real but narrow:

* `-h UCPOP`, `-h OC`, `-h UC`, `-h BUC`, `-h LIFO` and `-h FIFO` build no
  planning graph, so those configurations really are ground-free and an h² table
  would introduce grounding-scale work they deliberately avoid.
* The pair table is quadratic in the reachable atoms. These benchmarks are tiny
  — `logistics-a` has 100 facts and so 4,950 pairs — but 10⁴ facts is 6 MB as a
  bitset and 10⁵ facts is 625 MB, so it needs a cap, as `lplan::fact_mutexes`
  already has one.

For both exceptions the published answer is lifted mutex groups — Fišer,
*Lifted Fact-Alternating Mutex Groups and Pruned Grounding* (AAAI 2020) and
*Operator Pruning Using Lifted Mutex Groups* (ICAPS 2023) — which are computed
from the schemas, stay lifted, and are matched against a pair of conditions
without instantiating anything.

### Why they are off by default

Every rule is solution-preserving: each discards only plans it has proved
unrefinable, or proved to have none but non-minimal completions. None of them
changes the set of plans the planner *can* return.

They do change which plan a given search returns and how many nodes it visits.
Under an admissible heuristic (`LMCUT`, `LPLAN`) A\* remains cost-optimal and
the cost is unchanged; under an inadmissible one (`ADD`, the default) the
returned plan can differ, exactly as it would under any other change to the
node set. Since every measurement published from this planner was taken without
them, enabling one is a deliberate act rather than a silent default.

`tests/pruning.rs` pins both halves of that claim: the rules leave the plans
found on the example suite unchanged, and each rule is shown to actually fire.

---

## Acknowledgements

Potoroo builds on the following work:

- **VHPOP** — Håkan L. S. Younes and Reid G. Simmons, *VHPOP: Versatile Heuristic Partial Order Planner*, JAIR 2003. The original planner this reimplements.
- **Lplan** — Tom Bylander, *A Linear Programming Heuristic for Optimal Planning*, AAAI 1997.
- **Causal-link compilation** — Pascal Bercher, Tobias Geier, and Susanne Biundo, *Using State-Based Planning Heuristics for Partial-Order Causal-Link Planning*, KI 2013.
- **Sample-FF** — Pascal Bercher, Tobias Geier, Florian Richter, and Susanne Biundo, *On Delete Relaxation in Partial-Order Causal-Link Planning*, ICTAI 2013.
- **Fast Downward** — Malte Helmert, *The Fast Downward Planning System*, JAIR 2006.
- **Cutset pruning, mutex-extended threats** — XuanLong Nguyen and Subbarao Kambhampati, *Reviving Partial Order Planning*, IJCAI 2001.
- **Operator parameter domains** — Alfonso Gerevini and Lenhart Schubert, *Accelerating Partial-Order Planners: Some Techniques for Effective Search Control and Pruning*, JAIR 1996.
- **Recursion suspension** — David E. Smith and Mark A. Peot, *Suspending Recursion in Causal-link Planning*, AIPS 1996.
- **Minimality-based pruning** — Subbarao Kambhampati, *Admissible Pruning Strategies based on plan minimality for Plan-Space Planning*, IJCAI 1995.
- **Position paper & heuristic survey** — Scott Howsam, Harrison Oates, and Pascal Bercher, *Reviving Partial Order Causal Link (POCL) Planning: Is It Possible? Is It Worth It?*, HSDIP 2026. ([PDF](https://icaps26.icaps-conference.org/files/workshops/hsdip/ICAPS_HSDIP_2026_paper_8.pdf))

---

## License

This project is licensed under the [Apache License 2.0](LICENSE).
