# Planner usage

## Input, output, and defaults

Input files may appear in either order; a single file or stdin may contain both
domain and problem. Plans go to stdout. `-v` reports search progress on stderr;
`POTOROO_STATS_JSON=1` adds machine-readable statistics. An unsolved problem prints
`no plan` and a reason; a nonzero exit status indicates an error.

Defaults: lifted representation, A* search, `ADD/LIFO`, `STATIC` flaw selection,
task action costs, weight 1, and no optional pruning. Explicit `-h` replaces the
whole ranking: `-h ADD` omits the default LIFO tie preference.

## Options

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

## Search algorithms

| `-s` | Behaviour |
|---|---|
| `A` | A* / weighted best-first search; default. |
| `IDA` | Iterative-deepening A*. |
| `HC` | Accepted as a hill-climbing alias; currently uses the best-first search path. |
| `BFS` | Breadth-first search. |
| `GBFS` | Greedy best-first search. |
| `LGBFS` | Lazy GBFS: score children when popped. |
| `LGBFS-D` | Lazy GBFS with a secondary FIFO queue. |
| `ALT` | Alternate A* and GBFS queues. |

## Restart portfolios

Stages restart from the initial plan and release their search state when finished:

```bash
./target/release/potoroo --fdr-pocl \
  --stage 'CLFF@ALT=10' --stage ADD/LIFO \
  --time-limit 20 --stage-mem-mb 600 domain.pddl problem.pddl
```

This gives CLFF/ALT up to ten seconds, then ADD/LIFO the remaining time.
Only the final stage may omit its duration. Each stage inherits other command-line
options; stage heuristics are used exactly as written.

See [Heuristics](heuristics.md) and [Flaw selection and pruning](flaw-selection-and-pruning.md) for ranking and refinement choices.
