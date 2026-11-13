# Heuristics

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

## Cost, work, and reuse

`ADD_WORK` and `ADDR_WORK` estimate causal-link refinement effort. Initially true or reusable facts cost one link; other facts inherit the effort of cost-minimizing support plus one. `MW` and `LW` flaw orders use work estimates; `MC` and `LC` use action cost. A ranking such as `FFR/ADD_WORK/LIFO` uses work to break equal FFR ranks.

`FF` extracts one relaxed plan for the joint outstanding open conditions. `FFR` first discounts open conditions that a committed action could support under the current orderings. This reuse check is optimistic: it does not reject support necessarily overwritten between producer and consumer. It also does not discount existing support recursively needed by a future action. `FFOC` instead extracts a support plan per open condition; `FFOCR` adds the same reuse filter. These are experimental POCL adaptations, without FF's helpful-action pruning or enforced hill climbing.

`TADD`, `FLOW`, and `HYB` account for value-token shortfalls. An action that requires a variable's value and overwrites it consumes one occurrence of that value. `TADD` charges shortfalls at their cheapest reproduction costs; `FLOW` computes per-variable min-cost flow over the domain transition graph.

`REPOP` implements the regression ranking recurrence in Nguyen and Kambhampati (2001), §3. Use `-w 5` for the paper's heuristic weight. Selecting the ranking does not enable RePOP's consistency enforcement or change flaw selection.

## Experimental finite-domain search options

`-f ORDER@HEURISTIC[*WEIGHT]` assigns an interleaved flaw-order queue its own ranking and weight. A queue is dropped if its heuristic cannot handle the task. `--pea` enables partial-expansion A*: it queues children at the current f-value and revisits the parent at the next one.

`--preferred` adds a preferred-refinement queue to native finite-domain `A` or `GBFS` search. It favours future actions selected by an FF relaxed plan, links to existing steps, and ordering refinements. Every refinement also remains in the ordinary queue. The preferred queue receives five selections per ordinary selection, with fallback when either is empty. This changes expansion order, including for `A`, so it does not preserve ordinary A* ordering. It requires unconditional, axiom-free, unit-cost tasks.

Native `COMPILE_FF` and `COMPILE_LMCUT` rebuild a causal-link compiled task at each evaluation. Native `COMPILE_FF` uses additive supporters, so its tie choices can differ from Fast Downward's FF evaluator.

See [References](references.md) for the source papers. No single configuration dominates across domains; compare configurations on the tasks and limits relevant to your use case.
