# Flaw selection and pruning

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

See [Heuristics](heuristics.md) for queue rankings and [Command-line reference](planner-usage.md) for search algorithms and limits.
