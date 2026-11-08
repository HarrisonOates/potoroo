# Operator-class steps: achiever structure diagnostic

November 2026. Question: do high-branching open conditions in FDR have
achievers that could share one symbolic step (an operator class) and be split
later, as Descartes-style least commitment proposes?

`classes.py` over Potoroo's FD translation (default options) of p01/p05 of the
achiever-heavy and control domains; output in `p01-p05.txt`. Facts with more
than 20 achievers only.

## Result: no free collapse; initial ADD already separates achievers

* **Every achiever is distinct.** Distinct precondition maps equal the
  achiever count on every high-branching fact except data-network (256 of 288)
  and organic synthesis medians. Shared preconditions (MustPre) are 0–2.
  A class step would open almost nothing until split.
* **Single-variable splits are binary.** Achievers disagree on 15–270
  variables, mostly binary STRIPS atoms, so the cheapest variable split gives
  two classes: a log-depth binary decision tree over the same leaves.
* **Splitting by schema argument** gives 3–30 classes (snake headsnake 4,
  tidybot 3, pipesworld-tankage 3–4, pipesworld-notankage 12–16), i.e. lifted
  binding order.
* **Few ties.** Among achievers, those whose precondition ADD from the
  initial state is minimal: median 1–7, at most a few within +1. Exceptions:
  organic synthesis (`do_18_*`: 156–585 tied of 3,422) and pegsol
  `move-ended` (13 of 33).

## Implication

With PEA only the minimal-f children are queued, so a class step whose h is
the minimum over its members would save heuristic evaluations, not queued
plans, except in organic synthesis. Its search benefit depends on deferral
paying off: the cheapest achiever being wrong and later commitments revealing
it. That is not measured here; it needs instrumentation of how often A*
returns to sibling achievers of a high-branching condition.
