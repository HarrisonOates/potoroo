#!/usr/bin/env python3
"""Tabulate VHPOP benchmark stats (Phase 0b).

Reads one JSON object per line (the payloads emitted after `STATS ` by the
planner under VHPOP_STATS_JSON), from a file argument or stdin, and prints a
per-problem comparison table with one column group per heuristic:

    solved | plan_len | generated | visited | wall_ms

so a new heuristic can be compared against the UCPOP/ADD baselines at a glance.
Dependency-free (standard library only).
"""
import json
import sys
from collections import OrderedDict


def load(stream):
    rows = []
    for line in stream:
        line = line.strip()
        if not line:
            continue
        if line.startswith("STATS "):
            line = line[len("STATS "):]
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError:
            print(f"warning: skipping unparseable line: {line}", file=sys.stderr)
    return rows


def main():
    if len(sys.argv) > 1:
        with open(sys.argv[1]) as f:
            rows = load(f)
    else:
        rows = load(sys.stdin)

    if not rows:
        print("no STATS rows collected", file=sys.stderr)
        return 1

    # Preserve first-seen order for both problems and heuristics.
    problems = OrderedDict()
    heuristics = OrderedDict()
    for r in rows:
        problems.setdefault(r["problem"], None)
        heuristics.setdefault(r["heuristic"], None)
    # Index by (problem, heuristic) -> row.
    cell = {(r["problem"], r["heuristic"]): r for r in rows}

    heurs = list(heuristics)
    pcol = max([len("problem")] + [len(p) for p in problems])

    # Header.
    sub = ["slv", "len", "gen", "vis", "ms"]
    subw = {"slv": 3, "len": 5, "gen": 9, "vis": 9, "ms": 7}
    header1 = " " * pcol
    for h in heurs:
        width = sum(subw.values()) + len(sub) - 1
        header1 += "  " + h.center(width)
    print(header1)
    header2 = "problem".ljust(pcol)
    for _h in heurs:
        header2 += "  " + " ".join(s.rjust(subw[s]) for s in sub)
    print(header2)
    print("-" * len(header2))

    # Rows.
    for p in problems:
        line = p.ljust(pcol)
        for h in heurs:
            r = cell.get((p, h))
            if r is None:
                line += "  " + " ".join("-".rjust(subw[s]) for s in sub)
                continue
            vals = {
                "slv": "Y" if r.get("solved") else "n",
                "len": str(r.get("plan_len", 0)),
                "gen": str(r.get("nodes_generated", 0)),
                "vis": str(r.get("nodes_visited", 0)),
                "ms": str(r.get("wall_ms", 0)),
            }
            line += "  " + " ".join(vals[s].rjust(subw[s]) for s in sub)
        print(line)

    # Coverage summary.
    print()
    for h in heurs:
        solved = sum(1 for p in problems if (cell.get((p, h)) or {}).get("solved"))
        print(f"coverage[{h}] = {solved}/{len(problems)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
