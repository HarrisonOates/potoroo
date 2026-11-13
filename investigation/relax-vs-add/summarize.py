#!/usr/bin/env python3
"""Extract local probe outcomes and identical-plan evaluator timings."""
import csv
import hashlib
import json
from pathlib import Path
from statistics import median

root = Path(__file__).resolve().parent
summary = {"probes": [], "timings": {}, "heuristic_source_comparison": []}
for name in ("probe", "followup", "representations"):
    with (root / (name + ".csv")).open() as stream:
        for row in csv.DictReader(stream):
            fields = ("label", "outcome", "nodes_generated", "nodes_visited", "plan_cost", "h_evals", "h_eval_ms", "wall_ms")
            summary["probes"].append({"source": name + ".csv", **{f: row[f] for f in fields}})
for path in sorted(root.glob("*-diagnostic.txt")):
    lines = path.read_text().splitlines()
    header = next(line.split(",") for line in lines if line.startswith("kind,visited,"))
    rows = [dict(zip(header, line.split(","))) for line in lines if line.startswith("sample,")]
    measured = [r for r in rows if int(r["opens"]) > 0 and int(r["add_ns"]) > 0]
    summary["timings"][path.name] = {
        "samples": len(rows), "nonempty_samples": len(measured), "root": rows[0],
        "median_add_us": median(int(r["add_ns"]) / 1000 for r in measured),
        "median_relax_us": median(int(r["relax_ns"]) / 1000 for r in measured),
        "median_relax_over_add": median(int(r["relax_ns"]) / int(r["add_ns"]) for r in measured),
    }

repo = root.parents[1]
frozen = repo.parent / "potoroo-cluster/results/rerun-2026-11-04-memory/build/potoroo/src"
def function_body(source, name):
    start = source.index("fn " + name + "(")
    end = source.index("{", start) + 1
    depth = 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    return source[start:end]

for file, functions in {
    "planning_graph.rs": ("extract_relaxed_plan", "goal_atom", "cheapest_achiever"),
    "fdr_pocl.rs": ("relaxed_plan_size", "open_estimate", "push_add_rank"),
}.items():
    for name in functions:
        old = function_body((frozen / file).read_text(), name)
        current = function_body((repo / "src" / file).read_text(), name)
        summary["heuristic_source_comparison"].append({
            "file": file, "function": name, "identical": old == current,
            "frozen_sha256": hashlib.sha256(old.encode()).hexdigest(),
            "current_sha256": hashlib.sha256(current.encode()).hexdigest(),
        })
(root / "local-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary["timings"], indent=2))
