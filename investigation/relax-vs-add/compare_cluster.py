#!/usr/bin/env python3
"""Compare ADD and RELAX on identical completed tasks in one frozen snapshot.

Reject duplicate attempts and mismatched inputs/budgets rather than silently
combining overlapping snapshots. Uses only the Python standard library.
"""

import argparse
from collections import Counter, defaultdict
import hashlib
import json
import math
from pathlib import Path
from statistics import median


def fingerprint(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ratio(values):
    return {
        "pairs": len(values),
        "median": median(values) if values else None,
        "geometric_mean": math.exp(sum(map(math.log, values)) / len(values)) if values else None,
    }


def analyse(snapshot):
    experiment = json.loads((snapshot / "experiment.json").read_text())
    if fingerprint(snapshot / "tasks.tsv") != experiment["tasks_sha256"]:
        raise ValueError("task manifest does not match experiment.json")
    rows = defaultdict(dict)
    sources = []
    for path in sorted((snapshot / "results").glob("*.jsonl")):
        content = path.read_bytes()
        sources.append({"path": str(path.relative_to(snapshot)), "sha256": hashlib.sha256(content).hexdigest()})
        for line in content.splitlines():
            row = json.loads(line)
            for field in ("run_id", "image_sha256", "source_tree_sha256", "timeout_s", "mem_mb"):
                if row[field] != experiment[field]:
                    raise ValueError(f"{path}: mismatched {field}")
            task = (row["domain"], row["instance"])
            if task in rows[row["config"]]:
                raise ValueError(f"duplicate attempt: {row['config']} {task}")
            rows[row["config"]][task] = row

    comparisons = []
    for mode in ("fdr", "lifted", "ground"):
        add = rows[f"{mode}-zlifo-add+lifo"]
        relax = rows[f"{mode}-zlifo-relax+lifo"]
        common = sorted(add.keys() & relax.keys())
        pairs = []
        domains = defaultdict(Counter)
        outcomes = Counter()
        metrics = defaultdict(list)
        for task in common:
            a, r = add[task], relax[task]
            for field in ("domain_sha256", "problem_sha256", "timeout_s", "mem_mb", "image_sha256"):
                if a[field] != r[field]:
                    raise ValueError(f"{task}: pair mismatch for {field}")
            if a["flags"].replace("ADD/LIFO", "RELAX/LIFO") != r["flags"]:
                raise ValueError(f"{task}: mismatched flags")
            solved_a, solved_r = a["status"] == "solved", r["status"] == "solved"
            category = "both" if solved_a and solved_r else "add_only" if solved_a else "relax_only" if solved_r else "neither"
            domains[task[0]][category] += 1
            outcomes[f"{a['status']} -> {r['status']}"] += 1
            fields = ("status", "elapsed_ms", "nodes_generated", "nodes_visited", "stats_source", "planner_stats")
            pairs.append({"domain": task[0], "instance": task[1], "category": category,
                          "add": {k: a.get(k) for k in fields}, "relax": {k: r.get(k) for k in fields}})
            if solved_a and solved_r:
                for field in ("elapsed_ms", "nodes_generated", "nodes_visited", "plan_cost", "peak_rss_kb", "max_queued"):
                    av, rv = a.get(field), r.get(field)
                    if isinstance(av, (int, float)) and isinstance(rv, (int, float)) and av > 0 and rv > 0:
                        metrics[field].append(rv / av)
        counts = Counter(p["category"] for p in pairs)
        comparisons.append({
            "mode": mode, "add_completed": len(add), "relax_completed": len(relax), "common": len(common),
            "add_solved_common": counts["both"] + counts["add_only"],
            "relax_solved_common": counts["both"] + counts["relax_only"],
            "categories": dict(counts), "outcomes_add_to_relax": dict(outcomes),
            "relax_over_add_jointly_solved": {k: ratio(v) for k, v in metrics.items()},
            "domains": {k: dict(v) for k, v in sorted(domains.items())}, "pairs": pairs,
        })
    return {"snapshot": str(snapshot.resolve()), "experiment": experiment, "sources": sources,
            "tasks_sha256": fingerprint(snapshot / "tasks.tsv"),
            "caveats": ["Completed subsets are not random and RELAX is incomplete.",
                        "Failed-run progress counters are lower bounds, not final totals.",
                        "Jointly solved ratios exclude failures and do not describe the full suite."],
            "comparisons": comparisons}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = analyse(args.snapshot)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    for comparison in result["comparisons"]:
        print({k: comparison[k] for k in ("mode", "common", "add_solved_common", "relax_solved_common", "categories")})
