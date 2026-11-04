#!/usr/bin/env python3
"""Compare threat-coalescing traces from an instrumented planner.

Requires POTOROO_TRACE_MODE/POTOROO_TRACE_LIMIT support and TRACE/EDGE records.
Runs four bookkeeping variants and three queue-tie policies serially.
Timings are diagnostic only.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess


def records(path, kind):
    return [line.split("\t") for line in path.read_text().splitlines()
            if line.startswith(kind + "\t")]


def compare_paths(before, shared):
    paths, edges, counts = [], [], []
    for path in [before, shared]:
        visits = records(path, "TRACE")
        parents = {visit[2]: visit[-1] for visit in visits}
        collapsed = []
        for visit in visits:
            if not collapsed or visit[-1] != collapsed[-1]:
                collapsed.append(visit[-1])
        queued = records(path, "EDGE")
        # Keep parent, actual primary rank and child; omit the generation-id
        # tiebreaker, whose absolute value changes when a queue step is elided.
        substantive = [(parents[e[1]], json.loads(e[3])[0], e[-1])
                       for e in queued if parents[e[1]] != e[-1]]
        paths.append(collapsed)
        edges.append(substantive)
        counts.append(dict(visited=len(visits), distinct_successive=len(collapsed),
                           queued=len(queued), substantive=len(substantive),
                           redundant=len(queued) - len(substantive)))
    return dict(counts=counts, same_states=paths[0] == paths[1],
                same_substantive_edges=edges[0] == edges[1])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--domain", type=Path, required=True)
    parser.add_argument("--problem", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--seconds", type=int, default=600)
    parser.add_argument("--memory-mb", type=int, default=4096)
    args = parser.parse_args()
    if args.seconds <= 5 or args.memory_mb <= 0:
        parser.error("seconds must exceed 5 and memory-mb must be positive")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    if any(args.output_dir.iterdir()):
        parser.error("output-dir must be empty to preserve previous evidence")
    binary = args.binary.resolve()
    runs = []

    def cap():
        limit = args.memory_mb * 1024 ** 2
        resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    def run(heuristic, mode, trace_limit, prefix=""):
        name = prefix + heuristic.replace("/", "-") + "-" + mode
        command = [str(binary), "--fdr-pocl", "-f", "ZLIFO", "-h", heuristic,
                   "-p", "cutset,edelete,disjunctive,supporters,h2", "-v",
                   "--time-limit", str(args.seconds - 5), "--stage-mem-mb",
                   str(args.memory_mb), "-l", "unlimited",
                   str(args.domain.resolve()), str(args.problem.resolve())]
        settings = dict(POTOROO_TRACE_MODE=mode,
                        POTOROO_TRACE_LIMIT=str(trace_limit), POTOROO_STATS_JSON="1")
        error_path = args.output_dir / (name + ".err")
        with (args.output_dir / (name + ".out")).open("w") as out, error_path.open("w") as err:
            process = subprocess.Popen(command, stdout=out, stderr=err,
                                       env=dict(os.environ, **settings),
                                       preexec_fn=cap, start_new_session=True)
            try:
                process.wait(timeout=args.seconds)
            except BaseException:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
                raise
        error = error_path.read_text()
        payload = re.search(r"^STATS (.+)$", error, re.MULTILINE)
        if process.returncode != 0 or not payload:
            raise RuntimeError(f"{name} failed; inspect {error_path}")
        stats = json.loads(payload[1])
        if trace_limit and not records(error_path, "TRACE"):
            raise RuntimeError("binary did not emit diagnostic traces; apply the patch")
        runs.append(dict(name=name, mode=mode, heuristic=heuristic, command=command,
                         env=settings, returncode=process.returncode, stats=stats))
        print(name, stats["outcome"], stats["nodes_generated"], stats["nodes_visited"], flush=True)
        return error_path

    for heuristic in ["ADD", "ADD/LIFO", "ADD/FIFO"]:
        for mode in ["base", "storage", "share", "both"]:
            run(heuristic, mode, 1000 if heuristic == "ADD" else 0)
    # Use the observed full visit count, so the comparison cannot silently
    # succeed on a truncated trace of a larger problem.
    path_logs = []
    for mode in ["base", "share"]:
        previous = next(r for r in runs if r["heuristic"] == "ADD/LIFO" and r["mode"] == mode)
        path_logs.append(run("ADD/LIFO", mode, previous["stats"]["nodes_visited"] + 1, "path-"))
        assert runs[-1]["stats"]["outcome"] == "solved", "comparison requires completed searches"
        assert len(records(path_logs[-1], "TRACE")) == runs[-1]["stats"]["nodes_visited"]
    comparison = compare_paths(*path_logs)
    metadata = dict(binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                    domain_sha256=hashlib.sha256(args.domain.read_bytes()).hexdigest(),
                    problem_sha256=hashlib.sha256(args.problem.read_bytes()).hexdigest(),
                    seconds=args.seconds, memory_mb=args.memory_mb,
                    runs=runs, comparison=comparison)
    (args.output_dir / "results.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps(comparison, indent=2))


if __name__ == "__main__":
    main()
