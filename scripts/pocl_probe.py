#!/usr/bin/env python3
"""Serial, resource-bounded POCL comparisons from a JSON run manifest.

Each manifest entry has label, binary, revision, domain, problem and args.
Keep the manifest, output CSV and logs together to reproduce a comparison.
The planner gets a deadline five seconds before the external watchdog, so it
can normally report statistics before the watchdog kills its process group.
Linux RLIMIT_AS bounds each process, including translator children; the RSS
column is the planner's measured high-water mark, never a cap substituted for
a missing measurement. GNU time additionally measures the process tree's peak
individual-process RSS (not simultaneous aggregate memory).
"""

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shlex
import signal
import subprocess
import time


METRICS = [
    "solved", "plan_len", "plan_cost", "nodes_generated", "nodes_visited",
    "pruned", "supporter_forced", "h_evals", "h_eval_ms", "wall_ms",
    "peak_rss_kb", "max_queued", "h2_status", "h2_runs", "h2_completed",
    "h2_work", "h2_ms", "h2_max_mutex_pairs", "h2_max_new_mutex_pairs", "h2_max_unreachable_facts",
    "h2_supporters_removed",
]
FIELDS = [
    "run", "label", "revision", "binary_sha256", "family", "problem",
    "repeat", "memory_mb", "timeout_seconds", "planner_seconds", "node_limit",
    "returncode", "outcome", "stats_source", "external_ms", "tree_peak_rss_kb",
    "tree_user_seconds", "tree_system_seconds", *METRICS, "command",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--logs", type=Path, required=True)
    parser.add_argument("--seconds", type=int, default=600)
    parser.add_argument("--memory-mb", type=int, default=4096)
    parser.add_argument("--node-limit", default="unlimited")
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    if args.seconds <= 5 or args.memory_mb <= 0:
        parser.error("seconds must exceed 5 and memory-mb must be positive")
    runs = json.loads(args.manifest.read_text())
    args.logs.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    hashes = {}
    revisions = {}
    for run in runs:
        binary = str(Path(run["binary"]).resolve())
        if binary not in hashes:
            hashes[binary] = hashlib.sha256(Path(binary).read_bytes()).hexdigest()
        digest = hashes[binary]
        if digest in revisions and revisions[digest] != run["revision"]:
            parser.error("different revisions have identical binaries; check build directories")
        revisions[digest] = run["revision"]
        if not re.fullmatch(r"[a-zA-Z0-9_-]+", run["label"]):
            parser.error("labels must contain only letters, digits, underscores and hyphens")
    description = dict(
        runs=runs, hashes=hashes, seconds=args.seconds,
        memory_mb=args.memory_mb, node_limit=args.node_limit, fields=FIELDS,
    )
    metadata = args.output.with_suffix(".manifest.json")
    done = set()
    if args.resume and args.output.exists():
        if not metadata.exists() or json.loads(metadata.read_text()) != description:
            parser.error("resume manifest, binaries or limits differ from the original run")
        with args.output.open() as stream:
            reader = csv.DictReader(stream)
            if reader.fieldnames != FIELDS:
                parser.error("resume CSV columns differ from this harness version")
            for row in reader:
                if None in row or None in row.values() or not row["outcome"]:
                    parser.error("resume CSV has an incomplete row; preserve it and start a new file")
                done.add(int(row["run"]))
    metadata.write_text(json.dumps(description, indent=2) + "\n")
    mode = "a" if done else "w"
    env = dict(os.environ, POTOROO_STATS_JSON="1")

    def limit():
        cap = args.memory_mb * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    with args.output.open(mode) as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS, lineterminator="\n")
        if mode == "w":
            writer.writeheader()
        for index, run in enumerate(runs):
            if index in done:
                continue
            binary = str(Path(run["binary"]).resolve())
            stem = args.logs / f"{index:03d}-{run['label']}"
            timing = stem.with_suffix(".time")
            stdout = stem.with_suffix(".out")
            stderr = stem.with_suffix(".err")
            command = [
                binary, *run["args"], "-v", "--time-limit", str(args.seconds - 5),
                "--stage-mem-mb", str(args.memory_mb), "-l", args.node_limit,
                run["domain"], run["problem"],
            ]
            timed = ["/usr/bin/time", "-f", "%M %U %S", "-o", str(timing), *command]
            print(f"Starting {index + 1}/{len(runs)} {run['label']} {run['problem']}", flush=True)
            started = time.monotonic()
            timed_out = False
            with stdout.open("w") as out, stderr.open("w") as err:
                process = subprocess.Popen(
                    timed, env=env, stdout=out, stderr=err, preexec_fn=limit,
                    start_new_session=True,
                )
                try:
                    process.wait(timeout=args.seconds)
                except subprocess.TimeoutExpired:
                    timed_out = True
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass  # It exited between the deadline and the signal.
                    process.wait()
                except BaseException:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    process.wait()
                    raise
            elapsed = round((time.monotonic() - started) * 1000)
            error = stderr.read_text(errors="replace")
            payload = re.search(r"^STATS (.+)$", error, re.MULTILINE)
            stats = json.loads(payload[1]) if payload else {}
            stats_source = "final" if payload else "missing"
            outcome = "external-timeout" if timed_out else stats.get("outcome") or (
                "allocation-failure" if "memory allocation" in error else "error"
            )
            row = dict.fromkeys(FIELDS, "")
            row.update({k: stats.get(k, "") for k in METRICS})
            if timed_out:
                row["solved"] = False
            if not stats:
                # Retain last observed progress without presenting it as final.
                progress = re.findall(r"visited (\d+) \| generated (\d+)", error)
                if progress:
                    stats_source = "progress"
                    row["nodes_visited"], row["nodes_generated"] = progress[-1]
            if timing.exists():
                match = re.search(r"^(\d+) ([\d.]+) ([\d.]+)$", timing.read_text(), re.MULTILINE)
                if match:
                    row["tree_peak_rss_kb"], row["tree_user_seconds"], row["tree_system_seconds"] = match.groups()
            row.update(
                run=index, label=run["label"], revision=run["revision"],
                binary_sha256=hashes[binary], family=Path(run["problem"]).parent.name,
                problem=Path(run["problem"]).stem, repeat=run.get("repeat", 0),
                memory_mb=args.memory_mb, timeout_seconds=args.seconds,
                planner_seconds=args.seconds - 5, node_limit=args.node_limit,
                returncode=process.returncode, outcome=outcome, stats_source=stats_source, external_ms=elapsed,
                command=shlex.join(command),
            )
            writer.writerow(row)
            stream.flush()
            print({k: row[k] for k in ["label", "problem", "outcome", "wall_ms", "nodes_generated", "plan_cost", "h2_status", "h2_work"]}, flush=True)


if __name__ == "__main__":
    main()
