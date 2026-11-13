#!/usr/bin/env python3
"""Local coverage runner: one (config, task) per process, results as JSONL.

usage: run.py CONFIG_NAME OUT.jsonl [--tasks FILE] [--seconds S] [--mem-mb M] [-j N]
       [--fd SEARCH | -- POTOROO_FLAGS...]

Tasks default to every instance of the unit-cost Autoscale agile suite.
Already-recorded (config, domain, instance) triples in OUT are skipped.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

ROOT = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(ROOT, "..", ".."))
BENCH = os.path.abspath(os.path.join(REPO, "..", "autoscale-unitcost", "agile"))
POTOROO = os.environ.get("POTOROO_BIN", os.path.join(REPO, "target", "release", "potoroo"))
FD = os.path.join(REPO, "downward", "fast-downward.py")


def all_tasks():
    out = []
    for domain in sorted(os.listdir(BENCH)):
        d = os.path.join(BENCH, domain)
        for f in sorted(os.listdir(d)):
            if re.fullmatch(r"p\d+\.pddl", f):
                out.append((domain, f[:-5]))
    return out


def domain_file(domain, instance):
    d = os.path.join(BENCH, domain)
    specific = os.path.join(d, f"domain-{instance}.pddl")
    return specific if os.path.exists(specific) else os.path.join(d, "domain.pddl")


def run_one(args, flags, task, tmpdir):
    domain, instance = task
    dom = domain_file(domain, instance)
    prob = os.path.join(BENCH, domain, instance + ".pddl")
    limit = ["prlimit", f"--as={args.mem_mb * 1024 * 1024}", "--core=0",
             "timeout", "-k", "5", str(args.seconds)]
    if args.fd:
        work = os.path.join(tmpdir, f"{domain}-{instance}")
        os.makedirs(work, exist_ok=True)
        cmd = limit + [sys.executable, FD, dom, prob, "--search", args.fd]
        cwd = work
    else:
        cmd = limit + [POTOROO] + flags + ["-v", dom, prob]
        cwd = tmpdir
    start = time.time()
    env = dict(os.environ, POTOROO_FD=FD)
    p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, errors="replace")
    elapsed = time.time() - start
    out = p.stdout + "\n" + p.stderr
    rec = {"config": args.config, "domain": domain, "instance": instance,
           "elapsed": round(elapsed, 2), "rc": p.returncode}
    if args.fd:
        solved = "Solution found" in out
        m = re.search(r"Expanded (\d+) state", out)
        rec["expanded"] = int(m.group(1)) if m else None
        m = re.search(r"Plan length: (\d+)", out)
        rec["plan_len"] = int(m.group(1)) if m else None
    else:
        solved = re.search(r"^Plan: (\d+) steps", out, re.M) is not None
        m = re.search(r"^Plan: (\d+) steps", out, re.M)
        rec["plan_len"] = int(m.group(1)) if m else None
        gens = re.findall(r"generated (\d+)", out)
        rec["generated"] = int(gens[-1]) if gens else None
        vis = re.findall(r"visited (\d+)", out)
        rec["visited"] = int(vis[-1]) if vis else None
    if solved:
        status = "solved"
    elif "memory allocation" in out or "MemoryError" in out or "std::bad_alloc" in out \
            or p.returncode in (-6, 134, 137) or "Memory limit" in out:
        status = "memout"
    elif p.returncode == 124 or p.returncode == -9:
        status = "timeout"
    elif "No solution" in out or "unsolvable" in out.lower():
        status = "unsolvable"
    else:
        status = "error"
        rec["tail"] = out[-400:]
    rec["status"] = status
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("config")
    ap.add_argument("out")
    ap.add_argument("--tasks")
    ap.add_argument("--seconds", type=int, default=60)
    ap.add_argument("--mem-mb", type=int, default=2048)
    ap.add_argument("-j", type=int, default=6)
    ap.add_argument("--fd")
    ap.add_argument("flags", nargs="*")
    args = ap.parse_args()
    tasks = all_tasks()
    if args.tasks:
        keep = {tuple(l.split()[:2]) for l in open(args.tasks) if l.strip()}
        tasks = [t for t in tasks if t in keep]
    done = set()
    if os.path.exists(args.out):
        for l in open(args.out):
            r = json.loads(l)
            if r["config"] == args.config:
                done.add((r["domain"], r["instance"]))
    todo = [t for t in tasks if t not in done]
    tmpdir = os.path.join("/tmp/claude-1000", "pocl-runs", args.config)
    os.makedirs(tmpdir, exist_ok=True)
    print(f"{args.config}: {len(todo)} tasks to run", file=sys.stderr)
    solved = 0
    with ThreadPoolExecutor(args.j) as ex, open(args.out, "a") as fh:
        futures = [ex.submit(run_one, args, args.flags, t, tmpdir) for t in todo]
        for fut in as_completed(futures):
            rec = fut.result()
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            solved += rec["status"] == "solved"
    print(f"{args.config}: solved {solved}/{len(todo)}", file=sys.stderr)


if __name__ == "__main__":
    main()
