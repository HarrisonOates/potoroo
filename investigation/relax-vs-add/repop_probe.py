#!/usr/bin/env python3
"""Prepare/run the paper-recurrence comparison; all measurements run serially.

Build the release binary first. Selected failure cases are asserted against the
frozen cluster snapshot, and local inputs must match both cluster input hashes.
The optional --run invokes the existing bounded harness in potoroo-cluster.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
SNAPSHOT = ROOT.parent / "potoroo-cluster/results/cluster-memory-2026-11-07-0836"
CASES = [("gripper", "p01"), ("gripper", "p03"), ("miconic", "p01"),
         ("miconic", "p02"), ("childsnack", "p01"), ("elevators", "p02"),
         ("parcprinter", "p03")]
CE = "cutset,edelete,disjunctive,h2"
PROFILES = [
    ("add", "ADD", 1, "ZLIFO", "none"),
    ("relax", "RELAX", 1, "ZLIFO", "none"),
    ("relax_w5", "RELAX", 5, "ZLIFO", "none"),
    ("repop", "REPOP", 1, "ZLIFO", "none"),
    ("repop_w5", "REPOP", 5, "ZLIFO", "none"),
    ("repop_w5_lifo", "REPOP", 5, "UCPOP", "none"),
    ("repop_w5_ce", "REPOP", 5, "UCPOP", CE),
    ("add_w5_ce", "ADD", 5, "UCPOP", CE),
]
CONTROLS = [
    ("relax_w5_lifo", "RELAX", 5, "UCPOP", "none"),
    ("relax_w5_ce", "RELAX", 5, "UCPOP", CE),
    ("repop_lifo", "REPOP", 1, "UCPOP", "none"),
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(suite):
    prefix = "repop" if suite == "main" else f"repop-{suite}"
    cases = CASES if suite != "extended" else [CASES[i] for i in [0, 1, 4, 5]]
    profiles = PROFILES if suite == "main" else CONTROLS if suite == "controls" else [PROFILES[6]]
    rows = {}
    for path in sorted((SNAPSHOT / "results").glob("*.jsonl")):
        for line in path.read_text().splitlines():
            r = json.loads(line)
            if (r["domain"], r["instance"]) in CASES and r["config"] in (
                "fdr-zlifo-add+lifo", "fdr-zlifo-relax+lifo"
            ):
                key = (r["domain"], r["instance"], r["config"])
                assert key not in rows, key
                rows[key] = r
    runs, evidence = [], []
    for domain, instance in cases:
        bench = ROOT.parent / "autoscale-unitcost/agile" / domain
        d = bench / (f"domain-{instance}.pddl" if domain == "parcprinter" else "domain.pddl")
        p = bench / f"{instance}.pddl"
        add = rows[domain, instance, "fdr-zlifo-add+lifo"]
        relax = rows[domain, instance, "fdr-zlifo-relax+lifo"]
        assert add["status"] == "solved"
        if domain != "parcprinter":
            assert relax["status"] != "solved"
        for row in [add, relax]:
            assert digest(d) == row["domain_sha256"]
            assert digest(p) == row["problem_sha256"]
        evidence.append(dict(domain=domain, instance=instance, control=domain == "parcprinter",
                             domain_sha256=digest(d), problem_sha256=digest(p),
                             cluster_add=add["status"], cluster_relax=relax["status"]))
        for label, heuristic, weight, flaws, prune in profiles:
            runs.append(dict(
                label=f"{domain}-{instance}-{label}", binary=str(ROOT / "target/release/potoroo"),
                revision="2b7bf40+repop-investigation", domain=str(d), problem=str(p),
                args=["--fdr-pocl", "-f", flaws, "-h", heuristic + "/LIFO", "-s", "A",
                      "-w", str(weight), "-p", prune],
            ))
    (OUT / f"{prefix}-manifest.json").write_text(json.dumps(runs, indent=2) + "\n")
    sources = [ROOT / "Cargo.toml", ROOT / "Cargo.lock", *sorted((ROOT / "src").rglob("*.rs"))]
    provenance = dict(
        source_commit=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        source_dirty=True,
        source_hashes={str(p.relative_to(ROOT)): digest(p) for p in sources},
        binary_sha256=digest(ROOT / "target/release/potoroo"),
        rustc=subprocess.check_output(["rustc", "--version"], text=True).strip(),
        cases=evidence,
        harness_sha256=digest(ROOT.parent / "potoroo-cluster/scripts/potoroo/pocl_probe.py"),
        paper="https://rakaposhi.eas.asu.edu/ucpop-revive.pdf",
    )
    (OUT / f"{prefix}-provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    print(f"Prepared {len(runs)} runs; all inputs match the frozen snapshot.", flush=True)
    return prefix


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--suite", choices=["main", "controls", "extended"], default="main")
    args = parser.parse_args()
    prefix = prepare(args.suite)
    if args.run:
        subprocess.run([
            "python3", str(ROOT.parent / "potoroo-cluster/scripts/potoroo/pocl_probe.py"),
            str(OUT / f"{prefix}-manifest.json"), "--output", str(OUT / f"{prefix}.csv"),
            "--logs", str(ROOT / "target/relax-investigation" / prefix),
            "--seconds", "65" if args.suite == "extended" else "15",
            "--memory-mb", "2048" if args.suite == "extended" else "1024",
            "--node-limit", "2000000" if args.suite == "extended" else "200000",
        ], cwd=ROOT, env=dict(os.environ, POTOROO_FD=str(ROOT.parent / "downward/fast-downward.py")),
           check=True)
