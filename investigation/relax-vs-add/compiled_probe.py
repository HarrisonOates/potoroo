#!/usr/bin/env python3
"""Prepare/run the cost-correct compilation and open-occurrence FF comparison; all measurements run serially.

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
VHPOP_DOMAINS = [("driverlog", "p01"), ("zenotravel", "p01"), ("satellite", "p01")]
PROFILES = [
    (label, heuristic, weight, "ZLIFO", "none", search, False)
    for label, heuristic, weight, search in [
        ("add", "ADD", 1, "A"), ("ff", "FF", 1, "A"),
        ("clff", "CLFF", 1, "A"), ("ffoc", "FFOC", 1, "A"),
        ("ffoc_w5", "FFOC", 5, "A"), ("ffoc_gbfs", "FFOC", 1, "GBFS"),
        ("compile_ff", "COMPILE_FF", 1, "A"),
        ("compile_lmcut", "COMPILE_LMCUT", 1, "A"),
    ]
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(suite):
    prefix = "ff-compiled" if suite == "main" else f"ff-compiled-{suite}"
    cases = CASES if suite == "main" else VHPOP_DOMAINS
    profiles = PROFILES
    rows = {}
    for path in sorted((SNAPSHOT / "results").glob("*.jsonl")):
        for line in path.read_text().splitlines():
            r = json.loads(line)
            if (r["domain"], r["instance"]) in cases and r["config"] in (
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
        relax = rows.get((domain, instance, "fdr-zlifo-relax+lifo"))
        if suite == "main":
            assert add["status"] == "solved"
        if suite == "main" and domain != "parcprinter":
            assert relax is not None
            assert relax["status"] != "solved"
        for row in [r for r in [add, relax] if r is not None]:
            assert digest(d) == row["domain_sha256"]
            assert digest(p) == row["problem_sha256"]
        evidence.append(dict(domain=domain, instance=instance, control=domain == "parcprinter",
                             selection="ADD-only or Parcprinter control" if suite == "main" else "first autoscale instance in each VHPOP Table 1 domain",
                             domain_sha256=digest(d), problem_sha256=digest(p),
                             cluster_add=add["status"], cluster_relax=relax["status"] if relax else "missing"))
        for label, heuristic, weight, flaws, prune, search, preferred in profiles:
            runs.append(dict(
                label=f"{domain}-{instance}-{label}", binary=str(ROOT / "target/release/potoroo"),
                revision="2b7bf40+ff-compiled-investigation", domain=str(d), problem=str(p),
                args=["--fdr-pocl", "-f", flaws, "-h", heuristic + "/LIFO", "-s", search,
                      "-w", str(weight), "-p", prune] + (["--preferred"] if preferred else []),
            ))
    assert not (OUT / f"{prefix}.csv").exists(), "preserve existing results before rerunning"
    (OUT / f"{prefix}-manifest.json").write_text(json.dumps(runs, indent=2) + "\n")
    sources = [ROOT / "Cargo.toml", ROOT / "Cargo.lock", *sorted((ROOT / "src").rglob("*.rs"))]
    fd = (ROOT / "downward").resolve()
    translator = fd / "builds/release/bin/fast_downward/translate"
    provenance = dict(
        source_commit=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        source_dirty=True,
        source_hashes={str(p.relative_to(ROOT)): digest(p) for p in sources},
        binary_sha256=digest(ROOT / "target/release/potoroo"),
        probe_sha256=digest(Path(__file__)),
        rustc=subprocess.check_output(["rustc", "--version"], text=True).strip(),
        cases=evidence,
        harness_sha256=digest(ROOT.parent / "potoroo-cluster/scripts/potoroo/pocl_probe.py"),
        wrapper_sha256=digest(OUT / "ff_capture_translate.py"),
        translator_root=str(translator),
        translator_hashes={str(p.relative_to(translator)): digest(p) for p in sorted(translator.rglob("*.py"))},
        downward_revision=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=fd, text=True).strip(),
        downward_dirty=bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=fd, text=True).strip()),
        papers=["https://www.cs.cmu.edu/afs/cs/project/jair/pub/volume20/younes03a-html/node6.html",
                "https://arxiv.org/pdf/1106.0675"],
    )
    (OUT / f"{prefix}-provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    print(f"Prepared {len(runs)} runs; all inputs match the frozen snapshot.", flush=True)
    return prefix


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--suite", choices=["main", "vhpop-domains"], default="main")
    args = parser.parse_args()
    prefix = prepare(args.suite)
    if args.run:
        subprocess.run([
            "python3", str(ROOT.parent / "potoroo-cluster/scripts/potoroo/pocl_probe.py"),
            str(OUT / f"{prefix}-manifest.json"), "--output", str(OUT / f"{prefix}.csv"),
            "--logs", str(ROOT / "target/relax-investigation" / prefix),
            "--seconds", "15",
            "--memory-mb", "1024",
            "--node-limit", "200000",
        ], cwd=ROOT, env=dict(os.environ,
                             POTOROO_FD=str(ROOT / "downward/fast-downward.py"),
                             POTOROO_DOWNWARD=str(ROOT / "downward/builds/release/bin/downward"),
                             POTOROO_PYTHON=str(OUT / "ff_capture_translate.py"),
                             POTOROO_CAPTURE_DIR=str(ROOT / "target/relax-investigation" / f"{prefix}-sas")),
           check=True)
