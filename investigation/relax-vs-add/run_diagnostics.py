#!/usr/bin/env python3
"""Reproduce identical-plan timings; run from the Potoroo repository root.

Requires the sibling downward and autoscale-unitcost checkouts. Compilation
finishes before timings start, and all measurement processes run sequentially.
"""
import os
from pathlib import Path
import subprocess

root = Path.cwd()
out = root / "investigation/relax-vs-add"
scratch = root / "target/relax-investigation/sas"
scratch.mkdir(parents=True, exist_ok=True)
bench = root.parent / "autoscale-unitcost/agile"
fd = root.parent / "downward/fast-downward.py"
env = dict(os.environ, POTOROO_FD=str(fd))
subprocess.run(["cargo", "test", "--release", "--lib", "--no-run"], check=True, env=env)
subprocess.run(["cargo", "test", "--release", "--test", "relax_diagnostic", "--no-run"], check=True, env=env)
for domain in ("gripper", "miconic"):
    sas = scratch / (domain + "-p01.sas")
    with (scratch / (domain + "-p01.log")).open("w") as stream:
        subprocess.run(["python3", str(fd), "--sas-file", str(sas), "--translate",
                        str(bench / domain / "domain.pddl"), str(bench / domain / "p01.pddl")],
                       stdout=stream, stderr=subprocess.STDOUT, check=True, timeout=60)
    with (out / ("fdr-" + domain + "-diagnostic.txt")).open("w") as stream:
        subprocess.run(["cargo", "test", "--release", "--lib", "compare_on_identical_partial_plans",
                        "--", "--ignored", "--nocapture"],
                       env=dict(env, DIAG_SAS=str(sas)), stdout=stream, stderr=subprocess.STDOUT,
                       check=True, timeout=60)

for mode, domain, problem, nodes in [
    ("lifted", "miconic", "p01", 6000),
    ("ground", "miconic", "p01", 6000),
    ("lifted", "miconic", "p29", 1),
]:
    with (out / f"{mode}-{domain}-{problem}-diagnostic.txt").open("w") as stream:
        subprocess.run(["prlimit", "--as=1073741824", "--core=0", "cargo", "test", "--release",
                        "--test", "relax_diagnostic", "--", "--ignored", "--nocapture"],
                       env=dict(env, DIAG_DOMAIN=str(bench / domain / "domain.pddl"),
                                DIAG_PROBLEM=str(bench / domain / (problem + ".pddl")),
                                DIAG_GROUND=str(int(mode == "ground")), DIAG_NODES=str(nodes)),
                       stdout=stream, stderr=subprocess.STDOUT, check=True, timeout=60)
    print(mode, domain, problem, "complete", flush=True)
