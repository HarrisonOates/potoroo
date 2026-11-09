#!/usr/bin/env python3
"""Transparent interpreter wrapper preserving the actual benchmark SAS output."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

started = time.time_ns()
result = subprocess.run([sys.executable, *sys.argv[1:]])
args = sys.argv[1:]
if result.returncode == 0 and args[:2] == ["-m", "fast_downward.translate"]:
    sas = Path(args[args.index("--sas-file") + 1])
    domain, problem = Path(args[2]), Path(args[3])
    digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    output = Path(os.environ["POTOROO_CAPTURE_DIR"])
    output.mkdir(parents=True, exist_ok=True)
    sas_hash = digest(sas)
    saved = output / f"{sas_hash}.sas"
    if not saved.exists():
        saved.write_bytes(sas.read_bytes())
    record = dict(started_ns=started, finished_ns=time.time_ns(),
                  domain_sha256=digest(domain), problem_sha256=digest(problem),
                  sas_sha256=sas_hash, sas_file=saved.name,
                  python=sys.executable, python_version=sys.version,
                  pythonpath=os.environ.get("PYTHONPATH"),
                  pythonhashseed=os.environ.get("PYTHONHASHSEED"))
    (output / f"invocation-{started}.json").write_text(json.dumps(record, indent=2) + "\n")
sys.exit(result.returncode)
