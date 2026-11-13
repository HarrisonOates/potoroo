#!/usr/bin/env python3
"""Quick side-by-side: spot.py SECONDS TASKS(comma list) 'name::flags' ...  (env passes through)."""
import os, re, shlex, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run

secs = int(sys.argv[1])
tasks = [tuple(t.split('/')) for t in sys.argv[2].split(',')]
configs = [c.split('::') for c in sys.argv[3:]]

def one(task, cfg):
    name, flags = cfg[0], cfg[1]
    env = dict(os.environ, POTOROO_FD=run.FD)
    if len(cfg) > 2:
        env.update(dict(kv.split('=') for kv in cfg[2].split()))
    d, i = task
    cmd = ["timeout", str(secs), "prlimit", "--as=2000000000", run.POTOROO] + shlex.split(flags) + \
          ["-v", run.domain_file(d, i), os.path.join(run.BENCH, d, i + ".pddl")]
    out = subprocess.run(cmd, capture_output=True, text=True, env=env, errors="replace")
    o = out.stdout + out.stderr
    m = re.search(r"solved in ([0-9.]+)s", o)
    g = re.findall(r"generated (\d+)", o)
    return f"{'S '+m.group(1)+'s' if m else '-'} {g[-1] if g else '?'}"

with ThreadPoolExecutor(int(os.environ.get("SPOT_J", "4"))) as ex:
    futs = {(t, c[0]): ex.submit(one, t, c) for t in tasks for c in configs}
    print("task".ljust(28) + "".join(c[0][:22].rjust(24) for c in configs))
    for t in tasks:
        print(f"{t[0]}/{t[1]}".ljust(28) + "".join(futs[(t, c[0])].result().rjust(24) for c in configs))
