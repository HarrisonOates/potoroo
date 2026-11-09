#!/usr/bin/env python3
"""Calibrated-protocol summary vs cluster ADD/FD on the tasks each config finished."""
import json, collections, sys
f = sys.argv[1] if len(sys.argv) > 1 else 'calib.jsonl'
c = json.load(open('cluster-solved.json')); cadd = {tuple(k) for k in c['add']}; cfd = {tuple(k) for k in c['fd']}
d = collections.defaultdict(dict)
for l in open(f):
    r = json.loads(l); d[r['config']][(r['domain'], r['instance'])] = r['status'] == 'solved'
for cfg, v in d.items():
    ks = list(v)
    loc = d['add']
    print(f"{cfg:10} n={len(ks):4} solved={sum(v.values()):4}  local-ADD={sum(loc.get(k,0) for k in ks):4}"
          f"  cluster-ADD={sum(k in cadd for k in ks):4}  cluster-FD={sum(k in cfd for k in ks):4}")
if len(sys.argv) > 2:
    cfg = sys.argv[2]; v = d[cfg]
    dom = collections.defaultdict(lambda: [0, 0, 0, 0])
    for k in v:
        dom[k[0]][0] += d['add'].get(k, 0); dom[k[0]][1] += v[k]; dom[k[0]][2] += k in cadd; dom[k[0]][3] += k in cfd
    print('domain'.ljust(26) + 'locADD'.rjust(8) + cfg[:8].rjust(9) + 'clADD'.rjust(7) + 'clFD'.rjust(6))
    for x, a in sorted(dom.items()):
        if any(a): print(x.ljust(26) + ''.join(str(y).rjust(w) for y, w in zip(a, (8, 9, 7, 6))))
