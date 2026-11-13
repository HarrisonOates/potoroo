#!/usr/bin/env python3
"""Compare solved sets of result files on their common tasks: summarize.py A.jsonl B.jsonl ..."""
import json, sys, collections
data = {}
for f in sys.argv[1:]:
    d = {}
    for l in open(f):
        r = json.loads(l)
        d[(r['domain'], r['instance'])] = r['status'] == 'solved'
    data[f] = d
common = set.intersection(*(set(d) for d in data.values()))
print(f"common tasks: {len(common)}")
doms = sorted({k[0] for k in common})
names = list(data)
print("domain".ljust(26) + "".join(n.split('/')[-1][:10].rjust(11) for n in names))
for dm in doms:
    ks = [k for k in common if k[0] == dm]
    row = [sum(data[n][k] for k in ks) for n in names]
    if any(row):
        print(dm.ljust(26) + "".join(str(x).rjust(11) for x in row))
print("TOTAL".ljust(26) + "".join(str(sum(data[n][k] for k in common)).rjust(11) for n in names))
