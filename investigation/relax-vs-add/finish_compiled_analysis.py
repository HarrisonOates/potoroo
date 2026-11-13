#!/usr/bin/env python3
"""Verify corrected and tie batches, then report matched outcomes."""
from pathlib import Path
import subprocess
import json
from collections import Counter
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[1]
for script in ['summarize_compiled_v2.py','summarize_compiled_ties.py']:
    subprocess.run(['python3',str(OUT/script)],check=True,stdout=subprocess.DEVNULL)
for prefix in ['ff-compiled-v2','ff-ties']:
    subprocess.run(['python3',str(OUT/'validate_compiled_plans.py'),prefix],check=True)
x=json.loads((OUT/'ff-compiled-v2-summary.json').read_text())
y=json.loads((OUT/'ff-corrected-summary.json').read_text())
old={(r['case'],r['profile']):r for r in y['records']}
checks=[]
for r in x['records']:
    k=(r['case'],r['profile'])
    if k not in old:continue
    o=old[k]
    checks.append(dict(case=r['case'],profile=r['profile'],outcome=r['outcome'],outcome_equal=r['outcome']==o['outcome'],generated_equal=r['generated']==o['generated'],cost_equal=r['cost']==o['cost']))
result=dict(checked=len(checks),all_outcomes_equal=all(r['outcome_equal'] for r in checks),all_solved_and_node_limited_counts_and_costs_equal=all(r['generated_equal'] and r['cost_equal'] for r in checks if r['outcome'] in ['solved','limit']),records=checks)
(OUT/'ff-compiled-v2-baseline-check.json').write_text(json.dumps(result,indent=2)+'\n')
print('Baseline checks:',{k:v for k,v in result.items() if k!='records'})
for prefix in ['ff-compiled-v2','ff-ties']:
    rows=json.loads((OUT/f'{prefix}-summary.json').read_text())['records']
    print(prefix,'coverage',dict(Counter(r['profile'] for r in rows if r['solved'])))
    for r in rows:
        if r['profile'] not in ['add','ff','clff','ffoc_w5','ffoc_gbfs']:print(r['case'],r['profile'],r['outcome'],r['generated'],r['cost'],r['wall_ms'])
