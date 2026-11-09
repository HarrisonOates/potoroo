#!/usr/bin/env python3
"""Independently replay printed POCL solutions against the captured SAS tasks."""
import csv
import json
import re
import sys
from pathlib import Path
from preferred_fd_probe import validate, digest
ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
prefix_base = sys.argv[1] if len(sys.argv) > 1 else 'ff-compiled'
records=[]
for prefix in [prefix_base, prefix_base+'-vhpop-domains']:
    rows=list(csv.DictReader((OUT/f'{prefix}.csv').open()))
    folder=ROOT/'target/relax-investigation'/f'{prefix}-sas'
    captures=[json.loads(p.read_text()) for p in sorted(folder.glob('invocation-*.json'))]
    for row,capture in zip(rows,captures,strict=True):
        if row['outcome'] != 'solved': continue
        stem=ROOT/'target/relax-investigation'/prefix/f"{int(row['run']):03d}-{row['label']}"
        raw=stem.with_suffix('.out')
        actions=re.findall(r'^\d+:(\([^\n]+\))$',raw.read_text(),re.MULTILINE)
        assert actions, row['label']
        sas=folder/capture['sas_file']
        # CLI printing trims empty argument lists; SAS names may retain spaces.
        sas_lines=sas.read_text().splitlines()
        names={ ' '.join(sas_lines[i+1].split()):sas_lines[i+1]
                for i,line in enumerate(sas_lines) if line=='begin_operator' }
        assert len(names)==sas_lines.count('begin_operator')
        actions=['('+names[' '.join(a[1:-1].split())]+')' for a in actions]
        normalized=stem.with_suffix('.replay.plan')
        normalized.write_text('\n'.join(actions)+'\n')
        assert digest(sas)==capture['sas_sha256']
        length,cost=validate(sas,normalized)
        assert cost==int(row['plan_cost'])
        records.append(dict(label=row['label'],length=length,cost=cost,artifacts={str(p.relative_to(ROOT)):digest(p) for p in [raw,normalized,sas]}))
result={'validated':len(records),'validator_sha256':digest(Path(__file__)),'sas_validator_sha256':digest(OUT/'preferred_fd_probe.py'),'records':records}
dest=OUT/f'{prefix_base}-plan-validation.json'
if dest.exists(): assert json.loads(dest.read_text())==result
dest.write_text(json.dumps(result,indent=2)+'\n')
print('Independently replayed',len(records),'POCL solutions.')
