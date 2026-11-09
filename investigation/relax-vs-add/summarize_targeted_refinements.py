#!/usr/bin/env python3
"""Verify propagation statistics and report matched intervention results."""
import json
import re
import sys
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

for prefix in sys.argv[1:]:
    summary=json.loads((OUT/f'{prefix}-summary.json').read_text())
    manifest=json.loads((OUT/f'{prefix}-manifest.json').read_text())
    records=[]
    for i,(row,run) in enumerate(zip(summary['records'],manifest,strict=True)):
        path=ROOT/'target/relax-investigation'/prefix/f"{i:03d}-{run['label']}.err"
        assert digest(path)==summary['artifact_hashes'][str(path.relative_to(ROOT))]
        matches=re.findall(r'^STATS (.+)$',path.read_text(),re.M);assert len(matches)==1
        stats=json.loads(matches[0])
        forced=stats['threat_forced']
        assert stats['supporter_forced']==0
        assert 0<=forced<=row['generated']
        if run['args'][run['args'].index('-p')+1]=='none':assert forced==0
        records.append(dict(row,threat_forced=forced,generated_excluding_forced=row['generated']-forced,
                            h_evals=stats['h_evals'],pruned=stats['pruned'],max_steps=stats['max_steps']))
    result=dict(suite=prefix,records=records,counts=summary['counts'],
        summary_sha256=digest(OUT/f'{prefix}-summary.json'),script_sha256=digest(Path(__file__)),
        note='Generated counts retain forced refinements; generated_excluding_forced subtracts them. Times of failed tasks are censored. Single runs, not timing distributions.')
    (OUT/f'{prefix}-interventions.json').write_text(json.dumps(result,indent=2)+'\n')
    print(prefix,summary['counts'])
    for row in records:
        if row['solved']:print(row)
