#!/usr/bin/env python3
"""Existing invariant/supporter pruning on the seven FD-gap screen cases."""
import json
import os
import subprocess
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

if __name__=='__main__':
    prefix='ff-gap-pruning'
    assert not (OUT/f'{prefix}.csv').exists()
    provenance=json.loads((OUT/'ff-gap-screen-provenance.json').read_text())
    manifest=json.loads((OUT/'ff-gap-screen-manifest.json').read_text())
    runs=[]
    for r in manifest:
        if not r['label'].endswith(('-add_zlifo','-ffr_a')):continue
        args=list(r['args']);args[args.index('-p')+1]='h2,supporters,edelete'
        runs.append(dict(r,label=r['label']+'_pruned',args=args))
    provenance.update(script=Path(__file__).name,script_sha256=digest(Path(__file__)),
        selection='Seven user-targeted screen cases. Existing bounded h2 preprocessing, supporter propagation and e-deletion applied jointly to ADD and FFR A/LIFO; compare with the corresponding unpruned screen rows. This tests a package, not the individual contribution of each rule.')
    (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs,indent=2)+'\n')
    (OUT/f'{prefix}-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    subprocess.run(['python3',str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),
        str(OUT/f'{prefix}-manifest.json'),'--output',str(OUT/f'{prefix}.csv'),
        '--logs',str(ROOT/'target/relax-investigation'/prefix),'--seconds','20',
        '--memory-mb','1536','--rss-mb','512','--node-limit','unlimited'],
        env=dict(os.environ,POTOROO_FD=str(ROOT/'downward/fast-downward.py'),
            POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'),
            POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'),
            POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{prefix}-sas')),check=True)
    subprocess.run(['python3',str(OUT/'summarize_memory.py'),prefix],check=True)
