#!/usr/bin/env python3
"""Apply promising flaw control to FFR, then confirm on reserved second cases."""
import json
import os
import subprocess
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

def run(suite,profiles,prefix):
    assert not (OUT/f'{prefix}.csv').exists()
    source=json.loads((OUT/f'ff-gap-{suite}-manifest.json').read_text())
    provenance=json.loads((OUT/f'ff-gap-{suite}-provenance.json').read_text())
    chosen=[]
    for case in provenance['cases']:
        label=f"{case['domain']}-{case['instance']}"
        base={r['label'].removeprefix(label+'-'):r for r in source if r['label'].startswith(label+'-')}
        for profile in profiles:
            if profile=='ffr_zlr':
                r=base['add_zlr'];args=list(r['args']);args[args.index('-h')+1]='FFR/LIFO'
                r=dict(r,label=label+'-ffr_zlr',args=args)
            else:r=base[profile]
            chosen.append(r)
    provenance.update(script=Path(__file__).name,script_sha256=digest(Path(__file__)),
        selection=f'Adaptive follow-up using {suite} cases selected before screening. Profiles: {profiles}. FFR with the LR open tier tests whether the Pipesworld ADD/LR gain transfers to FF reuse. Confirmation always retains ADD/ZLIFO, ADD/LR, FFR/ZLIFO and FFR/LR, plus any other solving screen profiles (and matched ADD greedy if FFR greedy succeeds). Parcprinter is previously seen replication.',
        screen_summary_sha256=digest(OUT/'ff-gap-screen-summary.json'))
    (OUT/f'{prefix}-manifest.json').write_text(json.dumps(chosen,indent=2)+'\n')
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

if __name__=='__main__':
    summary=json.loads((OUT/'ff-gap-screen-summary.json').read_text())
    profiles=['add_zlifo','add_zlr','ffr_a','ffr_zlr']
    for r in summary['records']:
        if r['solved'] and r['profile'] not in profiles:profiles.append(r['profile'])
    if 'ffr_gpref' in profiles and 'add_gpref' not in profiles:profiles.append('add_gpref')
    run('screen',['ffr_zlr'],'ff-gap-reuse-lr')
    run('heldout',profiles,'ff-gap-confirm')
