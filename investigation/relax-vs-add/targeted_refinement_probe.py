#!/usr/bin/env python3
"""Matched forced-threat and bounded-LIFO interventions on the diagnosed tasks."""
import argparse
import hashlib
import json
import os
import subprocess
import tarfile
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

Z = '{n}LIFO/{o}0LIFO/{o}1NEW/'
PROFILES = [(h.lower()+'_'+policy+('_t' if force else ''), h+'/LIFO', flaw, force)
            for h in ['ADD','FFR']
            for policy,flaw in [('zlifo','ZLIFO'),('b8',Z+'{o}8LIFO/{o}LR/{s}LIFO')]
            for force in [False,True]]
PROFILES += [(h.lower()+'_lr',h+'/LIFO',Z+'{o}LR/{s}LIFO',False) for h in ['ADD','FFR']]

def prepare(suite):
    prefix='ff-target-'+suite
    assert not (OUT/f'{prefix}.csv').exists()
    source='screen' if suite=='screen' else 'heldout'
    provenance=json.loads((OUT/f'ff-gap-{source}-provenance.json').read_text())
    old=json.loads((OUT/f'ff-gap-{source}-manifest.json').read_text())
    frozen=json.loads((OUT/'ff-target-frozen.json').read_text())
    assert digest(ROOT/frozen['binary'])==frozen['binary_sha256']
    assert digest(ROOT/frozen['source_archive'])==frozen['source_archive_sha256']
    with tarfile.open(ROOT/frozen['source_archive']) as archive:
        hashes={m.name:hashlib.sha256(archive.extractfile(m).read()).hexdigest() for m in archive if m.isfile()}
    provenance.update(frozen=frozen,binary_sha256=frozen['binary_sha256'],source_hashes=hashes,
        script=Path(__file__).name,script_sha256=digest(Path(__file__)),suite=suite,
        selection='Mechanism follow-up on previously studied seven-domain panels; NOT unseen heldout data. Fully crossed ranking ADD/FFR x standard ZLIFO/bounded-LIFO8 x forced-threat compression off/on, plus matched plain LR controls. Bounded-LIFO8 preserves ZLIFO prefix, takes newest open with at most8 candidate supports, otherwise LR. Threshold8 fixed before these results. All A/LIFO, weight1, pruningnone or threats alone. Same new frozen binary. First/second panels selected before this round; confirmation profile selection may be adaptive and is recorded separately.',
        limits=dict(planner_seconds=15,watchdog_seconds=20,address_space_mb=1536,planner_rss_stop_mb=512,node_limit='unlimited'))
    runs=[]
    for case in provenance['cases']:
        label=case['domain']+'-'+case['instance']
        base=next(r for r in old if r['label']==label+'-add_zlifo')
        for profile,heuristic,flaw,force in PROFILES:
            runs.append(dict(base,label=label+'-'+profile,binary=str(ROOT/frozen['binary']),revision='2b7bf40+targeted-refinements',args=['--fdr-pocl','-f',flaw,'-h',heuristic,'-s','A','-w','1','-p','threats' if force else 'none']))
    (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs,indent=2)+'\n')
    (OUT/f'{prefix}-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    return prefix

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--suite',choices=['screen','second'],default='screen');ap.add_argument('--run',action='store_true');args=ap.parse_args()
    prefix=prepare(args.suite)
    if args.run:
        env=dict(os.environ,POTOROO_FDR_DIAGNOSTICS='0',POTOROO_FD=str(ROOT/'downward/fast-downward.py'),POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'),POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'),POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{prefix}-sas'))
        subprocess.run(['python3',str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),str(OUT/f'{prefix}-manifest.json'),'--output',str(OUT/f'{prefix}.csv'),'--logs',str(ROOT/'target/relax-investigation'/prefix),'--seconds','20','--memory-mb','1536','--rss-mb','512','--node-limit','unlimited'],env=env,check=True)
        subprocess.run(['python3',str(OUT/'summarize_memory.py'),prefix],check=True)
