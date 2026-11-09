#!/usr/bin/env python3
"""Test whether short FF stages add coverage to a matched ADD restart policy."""
import argparse
import json
import os
import subprocess
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, SNAPSHOT, digest

if __name__ == '__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',action='store_true');args=ap.parse_args()
    prefix='ff-memory-portfolio'
    assert not (OUT/f'{prefix}.csv').exists()
    provenance=json.loads((OUT/'ff-memory-screen-provenance.json').read_text())
    cases=list(provenance['cases'])+json.loads((OUT/'ff-memory-heldout-provenance.json').read_text())['cases']
    old=[]
    for name in ['ff-compiled-v2','ff-compiled-v2-vhpop-domains']:
        old+=json.loads((OUT/f'{name}-provenance.json').read_text())['cases']
    controls={(r['domain'],r['instance']) for r in old if r['domain'] not in {'parcprinter','driverlog'}}
    assert len(controls)==8
    rows=[json.loads(s) for p in sorted((SNAPSHOT/'results').glob('*.jsonl')) for s in p.read_text().splitlines()]
    cases+=sorted([r for r in rows if (r['domain'],r['instance']) in controls and r['config']=='fdr-zlifo-add+lifo'],key=lambda r:(r['domain'],r['instance']))
    assert len(cases)==24
    binary=ROOT/provenance['frozen']['binary'];assert digest(binary)==provenance['binary_sha256']
    profiles=[('add_portfolio',['ADD/LIFO@A=1','ADD/FIFO@GBFS']),('ff_portfolio',['ADD/LIFO@A=1','FFR/LIFO@A=1','FFR/FIFO@GBFS=2','ADD/FIFO@GBFS'])]
    runs=[]
    for row in cases:
        bench=ROOT.parent/'autoscale-unitcost/agile'/row['domain']
        problem=bench/(row['instance']+'.pddl');domain=bench/('domain-'+row['instance']+'.pddl')
        if not domain.exists():domain=bench/'domain.pddl'
        assert digest(domain)==row['domain_sha256'] and digest(problem)==row['problem_sha256']
        options=([('add_plain',[])] if (row['domain'],row['instance']) in controls else [])+profiles
        for label,stages in options:
            flags=['--fdr-pocl','-f','ZLIFO','-h','ADD/LIFO','-s','A','-w','1','-p','none']
            if stages:
                flags+=['--preferred']
                for stage in stages:flags+=['--stage',stage]
            runs.append(dict(label=f"{row['domain']}-{row['instance']}-{label}",binary=str(binary),revision='2b7bf40+ff-compiled-v2',domain=str(domain),problem=str(problem),args=flags))
    provenance.update(cases=cases,suite='portfolio',script=Path(__file__).name,script_sha256=digest(Path(__file__)),require_search_memout=False,selection='Adaptive fixed restart schedules from component screens, not a heldout portfolio evaluation. All16 previously selected search-memory failures plus all8 earlier ADD-success cases outside Parcprinter/Driverlog. Both portfolios start with preferred ADD A/LIFO for1s and end with preferred ADD GBFS/FIFO for remaining time; FF portfolio inserts FFR A/LIFO1s and FFR GBFS/FIFO2s. Same total15s and512MiB RSS. Plain ADD controls on8 earlier successes supplement the existing16 matched memory baselines. No per-domain schedule selection.',regression_controls=sorted([list(c) for c in controls]))
    (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs,indent=2)+'\n')
    (OUT/f'{prefix}-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    if args.run:
        subprocess.run(['python3',str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),str(OUT/f'{prefix}-manifest.json'),'--output',str(OUT/f'{prefix}.csv'),'--logs',str(ROOT/'target/relax-investigation'/prefix),'--seconds','20','--memory-mb','1536','--rss-mb','512','--node-limit','unlimited'],cwd=ROOT,env=dict(os.environ,POTOROO_FD=str(ROOT/'downward/fast-downward.py'),POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'),POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'),POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{prefix}-sas')),check=True)
