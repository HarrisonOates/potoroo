#!/usr/bin/env python3
"""Matched ADD versus occurrence-sensitive FF with existing-action reuse."""
import argparse
import json
import os
import subprocess
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, SNAPSHOT, digest

if __name__ == '__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--suite',choices=['screen','heldout'],default='screen')
    ap.add_argument('--run',action='store_true')
    args=ap.parse_args();prefix='ff-ffocr-'+args.suite
    assert not (OUT/f'{prefix}.csv').exists()
    provenance=json.loads((OUT/f'ff-memory-{args.suite}-provenance.json').read_text())
    cases=list(provenance['cases'])
    if args.suite=='screen':
        old=json.loads((OUT/'ff-compiled-v2-provenance.json').read_text())['cases']
        controls={(r['domain'],r['instance']) for r in old if not r['control']}
        assert len(controls)==6
        rows=[json.loads(s) for p in sorted((SNAPSHOT/'results').glob('*.jsonl')) for s in p.read_text().splitlines()]
        cases += sorted([r for r in rows if (r['domain'],r['instance']) in controls and r['config']=='fdr-zlifo-add+lifo'],key=lambda r:(r['domain'],r['instance']))
    frozen=json.loads((OUT/'ff-ffocr-frozen.json').read_text())
    binary=ROOT/frozen['binary'];assert digest(binary)==frozen['binary_sha256']
    sources=[ROOT/'Cargo.toml',ROOT/'Cargo.lock',*sorted((ROOT/'src').rglob('*.rs'))]
    provenance.update(cases=cases, suite=args.suite, script=Path(__file__).name, script_sha256=digest(Path(__file__)), frozen=frozen, binary_sha256=frozen['binary_sha256'],source_hashes={str(p.relative_to(ROOT)):digest(p) for p in sources},require_search_memout=False, selection='Adaptive FFOCR method: per-occurrence FF support demand plus order-compatible frontier reuse. Screen uses the same eight preselected historical ADD memory failures plus the six earlier ADD-only targets as regression controls. Heldout uses the previously selected second memory case per domain. Matched ADD and FFOCR off/on preference profiles, same new frozen binary.')
    runs=[]
    for row in cases:
        bench=ROOT.parent/'autoscale-unitcost/agile'/row['domain']
        problem=bench/(row['instance']+'.pddl');domain=bench/('domain-'+row['instance']+'.pddl')
        if not domain.exists():domain=bench/'domain.pddl'
        assert digest(domain)==row['domain_sha256'] and digest(problem)==row['problem_sha256']
        for label,h,pref in [('add','ADD',False),('ffocr','FFOCR',False),('ffocr_pref','FFOCR',True)]:
            runs.append(dict(label=f"{row['domain']}-{row['instance']}-{label}",binary=str(binary),revision='2b7bf40+ffocr',domain=str(domain),problem=str(problem),args=['--fdr-pocl','-f','ZLIFO','-h',h+'/LIFO','-s','A','-w','1','-p','none']+(['--preferred'] if pref else [])))
    (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs,indent=2)+'\n')
    (OUT/f'{prefix}-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    if args.run:
        subprocess.run(['python3',str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),str(OUT/f'{prefix}-manifest.json'),'--output',str(OUT/f'{prefix}.csv'),'--logs',str(ROOT/'target/relax-investigation'/prefix),'--seconds','20','--memory-mb','1536','--rss-mb','512','--node-limit','unlimited'],cwd=ROOT,env=dict(os.environ,POTOROO_FD=str(ROOT/'downward/fast-downward.py'),POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'),POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'),POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{prefix}-sas')),check=True)
