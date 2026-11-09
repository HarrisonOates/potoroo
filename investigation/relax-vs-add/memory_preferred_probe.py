#!/usr/bin/env python3
"""Matched preferred/refinement screen on historical ADD search-memory failures."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tarfile

ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
SNAPSHOT=ROOT.parent/'potoroo-cluster/results/cluster-memory-2026-11-07-0836'
DOMAINS=['parcprinter','driverlog','zenotravel','logistics','rovers','elevators','transport','blocksworld']
PROFILES=[(label+suffix,h,pref) for label,h in [('add','ADD'),('ffoc','FFOC'),('ffr','FFR')] for suffix,pref in [('',False),('_pref',True)]]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def prepare(suite):
    prefix='ff-memory-'+suite
    assert not (OUT/f'{prefix}.csv').exists(), 'preserve existing measurements'
    rows=[json.loads(s) for p in sorted((SNAPSHOT/'results').glob('*.jsonl')) for s in p.read_text().splitlines()]
    chosen=[]
    for domain in DOMAINS:
        eligible=sorted([r for r in rows if r['domain']==domain and r['config']=='fdr-zlifo-add+lifo' and r['status']=='memout' and 'Search [' in r['error_tail']],key=lambda r:r['instance'])
        assert len(eligible)>=2,domain
        chosen.append(eligible[0 if suite=='screen' else 1])
    sources=[ROOT/'Cargo.toml',ROOT/'Cargo.lock',*sorted((ROOT/'src').rglob('*.rs'))]
    frozen=json.loads((OUT/'ff-compiled-v2-frozen.json').read_text())
    assert digest(ROOT/'target/release/potoroo')==frozen['binary_sha256']
    assert digest(ROOT/frozen['source_archive'])==frozen['source_archive_sha256']
    with tarfile.open(ROOT/frozen['source_archive']) as t:
        for p in sources:assert t.extractfile(str(p.relative_to(ROOT))).read()==p.read_bytes(),str(p)
    runs=[];evidence=[]
    for row in chosen:
        bench=ROOT.parent/'autoscale-unitcost/agile'/row['domain']
        problem=bench/(row['instance']+'.pddl');domain=bench/('domain-'+row['instance']+'.pddl')
        if not domain.exists():domain=bench/'domain.pddl'
        assert digest(domain)==row['domain_sha256'];assert digest(problem)==row['problem_sha256']
        evidence.append(row)
        for label,h,pref in PROFILES:
            runs.append(dict(label=f"{row['domain']}-{row['instance']}-{label}",binary=str(ROOT/'target/release/potoroo'),revision='2b7bf40+ff-compiled-v2',domain=str(domain),problem=str(problem),args=['--fdr-pocl','-f','ZLIFO','-h',h+'/LIFO','-s','A','-w','1','-p','none']+(['--preferred'] if pref else [])))
    fd=(ROOT/'downward').resolve();translator=fd/'builds/release/bin/fast_downward/translate'
    provenance=dict(selection='First lexicographic historical ADD memout with explicit search progress in each of eight preselected classical domains; heldout is second, selected before screen outcomes.',domains=DOMAINS,suite=suite,cases=evidence,cluster_experiment=json.loads((SNAPSHOT/'experiment.json').read_text()),cluster_sources={str(p):digest(p) for p in sorted((SNAPSHOT/'results').glob('*.jsonl'))},frozen=frozen,source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),source_hashes={str(p.relative_to(ROOT)):digest(p) for p in sources},binary_sha256=digest(ROOT/'target/release/potoroo'),script_sha256=digest(Path(__file__)),harness_sha256=digest(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),wrapper_sha256=digest(OUT/'ff_capture_translate.py'),translator_root=str(translator),translator_hashes={str(p.relative_to(translator)):digest(p) for p in sorted(translator.rglob('*.py'))},limits=dict(planner_seconds=15,watchdog_seconds=20,address_space_mb=1536,planner_rss_stop_mb=512,node_limit='unlimited'))
    (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs,indent=2)+'\n')
    (OUT/f'{prefix}-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    print('Selected',[(r['domain'],r['instance']) for r in chosen],flush=True)
    return prefix

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--suite',choices=['screen','heldout'],default='screen');ap.add_argument('--run',action='store_true');args=ap.parse_args();prefix=prepare(args.suite)
    if args.run:
        subprocess.run(['python3',str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),str(OUT/f'{prefix}-manifest.json'),'--output',str(OUT/f'{prefix}.csv'),'--logs',str(ROOT/'target/relax-investigation'/prefix),'--seconds','20','--memory-mb','1536','--rss-mb','512','--node-limit','unlimited'],cwd=ROOT,env=dict(os.environ,POTOROO_FD=str(ROOT/'downward/fast-downward.py'),POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'),POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'),POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{prefix}-sas')),check=True)
