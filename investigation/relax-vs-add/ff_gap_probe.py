#!/usr/bin/env python3
"""Flaw-selection screen on historical FD A*/FF-only tasks; second case held out."""
import argparse
import hashlib
import json
import os
import subprocess
import tarfile
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

DOMAINS = ['thoughtful', 'pipesworld-tankage', 'pipesworld-notankage',
           'sokoban', 'parcprinter', 'pegsol', 'freecell']
CURRENT = ROOT.parent/'potoroo-cluster/results/cluster-memory-2026-11-07-1248'
HISTORICAL = ROOT.parent/'potoroo-cluster/results/cluster-2026-11-04-final-old'
# Only the final unrestricted open-condition criterion changes in these three
# variants. Threat priority and the zero/one-achiever ZLIFO rules stay fixed.
ZPREFIX = '{n}LIFO/{o}0LIFO/{o}1NEW/'
PROFILES = [
    ('add_zlifo', 'ADD/LIFO', 'A', 'ZLIFO', False),
    ('add_zfifo', 'ADD/LIFO', 'A', ZPREFIX+'{o}FIFO/{s}LIFO', False),
    ('add_zlr', 'ADD/LIFO', 'A', ZPREFIX+'{o}LR/{s}LIFO', False),
    ('add_zmc', 'ADD/LIFO', 'A', ZPREFIX+'{o}MC_add/{s}LIFO', False),
    ('ffr_a', 'FFR/LIFO', 'A', 'ZLIFO', False),
    ('ffocr_a', 'FFOCR/LIFO', 'A', 'ZLIFO', False),
    ('add_gpref', 'ADD/FIFO', 'GBFS', 'ZLIFO', True),
    ('ffr_gpref', 'FFR/FIFO', 'GBFS', 'ZLIFO', True),
]

def rows(snapshot):
    return [json.loads(s) for p in sorted((snapshot/'results').glob('*.jsonl'))
            for s in p.read_text().splitlines()]

def prepare(suite):
    prefix = 'ff-gap-'+suite
    assert not (OUT/f'{prefix}.csv').exists(), 'preserve measurements'
    add = {(r['domain'],r['instance']):r for r in rows(CURRENT) if r['config']=='fdr-zlifo-add+lifo'}
    fd = {(r['domain'],r['instance']):r for r in rows(HISTORICAL) if r['config']=='fd-astar-ff'}
    assert len(add)==len(fd)==1260 and add.keys()==fd.keys()
    chosen=[]
    for domain in DOMAINS:
        keys=[k for k in sorted(add) if k[0]==domain and add[k]['status']!='solved' and fd[k]['status']=='solved']
        chosen.append(keys[0 if suite=='screen' else 1])
    cases=[add[k] for k in chosen]
    assert all(r['status']=='memout' and 'Search [' in r['error_tail'] for r in cases)
    frozen=json.loads((OUT/'ff-ffocr-frozen.json').read_text())
    binary=ROOT/frozen['binary']; assert digest(binary)==frozen['binary_sha256']
    assert digest(ROOT/frozen['source_archive'])==frozen['source_archive_sha256']
    with tarfile.open(ROOT/frozen['source_archive']) as archive:
        source_hashes={m.name:hashlib.sha256(archive.extractfile(m).read()).hexdigest()
                       for m in archive if m.isfile()}
    provenance=json.loads((OUT/'ff-memory-screen-provenance.json').read_text())
    provenance.update(suite=suite, domains=DOMAINS, cases=cases,
        historical_fd_cases=[fd[k] for k in chosen],
        cluster_experiment=json.loads((CURRENT/'experiment.json').read_text()),
        cluster_sources={str(p):digest(p) for snapshot in [CURRENT,HISTORICAL]
                         for p in sorted((snapshot/'results').glob('*.jsonl'))},
        frozen=frozen,binary_sha256=frozen['binary_sha256'],source_hashes=source_hashes,
        script=Path(__file__).name,script_sha256=digest(Path(__file__)),
        selection='First lexicographic FD A*/FF solved, historical FDR ADD unsolved task in each of seven user-selected domains. Second such task reserved before screen. Parcprinter p05/p07 have already been examined; they are replication controls, not unseen heldout evidence. Historical runs differ in images and physical-core pinning. Local profiles match binary, inputs and limits.',
        limits=dict(planner_seconds=15,watchdog_seconds=20,address_space_mb=1536,
                    planner_rss_stop_mb=512,node_limit='unlimited'))
    runs=[]
    for row in cases:
        bench=ROOT.parent/'autoscale-unitcost/agile'/row['domain']
        problem=bench/(row['instance']+'.pddl'); domain=bench/('domain-'+row['instance']+'.pddl')
        if not domain.exists(): domain=bench/'domain.pddl'
        assert digest(problem)==row['problem_sha256'] and digest(domain)==row['domain_sha256']
        for label,h,search,flaw,pref in PROFILES:
            runs.append(dict(label=f"{row['domain']}-{row['instance']}-{label}",binary=str(binary),
                revision='2b7bf40+ffocr',domain=str(domain),problem=str(problem),
                args=['--fdr-pocl','-f',flaw,'-h',h,'-s',search,'-w','1','-p','none']
                     +(['--preferred'] if pref else [])))
    (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs,indent=2)+'\n')
    (OUT/f'{prefix}-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    print(prefix,chosen,flush=True)
    return prefix

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--suite',choices=['screen','heldout'],default='screen')
    ap.add_argument('--run',action='store_true');args=ap.parse_args()
    prefix=prepare(args.suite)
    if args.run:
        subprocess.run(['python3',str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),
            str(OUT/f'{prefix}-manifest.json'),'--output',str(OUT/f'{prefix}.csv'),
            '--logs',str(ROOT/'target/relax-investigation'/prefix),
            '--seconds','20','--memory-mb','1536','--rss-mb','512','--node-limit','unlimited'],
            cwd=ROOT,env=dict(os.environ,POTOROO_FD=str(ROOT/'downward/fast-downward.py'),
                POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'),
                POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'),
                POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{prefix}-sas')),check=True)
