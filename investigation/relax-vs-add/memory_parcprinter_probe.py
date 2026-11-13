#!/usr/bin/env python3
"""Exhaust all nine historical ADD search-memory failures in Parcprinter."""
import json
import os
import subprocess
import tarfile
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, SNAPSHOT, digest

PREFIX = 'ff-memory-parcprinter'
if __name__ == '__main__':
    assert not (OUT/f'{PREFIX}.csv').exists()
    provenance = json.loads((OUT/'ff-memory-screen-provenance.json').read_text())
    frozen = provenance['frozen']
    binary = ROOT/frozen['binary']
    assert digest(binary) == provenance['binary_sha256']
    assert digest(ROOT/frozen['source_archive']) == frozen['source_archive_sha256']
    with tarfile.open(ROOT/frozen['source_archive']) as archive:
        import hashlib
        for name, value in provenance['source_hashes'].items():
            assert hashlib.sha256(archive.extractfile(name).read()).hexdigest() == value
    rows = [json.loads(s) for p in sorted((SNAPSHOT/'results').glob('*.jsonl')) for s in p.read_text().splitlines()]
    cases = sorted([r for r in rows if r['domain']=='parcprinter' and r['config']=='fdr-zlifo-add+lifo' and r['status']=='memout' and 'Search [' in r['error_tail']], key=lambda r:r['instance'])
    assert len(cases) == 9
    runs = []
    for row in cases:
        bench = ROOT.parent/'autoscale-unitcost/agile/parcprinter'
        problem = bench/(row['instance']+'.pddl')
        domain = bench/('domain-'+row['instance']+'.pddl')
        if not domain.exists(): domain=bench/'domain.pddl'
        assert digest(problem)==row['problem_sha256'] and digest(domain)==row['domain_sha256']
        for h in ['ADD', 'FF', 'ADDR', 'FFR']:
            runs.append(dict(label=f"parcprinter-{row['instance']}-{h.lower()}", binary=str(binary), revision='2b7bf40+ff-compiled-v2', domain=str(domain), problem=str(problem), args=['--fdr-pocl','-f','ZLIFO','-h',h+'/LIFO','-s','A','-w','1','-p','none']))
    provenance.update(cases=cases, domains=['parcprinter'], suite='parcprinter', script=Path(__file__).name, script_sha256=digest(Path(__file__)), selection='Adaptive domain follow-up after FFR solved p05 and prespecified heldout p07. Includes every historical ADD search-phase memory failure in Parcprinter, not a heldout domain evaluation. ADD and FF control for joint extraction; ADDR is a separate more optimistic reuse control (seeds effects recursively, unlike frontier-only FFR).', parent_provenance_sha256=digest(OUT/'ff-memory-screen-provenance.json'))
    (OUT/f'{PREFIX}-manifest.json').write_text(json.dumps(runs,indent=2)+'\n')
    (OUT/f'{PREFIX}-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    subprocess.run(['python3',str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),str(OUT/f'{PREFIX}-manifest.json'),'--output',str(OUT/f'{PREFIX}.csv'),'--logs',str(ROOT/'target/relax-investigation'/PREFIX),'--seconds','20','--memory-mb','1536','--rss-mb','512','--node-limit','unlimited'],cwd=ROOT,env=dict(os.environ,POTOROO_FD=str(ROOT/'downward/fast-downward.py'),POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'),POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'),POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{PREFIX}-sas')),check=True)
