#!/usr/bin/env python3
"""Confirm greedy/preferred ADD and FFR on the preselected second instances."""
import json
import os
import subprocess
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

if __name__ == '__main__':
    prefix='ff-memory-greedy-confirm'
    assert not (OUT/f'{prefix}.csv').exists()
    provenance=json.loads((OUT/'ff-memory-heldout-provenance.json').read_text())
    binary=ROOT/provenance['frozen']['binary'];assert digest(binary)==provenance['binary_sha256']
    original=json.loads((OUT/'ff-memory-heldout-manifest.json').read_text())
    runs=[]
    for run in original[::6]:
        case=run['label'].removesuffix('-add')
        for h in ['ADD','FFR']:
            for pref in [False,True]:
                label=h.lower()+('_pref' if pref else '')
                runs.append(dict(run,binary=str(binary),label=case+'-'+label,args=['--fdr-pocl','-f','ZLIFO','-h',h+'/FIFO','-s','GBFS','-w','1','-p','none']+(['--preferred'] if pref else [])))
    provenance.update(script=Path(__file__).name,script_sha256=digest(Path(__file__)),selection='Adaptive confirmation after the greedy screen: retain ADD and FFR with preferences off/on, drop plain FF and FFOC. Evaluate all eight second eligible instances selected before the original screen outcomes; no domain dropped based on results. The unused eight-profile greedy-heldout manifest remains preparation only.',parent_provenance_sha256=digest(OUT/'ff-memory-heldout-provenance.json'))
    (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs,indent=2)+'\n')
    (OUT/f'{prefix}-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    subprocess.run(['python3',str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),str(OUT/f'{prefix}-manifest.json'),'--output',str(OUT/f'{prefix}.csv'),'--logs',str(ROOT/'target/relax-investigation'/prefix),'--seconds','20','--memory-mb','1536','--rss-mb','512','--node-limit','unlimited'],cwd=ROOT,env=dict(os.environ,POTOROO_FD=str(ROOT/'downward/fast-downward.py'),POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'),POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'),POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{prefix}-sas')),check=True)
