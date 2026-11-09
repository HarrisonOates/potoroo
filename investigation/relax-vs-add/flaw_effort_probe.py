#!/usr/bin/env python3
"""Corrected causal-link effort: matched MW policies and effort tie breakers."""
import hashlib
import json
import os
import subprocess
import tarfile
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

PROFILES = [('ffr_mw_loc', 'FFR/LIFO', 'MW-Loc'),
            ('ffr_mw_loc_conf', 'FFR/LIFO', 'MW-Loc-Conf'),
            ('ffr_work_zlifo', 'FFR/ADD_WORK/LIFO', 'ZLIFO'),
            ('ffr_work_mw_loc', 'FFR/ADD_WORK/LIFO', 'MW-Loc'),
            ('add_work_mw_loc', 'ADD/ADD_WORK/LIFO', 'MW-Loc')]

if __name__ == '__main__':
    prefix = 'ff-types-effort'
    assert not (OUT/f'{prefix}.csv').exists()
    parent = json.loads((OUT/'ff-types-screen-provenance.json').read_text())
    old = json.loads((OUT/'ff-types-screen-manifest.json').read_text())
    frozen = json.loads((OUT/'ff-types-diagnostic-frozen.json').read_text())
    assert digest(ROOT/frozen['binary']) == frozen['binary_sha256']
    assert digest(ROOT/frozen['source_archive']) == frozen['source_archive_sha256']
    with tarfile.open(ROOT/frozen['source_archive']) as archive:
        hashes = {m.name:hashlib.sha256(archive.extractfile(m).read()).hexdigest()
                  for m in archive if m.isfile()}
    parent.update(frozen=frozen, binary_sha256=frozen['binary_sha256'], source_hashes=hashes,
        script=Path(__file__).name, script_sha256=digest(Path(__file__)), suite='effort',
        selection=('Five profiles fixed before corrected-effort results, on same13 cases. '
                   'FFR/MW-Loc and MW-Loc-Conf have old-code matches in ff-types-screen. '
                   'Other profiles combine flaw selection/effort tie breakers and do not '
                   'alone isolate the correction. ADD/ADD_WORK with MW-Loc tests whether '
                   'benefits require FFR. Same limits and serial diagnostics-off protocol. '
                   'Corrected INIT/reuse effort1, cost-first propagation, finite saturation. '
                   'Cases previously studied, no unseen heldout claim.'), profiles=PROFILES)
    runs=[]
    for case in parent['cases']:
        label=case['domain']+'-'+case['instance']
        base=next(r for r in old if r['label'].startswith(label+'-'))
        for profile,heuristic,policy in PROFILES:
            runs.append(dict(base,label=label+'-'+profile,binary=str(ROOT/frozen['binary']),
                revision='2b7bf40+native-effort-correction',
                args=['--fdr-pocl','-f',policy,'-h',heuristic,'-s','A','-w','1','-p','none']))
    (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs,indent=2)+'\n')
    (OUT/f'{prefix}-provenance.json').write_text(json.dumps(parent,indent=2)+'\n')
    env=dict(os.environ,POTOROO_FDR_DIAGNOSTICS='0',POTOROO_FDR_FLAW_TYPES='0',
        POTOROO_FD=str(ROOT/'downward/fast-downward.py'),
        POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'),
        POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'),
        POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{prefix}-sas'))
    subprocess.run(['python3',str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),
        str(OUT/f'{prefix}-manifest.json'),'--output',str(OUT/f'{prefix}.csv'),
        '--logs',str(ROOT/'target/relax-investigation'/prefix),'--seconds','20',
        '--memory-mb','1536','--rss-mb','512','--node-limit','unlimited'],env=env,check=True)
    subprocess.run(['python3',str(OUT/'summarize_memory.py'),prefix],check=True)
