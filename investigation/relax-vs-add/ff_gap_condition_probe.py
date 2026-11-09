#!/usr/bin/env python3
"""Attribute selected flaws to FDR facts at a fixed generated-node budget."""
import json
import os
import subprocess
import tarfile
import hashlib
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

if __name__=='__main__':
    frozen=json.loads((OUT/'ff-gap-condition-frozen.json').read_text())
    assert digest(ROOT/frozen['binary'])==frozen['binary_sha256']
    assert digest(ROOT/frozen['source_archive'])==frozen['source_archive_sha256']
    with tarfile.open(ROOT/frozen['source_archive']) as archive:
        sources={m.name:hashlib.sha256(archive.extractfile(m).read()).hexdigest() for m in archive if m.isfile()}
    parent=json.loads((OUT/'ff-gap-screen-provenance.json').read_text())
    selected=[r for r in json.loads((OUT/'ff-gap-screen-manifest.json').read_text())
              if r['label'].endswith(('-add_zlifo','-add_zlr','-ffr_a'))]
    for mode in ['on']:
        prefix='ff-gap-condition'
        assert not (OUT/f'{prefix}.csv').exists()
        runs=[dict(r,binary=str(ROOT/frozen['binary']),revision='2b7bf40+ff-conditions') for r in selected]
        provenance=dict(parent,frozen=frozen,binary_sha256=frozen['binary_sha256'],source_hashes=sources,
            script=Path(__file__).name,script_sha256=digest(Path(__file__)),
            selection='Diagnostic follow-up on seven screen cases: ADD/ZLIFO, ADD with the final open tier set to LR, and FFR/ZLIFO, all A/LIFO. Per-fact attribution follow-up with diagnostics enabled, 500000 generated-node budget; compare recorded outcomes and counters with frozen v2 checks, not complete traces or runtime.',
            diagnostics=mode,limits=dict(planner_seconds=15,watchdog_seconds=20,address_space_mb=1536,
                                        planner_rss_stop_mb=512,node_limit='500000'))
        (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs,indent=2)+'\n')
        (OUT/f'{prefix}-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
        env=dict(os.environ,POTOROO_FDR_DIAGNOSTICS='1' if mode=='on' else '0',
            POTOROO_FD=str(ROOT/'downward/fast-downward.py'),
            POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'),
            POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'),
            POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{prefix}-sas'))
        subprocess.run(['python3',str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),
            str(OUT/f'{prefix}-manifest.json'),'--output',str(OUT/f'{prefix}.csv'),
            '--logs',str(ROOT/'target/relax-investigation'/prefix),'--seconds','20',
            '--memory-mb','1536','--rss-mb','512','--node-limit','500000'],env=env,check=True)
        subprocess.run(['python3',str(OUT/'summarize_memory.py'),prefix],check=True)
