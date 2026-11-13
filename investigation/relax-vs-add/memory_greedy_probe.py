#!/usr/bin/env python3
"""Matched greedy/preferred follow-up on the preselected ADD memory cases."""
import argparse
import json
import os
import subprocess
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

def prepare(suite):
    prefix = 'ff-memory-greedy-' + suite
    assert not (OUT / f'{prefix}.csv').exists()
    base = 'ff-memory-' + suite
    provenance = json.loads((OUT / f'{base}-provenance.json').read_text())
    assert digest(ROOT / 'target/release/potoroo') == provenance['binary_sha256']
    for name, value in provenance['source_hashes'].items(): assert digest(ROOT / name) == value
    original = json.loads((OUT / f'{base}-manifest.json').read_text())
    runs = []
    for run in original[::6]:
        case = run['label'].removesuffix('-add')
        for h in ['ADD', 'FF', 'FFR', 'FFOC']:
            for pref in [False, True]:
                label = h.lower() + ('_pref' if pref else '')
                runs.append(dict(run, label=case+'-'+label, args=['--fdr-pocl', '-f', 'ZLIFO', '-h', h+'/FIFO', '-s', 'GBFS', '-w', '1', '-p', 'none']+(['--preferred'] if pref else [])))
    provenance.update(script=Path(__file__).name, script_sha256=digest(Path(__file__)), selection=provenance['selection']+' Adaptive follow-up changes all profiles to GBFS/FIFO, prompted by frontier growth under A; FIFO chosen from the earlier recorded preferred-LIFO depth pathology. All four heuristics have matched off/on controls.', parent_provenance_sha256=digest(OUT/f'{base}-provenance.json'))
    (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs, indent=2)+'\n')
    (OUT/f'{prefix}-provenance.json').write_text(json.dumps(provenance, indent=2)+'\n')
    return prefix

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--suite', choices=['screen', 'heldout'], default='screen')
    ap.add_argument('--run', action='store_true')
    args = ap.parse_args()
    prefix = prepare(args.suite)
    if args.run:
        subprocess.run(['python3', str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'), str(OUT/f'{prefix}-manifest.json'), '--output', str(OUT/f'{prefix}.csv'), '--logs', str(ROOT/'target/relax-investigation'/prefix), '--seconds', '20', '--memory-mb', '1536', '--rss-mb', '512', '--node-limit', 'unlimited'], cwd=ROOT, env=dict(os.environ, POTOROO_FD=str(ROOT/'downward/fast-downward.py'), POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'), POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'), POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{prefix}-sas')), check=True)
