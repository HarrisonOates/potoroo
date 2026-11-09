#!/usr/bin/env python3
"""Adaptive confirmation of B8 after the completed targeted-refinement screen."""
import argparse
import json
import os
import subprocess
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

PREFIX = '{n}LIFO/{o}0LIFO/{o}1NEW/'
POLICIES = {'zlifo': 'ZLIFO', 'lr': PREFIX+'{o}LR/{s}LIFO',
            'b8': PREFIX+'{o}8LIFO/{o}LR/{s}LIFO'}
PROFILES = {
    'confirm': ['add_zlifo', 'add_lr', 'ffr_zlifo', 'ffr_lr', 'ffr_b8', 'ffr_b8_t'],
    'controls': ['add_zlifo', 'ffr_zlifo', 'ffr_b8', 'ffr_b8_t'],
}


def prepare(suite):
    prefix = 'ff-target-'+suite
    assert not (OUT/f'{prefix}.csv').exists()
    source = 'ff-target-second' if suite == 'confirm' else 'ff-ffocr-screen'
    provenance = json.loads((OUT/f'{source}-provenance.json').read_text())
    old = json.loads((OUT/f'{source}-manifest.json').read_text())
    screen = json.loads((OUT/'ff-target-screen-provenance.json').read_text())
    if suite == 'controls':
        provenance['cases'] = [c for c in provenance['cases'] if c['status'] == 'solved']
        assert len(provenance['cases']) == 6
    else:
        assert len(provenance['cases']) == 7
    for key in ['frozen', 'binary_sha256', 'source_hashes', 'limits']:
        provenance[key] = screen[key]
    frozen = provenance['frozen']
    assert digest(ROOT/frozen['binary']) == frozen['binary_sha256']
    assert digest(ROOT/frozen['source_archive']) == frozen['source_archive_sha256']
    provenance.update(
        suite=suite, script=Path(__file__).name, script_sha256=digest(Path(__file__)),
        selection=('Adaptive profile selection AFTER ff-target-screen. Previously seen second '
                   'instances or six historical ADD-success controls; NOT unseen heldout data. '
                   'Test whether FFR/B8 combines ZLIFO Parcprinter and LR NoTankage/Pegsol '
                   'coverage without losing ADD controls. Keep one propagation comparison '
                   'on FFR/B8; no new threshold tuning. Same frozen binary and resource limits.'),
        selected_profiles=PROFILES[suite],
        selection_evidence_sha256=digest(OUT/'ff-target-screen-interventions.json'))
    runs = []
    for case in provenance['cases']:
        label = case['domain']+'-'+case['instance']
        base = next(r for r in old if r['label'].startswith(label+'-'))
        for profile in PROFILES[suite]:
            heuristic, policy, *force = profile.split('_')
            runs.append(dict(base, label=label+'-'+profile,
                binary=str(ROOT/frozen['binary']), revision='2b7bf40+targeted-refinements',
                args=['--fdr-pocl', '-f', POLICIES[policy], '-h', heuristic.upper()+'/LIFO',
                      '-s', 'A', '-w', '1', '-p', 'threats' if force else 'none']))
    (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs, indent=2)+'\n')
    (OUT/f'{prefix}-provenance.json').write_text(json.dumps(provenance, indent=2)+'\n')
    return prefix


def run(prefix):
    env = dict(os.environ, POTOROO_FDR_DIAGNOSTICS='0',
        POTOROO_FD=str(ROOT/'downward/fast-downward.py'),
        POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'),
        POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'),
        POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{prefix}-sas'))
    subprocess.run(['python3', str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),
        str(OUT/f'{prefix}-manifest.json'), '--output', str(OUT/f'{prefix}.csv'),
        '--logs', str(ROOT/'target/relax-investigation'/prefix), '--seconds', '20',
        '--memory-mb', '1536', '--rss-mb', '512', '--node-limit', 'unlimited'],
        env=env, check=True)
    subprocess.run(['python3', str(OUT/'summarize_memory.py'), prefix], check=True)
    subprocess.run(['python3', str(OUT/'summarize_targeted_refinements.py'), prefix], check=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--suite', choices=PROFILES, required=True)
    ap.add_argument('--run', action='store_true')
    args = ap.parse_args()
    prefix = prepare(args.suite)
    if args.run:
        run(prefix)
