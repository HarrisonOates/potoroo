#!/usr/bin/env python3
"""Paired flaw-type observers on/off, bounded by generated nodes rather than time."""
import hashlib
import json
import os
import subprocess
import tarfile
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

PROFILES = [('add_zlifo', 'ADD', 'ZLIFO'), ('ffr_zlifo', 'FFR', 'ZLIFO'),
            ('ffr_lcfr_loc', 'FFR', 'LCFR-Loc'),
            ('ffr_lcfr_loc_conf', 'FFR', 'LCFR-Loc-Conf')]


if __name__ == '__main__':
    frozen = json.loads((OUT/'ff-types-diagnostic-frozen.json').read_text())
    assert digest(ROOT/frozen['binary']) == frozen['binary_sha256']
    assert digest(ROOT/frozen['source_archive']) == frozen['source_archive_sha256']
    with tarfile.open(ROOT/frozen['source_archive']) as archive:
        sources = {m.name:hashlib.sha256(archive.extractfile(m).read()).hexdigest()
                   for m in archive if m.isfile()}
    parent = json.loads((OUT/'ff-types-screen-provenance.json').read_text())
    old = json.loads((OUT/'ff-types-screen-manifest.json').read_text())
    for mode in ['baseline', 'off', 'on']:
        prefix = 'ff-types-diagnostic-'+mode
        assert not (OUT/f'{prefix}.csv').exists()
        selected_frozen = parent['frozen'] if mode=='baseline' else frozen
        selected_sources = parent['source_hashes'] if mode=='baseline' else sources
        provenance = dict(parent, frozen=selected_frozen, binary_sha256=selected_frozen['binary_sha256'],
            source_hashes=selected_sources, script=Path(__file__).name, script_sha256=digest(Path(__file__)),
            diagnostics=mode, selection=('Paired diagnostic observer off/on at 100000 generated '
                'nodes on 13 previously studied cases, plus old-binary baseline. ADD/ZLIFO and FFR with ZLIFO, LCFR-Loc, '
                'LCFR-Loc-Conf. Compare recorded search outcomes/counters, not complete traces. '
                'Type counts describe selected flaws/emitted children before outer pruning; '
                'bitmask buckets partition opens, named types overlap. No timing claim.'),
            limits=dict(planner_seconds=15, watchdog_seconds=20, address_space_mb=1536,
                        planner_rss_stop_mb=512, node_limit='100000'))
        runs = []
        for case in parent['cases']:
            label = case['domain']+'-'+case['instance']
            base = next(r for r in old if r['label'].startswith(label+'-'))
            for profile, heuristic, policy in PROFILES:
                runs.append(dict(base, label=label+'-'+profile,
                    binary=str(ROOT/selected_frozen['binary']),
                    revision='2b7bf40+targeted-refinements' if mode=='baseline' else '2b7bf40+native-effort-correction',
                    args=['--fdr-pocl', '-f', policy, '-h', heuristic+'/LIFO', '-s', 'A',
                          '-w', '1', '-p', 'none']))
        (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs, indent=2)+'\n')
        (OUT/f'{prefix}-provenance.json').write_text(json.dumps(provenance, indent=2)+'\n')
        env = dict(os.environ, POTOROO_FDR_DIAGNOSTICS='1' if mode=='on' else '0',
            POTOROO_FDR_FLAW_TYPES='1' if mode=='on' else '0',
            POTOROO_FD=str(ROOT/'downward/fast-downward.py'),
            POTOROO_DOWNWARD=str(ROOT/'downward/builds/release/bin/downward'),
            POTOROO_PYTHON=str(OUT/'ff_capture_translate.py'),
            POTOROO_CAPTURE_DIR=str(ROOT/'target/relax-investigation'/f'{prefix}-sas'))
        subprocess.run(['python3', str(ROOT.parent/'potoroo-cluster/scripts/potoroo/pocl_probe.py'),
            str(OUT/f'{prefix}-manifest.json'), '--output', str(OUT/f'{prefix}.csv'),
            '--logs', str(ROOT/'target/relax-investigation'/prefix), '--seconds', '20',
            '--memory-mb', '1536', '--rss-mb', '512', '--node-limit', '100000'],
            env=env, check=True)
        subprocess.run(['python3', str(OUT/'summarize_memory.py'), prefix], check=True)
