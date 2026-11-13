#!/usr/bin/env python3
"""Screen existing flaw-type policies with FFR using the unchanged frozen binary."""
import json
import os
import subprocess
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

POLICIES = ['LCFR', 'LCFR-Loc', 'LCFR-Conf', 'LCFR-Loc-Conf',
            'MC-Loc', 'MW-Loc', 'MW-Loc-Conf', 'DUnf-LIFO']


def prepare():
    prefix = 'ff-types-screen'
    assert not (OUT/f'{prefix}.csv').exists()
    parent = json.loads((OUT/'ff-target-screen-provenance.json').read_text())
    controls = json.loads((OUT/'ff-target-controls-provenance.json').read_text())
    old = json.loads((OUT/'ff-target-screen-manifest.json').read_text())
    old += json.loads((OUT/'ff-target-controls-manifest.json').read_text())
    parent['cases'] += controls['cases']
    assert len(parent['cases']) == 13
    frozen = parent['frozen']
    assert digest(ROOT/frozen['binary']) == frozen['binary_sha256']
    assert digest(ROOT/frozen['source_archive']) == frozen['source_archive_sha256']
    parent.update(suite='screen', script=Path(__file__).name,
        script_sha256=digest(Path(__file__)), require_search_memout=False,
        selection=('Eight existing flaw orders fixed before this screen, FFR/A/LIFO/w1, '
                   'no pruning/preferences. Seven previously diagnosed targets plus six '
                   'historical ADD-success controls. Same frozen binary as ff-target; '
                   'those matched ADD/ZLIFO and FFR/ZLIFO/B8 records are reused as '
                   'baselines (no cross-round timing speed claim). Previously seen cases, '
                   'not heldout. Advance at most two policies for matched ADD and second '
                   'instances if they add target solves or recover controls. No threshold tuning.'),
        policies=POLICIES,
        baseline_summary_sha256={name:digest(OUT/f'{name}-summary.json')
            for name in ['ff-target-screen', 'ff-target-controls']})
    runs = []
    for case in parent['cases']:
        label = case['domain']+'-'+case['instance']
        base = next(r for r in old if r['label'] == label+'-ffr_zlifo')
        for policy in POLICIES:
            profile = 'ffr_'+policy.lower().replace('-', '_')
            runs.append(dict(base, label=label+'-'+profile,
                args=['--fdr-pocl', '-f', policy, '-h', 'FFR/LIFO', '-s', 'A',
                      '-w', '1', '-p', 'none']))
    (OUT/f'{prefix}-manifest.json').write_text(json.dumps(runs, indent=2)+'\n')
    (OUT/f'{prefix}-provenance.json').write_text(json.dumps(parent, indent=2)+'\n')
    return prefix


if __name__ == '__main__':
    prefix = prepare()
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
