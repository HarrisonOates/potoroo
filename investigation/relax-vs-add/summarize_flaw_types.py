#!/usr/bin/env python3
"""Check paired search counts and partition selected flaws by diagnostic type."""
import json
import re
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

FLAGS = {'local':1, 'unsafe':2, 'initial':4, 'goal':8, 'static':16,
         'blocked_initial':32, 'reuse':64, 'blocked_reuse':128}
TRACKED = ['outcome', 'solved', 'nodes_generated', 'nodes_visited', 'plan_cost', 'plan_len', 'pruned', 'dropped',
           'h_evals', 'max_queued', 'max_steps', 'max_open_conditions', 'max_threats',
           'max_disjunctions', 'supporter_forced', 'threat_forced', 'preferred_generated', 'preferred_selected']


def records(text, prefix):
    return [json.loads(s) for s in re.findall('^'+re.escape(prefix)+r' (.+)$', text, re.M)]


if __name__ == '__main__':
    bundles = {}
    for mode in ['baseline', 'off', 'on']:
        prefix = 'ff-types-diagnostic-'+mode
        summary = json.loads((OUT/f'{prefix}-summary.json').read_text())
        manifest = json.loads((OUT/f'{prefix}-manifest.json').read_text())
        rows = []
        for i, (measurement, run) in enumerate(zip(summary['records'], manifest, strict=True)):
            assert measurement['stop_reason'] in {'solved', 'limit reached'}, measurement
            path = ROOT/'target/relax-investigation'/prefix/f"{i:03d}-{run['label']}.err"
            assert digest(path) == summary['artifact_hashes'][str(path.relative_to(ROOT))]
            raw = path.read_text()
            stats = records(raw, 'STATS'); assert len(stats)==1
            schema = records(raw, 'FDR_DIAGNOSTIC_FLAW_TYPES')
            opens = records(raw, 'FDR_DIAGNOSTIC_OPEN_TYPE')
            threats = records(raw, 'FDR_DIAGNOSTIC_THREAT_TYPE')
            totals = records(raw, 'FDR_DIAGNOSTIC')
            if mode != 'on':
                assert not schema and not opens and not threats and not totals
                rows.append((measurement, stats[0]))
                continue
            assert len(schema)==len(totals)==1
            assert schema[0]['version']==1
            assert all(schema[0][name]==bit for name,bit in FLAGS.items())
            assert len(opens)==len({r['mask'] for r in opens})
            assert len(threats)==len({(r['repairs'],r['confrontable']) for r in threats})
            assert sum(r['selected'] for r in opens)==totals[0]['open_expansions']
            assert sum(r['children'] for r in opens)==totals[0]['open_children']
            assert sum(r['selected'] for r in threats)==totals[0]['threat_expansions']
            assert sum(r['children'] for r in threats)==totals[0]['threat_children']
            assert schema[0]['disjunctions']==totals[0]['disjunction_expansions']==0
            assert totals[0]['expanded']==stats[0]['nodes_visited']
            assert all(not r['confrontable'] for r in threats)
            conditions=records(raw, 'FDR_DIAGNOSTIC_CONDITION')
            assert sum(r['insertions'] for r in opens)==sum(r['insertion_children'] for r in conditions)
            for row in opens:
                mask=row['mask']; assert 0<=mask<256 and row['insertions']<=row['children']
                if mask&32: assert mask&4 and mask&2
                if mask&128: assert mask&64 and mask&2
                if mask&16: assert not(mask&2 or mask&32 or mask&128)
            by_type={name:{key:sum(r[key] for r in opens if r['mask']&bit)
                           for key in ['selected','children','insertions']}
                     for name,bit in FLAGS.items()}
            by_type['blocked_initial_no_unblocked_reuse']={
                key:sum(r[key] for r in opens if r['mask']&32 and (not r['mask']&64 or r['mask']&128))
                for key in ['selected','children','insertions']}
            rows.append((measurement, stats[0], dict(case=measurement['case'], profile=measurement['profile'],
                open_expansions=totals[0]['open_expansions'], open_children=totals[0]['open_children'],
                threat_expansions=totals[0]['threat_expansions'], open_masks=opens,
                by_type=by_type, threat_types=threats)))
        bundles[mode]=(summary, rows)
    result=[]
    for baseline,off,on in zip(bundles['baseline'][1], bundles['off'][1], bundles['on'][1], strict=True):
        assert (off[0]['case'], off[0]['profile'])==(on[0]['case'],on[0]['profile'])
        assert (baseline[0]['case'], baseline[0]['profile'])==(off[0]['case'],off[0]['profile'])
        assert all(off[1][key]==on[1][key] for key in TRACKED), (off[0], on[0])
        assert all(baseline[1][key]==off[1][key] for key in TRACKED), (baseline[0], off[0])
        case=on[0]['case']
        assert bundles['off'][0]['case_sas'][case]==bundles['on'][0]['case_sas'][case]
        assert bundles['baseline'][0]['case_sas'][case]==bundles['off'][0]['case_sas'][case]
        result.append(on[2])
    output=dict(records=result, paired_runs=len(result), tracked_fields=TRACKED,
        source_summary_sha256={mode:digest(OUT/f'ff-types-diagnostic-{mode}-summary.json') for mode in bundles},
        script_sha256=digest(Path(__file__)),
        note='Selected-flaw counts at 100000 generated nodes; types overlap, masks partition opens. Forced clobbers are unconditional and necessarily between producer and consumer. Passing this check is not proof of a feasible causal link. Old/new and observer on/off agreement is for recorded outcomes/counters, not full traces or runtime.')
    (OUT/'ff-types-diagnostic-analysis.json').write_text(json.dumps(output,indent=2)+'\n')
    print('Verified', len(result), 'old/off/on triples, without resource stops.')
    for row in result:
        if row['profile'] in ['add_zlifo', 'ffr_zlifo']:
            denominator=max(1,row['open_children'])
            print(row['case'], row['profile'], 'open children', row['open_children'],
                  {name:round(100*c['children']/denominator,1) for name,c in row['by_type'].items()})
