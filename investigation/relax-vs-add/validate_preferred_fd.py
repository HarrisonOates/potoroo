#!/usr/bin/env python3
"""Check state-space controls, plan replay, and task equality with POCL runs."""
import json
from pathlib import Path
from preferred_fd_probe import digest, validate

ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
result=json.loads((OUT/'ff-preferred-fd.json').read_text())
provenance=result['provenance']
assert digest(Path(provenance['binary']))==provenance['binary_sha256']
assert digest(OUT/'preferred_fd_probe.py')==provenance['script_sha256']
for name, sha in provenance['source_hashes'].items():
    assert digest(ROOT/'downward'/name)==sha
rows=result['records']
assert len(rows)==30
assert len({(r['case'],r['profile']) for r in rows})==30
expected_sas={}
for prefix in ['ff-preferred','ff-preferred-vhpop-domains']:
    meta=json.loads((OUT/f'{prefix}.manifest.json').read_text())
    folder=ROOT/'target/relax-investigation'/f'{prefix}-sas'
    captures=[json.loads(p.read_text()) for p in sorted(folder.glob('invocation-*.json'))]
    for run,capture in zip(meta['runs'],captures,strict=True):
        case='-'.join(run['label'].split('-')[:2])
        if case in expected_sas: assert expected_sas[case]==capture['sas_sha256']
        expected_sas[case]=capture['sas_sha256']
previous_end=0
for row in rows:
    assert row['returncode'] in {0, 12, 22, 23, None}, row
    assert row['start_ns']>=previous_end
    previous_end=row['end_ns']
    assert row['sas_sha256']==expected_sas[row['case']]
    sas=ROOT/row['sas']
    assert digest(sas)==row['sas_sha256']
    for name,sha in row['artifact_hashes'].items(): assert digest(ROOT/name)==sha
    if row['solved']:
        plan=next(ROOT/name for name in row['artifact_hashes'] if name.endswith('.plan'))
        length,cost=validate(sas,plan)
        assert (length,cost)==(row['plan_length'],row['cost'])
print('Verified 30 FD runs, archived artifacts, executable solutions and exact SAS equality with POCL.')
for profile in ['astar','gbfs','gbfs_pref']:
    selected=[r for r in rows if r['profile']==profile]
    print(profile, sum(r['solved'] for r in selected), '/',len(selected))
