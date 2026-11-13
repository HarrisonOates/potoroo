#!/usr/bin/env python3
"""Verify memory-target measurements and independently replay every solution."""
import csv
import hashlib
import json
import re
import shlex
import sys
import tarfile
from collections import Counter, defaultdict
from pathlib import Path
from preferred_fd_probe import validate

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def summarize(prefix):
    provenance = json.loads((OUT / f'{prefix}-provenance.json').read_text())
    frozen = provenance['frozen']
    assert digest(ROOT / frozen['binary']) == provenance['binary_sha256']
    assert digest(ROOT / frozen['source_archive']) == frozen['source_archive_sha256']
    with tarfile.open(ROOT / frozen['source_archive']) as archive:
        for name, value in provenance['source_hashes'].items():
            assert hashlib.sha256(archive.extractfile(name).read()).hexdigest() == value
    assert digest(OUT / provenance.get('script', 'memory_preferred_probe.py')) == provenance['script_sha256']
    assert digest(OUT / 'ff_capture_translate.py') == provenance['wrapper_sha256']
    assert digest(ROOT.parent / 'potoroo-cluster/scripts/potoroo/pocl_probe.py') == provenance['harness_sha256']
    for name, value in provenance['translator_hashes'].items():
        assert digest(Path(provenance['translator_root']) / name) == value
    for name, value in provenance['cluster_sources'].items():
        assert digest(Path(name)) == value
    limits = provenance['limits']
    metadata = json.loads((OUT / f'{prefix}.manifest.json').read_text())
    manifest = json.loads((OUT / f'{prefix}-manifest.json').read_text())
    assert manifest == metadata['runs']
    assert set(metadata['hashes'].values()) == {provenance['binary_sha256']}
    assert (metadata['seconds'], metadata['memory_mb'], metadata['node_limit']) == (limits['watchdog_seconds'], limits['address_space_mb'], limits['node_limit'])
    rows = list(csv.DictReader((OUT / f'{prefix}.csv').open()))
    assert len(rows) == len(manifest) == len({r['label'] for r in rows})
    sas_dir = ROOT / 'target/relax-investigation' / f'{prefix}-sas'
    captures = [json.loads(p.read_text()) for p in sorted(sas_dir.glob('invocation-*.json'))]
    assert len(captures) == len(rows)
    cases = {(r['domain'], r['instance']): r for r in provenance['cases']}
    case_sas, inputs = defaultdict(set), defaultdict(set)
    records, solutions, artifacts = [], [], {}
    for row, run, capture in zip(rows, manifest, captures, strict=True):
        assert row['label'] == run['label']
        command = [run['binary'], *run['args'], '-v', '--time-limit', str(limits['planner_seconds']), '--stage-mem-mb', str(limits['planner_rss_stop_mb']), '-l', limits['node_limit'], run['domain'], run['problem']]
        assert shlex.split(row['command']) == command
        assert row['binary_sha256'] == provenance['binary_sha256']
        assert row['stats_source'] == 'final', row['label']
        assert row['node_limit'] == limits['node_limit']
        assert int(row['planner_seconds']) == limits['planner_seconds']
        assert int(row['memory_mb']) == limits['address_space_mb']
        evidence = cases[row['family'], row['problem']]
        if provenance.get('require_search_memout', True):
            assert evidence['status'] == 'memout' and 'Search [' in evidence['error_tail']
        else:
            assert evidence['status'] in {'solved', 'memout'}
            if evidence['status'] == 'memout': assert 'Search [' in evidence['error_tail']
        assert digest(Path(run['domain'])) == evidence['domain_sha256']
        assert digest(Path(run['problem'])) == evidence['problem_sha256']
        case = f"{row['family']}-{row['problem']}"
        inputs[case].add((capture['domain_sha256'], capture['problem_sha256']))
        case_sas[case].add(capture['sas_sha256'])
        sas = sas_dir / capture['sas_file']
        assert digest(sas) == capture['sas_sha256']
        stem = ROOT / 'target/relax-investigation' / prefix / f"{int(row['run']):03d}-{row['label']}"
        err = stem.with_suffix('.err').read_text()
        matches = re.findall(r'^STATS (.+)$', err, re.MULTILINE)
        assert len(matches) == 1
        stats = json.loads(matches[0])
        for key in ['outcome', 'nodes_generated', 'nodes_visited', 'plan_cost', 'wall_ms', 'peak_rss_kb', 'h_evals', 'h_eval_ms']:
            assert str(stats[key]) == row[key], (row['label'], key)
        preferred = '--preferred' in run['args']
        assert (stats['preferred_generated'] > 0) == preferred
        assert (stats['preferred_selected'] > 0) == preferred
        assert stats['preferred_selected'] <= stats['preferred_generated'] <= stats['nodes_generated']
        # The native planner labels both soft RSS and deadline stops "timeout".
        # Classify the reason from its explicit finish message, not sampled RSS.
        solved = row['outcome'] == 'solved'
        if solved: stop = 'solved'
        elif 'Search finished: memory bound reached' in err: stop = 'rss_limit'
        elif 'Search finished: time limit reached' in err: stop = 'time_limit'
        else:
            match = re.search(r'Search finished: (.+?) in ', err)
            stop = match[1] if match else row['outcome']
        if solved:
            raw = stem.with_suffix('.out')
            actions = re.findall(r'^\d+:(\([^\n]+\))$', raw.read_text(), re.MULTILINE)
            lines = sas.read_text().splitlines()
            names = {' '.join(lines[i+1].split()): lines[i+1] for i, line in enumerate(lines) if line == 'begin_operator'}
            assert len(names) == lines.count('begin_operator')
            normalized = stem.with_suffix('.replay.plan')
            normalized.write_text('\n'.join('('+names[' '.join(a[1:-1].split())]+')' for a in actions)+'\n')
            length, cost = validate(sas, normalized)
            assert cost == int(row['plan_cost'])
            solutions.append(dict(label=row['label'], length=length, cost=cost, sas_sha256=digest(sas), plan_sha256=digest(normalized)))
            artifacts[str(normalized.relative_to(ROOT))] = digest(normalized)
        for suffix in ['.err', '.out', '.time']:
            p = stem.with_suffix(suffix)
            artifacts[str(p.relative_to(ROOT))] = digest(p)
        records.append(dict(case=case, profile=row['label'].removeprefix(case+'-'), solved=solved, raw_outcome=row['outcome'], stop_reason=stop, generated=int(row['nodes_generated']), visited=int(row['nodes_visited']), cost=int(row['plan_cost']) if solved else None, planner_ms=int(row['wall_ms']), external_ms=int(row['external_ms']), planner_peak_rss_kb=int(row['peak_rss_kb']), tree_peak_rss_kb=int(row['tree_peak_rss_kb']), max_queued=stats['max_queued'], preferred_generated=stats['preferred_generated'], preferred_selected=stats['preferred_selected']))
    assert all(len(s) == 1 for s in case_sas.values())
    assert all(len(s) == 1 for s in inputs.values())
    for p in sorted(sas_dir.iterdir()): artifacts[str(p.relative_to(ROOT))] = digest(p)
    for suffix in ['.csv', '.manifest.json', '-manifest.json', '-provenance.json']:
        p = OUT / f'{prefix}{suffix}'
        artifacts[str(p.relative_to(ROOT))] = digest(p)
    counts = defaultdict(Counter)
    for r in records:
        counts[r['profile']]['attempted'] += 1
        counts[r['profile']][r['stop_reason']] += 1
    result = dict(suite=prefix, run_count=len(records), case_count=len(cases), binary_sha256=provenance['binary_sha256'], counts={p:dict(c) for p,c in counts.items()}, records=records, independently_replayed=len(solutions), solutions=solutions, case_sas={k:next(iter(v)) for k,v in case_sas.items()}, validator_sha256=digest(Path(__file__)), sas_validator_sha256=digest(OUT/'preferred_fd_probe.py'), artifact_hashes=artifacts)
    dest = OUT / f'{prefix}-summary.json'
    if dest.exists():
        previous = json.loads(dest.read_text())
        # Revalidation may add checks without changing measurements/artifacts.
        previous['validator_sha256'] = result['validator_sha256']
        assert previous == result
    dest.write_text(json.dumps(result, indent=2)+'\n')
    print(prefix, json.dumps(result['counts']))
    print('Independently replayed', len(solutions), 'solutions.')
    for r in records:
        if r['solved']: print(r)

if __name__ == '__main__':
    for prefix in sys.argv[1:]: summarize(prefix)
