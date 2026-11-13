#!/usr/bin/env python3
"""State-space control on the exact SAS tasks used in the corrected POCL runs."""
import csv
import hashlib
import json
import re
import resource
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
LOGS = ROOT / 'target/relax-investigation/ff-preferred-fd'
BINARY = ROOT / 'downward/builds/release/bin/downward'
PROFILES = {
    'astar': 'astar(ff(),max_time=10)',
    'gbfs': 'eager_greedy([ff()],max_time=10)',
    'gbfs_pref': 'let(h,ff(),eager_greedy([h],preferred=[h],max_time=10))',
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cap():
    resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))


def validate(sas, plan):
    """Replay FD's grounded plan, checking preconditions, goals and unit costs."""
    lines = iter(sas.read_text().splitlines())
    def expect(value):
        assert next(lines) == value
    expect('begin_version'); expect('3'); expect('end_version')
    expect('begin_metric'); next(lines); expect('end_metric')
    for _ in range(int(next(lines))):
        expect('begin_variable'); next(lines); assert int(next(lines)) == -1
        for _ in range(int(next(lines))): next(lines)
        expect('end_variable')
    for _ in range(int(next(lines))):
        expect('begin_mutex_group')
        for _ in range(int(next(lines))): next(lines)
        expect('end_mutex_group')
    expect('begin_state'); state = []
    for line in lines:
        if line == 'end_state': break
        state.append(int(line))
    expect('begin_goal')
    goals = [tuple(map(int, next(lines).split())) for _ in range(int(next(lines)))]
    expect('end_goal')
    operators = {}
    for _ in range(int(next(lines))):
        expect('begin_operator'); name = next(lines)
        pre = [tuple(map(int, next(lines).split())) for _ in range(int(next(lines)))]
        effects = []
        for _ in range(int(next(lines))):
            effect = list(map(int, next(lines).split()))
            assert len(effect) == 4 and effect[0] == 0, 'conditional effect'
            _, var, before, after = effect
            if before != -1: pre.append((var, before))
            effects.append((var, after))
        cost = int(next(lines)); assert cost == 1
        expect('end_operator')
        assert name not in operators
        operators[name] = pre, effects, cost
    assert int(next(lines)) == 0, 'axioms'
    cost = 0; length = 0
    for line in plan.read_text().splitlines():
        if not line or line.startswith(';'): continue
        assert line.startswith('(') and line.endswith(')')
        pre, effects, action_cost = operators[line[1:-1]]
        assert all(state[var] == value for var, value in pre), line
        for var, value in effects: state[var] = value
        cost += action_cost; length += 1
    assert all(state[var] == value for var, value in goals)
    return length, cost


def main():
    destination = OUT / 'ff-preferred-fd.json'
    assert not destination.exists(), 'preserve existing measurements'
    LOGS.mkdir(parents=True, exist_ok=True)
    cases = {}
    for prefix in ['ff-corrected', 'ff-corrected-vhpop-domains']:
        rows = list(csv.DictReader((OUT / f'{prefix}.csv').open()))
        folder = ROOT / 'target/relax-investigation' / f'{prefix}-sas'
        captures = [json.loads(p.read_text()) for p in sorted(folder.glob('invocation-*.json'))]
        for row, capture in zip(rows, captures, strict=True):
            case = f"{row['family']}-{row['problem']}"
            sas = folder / capture['sas_file']
            assert digest(sas) == capture['sas_sha256']
            if case in cases: assert digest(cases[case]) == digest(sas)
            cases[case] = sas
    provenance = dict(binary=str(BINARY.resolve()), binary_sha256=digest(BINARY),
                      revision=subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT/'downward',text=True).strip(),
                      source_hashes={str(p.relative_to(ROOT/'downward')): digest(p) for p in [
                          ROOT/'downward/src/search/heuristics/ff_heuristic.cc',
                          ROOT/'downward/src/search/search_algorithms/plugin_eager_greedy.cc']},
                      script_sha256=digest(Path(__file__)),
                      seconds=10, watchdog_seconds=15, memory_mb=1024, node_limit=None,
                      note='Search only: pretranslated SAS. FD state nodes and POCL partial plans are different units. Preferred FD queue uses default boost=0 (alternation).')
    records=[]
    for case, sas in cases.items():
        for profile, search in PROFILES.items():
            stem=LOGS/f'{case}-{profile}'
            plan=stem.with_suffix('.plan')
            command=[str(BINARY), '--internal-plan-file', str(plan), '--search', search]
            started=time.time_ns()
            timed_out=False
            with sas.open('rb') as inp, stem.with_suffix('.out').open('wb') as out, stem.with_suffix('.err').open('wb') as err:
                try:
                    result=subprocess.run(command, stdin=inp, stdout=out, stderr=err, preexec_fn=cap, timeout=15)
                    code=result.returncode
                except subprocess.TimeoutExpired:
                    code=None;timed_out=True
            ended=time.time_ns()
            log=stem.with_suffix('.out').read_text()
            solved='Solution found!' in log
            length=cost=None
            if solved:
                length,cost=validate(sas,plan)
                assert code==0
                assert int(re.search(r'Plan cost: (\d+)',log)[1])==cost
            def metric(name):
                matches=re.findall(rf'{name} (\d+) state',log)
                return int(matches[-1]) if matches else None
            files=[stem.with_suffix('.out'),stem.with_suffix('.err')]
            if solved: files.append(plan)
            row=dict(case=case,profile=profile,command=command,returncode=code,solved=solved,
                     watchdog_timeout=timed_out,plan_length=length,cost=cost,
                     generated=metric('Generated'),expanded=metric('Expanded'),
                     start_ns=started,end_ns=ended,wall_ms=(ended-started)//1_000_000,
                     sas=str(sas.relative_to(ROOT)),sas_sha256=digest(sas),
                     artifact_hashes={str(p.relative_to(ROOT)):digest(p) for p in files})
            records.append(row)
            print(case,profile,'solved' if solved else f'exit {code}',row['generated'],cost,flush=True)
            destination.write_text(json.dumps(dict(provenance=provenance,records=records),indent=2)+'\n')
    assert len(records)==30


if __name__=='__main__': main()
