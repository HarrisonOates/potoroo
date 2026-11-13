#!/usr/bin/env python3
"""Map observed FDR flaw facts to exact captured SAS labels and predicates."""
import collections
import json
import re
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

FIELDS = ['open_expansions', 'open_children', 'insertion_children', 'goal_opens',
          'threat_expansions', 'threat_children', 'initial_link_threats']

def read_variables(path):
    lines = iter(path.read_text().splitlines())
    def expect(value):
        assert next(lines) == value
    expect('begin_version'); expect('3'); expect('end_version')
    expect('begin_metric'); next(lines); expect('end_metric')
    variables = []
    for _ in range(int(next(lines))):
        expect('begin_variable'); name = next(lines); assert int(next(lines)) == -1
        values = [next(lines) for _ in range(int(next(lines)))]
        expect('end_variable'); variables.append(dict(name=name, values=values))
    for _ in range(int(next(lines))):
        expect('begin_mutex_group')
        for _ in range(int(next(lines))): next(lines)
        expect('end_mutex_group')
    expect('begin_state')
    initial = [int(next(lines)) for _ in variables]
    expect('end_state'); expect('begin_goal')
    for _ in range(int(next(lines))): next(lines)
    expect('end_goal')
    operators = int(next(lines))
    return variables, initial, operators

def label(value, values):
    match = re.fullmatch(r'(NegatedAtom|Atom) ([^(]+)\((.*)\)', value)
    if match:
        polarity, predicate, args = match.groups()
        return ('not ' if polarity == 'NegatedAtom' else '') + predicate, args.split(', ') if args else []
    assert value == '<none of those>', value
    predicates = sorted({re.fullmatch(r'(NegatedAtom|Atom) ([^(]+)\((.*)\)', v)[2]
                         for v in values if v != '<none of those>'})
    return 'none-of(' + ','.join(predicates) + ')', []

if __name__ == '__main__':
    current = json.loads((OUT/'ff-gap-condition-summary.json').read_text())
    baseline = json.loads((OUT/'ff-gap-diagnostic-v2-on-summary.json').read_text())
    old_diag = json.loads((OUT/'ff-gap-diagnostic-summary.json').read_text())
    manifest = json.loads((OUT/'ff-gap-condition-manifest.json').read_text())
    assert current['case_sas'] == baseline['case_sas']
    records = []
    for i, (a,b,old,run) in enumerate(zip(current['records'],baseline['records'],old_diag['records'],manifest,strict=True)):
        assert (a['case'],a['profile']) == (b['case'],b['profile']) == (old['case'],old['profile'])
        assert run['args'][run['args'].index('-p')+1] == 'none', 'SAS mapping requires no projection'
        for key in ['solved','stop_reason','generated','visited','cost','max_queued','preferred_generated','preferred_selected']:
            assert a[key] == b[key], (a['case'],a['profile'],key,a[key],b[key])
        assert a['stop_reason'] not in {'time_limit','rss_limit'}
        err = ROOT/'target/relax-investigation/ff-gap-condition'/f"{i:03d}-{run['label']}.err"
        text = err.read_text()
        total = re.findall(r'^FDR_DIAGNOSTIC (.+)$',text,re.M); assert len(total) == 1
        total = json.loads(total[0]); assert total == old['counters']
        facts = [json.loads(x) for x in re.findall(r'^FDR_DIAGNOSTIC_CONDITION (.+)$',text,re.M)]
        assert len({(x['variable'],x['value']) for x in facts}) == len(facts)
        for key in ['open_expansions','open_children','threat_expansions','threat_children']:
            assert sum(x[key] for x in facts) == total[key]
        sas_hash = current['case_sas'][a['case']]
        sas = ROOT/'target/relax-investigation/ff-gap-condition-sas'/(sas_hash+'.sas')
        assert digest(sas) == sas_hash
        variables, initial, operators = read_variables(sas)
        assert len(variables) == total['variables'] and operators == total['operators']
        groups = collections.defaultdict(lambda: dict.fromkeys(FIELDS,0))
        arguments = collections.defaultdict(lambda: dict.fromkeys(FIELDS,0))
        for fact in facts:
            v, value = fact['variable'], fact['value']
            labels = variables[v]['values']; symbol = labels[value]
            group, args = label(symbol, labels)
            fact.update(symbol=symbol, predicate=group, arguments=args, initially_true=initial[v]==value)
            assert fact['goal_opens'] <= fact['open_expansions']
            assert fact['insertion_children'] <= fact['open_children']
            assert fact['initial_link_threats'] <= fact['threat_expansions']
            for key in FIELDS:
                groups[group][key] += fact[key]
                if args: arguments[group+'['+args[0]+']'][key] += fact[key]
        record = dict(case=a['case'],profile=a['profile'],totals=total,
                      predicates=dict(groups),first_argument_groups=dict(arguments),facts=facts,
                      sas=str(sas.relative_to(ROOT)),sas_sha256=sas_hash,
                      log=str(err.relative_to(ROOT)),log_sha256=digest(err))
        records.append(record)
        if a['profile']=='add_zlifo':
            print(a['case'])
            for group,c in sorted(groups.items(),key=lambda x:-x[1]['open_children']):
                print(' ',group,'open',c['open_expansions'],'children',c['open_children'],
                      'new',c['insertion_children'],'threat',c['threat_expansions'],
                      'INIT threats',c['initial_link_threats'])
    result = dict(matched_v2_runs=len(records),records=records,
                  provenance=dict(script_sha256=digest(Path(__file__)),
                    current_summary_sha256=digest(OUT/'ff-gap-condition-summary.json'),
                    baseline_summary_sha256=digest(OUT/'ff-gap-diagnostic-v2-on-summary.json'),
                    baseline_diagnostic_sha256=digest(OUT/'ff-gap-diagnostic-summary.json')))
    (OUT/'ff-gap-condition-attribution.json').write_text(json.dumps(result,indent=2)+'\n')
