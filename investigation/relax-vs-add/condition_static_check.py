#!/usr/bin/env python3
"""Check achiever families and Parcprinter availability in captured SAS tasks."""
import collections
import json
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest
from summarize_conditions import label

def read_sas(path):
    lines=iter(path.read_text().splitlines())
    def expect(value): assert next(lines)==value
    expect('begin_version');expect('3');expect('end_version')
    expect('begin_metric');next(lines);expect('end_metric')
    variables=[]
    for _ in range(int(next(lines))):
        expect('begin_variable');next(lines);assert int(next(lines))==-1
        variables.append([next(lines) for _ in range(int(next(lines)))])
        expect('end_variable')
    for _ in range(int(next(lines))):
        expect('begin_mutex_group')
        for _ in range(int(next(lines))):next(lines)
        expect('end_mutex_group')
    expect('begin_state');initial=[int(next(lines)) for _ in variables];expect('end_state')
    expect('begin_goal')
    for _ in range(int(next(lines))):next(lines)
    expect('end_goal')
    operators=[]
    for _ in range(int(next(lines))):
        expect('begin_operator');name=next(lines)
        pre=[tuple(map(int,next(lines).split())) for _ in range(int(next(lines)))]
        eff=[]
        for _ in range(int(next(lines))):
            e=list(map(int,next(lines).split()));assert len(e)==4 and e[0]==0
            _,v,before,after=e
            if before!=-1:pre.append((v,before))
            eff.append((v,after))
        assert int(next(lines))==1;expect('end_operator')
        operators.append(dict(name=name,pre=pre,effects=eff))
    assert int(next(lines))==0
    return variables,initial,operators

if __name__=='__main__':
    attribution=json.loads((OUT/'ff-gap-condition-attribution.json').read_text())
    records=[]
    for row in attribution['records']:
        if row['profile']!='add_zlifo':continue
        path=ROOT/row['sas'];assert digest(path)==row['sas_sha256']
        variables,initial,operators=read_sas(path)
        highest=sorted(row['facts'],key=lambda f:-f['open_children'])[:4]
        details=[]
        for fact in highest:
            target=(fact['variable'],fact['value'])
            achievers=[op for op in operators if target in op['effects']]
            details.append(dict(symbol=fact['symbol'],ground_achievers=len(achievers),
              action_families=dict(collections.Counter(op['name'].split()[0] for op in achievers))))
        record=dict(case=row['case'],sas=row['sas'],sas_sha256=row['sas_sha256'],top_fact_achievers=details)
        if row['case'].startswith('parcprinter'):
            availability={v for v,values in enumerate(variables) if any(label(x,values)[0]=='available' for x in values)}
            assignments=[dict(operator=op['name'],variable=v,value=variables[v][value])
                         for op in operators for v,value in op['effects'] if v in availability]
            record['availability_assignments']=assignments
            assert assignments and all(a['operator'].strip()=='initialize' and a['value'].startswith('Atom available(') for a in assignments)
        records.append(record)
        print(record)
    (OUT/'ff-gap-condition-static.json').write_text(json.dumps(dict(records=records,
        script_sha256=digest(Path(__file__)),attribution_sha256=digest(OUT/'ff-gap-condition-attribution.json')),indent=2)+'\n')
