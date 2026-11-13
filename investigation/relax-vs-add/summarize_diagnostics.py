#!/usr/bin/env python3
"""Check paired diagnostic search summaries and summarize structural counters."""
import json
import re
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest

if __name__=='__main__':
    off=json.loads((OUT/'ff-gap-diagnostic-v2-off-summary.json').read_text())
    on=json.loads((OUT/'ff-gap-diagnostic-v2-on-summary.json').read_text())
    assert off['case_sas']==on['case_sas']
    assert off['binary_sha256']==on['binary_sha256']
    records=[]
    logs=ROOT/'target/relax-investigation/ff-gap-diagnostic-v2-on'
    manifest=json.loads((OUT/'ff-gap-diagnostic-v2-on-manifest.json').read_text())
    for i,(a,b,run) in enumerate(zip(off['records'],on['records'],manifest,strict=True)):
        assert (a['case'],a['profile'])==(b['case'],b['profile'])
        assert a['stop_reason'] not in {'time_limit','rss_limit'} and b['stop_reason'] not in {'time_limit','rss_limit'}, 'resource cutoff prevents fixed-node comparison'
        for key in ['solved','stop_reason','generated','visited','cost','max_queued','preferred_generated','preferred_selected']:
            assert a[key]==b[key],(a['case'],a['profile'],key,a[key],b[key])
        err=logs/f"{i:03d}-{run['label']}.err"
        off_err=ROOT/'target/relax-investigation/ff-gap-diagnostic-v2-off'/err.name
        assert not re.findall(r'^FDR_DIAGNOSTIC ',off_err.read_text(),re.M)
        matches=re.findall(r'^FDR_DIAGNOSTIC (.+)$',err.read_text(),re.M);assert len(matches)==1
        d=json.loads(matches[0]);assert d['expanded']==b['visited']
        assert d['open_expansions']+d['threat_expansions']+d['disjunction_expansions']==d['expanded']
        assert d['ordered_pairs']<=d['pairs'] and d['wk_restored']<=d['wk_checked']
        def ratio(n,k):return d[n]/d[k] if d[k] else None
        records.append(dict(case=a['case'],profile=a['profile'],counters=d,
            children_per_selected_open=ratio('open_children','open_expansions'),
            children_per_selected_threat=ratio('threat_children','threat_expansions'),
            mean_open=ratio('open_sum','expanded'),mean_threats=ratio('threat_sum','expanded'),
            threat_expansion_fraction=ratio('threat_expansions','expanded'),
            sampled_ordered_pair_fraction=ratio('ordered_pairs','pairs'),
            sampled_repeated_step_fraction=ratio('repeated_steps','sample_steps'),
            sampled_new_threats_per_insertion=ratio('insertion_new_threats','insertion_children'),
            artifact=str(err.relative_to(ROOT)),artifact_sha256=digest(err)))
    result=dict(paired_runs_verified=len(records),records=records,
        provenance=dict(script_sha256=digest(Path(__file__)),off_summary_sha256=digest(OUT/'ff-gap-diagnostic-v2-off-summary.json'),on_summary_sha256=digest(OUT/'ff-gap-diagnostic-v2-on-summary.json')))
    (OUT/'ff-gap-diagnostic-summary.json').write_text(json.dumps(result,indent=2)+'\n')
    for r in records:
        print(r['case'],r['profile'],'branch',round(r['children_per_selected_open'],2),
              'threat share',round(r['threat_expansion_fraction'],3),
              'ordered pairs',r['sampled_ordered_pair_fraction'],
              'restored',r['counters']['wk_restored'],'/',r['counters']['wk_checked'])
