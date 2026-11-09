#!/usr/bin/env python3
"""FD controls on the actual SAS tasks captured by the FD-gap POCL screen."""
import argparse
import json
import re
import resource
import subprocess
import time
from pathlib import Path
from memory_preferred_probe import ROOT, OUT, digest
from preferred_fd_probe import validate

def cap():
    resource.setrlimit(resource.RLIMIT_AS,(1536*1024**2,1536*1024**2))
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--suite',choices=['screen','heldout'],default='screen')
    ap.add_argument('--prefix',choices=['ff-gap-confirm'])
    args=ap.parse_args();prefix=args.prefix or 'ff-gap-'+args.suite
    summary=json.loads((OUT/f'{prefix}-summary.json').read_text())
    dest=OUT/f'{prefix}-fd.json'; assert not dest.exists()
    binary=ROOT/'downward/builds/release/bin/downward'
    logs=ROOT/'target/relax-investigation'/f'{prefix}-fd';logs.mkdir(parents=True,exist_ok=True)
    provenance=dict(binary=str(binary.resolve()),binary_sha256=digest(binary),
        revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT/'downward',text=True).strip(),
        source_hashes={str(p.relative_to(ROOT/'downward')):digest(p) for p in [
            ROOT/'downward/src/search/heuristics/ff_heuristic.cc',
            ROOT/'downward/src/search/search_algorithms/plugin_eager_greedy.cc']},
        script_sha256=digest(Path(__file__)),pocl_summary_sha256=digest(OUT/f'{prefix}-summary.json'),
        seconds=15,watchdog_seconds=20,address_space_mb=1536,rss_stop_mb=512,
        note='FD search only on identical pretranslated SAS; POCL 15s includes translation. RSS monitored at 50ms intervals; unlike native POCL stop, this kills FD on overflow. Both have 1536MiB per-process address-space limit. No claim of identical end-to-end timing budget.')
    records=[]
    for case,sas_hash in summary['case_sas'].items():
        sas=ROOT/'target/relax-investigation'/f'{prefix}-sas'/f'{sas_hash}.sas'
        assert digest(sas)==sas_hash
        for profile,search in [('astar','astar(ff(),max_time=15)'),
                ('gbfs_pref','let(h,ff(),eager_greedy([h],preferred=[h],max_time=15))')]:
            stem=logs/f'{case}-{profile}';plan=stem.with_suffix('.plan')
            command=[str(binary),'--internal-plan-file',str(plan),'--search',search]
            started=time.monotonic();peak=0;stop=None
            with sas.open('rb') as inp,stem.with_suffix('.out').open('wb') as out,stem.with_suffix('.err').open('wb') as err:
                proc=subprocess.Popen(command,stdin=inp,stdout=out,stderr=err,preexec_fn=cap)
                while proc.poll() is None:
                    try:
                        status=Path(f'/proc/{proc.pid}/status').read_text()
                        vals=re.findall(r'^Vm(?:RSS|HWM):\s*(\d+) kB$',status,re.M)
                        peak=max([peak,*map(int,vals)])
                    except FileNotFoundError: pass
                    if peak>512*1024: stop='rss_limit';proc.kill()
                    elif time.monotonic()-started>20: stop='watchdog';proc.kill()
                    if stop: break
                    time.sleep(.05)
                code=proc.wait()
            elapsed_ms=int((time.monotonic()-started)*1000)
            text=stem.with_suffix('.out').read_text()
            solved=code==0 and 'Solution found!' in text
            cost=length=None
            files=[stem.with_suffix('.out'),stem.with_suffix('.err')]
            if solved:
                length,cost=validate(sas,plan);files.append(plan)
                assert int(re.search(r'Plan cost: (\d+)',text)[1])==cost
            def metric(name):
                m=re.findall(rf'{name} (\d+) state',text)
                return int(m[-1]) if m else None
            records.append(dict(case=case,profile=profile,command=command,returncode=code,
                solved=solved,stop_reason='solved' if solved else stop or f'fd_exit_{code}',
                external_ms=elapsed_ms,sampled_peak_rss_kb=peak,cost=cost,length=length,
                generated=metric('Generated'),expanded=metric('Expanded'),sas_sha256=sas_hash,
                artifact_hashes={str(p.relative_to(ROOT)):digest(p) for p in files}))
            dest.write_text(json.dumps(dict(provenance=provenance,records=records),indent=2)+'\n')
            print(case,profile,records[-1]['stop_reason'],elapsed_ms,cost,flush=True)
