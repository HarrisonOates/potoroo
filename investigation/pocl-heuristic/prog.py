import json,collections
c=json.load(open('cluster-solved.json')); cadd={tuple(k) for k in c['add']}; cfd={tuple(k) for k in c['fd']}
for f in ['calib.jsonl','rest.jsonl']:
    v=collections.defaultdict(dict)
    for l in open(f):
        r=json.loads(l); v[r['config']][(r['domain'],r['instance'])]=r['status']=='solved'
    p=v['port3t']; a=v['add']
    ks=[k for k in p if k in a]
    print(f,'port3t n',len(p),'solved',sum(p.values()),'| on common',len(ks),': port3t',sum(p[k] for k in ks),'locADD',sum(a[k] for k in ks),'clADD',sum(k in cadd for k in ks),'clFD',sum(k in cfd for k in ks))
