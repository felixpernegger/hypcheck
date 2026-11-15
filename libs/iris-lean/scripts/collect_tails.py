"""P7: collect every still-unresolved row with the obstruction its wave agent logged (gave_up/untouched).
Usage (from the workspace root): python3 scripts/collect_tails.py OUT.jsonl
Each output row = the results row (open) + `prior_obstruction` (last logged obstruction, or 'untouched'/'not in any log')
+ `prior_cluster`."""
import json, glob, sys
sys.path.insert(0, 'scripts'); import results_io as io
obs = {}
import os  # newest log last, so the latest obstruction (e.g. a tail cluster's) wins
for f in sorted(glob.glob('runs/probe/*_log.jsonl') + glob.glob('runs/waves/*/*_log.jsonl'), key=os.path.getmtime):
    c = f.split('/')[-1][:-len('_log.jsonl')]
    for l in open(f):
        try: r = json.loads(l)
        except Exception: continue
        if 'outcome' not in r or r['outcome'] in ('necessary', 'removable', 'independent'): continue
        obs[(r['theorem'], r['idx'])] = (c, r.get('obstruction') or r['outcome'])
out = []
for b in io.BASES:
    for r in io.load(b):
        if r['status'] != 'unresolved': continue
        c, o = obs.get((r['theorem'], r['idx']), (None, 'not in any log'))
        out.append(dict(r, private=(b == 'private'), prior_cluster=c, prior_obstruction=o))
with open(sys.argv[1], 'w') as f:
    for r in out: f.write(json.dumps(r, ensure_ascii=False) + '\n')
import collections
print(len(out), 'open rows;', collections.Counter('logged' if r['prior_cluster'] else 'no log' for r in out))
print(collections.Counter(r['module'].split('.')[1] for r in out).most_common())
