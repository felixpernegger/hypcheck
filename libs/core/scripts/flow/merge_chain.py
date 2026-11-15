"""Merge checks/ChainProofsStdK.lean.ok.jsonl into results/std*.jsonl as necessary (found_by nec-transitive).
Usage (from the repository root): python3 scripts/flow/merge_chain.py K"""
import json, shutil, collections, sys, os
K = sys.argv[1]; R = 'results/'; D = 'runs/flow/'; os.makedirs(D, exist_ok=True)
ok = {(r['A'], r['i']): r for r in map(json.loads, open(f'checks/ChainProofsStd{K}.lean.ok.jsonl'))}
rows = [json.loads(l) for l in open(R + 'std.jsonl')]
c = collections.Counter()
for r in rows:
    k = (r['theorem'], r['idx'])
    if k in ok and r['status'] == 'unresolved':
        o = ok[k]; r.pop('reason', None)
        r.update(status='necessary', found_by='nec-transitive', via=f"{o['B']} idx {o['j']}" + ''.join(f"; removable {R} idx {k}" for R, k in o.get('rem', [])),
                 tactic=f'nec-transitive (checks/ChainProofsStd{K}.lean)')
        c['necessary'] += 1
print(dict(c))
for f in ['std', 'std_removable', 'std_unresolved', 'std_independent']:
    b = f'{D}{f}_before_{K}.jsonl'
    assert not os.path.exists(b), b
    if os.path.exists(R + f + '.jsonl'): shutil.copy(R + f + '.jsonl', b)
def save(rs, p):
    with open(p, 'w') as fh:
        for x in rs: fh.write(json.dumps(x) + '\n')
save(rows, R + 'std.jsonl')
for st in ('removable', 'unresolved', 'independent'):
    sel = [x for x in rows if x['status'] == st]
    if sel or os.path.exists(R + f'std_{st}.jsonl'): save(sel, R + f'std_{st}.jsonl')
print(collections.Counter(x['status'] for x in rows))
