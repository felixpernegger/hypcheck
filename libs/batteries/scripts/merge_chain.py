"""Merge checks/ChainProofsK.lean.ok.jsonl into the Batteries results as necessary (found_by nec-transitive).
Batteries port of libs/core/scripts/flow/merge_chain.py. Usage (from the workspace root): python3 scripts/merge_chain.py K"""
import json, collections, sys, os, shutil
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import results_io as io
K = sys.argv[1]
ok = {(r['A'], r['i']): r for r in map(json.loads, open(f'checks/ChainProofs{K}.lean.ok.jsonl'))}
for priv in (False, True):
    p = io.R + io.base(priv) + '.jsonl'
    if not os.path.exists(p): continue
    rows = io.load(p); c = collections.Counter()
    for r in rows:
        k = (r['theorem'], r['idx'])
        if k in ok and r['status'] == 'unresolved':
            o = ok[k]
            for f in ('reason', 'previous_status', 'proof_error'): r.pop(f, None)
            r.update(status='necessary', found_by='nec-transitive',
                     via=f"{o['B']} idx {o['j']}" + ''.join(f"; removable {R} idx {i}" for R, i in o.get('rem', [])),
                     tactic=f'nec-transitive (checks/ChainProofs{K}.lean)', proofs=f'checks/ChainProofs{K}.lean')
            c['necessary'] += 1
    for name in [io.base(priv)] + list(io.splits(priv).values()):
        b = f'runs/flow/{os.path.basename(name)}_before_{K}.jsonl'
        if not os.path.exists(b) and os.path.exists(io.R + name + '.jsonl'): shutil.copy(io.R + name + '.jsonl', b)
    io.write_splits(rows, priv)
    print('private' if priv else 'public', dict(c), collections.Counter(x['status'] for x in rows))
