"""Merge checks/ChainProofs<K>.lean.ok.jsonl (transitive necessity and twins) into results/ (CSLib port of
libs/core/scripts/flow/merge_chain.py). Usage: python3 scripts/merge_chain.py K"""
import json, sys, collections
sys.path.insert(0, 'scripts')
import results_io as io
K = sys.argv[1]
ok = [json.loads(l) for l in open(f'checks/ChainProofs{K}.lean.ok.jsonl')]
nec = {(o['A'], o['i']): o for o in ok if 'A' in o}
tw = {(o['T'], o['i']): o for o in ok if 'T' in o}
for base in io.BASES:
    rows = io.load(base); c = collections.Counter()
    for r in rows:
        k = (r['theorem'], r['idx'])
        if r['status'] != 'unresolved': continue
        if k in nec:
            o = nec[k]; r.pop('reason', None)
            r.update(status='necessary', found_by='nec-transitive', tactic=f'nec-transitive (checks/ChainProofs{K}.lean)',
                     via=f"{o['B']} idx {o['j']}" + ''.join(f"; removable {a} idx {b}" for a, b in o.get('rem', [])))
            c['necessary'] += 1
        elif k in tw:
            o = tw[k]; r.pop('reason', None)
            r.update(status=o['status'], found_by='twin', tactic=f'twin (checks/ChainProofs{K}.lean)', via=f"{o['S']} idx {o['i']}")
            c['twin ' + o['status']] += 1
    if c:
        io.backup(base, f'chain{K}')
        io.write_splits(rows, base)
    print(base, dict(c))
