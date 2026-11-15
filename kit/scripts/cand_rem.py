"""Transitive-necessity candidates (from libs/core/scripts/flow/cand_rem.py): sources B (necessary) whose
targets, minus non-dependent removable ones (passed to chain_proofs.py as `rem` premises), are exactly one
unresolved row A. EDGES: `nectrans` output over all rows (runs/struct/edges_all.jsonl).
Usage (from the workspace root): python3 scripts/cand_rem.py EDGES K   -> runs/flow/cand_K.jsonl
then: python3 scripts/chain_proofs.py runs/flow/cand_K.jsonl runs/flow/twins_K.jsonl checks/ChainProofs<K>.lean
      python3 scripts/merge_chain.py K"""
import json, sys, os
sys.path.insert(0, 'scripts')
import results_io as io
src, K = sys.argv[1], sys.argv[2]
os.makedirs('runs/flow', exist_ok=True)
rows = {}
for base in io.BASES:
    for r in io.load(base): rows[(r['theorem'], r['idx'])] = r
seen = set(); n = 0
with open(f'runs/flow/cand_{K}.jsonl', 'w') as f:
    for e in map(json.loads, open(src)):
        B = (e['B'], e['j'])
        if rows.get(B, {}).get('status') != 'necessary': continue
        ts = {tuple(t) for t in e['targets']} - {B}
        rem = sorted(t for t in ts if t in rows and rows[t]['status'] == 'removable' and not rows[t].get('dependent'))
        rest = ts - set(rem)
        if len(rest) != 1: continue
        (a, i), = rest
        if rows.get((a, i), {}).get('status') != 'unresolved' or (a, i) in seen: continue
        seen.add((a, i)); n += 1
        f.write(json.dumps({'A': a, 'i': i, 'B': e['B'], 'j': e['j'], 'rem': [list(t) for t in rem]},
                           ensure_ascii=False) + '\n')
print('round', K, 'candidates', n)
