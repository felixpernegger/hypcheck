"""Candidates whose source B has exactly one unresolved target once the removable (non-dependent) targets are
ignored (plain single-target sources included, `rem` empty); removable targets go to `chain_proofs.py` as `rem`
premises. NECTRANS.jsonl: `runs/flow/nectrans_K.jsonl` or `runs/flow/edges_raw.jsonl` (all sources). Writes runs/flow/cand_K.jsonl, then run
  python3 scripts/chain_proofs.py runs/flow/cand_K.jsonl runs/flow/twins_empty.jsonl checks/ChainProofsStdK.lean
Usage (from the repository root): python3 scripts/flow/cand_rem.py NECTRANS.jsonl K"""
import json, sys
src, K = sys.argv[1], sys.argv[2]
import os; os.makedirs('runs/flow', exist_ok=True)
rows = {(r['theorem'], r['idx']): r for r in map(json.loads, open('results/std.jsonl'))}
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
        f.write(json.dumps({'A': a, 'i': i, 'B': e['B'], 'j': e['j'], 'rem': [list(t) for t in rem],
                            'moduleA': rows[(a, i)]['module']}) + '\n')
print('round', K, 'candidates (with removable targets)', n)
