"""Twin candidates: for each twin group (runs/struct/pub_twins.jsonl, lists of theorem names with identical
statements), rows (T, i) unresolved whose twin (S, i) is decided (necessary/removable).
Usage: python3 scripts/twins_cand.py K -> runs/flow/twins_K.jsonl (input to chain_proofs.py)"""
import json, sys, os
sys.path.insert(0, 'scripts')
import results_io as io
K = sys.argv[1]
os.makedirs('runs/flow', exist_ok=True)
rows = {}
for base in io.BASES:
    for r in io.load(base): rows[(r['theorem'], r['idx'])] = r
n = 0
with open(f'runs/flow/twins_{K}.jsonl', 'w') as f:
    for g in map(json.loads, open('runs/struct/pub_twins.jsonl')):
        for T in g:
            for S in g:
                if S == T: continue
                for (t, i), r in [(k, v) for k, v in rows.items() if k[0] == T]:
                    s = rows.get((S, i))
                    if r['status'] == 'unresolved' and s and s['status'] in ('necessary', 'removable'):
                        f.write(json.dumps({'T': T, 'S': S, 'i': i, 'status': s['status']}, ensure_ascii=False) + '\n'); n += 1
print('twin candidates', n)
