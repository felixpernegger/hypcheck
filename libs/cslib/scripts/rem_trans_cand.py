"""Removable by transitivity (not yet automated): open rows (B, j) whose hypothesis the library proof of B passes
only to targets (A, i) that are already non-dependent removable. Then hc_nec_trans's `A' → B'` with A's stored
proof of A' proves B'. Prints the count (and rows); batch.sh calls it after each merge.
Usage (from the workspace root): python3 scripts/rem_trans_cand.py"""
import json, sys
sys.path.insert(0, 'scripts')
import results_io as io
rows = {(r['theorem'], r['idx']): r for b in io.BASES for r in io.load(b)}
rem = {k for k, r in rows.items() if r['status'] == 'removable' and not r.get('dependent')}
cand = []
for e in map(json.loads, open('runs/struct/edges_all.jsonl')):
    B = (e['B'], e['j'])
    if rows.get(B, {}).get('status') != 'unresolved': continue
    ts = {tuple(t) for t in e['targets']} - {B}
    if ts and ts <= rem: cand.append((B, sorted(ts)))
print(f'removable-by-transitivity candidates: {len(cand)}')
for B, ts in cand: print('  ', B, '<-', ts)
