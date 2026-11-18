"""Merge a checked hand-verdict file into results/.
Usage (from the workspace root): python3 scripts/merge_hand.py [--private] RUN CLUSTER[,CLUSTER2,...] [FOUND_BY]
--private merges into results/private*.jsonl instead of results/public*.jsonl.
  e.g. python3 scripts/merge_hand.py runs/hand11 RangeLoop
Several comma-separated clusters share one backup (named after the first); FOUND_BY (default "hand") is the
`found_by` recorded, e.g. "refute-dep" for generated files.
Reads RUN/CLUSTER_verdicts.jsonl (proofs in checks/CLUSTERHand.lean), and RUN/CLUSTER_independent.jsonl
if present (needs an `independence` kind per row, see results_io.EVIDENCE). Only unresolved rows change.
Backups: RUN/*_before_CLUSTER.jsonl (an existing backup is never overwritten)."""
import collections, json, os, shutil, sys
sys.path.insert(0, 'scripts')
import results_io as io

args = sys.argv[1:]
PRIV = args[:1] == ['--private']
if PRIV: args = args[1:]
run, cls = args[0].rstrip('/'), args[1].split(',')
found_by = args[2] if len(args) > 2 else 'hand'
cl = cls[0]
BASE = 'private' if PRIV else 'public'
io.backup(BASE, cl, run)
rows = io.load(BASE)
def decl_map(cl):
    p = f'checks/{cl}Hand.lean.map.jsonl'  # written by check_hand.py
    return {(m['theorem'], m['idx'], m['status']): m['decl'] for m in map(json.loads, open(p))} if os.path.exists(p) else {}
idx = {(r['theorem'], r['idx']): i for i, r in enumerate(rows)}
c = collections.Counter()
changed = set()
for cl in cls:
  dm = decl_map(cl)
  vf = f'{run}/{cl}_verdicts.jsonl'
  for v in (map(json.loads, open(vf)) if os.path.exists(vf) else []):
      if (v['theorem'], v['idx']) not in idx:
          c['in the other result file (public/private)'] += 1
          continue
      r = rows[idx[(v['theorem'], v['idx'])]]
      if r['status'] != 'unresolved' or v['status'] not in ('necessary', 'removable'):
          c['skipped'] += 1
          continue
      r.pop('reason', None)
      r['status'] = v['status']
      r['found_by'] = found_by
      r['tactic'] = f'{found_by} (checks/{cl}Hand.lean)'
      if v.get('note'): r['hand_note'] = v['note']
      d = dm.get((v['theorem'], v['idx'], v['status']))
      if d: r['proof_file'], r['proof_decl'] = f'checks/{cl}Hand.lean', d
      if v['status'] == 'removable': r['derivable'] = bool(v.get('derivable', False))
      if v.get('dependent'): r['dependent'] = True
      changed.add(idx[(v['theorem'], v['idx'])])
      c[v['status']] += 1
  inf = f'{run}/{cl}_independent.jsonl'
  for v in (map(json.loads, open(inf)) if os.path.exists(inf) else []):
      if (v['theorem'], v['idx']) not in idx: continue
      r = rows[idx[(v['theorem'], v['idx'])]]
      if r['status'] != 'unresolved':
          c['skipped'] += 1
          continue
      reason = v['reason'] if v['reason'].startswith('independent') else 'independent: ' + v['reason']
      io.mark_independent(r, v['independence'], reason,
                          v.get('independent_support') or f'checks/{cl}Hand.lean')
      changed.add(idx[(v['theorem'], v['idx'])])
      c['independent'] += 1
for i in changed:
    rows[i] = dict(sorted(rows[i].items()))
print(','.join(cls), dict(c))
io.write_splits(rows, BASE)
print(collections.Counter(r['status'] for r in rows))
