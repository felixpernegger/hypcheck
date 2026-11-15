"""Merge a checked hand-verdict file into results/.
Usage (from the workspace root): python3 scripts/merge_hand.py [--priv] RUN CLUSTER[,CLUSTER2,...] [FOUND_BY]
Merges into results/public*.jsonl; --priv into results/private*.jsonl.
  e.g. python3 scripts/merge_hand.py runs/<RUN> <CLUSTER>
Several comma-separated clusters share one backup (named after the first); FOUND_BY (default "hand") is the
`found_by` recorded, e.g. "refute-dep" for generated files.
Reads RUN/CLUSTER_verdicts.jsonl (proofs in checks/CLUSTERHand.lean), and RUN/CLUSTER_independent.jsonl
if present (needs an `independence` kind per row, see results_io.EVIDENCE). Only unresolved rows change.
Backups: RUN/*_before_CLUSTER.jsonl (an existing backup is never overwritten)."""
import collections, json, os, shutil, sys
sys.path.insert(0, 'scripts')
import results_io as io

args = sys.argv[1:]
PRIV = args[:1] == ['--priv']
if PRIV: args = args[1:]
run, cls = args[0].rstrip('/'), args[1].split(',')
found_by = args[2] if len(args) > 2 else 'hand'
cl = cls[0]
BASE = io.base(PRIV)
SPLITS = io.splits(PRIV)
for name in [BASE] + list(SPLITS.values()):
    bak = f'{run}/{os.path.basename(name)}_before_{cl}.jsonl'
    if os.path.exists(bak):
        print('keeping existing backup', bak)
    elif os.path.exists(io.R + name + '.jsonl'):
        shutil.copy(io.R + name + '.jsonl', bak)
rows = io.load(io.R + BASE + '.jsonl')
idx = {(r['theorem'], r['idx']): i for i, r in enumerate(rows)}
c = collections.Counter()
changed = set()
for cl in cls:
  vf = f'{run}/{cl}_verdicts.jsonl'
  for v in (map(json.loads, open(vf)) if os.path.exists(vf) else []):
      r = rows[idx[(v['theorem'], v['idx'])]]
      if r['status'] != 'unresolved' or v['status'] not in ('necessary', 'removable'):
          c['skipped'] += 1
          continue
      r.pop('reason', None)
      r['status'] = v['status']
      r['found_by'] = found_by
      r['tactic'] = f'{found_by} (checks/{cl}Hand.lean)'
      if v.get('note'): r['hand_note'] = v['note']
      if v['status'] == 'removable': r['derivable'] = bool(v.get('derivable', False))
      if v.get('dependent'): r['dependent'] = True
      changed.add(idx[(v['theorem'], v['idx'])])
      c[v['status']] += 1
  inf = f'{run}/{cl}_independent.jsonl'
  for v in (map(json.loads, open(inf)) if os.path.exists(inf) else []):
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
io.write_splits(rows, PRIV)
print(collections.Counter(r['status'] for r in rows))
