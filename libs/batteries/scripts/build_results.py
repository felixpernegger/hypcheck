"""Build results/public.jsonl (public) or results/private.jsonl from the inventory and
tool runs. Run from the workspace root:
    python3 scripts/build_results.py [--priv] RUN_OUT.jsonl[:TAG] ...
Every in-scope inventory row appears exactly once. A tool verdict counts only with proof_ok true (or no
proof field for an older format); a necessary/removable verdict whose stored proof failed stays unresolved with
`previous_status`, `witness` and `proof_error` (as in hypcheck). Later files override earlier ones for rows they
decide. Proof locations: `proofs_dir` = RUN_OUT.proofs. Existing results files are backed up to
results/backup/<name>_<timestamp>.jsonl first."""
import json, os, sys, time, shutil
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import results_io as io

args = sys.argv[1:]
PRIV = args[:1] == ['--priv']
if PRIV: args = args[1:]
inv = [r for r in map(json.loads, open('runs/inventory/rows.jsonl')) if r['private'] == PRIV]
rows = {}
for r in inv:
    rows[(r['theorem'], r['idx'])] = {k: r[k] for k in ('theorem', 'user_name', 'module', 'line', 'idx', 'name',
        'binder', 'type', 'dependent', 'folder', 'deprecated', 'deprecated_to', 'alias_of')} | {
        'status': 'unresolved', 'reason': 'not run yet'}
stats = {}
for spec in args:
    path, _, tag = spec.partition(':')
    tag = tag or os.path.basename(path).removesuffix('.jsonl')
    c = stats.setdefault(tag, {})
    for v in map(json.loads, open(path)):
        k = (v['theorem'], v['idx'])
        if k not in rows: c['not in scope'] = c.get('not in scope', 0) + 1; continue
        r = rows[k]
        if r['status'] in ('necessary', 'removable') and v['status'] == 'unresolved': continue
        st = v['status']
        if st in ('necessary', 'removable') and v.get('proof_ok') is False:
            if r['status'] in ('necessary', 'removable'): continue
            r.update(status='unresolved', previous_status=st, witness=v.get('witness'),
                     proof_error=(v.get('proof_error') or '')[:300],
                     reason=f'{st} verdict found by HypCheck ({tag}) but its stored proof failed')
            c['proof failed'] = c.get('proof failed', 0) + 1
            continue
        for f in ('reason', 'previous_status', 'proof_error'): r.pop(f, None)
        r['status'] = st
        for f in ('tactic', 'witness', 'derivable', 'reason', 'proof', 'proof_rendering', 'proof_derivability_only'):
            if f in v: r[f] = v[f]
        if st != 'unresolved':
            r['found_by'] = v.get('found_by', tag)
            r['proofs_file'] = v.get('proofs_file') or (path.removesuffix('.jsonl') + '.proofs')
        c[st] = c.get(st, 0) + 1
out = [dict(sorted(r.items())) for r in rows.values()]
os.makedirs(io.R + 'backup', exist_ok=True)
ts = time.strftime('%Y%m%d_%H%M%S')
for name in [io.base(PRIV)] + list(io.splits(PRIV).values()):
    p = io.R + name + '.jsonl'
    if os.path.exists(p): shutil.copy(p, f"{io.R}backup/{os.path.basename(name)}_{ts}.jsonl")
io.write_splits(out, PRIV)
print(json.dumps(stats))
from collections import Counter
print(Counter(r['status'] for r in out), 'rows', len(out))
