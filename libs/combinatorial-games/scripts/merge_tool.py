"""Merge a HypCheck run (OUT.jsonl + OUT.proofs/) into results/<base>*.jsonl (from hypcheck runs/v10/merge.py).
A verdict is merged only with proof_ok and when every part in OUT.proofs/compile.log is OK; only unresolved rows
change; rows that stay unresolved get the fresh `reason`. Output rows not in the inventory are reported, not added.
Usage (from the workspace root): python3 scripts/merge_tool.py OUT.jsonl TAG [--private] [--dry]"""
import json, collections, sys, os
sys.path.insert(0, 'scripts')
import results_io as io

out_path, tag = sys.argv[1], sys.argv[2]
base = 'private' if '--private' in sys.argv else 'public'
pdir = out_path[:-len('.jsonl')] + '.proofs'
# private runs: stored proofs only compile per module (scripts/priv/compile_priv.py -> bymod.log)
logf = pdir + ('/bymod.log' if base == 'private' else '/compile.log')
log = [l for l in open(logf).read().splitlines() if l[:4] in ('OK  ', 'OK   '[:4], 'FAIL')]
bad = [l for l in log if not l.startswith('OK')]
assert log and not bad, 'fresh compile failed:\n' + '\n'.join(bad)
out = {}
for l in open(out_path):
    r = json.loads(l)
    out[(r['theorem'], r['idx'])] = r
rows = io.load(base)
keys = {(r['theorem'], r['idx']) for r in rows}
c = collections.Counter()
for i, r in enumerate(rows):
    n = out.get((r['theorem'], r['idx']))
    if n is None:
        c['no output'] += 1
        continue
    if r['status'] != 'unresolved':
        continue
    if n['status'] in ('necessary', 'removable'):
        if not n.get('proof_ok'):
            c['unconfirmed (proof_ok false)'] += 1
            r['reason'] = f"unconfirmed {n['status']} verdict ({tag}): {str(n.get('proof_error', ''))[:200]}"
            continue
        m = dict(r)
        m.pop('reason', None)
        for k in ('status', 'tactic', 'witness', 'derivable', 'dependent', 'proof', 'proof_ok', 'proof_rendering',
                  'proof_derivability_only', 'proof_explicit'):
            if k in n:
                m[k] = n[k]
        m['found_by'] = 'hypcheck-' + tag
        m['proofs_file'] = pdir
        rows[i] = dict(sorted(m.items()))
        c[n['status']] += 1
    else:
        r['reason'] = n.get('reason', r.get('reason'))
        c['still unresolved'] += 1
extra = [k for k in out if k not in keys]
print(dict(c), '| output rows:', len(out), '| output rows not in inventory:', len(extra), extra[:5])
if '--dry' in sys.argv:
    sys.exit()
io.backup(base, tag)
io.write_splits(rows, base)
print(collections.Counter(x['status'] for x in rows))
