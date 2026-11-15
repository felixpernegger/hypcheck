"""Compare the theorem statements of two CSLib commits (two `scripts/Stmts.lean` dumps) for the theorems that have rows.
Writes OUTDIR/{same,changed,gone,fresh}.txt and OUTDIR/skip.jsonl (the unchanged theorems, for HypCheck's --skip).
The comparison is exact, so it is conservative: a renumbered hygienic binder name also counts as a change.
Usage (from the workspace root): python3 scripts/stmt_diff.py OLD.jsonl NEW.jsonl results OUTDIR"""
import json, sys, collections
old = {(d := json.loads(l))['name']: d for l in open(sys.argv[1])}
new = {(d := json.loads(l))['name']: d for l in open(sys.argv[2])}
res, out = sys.argv[3], sys.argv[4]
rows = [json.loads(l) for f in ('public', 'private') for l in open(f'{res}/{f}.jsonl')]
thms = collections.OrderedDict((r['theorem'], None) for r in rows)
gone = [t for t in thms if t not in new]
changed = [t for t in thms if t in new and (old[t]['type'], old[t]['lparams']) != (new[t]['type'], new[t]['lparams'])]
same = [t for t in thms if t in new and t not in changed]
modmoved = [t for t in same if old[t]['module'] != new[t]['module']]
fresh = [t for t in new if t not in old]
print(f'row theorems {len(thms)}: unchanged {len(same)} (module moved {len(modmoved)}), changed {len(changed)}, gone {len(gone)}')
print(f'theorems only in new build: {len(fresh)} (incl. auxiliary lemmas)')
for name, lst in (('gone', gone), ('changed', changed), ('fresh', fresh), ('same', same)):
    with open(f'{out}/{name}.txt', 'w') as f:
        f.write(''.join(t + '\n' for t in lst))
# --skip file for HypCheck: theorems whose rows are kept unchanged
with open(f'{out}/skip.jsonl', 'w') as f:
    for t in same:
        f.write(json.dumps({'theorem': t}) + '\n')
for t in gone + changed:
    print(('GONE   ' if t in gone else 'CHANGED'), t, sum(r['theorem'] == t for r in rows), 'rows')
