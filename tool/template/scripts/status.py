"""Dashboard: verdict counts per result file, per top folder and per source. Run before and after every wave.
Usage (from the workspace root): python3 scripts/status.py [--save]   (--save: snapshot runs/status/status_<time>.json)"""
import json, sys, os, collections, time
sys.path.insert(0, 'scripts')
import results_io as io

ST = io.STATUSES
snap = {}
for base in io.BASES:
    rows = io.load(base)
    if not rows: continue
    tot = collections.Counter(r['status'] for r in rows)
    fold = collections.defaultdict(collections.Counter)
    src = collections.Counter(r.get('found_by', '-') for r in rows if r['status'] in ('necessary', 'removable'))
    for r in rows:
        p = r['module'].split('.'); fold[p[1] if len(p) > 1 else p[0]][r['status']] += 1
    print(f'== {base}: {len(rows)} rows  ' + '  '.join(f'{s} {tot[s]}' for s in ST))
    for f, c in sorted(fold.items(), key=lambda x: -sum(x[1].values())):
        print(f'   {f:24} ' + ' '.join(f'{c[s]:6}' for s in ST))
    print('   decided by:', dict(src.most_common()))
    snap[base] = {'total': dict(tot), 'folders': {f: dict(c) for f, c in fold.items()}, 'found_by': dict(src)}
allc = collections.Counter()
for b in snap: allc.update(snap[b]['total'])
n = sum(allc.values())
if n:
    dec = allc['necessary'] + allc['removable'] + allc['independent']
    print(f'TOTAL {n} rows: ' + ' / '.join(f'{allc[s]} {s}' for s in ST) + f'  ({100 * dec / n:.1f}% decided)')
if '--save' in sys.argv:
    os.makedirs('runs/status', exist_ok=True)
    p = time.strftime('runs/status/status_%Y%m%d_%H%M.json')
    json.dump(snap, open(p, 'w'), indent=1); print('saved', p)
