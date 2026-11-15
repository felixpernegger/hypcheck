"""P7: emit tail clusters from runs/tails/open_now.jsonl (scripts/collect_tails.py) into runs/waves/T1/.
Groups are fixed below (by prior cluster and module); rows keep `prior_obstruction` and `prior_cluster`.
Usage: python3 scripts/emit_tails.py"""
import json, os
R = [json.loads(l) for l in open('runs/tails/open_now.jsonl')]
def grp(r):
    m, c = r['module'], r['prior_cluster']
    if m.startswith('Iris.BI.Updates') or c in ('W5c1', 'W5c5'): return 'T1c0'
    if c in ('W5c0', 'W5c3'): return 'T1c1'
    if c == 'W5c2': return 'T1c2'
    if m.startswith('Iris.HeapLang'): return 'T1c3'
    if m.startswith('Iris.ProgramLogic'): return 'T1c4'
    if m.startswith('Iris.Algebra') or m.startswith('Iris.Instances'): return 'T1c5'
    return None
KEEP = ('theorem', 'user_name', 'module', 'line', 'idx', 'name', 'binder', 'dependent', 'type', 'reason', 'private',
        'prior_cluster', 'prior_obstruction')
os.makedirs('runs/waves/T1', exist_ok=True)
out = {}
for r in R:
    g = grp(r)
    if g: out.setdefault(g, []).append(r)
for g, rs in sorted(out.items()):
    p = f'runs/waves/T1/todo_{g}.jsonl'
    if os.path.exists(p): print(g, 'exists, skipped'); continue
    rs.sort(key=lambda r: (r['module'], r.get('line', 0), r['idx']))
    with open(p, 'w') as f:
        for r in rs: f.write(json.dumps({k: r[k] for k in KEEP if k in r}, ensure_ascii=False) + '\n')
    json.dump({'cut_index': None, 'rows': len(rs), 'desc': 'tail ' + g}, open(f'runs/waves/T1/{g}.meta.json', 'w'))
    os.makedirs(f'runs/waves/T1/scratch_{g}', exist_ok=True)
    print(g, len(rs), sorted({r['module'] for r in rs})[:6])
