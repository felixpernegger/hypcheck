"""Cut the open rows into clusters of whole modules (path order, so neighbours share a folder), ~TARGET rows each.
Usage (from the workspace root): python3 scripts/cut_clusters.py plan [TARGET]      -> prints the cut
                                         python3 scripts/cut_clusters.py emit TARGET K C1,C2,..  -> writes
runs/waves/W<K>/todo_W<K>c<i>.jsonl for the listed cluster indices of the current cut (refuses to overwrite).
Rows carry `private` and `unlocks` (open rows a necessary verdict here decides via transitive necessity)."""
import json, sys, os, collections
sys.path.insert(0, 'scripts')
import results_io as io

def open_rows():
    rows = []; st = {}
    for b in io.BASES:
        for r in io.load(b):
            st[(r['theorem'], r['idx'])] = r['status']
            if r['status'] == 'unresolved': rows.append(dict(r, private=(b == 'private')))
    single = {}
    for e in map(json.loads, open('runs/struct/edges_all.jsonl')):
        ts = {tuple(t) for t in e['targets']}
        if len(ts) == 1: single[(e['B'], e['j'])] = next(iter(ts))
    for r in rows:
        k = (r['theorem'], r['idx']); n = 0; seen = set()
        while k in single and single[k] not in seen:
            k = single[k]; seen.add(k)
            if st.get(k) == 'unresolved': n += 1
            elif k not in st: break
        r['unlocks'] = n
    return rows

def cut(target):
    bymod = collections.defaultdict(list)
    for r in open_rows(): bymod[r['module']].append(r)
    clusters, cur = [], []
    for m in sorted(bymod):
        if cur and len(cur) + len(bymod[m]) > target * 1.25:
            clusters.append(cur); cur = []
        cur += sorted(bymod[m], key=lambda r: (r['line'], r['idx']))
        if len(cur) >= target: clusters.append(cur); cur = []
    if cur: clusters.append(cur)
    return clusters

def desc(c):
    mods = sorted({r['module'] for r in c})
    pre = os.path.commonprefix([m.split('.') for m in mods])
    return f"{len(c):4} rows {len(mods):3} modules  {'.'.join(pre) or mods[0]}  ..  {mods[-1].split('.',1)[1]}"

if __name__ == '__main__':
    mode = sys.argv[1]; target = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    cs = cut(target)
    if mode == 'plan':
        for i, c in enumerate(cs): print(i, desc(c))
        print(len(cs), 'clusters,', sum(map(len, cs)), 'rows')
    elif mode == 'emit':
        K, sel = sys.argv[3], [int(x) for x in sys.argv[4].split(',')]
        d = f'runs/waves/W{K}'; os.makedirs(d, exist_ok=True)
        for j, i in enumerate(sel):
            name = f'W{K}c{j}'; p = f'{d}/todo_{name}.jsonl'
            assert not os.path.exists(p), f'{p} exists'
            keep = ('theorem', 'user_name', 'module', 'line', 'idx', 'name', 'binder', 'dependent', 'type', 'reason', 'private', 'unlocks')
            with open(p, 'w') as f:
                for r in cs[i]: f.write(json.dumps({k: r[k] for k in keep if k in r}, ensure_ascii=False) + '\n')
            json.dump({'cut_target': target, 'cut_index': i, 'desc': desc(cs[i])}, open(f'{d}/{name}.meta.json', 'w'))
            print(name, desc(cs[i]))

# Emit from the frozen cut (runs/waves/cut120_snapshot.jsonl, made before P6b), keeping only still-open rows:
#   python3 scripts/cut_clusters.py snap K NAME_INDEX CLUSTER   e.g. snap 2 0 1  -> runs/waves/W2/todo_W2c0.jsonl
if __name__ == '__main__' and sys.argv[1] == 'snap':
    K, j, ci = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    st = {(r['theorem'], r['idx']): r['status'] for b in io.BASES for r in io.load(b)}
    rows = [r for r in map(json.loads, open('runs/waves/cut120_snapshot.jsonl')) if r['cluster'] == ci and st.get((r['theorem'], r['idx'])) == 'unresolved']
    d = f'runs/waves/W{K}'; os.makedirs(d, exist_ok=True); name = f'W{K}c{j}'; p = f'{d}/todo_{name}.jsonl'
    assert not os.path.exists(p), f'{p} exists'
    with open(p, 'w') as f:
        for r in rows: r.pop('cluster'); f.write(json.dumps(r, ensure_ascii=False) + '\n')
    json.dump({'cut_index': ci, 'rows': len(rows)}, open(f'{d}/{name}.meta.json', 'w'))
    print(name, 'cluster', ci, len(rows), 'rows')
