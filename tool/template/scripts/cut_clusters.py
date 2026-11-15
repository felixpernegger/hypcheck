"""Cut the open rows into agent clusters (~TARGET rows each), freeze the cut, emit clusters from it.

Usage (from the workspace root):
  python3 scripts/cut_clusters.py plan [TARGET] [--by module|stem]   print the cut of the current open rows
  python3 scripts/cut_clusters.py freeze [TARGET] [--by module|stem] write it to runs/waves/cut_snapshot.jsonl
  python3 scripts/cut_clusters.py snap K J CLUSTER                   emit the still-open rows of frozen cluster
                                                                     CLUSTER as runs/waves/W<K>/todo_W<K>c<J>.jsonl
  python3 scripts/cut_clusters.py next K                             emit the next frozen cluster not emitted yet
                                                                     (J = number of clusters already in W<K>)
Freeze before the first wave and emit only from the snapshot: clusters then never overlap while rows get decided
by other clusters and by flow.

--by module (default): whole modules in path order, so neighbouring rows share definitions and models (CSLib:
  17 clusters, 0.075-0.24 agent-min per row).
--by stem: whole lemma stems (last name component, e.g. `get_insert` across HashMap/DHashMap/HashSet/...), big
  stems first, small stems (<= 3 rows) packed in module order at SMALL (default TARGET/2.5). Pays off when the
  library states one lemma for many wrapper types (Std: 0.06-0.15 agent-min per row on stem clusters, via
  generators that port one hand proof to the siblings).
Rows carry `private` and `unlocks` (open rows that a necessary verdict here decides via transitive necessity)."""
import json, sys, os, collections
sys.path.insert(0, 'scripts')
import results_io as io

W = 'runs/waves'
SNAP = f'{W}/cut_snapshot.jsonl'
KEEP = ('theorem', 'user_name', 'module', 'line', 'idx', 'name', 'binder', 'dependent', 'type', 'reason', 'private',
        'unlocks')


def statuses():
    return {(r['theorem'], r['idx']): r['status'] for b in io.BASES for r in io.load(b)}


def open_rows():
    rows = []; st = {}
    for b in io.BASES:
        for r in io.load(b):
            st[(r['theorem'], r['idx'])] = r['status']
            if r['status'] == 'unresolved': rows.append(dict(r, private=(b == 'private')))
    single = {}
    if os.path.exists('runs/struct/edges_all.jsonl'):
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


def stem(r):
    return r.get('user_name', r['theorem']).split('.')[-1]


def pack(units, target):
    out, cur = [], []
    for rs in units:
        if cur and len(cur) + len(rs) > target * 1.25:
            out.append(cur); cur = []
        cur += rs
        if len(cur) >= target: out.append(cur); cur = []
    if cur: out.append(cur)
    return out


def cut(target, by):
    rows = open_rows()
    if by == 'module':
        bym = collections.defaultdict(list)
        for r in rows: bym[r['module']].append(r)
        units = []
        for m in sorted(bym):
            rs = sorted(bym[m], key=lambda r: (r['line'], r['idx']))
            if len(rs) <= target * 1.5: units.append(rs); continue
            # a module far above the target (iris-lean: Algebra.CMRA 380 rows) becomes consecutive chunks in line
            # order; a theorem's rows stay in one chunk
            k = -(-len(rs) // target); size = -(-len(rs) // k); cur = []
            for r in rs:
                if len(cur) >= size and r['theorem'] != cur[-1]['theorem']: units.append(cur); cur = []
                cur.append(r)
            units.append(cur)
        return pack(units, target)
    bys = collections.defaultdict(list)
    for r in rows: bys[stem(r)].append(r)
    units = []
    for s, rs in bys.items():
        rs.sort(key=lambda r: (r['type'], r['theorem'], r['idx']))
        units += [rs[i:i + target] for i in range(0, len(rs), target)]
    big = sorted((u for u in units if len(u) > 3), key=lambda u: -len(u))
    small = sorted((u for u in units if len(u) <= 3), key=lambda u: (u[0]['module'], stem(u[0])))
    return pack(big, target) + pack(small, int(os.environ.get('SMALL', target / 2.5)))


def desc(c):
    mods = sorted({r['module'] for r in c})
    pre = os.path.commonprefix([m.split('.') for m in mods])
    return (f"{len(c):4} rows {len(mods):3} modules {len({stem(r) for r in c}):3} stems  "
            f"{'.'.join(pre) or mods[0]} .. {mods[-1]}")


def emit(K, j, ci, rows):
    d = f'{W}/W{K}'; os.makedirs(d, exist_ok=True); name = f'W{K}c{j}'; p = f'{d}/todo_{name}.jsonl'
    assert not os.path.exists(p), f'{p} exists'
    with open(p, 'w') as f:
        for r in rows: f.write(json.dumps({k: r[k] for k in KEEP if k in r}, ensure_ascii=False) + '\n')
    json.dump({'cut_index': ci, 'rows': len(rows), 'desc': desc(rows) if rows else ''}, open(f'{d}/{name}.meta.json', 'w'))
    os.makedirs(f'{d}/scratch_{name}', exist_ok=True)
    print(name, 'cluster', ci, desc(rows) if rows else '0 rows')


def frozen():
    snap = collections.defaultdict(list)
    for r in map(json.loads, open(SNAP)): snap[r['cluster']].append(r)
    return snap


def emitted():
    out = set()
    for dp, _, fs in os.walk(W):
        for f in fs:
            if f.endswith('.meta.json'): out.add(json.load(open(os.path.join(dp, f))).get('cut_index'))
    return out


if __name__ == '__main__':
    a = sys.argv[1:]
    by = 'module'
    if '--by' in a:
        k = a.index('--by'); by = a[k + 1]; del a[k:k + 2]
    assert by in ('module', 'stem'), by
    mode = a[0]
    if mode in ('plan', 'freeze'):
        target = int(a[1]) if len(a) > 1 else 120
        cs = cut(target, by)
        for i, c in enumerate(cs): print(i, desc(c))
        print(len(cs), 'clusters,', sum(map(len, cs)), 'rows', f'(by {by}, target {target})')
        if mode == 'freeze':
            os.makedirs(W, exist_ok=True)
            assert not os.path.exists(SNAP), f'{SNAP} exists (a cut is frozen once per scope)'
            with open(SNAP, 'w') as f:
                for i, c in enumerate(cs):
                    for r in c: f.write(json.dumps(dict({k: r[k] for k in KEEP if k in r}, cluster=i), ensure_ascii=False) + '\n')
            print('frozen ->', SNAP)
    elif mode in ('snap', 'next'):
        st = statuses(); snap = frozen()
        if mode == 'snap':
            K, j, ci = a[1], int(a[2]), int(a[3])
        else:
            K = a[1]; done = emitted()
            left = [ci for ci in sorted(snap) if ci not in done]
            if not left: sys.exit('all frozen clusters emitted')
            ci = left[0]
            d = f'{W}/W{K}'
            j = sum(1 for f in os.listdir(d) if f.startswith('todo_')) if os.path.isdir(d) else 0
        rows = [r for r in snap[ci] if st.get((r['theorem'], r['idx'])) == 'unresolved']
        for r in rows: r.pop('cluster')
        emit(K, j, ci, rows)
