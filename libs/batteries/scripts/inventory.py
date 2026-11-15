"""Inventory summary of PropParams output (Batteries port). Usage: python3 scripts/inventory.py runs/inventory/propparams.jsonl
Writes runs/inventory/rows.jsonl: one row per Prop parameter (theorem, idx, ..., private, deprecated, alias_of, folder)."""
import json, sys, collections
rows = [json.loads(l) for l in open(sys.argv[1])]
def folder(m):
    p = m.split('.')
    if len(p) >= 3 and p[1] == 'Data': return 'Data/' + p[2]
    return p[1] if len(p) >= 2 else m
out = []
for t in rows:
    for p in t['params']:
        if not p['prop']: continue
        out.append(dict(theorem=t['name'], user_name=t['user_name'], module=t['module'], line=t['line'], idx=p['idx'],
            name=p['name'], binder=p['binder'], type=p['type'], dependent=p['dependent'], private=t['private'],
            has_pos=t['has_pos'], deprecated=t['deprecated'], deprecated_to=t['deprecated_to'], alias_of=t['alias_of'],
            folder=folder(t['module'])))
nopos = [r for r in out if not r['has_pos']]
out = [r for r in out if r['has_pos']]   # compiler-generated lemmas (inj, congr_simp, hcongr, eq_def, ...) out of scope
rows = [t for t in rows if t['has_pos']]
with open('runs/inventory/rows.jsonl', 'w') as f:
    for r in out: f.write(json.dumps(r, ensure_ascii=False) + '\n')
pub = [r for r in out if not r['private']]; prv = [r for r in out if r['private']]
print(f"theorems with Prop params: {len(rows)} ({sum(not t['private'] for t in rows)} public, {sum(t['private'] for t in rows)} private)")
print(f"Prop params: {len(out)} ({len(pub)} public, {len(prv)} private); excluded without source pos: {len(nopos)}")
for name, S in (('public', pub), ('private', prv)):
    n = len(S) or 1
    print(f"{name}: dependent {sum(r['dependent'] for r in S)} ({100*sum(r['dependent'] for r in S)/n:.1f}%), "
          f"instImplicit {sum(r['binder']=='instImplicit' for r in S)} ({100*sum(r['binder']=='instImplicit' for r in S)/n:.1f}%)")
print('\nby folder (public rows): rows / theorems / dependent / inst / deprecated')
c = collections.defaultdict(lambda: [0, set(), 0, 0, 0])
for r in pub:
    x = c[r['folder']]; x[0] += 1; x[1].add(r['theorem']); x[2] += r['dependent']; x[3] += r['binder']=='instImplicit'; x[4] += r['deprecated']
for k, x in sorted(c.items(), key=lambda kv: -kv[1][0]):
    print(f"  {k:28} {x[0]:5} {len(x[1]):5} {x[2]:5} {x[3]:5} {x[4]:5}")
dep = [r for r in out if r['deprecated']]
print(f"\ndeprecated rows: {len(dep)} in {len({r['theorem'] for r in dep})} theorems; aliases (value = constant): "
      f"{sum(1 for r in dep if r['alias_of'])} rows; target outside Batteries: "
      f"{sum(1 for r in dep if r['alias_of'] and not r['alias_of'].startswith(('Batteries',)) and r['alias_of'] not in {x['theorem'] for x in out})}")
print('non-deprecated aliases (value = constant):', sum(1 for r in out if r['alias_of'] and not r['deprecated']))
print('\nprivate rows by module:', collections.Counter(r['module'] for r in prv).most_common())
print('\ntop hypothesis types (public):')
for k, v in collections.Counter(r['type'] for r in pub).most_common(25): print(f'  {v:4} {k}')
