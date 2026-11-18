"""Inventory of Prop-parameter rows from PropParams --all-params output.
Usage: python3 scripts/inventory.py runs/inventory/pp_public.jsonl [runs/inventory/pp_private.jsonl]
Prints rows (theorem, idx) per top-level folder, dependent share, instance hypotheses, source positions,
and the head constants of the data binders (non-Prop params) of each row's theorem, split into those
HypCheck has value generators for (Methods.md "Counterexample search") and those it has none for."""
import json, sys, collections

# Heads HypCheck v10 enumerates (hypcheck Methods.md "Counterexample search"); 'sort' = type variables
# (Nat, Bool), 'forall' = function types (constants / one-point if-then-else when non-dependent).
ENUM = {'Nat', 'Int', 'Bool', 'Prop', 'BitVec', 'Fin', 'Char', 'String', 'List', 'Array', 'Option',
        'Vector', 'UInt8', 'UInt16', 'UInt32', 'UInt64', 'Int8', 'Int16', 'Int32', 'Int64', 'Prod', 'sort',
        'Rat', 'Sum', 'Subtype', 'Sigma', 'PSigma'}
# Heads that are 'maybe' (generic structure / function values, models, synthesized instances).
MAYBE = {'forall', 'fvar'}


def load(path):
    return [json.loads(l) for l in open(path)]


def folder(mod):
    p = mod.split('.')
    return p[1] if len(p) > 1 else p[0]


def report(name, thms):
    allrows = [(t, p) for t in thms for p in t['params'] if p['prop']]
    nopos = sum(1 for t, p in allrows if t['line'] == 0)
    thms = [t for t in thms if t['line'] > 0]
    rows = [(t, p) for t in thms for p in t['params'] if p['prop']]
    print(f'== {name}: {len(thms)} theorems, {len(rows)} rows (theorem, idx) in scope; '
          f'{nopos} more rows in compiler-generated lemmas without source position (excluded, as in hypcheck)')
    if not rows:
        return
    dep = sum(p['dependent'] for t, p in rows)
    inst = [(t, p) for t, p in rows if p['binder'] == 'instImplicit']
    print(f'   dependent: {dep} ({100*dep/len(rows):.1f}%)   instance hypotheses [C ..] : {len(inst)} '
          f'({100*len(inst)/len(rows):.1f}%)')
    print('   per folder (rows / dependent / instance / theorems):')
    byf = collections.defaultdict(lambda: [0, 0, 0, set()])
    for t, p in rows:
        b = byf[folder(t['module'])]
        b[0] += 1; b[1] += p['dependent']; b[2] += p['binder'] == 'instImplicit'; b[3].add(t['name'])
    for f, (r, d, i, ts) in sorted(byf.items(), key=lambda x: -x[1][0]):
        print(f'     {f:18} {r:5} {d:5} {i:5} {len(ts):5}')
    ic = collections.Counter(p['head'] for t, p in inst)
    print('   instance-hypothesis classes:', ', '.join(f'{c} {n}' for c, n in ic.most_common(15)))
    hc = collections.Counter(p['head'] for t, p in rows)
    print('   hypothesis heads (top 25):', ', '.join(f'{c} {n}' for c, n in hc.most_common(25)))
    # data binders: non-Prop params of the theorem (other than instance args, which are synthesized)
    noval = collections.Counter(); allenum = 0; rows_by_missing = collections.Counter()
    for t, p in rows:
        data = [q for q in t['params'] if not q['prop'] and q['binder'] != 'instImplicit']
        miss = sorted({q['head'] for q in data if q['head'] not in ENUM and q['head'] not in MAYBE})
        if not miss:
            allenum += 1
        for h in miss:
            noval[h] += 1
        rows_by_missing[len(miss)] += 1
    print(f'   rows whose data binders all have value generators (incl. functions/fvar-typed): {allenum} '
          f'({100*allenum/len(rows):.1f}%)')
    print('   rows by number of value-less data-binder heads:', dict(sorted(rows_by_missing.items())))
    print('   data-binder heads without counterexample values (rows affected, top 40):')
    for h, n in noval.most_common(40):
        print(f'     {n:5}  {h}')
    return rows


if __name__ == '__main__':
    for path in sys.argv[1:]:
        report(path, load(path))
