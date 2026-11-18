"""Rows (theorem, idx) from PropParams --all-params output, restricted to HC_MODULES and to declarations with a
source position (compiler-generated lemmas such as `inj`, `congr_simp`, `match_k.congr_eq_k` have none).
Usage (from the workspace root): python3 scripts/make_rows.py runs/inventory/pp_public.jsonl runs/inventory/rows_public.jsonl"""
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hcconf
src, dst = sys.argv[1], sys.argv[2]
n = nopos = out_scope = 0
with open(dst, 'w') as f:
    for t in map(json.loads, open(src)):
        props = [p for p in t['params'] if p['prop']]
        if not hcconf.in_scope(t['module']):
            out_scope += len(props); continue
        if t['line'] == 0:
            nopos += len(props); continue
        for p in props:
            f.write(json.dumps({'theorem': t['name'], 'user_name': t.get('user_name', t['name']), 'module': t['module'],
                                'line': t['line'], 'idx': p['idx'], 'name': p['name'], 'binder': p['binder'],
                                'dependent': p['dependent'], 'type': p['type']}, ensure_ascii=False) + '\n')
            n += 1
print(f'{n} rows -> {dst}; excluded: {nopos} without source position, {out_scope} outside HC_MODULES')
