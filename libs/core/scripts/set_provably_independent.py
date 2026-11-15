#!/usr/bin/env python3
"""Mark the platform rows certified by certs/platform (scripts/swapcheck.sh outputs in
certs/platform/out/) as provably independent (principle `opaque-swap`). Idempotent; backs up
results/init_all.jsonl to runs/provable/ once. Run from libs/core."""
import glob, os, re, shutil, sys
sys.path.insert(0, 'scripts')
import results_io as io

os.makedirs('runs/provable', exist_ok=True)
bak = 'runs/provable/init_all_before_provable.jsonl'
if not os.path.exists(bak):
    shutil.copy(io.R + 'init_all.jsonl', bak)

certs = {}   # (theorem, idx) -> {sign: (file, decl)}
for f in glob.glob('certs/platform/out/PCert*.out'):
    txt = open(f).read()
    if '\nOK swap ' not in txt:
        sys.exit(f'failed run: {f}')
    src = 'certs/platform/' + os.path.basename(f).removesuffix('.out') + '.lean'
    for m in re.finditer(r'^OK theorem (PCert\.(pos|neg)\.(.*?)\.h(\d+)) :', txt, re.M):
        key = (m.group(3).replace('«', '').replace('»', ''), m.group(4))
        certs.setdefault(key, {})[m.group(2)] = (src, m.group(1))

rows = io.load()
n = 0
for r in rows:
    if r.get('independence') != 'platform':
        continue
    c = certs.get((r['theorem'], str(r['idx'])), {})
    if set(c) != {'pos', 'neg'}:
        sys.exit(f"no complete certificate for {r['theorem']} {r['idx']}: {c}")
    cert = f"T': {c['pos'][0]} ({c['pos'][1]}); ¬T': {c['neg'][0]} ({c['neg'][1]})"
    io.mark_provably_independent(r, 'opaque-swap', cert)
    n += 1
io.write_splits(rows)
print(f'{n} rows marked provably independent')
