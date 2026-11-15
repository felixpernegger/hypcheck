#!/usr/bin/env python3
"""Summarize the SwapCheck runs of certs/platform: every platform row must have a kernel-checked
`S` in one platform environment and `¬S` in the other. Run from libs/core."""
import json, glob, re, collections
got = collections.defaultdict(dict)   # (theorem, idx) -> {k: sign}
for f in glob.glob('certs/platform/out/PCert*.out'):
    k = int(re.search(r'PCert(\d+)_', f).group(1))
    txt = open(f).read()
    if '\nOK swap ' not in txt: print('FAILED RUN', f); continue
    for m in re.finditer(r'^OK theorem PCert\.(pos|neg)\.(.*)\.h(\d+) :', txt, re.M):
        got[(m.group(2).replace('«', '').replace('»', ''), m.group(3))][k] = m.group(1)
rows = [r for r in map(json.loads, open('results/init_all.jsonl')) if r.get('independence') == 'platform']
ok = bad = 0
for r in rows:
    g = got.get((r['theorem'], str(r['idx'])), {})
    if sorted(g.values()) == ['neg', 'pos'] and len(g) == 2: ok += 1
    else: bad += 1; print('MISSING/INCONSISTENT', r['theorem'], r['idx'], g)
print(f'{ok}/{len(rows)} platform rows certified (S in one environment, ¬S in the other); {bad} not')
