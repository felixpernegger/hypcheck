#!/usr/bin/env python3
"""P3b generator, one chunk: `¬ indep0% T i := by refute_dep` for dependent rows (from hypcheck's Std Phase 1).

Usage (from the workspace root): python3 scripts/gen_dep.py ROWS.jsonl OUT.lean VERDICTS.jsonl
OUT.lean = runs/probe/Header.lean + runs/gen/RefuteCore.lean + runs/gen/Models.lean + one theorem per row. Compiled
with scripts/lean.sh; theorems with errors are dropped and the file recompiled (≤ 6 rounds). Kept rows go to
VERDICTS.jsonl (status necessary), dropped ones to VERDICTS.jsonl.failed.jsonl. Env: HB (maxHeartbeats per theorem,
default 400000), MODE=rem (prove `indep% T i` by simp_all/grind instead: dependent rows derivable from the others),
MEM/TMO for lean.sh. Exit 3: compile killed (memory cap or timeout); exit 1: errors outside the theorems.
Measured in Std: a success costs 2-4 s, a failure 35-110 s (the search exhausts models x values x closers), so
failure-heavy chunks are slow and memory-hungry; keep chunks at ~25 rows (~10 for failure-heavy strata)."""
import json, os, re, subprocess, sys, time

rows_f, out, verd = sys.argv[1:4]
rows = [json.loads(l) for l in open(rows_f)]
header = ''.join(open(p).read().rstrip('\n') + '\n' for p in
                 ('runs/probe/Header.lean', 'runs/gen/RefuteCore.lean', 'runs/gen/Models.lean'))
HB = os.environ.get('HB', '400000')
MODE = os.environ.get('MODE', 'nec')
MARK = '/-! ## Verdicts -/'


def esc(n):  # private names: `_private.M.0.x` is written `_private.M.«0».x` in terms (Header's hcConst)
    return '.'.join(f'«{c}»' if c.isdigit() else c for c in n.split('.'))


def block(k, r):
    ty = re.sub(r'\s+', ' ', r['type']).replace('`', "'")[:80]
    t = esc(r['theorem'])
    return (f"-- `{r['theorem']}` idx {r['idx']}: {ty}\nset_option maxHeartbeats {HB} in\n"
            + (f"theorem dep_{k} : indep% {t} {r['idx']} := by\n  intros; first | (simp_all; done) | grind\n"
               if MODE == 'rem' else f"theorem dep_{k} : ¬ (indep0% {t} {r['idx']}) := by refute_dep\n"))


live = list(range(len(rows)))
for rnd in range(6):
    lines = header.rstrip('\n').split('\n') + ['', MARK]
    ranges = []
    for k in live:
        start = len(lines) + 1
        lines += [''] + block(k, rows[k]).rstrip('\n').split('\n')
        ranges.append((start, len(lines)))
    open(out, 'w').write('\n'.join(lines) + '\n')
    t = time.time()
    r = subprocess.run(['scripts/lean.sh', '-DElab.async=false', out], capture_output=True, text=True,
                       env={**os.environ, 'MEM': os.environ.get('MEM', '3G'), 'TMO': os.environ.get('TMO', '3600')})
    msgs = r.stdout + r.stderr
    errs = [int(m.group(1)) for l in msgs.split('\n') if (m := re.match(r'^[^:]+:(\d+):\d+: error', l))]
    bad = {live[j] for ln in errs for j, (a, b) in enumerate(ranges) if a <= ln <= b}
    other = [ln for ln in errs if not any(a <= ln <= b for a, b in ranges)]
    print(f'round {rnd}: {len(live)} theorems, {len(bad)} failed, {len(other)} errors outside, '
          f'exit {r.returncode}, {time.time() - t:.0f} s', flush=True)
    if other:
        print(msgs[-3000:]); sys.exit(1)
    if r.returncode != 0 and not errs:
        print(msgs[-1000:]); sys.exit(3)
    if not bad: break
    live = [k for k in live if k not in bad]
keep = set(live)
with open(verd, 'w') as f, open(verd + '.failed.jsonl', 'w') as g:
    for k, r in enumerate(rows):
        if k in keep:
            v = dict(r); v.pop('reason', None)
            v.update(status='removable', dependent=True, derivable=True, note='derivable from the independent binders (simp_all/grind)') \
                if MODE == 'rem' else v.update(status='necessary', dependent=True, note='refute_dep')
            f.write(json.dumps(v, ensure_ascii=False) + '\n')
        else:
            g.write(json.dumps(r, ensure_ascii=False) + '\n')
print(f'{len(keep)} of {len(rows)} kept -> {out}')
