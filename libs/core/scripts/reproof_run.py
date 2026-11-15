#!/usr/bin/env python3
"""Reproof pass, step 2: for each module plan from `reproof_gen.py`, builds the copy with its
variants, compiles it with stage1 (dropping variants that have errors, in rounds, until the copy
compiles and its .olean is written), then runs `ReproofCheck.lean` on the remaining variants.

Usage: reproof_run.py OUTDIR [JOBS]    (reads OUTDIR/plans.jsonl; writes OUTDIR/results.jsonl,
OUTDIR/src/<module>.lean (final copies = stored proofs), OUTDIR/olean/, OUTDIR/logs/)
"""
import glob, json, os, re, shutil, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

LEAN = (os.environ.get('LEAN4_DIR') or sys.exit('set LEAN4_DIR to a lean4 checkout built at commit a2ec8251 (see README.md)')) + '/build/release/stage1/bin/lean'
LIB = (os.environ.get('LEAN4_DIR') or sys.exit('set LEAN4_DIR to a lean4 checkout built at commit a2ec8251 (see README.md)')) + '/build/release/stage1/lib/lean'


def make_overlay(outdir):
    """OUTDIR/overlay: symlink mirror of stage1's Init and Std; compiled copies replace their module's
    files there, so the checker can import a copy (Lean looks up all modules of a root in one dir)."""
    ov = os.path.join(outdir, 'overlay')
    if os.path.exists(ov): return ov
    os.makedirs(ov)
    for name in os.listdir(LIB):
        if name.split('.')[0] not in ('Init', 'Std'): continue
        src = os.path.join(LIB, name)
        if os.path.isdir(src): subprocess.run(['cp', '-rs', src, ov], check=True)
        else: os.symlink(src, os.path.join(ov, name))
    return ov


def install(outdir, rel):
    for f in glob.glob(os.path.join(outdir, 'olean', rel) + '.*'):
        dst = os.path.join(outdir, 'overlay', os.path.relpath(f, os.path.join(outdir, 'olean')))
        if os.path.lexists(dst): os.remove(dst)
        shutil.copy(f, dst)
HERE = os.path.dirname(os.path.abspath(__file__))


def header_end(lines):
    k = 0
    for i, l in enumerate(lines):
        s = l.strip()
        if s.startswith(('module', 'prelude', 'import ', 'public import ', 'meta import ')) or \
                re.match(r'^(public\s+)?(meta\s+)?import\b', s):
            k = i + 1
        elif s and not s.startswith(('/-', '--', '-/', '*', 'Copyright', 'Released', 'Authors')) and k:
            break
    return k


def build(lines, inserts, keep):
    hk = header_end(lines)
    by = {}
    for n, (k, t, v) in enumerate(inserts):
        if n in keep: by.setdefault(k, []).append((n, t))
    out, ranges = [], {}
    for k, l in enumerate(lines):
        if k == hk: out.append('set_option maxErrors 1000000')
        for n, t in by.get(k, []):
            start = len(out) + 1
            out += t.split('\n')
            ranges[n] = (start, len(out))
        out.append(l)
    for n, t in by.get(len(lines), []):
        start = len(out) + 1
        out += t.split('\n')
        ranges[n] = (start, len(out))
    return '\n'.join(out), ranges


def run_module(plan, outdir):
    mod = plan['module']
    rel = os.path.join(*mod.split('.'))
    src = os.path.join(outdir, 'src', rel + '.lean')
    ole = os.path.join(outdir, 'olean', rel + '.olean')
    log = os.path.join(outdir, 'logs', mod + '.log')
    for p in (src, ole, log): os.makedirs(os.path.dirname(p), exist_ok=True)
    lines = open(plan['path']).read().split('\n')
    inserts = plan['inserts']
    keep = set(range(len(inserts)))
    with open(log, 'w') as lg:
        for rnd in range(40):
            text, ranges = build(lines, inserts, keep)
            open(src, 'w').write(text)
            try:
                r = subprocess.run(['nice', '-n', '10', LEAN, '-DmaxErrors=1000000', f'--root={os.path.join(outdir, "src")}', '-o', ole, src],
                                   capture_output=True, text=True, timeout=3600)
            except subprocess.TimeoutExpired:
                lg.write(f'round {rnd}: timeout\n'); return mod, 'timeout', []
            errs = [int(m.group(1)) for l in (r.stdout + r.stderr).split('\n')
                    if (m := re.match(r'^[^:]+:(\d+):\d+: error', l))]
            bad = {n for e in errs for n, (a, b) in ranges.items() if a <= e <= b}
            outside = [e for e in errs if not any(a <= e <= b for a, b in ranges.values())]
            lg.write(f'round {rnd}: {len(errs)} errors, {len(bad)} variants dropped, {len(outside)} outside, {len(keep)} kept\n')
            # an error outside every variant: blame the nearest variant inserted before it (it may have
            # split a declaration whose end `reproof_gen.py` misjudged)
            for e in outside:
                before = [(b, n) for n, (a, b) in ranges.items() if b < e]
                if not before:
                    lg.write((r.stdout + r.stderr)[:3000]); return mod, 'copy broken', []
                bad.add(max(before)[1])
            if not errs: break
            keep -= bad
        else:
            return mod, 'too many rounds', []
    if not keep: return mod, 'ok', []
    install(outdir, rel)
    vin = os.path.join(outdir, 'logs', mod + '.variants.jsonl')
    vout = os.path.join(outdir, 'logs', mod + '.check.jsonl')
    with open(vin, 'w') as f:
        for n in sorted(keep): f.write(json.dumps(inserts[n][2]) + '\n')
    if os.path.exists(vout): os.remove(vout)
    subprocess.run([LEAN, '--run', os.path.join(HERE, 'ReproofCheck.lean'), os.path.join(outdir, 'overlay'),
                    mod, vin, vout], capture_output=True, text=True, timeout=3600)
    res = [json.loads(l) for l in open(vout)] if os.path.exists(vout) else []
    return mod, 'ok', res


def main():
    outdir = sys.argv[1]
    jobs = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    make_overlay(outdir)
    plans = [json.loads(l) for l in open(os.path.join(outdir, 'plans.jsonl'))]
    plans = [p for p in plans if p['inserts']]
    plans.sort(key=lambda p: -len(p['inserts']))
    resf = open(os.path.join(outdir, 'results.jsonl'), 'a')
    statf = open(os.path.join(outdir, 'modules.txt'), 'a')
    with ThreadPoolExecutor(jobs) as ex:
        for mod, st, res in ex.map(lambda p: run_module(p, outdir), plans):
            ok = sum(r['reproof'] == 'ok' for r in res)
            statf.write(f'{mod} {st} variants_compiled={len(res)} ok={ok}\n'); statf.flush()
            for r in res: resf.write(json.dumps(r) + '\n')
            resf.flush()


main()
