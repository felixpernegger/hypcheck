#!/usr/bin/env python3
"""P3b acceptance: check every finished gen_drive.py chunk with kept rows (check_hand.py + axioms) and merge it.

Usage (from the workspace root): python3 scripts/gen_accept.py WORKDIR [FOUND_BY]   (default found_by refute-dep)
A chunk is copied to checks/<P><chunk>Hand.lean (P = the basename of WORKDIR, e.g. runs/gen/G1 -> G1c0003Hand.lean)
with its verdicts in WORKDIR/<P><chunk>_verdicts.jsonl, and merged (public and private) only if check_hand reports
0 Lean errors, 0 not covered and standard axioms. This recompile reruns every `refute_dep` search (about the cost of
generation). Done chunks are recorded in WORKDIR/accepted.json; run flow (scripts/flow.sh) afterwards."""
import json, os, re, shutil, subprocess, sys
sys.path.insert(0, 'scripts')
import hcconf

work = sys.argv[1].rstrip('/'); fb = sys.argv[2] if len(sys.argv) > 2 else 'refute-dep'
P = os.path.basename(work); cdir = f'{work}/chunks'
accf = f'{work}/accepted.json'
acc = json.load(open(accf)) if os.path.exists(accf) else {}
for f in sorted(os.listdir(cdir)):
    if not f.endswith('_verdicts.jsonl.failed.jsonl'): continue
    ch = f[:-len('_verdicts.jsonl.failed.jsonl')]
    if ch in acc: continue
    n = sum(1 for _ in open(f'{cdir}/{ch}_verdicts.jsonl'))
    if n == 0:
        acc[ch] = 'empty'; continue
    C = P + ch
    shutil.copy(f'{cdir}/{ch}.lean', f'checks/{C}Hand.lean')
    shutil.copy(f'{cdir}/{ch}_verdicts.jsonl', f'{work}/{C}_verdicts.jsonl')
    out = subprocess.run(['systemd-run', '--user', '--scope', '--quiet', f'--slice={hcconf.SLICE}', '-p',
                          f"MemoryMax={os.environ.get('MEM', '3G')}", '-p', 'MemorySwapMax=0',
                          'python3', 'scripts/check_hand.py', f'checks/{C}Hand.lean', f'{work}/{C}_verdicts.jsonl'],
                         capture_output=True, text=True, env=dict(os.environ, HANDCHECK_AXIOMS='1')).stdout
    summ = [l for l in out.split('\n') if l.startswith(('lean errors', 'axioms:'))]
    ok = (any('lean errors: 0;' in l and 'not covered: 0' in l for l in summ)
          and any(re.match(r'axioms: \d+ standard, 0 other, 0 missing', l) for l in summ))
    print(C, n, 'rows;', ' | '.join(summ), '' if ok else '-> NOT merged')
    if ok:
        for priv in ([], ['--private']):
            r = subprocess.run(['python3', 'scripts/merge_hand.py', *priv, work, C, fb], capture_output=True, text=True)
            print('  ', r.stdout.strip().split('\n')[0] if r.returncode == 0 else 'merge FAILED: ' + r.stderr[-300:])
        acc[ch] = 'merged'
    else:
        acc[ch] = 'check failed'
    json.dump(acc, open(accf, 'w'), indent=0)
