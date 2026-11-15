#!/usr/bin/env python3
"""Reuse after agent waves (optional, v12): compile the agents' hand files as importable modules, so that a search-level
tool run (`exact?` sees their helper lemmas) can decide open rows with them.

Each agent hand file starts with an exact copy of the toolkit header (runs/probe/Header.lean), which defines
elaborators, so two hand files can't be imported together. Here the header is compiled once as module RUHeader and
each copy runs/reuse/mods/RU_<stem>.lean imports it instead. Files that don't start with the header are skipped.
Benchmark (iris-lean, all 73 wave files): 6 open rows decided through another file's helper, 3 of them not found
by rem_trans.py; cheap (~10 min compile, then a normal tool run).

Usage (from the workspace root): python3 scripts/hand_modules.py [PATTERN=checks/*Hand.lean] [JOBS=3]
then:  HC_EXTRA_PATH=$PWD/runs/reuse/mods scripts/run.sh 3 runs/reuse/out.jsonl --module ROOT --redo OPEN_ROWS \\
         --level search --goal removable $(sed 's/^/--import /' runs/reuse/modules.txt)
       python3 scripts/merge_tool.py runs/reuse/out.jsonl reuse<K>   (keep runs/reuse/mods: the stored proofs import it)
"""
import os, sys, glob, subprocess, concurrent.futures as cf
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hcconf

MODS = os.path.abspath('runs/reuse/mods')
CAP = ['systemd-run', '--user', '--scope', '--quiet', f'--slice={hcconf.SLICE}', '-p',
       f"MemoryMax={os.environ.get('MEM', '3G')}", '-p', 'MemorySwapMax=0', 'nice', '-n', '10']
ENV = dict(os.environ, HC_EXTRA_PATH=MODS + (':' + os.environ['HC_EXTRA_PATH'] if os.environ.get('HC_EXTRA_PATH') else ''))


def compile_mod(name):
    r = subprocess.run(CAP + [hcconf.LEAN, '-R', MODS, '-o', f'{MODS}/{name}.olean', f'{MODS}/{name}.lean'],
                       capture_output=True, text=True, env=ENV)
    return name, r.returncode, (r.stdout + r.stderr)[-400:]


def main():
    pat = sys.argv[1] if len(sys.argv) > 1 else 'checks/*Hand.lean'
    jobs = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    os.makedirs(MODS, exist_ok=True)
    H = open('runs/probe/Header.lean').read()
    open(f'{MODS}/RUHeader.lean', 'w').write(H)
    if compile_mod('RUHeader')[1]:
        sys.exit('header does not compile')
    imports = '\n'.join(l for l in H.splitlines() if l.startswith('import '))
    names, skipped = [], []
    for f in sorted(glob.glob(pat)):
        src = open(f).read()
        stem = os.path.basename(f)[:-5]
        if not src.startswith(H):
            skipped.append(stem)
            continue
        open(f'{MODS}/RU_{stem}.lean', 'w').write('import RUHeader\n' + imports + '\n' + src[len(H):])
        names.append(f'RU_{stem}')
    ok = []
    with cf.ThreadPoolExecutor(jobs) as ex:
        for name, rc, out in ex.map(compile_mod, names):
            print(name, 'ok' if rc == 0 else f'FAILED: {out[-200:]}', flush=True)
            if rc == 0:
                ok.append(name)
    open('runs/reuse/modules.txt', 'w').write(''.join(n + '\n' for n in ok))
    print(f'{len(ok)}/{len(names)} compiled -> runs/reuse/modules.txt; not starting with the header: {len(skipped)}')


if __name__ == '__main__':
    main()
