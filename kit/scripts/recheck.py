"""Recompile every stored proof file of this workspace against the analysed library.

Usage (from the workspace root), with the library checked out at the commit in Results.md and built:
    python3 scripts/recheck.py            # LANES=N parallel compiles (default 1), MEM=… per compile (default 4G)
    python3 scripts/recheck.py W1c0 bymod # only the files whose path contains one of these strings
Lean is the workspace's wrapper for the library's toolchain: scripts/hclean (set HC_LIBDIR in hc.env, then run
`scripts/hclean --refresh`), scripts/cslean (CSLib: set CSLIB_DIR) or scripts/blean (Batteries: set BATTERIES_DIR).

Compiles checks/*.lean, the public tool proofs proofs/tool/**/part_*.lean, and the private tool proofs
proofs/tool/**/bymod/**/*.lean (each with its own module as the main module, so private names resolve).
First builds what some of these files import, into tools/hcrepair/ and runs/remtrans/mods/:
- HCRepair (proof repair; imported by checks/Repair*Hand.lean),
- HCImportsM and HCHeaderM from runs/hcimports/ (the slim Mathlib imports, where that folder exists),
- RT_<path>: the proof files that checks/RemTrans*Hand.lean import, compiled as modules.
One line per file "OK|FAIL seconds file" in runs/recheck/summary.txt, full logs next to it; exit status 1 if any
file fails. This checks that Lean accepts the files; that each declaration states exactly the claimed verdict, with
standard axioms only, is checked by scripts/check_hand.py (run before every merge).
"""
import concurrent.futures
import glob
import os
import re
import shutil
import subprocess
import sys
import time

WS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if os.path.abspath(os.getcwd()) != WS:
    sys.exit(f'run this from the workspace root {WS}')
LEAN = next(os.path.join(WS, 'scripts', w) for w in ('hclean', 'cslean', 'blean')
            if os.path.exists(os.path.join(WS, 'scripts', w)))

MEM = os.environ.get('MEM', '4G')
LANES = int(os.environ.get('LANES', '1'))
OUT = 'runs/recheck'
TOOLS = os.path.abspath('tools/hcrepair')
MODS = os.path.abspath('runs/remtrans/mods')
ENV = dict(os.environ, HC_EXTRA_PATH=MODS + (':' + os.environ['HC_EXTRA_PATH'] if os.environ.get('HC_EXTRA_PATH') else ''))


def _systemd():
    try:
        return subprocess.run(['systemd-run', '--user', '--scope', '--quiet', 'true'], capture_output=True).returncode == 0
    except OSError:
        return False


CAP = (['systemd-run', '--user', '--scope', '--quiet', '-p', f'MemoryMax={MEM}', '-p', 'MemorySwapMax=0']
       if _systemd() else [])
if not CAP:
    print('note: systemd-run not available, compiling without a memory limit', file=sys.stderr)


def lean(args, log):
    """Run the library's lean (LEAN) on args, output to log; return (ok, seconds)."""
    start = time.time()
    with open(log, 'w') as f:
        r = subprocess.run(CAP + ['timeout', '3600', LEAN] + args, stdout=f, stderr=subprocess.STDOUT, env=ENV)
    text = open(log, errors='replace').read()
    ok = r.returncode == 0 and not re.search(r': error|declaration uses .sorry.', text)
    return ok, int(time.time() - start)


def build(src, outdir, name):
    """Compile src as module `name` into outdir, unless it is up to date. Compiled from a copy in outdir: lean wants
    the real file under its -R root, and some sources are symlinks into kit/."""
    olean = f'{outdir}/{name}.olean'
    if os.path.exists(olean) and os.path.getmtime(olean) >= os.path.getmtime(src):
        return True
    os.makedirs(outdir, exist_ok=True)
    copy = f'{outdir}/{name}.lean'
    if os.path.abspath(src) != os.path.abspath(copy):
        shutil.copy(src, copy)
    print(f'building {name}', flush=True)
    log = f'{OUT}/build_{name}.txt'
    ok, _ = lean(['-R', outdir, '-o', olean, '-i', f'{outdir}/{name}.ilean', copy], log)
    if not ok:
        print(f'FAIL building {name} from {src} (log: {log})', flush=True)
    return ok


def imports(path):
    return re.findall(r'^(?:public |meta |private )*import (?:all )?(\S+)', open(path, errors='replace').read(), re.M)


def rt_name(path):
    return 'RT_' + re.sub(r'\W', '_', path.removesuffix('.lean'))


def main():
    os.makedirs(OUT, exist_ok=True)
    checks = sorted(glob.glob('checks/*.lean'))
    tool, bymod = [], []
    for f in sorted(glob.glob('proofs/tool/**/*.lean', recursive=True)):
        if '/bymod/' in f:
            bymod.append(f)
        elif os.path.basename(f).startswith('part_') and not os.path.isdir(os.path.join(os.path.dirname(f), 'bymod')):
            tool.append(f)  # private runs keep their part_*.lean only as the source of bymod/
    sources = {rt_name(f): f for f in checks + tool}
    if sys.argv[1:]:
        keep = lambda fs: [f for f in fs if any(a in f for a in sys.argv[1:])]  # noqa: E731
        checks, tool, bymod = keep(checks), keep(tool), keep(bymod)
    needed = {m for f in checks + tool + bymod for m in imports(f)}
    needed |= {m for r in needed if r in sources for m in imports(sources[r])}  # what the RT_ sources import

    # 1. Modules some proof files import.
    ok = True
    if 'HCRepair' in needed:
        ok &= build('scripts/HCRepair.lean', TOOLS, 'HCRepair')
    if needed & {'HCImportsM', 'HCHeaderM'}:
        for m in ('HCImportsM', 'HCHeaderM'):  # HCHeaderM imports HCImportsM
            ok &= build(f'runs/hcimports/{m}.lean', TOOLS, m)
    for m in sorted(m for m in needed if m.startswith('RT_')):
        if m not in sources:
            print(f'FAIL: no source file for module {m}'); ok = False; continue
        ok &= build(sources[m], MODS, m)
    if not ok:
        sys.exit('a prerequisite failed to build; fix that first (is HC_LIBDIR built at the right commit?)')

    # 2. Every proof file.
    def check(f):
        args = [f]
        if f in bymod:
            args = ['-R', f[:f.index('/bymod/') + len('/bymod')], f]
        good, secs = lean(args, f"{OUT}/log_{f.replace('/', '_')}.txt")
        return f"{'OK  ' if good else 'FAIL'} {secs:5d}s {f}"

    files = checks + tool + bymod
    print(f'{len(files)} files, {LANES} lane(s), memory limit {MEM if CAP else "none"}')
    bad = 0
    with open(f'{OUT}/summary.txt', 'w') as s, concurrent.futures.ThreadPoolExecutor(LANES) as ex:
        for line in ex.map(check, files):
            print(line, flush=True); s.write(line + '\n'); s.flush()
            bad += line.startswith('FAIL')
    print(f'{len(files) - bad} OK, {bad} failed -> {OUT}/summary.txt')
    sys.exit(1 if bad else 0)


main()
