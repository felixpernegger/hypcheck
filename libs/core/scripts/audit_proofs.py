#!/usr/bin/env python3
"""Proof audit: recompile every stored-proof file with `scripts/AuditCheck.lean` appended, then check
that every decided row (removable/necessary) of every results file is covered by a kernel-accepted
declaration whose statement is exactly its `T'` / `¬T'` / `∀ indep, Hᵢ` and whose axioms are only
propext / Classical.choice / Quot.sound (chain and twin rows: by their chain declaration plus the
verified rows they rest on).

Usage (from libs/core):
  python3 scripts/audit_proofs.py run OUTDIR [--lanes 2] [--only REGEX] [--force] [--mem 3200M]
  python3 scripts/audit_proofs.py report OUTDIR
`run` resumes: files whose checker output exists are skipped unless --force.
Per file: OUTDIR/files/<key>.out.jsonl (checker output), <key>.log (compile log), and a line in
OUTDIR/compile.tsv. `report` writes OUTDIR/rows.jsonl (one audit line per decided row) and
OUTDIR/summary.txt.
"""
import argparse, collections, concurrent.futures as cf, glob, json, os, re, shutil, subprocess, sys, time

HOME = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = (os.environ.get('LEAN4_DIR') or sys.exit('set LEAN4_DIR to a lean4 checkout built at commit a2ec8251 (see README.md)')) + '/build/release/stage1/bin/lean'
CHECKER = os.path.join(HOME, 'scripts/AuditCheck.lean')
RESULTS = ['results/init_all.jsonl', 'results/std.jsonl', 'results/lean_lake.jsonl',
           'results/private/private_all.jsonl', 'results/internal_names_and_lake_unimported.jsonl']
STD_AX = {'propext', 'Classical.choice', 'Quot.sound'}
DECIDED = ('removable', 'necessary')


def norm(s):
    """`«0»`-style all-digit components → plain digits (as Lean's numeric components print)."""
    return re.sub(r'«(\d+)»', r'\1', s)


def load_rows():
    rows = []
    for f in RESULTS:
        for l in open(os.path.join(HOME, f)):
            r = json.loads(l)
            if r['status'] in DECIDED:
                r['_src'] = f
                r['idx'] = int(r['idx'])
                rows.append(r)
    return rows


def dir_files(d):
    d = os.path.join(HOME, d)
    if d.rstrip('/').endswith('bymod'):
        return sorted(os.path.relpath(p, HOME) for p in glob.glob(d + '/**/*.lean', recursive=True))
    return sorted(os.path.relpath(p, HOME) for p in glob.glob(d + '/*.lean'))


def row_files(r):
    fs = []
    if r.get('proofs_file'):
        fs += dir_files(r['proofs_file'])
    fs += re.findall(r'\((checks/[^)\s]+\.lean)\)', r.get('tactic', ''))
    return fs


def all_files(rows):
    fs = set()
    for r in rows:
        fs.update(row_files(r))
    fs.update(os.path.relpath(p, HOME) for p in glob.glob(HOME + '/checks/*.lean')
              if not os.path.basename(p).startswith('tmp'))
    return sorted(fs)


def key_of(f):
    return f.replace('/', '__')


def bymod_root(f):
    i = f.find('/bymod/')
    return f[:i + len('/bymod')] if i >= 0 else None


def parse_source(src, vnames):
    """(modified source lines, {decl: [candidates]}, {decl: chain spec}) -- candidates as check_hand.py."""
    out, cands, chains, comment, ns = [], {}, {}, [], []
    n = 0
    for line in src.split('\n'):
        mn = re.match(r'^namespace\s+(\S+)', line)
        if mn: ns.append(mn.group(1))
        elif re.match(r'^(noncomputable\s+)?section\b', line): ns.append(None)
        elif re.match(r'^end(\s|$)', line) and ns: ns.pop()
        mc = re.match(r'^hc_nec_trans\s+(\S+)\s+(\d+)\s+(\S+)\s+(\d+)(.*)$', line)
        if mc:
            B, j, A, i, rest = mc.groups()
            rs = [[norm(R), int(k)] for R, k in re.findall(r'\(\s*(\S+)\s+(\d+)\s*\)', rest)]
            chains[norm(f'HypCheckChain.{A}.h{i}')] = {'kind': 'nec', 'a': [norm(A), int(i)], 'b': [norm(B), int(j)], 'rs': rs}
        mt = re.match(r'^hc_twin\s+(\S+)\s+(\S+)\s+(\d+)\s*$', line)
        if mt:
            T, S, i = mt.groups()
            chains[norm(f'HypCheckChain.{T}.h{i}')] = {'kind': 'twin', 'a': [norm(T), int(i)], 'b': [norm(S), int(i)], 'rs': []}
        m = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+)?(example|theorem\s+(\S+))(\s|$)', line)
        if m:
            cs = []
            for c in comment:
                for t in re.findall(r'`([^`\s]+)`', c):
                    t = norm(t)
                    cs += [v for v in vnames if v == t or v.endswith('.' + t)]
                    if '.' in t: cs.append(t)
            if m.group(2):
                last = norm(m.group(2).split('.{')[0]).split('.')[-1]
                cs += [v for v in vnames if v.split('.')[-1] == last]
            cs = list(dict.fromkeys(cs))
            if m.group(1) == 'example':
                name = f'HandCheckEx.e{n}'; n += 1
                line = line.replace('example', f'theorem {name}', 1)
            else:
                name = m.group(2).split('.{')[0]
                prefix = '.'.join(x for x in ns if x)
                if prefix and not name.startswith('_root_.'): name = prefix + '.' + name
                name = name.removeprefix('_root_.')
            if cs: cands[norm(name)] = cs
            comment = []
        elif line.startswith('--'):
            comment.append(line)
        elif line.strip() and not line.startswith(' '):
            if not line.startswith('/-') and not line.startswith('set_option'):
                comment = []
        out.append(line)
    return out, cands, chains


def prepare(f, frows, work, outdir):
    src = open(os.path.join(HOME, f)).read()
    vnames = sorted({norm(r['theorem']) for r in frows})
    lines, cands, chains = parse_source(src, vnames)
    if not any(re.match(r'^import (Lean|Lean\.Elab\.Command)\s*$', l) for l in lines):
        k = next((i for i, l in enumerate(lines) if l.startswith('import ')), 0)
        lines.insert(k, 'import Lean.Elab.Command')
    key = key_of(f)
    spec = {'rows': [[norm(r['theorem']), r['idx'], r['status']] for r in frows], 'cands': cands, 'chains': chains}
    specp = os.path.join(work, key + '.spec.json')
    json.dump(spec, open(specp, 'w'))
    outp = os.path.join(outdir, 'files', key + '.out.jsonl')
    tail = open(CHECKER).read()
    lines += ['', tail, f'set_option maxHeartbeats 0 in', f'#eval HypAudit.run "{specp}" "{outp}.tmp"', '']
    root = bymod_root(f)
    if root:
        wroot = os.path.join(work, key + '_root')
        copy = os.path.join(wroot, os.path.relpath(f, root))
        os.makedirs(os.path.dirname(copy), exist_ok=True)
        args = ['-R', wroot, copy]
    else:
        copy = os.path.join(work, key + '.lean')
        args = [copy]
    open(copy, 'w').write('\n'.join(lines))
    return outp, args


def compile_one(f, frows, outdir, work, mem):
    outp, args = prepare(f, frows, work, outdir)
    logp = os.path.join(outdir, 'files', key_of(f) + '.log')
    if os.path.exists(outp + '.tmp'): os.unlink(outp + '.tmp')
    t0 = time.time()
    cmd = ['systemd-run', '--user', '--scope', '--quiet', '--slice=audit.slice', '-p', f'MemoryMax={mem}',
           '-p', 'MemorySwapMax=0', 'timeout', '5400', 'nice', '-n', '10', LEAN] + args
    with open(logp, 'w') as lf:
        rc = subprocess.run(cmd, stdout=lf, stderr=subprocess.STDOUT).returncode
    secs = int(time.time() - t0)
    log = open(logp).read()
    errs = len(re.findall(r': error', log))
    sorry = len(re.findall(r"declaration uses [`']sorry", log))
    got = os.path.exists(outp + '.tmp')
    if got: os.replace(outp + '.tmp', outp)
    status = 'ok' if got and rc == 0 else ('checked-with-errors' if got else ('killed' if rc in (137, -9) else f'failed-rc{rc}'))
    return f, rc, errs, sorry, secs, status


def cmd_run(a):
    outdir = os.path.abspath(a.outdir)
    os.makedirs(outdir + '/files', exist_ok=True)
    work = os.path.join(outdir, 'work'); os.makedirs(work, exist_ok=True)
    rows = load_rows()
    byfile = collections.defaultdict(list)
    for r in rows:
        for f in set(row_files(r)): byfile[f].append(r)
    files = all_files(rows)
    if a.only: files = [f for f in files if re.search(a.only, f)]
    if a.files: files = a.files.split(',')
    todo = [f for f in files if a.force or not os.path.exists(os.path.join(outdir, 'files', key_of(f) + '.out.jsonl'))]
    todo.sort(key=lambda f: -os.path.getsize(os.path.join(HOME, f)))
    print(f'{len(files)} files, {len(todo)} to compile, {a.lanes} lanes', flush=True)
    tsv = open(os.path.join(outdir, 'compile.tsv'), 'a')
    done = 0
    with cf.ThreadPoolExecutor(a.lanes) as ex:
        futs = [ex.submit(compile_one, f, byfile.get(f, []), outdir, work, a.mem) for f in todo]
        for fu in cf.as_completed(futs):
            f, rc, errs, sorry, secs, status = fu.result()
            done += 1
            tsv.write(f'{f}\t{status}\t{rc}\t{errs}\t{sorry}\t{secs}\t{time.strftime("%H:%M:%S")}\n'); tsv.flush()
            print(f'[{done}/{len(todo)}] {status} rc={rc} errors={errs} sorry={sorry} {secs}s {f}', flush=True)


def cmd_report(a):
    outdir = os.path.abspath(a.outdir)
    rows = load_rows()
    files = all_files(rows)
    # last compile status per file
    comp = {}
    if os.path.exists(outdir + '/compile.tsv'):
        for l in open(outdir + '/compile.tsv'):
            p = l.rstrip('\n').split('\t')
            comp[p[0]] = p[1:]
    direct = collections.defaultdict(list)   # (T, i, pol) -> [(file, decl, kind, axok)]
    chains = collections.defaultdict(list)   # (A, i) -> [(file, decl, chain, axok)]
    nonstd = []                               # (file, decl, axioms) for every local theorem
    timeouts = {}
    missing = []
    for f in files:
        p = os.path.join(outdir, 'files', key_of(f) + '.out.jsonl')
        if not os.path.exists(p): missing.append(f); continue
        ax = {}
        for l in open(p):
            if not l.strip(): continue
            r = json.loads(l)
            if 'fallback' in r:
                timeouts[f] = r['timeouts']
                for fb in r['fallback']:
                    d = norm(fb['d'])
                    for T, i, pol, kind in fb['m']:
                        direct[(norm(T), i, pol)].append((f, d, kind, ax.get(d, False), 'fallback'))
                continue
            d = norm(r['d']); ok = set(r['ax']) <= STD_AX; ax[d] = ok
            if not ok: nonstd.append((f, d, r['ax']))
            for T, i, pol, kind in r['m']:
                direct[(norm(T), i, pol)].append((f, d, kind, ok, 'cand'))
            if r.get('chain'):
                c = r['chain']
                chains[(norm(c['a'][0]), c['a'][1])].append((f, d, c, ok))
    key = lambda r: (norm(r['theorem']), r['idx'])
    status = {key(r): r['status'] for r in rows}
    res = {}
    for r in rows:
        k = key(r); pol = r['status']; pf = set(row_files(r))
        hits = direct.get((k[0], k[1], pol), [])
        good = [h for h in hits if h[3] and (pol == 'removable' or h[2] in ('plain', 'full'))]
        if good:
            res[k] = {'audit': 'ok' if any(h[0] in pf for h in good) else 'ok-other-file',
                      'by': [h[:3] for h in good[:3]]}
        elif any(h[3] for h in hits):
            res[k] = {'audit': 'narrow-only', 'by': [h[:3] for h in hits[:3]]}
        elif hits:
            res[k] = {'audit': 'nonstandard-axioms', 'by': [h[:3] for h in hits[:3]]}
        else:
            res[k] = {'audit': 'uncovered'}
    # chain / twin rows: fixpoint over their dependencies
    changed = True
    while changed:
        changed = False
        for r in rows:
            k = key(r)
            if res[k]['audit'] in ('ok', 'ok-other-file'): continue
            for f, d, c, axok in chains.get(k, []):
                if not (axok and c.get('ok')): continue
                if c['kind'] == 'nec':
                    if r['status'] != 'necessary': continue
                    deps = [((norm(c['b'][0]), c['b'][1]), 'necessary')] + [((norm(R), kk), 'removable') for R, kk in c['rs']]
                else:
                    deps = [((norm(c['b'][0]), c['b'][1]), r['status'])]
                if all(status.get(dk) == ds and res.get(dk, {}).get('audit') in ('ok', 'ok-other-file', 'ok-chain') for dk, ds in deps):
                    res[k] = {'audit': 'ok-chain', 'by': [(f, d, c['kind'])], 'deps': [list(dk) for dk, _ in deps]}
                    changed = True
                    break
            else:
                if chains.get(k) and res[k]['audit'] == 'uncovered':
                    res[k] = {'audit': 'chain-unverified', 'chains': [(f, d, c, axok) for f, d, c, axok in chains[k]]}
    with open(outdir + '/rows.jsonl', 'w') as o:
        for r in rows:
            k = key(r)
            o.write(json.dumps({'theorem': r['theorem'], 'idx': r['idx'], 'status': r['status'], 'results': r['_src'],
                                'found_by': r.get('found_by'), 'files': sorted(set(row_files(r))), **res[k]}) + '\n')
    S = []
    S.append(f'Proof audit report ({time.strftime("%Y-%m-%d %H:%M")})')
    S.append(f'files: {len(files)}; with checker output: {len(files) - len(missing)}; missing: {len(missing)}')
    cs = collections.Counter(v[0] for v in comp.values())
    S.append(f'compile status: {dict(cs)}')
    bad = [(f, v) for f, v in comp.items() if v[0] != 'ok' or v[2] != '0' or v[3] != '0']
    S.append(f'files with errors / sorry warnings / failures: {len(bad)}')
    for f, v in sorted(bad): S.append(f'   {f}: status={v[0]} rc={v[1]} errors={v[2]} sorry={v[3]}')
    for f in missing: S.append(f'   NO OUTPUT: {f}')
    S.append(f'local theorems with non-standard axioms: {len(nonstd)}')
    for f, d, ax in nonstd[:200]: S.append(f'   {f}: {d} {ax}')
    to = {f: t for f, t in timeouts.items() if t}
    S.append(f'files with defeq timeouts: {len(to)} ({sum(to.values())} timeouts)')
    for f, t in sorted(to.items()): S.append(f'   {f}: {t}')
    for src in RESULTS:
        c = collections.Counter(res[key(r)]['audit'] for r in rows if r['_src'] == src)
        S.append(f'{src}: {sum(c.values())} decided rows: {dict(c)}')
    c = collections.Counter(res[key(r)]['audit'] for r in rows)
    S.append(f'ALL: {sum(c.values())} decided rows: {dict(c)}')
    S.append('rows not ok (first 300):')
    n = 0
    for r in rows:
        v = res[key(r)]
        if v['audit'] in ('ok', 'ok-other-file', 'ok-chain'): continue
        n += 1
        if n <= 300: S.append(f"   {v['audit']}: {r['theorem']} idx {r['idx']} {r['status']} ({r.get('found_by')}; {sorted(set(row_files(r)))[:2]})")
    open(outdir + '/summary.txt', 'w').write('\n'.join(S) + '\n')
    print('\n'.join(S[:40]))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    r = sp.add_parser('run'); r.add_argument('outdir'); r.add_argument('--lanes', type=int, default=2)
    r.add_argument('--only'); r.add_argument('--force', action='store_true'); r.add_argument('--mem', default='3200M')
    r.add_argument('--files', help='comma-separated explicit file list (e.g. controls), instead of all proof files')
    p = sp.add_parser('report'); p.add_argument('outdir')
    a = ap.parse_args()
    {'run': cmd_run, 'report': cmd_report}[a.cmd](a)


main()
