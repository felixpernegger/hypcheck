"""Recompile the stored proofs of a private-theorem run under each theorem's own module name.
Usage (from the workspace root): python3 runs/priv/compile_priv.py OUT.proofs
Splits OUT.proofs/part_*.lean by the module in each block's `-- _private.<Module>.0.…` header into
OUT.proofs/bymod/<Module/Path>.lean and compiles each with `lean -R OUT.proofs/bymod` (memory-capped),
so the file's main module is the theorem's module and its private names resolve; log in bymod.log."""
import glob, os, re, subprocess, sys, collections
pdir = sys.argv[1].rstrip('/'); root = pdir + '/bymod'
header = None; blocks = collections.defaultdict(list)
for f in sorted(glob.glob(pdir + '/part_*.lean')):
    src = open(f).read()
    k = src.index('/-! Proofs emitted by HypCheck.lean')
    k = src.index('\n', k) + 1
    header = header or src[:k]
    cur = None
    for line in src[k:].splitlines(keepends=True):
        m = re.match(r'-- (\S+), hypothesis \d+: ', line)
        if m:
            n = m.group(1)
            mm = re.match(r'_private\.(.+?)\.0\.', n)
            cur = mm.group(1) if mm else '_public'
        if cur: blocks[cur].append(line)
sys.path.insert(0, "scripts")
import hcconf
lean = hcconf.LEAN
log = open(pdir + '/bymod.log', 'w'); bad = 0
for mod, ls in sorted(blocks.items()):
    path = os.path.join(root, *mod.split('.')) + '.lean'
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, 'w').write(header + ''.join(ls))
    r = subprocess.run(hcconf.cap(mem='2G', slice=False, timeout=900) + [lean, '-R', root, path], capture_output=True, text=True)
    err = [l for l in (r.stdout + r.stderr).splitlines() if 'error' in l]
    ok = r.returncode == 0 and not err
    bad += not ok
    log.write(f"{'OK  ' if ok else 'FAIL'} {mod}\n" + ''.join(f'    {l}\n' for l in err[:5]))
log.close()
print(f'{len(blocks)} module files, {bad} failed -> {pdir}/bymod.log')
