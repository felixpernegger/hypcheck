#!/usr/bin/env python3
"""Reproof pass, step 1: copies library modules and inserts, after each theorem with unresolved
hypotheses, one variant per hypothesis: the same declaration (same proof text) with that binder
deleted, named `<name>_hcdrop<idx>`. Binders that come from `variable` lines are dropped with
`omit … in`. Variants carry no attributes, so they don't change later proofs.

Usage: reproof_gen.py UNRESOLVED.jsonl OUTDIR [MODULE_PREFIX ...]
Writes OUTDIR/plans.jsonl: per module the source path and the variants to insert (line, text, record);
`reproof_run.py` builds, compiles and checks the copies.
"""
import json, os, re, sys, collections

SRC = (os.environ.get('LEAN4_DIR') or sys.exit('set LEAN4_DIR to a lean4 checkout built at commit a2ec8251 (see README.md)')) + '/src'
OPEN, CLOSE = '([{⦃', ')]}⦄'
DECL = re.compile(r'\b(theorem|instance)\s+(?:\(priority\s*:=\s*[^)]*\)\s*)?(?:([^\s\[\(\{⦃:]+)(?=[\s\[\(\{⦃:]))?')
CONT = re.compile(r'^(\||where\b|termination_by\b|decreasing_by\b|\s|$)')


def decl_end(lines, start):
    """Index of the first line after the declaration starting at `start` (0-based)."""
    k = start + 1
    depth = 0  # block comments
    while k < len(lines):
        l = lines[k]
        if depth == 0 and not CONT.match(l):
            break
        depth += l.count('/-') - l.count('-/')
        k += 1
    while k > start + 1 and lines[k - 1].strip() == '':
        k -= 1
    return k


def split_binders(text, pos):
    """Binder groups `(start, end)` from `pos` until the type colon; returns (groups, colon_pos)."""
    groups = []
    i = pos
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
        elif c in OPEN:
            depth, j = 0, i
            while j < len(text):
                if text[j] in OPEN: depth += 1
                elif text[j] in CLOSE:
                    depth -= 1
                    if depth == 0: break
                j += 1
            groups.append((i, j + 1))
            i = j + 1
        else:
            return groups, i
    return groups, i


def norm(s):
    s = re.sub(r'\s+', ' ', s).strip()
    return re.sub(r'\b(?:[A-Za-z_][\w!?]*\.)+([A-Za-z_][\w!?]*)', r'\1', s)


def drop_binder(sig, groups, h):
    """New signature text without hypothesis `h`, or None if it isn't in the signature."""
    name, ty = h['name'], h['type']
    for a, b in groups:
        inner = sig[a + 1:b - 1]
        m = re.match(r'^\s*([^:]*?)\s*:(?!=)(.*)$', inner, re.S)
        if m and sig[a] != '[':
            names = m.group(1).split()
            if name in names:
                names.remove(name)
                if not names: return sig[:a] + sig[b:]
                return sig[:a] + sig[a] + ' '.join(names) + ' :' + m.group(2) + sig[b - 1] + sig[b:]
        if sig[a] == '[' and h['binder'] == 'instImplicit':
            if m and m.group(1).strip() == name:
                return sig[:a] + sig[b:]
            if norm(inner) == norm(ty) or (m and norm(m.group(2)) == norm(ty)):
                return sig[:a] + sig[b:]
    return None


def main():
    inp, out = sys.argv[1], sys.argv[2]
    prefixes = sys.argv[3:] or ['']
    hyps = collections.defaultdict(list)
    for l in open(inp):
        r = json.loads(l)
        if r.get('dependent') or not any(r['module'].startswith(p) for p in prefixes): continue
        hyps[r['module']].append(r)
    plans = open(os.path.join(out, 'plans.jsonl'), 'w')
    stats = collections.Counter()
    for mod, hs in sorted(hyps.items()):
        path = os.path.join(SRC, *mod.split('.')) + '.lean'
        if not os.path.exists(path): stats['no source'] += len(hs); continue
        lines = open(path).read().split('\n')
        inserts = collections.defaultdict(list)
        bytheorem = collections.defaultdict(list)
        for h in hs: bytheorem[(h['theorem'], h['line'])].append(h)
        for (thm, line), hl in bytheorem.items():
            s = line - 1
            short = thm.split('.')[-1]
            m = DECL.search(lines[s]) if 0 <= s < len(lines) else None
            if not m or (m.group(1) == 'theorem' and (m.group(2) or '').split('.')[-1] != short) \
                    or (m.group(1) == 'instance' and m.group(2) and m.group(2).split('.')[-1] != short):
                stats['decl not found'] += len(hl); continue
            e = decl_end(lines, s)
            text = '\n'.join([lines[s][m.start():]] + lines[s + 1:e])
            nm_end = m.end() - m.start()
            groups, colon = split_binders(text, nm_end)
            if colon >= len(text) or text[colon] != ':':
                stats['no type colon'] += len(hl); continue
            sig, rest = text[nm_end:colon], text[colon:]
            gs = [(a - nm_end, b - nm_end) for a, b in groups]
            for h in hl:
                new = drop_binder(sig, gs, h)
                pre = ''
                if new is None:
                    if '✝' in h['type'] or '⋯' in h['type'] or re.search(r'\?\w*\.\d', h['type']):
                        stats['variable binder, unprintable'] += 1; continue
                    pre = (f"omit [{h['type']}] in\n" if h['binder'] == 'instImplicit'
                           else f"omit {h['name']} in\n")
                    new = sig
                    stats['omit'] += 1
                else:
                    stats['signature'] += 1
                vname = f"_root_.{thm}_hcdrop{h['idx']}"
                rec = {'theorem': thm, 'idx': h['idx'], 'module': mod, 'variant': thm + f"_hcdrop{h['idx']}"}
                inserts[e].append((f"\nset_option maxHeartbeats 100000 in\n{pre}theorem {vname}{new}{rest}\n", rec))
        plan = {'module': mod, 'path': path, 'inserts': [[k, t, v] for k, lst in inserts.items() for t, v in lst]}
        plans.write(json.dumps(plan) + '\n')
    print(dict(stats))


main()
