#!/usr/bin/env python3
"""Check that every decided result row in every workspace points to a stored proof that exists.

Usage (from anywhere): python3 scripts/verify_rows.py

For each workspace `libs/<name>/` (git-ignored folders there are skipped), every removable, necessary or independent
row of its results files is checked:
- a row with `proofs_file` (tool proofs): the folder or file exists, and the declaration named in `proof` occurs in it;
- otherwise every `checks/…`, `certs/…` or `proofs/…` file the row mentions exists (independent rows may have none).

This is a fast consistency check of the links between results and proofs (seconds); it does not compile anything.
To recompile the proofs: `scripts/recheck_proofs.sh` in `libs/core`, `scripts/recheck.py` in the workspaces made with
the tool; the README ("Checking the proofs yourself") lists all.
Exit status 1 if any row fails.
"""
import collections
import glob
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPLIT = re.compile(r'_(removable|unresolved|independent)\.jsonl$|pairs|obstruction')
REF = re.compile(r'((?:checks|certs|proofs)/[A-Za-z0-9_./-]+?\.lean)')

_text = {}


def text(path):
    if path not in _text:
        _text[path] = re.sub('[«»]', '', open(path, errors='replace').read())
    return _text[path]


def files_of(path):
    if os.path.isfile(path):
        return [path]
    if path.rstrip('/').endswith('bymod'):
        return glob.glob(path + '/**/*.lean', recursive=True)
    return glob.glob(path + '/*.lean')


def ignored(path):
    """True for a git-ignored folder (a workspace that is not part of the published repository)."""
    r = subprocess.run(['git', '-C', ROOT, 'check-ignore', '-q', path.rstrip('/')], capture_output=True)
    return r.returncode == 0


def main():
    total = collections.Counter()
    bad = []
    for ws in sorted(glob.glob(os.path.join(ROOT, 'libs', '*', ''))):
        if ignored(ws):
            continue
        count = collections.Counter()
        for f in sorted(glob.glob(ws + 'results/**/*.jsonl', recursive=True)):
            if SPLIT.search(f):
                continue
            for line in open(f):
                r = json.loads(line)
                status = r.get('status')
                if status not in ('removable', 'necessary', 'independent'):
                    continue
                count['rows'] += 1
                pf = r.get('proofs_file')
                if pf:
                    found = files_of(ws + pf)
                    decl = r.get('proof')
                    ok = bool(found) and (not decl or not r.get('proof_ok', True)
                                          or any(re.sub('[«»]', '', decl) in text(x) for x in found))
                else:
                    refs = [ws + m for m in REF.findall(line)]
                    ok = all(os.path.exists(x) for x in refs) if refs else status == 'independent'
                if not ok:
                    count['bad'] += 1
                    bad.append((os.path.relpath(f, ROOT), r['theorem'], r['idx'], pf or r.get('tactic')))
        print(f"{os.path.relpath(ws, ROOT):28s} decided {count['rows']:6d}  problems {count['bad']}")
        total.update(count)
    print(f"TOTAL decided {total['rows']}  problems {total['bad']}")
    for b in bad[:20]:
        print('  ', b)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
