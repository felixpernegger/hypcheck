"""Shared reading/writing of the result files and their per-status splits (run from the workspace root).
Bases: 'public' and 'private' (private theorems are analysed and merged separately). Files: results/<base>.jsonl and results/<base>_<status>.jsonl.
A results file is initialised from the inventory rows (runs/inventory/rows_<public|private>.jsonl), all unresolved."""
import json, os, shutil

R = 'results/'
STATUSES = ('necessary', 'removable', 'independent', 'unresolved')
BASES = {'public': 'runs/inventory/rows_public.jsonl', 'private': 'runs/inventory/rows_private.jsonl'}

# independence kind -> evidence in Lean (PLAYBOOK.md §1)
EVIDENCE = {
    'platform': 'both halves proved',
    'opaque-fixpoint': 'support lemma + model argument',
    'opaque-constant': 'argument only',
    'type-identity': 'argument only',
}


def path(base, status=None):
    return R + base + (f'_{status}' if status else '') + '.jsonl'


def load(base='public'):
    p = path(base)
    if not os.path.exists(p):
        rows = []
        if not os.path.exists(BASES[base]):
            return rows
        for l in open(BASES[base]):
            r = json.loads(l)
            r['status'] = 'unresolved'
            r['reason'] = 'not yet checked'
            rows.append(r)
        return rows
    return [json.loads(l) for l in open(p)]


def save(rows, p):
    with open(p, 'w') as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False) + '\n')


def backup(base, tag, d='runs/backups'):
    """Copy the base file and its splits to d/<name>_before_<tag>.jsonl; never overwrite a backup."""
    os.makedirs(d, exist_ok=True)
    for st in (None, 'removable', 'unresolved', 'independent'):
        src = path(base, st)
        if not os.path.exists(src):
            continue
        b = f"{d}/{os.path.basename(src)[:-6]}_before_{tag}.jsonl"
        assert not os.path.exists(b), f'backup {b} exists'
        shutil.copy(src, b)


def write_splits(rows, base='public'):
    """Rewrite results/<base>.jsonl and every split file from `rows`."""
    assert all(r['status'] in STATUSES for r in rows), {r['status'] for r in rows} - set(STATUSES)
    os.makedirs(R, exist_ok=True)
    save(rows, path(base))
    for st in ('removable', 'unresolved', 'independent'):
        save([r for r in rows if r['status'] == st], path(base, st))


def mark_independent(r, kind, reason=None, support=None):
    """Set row `r` (currently unresolved or independent) to status independent."""
    assert r['status'] in ('unresolved', 'independent'), (r['theorem'], r['idx'], r['status'])
    assert kind in EVIDENCE, kind
    r['status'] = 'independent'
    r['independence'] = kind
    r['independence_evidence'] = EVIDENCE[kind]
    if reason:
        r['reason'] = reason
    if support:
        r['independent_support'] = support
