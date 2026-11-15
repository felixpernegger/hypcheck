"""Shared reading/writing of results/public.jsonl (public) or results/private.jsonl
(private, PRIV=True) and their per-status splits. Run scripts from the workspace root."""
import json

R = 'results/'
STATUSES = ('necessary', 'removable', 'independent', 'unresolved')
BASE = 'public'               # public rows
PRIV_BASE = 'private'


def base(priv=False):
    return PRIV_BASE if priv else BASE


def splits(priv=False):
    b = base(priv)
    return {st: f'{b}_{st}' for st in ('removable', 'unresolved', 'independent')}


SPLITS = splits()

# independence kind -> evidence in Lean (see Methods.md "Verdicts", item 4)
EVIDENCE = {
    'platform': 'both halves proved',
    'opaque-fixpoint': 'support lemma + model argument',
    'opaque-constant': 'argument only',
    'type-identity': 'argument only',
}


def load(path=R + BASE + '.jsonl'):
    return [json.loads(l) for l in open(path)]


def save(rows, path=R + BASE + '.jsonl'):
    with open(path, 'w') as f:
        for r in rows:
            f.write(json.dumps(r) + '\n')


def write_splits(rows, priv=False):
    """Rewrite public.jsonl (or private.jsonl) and every split file from `rows`."""
    assert all(r['status'] in STATUSES for r in rows), {r['status'] for r in rows} - set(STATUSES)
    save(rows, R + base(priv) + '.jsonl')
    for st, name in splits(priv).items():
        save([r for r in rows if r['status'] == st], R + name + '.jsonl')


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
