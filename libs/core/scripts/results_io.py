"""Shared reading/writing of results/init_all.jsonl and its per-status splits."""
import json

R = 'results/'
STATUSES = ('necessary', 'removable', 'independent', 'unresolved')
SPLITS = {'removable': 'init_all_removable', 'unresolved': 'init_all_unresolved',
          'independent': 'init_all_independent'}

# independence kind -> evidence in Lean (see Methods.md "Verdicts", item 4)
EVIDENCE = {
    'platform': 'both halves proved',
    'opaque-fixpoint': 'support lemma + model argument',
    'opaque-constant': 'argument only',
    'type-identity': 'argument only',
}

# Sub-category "provably independent" (status stays 'independent'): the independence itself is
# proved, by kernel-checked certificates plus a meta-result named here (see Methods.md
# "Provably independent").
PRINCIPLES = {
    'opaque-swap': 'swap certificates: T\' and ¬T\' kernel-checked with an opaque constant '
                   'replaced by two definitions (scripts/SwapCheck.lean)',
}


def load(path=R + 'init_all.jsonl'):
    return [json.loads(l) for l in open(path)]


def save(rows, path=R + 'init_all.jsonl'):
    with open(path, 'w') as f:
        for r in rows:
            f.write(json.dumps(r) + '\n')


def write_splits(rows):
    """Rewrite init_all.jsonl and every split file from `rows`."""
    assert all(r['status'] in STATUSES for r in rows), {r['status'] for r in rows} - set(STATUSES)
    save(rows)
    for st, name in SPLITS.items():
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


def mark_provably_independent(r, principle, certificate):
    """Put independent row `r` into the sub-category "provably independent"."""
    assert r['status'] == 'independent', (r['theorem'], r['idx'], r['status'])
    assert principle in PRINCIPLES, principle
    r['provably_independent'] = True
    r['independence_principle'] = principle
    r['independence_evidence'] = PRINCIPLES[principle]
    r['independence_certificate'] = certificate
