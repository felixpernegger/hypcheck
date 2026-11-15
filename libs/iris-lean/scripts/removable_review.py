"""P7: write results/removable_review.md: every removable row with a one-line reason and its proof location,
grouped by module; joint-removal pairs from results/removable_pairs.jsonl; independent rows.
Reasons come from the agents' verdict files (`note`), else from `found_by`.
Usage (from the workspace root): python3 scripts/removable_review.py"""
import json, glob, sys, collections
sys.path.insert(0, 'scripts'); import results_io as io

notes = {}
for f in sorted(glob.glob('runs/probe/*_verdicts.jsonl') + glob.glob('runs/waves/*/*_verdicts.jsonl')):
    for l in open(f):
        try: v = json.loads(l)
        except Exception: continue
        if v.get('status') == 'removable' and v.get('note'): notes[(v['theorem'], v['idx'])] = v['note']
AUTO = {'unused-proof': "unused in the library's own proof (directly or transitively); stored proof `drop_unused%`",
        'inst-derivable': 'derivable by instance resolution from the other binders',
        'rem-transitive': 'only passed on to removable hypotheses of other theorems (removable by transitivity)'}

def one(s, n=220):
    s = ' '.join(str(s).split())
    return s if len(s) <= n else s[:n - 1] + '…'

rows = [dict(r, private=(b == 'private')) for b in io.BASES for r in io.load(b)]
rem = [r for r in rows if r['status'] == 'removable']
ind = [r for r in rows if r['status'] == 'independent']
pairs = [json.loads(l) for l in open('results/removable_pairs.jsonl')] if glob.glob('results/removable_pairs.jsonl') else []

out = ['# Removable hypotheses in iris-lean: review list', '',
       f'{len(rem)} removable hypotheses ({sum(r["private"] for r in rem)} in private theorems) in '
       f'{len({r["theorem"] for r in rem})} theorems. Each has a stored, kernel-checked proof of the theorem without it '
       '(file and declaration in the last column; standard axioms only). "Derivable" means the hypothesis itself '
       'follows from the other binders, so it can never fail where the theorem applies; otherwise it is just unneeded. '
       'Removing a hypothesis from a public lemma breaks callers that pass it explicitly: these are candidates, '
       'not patches.', '']
bym = collections.defaultdict(list)
for r in rem: bym[r['module']].append(r)
for m in sorted(bym):
    out += [f'## {m}', '', '| Theorem | # | Hypothesis | Derivable | Why removable | Proof |', '|---|---|---|---|---|---|']
    for r in sorted(bym[m], key=lambda r: (r.get('line', 0), r['theorem'], r['idx'])):
        fb = r.get('found_by') or ''
        why = notes.get((r['theorem'], r['idx'])) or AUTO.get(fb, '') or (
            f"HypCheck proved the theorem without it by `{r.get('tactic', '')}`" if fb.startswith('hypcheck') else r.get('tactic', ''))
        name = r['theorem'].replace('_private.', '(private) ')
        typ = one(r.get('type', ''), 70).replace('|', '\\|')
        out.append(f'| `{name}` | {r["idx"]} | `{r.get("name", "")} : {typ}` | {"yes" if str(r.get("derivable")).lower() == "true" else ""} | '
                   f'{one(why).replace("|", chr(92) + "|")} | `{r.get("proof_file", "")}` {r.get("proof_decl", "")} |')
    out.append('')
if pairs:
    jr = [p for p in pairs if p['status'] == 'jointly_removable']
    out += ['## Joint removal', '', f'{len(pairs)} pairs of individually removable hypotheses checked '
            f'(`checks/J*Hand.lean`, `scripts/check_pairs.py`): {len(jr)} jointly removable, {len(pairs) - len(jr)} not.', '',
            '| Theorem | Pair | Verdict | Reason |', '|---|---|---|---|']
    for p in sorted(pairs, key=lambda p: (p['theorem'], p['idx'])):
        out.append(f'| `{p["theorem"]}` | {p["idx"][0]}, {p["idx"][1]} | {"jointly" if p["status"] == "jointly_removable" else "not jointly"} | {one(p.get("reason", "")).replace("|", chr(92) + "|")} |')
    out.append('')
if ind:
    out += ['## Independent (argued, not certified)', '', '| Theorem | # | Kind | Argument |', '|---|---|---|---|']
    for r in ind:
        out.append(f'| `{r["theorem"]}` | {r["idx"]} | {r.get("independence", "")} | {one(r.get("reason", "")).replace("|", chr(92) + "|")} |')
    out.append('')
open('results/removable_review.md', 'w').write('\n'.join(out) + '\n')
missing = [r for r in rem if not (notes.get((r['theorem'], r['idx'])) or AUTO.get(r.get('found_by')) or (r.get('found_by') or '').startswith('hypcheck'))]
print(f'results/removable_review.md: {len(rem)} removable, {len(pairs)} pairs, {len(ind)} independent; '
      f'{len(missing)} rows without a recorded reason')
for r in missing: print('  no reason:', r['theorem'], r['idx'], r.get('found_by'))
