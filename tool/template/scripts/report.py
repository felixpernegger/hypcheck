"""Human-readable summary of the workspace's results: writes report.md and prints a short version.
Usage (from the workspace root): python3 scripts/report.py [OUT.md]   (default report.md)"""
import collections, datetime, json, os, re, sys
sys.path.insert(0, 'scripts')
import hcconf
import results_io as io

OUT = sys.argv[1] if len(sys.argv) > 1 else 'report.md'
BRACKETS = {'explicit': '()', 'implicit': '{}', 'instImplicit': '[]', 'strictImplicit': '⦃⦄'}
WHY = {  # found_by -> why the hypothesis is removable, in words
    'unused-proof': "the library's own proof never uses it",
    'inst-derivable': 'instance resolution derives it from the other hypotheses',
    'proof-repair': "the library's proof, repaired to work without it",
    'rem-transitive': 'the proof only passes it on to hypotheses that are themselves removable',
    'twin': 'same statement as a theorem whose hypothesis is removable',
}
NEC = {
    'nec-transitive': 'by transitivity (the proof passes it on to a necessary hypothesis of another theorem)',
    'twin': 'as copies of a theorem with the same statement',
    'refute-dep': 'by a counterexample from the generated `refute_dep` tactic',
    'hand': 'by a counterexample written in an agent pass',
}


def why(r):
    f = r.get('found_by', '')
    if f in WHY:
        return WHY[f]
    if f == 'hand':
        return 'proof written in an agent pass' + (f": {r['hand_note']}" if r.get('hand_note') else '')
    if f.startswith('hypcheck-'):
        t = r.get('tactic', '')
        return f'the statement without it is proved by `{t}`' if t else 'proved by a tactic'
    return f or '?'


def cell(s):
    return ' '.join(s.split()).replace('|', '\\|')


def proof(r):
    f = r.get('proofs_file') or r.get('proof_file')
    if not f:
        m = re.search(r'checks/\S+?\.lean', r.get('tactic', ''))
        f = m.group(0) if m else None
    if f and os.path.isdir(f):  # a tool run: the declaration is in one of its part files
        f = f.rstrip('/') + '/part_*.lean'
    d = r.get('proof') or r.get('proof_decl')
    return f'`{f}`' + (f' (`{d}`)' if d else '') if f else '?'


def hyp(r):
    o, c = BRACKETS.get(r.get('binder'), '()')
    t = ' '.join(r.get('type', '?').split())
    return f'`{o}{r.get("name", "?")} : {t}{c}`'.replace('|', '\\|')


rows = {b: io.load(b) for b in io.BASES}
tot = collections.Counter(r['status'] for b in rows for r in rows[b])
n = sum(tot.values())
rem = sorted((r for b in rows for r in rows[b] if r['status'] == 'removable'),
             key=lambda r: (r['module'], r.get('line', 0), r['idx']))
nec_by = collections.Counter(
    'by a counterexample found by the tool' if r.get('found_by', '').startswith('hypcheck-') else
    NEC.get(r.get('found_by'), r.get('found_by') or '?') for b in rows for r in rows[b] if r['status'] == 'necessary')

L = [f'# Hypothesis check: {hcconf.NAME}', '',
     f'Library `{hcconf.LIBDIR}`, modules `{", ".join(hcconf.MODULES)}`; report of '
     f'{datetime.datetime.now().strftime("%Y-%m-%d %H:%M")}.', '',
     'Each Prop-valued hypothesis of each theorem is checked on its own. **Removable**: the theorem stays true '
     'without it (a Lean proof of the weakened statement is stored). **Necessary**: without it the theorem is false '
     '(a Lean proof of the negation, i.e. a counterexample, is stored). **Unresolved**: the mechanical checks decided '
     'neither.', '',
     '| Hypotheses | Necessary | Removable | Independent | Unresolved |', '|---|---|---|---|---|',
     f'| {n} | {tot["necessary"]} | {tot["removable"]} | {tot["independent"]} | {tot["unresolved"]} |', '']
if rows.get('private'):
    p = collections.Counter(r['status'] for r in rows['private'])
    L += [f'Of these, {sum(p.values())} hypotheses belong to private theorems '
          f'({p["removable"]} removable, {p["unresolved"]} unresolved).', '']
L += ['## Removable hypotheses', '']
if rem:
    L += ['Read with care: each hypothesis is checked on its own (two removable hypotheses of one theorem need not be '
          'removable together), some are there by design, and removing one from a public lemma changes its callers. '
          'A *dependent* hypothesis (one that later parts of the statement mention) is removable in the sense that it '
          'follows from the other hypotheses, so it can be replaced by a derived proof.', '',
          '| Theorem | Hypothesis | Why it is not needed | Proof |', '|---|---|---|---|']
    for r in rem:
        dep = ' (dependent)' if r.get('dependent') else ''
        L.append(f'| `{r["theorem"]}` ({r["module"]}:{r.get("line", "?")}) | {hyp(r)}{dep} | {cell(why(r))} | {proof(r)} |')
else:
    L.append('None found.')
L += ['', '## Necessary hypotheses', '',
      f'{tot["necessary"]} hypotheses are necessary: ' +
      ('; '.join(f'{c} {k}' for k, c in nec_by.most_common()) or 'none') + '. They are in `results/public.jsonl` '
      '(and `private.jsonl`) with `status: necessary`, the stored proof of the negation, and for tool finds the '
      'counterexample values in `witness`.', '',
      '## Files', '',
      '- `results/public.jsonl`, `results/private.jsonl`: one JSON line per hypothesis (`theorem`, `idx` = position '
      'among the binders from 0, `name`, `type`, `status`, `found_by`, `tactic`, and where the proof is: `proofs_file` '
      'with the declaration in `proof`, or `proof_file`/`proof_decl`); `*_removable.jsonl` and '
      '`*_unresolved.jsonl` hold the subsets.',
      '- Proof files compile with the library: `scripts/hclean FILE.lean` (exit code 0 with no `error:` lines means every '
      'proof in it is accepted). `python3 scripts/check_hand.py FILE.lean VERDICTS.jsonl` also checks that each '
      'declaration proves exactly the stated verdict and uses only the standard axioms.']
open(OUT, 'w').write('\n'.join(L) + '\n')

print(f'{n} hypotheses: {tot["necessary"]} necessary, {tot["removable"]} removable, '
      f'{tot["independent"]} independent, {tot["unresolved"]} unresolved')
for r in rem[:15]:
    print(f'  removable: {r["theorem"]}  {r.get("name", "?")} : {" ".join(r.get("type", "?").split())[:80]}')
if len(rem) > 15:
    print(f'  ... and {len(rem) - 15} more')
print(f'full report: {os.path.abspath(OUT)}')
