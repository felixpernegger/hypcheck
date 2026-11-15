#!/usr/bin/env python3
"""Checks that the statements in a hand-verdict file are exactly the intended `T'`.

For every `example`/`theorem` in HAND.lean, the backticked names in the comment block above it give
the candidate original theorems. For each candidate `T` and each Prop binder `i` of `T`, the checker
builds `T'ᵢ` (T without binder i; for a dependent hypothesis `∀ indep, Hᵢ`, in two variants: all
independent binders, or only those `Hᵢ` mentions) and tests whether the proved statement `P` is
definitionally equal to `T'ᵢ` (removable) or to `¬T'ᵢ` (necessary), with `T`'s universe
parameters as metavariables. Then every (theorem, idx) verdict in VERDICTS.jsonl must be covered by
a match with the same polarity.

Usage: check_hand.py HAND.lean VERDICTS.jsonl   (run from anywhere; uses stage1 lean)
With HANDCHECK_AXIOMS=1 it also reports every declaration whose axioms are not among propext /
Classical.choice / Quot.sound (lines `AXIOMS OTHER:` / `AXIOMS MISSING:`).
"""
import json, os, re, subprocess, sys, tempfile

LEAN = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cslean')  # CSLib port: toolchain lean + lake env LEAN_PATH
AXIOMS = os.environ.get('HANDCHECK_AXIOMS') == '1'

CHECKER = r'''
section HandCheck
open Lean Meta Elab Command

/-- A name from its dotted string; all-digit components are numeric (private names `_private.M.0.x`). -/
def handName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => if !c.isEmpty && c.all Char.isDigit then .num n c.toNat! else .str n c) .anonymous

/-- `(i, T'ᵢ)` for every Prop binder `i` of `T`, plus dependent variants. -/
def handCheckVariants (T : Name) : MetaM (List Level × Array (Nat × Lean.Expr)) := do
  let ci ← getConstInfo T
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  let ty := ci.type.instantiateLevelParams ci.levelParams us
  return (us, ← forallTelescope ty fun xs body => do
    let mut out := #[]
    for i in [:xs.size] do
      let x := xs[i]!
      unless ← isProp (← inferType x) do continue
      let mut dep : Array Lean.Expr := #[x]
      for j in [i+1:xs.size] do
        let t ← inferType xs[j]!
        if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
      let rest := xs.filter (fun y => !dep.contains y)
      if dep.size > 1 || body.containsFVar x.fvarId! then
        let hx ← inferType x
        out := out.push (i, ← mkForallFVars rest hx)
        let used := rest.filter fun y => hx.containsFVar y.fvarId!
        -- close `used` under the types of its members
        let mut cl := used
        for y in rest.reverse do
          if cl.contains y then
            let ty ← inferType y
            for z in rest do
              if ty.containsFVar z.fvarId! && !cl.contains z then cl := cl.push z
        let clOrd := rest.filter (cl.contains ·)
        out := out.push (i, ← mkForallFVars clOrd hx)
      else
        out := out.push (i, ← mkForallFVars rest body)
    return out)

def handCheck (decl : Name) (cands : List Name) : CommandElabM Unit := liftTermElabM do
  let P ← instantiateMVars (← inferType (← mkConstWithFreshMVarLevels decl))
  let neg := P.not?.isSome
  -- A removable proof must hold in every universe: keep its own universe parameters fixed and
  -- require each universe of `T` to map to a distinct one of them (not e.g. to `0`).
  let S ← if neg then pure P.not?.get! else do
    let ci ← getConstInfo decl
    inferType (mkConst decl (ci.levelParams.map Level.param))
  let mut hits := #[]
  for T in cands do
    unless (← getEnv).contains T do continue
    let (us, vs) ← handCheckVariants T
    for (i, t) in vs do
      let ok ← withoutModifyingState <| withNewMCtxDepth (allowLevelAssignments := true) do
        unless ← isDefEq S t do return false
        if neg then return true
        let ls ← us.mapM instantiateLevelMVars
        return ls.all (·.isParam) && ls.eraseDups.length == ls.length
      if ok then
        hits := hits.push s!"{T} {i}"
      else if !neg then pure ()
  let pol := if neg then "necessary" else "removable"
  if hits.isEmpty then logInfo m!"HANDCHECK NOMATCH {decl} {pol}"
  else for h in hits do logInfo m!"HANDCHECK MATCH {decl} {pol} {h}"

/-- Axioms of `decl` (opt-in with `HANDCHECK_AXIOMS=1`). -/
def handAxioms (decl : Name) : CommandElabM Unit := liftTermElabM do
  logInfo m!"HANDCHECK AXIOMS {decl} {(← collectAxioms decl).toList}"

end HandCheck
'''

def main():
    hand, verdicts = sys.argv[1], sys.argv[2]
    src = open(hand).read().split('\n')
    vnames = sorted({json.loads(l)['theorem'] for l in open(verdicts)})
    out, decls, comment = [], [], []
    n = 0
    ns = []  # open namespaces (sections push None)
    for line in src:
        mn = re.match(r'^namespace\s+(\S+)', line)
        if mn: ns.append(mn.group(1))
        elif re.match(r'^(noncomputable\s+)?section\b', line): ns.append(None)
        elif re.match(r'^end(\s|$)', line) and ns: ns.pop()
        m = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+)?(example|theorem\s+(\S+))(\s|$)', line)
        if m:
            cands = []
            for c in comment:
                for t in re.findall(r'`([^`\s]+)`', c):
                    cands += [v for v in vnames if v == t or v.endswith('.' + t)]
                    if '.' in t: cands.append(t)
            if m.group(2):  # a theorem named like the original also gets it as a candidate
                last = m.group(2).split('.')[-1]
                cands += [v for v in vnames if v.split('.')[-1] == last]
            cands = list(dict.fromkeys(cands))
            if m.group(1) == 'example':
                name = f'HandCheckEx.e{n}'; n += 1
                line = line.replace('example', f'theorem {name}', 1)
            else:
                name = m.group(2).split('.{')[0]  # universe parameters
                prefix = '.'.join(x for x in ns if x)
                if prefix and not name.startswith('_root_.'): name = prefix + '.' + name
                name = name.removeprefix('_root_.')
            decls.append((name, cands, line))
            comment = []
        elif line.startswith('--'):
            comment.append(line)
        elif line.strip() and not line.startswith(' '):
            # keep comment context only across blank lines directly above a declaration
            if not line.startswith('/-') and not line.startswith('set_option'):
                comment = []
        out.append(line)
    if not any(l.startswith('import Lean') for l in out):
        out.insert(0, 'import Lean')
    out.append(CHECKER)
    for name, cands, _ in decls:
        if cands:
            out.append(f'#eval handCheck (handName "{name}") [{", ".join(f'handName "{c}"' for c in cands)}]')
        if AXIOMS:
            out.append(f'#eval handAxioms (handName "{name}")')
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False,
                                     dir=os.path.dirname(os.path.abspath(hand))) as f:
        f.write('\n'.join(out)); tmp = f.name
    try:
        r = subprocess.run([LEAN, tmp], capture_output=True, text=True)
    finally:
        os.unlink(tmp)
    text = r.stdout + r.stderr
    errs = [l for l in text.split('\n') if ': error' in l]
    matches = set(); nomatch = []
    for l in text.split('\n'):
        m = re.search(r'HANDCHECK MATCH (\S+) (\S+) (\S+) (\d+)', l)
        if m: matches.add((m.group(3), int(m.group(4)), m.group(2), m.group(1)))
        m = re.search(r'HANDCHECK NOMATCH (\S+) (\S+)', l)
        if m: nomatch.append((m.group(1), m.group(2)))
    vs = [json.loads(l) for l in open(verdicts)]
    bad = 0
    for v in vs:
        if v['status'] not in ('removable', 'necessary'): continue
        ok = any(t == v['theorem'] and i == v['idx'] and pol == v['status'] for t, i, pol, _ in matches)
        if not ok:
            bad += 1; print(f"NOT COVERED: {v['theorem']} idx {v['idx']} {v['status']}")
    print(f"lean errors: {len(errs)}; verdicts checked: {sum(v['status'] in ('removable','necessary') for v in vs)}; not covered: {bad}")
    for e in errs[:10]: print('  ', e)
    print('declarations without a match (helpers, transcription checks, derivability lemmas):')
    for d, pol in nomatch: print('  ', d, pol)
    if AXIOMS:
        ax = {}
        # Lean reflows long messages, so the axiom list may continue on the next lines
        for m in re.finditer(r'HANDCHECK AXIOMS (\S+)\s+\[([^\]]*)\]', text):
            ax[m.group(1)] = {a.strip() for a in m.group(2).split(',') if a.strip()}
        other = {d: a for d, a in ax.items() if not a <= {'propext', 'Classical.choice', 'Quot.sound'}}
        missing = [d for d, _, _ in decls if d not in ax]
        print(f'axioms: {len(ax) - len(other)} standard, {len(other)} other, {len(missing)} missing')
        for d, a in other.items(): print(f'AXIOMS OTHER: {d} {sorted(a)}')
        for d in missing: print(f'AXIOMS MISSING: {d}')

main()
