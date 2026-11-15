#!/usr/bin/env python3
"""Checks a joint-removal file (J1c0Hand.lean): every pair verdict in PAIRS.jsonl is proved by its `decl`.

For a pair (T, i, j): if neither binder is dependent, T'' = T without binders i and j; otherwise
T'' = ∀ rest, Hᵢ ∧ Hⱼ (rest = binders that mention neither, transitively). Built here independently of
the drop2%/indep2% macros. `jointly_removable` needs `decl : T''` with T's universes mapped to distinct
universe parameters; `not_jointly_removable` needs `decl : ¬T''` (any universes). Also reports axioms.
Usage: check_pairs.py HAND.lean PAIRS.jsonl
"""
import json, os, re, subprocess, sys, tempfile
LEAN = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cslean')
CHECKER = r'''
section PairCheck
open Lean Meta Elab Command

def pcName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => if !c.isEmpty && c.all Char.isDigit then .num n c.toNat! else .str n c) .anonymous

def pcTarget (T : Name) (i j : Nat) : MetaM (List Level × Lean.Expr) := do
  let ci ← getConstInfo T
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  let ty := ci.type.instantiateLevelParams ci.levelParams us
  let e ← forallTelescope ty fun xs body => do
    let xi := xs[i]!; let xj := xs[j]!
    unless (← isProp (← inferType xi)) && (← isProp (← inferType xj)) do throwError "not Prop binders"
    -- binders depending (transitively) on xi or xj
    let mut dep : Array Lean.Expr := #[]
    for k in [:xs.size] do
      if k == i || k == j then continue
      let t ← inferType xs[k]!
      if t.containsFVar xi.fvarId! || t.containsFVar xj.fvarId! || dep.any (fun d => t.containsFVar d.fvarId!) then
        dep := dep.push xs[k]!
    let rest := xs.filter fun y => y != xi && y != xj && !dep.contains y
    if dep.isEmpty && !body.containsFVar xi.fvarId! && !body.containsFVar xj.fvarId! then
      mkForallFVars rest body
    else
      mkForallFVars rest (mkAnd (← inferType xi) (← inferType xj))
  return (us, e)

def pairCheck (decl T : Name) (i j : Nat) (removable : Bool) : CommandElabM Unit := liftTermElabM do
  let ci ← getConstInfo decl
  let P ← instantiateMVars ci.type
  let (us, t) ← pcTarget T i j
  let ok ← withNewMCtxDepth (allowLevelAssignments := true) do
    if removable then
      unless ← isDefEq P t do return false
      let ls ← us.mapM instantiateLevelMVars
      return ls.all (·.isParam) && ls.eraseDups.length == ls.length
    else
      match P.not? with
      | some S => isDefEq S t
      | none => return false
  logInfo m!"PAIRCHECK {if ok then "OK" else "FAIL"} {decl}"
  logInfo m!"PAIRCHECK AXIOMS {decl} {(← collectAxioms decl).toList}"
end PairCheck
'''
def main():
    hand, pairs = sys.argv[1], sys.argv[2]
    vs = [json.loads(l) for l in open(pairs)]
    src = open(hand).read()
    for kw in ['sorry', 'native_decide', 'implemented_by']:
        for n, l in enumerate(src.split('\n'), 1):
            if re.search(r'\b%s\b' % kw, l) and not l.lstrip().startswith('--'): print(f'FORBIDDEN {kw} line {n}')
    out = src + CHECKER + '\n'.join(
        f'#eval pairCheck (pcName "{v["decl"]}") (pcName "{v["theorem"]}") {v["idx"][0]} {v["idx"][1]} '
        f'{"true" if v["status"] == "jointly_removable" else "false"}' for v in vs)
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False, dir=os.path.dirname(os.path.abspath(hand))) as f:
        f.write(out); tmp = f.name
    try: r = subprocess.run([LEAN, tmp], capture_output=True, text=True)
    finally: os.unlink(tmp)
    text = r.stdout + r.stderr
    errs = [l for l in text.split('\n') if ': error' in l]
    ok = set(re.findall(r'PAIRCHECK OK (\S+)', text)); fail = re.findall(r'PAIRCHECK FAIL (\S+)', text)
    ax = {m.group(1): {a.strip() for a in m.group(2).split(',') if a.strip()}
          for m in re.finditer(r'PAIRCHECK AXIOMS (\S+)\s+\[([^\]]*)\]', text)}
    std = {'propext', 'Classical.choice', 'Quot.sound'}
    bad_ax = {d: a for d, a in ax.items() if not a <= std}
    missing = [v['decl'] for v in vs if v['decl'] not in ok]
    print(f'lean errors: {len(errs)}; pairs: {len(vs)}; statement OK: {len(ok)}; failed/missing: {len(missing)}; '
          f'axioms standard: {len(ax) - len(bad_ax)}, other: {len(bad_ax)}')
    for e in errs[:10]: print('  ', e)
    for d in missing: print('  NOT OK:', d)
    for d, a in bad_ax.items(): print('  AXIOMS OTHER:', d, sorted(a))
main()
