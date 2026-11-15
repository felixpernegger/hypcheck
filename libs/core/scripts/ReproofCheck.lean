import Lean
/-!
Reproof pass, step 2: for each variant `T_hcdropI` from `reproof_gen.py`, imports the compiled module
copy (search path: OLEAN_DIR first) and checks that the variant exists, that its statement is `T'`
(T without binder I; `isDefEq` with fresh universe metavariables for T), and that its proof uses only
`propext`, `Classical.choice`, `Quot.sound` (a failed proof is added with `sorryAx`).

Usage: lean --run ReproofCheck.lean OLEAN_DIR MODULE VARIANTS.jsonl OUT.jsonl
-/
open Lean Meta

def check (T V : Name) (i : Nat) : MetaM String := do
  let env ← getEnv
  let some cv := env.find? V | return "missing"
  let some ct := env.find? T | return "original missing"
  let us ← ct.levelParams.mapM fun _ => mkFreshLevelMVar
  let tT ← forallTelescope (ct.type.instantiateLevelParams ct.levelParams us) fun xs body => do
    let some x := xs[i]? | throwError "bad idx"
    if body.containsFVar x.fvarId! then throwError "dependent"
    mkForallFVars (xs.eraseIdxIfInBounds i) body
  unless ← isDefEq tT cv.type do return "statement differs"
  let ax ← collectAxioms V
  for a in ax do
    unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
      return s!"axiom {a}"
  return "ok"

unsafe def main (args : List String) : IO Unit := do
  let [dir, mod, inp, out] := args | throw <| IO.userError "usage"
  initSearchPath ((← IO.getEnv "LEAN_SYSROOT").map System.FilePath.mk |>.getD (← getBuildDir))
  searchPathRef.modify fun sp => (dir : System.FilePath) :: sp
  enableInitializersExecution
  let env ← importModules #[{ module := mod.toName }] {} (loadExts := true)
  let h ← IO.FS.Handle.mk out .append
  let ctx : Core.Context := { fileName := "<r>", fileMap := default, maxHeartbeats := 0 }
  for l in ← IO.FS.lines inp do
    if l.isEmpty then continue
    let j ← IO.ofExcept (Json.parse l)
    unless (j.getObjValAs? String "module").toOption == some mod do continue
    let T := (← IO.ofExcept (j.getObjValAs? String "theorem")).toName
    let V := (← IO.ofExcept (j.getObjValAs? String "variant")).toName
    let i ← IO.ofExcept (j.getObjValAs? Nat "idx")
    let r ← try
        let (r, _) ← ((check T V i).run' {}).toIO ctx { env }
        pure r
      catch e => pure s!"error: {e}"
    h.putStrLn (Json.compress (j.mergeObj (Json.mkObj [("reproof", toJson r)])))
