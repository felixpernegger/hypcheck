import Lean
/-!
Emits the statements `T'` for unused-hypothesis verdicts (output of `Unused.lean`, entries with
`unused_check = "unused"`), printed readably and explicitly, as JSON lines
`{theorem, idx, lps, readable, explicit}`. `scripts/unused_proofs.py` turns them into a proof file.

Usage: lean --run UnusedEmit.lean MODULE_ROOTS(comma) IN.jsonl OUT.jsonl
-/
open Lean Meta

partial def eraseScopes : Expr → Expr
  | .forallE n t b bi => .forallE n.eraseMacroScopes (eraseScopes t) (eraseScopes b) bi
  | .lam n t b bi => .lam n.eraseMacroScopes (eraseScopes t) (eraseScopes b) bi
  | .letE n t v b nd => .letE n.eraseMacroScopes (eraseScopes t) (eraseScopes v) (eraseScopes b) nd
  | .app f a => .app (eraseScopes f) (eraseScopes a)
  | .mdata d e => .mdata d (eraseScopes e)
  | .proj s i e => .proj s i (eraseScopes e)
  | e => e

def pp (e : Expr) (explicit : Bool) : MetaM String := do
  let f ← withOptions (fun o => o |>.setBool `pp.fullNames true |>.setBool `pp.proofs true
      |>.setBool `pp.funBinderTypes true |>.setBool `pp.structureInstanceTypes true
      |>.setBool `pp.explicit explicit |>.setBool `pp.natLit explicit
      |>.set `format.width (100 : Nat)) (ppExpr (eraseScopes e))
  return (toString f).replace "\n" "\n    "

def emit (n : Name) (i : Nat) : MetaM Json := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs body => do
    let ty ← mkForallFVars (xs.eraseIdxIfInBounds i) body
    let used := (collectLevelParams {} ty).params
    let lps := ci.levelParams.filter used.contains
    return Json.mkObj [("theorem", toJson n.toString), ("idx", toJson i),
      ("lps", toJson (lps.map toString)), ("readable", toJson (← pp ty false)),
      ("explicit", toJson (← pp ty true))]

unsafe def main (args : List String) : IO Unit := do
  let [roots, inp, out] := args | throw <| IO.userError "usage"
  initSearchPath ((← IO.getEnv "LEAN_SYSROOT").map System.FilePath.mk |>.getD (← getBuildDir))
  enableInitializersExecution
  let mods := (roots.splitOn ",").toArray.map fun s => ({ module := s.toName } : Import)
  let env ← importModules mods {} (loadExts := true)
  let h ← IO.FS.Handle.mk out .write
  let opts : Options := Options.empty.setBool `Elab.async false
  let ctx : Core.Context := { fileName := "<emit>", fileMap := default, maxHeartbeats := 0, options := opts }
  for l in ← IO.FS.lines inp do
    if l.isEmpty then continue
    let j ← IO.ofExcept (Json.parse l)
    unless (j.getObjValAs? String "unused_check").toOption == some "unused" do continue
    let n := (← IO.ofExcept (j.getObjValAs? String "theorem")).toName
    let i ← IO.ofExcept (j.getObjValAs? Nat "idx")
    let (r, _) ← ((emit n i).run' {}).toIO ctx { env }
    h.putStrLn r.compress
