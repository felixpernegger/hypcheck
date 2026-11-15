import Lean
/-!
Exploration (v8): for each (theorem, idx) in a JSONL file, does the library's proof of the theorem
use hypothesis `idx` at all? If not (and nothing else in the statement depends on it), the proof
term with that binder dropped proves `T'`, which is checked by the kernel here.

Usage: lean --run Unused.lean MODULE_ROOTS(comma) IN.jsonl OUT.jsonl
-/
open Lean Meta

/-- `used`, `eta` (value has fewer lambdas than binders), `dependent`, `unused` (kernel-checked),
`unused-kernel-fail`, or `no-value`. -/
def classify (n : Name) (i : Nat) : MetaM String := do
  let some ci := (← getEnv).find? n | return "missing"
  let some v := ci.value? (allowOpaque := true) | return "no-value"
  forallTelescope ci.type fun xs body => do
    if i ≥ xs.size then return "bad-idx"
    lambdaBoundedTelescope v xs.size fun ys b => do
      if ys.size < xs.size then return "eta"
      let some x := ys[i]? | return "bad-idx"
      -- statement dependence
      let rest := ys.eraseIdxIfInBounds i
      let body' := body.replaceFVars xs ys
      if body'.containsFVar x.fvarId! then return "dependent"
      for y in rest do
        if (← inferType y).containsFVar x.fvarId! then return "dependent"
      if b.containsFVar x.fvarId! then return "used"
      let ty ← mkForallFVars rest body'
      let pf ← mkLambdaFVars rest b
      let ok ← withoutModifyingEnv do
        try
          addDecl (.thmDecl { name := `_unusedCheck, levelParams := ci.levelParams, type := ty, value := pf })
          pure true
        catch _ => pure false
      return if ok then "unused" else "unused-kernel-fail"

/-- Like `String.toName`, but numeric components (e.g. the `0` of `_private.M.0.x`) become `Name.num`. -/
def parseNamePriv (s : String) : Lean.Name :=
  (s.splitOn ".").foldl (fun n c => if !c.isEmpty && c.all Char.isDigit then .num n c.toNat! else .str n c) .anonymous

unsafe def main (args : List String) : IO Unit := do
  let [roots, inp, out] := args | throw <| IO.userError "usage"
  initSearchPath (← match (← IO.getEnv "LEAN_SYSROOT") with | some r => pure (r : System.FilePath) | none => getBuildDir)  -- batteries port
  enableInitializersExecution
  let mods := (roots.splitOn ",").toArray.map fun s => ({ module := s.toName } : Import)
  let env ← importModules mods {} (loadExts := true)
  let h ← IO.FS.Handle.mk out .write
  let opts : Options := Options.empty.setBool `Elab.async false
  let ctx : Core.Context := { fileName := "<unused>", fileMap := default, maxHeartbeats := 0, options := opts }
  for l in ← IO.FS.lines inp do
    if l.isEmpty then continue
    let j ← IO.ofExcept (Json.parse l)
    let n := parseNamePriv (← IO.ofExcept (j.getObjValAs? String "theorem"))
    let i ← IO.ofExcept (j.getObjValAs? Nat "idx")
    -- `toName` splits at dots; names with special characters may not round-trip
    let r ← try
        let (r, _) ← ((classify n i).run' {}).toIO ctx { env }
        pure r
      catch e => pure s!"error: {e}"
    h.putStrLn (Json.compress (j.mergeObj (Json.mkObj [("unused_check", toJson r)])))
