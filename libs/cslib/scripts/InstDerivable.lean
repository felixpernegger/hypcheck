import Lean
/-!
Exploration (v8): for each instance-implicit hypothesis (theorem, idx) in a JSONL file, can type class
resolution find it from the *other* binders of the theorem (as local instances)? If so it is
derivable, and `fun rest => T … (inst) …` proves `T'`, which is checked by the kernel here.

Usage: lean --run InstDerivable.lean MODULE_ROOTS(comma) IN.jsonl OUT.jsonl
-/
open Lean Meta

def check (n : Name) (i : Nat) : MetaM String := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs body => do
    let some x := xs[i]? | return "bad-idx"
    let hx ← inferType x
    -- statement must not depend on the instance (otherwise it's a different verdict kind)
    if body.containsFVar x.fvarId! then return "dependent"
    for y in xs.extract (i+1) xs.size do
      if (← inferType y).containsFVar x.fvarId! then return "dependent"
    let rest := xs.eraseIdxIfInBounds i
    -- rebuild the context without `x`, so that `x` itself is not a local instance
    let ty ← mkForallFVars rest body
    forallTelescope ty fun ys body' => do
      let hx' := hx.replaceFVars rest ys
      let some inst ← (try synthInstance? hx' catch _ => pure none) | return "no"
      let inst ← instantiateMVars inst
      if inst.hasMVar then return "no"
      let args := (xs.mapIdx fun j _ => if j == i then inst else
        ys[if j < i then j else j - 1]!)
      let pf ← mkLambdaFVars ys (mkAppN (mkConst n (ci.levelParams.map mkLevelParam)) args)
      let ty' ← mkForallFVars ys body'
      let decl := Declaration.thmDecl { name := `_instDerivCheck, levelParams := ci.levelParams, type := ty', value := pf }
      let ok : Bool ← withoutModifyingEnv do
        try
          addDecl decl
          pure true
        catch _ => pure false
      return if ok then "derivable" else "kernel-fail"

unsafe def main (args : List String) : IO Unit := do
  let [roots, inp, out] := args | throw <| IO.userError "usage"
  -- CSLib port: search path = LEAN_PATH (Cslib + Mathlib oleans, set by `scripts/cslean` / `lake env`)
  -- plus the running toolchain's own library.
  if (← IO.getEnv "LEAN_PATH").isNone then
    throw <| IO.userError "LEAN_PATH unset: run with scripts/cslean (or lake env lean in the CSLib checkout)"
  initSearchPath (← getBuildDir)
  enableInitializersExecution
  let mods := (roots.splitOn ",").toArray.map fun s => ({ module := s.toName } : Import)
  let env ← importModules mods {} (loadExts := true)
  let h ← IO.FS.Handle.mk out .write
  let opts : Options := Options.empty.setBool `Elab.async false
  let ctx : Core.Context := { fileName := "<instder>", fileMap := default, maxHeartbeats := 200000, options := opts }
  for l in ← IO.FS.lines inp do
    if l.isEmpty then continue
    let j ← IO.ofExcept (Json.parse l)
    unless (j.getObjValAs? String "binder").toOption == some "instImplicit" do continue
    let n := (← IO.ofExcept (j.getObjValAs? String "theorem")).toName
    let i ← IO.ofExcept (j.getObjValAs? Nat "idx")
    let r ← try
        let (r, _) ← ((check n i).run' {}).toIO ctx { env }
        pure r
      catch e => pure s!"error: {e}"
    h.putStrLn (Json.compress (j.mergeObj (Json.mkObj [("inst_derivable", toJson r)])))
