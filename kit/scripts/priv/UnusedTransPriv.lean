import Lean
/-!
Exploration (v8): transitive version of `Unused.lean`. Hypothesis `k` of theorem `C` is *droppable*
if it is not dependent and every occurrence of it in the proof of `C` is as argument `j` of a
theorem `C'` whose hypothesis `j` is droppable (recursively; direct non-use is the base case).
This only estimates; it builds no proofs (a proof would replace each such call by the call of the
callee's droppable version).

Usage: lean --run UnusedTrans.lean MODULE_ROOTS(comma) IN.jsonl OUT.jsonl
-/
open Lean Meta

structure St where
  memo : Std.HashMap (Name × Nat) Bool := {}
  inProgress : Std.HashSet (Name × Nat) := {}

abbrev M := StateRefT St MetaM

/-- Whether binder `k` of `ci.type` is non-dependent (neither later binders nor the conclusion
mention it), and if so the telescope of the value. -/
partial def droppable (c : Name) (k : Nat) (depth : Nat := 0) : M Bool := do
  if let some r := (← get).memo[(c, k)]? then return r
  if (← get).inProgress.contains (c, k) || depth > 40 then return false
  modify fun s => { s with inProgress := s.inProgress.insert (c, k) }
  let r ← go
  modify fun s => { s with memo := s.memo.insert (c, k) r, inProgress := s.inProgress.erase (c, k) }
  return r
where
  go : M Bool := do
    let some ci := (← getEnv).find? c | return false
    let .thmInfo _ := ci | return false
    let some v := ci.value? (allowOpaque := true) | return false
    forallTelescope ci.type fun xs body => do
      let some x := xs[k]? | return false
      unless ← isProp (← inferType x) do return false
      if body.containsFVar x.fvarId! then return false
      for y in xs.extract (k+1) xs.size do
        if (← inferType y).containsFVar x.fvarId! then return false
      lambdaBoundedTelescope v xs.size fun ys b => do
        if ys.size < xs.size then return false
        let some y := ys[k]? | return false
        occOk y.fvarId! b depth
  occOk (x : FVarId) (e : Expr) (depth : Nat) : M Bool := do
    if !e.containsFVar x then return true
    match e with
    | .fvar _ => return false
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .const n _ =>
        for h : i in [:args.size] do
          let a := args[i]
          if a == .fvar x then
            unless ← droppable n i (depth + 1) do return false
          else unless ← occOk x a depth do return false
        return true
      | _ =>
        unless ← occOk x f depth do return false
        args.allM (occOk x · depth)
    | .lam _ t b _ | .forallE _ t b _ => return (← occOk x t depth) && (← occOk x b depth)
    | .letE _ t v b _ => return (← occOk x t depth) && (← occOk x v depth) && (← occOk x b depth)
    | .mdata _ b => occOk x b depth
    | .proj _ _ b => occOk x b depth
    | _ => return true

/-- Like `String.toName`, but numeric components (e.g. the `0` of `_private.M.0.x`) become `Name.num`. -/
def parseNamePriv (s : String) : Lean.Name :=
  (s.splitOn ".").foldl (fun n c => if !c.isEmpty && c.all Char.isDigit then .num n c.toNat! else .str n c) .anonymous

unsafe def main (args : List String) : IO Unit := do
  let [roots, inp, out] := args | throw <| IO.userError "usage"
  -- Search path = LEAN_PATH (library + dependency oleans, set by `scripts/hcrun` / `lake env`)
  -- plus the running toolchain's own library.
  if (← IO.getEnv "LEAN_PATH").isNone then
    throw <| IO.userError "LEAN_PATH unset: run through scripts/hcrun or scripts/hclean (or `lake env` in the library)"
  initSearchPath (← getBuildDir)
  enableInitializersExecution
  let mods := (roots.splitOn ",").toArray.map fun s => ({ module := s.toName } : Import)
  let env ← importModules mods {} (loadExts := true)
  let h ← IO.FS.Handle.mk out .write
  let opts : Options := Options.empty.setBool `Elab.async false
  let ctx : Core.Context := { fileName := "<unused>", fileMap := default, maxHeartbeats := 0, options := opts }
  let st ← IO.mkRef ({} : St)
  for l in ← IO.FS.lines inp do
    if l.isEmpty then continue
    let j ← IO.ofExcept (Json.parse l)
    let n := parseNamePriv (← IO.ofExcept (j.getObjValAs? String "theorem"))
    let i ← IO.ofExcept (j.getObjValAs? Nat "idx")
    let r ← try
        let ((r, s'), _) ← (((droppable n i).run (← st.get)).run' {}).toIO ctx { env }
        st.set s'
        pure (toString r)
      catch e => pure s!"error: {e}"
    h.putStrLn (Json.compress (j.mergeObj (Json.mkObj [("droppable", toJson r)])))
