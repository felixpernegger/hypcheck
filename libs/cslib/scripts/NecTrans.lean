import Lean
/-! Estimate: unresolved (A, i) such that some necessary (B, j) has a proof term in which the binder
`h_j` occurs only as argument `i` of applications of `A`. Then `A'` would give `B'`, so `¬B'` gives `¬A'`. -/
open Lean Meta

/-- positions `(A, i)` where fvar `h` is passed; `none` if `h` also occurs elsewhere. -/
partial def uses (h : FVarId) (e : Expr) : StateT (Array (Name × Nat)) MetaM Bool := do
  if !e.containsFVar h then return true
  match e with
  | .fvar _ => return false
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const c _ := f then
      let mut ok := true
      for k in [:args.size] do
        if args[k]! == .fvar h then modify (·.push (c, k))
        else if !(← uses h args[k]!) then ok := false
      return ok
    else
      let mut ok ← uses h f
      for a in args do ok := ok && (← uses h a)
      return ok
  | .lam _ t b _ | .forallE _ t b _ => return (← uses h t) && (← uses h b)
  | .letE _ t v b _ => return (← uses h t) && (← uses h v) && (← uses h b)
  | .mdata _ b => uses h b
  | .proj _ _ b => uses h b
  | _ => return false

def scan (n : Name) (j : Nat) : MetaM (Array (Name × Nat)) := do
  let some ci := (← getEnv).find? n | return #[]
  let some v := ci.value? (allowOpaque := true) | return #[]
  forallTelescope ci.type fun xs _ => lambdaBoundedTelescope v xs.size fun ys b => do
    if ys.size < xs.size then return #[]
    let some y := ys[j]? | return #[]
    let (ok, acc) ← (uses y.fvarId! b).run #[]
    return if ok then acc else #[]

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
  let ctx : Core.Context := { fileName := "<n>", fileMap := default, maxHeartbeats := 0 }
  for l in ← IO.FS.lines inp do
    if l.isEmpty then continue
    let jj ← IO.ofExcept (Json.parse l)
    let n := (← IO.ofExcept (jj.getObjValAs? String "theorem")).toName
    let i ← IO.ofExcept (jj.getObjValAs? Nat "idx")
    let r ← try
        let (r, _) ← ((scan n i).run' {}).toIO ctx { env }
        pure r
      catch _ => pure #[]
    unless r.isEmpty do
      h.putStrLn (Json.compress (Json.mkObj [("B", toJson n.toString), ("j", toJson i),
        ("targets", toJson (r.map fun (c, k) => Json.arr #[toJson c.toString, toJson k]))]))
