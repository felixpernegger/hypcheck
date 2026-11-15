import Lean
/-! Groups theorems (from the result files) whose statements are equal up to binder and universe
parameter names. Output: one JSON line per group of size ≥ 2. -/
open Lean Meta

def parseNamePriv (s : String) : Lean.Name :=
  (s.splitOn ".").foldl (fun n c => if !c.isEmpty && c.all Char.isDigit then .num n c.toNat! else .str n c) .anonymous

unsafe def main (args : List String) : IO Unit := do
  let [roots, inp, out] := args | throw <| IO.userError "usage"
  initSearchPath (← match (← IO.getEnv "LEAN_SYSROOT") with | some r => pure (r : System.FilePath) | none => getBuildDir)  -- batteries port
  enableInitializersExecution
  let mods := (roots.splitOn ",").toArray.map fun s => ({ module := s.toName } : Import)
  let env ← importModules mods {} (loadExts := true)
  let mut names : Std.HashSet Name := {}
  for l in ← IO.FS.lines inp do
    if l.isEmpty then continue
    let j ← IO.ofExcept (Json.parse l)
    names := names.insert (parseNamePriv (← IO.ofExcept (j.getObjValAs? String "theorem")))
  let mut groups : Std.HashMap UInt64 (Array (Name × Expr)) := {}
  for n in names do
    let some ci := env.find? n | continue
    let lps := ci.levelParams
    let ty := ci.type.instantiateLevelParams lps
      ((List.range lps.length).map fun k => Level.param (Name.mkSimple s!"u{k}"))
    groups := groups.insert ty.hash ((groups.getD ty.hash #[]).push (n, ty))
  let h ← IO.FS.Handle.mk out .write
  for (_, g) in groups do
    if g.size < 2 then continue
    -- split by actual equality (`==` on `Expr` ignores binder names)
    let mut cls : Array (Array Name × Expr) := #[]
    for (n, t) in g do
      match cls.findIdx? (·.2 == t) with
      | some k => cls := cls.modify k fun (ns, t) => (ns.push n, t)
      | none => cls := cls.push (#[n], t)
    for (ns, _) in cls do
      if ns.size ≥ 2 then h.putStrLn (Json.compress (toJson (ns.map toString)))
