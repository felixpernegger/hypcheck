import Lean
open Lean Meta
/-- Counts Batteries constants with ≥ 1 Prop parameter that the inventory did NOT include, by reason. -/
unsafe def main : IO Unit := do
  enableInitializersExecution
  initSearchPath (← match (← IO.getEnv "LEAN_SYSROOT") with | some r => pure (r : System.FilePath) | none => getBuildDir)
  let env ← importModules #[{ module := `Batteries }] {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<scope>", fileMap := default, maxHeartbeats := 0 }
  let act : MetaM Unit := do
    let mut cnt : Std.HashMap String (Nat × Array String) := {}
    for mod in env.header.moduleNames, data in env.header.moduleData do
      unless mod.getRoot == `Batteries do continue
      for n in data.constNames do
        let some ci := env.find? n | continue
        let kind := match ci with
          | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
          | .axiomInfo _ => "axiom" | _ => "other"
        if kind == "other" then continue
        -- Prop-valued constants only (proofs), plus axioms
        unless kind == "axiom" || (← isProp ci.type) do continue
        let np ← forallTelescope ci.type fun xs _ => xs.filterM fun x => do isProp (← inferType x)
        if np.isEmpty then continue
        let pos := (← findDeclarationRanges? n).isSome
        let internal := (privateToUserName n).isInternalDetail
        let included := kind == "theorem" && pos && !internal
        if included then continue
        let key := s!"{kind}, pos={pos}, internal={internal}, private={isPrivateName n}"
        let (c, ex) := cnt.getD key (0, #[])
        cnt := cnt.insert key (c + np.size, if ex.size < (if kind == "def" && pos then 100 else 4) then ex.push s!"{n}" else ex)
    for (k, (c, ex)) in cnt.toList do
      IO.println s!"{c} Prop params | {k} | e.g. {ex}"
  let _ ← (act.run' {}).toIO ctx { env }
