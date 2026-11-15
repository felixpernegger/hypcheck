import Lean.Elab.Command
import Init
import Batteries.Data.Vector.Lemmas
import Batteries.Data.Array.Scan
-- add the library modules your rows need here (e.g. `import Init`, `import Std.Sat.AIG.CNF`); avoid `import Lean`/`import Std` (1.5 GB)

set_option linter.unusedVariables false

open Lean Meta Elab Term

/-- `_private.M.«0».x` ↦ `_private.M.0.x`: all-digit string components become numeric. -/
def hcFixName : Name → Name
  | .str p s => if !s.isEmpty && s.all Char.isDigit then .num (hcFixName p) s.toNat! else .str (hcFixName p) s
  | .num p k => .num (hcFixName p) k
  | .anonymous => .anonymous

/-- The constant named by `T`: a public name (resolved as usual) or a private one written in full
as `_private.Mod.«0».x` (private names are not reachable by their short name from another module). -/
def hcConst (T : Ident) : TermElabM Name := do
  let n := hcFixName T.getId
  if isPrivateName n then
    unless (← getEnv).contains n do throwError "unknown private constant {n}"
    return n
  realizeGlobalConstNoOverloadWithInfo T

/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

/-! Main-session re-check of the W1 independent rows (2026-11-10). -/
open Classical in
/-- Counter monad whose `map` adds 1 exactly when source and target type are equal (classical test). -/
noncomputable instance TM : Monad (fun α : Type => Nat × α) where
  pure a := (0, a)
  bind x f := ((f x.2).1 + x.1, (f x.2).2)
  map {α β} f x := if α = β then (x.1 + 1, f x.2) else (x.1, f x.2)

-- helper: Vector Bool 1 has two elements, List Bool more
theorem vne : Vector Bool 1 ≠ List Bool := by
  intro h
  have key : ∀ x y z : Vector Bool 1, x = y ∨ y = z ∨ x = z := by
    intro x y z
    rcases x with ⟨⟨xs⟩, hx⟩; rcases y with ⟨⟨ys⟩, hy⟩; rcases z with ⟨⟨zs⟩, hz⟩
    simp only [List.size_toArray, List.length_eq_one_iff] at hx hy hz
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; obtain ⟨c, rfl⟩ := hz
    cases a <;> cases b <;> cases c <;> simp
  rw [h] at key
  rcases key [] [true] [false] with h | h | h <;> simp at h

-- `Vector.toList_scanlM` idx 6 ([LawfulMonad m]): necessary. TM is a counter monad whose map adds 1 iff
-- source and target type are equal; with n = 0 the left map runs at Vector Bool 1 → List Bool (no +1),
-- the right one (List.scanlM = reverse <$> …) at List Bool → List Bool (+1).
theorem vec_toList_scanlM_nec : ¬ drop0% Vector.toList_scanlM 6 := by
  intro h
  have := @h (fun α : Type => Nat × α) Bool Bool 0 true TM (fun b _ => (0, b)) #v[]
  rw [Vector.scanlM, Vector.scanlM.loop] at this
  simp only [List.scanlM, Functor.map, Pure.pure] at this
  have h1 := congrArg Prod.fst this
  simp only [Nat.lt_irrefl, dite_false, ite_true] at h1
  rw [if_neg (show ¬ (Vector Bool (0 + 1) = List Bool) from vne)] at h1
  -- h1 : 0 = (scanAuxM …).fst + 1, and scanAuxM on [] is `pure [init]` = (0, [true])
  exact absurd h1 (by decide)

