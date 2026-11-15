import Lean.Elab.Command
import Iris
-- hypkit toolkit header: drop%/indep%/drop0%/indep0% state T' and ∀ indep, Hᵢ straight from the library.
-- Agents copy this file unchanged as the start of their output file (scripts/verify.sh checks it).
-- No `xs[i]!` here: libraries may declare a `]!` token (Foundation does), which breaks that syntax.


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
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    unless or (decide (dep.size > 1)) (body.containsFVar x.fvarId!) do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    unless or (decide (dep.size > 1)) (body.containsFVar x.fvarId!) do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

namespace W3c3
open Iris Iris.OFE

/-- Truncation OFE on naturals (copy of Probe1's TN): 1 and 2 agree at step 0 only. -/
structure TN where v : Nat
instance tnOFE : OFE TN where
  Dist n x y := min x.v (n+1) = min y.v (n+1)
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  eq_dist' {x y} := ⟨fun h n => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      have h' : min a (a+b+1) = min b (a+b+1) := h (a+b)
      simp only [TN.mk.injEq]; omega⟩
  dist_lt {n x y m} h hm := by
    have h' : min x.v (n+1) = min y.v (n+1) := h
    show min x.v (m+1) = min y.v (m+1); omega
theorem tn12 : (⟨1⟩ : TN) ≡{0}≡ ⟨2⟩ := rfl
instance tn0disc : DiscreteE (⟨0⟩ : TN) := ⟨fun {y} h => by
  cases y with | mk v =>
    have h' : min 0 (0+1) = min v (0+1) := h
    have : v = 0 := by omega
    subst this; rfl⟩

/-- Two-element discrete OFE. -/
inductive D2 | e | a deriving DecidableEq
instance : OFE D2 := OFE.ofDiscrete D2

end W3c3
open Iris Iris.OFE W3c3

-- `Iris.vec_ofe_discrete` idx 3: necessary (alpha = TN, n = 1: #v[1] and #v[2] agree at step 0 but differ)
theorem w3c3_1 : ¬ drop0% Iris.vec_ofe_discrete 3 := fun h => by
  have := (@h TN _ 1).discrete_0 (x := #v[⟨1⟩]) (y := #v[⟨2⟩]) (vec_dist_toList.mpr (.cons tn12 .nil))
  simp at this

-- `Iris.vec_toList_discrete` idx 4: necessary (v = #v[1] over TN: [1] and [2] agree at step 0)
theorem w3c3_2 : ¬ drop0% Iris.vec_toList_discrete 4 := fun h => by
  have := (@h TN _ 1 #v[⟨1⟩]).discrete (y := [⟨2⟩]) (.cons tn12 .nil)
  simp at this

-- `Iris.vec_cons_discrete` idx 5: necessary (x = 1 over TN, v = #v[] discrete: cons 1 [] and #v[2] agree at step 0)
theorem w3c3_3 : ¬ drop0% Iris.vec_cons_discrete 5 := fun h => by
  have := (@h TN _ 0 ⟨1⟩ #v[] _).discrete (y := #v[⟨2⟩]) (vec_dist_toList.mpr (by simp; exact .cons tn12 .nil))
  have := congrArg Vector.toList this
  simp at this

-- `Iris.vec_cons_discrete` idx 6: necessary (x = 0 discrete over TN, v = #v[1]: cons 0 v and #v[0, 2] agree at step 0)
theorem w3c3_4 : ¬ drop0% Iris.vec_cons_discrete 6 := fun h => by
  have := (@h TN _ 1 ⟨0⟩ #v[⟨1⟩] _).discrete (y := #v[⟨0⟩, ⟨2⟩])
    (vec_dist_toList.mpr (by simp; exact .cons (OFE.Dist.of_eq rfl) (.cons tn12 .nil)))
  have := congrArg Vector.toList this
  simp at this

-- `Iris.vec_getElem_ne` idx 4: necessary (n = 0, i = 0)
theorem w3c3_5 : ¬ indep0% Iris.vec_getElem_ne 4 := fun h => absurd (@h Unit _ 0 0) (by decide)

-- `Iris.vec_map_ext_ne` idx 9: necessary (alpha = Unit, beta = D2, f = const e, g = const a, v = #v[()])
theorem w3c3_6 : ¬ drop0% Iris.vec_map_ext_ne 9 := fun h => by
  have := vec_dist_toList.mp (@h Unit D2 1 _ _ 0 (fun _ => .e) (fun _ => .a) #v[()])
  have h2 : [D2.e] ≡{0}≡ [D2.a] := by simpa using this
  exact absurd (show D2.e = D2.a from (cons_dist_inj h2).1) (by decide)

-- `Iris.vec_map_ne` idx 8: necessary (alpha = Unit, beta = D2, f = const e, g = const a, u = v = #v[()])
theorem w3c3_7 : ¬ drop0% Iris.vec_map_ne 8 := fun h => by
  have := vec_dist_toList.mp (@h Unit D2 1 _ _ 0 (fun _ => .e) (fun _ => .a) #v[()] #v[()] OFE.Dist.rfl)
  have h2 : [D2.e] ≡{0}≡ [D2.a] := by simpa using this
  exact absurd (show D2.e = D2.a from (cons_dist_inj h2).1) (by decide)

-- `Iris.vec_map_ne` idx 11: necessary (alpha = beta = D2, f = g = id, u = #v[e], v = #v[a])
theorem w3c3_8 : ¬ drop0% Iris.vec_map_ne 11 := fun h => by
  have := vec_dist_toList.mp (@h D2 D2 1 _ _ 0 id id (fun h => h) #v[.e] #v[.a])
  have h2 : [D2.e] ≡{0}≡ [D2.a] := by simpa using this
  exact absurd (show D2.e = D2.a from (cons_dist_inj h2).1) (by decide)
