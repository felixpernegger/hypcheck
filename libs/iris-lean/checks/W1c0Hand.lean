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
namespace W1c0
open Iris Iris.OFE

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
theorem tn_dist {n} {x y : TN} : x ≡{n}≡ y ↔ min x.v (n+1) = min y.v (n+1) := Iff.rfl
theorem tn12 : (⟨1⟩ : TN) ≡{0}≡ ⟨2⟩ := rfl
theorem tn12ne : (⟨1⟩ : TN) ≠ ⟨2⟩ := by simp

/-- Raw agreement element with the given TN values. -/
def R (l : List Nat) (h : l ≠ [] := by simp) : Agree.Raw TN := ⟨l.map TN.mk, by simpa using h⟩
/-- Non-non-expansive map on TN: 1 ↦ 0, else ↦ 1. -/
def bad (x : TN) : TN := if x.v = 1 then ⟨0⟩ else ⟨1⟩

/-- Map on TN that is 0-close to the constant 1 but not non-expansive at step 1 (2 and 3 agree at 1). -/
def badc (x : TN) : TN := if x.v = 2 then ⟨1⟩ else ⟨2⟩
theorem badc_near (a : TN) : badc a ≡{0}≡ Function.const TN (⟨1⟩ : TN) a := by
  show min (badc a).v 1 = min 1 1; unfold badc; split <;> rfl
theorem badc_not_ne : badc ⟨2⟩ ≡{1}≡ badc ⟨3⟩ → False := by simp [badc, tn_dist]

/-- Discrete (Leibniz) OFE on Nat. -/
structure LD where v : Nat
instance : OFE LD := OFE.ofDiscrete LD
instance : OFE.Discrete LD := ⟨id⟩
/-- Raw agreement element with the given LD values. -/
def RD (l : List Nat) (h : l ≠ [] := by simp) : Agree.Raw LD := ⟨l.map LD.mk, by simpa using h⟩
/-- Agreement element with the given TN values. -/
def A (l : List Nat) (h : l ≠ [] := by simp) : Agree TN := Agree.mk (R l h)

end W1c0
open W1c0 Iris Iris.OFE

-- `Iris.Agree.Raw.op_sameElems` idx 6
theorem w0_1 : ¬ drop0% Iris.Agree.Raw.op_sameElems 6 := fun h => by
  have := @h TN (R [0]) (R [0]) (R [0]) (R [1]) (Agree.Raw.sameElems_equivalence.refl _)
  simp [Agree.Raw.SameElems, Agree.Raw.op, R] at this
-- `Iris.Agree.Raw.dist_lt` idx 6
theorem w0_2 : ¬ drop0% Iris.Agree.Raw.dist_lt 6 := fun h => by
  have := @h TN _ 1 0 (R [0]) (R [1]) (by omega)
  simp [Agree.Raw.dist, R, tn_dist] at this
-- `Iris.Agree.Raw.dist_lt` idx 7
theorem w0_3 : ¬ drop0% Iris.Agree.Raw.dist_lt 7 := fun h => by
  have := @h TN _ 0 1 (R [1]) (R [2]) (by simp [Agree.Raw.dist, R, tn_dist])
  simp [Agree.Raw.dist, R, tn_dist] at this
-- `Iris.Agree.Raw.dist_of_sameElems` idx 4
theorem w0_4 : ¬ drop0% Iris.Agree.Raw.dist_of_sameElems 4 := fun h => by
  have := @h TN _ (R [0]) (R [1]) 0
  simp [Agree.Raw.dist, R, tn_dist] at this
-- `Iris.Agree.Raw.validN_congr` idx 5
theorem w0_5 : ¬ drop0% Iris.Agree.Raw.validN_congr 5 := fun h => by
  have := (@h TN _ 0 (R [0]) (R [0, 1])).mp (by simp [Agree.Raw.validN_iff, R])
  simp [Agree.Raw.validN_iff, R, tn_dist] at this
-- `Iris.Agree.Raw.validN_ne` idx 5
theorem w0_6 : ¬ drop0% Iris.Agree.Raw.validN_ne 5 := fun h => by
  have := @h TN _ 0 (R [0]) (R [0, 1]) (by simp [Agree.Raw.validN_iff, R])
  simp [Agree.Raw.validN_iff, R, tn_dist] at this
-- `Iris.Agree.Raw.validN_ne` idx 6
theorem w0_7 : ¬ drop0% Iris.Agree.Raw.validN_ne 6 := fun h => by
  have := @h TN _ 0 (R [0, 1]) (R [0, 1]) (Agree.Raw.dist_equiv.refl _)
  simp [Agree.Raw.validN_iff, R, tn_dist] at this
-- `Iris.Agree.Raw.validN_succ` idx 4
theorem w0_8 : ¬ drop0% Iris.Agree.Raw.validN_succ 4 := fun h => by
  have := @h TN _ 0 (R [0, 1])
  simp [Agree.Raw.validN_iff, R, tn_dist] at this
-- `Iris.Agree.Raw.validN_op_left` idx 5
theorem w0_9 : ¬ drop0% Iris.Agree.Raw.validN_op_left 5 := fun h => by
  have := @h TN _ 0 (R [0, 1]) (R [0])
  simp [Agree.Raw.validN_iff, R, tn_dist] at this
-- `Iris.Agree.Raw.op_ne₂` idx 7
theorem w0_10 : ¬ drop0% Iris.Agree.Raw.op_ne₂ 7 := fun h => by
  have := @h TN _ 0 (R [0]) (R [1]) (R [0]) (R [0]) (Agree.Raw.dist_equiv.refl _)
  simp [Agree.Raw.dist, Agree.Raw.op, R, tn_dist] at this
-- `Iris.Agree.Raw.op_invN` idx 5
theorem w0_11 : ¬ drop0% Iris.Agree.Raw.op_invN 5 := fun h => by
  have := @h TN _ 0 (R [0]) (R [1])
  simp [Agree.Raw.dist, R, tn_dist] at this
-- `Iris.Agree.Raw.op_inv` idx 4
theorem w0_12 : ¬ drop0% Iris.Agree.Raw.op_inv 4 := fun h => by
  have := @h TN _ (R [0]) (R [1]) 0
  simp [Agree.Raw.dist, R, tn_dist] at this
-- `Iris.Agree.Raw.toAgree_uninjN` idx 4
theorem w0_13 : ¬ drop0% Iris.Agree.Raw.toAgree_uninjN 4 := fun h => by
  obtain ⟨a, ha⟩ := @h TN _ 0 (R [0, 1])
  simp [Agree.Raw.dist, Agree.Raw.toAgree, R, tn_dist] at ha
  omega
-- `Iris.Agree.Raw.toAgree_uninj` idx 3
theorem w0_14 : ¬ drop0% Iris.Agree.Raw.toAgree_uninj 3 := fun h => by
  obtain ⟨a, ha⟩ := @h TN _ (R [0, 1])
  have := ha 0
  simp [Agree.Raw.dist, Agree.Raw.toAgree, R, tn_dist] at this
  omega
-- `Iris.Agree.Raw.map'_ne` idx 6
theorem w0_15 : ¬ drop0% Iris.Agree.Raw.map'_ne 6 := fun h => by
  have := @h TN TN _ _ bad 0 (R [1]) (R [2]) (by simp [Agree.Raw.dist, R, tn_dist])
  simp [Agree.Raw.dist, Agree.Raw.map', R, tn_dist, bad] at this
-- `Iris.Agree.Raw.map'_ne` idx 9
theorem w0_16 : ¬ drop0% Iris.Agree.Raw.map'_ne 9 := fun h => by
  have := @h TN TN _ _ id 0 _ (R [0]) (R [1])
  simp [Agree.Raw.dist, Agree.Raw.map', R, tn_dist] at this
-- `Iris.Agree.Raw.map'_validN` idx 6
theorem w0_17 : ¬ drop0% Iris.Agree.Raw.map'_validN 6 := fun h => by
  have := @h TN TN _ _ bad 0 (R [1, 2]) (by simp [Agree.Raw.validN_iff, R, tn_dist])
  simp [Agree.Raw.validN_iff, Agree.Raw.map', R, tn_dist, bad] at this
-- `Iris.Agree.Raw.map'_validN` idx 8
theorem w0_18 : ¬ drop0% Iris.Agree.Raw.map'_validN 8 := fun h => by
  have := @h TN TN _ _ id 0 _ (R [0, 1])
  simp [Agree.Raw.validN_iff, Agree.Raw.map', R, tn_dist] at this
-- `Iris.Agree.Raw.discrete_0` idx 2
theorem w0_19 : ¬ drop0% Iris.Agree.Raw.discrete_0 2 := fun h => by
  have := @h TN _ (R [1]) (R [2]) (by simp [Agree.Raw.dist, R, tn_dist]) 1
  simp [Agree.Raw.dist, R, tn_dist] at this
-- `Iris.Agree.Raw.discrete_0` idx 5
theorem w0_20 : ¬ drop0% Iris.Agree.Raw.discrete_0 5 := fun h => by
  have := @h LD _ _ (RD [0]) (RD [1]) 0
  simp [Agree.Raw.dist, RD] at this
  cases this
-- `Iris.Agree.Raw.discrete_valid` idx 2
theorem w0_21 : ¬ drop0% Iris.Agree.Raw.discrete_valid 2 := fun h => by
  have := @h TN _ (R [1, 2]) (by simp [Agree.Raw.validN_iff, R, tn_dist]) 1
  simp [Agree.Raw.validN_iff, R, tn_dist] at this
-- `Iris.Agree.Raw.discrete_valid` idx 4
theorem w0_22 : ¬ drop0% Iris.Agree.Raw.discrete_valid 4 := fun h => by
  have := @h LD _ _ (RD [0, 1]) 0
  simp [Agree.Raw.validN_iff, RD] at this
  obtain ⟨h1, -⟩ := this
  cases h1
-- `Iris.Agree.Raw.toAgree_discrete` idx 3
theorem w0_23 : ¬ drop0% Iris.Agree.Raw.toAgree_discrete 3 := fun h => by
  have := @h TN _ ⟨1⟩ (R [2]) (by simp [Agree.Raw.dist, Agree.Raw.toAgree, R, tn_dist]) 1
  simp [Agree.Raw.dist, Agree.Raw.toAgree, R, tn_dist] at this
-- `Iris.Agree.Raw.toAgree_discrete` idx 5
theorem w0_24 : ¬ drop0% Iris.Agree.Raw.toAgree_discrete 5 := fun h => by
  have := @h LD _ ⟨0⟩ _ (RD [1]) 0
  simp [Agree.Raw.dist, Agree.Raw.toAgree, RD] at this
  cases this
-- `Iris.Agree.ind` idx 2
theorem w0_25 : ¬ drop0% Iris.Agree.ind 2 := fun h => @h TN (fun _ => False) (A [0])
-- `Iris.Agree.ind₂` idx 2
theorem w0_26 : ¬ drop0% Iris.Agree.ind₂ 2 := fun h => @h TN (fun _ _ => False) (A [0]) (A [0])
-- `Iris.Agree.ind₃` idx 2
theorem w0_27 : ¬ drop0% Iris.Agree.ind₃ 2 := fun h => @h TN (fun _ _ _ => False) (A [0]) (A [0]) (A [0])
-- `Iris.Agree.sound` idx 3
theorem w0_28 : ¬ drop0% Iris.Agree.sound 3 := fun h => by
  have := Agree.exact (@h TN (R [0]) (R [1]))
  simp [Agree.Raw.SameElems, R] at this
-- `Iris.Agree.lift_mk` idx 3 (resp), refuted at gamma = Raw TN (universe 1: at Prop the claim holds by proof irrelevance)
theorem w0_29 : ¬ (∀ {α : Type} {γ : Type} (f : Agree.Raw α → γ) (x x' y : Agree.Raw α),
    x'.SameElems y → f x' = f y) := fun h => by
  have := congrArg Agree.Raw.car (@h TN (Agree.Raw TN) id (R [0]) (R [0]) (R [0, 0])
    ⟨by simp [R], by simp [R]⟩)
  simp [R] at this
-- `Iris.Agree.lift₂_mk` idx 3 (resp), refuted at gamma = Raw TN
theorem w0_30 : ¬ (∀ {α : Type} {γ : Type} (f : Agree.Raw α → Agree.Raw α → γ) (x y a b c d : Agree.Raw α),
    a.SameElems c → b.SameElems d → f a b = f c d) := fun h => by
  have := congrArg Agree.Raw.car (@h TN (Agree.Raw TN) (fun a _ => a) (R [0]) (R [0]) (R [0]) (R [0]) (R [0, 0]) (R [0])
    ⟨by simp [R], by simp [R]⟩ (Agree.Raw.sameElems_equivalence.refl _))
  simp [R] at this
-- `Iris.Agree.validN_ne` idx 5
theorem w0_31 : ¬ drop0% Iris.Agree.validN_ne 5 := fun h => by
  have := @h TN _ 0 (A [0]) (A [0, 1]) (by simp [A, Agree.Raw.validN_iff, R])
  simp [A, Agree.Raw.validN_iff, R, tn_dist] at this
-- `Iris.Agree.validN_ne` idx 6
theorem w0_32 : ¬ drop0% Iris.Agree.validN_ne 6 := fun h => by
  have := @h TN _ 0 (A [0, 1]) (A [0, 1]) .rfl
  simp [A, Agree.Raw.validN_iff, R, tn_dist] at this
-- `Iris.Agree.validN_succ` idx 4
theorem w0_33 : ¬ drop0% Iris.Agree.validN_succ 4 := fun h => by
  have := @h TN _ 0 (A [0, 1])
  simp [A, Agree.Raw.validN_iff, R, tn_dist] at this
-- `Iris.Agree.validN_op_left` idx 5
theorem w0_34 : ¬ drop0% Iris.Agree.validN_op_left 5 := fun h => by
  have := @h TN _ 0 (A [0, 1]) (A [0])
  simp [A, Agree.Raw.validN_iff, R, tn_dist] at this
-- `Iris.Agree.op_invN` idx 5
theorem w0_35 : ¬ drop0% Iris.Agree.op_invN 5 := fun h => by
  have := @h TN _ 0 (A [0]) (A [1])
  simp [A, Agree.Raw.dist, R, tn_dist] at this
-- `Iris.Agree.op_inv` idx 4
theorem w0_36 : ¬ drop0% Iris.Agree.op_inv 4 := fun h => by
  have := Agree.exact (@h TN _ (A [0]) (A [1]))
  simp [Agree.Raw.SameElems, R] at this
-- `Iris.Agree.instDiscrete` idx 2
theorem w0_37 : ¬ drop0% Iris.Agree.instDiscrete 2 := fun h => by
  have := Agree.exact ((@h TN _).discrete_0 (x := A [1]) (y := A [2]) (by simp [A, Agree.Raw.dist, R, tn_dist]))
  simp [Agree.Raw.SameElems, R] at this
-- `Iris.Agree.instORADiscrete` idx 2
theorem w0_38 : ¬ drop0% Iris.Agree.instORADiscrete 2 := fun h => by
  have := Agree.exact ((@h TN _).discrete_0 (x := A [1]) (y := A [2]) (by simp [A, Agree.Raw.dist, R, tn_dist]))
  simp [Agree.Raw.SameElems, R] at this
-- `Iris.Agree.valid_ordN` idx 5
theorem w0_39 : ¬ drop0% Iris.Agree.valid_ordN 5 := fun h => by
  have := @h TN _ 0 (A [0]) (A [0, 1]) ⟨A [1], .rfl⟩
  simp [A, Agree.Raw.dist, R, tn_dist] at this
-- `Iris.Agree.valid_ordN` idx 6
theorem w0_40 : ¬ drop0% Iris.Agree.valid_ordN 6 := fun h => by
  have := @h TN _ 0 (A [0]) (A [1]) (by simp [Agree.validN_def, A, Agree.Raw.validN_iff, R])
  simp [A, Agree.Raw.dist, R, tn_dist] at this
-- `Iris.Agree.valid_includedN` idx 5
theorem w0_41 : ¬ drop0% Iris.Agree.valid_includedN 5 := fun h => by
  have := @h TN _ 0 (A [0]) (A [0, 1]) ⟨A [1], .rfl⟩
  simp [A, Agree.Raw.dist, R, tn_dist] at this
-- `Iris.Agree.valid_includedN` idx 6
theorem w0_42 : ¬ drop0% Iris.Agree.valid_includedN 6 := fun h => by
  have := @h TN _ 0 (A [0]) (A [1]) (by simp [Agree.validN_def, A, Agree.Raw.validN_iff, R])
  simp [A, Agree.Raw.dist, R, tn_dist] at this
-- `Iris.Agree.valid_ord` idx 4
theorem w0_43 : ¬ drop0% Iris.Agree.valid_ord 4 := fun h => by
  have := Agree.exact (@h TN _ (A [0]) (A [0, 1]) ⟨A [1], rfl⟩)
  simp [Agree.Raw.SameElems, R] at this
-- `Iris.Agree.valid_ord` idx 5
theorem w0_44 : ¬ drop0% Iris.Agree.valid_ord 5 := fun h => by
  have := Agree.exact (@h TN _ (A [0]) (A [1]) (fun n => by simp [Agree.Raw.validN_iff, R]))
  simp [Agree.Raw.SameElems, R] at this
-- `Iris.Agree.valid_included` idx 4
theorem w0_45 : ¬ drop0% Iris.Agree.valid_included 4 := fun h => by
  have := Agree.exact (@h TN _ (A [0]) (A [0, 1]) ⟨A [1], rfl⟩)
  simp [Agree.Raw.SameElems, R] at this
-- `Iris.Agree.valid_included` idx 5
theorem w0_46 : ¬ drop0% Iris.Agree.valid_included 5 := fun h => by
  have := Agree.exact (@h TN _ (A [0]) (A [1]) (fun n => by simp [Agree.Raw.validN_iff, R]))
  simp [Agree.Raw.SameElems, R] at this
-- `Iris.Agree.toAgree_uninjN` idx 4
theorem w0_47 : ¬ drop0% Iris.Agree.toAgree_uninjN 4 := fun h => by
  obtain ⟨a, ha⟩ := @h TN _ 0 (A [0, 1])
  simp [toAgree, A, Agree.Raw.dist, Agree.Raw.toAgree, R, tn_dist] at ha
  omega
-- `Iris.Agree.toAgree_uninj` idx 3
theorem w0_48 : ¬ drop0% Iris.Agree.toAgree_uninj 3 := fun h => by
  obtain ⟨⟨a⟩, ha⟩ := @h TN _ (A [0, 1])
  have := Agree.exact ha
  simp [Agree.Raw.SameElems, Agree.Raw.toAgree, R] at this
  omega
-- `Iris.Agree.toAgree.is_discrete` idx 3
theorem w0_49 : ¬ drop0% Iris.Agree.toAgree.is_discrete 3 := fun h => by
  have := Agree.exact ((@h TN _ ⟨1⟩).discrete (y := A [2]) (by simp [toAgree, A, Agree.Raw.dist, Agree.Raw.toAgree, R, tn_dist]))
  simp [Agree.Raw.SameElems, Agree.Raw.toAgree, R] at this
-- `Iris.instNonExpansive_AgreeMap'` idx 5
theorem w0_50 : ¬ drop0% Iris.instNonExpansive_AgreeMap' 5 := fun h => by
  have := (@h TN TN _ _ bad).ne (n := 0) (x₁ := A [1]) (x₂ := A [2]) (by simp [A, Agree.Raw.dist, R, tn_dist])
  simp [A, Agree.Raw.dist, Agree.Raw.map', R, tn_dist, bad] at this
-- `Iris.Agree.map_mk` idx 5
theorem w0_51 : ¬ indep0% Iris.Agree.map_mk 5 := fun h => by
  have := (@h TN TN _ _ bad (R [0])).ne (n := 0) (x₁ := ⟨1⟩) (x₂ := ⟨2⟩) tn12
  simp [tn_dist, bad] at this
-- `Iris.Agree.map_ne` idx 7
theorem w0_52 : ¬ indep0% Iris.Agree.map_ne 7 := fun h =>
  badc_not_ne ((@h TN TN _ _ 0 badc (Function.const TN ⟨1⟩) OFE.const_ne (A [0]) badc_near).ne
    (n := 1) (x₁ := ⟨2⟩) (x₂ := ⟨3⟩) rfl)
-- `Iris.Agree.map_ne` idx 8
theorem w0_53 : ¬ indep0% Iris.Agree.map_ne 8 := fun h =>
  badc_not_ne ((@h TN TN _ _ 0 (Function.const TN ⟨1⟩) badc OFE.const_ne (A [0])
    (fun a => (badc_near a).symm)).ne (n := 1) (x₁ := ⟨2⟩) (x₂ := ⟨3⟩) rfl)
-- `Iris.Agree.map_ne` idx 10
theorem w0_54 : ¬ drop0% Iris.Agree.map_ne 10 := fun h => by
  have := @h TN TN _ _ 0 (Function.const TN ⟨0⟩) (Function.const TN ⟨1⟩) OFE.const_ne OFE.const_ne (A [0])
  simp [A, Agree.map, Agree.Raw.dist, Agree.Raw.map', R, tn_dist] at this
-- `Iris.Agree.agree_map_ext` idx 6
-- removable: H gives f = g by funext, so NonExpansive f is NonExpansive g
theorem w0_55 : indep% Iris.Agree.agree_map_ext 6 := by
  intro α β _ _ f g hg x H
  have : f = g := funext H
  subst this; exact hg
-- `Iris.Agree.agree_map_ext` idx 7
-- removable: H gives f = g by funext, so NonExpansive g is NonExpansive f
theorem w0_56 : indep% Iris.Agree.agree_map_ext 7 := by
  intro α β _ _ f g hf x H
  have : f = g := funext H
  subst this; exact hf
-- `Iris.Agree.agree_map_ext` idx 9
theorem w0_57 : ¬ drop0% Iris.Agree.agree_map_ext 9 := fun h => by
  have := Agree.exact (@h TN TN _ _ (Function.const TN ⟨0⟩) (Function.const TN ⟨1⟩) OFE.const_ne OFE.const_ne (A [0]))
  simp [Agree.Raw.SameElems, Agree.Raw.map', R] at this
-- `Iris.Agree.map_toAgree` idx 5
theorem w0_58 : ¬ indep0% Iris.Agree.map_toAgree 5 := fun h => by
  have := (@h TN TN _ _ bad ⟨0⟩).ne (n := 0) (x₁ := ⟨1⟩) (x₂ := ⟨2⟩) tn12
  simp [tn_dist, bad] at this
namespace W1c0
open Iris Iris.OFE

/-- Two-element commutative monoid (e unit, a idempotent) with the equality order (as Probe3 NA). -/
inductive NA | e | a deriving DecidableEq
def NA.op : NA → NA → NA
  | .e, y => y
  | .a, _ => .a
instance : OFE NA := OFE.ofDiscrete NA
instance : OFE.Discrete NA := ⟨id⟩
@[instance_reducible] def naData : DiscreteORAData NA where
  pcore := fun _ => some .e
  op := NA.op
  Valid := fun _ => True
  Order := Eq
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := fun _ _ _ h1 h2 => h1.trans h2
  op_mono_left := by intro x y z h; cases h; rfl
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; rfl
  increasing_closed := by intro x y _ h; cases h; assumption
instance naORA : ORA NA := ORA.ofDiscreteORAData naData
instance : ORA.Discrete NA := ORA.ofDiscreteORAData_discrete naData
instance : OrderRefl NA := ⟨fun x => show x = x from rfl⟩
instance naUORA : UORA NA where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

/-- Three elements e (unit), a (idempotent), z (absorbing, the only invalid one); order: x ≤ y iff
y = z or x ≠ z. So a ≤ e although a is not included in e: not OrdInc. -/
inductive TX | e | a | z deriving DecidableEq
def TX.op : TX → TX → TX
  | .e, y => y
  | x, .e => x
  | .a, .a => .a
  | _, _ => .z
instance : OFE TX := OFE.ofDiscrete TX
instance : OFE.Discrete TX := ⟨id⟩
@[instance_reducible] def txData : DiscreteORAData TX where
  pcore := fun _ => some .e
  op := TX.op
  Valid := fun x => x ≠ .z
  Order := fun x y => y = .z ∨ x ≠ .z
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y; cases x <;> cases y <;> decide
  ord_trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  op_mono_left := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  valid_of_ord := by intro x y; cases x <;> cases y <;> decide
  pcore_mono := by intro x y cx h1 h2; cases h2; exact ⟨.e, rfl, by decide⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨.e, rfl, by decide⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> decide
  increasing_closed := by intro x y _ _ w; cases y <;> cases w <;> decide
instance txORA : ORA TX := ORA.ofDiscreteORAData txData
instance : ORA.Discrete TX := ORA.ofDiscreteORAData_discrete txData
instance : OrderRefl TX := ⟨fun x => show x = .z ∨ x ≠ .z by cases x <;> decide⟩
instance txUORA : UORA TX where
  unit := .e
  unit_valid := show TX.e ≠ .z by decide
  unit_left_id := rfl
  pcore_unit := rfl

/-- Three elements e (unit), a, z (a • a = z absorbing, the only invalid one) with the
extension order (x ≤ y iff x = e, x = y or y = z). -/
inductive EX | e | a | z deriving DecidableEq
def EX.op : EX → EX → EX
  | .e, y => y
  | x, .e => x
  | _, _ => .z
instance : OFE EX := OFE.ofDiscrete EX
instance : OFE.Discrete EX := ⟨id⟩
@[instance_reducible] def exData : DiscreteORAData EX where
  pcore := fun _ => some .e
  op := EX.op
  Valid := fun x => x ≠ .z
  Order := fun x y => x = .e ∨ x = y ∨ y = .z
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y; cases x <;> cases y <;> decide
  ord_trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  op_mono_left := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  valid_of_ord := by intro x y; cases x <;> cases y <;> decide
  pcore_mono := by intro x y cx h1 h2; cases h2; exact ⟨.e, rfl, by decide⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨.e, rfl, by decide⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> decide
  increasing_closed := by intro x y _ _ w; cases y <;> cases w <;> decide
instance exORA : ORA EX := ORA.ofDiscreteORAData exData
instance : OrderRefl EX := ⟨fun x => show x = .e ∨ x = x ∨ x = .z from .inr (.inl rfl)⟩
instance exUORA : UORA EX where
  unit := .e
  unit_valid := show EX.e ≠ .z by decide
  unit_left_id := rfl
  pcore_unit := rfl

/-- Two elements e (unit), a (absorbing), extension order, pcore = identity: everything is a
core, a is not included in e. -/
inductive AC | e | a deriving DecidableEq
def AC.op : AC → AC → AC
  | .e, y => y
  | .a, _ => .a
instance : OFE AC := OFE.ofDiscrete AC
instance : OFE.Discrete AC := ⟨id⟩
@[instance_reducible] def acData : DiscreteORAData AC where
  pcore := some
  op := AC.op
  Valid := fun _ => True
  Order := fun x y => x = .e ∨ x = y
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  op_mono_left := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; cases h2; exact ⟨y, rfl, h1⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨_, rfl, by cases x <;> cases y <;> decide⟩
  pcore_increasing := by intro x cx h y; cases h; cases x <;> cases y <;> decide
  increasing_closed := by intro x y _ _ w; cases y <;> cases w <;> decide
instance acORA : ORA AC := ORA.ofDiscreteORAData acData
instance : OrderRefl AC := ⟨fun x => show x = .e ∨ x = x from .inr rfl⟩
instance acUORA : UORA AC where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

end W1c0
namespace W1c0
open Iris Iris.OFE

instance : ORA.Discrete AC := ORA.ofDiscreteORAData_discrete acData
instance : OrdInc NA := ⟨fun {x y} h => by cases h; exact ⟨.e, by cases x <;> rfl⟩,
  fun {n x y} h => by cases h; exact ⟨.e, by cases x <;> rfl⟩⟩

instance : OrdInc EX := ⟨fun {x y} h => by
    cases x <;> cases y <;> first | exact ⟨.e, rfl⟩ | exact ⟨.a, rfl⟩ | exact ⟨.z, rfl⟩ |
      (rcases h with h | h | h <;> cases h),
  fun {n x y} h => by
    cases x <;> cases y <;> first | exact ⟨.e, rfl⟩ | exact ⟨.a, rfl⟩ | exact ⟨.z, rfl⟩ |
      (rcases h with h | h | h <;> cases h)⟩

/-- Two elements e (unit), a (absorbing); order: extension order (x = e or x = y), but the
step-indexed order is everything. An affine UORA that is not ORA.Discrete (a ≼ₒ{n} e for all n,
not a ≼ₒ e). -/
inductive AN | e | a deriving DecidableEq
def AN.op : AN → AN → AN
  | .e, y => y
  | .a, _ => .a
instance : OFE AN := OFE.ofDiscrete AN
instance : OFE.Discrete AN := ⟨id⟩
@[instance_reducible] def anData : DiscreteORAData AN where
  pcore := fun _ => some .e
  op := AN.op
  Valid := fun _ => True
  Order := fun x y => x = .e ∨ x = y
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  op_mono_left := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; cases h2; exact ⟨.e, rfl, .inl rfl⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨.e, rfl, .inl rfl⟩
  pcore_increasing := by intro x cx h y; cases h; exact .inr rfl
  increasing_closed := by intro x y _ _ w; cases y <;> cases w <;> decide
@[instance_reducible] def anBase : ORA AN := ORA.ofDiscreteORAData anData
instance anOp : Op AN := anBase.toOp
instance anPCore : PCore AN := anBase.toPCore
instance anValid : Valid AN := anBase.toValid
instance anOrd : Ordered AN where
  OrderN _ _ _ := True
  Order x y := x = .e ∨ x = y
  ordN_ne := fun _ _ _ => trivial
  ordN_succ := fun _ => trivial
  ordN_trans := fun _ _ => trivial
  ord_trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  ordN_of_ord := fun _ _ => trivial
instance anORA : ORA AN where
  validN_op_left := fun _ => trivial
  pcore_op_left := fun {x _} h => by cases h; cases x <;> rfl
  extend := fun {_ _ y₁ y₂} _ h => ⟨y₁, y₂, h, .rfl, .rfl⟩
  op_monoN_left_ord := fun _ _ => trivial
  op_mono_left_ord := fun {x y} z h => by
    show _ = AN.e ∨ _ = _
    cases x <;> cases y <;> cases z <;> first | exact Or.inl rfl | exact Or.inr rfl | (rcases h with h | h <;> cases h)
  validN_of_ordN := fun _ _ => trivial
  pcore_monoN_ord := fun {_ _ _ _} _ h => by cases h; exact ⟨.e, rfl, trivial⟩
  pcore_mono_ord := fun {_ _ _} _ h => by cases h; exact ⟨.e, rfl, .inl rfl⟩
  pcore_order_op := fun {_ _} h _ => by cases h; exact ⟨.e, rfl, .inl rfl⟩
  pcore_increasing := fun {_ _} h => by
    cases h; exact ⟨fun y => show y = .e ∨ y = AN.op .e y from .inr rfl⟩
  increasing_closed := fun {_ _ y} _ _ =>
    ⟨fun w => by
      show w = AN.e ∨ w = AN.op y w
      cases y <;> cases w <;> first | exact Or.inl rfl | exact Or.inr rfl⟩
  ordN_extend := fun {_ x _} _ _ => ⟨x, trivial, .rfl⟩
instance : OrderRefl AN := ⟨fun x => show x = .e ∨ x = x from .inr rfl⟩
instance anUORA : UORA AN where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl
instance : IncOrd AN := ⟨fun {x y} ⟨z, hz⟩ => by
  show x = .e ∨ x = y
  cases x <;> cases z <;> cases y <;> first | exact Or.inl rfl | exact Or.inr rfl | cases hz⟩

end W1c0
namespace W1c0
open Iris Iris.OFE

/-- Two elements e (unit), a (absorbing), extension order, discrete OFE, but a is valid only at
step 0: OFE.Discrete without ORA.Discrete. -/
inductive VN | e | a deriving DecidableEq
def VN.op : VN → VN → VN
  | .e, y => y
  | .a, _ => .a
instance : OFE VN := OFE.ofDiscrete VN
instance : OFE.Discrete VN := ⟨id⟩
@[instance_reducible] def vnData : DiscreteORAData VN where
  pcore := fun _ => some .e
  op := VN.op
  Valid := fun _ => True
  Order := fun x y => x = .e ∨ x = y
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  op_mono_left := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; cases h2; exact ⟨.e, rfl, .inl rfl⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨.e, rfl, .inl rfl⟩
  pcore_increasing := by intro x cx h y; cases h; exact .inr rfl
  increasing_closed := by intro x y _ _ w; cases y <;> cases w <;> decide
@[instance_reducible] def vnBase : ORA VN := ORA.ofDiscreteORAData vnData
instance vnOp : Op VN := vnBase.toOp
instance vnPCore : PCore VN := vnBase.toPCore
instance vnOrd : Ordered VN := vnBase.toOrdered
instance vnValid : Valid VN where
  ValidN n x := x = .e ∨ n = 0
  Valid x := x = .e
  validN_ne := fun h hv => h ▸ hv
  valid_iff_validN := fun {x} => ⟨fun h _ => .inl h, fun h => by
    rcases h 1 with h | h
    · exact h
    · cases h⟩
  validN_succ := fun {_ x} h => by rcases h with h | h; exact .inl h; cases h
instance vnORA : ORA VN where
  validN_op_left := fun {n x y} h => by
    rcases h with h | h
    · cases x <;> cases y <;> first | exact .inl rfl | cases h
    · exact .inr h
  pcore_op_left := fun {x _} h => by cases h; cases x <;> rfl
  extend := fun {_ _ y₁ y₂} _ h => ⟨y₁, y₂, h, .rfl, .rfl⟩
  op_monoN_left_ord := fun {_ x y} z h => vnData.op_mono_left x y z h
  op_mono_left_ord := fun {x y} z h => vnData.op_mono_left x y z h
  validN_of_ordN := fun {n x y} h hv => by
    rcases hv with hv | hv
    · subst hv; rcases h with h | h <;> exact .inl h
    · exact .inr hv
  pcore_monoN_ord := fun {_ _ _ _} _ h => by cases h; exact ⟨.e, rfl, .inl rfl⟩
  pcore_mono_ord := fun {_ _ _} _ h => by cases h; exact ⟨.e, rfl, .inl rfl⟩
  pcore_order_op := fun {_ _} h _ => by cases h; exact ⟨.e, rfl, .inl rfl⟩
  pcore_increasing := fun {_ _} h => by
    cases h; exact ⟨fun y => show y = .e ∨ y = VN.op .e y from .inr rfl⟩
  increasing_closed := fun {_ _ y} _ _ =>
    ⟨fun w => by
      show w = VN.e ∨ w = VN.op y w
      cases y <;> cases w <;> first | exact Or.inl rfl | exact Or.inr rfl⟩
  ordN_extend := fun {_ x _} _ h => ⟨x, h, .rfl⟩
instance : OrderRefl VN := ⟨fun x => show x = .e ∨ x = x from .inr rfl⟩
instance vnUORA : UORA VN where
  unit := .e
  unit_valid := show VN.e = .e from rfl
  unit_left_id := rfl
  pcore_unit := rfl

end W1c0
namespace W1c0
open Iris Iris.OFE

/-- Max-monoid on the non-discrete OFE TN (unit 0, all valid, order ≤ on truncations):
a UORA whose unit is discrete but 1 is not. -/
instance mtOp : Op TN where
  op x y := ⟨max x.v y.v⟩
  op_ne := ⟨fun {n} y₁ y₂ (h : min y₁.v (n+1) = min y₂.v (n+1)) =>
    show min (max _ y₁.v) (n+1) = min (max _ y₂.v) (n+1) by omega⟩
  assoc := congrArg TN.mk (Nat.max_assoc ..).symm
  comm := congrArg TN.mk (Nat.max_comm ..)
instance mtPCore : PCore TN where
  pcore _ := some ⟨0⟩
  pcore_ne _ h := by cases h; exact ⟨_, rfl, .rfl⟩
  pcore_idem h := by cases h; rfl
instance mtValid : Valid TN where
  ValidN _ _ := True
  Valid _ := True
  validN_ne _ _ := trivial
  valid_iff_validN := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ _ := trivial
instance mtOrd : Ordered TN where
  OrderN n x y := min x.v (n+1) ≤ min y.v (n+1)
  Order x y := x.v ≤ y.v
  ordN_ne {n x x' y y'} (hx : min x.v (n+1) = min x'.v (n+1)) (hy : min y.v (n+1) = min y'.v (n+1)) h := by
    show min x'.v (n+1) ≤ min y'.v (n+1); omega
  ordN_succ {n x y} (h : min x.v (n+1+1) ≤ min y.v (n+1+1)) := by show min x.v (n+1) ≤ min y.v (n+1); omega
  ordN_trans {n x y z} (h1 : min x.v (n+1) ≤ min y.v (n+1)) (h2 : min y.v (n+1) ≤ min z.v (n+1)) :=
    Nat.le_trans h1 h2
  ord_trans h1 h2 := Nat.le_trans h1 h2
  ordN_of_ord {x y} n (h : x.v ≤ y.v) := by show min x.v (n+1) ≤ min y.v (n+1); omega
/-- Witness for the extension law of mtORA. -/
def mtSplit (n : Nat) (x y₁ y₂ : TN) : TN × TN :=
  if x.v ≤ n then (y₁, y₂) else if n < y₁.v then (x, ⟨min y₂.v x.v⟩) else (y₁, x)
instance mtORA : ORA TN where
  validN_op_left _ := trivial
  pcore_op_left h := by cases h; exact congrArg TN.mk (Nat.zero_max _)
  extend {n x y₁ y₂} _ h := by
    cases x with | mk x => cases y₁ with | mk a => cases y₂ with | mk b =>
    have h' : min x (n+1) = min (max a b) (n+1) := h
    refine ⟨(mtSplit n ⟨x⟩ ⟨a⟩ ⟨b⟩).1, (mtSplit n ⟨x⟩ ⟨a⟩ ⟨b⟩).2, ?_, ?_, ?_⟩ <;> simp only [mtSplit] <;>
      split <;> (try split) <;>
      first
        | exact .rfl
        | (show TN.mk x = TN.mk (max (Prod.fst _ : TN).v (Prod.snd _ : TN).v); simp only [TN.mk.injEq]; omega)
        | (show TN.mk x = TN.mk (max (Prod.fst _ : TN).v (Prod.snd _ : TN).v); congr 1; simp only []; omega)
        | (show min _ (n+1) = min _ (n+1); simp only []; omega)
  op_monoN_left_ord {n x y} z (h : min x.v (n+1) ≤ min y.v (n+1)) := by
    show min (max x.v z.v) (n+1) ≤ min (max y.v z.v) (n+1); omega
  op_mono_left_ord {x y} z (h : x.v ≤ y.v) := by show max x.v z.v ≤ max y.v z.v; omega
  validN_of_ordN _ _ := trivial
  pcore_monoN_ord _ h := by cases h; exact ⟨_, rfl, Nat.le_refl _⟩
  pcore_mono_ord _ h := by cases h; exact ⟨_, rfl, Nat.le_refl _⟩
  pcore_order_op h _ := by cases h; exact ⟨_, rfl, Nat.le_refl _⟩
  pcore_increasing h := by cases h; exact ⟨fun y => show y.v ≤ max 0 y.v by omega⟩
  increasing_closed _ _ := ⟨fun w => show w.v ≤ max _ w.v by omega⟩
  ordN_extend {n x y} _ (h : min x.v (n+1) ≤ min y.v (n+1)) :=
    ⟨⟨min x.v y.v⟩, show min (min x.v y.v) (n+1+1) ≤ min y.v (n+1+1) by omega,
      show min (min x.v y.v) (n+1) = min x.v (n+1) by omega⟩
instance : OrderRefl TN := ⟨fun x => Nat.le_refl x.v⟩
instance mtUORA : UORA TN where
  unit := ⟨0⟩
  unit_valid := trivial
  unit_left_id := congrArg TN.mk (Nat.zero_max _)
  pcore_unit := rfl
instance tn0disc : DiscreteE (⟨0⟩ : TN) := ⟨fun {y} h => by
  cases y with | mk v =>
    have h' : min 0 (0+1) = min v (0+1) := h
    have : v = 0 := by omega
    subst this; rfl⟩

end W1c0
namespace W1c0
open Iris Iris.OFE

/-- Nat where 0 and 1 agree at step 0 only (everything else discrete), with max: a UORA whose
unit 0 is not discrete while 2 is. -/
structure MS where v : Nat
instance msOFE : OFE MS where
  Dist n x y := x.v = y.v ∨ (n = 0 ∧ x.v ≤ 1 ∧ y.v ≤ 1)
  dist_eqv := ⟨fun _ => .inl rfl, fun h => by omega, fun h1 h2 => by omega⟩
  eq_dist' {x y} := ⟨fun h n => .inl (h ▸ rfl), fun h => by
      cases x with | mk a => cases y with | mk b =>
      have := h 1; simp only [MS.mk.injEq] at this ⊢; omega⟩
  dist_lt {n x y m} h hm := by omega
/-- Canonical representative at step n (0 and 1 merged at step 0). -/
def msF (n x : Nat) : Nat := if n = 0 ∧ x ≤ 1 then 0 else x
instance msOp : Op MS where
  op x y := ⟨max x.v y.v⟩
  op_ne := ⟨fun {n} y₁ y₂ (h : y₁.v = y₂.v ∨ (n = 0 ∧ y₁.v ≤ 1 ∧ y₂.v ≤ 1)) =>
    show _ ∨ _ by dsimp only; omega⟩
  assoc := congrArg MS.mk (Nat.max_assoc ..).symm
  comm := congrArg MS.mk (Nat.max_comm ..)
instance msPCore : PCore MS where
  pcore _ := some ⟨0⟩
  pcore_ne _ h := by cases h; exact ⟨_, rfl, .inl rfl⟩
  pcore_idem h := by cases h; rfl
instance msValid : Valid MS where
  ValidN _ _ := True
  Valid _ := True
  validN_ne _ _ := trivial
  valid_iff_validN := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ _ := trivial
instance msOrd : Ordered MS where
  OrderN n x y := msF n x.v ≤ msF n y.v
  Order x y := x.v ≤ y.v
  ordN_ne {n x x' y y'} hx hy h := by
    have hx' : x.v = x'.v ∨ (n = 0 ∧ x.v ≤ 1 ∧ x'.v ≤ 1) := hx
    have hy' : y.v = y'.v ∨ (n = 0 ∧ y.v ≤ 1 ∧ y'.v ≤ 1) := hy
    have h' : msF n x.v ≤ msF n y.v := h
    show msF n x'.v ≤ msF n y'.v; simp only [msF] at *; split <;> split <;> split at h' <;> split at h' <;> omega
  ordN_succ {n x y} h := by
    have h' : msF (n+1) x.v ≤ msF (n+1) y.v := h
    show msF n x.v ≤ msF n y.v; simp only [msF] at *; split <;> split <;> split at h' <;> split at h' <;> omega
  ordN_trans {n x y z} h1 h2 := Nat.le_trans h1 h2
  ord_trans h1 h2 := Nat.le_trans h1 h2
  ordN_of_ord {x y} n (h : x.v ≤ y.v) := by
    show msF n x.v ≤ msF n y.v; simp only [msF]; split <;> split <;> omega
instance msORA : ORA MS where
  validN_op_left _ := trivial
  pcore_op_left h := by cases h; exact congrArg MS.mk (Nat.zero_max _)
  extend {n x y₁ y₂} _ h :=
    if hx : x.v = max y₁.v y₂.v then ⟨y₁, y₂, congrArg MS.mk hx, .inl rfl, .inl rfl⟩
    else ⟨x, ⟨0⟩, by
        cases x with | mk x =>
        have h' : x = max y₁.v y₂.v ∨ (n = 0 ∧ x ≤ 1 ∧ max y₁.v y₂.v ≤ 1) := h
        exact congrArg MS.mk (by simp only at hx ⊢; omega),
      by have h' : x.v = max y₁.v y₂.v ∨ (n = 0 ∧ x.v ≤ 1 ∧ max y₁.v y₂.v ≤ 1) := h
         show _ ∨ _; omega,
      by have h' : x.v = max y₁.v y₂.v ∨ (n = 0 ∧ x.v ≤ 1 ∧ max y₁.v y₂.v ≤ 1) := h
         show _ ∨ _; simp only []; omega⟩
  op_monoN_left_ord {n x y} z h := by
    have h' : msF n x.v ≤ msF n y.v := h
    show msF n (max x.v z.v) ≤ msF n (max y.v z.v)
    simp only [msF] at *; split <;> split <;> split at h' <;> split at h' <;> omega
  op_mono_left_ord {x y} z (h : x.v ≤ y.v) := by show max x.v z.v ≤ max y.v z.v; omega
  validN_of_ordN _ _ := trivial
  pcore_monoN_ord _ h := by cases h; exact ⟨_, rfl, Nat.le_refl _⟩
  pcore_mono_ord _ h := by cases h; exact ⟨_, rfl, Nat.le_refl _⟩
  pcore_order_op h _ := by cases h; exact ⟨_, rfl, Nat.le_refl _⟩
  pcore_increasing h := by cases h; exact ⟨fun y => show y.v ≤ max 0 y.v by omega⟩
  increasing_closed _ _ := ⟨fun w => show w.v ≤ max _ w.v by omega⟩
  ordN_extend {n x y} _ h := by
    have h' : msF n x.v ≤ msF n y.v := h
    refine ⟨⟨min x.v y.v⟩, ?_, ?_⟩
    · show msF (n+1) (min x.v y.v) ≤ msF (n+1) y.v; simp only [msF]; split <;> split <;> omega
    · show _ ∨ _; dsimp only; simp only [msF] at h'; split at h' <;> split at h' <;> omega
instance : OrderRefl MS := ⟨fun x => Nat.le_refl x.v⟩
instance msUORA : UORA MS where
  unit := ⟨0⟩
  unit_valid := trivial
  unit_left_id := congrArg MS.mk (Nat.zero_max _)
  pcore_unit := rfl
instance ms2disc : DiscreteE (⟨2⟩ : MS) := ⟨fun {y} h => by
  cases y with | mk v =>
    have h' : 2 = v ∨ (0 = 0 ∧ 2 ≤ 1 ∧ v ≤ 1) := h
    have : v = 2 := by omega
    subst this; rfl⟩

end W1c0
open W1c0 Iris Iris.OFE

-- `AuthViewRel.of_inc` idx 5
theorem w0_59 : ¬ drop0% AuthViewRel.of_inc 5 := fun h => by
  obtain ⟨⟨c, hc⟩, -⟩ := @h NA _ 0 .e .a
  cases c <;> cases hc
-- `AuthViewRel.iff_inc` idx 2
theorem w0_60 : ¬ drop0% AuthViewRel.iff_inc 2 := fun h => by
  obtain ⟨⟨w, hw⟩, -⟩ := (@h TX _ 0 .e .a).mp ⟨⟨.e, Or.inr (by intro h; cases h)⟩, by intro h; cases h⟩
  cases w <;> cases hw
-- `Auth.auth_dist_inj` idx 7
theorem w0_61 : ¬ drop0% Auth.auth_dist_inj 7 := fun h => by
  have := (@h NA _ 0 (.own 1) .discard .e .e).1
  cases this
-- `Auth.auth_inj` idx 6
theorem w0_62 : ¬ drop0% Auth.auth_inj 6 := fun h => by
  have := (@h NA _ (.own 1) .discard .e .e).1
  cases this
-- `Auth.frag_ord_of_ord` idx 4
theorem w0_63 : ¬ drop0% Auth.frag_ord_of_ord 4 := fun h => by
  have := (@h NA _ .a .e).2
  cases this
-- `Auth.frag_inc_of_inc` idx 4
theorem w0_64 : ¬ drop0% Auth.frag_inc_of_inc 4 := fun h => by
  obtain ⟨z, hz⟩ := @h NA _ .a .e
  have h2 : NA.e = NA.op .a (View.frag z) := congrArg View.frag hz
  cases h2
-- `Auth.instCoreIdFrag` idx 3
theorem w0_65 : ¬ drop0% Auth.instCoreIdFrag 3 := fun h => by
  have h1 := (@h NA _ .a).core_id
  have h3 : ORA.core (◯ NA.a : Auth NA) = ◯ NA.a := by unfold ORA.core; rw [h1]; rfl
  rw [Auth.frag_core] at h3
  have := Auth.frag_inj h3
  cases this
-- `Auth.instCoreIdOpAuthDiscardFrag` idx 4
theorem w0_66 : ¬ drop0% Auth.instCoreIdOpAuthDiscardFrag 4 := fun h => by
  have h1 := (@h NA _ .e .a).core_id
  have h3 : ORA.core ((●{.discard} NA.e : Auth NA) • ◯ NA.a) = (●{.discard} NA.e) • ◯ NA.a := by
    unfold ORA.core; rw [h1]; rfl
  rw [Auth.auth_both_core_discarded] at h3
  have := congrArg View.frag h3
  cases this
-- `Auth.instIsOpViewAuthViewRelFrag` idx 6
theorem w0_67 : ¬ drop0% Auth.instIsOpViewAuthViewRelFrag 6 := fun h => by
  have := congrArg View.frag (@h NA _ .split .e .a .a).is_op
  cases this
-- `Auth.auth_dfrac_op_invN` idx 7
theorem w0_68 : ¬ drop0% Auth.auth_dfrac_op_invN 7 := fun h => by
  have := @h NA _ 0 (.own 1) (.own 1) .e .a
  cases this
-- `Auth.auth_dfrac_op_inv` idx 6
theorem w0_69 : ¬ drop0% Auth.auth_dfrac_op_inv 6 := fun h => by
  have := @h NA _ (.own 1) (.own 1) .e .a
  cases this
-- `Auth.both_dfrac_validN_ord` idx 2
theorem w0_70 : ¬ drop0% Auth.both_dfrac_validN_ord 2 := fun h => by
  have := ((@h NA _ 0 (.own 1) .a .e).mp
    (Auth.both_dfrac_validN_frame.mpr ⟨DFrac.valid_own_one, ⟨.a, rfl⟩, trivial⟩)).2.1
  cases this
-- `Auth.both_validN_ord` idx 2
theorem w0_71 : ¬ drop0% Auth.both_validN_ord 2 := fun h => by
  have := ((@h NA _ 0 .a .e).mp (Auth.both_validN_frame.mpr ⟨⟨.a, rfl⟩, trivial⟩)).1
  cases this
-- `Auth.both_dfrac_valid_ord` idx 2
theorem w0_72 : ¬ drop0% Auth.both_dfrac_valid_ord 2 := fun h => by
  have := ((@h NA _ (.own 1) .a .e).mp
    (Auth.both_dfrac_valid_frame.mpr ⟨DFrac.valid_own_one, fun _ => ⟨.a, rfl⟩, trivial⟩)).2.1 0
  cases this
-- `Auth.auth_both_valid_ord` idx 2
theorem w0_73 : ¬ drop0% Auth.auth_both_valid_ord 2 := fun h => by
  have := ((@h NA _ .a .e).mp (Auth.auth_both_valid_frame.mpr ⟨fun _ => ⟨.a, rfl⟩, trivial⟩)).1 0
  cases this
-- `Auth.both_dfrac_validN` idx 2
theorem w0_74 : ¬ drop0% Auth.both_dfrac_validN 2 := fun h => by
  obtain ⟨w, hw⟩ := ((@h TX _ 0 (.own 1) .e .a).mp
    (Auth.both_dfrac_validN_frame.mpr ⟨DFrac.valid_own_one, ⟨.e, Or.inr (by intro h; cases h)⟩, by intro h; cases h⟩)).2.1
  cases w <;> cases hw
-- `Auth.both_validN` idx 2
theorem w0_75 : ¬ drop0% Auth.both_validN 2 := fun h => by
  obtain ⟨w, hw⟩ := ((@h TX _ 0 .e .a).mp
    (Auth.both_validN_frame.mpr ⟨⟨.e, Or.inr (by intro h; cases h)⟩, by intro h; cases h⟩)).1
  cases w <;> cases hw
-- `Auth.both_dfrac_valid` idx 2
theorem w0_76 : ¬ drop0% Auth.both_dfrac_valid 2 := fun h => by
  obtain ⟨w, hw⟩ := ((@h TX _ (.own 1) .e .a).mp
    (Auth.both_dfrac_valid_frame.mpr ⟨DFrac.valid_own_one, fun _ => ⟨.e, Or.inr (by intro h; cases h)⟩,
      by intro h; cases h⟩)).2.1 0
  cases w <;> cases hw
-- `Auth.auth_both_valid` idx 2
theorem w0_77 : ¬ drop0% Auth.auth_both_valid 2 := fun h => by
  obtain ⟨w, hw⟩ := ((@h TX _ .e .a).mp
    (Auth.auth_both_valid_frame.mpr ⟨fun _ => ⟨.e, Or.inr (by intro h; cases h)⟩, by intro h; cases h⟩)).1 0
  cases w <;> cases hw
-- `Auth.both_dfrac_valid_discrete_frame` idx 2
theorem w0_78 : ¬ drop0% Auth.both_dfrac_valid_discrete_frame 2 := fun h => by
  obtain ⟨c, hc⟩ := ((@h AN _ (.own 1) .e .a).mp
    (Auth.both_dfrac_valid_frame.mpr ⟨DFrac.valid_own_one, fun _ => ⟨.e, trivial⟩, trivial⟩)).2.1
  cases c <;> rcases hc with hc | hc <;> cases hc
-- `Auth.both_dfrac_valid_discrete_ord` idx 2
theorem w0_79 : ¬ drop0% Auth.both_dfrac_valid_discrete_ord 2 := fun h => by
  have hc := ((@h AN _ _ (.own 1) .e .a).mp
    (Auth.both_dfrac_valid_frame.mpr ⟨DFrac.valid_own_one, fun _ => ⟨.e, trivial⟩, trivial⟩)).2.1
  rcases hc with hc | hc <;> cases hc
-- `Auth.auth_both_valid_discrete_frame` idx 2
theorem w0_80 : ¬ drop0% Auth.auth_both_valid_discrete_frame 2 := fun h => by
  obtain ⟨c, hc⟩ := ((@h AN _ .e .a).mp
    (Auth.auth_both_valid_frame.mpr ⟨fun _ => ⟨.e, trivial⟩, trivial⟩)).1
  cases c <;> rcases hc with hc | hc <;> cases hc
-- `Auth.auth_both_valid_discrete_ord` idx 2
theorem w0_81 : ¬ drop0% Auth.auth_both_valid_discrete_ord 2 := fun h => by
  have hc := ((@h AN _ _ .e .a).mp
    (Auth.auth_both_valid_frame.mpr ⟨fun _ => ⟨.e, trivial⟩, trivial⟩)).1
  rcases hc with hc | hc <;> cases hc
-- `Auth.both_dfrac_valid_discrete_ord` idx 3
theorem w0_82 : ¬ drop0% Auth.both_dfrac_valid_discrete_ord 3 := fun h => by
  have := ((@h NA _ _ (.own 1) .a .e).mp
    (Auth.both_dfrac_valid_frame.mpr ⟨DFrac.valid_own_one, fun _ => ⟨.a, rfl⟩, trivial⟩)).2.1
  cases this
-- `Auth.auth_both_valid_discrete_ord` idx 3
theorem w0_83 : ¬ drop0% Auth.auth_both_valid_discrete_ord 3 := fun h => by
  have := ((@h NA _ _ .a .e).mp (Auth.auth_both_valid_frame.mpr ⟨fun _ => ⟨.a, rfl⟩, trivial⟩)).1
  cases this
-- `Auth.both_dfrac_valid_discrete` idx 3
theorem w0_84 : ¬ drop0% Auth.both_dfrac_valid_discrete 3 := fun h => by
  obtain ⟨w, hw⟩ := ((@h TX _ _ (.own 1) .e .a).mp
    (Auth.both_dfrac_valid_frame.mpr ⟨DFrac.valid_own_one, fun _ => ⟨.e, Or.inr (by intro h; cases h)⟩,
      by intro h; cases h⟩)).2.1
  cases w <;> cases hw
-- `Auth.auth_both_valid_discrete` idx 3
theorem w0_85 : ¬ drop0% Auth.auth_both_valid_discrete 3 := fun h => by
  obtain ⟨w, hw⟩ := ((@h TX _ _ .e .a).mp
    (Auth.auth_both_valid_frame.mpr ⟨fun _ => ⟨.e, Or.inr (by intro h; cases h)⟩, by intro h; cases h⟩)).1
  cases w <;> cases hw
-- `Auth.auth_both_dfrac_valid_2_ord` idx 6
theorem w0_86 : ¬ drop0% Auth.auth_both_dfrac_valid_2_ord 6 := fun h => by
  have := (Auth.both_dfrac_valid_frame.mp (@h EX _ (.own 1) .z .e DFrac.valid_own_one (Or.inl rfl))).2.2
  exact this rfl
-- `Auth.auth_both_dfrac_valid_2_ord` idx 7
theorem w0_87 : ¬ drop0% Auth.auth_both_dfrac_valid_2_ord 7 := fun h => by
  obtain ⟨c, hc⟩ := (Auth.both_dfrac_valid_frame.mp (@h NA _ (.own 1) .e .a DFrac.valid_own_one trivial)).2.1 0
  cases c <;> cases hc
-- `Auth.auth_both_dfrac_valid_2` idx 5
theorem w0_88 : ¬ drop0% Auth.auth_both_dfrac_valid_2 5 := fun h => by
  have := DFrac.valid_own_op_discard.mp
    (Auth.both_dfrac_valid_frame.mp (@h NA _ (DFrac.own 1 • DFrac.discard) .e .e trivial ⟨.e, rfl⟩)).1
  simp at this
-- `Auth.auth_both_dfrac_valid_2` idx 6
theorem w0_89 : ¬ drop0% Auth.auth_both_dfrac_valid_2 6 := fun h => by
  have := (Auth.both_dfrac_valid_frame.mp (@h EX _ (.own 1) .z .e DFrac.valid_own_one ⟨.z, rfl⟩)).2.2
  exact this rfl
-- `Auth.auth_both_dfrac_valid_2` idx 7
theorem w0_90 : ¬ drop0% Auth.auth_both_dfrac_valid_2 7 := fun h => by
  obtain ⟨c, hc⟩ := (Auth.both_dfrac_valid_frame.mp (@h NA _ (.own 1) .e .a DFrac.valid_own_one trivial)).2.1 0
  cases c <;> cases hc
-- `Auth.auth_both_valid_2_ord` idx 4
theorem w0_91 : ¬ drop0% Auth.auth_both_valid_2_ord 4 := fun h => by
  have := (Auth.auth_both_valid_frame.mp (@h EX _ .z .e (Or.inl rfl))).2
  exact this rfl
-- `Auth.auth_both_valid_2_ord` idx 5
theorem w0_92 : ¬ drop0% Auth.auth_both_valid_2_ord 5 := fun h => by
  obtain ⟨c, hc⟩ := (Auth.auth_both_valid_frame.mp (@h NA _ .e .a trivial)).1 0
  cases c <;> cases hc
-- `Auth.auth_both_valid_2` idx 4
theorem w0_93 : ¬ drop0% Auth.auth_both_valid_2 4 := fun h => by
  have := (Auth.auth_both_valid_frame.mp (@h EX _ .z .e ⟨.z, rfl⟩)).2
  exact this rfl
-- `Auth.auth_both_valid_2` idx 5
theorem w0_94 : ¬ drop0% Auth.auth_both_valid_2 5 := fun h => by
  obtain ⟨c, hc⟩ := (Auth.auth_both_valid_frame.mp (@h NA _ .e .a trivial)).1 0
  cases c <;> cases hc
-- `Auth.auth_dfrac_ordN` idx 8
theorem w0_95 : ¬ drop0% Auth.auth_dfrac_ordN 8 := fun h => by
  have := ((@h NA _ 0 (.own 1) (.own 1) .e .e .a).mpr ⟨Or.inr rfl, rfl⟩).2
  cases this
-- `Auth.auth_dfrac_ord` idx 7
theorem w0_96 : ¬ drop0% Auth.auth_dfrac_ord 7 := fun h => by
  have := ((@h NA _ (.own 1) (.own 1) .e .e .a).mpr ⟨Or.inr rfl, rfl⟩).2
  cases this
-- `Auth.auth_ordN` idx 6
theorem w0_97 : ¬ drop0% Auth.auth_ordN 6 := fun h => by
  have := ((@h NA _ 0 .e .e .a).mpr rfl).2
  cases this
-- `Auth.auth_ord` idx 5
theorem w0_98 : ¬ drop0% Auth.auth_ord 5 := fun h => by
  have := ((@h NA _ .e .e .a).mpr rfl).2
  cases this
-- `Auth.auth_update_ord` idx 6
theorem w0_99 : ¬ drop0% Auth.auth_update_ord 6 := fun h => by
  obtain ⟨c, hc⟩ := (Auth.both_validN_frame.mp (@h NA _ .e .e .e .a 0 none
    (Auth.both_validN_frame.mpr ⟨⟨.e, rfl⟩, trivial⟩))).1
  cases c <;> cases hc
-- `Auth.auth_update_alloc_ord` idx 5
theorem w0_100 : ¬ drop0% Auth.auth_update_alloc_ord 5 := fun h => by
  obtain ⟨c, hc⟩ := (Auth.both_validN_frame.mp (@h NA _ .e .e .a 0 none (Auth.auth_validN.mpr trivial))).1
  cases c <;> cases hc
-- `Auth.auth_update_dealloc_ord` idx 5
theorem w0_101 : ¬ drop0% Auth.auth_update_dealloc_ord 5 := fun h =>
  (Auth.auth_validN.mp (@h EX _ .e .e .z 0 none
    (Auth.both_validN_frame.mpr ⟨⟨.e, Or.inl rfl⟩, by intro h; cases h⟩))) rfl
-- `Auth.auth_update_auth_ord` idx 4
theorem w0_102 : ¬ drop0% Auth.auth_update_auth_ord 4 := fun h =>
  (Auth.auth_validN.mp (@h EX _ .e .z 0 none (Auth.auth_validN.mpr (by intro h; cases h)))) rfl
-- `Auth.auth_update` idx 7
theorem w0_103 : ¬ drop0% Auth.auth_update 7 := fun h => by
  obtain ⟨c, hc⟩ := (Auth.both_validN_frame.mp (@h NA _ _ .e .e .e .a 0 none
    (Auth.both_validN_frame.mpr ⟨⟨.e, rfl⟩, trivial⟩))).1
  cases c <;> cases hc
/-- In TX the local update (e, a) to (z, b') holds vacuously: e is never a • w. -/
theorem tx_lup (b' : TX) : (TX.e, TX.a) ~l~> (TX.z, b') := by
  intro n mz _ heq
  cases mz with
  | none => cases heq
  | some w => cases w <;> cases heq
-- `Auth.auth_update` idx 2
theorem w0_104 : ¬ drop0% Auth.auth_update 2 := fun h =>
  (Auth.both_validN_frame.mp (@h TX _ .e .a .z .e (tx_lup .e) 0 none
    (Auth.both_validN_frame.mpr ⟨⟨.e, Or.inr (by intro h; cases h)⟩, by intro h; cases h⟩))).2 rfl
-- `Auth.auth_update_alloc` idx 2
-- removable: the local update at the frame some a gives a' =n= b' • a and valid a', which is the
-- order-based premise of auth_update_alloc_ord (no OrdInc needed)
theorem w0_105 : drop% Auth.auth_update_alloc 2 := by
  intro A _ a a' b' hup
  refine Auth.auth_update_alloc_ord fun n bf hbf hv => ?_
  obtain ⟨hv', heq⟩ := hup n (some a) hv (OFE.Dist.of_eq (UORA.unit_left_id (x := a)).symm)
  exact ⟨Ordered.ordN_ne .rfl heq.symm (ORA.op_monoN_right_ord b' hbf), hv'⟩
-- `Auth.auth_update_alloc` idx 6
theorem w0_106 : ¬ drop0% Auth.auth_update_alloc 6 := fun h => by
  obtain ⟨c, hc⟩ := (Auth.both_validN_frame.mp (@h NA _ _ .e .e .a 0 none (Auth.auth_validN.mpr trivial))).1
  cases c <;> cases hc
-- `Auth.auth_update_dealloc` idx 2
theorem w0_107 : ¬ drop0% Auth.auth_update_dealloc 2 := fun h =>
  (Auth.auth_validN.mp (@h TX _ .e .a .z (tx_lup .e) 0 none
    (Auth.both_validN_frame.mpr ⟨⟨.e, Or.inr (by intro h; cases h)⟩, by intro h; cases h⟩))) rfl
-- `Auth.auth_update_dealloc` idx 6
theorem w0_108 : ¬ drop0% Auth.auth_update_dealloc 6 := fun h =>
  (Auth.auth_validN.mp (@h EX _ _ .e .e .z 0 none
    (Auth.both_validN_frame.mpr ⟨⟨.e, Or.inl rfl⟩, by intro h; cases h⟩))) rfl
-- `Auth.auth_update_auth` idx 6
theorem w0_109 : ¬ drop0% Auth.auth_update_auth 6 := fun h =>
  (Auth.auth_validN.mp (@h EX _ _ .e .z .e 0 none (Auth.auth_validN.mpr (by intro h; cases h)))) rfl
-- `Auth.auth_update_dfrac_alloc` idx 6
theorem w0_110 : ¬ drop0% Auth.auth_update_dfrac_alloc 6 := fun h => by
  obtain ⟨c, hc⟩ := (Auth.both_dfrac_validN_frame.mp (@h AC _ (.own 1) .e .a ⟨rfl⟩ 0 none
    (Auth.auth_dfrac_validN.mpr ⟨DFrac.valid_own_one, trivial⟩))).2.1
  cases c <;> rcases hc with hc | hc <;> cases hc
-- `Auth.auth_local_update_ord` idx 8
theorem w0_111 : ¬ drop0% Auth.auth_local_update_ord 8 := fun h => by
  have := ((@h NA _ .e .e .e .e .e .a rfl trivial) 0 none
    (Auth.both_validN_frame.mpr ⟨⟨.e, rfl⟩, trivial⟩) .rfl).2.2
  cases this
-- `Auth.auth_local_update_ord` idx 10
theorem w0_112 : ¬ drop0% Auth.auth_local_update_ord 10 := fun h =>
  (Auth.both_validN_frame.mp ((@h EX _ .e .e .e .z .e .e (fun _ _ hv heq => ⟨hv, heq⟩) (Or.inl rfl)) 0 none
    (Auth.both_validN_frame.mpr ⟨⟨.e, Or.inl rfl⟩, by intro h; cases h⟩) .rfl).1).2 rfl
-- `Auth.auth_local_update` idx 8
theorem w0_113 : ¬ drop0% Auth.auth_local_update 8 := fun h => by
  have := ((@h NA _ .e .e .e .e .e .a ⟨.e, rfl⟩ trivial) 0 none
    (Auth.both_validN_frame.mpr ⟨⟨.e, rfl⟩, trivial⟩) .rfl).2.2
  cases this
-- `Auth.auth_local_update` idx 9
theorem w0_114 : ¬ drop0% Auth.auth_local_update 9 := fun h => by
  obtain ⟨c, hc⟩ := (Auth.both_validN_frame.mp ((@h NA _ .a .a .a .e .a .a (fun _ _ hv heq => ⟨hv, heq⟩) trivial) 0 none
    (Auth.both_validN_frame.mpr ⟨⟨.e, rfl⟩, trivial⟩) .rfl).1).1
  cases c <;> cases hc
-- `Auth.auth_local_update` idx 10
theorem w0_115 : ¬ drop0% Auth.auth_local_update 10 := fun h =>
  (Auth.both_validN_frame.mp ((@h EX _ .e .e .e .z .e .e (fun _ _ hv heq => ⟨hv, heq⟩) ⟨.z, rfl⟩) 0 none
    (Auth.both_validN_frame.mpr ⟨⟨.e, Or.inl rfl⟩, by intro h; cases h⟩) .rfl).1).2 rfl
-- `Auth.authViewRel_map` idx 8
theorem w0_116 : ¬ drop0% Auth.authViewRel_map 8 := fun h => by
  obtain ⟨⟨c, hc⟩, -⟩ := @h NA NA _ _ ORA.Hom.id 0 .e .a
  cases c <;> cases hc
-- `Auth.instRFunctorAffineURF` idx 2
theorem w0_117 : ¬ drop0% Auth.instRFunctorAffineURF 2 := fun h => by
  have hi := (@h (constOF NA) _).affine (α := Unit) (β := Unit)
  have := (hi.inc_ord (x := (◯ NA.e : Auth NA)) (y := ◯ NA.a) ⟨◯ NA.a, rfl⟩).2
  cases this
-- `Auth.instRFunctorAffineRF` idx 2
theorem w0_118 : ¬ drop0% Auth.instRFunctorAffineRF 2 := fun h => by
  have hi := (@h (constOF NA) _).affine (α := Unit) (β := Unit)
  have := (hi.inc_ord (x := (◯ NA.e : Auth NA)) (y := ◯ NA.a) ⟨◯ NA.a, rfl⟩).2
  cases this
-- `Auth.auth_update_auth` idx 2
-- removable: the removable variant of auth_update_alloc (no OrdInc) followed by Update.op_l
theorem w0_119 : drop% Auth.auth_update_auth 2 := by
  intro A _ a a' b' hup
  exact Update.trans (w0_105 hup) Update.op_l
-- `Auth.auth_update_dfrac_alloc` idx 5
theorem w0_120 : ¬ drop0% Auth.auth_update_dfrac_alloc 5 := fun h => by
  have r := @h EX _ (.own 1) .a .a ⟨.e, rfl⟩ 0 (some (◯ EX.a))
    (Auth.both_dfrac_validN_frame.mpr ⟨DFrac.valid_own_one, ⟨.e, Or.inr (Or.inl rfl)⟩, by intro h; cases h⟩)
  have r' : ✓{0} (((●{.own 1} EX.a) • ◯ EX.a) • ◯ EX.a : Auth EX) := r
  rw [← ORA.assoc', ← Auth.frag_op] at r'
  obtain ⟨c, hc⟩ := (Auth.both_dfrac_validN_frame.mp r').2.1
  cases c <;> rcases hc with hc | hc | hc <;> cases hc
-- `AuthViewRel.instIsViewRelDiscreteOfDiscreteOfDiscrete` idx 3
theorem w0_121 : ¬ drop0% AuthViewRel.instIsViewRelDiscreteOfDiscreteOfDiscrete 3 := fun h => by
  have := ((@h VN _ _).discrete 1 .a .e ⟨⟨.e, Or.inl rfl⟩, Or.inr rfl⟩).2
  rcases this with h | h <;> cases h
-- `Auth.auth_discrete` idx 4
theorem w0_122 : ¬ drop0% Auth.auth_discrete 4 := fun h =>
  tn12ne (Auth.auth_inj ((@h TN _ (.own 1) ⟨1⟩ tn0disc).discrete (y := ●{.own 1} (⟨2⟩ : TN))
    (Auth.auth_ne.ne tn12))).2
-- `Auth.frag_discrete` idx 3
theorem w0_123 : ¬ drop0% Auth.frag_discrete 3 := fun h =>
  tn12ne (Auth.frag_inj ((@h TN _ ⟨1⟩).discrete (y := ◯ (⟨2⟩ : TN)) (Auth.frag_ne.ne tn12)))
-- `Auth.auth_discrete` idx 5
theorem w0_124 : ¬ drop0% Auth.auth_discrete 5 := fun h => by
  have := congrArg View.frag ((@h MS _ (.own 1) ⟨2⟩ ms2disc).discrete
    (y := ((●{.own 1} (⟨2⟩ : MS)) • ◯ (⟨1⟩ : MS) : Auth MS)) ⟨.rfl, .inr ⟨rfl, by decide, by decide⟩⟩)
  cases this
