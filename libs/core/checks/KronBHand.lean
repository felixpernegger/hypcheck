import Lean

/-!
Hand pass `KronB` (hand12): 119 unresolved hypotheses of `Init.Grind.Ring.Kronecker` from line 2325 on
(`toLinQ_spec`, the `kronQ`/`kronQLin`/`kron`/`kronLin` relation lemmas, `*_cancel_of_kronLinS`, the
`PPoly.Deg`/`PPoly.denoteSN` lemmas of the semiring Kronecker check, `toTL_spec`, `*_of_kronSN`).
For hypothesis `hᵢ` of `T` each declaration proves `¬T'` (`drop0% T i`, universes set to `0`), `T'`
(`drop% T i`, removable) or `¬ ∀ indep, Hᵢ` (`indep0% T i`, dependent).

98 necessary, 19 removable, 0 independent; left unresolved: `[AddRightCancel α]` of `le_cancel_of_kronLinS` and
`lt_cancel_of_kronLinS` (true without it, since linear semiring identities need no cancellation and `OrderedAdd`
cancels `c` in `≤`/`<`, but the library's `Expr.eq_of_kronLinS` goes through the ring envelope).

Reusable models (namespace `KronBHand`):
* `F2`: `Fin 2` as a `Field` (`0⁻¹ = 0`, characteristic 2). Refutes `[IsCharP α 0]`: with `invs = [(0, 2)]`
  the variable `x₀` must denote `2⁻¹ = 0⁻¹ = 0`, so `x₀ * 2` denotes `0` while the certificate reads it as `1`.
* `QS`/`ZS`: `Rat`/`Int` ordered through `sw` (swap `0` and `1`): a linear order (resp. preorder) with lawful `<`
  that is not an `OrderedRing` (`1 < 0`); refutes `[OrderedRing α]` (`0 ≤ 1` is false, `1 ≤ 2` is true).
* `Q0`/`Z0`: the usual `≤` and `a < b := a < b ∨ (a = 0 ∧ b = 0)`: an `OrderedRing` whose `<` is not lawful
  (`0 < 0`); refutes `[LawfulOrderLT α]` in `<` lemmas (`0 < 0` is true, `1 < 1` is false).
* `QF`: `Rat` with `≤` and `<` empty: lawful `<`, not a linear order (dependent `[IsLinearOrder α]`).
* `BS`: the Boolean semiring (copied from `AdapterHand`, made commutative): refutes `[AddRightCancel α]`
  (`0 + 1 = 1 + 1` but `0 ≠ 1`).
* `instARCInt`: `AddRightCancel Int` (no library instance), so `Int` can serve the `*_cancel_of_kronLinS` lemmas.
* Other counterexamples: `B = 1` or `K = 0` collide the Kronecker images of `x₀` and `x₁`; `x₀ * x₀` and `x₁`
  collide at the linear point `xᵢ = (2 ^ K) ^ (i + 1)`; inverse tables `[(0, 1)]` with `x₀ = 0` (without `ok`) and
  `[(0, 0)]` with `x₀ = 0` (without `nonzero_k`: denominator `0` makes every cross-multiplied check pass); base
  `B = 2` with `x₀ * x₀` overflowing into `x₁` for the `PPoly.Deg`/`dsum` bounds of `denoteSN`.

Removable verdicts and their helper lemmas (section "Removable"):
* `PPoly.Deg.mulTermTL`/`mulTL`/`powTL`: `1 < B` and `D₁ + D₂ < B` (resp. `D * k < B`) are not needed:
  the digit sum is subadditive (`dsum_add_le`), and is `0` for `B ≤ 1`.
* `PPoly.denoteSN_scale`/`denoteSN_mulTermTL`/`denoteSN_mulTL`: one non-negative factor suffices
  (`toNat_mul_left/right`), and for `B ≤ 1` every monomial denotes `1`; `denoteSN_powTL` and `Expr.toTL_spec`
  without `1 < B` follow (the latter by the library proof with the generalized lemmas).
* `PPoly.denoteSN_eq_of_coeff`: the size bound is only the induction measure.
* `le_of_kronQ_rel`/`le_of_kronQLin_rel` without `LawfulOrderLT`: `x ≤ 0 ↔ d • x ≤ 0` needs only
  `OrderedAdd`, linearity and characteristic `0`.

Run with the lean4 repo's stage1 binary (`runs/hand12/lean.sh checks/KronBHand.lean`).
-/

set_option linter.unusedVariables false
set_option linter.deprecated false

open Lean Meta Elab Term in
/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
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

open Lean Meta Elab Term in
/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => levelZero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => levelZero
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



open Lean.Grind CommRing
attribute [local instance] Semiring.natCast Ring.intCast

namespace KronBHand

/-! ## Models -/

/-- `Fin 2` as a field (`0⁻¹ = 0`), characteristic 2. -/
instance F2 : Lean.Grind.Field (Fin 2) := { (inferInstance : Lean.Grind.CommRing (Fin 2)) with inv := id, div := (· * ·), zpow := ⟨fun a n => a ^ n.natAbs⟩, div_eq_mul_inv := (by decide), zero_ne_one := (by decide), inv_zero := (by decide), mul_inv_cancel := (by decide), zpow_zero := fun a => Lean.Grind.Semiring.pow_zero a, zpow_succ := fun a n => Lean.Grind.Semiring.pow_succ a n, zpow_neg := (by intro a n; show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]) }

theorem F2_ok : InvVars.ok (α := Fin 2) (.leaf 0) [(0, 2)] := by
  unfold InvVars.ok InvVars.denoteVars InvVars.denoteInvs; decide

/-- Swap `0` and `1`. -/
def sw {α} [DecidableEq α] [OfNat α 0] [OfNat α 1] (a : α) : α := if a = 0 then 1 else if a = 1 then 0 else a

theorem sw_sw {α} [DecidableEq α] [OfNat α 0] [OfNat α 1] (h01 : (0 : α) ≠ 1) (a : α) : sw (sw a) = a := by
  unfold sw
  by_cases h0 : a = 0
  · subst h0; simp [Ne.symm h01]
  · by_cases h1 : a = 1
    · subst h1; simp
    · simp [h0, h1]

theorem sw_inj {α} [DecidableEq α] [OfNat α 0] [OfNat α 1] (h01 : (0 : α) ≠ 1) {a b : α} (h : sw a = sw b) : a = b := by
  rw [← sw_sw h01 a, ← sw_sw h01 b, h]

def QS := Rat
instance : Field QS := inferInstanceAs (Field Rat)
instance : IsCharP QS 0 := inferInstanceAs (IsCharP Rat 0)
instance : LE QS := ⟨fun a b => sw (α := Rat) a ≤ sw (α := Rat) b⟩
instance : LT QS := ⟨fun a b => sw (α := Rat) a < sw (α := Rat) b⟩
instance : DecidableRel (α := QS) (· ≤ ·) := fun a b => inferInstanceAs (Decidable (sw (α := Rat) a ≤ sw (α := Rat) b))
instance : DecidableRel (α := QS) (· < ·) := fun a b => inferInstanceAs (Decidable (sw (α := Rat) a < sw (α := Rat) b))
instance : Std.LawfulOrderLT QS := ⟨fun a b => Std.LawfulOrderLT.lt_iff (α := Rat) _ _⟩
instance : Std.IsLinearOrder QS where
  le_refl a := Std.le_refl (α := Rat) _
  le_trans a b c := Std.le_trans (α := Rat)
  le_antisymm a b h₁ h₂ := sw_inj (α := Rat) (by decide) (Std.le_antisymm (α := Rat) h₁ h₂)
  le_total a b := Std.le_total (α := Rat)

def ZS := Int
instance : CommRing ZS := inferInstanceAs (CommRing Int)
instance : LE ZS := ⟨fun a b => sw (α := Int) a ≤ sw (α := Int) b⟩
instance : LT ZS := ⟨fun a b => sw (α := Int) a < sw (α := Int) b⟩
instance : DecidableRel (α := ZS) (· ≤ ·) := fun a b => inferInstanceAs (Decidable (sw (α := Int) a ≤ sw (α := Int) b))
instance : DecidableRel (α := ZS) (· < ·) := fun a b => inferInstanceAs (Decidable (sw (α := Int) a < sw (α := Int) b))
instance : Std.LawfulOrderLT ZS := ⟨fun a b => Std.LawfulOrderLT.lt_iff (α := Int) _ _⟩
instance : Std.IsPreorder ZS where
  le_refl a := Std.le_refl (α := Int) _
  le_trans a b c := Std.le_trans (α := Int)
instance : AddRightCancel ZS := ⟨fun a b c h => (Int.add_left_inj (c : Int)).mp h⟩

/-- `Int` is right-cancellative (no library instance). -/
instance instARCInt : AddRightCancel Int := ⟨fun a b c h => (Int.add_left_inj c).mp h⟩

/-- `a < b ∨ (a = 0 ∧ b = 0)`. -/
abbrev lt0 {α} [LT α] [OfNat α 0] (a b : α) : Prop := a < b ∨ (a = 0 ∧ b = 0)

def Q0 := Rat
instance : Field Q0 := inferInstanceAs (Field Rat)
instance : IsCharP Q0 0 := inferInstanceAs (IsCharP Rat 0)
instance : LE Q0 := inferInstanceAs (LE Rat)
instance : LT Q0 := ⟨lt0 (α := Rat)⟩
instance : DecidableRel (α := Q0) (· ≤ ·) := inferInstanceAs (DecidableRel (α := Rat) (· ≤ ·))
instance : DecidableRel (α := Q0) (· < ·) := fun (a b : Rat) => inferInstanceAs (Decidable (lt0 a b))
instance : Std.IsLinearOrder Q0 := inferInstanceAs (Std.IsLinearOrder Rat)
instance : OrderedRing Q0 where
  toOrderedAdd := inferInstanceAs (OrderedAdd Rat)
  zero_lt_one := Or.inl (OrderedRing.zero_lt_one (R := Rat))
  mul_lt_mul_of_pos_left := by
    intro a b c h hc
    show lt0 (α := Rat) ((c : Rat) * a) ((c : Rat) * b)
    rcases hc with hc | ⟨-, hc⟩
    · rcases h with h | ⟨ha, hb⟩
      · exact Or.inl (OrderedRing.mul_lt_mul_of_pos_left (R := Rat) h hc)
      · subst ha hb; exact Or.inr ⟨Semiring.mul_zero _, Semiring.mul_zero _⟩
    · subst hc; exact Or.inr ⟨Semiring.zero_mul _, Semiring.zero_mul _⟩
  mul_lt_mul_of_pos_right := by
    intro a b c h hc
    show lt0 (α := Rat) ((a : Rat) * c) ((b : Rat) * c)
    rcases hc with hc | ⟨-, hc⟩
    · rcases h with h | ⟨ha, hb⟩
      · exact Or.inl (OrderedRing.mul_lt_mul_of_pos_right (R := Rat) h hc)
      · subst ha hb; exact Or.inr ⟨Semiring.zero_mul _, Semiring.zero_mul _⟩
    · subst hc; exact Or.inr ⟨Semiring.mul_zero _, Semiring.mul_zero _⟩

def Z0 := Int
instance : CommRing Z0 := inferInstanceAs (CommRing Int)
instance : LE Z0 := inferInstanceAs (LE Int)
instance : LT Z0 := ⟨lt0 (α := Int)⟩
instance : DecidableRel (α := Z0) (· ≤ ·) := inferInstanceAs (DecidableRel (α := Int) (· ≤ ·))
instance : DecidableRel (α := Z0) (· < ·) := fun (a b : Int) => inferInstanceAs (Decidable (lt0 a b))
instance : Std.IsPreorder Z0 := inferInstanceAs (Std.IsPreorder Int)
instance : AddRightCancel Z0 := ⟨fun a b c h => (Int.add_left_inj (c : Int)).mp h⟩
instance : OrderedRing Z0 where
  toOrderedAdd := inferInstanceAs (OrderedAdd Int)
  zero_lt_one := Or.inl (OrderedRing.zero_lt_one (R := Int))
  mul_lt_mul_of_pos_left := by
    intro a b c h hc
    show lt0 (α := Int) ((c : Int) * a) ((c : Int) * b)
    rcases hc with hc | ⟨-, hc⟩
    · rcases h with h | ⟨ha, hb⟩
      · exact Or.inl (OrderedRing.mul_lt_mul_of_pos_left (R := Int) h hc)
      · subst ha hb; exact Or.inr ⟨Semiring.mul_zero _, Semiring.mul_zero _⟩
    · subst hc; exact Or.inr ⟨Semiring.zero_mul _, Semiring.zero_mul _⟩
  mul_lt_mul_of_pos_right := by
    intro a b c h hc
    show lt0 (α := Int) ((a : Int) * c) ((b : Int) * c)
    rcases hc with hc | ⟨-, hc⟩
    · rcases h with h | ⟨ha, hb⟩
      · exact Or.inl (OrderedRing.mul_lt_mul_of_pos_right (R := Int) h hc)
      · subst ha hb; exact Or.inr ⟨Semiring.zero_mul _, Semiring.zero_mul _⟩
    · subst hc; exact Or.inr ⟨Semiring.mul_zero _, Semiring.mul_zero _⟩

def QF := Rat
instance : Field QF := inferInstanceAs (Field Rat)
instance : IsCharP QF 0 := inferInstanceAs (IsCharP Rat 0)
instance : LE QF := ⟨fun _ _ => False⟩
instance : LT QF := ⟨fun _ _ => False⟩
instance : Std.LawfulOrderLT QF := ⟨fun _ _ => ⟨False.elim, fun h => h.1⟩⟩
theorem QF.not_lin : ¬ Std.IsLinearOrder QF := fun h => h.le_refl (0 : Rat)

/-- The Boolean semiring on a copy of `Bool` (as in `AdapterHand`). -/
def BS : Type := Bool
instance : DecidableEq BS := inferInstanceAs (DecidableEq Bool)
instance : Add BS := ⟨Bool.or⟩
instance : Mul BS := ⟨Bool.and⟩
instance : NatCast BS := ⟨fun n => decide (n ≠ 0)⟩
instance (n : Nat) : OfNat BS n := ⟨decide (n ≠ 0)⟩
instance : SMul Nat BS := ⟨fun n a => Bool.and (decide (n ≠ 0)) a⟩
instance : HPow BS Nat BS := ⟨fun a n => Bool.or (decide (n = 0)) a⟩
instance BS.commSemiring : CommSemiring BS where
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_one a := by cases a <;> rfl
  one_mul a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
  pow_zero a := by cases a <;> rfl
  pow_succ a n := by
    show Bool.or (decide (n + 1 = 0)) a = Bool.and (Bool.or (decide (n = 0)) a) a
    cases a <;> simp
  ofNat_succ n := by
    show decide (n + 1 ≠ 0) = Bool.or (decide (n ≠ 0)) (decide (1 ≠ 0))
    simp
  mul_comm a b := by cases a <;> cases b <;> rfl

/-! ## Necessary -/

-- `Lean.Grind.CommRing.Expr.eq_of_kronQLin` (inst, 2): `Fin 2` (`F2`), `invs = [(0, 2)]`, `x₀ = 0 = 2⁻¹`: `x₀ * 2` denotes `0`, the certificate reads `1`.
theorem Expr_eq_of_kronQLin_h2 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_kronQLin 2 := by
  intro h
  have := h (α := Fin 2) (.leaf 0) 4 [(0, 2)] F2_ok (by decide +kernel) (.mul (.var 0) (.num 2)) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_kronQLin` (hok, 6): `invs = [(0, 1)]` claims `x₀ = 1`, but `x₀ = 0`: `x₀` vs `1`.
theorem Expr_eq_of_kronQLin_h6 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_kronQLin 6 := by
  intro h
  have := h (α := Rat) (.leaf 0) 3 [(0, 1)] (by decide +kernel) (.var 0) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_kronQLin` (hl, 10): `x₀ * x₀` and `x₁` collide at `xᵢ = 8 ^ (i + 1)`; `x₀ = 2`, `x₁ = 3`.
theorem Expr_eq_of_kronQLin_h10 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_kronQLin 10 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 2) (.leaf 3)) 3 [] rfl (by decide +kernel) (.mul (.var 0) (.var 0)) (.var 1) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_true_of_kronQLin` (inst, 2): `Fin 2` (`F2`), `invs = [(0, 2)]`, `x₀ = 0 = 2⁻¹`: `x₀ * 2` denotes `0`, the certificate reads `1`.
theorem eq_true_of_kronQLin_h2 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kronQLin 2 := by
  intro h
  have := h (α := Fin 2) (.leaf 0) 4 [(0, 2)] F2_ok (by decide +kernel) (.mul (.var 0) (.num 2)) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_true_of_kronQLin` (hok, 6): `invs = [(0, 1)]` claims `x₀ = 1`, but `x₀ = 0`: `x₀` vs `1`.
theorem eq_true_of_kronQLin_h6 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kronQLin 6 := by
  intro h
  have := h (α := Rat) (.leaf 0) 3 [(0, 1)] (by decide +kernel) (.var 0) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_true_of_kronQLin` (hl, 10): `x₀ * x₀` and `x₁` collide at `xᵢ = 8 ^ (i + 1)`; `x₀ = 2`, `x₁ = 3`.
theorem eq_true_of_kronQLin_h10 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kronQLin 10 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 2) (.leaf 3)) 3 [] rfl (by decide +kernel) (.mul (.var 0) (.var 0)) (.var 1) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_true_of_kronQLin` (hnz, 7): `invs = [(0, 0)]`, `x₀ = 0 = 0⁻¹`: denominators `0` make the cross-multiplied check pass; `0` vs `1`.
theorem eq_true_of_kronQLin_h7 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kronQLin 7 := by
  intro h
  have := h (α := Rat) (.leaf 0) 1 [(0, 0)] (by unfold InvVars.ok InvVars.denoteVars InvVars.denoteInvs; decide +kernel) (.var 0) (.add (.var 0) (.num 1)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQ` (inst, 2): `Fin 2` (`F2`), `invs = [(0, 2)]`, `x₀ = 0 = 2⁻¹`: `lhs = x₀ * 2` denotes `0`, `lhs' = 1`.
theorem Expr_sub_mul_eq_of_kronQ_h2 : ¬ drop0% Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQ 2 := by
  intro h
  have := h (α := Fin 2) (.leaf 0) 4 2 [(0, 2)] F2_ok (by decide +kernel) 1 (.mul (.var 0) (.num 2)) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQ` (hok, 7): `invs = [(0, 1)]` with `x₀ = 0`: `x₀ - 0` vs `1 - 0`.
theorem Expr_sub_mul_eq_of_kronQ_h7 : ¬ drop0% Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQ 7 := by
  intro h
  have := h (α := Rat) (.leaf 0) 3 2 [(0, 1)] (by decide +kernel) 1 (.var 0) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQ` (hnz, 8): `invs = [(0, 0)]`, `x₀ = 0`: denominators `0` pass every check; `x₀ - 0 = 0` vs `x₀ + 1 - 0 = 1`.
theorem Expr_sub_mul_eq_of_kronQ_h8 : ¬ drop0% Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQ 8 := by
  intro h
  have := h (α := Rat) (.leaf 0) 1 2 [(0, 0)] (by unfold InvVars.ok InvVars.denoteVars InvVars.denoteInvs; decide +kernel) 1 (.var 0) (.num 0) (.add (.var 0) (.num 1)) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQ` (hB, 14): `B = 1`: `x₀` and `x₁` both evaluate to `2 ^ K`; `x₀ = 1`, `x₁ = 2`.
theorem Expr_sub_mul_eq_of_kronQ_h14 : ¬ drop0% Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQ 14 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 1) (.leaf 2)) 3 1 [] rfl (by decide +kernel) 1 (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQ` (hK, 15): `K = 0`: `x₀` and `x₁` both evaluate to `1`; `x₀ = 1`, `x₁ = 2`.
theorem Expr_sub_mul_eq_of_kronQ_h15 : ¬ drop0% Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQ 15 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 1) (.leaf 2)) 0 2 [] rfl (by decide +kernel) 1 (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kronQ_rel` (inst, 2): `Fin 2` (`F2`), `invs = [(0, 2)]`, `x₀ = 0 = 2⁻¹`: `lhs = x₀ * 2` denotes `0`, `lhs' = 1`.
theorem eq_of_kronQ_rel_h2 : ¬ drop0% Lean.Grind.CommRing.eq_of_kronQ_rel 2 := by
  intro h
  have := h (α := Fin 2) (.leaf 0) 4 2 [(0, 2)] F2_ok (by decide +kernel) 1 rfl (.mul (.var 0) (.num 2)) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kronQ_rel` (hok, 7): `invs = [(0, 1)]` with `x₀ = 0`: `x₀ - 0` vs `1 - 0`.
theorem eq_of_kronQ_rel_h7 : ¬ drop0% Lean.Grind.CommRing.eq_of_kronQ_rel 7 := by
  intro h
  have := h (α := Rat) (.leaf 0) 3 2 [(0, 1)] (by decide +kernel) 1 rfl (.var 0) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kronQ_rel` (hnz, 8): `invs = [(0, 0)]`, `x₀ = 0`: denominators `0` pass every check; `x₀ - 0 = 0` vs `x₀ + 1 - 0 = 1`.
theorem eq_of_kronQ_rel_h8 : ¬ drop0% Lean.Grind.CommRing.eq_of_kronQ_rel 8 := by
  intro h
  have := h (α := Rat) (.leaf 0) 1 2 [(0, 0)] (by unfold InvVars.ok InvVars.denoteVars InvVars.denoteInvs; decide +kernel) 1 rfl (.var 0) (.num 0) (.add (.var 0) (.num 1)) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kronQ_rel` (hB, 15): `B = 1`: `x₀` and `x₁` both evaluate to `2 ^ K`; `x₀ = 1`, `x₁ = 2`.
theorem eq_of_kronQ_rel_h15 : ¬ drop0% Lean.Grind.CommRing.eq_of_kronQ_rel 15 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 1) (.leaf 2)) 3 1 [] rfl (by decide +kernel) 1 rfl (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kronQ_rel` (hK, 16): `K = 0`: `x₀` and `x₁` both evaluate to `1`; `x₀ = 1`, `x₁ = 2`.
theorem eq_of_kronQ_rel_h16 : ¬ drop0% Lean.Grind.CommRing.eq_of_kronQ_rel 16 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 1) (.leaf 2)) 0 2 [] rfl (by decide +kernel) 1 rfl (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kronQ_rel` (h, 17): the check fails: `1 ⋈ 0` vs `0 ⋈ 0`.
theorem eq_of_kronQ_rel_h17 : ¬ drop0% Lean.Grind.CommRing.eq_of_kronQ_rel 17 := by
  intro h
  have := h (α := Rat) (.leaf 0) 2 2 [] rfl (by decide +kernel) 1 rfl (.num 1) (.num 0) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronQ_rel` (hok, 12): `invs = [(0, 1)]` with `x₀ = 0`: `x₀ - 0` vs `1 - 0`.
theorem le_of_kronQ_rel_h12 : ¬ drop0% Lean.Grind.CommRing.le_of_kronQ_rel 12 := by
  intro h
  have := h (α := Rat) (.leaf 0) 3 2 [(0, 1)] (by decide +kernel) 1 rfl (.var 0) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronQ_rel` (hnz, 13): `invs = [(0, 0)]`, `x₀ = 0`: denominators `0` pass every check; `x₀ - 0 = 0` vs `x₀ + 1 - 0 = 1`.
theorem le_of_kronQ_rel_h13 : ¬ drop0% Lean.Grind.CommRing.le_of_kronQ_rel 13 := by
  intro h
  have := h (α := Rat) (.leaf 0) 1 2 [(0, 0)] (by unfold InvVars.ok InvVars.denoteVars InvVars.denoteInvs; decide +kernel) 1 rfl (.var 0) (.num 0) (.add (.var 0) (.num 1)) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronQ_rel` (hB, 20): `B = 1`: `x₀` and `x₁` both evaluate to `2 ^ K`; `x₀ = 2`, `x₁ = 1`.
theorem le_of_kronQ_rel_h20 : ¬ drop0% Lean.Grind.CommRing.le_of_kronQ_rel 20 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 2) (.leaf 1)) 3 1 [] rfl (by decide +kernel) 1 rfl (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronQ_rel` (hK, 21): `K = 0`: `x₀` and `x₁` both evaluate to `1`; `x₀ = 2`, `x₁ = 1`.
theorem le_of_kronQ_rel_h21 : ¬ drop0% Lean.Grind.CommRing.le_of_kronQ_rel 21 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 2) (.leaf 1)) 0 2 [] rfl (by decide +kernel) 1 rfl (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronQ_rel` (h, 22): the check fails: `1 ⋈ 0` vs `0 ⋈ 0`.
theorem le_of_kronQ_rel_h22 : ¬ drop0% Lean.Grind.CommRing.le_of_kronQ_rel 22 := by
  intro h
  have := h (α := Rat) (.leaf 0) 2 2 [] rfl (by decide +kernel) 1 rfl (.num 1) (.num 0) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronQ_rel` (inst, 7): `QS` (order through `sw`, not an `OrderedRing`): `0 ⋈ 1` false, `1 ⋈ 2` true.
theorem le_of_kronQ_rel_h7 : ¬ drop0% Lean.Grind.CommRing.le_of_kronQ_rel 7 := by
  intro h
  have := h (α := QS) (.leaf 0) 4 2 [] rfl (by decide +kernel) 1 rfl (.num 0) (.num 1) (.num 1) (.num 2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronQ_rel` (inst, 6): `QF` (empty `≤`/`<`): lawful `<`, all checks pass, not a linear order.
theorem le_of_kronQ_rel_h6 : ¬ indep0% Lean.Grind.CommRing.le_of_kronQ_rel 6 := by
  intro h
  exact QF.not_lin (h (α := QF) (.leaf 0) 2 2 [] rfl (by decide +kernel) 1 rfl (.num 0) (.num 0) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.CommRing.lt_of_kronQ_rel` (hok, 12): `invs = [(0, 1)]` with `x₀ = 0`: `0 < x₀` is false, `0 < 1` is true.
theorem lt_of_kronQ_rel_h12 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronQ_rel 12 := by
  intro h
  have := h (α := Rat) (.leaf 0) 3 2 [(0, 1)] (by decide +kernel) 1 rfl (.num 0) (.var 0) (.num 0) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronQ_rel` (hnz, 13): `invs = [(0, 0)]`, `x₀ = 0`: denominators `0` pass every check; `0 < x₀` false, `0 < x₀ + 1` true.
theorem lt_of_kronQ_rel_h13 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronQ_rel 13 := by
  intro h
  have := h (α := Rat) (.leaf 0) 1 2 [(0, 0)] (by unfold InvVars.ok InvVars.denoteVars InvVars.denoteInvs; decide +kernel) 1 rfl (.num 0) (.var 0) (.num 0) (.add (.var 0) (.num 1)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronQ_rel` (hB, 20): `B = 1`: `x₀` and `x₁` both evaluate to `2 ^ K`; `x₀ = 1`, `x₁ = 2`.
theorem lt_of_kronQ_rel_h20 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronQ_rel 20 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 1) (.leaf 2)) 3 1 [] rfl (by decide +kernel) 1 rfl (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronQ_rel` (hK, 21): `K = 0`: `x₀` and `x₁` both evaluate to `1`; `x₀ = 1`, `x₁ = 2`.
theorem lt_of_kronQ_rel_h21 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronQ_rel 21 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 1) (.leaf 2)) 0 2 [] rfl (by decide +kernel) 1 rfl (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronQ_rel` (h, 22): the check fails: `0 < 1` vs `0 < 0`.
theorem lt_of_kronQ_rel_h22 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronQ_rel 22 := by
  intro h
  have := h (α := Rat) (.leaf 0) 2 2 [] rfl (by decide +kernel) 1 rfl (.num 0) (.num 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronQ_rel` (inst, 7): `QS` (order through `sw`, not an `OrderedRing`): `0 ⋈ 1` false, `1 ⋈ 2` true.
theorem lt_of_kronQ_rel_h7 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronQ_rel 7 := by
  intro h
  have := h (α := QS) (.leaf 0) 4 2 [] rfl (by decide +kernel) 1 rfl (.num 0) (.num 1) (.num 1) (.num 2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronQ_rel` (inst, 6): `QF` (empty `≤`/`<`): lawful `<`, all checks pass, not a linear order.
theorem lt_of_kronQ_rel_h6 : ¬ indep0% Lean.Grind.CommRing.lt_of_kronQ_rel 6 := by
  intro h
  exact QF.not_lin (h (α := QF) (.leaf 0) 2 2 [] rfl (by decide +kernel) 1 rfl (.num 0) (.num 0) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.CommRing.lt_of_kronQ_rel` (inst, 5): `Q0` (`OrderedRing`, `0 < 0`): `0 < 0` true, `1 < 1` false.
theorem lt_of_kronQ_rel_h5 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronQ_rel 5 := by
  intro h
  have := h (α := Q0) (.leaf 0) 4 2 [] rfl (by decide +kernel) 1 rfl (.num 0) (.num 0) (.num 1) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQLin` (inst, 2): `Fin 2` (`F2`), `invs = [(0, 2)]`, `x₀ = 0 = 2⁻¹`: `lhs = x₀ * 2` denotes `0`, `lhs' = 1`.
theorem Expr_sub_mul_eq_of_kronQLin_h2 : ¬ drop0% Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQLin 2 := by
  intro h
  have := h (α := Fin 2) (.leaf 0) 4 [(0, 2)] F2_ok (by decide +kernel) 1 (.mul (.var 0) (.num 2)) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQLin` (hok, 6): `invs = [(0, 1)]` with `x₀ = 0`: `x₀ - 0` vs `1 - 0`.
theorem Expr_sub_mul_eq_of_kronQLin_h6 : ¬ drop0% Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQLin 6 := by
  intro h
  have := h (α := Rat) (.leaf 0) 3 [(0, 1)] (by decide +kernel) 1 (.var 0) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQLin` (hl, 13): `x₀ * x₀` and `x₁` collide at `xᵢ = 8 ^ (i + 1)`; `x₀ = 2`, `x₁ = 3`: `4` vs `3`.
theorem Expr_sub_mul_eq_of_kronQLin_h13 : ¬ drop0% Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQLin 13 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 2) (.leaf 3)) 3 [] rfl (by decide +kernel) 1 (.mul (.var 0) (.var 0)) (.num 0) (.var 1) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kronQLin_rel` (inst, 2): `Fin 2` (`F2`), `invs = [(0, 2)]`, `x₀ = 0 = 2⁻¹`: `lhs = x₀ * 2` denotes `0`, `lhs' = 1`.
theorem eq_of_kronQLin_rel_h2 : ¬ drop0% Lean.Grind.CommRing.eq_of_kronQLin_rel 2 := by
  intro h
  have := h (α := Fin 2) (.leaf 0) 4 [(0, 2)] F2_ok (by decide +kernel) 1 rfl (.mul (.var 0) (.num 2)) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kronQLin_rel` (hok, 6): `invs = [(0, 1)]` with `x₀ = 0`: `x₀ - 0` vs `1 - 0`.
theorem eq_of_kronQLin_rel_h6 : ¬ drop0% Lean.Grind.CommRing.eq_of_kronQLin_rel 6 := by
  intro h
  have := h (α := Rat) (.leaf 0) 3 [(0, 1)] (by decide +kernel) 1 rfl (.var 0) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kronQLin_rel` (hnz, 7): `invs = [(0, 0)]`, `x₀ = 0`: denominators `0` pass every check; `x₀ - 0 = 0` vs `x₀ + 1 - 0 = 1`.
theorem eq_of_kronQLin_rel_h7 : ¬ drop0% Lean.Grind.CommRing.eq_of_kronQLin_rel 7 := by
  intro h
  have := h (α := Rat) (.leaf 0) 1 [(0, 0)] (by unfold InvVars.ok InvVars.denoteVars InvVars.denoteInvs; decide +kernel) 1 rfl (.var 0) (.num 0) (.add (.var 0) (.num 1)) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kronQLin_rel` (hl, 14): `x₀ * x₀ - 4` and `x₁ - 4` collide at `xᵢ = 32 ^ (i + 1)`; `x₀ = 2`, `x₁ = 3`.
theorem eq_of_kronQLin_rel_h14 : ¬ drop0% Lean.Grind.CommRing.eq_of_kronQLin_rel 14 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 2) (.leaf 3)) 5 [] rfl (by decide +kernel) 1 rfl (.mul (.var 0) (.var 0)) (.num 4) (.var 1) (.num 4) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronQLin_rel` (hok, 11): `invs = [(0, 1)]` with `x₀ = 0`: `x₀ - 0` vs `1 - 0`.
theorem le_of_kronQLin_rel_h11 : ¬ drop0% Lean.Grind.CommRing.le_of_kronQLin_rel 11 := by
  intro h
  have := h (α := Rat) (.leaf 0) 3 [(0, 1)] (by decide +kernel) 1 rfl (.var 0) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronQLin_rel` (hnz, 12): `invs = [(0, 0)]`, `x₀ = 0`: denominators `0` pass every check; `x₀ - 0 = 0` vs `x₀ + 1 - 0 = 1`.
theorem le_of_kronQLin_rel_h12 : ¬ drop0% Lean.Grind.CommRing.le_of_kronQLin_rel 12 := by
  intro h
  have := h (α := Rat) (.leaf 0) 1 [(0, 0)] (by unfold InvVars.ok InvVars.denoteVars InvVars.denoteInvs; decide +kernel) 1 rfl (.var 0) (.num 0) (.add (.var 0) (.num 1)) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronQLin_rel` (hl, 19): `x₀ * x₀ - 4` and `x₁ - 4` collide at `xᵢ = 32 ^ (i + 1)`; `x₀ = 2`, `x₁ = 5`.
theorem le_of_kronQLin_rel_h19 : ¬ drop0% Lean.Grind.CommRing.le_of_kronQLin_rel 19 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 2) (.leaf 5)) 5 [] rfl (by decide +kernel) 1 rfl (.mul (.var 0) (.var 0)) (.num 4) (.var 1) (.num 4) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronQLin_rel` (inst, 7): `QS` (order through `sw`, not an `OrderedRing`): `0 ⋈ 1` false, `1 ⋈ 2` true.
theorem le_of_kronQLin_rel_h7 : ¬ drop0% Lean.Grind.CommRing.le_of_kronQLin_rel 7 := by
  intro h
  have := h (α := QS) (.leaf 0) 4 [] rfl (by decide +kernel) 1 rfl (.num 0) (.num 1) (.num 1) (.num 2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronQLin_rel` (inst, 6): `QF` (empty `≤`/`<`): lawful `<`, all checks pass, not a linear order.
theorem le_of_kronQLin_rel_h6 : ¬ indep0% Lean.Grind.CommRing.le_of_kronQLin_rel 6 := by
  intro h
  exact QF.not_lin (h (α := QF) (.leaf 0) 2 [] rfl (by decide +kernel) 1 rfl (.num 0) (.num 0) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.CommRing.lt_of_kronQLin_rel` (hok, 11): `invs = [(0, 1)]` with `x₀ = 0`: `0 < x₀` is false, `0 < 1` is true.
theorem lt_of_kronQLin_rel_h11 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronQLin_rel 11 := by
  intro h
  have := h (α := Rat) (.leaf 0) 3 [(0, 1)] (by decide +kernel) 1 rfl (.num 0) (.var 0) (.num 0) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronQLin_rel` (hnz, 12): `invs = [(0, 0)]`, `x₀ = 0`: denominators `0` pass every check; `0 < x₀` false, `0 < x₀ + 1` true.
theorem lt_of_kronQLin_rel_h12 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronQLin_rel 12 := by
  intro h
  have := h (α := Rat) (.leaf 0) 1 [(0, 0)] (by unfold InvVars.ok InvVars.denoteVars InvVars.denoteInvs; decide +kernel) 1 rfl (.num 0) (.var 0) (.num 0) (.add (.var 0) (.num 1)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronQLin_rel` (hl, 19): `x₀ * x₀ - 4` and `x₁ - 4` collide at `xᵢ = 32 ^ (i + 1)`; `x₀ = 2`, `x₁ = 3`.
theorem lt_of_kronQLin_rel_h19 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronQLin_rel 19 := by
  intro h
  have := h (α := Rat) (.branch 1 (.leaf 2) (.leaf 3)) 5 [] rfl (by decide +kernel) 1 rfl (.mul (.var 0) (.var 0)) (.num 4) (.var 1) (.num 4) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronQLin_rel` (inst, 7): `QS` (order through `sw`, not an `OrderedRing`): `0 ⋈ 1` false, `1 ⋈ 2` true.
theorem lt_of_kronQLin_rel_h7 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronQLin_rel 7 := by
  intro h
  have := h (α := QS) (.leaf 0) 4 [] rfl (by decide +kernel) 1 rfl (.num 0) (.num 1) (.num 1) (.num 2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronQLin_rel` (inst, 6): `QF` (empty `≤`/`<`): lawful `<`, all checks pass, not a linear order.
theorem lt_of_kronQLin_rel_h6 : ¬ indep0% Lean.Grind.CommRing.lt_of_kronQLin_rel 6 := by
  intro h
  exact QF.not_lin (h (α := QF) (.leaf 0) 2 [] rfl (by decide +kernel) 1 rfl (.num 0) (.num 0) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.CommRing.lt_of_kronQLin_rel` (inst, 5): `Q0` (`OrderedRing`, `0 < 0`): `0 < 0` true, `1 < 1` false.
theorem lt_of_kronQLin_rel_h5 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronQLin_rel 5 := by
  intro h
  have := h (α := Q0) (.leaf 0) 4 [] rfl (by decide +kernel) 1 rfl (.num 0) (.num 0) (.num 1) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kron_rel` (hB, 9): `B = 1`: `x₀` and `x₁` both evaluate to `2 ^ K`; `x₀ = 1`, `x₁ = 2`.
theorem eq_of_kron_rel_h9 : ¬ drop0% Lean.Grind.CommRing.eq_of_kron_rel 9 := by
  intro h
  have := h (α := Int) (.branch 1 (.leaf 1) (.leaf 2)) 3 1 (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kron_rel` (hK, 10): `K = 0`: `x₀` and `x₁` both evaluate to `1`; `x₀ = 1`, `x₁ = 2`.
theorem eq_of_kron_rel_h10 : ¬ drop0% Lean.Grind.CommRing.eq_of_kron_rel 10 := by
  intro h
  have := h (α := Int) (.branch 1 (.leaf 1) (.leaf 2)) 0 2 (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_of_kronLin_rel` (hl, 8): `x₀ * x₀` and `x₁` collide at `xᵢ = 8 ^ (i + 1)`; `x₀ = 2`, `x₁ = 3`.
theorem eq_of_kronLin_rel_h8 : ¬ drop0% Lean.Grind.CommRing.eq_of_kronLin_rel 8 := by
  intro h
  have := h (α := Int) (.branch 1 (.leaf 2) (.leaf 3)) 3 (.mul (.var 0) (.var 0)) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kron_rel` (hB, 13): `B = 1`: `x₀` and `x₁` both evaluate to `2 ^ K`; `x₀ = 2`, `x₁ = 1`.
theorem le_of_kron_rel_h13 : ¬ drop0% Lean.Grind.CommRing.le_of_kron_rel 13 := by
  intro h
  have := h (α := Int) (.branch 1 (.leaf 2) (.leaf 1)) 3 1 (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kron_rel` (hK, 14): `K = 0`: `x₀` and `x₁` both evaluate to `1`; `x₀ = 2`, `x₁ = 1`.
theorem le_of_kron_rel_h14 : ¬ drop0% Lean.Grind.CommRing.le_of_kron_rel 14 := by
  intro h
  have := h (α := Int) (.branch 1 (.leaf 2) (.leaf 1)) 0 2 (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronLin_rel` (hl, 12): `x₀ * x₀` and `x₁` collide at `xᵢ = 8 ^ (i + 1)`; `x₀ = 2`, `x₁ = 3`.
theorem le_of_kronLin_rel_h12 : ¬ drop0% Lean.Grind.CommRing.le_of_kronLin_rel 12 := by
  intro h
  have := h (α := Int) (.branch 1 (.leaf 2) (.leaf 3)) 3 (.mul (.var 0) (.var 0)) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kron_rel` (inst, 5): `ZS` (order through `sw`, not an `OrderedRing`): `0 ⋈ 1` false, `1 ⋈ 2` true.
theorem le_of_kron_rel_h5 : ¬ drop0% Lean.Grind.CommRing.le_of_kron_rel 5 := by
  intro h
  have := h (α := ZS) (.leaf 0) 4 2 (.num 0) (.num 1) (.num 1) (.num 2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_of_kronLin_rel` (inst, 5): `ZS` (order through `sw`, not an `OrderedRing`): `0 ⋈ 1` false, `1 ⋈ 2` true.
theorem le_of_kronLin_rel_h5 : ¬ drop0% Lean.Grind.CommRing.le_of_kronLin_rel 5 := by
  intro h
  have := h (α := ZS) (.leaf 0) 4 (.num 0) (.num 1) (.num 1) (.num 2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kron_rel` (hB, 14): `B = 1`: `x₀` and `x₁` both evaluate to `2 ^ K`; `x₀ = 1`, `x₁ = 2`.
theorem lt_of_kron_rel_h14 : ¬ drop0% Lean.Grind.CommRing.lt_of_kron_rel 14 := by
  intro h
  have := h (α := Int) (.branch 1 (.leaf 1) (.leaf 2)) 3 1 (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kron_rel` (hK, 15): `K = 0`: `x₀` and `x₁` both evaluate to `1`; `x₀ = 1`, `x₁ = 2`.
theorem lt_of_kron_rel_h15 : ¬ drop0% Lean.Grind.CommRing.lt_of_kron_rel 15 := by
  intro h
  have := h (α := Int) (.branch 1 (.leaf 1) (.leaf 2)) 0 2 (.var 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronLin_rel` (hl, 13): `x₀ * x₀` and `x₁` collide at `xᵢ = 8 ^ (i + 1)`; `x₀ = 2`, `x₁ = 5`.
theorem lt_of_kronLin_rel_h13 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronLin_rel 13 := by
  intro h
  have := h (α := Int) (.branch 1 (.leaf 2) (.leaf 5)) 3 (.mul (.var 0) (.var 0)) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kron_rel` (inst, 5): `ZS` (order through `sw`, not an `OrderedRing`): `0 ⋈ 1` false, `1 ⋈ 2` true.
theorem lt_of_kron_rel_h5 : ¬ drop0% Lean.Grind.CommRing.lt_of_kron_rel 5 := by
  intro h
  have := h (α := ZS) (.leaf 0) 4 2 (.num 0) (.num 1) (.num 1) (.num 2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kron_rel` (inst, 6): `Z0` (`OrderedRing`, `0 < 0`): `0 < 0` true, `1 < 1` false.
theorem lt_of_kron_rel_h6 : ¬ drop0% Lean.Grind.CommRing.lt_of_kron_rel 6 := by
  intro h
  have := h (α := Z0) (.leaf 0) 4 2 (.num 0) (.num 0) (.num 1) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronLin_rel` (inst, 5): `ZS` (order through `sw`, not an `OrderedRing`): `0 ⋈ 1` false, `1 ⋈ 2` true.
theorem lt_of_kronLin_rel_h5 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronLin_rel 5 := by
  intro h
  have := h (α := ZS) (.leaf 0) 4 (.num 0) (.num 1) (.num 1) (.num 2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_of_kronLin_rel` (inst, 6): `Z0` (`OrderedRing`, `0 < 0`): `0 < 0` true, `1 < 1` false.
theorem lt_of_kronLin_rel_h6 : ¬ drop0% Lean.Grind.CommRing.lt_of_kronLin_rel 6 := by
  intro h
  have := h (α := Z0) (.leaf 0) 4 (.num 0) (.num 0) (.num 1) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_cancel_of_kronLinS` (inst, 2): `BS` (Boolean semiring): `a = 1`, `b = 2` both denote `1`, but `a' = 0 ≠ 1 = b'`.
theorem eq_cancel_of_kronLinS_h2 : ¬ drop0% Lean.Grind.CommRing.eq_cancel_of_kronLinS 2 := by
  intro h
  have := h (α := BS) (.leaf 0) 4 (.num 1) (.num 2) (.num 0) (.num 1) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_cancel_of_kronLinS` (hl₁, 10): `a = x₀ * x₀` and `a' + c = x₁ + 0` collide; `x₀ = 0`, `x₁ = 1`.
theorem eq_cancel_of_kronLinS_h10 : ¬ drop0% Lean.Grind.CommRing.eq_cancel_of_kronLinS 10 := by
  intro h
  have := h (α := Nat) (.branch 1 (.leaf 0) (.leaf 1)) 3 (.mul (.var 0) (.var 0)) (.num 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_cancel_of_kronLinS` (hl₂, 13): `b = x₀ * x₀` and `b' + c = x₁ + 0` collide; `x₀ = 0`, `x₁ = 1`.
theorem eq_cancel_of_kronLinS_h13 : ¬ drop0% Lean.Grind.CommRing.eq_cancel_of_kronLinS 13 := by
  intro h
  have := h (α := Nat) (.branch 1 (.leaf 0) (.leaf 1)) 3 (.num 0) (.mul (.var 0) (.var 0)) (.num 0) (.var 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_cancel_of_kronLinS` (hl₁, 14): `a = x₀ * x₀` and `a' + c = x₁ + 0` collide; `x₀ = 0`, `x₁ = 1`.
theorem le_cancel_of_kronLinS_h14 : ¬ drop0% Lean.Grind.CommRing.le_cancel_of_kronLinS 14 := by
  intro h
  have := h (α := Nat) (.branch 1 (.leaf 0) (.leaf 1)) 3 (.mul (.var 0) (.var 0)) (.num 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_cancel_of_kronLinS` (hl₂, 17): `b = x₀ * x₀` and `b' + c = x₁ + 0` collide; `x₀ = 0`, `x₁ = 1`: `1 ≤ 0` vs `1 ≤ 1`.
theorem le_cancel_of_kronLinS_h17 : ¬ drop0% Lean.Grind.CommRing.le_cancel_of_kronLinS 17 := by
  intro h
  have := h (α := Nat) (.branch 1 (.leaf 0) (.leaf 1)) 3 (.num 1) (.mul (.var 0) (.var 0)) (.num 1) (.var 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_cancel_of_kronLinS` (hl₁, 15): `a = x₀ * x₀` and `a' + c = x₁ + 0` collide; `x₀ = 0`, `x₁ = 1`: `0 < 1` vs `1 < 1`.
theorem lt_cancel_of_kronLinS_h15 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronLinS 15 := by
  intro h
  have := h (α := Nat) (.branch 1 (.leaf 0) (.leaf 1)) 3 (.mul (.var 0) (.var 0)) (.num 1) (.var 1) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_cancel_of_kronLinS` (hl₂, 18): `b = x₀ * x₀` and `b' + c = x₁ + 0` collide; `x₀ = 1`, `x₁ = 0`: `0 < 1` vs `0 < 0`.
theorem lt_cancel_of_kronLinS_h18 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronLinS 18 := by
  intro h
  have := h (α := Nat) (.branch 1 (.leaf 1) (.leaf 0)) 3 (.num 0) (.mul (.var 0) (.var 0)) (.num 0) (.var 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_cancel_of_kronLinS` (inst, 6): `ZS` (order through `sw`, not an `OrderedRing`): `1 ≤ 2` true, `0 ≤ 1` false.
theorem le_cancel_of_kronLinS_h6 : ¬ drop0% Lean.Grind.CommRing.le_cancel_of_kronLinS 6 := by
  intro h
  have := h (α := ZS) (.leaf 0) 4 (.num 1) (.num 2) (.num 0) (.num 1) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_cancel_of_kronLinS` (hK₂, 18): `K = 0`: `x₀` and `x₁ + 0` both evaluate to `1`; `x₀ = 0`, `x₁ = -1`: `0 ≤ 0` vs `0 ≤ -1`.
theorem le_cancel_of_kronLinS_h18 : ¬ drop0% Lean.Grind.CommRing.le_cancel_of_kronLinS 18 := by
  intro h
  have := h (α := Int) (.branch 1 (.leaf 0) (.leaf (-1))) 0 (.num 0) (.var 0) (.num 0) (.var 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_cancel_of_kronLinS` (h₂, 19): the second check fails: `1 ≤ 0` vs `1 ≤ 1`.
theorem le_cancel_of_kronLinS_h19 : ¬ drop0% Lean.Grind.CommRing.le_cancel_of_kronLinS 19 := by
  intro h
  have := h (α := Nat) (.leaf 0) 3 (.num 1) (.num 0) (.num 1) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_cancel_of_kronLinS` (inst, 5): `Z0` (`OrderedRing`, `0 < 0`): `1 < 1` false, `0 < 0` true.
theorem lt_cancel_of_kronLinS_h5 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronLinS 5 := by
  intro h
  have := h (α := Z0) (.leaf 0) 4 (.num 1) (.num 1) (.num 0) (.num 0) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_cancel_of_kronLinS` (inst, 7): `ZS` (order through `sw`, not an `OrderedRing`): `1 < 2` true, `0 < 1` false.
theorem lt_cancel_of_kronLinS_h7 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronLinS 7 := by
  intro h
  have := h (α := ZS) (.leaf 0) 4 (.num 1) (.num 2) (.num 0) (.num 1) (.num 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_cancel_of_kronLinS` (hK₁, 16): `K = 0`: `x₀` and `x₁ + 0` both evaluate to `1`; `x₀ = -1`, `x₁ = 0`: `-1 < 0` vs `0 < 0`.
theorem lt_cancel_of_kronLinS_h16 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronLinS 16 := by
  intro h
  have := h (α := Int) (.branch 1 (.leaf (-1)) (.leaf 0)) 0 (.var 0) (.num 0) (.var 1) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_cancel_of_kronLinS` (h₁, 17): the first check fails: `0 < 1` vs `1 < 1`.
theorem lt_cancel_of_kronLinS_h17 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronLinS 17 := by
  intro h
  have := h (α := Nat) (.leaf 0) 3 (.num 0) (.num 1) (.num 1) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.toLinQ_spec` (inst, 2): `Fin 2` (`F2`), `invs = [(0, 2)]`, `f = 0` (`f 0 = 0 = 2⁻¹`):
-- for `e = x₀`, `toLinQ = (1, 2)`, and the first conjunct reads `1 = 2 * 0`.
theorem Expr_toLinQ_spec_h2 : ¬ drop0% Lean.Grind.CommRing.Expr.toLinQ_spec 2 := by
  intro h
  have := (h (α := Fin 2) (fun _ => 0) 1 [(0, 2)] (by
    intro x c hx
    cases x with
    | zero => cases hx; exact ⟨rfl, by decide⟩
    | succ n => cases hx) (.var 0) (by decide +kernel)).1
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.toLinQ_spec` (he, 8): `e = x₀ * x₀` is not linear; `toLinQ` scales by the constant value
-- `0` of `x₀`, so the Kronecker conjunct reads `0 = 2 ^ 2` (`K = 1`).
theorem Expr_toLinQ_spec_h8 : ¬ drop0% Lean.Grind.CommRing.Expr.toLinQ_spec 8 := by
  intro h
  have := (h (α := Rat) (fun _ => 0) 1 [] (by intro x c hx; cases hx) (.mul (.var 0) (.var 0))).2.2.1
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.Deg.mulTermTL` (hq, 9): `B = 2`, `q = x₀` (code 1) of degree 1 although `D₂ = 0`.
theorem PPoly_Deg_mulTermTL_h9 : ¬ drop0% Lean.Grind.CommRing.PPoly.Deg.mulTermTL 9 := by
  intro h
  have := h (B := 2) (D₁ := 0) (D₂ := 0) (by decide) (q := .add 1 1 1 (.num 0)) 1 0 0 (by decide +kernel) (by decide)
  revert this; simp only [PPoly.mulTermTL, PPoly.Deg]; decide +kernel

-- `Lean.Grind.CommRing.PPoly.denoteSN_mulTermTL` (hv, 13): `B = 2`, `x₀ · x₀` overflows into `x₁` (code 2):
-- `f = i ↦ i + 2` gives `3` vs `4`; `D₁ = 0`, `D₂ = 1`, `dsum 1 = 1 > D₁`.
theorem PPoly_denoteSN_mulTermTL_h13 : ¬ drop0% Lean.Grind.CommRing.PPoly.denoteSN_mulTermTL 13 := by
  intro h
  have := h (α := Nat) (fun i => i + 2) (B := 2) (D₁ := 0) (D₂ := 1) (by decide) (q := .add 1 1 1 (.num 0)) (k := 1) 0 1
    (by simp only [PPoly.NonNeg]; decide) (by decide) (by simp only [PPoly.Deg]; decide +kernel) (by decide)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.denoteSN_mulTermTL` (hd, 14): as for `hv`, with `D₁ = 1`, `D₂ = 0` (`q` has degree 1).
theorem PPoly_denoteSN_mulTermTL_h14 : ¬ drop0% Lean.Grind.CommRing.PPoly.denoteSN_mulTermTL 14 := by
  intro h
  have := h (α := Nat) (fun i => i + 2) (B := 2) (D₁ := 1) (D₂ := 0) (by decide) (q := .add 1 1 1 (.num 0)) (k := 1) 0 1
    (by simp only [PPoly.NonNeg]; decide) (by decide) (by decide +kernel) (by decide)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.denoteSN_mulTermTL` (hD, 15): as for `hv`, with `D₁ = D₂ = 1` (`D₁ + D₂ = B`).
theorem PPoly_denoteSN_mulTermTL_h15 : ¬ drop0% Lean.Grind.CommRing.PPoly.denoteSN_mulTermTL 15 := by
  intro h
  have := h (α := Nat) (fun i => i + 2) (B := 2) (D₁ := 1) (D₂ := 1) (by decide) (q := .add 1 1 1 (.num 0)) (k := 1) 0 1
    (by simp only [PPoly.NonNeg]; decide) (by decide) (by decide +kernel) (by simp only [PPoly.Deg]; decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.denoteSN_mulTL` (dp, 11): `B = 2`, `p = q = x₀`, `D₁ = 0`, `D₂ = 1`: `x₀ · x₀` overflows
-- into `x₁` (`f = i ↦ i + 2`: `3` vs `4`).
theorem PPoly_denoteSN_mulTL_h11 : ¬ drop0% Lean.Grind.CommRing.PPoly.denoteSN_mulTL 11 := by
  intro h
  have := h (α := Nat) (fun i => i + 2) (B := 2) (D₁ := 0) (D₂ := 1) (by decide) (p := .add 1 1 1 (.num 0)) (q := .add 1 1 1 (.num 0))
    (by simp only [PPoly.NonNeg]; decide) (by simp only [PPoly.NonNeg]; decide) (by simp only [PPoly.Deg]; decide +kernel) (by decide)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.denoteSN_mulTL` (dq, 12): as for `dp`, with `D₁ = 1`, `D₂ = 0`.
theorem PPoly_denoteSN_mulTL_h12 : ¬ drop0% Lean.Grind.CommRing.PPoly.denoteSN_mulTL 12 := by
  intro h
  have := h (α := Nat) (fun i => i + 2) (B := 2) (D₁ := 1) (D₂ := 0) (by decide) (p := .add 1 1 1 (.num 0)) (q := .add 1 1 1 (.num 0))
    (by simp only [PPoly.NonNeg]; decide) (by simp only [PPoly.NonNeg]; decide) (by simp only [PPoly.Deg]; decide +kernel) (by decide)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.denoteSN_mulTL` (hD, 13): as for `dp`, with `D₁ = D₂ = 1`.
theorem PPoly_denoteSN_mulTL_h13 : ¬ drop0% Lean.Grind.CommRing.PPoly.denoteSN_mulTL 13 := by
  intro h
  have := h (α := Nat) (fun i => i + 2) (B := 2) (D₁ := 1) (D₂ := 1) (by decide) (p := .add 1 1 1 (.num 0)) (q := .add 1 1 1 (.num 0))
    (by simp only [PPoly.NonNeg]; decide) (by simp only [PPoly.NonNeg]; decide) (by simp only [PPoly.Deg]; decide +kernel)
    (by simp only [PPoly.Deg]; decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.denoteSN_powTL` (dp, 8): `B = 2`, `p = x₀`, `D = 0`, `k = 2`: `x₀²` overflows into `x₁`.
theorem PPoly_denoteSN_powTL_h8 : ¬ drop0% Lean.Grind.CommRing.PPoly.denoteSN_powTL 8 := by
  intro h
  have := h (α := Nat) (fun i => i + 2) (B := 2) (D := 0) (by decide) (p := .add 1 1 1 (.num 0))
    (by simp only [PPoly.NonNeg]; decide) 2 (by decide)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.denoteSN_powTL` (hD, 10): as for `dp`, with `D = 1` (`D * k = B`).
theorem PPoly_denoteSN_powTL_h10 : ¬ drop0% Lean.Grind.CommRing.PPoly.denoteSN_powTL 10 := by
  intro h
  have := h (α := Nat) (fun i => i + 2) (B := 2) (D := 1) (by decide) (p := .add 1 1 1 (.num 0))
    (by simp only [PPoly.NonNeg]; decide) (by simp only [PPoly.Deg]; decide +kernel) 2
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.denoteSN_removeCode` (hp, 6): `p = x₀ - x₀` (as two terms), `c = 1`: the coefficient
-- of code 1 is `0`, but the terms denote `1 · 2 + 0`.
theorem PPoly_denoteSN_removeCode_h6 : ¬ drop0% Lean.Grind.CommRing.PPoly.denoteSN_removeCode 6 := by
  intro h
  have := h (α := Nat) (fun i => i + 2) 2 1 (.add 1 1 1 (.add (-1) 1 1 (.num 0)))
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.denoteSN_eq_of_coeff` (a, 8): `p = x₀ - x₀` (two terms) and `q = 0` have the same
-- coefficients, `q` is non-negative, but `p` denotes `2`.
theorem PPoly_denoteSN_eq_of_coeff_h8 : ¬ drop0% Lean.Grind.CommRing.PPoly.denoteSN_eq_of_coeff 8 := by
  intro h
  have := h (α := Nat) (fun i => i + 2) 2 2 (.add 1 1 1 (.add (-1) 1 1 (.num 0))) (.num 0) (by decide)
    (by simp only [PPoly.NonNeg]; decide) (by intro c; simp only [PPoly.coeff]; by_cases h1 : 1 = c <;> by_cases h0 : c = 0 <;> simp [h1, h0])
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.denoteSN_eq_of_coeff` (a, 9): the same with `p` and `q` swapped.
theorem PPoly_denoteSN_eq_of_coeff_h9 : ¬ drop0% Lean.Grind.CommRing.PPoly.denoteSN_eq_of_coeff 9 := by
  intro h
  have := h (α := Nat) (fun i => i + 2) 2 2 (.num 0) (.add 1 1 1 (.add (-1) 1 1 (.num 0))) (by decide)
    (by simp only [PPoly.NonNeg]; decide) (by intro c; simp only [PPoly.coeff]; by_cases h1 : 1 = c <;> by_cases h0 : c = 0 <;> simp [h1, h0])
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_kronSN` (hB, 7): `B = 1`: `x₀` and `x₁` both evaluate to `2 ^ K`; `x₀ = 0`, `x₁ = 1`.
theorem Expr_eq_of_kronSN_h7 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_kronSN 7 := by
  intro h
  have := h (α := Nat) (.branch 1 (.leaf 0) (.leaf 1)) 3 1 (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_true_of_kronSN` (hB, 7): as for `Lean.Grind.CommRing.Expr.eq_of_kronSN`.
theorem eq_true_of_kronSN_h7 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kronSN 7 := by
  intro h
  have := h (α := Nat) (.branch 1 (.leaf 0) (.leaf 1)) 3 1 (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.le_true_of_kronSN` (hB, 9): `B = 1`, `x₀ = 1`, `x₁ = 0`: `1 ≤ 0`.
theorem le_true_of_kronSN_h9 : ¬ drop0% Lean.Grind.CommRing.le_true_of_kronSN 9 := by
  intro h
  have := h (α := Nat) (.branch 1 (.leaf 1) (.leaf 0)) 3 1 (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.lt_false_of_kronSN` (hB, 11): `B = 1`, `x₀ = 0`, `x₁ = 1`: `0 < 1`.
theorem lt_false_of_kronSN_h11 : ¬ drop0% Lean.Grind.CommRing.lt_false_of_kronSN 11 := by
  intro h
  have := h (α := Nat) (.branch 1 (.leaf 0) (.leaf 1)) 3 1 (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

/-! ## Removable -/

section Removable
open AddCommMonoid AddCommGroup NatModule IntModule
open Semiring hiding add_zero add_comm add_assoc
open Ring hiding sub_eq_add_neg
open CommSemiring

/-! ### Digit sums: subadditive, and `0` for `B ≤ 1` -/

theorem dsum_of_not (B v : Nat) (hB : ¬ 1 < B) : PPoly.dsum B v = 0 := by
  rw [PPoly.dsum]; simp [hB]

theorem dsum_one {B : Nat} (hB : 1 < B) : PPoly.dsum B 1 = 1 := by
  rw [PPoly.dsum_eq hB, Nat.mod_eq_of_lt hB, Nat.div_eq_of_lt hB, PPoly.dsum_zero]

theorem dsum_add_le_aux (B : Nat) (hB : 1 < B) :
    ∀ n a b, a + b ≤ n → PPoly.dsum B (a + b) ≤ PPoly.dsum B a + PPoly.dsum B b := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro a b hab
  by_cases h0 : a + b = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb; simp [PPoly.dsum_zero]
  have hB0 : 0 < B := by omega
  have ea := Nat.mod_add_div a B
  have eb := Nat.mod_add_div b B
  have ma := Nat.mod_lt a hB0
  have mb := Nat.mod_lt b hB0
  have hdiv : (a + b) / B < a + b := Nat.div_lt_self (by omega) hB
  rw [PPoly.dsum_eq hB (a + b), PPoly.dsum_eq hB a, PPoly.dsum_eq hB b]
  by_cases hc : a % B + b % B < B
  · have hr := PPoly.add_mod_div hB a b hc
    rw [hr.1, hr.2]
    have := ih ((a + b) / B) (by omega) (a / B) (b / B) (by rw [hr.2]; exact Nat.le_refl _)
    rw [← hr.2] at this ⊢
    omega
  · have hlt : a % B + b % B - B < B := by omega
    have e : a + b = (a % B + b % B - B) + B * (a / B + b / B + 1) := by
      rw [Nat.mul_add, Nat.mul_add]; omega
    have hm : (a + b) % B = a % B + b % B - B := by
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    have hq : (a + b) / B = a / B + b / B + 1 := by
      rw [e, Nat.add_mul_div_left _ _ hB0, Nat.div_eq_of_lt hlt, Nat.zero_add]
    rw [hm, hq]
    have h₁ := ih ((a + b) / B) (by omega) (a / B + b / B) 1 (by rw [hq]; exact Nat.le_refl _)
    have h₂ := ih ((a + b) / B) (by omega) (a / B) (b / B) (by rw [hq]; omega)
    rw [dsum_one hB] at h₁
    omega

theorem dsum_add_le (B a b : Nat) : PPoly.dsum B (a + b) ≤ PPoly.dsum B a + PPoly.dsum B b := by
  by_cases hB : 1 < B
  · exact dsum_add_le_aux B hB _ a b (Nat.le_refl _)
  · simp [dsum_of_not B _ hB]

theorem deg_mulTermTL {B D₁ D₂ : Nat} {q : PPoly} (k : Int) (d v : Nat) (hv : PPoly.dsum B v ≤ D₁)
    (hq : q.Deg B D₂) : (q.mulTermTL k d v).Deg B (D₁ + D₂) := by
  induction q with
  | num c => exact ⟨by omega, trivial⟩
  | add k' d' v' q ih =>
    refine ⟨?_, ih hq.2⟩
    have := dsum_add_le B v v'; have := hq.1; omega

theorem deg_mulTL {B D₁ D₂ : Nat} {p q : PPoly} (hp : p.Deg B D₁) (hq : q.Deg B D₂) :
    (p.mulTL q).Deg B (D₁ + D₂) := by
  induction p with
  | num k => exact PPoly.Deg.mono (by omega) _ (PPoly.Deg.scale k hq)
  | add k d v p ih => exact PPoly.Deg.append (deg_mulTermTL k d v hp.1 hq) (ih hp.2)

theorem deg_powTL {B D : Nat} {p : PPoly} (hp : p.Deg B D) (k : Nat) : (p.powTL k).Deg B (D * k) := by
  induction k with
  | zero => trivial
  | succ k ih => rw [Nat.mul_succ]; exact deg_mulTL ih hp

-- `Lean.Grind.CommRing.PPoly.Deg.mulTermTL` (hB, 3): digit sums are subadditive (`dsum_add_le`), also for `B ≤ 1`.
theorem PPoly_Deg_mulTermTL_h3 : drop% Lean.Grind.CommRing.PPoly.Deg.mulTermTL 3 := by
  intro B D₁ D₂ q k d v hv hq _; exact deg_mulTermTL k d v hv hq

-- `Lean.Grind.CommRing.PPoly.Deg.mulTermTL` (hD, 10): digit sums are subadditive, a carry only lowers them.
theorem PPoly_Deg_mulTermTL_h10 : drop% Lean.Grind.CommRing.PPoly.Deg.mulTermTL 10 := by
  intro B D₁ D₂ _ q k d v hv hq; exact deg_mulTermTL k d v hv hq

-- `Lean.Grind.CommRing.PPoly.Deg.mulTL` (hB, 3): by subadditivity of digit sums.
theorem PPoly_Deg_mulTL_h3 : drop% Lean.Grind.CommRing.PPoly.Deg.mulTL 3 := by
  intro B D₁ D₂ p q hp hq _; exact deg_mulTL hp hq

-- `Lean.Grind.CommRing.PPoly.Deg.mulTL` (hD, 8): by subadditivity of digit sums.
theorem PPoly_Deg_mulTL_h8 : drop% Lean.Grind.CommRing.PPoly.Deg.mulTL 8 := by
  intro B D₁ D₂ _ p q hp hq; exact deg_mulTL hp hq

-- `Lean.Grind.CommRing.PPoly.Deg.powTL` (hB, 2): by subadditivity of digit sums.
theorem PPoly_Deg_powTL_h2 : drop% Lean.Grind.CommRing.PPoly.Deg.powTL 2 := by
  intro B D p hp k _; exact deg_powTL hp k

-- `Lean.Grind.CommRing.PPoly.Deg.powTL` (hD, 6): by subadditivity of digit sums.
theorem PPoly_Deg_powTL_h6 : drop% Lean.Grind.CommRing.PPoly.Deg.powTL 6 := by
  intro B D _ p hp k; exact deg_powTL hp k

/-! ### `denoteSN`: one non-negative factor suffices, every monomial is `1` for `B ≤ 1` -/

theorem toNat_mul_left {a b : Int} (ha : 0 ≤ a) : (a * b).toNat = a.toNat * b.toNat := by
  by_cases hb : 0 ≤ b
  · exact Int.toNat_mul ha hb
  · rw [Int.toNat_of_nonpos (Int.mul_nonpos_of_nonneg_of_nonpos ha (by omega)),
      Int.toNat_of_nonpos (z := b) (by omega), Nat.mul_zero]

theorem toNat_mul_right {a b : Int} (hb : 0 ≤ b) : (a * b).toNat = a.toNat * b.toNat := by
  rw [Int.mul_comm, toNat_mul_left hb, Nat.mul_comm]

theorem toNat_mul_or {a b : Int} (h : 0 ≤ a ∨ 0 ≤ b) : (a * b).toNat = a.toNat * b.toNat :=
  h.elim toNat_mul_left toNat_mul_right

theorem monDenote_of_not {α} [Semiring α] (f : Nat → α) {B : Nat} (hB : ¬ 1 < B) (i v : Nat) :
    PPoly.monDenote f B i v = 1 := by
  rw [PPoly.monDenote]; simp [hB]

theorem monDenote_add_gen {α} [CommSemiring α] (f : Nat → α) {B : Nat} (i v₁ v₂ : Nat)
    (h : 1 < B → PPoly.dsum B v₁ + PPoly.dsum B v₂ < B) :
    PPoly.monDenote f B i (v₁ + v₂) = PPoly.monDenote f B i v₁ * PPoly.monDenote f B i v₂ := by
  by_cases hB : 1 < B
  · exact PPoly.monDenote_add f hB i v₁ v₂ (h hB)
  · rw [monDenote_of_not f hB, monDenote_of_not f hB, monDenote_of_not f hB, Semiring.mul_one]

theorem denoteSN_scale_gen {α} [Semiring α] (f : Nat → α) (B : Nat) {p : PPoly} {k : Int}
    (hs : 0 ≤ k ∨ p.NonNeg) : (p.scale k).denoteSN f B = (k.toNat : α) * p.denoteSN f B := by
  induction p with
  | num k' => show ((k * k').toNat : α) = _; rw [toNat_mul_or hs, Semiring.natCast_mul]; rfl
  | add k' d v p ih =>
    show ((k * k').toNat : α) * PPoly.monDenote f B 0 v + (p.scale k).denoteSN f B =
      (k.toNat : α) * ((k'.toNat : α) * PPoly.monDenote f B 0 v + p.denoteSN f B)
    rw [ih (hs.imp id (·.2)), toNat_mul_or (hs.imp id (·.1)), Semiring.natCast_mul, Semiring.left_distrib,
      Semiring.mul_assoc]

theorem denoteSN_mulTermTL_gen {α} [CommSemiring α] (f : Nat → α) {B D₁ D₂ : Nat} {q : PPoly} {k : Int} (d v : Nat)
    (hs : 0 ≤ k ∨ q.NonNeg) (hdeg : 1 < B → PPoly.dsum B v ≤ D₁ ∧ q.Deg B D₂ ∧ D₁ + D₂ < B) :
    (q.mulTermTL k d v).denoteSN f B = (k.toNat : α) * PPoly.monDenote f B 0 v * q.denoteSN f B := by
  induction q with
  | num c =>
    show ((k * c).toNat : α) * PPoly.monDenote f B 0 v + ((0 : Int).toNat : α) = _ * (c.toNat : α)
    rw [toNat_mul_or hs, Semiring.natCast_mul, show (0 : Int).toNat = 0 from rfl, Semiring.natCast_zero,
      Semiring.add_zero, Semiring.mul_assoc, Semiring.mul_assoc, CommSemiring.mul_comm (c.toNat : α)]
  | add k' d' v' q ih =>
    show ((k * k').toNat : α) * PPoly.monDenote f B 0 (v + v') + (q.mulTermTL k d v).denoteSN f B =
      (k.toNat : α) * PPoly.monDenote f B 0 v * ((k'.toNat : α) * PPoly.monDenote f B 0 v' + q.denoteSN f B)
    rw [ih (hs.imp id (·.2)) (fun hB => ⟨(hdeg hB).1, (hdeg hB).2.1.2, (hdeg hB).2.2⟩),
      toNat_mul_or (hs.imp id (·.1)), Semiring.natCast_mul,
      monDenote_add_gen f 0 v v' (fun hB => by have := hdeg hB; have := (hdeg hB).2.1.1; omega),
      Semiring.left_distrib]
    congr 1
    simp only [Semiring.mul_assoc, CommSemiring.mul_left_comm]

theorem addConst_zero (r : PPoly) : PPoly.append.addConst r 0 = r := by
  induction r with
  | num k => simp [PPoly.append.addConst]
  | add k d v r ih => simp [PPoly.append.addConst, ih]

theorem denoteSN_append_mulTermTL {α} [Semiring α] (f : Nat → α) (B : Nat) (k : Int) (d v : Nat) (q r : PPoly) :
    ((q.mulTermTL k d v).append r).denoteSN f B = (q.mulTermTL k d v).denoteSN f B + r.denoteSN f B := by
  induction q with
  | num c =>
    show ((k * c).toNat : α) * PPoly.monDenote f B 0 v + (PPoly.append.addConst r 0).denoteSN f B =
      ((k * c).toNat : α) * PPoly.monDenote f B 0 v + ((0 : Int).toNat : α) + r.denoteSN f B
    rw [addConst_zero, show (0 : Int).toNat = 0 from rfl, Semiring.natCast_zero, Semiring.add_zero]
  | add k' d' v' q ih =>
    show ((k * k').toNat : α) * PPoly.monDenote f B 0 (v + v') + ((q.mulTermTL k d v).append r).denoteSN f B =
      ((k * k').toNat : α) * PPoly.monDenote f B 0 (v + v') + (q.mulTermTL k d v).denoteSN f B + r.denoteSN f B
    rw [ih, Semiring.add_assoc]

theorem denoteSN_mulTL_gen {α} [CommSemiring α] (f : Nat → α) {B D₁ D₂ : Nat} {p q : PPoly}
    (hs : p.NonNeg ∨ q.NonNeg) (hdeg : 1 < B → p.Deg B D₁ ∧ q.Deg B D₂ ∧ D₁ + D₂ < B) :
    (p.mulTL q).denoteSN f B = p.denoteSN f B * q.denoteSN f B := by
  induction p with
  | num k => show (q.scale k).denoteSN f B = (k.toNat : α) * _; rw [denoteSN_scale_gen f B hs]
  | add k d v p ih =>
    show ((q.mulTermTL k d v).append (p.mulTL q)).denoteSN f B =
      ((k.toNat : α) * PPoly.monDenote f B 0 v + p.denoteSN f B) * _
    rw [denoteSN_append_mulTermTL, denoteSN_mulTermTL_gen f d v (hs.imp (·.1) id)
        (fun hB => ⟨(hdeg hB).1.1, (hdeg hB).2.1, (hdeg hB).2.2⟩),
      ih (hs.imp (·.2) id) (fun hB => ⟨(hdeg hB).1.2, (hdeg hB).2.1, (hdeg hB).2.2⟩), Semiring.right_distrib]

-- `Lean.Grind.CommRing.PPoly.denoteSN_scale` (hp, 6): `(k * c).toNat = k.toNat * c.toNat` once `0 ≤ k`.
theorem PPoly_denoteSN_scale_h6 : drop% Lean.Grind.CommRing.PPoly.denoteSN_scale 6 := by
  intro α _ f B p k hk; exact denoteSN_scale_gen f B (Or.inl hk)

-- `Lean.Grind.CommRing.PPoly.denoteSN_scale` (hk, 7): `(k * c).toNat = k.toNat * c.toNat` once every `0 ≤ c`.
theorem PPoly_denoteSN_scale_h7 : drop% Lean.Grind.CommRing.PPoly.denoteSN_scale 7 := by
  intro α _ f B p k hp; exact denoteSN_scale_gen f B (Or.inr hp)

-- `Lean.Grind.CommRing.PPoly.denoteSN_mulTermTL` (hB, 6): for `B ≤ 1` every monomial denotes `1`.
theorem PPoly_denoteSN_mulTermTL_h6 : drop% Lean.Grind.CommRing.PPoly.denoteSN_mulTermTL 6 := by
  intro α _ f B D₁ D₂ q k d v hq hk hv hd hD; exact denoteSN_mulTermTL_gen f d v (Or.inl hk) (fun _ => ⟨hv, hd, hD⟩)

-- `Lean.Grind.CommRing.PPoly.denoteSN_mulTermTL` (hq, 11): `0 ≤ k` alone gives `(k * c).toNat = k.toNat * c.toNat`.
theorem PPoly_denoteSN_mulTermTL_h11 : drop% Lean.Grind.CommRing.PPoly.denoteSN_mulTermTL 11 := by
  intro α _ f B D₁ D₂ hB q k d v hk hv hd hD; exact denoteSN_mulTermTL_gen f d v (Or.inl hk) (fun _ => ⟨hv, hd, hD⟩)

-- `Lean.Grind.CommRing.PPoly.denoteSN_mulTermTL` (hk, 12): non-negative coefficients of `q` alone suffice.
theorem PPoly_denoteSN_mulTermTL_h12 : drop% Lean.Grind.CommRing.PPoly.denoteSN_mulTermTL 12 := by
  intro α _ f B D₁ D₂ hB q k d v hq hv hd hD; exact denoteSN_mulTermTL_gen f d v (Or.inr hq) (fun _ => ⟨hv, hd, hD⟩)

-- `Lean.Grind.CommRing.PPoly.denoteSN_mulTL` (hB, 6): for `B ≤ 1` every monomial denotes `1`.
theorem PPoly_denoteSN_mulTL_h6 : drop% Lean.Grind.CommRing.PPoly.denoteSN_mulTL 6 := by
  intro α _ f B D₁ D₂ p q hp hq dp dq hD; exact denoteSN_mulTL_gen f (Or.inl hp) (fun _ => ⟨dp, dq, hD⟩)

-- `Lean.Grind.CommRing.PPoly.denoteSN_mulTL` (hp, 9): non-negative coefficients of `q` alone suffice.
theorem PPoly_denoteSN_mulTL_h9 : drop% Lean.Grind.CommRing.PPoly.denoteSN_mulTL 9 := by
  intro α _ f B D₁ D₂ hB p q hq dp dq hD; exact denoteSN_mulTL_gen f (Or.inr hq) (fun _ => ⟨dp, dq, hD⟩)

-- `Lean.Grind.CommRing.PPoly.denoteSN_mulTL` (hq, 10): non-negative coefficients of `p` alone suffice.
theorem PPoly_denoteSN_mulTL_h10 : drop% Lean.Grind.CommRing.PPoly.denoteSN_mulTL 10 := by
  intro α _ f B D₁ D₂ hB p q hp dp dq hD; exact denoteSN_mulTL_gen f (Or.inl hp) (fun _ => ⟨dp, dq, hD⟩)

-- `Lean.Grind.CommRing.PPoly.denoteSN_powTL` (hB, 5): for `B ≤ 1` every monomial denotes `1`.
theorem PPoly_denoteSN_powTL_h5 : drop% Lean.Grind.CommRing.PPoly.denoteSN_powTL 5 := by
  intro α _ f B D p hp dp k hD
  by_cases hB : 1 < B
  · exact PPoly.denoteSN_powTL f hB hp dp k hD
  · induction k with
    | zero => show ((1 : Int).toNat : α) = _; rw [Semiring.pow_zero]; exact Semiring.natCast_one
    | succ k ih =>
      show ((p.powTL k).mulTL p).denoteSN f B = _
      rw [denoteSN_mulTL_gen f (D₁ := 0) (D₂ := 0) (Or.inl (PPoly.NonNeg.powTL hp k)) (fun h => absurd h hB),
        ih (by rw [Nat.mul_succ] at hD; omega), Semiring.pow_succ]

-- `Lean.Grind.CommRing.PPoly.denoteSN_eq_of_coeff` (a, 7): the size bound is only the induction measure.
theorem PPoly_denoteSN_eq_of_coeff_h7 : drop% Lean.Grind.CommRing.PPoly.denoteSN_eq_of_coeff 7 := by
  intro α _ f B n p q hp hq h; exact PPoly.denoteSN_eq_of_coeff f B _ p q (Nat.le_refl _) hp hq h

end Removable

section Removable2
open AddCommMonoid AddCommGroup NatModule IntModule
open Semiring hiding add_zero add_comm add_assoc
open Ring hiding sub_eq_add_neg
open CommSemiring

-- `Lean.Grind.CommRing.Expr.toTL_spec` (hB, 5): the library proof, with `1 < B` taken from `he` in the variable case
-- and the generalized `deg_mulTL`, `denoteSN_mulTL_gen`, `deg_powTL`, `PPoly_denoteSN_powTL_h5` elsewhere.
theorem Expr_toTL_spec_h5 : drop% Lean.Grind.CommRing.Expr.toTL_spec 5 := by
  intro α _ ctx X B e hs he
  induction e with
  | num k =>
    cases k with
    | ofNat n =>
      refine ⟨Int.natCast_nonneg n, trivial, ?_, ?_, ?_⟩
      · show ((Int.ofNat n).toNat : α) = OfNat.ofNat (α := α) (Int.ofNat n).natAbs
        rw [Semiring.ofNat_eq_natCast]; rfl
      · show (Int.ofNat n) = denoteInt (Int.ofNat n); rw [denoteInt_eq]; rfl
      · show (Int.ofNat n).natAbs ≤ Int.natAbs_k (Int.ofNat n); rw [Int.natAbs_k_eq]; exact Nat.le_refl _
    | negSucc => cases hs
  | natCast n =>
    refine ⟨Int.natCast_nonneg n, trivial, ?_, rfl, ?_⟩
    · show ((n : Int).toNat : α) = OfNat.ofNat (α := α) n; rw [Semiring.ofNat_eq_natCast]; rfl
    · show (n : Int).natAbs ≤ n; simp
  | intCast => cases hs
  | var x =>
    refine ⟨⟨by decide, show (0 : Int) ≤ 0 by decide⟩, ⟨?_, trivial⟩, ?_, ?_, ?_⟩
    · have hB : 1 < B := he
      have := PPoly.dsum_mul_pow hB x 1 hB; rw [Nat.one_mul] at this; rw [this]; exact Nat.le_refl _
    · show ((1 : Int).toNat : α) * PPoly.monDenote (Var.denote ctx) B 0 (B ^ x) + ((0 : Int).toNat : α) = Var.denote ctx x
      have hB : 1 < B := he
      have hm := PPoly.monDenote_mul_pow (Var.denote ctx) hB 0 x 1 hB
      rw [Nat.one_mul, Nat.zero_add, pow_one] at hm
      rw [hm, show (1 : Int).toNat = 1 from rfl, show (0 : Int).toNat = 0 from rfl, Semiring.natCast_one, one_mul,
        Semiring.natCast_zero, add_zero]
    · show (1 : Int) * X ^ (B ^ x) + 0 = X ^ (B ^ x); omega
    · show (1 : Int).natAbs + (0 : Int).natAbs ≤ 1; simp
  | neg => cases hs
  | sub => cases hs
  | add a b iha ihb =>
    have hs := Expr.semi_k_and hs
    have hm := Expr.le_max_k a.degB_k b.degB_k
    have he' : Bool.rec a.degB_k b.degB_k (Nat.blt a.degB_k b.degB_k) < B := he
    obtain ⟨a₁, a₂, a₃, a₄, a₅⟩ := iha hs.1 (by omega)
    obtain ⟨b₁, b₂, b₃, b₄, b₅⟩ := ihb hs.2 (by omega)
    have hD : (Bool.rec a.degB_k b.degB_k (Nat.blt a.degB_k b.degB_k) : Nat) = (Expr.add a b).degB_k := rfl
    refine ⟨PPoly.NonNeg.append a₁ b₁, PPoly.Deg.append (PPoly.Deg.mono (by rw [← hD]; exact hm.1) _ a₂)
      (PPoly.Deg.mono (by rw [← hD]; exact hm.2) _ b₂), ?_, ?_, ?_⟩
    · show ((a.toTL B).append (b.toTL B)).denoteSN _ B = a.denoteS ctx + b.denoteS ctx
      rw [PPoly.denoteSN_append _ B a₁ b₁, a₃, b₃]
    · show ((a.toTL B).append (b.toTL B)).kron X = a.denoteF _ + b.denoteF _; rw [PPoly.kron_append, a₄, b₄]
    · show ((a.toTL B).append (b.toTL B)).norm1 ≤ Nat.add a.majorant_k b.majorant_k
      have := PPoly.norm1_append (a.toTL B) (b.toTL B); simp only [Nat.add_eq]; omega
  | mul a b iha ihb =>
    have hs := Expr.semi_k_and hs
    have he' : Nat.add a.degB_k b.degB_k < B := he
    obtain ⟨a₁, a₂, a₃, a₄, a₅⟩ := iha hs.1 (by simp at he'; omega)
    obtain ⟨b₁, b₂, b₃, b₄, b₅⟩ := ihb hs.2 (by simp at he'; omega)
    refine ⟨PPoly.NonNeg.mulTL a₁ b₁, deg_mulTL (D₁ := a.degB_k) (D₂ := b.degB_k) a₂ b₂, ?_, ?_, ?_⟩
    · show ((a.toTL B).mulTL (b.toTL B)).denoteSN _ B = a.denoteS ctx * b.denoteS ctx
      rw [denoteSN_mulTL_gen _ (Or.inl a₁) (fun _ => ⟨a₂, b₂, by simp at he'; omega⟩), a₃, b₃]
    · show ((a.toTL B).mulTL (b.toTL B)).kron X = a.denoteF _ * b.denoteF _; rw [PPoly.kron_mulTL, a₄, b₄]
    · show ((a.toTL B).mulTL (b.toTL B)).norm1 ≤ Nat.mul a.majorant_k b.majorant_k
      exact Nat.le_trans (PPoly.norm1_mulTL _ _) (Nat.mul_le_mul a₅ b₅)
  | pow a k ih =>
    have he' : Nat.mul a.degB_k k < B := he
    by_cases hk : k = 0
    · subst hk
      refine ⟨by show (0 : Int) ≤ 1; decide, trivial, ?_, ?_, ?_⟩
      · show ((1 : Int).toNat : α) = a.denoteS ctx ^ 0; rw [pow_zero]; exact Semiring.natCast_one
      · show (1 : Int) = a.denoteF _ ^ 0; rw [pow_zero]
      · show (1 : Int).natAbs ≤ Nat.pow a.majorant_k 0; simp
    have hk' : a.degB_k ≤ a.degB_k * k := Nat.le_mul_of_pos_right _ (by omega)
    obtain ⟨a₁, a₂, a₃, a₄, a₅⟩ := ih hs (by simp at he'; omega)
    refine ⟨PPoly.NonNeg.powTL a₁ k, deg_powTL a₂ k, ?_, ?_, ?_⟩
    · show ((a.toTL B).powTL k).denoteSN _ B = a.denoteS ctx ^ k
      rw [PPoly_denoteSN_powTL_h5 _ a₁ a₂ k (by simp at he'; omega), a₃]
    · show ((a.toTL B).powTL k).kron X = a.denoteF _ ^ k; rw [PPoly.kron_powTL, a₄]
    · show ((a.toTL B).powTL k).norm1 ≤ Nat.pow a.majorant_k k
      exact Nat.le_trans (PPoly.norm1_powTL _ k) (Nat.pow_le_pow_left a₅ k)
theorem sub_nonpos_iff'' {α} [Ring α] [LE α] [Std.IsPreorder α] [OrderedAdd α] {a b : α} : a - b ≤ 0 ↔ a ≤ b := by
  rw [← OrderedAdd.neg_nonneg_iff, AddCommGroup.neg_sub, OrderedAdd.sub_nonneg_iff]

theorem mul_natCast_nonpos {α} [Ring α] [LE α] [Std.IsPreorder α] [OrderedAdd α] {x : α} (hx : x ≤ 0) (n : Nat) :
    x * (n : α) ≤ 0 := by
  induction n with
  | zero => rw [Semiring.natCast_zero, Semiring.mul_zero]; exact Std.le_refl _
  | succ n ih =>
    rw [Semiring.natCast_succ, Semiring.left_distrib, Semiring.mul_one]
    have := OrderedAdd.add_le_left ih x
    rw [AddCommMonoid.zero_add] at this
    exact Std.le_trans this hx

theorem mul_natCast_nonneg {α} [Ring α] [LE α] [Std.IsPreorder α] [OrderedAdd α] {x : α} (hx : 0 ≤ x) (n : Nat) :
    0 ≤ x * (n : α) := by
  induction n with
  | zero => rw [Semiring.natCast_zero, Semiring.mul_zero]; exact Std.le_refl _
  | succ n ih =>
    rw [Semiring.natCast_succ, Semiring.left_distrib, Semiring.mul_one]
    have := OrderedAdd.add_le_left ih x
    rw [AddCommMonoid.zero_add] at this
    exact Std.le_trans hx this

/-- `x * d ≤ 0 ↔ x ≤ 0` for `d ≠ 0`, from `OrderedAdd`, linearity and characteristic `0` (no `<` needed). -/
theorem mul_natCast_nonpos_iff {α} [Field α] [IsCharP α 0] [LE α] [Std.IsLinearOrder α] [OrderedAdd α] {d : Nat}
    (hd : d ≠ 0) (x : α) : x * (d : α) ≤ 0 ↔ x ≤ 0 := by
  refine ⟨fun h => ?_, fun h => mul_natCast_nonpos h d⟩
  rcases Std.le_total (a := x) (b := 0) with hx | hx
  · exact hx
  · have h0 : x * (d : α) = 0 := Std.le_antisymm h (mul_natCast_nonneg hx d)
    rcases Field.of_mul_eq_zero h0 with h1 | h1
    · rw [h1]; exact Std.le_refl _
    · exact absurd h1 (Field.natCast_ne_zero hd)

-- `Lean.Grind.CommRing.le_of_kronQ_rel` (inst, 5): `≤` alone decides `x ≤ 0 ↔ x * d ≤ 0` (`mul_natCast_nonpos_iff`),
-- so `<` and its lawfulness are not used.
theorem le_of_kronQ_rel_h5 : drop% Lean.Grind.CommRing.le_of_kronQ_rel 5 := by
  intro α _ _ _ _ _ _ ctx K B invs hok hnz d hd lhs rhs lhs' rhs' hB hK h
  have h := Expr.sub_mul_eq_of_kronQ ctx K B invs hok hnz d lhs rhs lhs' rhs' hB hK h
  have hd0 : d ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.blt_eq.mp hd)
  rw [← sub_nonpos_iff'' (a := lhs.denote ctx), ← sub_nonpos_iff'' (a := lhs'.denote ctx), ← h]
  exact propext (mul_natCast_nonpos_iff hd0 _).symm

-- `Lean.Grind.CommRing.le_of_kronQLin_rel` (inst, 5): as for `Lean.Grind.CommRing.le_of_kronQ_rel`.
theorem le_of_kronQLin_rel_h5 : drop% Lean.Grind.CommRing.le_of_kronQLin_rel 5 := by
  intro α _ _ _ _ _ _ ctx K invs hok hnz d hd lhs rhs lhs' rhs' hl hK h
  have h := Expr.sub_mul_eq_of_kronQLin ctx K invs hok hnz d lhs rhs lhs' rhs' hl hK h
  have hd0 : d ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.blt_eq.mp hd)
  rw [← sub_nonpos_iff'' (a := lhs.denote ctx), ← sub_nonpos_iff'' (a := lhs'.denote ctx), ← h]
  exact propext (mul_natCast_nonpos_iff hd0 _).symm

end Removable2
end KronBHand
