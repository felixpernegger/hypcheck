import Lean

/-!
Hand pass `KronA` (hand12): the unresolved hypotheses of `Init.Grind.Ring.Kronecker` up to line 2325
(Kronecker substitution: `PPoly` digits, `Expr.eq_of_kron*`, `KList`/`MList` certificates,
`Stepwise.*K*`/`*M*`, `Expr.toPPQ_spec`/`eq_of_kronQ`/`evalQ_spec`).

Reusable models (namespace `KronAHand`):
* `c2 a b`: the context `x₀ = a, x₁ = b`; `px i`: the polynomial `xᵢ`; `sq0`: the expression `x₀ * x₀`.
* Base `B = 1`: every variable evaluates to `2 ^ K` (`Expr.kronEval_k`, `Poly.kron_k`), so `x₀` and
  `x₁` collide (refutes every `degOk_k`/`degSOk_k`/`degQOk_k`/`1 < B ∧ …` check).
* Digit overflow `sq0` vs `x₁`: with `B = 2` (`kronEval_k`) or the linear point `(2 ^ K) ^ (i + 1)`
  (`kronLinEval_k`), `x₀²` and `x₁` have the same value (refutes `linOk_k`, `degSOk_k` degree bounds,
  `KList`/`MList.ok_k`, `degQB_k < B`).
* Small coefficient bound `K = 0`: the point is `1`, so `x₀` and `1` collide (refutes `kronOk_k`-style bounds).
* `arcInt`: `AddRightCancel Int` (for `Int` as a commutative semiring, with negative context values).
* `fieldFin2`: `Field (Fin 2)` with `x⁻¹ = x` (characteristic 2, `2⁻¹ = 0`), for `IsCharP α 0`;
  `Fin 2` (library `CommRing`, `IsCharP (Fin 2) 2`) refutes `NoNatZeroDivisors` (`2 * 1 = 0`).
* Order models on `Int`: `leZ`/`preZ`/`ltZ`/`lawZ` (preorder `a = b ∨ a = 0`, not translation
  invariant: refutes `OrderedRing`), `ltW`/`ordW` (usual `≤`, `<` without the pair `1 < 2`, still an
  `OrderedRing`: refutes `LawfulOrderLT`), `leF`/`ltF`/`lawF` (empty relations: refutes `IsPreorder`).
* `BS`: the Boolean commutative semiring (`1 + 1 = 1`, no `AddRightCancel`), as BS of the Adapter pass.

Removable: `p.size ≤ n` of `PPoly.denote_eq_zero_of_coeff`/`denoteG_eq_zero_of_coeff` (instantiate
`n := p.size`), `1 < B` of `PPoly.kron_combine_k` (`combine_k` does not use `B`), and `1 < B` of
`KList.toPP_spec`, `MList.toPP_spec`, `Expr.toPPQ_spec`: `B = 0` is excluded by the degree check, and
for `B = 1` the degree check forces degree `0`, where all packed codes are `0` and every base gives the
same polynomial; at `B = 1` a packed polynomial denotes the sum of its coefficients (`denote_one`),
and at `B = 2` with degree `0` too (`denote_two_deg0`); `kron_mulB_deg0`, `toPPQ_indep` transport the
library's `B = 2` statement. Conjuncts that don't use `1 < B` are copied from the library proofs.

Left unresolved: `AddRightCancel α` of `Expr.eq_of_kronS`, `Expr.eq_of_kronLinS` and their
`eq_true`/`le_true`/`lt_false`/`le_cancel`/`lt_cancel` variants (10): very likely removable (two
semiring expressions with the same integer polynomial are equal in every commutative semiring, since
the polynomial semiring over `Nat` is free), but a proof needs a semiring normal form.

Run with the lean4 repo's stage1 binary: `lean checks/KronAHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open Lean Meta Elab Term in
def HandDrop.dropType (T : Ident) (i : Nat) (us? : Option (List Level)) : TermElabM Expr := do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← match us? with
    | some us => pure us
    | none => ci.levelParams.mapM fun _ => mkFreshLevelMVar
  unless us.length == ci.levelParams.length do
    throwError "{n} has {ci.levelParams.length} universe parameters"
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i]!
    unless ← isProp (← inferType x) do throwError "binder {i} of {n} is not a Prop"
    for j in [i+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i) body
open Lean Elab Term in
elab "drop0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  HandDrop.dropType T i.getNat (some (ci.levelParams.map fun _ => Lean.Level.zero))
elab "drop% " T:ident i:num : term => HandDrop.dropType T i.getNat none

open Lean Meta Elab Term in
def HandDrop.indepType (T : Ident) (i : Nat) (zero : Bool) : TermElabM Expr := do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← if zero then pure (ci.levelParams.map fun _ => levelZero) else ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i]!
    unless ← isProp (← inferType x) do throwError "binder {i} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)
elab "indep0% " T:ident i:num : term => HandDrop.indepType T i.getNat true
elab "indep% " T:ident i:num : term => HandDrop.indepType T i.getNat false

open Lean.Grind CommRing
attribute [local instance] Semiring.natCast Ring.intCast

namespace KronAHand

/-- Two-variable contexts. -/
abbrev c2 {α} (a b : α) : Context α := .branch 1 (.leaf a) (.leaf b)
/-- The polynomial `x_i`. -/
abbrev px (i : Nat) : Poly := .add 1 (.mult ⟨i, 1⟩ .unit) (.num 0)
abbrev sq0 : Expr := .mul (.var 0) (.var 0)
abbrev k1 : KList := .cons 1 .unit (.num 1) .nil
abbrev m1 : MList := .cons (.num 1) (.num 1) .nil
instance arcInt : AddRightCancel Int := ⟨fun a b c h => by have h : a + c = b + c := h; omega⟩

/-- `Fin 2` as a field with `x⁻¹ = x` (so `2⁻¹ = 0⁻¹ = 0`); characteristic `2`. -/
instance fieldFin2 : Field (Fin 2) :=
  { (inferInstance : CommRing (Fin 2)) with
    inv := id, div := (· * ·), zpow := ⟨fun a n => a ^ n.natAbs⟩, div_eq_mul_inv := (by decide),
    zero_ne_one := (by decide), inv_zero := (by decide), mul_inv_cancel := (by decide),
    zpow_zero := fun a => Semiring.pow_zero a, zpow_succ := fun a n => Semiring.pow_succ a n,
    zpow_neg := (by intro a n; show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]) }

theorem lookup_single {x c x₀ c₀ : Nat} (h : InvVars.lookup_k [(x₀, c₀)] x = some c) : c = c₀ := by
  revert h
  show Bool.rec (Bool.rec none (some c₀) (Nat.beq x₀ x)) none (Nat.blt x x₀) = some c → c = c₀
  cases Nat.blt x x₀ <;> cases Nat.beq x₀ x <;> simp <;> exact Eq.symm

set_option warn.classDefReducibility false
set_option linter.defProp false

/-- A preorder on `Int` that is not translation invariant: `a ≤ b` iff `a = b ∨ a = 0`. -/
def leZ : LE Int := ⟨fun a b => a = b ∨ a = 0⟩
def preZ : @Std.IsPreorder Int leZ :=
  @Std.IsPreorder.mk Int leZ (fun a => Or.inl rfl) (fun a b c h₁ h₂ => by
    change a = b ∨ a = 0 at h₁; change b = c ∨ b = 0 at h₂; change a = c ∨ a = 0; omega)
/-- Its strict order. -/
def ltZ : LT Int := ⟨fun a b => (a = b ∨ a = 0) ∧ ¬ (b = a ∨ b = 0)⟩
theorem lawZ : @Std.LawfulOrderLT Int ltZ leZ := @Std.LawfulOrderLT.mk Int ltZ leZ (fun _ _ => Iff.rfl)

/-- The usual `≤` on `Int` with a strict order that drops the pair `1 < 2`; still an `OrderedRing`. -/
def ltW : LT Int := ⟨fun a b => a ≤ b ∧ ¬ (a = 1 ∧ b = 2)⟩
def ordW : @OrderedRing Int _ _ ltW _ :=
  @OrderedRing.mk Int _ _ ltW _ ⟨fun {a b} c => by show a ≤ b ↔ a + c ≤ b + c; omega⟩
    (by show (0:Int) ≤ 1 ∧ ¬ ((0:Int) = 1 ∧ (1:Int) = 2); decide)
    (fun {a b c} h hc => by
      change a ≤ b ∧ ¬ (a = 1 ∧ b = 2) at h; change 0 ≤ c ∧ ¬ (0 = 1 ∧ c = 2) at hc
      change c * a ≤ c * b ∧ ¬ (c * a = 1 ∧ c * b = 2)
      refine ⟨Int.mul_le_mul_of_nonneg_left h.1 hc.1, fun ⟨h1, h2⟩ => ?_⟩
      have := Int.eq_one_of_mul_eq_one_right hc.1 h1; subst this; omega)
    (fun {a b c} h hc => by
      change a ≤ b ∧ ¬ (a = 1 ∧ b = 2) at h; change 0 ≤ c ∧ ¬ (0 = 1 ∧ c = 2) at hc
      change a * c ≤ b * c ∧ ¬ (a * c = 1 ∧ b * c = 2)
      refine ⟨Int.mul_le_mul_of_nonneg_right h.1 hc.1, fun ⟨h1, h2⟩ => ?_⟩
      have := Int.eq_one_of_mul_eq_one_left hc.1 h1; subst this; omega)

/-- `False` as `≤` and `<`: lawful, not reflexive. -/
def leF : LE Int := ⟨fun _ _ => False⟩
def ltF : LT Int := ⟨fun _ _ => False⟩
theorem lawF : @Std.LawfulOrderLT Int ltF leF :=
  @Std.LawfulOrderLT.mk Int ltF leF (fun _ _ => ⟨False.elim, fun h => h.1⟩)

/-- The Boolean semiring (`||`, `&&`) on a copy of `Bool` (as BS of the Adapter pass, made commutative):
`1 + 1 = 1`, so no `AddRightCancel`. -/
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

-- `Lean.Grind.CommRing.PPoly.denote_eq_zero_of_coeff`
theorem PPoly.denote_eq_zero_of_coeff.h6 : drop% Lean.Grind.CommRing.PPoly.denote_eq_zero_of_coeff 6 := by
  intro α _ f B n p h
  exact PPoly.denote_eq_zero_of_coeff f B p.size p (Nat.le_refl _) h

-- `Lean.Grind.CommRing.PPoly.denote_eq_of_kron`
theorem PPoly.denote_eq_of_kron.h9 : ¬ drop0% Lean.Grind.CommRing.PPoly.denote_eq_of_kron 9 := fun h => by
  have := h (α := Int) (fun _ => 5) 2 2 (by decide) (.num 2) (.add 1 1 1 (.num 0)) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.denoteG_eq_zero_of_coeff`
theorem PPoly.denoteG_eq_zero_of_coeff.h6 : drop% Lean.Grind.CommRing.PPoly.denoteG_eq_zero_of_coeff 6 := by
  intro α _ g hg n p h
  exact PPoly.denoteG_eq_zero_of_coeff g hg p.size p (Nat.le_refl _) h

-- `Lean.Grind.CommRing.PPoly.denoteG_eq_zero_of_coeff`
theorem PPoly.denoteG_eq_zero_of_coeff.h3 : ¬ drop0% Lean.Grind.CommRing.PPoly.denoteG_eq_zero_of_coeff 3 := fun h => by
  have := h (α := Int) (fun _ => 0) 1 (.add 1 0 0 (.num (-1))) (by decide)
    (by intro c; rcases c with _ | c <;> simp [PPoly.coeff])
  revert this; decide +kernel

-- `Lean.Grind.CommRing.PPoly.kron_combine_k`
theorem PPoly.kron_combine_k.h2 : drop% Lean.Grind.CommRing.PPoly.kron_combine_k 2 := by
  intro X B p q
  exact PPoly.kron_combine_k X (B := 2) (by decide) p q

-- `Lean.Grind.CommRing.KList.toPP_spec`
theorem KList.toPP_spec.h7 : ¬ drop0% Lean.Grind.CommRing.KList.toPP_spec 7 := fun h => by
  have := (h (α := Int) (c2 0 1) 3 2 (by decide) (.cons 1 (.mult ⟨0, 1⟩ .unit) (px 0) .nil)).2.2
    (KList.allZero_cons _ _ _ _ _ (by decide +kernel) (KList.allZero_nil _))
  revert this; decide +kernel

-- `Lean.Grind.CommRing.MList.toPP_spec`
theorem MList.toPP_spec.h7 : ¬ drop0% Lean.Grind.CommRing.MList.toPP_spec 7 := fun h => by
  have := (h (α := Int) (c2 0 1) 3 2 (by decide) (.cons (px 0) (px 0) .nil)).2.2
    (MList.allZero_cons _ _ _ _ (by decide +kernel) (MList.allZero_nil _))
  revert this; decide +kernel

-- `Lean.Grind.CommRing.KList.denote_eq`
theorem KList.denote_eq.h10 : ¬ drop0% Lean.Grind.CommRing.KList.denote_eq 10 := fun h => by
  have := h (α := Int) (c2 0 1) 3 1 0 (px 1) (px 0) (.num 0) .nil (by decide +kernel) (by decide +kernel) trivial
  revert this; decide +kernel

-- `Lean.Grind.CommRing.KList.denote_eq`
theorem KList.denote_eq.h11 : ¬ drop0% Lean.Grind.CommRing.KList.denote_eq 11 := fun h => by
  have := h (α := Int) (c2 0 1) 0 2 0 (px 0) (.num 1) (.num 0) .nil (by decide +kernel) (by decide +kernel) trivial
  revert this; decide +kernel

-- `Lean.Grind.CommRing.KList.denote_eq`
theorem KList.denote_eq.h13 : ¬ drop0% Lean.Grind.CommRing.KList.denote_eq 13 := fun h => by
  have := h (α := Int) (c2 0 1) 3 2 0 (.num 0) (.num 1) (.num 0) (.cons 1 .unit (.num 1) .nil)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.MList.denote_eq`
theorem MList.denote_eq.h10 : ¬ drop0% Lean.Grind.CommRing.MList.denote_eq 10 := fun h => by
  have := h (α := Int) (c2 0 1) 3 1 0 (px 1) (px 0) (.num 0) .nil (by decide +kernel) (by decide +kernel) trivial
  revert this; decide +kernel

-- `Lean.Grind.CommRing.MList.denote_eq`
theorem MList.denote_eq.h11 : ¬ drop0% Lean.Grind.CommRing.MList.denote_eq 11 := fun h => by
  have := h (α := Int) (c2 0 1) 0 2 0 (px 0) (.num 1) (.num 0) .nil (by decide +kernel) (by decide +kernel) trivial
  revert this; decide +kernel

-- `Lean.Grind.CommRing.MList.denote_eq`
theorem MList.denote_eq.h13 : ¬ drop0% Lean.Grind.CommRing.MList.denote_eq 13 := fun h => by
  have := h (α := Int) (c2 0 1) 3 2 0 (.num 0) (.num 1) (.num 0) (.cons (.num 1) (.num 1) .nil)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.denote_eq_of_kron_poly`
theorem Expr.denote_eq_of_kron_poly.h9 : ¬ drop0% Lean.Grind.CommRing.Expr.denote_eq_of_kron_poly 9 := fun h => by
  have := h (α := Int) (c2 0 1) 3 1 0 (.var 0) (px 1) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.denote_eq_of_kron_poly`
theorem Expr.denote_eq_of_kron_poly.h10 : ¬ drop0% Lean.Grind.CommRing.Expr.denote_eq_of_kron_poly 10 := fun h => by
  have := h (α := Int) (c2 0 1) 0 2 0 (.var 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_kron`
theorem Expr.eq_of_kron.h7 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_kron 7 := fun h => by
  have := h (α := Int) (c2 0 1) 3 1 (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_true_of_kron`
theorem eq_true_of_kron.h7 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kron 7 := fun h => by
  have := h (α := Int) (c2 0 1) 3 1 (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  exact absurd (of_eq_true this) (by decide +kernel)

-- `Lean.Grind.CommRing.le_true_of_kron`
theorem le_true_of_kron.h9 : ¬ drop0% Lean.Grind.CommRing.le_true_of_kron 9 := fun h => by
  have := h (α := Int) (c2 1 0) 3 1 (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  exact absurd (of_eq_true this) (by decide +kernel)

-- `Lean.Grind.CommRing.lt_false_of_kron`
theorem lt_false_of_kron.h11 : ¬ drop0% Lean.Grind.CommRing.lt_false_of_kron 11 := fun h => by
  have := h (α := Int) (c2 0 1) 3 1 (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  exact of_eq_false this (by decide +kernel)

-- `Lean.Grind.CommRing.Expr.sub_eq_of_kron`
theorem Expr.sub_eq_of_kron.h8 : ¬ drop0% Lean.Grind.CommRing.Expr.sub_eq_of_kron 8 := fun h => by
  have := h (α := Int) (c2 0 1) 3 1 (.var 0) (.var 1) 0 (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_kronS`
theorem Expr.eq_of_kronS.h8 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_kronS 8 := fun h => by
  have := h (α := Int) (c2 0 1) 3 1 (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_true_of_kronS`
theorem eq_true_of_kronS.h8 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kronS 8 := fun h => by
  have := h (α := Int) (c2 0 1) 3 1 (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  exact absurd (of_eq_true this) (by decide +kernel)

-- `Lean.Grind.CommRing.le_true_of_kronS`
theorem le_true_of_kronS.h10 : ¬ drop0% Lean.Grind.CommRing.le_true_of_kronS 10 := fun h => by
  have := h (α := Int) (c2 1 0) 3 1 (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  exact absurd (of_eq_true this) (by decide +kernel)

-- `Lean.Grind.CommRing.lt_false_of_kronS`
theorem lt_false_of_kronS.h12 : ¬ drop0% Lean.Grind.CommRing.lt_false_of_kronS 12 := fun h => by
  have := h (α := Int) (c2 0 1) 3 1 (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  exact of_eq_false this (by decide +kernel)

-- `Lean.Grind.CommRing.Expr.eq_of_kronLin`
theorem Expr.eq_of_kronLin.h6 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_kronLin 6 := fun h => by
  have := h (α := Int) (c2 0 1) 3 sq0 (.var 1) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_true_of_kronLin`
theorem eq_true_of_kronLin.h6 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kronLin 6 := fun h => by
  have := h (α := Int) (c2 0 1) 3 sq0 (.var 1) (by decide +kernel) (by decide +kernel)
  exact absurd (of_eq_true this) (by decide +kernel)

-- `Lean.Grind.CommRing.le_true_of_kronLin`
theorem le_true_of_kronLin.h8 : ¬ drop0% Lean.Grind.CommRing.le_true_of_kronLin 8 := fun h => by
  have := h (α := Int) (c2 2 0) 3 sq0 (.var 1) (by decide +kernel) (by decide +kernel)
  exact absurd (of_eq_true this) (by decide +kernel)

-- `Lean.Grind.CommRing.lt_false_of_kronLin`
theorem lt_false_of_kronLin.h10 : ¬ drop0% Lean.Grind.CommRing.lt_false_of_kronLin 10 := fun h => by
  have := h (α := Int) (c2 0 1) 3 sq0 (.var 1) (by decide +kernel) (by decide +kernel)
  exact of_eq_false this (by decide +kernel)

-- `Lean.Grind.CommRing.Expr.sub_eq_of_kronLin`
theorem Expr.sub_eq_of_kronLin.h7 : ¬ drop0% Lean.Grind.CommRing.Expr.sub_eq_of_kronLin 7 := fun h => by
  have := h (α := Int) (c2 0 1) 3 sq0 (.var 1) 0 (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_kronLinS`
theorem Expr.eq_of_kronLinS.h7 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_kronLinS 7 := fun h => by
  have := h (α := Int) (c2 0 1) 3 sq0 (.var 1) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_true_of_kronLinS`
theorem eq_true_of_kronLinS.h7 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kronLinS 7 := fun h => by
  have := h (α := Int) (c2 0 1) 3 sq0 (.var 1) (by decide +kernel) (by decide +kernel)
  exact absurd (of_eq_true this) (by decide +kernel)

-- `Lean.Grind.CommRing.le_true_of_kronLinS`
theorem le_true_of_kronLinS.h9 : ¬ drop0% Lean.Grind.CommRing.le_true_of_kronLinS 9 := fun h => by
  have := h (α := Int) (c2 2 0) 3 sq0 (.var 1) (by decide +kernel) (by decide +kernel)
  exact absurd (of_eq_true this) (by decide +kernel)

-- `Lean.Grind.CommRing.lt_false_of_kronLinS`
theorem lt_false_of_kronLinS.h11 : ¬ drop0% Lean.Grind.CommRing.lt_false_of_kronLinS 11 := fun h => by
  have := h (α := Int) (c2 0 1) 3 sq0 (.var 1) (by decide +kernel) (by decide +kernel)
  exact of_eq_false this (by decide +kernel)

/-! Cancellation lemmas (semiring `Int`). -/

-- `Lean.Grind.CommRing.eq_cancel_of_kronS`
theorem eq_cancel_of_kronS.h11 : ¬ drop0% Lean.Grind.CommRing.eq_cancel_of_kronS 11 := fun h => by
  have := h (α := Int) (c2 1 0) 3 2 sq0 (.num 0) (.var 1) (.num 0) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.eq_cancel_of_kronS`
theorem eq_cancel_of_kronS.h12 : ¬ drop0% Lean.Grind.CommRing.eq_cancel_of_kronS 12 := fun h => by
  have := h (α := Int) (c2 0 0) 0 2 (.var 0) (.num 0) (.num 1) (.num 0) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.eq_cancel_of_kronS`
theorem eq_cancel_of_kronS.h14 : ¬ drop0% Lean.Grind.CommRing.eq_cancel_of_kronS 14 := fun h => by
  have := h (α := Int) (c2 1 0) 3 2 (.num 0) sq0 (.num 0) (.var 1) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.eq_cancel_of_kronS`
theorem eq_cancel_of_kronS.h15 : ¬ drop0% Lean.Grind.CommRing.eq_cancel_of_kronS 15 := fun h => by
  have := h (α := Int) (c2 0 0) 0 2 (.num 0) (.var 0) (.num 0) (.num 1) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.le_cancel_of_kronS`
theorem le_cancel_of_kronS.h15 : ¬ drop0% Lean.Grind.CommRing.le_cancel_of_kronS 15 := fun h => by
  have := h (α := Int) (c2 1 0) 3 2 sq0 (.num 0) (.var 1) (.num 0) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.le_cancel_of_kronS`
theorem le_cancel_of_kronS.h16 : ¬ drop0% Lean.Grind.CommRing.le_cancel_of_kronS 16 := fun h => by
  have := h (α := Int) (c2 0 0) 0 2 (.var 0) (.num 0) (.num 1) (.num 0) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.le_cancel_of_kronS`
theorem le_cancel_of_kronS.h17 : ¬ drop0% Lean.Grind.CommRing.le_cancel_of_kronS 17 := fun h => by
  have := h (α := Int) (c2 0 0) 3 2 (.num 1) (.num 0) (.num 0) (.num 0) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.le_cancel_of_kronS`
theorem le_cancel_of_kronS.h18 : ¬ drop0% Lean.Grind.CommRing.le_cancel_of_kronS 18 := fun h => by
  have := h (α := Int) (c2 0 (-1)) 3 2 (.num 0) sq0 (.num 0) (.var 1) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.le_cancel_of_kronS`
theorem le_cancel_of_kronS.h19 : ¬ drop0% Lean.Grind.CommRing.le_cancel_of_kronS 19 := fun h => by
  have := h (α := Int) (c2 (-1) 0) 0 2 (.num 0) (.var 0) (.num 0) (.num 1) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.le_cancel_of_kronS`
theorem le_cancel_of_kronS.h20 : ¬ drop0% Lean.Grind.CommRing.le_cancel_of_kronS 20 := fun h => by
  have := h (α := Int) (c2 0 0) 3 2 (.num 1) (.num 1) (.num 1) (.num 0) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.lt_cancel_of_kronS`
theorem lt_cancel_of_kronS.h16 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronS 16 := fun h => by
  have := h (α := Int) (c2 0 (-1)) 3 2 sq0 (.num 0) (.var 1) (.num 0) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.lt_cancel_of_kronS`
theorem lt_cancel_of_kronS.h17 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronS 17 := fun h => by
  have := h (α := Int) (c2 (-1) 0) 0 2 (.var 0) (.num 0) (.num 1) (.num 0) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.lt_cancel_of_kronS`
theorem lt_cancel_of_kronS.h18 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronS 18 := fun h => by
  have := h (α := Int) (c2 0 0) 3 2 (.num 1) (.num 1) (.num 0) (.num 1) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.lt_cancel_of_kronS`
theorem lt_cancel_of_kronS.h19 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronS 19 := fun h => by
  have := h (α := Int) (c2 0 1) 3 2 (.num 0) sq0 (.num 0) (.var 1) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.lt_cancel_of_kronS`
theorem lt_cancel_of_kronS.h20 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronS 20 := fun h => by
  have := h (α := Int) (c2 0 0) 0 2 (.num 0) (.var 0) (.num 0) (.num 1) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.lt_cancel_of_kronS`
theorem lt_cancel_of_kronS.h21 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronS 21 := fun h => by
  have := h (α := Int) (c2 0 0) 3 2 (.num 0) (.num 1) (.num 0) (.num 0) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.Stepwise.simpsK`
theorem Stepwise.simpsK.h10 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsK 10 := fun h => by
  have := h (α := Int) (c2 0 0) 3 2 (.num 0) (.num 1) k1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.simpsK`
theorem Stepwise.simpsK.h11 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsK 11 := fun h => by
  have := h (α := Int) (c2 0 0) 3 2 (.num 1) (.num 1) .nil (by decide +kernel) (by decide +kernel) trivial
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.simpsKC`
theorem Stepwise.simpsKC.h3 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsKC 3 := fun h => by
  have := h (α := Int) (c := 1) (c2 0 0) 3 2 (.num 0) (.num 1) (.num 1) .nil (by decide +kernel) (by decide +kernel)
    trivial (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.simpsKC`
theorem Stepwise.simpsKC.h13 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsKC 13 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 3 2 (.num 0) (.num 1) (.num 0) k1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.simpsKC`
theorem Stepwise.simpsKC.h14 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsKC 14 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 3 2 (.num 1) (.num 1) (.num 0) .nil (by decide +kernel) (by decide +kernel) trivial
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.d_stepsK`
theorem Stepwise.d_stepsK.h12 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsK 12 := fun h => by
  have := h (α := Int) (c2 0 0) 0 (.num 0) 3 2 (.num 0) (.num 1) k1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.d_stepsKC`
theorem Stepwise.d_stepsKC.h3 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsKC 3 := fun h => by
  have := h (α := Int) (c := 1) (c2 0 0) 0 (.num 0) 3 2 (.num 0) (.num 1) (.num 1) .nil (by decide +kernel)
    (by decide +kernel) trivial (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.d_stepsKC`
theorem Stepwise.d_stepsKC.h14 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsKC 14 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 0 (.num 0) 3 2 (.num 0) (.num 1) (.num 0) .nil (by decide +kernel)
    trivial (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.d_stepsKC`
theorem Stepwise.d_stepsKC.h15 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsKC 15 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 0 (.num 0) 3 2 (.num 0) (.num 1) (.num 0) k1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.simpsM`
theorem Stepwise.simpsM.h10 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsM 10 := fun h => by
  have := h (α := Int) (c2 0 0) 3 2 (.num 0) (.num 1) m1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.simpsM`
theorem Stepwise.simpsM.h11 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsM 11 := fun h => by
  have := h (α := Int) (c2 0 0) 3 2 (.num 1) (.num 1) .nil (by decide +kernel) (by decide +kernel) trivial
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.simpsMC`
theorem Stepwise.simpsMC.h3 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsMC 3 := fun h => by
  have := h (α := Int) (c := 1) (c2 0 0) 3 2 (.num 0) (.num 1) (.num 1) .nil (by decide +kernel) (by decide +kernel)
    trivial (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.simpsMC`
theorem Stepwise.simpsMC.h13 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsMC 13 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 3 2 (.num 0) (.num 1) (.num 0) m1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.simpsMC`
theorem Stepwise.simpsMC.h14 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsMC 14 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 3 2 (.num 1) (.num 1) (.num 0) .nil (by decide +kernel) (by decide +kernel) trivial
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.d_stepsM`
theorem Stepwise.d_stepsM.h12 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsM 12 := fun h => by
  have := h (α := Int) (c2 0 0) 0 (.num 0) 3 2 (.num 0) (.num 1) m1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.d_stepsMC`
theorem Stepwise.d_stepsMC.h3 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsMC 3 := fun h => by
  have := h (α := Int) (c := 1) (c2 0 0) 0 (.num 0) 3 2 (.num 0) (.num 1) (.num 1) .nil (by decide +kernel)
    (by decide +kernel) trivial (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.d_stepsMC`
theorem Stepwise.d_stepsMC.h14 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsMC 14 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 0 (.num 0) 3 2 (.num 0) (.num 1) (.num 0) .nil (by decide +kernel)
    trivial (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.d_stepsMC`
theorem Stepwise.d_stepsMC.h15 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsMC 15 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 0 (.num 0) 3 2 (.num 0) (.num 1) (.num 0) m1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

/-! Implications (`lhs - rhs` checked against `p₁`). -/

-- `Lean.Grind.CommRing.Stepwise.imp_1eqK`
theorem Stepwise.imp_1eqK.h11 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_1eqK 11 := fun h => by
  have := h (α := Int) (c2 0 0) 3 2 (.num 1) (.num 0) (.num 1) (.num 1) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_1eqK`
theorem Stepwise.imp_1eqK.h12 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_1eqK 12 := fun h => by
  have := h (α := Int) (c2 0 0) 3 2 (.num 1) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel) rfl
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_1eqKC`
theorem Stepwise.imp_1eqKC.h3 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_1eqKC 3 := fun h => by
  have := h (α := Int) (c := 1) (c2 0 0) 3 2 (.num 1) (.num 0) (.num 0) (.num 0) (.num 1) (by decide +kernel)
    (by decide +kernel) rfl (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_1eqKC`
theorem Stepwise.imp_1eqKC.h14 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_1eqKC 14 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 3 2 (.num 1) (.num 0) (.num 1) (.num 1) (.num 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_1eqKC`
theorem Stepwise.imp_1eqKC.h15 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_1eqKC 15 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 3 2 (.num 1) (.num 0) (.num 1) (.num 0) (.num 0) (by decide +kernel)
    (by decide +kernel) rfl
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.coreK`
theorem Stepwise.coreK.h10 : ¬ drop0% Lean.Grind.CommRing.Stepwise.coreK 10 := fun h => by
  have := h (α := Int) (c2 0 0) 3 2 (.num 1) (.num 0) (.num 1) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.coreKC`
theorem Stepwise.coreKC.h3 : ¬ drop0% Lean.Grind.CommRing.Stepwise.coreKC 3 := fun h => by
  have := h (α := Int) (c := 1) (c2 0 0) 3 2 (.num 0) (.num 0) (.num (-1)) (.num 1) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.coreKC`
theorem Stepwise.coreKC.h13 : ¬ drop0% Lean.Grind.CommRing.Stepwise.coreKC 13 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 3 2 (.num 1) (.num 0) (.num 1) (.num 0) (by decide +kernel)
    (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_keqK`
theorem Stepwise.imp_keqK.h3 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_keqK 3 := fun h => by
  have := h (α := Fin 2) (c2 0 0) 2 3 2 (.num 1) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_keqK`
theorem Stepwise.imp_keqK.h11 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_keqK 11 := fun h => by
  have := h (α := Int) (c2 0 0) 0 3 2 (.num 1) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_keqK`
theorem Stepwise.imp_keqK.h13 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_keqK 13 := fun h => by
  have := h (α := Int) (c2 0 0) 1 3 2 (.num 1) (.num 0) (.num 0) (.num 0) (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_keqK`
theorem Stepwise.imp_keqK.h14 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_keqK 14 := fun h => by
  have := h (α := Int) (c2 0 0) 1 3 2 (.num 1) (.num 0) (.num 1) (.num 1) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_keqK`
theorem Stepwise.imp_keqK.h15 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_keqK 15 := fun h => by
  have := h (α := Int) (c2 0 0) 1 3 2 (.num 1) (.num 0) (.num 1) (.num 0) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_keqKC`
theorem Stepwise.imp_keqKC.h3 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_keqKC 3 := fun h => by
  have := h (α := Int) (c := 1) (c2 0 0) 1 3 2 (.num 1) (.num 0) (.num 0) (.num 0) (.num 1) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_keqKC`
theorem Stepwise.imp_keqKC.h5 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_keqKC 5 := fun h => by
  have := h (α := Fin 2) (c := 2) (c2 0 0) 2 3 2 (.num 1) (.num 0) (.num 1) (.num 0) (.num 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_keqKC`
theorem Stepwise.imp_keqKC.h14 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_keqKC 14 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 0 3 2 (.num 1) (.num 0) (.num 1) (.num 0) (.num 0) (by decide +kernel)
    (by decide +kernel) rfl (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_keqKC`
theorem Stepwise.imp_keqKC.h15 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_keqKC 15 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 1) 1 3 1 (.var 0) (.var 1) (.num 0) (.num 0) (.num 0) (by decide +kernel)
    (by decide +kernel) rfl (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_keqKC`
theorem Stepwise.imp_keqKC.h16 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_keqKC 16 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 1 3 2 (.num 1) (.num 0) (.num 0) (.num 0) (.num 0) (by decide +kernel)
    (by decide +kernel) rfl (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_keqKC`
theorem Stepwise.imp_keqKC.h17 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_keqKC 17 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 1 3 2 (.num 1) (.num 0) (.num 1) (.num 1) (.num 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.imp_keqKC`
theorem Stepwise.imp_keqKC.h18 : ¬ drop0% Lean.Grind.CommRing.Stepwise.imp_keqKC 18 := fun h => by
  have := h (α := Int) (c := 0) (c2 0 0) 1 3 2 (.num 1) (.num 0) (.num 1) (.num 0) (.num 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.evalQ_spec`
theorem Expr.evalQ_spec.h2 : ¬ drop0% Lean.Grind.CommRing.Expr.evalQ_spec 2 := fun h => by
  have := (h (α := Fin 2) (fun _ => 0) [(0, 2)]
    (fun x c hx => by cases lookup_single hx; exact ⟨by decide, by decide⟩) (.var 0) (by decide +kernel)).1
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.evalQ_spec`
theorem Expr.evalQ_spec.h7 : ¬ drop0% Lean.Grind.CommRing.Expr.evalQ_spec 7 := fun h => by
  have := (h (α := Rat) (fun _ => 1) [] (fun x c hx => nomatch hx) (.var 0)).1
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.toPPQ_spec`
theorem Expr.toPPQ_spec.h2 : ¬ drop0% Lean.Grind.CommRing.Expr.toPPQ_spec 2 := fun h => by
  have := (h (α := Fin 2) (fun _ => 0) 0 2 (by decide) [(0, 2)]
    (fun x c hx => by cases lookup_single hx; exact ⟨by decide, by decide⟩) (.var 0) (by decide +kernel)).1
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.toPPQ_spec`
theorem Expr.toPPQ_spec.h10 : ¬ drop0% Lean.Grind.CommRing.Expr.toPPQ_spec 10 := fun h => by
  have := (h (α := Rat) (fun i => (i : Rat) + 2) 0 2 (by decide) [] (fun x c hx => nomatch hx) sq0).1
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_kronQ`
theorem Expr.eq_of_kronQ.h2 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_kronQ 2 := fun h => by
  have := h (α := Fin 2) (.leaf 0) 5 2 [(0, 2)] ((InvVars.ok_cons _ _ _ _).2 ⟨by decide +kernel, rfl⟩)
    (by decide +kernel) (.var 0) (.sub (.num 1) (.var 0)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_kronQ`
theorem Expr.eq_of_kronQ.h7 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_kronQ 7 := fun h => by
  have := h (α := Rat) (.leaf 0) 3 2 [(0, 1)] (by decide +kernel) (.var 0) (.num 1) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_kronQ`
theorem Expr.eq_of_kronQ.h8 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_kronQ 8 := fun h => by
  have := h (α := Rat) (.leaf 0) 0 2 [(0, 0)] ((InvVars.ok_cons _ _ _ _).2 ⟨by decide +kernel, rfl⟩)
    (.var 0) (.add (.var 0) (.num 1)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Expr.eq_of_kronQ`
theorem Expr.eq_of_kronQ.h11 : ¬ drop0% Lean.Grind.CommRing.Expr.eq_of_kronQ 11 := fun h => by
  have := h (α := Rat) (c2 0 1) 3 1 [] rfl (by decide +kernel) (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.eq_cancel_of_kronS`
theorem eq_cancel_of_kronS.h2 : ¬ drop0% Lean.Grind.CommRing.eq_cancel_of_kronS 2 := fun h => by
  have := h (α := BS) (.leaf false) 4 2 (.num 1) (.num 2) (.num 0) (.num 1) (.num 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by decide +kernel)

-- `Lean.Grind.CommRing.le_cancel_of_kronS`
theorem le_cancel_of_kronS.h6 : ¬ drop0% Lean.Grind.CommRing.le_cancel_of_kronS 6 := fun h => by
  have := @h Int _ _ leZ ltZ preZ (c2 0 0) 4 2 (.num 1) (.num 2) (.num 0) (.num 1) (.num 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this)
    (by show ¬ (((1:Int) = 2 ∨ (1:Int) = 0) ↔ ((0:Int) = 1 ∨ (0:Int) = 0)); decide)

-- `Lean.Grind.CommRing.lt_cancel_of_kronS`
theorem lt_cancel_of_kronS.h7 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronS 7 := fun h => by
  have := @h Int _ _ leZ ltZ lawZ preZ (c2 0 0) 4 2 (.num 1) (.num 2) (.num 0) (.num 1) (.num 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by
    show ¬ ((((1:Int) = 2 ∨ (1:Int) = 0) ∧ ¬ ((2:Int) = 1 ∨ (2:Int) = 0)) ↔
      (((0:Int) = 1 ∨ (0:Int) = 0) ∧ ¬ ((1:Int) = 0 ∨ (1:Int) = 0))); decide)

-- `Lean.Grind.CommRing.lt_cancel_of_kronS`
theorem lt_cancel_of_kronS.h5 : ¬ drop0% Lean.Grind.CommRing.lt_cancel_of_kronS 5 := fun h => by
  have := @h Int _ _ _ ltW _ ordW (c2 0 0) 4 2 (.num 1) (.num 2) (.num 0) (.num 1) (.num 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (Iff.of_eq this) (by
    show ¬ (((1:Int) ≤ 2 ∧ ¬ ((1:Int) = 1 ∧ (2:Int) = 2)) ↔ ((0:Int) ≤ 1 ∧ ¬ ((0:Int) = 1 ∧ (1:Int) = 2))); decide)

-- `Lean.Grind.CommRing.lt_cancel_of_kronS`
theorem lt_cancel_of_kronS.h6 : ¬ indep0% Lean.Grind.CommRing.lt_cancel_of_kronS 6 := fun h =>
  (@h Int _ _ leF ltF lawF (c2 0 0) 0 2 (.num 0) (.num 0) (.num 0) (.num 0) (.num 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).le_refl 0

-- `Lean.Grind.CommRing.eq_true_of_kronQ`
theorem eq_true_of_kronQ.h2 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kronQ 2 := fun h => by
  have := h (α := Fin 2) (.leaf 0) 5 2 [(0, 2)] ((InvVars.ok_cons _ _ _ _).2 ⟨by decide +kernel, rfl⟩)
    (by decide +kernel) (.var 0) (.sub (.num 1) (.var 0)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (of_eq_true this) (by decide +kernel)

-- `Lean.Grind.CommRing.eq_true_of_kronQ`
theorem eq_true_of_kronQ.h7 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kronQ 7 := fun h => by
  have := h (α := Rat) (.leaf 0) 3 2 [(0, 1)] (by decide +kernel) (.var 0) (.num 1) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  exact absurd (of_eq_true this) (by decide +kernel)

-- `Lean.Grind.CommRing.eq_true_of_kronQ`
theorem eq_true_of_kronQ.h8 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kronQ 8 := fun h => by
  have := h (α := Rat) (.leaf 0) 0 2 [(0, 0)] ((InvVars.ok_cons _ _ _ _).2 ⟨by decide +kernel, rfl⟩)
    (.var 0) (.add (.var 0) (.num 1)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd (of_eq_true this) (by decide +kernel)

-- `Lean.Grind.CommRing.eq_true_of_kronQ`
theorem eq_true_of_kronQ.h11 : ¬ drop0% Lean.Grind.CommRing.eq_true_of_kronQ 11 := fun h => by
  have := h (α := Rat) (c2 0 1) 3 1 [] rfl (by decide +kernel) (.var 0) (.var 1) (by decide +kernel) (by decide +kernel)
  exact absurd (of_eq_true this) (by decide +kernel)

/-! ## Removable base conditions `1 < B`: with `B = 1` and degree `0` all codes are `0`. -/

theorem denote_one {α} [Ring α] (f : Nat → α) (p : PPoly) : p.denote f 1 = ((p.kron 1 : Int) : α) := by
  induction p with
  | num k => rfl
  | add k d v p ih =>
    have hm : PPoly.monDenote f 1 0 v = 1 := by rw [PPoly.monDenote]; simp
    show (k : α) * PPoly.monDenote f 1 0 v + p.denote f 1 = ((k * 1 ^ v + p.kron 1 : Int) : α)
    rw [hm, ih, Int.one_pow, Int.mul_one, Ring.intCast_add, Semiring.mul_one]

theorem dsum_two_eq_zero {v : Nat} (h : PPoly.dsum 2 v ≤ 0) : v = 0 := by
  induction v using Nat.strongRecOn with
  | _ v ih =>
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · exact h0
    · rw [PPoly.dsum_eq (by decide)] at h
      have := ih (v / 2) (Nat.div_lt_self h0 (by decide)) (by omega)
      omega

theorem denote_two_deg0 {α} [Ring α] (f : Nat → α) (p : PPoly) (hp : p.Deg 2 0) :
    p.denote f 2 = ((p.kron 1 : Int) : α) := by
  induction p with
  | num k => rfl
  | add k d v p ih =>
    obtain ⟨hv, hp⟩ := hp
    cases dsum_two_eq_zero hv
    show (k : α) * PPoly.monDenote f 2 0 0 + p.denote f 2 = ((k * 1 ^ 0 + p.kron 1 : Int) : α)
    rw [PPoly.monDenote_zero, ih hp, Int.pow_zero, Int.mul_one, Ring.intCast_add, Semiring.mul_one]

theorem kron1_toPP (B B' : Nat) (q : Poly) : (q.toPP_k B).kron 1 = (q.toPP_k B').kron 1 := by
  induction q with
  | num k => rfl
  | add k m p ih =>
    show k * 1 ^ _ + (p.toPP_k B).kron 1 = k * 1 ^ _ + (p.toPP_k B').kron 1
    rw [Int.one_pow, Int.one_pow, ih]

/-- A polynomial of degree `0` denotes the sum of its coefficients. -/
theorem denote_deg0 {α} [CommRing α] (ctx : Context α) (B : Nat) (q : Poly) (hq : q.maxDeg_k = 0) :
    q.denote ctx = (((q.toPP_k B).kron 1 : Int) : α) := by
  have s := Poly.toPP_k_spec ctx (B := 2) (by decide) q (by omega)
  rw [hq] at s
  rw [← s.1, denote_two_deg0 _ _ s.2, kron1_toPP 2 B]

-- `Lean.Grind.CommRing.KList.toPP_spec`
theorem KList.toPP_spec.h5 : drop% Lean.Grind.CommRing.KList.toPP_spec 5 := by
  intro α _ ctx K B ls hok
  by_cases hB : 1 < B
  · exact KList.toPP_spec ctx K B hB ls hok
  have c12 : ∀ ls : KList, (ls.toPP B).kron (2 ^ K) = ls.kron_k K B ∧ (ls.toPP B).norm1 ≤ ls.norm_k := by
    intro ls
    induction ls with
    | nil => exact ⟨rfl, Nat.le_refl _⟩
    | cons k m q ls ih =>
      refine ⟨?_, ?_⟩
      · show (PPoly.append _ (ls.toPP B)).kron (2 ^ K) = Int.sumB_k (Int.mul_k k (Int.shl_k (q.kron_k K B) (Nat.mul K (Mon.code_k B m))) :: ls.kronTerms_k K B)
        rw [PPoly.kron_append, PPoly.kron_mulMonN, ih.1, KList.kron_k, Int.sumB_k_eq, Int.sumB_k_eq]
        show _ = Int.mul_k k (Int.shl_k (q.kron_k K B) (Nat.mul K (Mon.code_k B m))) + _
        rw [Int.mul_k_eq, Int.shl_k_eq, Poly.kron_k_eq]
        show k * ((2 : Int) ^ K) ^ (Mon.code_k B m) * _ + _ = k * (_ * (2 : Int) ^ (K * Mon.code_k B m)) + _
        rw [Int.pow_mul, Int.mul_assoc, Int.mul_comm (((2 : Int) ^ K) ^ (Mon.code_k B m))]
      · show (PPoly.append _ (ls.toPP B)).norm1 ≤ Nat.add (Nat.mul (Int.natAbs_k k) q.norm1_k) ls.norm_k
        have := PPoly.norm1_append ((q.toPP_k B).mulMonN_k (fun k => k) k (Mon.degree_k m) (Mon.code_k B m)) (ls.toPP B)
        have := PPoly.norm1_mulMonN k (Mon.degree_k m) (Mon.code_k B m) (q.toPP_k B)
        rw [Int.natAbs_k_eq, Poly.norm1_k_eq B, Nat.add_eq, Nat.mul_eq]
        have := ih.2
        omega
  refine ⟨(c12 ls).1, (c12 ls).2, fun hz => ?_⟩
  rcases Nat.lt_or_ge B 1 with h0 | h1
  · cases ls with
    | nil => exact Ring.intCast_zero
    | cons k m q ls =>
      have hok : Bool.rec false (ls.ok_k B) (Nat.blt (Nat.add (Mon.degree_k m) q.maxDeg_k) B) = true := hok
      have := (PPoly.and_of_rec hok).1
      rw [Nat.blt_eq] at this; omega
  · have : B = 1 := by omega
    subst this
    rw [denote_one]
    clear c12
    induction ls with
    | nil => exact Ring.intCast_zero
    | cons k m q ls ih =>
      have hok : Bool.rec false (ls.ok_k 1) (Nat.blt (Nat.add (Mon.degree_k m) q.maxDeg_k) 1) = true := hok
      have hok := PPoly.and_of_rec hok
      have hd := Nat.blt_eq.mp hok.1
      rw [Nat.add_eq] at hd
      obtain ⟨hq, hz⟩ := hz
      show ((PPoly.append _ (ls.toPP 1)).kron 1 : α) = 0
      rw [PPoly.kron_append, PPoly.kron_mulMonN, Int.one_pow, Int.mul_one, Ring.intCast_add, Ring.intCast_mul,
        ← denote_deg0 ctx 1 q (by omega), hq, Semiring.mul_zero, AddCommMonoid.zero_add]
      exact ih hz hok.2

theorem code_one_eq_zero (m : Mon) (h : Mon.degree_k m = 0) : Mon.code_k 1 m = 0 := by
  induction m with
  | unit => rfl
  | mult pw m ih =>
    have h' : Nat.add pw.k (Mon.degree_k m) = 0 := h
    show Nat.add (Nat.mul pw.k (Nat.pow 1 pw.x)) (Mon.code_k 1 m) = 0
    simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.one_pow, Nat.mul_one] at h' ⊢
    rw [ih (by omega)]; omega

theorem toPP_one_deg0 (q : Poly) (h : q.maxDeg_k = 0) : (q.toPP_k 1).Deg 2 0 := by
  induction q with
  | num k => trivial
  | add k m p ih =>
    have h' : (Bool.rec p.maxDeg_k (Mon.degree_k m) (Nat.blt p.maxDeg_k (Mon.degree_k m)) : Nat) = 0 := h
    rw [Expr.max_k_eq] at h'
    show PPoly.dsum 2 (Mon.code_k 1 m) ≤ 0 ∧ (p.toPP_k 1).Deg 2 0
    rw [code_one_eq_zero m (by omega), PPoly.dsum_zero]
    exact ⟨Nat.le_refl _, ih (by omega)⟩

theorem kron_deg0 (X : Int) (p : PPoly) (hp : p.Deg 2 0) : p.kron X = p.kron 1 := by
  induction p with
  | num k => rfl
  | add k d v p ih =>
    obtain ⟨hv, hp⟩ := hp
    cases dsum_two_eq_zero hv
    show k * X ^ 0 + p.kron X = k * 1 ^ 0 + p.kron 1
    rw [ih hp, Int.pow_zero, Int.pow_zero]

theorem kron_mulB_deg0 (X : Int) (p q : PPoly) (hp : p.Deg 2 0) (hq : q.Deg 2 0) :
    (p.mulB_k q).kron X = p.kron X * q.kron X := by
  have s := PPoly.mulB_k_spec (fun _ => (0 : Int)) 2 0 0 (by decide) (by decide) p q hp hq
  have e1 : (p.mulB_k q).denote (fun _ => (0 : Int)) 2 = (p.mulB_k q).kron 1 := denote_two_deg0 _ _ s.2
  have e2 : p.denote (fun _ => (0 : Int)) 2 = p.kron 1 := denote_two_deg0 _ _ hp
  have e3 : q.denote (fun _ => (0 : Int)) 2 = q.kron 1 := denote_two_deg0 _ _ hq
  rw [kron_deg0 X _ s.2, kron_deg0 X _ hp, kron_deg0 X _ hq, ← e1, ← e2, ← e3, s.1]

-- `Lean.Grind.CommRing.MList.toPP_spec`
theorem MList.toPP_spec.h5 : drop% Lean.Grind.CommRing.MList.toPP_spec 5 := by
  intro α _ ctx K B ls hok
  by_cases hB : 1 < B
  · exact MList.toPP_spec ctx K B hB ls hok
  rcases Nat.lt_or_ge B 1 with h0 | h1
  · cases ls with
    | nil => exact ⟨rfl, Nat.le_refl _, fun _ => Ring.intCast_zero⟩
    | cons M q ls =>
      have hok : Bool.rec false (ls.ok_k B) (Nat.blt (Nat.add M.maxDeg_k q.maxDeg_k) B) = true := hok
      have := (PPoly.and_of_rec hok).1
      rw [Nat.blt_eq] at this; omega
  have : B = 1 := by omega
  subst this
  induction ls with
  | nil => exact ⟨rfl, Nat.le_refl _, fun _ => Ring.intCast_zero⟩
  | cons M q ls ih =>
    have hok : Bool.rec false (ls.ok_k 1) (Nat.blt (Nat.add M.maxDeg_k q.maxDeg_k) 1) = true := hok
    have hok := PPoly.and_of_rec hok
    have ih := ih hok.2
    have hd := Nat.blt_eq.mp hok.1
    rw [Nat.add_eq] at hd
    have dM := toPP_one_deg0 M (by omega)
    have dq := toPP_one_deg0 q (by omega)
    refine ⟨?_, ?_, fun hz => ?_⟩
    · show (PPoly.append _ (ls.toPP 1)).kron (2 ^ K) = Int.sumB_k (Int.mul_k (M.kron_k K 1) (q.kron_k K 1) :: ls.kronTerms_k K 1)
      rw [PPoly.kron_append, kron_mulB_deg0 _ _ _ dM dq, ih.1, MList.kron_k, Int.sumB_k_eq, Int.sumB_k_eq]
      show _ = Int.mul_k (M.kron_k K 1) (q.kron_k K 1) + _
      rw [Int.mul_k_eq, Poly.kron_k_eq, Poly.kron_k_eq]; rfl
    · show (PPoly.append _ (ls.toPP 1)).norm1 ≤ Nat.add (Nat.mul M.norm1_k q.norm1_k) ls.norm_k
      have := PPoly.norm1_append ((M.toPP_k 1).mulB_k (q.toPP_k 1)) (ls.toPP 1)
      have := PPoly.norm1_mulB_k (M.toPP_k 1) (q.toPP_k 1)
      rw [Poly.norm1_k_eq 1 M, Poly.norm1_k_eq 1 q, Nat.add_eq, Nat.mul_eq]
      have := ih.2.1
      omega
    · obtain ⟨hq, hz⟩ := hz
      have h3 := ih.2.2 hz
      rw [denote_one] at h3 ⊢
      show ((PPoly.append _ (ls.toPP 1)).kron 1 : α) = 0
      rw [PPoly.kron_append, kron_mulB_deg0 _ _ _ dM dq, Ring.intCast_add, Ring.intCast_mul,
        ← denote_deg0 ctx 1 q (by omega), hq, Semiring.mul_zero, AddCommMonoid.zero_add, h3]

theorem toPPQ_indep (K : Nat) (invs : InvVars) (e : Expr) (h : e.degQB_k invs = 0) :
    e.toPPQ 1 invs = e.toPPQ 2 invs ∧ e.kronQ_k K 1 invs = e.kronQ_k K 2 invs := by
  induction e with
  | num k => exact ⟨rfl, rfl⟩
  | natCast n => exact ⟨rfl, rfl⟩
  | intCast k => exact ⟨rfl, rfl⟩
  | var x =>
    have h' : (Option.rec 1 (fun _ => 0) (InvVars.lookup_k invs x) : Nat) = 0 := h
    cases hx : InvVars.lookup_k invs x with
    | none => rw [hx] at h'; cases h'
    | some c =>
      refine ⟨by simp only [Expr.toPPQ, hx], ?_⟩
      show (Option.rec _ (fun c => (Int.ofNat 1, c)) (InvVars.lookup_k invs x) : Int × Nat) =
        Option.rec _ (fun c => (Int.ofNat 1, c)) (InvVars.lookup_k invs x)
      rw [hx]
  | neg a ih =>
    have ih := ih h
    exact ⟨by simp only [Expr.toPPQ, ih.1], congrArg (fun x : Int × Nat => (Int.neg_k x.1, x.2)) ih.2⟩
  | add a b iha ihb =>
    have h' : (Bool.rec (a.degQB_k invs) (b.degQB_k invs) (Nat.blt (a.degQB_k invs) (b.degQB_k invs)) : Nat) = 0 := h
    rw [Expr.max_k_eq] at h'
    have iha := iha (by omega); have ihb := ihb (by omega)
    exact ⟨by simp only [Expr.toPPQ, iha.1, ihb.1],
      (by have e := congr (congrArg (fun x y : Int × Nat => (Int.add_k (Int.mul_k x.1 (Int.ofNat y.2)) (Int.mul_k y.1 (Int.ofNat x.2)), Nat.mul x.2 y.2)) iha.2) ihb.2; exact e)⟩
  | sub a b iha ihb =>
    have h' : (Bool.rec (a.degQB_k invs) (b.degQB_k invs) (Nat.blt (a.degQB_k invs) (b.degQB_k invs)) : Nat) = 0 := h
    rw [Expr.max_k_eq] at h'
    have iha := iha (by omega); have ihb := ihb (by omega)
    exact ⟨by simp only [Expr.toPPQ, iha.1, ihb.1],
      (by have e := congr (congrArg (fun x y : Int × Nat => (Int.sub_k (Int.mul_k x.1 (Int.ofNat y.2)) (Int.mul_k y.1 (Int.ofNat x.2)), Nat.mul x.2 y.2)) iha.2) ihb.2; exact e)⟩
  | mul a b iha ihb =>
    have h' : Nat.add (a.degQB_k invs) (b.degQB_k invs) = 0 := h
    have iha := iha (by simp at h'; omega); have ihb := ihb (by simp at h'; omega)
    exact ⟨by simp only [Expr.toPPQ, iha.1, ihb.1],
      (by have e := congr (congrArg (fun x y : Int × Nat => (Int.mul_k x.1 y.1, Nat.mul x.2 y.2)) iha.2) ihb.2; exact e)⟩
  | pow a k ih =>
    have h' : Nat.mul (a.degQB_k invs) k = 0 := h
    rcases Nat.mul_eq_zero.mp h' with h0 | h0
    · have ih := ih h0
      exact ⟨by simp only [Expr.toPPQ, ih.1], congrArg (fun x : Int × Nat => (Int.pow_k x.1 k, Nat.pow x.2 k)) ih.2⟩
    · subst h0
      refine ⟨?_, ?_⟩
      · simp only [Expr.toPPQ, Nat.pow_zero]; rfl
      · show (Int.pow_k (a.kronQ_k K 1 invs).1 0, Nat.pow (a.kronQ_k K 1 invs).2 0) =
          (Int.pow_k (a.kronQ_k K 2 invs).1 0, Nat.pow (a.kronQ_k K 2 invs).2 0)
        rw [Int.pow_k_eq, Int.pow_k_eq, Int.pow_zero, Int.pow_zero]; rfl

theorem deg_two_zero (B : Nat) (p : PPoly) (hp : p.Deg 2 0) : p.Deg B 0 := by
  induction p with
  | num k => trivial
  | add k d v p ih =>
    obtain ⟨hv, hp⟩ := hp
    cases dsum_two_eq_zero hv
    exact ⟨by rw [PPoly.dsum_zero]; exact Nat.le_refl _, ih hp⟩

-- `Lean.Grind.CommRing.Expr.toPPQ_spec`
theorem Expr.toPPQ_spec.h6 : drop% Lean.Grind.CommRing.Expr.toPPQ_spec 6 := by
  intro α _ _ f K B invs hf e he
  by_cases hB : 1 < B
  · exact Expr.toPPQ_spec f K B hB invs hf e he
  have : B = 1 := by omega
  subst this
  have h0 : e.degQB_k invs = 0 := by omega
  have s := Expr.toPPQ_spec f K 2 (by decide) invs hf e (by omega)
  obtain ⟨i1, i2⟩ := toPPQ_indep K invs e h0
  rw [h0] at s ⊢
  rw [i1, i2]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := s
  refine ⟨?_, deg_two_zero 1 _ s2, s3, s4, s5, s6, s7⟩
  rw [denote_one, ← s1, denote_two_deg0 f _ s2]

end KronAHand
