import Lean

/-!
Hand pass `Free` (hand12): 17 hypotheses left over by the KronA, KronB and Packed passes:
`[AddRightCancel α]` of the semiring Kronecker/packing lemmas (`*_of_kronS`, `*_of_kronLinS`,
`*_of_toPPX_eqS`, incl. `le_cancel`/`lt_cancel`) and `[ExistsAddOfLT α]` of the ordered-ring instance
on the ring envelope `Q α`. 1 necessary, 16 removable, 0 independent, 0 left unresolved.

Removable (`drop% T i`, universes kept): the library already proves the base-`B` Kronecker identity
for semirings without cancellation (`Expr.eq_of_kronSN`, via nonnegative term lists). The other
checks are reduced to its hypotheses:
* `eq_of_kronLinF`: the library's ring lemma `Expr.eq_of_kronLin` for an arbitrary valuation `f`
  instead of a context; over `Int` at `xᵢ = (2 ^ K) ^ (2 ^ i)` it turns the linear-point equality into
  `kronEval_k K 2` equality. `degSOk_two`: `linSOk_k a b` implies `degSOk_k 2 a b`.
  `eq_of_kronLinS'`: `Expr.eq_of_kronLinS` without `AddRightCancel`.
* `eq_of_toPPX_eqS'`: equal packed polynomials have equal Kronecker values (`Expr.denote_toPPX_k`
  over `Int`) for `K = 2 * (majorants)`, so `Expr.eq_of_kronSN` applies.
* `le_cancel`/`lt_cancel`: after rewriting both sides, `OrderedAdd` (part of `OrderedRing`) cancels
  the common summand; no `AddRightCancel` is involved (unlike `eq_cancel_*`, refuted earlier with `BS`).

Reusable model (namespace `FreeHand.D`): `D = {0} ∪ {a + b ε : a ≥ 1}` inside the dual numbers
`ℤ[ε]/(ε²)` (`D.pos n b` is `(n + 1) + b ε`), a commutative semiring with the lexicographic order
(`ε` infinitesimal, `D.le_def`, `D.lt_iff'`): a linear order, lawful `<`, `OrderedRing` (every
positive element has real part `≥ 1`), but no `ExistsAddOfLT` (`D.not_existsAddOfLT`: `1 < 1 + ε`).
It is additively cancellative and embeds in `Q D = ℤ[ε]/(ε²)`, where `ε > 0` but `ε * ε = 0`.

Run with the lean4 repo's stage1 binary: `runs/hand12/lean.sh checks/FreeHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

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

namespace FreeHand
open Lean.Grind Lean.Grind.CommRing
open AddCommMonoid AddCommGroup NatModule IntModule
open Semiring hiding add_zero add_comm add_assoc
open Ring hiding sub_eq_add_neg

/-- The library's Expr.eq_of_kronLin for an arbitrary valuation f instead of a context. -/
theorem eq_of_kronLinF {α} [CommRing α] (f : Nat → α) (K : Nat) (a b : Expr)
    (hl : Expr.linOk_k a b = true) (hK : Expr.kronOk_k K a b = true) (h : a.kronLinEval_k K = b.kronLinEval_k K) :
    a.denoteF f = b.denoteF f := by
  have hl := PPoly.and_of_rec hl
  have ha := Nat.le_trans (Expr.degB_le_lin_k a) (Nat.le_of_ble_eq_true hl.1)
  have hb := Nat.le_trans (Expr.degB_le_lin_k b) (Nat.le_of_ble_eq_true hl.2)
  have hK : 2 * (a.majorant_k + b.majorant_k) < 2 ^ K := Nat.blt_eq.mp hK
  have hX : (0 : Int) < 2 ^ K := Int.pow_pos (by decide)
  have sa := Expr.toLin_spec f ((2 : Int) ^ K) a ha
  have sb := Expr.toLin_spec f ((2 : Int) ^ K) b hb
  have hk : (a.toLin.append b.toLin.neg).kron ((2 : Int) ^ K) = 0 := by
    rw [PPoly.kron_append, PPoly.kron_neg, sa.2.1, sb.2.1, ← Expr.kronLinEval_k_eq, ← Expr.kronLinEval_k_eq, h]; omega
  have hn : 2 * ((a.toLin.append b.toLin.neg).norm1 : Int) < 2 ^ K := by
    have := PPoly.norm1_append a.toLin b.toLin.neg; rw [PPoly.norm1_neg] at this
    have : 2 * (a.toLin.append b.toLin.neg).norm1 < 2 ^ K := by have := sa.2.2; have := sb.2.2; omega
    have h2 : ((2 ^ K : Nat) : Int) = (2 : Int) ^ K := Int.natCast_pow 2 K
    rw [← h2]; exact Int.ofNat_lt.mpr (by simpa using this)
  have hz := PPoly.denoteG_eq_zero_of_coeff (PPoly.linVal f) (by simp [PPoly.linVal]) _ _ (Nat.le_refl _)
    (fun c => PPoly.coeff_eq_zero_of_kron _ hX c _ hk hn)
  rw [PPoly.denoteG_append, PPoly.denoteG_neg, sa.1, sb.1] at hz
  rw [← sub_eq_zero_iff, sub_eq_add_neg, hz]

/-- A linear semiring term passes the semiring degree check in base `2`. -/
theorem degS_two_le (e : Expr) (h : e.linS_k ≤ 1) : e.degS_k 2 ≤ e.linS_k := by
  induction e with
  | num k => cases k <;> simp_all [Expr.degS_k, Expr.linS_k]
  | natCast | intCast | var | neg | sub => simp_all [Expr.degS_k, Expr.linS_k]
  | add a b iha ihb =>
    have h' : a.linS_k ||| b.linS_k ≤ 1 := h
    have := @Nat.left_le_or a.linS_k b.linS_k; have := @Nat.right_le_or a.linS_k b.linS_k
    exact Expr.max_le_lor _ _ _ _ (iha (by omega)) (ihb (by omega))
  | mul a b iha ihb =>
    have h' : Nat.add a.linS_k b.linS_k ≤ 1 := h
    simp only [Nat.add_eq] at h'
    show Nat.add (a.degS_k 2) (b.degS_k 2) ≤ Nat.add a.linS_k b.linS_k
    have := iha (by omega); have := ihb (by omega); simp only [Nat.add_eq]; omega
  | pow a k ih =>
    have h' : (Bool.rec (Nat.mul a.linS_k k) 2 (Nat.ble 2 a.linS_k) : Nat) ≤ 1 := h
    cases hb : Nat.ble 2 a.linS_k
    · rw [hb] at h'
      have ha : a.linS_k ≤ 1 := Nat.le_of_lt_succ (Nat.gt_of_not_le (fun hle => by rw [Nat.ble_eq.mpr hle] at hb; cases hb))
      have da := ih ha
      have hb2 : Nat.ble 2 (a.degS_k 2) = false := by
        cases hh : Nat.ble 2 (a.degS_k 2)
        · rfl
        · have := Nat.le_of_ble_eq_true hh; omega
      show (Bool.rec (Nat.mul (a.degS_k 2) k) 2 (Nat.ble 2 (a.degS_k 2)) : Nat) ≤ Bool.rec (Nat.mul a.linS_k k) 2 (Nat.ble 2 a.linS_k)
      rw [hb, hb2]; exact Nat.mul_le_mul_right k da
    · rw [hb] at h'; exact (Nat.not_succ_le_self 1 h').elim

theorem degSOk_two {a b : Expr} (h : Expr.linSOk_k a b = true) : Expr.degSOk_k 2 a b = true := by
  have h := PPoly.and_of_rec h
  have ha := Nat.le_of_ble_eq_true h.1
  have hb := Nat.le_of_ble_eq_true h.2
  have da := degS_two_le a ha
  have db := degS_two_le b hb
  unfold Expr.degSOk_k
  rw [show Nat.blt 1 2 = true from rfl, Nat.blt_eq.mpr (show a.degS_k 2 < 2 by omega),
    Nat.blt_eq.mpr (show b.degS_k 2 < 2 by omega)]

/-- `Expr.eq_of_kronLinS` without `AddRightCancel`: base `2` Kronecker values agree (by the ring
lemma over `Int`), so `Expr.eq_of_kronSN` applies. -/
theorem eq_of_kronLinS' {α} [CommSemiring α] (ctx : Context α) (K : Nat) (a b : Expr)
    (hl : Expr.linSOk_k a b = true) (hK : Expr.kronOk_k K a b = true)
    (h : a.kronLinEval_k K = b.kronLinEval_k K) : a.denoteS ctx = b.denoteS ctx :=
  Expr.eq_of_kronSN ctx K 2 a b (degSOk_two hl) hK (by
    rw [Expr.kronEval_k_eq, Expr.kronEval_k_eq]
    exact eq_of_kronLinF _ K a b (Expr.of_linSOk_k hl).2 hK h)

/-- `Expr.eq_of_toPPX_eqS` without `AddRightCancel`: equal packed polynomials give equal Kronecker
values at any `K`; pick `K` large enough for `Expr.eq_of_kronSN`. -/
theorem eq_of_toPPX_eqS' {α} [CommSemiring α] (ctx : Context α) (B : Nat) (bal₁ bal₂ : Bool)
    (a b : Expr) (p : PPoly) (hB : Expr.degSOk_k B a b = true)
    (h₁ : p = a.toPPX_k B bal₁) (h₂ : p = b.toPPX_k B bal₂) : a.denoteS ctx = b.denoteS ctx := by
  have hd := Expr.of_degOk_k (Expr.of_degSOk_k hB).2
  let K := 2 * (a.majorant_k + b.majorant_k)
  have hK : Expr.kronOk_k K a b = true := Nat.blt_eq.mpr (Nat.lt_two_pow_self)
  refine Expr.eq_of_kronSN ctx K B a b hB hK ?_
  rw [Expr.kronEval_k_eq, Expr.kronEval_k_eq, ← Expr.denote_toPPX_k _ B hd.1 bal₁ a hd.2.1,
    ← Expr.denote_toPPX_k _ B hd.1 bal₂ b hd.2.2, ← h₁, ← h₂]

end FreeHand

namespace FreeHand
open Lean.Grind

/-- `D`: the semiring `{0} ∪ {a + b ε : a ≥ 1}` inside the dual numbers `ℤ[ε]/(ε²)`
(`pos n b` is `(n + 1) + b ε`), ordered lexicographically with `ε` infinitesimal. -/
inductive D where
  | zero
  | pos (n : Nat) (b : Int)
deriving DecidableEq

namespace D
def re : D → Int
  | zero => 0
  | pos n _ => (n : Int) + 1
def im : D → Int
  | zero => 0
  | pos _ b => b
def add : D → D → D
  | zero, y => y
  | pos n b, zero => pos n b
  | pos n b, pos m c => pos (n + m + 1) (b + c)
def mul : D → D → D
  | zero, _ => zero
  | pos _ _, zero => zero
  | pos n b, pos m c => pos (n * m + n + m) (((n : Int) + 1) * c + ((m : Int) + 1) * b)
def nc : Nat → D
  | 0 => zero
  | k + 1 => pos k 0
def pow (a : D) : Nat → D
  | 0 => nc 1
  | n + 1 => mul (pow a n) a

theorem re_nonneg (x : D) : 0 ≤ x.re := by cases x <;> simp [re] <;> omega
theorem ext' {x y : D} (h₁ : x.re = y.re) (h₂ : x.im = y.im) : x = y := by
  cases x <;> cases y <;> simp only [re, im, D.pos.injEq, reduceCtorEq] at * <;> omega
theorem re_add (x y : D) : (add x y).re = x.re + y.re := by
  cases x <;> cases y <;> simp [add, re] <;> omega
theorem im_add (x y : D) : (add x y).im = x.im + y.im := by
  cases x <;> cases y <;> simp [add, im]
theorem re_mul (x y : D) : (mul x y).re = x.re * y.re := by
  cases x <;> cases y <;> simp [mul, re]
  grind
theorem im_mul (x y : D) : (mul x y).im = x.re * y.im + x.im * y.re := by
  cases x <;> cases y <;> simp [mul, im, re]
  grind
theorem re_nc (k : Nat) : (nc k).re = k := by cases k <;> simp [nc, re]
theorem im_nc (k : Nat) : (nc k).im = 0 := by cases k <;> simp [nc, im]

instance : Add D := ⟨add⟩
instance : Mul D := ⟨mul⟩
instance : NatCast D := ⟨nc⟩
instance : OfNat D n := ⟨nc n⟩
instance : SMul Nat D := ⟨fun n a => mul (nc n) a⟩
instance : HPow D Nat D := ⟨pow⟩

theorem re_add' (x y : D) : (x + y).re = x.re + y.re := re_add x y
theorem im_add' (x y : D) : (x + y).im = x.im + y.im := im_add x y
theorem re_mul' (x y : D) : (x * y).re = x.re * y.re := re_mul x y
theorem im_mul' (x y : D) : (x * y).im = x.re * y.im + x.im * y.re := im_mul x y
theorem re_ofNat (k : Nat) : (OfNat.ofNat k : D).re = k := re_nc k
theorem im_ofNat (k : Nat) : (OfNat.ofNat k : D).im = 0 := im_nc k

theorem mul_one' (a : D) : mul a (nc 1) = a :=
  ext' (by rw [re_mul, re_nc]; omega) (by rw [im_mul, re_nc, im_nc]; omega)
theorem one_mul' (a : D) : mul (nc 1) a = a :=
  ext' (by rw [re_mul, re_nc]; omega) (by rw [im_mul, re_nc, im_nc]; omega)
theorem nc_succ (k : Nat) : nc (k + 1) = add (nc k) (nc 1) :=
  ext' (by rw [re_add, re_nc, re_nc, re_nc]; omega) (by rw [im_add, im_nc, im_nc, im_nc]; omega)

instance : CommSemiring D where
  add_zero a := by cases a <;> rfl
  add_comm a b := ext' (by rw [re_add', re_add']; omega) (by rw [im_add', im_add']; omega)
  add_assoc a b c := ext' (by rw [re_add', re_add', re_add', re_add']; omega) (by rw [im_add', im_add', im_add', im_add']; omega)
  mul_assoc a b c := ext' (by simp only [re_mul']; grind) (by simp only [re_mul', im_mul']; grind)
  mul_one := mul_one'
  one_mul := one_mul'
  mul_comm a b := ext' (by simp only [re_mul']; grind) (by simp only [re_mul', im_mul']; grind)
  left_distrib a b c := ext' (by simp only [re_mul', re_add']; grind) (by simp only [re_mul', im_mul', re_add', im_add']; grind)
  right_distrib a b c := ext' (by simp only [re_mul', re_add']; grind) (by simp only [re_mul', im_mul', re_add', im_add']; grind)
  zero_mul a := rfl
  mul_zero a := by cases a <;> rfl
  pow_zero a := rfl
  pow_succ a n := rfl
  ofNat_succ := nc_succ

/-- Lexicographic order on `(re, im)`. -/
instance : LE D := ⟨fun x y => x.re < y.re ∨ (x.re = y.re ∧ x.im ≤ y.im)⟩
instance : LT D := ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩
theorem le_def {x y : D} : x ≤ y ↔ x.re < y.re ∨ (x.re = y.re ∧ x.im ≤ y.im) := Iff.rfl
instance : Std.LawfulOrderLT D := ⟨fun _ _ => Iff.rfl⟩
instance : Std.IsPreorder D where
  le_refl x := Or.inr ⟨rfl, Int.le_refl _⟩
  le_trans := by intro x y z h₁ h₂; rw [le_def] at *; omega
theorem lt_iff' {x y : D} : x < y ↔ x.re < y.re ∨ (x.re = y.re ∧ x.im < y.im) := by
  show (x ≤ y ∧ ¬ y ≤ x) ↔ _
  rw [le_def, le_def]; omega

instance : OrderedRing D where
  add_le_left_iff c := by rw [le_def, le_def, re_add', im_add', re_add', im_add']; omega
  zero_lt_one := by rw [lt_iff']; exact Or.inl (by decide)
  mul_lt_mul_of_pos_left {a b c} h hc := by
    rw [lt_iff'] at *
    have hc1 : 1 ≤ c.re := by
      cases c with
      | zero => rcases hc with h | ⟨_, h⟩ <;> exact absurd h (by decide)
      | pos n b => simp only [re]; omega
    simp only [re_mul', im_mul']
    rcases h with h | ⟨h₁, h₂⟩
    · exact Or.inl (Int.mul_lt_mul_of_pos_left h (by omega))
    · refine Or.inr ⟨by rw [h₁], ?_⟩
      have := Int.mul_lt_mul_of_pos_left h₂ (show 0 < c.re by omega)
      rw [h₁]; omega
  mul_lt_mul_of_pos_right {a b c} h hc := by
    rw [lt_iff'] at *
    have hc1 : 1 ≤ c.re := by
      cases c with
      | zero => rcases hc with h | ⟨_, h⟩ <;> exact absurd h (by decide)
      | pos n b => simp only [re]; omega
    simp only [re_mul', im_mul']
    rcases h with h | ⟨h₁, h₂⟩
    · exact Or.inl (Int.mul_lt_mul_of_pos_right h (by omega))
    · refine Or.inr ⟨by rw [h₁], ?_⟩
      have := Int.mul_lt_mul_of_pos_right h₂ (show 0 < c.re by omega)
      rw [h₁]; omega

/-- `D` has no `ExistsAddOfLT`: `1 < 1 + ε`, but `ε ∉ D`. -/
theorem not_existsAddOfLT : ¬ ∃ c : D, 0 < c ∧ pos 0 1 = pos 0 0 + c := by
  rintro ⟨c, -, hc⟩
  have h1 := congrArg re hc; have h2 := congrArg im hc
  rw [re_add'] at h1; rw [im_add'] at h2
  cases c <;> simp only [re, im] at h1 h2 <;> omega
end D

open Lean.Grind.Ring.OfSemiring in
-- `Lean.Grind.Ring.OfSemiring.instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT` (hypothesis 7, Lean.Grind.ExistsAddOfLT α): necessary; D = {0} ∪ {a + bε : a ≥ 1} ⊂ ℤ[ε]/(ε²), lex order with ε infinitesimal: an OrderedRing (positive elements have a ≥ 1) without ExistsAddOfLT (1 < 1 + ε); in Q D, e = (1 + ε) - 1 = ε is positive but e·e = 0 = e·0, so e·0 < e·e fails
theorem instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT.h7 :
    ¬ drop0% Lean.Grind.Ring.OfSemiring.instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT 7 := fun h => by
  have hQ := h (α := D)
  let e : Q D := Q.mk (D.pos 0 1, D.pos 0 0)
  have he : (0 : Q D) < e := by
    rw [← toQ_ofNat]
    refine ⟨(mk_le_mk).2 ?_, fun h => ?_⟩
    · rw [D.le_def]; decide
    · have := (mk_le_mk).1 h; rw [D.le_def] at this; revert this; decide
  have hee : e * e = e * 0 := Quot.sound ⟨0, by decide⟩
  have := hQ.mul_lt_mul_of_pos_left (a := 0) (b := e) (c := e) he he
  rw [hee] at this
  exact this.2 (Std.le_refl _)
end FreeHand

namespace FreeHand
open Lean.Grind Lean.Grind.CommRing

-- `Lean.Grind.CommRing.Expr.eq_of_kronS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; the library's AddRightCancel-free Expr.eq_of_kronSN has the same hypotheses
theorem eq_of_kronS.h2 : drop% Lean.Grind.CommRing.Expr.eq_of_kronS 2 :=
  fun ctx K B a b hB hK h => Expr.eq_of_kronSN ctx K B a b hB hK h
-- `Lean.Grind.CommRing.eq_true_of_kronS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; the library's AddRightCancel-free Expr.eq_of_kronSN has the same hypotheses
theorem eq_true_of_kronS.h2 : drop% Lean.Grind.CommRing.eq_true_of_kronS 2 :=
  fun ctx K B a b hB hK h => eq_true_of_kronSN ctx K B a b hB hK h
-- `Lean.Grind.CommRing.le_true_of_kronS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; the library's AddRightCancel-free Expr.eq_of_kronSN has the same hypotheses
theorem le_true_of_kronS.h2 : drop% Lean.Grind.CommRing.le_true_of_kronS 2 :=
  fun ctx K B a b hB hK h => le_true_of_kronSN ctx K B a b hB hK h
-- `Lean.Grind.CommRing.lt_false_of_kronS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; the library's AddRightCancel-free Expr.eq_of_kronSN has the same hypotheses
theorem lt_false_of_kronS.h2 : drop% Lean.Grind.CommRing.lt_false_of_kronS 2 :=
  fun ctx K B a b hB hK h => lt_false_of_kronSN ctx K B a b hB hK h
-- `Lean.Grind.CommRing.le_cancel_of_kronS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; Expr.eq_of_kronSN rewrites both sides, then OrderedAdd (from OrderedRing) cancels c, no AddRightCancel needed
theorem le_cancel_of_kronS.h2 : drop% Lean.Grind.CommRing.le_cancel_of_kronS 2 :=
  fun ctx K B a b a' b' c hB₁ hK₁ h₁ hB₂ hK₂ h₂ => by
    rw [Expr.eq_of_kronSN ctx K B a (a'.add c) hB₁ hK₁ h₁, Expr.eq_of_kronSN ctx K B b (b'.add c) hB₂ hK₂ h₂]
    exact propext (OrderedAdd.add_le_left_iff _).symm
-- `Lean.Grind.CommRing.lt_cancel_of_kronS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; Expr.eq_of_kronSN rewrites both sides, then OrderedAdd (from OrderedRing) cancels c, no AddRightCancel needed
theorem lt_cancel_of_kronS.h2 : drop% Lean.Grind.CommRing.lt_cancel_of_kronS 2 :=
  fun ctx K B a b a' b' c hB₁ hK₁ h₁ hB₂ hK₂ h₂ => by
    rw [Expr.eq_of_kronSN ctx K B a (a'.add c) hB₁ hK₁ h₁, Expr.eq_of_kronSN ctx K B b (b'.add c) hB₂ hK₂ h₂]
    exact propext (OrderedAdd.add_lt_left_iff _).symm

-- `Lean.Grind.CommRing.Expr.eq_of_kronLinS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; linSOk_k implies degSOk_k 2, and the Int instance of the ring lemma (eq_of_kronLin at the valuation xᵢ = (2^K)^(2^i)) turns the linear check into the base-2 Kronecker equality, so Expr.eq_of_kronSN applies
theorem eq_of_kronLinS.h2 : drop% Lean.Grind.CommRing.Expr.eq_of_kronLinS 2 :=
  fun ctx K a b hl hK h => eq_of_kronLinS' ctx K a b hl hK h
-- `Lean.Grind.CommRing.eq_true_of_kronLinS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; linSOk_k implies degSOk_k 2, and the Int instance of the ring lemma (eq_of_kronLin at the valuation xᵢ = (2^K)^(2^i)) turns the linear check into the base-2 Kronecker equality, so Expr.eq_of_kronSN applies
theorem eq_true_of_kronLinS.h2 : drop% Lean.Grind.CommRing.eq_true_of_kronLinS 2 :=
  fun ctx K a b hl hK h => eq_true (eq_of_kronLinS' ctx K a b hl hK h)
-- `Lean.Grind.CommRing.le_true_of_kronLinS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; linSOk_k implies degSOk_k 2, and the Int instance of the ring lemma (eq_of_kronLin at the valuation xᵢ = (2^K)^(2^i)) turns the linear check into the base-2 Kronecker equality, so Expr.eq_of_kronSN applies
theorem le_true_of_kronLinS.h2 : drop% Lean.Grind.CommRing.le_true_of_kronLinS 2 :=
  fun ctx K a b hl hK h => by rw [eq_of_kronLinS' ctx K a b hl hK h]; exact eq_true (Std.le_refl _)
-- `Lean.Grind.CommRing.lt_false_of_kronLinS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; linSOk_k implies degSOk_k 2, and the Int instance of the ring lemma (eq_of_kronLin at the valuation xᵢ = (2^K)^(2^i)) turns the linear check into the base-2 Kronecker equality, so Expr.eq_of_kronSN applies
theorem lt_false_of_kronLinS.h2 : drop% Lean.Grind.CommRing.lt_false_of_kronLinS 2 :=
  fun ctx K a b hl hK h => by rw [eq_of_kronLinS' ctx K a b hl hK h]; exact eq_false Std.lt_irrefl
-- `Lean.Grind.CommRing.le_cancel_of_kronLinS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; eq_of_kronLinS without AddRightCancel (via Expr.eq_of_kronSN in base 2) rewrites both sides, then OrderedAdd cancels c
theorem le_cancel_of_kronLinS.h2 : drop% Lean.Grind.CommRing.le_cancel_of_kronLinS 2 :=
  fun ctx K a b a' b' c hl₁ hK₁ h₁ hl₂ hK₂ h₂ => by
    rw [eq_of_kronLinS' ctx K a (a'.add c) hl₁ hK₁ h₁, eq_of_kronLinS' ctx K b (b'.add c) hl₂ hK₂ h₂]
    exact propext (OrderedAdd.add_le_left_iff _).symm
-- `Lean.Grind.CommRing.lt_cancel_of_kronLinS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; eq_of_kronLinS without AddRightCancel (via Expr.eq_of_kronSN in base 2) rewrites both sides, then OrderedAdd cancels c
theorem lt_cancel_of_kronLinS.h2 : drop% Lean.Grind.CommRing.lt_cancel_of_kronLinS 2 :=
  fun ctx K a b a' b' c hl₁ hK₁ h₁ hl₂ hK₂ h₂ => by
    rw [eq_of_kronLinS' ctx K a (a'.add c) hl₁ hK₁ h₁, eq_of_kronLinS' ctx K b (b'.add c) hl₂ hK₂ h₂]
    exact propext (OrderedAdd.add_lt_left_iff _).symm

-- `Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; equal packed polynomials give equal Kronecker values (denote_toPPX_k over Int at xᵢ = (2^K)^(B^i)) for K = 2·(majorants), so Expr.eq_of_kronSN applies
theorem eq_of_toPPX_eqS.h2 : drop% Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS 2 :=
  fun ctx B bal₁ bal₂ a b p hB h₁ h₂ => eq_of_toPPX_eqS' ctx B bal₁ bal₂ a b p hB h₁ h₂
-- `Lean.Grind.CommRing.eq_true_of_toPPX_eqS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; equal packed polynomials give equal Kronecker values (denote_toPPX_k over Int at xᵢ = (2^K)^(B^i)) for K = 2·(majorants), so Expr.eq_of_kronSN applies
theorem eq_true_of_toPPX_eqS.h2 : drop% Lean.Grind.CommRing.eq_true_of_toPPX_eqS 2 :=
  fun ctx B bal₁ bal₂ a b p hB h₁ h₂ => eq_true (eq_of_toPPX_eqS' ctx B bal₁ bal₂ a b p hB h₁ h₂)
-- `Lean.Grind.CommRing.le_true_of_toPPX_eqS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; equal packed polynomials give equal Kronecker values (denote_toPPX_k over Int at xᵢ = (2^K)^(B^i)) for K = 2·(majorants), so Expr.eq_of_kronSN applies
theorem le_true_of_toPPX_eqS.h2 : drop% Lean.Grind.CommRing.le_true_of_toPPX_eqS 2 :=
  fun ctx B bal₁ bal₂ a b p hB h₁ h₂ => by
    rw [eq_of_toPPX_eqS' ctx B bal₁ bal₂ a b p hB h₁ h₂]; exact eq_true (Std.le_refl _)
-- `Lean.Grind.CommRing.lt_false_of_toPPX_eqS` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; equal packed polynomials give equal Kronecker values (denote_toPPX_k over Int at xᵢ = (2^K)^(B^i)) for K = 2·(majorants), so Expr.eq_of_kronSN applies
theorem lt_false_of_toPPX_eqS.h2 : drop% Lean.Grind.CommRing.lt_false_of_toPPX_eqS 2 :=
  fun ctx B bal₁ bal₂ a b p hB h₁ h₂ => by
    rw [eq_of_toPPX_eqS' ctx B bal₁ bal₂ a b p hB h₁ h₂]; exact eq_false Std.lt_irrefl

end FreeHand
