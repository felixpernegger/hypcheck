module
public import HCHeaderM
import HCRefute
import all CombinatorialGames.Counterexamples.Multiplication
import all CombinatorialGames.Counterexamples.OrdinalSum
import all CombinatorialGames.Counterexamples.TinyOrder
import all CombinatorialGames.Game.Basic
import all CombinatorialGames.Game.Birthday
import all CombinatorialGames.Game.Canonical
import all CombinatorialGames.Game.Classes
import all CombinatorialGames.Game.Confusion
import all CombinatorialGames.Game.Functor
import all CombinatorialGames.Game.Graph
import all CombinatorialGames.Game.IGame
import all CombinatorialGames.Game.Impartial.Grundy
import all CombinatorialGames.Game.Impartial.Multiplication
import all CombinatorialGames.Game.Loopy.Basic
import all CombinatorialGames.Game.Loopy.IGame
import all CombinatorialGames.Game.Loopy.Outcome
import all CombinatorialGames.Game.Loopy.StoppingTime
import all CombinatorialGames.Game.Order
import all CombinatorialGames.Game.Ordinal
import all CombinatorialGames.Game.OrdinalSum
import all CombinatorialGames.Game.Player
import all CombinatorialGames.Game.Small
import all CombinatorialGames.Game.Special
import all CombinatorialGames.Game.Specific.Domineering
import all CombinatorialGames.Game.Specific.Nim
import all CombinatorialGames.Game.Specific.Poset
import all CombinatorialGames.Game.Stops
import all CombinatorialGames.Mathlib.Dyadic
import all CombinatorialGames.Mathlib.EtaSet
import all CombinatorialGames.Mathlib.SignType
import all CombinatorialGames.Mathlib.Small
import all CombinatorialGames.Mathlib.WithTop
import all CombinatorialGames.NatOrdinal.AddMonoidAlgebra
import all CombinatorialGames.NatOrdinal.Basic
import all CombinatorialGames.NatOrdinal.Pow
import all CombinatorialGames.Nimber.Basic
import all CombinatorialGames.Nimber.Field
import all CombinatorialGames.Nimber.Nat
import all CombinatorialGames.Nimber.NatOrdinal
import all CombinatorialGames.Nimber.Omega
import all CombinatorialGames.Nimber.SimplestExtension.Algebraic
import all CombinatorialGames.Nimber.SimplestExtension.Basic
import all CombinatorialGames.Nimber.SimplestExtension.Closure
import all CombinatorialGames.Nimber.SimplestExtension.Polynomial
import all CombinatorialGames.Nimber.SmallDegree.Inseparable
import all CombinatorialGames.Nimber.SmallDegree.Quartic
import all CombinatorialGames.SignExpansion.Basic
import all CombinatorialGames.SignExpansion.Simplicity
import all CombinatorialGames.SignExpansion.Surreal
import all CombinatorialGames.Surreal.Basic
import all CombinatorialGames.Surreal.Birthday.Basic
import all CombinatorialGames.Surreal.Birthday.Cut
import all CombinatorialGames.Surreal.Birthday.Dyadic
import all CombinatorialGames.Surreal.Cut
import all CombinatorialGames.Surreal.Division
import all CombinatorialGames.Surreal.Dyadic
import all CombinatorialGames.Surreal.HahnSeries.Basic
import all CombinatorialGames.Surreal.Leading
import all CombinatorialGames.Surreal.Multiplication
import all CombinatorialGames.Surreal.Omnific.Basic
import all CombinatorialGames.Surreal.Ordinal
import all CombinatorialGames.Surreal.Pow
import all CombinatorialGames.Surreal.Real
import all CombinatorialGames.Tactic.AddInstances
import all CombinatorialGames.Tactic.GameCmp
import all CombinatorialGames.Tactic.OrdinalAlias
import all CombinatorialGames.Tactic.Register
import all CombinatorialGames.Test.GameCmp

namespace T1c0
universe u
open Nimber Polynomial Ordinal Order Set

noncomputable def T : Nimber.{0} := algClosure 0
theorem hT : IsAlgClosed T := IsAlgClosed.algClosure 0
noncomputable def R : Nimber.{0} := ∗(val T ^ ω)
theorem hR : IsRing R := hT.isRing_opow_omega0
theorem T_lt_R : T < R := val_lt_iff.1 (left_lt_opow hT.one_lt_val one_lt_omega0)

theorem inv_not_lt {a : Nimber.{0}} (ha : a < T) : ¬ (T + a)⁻¹ < R := by
  intro h
  obtain ⟨p, hpc, hp⟩ := eq_oeval_of_lt_opow_omega0 h
  rw [← hT.eval_eq_of_lt hpc] at hp
  have hTa : T + a ≠ 0 := by
    intro e; rw [Nimber.add_eq_zero] at e; exact ha.ne' e
  have hq : ∀ k, ((X + C a) * p).coeff k < T :=
    hT.toIsRing.coeff_mul_lt (hT.toIsGroup.coeff_add_lt (coeff_X_lt hT.one_lt) (coeff_C_lt ha)) hpc
  have e1 : oeval T ((X + C a) * p) = oeval T 1 := by
    rw [← hT.eval_eq_of_lt hq, ← hT.eval_eq_of_lt (coeff_one_lt hT.one_lt), eval_mul, hp]
    simp [mul_inv_cancel₀ hTa]
  have e2 := (oeval_inj hq (coeff_one_lt hT.one_lt)).1 e1
  have hu : IsUnit (X + C a) := ⟨⟨_, _, e2, by rw [_root_.mul_comm]; exact e2⟩, rfl⟩
  have := degree_eq_zero_of_isUnit hu
  rw [degree_X_add_C] at this
  exact one_ne_zero this

theorem Tinv_not_lt : ¬ T⁻¹ < R := by simpa using inv_not_lt (a := 0) hT.pos
theorem notFieldR : ¬ IsField R := fun h => Tinv_not_lt (h.inv_lt T_lt_R)
theorem Rinv : R⁻¹ = T := by
  rcases lt_trichotomy R⁻¹ T with h | h | h
  · have := hT.toIsField.inv_lt h
    rw [inv_inv] at this
    exact absurd (this.trans T_lt_R) (lt_irrefl _)
  · exact h
  · have := hR.inv_lt_of_not_isField notFieldR h
    exact absurd this Tinv_not_lt
theorem Tinv : T⁻¹ = R := by rw [← Rinv, inv_inv]
theorem R_mul_T : R * T = 1 := by rw [← Tinv]; exact inv_mul_cancel₀ hT.ne_zero
theorem one_lt_T : (1 : Nimber.{0}) < T := hT.one_lt
theorem RT_ne : ∗(val R * val T) ≠ 1 := by
  intro e
  have h1 : val T ≤ val R * val T := Ordinal.le_mul_right _ (by
    have := hR.one_lt_val; exact (zero_lt_one.trans this))
  have : T ≤ ∗(val R * val T) := h1
  rw [e] at this
  exact absurd one_lt_T (not_lt.2 this)

theorem T_lt_T1 : T < T + 1 :=
  lt_of_le_of_ne (hT.toIsGroup.le_add_self one_lt_T) (fun e => (one_ne_zero : (1 : Nimber.{0}) ≠ 0) (by
    have := congrArg (· + T) e
    simp only [CharTwo.add_self_eq_zero, _root_.add_comm T 1, _root_.add_assoc, _root_.add_zero] at this
    exact this.symm))
theorem T1_lt_R : T + 1 < R := hR.add_lt T_lt_R (one_lt_T.trans T_lt_R)
theorem R_lt_T1inv : R < (T + 1)⁻¹ := by
  rcases lt_trichotomy (T + 1)⁻¹ R with h | h | h
  · exact absurd h (inv_not_lt one_lt_T)
  · have := congrArg (·⁻¹) h; simp only [inv_inv, Rinv] at this
    exact absurd this T_lt_T1.ne'
  · exact h
theorem notFieldT1 : ¬ IsField (T + 1) := fun h => by
  have := h.inv_lt T_lt_T1
  rw [Tinv] at this
  exact lt_asymm this T1_lt_R

theorem one_lt_two2 : (1 : Nimber.{0}) < ∗2 := IsRing.two.one_lt
theorem two_lt_T : (∗2 : Nimber.{0}) < T :=
  (show (∗2 : Nimber.{0}) < ∗ω from of.lt_iff_lt.2 (by exact_mod_cast natCast_lt_omega0 2)).trans_le hT.omega0_le

-- helper: polynomials in T with coefficients in F2 form a subring
noncomputable def S2 : Subring Nimber.{0} where
  carrier := {y | ∃ p : Nimber[X], (∀ k, p.coeff k < ∗2) ∧ eval T p = y}
  zero_mem' := ⟨0, coeff_zero_lt (by simp), by simp⟩
  one_mem' := ⟨1, coeff_one_lt one_lt_two2, by simp⟩
  add_mem' := by
    rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨p + q, IsGroup.two.coeff_add_lt hp hq, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨p * q, IsRing.two.coeff_mul_lt hp hq, by simp⟩
  neg_mem' := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, hp, by simp⟩

theorem T_mem_S2 : T ∈ S2 := ⟨X, coeff_X_lt one_lt_two2, by simp⟩
theorem closure_le_S2 : Subring.closure {T} ≤ S2 :=
  Subring.closure_le.2 (Set.singleton_subset_iff.2 T_mem_S2)

-- helper: an F2-polynomial in T equal to a times another one has all coefficients related
theorem key2 {p q : Nimber.{0}[X]} (hp : ∀ k, p.coeff k < ∗2) (hq : ∀ k, q.coeff k < ∗2)
    (e : eval T p = ∗2 * eval T q) : q = 0 := by
  have hc : ∀ k, (p + C (∗2) * q).coeff k < T := by
    intro k
    rw [coeff_add, coeff_C_mul]
    exact hT.toIsGroup.add_lt ((hp k).trans two_lt_T) (hT.toIsRing.mul_lt two_lt_T ((hq k).trans two_lt_T))
  have h0 : oeval T (p + C (∗2) * q) = 0 := by
    rw [← hT.eval_eq_of_lt hc, eval_add, eval_mul, eval_C, e]
    exact CharTwo.add_self_eq_zero _
  rw [oeval_eq_zero_iff hT.ne_zero] at h0
  have hz : ∀ k, q.coeff k = 0 := by
    intro k
    have hk := congrArg (fun r : Nimber.{0}[X] => r.coeff k) h0
    simp only [coeff_add, coeff_C_mul, coeff_zero] at hk
    rw [Nimber.add_eq_zero] at hk
    rcases lt_two_iff.1 (hq k) with h | h
    · exact h
    · rw [h, _root_.mul_one] at hk
      exact absurd (hk ▸ hp k) (lt_irrefl _)
  ext k
  simpa using hz k

theorem two_notMem_S2 : ∗2 ∉ S2 := by
  rintro ⟨p, hp, e⟩
  have := key2 hp (coeff_one_lt one_lt_two2) (by rw [e, eval_one, _root_.mul_one])
  exact one_ne_zero this

-- helper: IsGroup.mul_eq_of_lt' without hz and hyx (b + w < y ≤ z replaces hz; hyx only fed the recursion)
theorem mulEqGen {x y z w : Ordinal.{u}}
    (hx : IsGroup (∗x)) (hy : IsGroup (∗y)) (hyz : y ≤ z) (hwy : w < y)
    (H : ∀ a < y, (∗a)⁻¹ < ∗z) (H' : ∀ ⦃a b⦄, a < x → b < z → ∗a * ∗b < ∗x) :
    x * w = val (∗x * ∗w) := by
  apply le_antisymm
  · apply le_of_forall_lt_imp_ne
    rw [forall_lt_mul]
    intro a ha b hb
    rw [ne_eq, ← of_eq_iff, hx.mul_add_eq_of_lt' hb,
      mulEqGen hx hy hyz (ha.trans hwy) H H', _root_.add_comm, CharTwo.add_eq_iff_eq_add,
      of_val, ← _root_.mul_add]
    obtain hwa | hwa := eq_or_ne (∗w + ∗a) 0
    · cases ha.ne' (Nimber.add_eq_zero.1 hwa)
    · rw [← _root_.div_eq_iff hwa]
      exact (H' hb (H _ (hy.add_lt hwy (ha.trans hwy)))).ne
  · rw [val_le_iff]
    refine mul_le_of_forall_ne fun a ha b hb ↦ ?_
    rw [_root_.add_comm, ← _root_.add_assoc, ← _root_.mul_add, _root_.add_comm]
    cases b with | of b
    rw [of.lt_iff_lt] at hb
    have hbw : ∗b + ∗w < ∗z := (hy.add_lt (hb.trans hwy) hwy).trans_le hyz
    have hx' : val (a * (∗b + ∗w)) < x := H' ha hbw
    rw [← of_val (_ * _), ← mulEqGen hx hy hyz (hb.trans hwy) H H',
      ← of_val (a * _), ← hx.mul_add_eq_of_lt' hx']
    exact (Ordinal.mul_add_lt hx' hb).ne
termination_by w

-- helpers: F2/F4 arithmetic (from W2c1)
theorem two_add_one : ∗2 + 1 = (∗3 : Nimber.{0}) := by
  have := IsGroup.two.add_eq_of_lt (y := 1) (by simp)
  rw [← this]; simp; norm_num
theorem two_ne_one : (∗2 : Nimber.{0}) ≠ 1 := by
  rw [← of_one, Ne, of.eq_iff_eq]; exact_mod_cast (show (2:ℕ) ≠ 1 by decide)
theorem two_ne_zero' : (∗2 : Nimber.{0}) ≠ 0 := IsGroup.two.ne_zero
theorem two_lt_three : (∗2 : Nimber.{0}) < ∗3 := by
  rw [of.lt_iff_lt]; exact_mod_cast (show (2:ℕ) < 3 by decide)
theorem three_lt_four : (∗3 : Nimber.{0}) < ∗4 := by
  rw [of.lt_iff_lt]; exact_mod_cast (show (3:ℕ) < 4 by decide)
theorem three_ne : (∗3 : Nimber.{0}) ≠ 0 ∧ (∗3 : Nimber.{0}) ≠ 1 ∧ (∗3 : Nimber.{0}) ≠ ∗2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (IsGroup.two.zero_lt.trans two_lt_three).ne'
  · rw [← of_one, Ne, of.eq_iff_eq]; exact_mod_cast (show (3:ℕ) ≠ 1 by decide)
  · rw [Ne, of.eq_iff_eq]; exact_mod_cast (show (3:ℕ) ≠ 2 by decide)
theorem lt_three {y : Nimber.{0}} (h : y < ∗3) : y = 0 ∨ y = 1 ∨ y = ∗2 := by
  rcases lt_or_ge y (∗2) with h2 | h2
  · rcases lt_two_iff.1 h2 with h | h <;> simp [h]
  · right; right
    apply le_antisymm _ h2
    cases y with | of y
    rw [of.lt_iff_lt] at h; rw [of.le_iff_le]
    have h3 : (3:Ordinal) = 2 + 1 := by norm_num
    rw [h3] at h; exact Order.lt_add_one_iff.1 h
theorem two_mul_two : ∗2 * ∗2 = (∗3 : Nimber.{0}) := by
  apply le_antisymm
  · apply mul_le_of_forall_ne
    intro a ha b hb
    rcases lt_two_iff.1 ha with rfl | rfl <;> rcases lt_two_iff.1 hb with rfl | rfl
    · simp; exact three_ne.1.symm
    · simp
    · simp
    · simp only [_root_.one_mul, _root_.mul_one, CharTwo.add_self_eq_zero, _root_.zero_add]
      exact three_ne.2.1.symm
  · by_contra hlt
    rcases lt_three (not_le.1 hlt) with h | h | h
    · exact two_ne_zero' (mul_self_eq_zero.1 h)
    · have : (∗2 + 1) * (∗2 + 1) = (0 : Nimber.{0}) := by
        calc (∗2 + 1) * (∗2 + 1) = ∗2 * ∗2 + (∗2 + ∗2) + 1 := by ring
          _ = 0 := by rw [h, CharTwo.add_self_eq_zero, _root_.add_zero, CharTwo.add_self_eq_zero]
      have := mul_self_eq_zero.1 this
      exact two_ne_one (Nimber.add_eq_zero.1 this)
    · exact two_ne_one (mul_left_cancel₀ two_ne_zero' (h.trans (_root_.mul_one _).symm))
theorem three_sq : (∗3 : Nimber.{0}) ^ 2 = ∗2 := by
  rw [← two_add_one, sq]
  calc (∗2 + 1) * (∗2 + 1) = ∗2 * ∗2 + (∗2 + ∗2) + (1 : Nimber.{0}) := by ring
    _ = ∗2 := by
      rw [two_mul_two, CharTwo.add_self_eq_zero, _root_.add_zero, ← two_add_one, _root_.add_assoc,
        CharTwo.add_self_eq_zero, _root_.add_zero]
theorem sq_inj {a b : Nimber.{0}} (h : a ^ 2 = b ^ 2) : a = b := by
  rw [← sqrt_sq a, h, sqrt_sq]
theorem four_ne_three : (∗4 : Nimber.{0}) ≠ ∗3 := three_lt_four.ne'
theorem sqrt_two : √(∗2 : Nimber.{0}) = ∗3 := by rw [← three_sq, sqrt_sq]
-- helper: the field closure of succ 0 is ∗2
theorem fc0 : fieldClosure (succ (0 : Nimber.{0})) = ∗2 := by
  apply le_antisymm
  · rw [IsField.two.fieldClosure_le_iff]
    exact Order.succ_le_of_lt IsGroup.two.pos
  · exact (IsField.fieldClosure _).toIsRing.two_le
theorem pow0 : (∗(val (fieldClosure (succ (0 : Nimber.{0}))) ^ 2 ^ 0) : Nimber.{0}) = ∗2 := by
  rw [fc0]; simp
theorem pow1 : (∗(val (fieldClosure (succ (0 : Nimber.{0}))) ^ 2 ^ (0 + 1)) : Nimber.{0}) = ∗4 := by
  rw [fc0]; simp only [val_of, zero_add, pow_one]
  exact congrArg of (by exact_mod_cast (show (2:ℕ) ^ 2 = 4 by norm_num))
theorem noRoot {x r : Nimber.{0}} {p : Nimber.{0}[X]} (e : leastNoRoots x = p) (hr : r < x) :
    ¬ p.IsRoot r := by
  have ht : leastNoRoots x ≠ ⊤ := by rw [e]; exact WithTop.coe_ne_top
  have := not_isRoot_leastNoRoots_of_lt ht hr
  convert this
  simp [e]

-- helper: ∗(T²) is not a ring (the ring closure of succ T is ∗(T^ω) > ∗(T²))
theorem notRingT2 : ¬ IsRing (∗(val T ^ 2)) := fun hf => by
  have h1 : T < ∗(val T ^ 2) := val_lt_iff.1 (lt_self_pow₀ hT.one_lt_val one_lt_two)
  have h2 := hf.ringClosure_le_iff.2 (Order.succ_le_of_lt h1)
  rw [hT.ringClosure_eq] at h2
  have h3 : val T ^ (2 : ℕ) < val T ^ ω := by
    rw [← opow_natCast]
    exact (opow_lt_opow_iff_right hT.one_lt_val).2 (natCast_lt_omega0 2)
  exact absurd h2 (not_le.2 (by simpa using h3))

end T1c0
open Nimber Polynomial Ordinal Order Set T1c0

-- `Nimber.IsRing.mul_eq_of_lt` idx 7: necessary (x = y = R = ∗(T^ω), z = T)
theorem t_1 : ¬ drop0% Nimber.IsRing.mul_eq_of_lt 7 := fun h =>
  RT_ne ((@h R R T hR hR.toIsGroup le_rfl T_lt_R).trans R_mul_T)

-- `Nimber.IsRing.toIsField_of_X_sq_lt_leastNoRoots` idx 2: necessary (x = R)
theorem t_2 : ¬ drop0% Nimber.IsRing.toIsField_of_X_sq_lt_leastNoRoots 2 := fun h =>
  notFieldR (@h R hR)

-- `Nimber.IsRing.mul_eq_of_lt'` idx 7: necessary (x = y = R, z = T as ordinals)
theorem t_3 : ¬ drop0% Nimber.IsRing.mul_eq_of_lt' 7 := fun h => by
  have e := @h (val R) (val R) (val T) hR hR.toIsGroup le_rfl T_lt_R
  apply RT_ne
  rw [e]; simpa using R_mul_T

-- `Nimber.IsField.mul_eq_of_lt` idx 4: necessary (x = y = R, z = T)
theorem t_4 : ¬ drop0% Nimber.IsField.mul_eq_of_lt 4 := fun h =>
  RT_ne ((@h R R T hR le_rfl T_lt_R).trans R_mul_T)

-- `Nimber.IsField.mul_eq_of_lt'` idx 4: necessary (x = y = R, z = T as ordinals)
theorem t_5 : ¬ drop0% Nimber.IsField.mul_eq_of_lt' 4 := fun h => by
  have e := @h (val R) (val R) (val T) hR le_rfl T_lt_R
  apply RT_ne
  rw [e]; simpa using R_mul_T

-- `Nimber.IsRing.inv_lt_of_not_isField` idx 4: necessary (x = R, y = T)
theorem t_6 : ¬ drop0% Nimber.IsRing.inv_lt_of_not_isField 4 := fun h =>
  Tinv_not_lt (@h R T hR notFieldR)

-- `Nimber.IsRing.inv_le_of_not_isField` idx 4: necessary (x = R, y = T + 1)
theorem t_7 : ¬ drop0% Nimber.IsRing.inv_le_of_not_isField 4 := fun h =>
  absurd (@h R (T + 1) hR notFieldR) (not_le.2 R_lt_T1inv)

-- `Nimber.IsRing.inv_lt_of_not_isField` idx 2: necessary (x = T + 1, y = T)
theorem t_8 : ¬ drop0% Nimber.IsRing.inv_lt_of_not_isField 2 := fun h => by
  have := @h (T + 1) T notFieldT1 (T_lt_R.trans R_lt_T1inv)
  rw [Tinv] at this
  exact lt_asymm this T1_lt_R

-- `Nimber.IsRing.inv_le_of_not_isField` idx 2: necessary (x = T + 1, y = T)
theorem t_9 : ¬ drop0% Nimber.IsRing.inv_le_of_not_isField 2 := fun h => by
  have := @h (T + 1) T notFieldT1 (T_lt_R.trans R_lt_T1inv).le
  rw [Tinv] at this
  exact absurd this (not_le.2 T1_lt_R)

-- `Nimber.IsRing.mul_eq_of_lt` idx 5: removable (H forces y ≤ x: if x < y then x⁻¹ < x < y and x = (x⁻¹)⁻¹ < x)
theorem t_10 : drop% Nimber.IsRing.mul_eq_of_lt 5 := by
  intro x y z hx hy hzy H
  have hyx : y ≤ x := by
    by_contra hc
    rw [not_le] at hc
    have h1 := H x hc
    have h2 := H x⁻¹ (h1.trans hc)
    rw [inv_inv] at h2
    exact lt_irrefl _ h2
  exact hx.mul_eq_of_lt hy hyx hzy H

-- `Nimber.IsRing.mul_eq_of_lt'` idx 5: removable (as for the Nimber version)
theorem t_11 : drop% Nimber.IsRing.mul_eq_of_lt' 5 := by
  intro x y z hx hy hzy H
  have hyx : y ≤ x := by
    by_contra hc
    rw [not_le] at hc
    have h1 := H x hc
    have h2 := H (val (∗x)⁻¹) (h1.trans hc)
    rw [of_val, inv_inv] at h2
    exact lt_irrefl _ h2
  exact hx.mul_eq_of_lt' hy hyx hzy H

-- `Nimber.isLowerSet_subringClosure` idx 1: necessary (s = {T}: ∗2 < T is not an F2-polynomial in T)
theorem t_12 : ¬ drop0% Nimber.isLowerSet_subringClosure 1 := fun h =>
  two_notMem_S2 (closure_le_S2 (@h {T} T (∗2) two_lt_T.le (Subring.subset_closure (Set.mem_singleton T))))

-- `Nimber.isLowerSet_subfieldClosure` idx 1: necessary (s = {T}: ∗2 < T is not in F2(T))
theorem t_13 : ¬ drop0% Nimber.isLowerSet_subfieldClosure 1 := fun h => by
  have h2 := @h {T} T (∗2) two_lt_T.le (Subfield.subset_closure (Set.mem_singleton T))
  obtain ⟨y, hy, z, hz, e⟩ := Subfield.mem_closure_iff.1 h2
  obtain ⟨p, hp, ep⟩ := closure_le_S2 hy
  obtain ⟨q, hq, eq⟩ := closure_le_S2 hz
  rw [← ep, ← eq] at e
  by_cases hz0 : eval T q = 0
  · rw [hz0, _root_.div_zero] at e
    exact absurd e.symm (by simp)
  · have e' : eval T p = ∗2 * eval T q := by rw [← e, div_mul_cancel₀ _ hz0]
    exact hz0 (by rw [key2 hp hq e', eval_zero])

-- `Nimber.IsGroup.mul_eq_of_lt'` idx 6: removable (hz is only used for b + w < z, which follows from hy and hyz)
theorem t_14 : drop% Nimber.IsGroup.mul_eq_of_lt' 6 := by
  intro x y z w hx hy hyx hyz hwy H H'
  exact mulEqGen hx hy hyz hwy H H'

-- `Nimber.IsGroup.mul_eq_of_lt'` idx 7: removable (hyx is only passed to the recursive calls)
theorem t_15 : drop% Nimber.IsGroup.mul_eq_of_lt' 7 := by
  intro x y z w hx hy hz hyz hwy H H'
  exact mulEqGen hx hy hyz hwy H H'

-- `Nimber.IsGroup.mul_eq_of_lt` idx 6: removable (as for the Ordinal version)
theorem t_16 : drop% Nimber.IsGroup.mul_eq_of_lt 6 := by
  intro x y z w hx hy hyx hyz hwy H H'
  exact mulEqGen hx hy hyz hwy H H'

-- `Nimber.IsGroup.mul_eq_of_lt` idx 7: removable (as for the Ordinal version)
theorem t_17 : drop% Nimber.IsGroup.mul_eq_of_lt 7 := by
  intro x y z w hx hy hz hyz hwy H H'
  exact mulEqGen hx hy hyz hwy H H'

-- `Nimber.IsGroup.mul_eq_of_lt` idx 10: necessary (x = y = z = R, w = T)
theorem t_18 : ¬ drop0% Nimber.IsGroup.mul_eq_of_lt 10 := fun h =>
  RT_ne ((@h R R R T hR.toIsGroup hR.toIsGroup hR.toIsGroup le_rfl le_rfl T_lt_R
    (fun _ _ ha hb => hR.mul_lt ha hb)).trans R_mul_T)

-- `Nimber.IsGroup.mul_eq_of_lt'` idx 10: necessary (x = y = z = R, w = T as ordinals)
theorem t_19 : ¬ drop0% Nimber.IsGroup.mul_eq_of_lt' 10 := fun h => by
  have e := @h (val R) (val R) (val R) (val T) hR.toIsGroup hR.toIsGroup hR.toIsGroup le_rfl le_rfl
    T_lt_R (fun _ _ ha hb => hR.mul_lt ha hb)
  apply RT_ne
  rw [e]; simpa using R_mul_T

-- `Nimber.IsAlgClosed.leastNoRoots_fieldClosure_succ_pow_two_pow_succ` idx 1: necessary (t = 0, n = 0: ∗3 is a root of X² + ∗2 below ∗4)
theorem t_20 : ¬ drop0% Nimber.IsAlgClosed.leastNoRoots_fieldClosure_succ_pow_two_pow_succ 1 := fun h => by
  have e := @h 0 0
  rw [pow1, pow0] at e
  apply noRoot e three_lt_four
  simp [three_sq]

-- `Nimber.IsAlgClosed.fieldClosure_succ_pow_two_pow_succ_pow_two` idx 1: necessary (t = 0, n = 0: ∗4² ≠ ∗2 = ∗3²)
theorem t_21 : ¬ drop0% Nimber.IsAlgClosed.fieldClosure_succ_pow_two_pow_succ_pow_two 1 := fun h => by
  have e := @h 0 0
  rw [pow1, pow0, ← three_sq] at e
  exact four_ne_three (sq_inj e)

-- `Nimber.IsAlgClosed.sqrt_fieldClosure_succ_pow_two_pow` idx 1: necessary (t = 0, n = 0: √∗2 = ∗3 ≠ ∗4)
theorem t_22 : ¬ drop0% Nimber.IsAlgClosed.sqrt_fieldClosure_succ_pow_two_pow 1 := fun h => by
  have e := @h 0 0
  rw [pow1, pow0, sqrt_two] at e
  exact four_ne_three e.symm

-- `_private.CombinatorialGames.Nimber.SmallDegree.Inseparable.0.Nimber.IsAlgClosed.sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux` idx 1: necessary (t = 0, n = 0: ∗2 < ∗4 is not √ of anything below ∗2)
theorem t_23 : ¬ drop0% _private.CombinatorialGames.Nimber.SmallDegree.Inseparable.«0».Nimber.IsAlgClosed.sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux 1 := fun h => by
  have e := @h 0 0
  rw [pow1, pow0] at e
  have h2 : (∗2 : Nimber.{0}) ∈ Set.Iio (∗4) := two_lt_three.trans three_lt_four
  rw [← e] at h2
  obtain ⟨a, ha, ha2⟩ := h2
  have : a = ∗3 := by rw [← sq_sqrt a, ha2, sq, two_mul_two]
  rw [this] at ha
  exact lt_asymm ha two_lt_three

-- `Nimber.IsAlgClosed.enumField_add_omega0` idx 3: necessary (t = T, x = 0: enumField ω = ∗ω < T < ∗(F^ω))
theorem t_24 : ¬ drop0% Nimber.IsAlgClosed.enumField_add_omega0 3 := fun h => by
  have e := @h T hT 0
  rw [zero_add, enumField_omega0] at e
  have h1 : (1 : Nimber.{0}) < fieldClosure (succ T) := (IsField.fieldClosure _).one_lt
  have h2 : T < fieldClosure (succ T) := (lt_succ T).trans_le (le_fieldClosure _)
  have h3 : fieldClosure (succ T) < ∗(val (fieldClosure (succ T)) ^ ω) :=
    val_lt_iff.1 (left_lt_opow h1 one_lt_omega0)
  rw [← e] at h3
  exact absurd (hT.omega0_le.trans_lt (h2.trans h3)) (lt_irrefl _)

-- `Nimber.IsField.sq_of_pow_four` idx 2: necessary (x = T algebraically closed; ∗(T²) is not a ring)
theorem t_25 : ¬ drop0% Nimber.IsField.sq_of_pow_four 2 := fun h =>
  notRingT2 (@h T hT.toIsField).toIsRing

-- `Nimber.IsGroup.mul_eq_of_lt'` idx 8: removable (H forces y ≤ z: if z < y then (∗z)⁻¹ < ∗z, so z = ((∗z)⁻¹)⁻¹ < z)
theorem t_26 : drop% Nimber.IsGroup.mul_eq_of_lt' 8 := by
  intro x y z w hx hy hz hyx hwy H H'
  have hyz : y ≤ z := by
    by_contra hc
    rw [not_le] at hc
    have h1 : val (∗z)⁻¹ < z := H z hc
    have h2 := H (val (∗z)⁻¹) (h1.trans hc)
    rw [of_val, inv_inv] at h2
    exact lt_irrefl _ h2
  exact mulEqGen hx hy hyz hwy H H'

-- `Nimber.IsGroup.mul_eq_of_lt` idx 8: removable (as for the Ordinal version)
theorem t_27 : drop% Nimber.IsGroup.mul_eq_of_lt 8 := by
  intro x y z w hx hy hz hyx hwy H H'
  have hyz : y ≤ z := by
    by_contra hc
    rw [not_le] at hc
    have h1 := H z hc
    have h2 := H z⁻¹ (h1.trans hc)
    rw [inv_inv] at h2
    exact lt_irrefl _ h2
  exact mulEqGen hx hy hyz hwy H H'

namespace T1c0
open Nimber Polynomial Ordinal Order Set

theorem add_one_le_succ' (a : Nimber.{0}) : a + 1 ≤ succ a := by
  induction a using WellFoundedLT.induction with | ind a IH =>
  apply add_le_of_forall_ne
  · intro a' ha' e
    have := (IH a' ha').trans_lt (Order.succ_lt_succ ha')
    rw [e] at this
    exact lt_irrefl _ this
  · intro b' hb' e
    have hb0 : b' = 0 := by
      rcases Nimber.le_one_iff.1 hb'.le with h | h
      · exact h
      · exact absurd h hb'.ne
    rw [hb0, _root_.add_zero] at e
    exact (Order.lt_succ a).ne e

theorem T1_succ : T + 1 = succ T :=
  le_antisymm (add_one_le_succ' T) (Order.succ_le_of_lt T_lt_T1)

-- helper: the ring generated by R and everything below it (Laurent polynomials in T)
noncomputable def X1 : Nimber.{0} := ringClosure (succ R)
theorem hX1 : IsRing X1 := IsRing.ringClosure _
theorem R_lt_X1 : R < X1 := (lt_succ R).trans_le (le_ringClosure _)
theorem TR : T * R = 1 := by rw [← Tinv]; exact mul_inv_cancel₀ hT.ne_zero

-- helper: Laurent polynomials in T with coefficients below T
noncomputable def LS : Subring Nimber.{0} where
  carrier := {y | ∃ p : Nimber[X], ∃ n : ℕ, (∀ k, p.coeff k < T) ∧ y = eval T p * R ^ n}
  zero_mem' := ⟨0, 0, coeff_zero_lt hT.ne_zero, by simp⟩
  one_mem' := ⟨1, 0, coeff_one_lt one_lt_T, by simp⟩
  add_mem' := by
    rintro _ _ ⟨p, n, hp, rfl⟩ ⟨q, m, hq, rfl⟩
    refine ⟨p * X ^ m + q * X ^ n, n + m, hT.toIsGroup.coeff_add_lt
      (hT.toIsRing.coeff_mul_lt hp (coeff_X_pow_lt _ one_lt_T))
      (hT.toIsRing.coeff_mul_lt hq (coeff_X_pow_lt _ one_lt_T)), ?_⟩
    simp only [eval_add, eval_mul, eval_pow, eval_X]
    have e1 : T ^ m * R ^ m = 1 := by rw [← mul_pow, TR, one_pow]
    have e2 : T ^ n * R ^ n = 1 := by rw [← mul_pow, TR, one_pow]
    calc eval T p * R ^ n + eval T q * R ^ m
        = eval T p * R ^ n * (T ^ m * R ^ m) + eval T q * R ^ m * (T ^ n * R ^ n) := by
          rw [e1, e2, _root_.mul_one, _root_.mul_one]
      _ = (eval T p * T ^ m + eval T q * T ^ n) * R ^ (n + m) := by ring
  mul_mem' := by
    rintro _ _ ⟨p, n, hp, rfl⟩ ⟨q, m, hq, rfl⟩
    exact ⟨p * q, n + m, hT.toIsRing.coeff_mul_lt hp hq, by rw [eval_mul, pow_add]; ring⟩
  neg_mem' := by
    rintro _ ⟨p, n, hp, rfl⟩
    exact ⟨p, n, hp, by simp⟩

theorem Iio_le_LS : Set.Iio (succ R) ⊆ LS := by
  intro y hy
  rw [Set.mem_Iio, Order.lt_succ_iff] at hy
  rcases hy.lt_or_eq with hy | rfl
  · obtain ⟨p, hpc, hp⟩ := eq_oeval_of_lt_opow_omega0 hy
    exact ⟨p, 0, hpc, by rw [← hp, ← hT.eval_eq_of_lt hpc]; simp⟩
  · exact ⟨1, 1, coeff_one_lt one_lt_T, by simp⟩

theorem lt_X1_mem {a : Nimber.{0}} (ha : a < X1) : a ∈ LS := by
  have : a ∈ (Subring.closure (Set.Iio (succ R)) : Set Nimber.{0}) := by
    rw [coe_subringClosure_Iio]; exact ha
  exact Subring.closure_le.2 Iio_le_LS this

theorem T1inv_notMem : (T + 1)⁻¹ ∉ LS := by
  rintro ⟨p, n, hp, e⟩
  have hT1 : T + 1 ≠ 0 := fun h => (one_lt_T.ne') (Nimber.add_eq_zero.1 h)
  have e2 : T ^ n = (T + 1) * eval T p := by
    have := congrArg (fun y => (T + 1) * y * T ^ n) e
    rw [mul_inv_cancel₀ hT1, _root_.one_mul] at this
    rw [this, _root_.mul_assoc, _root_.mul_assoc, ← mul_pow, _root_.mul_comm R T, TR, one_pow,
      _root_.mul_one]
  have hc : ∀ k, (X ^ n + (X + 1) * p).coeff k < T :=
    hT.toIsGroup.coeff_add_lt (coeff_X_pow_lt _ one_lt_T)
      (hT.toIsRing.coeff_mul_lt (hT.toIsGroup.coeff_add_lt (coeff_X_lt one_lt_T)
        (coeff_one_lt one_lt_T)) hp)
  have h0 : oeval T (X ^ n + (X + 1) * p) = 0 := by
    rw [← hT.eval_eq_of_lt hc]
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_one]
    rw [e2]; exact CharTwo.add_self_eq_zero _
  rw [oeval_eq_zero_iff hT.ne_zero] at h0
  have := congrArg (eval 1) h0
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_one, one_pow, CharTwo.add_self_eq_zero,
    MulZeroClass.zero_mul, _root_.add_zero, eval_zero] at this
  exact one_ne_zero this

theorem T1_lt_X1 : T + 1 < X1 := T1_lt_R.trans R_lt_X1
theorem notFieldX1 : ¬ IsField X1 := fun h => T1inv_notMem (lt_X1_mem (h.inv_lt T1_lt_X1))
theorem X1inv : X1⁻¹ = T + 1 := by
  apply le_antisymm
  · by_contra h
    rw [not_le] at h
    exact T1inv_notMem (lt_X1_mem (hX1.inv_lt_of_not_isField notFieldX1 h))
  · rw [T1_succ]
    apply Order.succ_le_of_lt
    by_contra h
    rw [not_lt] at h
    rcases h.lt_or_eq with h | h
    · have := hT.toIsField.inv_lt h
      rw [inv_inv] at this
      exact lt_asymm this (T_lt_R.trans R_lt_X1)
    · have := congrArg (·⁻¹) h
      simp only [inv_inv, Tinv] at this
      exact R_lt_X1.ne' this
theorem X1_mul_T : X1 * T = 1 + X1 := by
  have h1 : X1 * (T + 1) = 1 := by rw [← X1inv]; exact mul_inv_cancel₀ hX1.ne_zero
  calc X1 * T = X1 * (T + 1) + X1 := by
        rw [_root_.mul_add, _root_.mul_one, _root_.add_assoc, CharTwo.add_self_eq_zero, _root_.add_zero]
    _ = 1 + X1 := by rw [h1]
theorem X1T_ne : ∗(val X1 * val T) ≠ 1 + X1 := by
  rw [_root_.add_comm, ← hX1.toIsGroup.add_eq_of_lt hX1.one_lt]
  intro e
  have e' : val X1 * val T = val X1 + 1 := by simpa using congrArg val e
  have h2 : val X1 * 2 ≤ val X1 * val T := by
    gcongr; exact (show (2 : Ordinal) ≤ val T from two_lt_T.le)
  have h3 : val X1 + 1 < val X1 + val X1 := (add_lt_add_iff_left (val X1)).2 hX1.one_lt_val
  rw [Ordinal.mul_two] at h2
  rw [e'] at h2
  exact absurd h2 (not_le.2 h3)
theorem HX1 : ∀ a < T + 1, a⁻¹ < X1 := by
  intro a ha
  rw [T1_succ, Order.lt_succ_iff] at ha
  rcases ha.lt_or_eq with ha | rfl
  · exact (hT.toIsField.inv_lt ha).trans (T_lt_R.trans R_lt_X1)
  · rw [Tinv]; exact R_lt_X1

end T1c0
open Nimber Polynomial Ordinal Order Set T1c0

-- `Nimber.IsRing.mul_eq_of_lt` idx 4: necessary (x = X1 = ringClosure (succ R), Laurent polynomials in T, with X1⁻¹ = T + 1; y = T + 1, z = T)
theorem t_39 : ¬ drop0% Nimber.IsRing.mul_eq_of_lt 4 := fun h =>
  X1T_ne ((@h X1 (T + 1) T hX1 T1_lt_X1.le T_lt_T1 HX1).trans X1_mul_T)

-- `Nimber.IsRing.mul_eq_of_lt'` idx 4: necessary (ordinals x = val X1, y = val (T + 1), z = val T)
theorem t_40 : ¬ drop0% Nimber.IsRing.mul_eq_of_lt' 4 := fun h => by
  have e := @h (val X1) (val (T + 1)) (val T) hX1 T1_lt_X1.le T_lt_T1 HX1
  apply X1T_ne
  rw [e]; simpa using X1_mul_T

-- `Nimber.IsGroup.mul_eq_of_lt` idx 5: necessary (x = z = X1, y = T + 1, w = T)
theorem t_41 : ¬ drop0% Nimber.IsGroup.mul_eq_of_lt 5 := fun h =>
  X1T_ne ((@h X1 (T + 1) X1 T hX1.toIsGroup hX1.toIsGroup T1_lt_X1.le T1_lt_X1.le T_lt_T1 HX1
    (fun _ _ ha hb => hX1.mul_lt ha hb)).trans X1_mul_T)

-- `Nimber.IsGroup.mul_eq_of_lt'` idx 5: necessary (ordinals x = z = val X1, y = val (T + 1), w = val T)
theorem t_42 : ¬ drop0% Nimber.IsGroup.mul_eq_of_lt' 5 := fun h => by
  have e := @h (val X1) (val (T + 1)) (val X1) (val T) hX1.toIsGroup hX1.toIsGroup T1_lt_X1.le
    T1_lt_X1.le T_lt_T1 HX1 (fun _ _ ha hb => hX1.mul_lt ha hb)
  apply X1T_ne
  rw [e]; simpa using X1_mul_T

namespace T1c0
universe u
open Nimber Polynomial Ordinal Order Set

theorem u_two_ne_one : (∗2 : Nimber.{u}) ≠ 1 := by
  rw [← of_one, Ne, of.eq_iff_eq]; exact_mod_cast (show (2:ℕ) ≠ 1 by decide)
theorem u_two_ne_zero : (∗2 : Nimber.{u}) ≠ 0 := IsGroup.two.ne_zero
theorem u_two_lt_three : (∗2 : Nimber.{u}) < ∗3 := by
  rw [of.lt_iff_lt]; exact_mod_cast (show (2:ℕ) < 3 by decide)
theorem u_lt_three {y : Nimber.{u}} (h : y < ∗3) : y = 0 ∨ y = 1 ∨ y = ∗2 := by
  rcases lt_or_ge y (∗2) with h2 | h2
  · rcases lt_two_iff.1 h2 with h | h <;> simp [h]
  · right; right
    apply le_antisymm _ h2
    cases y with | of y
    rw [of.lt_iff_lt] at h; rw [of.le_iff_le]
    have h3 : (3:Ordinal) = 2 + 1 := by norm_num
    rw [h3] at h; exact Order.lt_add_one_iff.1 h
theorem u_two_add_one : ∗2 + 1 = (∗3 : Nimber.{u}) := by
  have := IsGroup.two.add_eq_of_lt (y := 1) (by simp)
  rw [← this]; simp; norm_num
-- helper: ∗2 * ∗2 is not below ∗3
theorem u_two_sq_not_lt : ¬ (∗2 * ∗2 : Nimber.{u}) < ∗3 := fun hlt => by
  rcases u_lt_three hlt with h | h | h
  · exact u_two_ne_zero (mul_self_eq_zero.1 h)
  · have : (∗2 + 1) * (∗2 + 1) = (0 : Nimber.{u}) := by
      calc (∗2 + 1) * (∗2 + 1) = ∗2 * ∗2 + (∗2 + ∗2) + (1 : Nimber.{u}) := by ring
        _ = 0 := by rw [h, CharTwo.add_self_eq_zero, _root_.add_zero, CharTwo.add_self_eq_zero]
    have := mul_self_eq_zero.1 this
    exact u_two_ne_one (Nimber.add_eq_zero.1 this)
  · exact u_two_ne_one (mul_left_cancel₀ u_two_ne_zero (h.trans (_root_.mul_one _).symm))

-- helper: nim addition of 1 is at most the successor
theorem add_one_le_succ (a : Nimber.{u}) : a + 1 ≤ succ a := by
  induction a using WellFoundedLT.induction with | ind a IH =>
  apply add_le_of_forall_ne
  · intro a' ha' e
    have := (IH a' ha').trans_lt (Order.succ_lt_succ ha')
    rw [e] at this
    exact lt_irrefl _ this
  · intro b' hb' e
    have hb0 : b' = 0 := by
      rcases Nimber.le_one_iff.1 hb'.le with h | h
      · exact h
      · exact absurd h hb'.ne
    rw [hb0, _root_.add_zero] at e
    exact (Order.lt_succ a).ne e

-- helper: X² ≤ leastNoRoots x makes Iio x closed under division
theorem divCl {x a b : Nimber.{u}} (h' : (.some (X ^ 2) : WithTop Nimber.{u}[X]) ≤ leastNoRoots x)
    (ha : a < x) (hb : b < x) (ha0 : a ≠ 0) : b / a < x := by
  have hd : (C a * X + C b).degree = 1 := degree_linear ha0
  have h0 : (0 : Nimber.{u}) < x := bot_lt_iff_ne_bot.2 (ne_bot_of_gt ha)
  have hc : ∀ k, (C a * X + C b).coeff k < x := by
    intro k
    rcases k with _ | _ | k <;> simp [coeff_C, coeff_X, ha, hb, h0]
  have hlt : ((C a * X + C b : Nimber.{u}[X]) : WithTop Nimber.{u}[X]) < leastNoRoots x :=
    lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Lex.lt_X_pow_iff.2 (by rw [hd]; decide))) h'
  obtain ⟨r, hr, hroot⟩ := exists_root_of_lt_leastNoRoots (by rw [hd]; decide) hc hlt
  have e : a * r + b = 0 := by simpa using hroot
  rw [Nimber.add_eq_zero] at e
  have : r = b / a := by rw [← e, mul_div_cancel_left₀ _ ha0]
  rw [← this]; exact hr

-- helper: 1 < x and X² ≤ leastNoRoots x make x a field
theorem fieldOf {x : Nimber.{u}} (h1 : 1 < x)
    (h' : (.some (X ^ 2) : WithTop Nimber.{u}[X]) ≤ leastNoRoots x) : IsField x := by
  have h0 : (0 : Nimber.{u}) < x := bot_lt_iff_ne_bot.2 (ne_bot_of_gt h1)
  have hm : ∀ {a b : Nimber.{u}}, a < x → b < x → a * b < x := fun {a b} ha hb => by
    by_cases hb0 : b = 0
    · rw [hb0, MulZeroClass.mul_zero]; exact h0
    have hi : b⁻¹ < x := by simpa using divCl h' hb h1 hb0
    simpa using divCl h' hi ha (inv_ne_zero hb0)
  have claim : ∀ {y z : Nimber.{u}}, y < x → z < x → y ≠ 0 → x ≤ y + z → z / y = x + 1 := by
    intro y z hy hz hy0 hxyz
    have hc := divCl h' hy hz hy0
    have h2 : x ≤ 1 + z / y := by
      by_contra hlt
      rw [not_le] at hlt
      have := hm hy hlt
      rw [_root_.mul_add, _root_.mul_one, mul_div_cancel₀ _ hy0] at this
      exact absurd hxyz (not_le.2 this)
    have h3 : 1 + z / y ≤ succ (z / y) := by rw [_root_.add_comm]; exact add_one_le_succ _
    have e : x = 1 + z / y := le_antisymm h2 (h3.trans (Order.succ_le_of_lt hc))
    rw [e, _root_.add_comm 1, _root_.add_assoc, CharTwo.add_self_eq_zero, _root_.add_zero]
  have hgrp : IsGroup x := by
    refine ⟨fun y z hy hz => ?_, h0.ne'⟩
    by_contra hyz
    rw [not_lt] at hyz
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [_root_.zero_add] at hyz
      exact absurd hz (not_lt.2 hyz)
    set c := x + 1 with hc_def
    have hxc : 1 + c = x := by
      rw [hc_def, _root_.add_comm x 1, ← _root_.add_assoc, CharTwo.add_self_eq_zero, _root_.zero_add]
    have bad : ∀ {y z : Nimber.{u}}, y < x → z < x → y ≠ 0 → x ≤ y + z → z = c * y := by
      intro y z hy hz hy0 h
      rw [← claim hy hz hy0 h, div_mul_cancel₀ _ hy0]
    have hcx : c < x := by rw [← claim hy hz hy0 hyz]; exact divCl h' hy hz hy0
    have hc0 : c ≠ 0 := by
      intro e; rw [hc_def, Nimber.add_eq_zero] at e; exact h1.ne' e
    have h2x : ∗2 ≤ x := by rw [← succ_one]; exact Order.succ_le_of_lt h1
    have h2x' : ∗2 < x := by
      refine lt_of_le_of_ne h2x fun e => ?_
      rw [← e] at hy hz hyz
      rcases lt_two_iff.1 hy with rfl | rfl <;> rcases lt_two_iff.1 hz with rfl | rfl <;>
        simp at hyz
    obtain ⟨u, hu, hu0, hu1, huc⟩ : ∃ u < x, u ≠ 0 ∧ u ≠ 1 ∧ u ≠ c := by
      by_cases hc2 : c = ∗2
      · exfalso
        have hx3 : x = ∗3 := by rw [← hxc, hc2, _root_.add_comm, u_two_add_one]
        exact u_two_sq_not_lt (hx3 ▸ hm h2x' h2x')
      · exact ⟨∗2, h2x', u_two_ne_zero, u_two_ne_one, fun e => hc2 e.symm⟩
    have hv : 1 + u < x := by
      by_contra h
      rw [not_lt] at h
      have := bad h1 hu one_ne_zero h
      exact huc (by simpa using this)
    have hv1 : 1 + u ≠ 1 := fun e => hu0 (by
      have := congrArg (· + 1) e
      simpa [_root_.add_comm 1 u, _root_.add_assoc, CharTwo.add_self_eq_zero] using this)
    have hv0 : 1 + u ≠ 0 := fun e => hu1 (Nimber.add_eq_zero.1 e).symm
    have hw : (1 + u) + c < x := by
      by_contra h
      rw [not_lt] at h
      have := bad hv hcx hv0 h
      exact hv1 (mul_left_cancel₀ hc0 (by rw [_root_.mul_one]; exact this.symm))
    have hsum : u + ((1 + u) + c) = x := by
      rw [← hxc]
      calc u + (1 + u + c) = (u + u) + (1 + c) := by ring
        _ = 1 + c := by rw [CharTwo.add_self_eq_zero, _root_.zero_add]
    have hcu := bad hu hw hu0 hsum.ge
    have : u * x = 1 * x := by
      rw [← hxc, _root_.mul_add, _root_.mul_one, _root_.mul_comm u c, ← hcu, hsum, hxc, _root_.one_mul]
    exact hu1 (mul_right_cancel₀ h0.ne' this)
  have hring : IsRing x := ⟨hgrp, fun _ _ ha hb => hm ha hb, h1.ne'⟩
  exact hring.toIsField_of_X_sq_lt_leastNoRoots h'

-- helper: the X ^ 2 condition from a power
theorem sqLe {x : Nimber.{u}} {n : ℕ} (hn : 2 ≤ n)
    (h' : (.some (X ^ n) : WithTop Nimber.{u}[X]) ≤ leastNoRoots x) :
    (.some (X ^ 2) : WithTop Nimber.{u}[X]) ≤ leastNoRoots x :=
  (WithTop.coe_le_coe.2 (Lex.X_pow_le_X_pow_iff.2 hn)).trans h'

-- helper: eval = oeval without the ring hypothesis
theorem evalGen {n : ℕ} {x : Nimber.{u}}
    (h' : (.some (X ^ n) : WithTop Nimber.{u}[X]) ≤ leastNoRoots x) {p : Nimber.{u}[X]}
    (hpn : p.degree < n) (hpk : ∀ k, p.coeff k < x) : p.eval x = oeval x p := by
  rcases le_or_gt x 1 with hx | hx
  · rw [polynomial_eq_zero_of_le_one hx hpk]; simp
  by_cases h2 : (.some (X ^ 2) : WithTop Nimber.{u}[X]) ≤ leastNoRoots x
  · exact (fieldOf hx h2).toIsRing.eval_eq_of_lt h' hpn hpk
  · have hlt : (.some (X ^ n) : WithTop Nimber.{u}[X]) < .some (X ^ 2) := h'.trans_lt (not_le.1 h2)
    have hn : n < 2 := Lex.X_pow_lt_X_pow_iff.1 (WithTop.coe_lt_coe.1 hlt)
    have hp : p.degree ≤ 0 := by
      have : p.degree < 1 := hpn.trans_le (by exact_mod_cast Nat.lt_succ_iff.1 hn)
      exact Nat.WithBot.lt_one_iff_le_zero.1 this
    rw [eq_C_of_degree_le_zero hp, eval_C, oeval_C]

-- helper: pow_mul_eq without the ring hypothesis
theorem pmeGen {n : ℕ} {x y : Nimber.{u}}
    (h' : (.some (X ^ (n + 1)) : WithTop Nimber.{u}[X]) ≤ leastNoRoots x) (hy : y < x) :
    x ^ n * y = ∗(x.val ^ n * y.val) := by
  rcases le_or_gt x 1 with hx | hx
  · have hy0 : y = 0 := by
      rcases Nimber.le_one_iff.1 (hy.le.trans hx) with h | h
      · exact h
      · exact absurd (h ▸ hy) (not_lt.2 hx)
    subst hy0; simp
  cases n with
  | zero => simp
  | succ m => exact (fieldOf hx (sqLe (by omega) h')).toIsRing.pow_mul_eq h' hy

end T1c0
open Nimber Polynomial Ordinal Order Set T1c0

-- `Nimber.IsRing.eval_eq_of_lt` idx 2: removable (X ^ 2 ≤ leastNoRoots x with 1 < x forces a field; otherwise p is constant or 0)
theorem t_28 : drop% Nimber.IsRing.eval_eq_of_lt 2 := by
  intro n x h' p hpn hpk
  exact evalGen h' hpn hpk

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.0.Nimber.IsField.eval_eq_of_lt` idx 2: removable (as for the IsRing version)
theorem t_29 : drop% _private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.«0».Nimber.IsField.eval_eq_of_lt 2 := by
  intro n x h' p hpn hpk
  exact evalGen h' hpn hpk

-- `Nimber.IsRing.pow_mul_eq` idx 3: removable (x ≤ 1 forces y = 0; n = 0 trivial; else X ^ 2 ≤ leastNoRoots x gives a field)
theorem t_30 : drop% Nimber.IsRing.pow_mul_eq 3 := by
  intro n x y h' hy
  exact pmeGen h' hy

-- `Nimber.IsRing.pow_eq` idx 2: removable (as for pow_mul_eq, with y = 1; x ≤ 1 by cases)
theorem t_31 : drop% Nimber.IsRing.pow_eq 2 := by
  intro n x h'
  obtain hx | hx := le_or_gt x 1
  · rcases Nimber.le_one_iff.1 hx with rfl | rfl
    · cases n <;> simp
    · simp
  · simpa using pmeGen h' hx

-- `Nimber.IsField.sqrt_lt` idx 2: removable (x ≤ 1 forces y = 0; else X ^ 2 ≤ X ^ 2 + C y < leastNoRoots x gives a field)
theorem t_32 : drop% Nimber.IsField.sqrt_lt 2 := by
  intro x y hy hx
  rcases le_or_gt x 1 with h1 | h1
  · have hy0 : y = 0 := by
      rcases Nimber.le_one_iff.1 (hy.le.trans h1) with h | h
      · exact h
      · exact absurd (h ▸ hy) (not_lt.2 h1)
    subst hy0; simpa using hy
  · have h2 : (.some (X ^ 2) : WithTop Nimber[X]) ≤ leastNoRoots x := by
      refine le_trans ?_ hx.le
      rw [WithTop.coe_le_coe, Lex.X_pow_le_iff, degree_X_pow_add_C two_pos]
    exact (fieldOf h1 h2).sqrt_lt hy hx

-- `Nimber.IsField.X_pow_five_lt_leastNoRoots_of_X_pow_four_le_leastNoRoots` idx 1: removable (x ≤ 1 gives ⊤; else a field)
theorem t_33 : drop% Nimber.IsField.X_pow_five_lt_leastNoRoots_of_X_pow_four_le_leastNoRoots 1 := by
  intro x hl
  rcases le_or_gt x 1 with h1 | h1
  · rw [leastNoRoots_of_le_one h1]; exact WithTop.coe_lt_top _
  · exact (fieldOf h1 (sqLe (by omega) hl)).X_pow_five_lt_leastNoRoots_of_X_pow_four_le_leastNoRoots hl

-- `Nimber.IsField.leastNoRoots_lt_X_pow_four_of_leastNoRoots_le_X_pow_five` idx 1: removable (contrapositive of the previous row)
theorem t_34 : drop% Nimber.IsField.leastNoRoots_lt_X_pow_four_of_leastNoRoots_le_X_pow_five 1 := by
  intro x hl
  by_contra h
  rw [not_lt] at h
  rcases le_or_gt x 1 with h1 | h1
  · rw [leastNoRoots_of_le_one h1] at hl; exact absurd hl (not_le.2 (WithTop.coe_lt_top _))
  · exact absurd hl (not_le.2
      ((fieldOf h1 (sqLe (by omega) h)).X_pow_five_lt_leastNoRoots_of_X_pow_four_le_leastNoRoots h))

-- `Nimber.IsField.degree_leastNoRoots_ne_four` idx 1: removable (degree 4 gives X ^ 2 < leastNoRoots x, hence a field)
theorem t_35 : drop% Nimber.IsField.degree_leastNoRoots_ne_four 1 := by
  intro x ht hd
  rcases le_or_gt x 1 with h1 | h1
  · exact ht (leastNoRoots_of_le_one h1)
  · have h2 := X_pow_lt_leastNoRoots_of_le_degree (n := 2) ht (by rw [hd]; decide)
    exact (fieldOf h1 h2.le).degree_leastNoRoots_ne_four ht hd

-- `Nimber.IsField.natDegree_leastNoRoots_ne_four` idx 1: removable (as for the degree version)
theorem t_36 : drop% Nimber.IsField.natDegree_leastNoRoots_ne_four 1 := by
  intro x ht hd
  rcases le_or_gt x 1 with h1 | h1
  · exact ht (leastNoRoots_of_le_one h1)
  · have h2 := X_pow_lt_leastNoRoots_of_le_degree (n := 2) ht
      (by rw [degree_eq_natDegree (leastNoRoots_ne_zero' ht), hd]; decide)
    exact (fieldOf h1 h2.le).natDegree_leastNoRoots_ne_four ht hd

-- `Nimber.IsField.root_lt` idx 2: removable (x ≤ 1 forces p = 0; X ^ 2 ≤ leastNoRoots x with 1 < x gives a field; otherwise p is linear and its only root is the root below x)
theorem t_37 : drop% Nimber.IsField.root_lt 2 := by
  intro x r p hpn hpk hr
  have hp0 : p ≠ 0 := Polynomial.ne_zero_of_mem_roots hr
  rcases le_or_gt x 1 with h1 | h1
  · exact absurd (polynomial_eq_zero_of_le_one h1 hpk) hp0
  by_cases h2 : (.some (X ^ 2) : WithTop Nimber[X]) ≤ leastNoRoots x
  · exact (fieldOf h1 h2).root_lt hpn hpk hr
  · have hlt : (p : WithTop Nimber[X]) < .some (X ^ 2) := hpn.trans (not_le.1 h2)
    have hd : p.degree < 2 := Lex.lt_X_pow_iff.1 (WithTop.coe_lt_coe.1 hlt)
    have hroot : p.IsRoot r := (mem_roots hp0).1 hr
    by_cases hd0 : p.degree = 0
    · have hc := eq_C_of_degree_eq_zero hd0
      rw [hc] at hroot
      simp only [IsRoot.def, eval_C] at hroot
      exact absurd (by rw [hc, hroot, C_0]) hp0
    · have hd1 : p.degree = 1 := by
        rw [degree_eq_natDegree hp0] at hd hd0 ⊢
        norm_cast at hd hd0 ⊢
        omega
      obtain ⟨s, hs, hsr⟩ := exists_root_of_lt_leastNoRoots hd0 hpk hpn
      have ha : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
      have hp := eq_X_add_C_of_degree_eq_one hd1
      rw [hp] at hroot hsr
      simp only [IsRoot.def, eval_add, eval_mul, eval_C, eval_X] at hroot hsr
      rw [Nimber.add_eq_zero] at hroot hsr
      have : p.leadingCoeff * r = p.leadingCoeff * s := by rw [hroot, hsr]
      rw [mul_left_cancel₀ ha this]
      exact hs

-- `Nimber.IsField.degree_leastNoRoots_le_of_isField_pow` idx 3: removable (x ≤ 1 and n = 0 make ∗(x ^ n) ≤ 1; if X ^ 2 ≤ leastNoRoots x then x is a field, otherwise leastNoRoots x has degree < 2 ≤ n)
theorem t_38 : drop% Nimber.IsField.degree_leastNoRoots_le_of_isField_pow 3 := by
  intro x n hn hxn
  have hone := hxn.one_lt
  rcases le_or_gt x 1 with h1 | h1
  · exfalso
    rcases Nimber.le_one_iff.1 h1 with rfl | rfl <;> cases n <;> simp at hone
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have : n = 0 := by omega
    subst this; simp at hone
  by_cases h2 : (.some (X ^ 2) : WithTop Nimber[X]) ≤ leastNoRoots x
  · exact (fieldOf h1 h2).degree_leastNoRoots_le_of_isField_pow hn hxn
  · have hlt := not_le.1 h2
    have ht : leastNoRoots x ≠ ⊤ := ne_top_of_lt hlt
    refine ⟨ht, ?_⟩
    have hd : ((leastNoRoots x).untop ht).degree < 2 := by
      rw [← WithTop.coe_untop _ ht, WithTop.coe_lt_coe, Lex.lt_X_pow_iff] at hlt
      exact_mod_cast hlt
    exact hd.le.trans (by exact_mod_cast hn2)
