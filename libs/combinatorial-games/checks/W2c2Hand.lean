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

namespace W2c2
open Nimber Polynomial

theorem lt23 : (∗2 : Nimber) < ∗3 := by rw [of.lt_iff_lt]; exact_mod_cast (show (2:ℕ) < 3 by decide)

theorem two_add_one : ∗2 + 1 = ∗3 := by
  have := IsGroup.two.add_eq_of_lt (y := 1) (by simp)
  rw [← this]; simp; norm_num

theorem notGroup3 : ¬ IsGroup (∗3) := by
  intro h
  have := h.add_lt (y := ∗2) (z := 1) lt23 (by simp)
  rw [two_add_one] at this; exact lt_irrefl _ this

theorem notField3 : ¬ IsField (∗3) := fun h => notGroup3 h.toIsGroup

theorem one_lt_two' : (1 : Nimber) < ∗2 := by simp

theorem two_ne_one : (∗2 : Nimber) ≠ 1 := one_lt_two'.ne'

theorem lt3 {r : Nimber} (h : r < ∗3) : r = 0 ∨ r = 1 ∨ r = ∗2 := by
  rcases lt_or_ge r (∗2) with h2 | h2
  · rcases lt_two_iff.1 h2 with h | h <;> simp [h]
  · right; right
    apply le_antisymm _ h2
    have h3 : val r < 3 := by simpa using val.lt_iff_lt.2 h
    have h2' : (2 : Ordinal) ≤ val r := by simpa using val.le_iff_le.2 h2
    have : val r ≤ 2 := Order.le_of_lt_succ (by rwa [Order.succ_eq_add_one, show (2:Ordinal)+1 = 3 by norm_num])
    have e : val r = 2 := le_antisymm this h2'
    rw [← of_val r, e]

theorem sq_two_ne_one : ∗2 * ∗2 ≠ (1 : Nimber) := by
  intro e
  have h0 : (∗2 + 1) * (∗2 + 1) = (0 : Nimber) := by
    have : (∗2 + 1) * (∗2 + 1) = ∗2 * ∗2 + (∗2 + ∗2) + (1 : Nimber) := by ring
    rw [this, e, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  rw [mul_self_eq_zero, two_add_one] at h0
  exact absurd h0 (by simp)

theorem coeffC_lt (c x : Nimber) (k : ℕ) (hc : c < x) : (C c).coeff k < x := by
  rw [coeff_C]; split_ifs
  · exact hc
  · exact lt_of_le_of_lt _root_.zero_le hc

theorem notXleC (a : Nimber) : ¬ (X : Nimber[X]) ≤ C a := fun h => by
  have := (Lex.degree_mono h).trans degree_C_le
  rw [degree_X] at this; exact absurd this (by decide)

end W2c2

open Nimber Polynomial W2c2

-- `Polynomial.monomial_induction`
theorem c_1 : ¬ drop0% Polynomial.monomial_induction 3 := fun h =>
  @h ℕ _ (fun _ => False) (fun _ _ _ _ h => h) 0

-- `Polynomial.monomial_induction`
theorem c_2 : ¬ drop0% Polynomial.monomial_induction 4 := fun h =>
  X_ne_zero (@h ℕ _ (fun p => p = 0) rfl X)

-- `Polynomial.eq_add_C_mul_X_pow_of_degree_le`
theorem c_3 : ¬ drop0% Polynomial.eq_add_C_mul_X_pow_of_degree_le 4 := fun h => by
  obtain ⟨a, q, e, hq⟩ := @h ℕ _ (X ^ 2) 0
  have hq2 : q.coeff 2 = 0 := coeff_eq_zero_of_degree_lt (hq.trans (by norm_num))
  have := congrArg (fun p : ℕ[X] => p.coeff 2) e
  simp [hq2, coeff_C] at this

-- `WithBot.le_zero_iff`
theorem c_4 : ¬ drop0% WithBot.le_zero_iff 3 := fun h => by
  have := (@h ℤ _ _ ((-1 : ℤ) : WithBot ℤ)).1 (by exact_mod_cast (show (-1 : ℤ) ≤ 0 by decide))
  rcases this with h | h <;> simp at h

-- `WithBot.add_pos_of_pos_of_nonneg`
theorem c_5 : ¬ drop0% WithBot.add_pos_of_pos_of_nonneg 6 := fun h => by
  have := @h ℕ _ _ _ 0 0 le_rfl
  simp at this

-- `WithBot.add_pos_of_pos_of_nonneg`
theorem c_6 : ¬ drop0% WithBot.add_pos_of_pos_of_nonneg 7 := fun h => by
  have := @h ℤ _ _ _ ((1 : ℤ) : WithBot ℤ) ((-1 : ℤ) : WithBot ℤ) (by exact_mod_cast (show (0:ℤ) < 1 by decide))
  rw [← WithBot.coe_add] at this
  norm_num at this

-- `Nimber.polynomial_eq_zero_of_le_one`
theorem c_7 : ¬ drop0% Nimber.polynomial_eq_zero_of_le_one 2 := fun h => by
  have := @h (∗2) 1 (fun k => coeffC_lt 1 _ k one_lt_two')
  exact one_ne_zero this

-- `Nimber.IsRing.eval_lt`
theorem c_8 : ¬ drop0% Nimber.IsRing.eval_lt 4 := fun h => by
  have := @h (∗2) 0 IsRing.two (C (∗2)) (by simp)
  simp at this

-- `Nimber.IsRing.eval_lt`
theorem c_9 : ¬ drop0% Nimber.IsRing.eval_lt 5 := fun h => by
  have := @h (∗2) (∗2) IsRing.two X (fun k => by rcases k with _ | _ | k <;> simp [coeff_X])
  simp at this

-- `Nimber.IsGroup.coeff_add_lt`
theorem c_10 : ¬ drop0% Nimber.IsGroup.coeff_add_lt 3 := fun h => by
  have := @h (∗3) (C 1) (C (∗2)) (fun k => coeffC_lt _ _ k (by simpa using lt_trans one_lt_two' lt23))
    (fun k => coeffC_lt _ _ k lt23) 0
  simp at this
  rw [add_comm, two_add_one] at this; exact lt_irrefl _ this

-- `Nimber.IsGroup.coeff_add_lt`
theorem c_11 : ¬ drop0% Nimber.IsGroup.coeff_add_lt 4 := fun h => by
  have := @h (∗2) (C (∗2)) 0 IsGroup.two (by simp) 0
  simp at this

-- `Nimber.IsGroup.coeff_add_lt`
theorem c_12 : ¬ drop0% Nimber.IsGroup.coeff_add_lt 5 := fun h => by
  have := @h (∗2) 0 (C (∗2)) IsGroup.two (by simp) 0
  simp at this

-- `Nimber.IsGroup.coeff_sum_lt`
theorem c_13 : ¬ drop0% Nimber.IsGroup.coeff_sum_lt 5 := fun h => by
  have := @h 1 Unit (fun _ => C 1) {()} IsGroup.one 0
  simp at this

-- `Nimber.IsRing.coeff_mul_lt`
theorem c_14 : ¬ drop0% Nimber.IsRing.coeff_mul_lt 3 := fun h => by
  have := @h (∗3) (C (∗2)) (C (∗2)) (fun k => coeffC_lt _ _ k lt23) (fun k => coeffC_lt _ _ k lt23) 0
  rw [← C_mul, coeff_C_zero] at this
  rcases lt3 this with e | e | e
  · simp at e
  · exact sq_two_ne_one e
  · have : (∗2 : Nimber.{0}) = 1 := by
      have := congrArg (· * (∗2 : Nimber)⁻¹) e
      simpa using this
    exact two_ne_one this

-- `Nimber.IsRing.coeff_mul_lt`
theorem c_15 : ¬ drop0% Nimber.IsRing.coeff_mul_lt 4 := fun h => by
  have := @h (∗2) (C (∗2)) 1 IsRing.two (fun k => coeffC_lt _ _ k one_lt_two') 0
  simp at this

-- `Nimber.IsRing.coeff_mul_lt`
theorem c_16 : ¬ drop0% Nimber.IsRing.coeff_mul_lt 5 := fun h => by
  have := @h (∗2) 1 (C (∗2)) IsRing.two (fun k => coeffC_lt _ _ k one_lt_two') 0
  simp at this

-- `Nimber.IsRing.coeff_prod_lt`
theorem c_17 : ¬ drop0% Nimber.IsRing.coeff_prod_lt 4 := fun h => by
  have := @h 1 Unit (fun _ => 0) ∅ (by simp) 0
  simp at this

-- `Nimber.IsRing.coeff_prod_lt`
theorem c_18 : ¬ drop0% Nimber.IsRing.coeff_prod_lt 5 := fun h => by
  have := @h (∗2) Unit (fun _ => C (∗2)) {()} IsRing.two 0
  simp at this

-- `Nimber.IsField.coeff_embed`
theorem c_19 : ¬ indep0% Nimber.IsField.coeff_embed 1 := fun h =>
  notField3 (@h (∗3) 0 (by simp) 0)

-- `Nimber.IsField.coeff_embed`
theorem c_20 : ¬ indep0% Nimber.IsField.coeff_embed 3 := fun h => by
  have := @h (∗2) IsField.two (C (∗2)) 0 0
  simp at this

-- `Nimber.IsField.degree_embed`
theorem c_21 : ¬ indep0% Nimber.IsField.degree_embed 1 := fun h =>
  notField3 (@h (∗3) 0 (by simp))

-- `Nimber.IsField.degree_embed`
theorem c_22 : ¬ indep0% Nimber.IsField.degree_embed 3 := fun h => by
  have := @h (∗2) IsField.two (C (∗2)) 0
  simp at this

-- `Nimber.IsField.leadingCoeff_embed`
theorem c_23 : ¬ indep0% Nimber.IsField.leadingCoeff_embed 1 := fun h =>
  notField3 (@h (∗3) 0 (by simp))

-- `Nimber.IsField.monic_embed`
theorem c_24 : ¬ indep0% Nimber.IsField.monic_embed 1 := fun h =>
  notField3 (@h (∗3) 0 (by simp))

-- `Nimber.IsField.monic_embed`
theorem c_25 : ¬ indep0% Nimber.IsField.monic_embed 3 := fun h => by
  have := @h (∗2) IsField.two (C (∗2)) 0
  simp at this

-- `Nimber.IsField.map_embed`
theorem c_26 : ¬ indep0% Nimber.IsField.map_embed 1 := fun h =>
  notField3 (@h (∗3) 0 (by simp))

-- `Nimber.IsField.map_embed`
theorem c_27 : ¬ indep0% Nimber.IsField.map_embed 3 := fun h => by
  have := @h (∗2) IsField.two (C (∗2)) 0
  simp at this

-- `Nimber.IsField.embed_C`
theorem c_28 : ¬ indep0% Nimber.IsField.embed_C 1 := fun h =>
  notField3 (@h (∗3) 0 (by simp))

-- `Nimber.IsField.embed_C`
theorem c_29 : ¬ indep0% Nimber.IsField.embed_C 3 := fun h => by
  have := @h (∗2) IsField.two (∗2) 0
  simp at this

-- `Nimber.IsField.eval_embed`
theorem c_30 : ¬ indep0% Nimber.IsField.eval_embed 1 := fun h =>
  notField3 (@h (∗3) 0 (by simp))

-- `Nimber.IsField.eval_embed`
theorem c_31 : ¬ indep0% Nimber.IsField.eval_embed 3 := fun h => by
  have := @h (∗2) IsField.two (C (∗2)) 0 0
  simp at this

-- `Nimber.Lex.X_pow_add_le`
theorem c_32 : ¬ drop0% Nimber.Lex.X_pow_add_le 3 := fun h => by
  have := Lex.degree_mono (@h 1 X monic_one)
  rw [natDegree_one, pow_zero, degree_one, _root_.add_comm, ← C_1, degree_X_add_C] at this
  exact absurd this (by decide)

-- `Nimber.Lex.succ_eq_add_one_of_coeff_zero`
theorem c_33 : ¬ drop0% Nimber.Lex.succ_eq_add_one_of_coeff_zero 1 := fun h => by
  have e := congrArg (fun p : Nimber[X] => p.coeff 0) (@h 1)
  simp at e

-- `Nimber.oeval_C_mul_X_pow_add`
theorem c_34 : ¬ drop0% Nimber.oeval_C_mul_X_pow_add 2 := fun h => by
  have e1 := @h 0 X (∗Ordinal.omega0) 1
  have e2 := oeval_C_mul_X_pow_add (n := 1) (p := C 1) (by simp) (∗Ordinal.omega0) 1
  have : C 1 * X ^ 0 + X = C (1 : Nimber) * X ^ 1 + C 1 := by
    rw [pow_zero, pow_one, mul_one, C_1, _root_.one_mul, _root_.add_comm]
  rw [this, e2] at e1
  simp at e1

-- `Nimber.oeval_lt_pow`
theorem c_35 : ¬ drop0% Nimber.oeval_lt_pow 4 := fun h => by
  have := @h (∗2) X 0 (coeff_X_lt one_lt_two')
  simp at this

-- `Nimber.oeval_lt_oeval`
theorem c_36 : ¬ drop0% Nimber.oeval_lt_oeval 3 := fun h => by
  have := @h 1 0 0 (by simp) (by simp)
  simp at this

-- `Nimber.oeval_lt_oeval`
theorem c_37 : ¬ drop0% Nimber.oeval_lt_oeval 4 := fun h => by
  have := @h (∗2) (C (∗3)) X (Lex.lt_of_degree_lt (by simp)) (coeff_X_lt one_lt_two')
  simp at this

-- `Nimber.oeval_le_oeval`
theorem c_39 : ¬ drop0% Nimber.oeval_le_oeval 3 := fun h => by
  have := @h (∗2) X 0 (coeff_X_lt one_lt_two') (by simp)
  simp at this

-- `Nimber.oeval_le_oeval`
theorem c_40 : ¬ drop0% Nimber.oeval_le_oeval 4 := fun h => by
  have := @h (∗2) (C (∗3)) X (Lex.lt_of_degree_lt (by simp)).le (coeff_X_lt one_lt_two')
  rw [oeval_C, oeval_X] at this
  exact not_le.2 lt23 this

-- `Nimber.oeval_lt_oeval_iff`
theorem c_42 : ¬ drop0% Nimber.oeval_lt_oeval_iff 3 := fun h => by
  have := @h (∗2) (C (∗3)) X (coeff_X_lt one_lt_two')
  rw [oeval_C, oeval_X] at this
  exact lt_asymm lt23 (this.2 (Lex.lt_of_degree_lt (by simp)))

-- `Nimber.oeval_lt_oeval_iff`
theorem c_43 : ¬ drop0% Nimber.oeval_lt_oeval_iff 4 := fun h => by
  have := @h (∗2) X (C (∗3)) (coeff_X_lt one_lt_two')
  rw [oeval_C, oeval_X] at this
  exact notXleC _ (this.1 lt23).le

-- `Nimber.oeval_le_oeval_iff`
theorem c_44 : ¬ drop0% Nimber.oeval_le_oeval_iff 3 := fun h => by
  have := @h (∗2) (C (∗3)) X (coeff_X_lt one_lt_two')
  rw [oeval_C, oeval_X] at this
  exact not_le.2 lt23 (this.2 (Lex.lt_of_degree_lt (by simp)).le)

-- `Nimber.oeval_le_oeval_iff`
theorem c_45 : ¬ drop0% Nimber.oeval_le_oeval_iff 4 := fun h => by
  have := @h (∗2) X (C (∗3)) (coeff_X_lt one_lt_two')
  rw [oeval_C, oeval_X] at this
  exact notXleC _ (this.1 lt23.le)

-- `Nimber.oeval_inj`
theorem c_46 : ¬ drop0% Nimber.oeval_inj 3 := fun h => by
  have := (@h (∗2) (C (∗2)) X (coeff_X_lt one_lt_two')).1 (by simp)
  exact absurd (congrArg natDegree this) (by simp)

-- `Nimber.oeval_inj`
theorem c_47 : ¬ drop0% Nimber.oeval_inj 4 := fun h => by
  have := (@h (∗2) X (C (∗2)) (coeff_X_lt one_lt_two')).1 (by simp)
  exact absurd (congrArg natDegree this) (by simp)

-- `Nimber.eq_oeval_of_lt_pow'`
theorem c_48 : ¬ drop0% Nimber.eq_oeval_of_lt_pow' 3 := fun h => by
  obtain ⟨p, -, hp, -⟩ := @h 0 0 0 (by simp)
  exact absurd (hp 0) (by simp)

-- `Nimber.eq_oeval_of_lt_pow'`
theorem c_49 : ¬ drop0% Nimber.eq_oeval_of_lt_pow' 4 := fun h => by
  obtain ⟨p, hd, -, he⟩ := @h 1 1 0 one_ne_zero
  have : p = 0 := by simpa using hd
  subst this
  simp at he

-- `Nimber.eq_oeval_of_lt_pow`
theorem c_50 : ¬ drop0% Nimber.eq_oeval_of_lt_pow 3 := fun h => by
  obtain ⟨p, -, hp, -⟩ := @h 0 0 0 (by simp)
  exact absurd (hp 0) (by simp)

-- `Nimber.eq_oeval_of_lt_pow`
theorem c_51 : ¬ drop0% Nimber.eq_oeval_of_lt_pow 4 := fun h => by
  obtain ⟨p, hd, -, he⟩ := @h 1 1 0 one_ne_zero
  have : p = 0 := by simpa using hd
  subst this
  simp at he

-- `Nimber.eq_oeval_of_lt_oeval`
theorem c_52 : ¬ drop0% Nimber.eq_oeval_of_lt_oeval 4 := fun h => by
  obtain ⟨q, -, hq, he⟩ := @h 1 1 (C (∗2)) one_ne_zero (by simp)
  have : q = 0 := polynomial_eq_zero_of_le_one le_rfl hq
  subst this
  simp at he

-- `Nimber.eq_oeval_of_lt_oeval`
theorem c_53 : ¬ drop0% Nimber.eq_oeval_of_lt_oeval 5 := fun h => by
  obtain ⟨q, hq, -, -⟩ := @h 1 0 0 one_ne_zero (by simp)
  obtain ⟨n, -, hn⟩ := hq
  simp at hn

-- `Nimber.forall_lt_oeval_iff`
theorem c_54 : ¬ drop0% Nimber.forall_lt_oeval_iff 3 := fun h => by
  have := (@h 1 (fun y => y = 0) (C (∗2))).2 (fun q _ hq => by
    rw [polynomial_eq_zero_of_le_one le_rfl hq]; simp) 1 (by simp)
  exact one_ne_zero this

namespace W2c2
open Nimber Polynomial

theorem two_lt_omega : (∗2 : Nimber) < ∗Ordinal.omega0 := by
  rw [of.lt_iff_lt]; simpa using Ordinal.natCast_lt_omega0 2

theorem acl : IsAlgClosed (∗Ordinal.omega 1) := IsAlgClosed.omega one_ne_zero

theorem two_lt_acl {c : Nimber} (hc : IsAlgClosed c) : (∗2 : Nimber) < c :=
  two_lt_omega.trans_le hc.omega0_le

theorem L2top : leastNoRoots (∗2) ≠ ⊤ := fun e =>
  absurd ((isAlgClosed_iff_leastNoRoots_eq_top IsRing.two).2 e).omega0_le (not_le.2 two_lt_omega)

theorem X2ltL2 : ((X ^ 2 : Nimber[X]) : WithTop Nimber[X]) < leastNoRoots (∗2) :=
  IsField.two.X_sq_lt_leastNoRoots

theorem eqL {x : Nimber} (ht : leastNoRoots x ≠ ⊤) : leastNoRoots x = ((leastNoRoots x).untop ht : WithTop Nimber[X]) :=
  (WithTop.coe_untop _ ht).symm

theorem CltL {x : Nimber} (ht : leastNoRoots x ≠ ⊤) (a : Nimber) : ((C a : Nimber[X]) : WithTop Nimber[X]) < leastNoRoots x := by
  rw [eqL ht, WithTop.coe_lt_coe]
  apply Lex.lt_of_degree_lt
  exact (degree_C_le).trans_lt (degree_leastNoRoots_pos ht)

theorem degL_ne {x : Nimber} (ht : leastNoRoots x ≠ ⊤) : ((leastNoRoots x).untop ht).degree ≠ 0 :=
  (degree_leastNoRoots_pos ht).ne'

theorem L2le : leastNoRoots (∗2) ≤ ((X ^ 2 + X + 1 : Nimber[X]) : WithTop Nimber[X]) := by
  apply leastNoRoots_le_of_not_isRoot
  · have : (X ^ 2 + X + 1 : Nimber[X]).degree = 2 := by compute_degree!
    rw [this]; decide
  · intro k; rcases k with _ | _ | _ | k <;> simp [coeff_X, coeff_one, coeff_X_pow]
  · intro r hr
    rcases lt_two_iff.1 hr with rfl | rfl
    · simp
    · simp [CharTwo.add_self_eq_zero]

theorem one_lt_three : (1 : Nimber) < ∗3 := one_lt_two'.trans lt23

theorem L3le : leastNoRoots (∗3) ≤ ((C (∗2) * X + 1 : Nimber[X]) : WithTop Nimber[X]) := by
  apply leastNoRoots_le_of_not_isRoot
  · have : (C (∗2) * X + 1 : Nimber[X]).degree = 1 := by compute_degree!
    rw [this]; decide
  · intro k; rcases k with _ | _ | k <;> simp [coeff_X, coeff_one, coeff_C, lt23, one_lt_three]
    exact_mod_cast (show (2:ℕ) < 3 by decide)
  · intro r hr
    rcases lt3 hr with rfl | rfl | rfl
    · simp
    · simp [two_add_one]
    · intro e; simp [IsRoot] at e
      have := congrArg (· + 1) e
      simp only [_root_.add_assoc, CharTwo.add_self_eq_zero, _root_.add_zero, _root_.zero_add] at this
      exact sq_two_ne_one this

theorem L3top : leastNoRoots (∗3) ≠ ⊤ := fun e => by
  have := L3le; rw [e] at this; exact WithTop.not_top_le_coe _ this

theorem L3deg : ((leastNoRoots (∗3)).untop L3top).degree ≤ 1 := by
  have := L3le
  rw [eqL L3top, WithTop.coe_le_coe] at this
  exact (Lex.degree_mono this).trans (by compute_degree)

theorem L2root : ∃ r, IsRoot ((leastNoRoots (∗2)).untop L2top) r :=
  _root_.IsAlgClosed.exists_root _ (degL_ne L2top)

theorem L2mem : ∃ r, r ∈ ((leastNoRoots (∗2)).untop L2top).roots := by
  obtain ⟨r, hr⟩ := L2root
  exact ⟨r, (mem_roots (leastNoRoots_ne_zero' L2top)).2 hr⟩

theorem noRootEmbed (hk) (s : IsField.two.toSubfield) :
    ¬ (IsField.two.embed ((leastNoRoots (∗2)).untop L2top) hk).IsRoot s := by
  intro hr
  rw [IsRoot, IsField.eval_embed] at hr
  have := congrArg Subtype.val hr
  exact not_isRoot_leastNoRoots_of_lt L2top s.2 this

end W2c2

open Nimber Polynomial W2c2

-- `Nimber.not_isRoot_leastNoRoots_of_lt`
theorem c_55 : ¬ drop0% Nimber.not_isRoot_leastNoRoots_of_lt 3 := fun h => by
  obtain ⟨r, hr⟩ := L2root
  exact @h (∗2) r L2top hr

-- `Nimber.leastNoRoots_of_le_one`
theorem c_56 : ¬ drop0% Nimber.leastNoRoots_of_le_one 1 := fun h => L2top (@h (∗2))

-- `Nimber.X_pow_lt_leastNoRoots_of_le_degree`
theorem c_57 : ¬ drop0% Nimber.X_pow_lt_leastNoRoots_of_le_degree 3 := fun h => by
  have := @h (∗2) (((leastNoRoots (∗2)).untop L2top).natDegree + 1) L2top
  rw [← WithTop.lt_untop_iff L2top] at this
  have h2 := (Lex.X_pow_le_iff.1 this.le).trans degree_le_natDegree
  have h3 : ((leastNoRoots (∗2)).untop L2top).natDegree + 1 ≤ ((leastNoRoots (∗2)).untop L2top).natDegree := by
    exact_mod_cast h2
  omega

-- `Nimber.leastNoRoots_le_of_not_isRoot`
theorem c_58 : ¬ drop0% Nimber.leastNoRoots_le_of_not_isRoot 2 := fun h => by
  have := X2ltL2.trans_le (@h (∗2) (C 1) (fun k => coeffC_lt _ _ k one_lt_two') (fun r _ => by simp))
  rw [WithTop.coe_lt_coe] at this
  exact lt_asymm this (Lex.lt_of_degree_lt (by simp))

-- `Nimber.leastNoRoots_le_of_not_isRoot`
theorem c_59 : ¬ drop0% Nimber.leastNoRoots_le_of_not_isRoot 4 := fun h => by
  have := X2ltL2.trans_le (@h (∗2) X (by simp) (coeff_X_lt one_lt_two'))
  rw [WithTop.coe_lt_coe] at this
  exact lt_asymm this (by simpa using (Lex.X_pow_lt_X_pow_iff (m := 1) (n := 2)).2 one_lt_two)

-- `Nimber.exists_root_of_lt_leastNoRoots`
theorem c_60 : ¬ drop0% Nimber.exists_root_of_lt_leastNoRoots 2 := fun h => by
  obtain ⟨r, -, hr⟩ := @h (∗2) (C 1) (fun k => coeffC_lt _ _ k one_lt_two') (CltL L2top 1)
  simp at hr

-- `Nimber.exists_root_of_lt_leastNoRoots`
theorem c_61 : ¬ drop0% Nimber.exists_root_of_lt_leastNoRoots 4 := fun h => by
  obtain ⟨r, hr, hroot⟩ := @h (∗2) _ (degL_ne L2top) (coeff_leastNoRoots_lt L2top)
  exact not_isRoot_leastNoRoots_of_lt L2top hr hroot

-- `Nimber.le_leastNoRoots_of_exists_isRoot`
theorem c_62 : ¬ drop0% Nimber.le_leastNoRoots_of_exists_isRoot 2 := fun h => by
  have := @h (∗2) (Order.succ ((leastNoRoots (∗2)).untop L2top))
  rw [← WithTop.le_untop_iff L2top] at this
  exact (Order.lt_succ _).not_ge this

-- `Nimber.IsField.exists_root_subfield`
theorem c_63 : ¬ drop0% Nimber.IsField.exists_root_subfield 3 := fun h => by
  obtain ⟨r, hr⟩ := @h (∗2) IsField.two 1 (by simpa using CltL L2top 1)
  simp at hr

-- `Nimber.IsField.exists_root_subfield`
theorem c_64 : ¬ drop0% Nimber.IsField.exists_root_subfield 4 := fun h => by
  obtain ⟨r, hr⟩ := @h (∗2) IsField.two (IsField.two.embed _ (coeff_leastNoRoots_lt L2top))
    (by rw [IsField.degree_embed]; exact degL_ne L2top)
  exact noRootEmbed _ r hr

-- `Nimber.IsField.splits_subfield`
theorem c_65 : ¬ drop0% Nimber.IsField.splits_subfield 3 := fun h => by
  have hs := @h (∗2) IsField.two (IsField.two.embed _ (coeff_leastNoRoots_lt L2top))
  obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero (by rw [IsField.degree_embed]; exact degL_ne L2top)
  exact noRootEmbed _ r hr

-- `Nimber.IsField.roots_eq_map`
theorem c_66 : ¬ indep0% Nimber.IsField.roots_eq_map 1 := fun h =>
  notField3 (@h (∗3) (C 0) (CltL L3top 0) (fun k => coeffC_lt _ _ k (by simp)))

-- `Nimber.IsField.roots_eq_map`
theorem c_67 : ¬ drop0% Nimber.IsField.roots_eq_map 3 := fun h => by
  obtain ⟨r, hr⟩ := L2mem
  have e := @h (∗2) IsField.two _ (coeff_leastNoRoots_lt L2top)
  rw [e, Multiset.mem_map] at hr
  obtain ⟨s, hs, -⟩ := hr
  exact noRootEmbed _ s (isRoot_of_mem_roots hs)

-- `Nimber.IsField.roots_eq_map`
theorem c_68 : ¬ indep0% Nimber.IsField.roots_eq_map 4 := fun h => by
  have := @h (∗2) IsField.two (C (∗2)) (CltL L2top _) 0
  simp at this

-- `Nimber.IsField.root_lt`
theorem c_70 : ¬ drop0% Nimber.IsField.root_lt 4 := fun h => by
  obtain ⟨r, hr⟩ := L2mem
  have := @h (∗2) r IsField.two _ (coeff_leastNoRoots_lt L2top) hr
  exact not_isRoot_leastNoRoots_of_lt L2top this (isRoot_of_mem_roots hr)

-- `Nimber.IsField.root_lt`
theorem c_71 : ¬ drop0% Nimber.IsField.root_lt 5 := fun h => by
  have hpn : ((X + C (∗2) : Nimber[X]) : WithTop Nimber[X]) < leastNoRoots (∗2) := by
    refine lt_trans ?_ X2ltL2
    rw [WithTop.coe_lt_coe, Lex.lt_X_pow_iff, degree_X_add_C]; decide
  have := @h (∗2) (∗2) IsField.two _ hpn ((mem_roots (X_add_C_ne_zero _)).2 (by simp [CharTwo.add_self_eq_zero]))
  exact lt_irrefl _ this

-- `Nimber.IsField.root_lt`
theorem c_72 : ¬ drop0% Nimber.IsField.root_lt 6 := fun h =>
  lt_irrefl _ (@h (∗2) (∗2) IsField.two (C 0) (CltL L2top 0) (fun k => coeffC_lt _ _ k (by simp)))

namespace W2c2
open Nimber Polynomial

theorem lin_lt_X2 : (C (∗2) * X + 1 : Nimber[X]) < X ^ 2 := by
  have : (C (∗2) * X + 1 : Nimber[X]).degree = 1 := by compute_degree!
  rw [Lex.lt_X_pow_iff, this]; decide

theorem L3natDeg : ((leastNoRoots (∗3)).untop L3top).natDegree = 1 :=
  le_antisymm (natDegree_le_of_degree_le L3deg) (one_le_natDegree_leastNoRoots L3top)

theorem acl2 : IsAlgClosed (∗Ordinal.omega 2) := IsAlgClosed.omega two_ne_zero

theorem acl_lt : (∗Ordinal.omega 1 : Nimber) < ∗Ordinal.omega 2 := by
  rw [of.lt_iff_lt]; exact Ordinal.omega_lt_omega.2 one_lt_two

end W2c2

open Nimber Polynomial W2c2

-- `Nimber.IsField.eq_prod_roots_of_lt_leastNoRoots`
-- removable: the nimbers are algebraically closed, so every polynomial splits
theorem c_73 : drop% Nimber.IsField.eq_prod_roots_of_lt_leastNoRoots 1 := by
  intros
  exact (C_leadingCoeff_mul_prod_multiset_X_sub_C _root_.IsAlgClosed.card_roots_eq_natDegree).symm

-- `Nimber.IsField.eq_prod_roots_of_lt_leastNoRoots`
-- removable: the nimbers are algebraically closed, so every polynomial splits
theorem c_74 : drop% Nimber.IsField.eq_prod_roots_of_lt_leastNoRoots 3 := by
  intros
  exact (C_leadingCoeff_mul_prod_multiset_X_sub_C _root_.IsAlgClosed.card_roots_eq_natDegree).symm

-- `Nimber.IsField.eq_prod_roots_of_lt_leastNoRoots`
-- removable: the nimbers are algebraically closed, so every polynomial splits
theorem c_75 : drop% Nimber.IsField.eq_prod_roots_of_lt_leastNoRoots 4 := by
  intros
  exact (C_leadingCoeff_mul_prod_multiset_X_sub_C _root_.IsAlgClosed.card_roots_eq_natDegree).symm

-- `Nimber.IsField.le_leastNoRoots_of_exists_isRoot`
theorem c_76 : ¬ drop0% Nimber.IsField.le_leastNoRoots_of_exists_isRoot 1 := fun h => by
  have := (@h (∗3) (X ^ 2) (fun q hq hd _ => by
    have h2 := Lex.lt_X_pow_iff.1 hq
    rw [WithBot.natCast_eq_coe, show (2:ℕ) = 1 + 1 from rfl, WithBot.coe_add_one, WithBot.lt_add_one] at h2
    exact absurd hd (not_lt.2 h2))).trans L3le
  rw [WithTop.coe_le_coe] at this
  exact not_le.2 lin_lt_X2 this

-- `Nimber.IsField.le_leastNoRoots_of_exists_isRoot`
theorem c_77 : ¬ drop0% Nimber.IsField.le_leastNoRoots_of_exists_isRoot 3 := fun h => by
  have := @h (∗2) IsField.two (Order.succ ((leastNoRoots (∗2)).untop L2top))
  rw [← WithTop.le_untop_iff L2top] at this
  exact (Order.lt_succ _).not_ge this

-- `Nimber.IsField.X_sq_lt_leastNoRoots`
theorem c_78 : ¬ drop0% Nimber.IsField.X_sq_lt_leastNoRoots 1 := fun h => by
  have := (@h (∗3)).trans_le L3le
  rw [WithTop.coe_lt_coe] at this
  exact lt_asymm this lin_lt_X2

-- `Nimber.IsField.one_lt_degree_leastNoRoots`
theorem c_79 : ¬ drop0% Nimber.IsField.one_lt_degree_leastNoRoots 1 := fun h =>
  not_lt.2 L3deg (@h (∗3) L3top)

-- `Nimber.IsField.one_lt_degree_leastNoRoots`
theorem c_80 : ¬ indep0% Nimber.IsField.one_lt_degree_leastNoRoots 2 := fun h =>
  @h _ acl.toIsField acl.leastNoRoots_eq_top

-- `Nimber.IsField.one_lt_natDegree_leastNoRoots`
theorem c_81 : ¬ drop0% Nimber.IsField.one_lt_natDegree_leastNoRoots 1 := fun h => by
  have := @h (∗3) L3top
  rw [L3natDeg] at this
  exact lt_irrefl _ this

-- `Nimber.IsField.one_lt_natDegree_leastNoRoots`
theorem c_82 : ¬ indep0% Nimber.IsField.one_lt_natDegree_leastNoRoots 2 := fun h =>
  @h _ acl.toIsField acl.leastNoRoots_eq_top

-- `Nimber.IsField.monic_leastNoRoots`
theorem c_84 : ¬ drop0% Nimber.IsField.monic_leastNoRoots 1 := fun h => by
  have e := (@h (∗3) L3top).eq_X_add_C L3natDeg
  apply not_isRoot_leastNoRoots_of_lt L3top (coeff_leastNoRoots_lt L3top 0)
  rw [IsRoot, e]
  simp [CharTwo.add_self_eq_zero]

-- `Nimber.IsField.monic_leastNoRoots`
theorem c_85 : ¬ indep0% Nimber.IsField.monic_leastNoRoots 2 := fun h =>
  @h _ acl.toIsField acl.leastNoRoots_eq_top

-- `Nimber.IsField.irreducible_embed_leastNoRoots`
theorem c_86 : ¬ indep0% Nimber.IsField.irreducible_embed_leastNoRoots 1 := fun h =>
  notField3 (@h (∗3) L3top)

-- `Nimber.IsField.irreducible_embed_leastNoRoots`
theorem c_87 : ¬ indep0% Nimber.IsField.irreducible_embed_leastNoRoots 2 := fun h =>
  @h _ acl.toIsField acl.leastNoRoots_eq_top

-- `Nimber.le_leastNoRoots_sSup`
theorem c_88 : ¬ drop0% Nimber.le_leastNoRoots_sSup 2 := fun h => by
  have := @h {∗2} ⊤
  rw [csSup_singleton, top_le_iff] at this
  exact L2top this

-- `Nimber.le_leastNoRoots_iSup`
theorem c_89 : ¬ drop0% Nimber.le_leastNoRoots_iSup 3 := fun h => by
  have := @h True (fun _ => ∗2) ⊤
  rw [ciSup_const, top_le_iff] at this
  exact L2top this

-- `RingEquiv.coe_subfieldCongr_apply`
theorem c_90 : ¬ ∀ {K : Type 1} [DivisionRing K] {s t : Subfield K} (_ : ↥s), s = t := fun h => by
  have e := @h Nimber.{0} _ ⊥ ⊤ 0
  have : (∗2 : Nimber) ∈ (⊥ : Subfield Nimber) := e ▸ Subfield.mem_top _
  rw [subfieldBot_eq, mem_toSubfield_iff] at this
  exact lt_irrefl _ this

-- `Nimber.IsAlgClosed.sqrt_eq`
theorem c_91 : ¬ drop0% Nimber.IsAlgClosed.sqrt_eq 1 := fun h => by
  have e := @h 0
  rw [sqrt_zero] at e
  have := le_fieldClosure (Order.succ (0 : Nimber))
  rw [← e] at this
  exact (Order.lt_succ (0 : Nimber)).not_ge this

-- `Nimber.IsAlgClosed.enumField_add_natCast_add_one`
theorem c_99 : ¬ drop0% Nimber.IsAlgClosed.enumField_add_natCast_add_one 3 := fun h => by
  have e1 := @h _ acl 0 0
  have e2 := @h _ acl2 0 0
  have e := e1.symm.trans e2
  simp only [pow_zero, pow_one, of_val] at e
  have h1 : fieldClosure (Order.succ (∗Ordinal.omega 1 : Nimber)) ≤ ∗Ordinal.omega 2 :=
    acl2.toIsField.fieldClosure_le_iff.2 (Order.succ_le_of_lt acl_lt)
  rw [e] at h1
  exact (Order.lt_succ _).not_ge ((le_fieldClosure _).trans h1)

-- `Polynomial.exists_irreducible_quadratic_or_cubic_of_irreducible_quartic`
theorem c_111 : ¬ ∀ {k : Type 1} [Field k] (p : Polynomial k), p.degree = 4 →
    ∃ q : Polynomial k, Irreducible q ∧ (q.degree = 2 ∨ q.degree = 3) := fun h => by
  obtain ⟨q, hq, hd⟩ := @h Nimber.{0} _ (X ^ 4) (degree_X_pow 4)
  rw [_root_.IsAlgClosed.degree_eq_one_of_irreducible Nimber hq] at hd
  rcases hd with hd | hd <;> exact absurd hd (by decide)

-- `Polynomial.exists_irreducible_quadratic_or_cubic_of_irreducible_quartic`
theorem c_112 : ¬ ∀ {k : Type 1} [Field k] (p : Polynomial k), Irreducible p →
    ∃ q : Polynomial k, Irreducible q ∧ (q.degree = 2 ∨ q.degree = 3) := fun h => by
  obtain ⟨q, hq, hd⟩ := @h Nimber.{0} _ X irreducible_X
  rw [_root_.IsAlgClosed.degree_eq_one_of_irreducible Nimber hq] at hd
  rcases hd with hd | hd <;> exact absurd hd (by decide)

-- `Nimber.IsField.degree_leastNoRoots_ne_four`
theorem c_114 : ¬ indep0% Nimber.IsField.degree_leastNoRoots_ne_four 2 := fun h =>
  @h _ acl.toIsField acl.leastNoRoots_eq_top

-- `Nimber.IsField.X_pow_five_lt_leastNoRoots_of_X_pow_four_le_leastNoRoots`
theorem c_117 : ¬ drop0% Nimber.IsField.X_pow_five_lt_leastNoRoots_of_X_pow_four_le_leastNoRoots 2 := fun h => by
  have := (@h (∗2) IsField.two).trans_le L2le
  rw [WithTop.coe_lt_coe] at this
  have h2 : (X ^ 2 + X + 1 : Nimber[X]).degree = 2 := by compute_degree!
  exact lt_asymm this (by rw [Lex.lt_X_pow_iff, h2]; decide)

-- `Nimber.IsField.leastNoRoots_lt_X_pow_four_of_leastNoRoots_le_X_pow_five`
theorem c_119 : ¬ drop0% Nimber.IsField.leastNoRoots_lt_X_pow_four_of_leastNoRoots_le_X_pow_five 2 := fun h => by
  have := @h _ acl.toIsField
  rw [acl.leastNoRoots_eq_top] at this
  exact not_top_lt this

section
open Order Ordinal

-- `Nimber.oeval_lt_oeval`
-- removable: the proof only uses the coefficient bound of the smaller polynomial
theorem c_38 : drop% Nimber.oeval_lt_oeval 5 := by
  intro x p q h hpk
  rw [Nimber.Lex.lt_def] at h
  obtain ⟨n, hnl, hnr⟩ := h
  have hx : 0 < x := (hpk 0).pos
  induction hk : p.natDegree - n using Nat.caseStrongRecOn generalizing p q with
  | zero =>
    rw [Nat.sub_eq_zero_iff_le] at hk
    apply (mul_coeff_le_oeval x q n).trans_lt'
    have hpn : Polynomial.degree (AddMonoidAlgebra.erase n p) < n := by
      apply lt_of_le_of_ne ((p.degree_erase_le n).trans
        (degree_le_natDegree.trans (WithBot.coe_mono hk)))
      intro hdd
      exact coeff_ne_zero_of_eq_degree hdd Finsupp.erase_same
    rw [← p.monomial_add_erase n, ← C_mul_X_pow_eq_monomial]
    rw [oeval_C_mul_X_pow_add hpn, of.lt_iff_lt]
    have hpe (k : Nat) : (p.erase n).coeff k < x := by
      rw [p.coeff_erase]
      split <;> simp [hpk, hx]
    apply (add_lt_add_right (val_lt_iff.2 (oeval_lt_pow hpe hpn)) _).trans_le
    rw [← mul_add_one]
    apply mul_le_mul_right
    rwa [add_one_le_iff, val.lt_iff_lt]
  | ind k ih =>
    have hp0 : p ≠ 0 := by rintro rfl; simp at hk
    have hq0 : q ≠ 0 := by rintro rfl; simp at hnr
    have hqd : n ≤ q.natDegree := by
      by_contra! hn
      apply coeff_eq_zero_of_natDegree_lt at hn
      simp [hn] at hnr
    have hpqd : p.natDegree ≤ q.natDegree := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      exact (hnl N (hqd.trans_lt hN)).trans (coeff_eq_zero_of_natDegree_lt hN)
    replace hqd : n < q.natDegree := by
      apply lt_of_le_of_ne hqd
      rintro rfl
      simp [hpqd] at hk
    replace hpqd : p.natDegree = q.natDegree := by
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hpqd
      rw [hnl _ hqd]
      simp [hq0]
    rw [← p.eraseLead_add_C_mul_X_pow, add_comm p.eraseLead,
      ← q.eraseLead_add_C_mul_X_pow, add_comm q.eraseLead]
    rw [oeval_C_mul_X_pow_add ((degree_eraseLead_lt hp0).trans_le degree_le_natDegree),
      oeval_C_mul_X_pow_add ((degree_eraseLead_lt hq0).trans_le degree_le_natDegree)]
    rw [hpqd, ← coeff_natDegree, hpqd, (hnl _ hqd), coeff_natDegree, of.lt_iff_lt,
      add_lt_add_iff_left, val.lt_iff_lt]
    by_cases hpe : p.eraseLead = 0
    · rw [hpe, oeval_zero]
      rw [← eraseLead_coeff_of_ne n (hqd.trans_eq hpqd.symm).ne, hpe, coeff_zero,
        ← eraseLead_coeff_of_ne n hqd.ne] at hnr
      have hqe : q.eraseLead ≠ 0 := fun h => by simp [h] at hnr
      apply (opow_natDegree_le_oeval x hqe).trans_lt'
      rw [← val_lt_iff, val_zero, ← Ordinal.opow_natCast]
      apply Ordinal.opow_pos
      rwa [← of_lt_iff, of_zero]
    apply ih (p.eraseLead.natDegree - n)
    · rw [Nat.sub_le_iff_le_add, ← Nat.lt_succ_iff,
        ← Nat.succ_add, ← hk, Nat.sub_add_cancel (hqd.le.trans_eq hpqd.symm)]
      exact p.eraseLead_natDegree_lt_or_eraseLead_eq_zero.resolve_right hpe
    · intro u
      rw [eraseLead_coeff]
      split <;> simp [hx, hpk]
    · intro u hu
      rw [eraseLead_coeff, eraseLead_coeff, hpqd]
      split
      · rfl
      · exact hnl u hu
    · rwa [eraseLead_coeff, eraseLead_coeff, hpqd, ite_eq_right hqd.ne, ite_eq_right hqd.ne]
    · rfl

-- `Nimber.oeval_le_oeval`
-- removable: as for oeval_lt_oeval, only the bound on the smaller polynomial is needed
theorem c_41 : drop% Nimber.oeval_le_oeval 5 := by
  intro x p q h hpk
  obtain rfl | h := h.eq_or_lt
  · rfl
  · exact (c_38 h hpk).le

end

namespace W2c2
open Nimber Polynomial

theorem F_gt : (∗2 : Nimber) < fieldClosure (Order.succ (∗Ordinal.omega 1)) :=
  (two_lt_acl acl).trans ((Order.lt_succ _).trans_le (le_fieldClosure _))

theorem F_le_opow (o : Ordinal) (ho : 0 < o) :
    fieldClosure (Order.succ (∗Ordinal.omega 1)) ≤ of (val (fieldClosure (Order.succ (∗Ordinal.omega 1))) ^ o) :=
  calc _ = of (val (fieldClosure (Order.succ (∗Ordinal.omega 1)))) := (of_val _).symm
    _ ≤ _ := of.le_iff_le.2 (Ordinal.left_le_opow _ ho)

/-- ℤ ordered by absolute value: addition is not monotone. -/
def AZ : Type := ℤ
instance : AddZeroClass AZ := inferInstanceAs (AddZeroClass ℤ)
instance : Preorder AZ := Preorder.lift (fun z : ℤ => Int.natAbs z)

end W2c2

open Nimber Polynomial W2c2

-- `WithBot.add_pos_of_pos_of_nonneg`
theorem c_4m : ¬ drop0% WithBot.add_pos_of_pos_of_nonneg 3 := fun h => by
  have ha : (WithBot.some (show AZ from (0 : ℤ))) < (WithBot.some (show AZ from (1 : ℤ))) :=
    WithBot.coe_lt_coe.2 (show Int.natAbs 0 < Int.natAbs 1 by decide)
  have hb : (WithBot.some (show AZ from (0 : ℤ))) ≤ (WithBot.some (show AZ from (-1 : ℤ))) :=
    WithBot.coe_le_coe.2 (show Int.natAbs 0 ≤ Int.natAbs (-1) by decide)
  have := @h AZ _ _ (a := (WithBot.some (show AZ from (1 : ℤ)))) (b := (WithBot.some (show AZ from (-1 : ℤ)))) ha hb
  rw [← WithBot.coe_add] at this
  exact absurd (WithBot.coe_lt_coe.1 this) (show ¬ Int.natAbs 0 < Int.natAbs (1 + -1) by decide)

-- `Nimber.IsAlgClosed.exists_fieldClosure_succ_pow_two_pow_eq_of_isField_of_btwn`
theorem c_104 : ¬ drop0% Nimber.IsAlgClosed.exists_fieldClosure_succ_pow_two_pow_eq_of_isField_of_btwn 4 := fun h => by
  obtain ⟨n, hn⟩ := @h _ acl (∗2) IsField.two (F_gt.trans_le (F_le_opow _ Ordinal.omega0_pos))
  have := F_le_opow ((2 ^ n : ℕ) : Ordinal) (by exact_mod_cast (show 0 < 2 ^ n by positivity))
  rw [Ordinal.opow_natCast, hn] at this
  exact not_le.2 F_gt this

-- `Nimber.IsAlgClosed.exists_fieldClosure_succ_pow_two_pow_eq_of_isField_of_btwn`
theorem c_105 : ¬ drop0% Nimber.IsAlgClosed.exists_fieldClosure_succ_pow_two_pow_eq_of_isField_of_btwn 5 := fun h => by
  obtain ⟨n, hn⟩ := @h _ acl _ acl.isField_fieldClosure_succ_pow_omega0 (F_le_opow _ Ordinal.omega0_pos)
  have h1 : (1 : Ordinal) < val (fieldClosure (Order.succ (∗Ordinal.omega 1))) := by
    simpa using val.lt_iff_lt.2 (one_lt_two'.trans F_gt)
  have e := congrArg val hn
  simp only [val_of] at e
  rw [← Ordinal.opow_natCast] at e
  have := (Ordinal.opow_lt_opow_iff_right h1).2 (Ordinal.natCast_lt_omega0 (2 ^ n))
  rw [e] at this
  exact lt_irrefl _ this

namespace W2c2
open Nimber Polynomial

theorem omega_le_F : Ordinal.omega0 ≤ val (fieldClosure (Order.succ (∗Ordinal.omega 1))) := by
  have := acl.omega0_le.trans ((Order.lt_succ _).le.trans (le_fieldClosure (Order.succ (∗Ordinal.omega 1))))
  simpa using val.le_iff_le.2 this

theorem succ_F : Order.succ (fieldClosure (Order.succ (∗Ordinal.omega 1))) =
    of (val (fieldClosure (Order.succ (∗Ordinal.omega 1))) + 1) := rfl

theorem add_one_lt_sq {a : Ordinal} (ha : Ordinal.omega0 ≤ a) : a + 1 < a ^ (2 : Ordinal) := by
  have h1 : (1 : Ordinal) < a := lt_of_lt_of_le (by simpa using Ordinal.natCast_lt_omega0 1) ha
  have h2 : (2 : Ordinal) ≤ a := le_of_lt (lt_of_lt_of_le (by simpa using Ordinal.natCast_lt_omega0 2) ha)
  calc a + 1 < a + a := by gcongr
    _ = a * 2 := by rw [Ordinal.mul_two]
    _ ≤ a * a := by gcongr
    _ = a ^ (2 : Ordinal) := by
      have := Ordinal.opow_natCast a 2; simp only [Nat.cast_ofNat] at this; rw [this, _root_.pow_two]

end W2c2

open Nimber Polynomial W2c2

-- `IsSimpleGroup.isMulCommutative_iff_isSolvable`
theorem c_110 : ¬ drop0% IsSimpleGroup.isMulCommutative_iff_isSolvable 2 := fun h => by
  have hc := (@h (Equiv.Perm (Fin 3)) _).2 (Equiv.Perm.isSolvable (by simp))
  have := hc.is_comm.comm (Equiv.swap 0 1) (Equiv.swap 1 2)
  exact absurd this (by decide)

-- `Nimber.IsAlgClosed.exists_fieldClosure_succ_pow_two_pow_eq_of_isField_of_btwn`
theorem c_103 : ¬ drop0% Nimber.IsAlgClosed.exists_fieldClosure_succ_pow_two_pow_eq_of_isField_of_btwn 3 := fun h => by
  have hs := add_one_lt_sq omega_le_F
  have hpos : (0 : Ordinal) < val (fieldClosure (Order.succ (∗Ordinal.omega 1))) :=
    lt_of_lt_of_le Ordinal.omega0_pos omega_le_F
  obtain ⟨n, hn⟩ := @h _ acl (Order.succ _) (Order.le_succ _) (by
    rw [succ_F, of.lt_iff_lt]
    exact hs.trans_le (Ordinal.opow_le_opow_right hpos (by simpa using (Ordinal.natCast_lt_omega0 2).le)))
  rw [succ_F] at hn
  have e := congrArg val hn
  simp only [val_of] at e
  rcases n with _ | n
  · simp at e
  · have h2 : val (fieldClosure (Order.succ (∗Ordinal.omega 1))) ^ (2 : Ordinal) ≤
        val (fieldClosure (Order.succ (∗Ordinal.omega 1))) ^ (2 ^ (n + 1) : ℕ) := by
      rw [← Ordinal.opow_natCast]
      exact Ordinal.opow_le_opow_right hpos (by exact_mod_cast (show 2 ≤ 2 ^ (n + 1) by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right two_pos (by omega)))
    rw [e] at h2
    exact absurd hs (not_lt.2 h2)

-- `IsSimpleAddGroup.isAddCommutative_iff_isSolvable`
theorem c_109 : ¬ drop0% IsSimpleAddGroup.isAddCommutative_iff_isSolvable 2 := fun h => by
  have hc3 : ∀ a b : alternatingGroup (Fin 3), a * b = b * a := by decide
  have hA : AddGroup.IsSolvable (Additive (alternatingGroup (Fin 3))) :=
    AddGroup.isSolvable_of_comm (fun a b => congrArg Additive.ofMul (hc3 (Additive.toMul a) (Additive.toMul b)))
  have hU : AddGroup.IsSolvable (Additive ℤˣ) := AddGroup.isSolvable_of_comm (fun a b => _root_.add_comm a b)
  have hs : AddGroup.IsSolvable (Additive (Equiv.Perm (Fin 3))) :=
    AddGroup.isSolvable_of_ker_le_range (MonoidHom.toAdditive (alternatingGroup (Fin 3)).subtype)
      (MonoidHom.toAdditive Equiv.Perm.sign) (fun x hx => ⟨Additive.ofMul ⟨Additive.toMul x, hx⟩, rfl⟩)
  have hc := (@h _ _).2 hs
  have := hc.is_comm.comm (Additive.ofMul (Equiv.swap (0 : Fin 3) 1)) (Additive.ofMul (Equiv.swap 1 2))
  exact absurd (congrArg Additive.toMul this) (by decide)
