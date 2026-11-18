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

namespace T3c2
universe u
open Nimber Ordinal Set

theorem two_add_one : ∗2 + 1 = (∗3 : Nimber.{u}) := by
  have := (IsGroup.two : IsGroup (∗2 : Nimber.{u})).add_eq_of_lt (y := 1) (by simp)
  rw [← this]; simp; norm_num

theorem three_add_two : ∗3 + ∗2 = (1 : Nimber.{u}) := by
  rw [← two_add_one, _root_.add_comm (∗2), _root_.add_assoc, CharTwo.add_self_eq_zero, _root_.add_zero]

theorem two_ne_one : (∗2 : Nimber.{u}) ≠ 1 := by
  rw [← of_one, Ne, of.eq_iff_eq]; exact_mod_cast (show (2:ℕ) ≠ 1 by decide)

theorem two_ne_zero' : (∗2 : Nimber.{u}) ≠ 0 := IsGroup.two.ne_zero

theorem two_lt_three : (∗2 : Nimber.{u}) < ∗3 := by
  rw [of.lt_iff_lt]; exact_mod_cast (show (2:ℕ) < 3 by decide)

theorem three_ne : (∗3 : Nimber.{u}) ≠ 0 ∧ (∗3 : Nimber.{u}) ≠ 1 ∧ (∗3 : Nimber.{u}) ≠ ∗2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (IsGroup.two.zero_lt.trans two_lt_three).ne'
  · rw [← of_one, Ne, of.eq_iff_eq]; exact_mod_cast (show (3:ℕ) ≠ 1 by decide)
  · rw [Ne, of.eq_iff_eq]; exact_mod_cast (show (3:ℕ) ≠ 2 by decide)

theorem lt_three {y : Nimber.{u}} (h : y < ∗3) : y = 0 ∨ y = 1 ∨ y = ∗2 := by
  rcases lt_or_ge y (∗2) with h2 | h2
  · rcases lt_two_iff.1 h2 with h | h <;> simp [h]
  · right; right
    apply le_antisymm _ h2
    cases y with | of y
    rw [of.lt_iff_lt] at h; rw [of.le_iff_le]
    have h3 : (3:Ordinal) = 2 + 1 := by norm_num
    rw [h3] at h; exact Order.lt_add_one_iff.1 h

theorem two_mul_two : ∗2 * ∗2 = (∗3 : Nimber.{u}) := by
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
    · have : (∗2 + 1) * (∗2 + 1) = (0 : Nimber.{u}) := by
        calc (∗2 + 1) * (∗2 + 1) = ∗2 * ∗2 + (∗2 + ∗2) + 1 := by ring
          _ = 0 := by rw [h, CharTwo.add_self_eq_zero, _root_.add_zero, CharTwo.add_self_eq_zero]
      have := mul_self_eq_zero.1 this
      exact two_ne_one (Nimber.add_eq_zero.1 this)
    · exact two_ne_one (mul_left_cancel₀ two_ne_zero' (h.trans (_root_.mul_one _).symm))

theorem three_mul_two : ∗3 * ∗2 = (1 : Nimber.{u}) := by
  rw [← two_add_one, _root_.add_mul, two_mul_two, _root_.one_mul, three_add_two]

theorem two_mul_three : ∗2 * ∗3 = (1 : Nimber.{u}) := by rw [_root_.mul_comm, three_mul_two]

theorem inv_two : (∗2 : Nimber.{u})⁻¹ = ∗3 := inv_eq_of_mul_eq_one_right two_mul_three
theorem inv_three : (∗3 : Nimber.{u})⁻¹ = ∗2 := inv_eq_of_mul_eq_one_right three_mul_two

theorem three_add_one : ∗3 + 1 = (∗2 : Nimber.{u}) := by
  rw [← two_add_one, _root_.add_assoc, CharTwo.add_self_eq_zero, _root_.add_zero]

theorem three_mul_three : ∗3 * ∗3 = (∗2 : Nimber.{u}) := by
  rw [← two_add_one]
  calc (∗2 + 1) * (∗2 + 1) = ∗2 * ∗2 + (∗2 + ∗2) + (1 : Nimber.{u}) := by ring
    _ = ∗2 := by rw [two_mul_two, CharTwo.add_self_eq_zero, _root_.add_zero, three_add_one]

theorem lt_four {y : Nimber.{u}} (h : y < ∗4) : y = 0 ∨ y = 1 ∨ y = ∗2 ∨ y = ∗3 := by
  rcases lt_or_ge y (∗3) with h3 | h3
  · rcases lt_three h3 with h | h | h <;> simp [h]
  · right; right; right
    apply le_antisymm _ h3
    cases y with | of y
    rw [of.lt_iff_lt] at h; rw [of.le_iff_le]
    have h4 : (4:Ordinal) = 3 + 1 := by norm_num
    rw [h4] at h; exact Order.lt_add_one_iff.1 h

theorem three_lt_four : (∗3 : Nimber.{u}) < ∗4 := by
  rw [of.lt_iff_lt]; exact_mod_cast (show (3:ℕ) < 4 by decide)
theorem one_lt_two'' : (1 : Nimber.{u}) < ∗2 := IsRing.two.one_lt
theorem two_lt_four : (∗2 : Nimber.{u}) < ∗4 := two_lt_three.trans three_lt_four
theorem one_lt_four : (1 : Nimber.{u}) < ∗4 := one_lt_two''.trans two_lt_four
theorem zero_lt_four : (0 : Nimber.{u}) < ∗4 := zero_lt_one.trans one_lt_four
theorem one_add_two : 1 + ∗2 = (∗3 : Nimber.{u}) := by rw [_root_.add_comm, two_add_one]
theorem two_add_three : ∗2 + ∗3 = (1 : Nimber.{u}) := by rw [_root_.add_comm, three_add_two]
theorem one_add_three : 1 + ∗3 = (∗2 : Nimber.{u}) := by rw [_root_.add_comm, three_add_one]

theorem field4 : IsField (∗4 : Nimber.{u}) where
  add_lt y z hy hz := by
    rcases lt_four hy with rfl | rfl | rfl | rfl <;> rcases lt_four hz with rfl | rfl | rfl | rfl <;>
      simp [two_add_one, three_add_two, one_add_two, two_add_three, three_add_one, one_add_three,
        zero_lt_four, one_lt_four, two_lt_four, three_lt_four] <;>
      first | exact_mod_cast (show (2:ℕ) < 4 by decide) | exact_mod_cast (show (3:ℕ) < 4 by decide)
  ne_zero := zero_lt_four.ne'
  mul_lt y z hy hz := by
    rcases lt_four hy with rfl | rfl | rfl | rfl <;> rcases lt_four hz with rfl | rfl | rfl | rfl <;>
      simp [two_mul_two, two_mul_three, three_mul_two, three_mul_three,
        zero_lt_four, one_lt_four, two_lt_four, three_lt_four] <;>
      first | exact_mod_cast (show (2:ℕ) < 4 by decide) | exact_mod_cast (show (3:ℕ) < 4 by decide)
  ne_one := one_lt_four.ne'
  inv_lt' y hy0 hy := by
    rcases lt_four hy with rfl | rfl | rfl | rfl
    · exact absurd rfl hy0
    · simpa using one_lt_four
    · rw [inv_two]; exact three_lt_four
    · rw [inv_three]; exact two_lt_four


theorem o1 : (1 : Ordinal.{u}) < 4 := by exact_mod_cast (show (1:ℕ) < 4 by decide)
theorem o2 : (2 : Ordinal.{u}) < 4 := by exact_mod_cast (show (2:ℕ) < 4 by decide)
theorem o3 : (3 : Ordinal.{u}) < 4 := by exact_mod_cast (show (3:ℕ) < 4 by decide)

-- helper: ∗(4^α * d + s) = ∗(4^α) * ∗d + ∗s for d < 4, s < 4^α
theorem expand4 {α P d s : Ordinal.{u}} (hP : 4 ^ α = P) (hd : d < 4) (hs : s < P) :
    ∗(P * d + s) = ∗P * ∗d + ∗s := by
  subst hP
  rw [(field4.toIsGroup.opow' α).mul_add_eq_of_lt' hs,
    field4.opow_mul_eq_of_lt' α (by exact_mod_cast hd), of_val]

theorem mul_lt4 {α P : Ordinal.{u}} (hP : 4 ^ α = P) {c s : Nimber.{u}} (hc : c < ∗4) (hs : s < ∗P) :
    s * c < ∗P := by
  subst hP
  exact field4.mul_lt_opow_of_right_lt (o := α) hs hc

-- helper: if Iio (∗o) is closed under multiplication by ∗2 then o is a power of 4
theorem pow4_of_closed {o : Ordinal.{u}} (ho : o ≠ 0) (h2 : ∀ a < ∗o, a * ∗2 < ∗o) :
    ∗o = ∗((4 : Ordinal.{u}) ^ log 4 o) := by
  have hq : o / (4 : Ordinal.{u}) ^ log 4 o < 4 := div_opow_log_lt o (by norm_num)
  have hq0 : 0 < o / (4 : Ordinal.{u}) ^ log 4 o := div_opow_log_pos 4 ho
  have hdec := div_add_mod o ((4 : Ordinal.{u}) ^ log 4 o)
  have hr : o % (4 : Ordinal.{u}) ^ log 4 o < (4 : Ordinal.{u}) ^ log 4 o :=
    mod_lt _ (opow_ne_zero _ (by norm_num))
  generalize hPdef : (4 : Ordinal.{u}) ^ log 4 o = P at hq hq0 hdec hr ⊢
  generalize o / P = q at hq hq0 hdec
  generalize o % P = r at hr hdec
  subst hdec
  have hP : P ≠ 0 := by rw [← hPdef]; exact opow_ne_zero _ (by norm_num)
  have ht : ∗r * ∗3 < ∗P := mul_lt4 hPdef three_lt_four hr
  have ht2 : ∗(val (∗r * ∗3)) * ∗2 = ∗r := by
    rw [of_val, _root_.mul_assoc, three_mul_two, _root_.mul_one]
  have hq4 : ∗q < ∗4 := hq
  rcases lt_four hq4 with h | h | h | h
  · exact absurd (show q = 0 from h) hq0.ne'
  · have hq1 : q = 1 := h
    subst hq1
    by_contra hne
    have hr0 : r ≠ 0 := by
      intro h0; apply hne; rw [h0, _root_.add_zero, _root_.mul_one]
    have hlt : ∗P < ∗(P * 1 + r) := by
      show P < P * 1 + r
      rw [_root_.mul_one]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr0)
    have := h2 _ hlt
    rw [show ∗P * ∗2 = ∗(P * 2 + 0) by
      rw [expand4 hPdef o2 (pos_iff_ne_zero.2 hP)]; simp] at this
    apply (lt_asymm this)
    show P * 1 + r < P * 2 + 0
    rw [_root_.add_zero, _root_.mul_one]
    calc P + r < P + P := (add_lt_add_iff_left P).2 hr
      _ = P * 2 := by rw [Ordinal.mul_two]
  · have hq2 : q = 2 := h
    subst hq2
    have hlt : ∗(P * 1 + val (∗r * ∗3)) < ∗(P * 2 + r) := by
      show P * 1 + val (∗r * ∗3) < P * 2 + r
      exact (Ordinal.mul_add_lt ht (by norm_num)).trans_le (le_self_add ..)
    have := h2 _ hlt
    rw [expand4 hPdef o1 (show val (∗r * ∗3) < P from ht), _root_.add_mul, ht2, of_one, _root_.mul_one,
      ← expand4 hPdef o2 hr] at this
    exact absurd this (lt_irrefl _)
  · have hq3 : q = 3 := h
    subst hq3
    have hlt : ∗(P * 2 + val (∗r * ∗3)) < ∗(P * 3 + r) := by
      show P * 2 + val (∗r * ∗3) < P * 3 + r
      exact (Ordinal.mul_add_lt ht (by exact_mod_cast (show (2:ℕ) < 3 by decide))).trans_le (le_self_add ..)
    have := h2 _ hlt
    rw [expand4 hPdef o2 (show val (∗r * ∗3) < P from ht), _root_.add_mul, ht2, _root_.mul_assoc, two_mul_two,
      ← expand4 hPdef o3 hr] at this
    exact absurd this (lt_irrefl _)


-- helper: IsGroup.mul_eq_of_lt' without hx (for w ≥ 2, H' makes Iio x closed under ∗2, so x = 4^α)
theorem mulEqNoHx {x y z w : Ordinal.{u}}
    (hy : IsGroup (∗y)) (hz : IsGroup (∗z))
    (hyx : y ≤ x) (hyz : y ≤ z) (hwy : w < y)
    (H : ∀ a < y, (∗a)⁻¹ < ∗z) (H' : ∀ ⦃a b⦄, a < x → b < z → ∗a * ∗b < ∗x) :
    x * w = val (∗x * ∗w) := by
  by_cases h2y : (∗2 : Nimber.{u}) < ∗y
  · have h3y : (∗3 : Nimber.{u}) < ∗y := two_add_one ▸ hy.add_lt h2y (one_lt_two''.trans h2y)
    have h2z : (2 : Ordinal.{u}) < z := (two_lt_three.trans (h3y.trans_le hyz) : (∗2 : Nimber.{u}) < ∗z)
    have hx0 : x ≠ 0 := (hy.pos.trans_le hyx).ne'
    have hx : IsGroup (∗x) := by
      rw [pow4_of_closed hx0 (fun a ha => H' (a := val a) ha h2z)]
      exact field4.toIsGroup.opow' _
    exact hx.mul_eq_of_lt' hy hz hyx hyz hwy H H'
  · have hw : (∗w : Nimber.{u}) < ∗2 := (show ∗w < ∗y from hwy).trans_le (not_lt.1 h2y)
    rcases lt_two_iff.1 hw with h | h
    · have : w = 0 := h
      subst this; simp
    · have : w = 1 := h
      subst this; simp

-- `Nimber.IsGroup.mul_eq_of_lt'` idx 4: removable (H' with ∗2 < z makes Iio x closed under ∗2, so x = 4^α is a group; w ≤ 1 is trivial)
theorem c_1 : drop% Nimber.IsGroup.mul_eq_of_lt' 4 := by
  intro x y z w hy hz hyx hyz hwy H H'
  exact mulEqNoHx hy hz hyx hyz hwy H H'

-- `Nimber.IsGroup.mul_eq_of_lt` idx 4: removable (as the Ordinal version)
theorem c_2 : drop% Nimber.IsGroup.mul_eq_of_lt 4 := by
  intro x y z w hy hz hyx hyz hwy H H'
  exact mulEqNoHx (x := val x) (y := val y) (z := val z) (w := val w) hy hz hyx hyz hwy H
    (fun a b ha hb => H' ha hb)

end T3c2
