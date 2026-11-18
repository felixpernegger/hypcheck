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

namespace W3c3
open IGame Surreal

-- `Surreal.mul_wpow_lt_wpow` idx 3: necessary (x = y = 0, r = 1: 1 < 1)
theorem w3c3_1 : ¬ drop0% Surreal.mul_wpow_lt_wpow 3 := fun h => by simpa using @h 0 0 1
-- `Surreal.wpow_lt_mul_wpow` idx 3: necessary (r = 0, x = 0, y = 1: 1 < 0)
theorem w3c3_2 : ¬ drop0% Surreal.wpow_lt_mul_wpow 3 := fun h => by
  have := @h 0 1 0 zero_lt_one; simp at this; norm_num at this
-- `Surreal.wpow_lt_mul_wpow` idx 4: necessary (x = y = 0, r = 1: 1 < 1)
theorem w3c3_3 : ¬ drop0% Surreal.wpow_lt_mul_wpow 4 := fun h => by simpa using @h 0 0 1 one_pos
-- `Surreal.mul_wpow_lt_mul_wpow_of_pos` idx 4: necessary (r = s = 0, x = 0 < y = 1: 0 < 0)
theorem w3c3_4 : ¬ drop0% Surreal.mul_wpow_lt_mul_wpow_of_pos 4 := fun h => by simpa using @h 0 1 0 0 zero_lt_one
-- `Surreal.mul_wpow_lt_mul_wpow_of_pos` idx 5: necessary (x = y = 0, r = s = 1: 1 < 1)
theorem w3c3_5 : ¬ drop0% Surreal.mul_wpow_lt_mul_wpow_of_pos 5 := fun h => by simpa using @h 0 0 1 1 one_pos
-- `Surreal.mul_wpow_lt_mul_wpow_of_neg` idx 4: necessary (r = s = 0, x = 1, y = 0: 0 < 0)
theorem w3c3_6 : ¬ drop0% Surreal.mul_wpow_lt_mul_wpow_of_neg 4 := fun h => by simpa using @h 1 0 0 0 zero_lt_one
-- `Surreal.mul_wpow_lt_mul_wpow_of_neg` idx 5: necessary (x = y = 0, r = s = -1: -1 < -1)
theorem w3c3_7 : ¬ drop0% Surreal.mul_wpow_lt_mul_wpow_of_neg 5 := fun h => by simpa using @h 0 0 (-1) (-1) (by norm_num)
-- `Surreal.mk_realCast` idx 1: necessary (r = 0: mk 0 = top, not 0)
theorem w3c3_8 : ¬ drop0% Surreal.mk_realCast 1 := fun h => by
  have := @h 0
  simp only [Real.toSurreal_zero, ArchimedeanClass.mk_zero] at this
  exact one_ne_zero (ArchimedeanClass.mk_eq_top_iff.1 (ArchimedeanClass.mk_one.trans this.symm))
-- `Surreal.wlog_congr` idx 2: necessary (x = 0, y = ω^ 1: wlog 0 = 0, wlog ω = 1)
theorem w3c3_9 : ¬ drop0% Surreal.wlog_congr 2 := fun h => by simpa using @h 0 (ω^ 1)
-- `Surreal.wlog_add_eq_left` idx 2: necessary (x = 0, y = ω^ 1)
theorem w3c3_10 : ¬ drop0% Surreal.wlog_add_eq_left 2 := fun h => by simpa using @h 0 (ω^ 1)
-- `Surreal.wlog_add_eq_right` idx 2: necessary (x = 0, y = ω^ 1)
theorem w3c3_11 : ¬ drop0% Surreal.wlog_add_eq_right 2 := fun h => by simpa using @h 0 (ω^ 1)
-- `Surreal.wlog_sub_eq_left` idx 2: necessary (x = 0, y = ω^ 1)
theorem w3c3_12 : ¬ drop0% Surreal.wlog_sub_eq_left 2 := fun h => by simpa using @h 0 (ω^ 1)
-- `Surreal.wlog_sub_eq_right` idx 2: necessary (x = 0, y = ω^ 1)
theorem w3c3_13 : ¬ drop0% Surreal.wlog_sub_eq_right 2 := fun h => by simpa using @h 0 (ω^ 1)
-- `Surreal.wlog_le_wlog_iff` idx 2: necessary (x = 0, y = ω^ -1: 0 ≤ -1 false but 0 ≤ᵥ y)
theorem w3c3_14 : ¬ drop0% Surreal.wlog_le_wlog_iff 2 := fun h => by
  have := @h 0 (ω^ (-1)) (wpow_ne_zero _); simp [vle_def] at this; norm_num at this
-- `Surreal.wlog_le_wlog_of_vle` idx 2: necessary (x = 0, y = ω^ -1: 0 ≤ᵥ y, wlog 0 = 0 > -1)
theorem w3c3_15 : ¬ drop0% Surreal.wlog_le_wlog_of_vle 2 := fun h => by
  have := @h 0 (ω^ (-1)) (by simp); simp at this; norm_num at this
-- `Surreal.wlog_le_wlog_of_vle` idx 3: necessary (x = ω^ 1, y = 1: wlog 1 = 1 > 0)
theorem w3c3_16 : ¬ drop0% Surreal.wlog_le_wlog_of_vle 3 := fun h => by
  have := @h (ω^ 1) 1 (wpow_ne_zero _); simp at this; norm_num at this
-- `Surreal.wlog_lt_wlog_iff` idx 3: necessary (x = ω^ -1, y = 0: -1 < 0 but not x <ᵥ 0)
theorem w3c3_17 : ¬ drop0% Surreal.wlog_lt_wlog_iff 3 := fun h => by
  simpa [vlt_def] using @h (ω^ (-1)) 0 (wpow_ne_zero _)
-- `Surreal.wlog_mul` idx 2: necessary (x = 0, y = ω^ 1: 0 ≠ 0 + 1)
theorem w3c3_18 : ¬ drop0% Surreal.wlog_mul 2 := fun h => by simpa using @h 0 (ω^ 1) (wpow_ne_zero _)
-- `Surreal.wlog_mul` idx 3: necessary (x = ω^ 1, y = 0: 0 ≠ 1 + 0)
theorem w3c3_19 : ¬ drop0% Surreal.wlog_mul 3 := fun h => by simpa using @h (ω^ 1) 0 (wpow_ne_zero _)

-- `IGame.Numeric.wpow_lt_mul_wpow` idx 5: necessary (x = 0, y = 1, r = 0: 1 < 0)
theorem w3c3_20 : ¬ drop0% IGame.Numeric.wpow_lt_mul_wpow 5 := fun h => by
  have := @h 0 1 _ _ 0 (by game_cmp)
  rw [← Surreal.mk_lt_mk] at this; simp at this; try norm_num at this
-- `IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg` idx 6: necessary (x = 1, y = 0, r = 0, s = -1: 0 < -1)
theorem w3c3_21 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg 6 := fun h => by
  have := @h 1 0 _ _ 0 (-1) (by game_cmp)
  rw [← Surreal.mk_lt_mk] at this; simp at this; try norm_num at this
-- `IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow` idx 9: necessary (r = s = t = 0: 0 < 0)
theorem w3c3_22 : ¬ drop0% IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow 9 := fun h => by
  have := @h 0 0 1 _ _ _ 0 0 0 (by game_cmp) (by game_cmp)
  rw [← Surreal.mk_lt_mk] at this; simp at this; try norm_num at this
-- `IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow` idx 10: necessary (x = z = 0, y = -1, r = t = 1, s = 0: 1 < 1)
theorem w3c3_23 : ¬ drop0% IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow 10 := fun h => by
  have := @h 0 (-1) 0 _ _ _ 1 0 1 one_pos (by game_cmp)
  rw [← Surreal.mk_lt_mk] at this; simp at this; try norm_num at this
-- `IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow` idx 11: necessary (y = z = 0, x = -1, s = t = 1, r = 0: 1 < 1)
theorem w3c3_24 : ¬ drop0% IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow 11 := fun h => by
  have := @h (-1) 0 0 _ _ _ 0 1 1 one_pos (by game_cmp)
  rw [← Surreal.mk_lt_mk] at this; simp at this; try norm_num at this
-- `IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow'` idx 10: necessary (x = z = 0, y = -1, r = t = 1, s = 0: 1 < 1)
theorem w3c3_25 : ¬ drop0% IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow' 10 := fun h => by
  have := @h 0 (-1) 0 _ _ _ 1 0 1 one_pos (by game_cmp)
  rw [← Surreal.mk_lt_mk] at this; simp at this; try norm_num at this
-- `IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow'` idx 11: necessary (y = z = 0, x = -1, s = t = 1, r = 0: 1 < 1)
theorem w3c3_26 : ¬ drop0% IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow' 11 := fun h => by
  have := @h (-1) 0 0 _ _ _ 0 1 1 one_pos (by game_cmp)
  rw [← Surreal.mk_lt_mk] at this; simp at this; try norm_num at this
-- `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow` idx 9: necessary (x = 0, y = z = 1, r = 0, s = -1, t = 1: 0 < 0)
theorem w3c3_27 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow 9 := fun h => by
  have := @h 0 1 1 _ _ _ 0 (-1) 1 one_pos (by game_cmp) (by game_cmp)
  rw [← Surreal.mk_lt_mk] at this; simp at this; try norm_num at this
-- `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow'` idx 9: necessary (x = 0, y = z = 1, r = 0, s = -1, t = 1: 0 < 0)
theorem w3c3_28 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow' 9 := fun h => by
  have := @h 0 1 1 _ _ _ 0 (-1) 1 one_pos (by game_cmp) (by game_cmp)
  rw [← Surreal.mk_lt_mk] at this; simp at this; try norm_num at this
-- `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow` idx 11: removable (r ω^x < t ω^z (from x < z) and s ω^y > 0)
theorem w3c3_29 : drop% IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow 11 := by
  intro x y z _ _ _ r s t hs ht hz
  have h1 := Numeric.mul_wpow_lt_mul_wpow_of_pos r ht hz
  have h2 : 0 < (s : IGame) * ω^ y := Numeric.mul_pos (mod_cast hs) (Numeric.wpow_pos y)
  rw [← Surreal.mk_lt_mk] at h1 h2 ⊢
  simp only [Surreal.mk_add] at h1 h2 ⊢
  exact lt_add_of_pos_of_lt h2 h1
-- `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow` idx 12: removable (r ω^x < s ω^y (from x < y) and t ω^z > 0)
theorem w3c3_30 : drop% IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow 12 := by
  intro x y z _ _ _ r s t hs ht hy
  have h1 := Numeric.mul_wpow_lt_mul_wpow_of_pos r hs hy
  have h2 : 0 < (t : IGame) * ω^ z := Numeric.mul_pos (mod_cast ht) (Numeric.wpow_pos z)
  rw [← Surreal.mk_lt_mk] at h1 h2 ⊢
  simp only [Surreal.mk_add] at h1 h2 ⊢
  exact lt_add_of_lt_of_pos h1 h2
-- `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow'` idx 11: removable (r ω^x < t ω^z (from x < z) and s ω^y > 0)
theorem w3c3_31 : drop% IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow' 11 := by
  intro x y z _ _ _ r s t hs ht hz
  have h1 := Numeric.mul_wpow_lt_mul_wpow_of_pos' r ht hz
  have h2 : 0 < (s : IGame) * ω^ y := Numeric.mul_pos (by simpa) (Numeric.wpow_pos y)
  rw [← Surreal.mk_lt_mk] at h1 h2 ⊢
  simp only [Surreal.mk_add] at h1 h2 ⊢
  exact lt_add_of_pos_of_lt h2 h1
-- `IGame.Numeric.wpow_congr` idx 4: necessary (x = 0, y = 1: ω^ 1 ≤ 1 false)
theorem w3c3_32 : ¬ drop0% IGame.Numeric.wpow_congr 4 := fun h => by
  have := (@h 0 1 _ _).ge
  rw [← Surreal.mk_le_mk] at this; simp at this
  have h2 : (ω^ (0:Surreal)) < ω^ 1 := Surreal.wpow_lt_wpow.2 zero_lt_one
  simp at h2; exact absurd this (not_le.2 h2)
end W3c3

namespace W3c3
open IGame Surreal

theorem oneLtW : (1:Surreal) < ω^ 1 := by simpa using (Surreal.wpow_lt_wpow (x := 0) (y := 1)).2 zero_lt_one
theorem we (a b : IGame) [Numeric a] [Numeric b] : ω^ (a + b) ≈ ω^ a * ω^ b := Numeric.wpow_add_equiv a b

theorem L3 {X Y Z W : Surreal} (h1 : Z < X) (h2 : W < Y) (a b c : ℚ) :
    (a:Surreal) * ω^ Z * ω^ Y + (b:Surreal) * (ω^ X * ω^ W) + (c:Surreal) * (ω^ Z * ω^ W) < ω^ X * ω^ Y := by
  have w3c3_57 := Surreal.mul_wpow_lt_mul_wpow_of_pos (((3*a : ℚ)):ℝ) (s := 1) one_pos (add_lt_add_left h1 Y)
  have w3c3_58 := Surreal.mul_wpow_lt_mul_wpow_of_pos (((3*b : ℚ)):ℝ) (s := 1) one_pos (add_lt_add_right h2 X)
  have w3c3_59 := Surreal.mul_wpow_lt_mul_wpow_of_pos (((3*c : ℚ)):ℝ) (s := 1) one_pos (add_lt_add h1 h2)
  simp only [Surreal.wpow_add, Real.toSurreal_ratCast, Real.toSurreal_one] at w3c3_57 w3c3_58 w3c3_59
  push_cast at w3c3_57 w3c3_58 w3c3_59
  linear_combination (w3c3_57 + w3c3_58 + w3c3_59) / 3

theorem L4 {X Y Z W : Surreal} (h1 : X < Z) (h2 : W < Y) (r : ℚ) (hr : 0 < r) (b c : ℚ) :
    ω^ X * ω^ Y + (b:Surreal) * (ω^ X * ω^ W) + (c:Surreal) * (ω^ Z * ω^ W) < (r:Surreal) * ω^ Z * ω^ Y := by
  have hr' : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have w3c3_57 := Surreal.mul_wpow_lt_mul_wpow_of_pos (((3 : ℚ)):ℝ) hr' (add_lt_add_right h1 Y)
  have w3c3_58 := Surreal.mul_wpow_lt_mul_wpow_of_pos (((3*b : ℚ)):ℝ) hr' (add_lt_add_left h2 X |>.trans (add_lt_add_right h1 Y))
  have w3c3_59 := Surreal.mul_wpow_lt_mul_wpow_of_pos (((3*c : ℚ)):ℝ) hr' (add_lt_add_left h2 Z)
  simp only [Surreal.wpow_add, Real.toSurreal_ratCast] at w3c3_57 w3c3_58 w3c3_59
  push_cast at w3c3_57 w3c3_58 w3c3_59
  linear_combination (w3c3_57 + w3c3_58 + w3c3_59) / 3

-- mulOption_lt_wpow
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow` idx 10: necessary (x = y = 0, z = w = 1, r = 0, s = 1: mulOption = ω, not < 1)
theorem w3c3_33 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow 10 := fun h => by
  have := @h 0 0 1 1 _ _ _ _ 0 1 one_pos (by game_cmp) (by game_cmp) (we ..) (we ..) (we ..)
  rw [← Surreal.mk_lt_mk] at this; simp [mulOption] at this
  linarith [oneLtW]
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow` idx 11: necessary (x = y = 0, z = w = 1, r = 1, s = 0: mulOption = ω, not < 1)
theorem w3c3_34 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow 11 := fun h => by
  have := @h 0 0 1 1 _ _ _ _ 1 0 one_pos (by game_cmp) (by game_cmp) (we ..) (we ..) (we ..)
  rw [← Surreal.mk_lt_mk] at this; simp [mulOption] at this
  linarith [oneLtW]
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow` idx 12: necessary (x = y = z = 0, w = 1, r = s = 1: mulOption = 1, not < 1)
theorem w3c3_35 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow 12 := fun h => by
  have := @h 0 0 0 1 _ _ _ _ 1 1 one_pos one_pos (by game_cmp) (we ..) (we ..) (we ..)
  rw [← Surreal.mk_lt_mk] at this; simp [mulOption] at this
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow` idx 13: necessary (x = y = w = 0, z = 1, r = s = 1: mulOption = 1, not < 1)
theorem w3c3_36 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow 13 := fun h => by
  have := @h 0 0 1 0 _ _ _ _ 1 1 one_pos one_pos (by game_cmp) (we ..) (we ..) (we ..)
  rw [← Surreal.mk_lt_mk] at this; simp [mulOption] at this
-- mulOption_lt_wpow'
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow'` idx 10: removable (all three terms have exponents below x + y, so any sign of r works)
theorem w3c3_37 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow' 10 := by
  intro x y z w _ _ _ _ r s hs h1 h2 IH1 IH2 IH3
  rw [← Surreal.mk_lt_mk]; simp [mulOption]
  have := L3 (Surreal.mk_lt_mk.2 h1) (Surreal.mk_lt_mk.2 h2) r s (-(r*s))
  refine lt_of_eq_of_lt ?_ this; push_cast; ring
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow'` idx 11: removable (all three terms have exponents below x + y, so any sign of s works)
theorem w3c3_38 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow' 11 := by
  intro x y z w _ _ _ _ r s hr h1 h2 IH1 IH2 IH3
  rw [← Surreal.mk_lt_mk]; simp [mulOption]
  have := L3 (Surreal.mk_lt_mk.2 h1) (Surreal.mk_lt_mk.2 h2) r s (-(r*s))
  refine lt_of_eq_of_lt ?_ this; push_cast; ring
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow'` idx 12: necessary (x = z = w = 0, y = 1, r = s = 1: mulOption = ω, not < ω)
theorem w3c3_39 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow' 12 := fun h => by
  have := @h 0 1 0 0 _ _ _ _ 1 1 one_pos one_pos (by game_cmp) (we ..) (we ..) (we ..)
  rw [← Surreal.mk_lt_mk] at this; simp [mulOption] at this
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow'` idx 13: necessary (y = z = w = 0, x = 1, r = s = 1: mulOption = ω, not < ω)
theorem w3c3_40 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow' 13 := fun h => by
  have := @h 1 0 0 0 _ _ _ _ 1 1 one_pos one_pos (by game_cmp) (we ..) (we ..) (we ..)
  rw [← Surreal.mk_lt_mk] at this; simp [mulOption] at this
-- wpow_lt_mulOption
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.wpow_lt_mulOption` idx 10: necessary (x = w = 0, y = z = 1, r = 0, s = 1: mulOption = 1, ω < 1 false)
theorem w3c3_41 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.wpow_lt_mulOption 10 := fun h => by
  have := @h 0 1 1 0 _ _ _ _ 0 1 one_pos (by game_cmp) (by game_cmp) (we ..) (we ..)
  rw [← Surreal.mk_lt_mk] at this; simp [mulOption] at this
  linarith [oneLtW]
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.wpow_lt_mulOption` idx 11: removable (leading term r ω^(z+y) dominates for any sign of s)
theorem w3c3_42 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.wpow_lt_mulOption 11 := by
  intro x y z w _ _ _ _ r s hr h1 h2 IH1 IH2
  rw [← Surreal.mk_lt_mk]; simp [mulOption]
  have := L4 (Surreal.mk_lt_mk.2 h1) (Surreal.mk_lt_mk.2 h2) r (by exact_mod_cast hr) (-s) (r*s)
  push_cast at this
  linear_combination this
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.wpow_lt_mulOption` idx 12: necessary (x = z = w = 0, y = 1, r = s = 1: mulOption = ω, ω < ω false)
theorem w3c3_43 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.wpow_lt_mulOption 12 := fun h => by
  have := @h 0 1 0 0 _ _ _ _ 1 1 one_pos one_pos (by game_cmp) (we ..) (we ..)
  rw [← Surreal.mk_lt_mk] at this; simp [mulOption] at this
end W3c3

namespace W3c3
open IGame Surreal

theorem numOfW (x : IGame) [h : Numeric (ω^ x)] : Numeric x := by
  have hL : ∀ y ∈ xᴸ, Numeric (ω^ y) := fun y hy => Numeric.of_mem_moves (wpow_mem_moves_left_wpow hy)
  have hR : ∀ y ∈ xᴿ, Numeric (ω^ y) := fun y hy => Numeric.of_mem_moves (wpow_mem_moves_right_wpow hy)
  refine Numeric.mk (fun a ha b hb => ?_) (fun p y hy => ?_)
  · have := hL a ha; have := hR b hb; have := numOfW a; have := numOfW b
    exact Numeric.wpow_lt_wpow.1
      (Numeric.left_lt_right (wpow_mem_moves_left_wpow ha) (wpow_mem_moves_right_wpow hb))
  · cases p
    · have := hL y hy; exact numOfW y
    · have := hR y hy; exact numOfW y
termination_by x
decreasing_by all_goals igame_wf

noncomputable abbrev gS : IGame := !{{1} | {⋆}}
theorem gS_pos : 0 < gS := by game_cmp
theorem gS_not : ¬ Numeric gS := fun h => not_numeric_star (@Numeric.of_mem_moves _ _ Player.right h (by simp))

-- `IGame.Numeric.wpow` idx 1: necessary (x = ⋆: ω^ x numeric would force x numeric)
theorem w3c3_44 : ¬ drop0% IGame.Numeric.wpow 1 := fun h => not_numeric_star (@numOfW ⋆ (h ⋆))
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.wpow_strictMono_aux` idx 2: removable (Numeric x follows from Numeric (ω^ x) (induction: options 1 * ω^ y, ω^ a < ω^ b))
theorem w3c3_45 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.wpow_strictMono_aux 2 := by
  intro x y _ _ _; have := numOfW x
  have k := (priv% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.wpow_strictMono_aux)
  exact k
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.wpow_strictMono_aux` idx 3: removable (Numeric y follows from Numeric (ω^ y))
theorem w3c3_46 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.wpow_strictMono_aux 3 := by
  intro x y _ _ _; have := numOfW y
  have k := (priv% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.wpow_strictMono_aux)
  exact k
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.mk_lt_mk_of_ne` idx 1: necessary (x = {1 | ⋆}: positive, positive left option 1, not numeric)
theorem w3c3_47 : ¬ indep0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.mk_lt_mk_of_ne 1 := fun h =>
  gS_not (@h gS gS_pos 1 (by simp) (by game_cmp))
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.mk_wpow_wlog_left` idx 1: necessary (x = {1 | ⋆}, y = 1)
theorem w3c3_48 : ¬ indep0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.mk_wpow_wlog_left 1 := fun h =>
  gS_not (@h gS ⟨1, by simp, Set.mem_Ioi.2 (by game_cmp)⟩)
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.mk_wpow_wlog_right` idx 1: necessary (x = {1 | ⋆}, y = ⋆)
theorem w3c3_49 : ¬ indep0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.mk_wpow_wlog_right 1 := fun h =>
  gS_not (@h gS gS_pos ⟨⋆, by simp⟩)
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.exists_mk_wpow_eq` idx 1: necessary (x = {1 | ⋆}: positive, not numeric)
theorem w3c3_50 : ¬ indep0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.exists_mk_wpow_eq 1 := fun h =>
  gS_not (@h gS gS_pos)
-- `Surreal.numeric_of_forall_mk_ne_mk` idx 1: necessary (x = {1 | ⋆}: positive, not numeric)
theorem w3c3_51 : ¬ indep0% Surreal.numeric_of_forall_mk_ne_mk 1 := fun h => gS_not (@h gS gS_pos)
-- `Surreal.wpow_equiv_of_forall_mk_ne_mk` idx 1: necessary (x = {1 | ⋆}: positive, not numeric)
theorem w3c3_52 : ¬ indep0% Surreal.wpow_equiv_of_forall_mk_ne_mk 1 := fun h => gS_not (@h gS gS_pos)
-- `Surreal.mem_range_wpow_of_forall_mk_ne_mk` idx 1: necessary (x = {1 | ⋆}: positive, not numeric)
theorem w3c3_53 : ¬ indep0% Surreal.mem_range_wpow_of_forall_mk_ne_mk 1 := fun h => gS_not (@h gS gS_pos)
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.numeric_of_forall_mk_ne_mk'` idx 1: necessary (x = {1 | ⋆}: positive, not numeric)
theorem w3c3_54 : ¬ indep0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.numeric_of_forall_mk_ne_mk' 1 := fun h =>
  gS_not (@h gS gS_pos (fun _ => ⟨0, .zero⟩) (fun _ => ⟨0, .zero⟩))
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.wpow_equiv_of_forall_mk_ne_mk'` idx 1: necessary (x = {1 | ⋆}: positive, not numeric)
theorem w3c3_55 : ¬ indep0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.wpow_equiv_of_forall_mk_ne_mk' 1 := fun h =>
  gS_not (@h gS gS_pos (fun _ => ⟨0, .zero⟩) (fun _ => ⟨0, .zero⟩))
noncomputable abbrev gU : IGame := !{{↑} | ∅}
-- `Surreal.instNumericValIGameMemSetMinMovesLeftIoiOfNat` idx 1: necessary (x = {↑ |}: positive left option ↑ not numeric)
theorem w3c3_56 : ¬ drop0% Surreal.instNumericValIGameMemSetMinMovesLeftIoiOfNat 1 := fun h => by
  have hn := h gU ⟨↑, by simp, up_pos⟩
  exact not_numeric_star (Numeric.of_mem_moves (p := .right) (x := IGame.up) (by simp [IGame.up]))

-- mul_wpow_mem rows
-- `IGame.mul_wpow_mem_moves_left_wpow` idx 3: necessary (x = 1, y = 0, r = -1: -1 is not 0 or a positive dyadic)
theorem w3c3_57 : ¬ drop0% IGame.mul_wpow_mem_moves_left_wpow 3 := fun h => by
  have := @h 1 0 (-1) (by simp)
  simp [moves_left_wpow] at this
  obtain ⟨q, hq, e⟩ := this
  have : q = -1 := Dyadic.toIGame_inj.1 (e.trans (by simp))
  subst this; exact absurd hq (by decide)
-- `IGame.mul_wpow_mem_moves_right_wpow` idx 3: necessary (x = -1, y = 0, r = 0: 0 is not a positive dyadic)
theorem w3c3_58 : ¬ drop0% IGame.mul_wpow_mem_moves_right_wpow 3 := fun h => by
  have := @h (-1) 0 0 (by simp)
  simp [moves_right_wpow] at this
-- `IGame.natCast_mul_wpow_mem_moves_right_wpow` idx 3: necessary (x = -1, y = 0, n = 0)
theorem w3c3_59 : ¬ drop0% IGame.natCast_mul_wpow_mem_moves_right_wpow 3 := fun h => by
  have := @h (-1) 0 0 (by simp)
  simp [moves_right_wpow] at this
end W3c3

namespace W3c3
open IGame Surreal

theorem topNe : (⊤ : ArchimedeanClass Surreal) ≠ 0 := fun e =>
  one_ne_zero (ArchimedeanClass.mk_eq_top_iff.1 (ArchimedeanClass.mk_one.trans e.symm))
noncomputable abbrev two : IGame := ((2:ℕ):IGame)
theorem two_left : twoᴸ = {1} := by
  show ((Nat.succ 1 : ℕ) : IGame)ᴸ = {1}; rw [moves_left_natCast_succ']; simp
theorem mk2 : Surreal.mk two = 2 := Surreal.mk_natCast 2
theorem two_right : twoᴿ = ∅ := moves_right_natCast 2
theorem two_pos : 0 < two := by rw [← Surreal.mk_lt_mk, mk2]; simp
theorem w2e : Surreal.wlog (2:Surreal) = 0 := by simpa using Surreal.wlog_natCast 2
theorem notR2 : mk two ∉ Set.range (ω^ · : Surreal → Surreal) := by
  rintro ⟨y, hy⟩
  rw [mk2] at hy
  have := congrArg Surreal.wlog hy
  simp at this
  subst this; rw [w2e] at hy; simp at hy
theorem notRHalf : mk ½ ∉ Set.range (ω^ · : Surreal → Surreal) := by
  rintro ⟨y, hy⟩
  rw [IGame.mk_half] at hy
  have := congrArg Surreal.wlog hy
  simp at this
  subst this; simp [w2e] at hy; try norm_num at hy

theorem keyW {x a b : IGame} [Numeric x] [Numeric a] [Numeric b] (ha : a ∈ xᴸ) (ha0 : 0 < a) (hb : b ∈ xᴿ)
    (H : ArchimedeanClass.mk (mk a) ≠ .mk (mk x) ∨ ArchimedeanClass.mk (mk b) ≠ .mk (mk x)) :
    (mk a).wlog < (mk b).wlog := by
  have hax := Numeric.left_lt ha
  have hxb := Numeric.lt_right hb
  have hx0 := ha0.trans hax
  have hb0 := hx0.trans hxb
  rw [← Surreal.mk_lt_mk] at hax hxb hx0 hb0 ha0
  simp only [Surreal.mk_zero] at hx0 hb0 ha0
  have m1 : (mk a).wlog ≤ (mk x).wlog := wlog_monotoneOn ha0 hx0 hax.le
  have m2 : (mk x).wlog ≤ (mk b).wlog := wlog_monotoneOn hx0 hb0 hxb.le
  rcases H with H | H
  · have : (mk a).wlog < (mk x).wlog := by
      rw [wlog_lt_wlog_iff ha0.ne' hx0.ne', vlt_def]
      exact lt_of_le_of_ne (ArchimedeanClass.mk_antitoneOn ha0.le hx0.le hax.le) (Ne.symm H)
    exact this.trans_le m2
  · have : (mk x).wlog < (mk b).wlog := by
      rw [wlog_lt_wlog_iff hx0.ne' hb0.ne', vlt_def]
      exact lt_of_le_of_ne (ArchimedeanClass.mk_antitoneOn hx0.le hb0.le hxb.le) H
    exact m1.trans_lt this

-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.mk_lt_mk_of_ne` idx 2: removable (0 < x follows from a positive left option)
theorem w3c3_60 : drop% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.mk_lt_mk_of_ne 2 := by
  intro x _ Hl y hy hy'
  have k := priv% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.mk_lt_mk_of_ne
  exact k (hy'.trans (Numeric.left_lt hy)) Hl y hy hy'
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.mk_lt_mk_of_ne` idx 3: necessary (x = 2, y = 1: same Archimedean class)
theorem w3c3_61 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.mk_lt_mk_of_ne 3 := fun h => by
  have := @h two _ two_pos 1 (by rw [two_left]; rfl) (by game_cmp)
  simp only [mk2] at this; simp at this
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.mk_lt_mk_of_ne'` idx 2: necessary (x = -1, y = 0: class of 0 is top)
theorem w3c3_62 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.mk_lt_mk_of_ne' 2 := fun h => by
  have := @h (-1) _ (fun y hy => by simp at hy; subst hy; simpa using topNe) 0 (by simp)
  simp at this
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.mk_lt_mk_of_ne'` idx 3: necessary (x = ½, y = 1: same Archimedean class)
theorem w3c3_63 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.mk_lt_mk_of_ne' 3 := fun h => by
  have := @h ½ _ zero_lt_half 1 (by simp)
  simp [IGame.mk_half] at this
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.mk_wpow_wlog_right` idx 2: necessary (x = -1, y = 0: class 0 vs top)
theorem w3c3_64 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.mk_wpow_wlog_right 2 := fun h => by
  have := @h (-1) _ ⟨0, by simp⟩
  simp at this

-- `Surreal.numeric_of_forall_mk_ne_mk` idx 3: removable (Hr alone gives wlog a ≤ wlog x < wlog b (wlog monotone on positives))
theorem w3c3_65 : drop% Surreal.numeric_of_forall_mk_ne_mk 3 := by
  intro x _ h Hr
  refine Numeric.mk ?_ ?_
  · simp only [moves_left_ofSets, moves_right_ofSets]
    rintro _ ⟨a, ⟨ha, ha0⟩, rfl⟩ _ ⟨b, hb, rfl⟩
    have := Numeric.of_mem_moves ha; have := Numeric.of_mem_moves hb
    rw [← Surreal.mk_lt_mk, mk_wlog, mk_wlog]
    exact keyW ha ha0 hb (Or.inr (Hr b hb))
  · intro p y hy
    cases p <;> (simp only [moves_left_ofSets, moves_right_ofSets] at hy; obtain ⟨z, -, rfl⟩ := hy; exact Numeric.wlog z)
-- `Surreal.numeric_of_forall_mk_ne_mk` idx 4: removable (Hl alone gives wlog a < wlog x ≤ wlog b)
theorem w3c3_66 : drop% Surreal.numeric_of_forall_mk_ne_mk 4 := by
  intro x _ h Hl
  refine Numeric.mk ?_ ?_
  · simp only [moves_left_ofSets, moves_right_ofSets]
    rintro _ ⟨a, ⟨ha, ha0⟩, rfl⟩ _ ⟨b, hb, rfl⟩
    have := Numeric.of_mem_moves ha; have := Numeric.of_mem_moves hb
    rw [← Surreal.mk_lt_mk, mk_wlog, mk_wlog]
    exact keyW ha ha0 hb (Or.inl (Hl a ha ha0))
  · intro p y hy
    cases p <;> (simp only [moves_left_ofSets, moves_right_ofSets] at hy; obtain ⟨z, -, rfl⟩ := hy; exact Numeric.wlog z)
-- `Surreal.numeric_of_forall_mk_ne_mk` idx 2: removable (0 < x follows from any positive left option; without one the left side is empty)
theorem w3c3_67 : drop% Surreal.numeric_of_forall_mk_ne_mk 2 := by
  intro x _ Hl Hr
  refine Numeric.mk ?_ ?_
  · simp only [moves_left_ofSets, moves_right_ofSets]
    rintro _ ⟨a, ⟨ha, ha0⟩, rfl⟩ _ ⟨b, hb, rfl⟩
    have := Numeric.of_mem_moves ha; have := Numeric.of_mem_moves hb
    rw [← Surreal.mk_lt_mk, mk_wlog, mk_wlog]
    exact keyW ha ha0 hb (Or.inl (Hl a ha ha0))
  · intro p y hy
    cases p <;> (simp only [moves_left_ofSets, moves_right_ofSets] at hy; obtain ⟨z, -, rfl⟩ := hy; exact Numeric.wlog z)

-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.numeric_of_forall_mk_ne_mk'` idx 7: removable (f, g are wlog by hf, hg; Hr alone gives wlog a ≤ wlog x < wlog b)
theorem w3c3_68 : drop% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.numeric_of_forall_mk_ne_mk' 7 := by
  intro x _ h f g hf hg Hr
  refine Numeric.mk ?_ ?_
  · simp only [moves_left_ofSets, moves_right_ofSets]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have := (f a).2; have := (g b).2
    have := Numeric.of_mem_moves a.2.1; have := Numeric.of_mem_moves b.2
    simp only [Function.comp_apply]; rw [← Surreal.mk_lt_mk]
    rw [← wlog_eq_of_wpow_veq (veq_def.2 (hf a)), ← wlog_eq_of_wpow_veq (veq_def.2 (hg b))]
    exact keyW a.2.1 a.2.2 b.2 (Or.inr (Hr _ b.2))
  · aesop (add simp [Subtype.prop])
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.numeric_of_forall_mk_ne_mk'` idx 8: removable (f, g are wlog by hf, hg; Hl alone gives wlog a < wlog x ≤ wlog b)
theorem w3c3_69 : drop% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.numeric_of_forall_mk_ne_mk' 8 := by
  intro x _ h f g hf hg Hl
  refine Numeric.mk ?_ ?_
  · simp only [moves_left_ofSets, moves_right_ofSets]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have := (f a).2; have := (g b).2
    have := Numeric.of_mem_moves a.2.1; have := Numeric.of_mem_moves b.2
    simp only [Function.comp_apply]; rw [← Surreal.mk_lt_mk]
    rw [← wlog_eq_of_wpow_veq (veq_def.2 (hf a)), ← wlog_eq_of_wpow_veq (veq_def.2 (hg b))]
    exact keyW a.2.1 a.2.2 b.2 (Or.inl (Hl _ a.2.1 a.2.2))
  · aesop (add simp [Subtype.prop])
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.numeric_of_forall_mk_ne_mk'` idx 2: removable (0 < x follows from any positive left option)
theorem w3c3_70 : drop% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.numeric_of_forall_mk_ne_mk' 2 := by
  intro x _ f g hf hg Hl Hr
  refine Numeric.mk ?_ ?_
  · simp only [moves_left_ofSets, moves_right_ofSets]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have := (f a).2; have := (g b).2
    have := Numeric.of_mem_moves a.2.1; have := Numeric.of_mem_moves b.2
    simp only [Function.comp_apply]; rw [← Surreal.mk_lt_mk]
    rw [← wlog_eq_of_wpow_veq (veq_def.2 (hf a)), ← wlog_eq_of_wpow_veq (veq_def.2 (hg b))]
    exact keyW a.2.1 a.2.2 b.2 (Or.inl (Hl _ a.2.1 a.2.2))
  · aesop (add simp [Subtype.prop])

-- `Surreal.mem_range_wpow_of_forall_mk_ne_mk` idx 3: necessary (x = 2 (no right options): 2 is not a power of ω)
theorem w3c3_71 : ¬ drop0% Surreal.mem_range_wpow_of_forall_mk_ne_mk 3 := fun h =>
  notR2 (@h two _ two_pos (fun y hy => by simp [two_right] at hy))
-- `Surreal.mem_range_wpow_of_forall_mk_ne_mk` idx 4: necessary (x = ½ (no positive left option): ½ is not a power of ω)
theorem w3c3_72 : ¬ drop0% Surreal.mem_range_wpow_of_forall_mk_ne_mk 4 := fun h =>
  notRHalf (@h ½ _ zero_lt_half (fun y hy hy' => by simp at hy; subst hy; exact absurd hy' (lt_irrefl _)))
-- `Surreal.wpow_equiv_of_forall_mk_ne_mk` idx 3: necessary (x = 2: would put 2 in the range of ω^)
theorem w3c3_73 : ¬ drop0% Surreal.wpow_equiv_of_forall_mk_ne_mk 3 := fun h => w3c3_71 (by
  intro x _ hx Hr
  have := w3c3_65 hx Hr
  exact ⟨_, (Surreal.mk_wpow _).symm.trans (Surreal.mk_eq (h hx Hr))⟩)
-- `Surreal.wpow_equiv_of_forall_mk_ne_mk` idx 4: necessary (x = ½: would put ½ in the range of ω^)
theorem w3c3_74 : ¬ drop0% Surreal.wpow_equiv_of_forall_mk_ne_mk 4 := fun h => w3c3_72 (by
  intro x _ hx Hl
  have := w3c3_66 hx Hl
  exact ⟨_, (Surreal.mk_wpow _).symm.trans (Surreal.mk_eq (h hx Hl))⟩)
-- `Surreal.wpow_equiv_of_forall_mk_ne_mk` idx 2: necessary (x = 0: ω^ 0-game ≈ 0 contradicts 0 ⧏ ω^ _)
theorem w3c3_75 : ¬ drop0% Surreal.wpow_equiv_of_forall_mk_ne_mk 2 := fun h =>
  zero_lf_wpow _ (@h 0 _ (fun y hy => by simp at hy) (fun y hy => by simp at hy)).le
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.wpow_equiv_of_forall_mk_ne_mk'` idx 2: necessary (x = 0: contradicts 0 ⧏ ω^ _)
theorem w3c3_76 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.wpow_equiv_of_forall_mk_ne_mk' 2 := fun h =>
  zero_lf_wpow _ (@h 0 _ (fun _ => ⟨0, .zero⟩) (fun _ => ⟨0, .zero⟩) (fun y => absurd y.2.1 (by simp))
    (fun y => absurd y.2 (by simp)) (fun y hy => by simp at hy) (fun y hy => by simp at hy)).le

-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.wpow_equiv_of_forall_mk_ne_mk'` idx 7: necessary (x = 2, f = 0: would put 2 in the range of ω^)
theorem w3c3_77 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.wpow_equiv_of_forall_mk_ne_mk' 7 := fun h => by
  let f : ↑(twoᴸ ∩ Set.Ioi 0) → Subtype Numeric := fun _ => ⟨0, .zero⟩
  let g : ↑twoᴿ → Subtype Numeric := fun _ => ⟨0, .zero⟩
  have hf : ∀ y, ArchimedeanClass.mk (ω^ mk (f y).1) = .mk (@mk y.1 (Numeric.of_mem_moves y.2.1)) := by
    rintro ⟨y, hy, -⟩; rw [two_left] at hy; obtain rfl := hy; simp [f]
  have hg : ∀ y, ArchimedeanClass.mk (ω^ mk (g y).1) = .mk (@mk y.1 (Numeric.of_mem_moves y.2)) := by
    rintro ⟨y, hy⟩; rw [two_right] at hy; exact absurd hy (Set.notMem_empty _)
  have := w3c3_68 two_pos hf hg (fun y hy => absurd (two_right ▸ hy) (Set.notMem_empty _))
  exact notR2 ⟨_, (Surreal.mk_wpow _).symm.trans (Surreal.mk_eq
    (h two_pos hf hg (fun y hy => absurd (two_right ▸ hy) (Set.notMem_empty _))))⟩
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.wpow_equiv_of_forall_mk_ne_mk'` idx 8: necessary (x = ½, g = 0: would put ½ in the range of ω^)
theorem w3c3_78 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.wpow_equiv_of_forall_mk_ne_mk' 8 := fun h => by
  let f : ↑(½ᴸ ∩ Set.Ioi 0) → Subtype Numeric := fun _ => ⟨0, .zero⟩
  let g : ↑½ᴿ → Subtype Numeric := fun _ => ⟨0, .zero⟩
  have hf : ∀ y, ArchimedeanClass.mk (ω^ mk (f y).1) = .mk (@mk y.1 (Numeric.of_mem_moves y.2.1)) := by
    rintro ⟨y, hy, hy'⟩; simp at hy; subst hy; exact absurd (Set.mem_Ioi.1 hy') (lt_irrefl _)
  have hg : ∀ y, ArchimedeanClass.mk (ω^ mk (g y).1) = .mk (@mk y.1 (Numeric.of_mem_moves y.2)) := by
    rintro ⟨y, hy⟩; simp at hy; subst hy; simp [g]
  have Hl : ∀ (y : IGame) (hy : y ∈ ½ᴸ), 0 < y → ArchimedeanClass.mk (@mk y (Numeric.of_mem_moves hy)) ≠ .mk (mk ½) := by
    intro y hy hy'; simp at hy; subst hy; exact absurd hy' (lt_irrefl _)
  have := w3c3_69 zero_lt_half hf hg Hl
  exact notRHalf ⟨_, (Surreal.mk_wpow _).symm.trans (Surreal.mk_eq (h zero_lt_half hf hg Hl))⟩
end W3c3

namespace W3c3
open IGame Surreal

theorem clsW {a b : Surreal} : ArchimedeanClass.mk (ω^ a) = ArchimedeanClass.mk (ω^ b) ↔ a = b := by
  rw [← veq_def, wpow_veq_wpow_iff]
theorem clsMul (r : Dyadic) (hr : 0 < r) (y : IGame) [Numeric y] :
    ArchimedeanClass.mk (mk ((r:IGame) * ω^ y)) = ArchimedeanClass.mk (ω^ mk y) := by
  simp; exact ArchimedeanClass.mk_ratCast (by exact_mod_cast hr.ne')

theorem notMemE {s : Set IGame} (hs : s = ∅) (y : IGame) (h : y ∈ s) : False := by
  rw [hs] at h; exact h

-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.wpow_equiv_of_forall_mk_ne_mk'` idx 5: necessary (x = ω^ 1, f = 1 (should be 0): ω^ {1|} ≈ ω^ 1 would give {1|} ≤ 1)
theorem w3c3_79 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.wpow_equiv_of_forall_mk_ne_mk' 5 := fun h => by
  let f : ↑((ω^ (1:IGame))ᴸ ∩ Set.Ioi 0) → Subtype Numeric := fun _ => ⟨1, .one⟩
  let g : ↑(ω^ (1:IGame))ᴿ → Subtype Numeric := fun _ => ⟨1, .one⟩
  have hR : (ω^ (1:IGame))ᴿ = ∅ := by simp [moves_right_wpow]
  have hg : ∀ y : ↑(ω^ (1:IGame))ᴿ, ArchimedeanClass.mk (ω^ mk (g y).1) = .mk (@mk y.1 (Numeric.of_mem_moves y.2)) :=
    fun y => (notMemE hR _ y.2).elim
  have Hl : ∀ (y : IGame) (hy : y ∈ (ω^ (1:IGame))ᴸ), 0 < y →
      ArchimedeanClass.mk (@mk y (Numeric.of_mem_moves hy)) ≠ .mk (mk (ω^ (1:IGame))) := by
    intro y hy hy0
    have hy' := hy
    rw [moves_left_wpow] at hy'
    rcases hy' with rfl | ⟨r, hr, z, hz, rfl⟩
    · exact absurd hy0 (lt_irrefl _)
    · simp at hz; subst hz
      rw [clsMul r hr 0, Surreal.mk_wpow, Ne, clsW]; simp
  have e := @h (ω^ (1:IGame)) _ (Numeric.wpow_pos _) f g hg Hl (fun y hy => (notMemE hR _ hy).elim)
  have hG : Numeric !{Set.range (Subtype.val ∘ f) | Set.range (Subtype.val ∘ g)} := by
    apply Numeric.mk
    · simp only [moves_left_ofSets, moves_right_ofSets]
      rintro _ _ _ ⟨b, rfl⟩; exact (notMemE hR _ b.2).elim
    · aesop (add simp [Subtype.prop])
  have h1 := Numeric.wpow_le_wpow.1 e.le
  have hmem : (1:IGame) ∈ (ω^ (1:IGame))ᴸ ∩ Set.Ioi 0 := ⟨by simp [moves_left_wpow], Set.mem_Ioi.2 (by game_cmp)⟩
  exact left_lf (show (1:IGame) ∈ (!{Set.range (Subtype.val ∘ f) | Set.range (Subtype.val ∘ g)})ᴸ by
    simp only [moves_left_ofSets]; exact ⟨⟨1, hmem⟩, rfl⟩) h1

-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.wpow_equiv_of_forall_mk_ne_mk'` idx 6: necessary (x = ω^ -1, g = 1 (should be 0): {|1} ≥ 0 but would be ≤ -1)
theorem w3c3_80 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.wpow_equiv_of_forall_mk_ne_mk' 6 := fun h => by
  let f : ↑((ω^ (-1:IGame))ᴸ ∩ Set.Ioi 0) → Subtype Numeric := fun _ => ⟨0, .zero⟩
  let g : ↑(ω^ (-1:IGame))ᴿ → Subtype Numeric := fun _ => ⟨1, .one⟩
  have hL : ∀ y ∈ (ω^ (-1:IGame))ᴸ, y = 0 := by intro y hy; simpa [moves_left_wpow] using hy
  have hf : ∀ y : ↑((ω^ (-1:IGame))ᴸ ∩ Set.Ioi 0), ArchimedeanClass.mk (ω^ mk (f y).1) = .mk (@mk y.1 (Numeric.of_mem_moves y.2.1)) := by
    rintro ⟨y, hy, hy0⟩; obtain rfl := hL y hy; exact absurd (Set.mem_Ioi.1 hy0) (lt_irrefl _)
  have Hl : ∀ (y : IGame) (hy : y ∈ (ω^ (-1:IGame))ᴸ), 0 < y →
      ArchimedeanClass.mk (@mk y (Numeric.of_mem_moves hy)) ≠ .mk (mk (ω^ (-1:IGame))) := by
    intro y hy hy0; obtain rfl := hL y hy; exact absurd hy0 (lt_irrefl _)
  have Hr : ∀ (y : IGame) (hy : y ∈ (ω^ (-1:IGame))ᴿ),
      ArchimedeanClass.mk (@mk y (Numeric.of_mem_moves hy)) ≠ .mk (mk (ω^ (-1:IGame))) := by
    intro y hy
    have hy' := hy
    rw [moves_right_wpow] at hy'
    obtain ⟨r, hr, z, hz, rfl⟩ := hy'
    simp at hz; subst hz
    rw [clsMul r hr 0, Surreal.mk_wpow, Ne, clsW]; simp
  have e := @h (ω^ (-1:IGame)) _ (Numeric.wpow_pos _) f g hf Hl Hr
  have hG : Numeric !{Set.range (Subtype.val ∘ f) | Set.range (Subtype.val ∘ g)} := by
    apply Numeric.mk
    · simp only [moves_left_ofSets, moves_right_ofSets]
      rintro _ ⟨⟨a, ha, ha0⟩, rfl⟩; obtain rfl := hL a ha; exact absurd (Set.mem_Ioi.1 ha0) (lt_irrefl _)
    · aesop (add simp [Subtype.prop])
  have h1 := Numeric.wpow_le_wpow.1 e.le
  have h0 : (0:IGame) ≤ !{Set.range (Subtype.val ∘ f) | Set.range (Subtype.val ∘ g)} := by
    rw [le_iff_forall_lf]; refine ⟨by simp, ?_⟩
    simp only [moves_right_ofSets]
    rintro _ ⟨c, rfl⟩; exact (by game_cmp : (0:IGame) ⧏ 1)
  exact absurd (h0.trans h1) (by game_cmp)

noncomputable abbrev y0 : IGame := !{{-1} | {1}}
instance y0num : Numeric y0 := by
  apply Numeric.mk
  · simp only [moves_left_ofSets, moves_right_ofSets, Set.mem_singleton_iff]
    rintro _ rfl _ rfl; game_cmp
  · intro p y hy; cases p <;> simp at hy <;> subst hy <;> infer_instance
theorem mky0 : mk y0 = 0 := by
  rw [← Surreal.mk_zero, Surreal.mk_eq_mk]; game_cmp
theorem y0L : ∀ a ∈ (ω^ y0)ᴸ, 0 < a → ∃ r : Dyadic, 0 < r ∧ a = r * ω^ (-1 : IGame) := by
  intro a ha ha0
  rw [moves_left_wpow] at ha
  rcases ha with rfl | ⟨r, hr, z, hz, rfl⟩
  · exact absurd ha0 (lt_irrefl _)
  · simp at hz; subst hz; exact ⟨r, hr, rfl⟩
theorem y0R : ∀ b ∈ (ω^ y0)ᴿ, ∃ r : Dyadic, 0 < r ∧ b = r * ω^ (1 : IGame) := by
  intro b hb
  rw [moves_right_wpow] at hb
  obtain ⟨r, hr, z, hz, rfl⟩ := hb
  simp at hz; subst hz; exact ⟨r, hr, rfl⟩
theorem y0Hl : ∀ (y : IGame) (hy : y ∈ (ω^ y0)ᴸ), 0 < y →
    ArchimedeanClass.mk (@mk y (Numeric.of_mem_moves hy)) ≠ .mk (mk (ω^ y0)) := by
  intro y hy hy0
  obtain ⟨r, hr, rfl⟩ := y0L y hy hy0
  rw [clsMul r hr, Surreal.mk_wpow, Ne, clsW, mky0]; simp
theorem y0Hr : ∀ (y : IGame) (hy : y ∈ (ω^ y0)ᴿ),
    ArchimedeanClass.mk (@mk y (Numeric.of_mem_moves hy)) ≠ .mk (mk (ω^ y0)) := by
  intro y hy
  obtain ⟨r, hr, rfl⟩ := y0R y hy
  rw [clsMul r hr, Surreal.mk_wpow, Ne, clsW, mky0]; simp
theorem y0lm : ω^ (-1 : IGame) ∈ (ω^ y0)ᴸ ∩ Set.Ioi 0 :=
  ⟨wpow_mem_moves_left_wpow (by simp), Set.mem_Ioi.2 (Numeric.wpow_pos _)⟩
theorem y0rm : ω^ (1 : IGame) ∈ (ω^ y0)ᴿ := wpow_mem_moves_right_wpow (by simp)

-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.numeric_of_forall_mk_ne_mk'` idx 5: necessary (x = ω^ {-1|1} (≈ 1), f = g = 1: {1|1} not numeric)
theorem w3c3_81 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.numeric_of_forall_mk_ne_mk' 5 := fun h => by
  let f : ↑((ω^ y0)ᴸ ∩ Set.Ioi 0) → Subtype Numeric := fun _ => ⟨1, .one⟩
  let g : ↑(ω^ y0)ᴿ → Subtype Numeric := fun _ => ⟨1, .one⟩
  have hg : ∀ y : ↑(ω^ y0)ᴿ, ArchimedeanClass.mk (ω^ mk (g y).1) = .mk (@mk y.1 (Numeric.of_mem_moves y.2)) := by
    rintro ⟨y, hy⟩
    obtain ⟨r, hr, rfl⟩ := y0R y hy
    rw [clsMul r hr]
  have hG := @h (ω^ y0) _ (Numeric.wpow_pos _) f g hg y0Hl y0Hr
  exact lt_irrefl (1:IGame) (@Numeric.left_lt_right _ _ _ hG
    (by simp only [moves_left_ofSets]; exact ⟨⟨_, y0lm⟩, rfl⟩)
    (by simp only [moves_right_ofSets]; exact ⟨⟨_, y0rm⟩, rfl⟩))
-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.numeric_of_forall_mk_ne_mk'` idx 6: necessary (x = ω^ {-1|1} (≈ 1), f = g = -1: {-1|-1} not numeric)
theorem w3c3_82 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.numeric_of_forall_mk_ne_mk' 6 := fun h => by
  let f : ↑((ω^ y0)ᴸ ∩ Set.Ioi 0) → Subtype Numeric := fun _ => ⟨-1, inferInstance⟩
  let g : ↑(ω^ y0)ᴿ → Subtype Numeric := fun _ => ⟨-1, inferInstance⟩
  have hf : ∀ y : ↑((ω^ y0)ᴸ ∩ Set.Ioi 0), ArchimedeanClass.mk (ω^ mk (f y).1) = .mk (@mk y.1 (Numeric.of_mem_moves y.2.1)) := by
    rintro ⟨y, hy, hy0⟩
    obtain ⟨r, hr, rfl⟩ := y0L y hy hy0
    rw [clsMul r hr]
  have hG := @h (ω^ y0) _ (Numeric.wpow_pos _) f g hf y0Hl y0Hr
  exact lt_irrefl (-1:IGame) (@Numeric.left_lt_right _ _ _ hG
    (by simp only [moves_left_ofSets]; exact ⟨⟨_, y0lm⟩, rfl⟩)
    (by simp only [moves_right_ofSets]; exact ⟨⟨_, y0rm⟩, rfl⟩))
end W3c3

namespace W3c3
open IGame Surreal

noncomputable abbrev two0 : IGame.{0} := ((2:ℕ):IGame)
theorem two0_left : two0ᴸ = {1} := by
  show ((Nat.succ 1 : ℕ) : IGame.{0})ᴸ = {1}; rw [moves_left_natCast_succ']; simp
theorem two0_right : two0ᴿ = ∅ := moves_right_natCast 2
theorem dTwo : ((2:Dyadic):IGame.{0}) = two0 := by simpa using Dyadic.toIGame_natCast 2

noncomputable abbrev Gs : IGame.{0} := ω^ (⋆ : IGame)
theorem Gs_nonneg : (0:IGame) ≤ Gs := by
  rw [le_iff_forall_lf]; refine ⟨by simp, ?_⟩
  intro b hb
  rw [moves_right_wpow] at hb
  obtain ⟨r, hr, z, hz, rfl⟩ := hb
  simp at hz; subst hz
  have : ((0:Dyadic):IGame.{0}) < r := Dyadic.toIGame_lt_toIGame.2 hr
  simp at this ⊢; first | exact this | exact this.not_ge
theorem one_mem_Gs : (1:IGame) ∈ Gsᴸ := by simp [moves_left_wpow]
theorem K : (1:IGame) ≤ two0 * Gs := by
  rw [le_iff_forall_lf]; constructor
  · intro z hz; simp at hz; subst hz
    rw [lf_iff_exists_le]; left
    refine ⟨mulOption two0 Gs 1 0, mulOption_mem_moves_mul (px := .left) (py := .left) (by simp [two0_left]) (zero_mem_moves_left_wpow _), ?_⟩
    simp [mulOption, Gs_nonneg]
  · intro z hz
    rw [moves_mul] at hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hz
    simp [two0_left, two0_right] at hab
    obtain ⟨rfl, hb⟩ := hab
    rw [moves_right_wpow] at hb
    obtain ⟨r, hr, z, hz, rfl⟩ := hb
    simp at hz; subst hz
    rw [lf_iff_exists_le]; left
    simp only [IGame.wpow_zero, mul_one]
    refine ⟨(1 + two0 * r) - 1 * r, ?_, ?_⟩
    · rw [moves_mulOption]
      rw [moves_sub]; left
      exact ⟨_, add_right_mem_moves_add (by rw [one_mul]; exact one_mem_Gs) _, rfl⟩
    · have hr' : (0:ℚ) < r := by exact_mod_cast hr
      rw [← Surreal.mk_le_mk]; simp
      have e : Surreal.mk (2:IGame.{0}) = 2 := Surreal.mk_natCast 2
      rw [e]
      have : (0:Surreal.{0}) < ((r:ℚ):Surreal.{0}) := by exact_mod_cast hr'
      linarith

noncomputable abbrev Ys : IGame.{0} := !{{⋆} | ∅}
theorem Ys_equiv : Ys ≈ 0 := by game_cmp
theorem wY_not_le : ¬ (ω^ Ys ≤ 1) :=
  lf_of_le_left (by rw [dTwo]; exact K) (mul_wpow_mem_moves_left_wpow (by decide) (by simp))
theorem one_le_wY : (1:IGame) ≤ ω^ Ys := by
  rw [le_iff_forall_lf]; constructor
  · intro z hz; simp at hz; subst hz; exact zero_lf_wpow _
  · intro z hz; simp [moves_right_wpow] at hz
theorem one_lt_wY : (1:IGame) < ω^ Ys := lt_of_le_not_ge one_le_wY wY_not_le

-- `IGame.Numeric.wpow_lt_wpow` idx 3: necessary (x = 0, y = {⋆|} ≈ 0: ω^ y > 1 (left option 2·ω^ ⋆ ≥ 1) but not 0 < y)
theorem w3c3_83 : ¬ drop0% IGame.Numeric.wpow_lt_wpow 3 := fun h => by
  have := (@h 0 Ys _)
  rw [IGame.wpow_zero] at this
  exact (this.1 one_lt_wY).not_ge Ys_equiv.1
-- `IGame.Numeric.wpow_le_wpow` idx 2: necessary (x = {⋆|} ≈ 0, y = 0: x ≤ 0 but ω^ x not ≤ 1)
theorem w3c3_84 : ¬ drop0% IGame.Numeric.wpow_le_wpow 2 := fun h => by
  have := (@h Ys 0 _).2 Ys_equiv.1
  rw [IGame.wpow_zero] at this
  exact wY_not_le this
-- `IGame.Numeric.wpow_congr` idx 2: necessary (x = {⋆|} ≈ 0 = y, but ω^ x not ≤ 1)
theorem w3c3_85 : ¬ drop0% IGame.Numeric.wpow_congr 2 := fun h => by
  have := (@h Ys 0 _ Ys_equiv).1
  rw [IGame.wpow_zero] at this
  exact wY_not_le this
-- `IGame.Numeric.wpow_congr` idx 3: necessary (x = 0 ≈ y = {⋆|}, but ω^ y not ≤ 1)
theorem w3c3_86 : ¬ drop0% IGame.Numeric.wpow_congr 3 := fun h => by
  have := (@h 0 Ys _ Ys_equiv.symm).2
  rw [IGame.wpow_zero] at this
  exact wY_not_le this

theorem mkTwo : Surreal.mk (2:IGame.{0}) = 2 := Surreal.mk_natCast 2
theorem mkThree : Surreal.mk (3:IGame.{0}) = 3 := Surreal.mk_natCast 3
theorem two_mem_Gs : (2:IGame.{0}) ∈ Gsᴸ := by
  simp [moves_left_wpow]; exact ⟨2, by decide, by simpa using Dyadic.toIGame_natCast 2⟩
theorem monoS {a a' b c d e : IGame} (h : a ≤ a') : a + b - c + d - e ≤ a' + b - c + d - e := by
  simp only [sub_eq_add_neg]
  exact add_le_add_left (add_le_add_left (add_le_add_left (add_le_add_left h _) _) _) _
theorem stepQ (k : ℕ) (h0 : (k:IGame.{0}) ≤ ((k+1:ℕ):IGame) * Gs) (h1 : ((k+1:ℕ):IGame.{0}) ≤ ((k+2:ℕ):IGame) * Gs) :
    ((k+2:ℕ):IGame.{0}) ≤ ((k+3:ℕ):IGame) * Gs := by
  rw [le_iff_forall_lf]; constructor
  · intro z hz
    have e : ((k+2:ℕ):IGame.{0})ᴸ = {((k+1:ℕ):IGame)} := moves_left_natCast_succ' (k+1)
    rw [e] at hz
    simp only [Set.mem_singleton_iff] at hz; subst hz
    rw [lf_iff_exists_le]; left
    refine ⟨mulOption ((k+3:ℕ):IGame) Gs ((k+2:ℕ):IGame) 0,
      mulOption_mem_moves_mul (px := .left) (py := .left) ?_ (zero_mem_moves_left_wpow _), ?_⟩
    · have e : ((k+3:ℕ):IGame.{0})ᴸ = {((k+2:ℕ):IGame)} := moves_left_natCast_succ' (k+2)
      rw [e]; rfl
    · simp only [mulOption, mul_zero, add_zero, sub_zero]; exact h1
  · intro z hz
    rw [moves_mul] at hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hz
    simp only [Player.neg_right, Set.mem_union, Set.mem_prod, moves_right_natCast, Set.mem_empty_iff_false,
      false_and, or_false] at hab
    obtain ⟨ha, hb⟩ := hab
    have e : ((k+3:ℕ):IGame.{0})ᴸ = {((k+2:ℕ):IGame)} := moves_left_natCast_succ' (k+2)
    rw [e, Set.mem_singleton_iff] at ha
    subst ha
    rw [moves_right_wpow] at hb
    obtain ⟨r, hr, w, hw, rfl⟩ := hb
    simp at hw; subst hw
    simp only [IGame.wpow_zero, mul_one]
    rw [lf_iff_exists_le]; left
    refine ⟨mulOption ((k+2:ℕ):IGame) Gs ((k+1:ℕ):IGame) 2 + ((k+3:ℕ):IGame) * r - ((k+2:ℕ):IGame) * r, ?_, ?_⟩
    · rw [moves_mulOption, moves_sub]; left
      refine ⟨_, add_right_mem_moves_add (mulOption_mem_moves_mul (px := .left) (py := .left) ?_ two_mem_Gs) _, rfl⟩
      have e : ((k+2:ℕ):IGame.{0})ᴸ = {((k+1:ℕ):IGame)} := moves_left_natCast_succ' (k+1)
      rw [e]; rfl
    · unfold mulOption
      refine le_trans ?_ (monoS (b := ((k+2:ℕ):IGame) * 2) (c := ((k+1:ℕ):IGame) * 2)
        (d := ((k+3:ℕ):IGame) * r) (e := ((k+2:ℕ):IGame) * r) h0)
      have hr' : (0:ℚ) < r := by exact_mod_cast hr
      rw [← Surreal.mk_le_mk]; simp [mkTwo, mkThree]
      have : (0:Surreal.{0}) < ((r:ℚ):Surreal.{0}) := by exact_mod_cast hr'
      push_cast; linarith
theorem allQ : ∀ n : ℕ, (n:IGame.{0}) ≤ ((n+1:ℕ):IGame) * Gs ∧ ((n+1:ℕ):IGame.{0}) ≤ ((n+2:ℕ):IGame) * Gs
  | 0 => ⟨by simpa using Gs_nonneg, by simpa using K⟩
  | n+1 => ⟨(allQ n).2, stepQ n (allQ n).1 (allQ n).2⟩
theorem w1_le_wY : ω^ (1:IGame.{0}) ≤ ω^ Ys := by
  rw [le_iff_forall_lf]; constructor
  · intro z hz
    rw [moves_left_wpow] at hz
    rcases hz with rfl | ⟨r, hr, w, hw, rfl⟩
    · exact zero_lf_wpow _
    · simp at hw; subst hw
      simp only [IGame.wpow_zero, mul_one]
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (r:ℚ) ≤ n := ⟨_, Nat.le_ceil _⟩
      have hle : (r:IGame.{0}) ≤ (n:IGame) := by
        rw [← Surreal.mk_le_mk]; simp; exact_mod_cast hn
      refine lf_of_le_left (hle.trans (allQ n).1) ?_
      have hm : (((n+1:ℕ):Dyadic):IGame.{0}) * ω^ ⋆ ∈ (ω^ Ys)ᴸ :=
        mul_wpow_mem_moves_left_wpow (by positivity) (by simp)
      rw [Dyadic.toIGame_natCast] at hm; exact hm
  · intro z hz; simp [moves_right_wpow] at hz

theorem Ys_lt_one : Ys < 1 := by game_cmp
theorem not_wY_lt_w1 : ¬ (ω^ Ys < ω^ (1:IGame.{0})) := fun h => h.not_ge w1_le_wY

-- `IGame.Numeric.wpow_lt_wpow` idx 2: necessary (x = {⋆|} < 1 = y, but ω^ 1 ≤ ω^ x (n ≤ (n+1)·ω^ ⋆ for all n))
theorem w3c3_87 : ¬ drop0% IGame.Numeric.wpow_lt_wpow 2 := fun h => not_wY_lt_w1 ((@h Ys 1 _).2 Ys_lt_one)
-- `IGame.Numeric.wpow_le_wpow` idx 3: necessary (x = 1, y = {⋆|}: ω^ 1 ≤ ω^ y but not 1 ≤ y)
theorem w3c3_88 : ¬ drop0% IGame.Numeric.wpow_le_wpow 3 := fun h => by
  have := (@h 1 Ys _).1 w1_le_wY
  exact (Ys_lt_one.not_ge this)
-- `IGame.Numeric.mul_wpow_lt_wpow'` idx 2: necessary (x = {⋆|}, y = 1, r = 1: ω^ 1 ≤ ω^ x)
theorem w3c3_89 : ¬ drop0% IGame.Numeric.mul_wpow_lt_wpow' 2 := fun h => by
  have := @h Ys 1 _ 1 Ys_lt_one
  simp only [Dyadic.toIGame_one, one_mul] at this
  exact not_wY_lt_w1 this
-- `IGame.Numeric.wpow_lt_mul_wpow'` idx 2: necessary (x = {⋆|}, y = 1, r = 1: ω^ 1 ≤ ω^ x)
theorem w3c3_90 : ¬ drop0% IGame.Numeric.wpow_lt_mul_wpow' 2 := fun h => by
  have := @h Ys 1 _ 1 (by decide) Ys_lt_one
  simp only [Dyadic.toIGame_one, one_mul] at this
  exact not_wY_lt_w1 this
-- `IGame.Numeric.mul_wpow_lt_mul_wpow_of_pos'` idx 2: necessary (x = {⋆|}, y = 1, r = s = 1: ω^ 1 ≤ ω^ x)
theorem w3c3_91 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_of_pos' 2 := fun h => by
  have := @h Ys 1 _ 1 1 (by decide) Ys_lt_one
  simp only [Dyadic.toIGame_one, one_mul] at this
  exact not_wY_lt_w1 this
-- `IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow'` idx 3: necessary (x = {⋆|}, y = 0, z = 1, r = t = 1, s = 0: ω^ 1 ≤ ω^ x)
theorem w3c3_92 : ¬ drop0% IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow' 3 := fun h => by
  have := @h Ys 0 1 _ _ 1 0 1 (by decide) Ys_lt_one (by game_cmp)
  simp only [Dyadic.toIGame_one, Dyadic.toIGame_zero, one_mul, zero_mul, add_zero] at this
  exact not_wY_lt_w1 this
-- `IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow'` idx 4: necessary (y = {⋆|}, x = 0, z = 1, s = t = 1, r = 0: ω^ 1 ≤ ω^ y)
theorem w3c3_93 : ¬ drop0% IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow' 4 := fun h => by
  have := @h 0 Ys 1 _ _ 0 1 1 (by decide) (by game_cmp) Ys_lt_one
  simp only [Dyadic.toIGame_one, Dyadic.toIGame_zero, one_mul, zero_mul, zero_add] at this
  exact not_wY_lt_w1 this
-- `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow'` idx 3: necessary (x = {⋆|}, y = z = 1, r = 1, s = t = 1/2: ω^ 1 ≤ ω^ x)
theorem w3c3_94 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow' 3 := fun h => by
  have := @h Ys 1 1 _ _ 1 Dyadic.half Dyadic.half (by decide) (by decide) Ys_lt_one Ys_lt_one
  simp only [Dyadic.toIGame_one, one_mul] at this
  have hle : (Dyadic.half : IGame.{0}) * ω^ (1:IGame) + (Dyadic.half : IGame) * ω^ (1:IGame) ≤ ω^ (1:IGame) := by
    rw [← Surreal.mk_le_mk]; simp
    exact le_of_eq (by ring)
  exact this.not_ge (hle.trans w1_le_wY)

-- `IGame.Numeric.wpow_lt_mul_wpow` idx 2: necessary (x = {⋆|}, y = 1, r = 1: 1·ω^ 1 ≤ ω^ 1 ≤ ω^ x)
theorem w3c3_95 : ¬ drop0% IGame.Numeric.wpow_lt_mul_wpow 2 := fun h => by
  have := @h Ys 1 _ 1 one_pos Ys_lt_one
  have hle : ((1:ℝ) : IGame.{0}) * ω^ (1:IGame) ≤ ω^ (1:IGame) := by
    rw [← Surreal.mk_le_mk]; simp
  exact this.not_ge (hle.trans w1_le_wY)

-- `IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg'` idx 3: necessary (x = 1, y = {⋆|} < 1, r = s = -1: -ω^ 1 < -ω^ y false since ω^ 1 ≤ ω^ y)
theorem w3c3_96 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg' 3 := fun h => by
  have := @h 1 Ys _ (-1) (-1) (by decide) Ys_lt_one
  simp only [Dyadic.toIGame_neg, Dyadic.toIGame_one, neg_mul, one_mul] at this
  exact not_wY_lt_w1 (IGame.neg_lt_neg_iff.1 this)
end W3c3

namespace W3c3
open IGame Surreal
theorem weq (a b : IGame) [Numeric a] [Numeric b] : ω^ (a + b) ≈ ω^ a * ω^ b := Numeric.wpow_add_equiv a b
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow` idx 14: removable (the IH equivalence is an instance of wpow_add_equiv for numeric games)
theorem w3c3_97 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow 14 := by
  intro x y z w _ _ _ _ r s hr hs h1 h2 I1 I2
  have k := priv% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow
  exact k hr hs h1 h2 (weq _ _) I1 I2
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow` idx 15: removable (the IH equivalence is an instance of wpow_add_equiv for numeric games)
theorem w3c3_98 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow 15 := by
  intro x y z w _ _ _ _ r s hr hs h1 h2 I0 I2
  have k := priv% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow
  exact k hr hs h1 h2 I0 (weq _ _) I2
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow` idx 16: removable (the IH equivalence is an instance of wpow_add_equiv for numeric games)
theorem w3c3_99 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow 16 := by
  intro x y z w _ _ _ _ r s hr hs h1 h2 I0 I1
  have k := priv% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow
  exact k hr hs h1 h2 I0 I1 (weq _ _)
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow'` idx 14: removable (the IH equivalence is an instance of wpow_add_equiv for numeric games)
theorem w3c3_100 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow' 14 := by
  intro x y z w _ _ _ _ r s hr hs h1 h2 I1 I2
  have k := priv% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow'
  exact k hr hs h1 h2 (weq _ _) I1 I2
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow'` idx 15: removable (the IH equivalence is an instance of wpow_add_equiv for numeric games)
theorem w3c3_101 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow' 15 := by
  intro x y z w _ _ _ _ r s hr hs h1 h2 I0 I2
  have k := priv% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow'
  exact k hr hs h1 h2 I0 (weq _ _) I2
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.mulOption_lt_wpow'` idx 16: removable (the IH equivalence is an instance of wpow_add_equiv for numeric games)
theorem w3c3_102 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow' 16 := by
  intro x y z w _ _ _ _ r s hr hs h1 h2 I0 I1
  have k := priv% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.mulOption_lt_wpow'
  exact k hr hs h1 h2 I0 I1 (weq _ _)
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.wpow_lt_mulOption` idx 14: removable (the IH equivalence is an instance of wpow_add_equiv for numeric games)
theorem w3c3_103 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.wpow_lt_mulOption 14 := by
  intro x y z w _ _ _ _ r s hr hs h1 h2 I1
  have k := priv% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.wpow_lt_mulOption
  exact k hr hs h1 h2 (weq _ _) I1
-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.wpow_lt_mulOption` idx 15: removable (the IH equivalence is an instance of wpow_add_equiv for numeric games)
theorem w3c3_104 : drop% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.wpow_lt_mulOption 15 := by
  intro x y z w _ _ _ _ r s hr hs h1 h2 I0
  have k := priv% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.wpow_lt_mulOption
  exact k hr hs h1 h2 I0 (weq _ _)
end W3c3
