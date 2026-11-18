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

namespace W3c2
open IGame Set

-- helper: Y = {-1, 0 | } is a numeric game equal to 1; up times Y is fuzzy with 0
noncomputable abbrev Y : IGame := !{{-1, 0} | ∅}
-- helper: nY = { | 0, 1} (the negative of Y)
noncomputable abbrev nY : IGame := !{∅ | {0, 1}}
-- helper: the hot game plus-or-minus one
noncomputable abbrev pm : IGame := !{{1} | {-1}}
-- helper: t = {0 | 3} is numeric and equal to 1, but t times star is not equal to star
noncomputable abbrev t : IGame := !{{0} | {3}}

instance numY : Numeric Y := by
  apply Numeric.mk <;> simp <;> first | game_cmp | infer_instance
instance numNY : Numeric nY := by
  apply Numeric.mk <;> simp <;> first | game_cmp | infer_instance
instance numT : Numeric t := by
  apply Numeric.mk <;> simp <;> first | game_cmp | infer_instance

theorem t1' : (1 : IGame) ≈ t := by game_cmp

-- helper: up is not numeric
theorem notNumUp : ¬ Numeric IGame.up := by
  intro hn
  exact not_numeric_star (Numeric.of_mem_moves (p := .right) (x := IGame.up) (by simp [IGame.up]))

-- helper: rounding one half by one gives zero
theorem hr : (2⁻¹ : Surreal).round 1 = 0 :=
  Surreal.round_of_zero_mem (by simp only [Set.mem_Ioo]; constructor <;> norm_num)

theorem half_ne : (0 : Surreal) ≠ 2⁻¹ := by norm_num

-- helper: rounding one by four gives zero
theorem r4 : (1 : Surreal).round (-2 * -2) = 0 :=
  Surreal.round_of_zero_mem (by simp only [Set.mem_Ioo]; constructor <;> norm_num)

-- helper: W = {up | } is equivalent to 1 but not numeric; W times one half is not equivalent to one half
noncomputable abbrev W : IGame := !{{IGame.up} | ∅}
theorem W1 : W ≈ 1 := by game_cmp
set_option maxHeartbeats 3000000 in
theorem Wh : ¬ W * ½ ≈ ½ := by game_cmp
theorem hW : ¬ ½ * W ≈ ½ := by rw [_root_.mul_comm]; exact Wh
-- helper: Y times W is at most 0 although both are equivalent to 1
set_option maxHeartbeats 3000000 in
theorem YW : Y * W ≤ 0 := by game_cmp

end W3c2

open IGame Set W3c2

-- `IGame.Numeric.mul_pos` idx 2: necessary (x = IGame.up, y = Y (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_1 : ¬ drop0% IGame.Numeric.mul_pos 2 := fun h => absurd (@h IGame.up Y _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_pos` idx 3: necessary (x = Y, y = IGame.up (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_2 : ¬ drop0% IGame.Numeric.mul_pos 3 := fun h => absurd (@h Y IGame.up _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `Surreal.mk_mul` idx 2: necessary (x = ⋆ is not numeric)
theorem w3c2_3 : ¬ indep0% Surreal.mk_mul 2 := fun h => not_numeric_star (@h ⋆ 0 Numeric.zero)

-- `Surreal.mk_mul` idx 3: necessary (y = ⋆ is not numeric)
theorem w3c2_4 : ¬ indep0% Surreal.mk_mul 3 := fun h => not_numeric_star (@h 0 ⋆ Numeric.zero)

-- `IGame.Numeric.mul_neg_of_pos_of_neg` idx 2: necessary (x = IGame.up, y = nY (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_5 : ¬ drop0% IGame.Numeric.mul_neg_of_pos_of_neg 2 := fun h => absurd (@h IGame.up nY _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_neg_of_pos_of_neg` idx 3: necessary (x = Y, y = IGame.down (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_6 : ¬ drop0% IGame.Numeric.mul_neg_of_pos_of_neg 3 := fun h => absurd (@h Y IGame.down _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_neg_of_neg_of_pos` idx 2: necessary (x = IGame.down, y = Y (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_7 : ¬ drop0% IGame.Numeric.mul_neg_of_neg_of_pos 2 := fun h => absurd (@h IGame.down Y _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_neg_of_neg_of_pos` idx 3: necessary (x = nY, y = IGame.up (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_8 : ¬ drop0% IGame.Numeric.mul_neg_of_neg_of_pos 3 := fun h => absurd (@h nY IGame.up _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_pos_of_neg_of_neg` idx 2: necessary (x = IGame.down, y = nY (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_9 : ¬ drop0% IGame.Numeric.mul_pos_of_neg_of_neg 2 := fun h => absurd (@h IGame.down nY _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_pos_of_neg_of_neg` idx 3: necessary (x = nY, y = IGame.down (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_10 : ¬ drop0% IGame.Numeric.mul_pos_of_neg_of_neg 3 := fun h => absurd (@h nY IGame.down _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_nonneg` idx 2: necessary (x = IGame.up, y = Y (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_11 : ¬ drop0% IGame.Numeric.mul_nonneg 2 := fun h => absurd (@h IGame.up Y _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_nonneg` idx 3: necessary (x = Y, y = IGame.up (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_12 : ¬ drop0% IGame.Numeric.mul_nonneg 3 := fun h => absurd (@h Y IGame.up _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_nonpos_of_nonneg_of_nonpos` idx 2: necessary (x = IGame.up, y = nY (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_13 : ¬ drop0% IGame.Numeric.mul_nonpos_of_nonneg_of_nonpos 2 := fun h => absurd (@h IGame.up nY _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_nonpos_of_nonneg_of_nonpos` idx 3: necessary (x = Y, y = IGame.down (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_14 : ¬ drop0% IGame.Numeric.mul_nonpos_of_nonneg_of_nonpos 3 := fun h => absurd (@h Y IGame.down _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_nonpos_of_nonneg_of_nonpos` idx 4: necessary (x = y = -1: product 1 > 0)
theorem w3c2_15 : ¬ drop0% IGame.Numeric.mul_nonpos_of_nonneg_of_nonpos 4 := fun h => absurd (@h (-1) (-1) _ _ (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_nonpos_of_nonpos_of_nonneg` idx 2: necessary (x = IGame.down, y = Y (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_16 : ¬ drop0% IGame.Numeric.mul_nonpos_of_nonpos_of_nonneg 2 := fun h => absurd (@h IGame.down Y _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_nonpos_of_nonpos_of_nonneg` idx 3: necessary (x = nY, y = IGame.up (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_17 : ¬ drop0% IGame.Numeric.mul_nonpos_of_nonpos_of_nonneg 3 := fun h => absurd (@h nY IGame.up _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_nonneg_of_nonpos_of_nonpos` idx 2: necessary (x = IGame.down, y = nY (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_18 : ¬ drop0% IGame.Numeric.mul_nonneg_of_nonpos_of_nonpos 2 := fun h => absurd (@h IGame.down nY _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_nonneg_of_nonpos_of_nonpos` idx 3: necessary (x = nY, y = IGame.down (Y = {-1, 0 | } ≈ 1 numeric; ↑·Y is fuzzy with 0))
theorem w3c2_19 : ¬ drop0% IGame.Numeric.mul_nonneg_of_nonpos_of_nonpos 3 := fun h => absurd (@h nY IGame.down _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_left_cancel` idx 3: necessary (x = ⋆, y = 2, z = 0: ⋆·2 ≈ 0)
theorem w3c2_20 : ¬ drop0% IGame.Numeric.mul_left_cancel 3 := fun h => absurd (@h ⋆ 2 0 _ _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_left_cancel` idx 4: necessary (x = 2, y = ⋆, z = 0: 2·⋆ ≈ 0)
theorem w3c2_21 : ¬ drop0% IGame.Numeric.mul_left_cancel 4 := fun h => absurd (@h 2 ⋆ 0 _ _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_left_cancel` idx 5: necessary (x = 2, y = 0, z = ⋆: 2·⋆ ≈ 0)
theorem w3c2_22 : ¬ drop0% IGame.Numeric.mul_left_cancel 5 := fun h => absurd (@h 2 0 ⋆ _ _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_right_cancel` idx 3: necessary (x = ⋆, y = 2, z = 0: 2·⋆ ≈ 0)
theorem w3c2_23 : ¬ drop0% IGame.Numeric.mul_right_cancel 3 := fun h => absurd (@h ⋆ 2 0 _ _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_right_cancel` idx 4: necessary (x = 2, y = ⋆, z = 0: ⋆·2 ≈ 0)
theorem w3c2_24 : ¬ drop0% IGame.Numeric.mul_right_cancel 4 := fun h => absurd (@h 2 ⋆ 0 _ _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_right_cancel` idx 5: necessary (x = 2, y = 0, z = ⋆)
theorem w3c2_25 : ¬ drop0% IGame.Numeric.mul_right_cancel 5 := fun h => absurd (@h 2 0 ⋆ _ _ (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul_iff_left` idx 3: necessary (x = ↑, y = 0, z = Y: 0 ≤ Y but ¬ 0 ≤ Y·↑)
theorem w3c2_26 : ¬ drop0% IGame.Numeric.mul_le_mul_iff_left 3 := fun h => absurd ((@h IGame.up 0 Y _ _ (by game_cmp)).2 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul_iff_left` idx 4: necessary (x = 2, y = ⋆, z = 0: ⋆·2 ≈ 0)
theorem w3c2_27 : ¬ drop0% IGame.Numeric.mul_le_mul_iff_left 4 := fun h => absurd ((@h 2 ⋆ 0 _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul_iff_left` idx 5: necessary (x = 2, y = 0, z = ⋆: ⋆·2 ≈ 0)
theorem w3c2_28 : ¬ drop0% IGame.Numeric.mul_le_mul_iff_left 5 := fun h => absurd ((@h 2 0 ⋆ _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul_iff_right` idx 3: necessary (x = ↑, y = 0, z = Y)
theorem w3c2_29 : ¬ drop0% IGame.Numeric.mul_le_mul_iff_right 3 := fun h => absurd ((@h IGame.up 0 Y _ _ (by game_cmp)).2 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul_iff_right` idx 4: necessary (x = 2, y = ⋆, z = 0)
theorem w3c2_30 : ¬ drop0% IGame.Numeric.mul_le_mul_iff_right 4 := fun h => absurd ((@h 2 ⋆ 0 _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul_iff_right` idx 5: necessary (x = 2, y = 0, z = ⋆)
theorem w3c2_31 : ¬ drop0% IGame.Numeric.mul_le_mul_iff_right 5 := fun h => absurd ((@h 2 0 ⋆ _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul_iff_left` idx 3: necessary (x = ↑, y = 0, z = Y)
theorem w3c2_32 : ¬ drop0% IGame.Numeric.mul_lt_mul_iff_left 3 := fun h => absurd ((@h IGame.up 0 Y _ _ (by game_cmp)).2 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul_iff_left` idx 4: necessary (x = 2, y = ±1, z = 1: ±1·2 ≈ 0 < 2 but ¬ ±1 < 1)
theorem w3c2_33 : ¬ drop0% IGame.Numeric.mul_lt_mul_iff_left 4 := fun h => absurd ((@h 2 pm 1 _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul_iff_left` idx 5: necessary (x = 2, y = -1, z = ±1)
theorem w3c2_34 : ¬ drop0% IGame.Numeric.mul_lt_mul_iff_left 5 := fun h => absurd ((@h 2 (-1) pm _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul_iff_right` idx 3: necessary (x = ↑, y = 0, z = Y)
theorem w3c2_35 : ¬ drop0% IGame.Numeric.mul_lt_mul_iff_right 3 := fun h => absurd ((@h IGame.up 0 Y _ _ (by game_cmp)).2 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul_iff_right` idx 4: necessary (x = 2, y = ±1, z = 1)
theorem w3c2_36 : ¬ drop0% IGame.Numeric.mul_lt_mul_iff_right 4 := fun h => absurd ((@h 2 pm 1 _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul_iff_right` idx 5: necessary (x = 2, y = -1, z = ±1)
theorem w3c2_37 : ¬ drop0% IGame.Numeric.mul_lt_mul_iff_right 5 := fun h => absurd ((@h 2 (-1) pm _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul_left_of_neg` idx 3: necessary (z = -2, x = ⋆, y = 0)
theorem w3c2_38 : ¬ drop0% IGame.Numeric.mul_le_mul_left_of_neg 3 := fun h => absurd ((@h ⋆ 0 (-2) _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul_left_of_neg` idx 4: necessary (z = -2, x = 0, y = ⋆)
theorem w3c2_39 : ¬ drop0% IGame.Numeric.mul_le_mul_left_of_neg 4 := fun h => absurd ((@h 0 ⋆ (-2) _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul_left_of_neg` idx 5: necessary (z = ↓, x = 0, y = -Y)
theorem w3c2_40 : ¬ drop0% IGame.Numeric.mul_le_mul_left_of_neg 5 := fun h => absurd ((@h 0 nY IGame.down _ _ (by game_cmp)).2 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul_right_of_neg` idx 3: necessary (z = -2, x = ⋆, y = 0)
theorem w3c2_41 : ¬ drop0% IGame.Numeric.mul_le_mul_right_of_neg 3 := fun h => absurd ((@h ⋆ 0 (-2) _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul_right_of_neg` idx 4: necessary (z = -2, x = 0, y = ⋆)
theorem w3c2_42 : ¬ drop0% IGame.Numeric.mul_le_mul_right_of_neg 4 := fun h => absurd ((@h 0 ⋆ (-2) _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul_right_of_neg` idx 5: necessary (z = ↓, x = 0, y = -Y)
theorem w3c2_43 : ¬ drop0% IGame.Numeric.mul_le_mul_right_of_neg 5 := fun h => absurd ((@h 0 nY IGame.down _ _ (by game_cmp)).2 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul_left_of_neg` idx 3: necessary (z = -2, x = ±1, y = -1)
theorem w3c2_44 : ¬ drop0% IGame.Numeric.mul_lt_mul_left_of_neg 3 := fun h => absurd ((@h pm (-1) (-2) _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul_left_of_neg` idx 4: necessary (z = -2, x = 1, y = ±1)
theorem w3c2_45 : ¬ drop0% IGame.Numeric.mul_lt_mul_left_of_neg 4 := fun h => absurd ((@h 1 pm (-2) _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul_left_of_neg` idx 5: necessary (z = ↓, x = 0, y = -Y)
theorem w3c2_46 : ¬ drop0% IGame.Numeric.mul_lt_mul_left_of_neg 5 := fun h => absurd ((@h 0 nY IGame.down _ _ (by game_cmp)).2 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul_right_of_neg` idx 3: necessary (z = -2, x = ±1, y = -1)
theorem w3c2_47 : ¬ drop0% IGame.Numeric.mul_lt_mul_right_of_neg 3 := fun h => absurd ((@h pm (-1) (-2) _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul_right_of_neg` idx 4: necessary (z = -2, x = 1, y = ±1)
theorem w3c2_48 : ¬ drop0% IGame.Numeric.mul_lt_mul_right_of_neg 4 := fun h => absurd ((@h 1 pm (-2) _ _ (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul_right_of_neg` idx 5: necessary (z = ↓, x = 0, y = -Y)
theorem w3c2_49 : ¬ drop0% IGame.Numeric.mul_lt_mul_right_of_neg 5 := fun h => absurd ((@h 0 nY IGame.down _ _ (by game_cmp)).2 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul` idx 4: necessary (a = ↓, b = 0, c = d = Y)
theorem w3c2_50 : ¬ drop0% IGame.Numeric.mul_le_mul 4 := fun h => absurd (@h IGame.down 0 Y Y _ _ _ (by game_cmp) (by game_cmp) (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul` idx 5: necessary (a = 0, b = ↑, c = d = Y)
theorem w3c2_51 : ¬ drop0% IGame.Numeric.mul_le_mul 5 := fun h => absurd (@h 0 IGame.up Y Y _ _ _ (by game_cmp) (by game_cmp) (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul` idx 6: necessary (a = -Y, b = 0, c = ↑, d = 1)
theorem w3c2_52 : ¬ drop0% IGame.Numeric.mul_le_mul 6 := fun h => absurd (@h nY 0 IGame.up 1 _ _ _ (by game_cmp) (by game_cmp) (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul` idx 7: necessary (a = 0, b = Y, c = 0, d = ↑)
theorem w3c2_53 : ¬ drop0% IGame.Numeric.mul_le_mul 7 := fun h => absurd (@h 0 Y 0 IGame.up _ _ _ (by game_cmp) (by game_cmp) (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul` idx 10: necessary (a = 0, b = 1, c = d = -1)
theorem w3c2_54 : ¬ drop0% IGame.Numeric.mul_le_mul 10 := fun h => absurd (@h 0 1 (-1) (-1) _ _ _ _ (by game_cmp) (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_le_mul` idx 11: necessary (a = b = -1, c = 0, d = 1)
theorem w3c2_55 : ¬ drop0% IGame.Numeric.mul_le_mul 11 := fun h => absurd (@h (-1) (-1) 0 1 _ _ _ _ (by game_cmp) (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul` idx 4: necessary (a = ↓, b = 0, c = d = Y)
theorem w3c2_56 : ¬ drop0% IGame.Numeric.mul_lt_mul 4 := fun h => absurd (@h IGame.down 0 Y Y _ _ _ (by game_cmp) (by game_cmp) (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul` idx 5: necessary (a = 0, b = ↑, c = d = Y)
theorem w3c2_57 : ¬ drop0% IGame.Numeric.mul_lt_mul 5 := fun h => absurd (@h 0 IGame.up Y Y _ _ _ (by game_cmp) (by game_cmp) (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul` idx 6: necessary (a = -Y, b = 0, c = ↑, d = 1)
theorem w3c2_58 : ¬ drop0% IGame.Numeric.mul_lt_mul 6 := fun h => absurd (@h nY 0 IGame.up 1 _ _ _ (by game_cmp) (by game_cmp) (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_lt_mul` idx 11: necessary (a = -2, b = -1, c = 1, d = 2)
theorem w3c2_59 : ¬ drop0% IGame.Numeric.mul_lt_mul 11 := fun h => absurd (@h (-2) (-1) 1 2 _ _ _ _ (by game_cmp) (by game_cmp) (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_pos_iff_of_pos_left` idx 2: necessary (a = ↑, b = Y)
theorem w3c2_60 : ¬ drop0% IGame.Numeric.mul_pos_iff_of_pos_left 2 := fun h => absurd ((@h IGame.up Y _ (by game_cmp)).2 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_pos_iff_of_pos_left` idx 3: necessary (a = Y, b = ↑)
theorem w3c2_61 : ¬ drop0% IGame.Numeric.mul_pos_iff_of_pos_left 3 := fun h => absurd ((@h Y IGame.up _ (by game_cmp)).2 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_pos_iff_of_pos_right` idx 2: necessary (a = ↑, b = Y)
theorem w3c2_62 : ¬ drop0% IGame.Numeric.mul_pos_iff_of_pos_right 2 := fun h => absurd ((@h IGame.up Y _ (by game_cmp)).2 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_pos_iff_of_pos_right` idx 3: necessary (a = Y, b = ↑)
theorem w3c2_63 : ¬ drop0% IGame.Numeric.mul_pos_iff_of_pos_right 3 := fun h => absurd ((@h Y IGame.up _ (by game_cmp)).2 (by game_cmp)) (by game_cmp)

-- `IGame.Numeric.mul_equiv_zero` idx 2: necessary (x = ⋆, y = 2: ⋆·2 ≈ 0)
theorem w3c2_64 : ¬ drop0% IGame.Numeric.mul_equiv_zero 2 := fun h => by rcases (@h ⋆ 2 _).1 (by game_cmp) with e | e <;> exact absurd e (by game_cmp)

-- `IGame.Numeric.mul_equiv_zero` idx 3: necessary (x = 2, y = ⋆: ⋆·2 ≈ 0)
theorem w3c2_65 : ¬ drop0% IGame.Numeric.mul_equiv_zero 3 := fun h => by rcases (@h 2 ⋆ _).1 (by game_cmp) with e | e <;> exact absurd e (by game_cmp)

-- `IGame.Numeric.mulOption_congr₁` idx 7: removable (y only occurs in a·y, the same on both sides)
theorem w3c2_66 : drop% IGame.Numeric.mulOption_congr₁ 7 := by
  intro x₁ x₂ y a b _ _ _ _ he
  exact sub_congr (add_congr .rfl (Numeric.mul_congr_left he)) .rfl

-- `IGame.Numeric.mulOption_congr₁` idx 8: removable (a only occurs in a·y and a·b, the same on both sides)
theorem w3c2_67 : drop% IGame.Numeric.mulOption_congr₁ 8 := by
  intro x₁ x₂ y a b _ _ _ _ he
  exact sub_congr (add_congr .rfl (Numeric.mul_congr_left he)) .rfl

-- `IGame.Numeric.mulOption_congr₁` idx 9: necessary (x₁ = 1, x₂ = t = {0 | 3} ≈ 1, b = ⋆: 1·⋆ = ⋆ but t·⋆ ≈ ∗2)
theorem w3c2_68 : ¬ drop0% IGame.Numeric.mulOption_congr₁ 9 := fun h => absurd (@h 1 t 0 0 ⋆ _ _ _ _ t1') (by unfold mulOption; game_cmp)

-- `IGame.Numeric.mulOption_congr₂` idx 5: removable (x only occurs in x·b, the same on both sides)
theorem w3c2_69 : drop% IGame.Numeric.mulOption_congr₂ 5 := by
  intro x y₁ y₂ a b _ _ _ _ he
  exact sub_congr (add_congr (Numeric.mul_congr_right he) .rfl) .rfl

-- `IGame.Numeric.mulOption_congr₂` idx 8: necessary (y₁ = 1, y₂ = t = {0 | 3}, a = ⋆: ⋆·t ≉ ⋆)
theorem w3c2_70 : ¬ drop0% IGame.Numeric.mulOption_congr₂ 8 := fun h => absurd (@h 0 1 t ⋆ 0 _ _ _ _ t1') (by unfold mulOption; game_cmp)

-- `IGame.Numeric.mulOption_congr₂` idx 9: removable (b only occurs in x·b and a·b, the same on both sides)
theorem w3c2_71 : drop% IGame.Numeric.mulOption_congr₂ 9 := by
  intro x y₁ y₂ a b _ _ _ _ he
  exact sub_congr (add_congr (Numeric.mul_congr_right he) .rfl) .rfl

-- `IGame.Numeric.mulOption_congr₃` idx 5: removable (x only occurs in x·b, the same on both sides)
theorem w3c2_72 : drop% IGame.Numeric.mulOption_congr₃ 5 := by
  intro x y a₁ a₂ b _ _ _ _ he
  exact sub_congr (add_congr (Numeric.mul_congr_left he) .rfl) (Numeric.mul_congr_left he)

-- `IGame.Numeric.mulOption_congr₃` idx 6: necessary (y = ⋆, a₁ = 1, a₂ = t = {0 | 3}: t·⋆ ≉ ⋆)
theorem w3c2_73 : ¬ drop0% IGame.Numeric.mulOption_congr₃ 6 := fun h => absurd (@h 0 ⋆ 1 t 0 _ _ _ _ t1') (by unfold mulOption; game_cmp)

-- `IGame.Numeric.mulOption_congr₃` idx 9: necessary (b = ⋆, a₁ = 1, a₂ = t = {0 | 3})
theorem w3c2_74 : ¬ drop0% IGame.Numeric.mulOption_congr₃ 9 := fun h => absurd (@h 0 0 1 t ⋆ _ _ _ _ t1') (by unfold mulOption; game_cmp)

-- `IGame.Numeric.mulOption_congr₄` idx 5: necessary (x = ⋆, b₁ = 1, b₂ = t = {0 | 3})
theorem w3c2_75 : ¬ drop0% IGame.Numeric.mulOption_congr₄ 5 := fun h => absurd (@h ⋆ 0 0 1 t _ _ _ _ t1') (by unfold mulOption; game_cmp)

-- `IGame.Numeric.mulOption_congr₄` idx 6: removable (y only occurs in a·y, the same on both sides)
theorem w3c2_76 : drop% IGame.Numeric.mulOption_congr₄ 6 := by
  intro x y a b₁ b₂ _ _ _ _ he
  exact sub_congr (add_congr .rfl (Numeric.mul_congr_right he)) (Numeric.mul_congr_right he)

-- `IGame.Numeric.mulOption_congr₄` idx 7: necessary (a = ⋆, b₁ = 1, b₂ = t = {0 | 3})
theorem w3c2_77 : ¬ drop0% IGame.Numeric.mulOption_congr₄ 7 := fun h => absurd (@h 0 0 ⋆ 1 t _ _ _ _ t1') (by unfold mulOption; game_cmp)

-- `Surreal.round_of_nonpos` idx 2: necessary (x = ½, r = 1: round = 0)
theorem w3c2_78 : ¬ drop0% Surreal.round_of_nonpos 2 := fun h => half_ne (by rw [← @h 2⁻¹ 1, hr])

-- `Surreal.round_mk_of_pos` idx 4: necessary (r = ↑ is positive but not numeric)
theorem w3c2_79 : ¬ indep0% Surreal.round_mk_of_pos 4 := fun h => notNumUp (@h 0 IGame.up (by game_cmp) Numeric.zero)

-- `Surreal.birthday_round_le` idx 3: necessary (x = 1, r = 0, y = 0: birthday 1 > 0)
theorem w3c2_80 : ¬ drop0% Surreal.birthday_round_le 3 := fun h => absurd (@h 1 0 0) (by rw [Surreal.round_of_nonpos le_rfl]; simp)

-- `Surreal.round_of_zero_mem` idx 2: necessary (x = 1, r = 0)
theorem w3c2_81 : ¬ drop0% Surreal.round_of_zero_mem 2 := fun h => one_ne_zero ((Surreal.round_of_nonpos le_rfl).symm.trans (@h 1 0))

-- `Surreal.round_add_of_eq` idx 3: necessary (x = ½, y = 0, r = 1)
theorem w3c2_82 : ¬ drop0% Surreal.round_add_of_eq 3 := fun h => half_ne (by have := @h 2⁻¹ 0 1 (Surreal.round_zero 1); rw [add_zero, hr] at this; exact this)

-- `Surreal.round_add_of_eq` idx 4: necessary (x = 0, y = ½, r = 1)
theorem w3c2_83 : ¬ drop0% Surreal.round_add_of_eq 4 := fun h => half_ne (by have := @h 0 2⁻¹ 1 (Surreal.round_zero 1); rw [zero_add, hr] at this; exact this)

-- `Surreal.round_sub_of_eq` idx 3: necessary (x = ½, y = 0, r = 1)
theorem w3c2_84 : ¬ drop0% Surreal.round_sub_of_eq 3 := fun h => half_ne (by have := @h 2⁻¹ 0 1 (Surreal.round_zero 1); rw [sub_zero, hr] at this; exact this)

-- `Surreal.round_sub_of_eq` idx 4: necessary (x = 0, y = ½, r = 1)
theorem w3c2_85 : ¬ drop0% Surreal.round_sub_of_eq 4 := fun h => half_ne (by have := @h 0 2⁻¹ 1 (Surreal.round_zero 1); rw [zero_sub, Surreal.round_neg, hr, neg_zero] at this; exact (neg_eq_zero.1 this.symm).symm)

-- `Surreal.round_mul_of_eq` idx 3: necessary (x = y = 1, r = -2: round 1 4 = 0)
theorem w3c2_86 : ¬ drop0% Surreal.round_mul_of_eq 3 := fun h => one_ne_zero (by have := @h 1 1 (-2) (Surreal.round_of_nonpos (by norm_num)) (Surreal.round_of_nonpos (by norm_num)); rw [mul_one, r4] at this; exact this.symm)

-- `Surreal.round_mul_of_eq` idx 4: necessary (x = ½, y = 1, r = 1)
theorem w3c2_87 : ¬ drop0% Surreal.round_mul_of_eq 4 := fun h => half_ne (by have := @h 2⁻¹ 1 1 zero_lt_one Surreal.IsOmnific.one; rw [mul_one, mul_one, hr] at this; exact this)

-- `Surreal.round_mul_of_eq` idx 5: necessary (x = 1, y = ½, r = 1)
theorem w3c2_88 : ¬ drop0% Surreal.round_mul_of_eq 5 := fun h => half_ne (by have := @h 1 2⁻¹ 1 zero_lt_one Surreal.IsOmnific.one; rw [one_mul, mul_one, hr] at this; exact this)

-- `Surreal.IsOmnific.eq` idx 1: necessary (x = ½)
theorem w3c2_89 : ¬ drop0% Surreal.IsOmnific.eq 1 := fun h => half_ne (by rw [← @h 2⁻¹, hr])

-- `Surreal.IsOmnific.neg` idx 1: necessary (x = ½)
theorem w3c2_90 : ¬ drop0% Surreal.IsOmnific.neg 1 := fun h => half_ne (by have := (@h 2⁻¹); unfold Surreal.IsOmnific at this; rw [Surreal.round_neg, hr, neg_zero] at this; exact (neg_eq_zero.1 this.symm).symm)

-- `Surreal.IsOmnific.add` idx 2: necessary (x = ½, y = 0)
theorem w3c2_91 : ¬ drop0% Surreal.IsOmnific.add 2 := fun h => half_ne (by have := @h 2⁻¹ 0 Surreal.IsOmnific.zero; unfold Surreal.IsOmnific at this; rw [add_zero, hr] at this; exact this)

-- `Surreal.IsOmnific.add` idx 3: necessary (x = 0, y = ½)
theorem w3c2_92 : ¬ drop0% Surreal.IsOmnific.add 3 := fun h => half_ne (by have := @h 0 2⁻¹ Surreal.IsOmnific.zero; unfold Surreal.IsOmnific at this; rw [zero_add, hr] at this; exact this)

-- `Surreal.IsOmnific.sub` idx 2: necessary (x = ½, y = 0)
theorem w3c2_93 : ¬ drop0% Surreal.IsOmnific.sub 2 := fun h => half_ne (by have := @h 2⁻¹ 0 Surreal.IsOmnific.zero; unfold Surreal.IsOmnific at this; rw [sub_zero, hr] at this; exact this)

-- `Surreal.IsOmnific.sub` idx 3: necessary (x = 0, y = ½)
theorem w3c2_94 : ¬ drop0% Surreal.IsOmnific.sub 3 := fun h => half_ne (by have := @h 0 2⁻¹ Surreal.IsOmnific.zero; unfold Surreal.IsOmnific at this; rw [zero_sub, Surreal.round_neg, hr, neg_zero] at this; exact (neg_eq_zero.1 this.symm).symm)

-- `Surreal.IsOmnific.mul` idx 2: necessary (x = ½, y = 1)
theorem w3c2_95 : ¬ drop0% Surreal.IsOmnific.mul 2 := fun h => half_ne (by have := @h 2⁻¹ 1 Surreal.IsOmnific.one; unfold Surreal.IsOmnific at this; rw [mul_one, hr] at this; exact this)

-- `Surreal.IsOmnific.mul` idx 3: necessary (x = 1, y = ½)
theorem w3c2_96 : ¬ drop0% Surreal.IsOmnific.mul 3 := fun h => half_ne (by have := @h 1 2⁻¹ Surreal.IsOmnific.one; unfold Surreal.IsOmnific at this; rw [one_mul, hr] at this; exact this)

-- `IGame.Numeric.mul_congr` idx 4: necessary (x₁ = W, x₂ = 1, y₁ = y₂ = ½ (W = {↑ | } ≈ 1 not numeric; W·½ ≉ ½))
theorem w3c2_97 : ¬ drop0% IGame.Numeric.mul_congr 4 := fun h =>
  Wh (by simpa using @h W 1 ½ ½ _ _ _ W1 .rfl)

-- `IGame.Numeric.mul_congr` idx 5: necessary (x₁ = 1, x₂ = W, y₁ = y₂ = ½ (W = {↑ | } ≈ 1 not numeric; W·½ ≉ ½))
theorem w3c2_98 : ¬ drop0% IGame.Numeric.mul_congr 5 := fun h =>
  Wh (by simpa using (@h 1 W ½ ½ _ _ _ W1.symm .rfl).symm)

-- `IGame.Numeric.mul_congr` idx 6: necessary (x₁ = x₂ = ½, y₁ = W, y₂ = 1 (W = {↑ | } ≈ 1 not numeric; W·½ ≉ ½))
theorem w3c2_99 : ¬ drop0% IGame.Numeric.mul_congr 6 := fun h =>
  hW (by simpa using @h ½ ½ W 1 _ _ _ .rfl W1)

-- `IGame.Numeric.mul_congr` idx 7: necessary (x₁ = x₂ = ½, y₁ = 1, y₂ = W (W = {↑ | } ≈ 1 not numeric; W·½ ≉ ½))
theorem w3c2_100 : ¬ drop0% IGame.Numeric.mul_congr 7 := fun h =>
  hW (by simpa using (@h ½ ½ 1 W _ _ _ .rfl W1.symm).symm)

-- `IGame.Numeric.mulOption_congr₁` idx 5: necessary (x₁ = W, x₂ = 1, y = a = 0, b = ½ (W = {↑ | } ≈ 1 not numeric; W·½ ≉ ½))
theorem w3c2_101 : ¬ drop0% IGame.Numeric.mulOption_congr₁ 5 := fun h =>
  Wh (by simpa [mulOption] using @h W 1 0 0 ½ _ _ _ _ W1)

-- `IGame.Numeric.mulOption_congr₁` idx 6: necessary (x₁ = 1, x₂ = W, y = a = 0, b = ½ (W = {↑ | } ≈ 1 not numeric; W·½ ≉ ½))
theorem w3c2_102 : ¬ drop0% IGame.Numeric.mulOption_congr₁ 6 := fun h =>
  Wh (by simpa [mulOption] using (@h 1 W 0 0 ½ _ _ _ _ W1.symm).symm)

-- `IGame.Numeric.mulOption_congr₂` idx 6: necessary (y₁ = W, y₂ = 1, a = ½, x = b = 0 (W = {↑ | } ≈ 1 not numeric; W·½ ≉ ½))
theorem w3c2_103 : ¬ drop0% IGame.Numeric.mulOption_congr₂ 6 := fun h =>
  hW (by simpa [mulOption] using @h 0 W 1 ½ 0 _ _ _ _ W1)

-- `IGame.Numeric.mulOption_congr₂` idx 7: necessary (y₁ = 1, y₂ = W, a = ½, x = b = 0 (W = {↑ | } ≈ 1 not numeric; W·½ ≉ ½))
theorem w3c2_104 : ¬ drop0% IGame.Numeric.mulOption_congr₂ 7 := fun h =>
  hW (by simpa [mulOption] using (@h 0 1 W ½ 0 _ _ _ _ W1.symm).symm)

-- `IGame.Numeric.mulOption_congr₃` idx 7: necessary (a₁ = W, a₂ = 1, y = ½, x = b = 0 (W = {↑ | } ≈ 1 not numeric; W·½ ≉ ½))
theorem w3c2_105 : ¬ drop0% IGame.Numeric.mulOption_congr₃ 7 := fun h =>
  Wh (by simpa [mulOption] using @h 0 ½ W 1 0 _ _ _ _ W1)

-- `IGame.Numeric.mulOption_congr₃` idx 8: necessary (a₁ = 1, a₂ = W, y = ½, x = b = 0 (W = {↑ | } ≈ 1 not numeric; W·½ ≉ ½))
theorem w3c2_106 : ¬ drop0% IGame.Numeric.mulOption_congr₃ 8 := fun h =>
  Wh (by simpa [mulOption] using (@h 0 ½ 1 W 0 _ _ _ _ W1.symm).symm)

-- `IGame.Numeric.mulOption_congr₄` idx 8: necessary (b₁ = W, b₂ = 1, x = ½, y = a = 0 (W = {↑ | } ≈ 1 not numeric; W·½ ≉ ½))
theorem w3c2_107 : ¬ drop0% IGame.Numeric.mulOption_congr₄ 8 := fun h =>
  hW (by simpa [mulOption] using @h ½ 0 0 W 1 _ _ _ _ W1)

-- `IGame.Numeric.mulOption_congr₄` idx 9: necessary (b₁ = 1, b₂ = W, x = ½, y = a = 0 (W = {↑ | } ≈ 1 not numeric; W·½ ≉ ½))
theorem w3c2_108 : ¬ drop0% IGame.Numeric.mulOption_congr₄ 9 := fun h =>
  hW (by simpa [mulOption] using (@h ½ 0 0 1 W _ _ _ _ W1.symm).symm)

-- `IGame.Numeric.mul_lt_mul` idx 7: necessary (a = 0, b = Y, c = 1, d = W: Y·W ≤ 0 (W = {↑ | } ≈ 1, Y = {-1, 0 | } ≈ 1))
theorem w3c2_109 : ¬ drop0% IGame.Numeric.mul_lt_mul 7 := fun h =>
  absurd (@h 0 Y 1 W _ _ _ (by game_cmp) (by game_cmp) (by game_cmp) (by game_cmp))
    (by rw [MulZeroClass.zero_mul]; exact YW.not_gt)

