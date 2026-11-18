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

namespace T1c1
open IGame Set

noncomputable abbrev Y : IGame := !{{-1, 0} | ∅}

noncomputable abbrev nY : IGame := !{∅ | {0, 1}}

noncomputable abbrev W : IGame := !{{IGame.up} | ∅}

instance numY : Numeric Y := by
  apply Numeric.mk <;> simp <;> first | game_cmp | infer_instance

instance numNY : Numeric nY := by
  apply Numeric.mk <;> simp <;> first | game_cmp | infer_instance

theorem W1 : W ≈ 1 := by game_cmp

set_option maxHeartbeats 3000000 in
theorem Wh : ¬ W * ½ ≈ ½ := by game_cmp

theorem hW : ¬ ½ * W ≈ ½ := by rw [_root_.mul_comm]; exact Wh

noncomputable abbrev Z0 : IGame := !{∅ | {2}}

instance numZ0 : Numeric Z0 := by
  rw [numeric_def]; refine ⟨by simp, ?_⟩
  rintro (_ | _) y hy <;> simp at hy; subst hy; infer_instance

theorem z0Equiv : Z0 ≈ 0 := by game_cmp

theorem z0StarLe : ¬ Z0 * ⋆ ≤ 0 := by game_cmp

theorem z0Star : Z0 * ⋆ ≈ ⋆ := by game_cmp

theorem ih4W2 : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH4) W 2 ½ := by
  intro p q z w hw
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · have : z = IGame.up := by cases q <;> simp at hz; exact hz
    subst this
    exact fun e => absurd e (by game_cmp)
  · have : z = 1 := by cases q <;> simp at hz; exact hz
    subst this
    intro _
    have : w = 0 ∨ w = 1 := by cases p <;> simp at hw <;> simp [hw]
    rcases this with rfl | rfl
    · simp
    · rw [mul_one, mul_one]; exact Game.mk_eq W1

theorem ih24Z0 : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH24) Z0 1 1 := by
  intro p z
  refine ⟨fun hz => ?_, fun hz => ?_, fun hz => ?_⟩
  · obtain rfl : z = 2 := by cases p <;> simpa using hz
    exact And.intro (fun e => absurd e (by game_cmp)) (fun e => absurd e (by game_cmp))
  · obtain rfl : z = 0 := by cases p <;> simpa using hz
    refine And.intro (fun _ => ?_) (fun e => absurd e (by game_cmp))
    rw [mul_one, mul_one]; exact Game.mk_eq z0Equiv
  · obtain rfl : z = 0 := by cases p <;> simpa using hz
    exact And.intro (fun e => absurd e (by game_cmp)) (fun _ => And.intro (fun a ha => by simp at ha) (fun a ha => by simp at ha))

theorem ih4Z0 : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH4) Z0 1 1 := by
  intro p q z w hw
  obtain rfl : w = 0 := by cases p <;> simpa using hw
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain rfl : z = 2 := by cases q <;> simpa using hz
    exact fun e => absurd e (by game_cmp)
  · obtain rfl : z = 0 := by cases q <;> simpa using hz
    intro _; simp

noncomputable abbrev Ys0 : IGame := !{{⋆} | {0}}

theorem ih24Z0m : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH24) Z0 (-2) Ys0 := by
  intro p z
  refine ⟨fun hz => ?_, fun hz => ?_, fun hz => ?_⟩
  · obtain rfl : z = 2 := by cases p <;> simpa using hz
    exact ⟨fun e => absurd e (by game_cmp), fun e => absurd e (by game_cmp)⟩
  · obtain rfl : z = -1 := by cases p <;> simp at hz <;> simp [hz]
    exact ⟨fun e => absurd e (by game_cmp), fun e => absurd e (by game_cmp)⟩
  · exact ⟨fun e => absurd e (by game_cmp), fun e => absurd e (by game_cmp)⟩

theorem ih4Z0m : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH4) Z0 (-2) Ys0 := by
  intro p q z w hw
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain rfl : z = 2 := by cases q <;> simpa using hz
    exact fun e => absurd e (by game_cmp)
  · obtain rfl : z = -1 := by cases q <;> simp at hz <;> simp [hz]
    exact fun e => absurd e (by game_cmp)

theorem starConst : ∀ p q (a b : IGame), a ∈ (⋆ : IGame).moves p → b ∈ (⋆ : IGame).moves q → a = b := by
  intro p q a b ha hb; cases p <;> cases q <;> simp_all

theorem oneConst : ∀ p q (a b : IGame), a ∈ (1 : IGame).moves p → b ∈ (1 : IGame).moves q → a = b := by
  intro p q a b ha hb; cases p <;> cases q <;> simp_all

-- helper: IH1 holds when all options of x coincide
theorem ih1Const {x y : IGame} (hx : ∀ p q a b, a ∈ x.moves p → b ∈ x.moves q → a = b) :
    (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH1) x y := by
  intro p q a b y' ha hb _
  obtain rfl := hx p q a b ha hb
  exact And.intro (fun _ => rfl) (fun h => absurd h (lt_irrefl _))

-- helper: XP = {±1 | } is equivalent to 0 but not numeric, and XP * star is fuzzy with 0
noncomputable abbrev PM : IGame := !{{1} | {-1}}

noncomputable abbrev XP : IGame := !{{PM} | ∅}

theorem xpEquiv : XP ≈ 0 := by game_cmp

theorem ih24XP : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH24) XP 0 ⋆ := by
  intro p z
  refine ⟨fun hz => ?_, fun hz => ?_, fun hz => ?_⟩
  · obtain rfl : z = PM := by cases p <;> simpa using hz
    exact ⟨fun e => absurd e (by game_cmp), fun e => absurd e (by game_cmp)⟩
  · cases p <;> simp at hz
  · obtain rfl : z = 0 := by cases p <;> simpa using hz
    exact ⟨fun _ => by simp, fun e => absurd e (by game_cmp)⟩

theorem ih24XP' : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH24) 0 XP ⋆ := by
  intro p z
  refine ⟨fun hz => ?_, fun hz => ?_, fun hz => ?_⟩
  · cases p <;> simp at hz
  · obtain rfl : z = PM := by cases p <;> simpa using hz
    exact ⟨fun e => absurd e (by game_cmp), fun e => absurd e (by game_cmp)⟩
  · obtain rfl : z = 0 := by cases p <;> simpa using hz
    exact ⟨fun _ => by simp, fun e => absurd e (by game_cmp)⟩

-- helper: XH = {0 | {1/2 | -1}} is equivalent to 1/2, not numeric, and has no positive option, so XH⁻¹ = 1
noncomputable abbrev QH : IGame := !{{½} | {-1}}

noncomputable abbrev XH : IGame := !{{0} | {QH}}

theorem xhEquiv : XH ≈ ½ := by game_cmp

theorem invMoves_triv {x : IGame} (hx : 0 < x) (hno : ∀ p, ∀ y ∈ x.moves p, ¬ 0 < y) :
    ∀ p y, y ∈ x⁻¹.moves p → p = .left ∧ y = 0 :=
  invRec hx (P := fun p y _ => p = .left ∧ y = 0) ⟨rfl, rfl⟩
    (fun _ _ y hy hyx _ _ _ => absurd hy (hno _ y hyx))

theorem inv_eq_one {x : IGame} (hx : 0 < x) (hno : ∀ p, ∀ y ∈ x.moves p, ¬ 0 < y) : x⁻¹ = 1 := by
  ext p y
  cases p
  · constructor
    · intro h; have := (invMoves_triv hx hno _ _ h).2; simp [this]
    · intro h; simp at h; subst h; exact zero_mem_moves_left_inv hx
  · constructor
    · intro h; exact absurd (invMoves_triv hx hno _ _ h).1 (by decide)
    · intro h; simp at h

theorem xhInv : XH⁻¹ = 1 :=
  inv_eq_one (by game_cmp) (fun p y hy => by
    cases p <;> simp at hy <;> subst hy <;> game_cmp)

theorem oneHalfInv : ¬ (1 : IGame) ≈ (½ : IGame)⁻¹ := fun e => by
  have := Surreal.mk_eq e
  rw [Surreal.mk_inv, IGame.mk_half, Surreal.mk_one, inv_inv] at this
  norm_num at this

end T1c1

open IGame Set T1c1

-- `IGame.Numeric.mul_congr_right` idx 4
theorem t1_1 : ¬ drop0% IGame.Numeric.mul_congr_right 4 := fun h => by
  have := @h ½ W 1 _ _ W1
  rw [mul_one] at this
  exact hW this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.main_P24` idx 3
theorem t1_2 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».main_P24 3 := fun h => by
  have := (@h W 1 ½ _ _).1 W1
  rw [one_mul] at this
  exact Wh (Game.mk_eq_mk.1 this)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.main_P24` idx 4
theorem t1_3 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».main_P24 4 := fun h => by
  have := (@h 1 W ½ _ _).1 W1.symm
  rw [one_mul] at this
  exact Wh (Game.mk_eq_mk.1 this.symm)

-- `_private.CombinatorialGames.Surreal.Division.0.mulOption_le` idx 4
theorem t1_4 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».mulOption_le 4 := fun h => by
  have := @h 0 IGame.up nY 0 _ _ (by game_cmp) (by game_cmp)
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Division.0.mulOption_le` idx 5
theorem t1_5 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».mulOption_le 5 := fun h => by
  have := @h 0 Y IGame.down 0 _ _ (by game_cmp) (by game_cmp)
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Division.0.mulOption_le` idx 6
theorem t1_6 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».mulOption_le 6 := fun h => by
  have := @h 0 0 nY IGame.down _ _ (by game_cmp) (by game_cmp)
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Division.0.le_mulOption` idx 4
theorem t1_7 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».le_mulOption 4 := fun h => by
  have := @h 0 IGame.down nY 0 _ _ (by game_cmp) (by game_cmp)
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Division.0.le_mulOption` idx 5
theorem t1_8 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».le_mulOption 5 := fun h => by
  have := @h 0 0 IGame.down Y _ _ (by game_cmp) (by game_cmp)
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Division.0.le_mulOption` idx 6
theorem t1_9 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».le_mulOption 6 := fun h => by
  have := @h 0 0 nY IGame.up _ _ (by game_cmp) (by game_cmp)
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3_of_lt_of_lt` idx 4
theorem t1_10 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3_of_lt_of_lt 4 := fun h => by
  have := @h IGame.down 0 0 Y _ _ _ (by game_cmp) (by game_cmp)
  change Game.mk (IGame.down * Y) + Game.mk (0 * 0) < Game.mk (IGame.down * 0) + Game.mk (0 * Y) at this
  simp only [zero_mul, mul_zero, Game.mk_zero, add_zero, zero_add] at this
  rw [← Game.mk_zero, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3_of_lt_of_lt` idx 5
theorem t1_11 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3_of_lt_of_lt 5 := fun h => by
  have := @h 0 IGame.up 0 Y _ _ _ (by game_cmp) (by game_cmp)
  change Game.mk (0 * Y) + Game.mk (IGame.up * 0) < Game.mk (0 * 0) + Game.mk (IGame.up * Y) at this
  simp only [zero_mul, mul_zero, Game.mk_zero, add_zero, zero_add] at this
  rw [← Game.mk_zero, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3_of_lt_of_lt` idx 6
theorem t1_12 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3_of_lt_of_lt 6 := fun h => by
  have := @h 0 Y IGame.down 0 _ _ _ (by game_cmp) (by game_cmp)
  change Game.mk (0 * 0) + Game.mk (Y * IGame.down) < Game.mk (0 * IGame.down) + Game.mk (Y * 0) at this
  simp only [zero_mul, mul_zero, Game.mk_zero, add_zero, zero_add] at this
  rw [← Game.mk_zero, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3_of_lt_of_lt` idx 7
theorem t1_13 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3_of_lt_of_lt 7 := fun h => by
  have := @h 0 Y 0 IGame.up _ _ _ (by game_cmp) (by game_cmp)
  change Game.mk (0 * IGame.up) + Game.mk (Y * 0) < Game.mk (0 * 0) + Game.mk (Y * IGame.up) at this
  simp only [zero_mul, mul_zero, Game.mk_zero, add_zero, zero_add] at this
  rw [← Game.mk_zero, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH3_of_IH` idx 5
set_option maxHeartbeats 3000000 in
theorem t1_14 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH3_of_IH 5 := fun h => by
  have := (@h W 2 ½ 1 0 ih4W2 (by simp) (by simp) (by game_cmp)).2.1 W1
  rw [one_mul] at this
  exact Wh (Game.mk_eq_mk.1 this)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH3_of_IH` idx 8
theorem t1_15 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH3_of_IH 8 := fun h => by
  have := (@h Z0 1 1 0 ⋆ ih24Z0 ih4Z0 (by simp) (by game_cmp)).1 z0Equiv
  rw [zero_mul] at this
  exact z0StarLe (Game.mk_eq_mk.1 this).1

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P1_of_equiv` idx 8
theorem t1_16 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P1_of_equiv 8 := fun h => by
  have := @h 0 1 Z0 0 (IGame.down + ⋆) ⋆ z0Equiv.symm (fun _ => by simp) (by
    change Game.mk (0 * ⋆) + Game.mk (1 * (IGame.down + ⋆)) < Game.mk (0 * (IGame.down + ⋆)) + Game.mk (1 * ⋆)
    simp only [zero_mul, one_mul, Game.mk_zero, zero_add, add_zero]
    rw [Game.mk_lt_mk]; game_cmp)
  change Game.mk (mulOption 1 0 0 (IGame.down + ⋆)) < Game.mk (mulOption 1 0 Z0 ⋆) at this
  simp only [mulOption, mul_zero, zero_mul, one_mul, Game.mk_sub, Game.mk_add, Game.mk_zero, zero_add, add_zero] at this
  rw [Game.mk_eq z0Star, sub_self] at this
  simp only [Game.mk_zero, sub_zero] at this
  rw [← Game.mk_add, ← Game.mk_zero, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH3_of_IH` idx 7
theorem t1_18 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH3_of_IH 7 := fun h => by
  have := (@h Z0 (-2) Ys0 0 ⋆ ih24Z0m ih4Z0m (by simp) (by game_cmp)).1 z0Equiv
  rw [zero_mul] at this
  exact z0StarLe (Game.mk_eq_mk.1 this).1

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt` idx 3
theorem t1_19 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt 3 := fun h => by
  have := @h 1 ⋆ _ (ih1Const oneConst) (ih1Const starConst) 0 0 0 0 (by simp) (by simp) (by simp) (by simp)
  rw [← Game.mk_neg, Game.mk_lt_mk] at this
  exact absurd this (by simp only [mulOption]; game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mul_right_le_of_equiv` idx 3
theorem t1_20 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mul_right_le_of_equiv 3 := fun h => by
  have := @h XP 0 ⋆ _ ih24XP ih24XP' xpEquiv
  rw [zero_mul] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mul_right_le_of_equiv` idx 4
theorem t1_21 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mul_right_le_of_equiv 4 := fun h => by
  have := @h 0 XP ⋆ _ ih24XP' ih24XP xpEquiv.symm
  rw [zero_mul] at this
  exact absurd this (by game_cmp)

-- `IGame.Numeric.inv_congr` idx 2
theorem t1_23 : ¬ drop0% IGame.Numeric.inv_congr 2 := fun h => by
  have := @h XH ½ _ xhEquiv
  rw [xhInv] at this
  exact oneHalfInv this

-- `IGame.Numeric.inv_congr` idx 3
theorem t1_24 : ¬ drop0% IGame.Numeric.inv_congr 3 := fun h => by
  have := @h ½ XH _ xhEquiv.symm
  rw [xhInv] at this
  exact oneHalfInv this.symm

-- `IGame.Numeric.div_congr_right` idx 4
theorem t1_25 : ¬ drop0% IGame.Numeric.div_congr_right 4 := fun h => by
  have := @h 1 XH ½ _ _ xhEquiv
  rw [IGame.div_eq_mul_inv, IGame.div_eq_mul_inv, one_mul, one_mul, xhInv] at this
  exact oneHalfInv this

-- `IGame.Numeric.div_congr_right` idx 5
theorem t1_26 : ¬ drop0% IGame.Numeric.div_congr_right 5 := fun h => by
  have := @h 1 ½ XH _ _ xhEquiv.symm
  rw [IGame.div_eq_mul_inv, IGame.div_eq_mul_inv, one_mul, one_mul, xhInv] at this
  exact oneHalfInv this.symm

-- `IGame.Numeric.div_congr` idx 6
theorem t1_27 : ¬ drop0% IGame.Numeric.div_congr 6 := fun h => by
  have := @h 1 1 XH ½ _ _ _ (by game_cmp) xhEquiv
  rw [IGame.div_eq_mul_inv, IGame.div_eq_mul_inv, one_mul, one_mul, xhInv] at this
  exact oneHalfInv this

-- `IGame.Numeric.div_congr` idx 7
theorem t1_28 : ¬ drop0% IGame.Numeric.div_congr 7 := fun h => by
  have := @h 1 1 ½ XH _ _ _ (by game_cmp) xhEquiv.symm
  rw [IGame.div_eq_mul_inv, IGame.div_eq_mul_inv, one_mul, one_mul, xhInv] at this
  exact oneHalfInv this.symm
