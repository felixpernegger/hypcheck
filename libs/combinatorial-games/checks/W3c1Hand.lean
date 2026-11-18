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

namespace W3c1
open IGame

noncomputable abbrev X1 : IGame := !{{⋆} | ∅}
noncomputable abbrev X2 : IGame := !{{⋆, star'} | ∅}

theorem starX1 : ⋆ ∈ X1.moves .left := by simp [X1]

-- helper: IH1 X2 star fails (star' equiv star but star' * star not equiv star * star)
theorem badIH1 : ¬ (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH1) X2 ⋆ := fun h => by
  have h2 : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».P24) star' ⋆ ⋆ :=
    h (p := .left) (q := .left) (x₁ := star') (x₂ := ⋆) (y' := ⋆) (by simp [X2]) (by simp [X2]) (.inl rfl)
  obtain ⟨h2a, -⟩ := h2
  have : Game.mk (star' * ⋆) = Game.mk (⋆ * ⋆) := h2a star'_equiv_star
  rw [star_mul_star] at this
  exact star'_mul_star_not_equiv (Game.mk_eq_mk.1 this)

-- helper: IH1 holds when all options of x coincide
theorem ih1Const {x y : IGame} (hx : ∀ p q a b, a ∈ x.moves p → b ∈ x.moves q → a = b) :
    (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH1) x y := by
  intro p q a b y' ha hb _
  obtain rfl := hx p q a b ha hb
  exact And.intro (fun _ => rfl) (fun h => absurd h (lt_irrefl _))

-- helper: IH1 holds for numeric games
theorem ih1Num {x y : IGame} [hx : Numeric x] [hy : Numeric y] : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH1) x y := by
  intro p q a b y' ha hb hy'
  have : Numeric a := Numeric.of_mem_moves ha
  have : Numeric b := Numeric.of_mem_moves hb
  have : Numeric y' := by
    rcases hy' with rfl | ⟨u, hu⟩
    · exact hy
    · exact Numeric.of_mem_moves hu
  exact (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».main_P24) a b y'

-- helper: the induction hypothesis holds below numeric arguments
theorem ihNum (a : priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args) (ha : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.Numeric) a) :
    ∀ a', (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».ArgsRel) a' a → (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».P124) a' :=
  fun a' h => (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».main) a' ((priv% _private.CombinatorialGames.Surreal.Multiplication.«0».ArgsRel.numeric_closed) h ha)

theorem numP1 (x y : IGame) [Numeric x] [Numeric y] : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.Numeric) ((priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.P1) x y) :=
  (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.numeric_P1).2 ⟨inferInstance, inferInstance⟩

end W3c1

open IGame W3c1

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3.trans`
theorem w3c1_1 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3.trans 5 := fun h => by
  have := h (x₁ := 0) (x₂ := 1) (x₃ := 0) (y₁ := 1) (y₂ := 0) (by
    show Game.mk (1 * 0) + Game.mk (0 * 1) < Game.mk (1 * 1) + Game.mk (0 * 0)
    simp)
  change Game.mk (0 * 0) + Game.mk (0 * 1) < Game.mk (0 * 1) + Game.mk (0 * 0) at this
  rw [add_comm] at this
  exact lt_irrefl _ this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3.trans`
theorem w3c1_2 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3.trans 6 := fun h => by
  have := h (x₁ := 1) (x₂ := 0) (x₃ := 1) (y₁ := 1) (y₂ := 0) (by
    show Game.mk (1 * 0) + Game.mk (0 * 1) < Game.mk (1 * 1) + Game.mk (0 * 0)
    simp)
  change Game.mk (1 * 0) + Game.mk (1 * 1) < Game.mk (1 * 1) + Game.mk (1 * 0) at this
  rw [add_comm] at this
  exact lt_irrefl _ this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH1_of_IH`
theorem w3c1_3 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH1_of_IH 2 := fun h => badIH1 (h (x := X2) (y := ⋆))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH1_swap_of_IH`
theorem w3c1_4 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH1_swap_of_IH 2 := fun h => badIH1 (h (x := ⋆) (y := X2))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH1_neg_left`
theorem w3c1_5 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH1_neg_left 2 := fun h => badIH1 (by simpa using h (x := -X2) (y := ⋆))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH1_neg_right`
theorem w3c1_6 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH1_neg_right 2 := fun h => badIH1 (by simpa using h (x := X2) (y := -⋆))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.numeric_move_mul_of_IH`
theorem w3c1_7 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».numeric_move_mul_of_IH 4 := fun h => by
  have := h (x := X1) (x' := ⋆) (y := 1) (p := .left) starX1
  rw [mul_one] at this
  exact not_numeric_star this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.numeric_move_mul_of_IH`
theorem w3c1_8 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».numeric_move_mul_of_IH 5 := fun h => by
  have := h (x := 0) (x' := ⋆) (y := 1) (p := .left) (ihNum _ (numP1 0 1))
  rw [mul_one] at this
  exact not_numeric_star this

namespace W3c1
open IGame

noncomputable abbrev Y2 : IGame := !{{1} | ∅}
noncomputable abbrev Y3 : IGame := !{{-1} | {1}}
noncomputable abbrev X3 : IGame := !{{star'} | ∅}

instance numY2 : Numeric Y2 := by
  rw [numeric_def]; refine ⟨by simp, ?_⟩
  rintro (_ | _) y hy <;> simp at hy <;> subst hy <;> infer_instance

instance numY3 : Numeric Y3 := by
  rw [numeric_def]; refine ⟨by simp; game_cmp, ?_⟩
  rintro (_ | _) y hy <;> simp at hy <;> subst hy <;> infer_instance

theorem oneY2 : (1 : IGame) ∈ Y2.moves .left := by simp [Y2]

theorem starConst : ∀ p q (a b : IGame), a ∈ (⋆ : IGame).moves p → b ∈ (⋆ : IGame).moves q → a = b := by
  intro p q a b ha hb; cases p <;> cases q <;> simp_all

theorem oneConst : ∀ p q (a b : IGame), a ∈ (1 : IGame).moves p → b ∈ (1 : IGame).moves q → a = b := by
  intro p q a b ha hb; cases p <;> cases q <;> simp_all

-- helper: P24 star' star star fails
theorem badP24 : ¬ (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».P24) star' ⋆ ⋆ := fun h2 => by
  obtain ⟨h2a, -⟩ := h2
  have : Game.mk (star' * ⋆) = Game.mk (⋆ * ⋆) := h2a star'_equiv_star
  rw [star_mul_star] at this
  exact star'_mul_star_not_equiv (Game.mk_eq_mk.1 this)

-- helper: P24 0 1 star fails (P4 part: 0 < star fails)
theorem bad01 : ¬ (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».P24) 0 1 ⋆ := fun h2 => by
  obtain ⟨-, h4⟩ := h2
  have h3 := ((h4 (by game_cmp)).1 0 (by simp) : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».P3) 0 1 0 ⋆)
  change Game.mk (0 * ⋆) + Game.mk (1 * 0) < Game.mk (0 * 0) + Game.mk (1 * ⋆) at h3
  simp only [zero_mul, mul_zero, one_mul, Game.mk_zero, zero_add, add_zero] at h3
  rw [← Game.mk_zero, Game.mk_lt_mk] at h3
  exact absurd h3 (by game_cmp)

-- helper: IH24 for numeric games
theorem ih24Num {x₁ x₂ y : IGame} [Numeric x₁] [Numeric x₂] [Numeric y] : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH24) x₁ x₂ y := by
  intro p z
  refine ⟨fun hz => ?_, fun hz => ?_, fun hz => ?_⟩ <;> have := Numeric.of_mem_moves hz
  · exact (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».main_P24) z x₂ y
  · exact (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».main_P24) x₁ z y
  · exact (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».main_P24) x₁ x₂ z

theorem numP24 (x₁ x₂ y : IGame) [Numeric x₁] [Numeric x₂] [Numeric y] :
    (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.Numeric) ((priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.P24) x₁ x₂ y) :=
  (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.numeric_P24).2 ⟨inferInstance, inferInstance, inferInstance⟩

end W3c1

open IGame W3c1 Relation WellFounded

-- `_private.CombinatorialGames.Surreal.Multiplication.0.numeric_mul_move_of_IH`
theorem w3c1_9 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».numeric_mul_move_of_IH 4 := fun h => by
  have := h (x := 1) (y' := ⋆) (y := X1) (p := .left) starX1
  rw [one_mul] at this
  exact not_numeric_star this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.numeric_mul_move_of_IH`
theorem w3c1_10 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».numeric_mul_move_of_IH 5 := fun h => by
  have := h (x := 1) (y' := ⋆) (y := 0) (p := .left) (ihNum _ (numP1 1 0))
  rw [one_mul] at this
  exact not_numeric_star this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.numeric_move_mul_move_of_IH`
theorem w3c1_11 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».numeric_move_mul_move_of_IH 6 := fun h => by
  have := h (x := X1) (x' := ⋆) (y := X1) (y' := ⋆) (p := .left) (q := .left) starX1 starX1
  rw [star_mul_star] at this
  exact not_numeric_star this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.numeric_move_mul_move_of_IH`
theorem w3c1_12 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».numeric_move_mul_move_of_IH 7 := fun h => by
  have := h (x := 0) (x' := ⋆) (y := Y2) (y' := 1) (p := .left) (q := .left) (ihNum _ (numP1 0 Y2)) oneY2
  rw [mul_one] at this
  exact not_numeric_star this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.numeric_move_mul_move_of_IH`
theorem w3c1_13 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».numeric_move_mul_move_of_IH 8 := fun h => by
  have := h (x := Y2) (x' := 1) (y := 0) (y' := ⋆) (p := .left) (q := .left) (ihNum _ (numP1 Y2 0)) oneY2
  rw [one_mul] at this
  exact not_numeric_star this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.ArgsRel.numeric_closed`
theorem w3c1_14 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».ArgsRel.numeric_closed 2 := fun h => by
  have := h (a' := (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.P1) ⋆ 0) (a := (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.P1) 0 0) (numP1 0 0)
  exact not_numeric_star ((priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.numeric_P1).1 this).1

-- `_private.CombinatorialGames.Surreal.Multiplication.0.ArgsRel.numeric_closed`
theorem w3c1_15 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».ArgsRel.numeric_closed 3 := fun h => by
  have hr : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».ArgsRel) ((priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.P1) ⋆ 0) ((priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.P1) X1 0) :=
    TransGen.single (cutExpand_pair_left ⟨.left, starX1⟩)
  have := h hr
  exact not_numeric_star ((priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.numeric_P1).1 this).1

-- `_private.CombinatorialGames.Surreal.Multiplication.0.numeric_of_IH`
theorem w3c1_16 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».numeric_of_IH 3 := fun h => by
  have := (h (x₁ := ⋆) (x₂ := 0) (y := 1)).1
  rw [mul_one] at this
  exact not_numeric_star this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P1_of_equiv`
theorem w3c1_17 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P1_of_equiv 6 := fun h => by
  have := h (x₁ := 1) (x₂ := 0) (x₃ := 0) (y₁ := 0) (y₂ := 0) (y₃ := -1)
    (fun e => absurd e (by game_cmp)) (fun e => absurd e (by game_cmp)) (by
      show Game.mk (1 * -1) + Game.mk (0 * 0) < Game.mk (1 * 0) + Game.mk (0 * -1)
      simp)
  change Game.mk (mulOption 0 0 1 0) < Game.mk (mulOption 0 0 0 (-1)) at this
  simp [mulOption] at this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P1_of_P3`
theorem w3c1_18 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P1_of_P3 6 := fun h => by
  have := h (x₁ := 1) (x₂ := 1) (x₃ := 0) (y₁ := 0) (y₂ := 1) (y₃ := 0) (by
      show Game.mk (1 * 0) + Game.mk (0 * 1) < Game.mk (1 * 1) + Game.mk (0 * 0)
      simp)
  change Game.mk (mulOption 1 0 1 1) < Game.mk (mulOption 1 0 0 0) at this
  simp [mulOption] at this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3_of_IH1`
theorem w3c1_19 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3_of_IH1 5 := fun h => by
  have := h (x := 1) (y := ⋆) (a := 0) (b := 0) (d := 0) (ih1Const starConst) (by simp) (by simp) (by simp)
  change Game.mk (0 * -0) + Game.mk (1 * 0) < Game.mk (0 * 0) + Game.mk (1 * -0) at this
  simp at this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3_of_IH1`
theorem w3c1_20 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3_of_IH1 6 := fun h => by
  have := h (x := X1) (y := Y3) (a := ⋆) (b := -1) (d := -1) starX1 (by simp) (by simp)
  change Game.mk (⋆ * -(-1)) + Game.mk (X1 * -1) < Game.mk (⋆ * -1) + Game.mk (X1 * -(-1)) at this
  simp only [neg_neg, mul_one, mul_neg, ← Game.mk_neg, ← Game.mk_add, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3_of_IH1`
theorem w3c1_21 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3_of_IH1 7 := fun h => by
  have := h (x := 0) (y := Y3) (a := 0) (b := -1) (d := -1) ih1Num (by simp) (by simp)
  change Game.mk (0 * -(-1)) + Game.mk (0 * -1) < Game.mk (0 * -1) + Game.mk (0 * -(-1)) at this
  rw [add_comm] at this
  exact lt_irrefl _ this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3_of_IH1`
theorem w3c1_22 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3_of_IH1 9 := fun h => by
  have := h (x := 1) (y := 1) (a := 0) (b := 0) (d := 0) ih1Num (by simp) (by simp)
  change Game.mk (0 * -0) + Game.mk (1 * 0) < Game.mk (0 * 0) + Game.mk (1 * -0) at this
  simp at this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P24_of_IH1`
theorem w3c1_23 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P24_of_IH1 4 := fun h =>
  badP24 (h (x := X2) (y := ⋆) (a := star') (b := ⋆) (by simp [X2]) (by simp [X2]))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P24_of_IH1`
theorem w3c1_24 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P24_of_IH1 6 := fun h =>
  bad01 (h (x := 1) (y := ⋆) (a := 0) (b := 1) (ih1Const oneConst) (by simp))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.main_P24`
theorem w3c1_25 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».main_P24 5 := fun h => bad01 (h 0 1 ⋆)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P4_of_IH`
theorem w3c1_26 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P4_of_IH 3 := fun h =>
  bad01 (And.intro (fun e => absurd e (by game_cmp)) (h (x₁ := 0) (x₂ := 1) (y := ⋆)))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.main`
theorem w3c1_27 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».main 1 := fun h => by
  have : Numeric (⋆ * 1) := h ((priv% _private.CombinatorialGames.Surreal.Multiplication.«0».Args.P1) ⋆ 1)
  rw [mul_one] at this
  exact not_numeric_star this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3_of_lt_of_lt`
theorem w3c1_28 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3_of_lt_of_lt 8 := fun h => by
  have := h (x₁ := 0) (x₂ := 0) (y₁ := 0) (y₂ := 1) (by game_cmp)
  change Game.mk (0 * 1) + Game.mk (0 * 0) < Game.mk (0 * 0) + Game.mk (0 * 1) at this
  rw [add_comm] at this
  exact lt_irrefl _ this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P2_of_IH`
theorem w3c1_29 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P2_of_IH 6 := fun h => by
  have := h (x₁ := 0) (x₂ := 1) (y := 1) (ihNum _ (numP24 0 1 1))
  simp only [zero_mul, mul_one] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mul_right_le_of_equiv`
theorem w3c1_30 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mul_right_le_of_equiv 7 := fun h => by
  have := h (x₁ := 1) (x₂ := 0) (y := 1) ih24Num ih24Num
  simp only [zero_mul, mul_one] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt_mul_of_equiv`
theorem w3c1_31 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt_mul_of_equiv 7 := fun h => by
  have := h (x₁ := 1) (x₂ := 0) (y := 1) (a := 0) (b := 0) ih24Num (by simp) (by simp)
  simp [mulOption] at this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt_mul_of_equiv`
theorem w3c1_32 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt_mul_of_equiv 8 := fun h => by
  have := h (x₁ := 1) (x₂ := 1) (y := 1) (a := 1) (b := 0) ih24Num .rfl (by simp)
  simp [mulOption] at this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt_mul_of_equiv`
theorem w3c1_33 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt_mul_of_equiv 9 := fun h => by
  have := h (x₁ := 1) (x₂ := 1) (y := 1) (a := 0) (b := 1) ih24Num .rfl (by simp)
  simp [mulOption] at this

namespace W3c1
open IGame

-- helper: IH24 star star y holds for every y
theorem ih24Star (y : IGame) : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH24) ⋆ ⋆ y := by
  intro p z
  refine ⟨fun hz => ?_, fun hz => ?_, fun _ => And.intro (fun _ => rfl) (fun e => absurd e (lt_irrefl _))⟩
  · obtain rfl : z = 0 := by cases p <;> simpa using hz
    exact And.intro (fun e => absurd e (by game_cmp)) (fun e => absurd e (by game_cmp))
  · obtain rfl : z = 0 := by cases p <;> simpa using hz
    exact And.intro (fun e => absurd e (by game_cmp)) (fun e => absurd e (by game_cmp))

end W3c1

open IGame W3c1

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH24_of_IH`
theorem w3c1_34 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH24_of_IH 3 := fun h =>
  badP24 ((h (x₁ := X3) (x₂ := ⋆) (y := ⋆) (p := .left) (z := star')).1 (by simp [X3]))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH24_swap_of_IH`
theorem w3c1_35 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH24_swap_of_IH 3 := fun h =>
  badP24 ((h (x₂ := X3) (x₁ := ⋆) (y := ⋆) (p := .left) (z := star')).1 (by simp [X3]))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH24_neg`
theorem w3c1_36 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH24_neg 3 := fun h => by
  have := (h (x₁ := X3) (x₂ := ⋆) (y := -⋆)).2
  rw [neg_neg] at this
  exact badP24 ((this (p := .left) (z := star')).1 (by simp [X3]))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH4_of_IH`
theorem w3c1_37 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH4_of_IH 3 := fun h => by
  have h2 : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».P2) star' ⋆ ⋆ :=
    ((h (x₁ := X3) (x₂ := ⋆) (y := X1)) (p := .left) (q := .left) (z := star') (w := ⋆) starX1).1 (by simp [X3])
  exact badP24 (And.intro h2 (fun e => absurd e (by game_cmp)))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH4_neg`
theorem w3c1_38 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH4_neg 3 := fun h => by
  have := (h (x₁ := X3) (x₂ := ⋆) (y := -X1)).2
  rw [neg_neg] at this
  have h2 : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».P2) star' ⋆ ⋆ :=
    (this (p := .left) (q := .left) (z := star') (w := ⋆) starX1).1 (by simp [X3])
  exact badP24 (And.intro h2 (fun e => absurd e (by game_cmp)))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt_mul_of_equiv`
theorem w3c1_39 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt_mul_of_equiv 5 := fun h => by
  have := h (x₁ := ⋆) (x₂ := ⋆) (y := 1) (a := 0) (b := 0) (ih24Star 1) .rfl (by simp) (by simp)
  simp only [mulOption, zero_mul, mul_zero, mul_one, add_zero, sub_zero] at this
  exact absurd (Game.mk_lt_mk.1 this) (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt`
theorem w3c1_40 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt 10 := fun h => by
  have := h (x := 1) (y := Y3) (a := 2) (b := -1) (c := 0) (d := -1) ih1Num ih1Num (by simp) (by simp) (by simp)
  have e : Game.mk (2 * Y3) = 0 := by
    rw [Game.mk_eq (Numeric.mul_congr_right (by game_cmp : Y3 ≈ 0))]; simp
  simp [mulOption] at this
  rw [e, zero_add] at this
  simp only [← Game.mk_one] at this
  rw [neg_add_lt_iff_lt_add, ← Game.mk_add, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt`
theorem w3c1_41 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt 11 := fun h => by
  have := h (x := 1) (y := Y3) (a := 0) (b := 1) (c := 0) (d := -1) ih1Num ih1Num (by simp) (by simp) (by simp)
  simp [mulOption] at this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt`
theorem w3c1_42 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt 12 := fun h => by
  have := h (x := 1) (y := Y3) (a := 0) (b := -1) (c := 2) (d := -1) ih1Num ih1Num (by simp) (by simp) (by simp)
  have e : Game.mk (2 * Y3) = 0 := by
    rw [Game.mk_eq (Numeric.mul_congr_right (by game_cmp : Y3 ≈ 0))]; simp
  simp [mulOption] at this
  rw [e, add_zero] at this
  simp only [← Game.mk_one] at this
  rw [← sub_eq_add_neg, sub_lt_iff_lt_add, ← Game.mk_add, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt`
theorem w3c1_43 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt 13 := fun h => by
  have := h (x := 1) (y := Y3) (a := 0) (b := -1) (c := 0) (d := 1) ih1Num ih1Num (by simp) (by simp) (by simp)
  simp [mulOption] at this

-- `IGame.Numeric.mulOption`
theorem w3c1_44 : ¬ drop0% IGame.Numeric.mulOption 4 := fun h => by
  have := h ⋆ 0 0 1
  simp [mulOption] at this

-- `IGame.Numeric.mulOption`
theorem w3c1_45 : ¬ drop0% IGame.Numeric.mulOption 5 := fun h => by
  have := h 0 ⋆ 1 0
  simp [mulOption] at this

-- `IGame.Numeric.mulOption`
theorem w3c1_46 : ¬ drop0% IGame.Numeric.mulOption 6 := fun h => by
  have := h 0 1 ⋆ 0
  simp [mulOption] at this

-- `IGame.Numeric.mulOption`
theorem w3c1_47 : ¬ drop0% IGame.Numeric.mulOption 7 := fun h => by
  have := h 1 0 0 ⋆
  simp [mulOption] at this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH3_of_IH`
theorem w3c1_48 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH3_of_IH 9 := fun h => by
  have h3 := h (x₁ := 0) (x₂ := ⋆) (y := 1) (a := 0) (b := 0) (by
      intro p z
      refine ⟨fun hz => by cases p <;> simp at hz, fun hz => ?_, fun hz => ?_⟩
      · obtain rfl : z = 0 := by cases p <;> simpa using hz
        exact And.intro (fun _ => rfl) (fun e => absurd e (lt_irrefl _))
      · obtain rfl : z = 0 := by cases p <;> simpa using hz
        exact And.intro (fun _ => by simp) (fun e => absurd e (by game_cmp)))
    (by
      intro p q z w hw
      refine ⟨fun hz => by cases q <;> simp at hz, fun hz _ => ?_⟩
      obtain rfl : z = 0 := by cases q <;> simpa using hz
      simp)
    (by simp) (by simp)
  obtain ⟨-, -, h3, -⟩ := h3
  change Game.mk (0 * 1) + Game.mk (⋆ * 0) < Game.mk (0 * 0) + Game.mk (⋆ * 1) at h3
  simp only [zero_mul, mul_zero, mul_one, Game.mk_zero, zero_add, add_zero] at h3
  rw [← Game.mk_zero, Game.mk_lt_mk] at h3
  exact absurd h3 (by game_cmp)

namespace W3c1
open IGame

noncomputable abbrev X10 : IGame := !{{-1, 0} | ∅}

instance numX10 : Numeric X10 := by
  rw [numeric_def]; refine ⟨by simp, ?_⟩
  rintro (_ | _) y hy <;> simp at hy <;> rcases hy with rfl | rfl <;> infer_instance

theorem eX10 : Game.mk X10 = 1 := by
  rw [Game.mk_eq (by game_cmp : X10 ≈ 1), Game.mk_one]

end W3c1

open IGame W3c1

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P24_of_IH1`
theorem w3c1_49 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P24_of_IH1 5 := fun h => by
  have h2 := h (x := 1) (y := ⋆) (a := -1) (b := 0) (ih1Const oneConst) (by simp)
  obtain ⟨-, h4⟩ := h2
  have h3 := ((h4 (by game_cmp)).1 0 (by simp) : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».P3) (-1) 0 0 ⋆)
  change Game.mk (-1 * ⋆) + Game.mk (0 * 0) < Game.mk (-1 * 0) + Game.mk (0 * ⋆) at h3
  simp only [neg_mul, one_mul, zero_mul, mul_zero, neg_zero, Game.mk_zero, add_zero] at h3
  rw [← Game.mk_zero, Game.mk_lt_mk] at h3
  exact absurd h3 (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P1_of_equiv`
theorem w3c1_50 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P1_of_equiv 9 := fun h => by
  have := h (x₁ := 0) (x₂ := 0) (x₃ := 0) (y₁ := 0) (y₂ := 0) (y₃ := 0) .rfl (fun _ => rfl) (fun _ => rfl)
  exact lt_irrefl _ this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3_of_le_left`
theorem w3c1_51 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3_of_le_left 6 := fun h => by
  have p3 : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».P3) 0 1 0 1 := by
    show Game.mk (0 * 1) + Game.mk (1 * 0) < Game.mk (0 * 0) + Game.mk (1 * 1)
    simp
  have := h (x₁ := 1) (x₂ := 1) (y₁ := 0) (y₂ := 1) (i := 0)
    (And.intro (fun e => absurd e (by game_cmp)) (And.intro (fun e => absurd e (by game_cmp))
      (And.intro p3 (fun e => absurd e (by game_cmp)))))
  change Game.mk (1 * 1) + Game.mk (1 * 0) < Game.mk (1 * 0) + Game.mk (1 * 1) at this
  rw [add_comm] at this
  exact lt_irrefl _ this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3_of_IH3`
theorem w3c1_52 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3_of_IH3 5 := fun h => by
  have := h (x₁ := -1) (x₂ := 0) (y₁ := 0) (y₂ := 0) (fun i hi => by simp at hi) (by game_cmp)
  exact lt_irrefl _ this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt_of_lt`
theorem w3c1_53 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt_of_lt 11 := fun h => by
  have := h (x := X10) (y := -1) (a := -1) (b := 0) (c := 0) (d := 0) ih1Num ih1Num (by game_cmp)
    (by simp) (by simp) (by simp)
  simp [mulOption] at this
  rw [← Game.mk_one, ← Game.mk_zero, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt_of_lt`
theorem w3c1_54 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt_of_lt 12 := fun h => by
  have := h (x := 1) (y := Y3) (a := 0) (b := -1) (c := 2) (d := -1) ih1Num ih1Num (by game_cmp)
    (by simp) (by simp) (by simp)
  have e : Game.mk (2 * Y3) = 0 := by
    rw [Game.mk_eq (Numeric.mul_congr_right (by game_cmp : Y3 ≈ 0))]; simp
  simp [mulOption] at this
  rw [e, add_zero] at this
  simp only [← Game.mk_one] at this
  rw [← sub_eq_add_neg, sub_lt_iff_lt_add, ← Game.mk_add, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt_of_lt`
theorem w3c1_55 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt_of_lt 13 := fun h => by
  have := h (x := X10) (y := 1) (a := -1) (b := 0) (c := 0) (d := 1) ih1Num ih1Num (by game_cmp)
    (by simp) (by simp) (by simp)
  rw [← Game.mk_neg, Game.mk_lt_mk] at this
  simp only [mulOption, neg_mul, one_mul, mul_one, mul_zero, zero_mul, neg_zero, add_zero, zero_add,
    sub_zero] at this
  exact absurd this (by game_cmp)

namespace W3c1
open IGame

noncomputable abbrev X5 : IGame := !{{0, 1} | {0}}

theorem eY3 : Game.mk Y3 = 0 := by
  rw [Game.mk_eq (by game_cmp : Y3 ≈ 0)]; simp

-- helper: IH1 holds when all options of x are numeric and y is numeric
theorem ih1Opt {x y : IGame} (hx : ∀ p z, z ∈ x.moves p → Numeric z) [hy : Numeric y] :
    (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH1) x y := by
  intro p q a b y' ha hb hy'
  have : Numeric a := hx _ _ ha
  have : Numeric b := hx _ _ hb
  have : Numeric y' := by
    rcases hy' with rfl | ⟨u, hu⟩
    · exact hy
    · exact Numeric.of_mem_moves hu
  exact (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».main_P24) a b y'

theorem optX5 : ∀ p z, z ∈ X5.moves p → Numeric z := by
  intro p z hz
  cases p <;> simp [X5] at hz
  · rcases hz with rfl | rfl <;> infer_instance
  · subst hz; infer_instance

-- helper: a left option of x * y is less than a right option, for numeric x and y
theorem mulLt {x y a b c d : IGame} [Numeric x] [Numeric y] (ha : a ∈ xᴸ) (hb : b ∈ yᴸ)
    (hc : c ∈ xᴸ) (hd : d ∈ (-y)ᴸ) :
    Game.mk (mulOption x y a b) < -Game.mk (mulOption x (-y) c d) := by
  rw [mulOption_neg_right, Game.mk_neg, neg_neg, Game.mk_lt_mk]
  rw [moves_neg] at hd
  have hd' : -d ∈ y.moves .right := by simpa using hd
  have h1 : mulOption x y a b ∈ (x * y).moves .left := mulOption_mem_moves_mul ha hb
  have h2 : mulOption x y c (-d) ∈ (x * y).moves .right := mulOption_mem_moves_mul hc hd'
  exact Numeric.left_lt_right h1 h2

end W3c1

open IGame W3c1

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P1_of_equiv`
theorem w3c1_56 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P1_of_equiv 7 := fun h => by
  have := h (x₁ := ⋆) (x₂ := miny 1 + ⋆) (x₃ := star') (y₁ := ⋆) (y₂ := 1) (y₃ := 0)
    star'_equiv_star.symm (fun _ => by simp) (by
      show Game.mk (⋆ * 0) + Game.mk ((miny 1 + ⋆) * 1) < Game.mk (⋆ * 1) + Game.mk ((miny 1 + ⋆) * 0)
      simp only [mul_zero, mul_one, Game.mk_zero, zero_add, add_zero]
      rw [Game.mk_lt_mk]
      game_cmp)
  change Game.mk (mulOption (miny 1 + ⋆) ⋆ ⋆ 1) < Game.mk (mulOption (miny 1 + ⋆) ⋆ star' 0) at this
  simp only [mulOption, star_mul_star, mul_one, mul_zero, add_zero, sub_zero] at this
  have e : Game.mk (⋆ + (miny 1 + ⋆) - ⋆) = Game.mk (miny 1 + ⋆) := by
    rw [Game.mk_sub, Game.mk_add, add_sub_cancel_left]
  rw [e, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt`
theorem w3c1_57 : drop% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt 4 := by
  intro x y _ _ _ a b c d ha hb hc hd
  exact mulLt ha hb hc hd

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt`
theorem w3c1_58 : drop% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt 5 := by
  intro x y _ _ _ a b c d ha hb hc hd
  exact mulLt ha hb hc hd

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt_of_lt`
theorem w3c1_59 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt_of_lt 4 := fun h => by
  have := h (x := X5) (y := Y3) (a := 0) (b := -1) (c := 1) (d := -1) (ih1Opt optX5) (by game_cmp)
    (by simp [X5]) (by simp) (by simp [X5]) (by simp)
  have e1 : Game.mk (mulOption X5 Y3 0 (-1)) = Game.mk (-X5) := by simp [mulOption]
  have e2 : -Game.mk (mulOption X5 (-Y3) 1 (-1)) = Game.mk (X5 + -1) := by
    simp only [mulOption, Game.mk_sub, Game.mk_add, mul_neg, one_mul, mul_one, Game.mk_neg, eY3,
      Game.mk_one, neg_zero]
    abel
  rw [e1, e2, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

namespace W3c1
open IGame

noncomputable abbrev Z0 : IGame := !{∅ | {2}}

instance numZ0 : Numeric Z0 := by
  rw [numeric_def]; refine ⟨by simp, ?_⟩
  rintro (_ | _) y hy <;> simp at hy; subst hy; infer_instance

theorem z0Equiv : Z0 ≈ 0 := by game_cmp

-- helper: Z0 * star is not below 0 (it is equivalent to star)
theorem z0StarLe : ¬ Z0 * ⋆ ≤ 0 := by game_cmp

theorem z0StarGe : ¬ 0 ≤ Z0 * ⋆ := by game_cmp

-- helper: IH24 Z0 0 star holds
theorem ih24Z0 : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH24) Z0 0 ⋆ := by
  intro p z
  refine ⟨fun hz => ?_, fun hz => by cases p <;> simp at hz, fun hz => ?_⟩
  · obtain rfl : z = 2 := by cases p <;> simpa using hz
    exact And.intro (fun e => absurd e (by game_cmp)) (fun e => absurd e (by game_cmp))
  · obtain rfl : z = 0 := by cases p <;> simpa using hz
    exact And.intro (fun _ => by simp) (fun _ => And.intro (fun a ha => by simp at ha) (fun a ha => by simp at ha))

end W3c1

open IGame W3c1

-- `IGame.Numeric.mul_congr_left`
theorem w3c1_60 : ¬ drop0% IGame.Numeric.mul_congr_left 5 := fun h => by
  have := h (x₁ := Z0) (x₂ := 0) (y := ⋆) z0Equiv
  rw [zero_mul] at this
  exact z0StarLe this.1

-- `IGame.Numeric.mul_congr_right`
theorem w3c1_61 : ¬ drop0% IGame.Numeric.mul_congr_right 3 := fun h => by
  have := h (x := ⋆) (y₁ := Z0) (y₂ := 0) z0Equiv
  rw [mul_zero, mul_comm] at this
  exact z0StarLe this.1

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P2_of_IH`
theorem w3c1_62 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P2_of_IH 3 := fun h => by
  have := h (x₁ := Z0) (x₂ := 0) (y := ⋆) z0Equiv
  rw [zero_mul] at this
  exact z0StarLe this.1

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mul_right_le_of_equiv`
theorem w3c1_63 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mul_right_le_of_equiv 5 := fun h => by
  have := h (x₁ := 0) (x₂ := Z0) (y := ⋆) ih24Z0 z0Equiv.symm
  rw [zero_mul] at this
  exact z0StarGe this

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mul_right_le_of_equiv`
theorem w3c1_64 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mul_right_le_of_equiv 6 := fun h => by
  have := h (x₁ := Z0) (x₂ := 0) (y := ⋆) ih24Z0 z0Equiv
  rw [zero_mul] at this
  exact z0StarLe this
