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

namespace W1c2
open IGame Nimber IGame.Impartial Set

universe u

-- helper: Grundy value of the game with every move available to both players
noncomputable def symG (x : IGame.{u}) : Nimber.{u} :=
  sInf (Set.range fun y : (Σ p, x.moves p) ↦ symG y.2.1)ᶜ
termination_by x
decreasing_by igame_wf

theorem le_symG_iff {x : IGame.{u}} {o : Nimber.{u}} :
    o ≤ symG x ↔ Iio o ⊆ Set.range fun y : (Σ p, x.moves p) ↦ symG y.2.1 := by
  rw [symG, le_csInf_iff']
  · rw [← compl_subset_compl (t := Iio o), subset_def]
    simp
  · exact nonempty_of_not_bddAbove (Nimber.not_bddAbove_compl_of_small _)

theorem mem_symG_of_lt {x : IGame.{u}} {o : Nimber.{u}} (h : o < symG x) :
    ∃ p, ∃ a ∈ x.moves p, symG a = o := by
  obtain ⟨⟨p, a, ha⟩, e⟩ := le_symG_iff.1 le_rfl h
  exact ⟨p, a, ha, e⟩

theorem symG_ne {p : Player} {x a : IGame.{u}} (ha : a ∈ x.moves p) : symG a ≠ symG x := by
  intro e
  have := csInf_mem (nonempty_of_not_bddAbove <|
    Nimber.not_bddAbove_compl_of_small (Set.range fun y : (Σ p, x.moves p) ↦ symG y.2.1))
  rw [← symG] at this
  exact this ⟨⟨p, a, ha⟩, e⟩


-- helper: x * y is impartial for every x once y is impartial, with Grundy value symG x * grundy y
theorem key (x y : IGame.{u}) [Impartial y] :
    Impartial (x * y) ∧ ∀ p, grundyAux p (x * y) = symG x * grundy y := by
  have h (p) : grundyAux p (x * y) = symG x * grundy y := by
    apply le_antisymm
    · apply grundyAux_le_of_notMem
      intro ⟨z, hz, hz'⟩
      rw [moves_mul] at hz
      obtain ⟨⟨a, b⟩, ⟨ha, hb⟩ | ⟨ha, hb⟩, rfl⟩ := hz
      all_goals
        impartial
        have hsa : Subposition a x := .of_mem_moves ha
        have hsb : Subposition b y := .of_mem_moves hb
        have h1 := key a y; have h2 := key x b; have h3 := key a b
        have := h1.1; have := h2.1; have := h3.1
        simp_rw [mulOption, grundyAux_sub, grundyAux_add, h1.2, h2.2, h3.2] at hz'
        exact mul_ne_of_ne (symG_ne ha) (grundy_moves_ne hb) hz'
    · rw [le_grundyAux_iff]
      intro c hc
      obtain ⟨a', ha', b', hb', rfl⟩ := exists_of_lt_mul hc
      obtain ⟨q, a, ha, rfl⟩ := mem_symG_of_lt ha'
      rw [← grundyAux_eq_grundy (q * p)] at hb'
      obtain ⟨b, hb, rfl⟩ := mem_grundyAux_image_of_lt hb'
      have hm := mulOption_mem_moves_mul ha hb
      rw [show q * (q * p) = p by cases q <;> cases p <;> rfl] at hm
      refine ⟨_, hm, ?_⟩
      impartial
      have hsa : Subposition a x := .of_mem_moves ha
      have hsb : Subposition b y := .of_mem_moves hb
      have h1 := key a y; have h2 := key x b; have h3 := key a b
      have := h1.1; have := h2.1; have := h3.1
      simp_rw [mulOption, grundyAux_sub, grundyAux_add, h1.2, h2.2, h3.2, grundyAux_eq_grundy]
  refine ⟨of_grundyAux_left_eq_grundyAux_right ?_ ((h left).trans (h right).symm), h⟩
  intro p
  simp only [forall_moves_mul, mulOption]
  intro p' a ha b hb
  impartial
  have hsa : Subposition a x := .of_mem_moves ha
  have hsb : Subposition b y := .of_mem_moves hb
  have := (key a y).1; have := (key x b).1; have := (key a b).1
  infer_instance
termination_by (x, y)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ hsa
    | exact Prod.Lex.right _ hsb


-- helper: right Grundy value of 1 is 0
theorem grAuxOne : grundyAux .right (1 : IGame) = 0 := by
  rw [grundyAux_def]; simp

-- helper: 2 * star is equivalent to 0
theorem twoStar : (2 : IGame) * ⋆ ≈ 0 := by game_cmp

end W1c2

open IGame Nimber IGame.Impartial W1c2

universe u

-- `_private.CombinatorialGames.Game.Impartial.Multiplication.0.IGame.Impartial.mul'`
theorem w1c2_1 : ¬ drop0% _private.CombinatorialGames.Game.Impartial.Multiplication.«0».IGame.Impartial.mul' 2 := fun h => by
  have := (@h 1 ⋆ inferInstance).2
  simp only [_root_.one_mul, grAuxOne, MulZeroClass.zero_mul, grundyAux_eq_grundy, grundy_star] at this
  exact one_ne_zero this

-- `_private.CombinatorialGames.Game.Impartial.Multiplication.0.IGame.Impartial.mul'`
theorem w1c2_2 : ¬ drop0% _private.CombinatorialGames.Game.Impartial.Multiplication.«0».IGame.Impartial.mul' 3 := fun h => by
  have := (@h ⋆ 1 inferInstance).2
  simp only [_root_.mul_one, grAuxOne, MulZeroClass.mul_zero, grundyAux_eq_grundy, grundy_star] at this
  exact one_ne_zero this

-- `IGame.Impartial.mul`
theorem w1c2_3 : drop% IGame.Impartial.mul 2 := fun x y _ => (key x y).1

-- `IGame.Impartial.mul`
theorem w1c2_4 : drop% IGame.Impartial.mul 3 := fun x y _ => by
  rw [_root_.mul_comm]; exact (key y x).1

-- `IGame.Impartial.grundy_mul`
theorem w1c2_5 : ¬ indep0% IGame.Impartial.grundy_mul 2 := fun h => by
  have := impartial_def.1 (@h 1 0 Impartial.zero)
  exact absurd this.1 (by game_cmp)

-- `IGame.Impartial.grundy_mul`
theorem w1c2_6 : ¬ indep0% IGame.Impartial.grundy_mul 3 := fun h => by
  have := impartial_def.1 (@h 0 1 Impartial.zero)
  exact absurd this.1 (by game_cmp)

-- `IGame.Impartial.mul_equiv_zero`
theorem w1c2_7 : ¬ drop0% IGame.Impartial.mul_equiv_zero 2 := fun h => by
  rcases (@h 2 ⋆ inferInstance).1 twoStar with e | e <;> exact absurd e (by game_cmp)

-- `IGame.Impartial.mul_equiv_zero`
theorem w1c2_8 : ¬ drop0% IGame.Impartial.mul_equiv_zero 3 := fun h => by
  rcases (@h ⋆ 2 inferInstance).1 (by rw [_root_.mul_comm]; exact twoStar) with e | e <;>
    exact absurd e (by game_cmp)

-- `IGame.Impartial.mulOption`
theorem w1c2_9 : drop% IGame.Impartial.mulOption 4 := fun x y a b _ _ _ => by
  have := (key a y).1; have := (key x b).1; have := (key a b).1
  exact .sub ..

-- `IGame.Impartial.mulOption`
theorem w1c2_10 : drop% IGame.Impartial.mulOption 5 := fun x y a b _ _ _ => by
  have := (key y a).1; have := (key x b).1; have := (key a b).1
  rw [_root_.mul_comm] at this; rw [mulOption, _root_.mul_comm a y]
  exact .sub ..

-- `IGame.Impartial.mulOption`
theorem w1c2_11 : drop% IGame.Impartial.mulOption 6 := fun x y a b _ _ _ => by
  have := (key a y).1; have := (key x b).1; have := (key a b).1
  exact .sub ..

-- `IGame.Impartial.mulOption`
theorem w1c2_12 : drop% IGame.Impartial.mulOption 7 := fun x y a b _ _ _ => by
  have := (key a y).1; have := (key b x).1; have := (key b a).1
  rw [mulOption, _root_.mul_comm x b, _root_.mul_comm a b]
  exact .sub ..

-- `IGame.Impartial.mul_congr_left`
theorem w1c2_13 : drop% IGame.Impartial.mul_congr_left 3 := fun {y x₁ x₂} _ _ he => by
  have h1 := key y x₁; have h2 := key y x₂
  have := h1.1; have := h2.1
  rw [_root_.mul_comm x₁, _root_.mul_comm x₂, ← grundy_eq_iff_equiv, ← grundyAux_eq_grundy right,
    ← grundyAux_eq_grundy right (y * x₂), h1.2, h2.2, grundy_eq_iff_equiv.2 he]

-- `IGame.Impartial.mul_congr_left`
theorem w1c2_14 : ¬ drop0% IGame.Impartial.mul_congr_left 4 := fun h => by
  have := @h ⋆ star' ⋆ inferInstance inferInstance star'_equiv_star
  rw [IGame.star_mul_star] at this
  exact star'_mul_star_not_equiv this

-- `IGame.Impartial.mul_congr_left`
theorem w1c2_15 : ¬ drop0% IGame.Impartial.mul_congr_left 5 := fun h => by
  have := @h ⋆ ⋆ star' inferInstance inferInstance star'_equiv_star.symm
  rw [IGame.star_mul_star] at this
  exact star'_mul_star_not_equiv this.symm

-- `IGame.Impartial.mul_congr_left`
theorem w1c2_16 : ¬ drop0% IGame.Impartial.mul_congr_left 6 := fun h => by
  have := @h ⋆ 0 ⋆ inferInstance inferInstance inferInstance
  rw [IGame.star_mul_star, MulZeroClass.zero_mul] at this
  exact absurd this (by game_cmp)

-- `IGame.Impartial.mul_congr_right`
theorem w1c2_17 : drop% IGame.Impartial.mul_congr_right 3 := fun {x y₁ y₂} _ _ he => by
  have h1 := key x y₁; have h2 := key x y₂
  have := h1.1; have := h2.1
  rw [← grundy_eq_iff_equiv, ← grundyAux_eq_grundy right,
    ← grundyAux_eq_grundy right (x * y₂), h1.2, h2.2, grundy_eq_iff_equiv.2 he]

-- `IGame.Impartial.mul_congr_right`
theorem w1c2_18 : ¬ drop0% IGame.Impartial.mul_congr_right 4 := fun h => by
  have := @h ⋆ star' ⋆ inferInstance inferInstance star'_equiv_star
  rw [IGame.star_mul_star, _root_.mul_comm] at this
  exact star'_mul_star_not_equiv this

-- `IGame.Impartial.mul_congr_right`
theorem w1c2_19 : ¬ drop0% IGame.Impartial.mul_congr_right 5 := fun h => by
  have := @h ⋆ ⋆ star' inferInstance inferInstance star'_equiv_star.symm
  rw [IGame.star_mul_star, _root_.mul_comm] at this
  exact star'_mul_star_not_equiv this.symm

-- `IGame.Impartial.mul_congr_right`
theorem w1c2_20 : ¬ drop0% IGame.Impartial.mul_congr_right 6 := fun h => by
  have := @h ⋆ 0 ⋆ inferInstance inferInstance inferInstance
  rw [IGame.star_mul_star, MulZeroClass.mul_zero] at this
  exact absurd this (by game_cmp)

-- `IGame.Impartial.mul_congr`
theorem w1c2_21 : ¬ drop0% IGame.Impartial.mul_congr 4 := fun h => by
  have := @h star' ⋆ ⋆ ⋆ inferInstance inferInstance inferInstance star'_equiv_star .rfl
  rw [IGame.star_mul_star] at this
  exact star'_mul_star_not_equiv this

-- `IGame.Impartial.mul_congr`
theorem w1c2_22 : ¬ drop0% IGame.Impartial.mul_congr 5 := fun h => by
  have := @h ⋆ star' ⋆ ⋆ inferInstance inferInstance inferInstance star'_equiv_star.symm .rfl
  rw [IGame.star_mul_star] at this
  exact star'_mul_star_not_equiv this.symm

-- `IGame.Impartial.mul_congr`
theorem w1c2_23 : ¬ drop0% IGame.Impartial.mul_congr 6 := fun h => by
  have := @h ⋆ ⋆ star' ⋆ inferInstance inferInstance inferInstance .rfl star'_equiv_star
  rw [IGame.star_mul_star, _root_.mul_comm] at this
  exact star'_mul_star_not_equiv this

-- `IGame.Impartial.mul_congr`
theorem w1c2_24 : ¬ drop0% IGame.Impartial.mul_congr 7 := fun h => by
  have := @h ⋆ ⋆ ⋆ star' inferInstance inferInstance inferInstance .rfl star'_equiv_star.symm
  rw [IGame.star_mul_star, _root_.mul_comm] at this
  exact star'_mul_star_not_equiv this.symm

-- `IGame.Impartial.mul_congr`
theorem w1c2_25 : ¬ drop0% IGame.Impartial.mul_congr 8 := fun h => by
  have := @h 0 ⋆ ⋆ ⋆ inferInstance inferInstance inferInstance inferInstance .rfl
  rw [IGame.star_mul_star, MulZeroClass.zero_mul] at this
  exact absurd this (by game_cmp)

-- `IGame.Impartial.mul_congr`
theorem w1c2_26 : ¬ drop0% IGame.Impartial.mul_congr 9 := fun h => by
  have := @h ⋆ ⋆ 0 ⋆ inferInstance inferInstance inferInstance inferInstance .rfl
  rw [IGame.star_mul_star, MulZeroClass.mul_zero] at this
  exact absurd this (by game_cmp)
