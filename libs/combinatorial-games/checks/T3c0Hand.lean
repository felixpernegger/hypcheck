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

namespace T3c0
open IGame

noncomputable abbrev Y : IGame := !{{-1, 0} | ∅}
noncomputable abbrev N2 : IGame := !{{0, ⋆} | {0, ⋆}}
noncomputable abbrev N3 : IGame := !{{0, ⋆, N2} | {0, ⋆, N2}}

instance numY : Numeric Y := by
  apply Numeric.mk <;> simp

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

theorem oneInv : (1 : IGame)⁻¹ = 1 :=
  inv_eq_one (by game_cmp) (fun p y hy => by cases p <;> simp at hy; subst hy; exact lt_irrefl 0)

theorem upInv : IGame.up⁻¹ = 1 :=
  inv_eq_one (by game_cmp) (fun p y hy => by
    cases p <;> simp [IGame.up] at hy <;> subst hy
    · exact lt_irrefl 0
    · game_cmp)

theorem YInv : Y⁻¹ = 1 :=
  inv_eq_one (by game_cmp) (fun p y hy => by
    cases p <;> simp at hy
    rcases hy with rfl | rfl <;> game_cmp)

theorem Y1 : Y ≈ 1 := by game_cmp
theorem YY : Y * Y ≈ 1 := by game_cmp
theorem upY : ¬ IGame.up * Y ≈ IGame.up := by game_cmp
theorem sY : ⋆ * Y ≈ N2 := by game_cmp
set_option maxHeartbeats 3000000 in
theorem sYY : ⋆ * (Y * Y) ≈ N3 := by game_cmp
theorem nimNe : ¬ ⋆ + N3 ≈ N2 + N2 := by game_cmp

theorem fix {a b L R : Game} (e : L = R) (h : a + (L - R) = b) : a = b := by
  rw [e, sub_self, add_zero] at h; exact h

theorem fix' {a b L R : Game} (e : L = R) (h : a - (L - R) = b) : a = b := by
  rw [e, sub_self, sub_zero] at h; exact h

theorem swq (p q r : IGame) : Game.mk (p * (q * r)) = Game.mk (q * (p * r)) := by
  rw [← Game.mk_mul_assoc, mul_comm p q, Game.mk_mul_assoc]

end T3c0
open T3c0 IGame

-- `_private.CombinatorialGames.Surreal.Division.0.mulOption_self_inv` idx 4
theorem c0_1 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».mulOption_self_inv 4 := fun h => by
  have hy : Y * Y⁻¹ ≈ 1 := by rw [YInv, mul_one]; exact Y1
  have h5 : Numeric IGame.up⁻¹ := by rw [upInv]; exact Numeric.one
  have h7 : Numeric Y⁻¹ := by rw [YInv]; exact Numeric.one
  have := @h IGame.up Y hy 1 h5 numY h7 Numeric.one
  simp only [invOption, IGame.div_eq_mul_inv, upInv, YInv, mul_one] at this
  rw [← Game.mk_eq_mk] at this
  simp only [Game.mk_mulOption, Game.mk_add, Game.mk_sub, Game.mk_sub_mul, Game.mk_add_mul,
    one_mul, mul_one, Game.mk_one] at this
  rw [Game.mk_eq YY, Game.mk_eq Y1, Game.mk_one] at this
  apply upY
  rw [← Game.mk_eq_mk]
  refine fix this ?_
  abel

-- `_private.CombinatorialGames.Surreal.Division.0.mulOption_self_inv` idx 8
theorem c0_2 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».mulOption_self_inv 8 := fun h => by
  have hy : Y * Y⁻¹ ≈ 1 := by rw [YInv, mul_one]; exact Y1
  have h5 : Numeric (1 : IGame)⁻¹ := by rw [oneInv]; exact Numeric.one
  have h7 : Numeric Y⁻¹ := by rw [YInv]; exact Numeric.one
  have := @h 1 Y hy ⋆ Numeric.one h5 numY h7
  simp only [invOption, IGame.div_eq_mul_inv, oneInv, YInv, mul_one, one_mul] at this
  rw [← Game.mk_eq_mk] at this
  simp only [Game.mk_mulOption, Game.mk_add, Game.mk_sub, Game.mk_sub_mul, Game.mk_add_mul,
    Game.mk_mul_assoc, one_mul, mul_one, Game.mk_one] at this
  rw [swq Y ⋆ Y, mul_comm Y ⋆, Game.mk_eq sYY, Game.mk_eq sY, Game.mk_eq Y1, Game.mk_one] at this
  apply nimNe
  rw [← Game.mk_eq_mk, Game.mk_add, Game.mk_add]
  refine fix' this ?_
  abel
