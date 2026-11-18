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

namespace W3c4
open IGame

-- helper: drop% at explicit universe levels (from W1c3)
open Lean Meta Elab Term in
elab "dropU% " T:ident i:num " [" us:num,* "]" : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := us.getElems.toList.map fun u => Level.ofNat u.getNat
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    mkForallFVars (xs.eraseIdx! i.getNat) body

-- helper: ZMod 2 ordered as Fin 2
instance loZ2 : LinearOrder (ZMod 2) := inferInstanceAs (LinearOrder (Fin 2))

-- `exists_dyadic_btwn` idx 3: necessary (K = ZMod 2 ordered as Fin 2, Archimedean; no rational strictly between 0 and 1)
theorem w34_1 : ¬ drop0% exists_dyadic_btwn 3 := fun h => by
  obtain ⟨q, h1, h2⟩ := @h (ZMod 2) _ _ ⟨by intro x y hy; refine ⟨1, ?_⟩; revert x y hy; decide⟩ 0 1 (by decide)
  generalize ((q.toRat : ℚ) : ZMod 2) = z at h1 h2
  revert z; decide

-- helper: omega as a surreal
noncomputable abbrev ωS : Surreal.{0} := Surreal.mk (NatOrdinal.toIGame (NatOrdinal.of Ordinal.omega0))

-- `exists_dyadic_btwn` idx 4: necessary (K = Surreal at universe 1, x = omega, y = omega + 1; dyadics are short, hence below omega)
theorem w34_2 : ¬ dropU% exists_dyadic_btwn 4 [1] := fun h => by
  obtain ⟨q, h1, -⟩ := @h Surreal.{0} _ _ _ ωS (ωS + 1) (by simp)
  rw [← Surreal.mk_ratCast, ← Surreal.mk_eq (Dyadic.toIGame_equiv q), Surreal.mk_lt_mk] at h1
  exact lt_asymm h1 (Short.lt_omega0 _)

-- `exists_dyadic_btwn` idx 7: necessary (K = Rat, x = y = 0)
theorem w34_3 : ¬ drop0% exists_dyadic_btwn 7 := fun h => by
  obtain ⟨q, h1, h2⟩ := @h ℚ _ _ _ _ 0 0
  exact lt_asymm h1 h2

-- `Real.mem_moves_left_toIGame_of_lt` idx 2: necessary (q = 1, x = 0)
theorem w34_4 : ¬ drop0% Real.mem_moves_left_toIGame_of_lt 2 := fun h => by
  have := @h 1 0
  simp at this
  exact absurd this (by decide)

-- `_private.CombinatorialGames.Surreal.Real.0.Real.toSurreal_def_aux` idx 2: necessary (x = 0, y = z = 1)
theorem w34_5 : ¬ drop0% _private.CombinatorialGames.Surreal.Real.«0».Real.toSurreal_def_aux 2 := fun h => by
  have := @h 0 1 1 ⟨1, by simp, by simp⟩
  exact lt_irrefl _ this

-- `_private.CombinatorialGames.Surreal.Real.0.Real.toSurreal_def_aux` idx 4: necessary (x = 0, y = z = -1)
theorem w34_6 : ¬ drop0% _private.CombinatorialGames.Surreal.Real.«0».Real.toSurreal_def_aux 4 := fun h => by
  have := @h 0 (-1) ⟨-1, by simp, by simp⟩ (-1)
  exact lt_irrefl _ this

-- `_private.CombinatorialGames.Surreal.Real.0.Real.exists_rat_mul_btwn` idx 3: necessary (a = b = x = 0)
theorem w34_7 : ¬ drop0% _private.CombinatorialGames.Surreal.Real.«0».Real.exists_rat_mul_btwn 3 := fun h => by
  obtain ⟨q, -, h2⟩ := @h 0 0 0
  simp at h2

-- `_private.CombinatorialGames.Surreal.Real.0.Real.exists_rat_mul_btwn'` idx 3: necessary (a = b = x = 0)
theorem w34_8 : ¬ drop0% _private.CombinatorialGames.Surreal.Real.«0».Real.exists_rat_mul_btwn' 3 := fun h => by
  obtain ⟨q, h1, -⟩ := @h 0 0 0
  simp at h1

-- `_private.CombinatorialGames.Surreal.Real.0.Real.toIGame_mul_le_mul` idx 3: necessary (x = 1, q = 0, r = 1)
theorem w34_9 : ¬ drop0% _private.CombinatorialGames.Surreal.Real.«0».Real.toIGame_mul_le_mul 3 := fun h => by
  have := @h 1 0 1
  rw [← Surreal.mk_le_mk] at this
  simp at this
  exact zero_lt_one.not_ge this

-- `_private.CombinatorialGames.Surreal.Real.0.Real.toIGame_mul_le_mul'` idx 3: necessary (x = 0, q = 1, r = 1)
theorem w34_10 : ¬ drop0% _private.CombinatorialGames.Surreal.Real.«0».Real.toIGame_mul_le_mul' 3 := fun h => by
  have := @h 0 1 1
  rw [← Surreal.mk_le_mk] at this
  simp at this
  exact zero_lt_one.not_ge this

-- `_private.CombinatorialGames.Surreal.Real.0.Real.dyadic_lt_mul_toIGame'` idx 3: removable (follows from the sign-free dyadic_lt_mul_toIGame)
theorem w34_11 : drop% _private.CombinatorialGames.Surreal.Real.«0».Real.dyadic_lt_mul_toIGame' 3 :=
  fun _ h => (priv% _private.CombinatorialGames.Surreal.Real.«0».Real.dyadic_lt_mul_toIGame) _ h


-- `_private.CombinatorialGames.Surreal.Real.0.Real.dyadic_lt_mul_toIGame'` idx 4: removable (follows from the sign-free dyadic_lt_mul_toIGame)
theorem w34_12 : drop% _private.CombinatorialGames.Surreal.Real.«0».Real.dyadic_lt_mul_toIGame' 4 :=
  fun _ h => (priv% _private.CombinatorialGames.Surreal.Real.«0».Real.dyadic_lt_mul_toIGame) _ h

-- `_private.CombinatorialGames.Surreal.Real.0.Real.dyadic_lt_mul_toIGame'` idx 5: necessary (x = y = 1, q = 1)
theorem w34_13 : ¬ drop0% _private.CombinatorialGames.Surreal.Real.«0».Real.dyadic_lt_mul_toIGame' 5 := fun h => by
  have := @h 1 1 1 one_pos one_pos
  rw [← Surreal.mk_lt_mk] at this
  simp at this

-- `_private.CombinatorialGames.Surreal.Real.0.Real.mul_toIGame_lt_dyadic'` idx 4: removable (follows from the sign-free mul_toIGame_lt_dyadic)
theorem w34_14 : drop% _private.CombinatorialGames.Surreal.Real.«0».Real.mul_toIGame_lt_dyadic' 4 :=
  fun _ h => (priv% _private.CombinatorialGames.Surreal.Real.«0».Real.mul_toIGame_lt_dyadic) _ h

-- `_private.CombinatorialGames.Surreal.Real.0.Real.mul_toIGame_lt_dyadic'` idx 5: necessary (x = y = 1, q = 1)
theorem w34_15 : ¬ drop0% _private.CombinatorialGames.Surreal.Real.«0».Real.mul_toIGame_lt_dyadic' 5 := fun h => by
  have := @h 1 1 1 one_pos one_pos
  rw [← Surreal.mk_lt_mk] at this
  simp at this

-- `_private.CombinatorialGames.Surreal.Real.0.Real.dyadic_lt_mul_toIGame` idx 3: necessary (x = y = 1, q = 1)
theorem w34_16 : ¬ drop0% _private.CombinatorialGames.Surreal.Real.«0».Real.dyadic_lt_mul_toIGame 3 := fun h => by
  have := @h 1 1 1
  rw [← Surreal.mk_lt_mk] at this
  simp at this

-- `_private.CombinatorialGames.Surreal.Real.0.Real.mul_toIGame_lt_dyadic` idx 3: necessary (x = y = 1, q = 1)
theorem w34_17 : ¬ drop0% _private.CombinatorialGames.Surreal.Real.«0».Real.mul_toIGame_lt_dyadic 3 := fun h => by
  have := @h 1 1 1
  rw [← Surreal.mk_lt_mk] at this
  simp at this

end W3c4
