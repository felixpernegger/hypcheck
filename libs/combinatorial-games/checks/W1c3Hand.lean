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

open Lean Meta Elab Term in
/-- `indepU% T i [l₀, l₁, …]`: `indep% T i` with the universe parameters of `T` set to the given numerals. -/
elab "indepU% " T:ident i:num " [" us:num,* "]" : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := us.getElems.toList.map fun u => Level.ofNat u.getNat
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs _ => do
    let x := (xs.getD (i.getNat) default)
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

open Lean Meta Elab Term in
/-- `dropU% T i [l₀, l₁, …]`: `drop% T i` with the universe parameters of `T` set to the given numerals. -/
elab "dropU% " T:ident i:num " [" us:num,* "]" : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := us.getElems.toList.map fun u => Level.ofNat u.getNat
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    mkForallFVars (xs.eraseIdx! i.getNat) body

namespace W1c3
open LGame Set

-- helper: the universe of Type is not 0-small
theorem notSmallType : ¬ Small.{0} (Set.univ : Set Type) := by
  rw [small_univ_iff]; exact not_small_type.{0, 0}

-- helper: Option Type is not 0-small
theorem notSmallOptType : ¬ Small.{0} (Set.univ : Set (Option Type)) := by
  rw [small_univ_iff]; intro h
  exact not_small_type.{0, 0} (small_of_injective (f := fun t : Type => some t) (Option.some_injective _))

-- helper: the universe of IGame is not small
theorem notSmallIGame.{u} : ¬ Small.{u} (Set.univ : Set IGame.{u}) := by
  rw [small_univ_iff]; intro h
  exact not_small_ordinal.{u} (small_of_injective (f := fun o : NatOrdinal.{u} => NatOrdinal.toIGame o)
    NatOrdinal.toIGame.injective)

-- helper: the universe of LGame is not small
theorem notSmallLGame.{u} : ¬ Small.{u} (Set.univ : Set LGame.{u}) := by
  rw [small_univ_iff]; intro h
  exact notSmallIGame.{u} (small_univ_iff.2 (small_of_injective IGame.toLGame.injective))

-- helper: 1 ≠ 0 in LGame
theorem oneNeZero : (1 : LGame) ≠ 0 := fun h => by
  have := congrArg (moves left) h; simp at this

-- helper: dud is not a stopper for any player
theorem notStopperForDud (p : Player) : ¬ StopperFor p dud := by
  intro h
  suffices ∀ q x, StopperFor q x → x ≠ dud from this p dud h rfl
  intro q x hx
  induction hx with
  | @mk q x _ ih => rintro rfl; exact ih dud (by simp) rfl


-- helper: models on Type (left / right moves everything) and the empty model
def ML : Player → Type → Set Type := Player.cases (fun _ => univ) (fun _ => ∅)
def MR : Player → Type → Set Type := Player.cases (fun _ => ∅) (fun _ => univ)
def ME {γ : Type} : Player → γ → Set γ := fun _ _ => ∅

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.unique`
theorem c3_1 : ¬ indepU% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.unique 2 [0, 1] := fun h =>
  notSmallType (@h Type ML (fun _ => small_empty) PUnit (fun _ => 0) (fun _ => 0) ⟨PUnit, Relation.ReflTransGen.refl⟩ PUnit)

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.unique`
theorem c3_2 : ¬ indepU% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.unique 3 [0, 1] := fun h =>
  notSmallType (@h Type MR (fun _ => small_empty) PUnit (fun _ => 0) (fun _ => 0) ⟨PUnit, Relation.ReflTransGen.refl⟩ PUnit)

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.corec'_trans`
theorem c3_3 : ¬ indepU% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.corec'_trans 2 [0, 1] := fun h =>
  notSmallType (@h Type ML (fun _ => small_empty) PUnit PUnit Relation.ReflTransGen.refl ⟨PUnit, Relation.ReflTransGen.refl⟩ PUnit)

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.corec'_trans`
theorem c3_4 : ¬ indepU% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.corec'_trans 3 [0, 1] := fun h =>
  notSmallType (@h Type MR (fun _ => small_empty) PUnit PUnit Relation.ReflTransGen.refl ⟨PUnit, Relation.ReflTransGen.refl⟩ PUnit)

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.corec'_aux`
theorem c3_5 : ¬ indepU% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.corec'_aux 2 [0, 1] := fun h =>
  notSmallType (@h Type ML (fun _ => small_empty) PUnit PUnit (Or.inl trivial) 0 PUnit)

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.corec'_aux`
theorem c3_6 : ¬ indepU% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.corec'_aux 3 [0, 1] := fun h =>
  notSmallType (@h Type MR (fun _ => small_empty) PUnit PUnit (Or.inr trivial) 0 PUnit)

-- `LGame.moves_corec`
theorem c3_7 : ¬ indepU% LGame.moves_corec 3 [0, 1] := fun h =>
  notSmallType (@h Type .left ML (fun _ => small_empty) PUnit PUnit)

-- `LGame.moves_comp_corec`
theorem c3_8 : ¬ indepU% LGame.moves_comp_corec 3 [0, 1] := fun h =>
  notSmallType (@h Type .left ML (fun _ => small_empty) PUnit)

-- `LGame.moves_comp_corec`
theorem c3_9 : ¬ indepU% LGame.moves_comp_corec 4 [0, 1] := fun h =>
  notSmallType (@h Type .left MR (fun _ => small_empty) PUnit)

-- `LGame.neg_corec`
theorem c3_10 : ¬ indepU% LGame.neg_corec 2 [0, 1] := fun h =>
  notSmallType (@h Type ML (fun _ => small_empty) PUnit)

-- `LGame.neg_corec`
theorem c3_11 : ¬ indepU% LGame.neg_corec 3 [0, 1] := fun h =>
  notSmallType (@h Type MR (fun _ => small_empty) PUnit)

-- `LGame.neg_corec_apply`
theorem c3_12 : ¬ indepU% LGame.neg_corec_apply 2 [0, 1] := fun h =>
  notSmallType (@h Type ML (fun _ => small_empty) PUnit PUnit)

-- `LGame.neg_corec_apply`
theorem c3_13 : ¬ indepU% LGame.neg_corec_apply 3 [0, 1] := fun h =>
  notSmallType (@h Type MR (fun _ => small_empty) PUnit PUnit)

-- `LGame.corec_add_corec`
theorem c3_14 : ¬ indepU% LGame.corec_add_corec 4 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit ML ME (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit PUnit.unit PUnit)

-- `LGame.corec_add_corec`
theorem c3_15 : ¬ indepU% LGame.corec_add_corec 5 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit MR ME (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit PUnit.unit PUnit)

-- `LGame.corec_add_corec`
theorem c3_16 : ¬ indepU% LGame.corec_add_corec 6 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME ML (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit.unit PUnit PUnit)

-- `LGame.corec_add_corec`
theorem c3_17 : ¬ indepU% LGame.corec_add_corec 7 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME MR (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit.unit PUnit PUnit)

-- `LGame.corec_sub_corec`
theorem c3_18 : ¬ indepU% LGame.corec_sub_corec 5 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit MR ME (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit PUnit.unit PUnit)

-- `LGame.corec_sub_corec`
theorem c3_19 : ¬ indepU% LGame.corec_sub_corec 6 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME ML (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit.unit PUnit PUnit)

-- `LGame.corec_sub_corec`
theorem c3_20 : ¬ indepU% LGame.corec_sub_corec 7 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME MR (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit.unit PUnit PUnit)

-- `LGame.MulTy.moves_toLGame`
theorem c3_21 : ¬ indepU% LGame.MulTy.moves_toLGame 7 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit .left ML ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) (.left, PUnit, PUnit.unit) PUnit)

-- `LGame.MulTy.moves_toLGame`
theorem c3_22 : ¬ indepU% LGame.MulTy.moves_toLGame 8 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit .left MR ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) (.left, PUnit, PUnit.unit) PUnit)

-- `LGame.MulTy.moves_toLGame`
theorem c3_23 : ¬ indepU% LGame.MulTy.moves_toLGame 9 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type .left ME ML (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) (.left, PUnit.unit, PUnit) PUnit)

-- `LGame.MulTy.moves_toLGame`
theorem c3_24 : ¬ indepU% LGame.MulTy.moves_toLGame 10 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type .left ME MR (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) (.left, PUnit.unit, PUnit) PUnit)

-- `LGame.MulTy.corec_zero`
theorem c3_25 : ¬ indepU% LGame.MulTy.corec_zero 6 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit ML ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit)

-- `LGame.MulTy.corec_zero`
theorem c3_26 : ¬ indepU% LGame.MulTy.corec_zero 7 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit MR ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit)

-- `LGame.MulTy.corec_zero`
theorem c3_27 : ¬ indepU% LGame.MulTy.corec_zero 8 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME ML (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit)

-- `LGame.MulTy.corec_zero`
theorem c3_28 : ¬ indepU% LGame.MulTy.corec_zero 9 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME MR (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit)

-- `LGame.MulTy.corec_neg`
theorem c3_29 : ¬ indepU% LGame.MulTy.corec_neg 6 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit ML ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 PUnit)

-- `LGame.MulTy.corec_neg`
theorem c3_30 : ¬ indepU% LGame.MulTy.corec_neg 7 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit MR ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 PUnit)

-- `LGame.MulTy.corec_neg`
theorem c3_31 : ¬ indepU% LGame.MulTy.corec_neg 9 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME MR (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 PUnit)

-- `LGame.MulTy.corec_add`
theorem c3_32 : ¬ indepU% LGame.MulTy.corec_add 6 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit ML ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 0 PUnit)

-- `LGame.MulTy.corec_add`
theorem c3_33 : ¬ indepU% LGame.MulTy.corec_add 7 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit MR ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 0 PUnit)

-- `LGame.MulTy.corec_add`
theorem c3_34 : ¬ indepU% LGame.MulTy.corec_add 8 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME ML (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 0 PUnit)

-- `LGame.MulTy.corec_add`
theorem c3_35 : ¬ indepU% LGame.MulTy.corec_add 9 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME MR (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 0 PUnit)

-- `LGame.MulTy.corec_mulOption`
theorem c3_36 : ¬ indepU% LGame.MulTy.corec_mulOption 6 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit ML ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) .left (PUnit, PUnit.unit) (PUnit, PUnit.unit) PUnit)

-- `LGame.MulTy.corec_mulOption`
theorem c3_37 : ¬ indepU% LGame.MulTy.corec_mulOption 7 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit MR ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) .left (PUnit, PUnit.unit) (PUnit, PUnit.unit) PUnit)

-- `LGame.MulTy.corec_mulOption`
theorem c3_38 : ¬ indepU% LGame.MulTy.corec_mulOption 8 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME ML (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) .left (PUnit.unit, PUnit) (PUnit.unit, PUnit) PUnit)

-- `LGame.MulTy.corec_mulOption`
theorem c3_39 : ¬ indepU% LGame.MulTy.corec_mulOption 9 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME MR (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) .left (PUnit.unit, PUnit) (PUnit.unit, PUnit) PUnit)

-- `LGame.corec_mulTy`
theorem c3_40 : ¬ indepU% LGame.corec_mulTy 6 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit ML ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 PUnit)

-- `LGame.corec_mulTy`
theorem c3_41 : ¬ indepU% LGame.corec_mulTy 7 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit MR ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 PUnit)

-- `LGame.corec_mulTy`
theorem c3_42 : ¬ indepU% LGame.corec_mulTy 8 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME ML (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 PUnit)

-- `LGame.corec_mulTy`
theorem c3_43 : ¬ indepU% LGame.corec_mulTy 9 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME MR (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 PUnit)

-- `LGame.MulTy.corec_swap`
theorem c3_44 : ¬ indepU% LGame.MulTy.corec_swap 6 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit ML ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 PUnit)

-- `LGame.MulTy.corec_swap`
theorem c3_45 : ¬ indepU% LGame.MulTy.corec_swap 7 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit MR ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 PUnit)

-- `LGame.MulTy.corec_swap`
theorem c3_46 : ¬ indepU% LGame.MulTy.corec_swap 8 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME ML (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 PUnit)

-- `LGame.MulTy.corec_swap`
theorem c3_47 : ¬ indepU% LGame.MulTy.corec_swap 9 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME MR (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 PUnit)

-- `LGame.corec_mul_corec`
theorem c3_48 : ¬ indepU% LGame.corec_mul_corec 6 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit ML ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit PUnit.unit PUnit)

-- `LGame.corec_mul_corec`
theorem c3_49 : ¬ indepU% LGame.corec_mul_corec 7 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit MR ME (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit PUnit.unit PUnit)

-- `LGame.corec_mul_corec`
theorem c3_50 : ¬ indepU% LGame.corec_mul_corec 8 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME ML (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit.unit PUnit PUnit)

-- `LGame.corec_mul_corec`
theorem c3_51 : ¬ indepU% LGame.corec_mul_corec 9 [0, 0, 1] := fun h =>
  notSmallType (@h PUnit Type ME MR (Classical.decEq _) (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) PUnit.unit PUnit PUnit)

-- helper: depth-one and depth-two subpositions
theorem notSubZero (x : LGame) : ¬ Subposition x 0 := by
  intro h; obtain ⟨b, -, hb⟩ := Relation.TransGen.tail'_iff.1 h; simp at hb

theorem sub01 : Subposition 0 1 := Subposition.of_mem_moves (p := left) (by simp)

theorem subOne {x : LGame} (h : Subposition x 1) : x = 0 := by
  obtain ⟨b, hx, hb⟩ := Relation.TransGen.tail'_iff.1 h
  simp at hb; subst hb
  rcases Relation.ReflTransGen.cases_tail hx with rfl | ⟨c, -, hc⟩
  · rfl
  · simp at hc

-- helper: the game two = !{{1} | ∅}
noncomputable def two : LGame := !{{1} | ∅}

theorem sub0two : Subposition 0 two :=
  sub01.trans (Subposition.of_mem_moves (p := left) (by simp [two]))

theorem zeroNotMemTwo : (0 : LGame) ∉ ⋃ p, two.moves p := by
  simp [two]; exact oneNeZero.symm

-- `LGame.Subposition.of_mem_moves`
theorem c3_101 : ¬ drop0% LGame.Subposition.of_mem_moves 3 := fun h => notSubZero 0 (@h .left 0 0)

-- `LGame.Subposition.trans`
theorem c3_102 : ¬ drop0% LGame.Subposition.trans 3 := fun h => oneNeZero (subOne (@h 1 0 1 sub01))

-- `LGame.Subposition.trans`
theorem c3_103 : ¬ drop0% LGame.Subposition.trans 4 := fun h => notSubZero 0 (@h 0 1 0 sub01)

-- `LGame.Subposition.head_induction`
theorem c3_104 : ¬ drop0% LGame.Subposition.head_induction 2 := fun h =>
  @h 1 (fun _ _ => False) (fun _ _ _ _ _ h => h) 0 sub01

-- `LGame.Subposition.head_induction`
theorem c3_105 : ¬ drop0% LGame.Subposition.head_induction 3 := fun h =>
  zeroNotMemTwo (@h two (fun x _ => x ∈ ⋃ p, two.moves p) (fun p _ hx => mem_iUnion_of_mem p hx) 0 sub0two)

-- `LGame.Subposition.head_induction`
theorem c3_106 : ¬ indep0% LGame.Subposition.head_induction 5 := fun h =>
  notSubZero 0 (@h 0 (fun _ _ => True) (fun _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) 0)

-- `LGame.Subposition.tail_induction`
theorem c3_107 : ¬ drop0% LGame.Subposition.tail_induction 2 := fun h =>
  @h 0 (fun _ _ => False) (fun _ _ _ _ _ h => h) 1 sub01

-- `LGame.Subposition.tail_induction`
theorem c3_108 : ¬ drop0% LGame.Subposition.tail_induction 3 := fun h =>
  zeroNotMemTwo (@h 0 (fun y _ => 0 ∈ ⋃ p, y.moves p) (fun p _ hy => mem_iUnion_of_mem p hy) two sub0two)

-- `LGame.Subposition.tail_induction`
theorem c3_109 : ¬ indep0% LGame.Subposition.tail_induction 5 := fun h =>
  notSubZero 0 (@h 0 (fun _ _ => True) (fun _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) 0)

-- `LGame.Subposition.trans_induction`
theorem c3_110 : ¬ drop0% LGame.Subposition.trans_induction 1 := fun h =>
  @h (fun _ _ _ => False) (fun _ _ _ _ _ h _ => h) 0 1 sub01

-- `LGame.Subposition.trans_induction`
theorem c3_111 : ¬ drop0% LGame.Subposition.trans_induction 2 := fun h =>
  zeroNotMemTwo (@h (fun x y _ => x ∈ ⋃ p, y.moves p) (fun p _ _ hxy => mem_iUnion_of_mem p hxy) 0 two sub0two)

-- `LGame.Subposition.trans_induction`
theorem c3_112 : ¬ indep0% LGame.Subposition.trans_induction 5 := fun h =>
  notSubZero 0 (@h (fun _ _ _ => True) (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) 0 0)

-- `LGame.eq_of_bisim`
theorem c3_113 : ¬ drop0% LGame.eq_of_bisim 1 := fun h => oneNeZero (@h (fun _ _ => True) 1 0 trivial)

-- `LGame.eq_of_bisim`
theorem c3_114 : ¬ drop0% LGame.eq_of_bisim 4 := fun h => oneNeZero (@h (fun _ _ => False) (fun _ _ h => h.elim) 1 0)

-- `LGame.ext`
theorem c3_115 : ¬ drop0% LGame.ext 2 := fun h => oneNeZero (@h 1 0)

-- `LGame.StopperFor.of_mem_moves`
theorem c3_116 : ¬ drop0% LGame.StopperFor.of_mem_moves 3 := fun h =>
  notStopperForDud _ (@h .left dud dud (by simp))

-- `LGame.StopperFor.of_mem_moves`
theorem c3_117 : ¬ drop0% LGame.StopperFor.of_mem_moves 4 := fun h =>
  notStopperForDud _ (@h .left 0 dud (StopperFor.mk (by simp)))

-- `LGame.StopperFor.neg`
theorem c3_118 : ¬ drop0% LGame.StopperFor.neg 2 := fun h => by
  have := @h .left dud; rw [neg_dud] at this; exact notStopperForDud _ this

-- `LGame.Stopper.stopperFor`
theorem c3_119 : ¬ drop0% LGame.Stopper.stopperFor 2 := fun h => notStopperForDud _ (@h .left dud)

-- `LGame.Stopper.mk`
theorem c3_120 : ¬ drop0% LGame.Stopper.mk 1 := fun h => notStopperForDud .left (@h dud .left)

-- `LGame.Stopper.neg`
theorem c3_121 : ¬ drop0% LGame.Stopper.neg 1 := fun h => by
  have := @h dud; rw [neg_dud] at this; exact notStopperForDud .left (this .left)

-- `LGame.moves_ofSets`
theorem c3_122 : ¬ indep0% LGame.moves_ofSets 2 := fun h =>
  notSmallLGame (@h .left (Player.cases univ ∅) small_empty)

-- `LGame.moves_ofSets`
theorem c3_123 : ¬ indep0% LGame.moves_ofSets 3 := fun h =>
  notSmallLGame (@h .left (Player.cases ∅ univ) small_empty)

-- `LGame.moves_left_ofSets`
theorem c3_124 : ¬ indep0% LGame.moves_left_ofSets 2 := fun h => notSmallLGame (@h univ ∅ small_empty)

-- `LGame.moves_left_ofSets`
theorem c3_125 : ¬ indep0% LGame.moves_left_ofSets 3 := fun h => notSmallLGame (@h ∅ univ small_empty)

-- `LGame.moves_right_ofSets`
theorem c3_126 : ¬ indep0% LGame.moves_right_ofSets 2 := fun h => notSmallLGame (@h univ ∅ small_empty)

-- `LGame.moves_right_ofSets`
theorem c3_127 : ¬ indep0% LGame.moves_right_ofSets 3 := fun h => notSmallLGame (@h ∅ univ small_empty)

-- `LGame.neg_ofSets`
theorem c3_128 : ¬ indep0% LGame.neg_ofSets 2 := fun h => notSmallLGame (@h univ ∅ small_empty)

-- `LGame.neg_ofSets`
theorem c3_129 : ¬ indep0% LGame.neg_ofSets 3 := fun h => notSmallLGame (@h ∅ univ small_empty)

-- `LGame.neg_ofSets'`
theorem c3_130 : ¬ indep0% LGame.neg_ofSets' 1 := fun h =>
  notSmallLGame (@h (Player.cases univ ∅) small_empty)

-- `LGame.neg_ofSets'`
theorem c3_131 : ¬ indep0% LGame.neg_ofSets' 2 := fun h =>
  notSmallLGame (@h (Player.cases ∅ univ) small_empty)

-- `LGame.neg_ofSets_const`
theorem c3_132 : ¬ indep0% LGame.neg_ofSets_const 1 := fun h => notSmallLGame (@h univ)

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.small_succ'`
theorem c3_133 : ¬ dropU% _private.CombinatorialGames.Game.Loopy.Basic.«0».small_succ' 1 [2, 0] := fun h =>
  not_small_type.{1, 1} (h (Type 1))

-- helper: models on Type 1
def ML1 : Player → Type 1 → Set (Type 1) := Player.cases (fun _ => univ) (fun _ => ∅)
def MR1 : Player → Type 1 → Set (Type 1) := Player.cases (fun _ => ∅) (fun _ => univ)

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.instSmallSubtypeReachable`
theorem c3_134 : ¬ dropU% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.instSmallSubtypeReachable 2 [0, 2] :=
  fun h => by
    have := @h (Type 1) ML1 (fun _ => small_empty) PUnit
    exact not_small_type.{1, 1} (@small_of_surjective _ _ this Subtype.val
      (fun x => ⟨⟨x, Relation.ReflTransGen.single (Or.inl trivial)⟩, rfl⟩))

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.instSmallSubtypeReachable`
theorem c3_135 : ¬ dropU% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.instSmallSubtypeReachable 3 [0, 2] :=
  fun h => by
    have := @h (Type 1) MR1 (fun _ => small_empty) PUnit
    exact not_small_type.{1, 1} (@small_of_surjective _ _ this Subtype.val
      (fun x => ⟨⟨x, Relation.ReflTransGen.single (Or.inr trivial)⟩, rfl⟩))

-- helper: hom_unique without smallness
theorem homUnique.{u, v} {α : Type v} {mov : Player → α → Set α} (f g : α → LGame.{u})
    (hf : ∀ p, moves p ∘ f = image f ∘ mov p) (hg : ∀ p, moves p ∘ g = image g ∘ mov p) (x : α) :
    f x = g x := by
  refine eq_of_bisim (fun a b => ∃ y, f y = a ∧ g y = b) ?_ ⟨x, rfl, rfl⟩
  rintro _ _ ⟨y, rfl, rfl⟩ p
  refine ⟨(fun z => (f z, g z)) '' mov p y, ?_, ?_, ?_⟩
  · rw [image_image]; exact (congrFun (hf p) y).symm
  · rw [image_image]; exact (congrFun (hg p) y).symm
  · rintro _ ⟨z, -, rfl⟩; exact ⟨z, rfl, rfl⟩

-- `LGame.hom_unique_apply`
theorem c3_136 : drop% LGame.hom_unique_apply 2 := fun f g hf hg x => homUnique f g hf hg x

-- `LGame.hom_unique_apply`
theorem c3_137 : drop% LGame.hom_unique_apply 3 := fun f g hf hg x => homUnique f g hf hg x

-- `LGame.hom_unique`
theorem c3_138 : drop% LGame.hom_unique 2 := fun f g hf hg => funext (homUnique f g hf hg)

-- `LGame.hom_unique`
theorem c3_139 : drop% LGame.hom_unique 3 := fun f g hf hg => funext (homUnique f g hf hg)

-- helper: the zero morphism
theorem homZero {α : Type} (p : Player) :
    moves p ∘ (fun _ : α => (0 : LGame)) = image (fun _ => (0 : LGame)) ∘ (ME p : α → Set α) := by
  funext a; simp [ME]

-- `LGame.hom_unique_apply`
theorem c3_140 : ¬ drop0% LGame.hom_unique_apply 6 := fun h =>
  oneNeZero (@h PUnit ME (fun _ => small_empty) (fun _ => small_empty) (fun _ => 1) (fun _ => 0) homZero PUnit.unit)

-- `LGame.hom_unique_apply`
theorem c3_141 : ¬ drop0% LGame.hom_unique_apply 7 := fun h =>
  oneNeZero (@h PUnit ME (fun _ => small_empty) (fun _ => small_empty) (fun _ => 0) (fun _ => 1) homZero PUnit.unit).symm

-- `LGame.hom_unique`
theorem c3_142 : ¬ drop0% LGame.hom_unique 6 := fun h =>
  oneNeZero (congrFun (@h PUnit ME (fun _ => small_empty) (fun _ => small_empty) (fun _ => 1) (fun _ => 0) homZero) PUnit.unit)

-- `LGame.hom_unique`
theorem c3_143 : ¬ drop0% LGame.hom_unique 7 := fun h =>
  oneNeZero (congrFun (@h PUnit ME (fun _ => small_empty) (fun _ => small_empty) (fun _ => 0) (fun _ => 1) homZero) PUnit.unit).symm

-- helper: models with every move set full, or one player full on PUnit, or on Option Type
def MU {γ : Type} : Player → γ → Set γ := fun _ _ => univ
def U1 : Player → PUnit → Set PUnit := Player.cases (fun _ => univ) (fun _ => ∅)
def U2 : Player → PUnit → Set PUnit := Player.cases (fun _ => ∅) (fun _ => univ)
def OL : Player → Option Type → Set (Option Type) := Player.cases (fun b => b.elim ∅ (fun _ => univ)) (fun _ => ∅)
def OR : Player → Option Type → Set (Option Type) := Player.cases (fun _ => ∅) (fun b => b.elim ∅ (fun _ => univ))

-- `LGame.corec_comp_hom`
theorem c3_150 : ¬ indepU% LGame.corec_comp_hom 4 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit ML U1 (fun _ => small_empty) (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => PUnit.unit) (by intro p; cases p <;> funext a <;> ext <;> simp [ML, U1]) PUnit)

-- `LGame.corec_comp_hom`
theorem c3_151 : ¬ indepU% LGame.corec_comp_hom 5 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit MR U2 (fun _ => small_empty) (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => PUnit.unit) (by intro p; cases p <;> funext a <;> ext <;> simp [MR, U2]) PUnit)

-- `LGame.corec_comp_hom`
theorem c3_152 : ¬ indepU% LGame.corec_comp_hom 6 [0, 0, 1] := fun h =>
  notSmallOptType (@h PUnit (Option Type) ME OL (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => small_empty) (fun _ => none) (by intro p; cases p <;> funext a <;> simp [ME, OL]) (some PUnit))

-- `LGame.corec_comp_hom`
theorem c3_153 : ¬ indepU% LGame.corec_comp_hom 7 [0, 0, 1] := fun h =>
  notSmallOptType (@h PUnit (Option Type) ME OR (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => small_empty) (fun _ => none) (by intro p; cases p <;> funext a <;> simp [ME, OR]) (some PUnit))

-- `LGame.corec_comp_hom_apply`
theorem c3_154 : ¬ indepU% LGame.corec_comp_hom_apply 4 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit ML U1 (fun _ => small_empty) (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => PUnit.unit) (by intro p; cases p <;> funext a <;> ext <;> simp [ML, U1]) PUnit PUnit)

-- `LGame.corec_comp_hom_apply`
theorem c3_155 : ¬ indepU% LGame.corec_comp_hom_apply 5 [0, 1, 0] := fun h =>
  notSmallType (@h Type PUnit MR U2 (fun _ => small_empty) (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => PUnit.unit) (by intro p; cases p <;> funext a <;> ext <;> simp [MR, U2]) PUnit PUnit)

-- `LGame.corec_comp_hom_apply`
theorem c3_156 : ¬ indepU% LGame.corec_comp_hom_apply 6 [0, 0, 1] := fun h =>
  notSmallOptType (@h PUnit (Option Type) ME OL (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => small_empty) (fun _ => none) (by intro p; cases p <;> funext a <;> simp [ME, OL]) PUnit.unit (some PUnit))

-- `LGame.corec_comp_hom_apply`
theorem c3_157 : ¬ indepU% LGame.corec_comp_hom_apply 7 [0, 0, 1] := fun h =>
  notSmallOptType (@h PUnit (Option Type) ME OR (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => small_empty) (fun _ => none) (by intro p; cases p <;> funext a <;> simp [ME, OR]) PUnit.unit (some PUnit))

-- `LGame.corec_comp_hom`
theorem c3_158 : ¬ drop0% LGame.corec_comp_hom 9 := fun h => by
  have := congrArg (moves left) (congrFun (@h PUnit PUnit ME U1 (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => inferInstance) (fun _ => inferInstance) id) PUnit.unit)
  simp only [Function.comp_apply, id] at this
  rw [moves_corec, moves_corec] at this
  simp [ME, U1] at this

-- `LGame.corec_comp_hom_apply`
theorem c3_159 : ¬ drop0% LGame.corec_comp_hom_apply 9 := fun h => by
  have := congrArg (moves left) (@h PUnit PUnit ME U1 (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => inferInstance) (fun _ => inferInstance) id PUnit.unit)
  rw [moves_corec, moves_corec] at this
  simp [ME, U1] at this

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.corec'_trans`
theorem c3_160 : ¬ indep0% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.corec'_trans 6 := fun h => by
  have hr := @h Bool ME (fun _ => small_empty) (fun _ => small_empty) true false ⟨false, Relation.ReflTransGen.refl⟩
  have := (Relation.reflTransGen_iff_eq (r := fun x y : Bool => x ∈ ME left y ∪ ME right y) (a := false)
    (fun b hb => by simp [ME] at hb)).1 hr
  exact absurd this (by decide)

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.corec'_aux`
theorem c3_161 : ¬ drop0% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.corec'_aux 6 := fun h => by
  obtain ⟨hr, -⟩ := (@h Bool ME (fun _ => small_empty) (fun _ => small_empty) true false
    (corec ME false)).2 rfl
  have := (Relation.reflTransGen_iff_eq (r := fun x y : Bool => x ∈ ME left y ∪ ME right y) (a := false)
    (fun b hb => by simp [ME] at hb)).1 hr
  exact absurd this (by decide)

-- `LGame.MulTy.map_erase`
theorem c3_162 : ¬ drop0% LGame.MulTy.map_erase 12 := fun h => by
  have := @h Bool PUnit PUnit PUnit (fun _ => PUnit.unit) id _ _ _ _ {(.left, true, PUnit.unit)}
    (.left, false, PUnit.unit)
  simp [LGame.MulTy.map] at this

-- `LGame.MulTy.movesSingle_comp_prodMap`
theorem c3_163 : ¬ drop0% LGame.MulTy.movesSingle_comp_prodMap 11 := fun h => by
  have := congrFun (@h .left PUnit PUnit PUnit PUnit ME MU MU MU id id
    (fun p => by funext; simp [MU])) (.left, PUnit.unit, PUnit.unit)
  simp [LGame.MulTy.movesSingle, LGame.MulTy.movesSet, ME, MU] at this

-- `LGame.MulTy.movesSingle_comp_prodMap`
theorem c3_164 : ¬ drop0% LGame.MulTy.movesSingle_comp_prodMap 12 := fun h => by
  have := congrFun (@h .left PUnit PUnit PUnit PUnit MU ME MU MU id id
    (fun p => by funext; simp [MU])) (.left, PUnit.unit, PUnit.unit)
  simp [LGame.MulTy.movesSingle, LGame.MulTy.movesSet, ME, MU] at this

-- `LGame.MulTy.moves_comp_map`
theorem c3_165 : ¬ drop0% LGame.MulTy.moves_comp_map 15 := fun h => by
  have := congrFun (@h .left PUnit PUnit PUnit PUnit ME MU MU MU id id _ _ _ _
    (fun p => by funext; simp [MU])) {(.left, PUnit.unit, PUnit.unit)}
  simp [LGame.MulTy.moves, LGame.MulTy.movesSingle, LGame.MulTy.movesSet, LGame.MulTy.map, ME, MU] at this

-- `LGame.MulTy.moves_comp_map`
theorem c3_166 : ¬ drop0% LGame.MulTy.moves_comp_map 16 := fun h => by
  have := congrFun (@h .left PUnit PUnit PUnit PUnit MU ME MU MU id id _ _ _ _
    (fun p => by funext; simp [MU])) {(.left, PUnit.unit, PUnit.unit)}
  simp [LGame.MulTy.moves, LGame.MulTy.movesSingle, LGame.MulTy.movesSet, LGame.MulTy.map, ME, MU] at this

-- helper: a movesSet with a large first (resp. second) coordinate is not small
theorem notSmallMovesSetA (m : Player → Type → Set Type) (q : Player) (hq : m q PUnit = univ) :
    ¬ Small.{0} ↑(LGame.MulTy.movesSet .left m (MU : Player → PUnit → Set PUnit) (.left, PUnit, PUnit.unit)) := by
  intro hs
  apply notSmallType
  have := small_image Prod.fst (LGame.MulTy.movesSet .left m (MU : Player → PUnit → Set PUnit) (.left, PUnit, PUnit.unit))
  refine small_subset (s := Prod.fst '' LGame.MulTy.movesSet .left m (MU : Player → PUnit → Set PUnit)
    (.left, PUnit, PUnit.unit)) (fun t _ => ⟨(t, PUnit.unit), ?_, rfl⟩)
  cases q <;> simp [LGame.MulTy.movesSet, MU, hq]

theorem notSmallMovesSetB (m : Player → Type → Set Type) (q : Player) (hq : m q PUnit = univ) :
    ¬ Small.{0} ↑(LGame.MulTy.movesSet .left (MU : Player → PUnit → Set PUnit) m (.left, PUnit.unit, PUnit)) := by
  intro hs
  apply notSmallType
  have := small_image Prod.snd (LGame.MulTy.movesSet .left (MU : Player → PUnit → Set PUnit) m (.left, PUnit.unit, PUnit))
  refine small_subset (s := Prod.snd '' LGame.MulTy.movesSet .left (MU : Player → PUnit → Set PUnit) m
    (.left, PUnit.unit, PUnit)) (fun t _ => ⟨(PUnit.unit, t), ?_, rfl⟩)
  cases q <;> simp [LGame.MulTy.movesSet, MU, hq]

-- helper: movesSet is small when movesSingle is (mulOption is injective in its last argument)
theorem smallSet_of_single.{u, v, w} {α : Type v} {β : Type w} [Nonempty α] [Nonempty β] (p : Player)
    (movα : Player → α → Set α) (movβ : Player → β → Set β) (x : Player × α × β)
    (h : Small.{u} ↑(LGame.MulTy.movesSingle p movα movβ x)) :
    Small.{u} ↑(LGame.MulTy.movesSet p movα movβ x) := by
  let e : LGame.MulTy α β → α × β := fun m => Classical.epsilon (fun z => (-x.1, z) ∈ m)
  have he : ∀ y, e (LGame.MulTy.mulOption x.1 x.2 y) = y := by
    intro y
    have hs := Classical.epsilon_spec (p := fun z => (-x.1, z) ∈ LGame.MulTy.mulOption x.1 x.2 y)
      ⟨y, by simp [LGame.MulTy.mulOption]⟩
    obtain ⟨q, a, b⟩ := x
    cases q <;> simpa [e, LGame.MulTy.mulOption] using hs
  have := small_image e (LGame.MulTy.movesSingle p movα movβ x)
  exact small_subset (s := e '' LGame.MulTy.movesSingle p movα movβ x)
    (fun y hy => ⟨_, mem_image_of_mem _ hy, he y⟩)

-- helper: movesSingle is small when the moves of the singleton are
theorem smallSingle_of_moves.{u, v, w} {α : Type v} {β : Type w} [DecidableEq α] [DecidableEq β] (p : Player)
    (movα : Player → α → Set α) (movβ : Player → β → Set β) (t : Player × α × β)
    (h : Small.{u} ↑(LGame.MulTy.moves p movα movβ {t})) :
    Small.{u} ↑(LGame.MulTy.movesSingle p movα movβ t) :=
  small_subset (s := LGame.MulTy.moves p movα movβ {t}) (fun m hm => by
    simp only [LGame.MulTy.moves, mem_iUnion, mem_image]
    exact ⟨t, Multiset.mem_singleton_self t, m, hm, by simp⟩)

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.MulTy.instSmallElemProdMovesSet`
theorem c3_170 : ¬ dropU% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.MulTy.instSmallElemProdMovesSet 5 [0, 1, 0] :=
  fun h => notSmallMovesSetA ML .left rfl
    (@h Type PUnit .left ML MU (fun _ => small_empty) (fun _ => inferInstance) (fun _ => inferInstance) (.left, PUnit, PUnit.unit))

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.MulTy.instSmallElemProdMovesSet`
theorem c3_171 : ¬ dropU% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.MulTy.instSmallElemProdMovesSet 7 [0, 0, 1] :=
  fun h => notSmallMovesSetB ML .left rfl
    (@h PUnit Type .left MU ML (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => small_empty) (.left, PUnit.unit, PUnit))

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.MulTy.instSmallElemProdMovesSet`
theorem c3_172 : ¬ dropU% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.MulTy.instSmallElemProdMovesSet 8 [0, 0, 1] :=
  fun h => notSmallMovesSetB MR .right rfl
    (@h PUnit Type .left MU MR (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => small_empty) (.left, PUnit.unit, PUnit))

-- `LGame.MulTy.instSmallElemMovesSingle`
theorem c3_173 : ¬ dropU% LGame.MulTy.instSmallElemMovesSingle 5 [0, 1, 0] :=
  fun h => notSmallMovesSetA ML .left rfl (smallSet_of_single _ _ _ _
    (@h Type PUnit .left ML MU (fun _ => small_empty) (fun _ => inferInstance) (fun _ => inferInstance) (.left, PUnit, PUnit.unit)))

-- `LGame.MulTy.instSmallElemMovesSingle`
theorem c3_174 : ¬ dropU% LGame.MulTy.instSmallElemMovesSingle 6 [0, 1, 0] :=
  fun h => notSmallMovesSetA MR .right rfl (smallSet_of_single _ _ _ _
    (@h Type PUnit .left MR MU (fun _ => small_empty) (fun _ => inferInstance) (fun _ => inferInstance) (.left, PUnit, PUnit.unit)))

-- `LGame.MulTy.instSmallElemMovesSingle`
theorem c3_175 : ¬ dropU% LGame.MulTy.instSmallElemMovesSingle 7 [0, 0, 1] :=
  fun h => notSmallMovesSetB ML .left rfl (smallSet_of_single _ _ _ _
    (@h PUnit Type .left MU ML (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => small_empty) (.left, PUnit.unit, PUnit)))

-- `LGame.MulTy.instSmallElemMovesSingle`
theorem c3_176 : ¬ dropU% LGame.MulTy.instSmallElemMovesSingle 8 [0, 0, 1] :=
  fun h => notSmallMovesSetB MR .right rfl (smallSet_of_single _ _ _ _
    (@h PUnit Type .left MU MR (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => small_empty) (.left, PUnit.unit, PUnit)))

-- `LGame.MulTy.instSmallElemMoves`
theorem c3_177 : ¬ dropU% LGame.MulTy.instSmallElemMoves 7 [0, 1, 0] :=
  fun h => notSmallMovesSetA ML .left rfl (smallSet_of_single _ _ _ _ (@smallSingle_of_moves _ _ (Classical.decEq _) inferInstance _ _ _ _ (
    @h Type PUnit .left ML MU (Classical.decEq _) inferInstance (fun _ => small_empty) (fun _ => inferInstance)
      (fun _ => inferInstance) {(.left, PUnit, PUnit.unit)})))

-- `LGame.MulTy.instSmallElemMoves`
theorem c3_178 : ¬ dropU% LGame.MulTy.instSmallElemMoves 8 [0, 1, 0] :=
  fun h => notSmallMovesSetA MR .right rfl (smallSet_of_single _ _ _ _ (@smallSingle_of_moves _ _ (Classical.decEq _) inferInstance _ _ _ _ (
    @h Type PUnit .left MR MU (Classical.decEq _) inferInstance (fun _ => small_empty) (fun _ => inferInstance)
      (fun _ => inferInstance) {(.left, PUnit, PUnit.unit)})))

-- `LGame.MulTy.instSmallElemMoves`
theorem c3_179 : ¬ dropU% LGame.MulTy.instSmallElemMoves 9 [0, 0, 1] :=
  fun h => notSmallMovesSetB ML .left rfl (smallSet_of_single _ _ _ _ (@smallSingle_of_moves _ _ inferInstance (Classical.decEq _) _ _ _ _ (
    @h PUnit Type .left MU ML inferInstance (Classical.decEq _) (fun _ => inferInstance) (fun _ => inferInstance)
      (fun _ => small_empty) {(.left, PUnit.unit, PUnit)})))

-- `LGame.MulTy.instSmallElemMoves`
theorem c3_180 : ¬ dropU% LGame.MulTy.instSmallElemMoves 10 [0, 0, 1] :=
  fun h => notSmallMovesSetB MR .right rfl (smallSet_of_single _ _ _ _ (@smallSingle_of_moves _ _ inferInstance (Classical.decEq _) _ _ _ _ (
    @h PUnit Type .left MU MR inferInstance (Classical.decEq _) (fun _ => inferInstance) (fun _ => inferInstance)
      (fun _ => small_empty) {(.left, PUnit.unit, PUnit)})))

-- helper: two coalgebra maps PUnit → GameFunctor PUnit (no moves / every move)
def gEmpty : PUnit.{2} → GameFunctor.{0} PUnit.{2} := fun _ => ⟨fun _ => ∅, fun _ => small_empty⟩
def gFull : PUnit.{2} → GameFunctor.{0} PUnit.{2} := fun _ => ⟨fun _ => univ, fun _ => inferInstance⟩

theorem corecNe : QPF.Cofix.corec gFull PUnit.unit ≠ QPF.Cofix.corec gEmpty PUnit.unit := fun e => by
  have := congrArg (fun z => (QPF.Cofix.dest z).1 left) e
  simp only [QPF.Cofix.dest_corec] at this
  change QPF.Cofix.corec gFull '' univ = QPF.Cofix.corec gEmpty '' ∅ at this
  simp at this

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.QPF.Cofix.unique`
theorem c3_190 : ¬ drop1% _private.CombinatorialGames.Game.Loopy.Basic.«0».QPF.Cofix.unique 6 := fun h =>
  corecNe (congrFun (@h GameFunctor _ PUnit gEmpty (QPF.Cofix.corec gFull) (QPF.Cofix.corec gEmpty)
    (funext fun x => QPF.Cofix.dest_corec gEmpty x)) PUnit.unit)

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.QPF.Cofix.unique`
theorem c3_191 : ¬ drop1% _private.CombinatorialGames.Game.Loopy.Basic.«0».QPF.Cofix.unique 7 := fun h =>
  corecNe (congrFun (@h GameFunctor _ PUnit gFull (QPF.Cofix.corec gFull) (QPF.Cofix.corec gEmpty)
    (funext fun x => QPF.Cofix.dest_corec gFull x)) PUnit.unit)

-- helper: 1 is not the corecursion of the empty model
theorem oneNeCorecME : (1 : LGame.{0}) ≠ corec (ME : Player → PUnit → Set PUnit) PUnit.unit := fun e => by
  have := congrArg (moves left) e
  rw [moves_corec] at this
  simp [ME] at this

section
attribute [local semireducible] LGame

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.unique`
theorem c3_192 : ¬ drop0% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.unique 7 := fun h => by
  refine oneNeCorecME (@h PUnit ME (fun _ => inferInstance) (fun _ => inferInstance) PUnit.unit (fun _ => 1)
    ((priv% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.corec') ME PUnit.unit) ?_
    ⟨PUnit.unit, Relation.ReflTransGen.refl⟩)
  funext s
  refine (QPF.Cofix.dest_corec _ _).trans ?_
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  congr 1
  funext t
  exact congrArg (QPF.Cofix.corec _) (Equiv.apply_symm_apply _ t).symm

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.unique`
theorem c3_193 : ¬ drop0% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.unique 8 := fun h => by
  refine oneNeCorecME (@h PUnit ME (fun _ => inferInstance) (fun _ => inferInstance) PUnit.unit
    ((priv% _private.CombinatorialGames.Game.Loopy.Basic.«0».LGame.corec') ME PUnit.unit) (fun _ => 1) ?_
    ⟨PUnit.unit, Relation.ReflTransGen.refl⟩).symm
  funext s
  refine (QPF.Cofix.dest_corec _ _).trans ?_
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  congr 1
  funext t
  exact congrArg (QPF.Cofix.corec _) (Equiv.apply_symm_apply _ t).symm

end
end W1c3
