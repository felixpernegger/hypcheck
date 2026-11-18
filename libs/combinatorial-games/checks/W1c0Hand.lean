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

namespace W1c0

section
open IGame Set

-- helper: omega as an IGame
noncomputable abbrev ωI : IGame.{0} := NatOrdinal.toIGame (NatOrdinal.of Ordinal.omega0)

-- helper: the universe of IGame is not small
theorem notSmallIGame.{u} : ¬ Small.{u} (Set.univ : Set IGame.{u}) := by
  rw [small_univ_iff]; intro h
  exact not_small_ordinal.{u} (small_of_injective (f := fun o : NatOrdinal.{u} => NatOrdinal.toIGame o)
    NatOrdinal.toIGame.injective)

-- helper: the universe of Game is not small
theorem notSmallGame.{u} : ¬ Small.{u} (Set.univ : Set Game.{u}) := by
  rw [small_univ_iff]; intro h
  exact not_small_ordinal.{u} (small_of_injective (f := fun o : NatOrdinal.{u} => NatOrdinal.toGame o)
    NatOrdinal.toGame.injective)

-- helper: a player-indexed pair of sets
def lr {α : Type 1} (s t : Set α) : Player → Set α := fun p => match p with | .left => s | .right => t

-- helper: singletons are small
theorem smallS {α : Type 1} (a : α) : Small.{0} ({a} : Set α) :=
  @Countable.toSmall _ (Set.countable_singleton a).to_subtype

-- helper: omega is not short
theorem notShortOmega : ¬ Short ωI := fun _ => lt_irrefl _ (Short.lt_omega0 ωI)

-- helper: 1 is not dicotic
theorem notDic1 : ¬ Dicotic (1 : IGame.{0}) := by rw [dicotic_def]; simp

-- helper: 1 is not impartial
theorem notImp1 : ¬ Impartial (1 : IGame.{0}) := fun h => absurd (impartial_def.1 h).1 (by game_cmp)

-- helper: the game with left option star only is not numeric
theorem notNumYS : ¬ Numeric !{{IGame.star} | ∅} := by
  intro hn
  exact not_numeric_star (Numeric.of_mem_moves (p := .left) (x := !{{IGame.star} | ∅}) (by simp))

-- helper: up is not numeric
theorem notNumUp : ¬ Numeric IGame.up := by
  intro hn
  exact not_numeric_star (Numeric.of_mem_moves (p := .right) (x := IGame.up) (by simp [IGame.up]))

-- helper: a game with infinitely many left moves
noncomputable def natG : IGame.{0} := !{Set.range (fun n : ℕ => (n : IGame.{0})) | ∅}

theorem natG_inf : ¬ (natG.moves .left).Finite := by
  rw [natG, moves_ofSets]
  refine Set.infinite_range_of_injective fun m n hmn => ?_
  have : ((m : Game.{0}) = n) := by simpa using congrArg Game.mk hmn
  exact_mod_cast this

end

section
open Set
-- `Game.ofSets_eq_mk'`
theorem b_1 : ¬ indep0% Game.ofSets_eq_mk' 1 := fun h => notSmallGame (@h (lr univ ∅) small_empty)

-- `Game.ofSets_eq_mk'`
theorem b_2 : ¬ indep0% Game.ofSets_eq_mk' 2 := fun h => notSmallGame (@h (lr ∅ univ) small_empty)

-- `Game.ofSets_eq_mk`
theorem b_3 : ¬ indep0% Game.ofSets_eq_mk 2 := fun h => notSmallGame (@h univ ∅ small_empty)

-- `Game.ofSets_eq_mk`
theorem b_4 : ¬ indep0% Game.ofSets_eq_mk 3 := fun h => notSmallGame (@h ∅ univ small_empty)

-- `Game.mk_ofSets'`
theorem b_5 : ¬ indep0% Game.mk_ofSets' 1 := fun h => notSmallIGame (@h (lr univ ∅) small_empty)

-- `Game.mk_ofSets`
theorem b_6 : ¬ indep0% Game.mk_ofSets 2 := fun h => notSmallIGame (@h univ ∅ small_empty)

-- `Game.mk_ofSets`
theorem b_7 : ¬ indep0% Game.mk_ofSets 3 := fun h => notSmallIGame (@h ∅ univ small_empty)

-- `Game.lf_ofSets_of_mem_left'`
theorem b_8 : ¬ indep0% Game.lf_ofSets_of_mem_left' 1 := fun h => notSmallGame (@h (lr univ ∅) small_empty 0 trivial)

-- `Game.lf_ofSets_of_mem_left'`
theorem b_9 : ¬ indep0% Game.lf_ofSets_of_mem_left' 2 := fun h => notSmallGame (@h (lr {0} univ) (smallS 0) 0 rfl)

-- `Game.ofSets_lf_of_mem_right'`
theorem b_10 : ¬ indep0% Game.ofSets_lf_of_mem_right' 1 := fun h => notSmallGame (@h (lr univ {0}) (smallS 0) 0 rfl)

-- `Game.ofSets_lf_of_mem_right'`
theorem b_11 : ¬ indep0% Game.ofSets_lf_of_mem_right' 2 := fun h => notSmallGame (@h (lr ∅ univ) small_empty 0 trivial)

-- `Game.lf_ofSets_of_mem_left`
theorem b_12 : ¬ indep0% Game.lf_ofSets_of_mem_left 3 := fun h => notSmallGame (@h {0} univ (smallS 0) 0 rfl)

-- `Game.ofSets_lf_of_mem_right`
theorem b_13 : ¬ indep0% Game.ofSets_lf_of_mem_right 2 := fun h => notSmallGame (@h univ {0} (smallS 0) 0 rfl)

-- `Game.ofSets_lf_of_mem_right`
theorem b_14 : ¬ indep0% Game.ofSets_lf_of_mem_right 3 := fun h => notSmallGame (@h ∅ univ small_empty 0 trivial)

-- `Game.ofSets_le_ofSets_iff'`
theorem b_15 : ¬ indep0% Game.ofSets_le_ofSets_iff' 2 := fun h => notSmallGame (@h (lr univ ∅) (fun _ => ∅) small_empty small_empty small_empty)

-- `Game.ofSets_le_ofSets_iff'`
theorem b_16 : ¬ indep0% Game.ofSets_le_ofSets_iff' 3 := fun h => notSmallGame (@h (lr ∅ univ) (fun _ => ∅) small_empty small_empty small_empty)

-- `Game.ofSets_le_ofSets_iff'`
theorem b_17 : ¬ indep0% Game.ofSets_le_ofSets_iff' 5 := fun h => notSmallGame (@h (fun _ => ∅) (lr ∅ univ) small_empty small_empty small_empty)

-- `Game.ofSets_lf_ofSets_iff'`
theorem b_18 : ¬ indep0% Game.ofSets_lf_ofSets_iff' 2 := fun h => notSmallGame (@h (lr univ ∅) (fun _ => ∅) small_empty small_empty small_empty)

-- `Game.ofSets_lf_ofSets_iff'`
theorem b_19 : ¬ indep0% Game.ofSets_lf_ofSets_iff' 3 := fun h => notSmallGame (@h (lr ∅ univ) (fun _ => ∅) small_empty small_empty small_empty)

-- `Game.ofSets_lf_ofSets_iff'`
theorem b_20 : ¬ indep0% Game.ofSets_lf_ofSets_iff' 4 := fun h => notSmallGame (@h (fun _ => ∅) (lr univ ∅) small_empty small_empty small_empty)

-- `Game.ofSets_lf_ofSets_iff'`
theorem b_21 : ¬ indep0% Game.ofSets_lf_ofSets_iff' 5 := fun h => notSmallGame (@h (fun _ => ∅) (lr ∅ univ) small_empty small_empty small_empty)

-- `Game.ofSets_le_ofSets_iff`
theorem b_22 : ¬ indep0% Game.ofSets_le_ofSets_iff 4 := fun h => notSmallGame (@h univ ∅ ∅ ∅ small_empty small_empty small_empty)

-- `Game.ofSets_le_ofSets_iff`
theorem b_23 : ¬ indep0% Game.ofSets_le_ofSets_iff 5 := fun h => notSmallGame (@h ∅ univ ∅ ∅ small_empty small_empty small_empty)

-- `Game.ofSets_le_ofSets_iff`
theorem b_24 : ¬ indep0% Game.ofSets_le_ofSets_iff 6 := fun h => notSmallGame (@h ∅ ∅ univ ∅ small_empty small_empty small_empty)

-- `Game.ofSets_le_ofSets_iff`
theorem b_25 : ¬ indep0% Game.ofSets_le_ofSets_iff 7 := fun h => notSmallGame (@h ∅ ∅ ∅ univ small_empty small_empty small_empty)

-- `Game.ofSets_lf_ofSets_iff`
theorem b_26 : ¬ indep0% Game.ofSets_lf_ofSets_iff 4 := fun h => notSmallGame (@h univ ∅ ∅ ∅ small_empty small_empty small_empty)

-- `Game.ofSets_lf_ofSets_iff`
theorem b_27 : ¬ indep0% Game.ofSets_lf_ofSets_iff 5 := fun h => notSmallGame (@h ∅ univ ∅ ∅ small_empty small_empty small_empty)

-- `Game.ofSets_lf_ofSets_iff`
theorem b_28 : ¬ indep0% Game.ofSets_lf_ofSets_iff 6 := fun h => notSmallGame (@h ∅ ∅ univ ∅ small_empty small_empty small_empty)

-- `Game.ofSets_lf_ofSets_iff`
theorem b_29 : ¬ indep0% Game.ofSets_lf_ofSets_iff 7 := fun h => notSmallGame (@h ∅ ∅ ∅ univ small_empty small_empty small_empty)

-- `IGame.birthday_ofSets`
theorem b_30 : ¬ indep0% IGame.birthday_ofSets 2 := fun h => notSmallIGame (@h univ ∅ small_empty)

-- `IGame.birthday_ofSets`
theorem b_31 : ¬ indep0% IGame.birthday_ofSets 3 := fun h => notSmallIGame (@h ∅ univ small_empty)

-- `IGame.birthday_ofSets'`
theorem b_32 : ¬ indep0% IGame.birthday_ofSets' 1 := fun h => notSmallIGame (@h (lr univ ∅) small_empty)

-- `IGame.birthday_ofSets'`
theorem b_33 : ¬ indep0% IGame.birthday_ofSets' 2 := fun h => notSmallIGame (@h (lr ∅ univ) small_empty)

-- `IGame.birthday_ofSets_const`
theorem b_34 : ¬ indep0% IGame.birthday_ofSets_const 1 := fun h => notSmallIGame (@h univ)

-- `Game.birthday_ofSets_le'`
theorem b_35 : ¬ indep0% Game.birthday_ofSets_le' 1 := fun h => notSmallGame (@h (lr univ ∅) small_empty)

-- `Game.birthday_ofSets_le`
theorem b_36 : ¬ indep0% Game.birthday_ofSets_le 2 := fun h => notSmallGame (@h univ ∅ small_empty)

-- `Game.birthday_ofSets_le`
theorem b_37 : ¬ indep0% Game.birthday_ofSets_le 3 := fun h => notSmallGame (@h ∅ univ small_empty)
end

section
open IGame Set


-- `Game.ind`
theorem m_1 : ¬ drop0% Game.ind 1 := fun h => @h (fun _ => False) 0

-- `Game.lf_ofSets_of_mem_left'`
theorem m_2 : ¬ drop0% Game.lf_ofSets_of_mem_left' 4 := fun h =>
  @h (fun _ => ∅) small_empty small_empty _ le_rfl

-- `Game.ofSets_lf_of_mem_right'`
theorem m_3 : ¬ drop0% Game.ofSets_lf_of_mem_right' 4 := fun h =>
  @h (fun _ => ∅) small_empty small_empty _ le_rfl

-- `Game.lf_ofSets_of_mem_left`
theorem m_4 : ¬ drop0% Game.lf_ofSets_of_mem_left 5 := fun h =>
  @h ∅ ∅ small_empty small_empty _ le_rfl

-- `Game.ofSets_lf_of_mem_right`
theorem m_5 : ¬ drop0% Game.ofSets_lf_of_mem_right 5 := fun h =>
  @h ∅ ∅ small_empty small_empty _ le_rfl

-- `IGame.Impartial.fuzzy_iff_add_fuzzy_zero`
theorem m_6 : drop% IGame.Impartial.fuzzy_iff_add_fuzzy_zero 2 := by
  intro x y hy
  rw [← add_fuzzy_add_iff_right (a := y)]
  exact AntisymmRel.incompRel_congr_right (Impartial.add_self_equiv y)

-- `IGame.Impartial.fuzzy_iff_add_fuzzy_zero`
theorem m_7 : drop% IGame.Impartial.fuzzy_iff_add_fuzzy_zero 3 := by
  intro x y hx
  rw [incompRel_comm, add_comm, ← add_fuzzy_add_iff_right (a := x)]
  exact AntisymmRel.incompRel_congr_right (Impartial.add_self_equiv x)

-- `_private.CombinatorialGames.Game.Birthday.0.ciSup_eq_bot`
theorem m_8 : ¬ ∀ {α : Type} {ι : Type} [ConditionallyCompleteLinearOrderBot α] {f : ι → α},
    ⨆ i, f i = ⊥ ↔ ∀ i, f i = ⊥ := fun h => by
  have := (@h ℕ ℕ _ id).1 (by
    rw [ciSup_of_not_bddAbove, csSup_empty]
    simp [Set.range_id]) 1
  simp at this

-- `IGame.equiv_ordinal_of_right_eq_empty`
theorem m_9 : ¬ drop0% IGame.equiv_ordinal_of_right_eq_empty 1 := fun h => by
  obtain ⟨o, ho⟩ := @h (-1)
  exact absurd ((NatOrdinal.toIGame_nonneg o).trans ho.2) (by game_cmp)

-- `IGame.equiv_neg_ordinal_of_left_eq_empty`
theorem m_10 : ¬ drop0% IGame.equiv_neg_ordinal_of_left_eq_empty 1 := fun h => by
  obtain ⟨o, ho⟩ := @h 1
  exact absurd (ho.1.trans (neg_le_zero.2 (NatOrdinal.toIGame_nonneg o))) (by game_cmp)

-- `IGame.Short.birthday_lt_omega0`
theorem m_11 : ¬ drop0% IGame.Short.birthday_lt_omega0 1 := fun h =>
  lt_irrefl (NatOrdinal.of.{0} Ordinal.omega0) (by simpa [birthday_toIGame] using h ωI)

-- `Game.confusionInterval_switch_of_numeric`
theorem m_12 : drop% Game.confusionInterval_switch_of_numeric 1 := by
  intro x hx
  by_cases h : 0 ≤ x
  · exact Game.confusionInterval_switch_of_numeric h
  · rw [Game.mk_eq (switch_equiv_zero h), Game.mk_zero, Game.confusionInterval_zero]
    symm; apply Set.Icc_eq_empty
    have : x < 0 := Numeric.lt_of_not_ge h
    have h2 : Surreal.mk x < 0 := by rw [← Surreal.mk_zero, Surreal.mk_lt_mk]; exact this
    intro h3
    exact absurd (h2.trans_le' (neg_le_self_iff.1 h3)) (lt_irrefl _)

-- `Game.confusionInterval_switch_of_numeric`
theorem m_13 : ¬ indep0% Game.confusionInterval_switch_of_numeric 2 := fun h =>
  notNumUp (@h IGame.up (by game_cmp))

-- `GameFunctor.ext`
theorem m_14 : ¬ drop0% GameFunctor.ext 3 := fun h => by
  have := congrArg (fun z : GameFunctor PUnit.{2} => (PUnit.unit ∈ z.1 .left))
    (@h PUnit.{2} ⟨fun _ => ∅, fun _ => small_empty⟩ ⟨fun _ => Set.univ, fun _ => inferInstance⟩)
  simp at this

end

section
open IGame Set

-- `IGame.Dicotic.of_mem_moves`
theorem c_1 : ¬ drop0% IGame.Dicotic.of_mem_moves 3 := fun h =>
  notDic1 (@h !{{1} | ∅} 1 .left (by simp))

-- `IGame.Dicotic.of_mem_moves`
theorem c_2 : ¬ drop0% IGame.Dicotic.of_mem_moves 4 := fun h => notDic1 (@h 0 1 .left Dicotic.zero)

-- `IGame.Dicotic.subposition`
theorem c_3 : ¬ drop0% IGame.Dicotic.subposition 2 := fun h =>
  notDic1 (@h !{{1} | ∅} 1 (Subposition.of_mem_moves (p := .left) (by simp)))

-- `IGame.Dicotic.subposition`
theorem c_4 : ¬ drop0% IGame.Dicotic.subposition 3 := fun h => notDic1 (@h 0 1 Dicotic.zero)

-- `IGame.Dicotic.wsubposition`
theorem c_5 : ¬ drop0% IGame.Dicotic.wsubposition 2 := fun h => notDic1 (@h 1 1 (Or.inl rfl))

-- `IGame.Dicotic.wsubposition`
theorem c_6 : ¬ drop0% IGame.Dicotic.wsubposition 3 := fun h => notDic1 (@h 0 1 Dicotic.zero)

-- `IGame.Dicotic.neg`
theorem c_7 : ¬ drop0% IGame.Dicotic.neg 1 := fun h => notDic1 (by simpa using h (-1))

-- `IGame.Dicotic.add`
theorem c_8 : ¬ drop0% IGame.Dicotic.add 2 := fun h => notDic1 (by simpa using @h 1 0 Dicotic.zero)

-- `IGame.Dicotic.add`
theorem c_9 : ¬ drop0% IGame.Dicotic.add 3 := fun h => notDic1 (by simpa using @h 0 1 Dicotic.zero)

-- `IGame.Dicotic.sub`
theorem c_10 : ¬ drop0% IGame.Dicotic.sub 2 := fun h => notDic1 (by simpa using @h 1 0 Dicotic.zero)

-- `IGame.Dicotic.sub`
theorem c_11 : ¬ drop0% IGame.Dicotic.sub 3 := fun h => notDic1 (by simpa using @h 0 1 Dicotic.zero)

-- `IGame.Dicotic.nsmul`
theorem c_12 : ¬ drop0% IGame.Dicotic.nsmul 2 := fun h => notDic1 (by simpa using h 1 1)

-- `IGame.Dicotic.zsmul`
theorem c_13 : ¬ drop0% IGame.Dicotic.zsmul 2 := fun h => notDic1 (by simpa using h 1 1)

-- `IGame.Impartial.of_mem_moves`
theorem c_14 : ¬ drop0% IGame.Impartial.of_mem_moves 3 := fun h =>
  notImp1 (@h .left !{{1} | ∅} 1 (by simp))

-- `IGame.Impartial.of_mem_moves`
theorem c_15 : ¬ drop0% IGame.Impartial.of_mem_moves 4 := fun h => notImp1 (@h .left 0 1 Impartial.zero)

-- `IGame.Impartial.subposition`
theorem c_16 : ¬ drop0% IGame.Impartial.subposition 2 := fun h =>
  notImp1 (@h !{{1} | ∅} 1 (Subposition.of_mem_moves (p := .left) (by simp)))

-- `IGame.Impartial.subposition`
theorem c_17 : ¬ drop0% IGame.Impartial.subposition 3 := fun h => notImp1 (@h 0 1 Impartial.zero)

-- `IGame.Impartial.wsubposition`
theorem c_18 : ¬ drop0% IGame.Impartial.wsubposition 3 := fun h => notImp1 (@h 0 1 Impartial.zero)

-- `IGame.Impartial.add`
theorem c_19 : ¬ drop0% IGame.Impartial.add 2 := fun h => notImp1 (by simpa using @h 1 0 Impartial.zero)

-- `IGame.Impartial.add`
theorem c_20 : ¬ drop0% IGame.Impartial.add 3 := fun h => notImp1 (by simpa using @h 0 1 Impartial.zero)

-- `IGame.Impartial.sub`
theorem c_21 : ¬ drop0% IGame.Impartial.sub 2 := fun h => notImp1 (by simpa using @h 1 0 Impartial.zero)

-- `not_equiv_iff_of_neg_equiv`
theorem c_22 : ¬ drop0% not_equiv_iff_of_neg_equiv 2 := fun h =>
  absurd ((@h 1 0 (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `not_equiv_iff_of_neg_equiv`
theorem c_23 : ¬ drop0% not_equiv_iff_of_neg_equiv 3 := fun h =>
  absurd ((@h 0 1 (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Impartial.not_equiv_iff`
theorem c_24 : ¬ drop0% IGame.Impartial.not_equiv_iff 2 := fun h =>
  absurd ((@h 1 0 Impartial.zero).1 (by game_cmp)) (by game_cmp)

-- `IGame.Impartial.not_equiv_iff`
theorem c_25 : ¬ drop0% IGame.Impartial.not_equiv_iff 3 := fun h =>
  absurd ((@h 0 1 Impartial.zero).1 (by game_cmp)) (by game_cmp)

-- `not_fuzzy_iff_of_neg_equiv`
theorem c_26 : ¬ drop0% not_fuzzy_iff_of_neg_equiv 2 := fun h =>
  absurd ((@h 1 0 (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `not_fuzzy_iff_of_neg_equiv`
theorem c_27 : ¬ drop0% not_fuzzy_iff_of_neg_equiv 3 := fun h =>
  absurd ((@h 0 1 (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Impartial.not_fuzzy_iff`
theorem c_28 : ¬ drop0% IGame.Impartial.not_fuzzy_iff 2 := fun h =>
  absurd ((@h 1 0 Impartial.zero).1 (by game_cmp)) (by game_cmp)

-- `IGame.Impartial.not_fuzzy_iff`
theorem c_29 : ¬ drop0% IGame.Impartial.not_fuzzy_iff 3 := fun h =>
  absurd ((@h 0 1 Impartial.zero).1 (by game_cmp)) (by game_cmp)

-- `lf_iff_fuzzy_of_neg_equiv`
theorem c_30 : ¬ drop0% lf_iff_fuzzy_of_neg_equiv 2 := fun h =>
  absurd ((@h (-1) 0 (by game_cmp)).1 (by game_cmp)) (by game_cmp)

-- `IGame.Impartial.lf_iff_fuzzy`
theorem c_31 : ¬ drop0% IGame.Impartial.lf_iff_fuzzy 2 := fun h =>
  absurd ((@h (-1) 0 Impartial.zero).1 (by game_cmp)) (by game_cmp)

-- `_private.CombinatorialGames.Game.Classes.0.IGame.Impartial.equiv_iff_forall_fuzzy'`
theorem c_32 : ¬ drop0% _private.CombinatorialGames.Game.Classes.«0».IGame.Impartial.equiv_iff_forall_fuzzy' 2 :=
  fun h => absurd ((@h (-1) 0 Impartial.zero).2 ⟨by simp, by simp⟩) (by game_cmp)

-- `_private.CombinatorialGames.Game.Classes.0.IGame.Impartial.equiv_iff_forall_fuzzy'`
theorem c_33 : ¬ drop0% _private.CombinatorialGames.Game.Classes.«0».IGame.Impartial.equiv_iff_forall_fuzzy' 3 :=
  fun h => absurd ((@h 0 1 Impartial.zero).2 ⟨by simp, by simp⟩) (by game_cmp)

-- `IGame.Impartial.fuzzy_zero_of_forall_exists`
theorem c_34 : ¬ drop0% IGame.Impartial.fuzzy_zero_of_forall_exists 5 := fun h =>
  absurd (@h (IGame.star + IGame.star) inferInstance .left IGame.star (by simp)) (by game_cmp)

-- `IGame.Numeric.left_lt_right`
theorem c_35 : ¬ drop0% IGame.Numeric.left_lt_right 3 := fun h =>
  lt_irrefl _ (@h IGame.star 0 0 (by simp) (by simp))

-- `IGame.Numeric.left_lt_right`
theorem c_36 : ¬ drop0% IGame.Numeric.left_lt_right 4 := fun h =>
  absurd (@h (-1) 1 0 inferInstance (by simp)) (by game_cmp)

-- `IGame.Numeric.of_mem_moves`
theorem c_37 : ¬ drop0% IGame.Numeric.of_mem_moves 3 := fun h =>
  not_numeric_star (@h !{{IGame.star} | ∅} IGame.star .left (by simp))

-- `IGame.Numeric.subposition`
theorem c_38 : ¬ drop0% IGame.Numeric.subposition 2 := fun h =>
  not_numeric_star (@h !{{IGame.star} | ∅} IGame.star (Subposition.of_mem_moves (p := .left) (by simp)))

-- `IGame.Numeric.subposition`
theorem c_39 : ¬ drop0% IGame.Numeric.subposition 3 := fun h =>
  not_numeric_star (@h 0 IGame.star Numeric.zero)

-- `IGame.Numeric.wsubposition`
theorem c_40 : ¬ drop0% IGame.Numeric.wsubposition 2 := fun h =>
  not_numeric_star (@h IGame.star IGame.star (Or.inl rfl))

-- `IGame.Numeric.wsubposition`
theorem c_41 : ¬ drop0% IGame.Numeric.wsubposition 3 := fun h =>
  not_numeric_star (@h 0 IGame.star Numeric.zero)

-- `IGame.Numeric.moves`
theorem c_42 : ¬ drop0% IGame.Numeric.moves 1 := fun h =>
  not_numeric_star (@h !{{IGame.star} | ∅} .left ⟨IGame.star, by simp⟩)

-- `IGame.Numeric.mk_of_lf`
theorem c_43 : ¬ drop0% IGame.Numeric.mk_of_lf 2 := fun h => notNumYS (@h _ (by simp))

-- `IGame.Numeric.le_iff_forall_lt`
theorem c_44 : ¬ drop0% IGame.Numeric.le_iff_forall_lt 2 := fun h =>
  absurd (((@h !{{IGame.star} | ∅} 0 Numeric.zero).1 (by game_cmp)).1 IGame.star (by simp)) (by game_cmp)

-- `IGame.Short.mk`
theorem c_45 : ¬ drop0% IGame.Short.mk 1 := fun h => notShortOmega h

-- `IGame.Short.finite_moves`
theorem c_46 : ¬ drop0% IGame.Short.finite_moves 2 := fun h => natG_inf (h .left natG)

-- `IGame.Short.instFiniteElemMoves`
theorem c_47 : ¬ drop0% IGame.Short.instFiniteElemMoves 2 := fun h =>
  natG_inf (@Set.toFinite _ _ (h .left natG))

-- `IGame.Short.of_mem_moves`
theorem c_48 : ¬ drop0% IGame.Short.of_mem_moves 2 := fun h =>
  notShortOmega (@h !{{ωI} | ∅} ωI .left (by simp))

-- `IGame.Short.of_mem_moves`
theorem c_49 : ¬ drop0% IGame.Short.of_mem_moves 4 := fun h => notShortOmega (@h 0 ωI Short.zero .left)

-- `IGame.Short.subposition`
theorem c_50 : ¬ drop0% IGame.Short.subposition 2 := fun h =>
  notShortOmega (@h !{{ωI} | ∅} ωI (Subposition.of_mem_moves (p := .left) (by simp)))

-- `IGame.Short.subposition`
theorem c_51 : ¬ drop0% IGame.Short.subposition 3 := fun h => notShortOmega (@h 0 ωI Short.zero)

-- `IGame.Short.wsubposition`
theorem c_52 : ¬ drop0% IGame.Short.wsubposition 2 := fun h =>
  not_numeric_star (@h IGame.star IGame.star (Or.inl rfl))

-- `IGame.Short.wsubposition`
theorem c_53 : ¬ drop0% IGame.Short.wsubposition 3 := fun h =>
  not_numeric_star (@h 0 IGame.star Numeric.zero)

-- `IGame.Short.finite_setOfPred_subposition`
theorem c_54 : ¬ drop0% IGame.Short.finite_setOfPred_subposition 1 := fun h =>
  natG_inf ((h natG).subset fun _ hy => Subposition.of_mem_moves hy)

-- `IGame.Short.instFiniteElemOfPredSubposition`
theorem c_55 : ¬ drop0% IGame.Short.instFiniteElemOfPredSubposition 1 := fun h =>
  natG_inf ((@Set.toFinite _ _ (h natG)).subset fun _ hy => Subposition.of_mem_moves hy)

-- `IGame.Short.neg`
theorem c_56 : ¬ drop0% IGame.Short.neg 1 := fun h => notShortOmega (by simpa using h (-ωI))

-- `IGame.Short.add`
theorem c_57 : ¬ drop0% IGame.Short.add 2 := fun h => notShortOmega (by simpa using @h ωI 0 Short.zero)

-- `IGame.Short.add`
theorem c_58 : ¬ drop0% IGame.Short.add 3 := fun h => notShortOmega (by simpa using @h 0 ωI Short.zero)

-- `IGame.Short.sub`
theorem c_59 : ¬ drop0% IGame.Short.sub 2 := fun h => notShortOmega (by simpa using @h ωI 0 Short.zero)

-- `IGame.Short.sub`
theorem c_60 : ¬ drop0% IGame.Short.sub 3 := fun h =>
  notShortOmega (by simpa [Short.neg_iff] using @h 0 ωI Short.zero)

-- `IGame.Short.mul`
theorem c_61 : ¬ drop0% IGame.Short.mul 2 := fun h => notShortOmega (by simpa using @h ωI 1 Short.one)

-- `IGame.Short.mul`
theorem c_62 : ¬ drop0% IGame.Short.mul 3 := fun h => notShortOmega (by simpa using @h 1 ωI Short.one)

-- `IGame.Short.mulOption`
theorem c_63 : ¬ drop0% IGame.Short.mulOption 4 := fun h =>
  notShortOmega (by simpa [mulOption] using @h ωI 0 0 1 Short.zero Short.zero Short.one)

-- `IGame.Short.mulOption`
theorem c_64 : ¬ drop0% IGame.Short.mulOption 5 := fun h =>
  notShortOmega (by simpa [mulOption] using @h 0 ωI 1 0 Short.zero Short.one Short.zero)

-- `IGame.Short.mulOption`
theorem c_65 : ¬ drop0% IGame.Short.mulOption 6 := fun h =>
  notShortOmega (by simpa [mulOption] using @h 0 1 ωI 0 Short.zero Short.one Short.zero)

-- `IGame.Short.mulOption`
theorem c_66 : ¬ drop0% IGame.Short.mulOption 7 := fun h =>
  notShortOmega (by simpa [mulOption] using @h 1 0 0 ωI Short.one Short.zero Short.zero)

end

section
open IGame Set Nimber

-- helper: the left moves of undominate natG are all dominated
theorem undomNatG_left : (undominate natG).moves .left = ∅ := by
  rw [moves_left_undominate, Set.eq_empty_iff_forall_notMem]
  rintro _ ⟨⟨y, hy, rfl⟩, h⟩
  rw [natG, moves_ofSets] at hy h
  obtain ⟨n, rfl⟩ := hy
  apply h ((n + 1 : ℕ) : IGame) ⟨n + 1, rfl⟩
  rw [(undominate_equiv _).lt_congr_left]
  exact IGame.natCast_lt.2 (Nat.lt_succ_self n)

theorem undomNatG_right : (undominate natG).moves .right = ∅ := by
  rw [moves_right_undominate, natG, moves_ofSets]; simp

theorem undomNatG : undominate natG = 0 :=
  IGame.ext fun p => by
    cases p
    · rw [undomNatG_left]; simp
    · rw [undomNatG_right]; simp

theorem natG_not_le : ¬ natG ≤ 0 := fun h =>
  (le_iff_forall_lf.1 h).1 1 (by rw [natG, moves_ofSets]; exact ⟨1, Nat.cast_one⟩) (by game_cmp)

-- `_private.CombinatorialGames.Game.Canonical.0.IGame.le_undominate`
theorem k_1 : ¬ drop0% _private.CombinatorialGames.Game.Canonical.«0».IGame.le_undominate 1 := fun h =>
  natG_not_le (undomNatG ▸ h natG)

-- `IGame.undominate_equiv`
theorem k_2 : ¬ drop0% IGame.undominate_equiv 1 := fun h =>
  natG_not_le (undomNatG ▸ (h natG).2)

-- helper: finite nim heaps are short
theorem nimS (n : ℕ) : Short (nim (∗(n : Ordinal.{0}))) := by
  rw [short_iff_birthday_finite, birthday_nim]; simpa using Ordinal.natCast_lt_omega0 n

-- helper: a game whose left moves are all finite nim heaps
noncomputable def nimG : IGame.{0} := !{Set.range (fun n : ℕ => nim (∗(n : Ordinal.{0}))) | ∅}

-- `IGame.instShortUndominate`
theorem k_3 : ¬ drop0% IGame.instShortUndominate 1 := fun h => by
  have hf := @Short.finite_moves .left (undominate nimG) (@h nimG)
  rw [moves_left_undominate] at hf
  refine Set.infinite_range_of_injective
    (f := fun n : ℕ => undominate (nim (∗(n : Ordinal.{0})))) ?_ (hf.subset ?_)
  · intro m n hmn
    have := nimS m; have := nimS n
    have e : nim (∗(m : Ordinal.{0})) ≈ nim (∗(n : Ordinal.{0})) :=
      ((undominate_equiv _).symm.trans (AntisymmRel.of_eq hmn)).trans (undominate_equiv _)
    simpa using nim_equiv_iff.1 e
  · rintro _ ⟨n, rfl⟩
    rw [nimG, moves_ofSets]
    refine ⟨⟨_, ⟨n, rfl⟩, rfl⟩, ?_⟩
    rintro z ⟨m, rfl⟩ hlt
    have := nimS n
    rw [(undominate_equiv _).lt_congr_left] at hlt
    exact Impartial.not_lt _ _ hlt

end

end W1c0
