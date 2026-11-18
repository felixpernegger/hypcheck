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

namespace Probe1

section
open IGame Nimber

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

-- `Game.mk_ofSets'`
theorem p1_1 : ¬ indep0% Game.mk_ofSets' 2 := fun h =>
  notSmallIGame (@h (fun p => match p with | .left => ∅ | .right => Set.univ)
    (small_empty (α := IGame.{0})))

-- `Game.lf_ofSets_of_mem_left`
theorem p1_2 : ¬ indep0% Game.lf_ofSets_of_mem_left 2 := fun h =>
  notSmallGame (@h _ (∅ : Set Game.{0}) small_empty (0 : Game.{0}) trivial)

-- `Game.ofSets_le_ofSets_iff'`
theorem p1_3 : ¬ indep0% Game.ofSets_le_ofSets_iff' 4 := fun h =>
  notSmallGame (@h (fun _ => ∅) (fun p => match p with | .left => Set.univ | .right => ∅)
    (small_empty (α := Game.{0})) (small_empty (α := Game.{0}))
    (small_empty (α := Game.{0})))

-- `Game.birthday_ofSets_le'`
theorem p1_4 : ¬ indep0% Game.birthday_ofSets_le' 2 := fun h =>
  notSmallGame (@h (fun p => match p with | .left => ∅ | .right => Set.univ)
    (small_empty (α := Game.{0})))

-- `IGame.ofSets_add_ofSets'`
theorem p1_5 : ¬ indep0% IGame.ofSets_add_ofSets' 2 := fun h =>
  notSmallIGame (@h (fun p => match p with | .left => Set.univ | .right => ∅) (fun _ => ∅)
    (small_empty (α := IGame.{0})) (small_empty (α := IGame.{0}))
    (small_empty (α := IGame.{0})))

-- `IGame.Impartial.wsubposition`
theorem p1_6 : ¬ drop0% IGame.Impartial.wsubposition 2 := fun h => by
  have h1 := impartial_def.1 (@h 1 1 (Or.inl rfl))
  exact absurd h1.1 (by game_cmp)

-- `IGame.Impartial.sub`
theorem p1_7 : ¬ drop0% IGame.Impartial.sub 3 := fun h => by
  have h1 := impartial_def.1 (h 0 1)
  exact absurd h1.1 (by game_cmp)

-- `IGame.Subposition.trans`
theorem p1_8 : ¬ drop0% IGame.Subposition.trans 3 := fun h =>
  Subposition.irrefl 1 (@h 1 0 1 (Subposition.of_mem_moves (p := .left) (by simp)))

-- `IGame.WSubposition.trans`
theorem p1_9 : ¬ drop0% IGame.WSubposition.trans 3 := fun h =>
  not_wsubposition_of_subposition (x := 0) (y := 1) (Subposition.of_mem_moves (p := .left) (by simp))
    (@h 1 0 0 (Or.inl rfl))

-- `IGame.subposition_of_wsubposition_of_ne`
theorem p1_10 : ¬ drop0% IGame.subposition_of_wsubposition_of_ne 2 := fun h =>
  Subposition.irrefl 0 (Subposition.trans (Subposition.of_mem_moves (p := .left) (by simp))
    (@h 1 0 one_ne_zero))

-- `IGame.Short.lt_omega0`
theorem p1_11 : ¬ drop0% IGame.Short.lt_omega0 1 := fun h => lt_irrefl _ (h _)

end

section
open IGame Nimber

-- helper: 3 is not a group
theorem notGroup3 : ¬ IsGroup (∗3) := by
  intro h
  have e : ∗2 + 1 = ∗3 := by
    have := IsGroup.two.add_eq_of_lt (y := 1) (by simp)
    rw [← this]; simp; norm_num
  have := h.add_lt (y := ∗2) (z := 1) (by rw [of.lt_iff_lt]; exact_mod_cast (show (2:ℕ) < 3 by decide)) (by simp)
  rw [e] at this; exact lt_irrefl _ this

-- helper: 1 is not small
theorem notSmallOne : ¬ IGame.Small 1 := fun h =>
  absurd (h.le_numeric_of_pos (y := ½) (by game_cmp)) (by game_cmp)

-- `IGame.Small.of_equiv`
theorem p1_12 : ¬ drop0% IGame.Small.of_equiv 2 := fun h => notSmallOne (@h 0 1 IGame.Small.zero)

-- `IGame.Small.sub`
theorem p1_13 : ¬ drop0% IGame.Small.sub 2 := fun h =>
  absurd ((h 1 0).le_numeric_of_pos (y := ½) (by game_cmp)) (by game_cmp)

-- `IGame.Small.sub`
theorem p1_14 : ¬ drop0% IGame.Small.sub 3 := fun h =>
  absurd ((h 0 1).numeric_le_of_neg (y := -½) (by game_cmp)) (by game_cmp)

-- `IGame.Small.of_infinitesimal`
theorem p1_15 : ¬ drop0% IGame.Small.of_infinitesimal 2 := fun h => by
  have hs := @h (-1) inferInstance (fun y hy => by
    have : (0 : IGame.{0}) < y := by simpa using hy
    exact le_of_lt (lt_trans (by game_cmp) this))
  exact absurd (hs.numeric_le_of_neg (y := -½) (by game_cmp)) (by game_cmp)

-- `IGame.switch_fuzzy_self`
theorem p1_16 : ¬ drop0% IGame.switch_fuzzy_self 1 := fun h =>
  switch_fuzzy_self_iff.1 (@h (-1)) (by game_cmp)

-- `_private.CombinatorialGames.Game.Impartial.Grundy.0.IGame.Impartial.of_grundyAux_left_eq_grundyAux_right'`
theorem p1_17 : ¬ drop0% _private.CombinatorialGames.Game.Impartial.Grundy.«0».IGame.Impartial.of_grundyAux_left_eq_grundyAux_right' 2 := fun h => by
  have := @h 1 (fun p y hy => by cases p <;> simp at hy <;> subst hy <;> infer_instance)
  rw [grundyAux_def] at this
  simp at this
  exact absurd this (by game_cmp)

-- `Nimber.apply_omega0_of_isNormal`
theorem p1_18 : ¬ drop0% Nimber.apply_omega0_of_isNormal 1 := fun h => by
  have h2 := @h (fun o => if o = Ordinal.omega0 then 1 else 0)
  have e : ∀ n : ℕ, (if (n : Ordinal.{0}) = Ordinal.omega0 then (1 : Nimber.{0}) else 0) = 0 :=
    fun n => ite_eq_right_iff.2 fun h => absurd h (Ordinal.natCast_lt_omega0 n).ne
  simp only [e, ciSup_const] at h2
  simp at h2

-- `Nimber.IsAlgClosed.iSup`
theorem p1_19 : ¬ drop0% Nimber.IsAlgClosed.iSup 3 := fun h => by
  have := @h True ⟨trivial⟩ (fun _ => ∗3) ⟨∗3, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  simp only [ciSup_const] at this
  exact notGroup3 this.toIsGroup

-- `Nimber.IsGroup.mul_le_of_forall_lt`
theorem p1_20 : ¬ drop0% Nimber.IsGroup.mul_le_of_forall_lt 4 := fun h => by
  have := @h 1 IsGroup.one 1 (∗2) (fun r hr => by simp_all) (fun r hr l _ => by simp_all)
  simp at this

-- `Nimber.IsGroup.mul_le_of_forall_lt`
theorem p1_21 : ¬ drop0% Nimber.IsGroup.mul_le_of_forall_lt 5 := fun h => by
  have := @h 1 IsGroup.one (∗2) 1 (fun l hl => by simp_all) (fun r _ l hl => by simp_all)
  simp at this

-- `Nimber.IsField.sSup`
theorem p1_22 : ¬ drop0% Nimber.IsField.sSup 1 := fun h => by
  have := @h {∗3} (Set.singleton_nonempty _) (bddAbove_singleton)
  rw [csSup_singleton] at this
  exact notGroup3 this.toIsGroup

-- `Nimber.IsField.leadingCoeff_embed`
theorem p1_23 : ¬ indep0% Nimber.IsField.leadingCoeff_embed 3 := fun h => by
  have := @h (∗2) IsField.two (Polynomial.C (∗2)) 0
  simp at this

-- `Nimber.IsField.natDegree_leastNoRoots_ne_four`
theorem p1_24 : ¬ indep0% Nimber.IsField.natDegree_leastNoRoots_ne_four 2 := fun h => by
  have hc := IsAlgClosed.omega (x := 1) one_ne_zero
  exact @h _ hc.toIsField hc.leastNoRoots_eq_top

-- `SignExpansion.Small.apply_length`
theorem p1_25 : ¬ indep0% SignExpansion.Small.apply_length 1 := fun h =>
  (SignExpansion.small_iff_length_ne_top.1 (h ⊤)) SignExpansion.length_top

-- `SignExpansion.succ_apply_of_eq`
-- removable: the hypothesis follows from the length being an ordinal
theorem p1_26 : indep% SignExpansion.succ_apply_of_eq 1 := fun ho =>
  SignExpansion.small_iff_length_ne_top.2 (ho ▸ WithTop.coe_ne_top)

-- `GameGraph.Poset.impartial_toIGame`
theorem p1_27 : ¬ indep0% GameGraph.Poset.impartial_toIGame 2 := fun h => by
  have := @h ℤ inferInstance ∅
  obtain ⟨m, -, hm⟩ := (wellFounded_lt (α := ℤ)).has_min Set.univ ⟨0, trivial⟩
  exact hm (m - 1) trivial (by omega)

-- helper: the trivial successor order on Unit
@[reducible] def unitSucc : SuccOrder Unit where
  succ := id
  le_succ _ := le_rfl
  max_of_succ_le _ _ _ := le_rfl
  succ_le_of_lt h := absurd h (lt_irrefl _)

-- `IsClub.exists_between_closure`
theorem p1_28 : ¬ drop0% IsClub.exists_between_closure 3 := fun h => by
  obtain ⟨l, -, -, hl⟩ := @h Unit inferInstance inferInstance unitSucc Set.univ
    ⟨fun _ _ _ _ _ _ => trivial, fun _ => ⟨(), trivial, le_rfl⟩⟩ () ⟨(), trivial, le_rfl⟩ id (fun _ => le_rfl)
    (fun _ => trivial)
  exact lt_irrefl _ hl

end

section
open IGame Nimber Polynomial

-- helper: the universe of Type is not small
theorem notSmallType : ¬ Small.{0} (Set.univ : Set Type) := by
  rw [small_univ_iff]; exact not_small_type.{0, 0}

-- `GameGraph.moves_toLGame`
theorem p1_29 : ¬ ∀ {α : Type 1} (c : GameGraph.{1} α) (p : Player)
    [Hr : ∀ a, Small.{0} ↑(c.moves .right a)] (a a' : α), Small.{0} ↑(c.moves .left a') := fun h =>
  notSmallType (@h Type ⟨fun p _ => match p with | .left => Set.univ | .right => ∅⟩ .left
    (fun _ => small_empty) Unit Unit)

-- `LGame.moves_corec`
theorem p1_30 : ¬ ∀ {α : Type 1} (p : Player) (mov : Player → α → Set α)
    [∀ a, Small.{0} ↑(mov .left a)] (init a : α), Small.{0} ↑(mov .right a) := fun h =>
  notSmallType (@h Type .left (fun p _ => match p with | .left => ∅ | .right => Set.univ)
    (fun _ => small_empty) Unit Unit)

-- `LGame.corec_sub_corec`
theorem p1_31 : ¬ ∀ {α : Type 1} {β : Type} {movα : Player → α → Set α} {movβ : Player → β → Set β}
    [∀ x, Small.{0} ↑(movα .right x)] [∀ x, Small.{0} ↑(movβ .left x)]
    [∀ x, Small.{0} ↑(movβ .right x)] (initα : α) (initβ : β) (x : α), Small.{0} ↑(movα .left x) :=
  fun h => notSmallType (@h Type Unit (fun p _ => match p with | .left => Set.univ | .right => ∅)
    (fun _ _ => ∅) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) Unit () Unit)

-- `LGame.MulTy.corec_neg`
theorem p1_32 : ¬ ∀ {α : Type} {β : Type 1} (movα : Player → α → Set α) (movβ : Player → β → Set β)
    [Hα : DecidableEq α] [Hβ : DecidableEq β]
    [∀ x, Small.{0} ↑(movα .left x)] [∀ x, Small.{0} ↑(movα .right x)]
    [∀ x, Small.{0} ↑(movβ .right x)] (init : LGame.MulTy α β) (x : β), Small.{0} ↑(movβ .left x) :=
  fun h => notSmallType (@h Unit Type (fun _ _ => ∅) (fun p _ => match p with | .left => Set.univ | .right => ∅)
    inferInstance (Classical.decEq _) (fun _ => small_empty) (fun _ => small_empty) (fun _ => small_empty) 0 Unit)

-- `_private.CombinatorialGames.Game.Loopy.Basic.0.LGame.MulTy.instSmallElemProdMovesSet`
theorem p1_33 : ¬ ∀ {α : Type 1} {β : Type} (p : Player) (movα : Player → α → Set α) (movβ : Player → β → Set β)
    [∀ x, Small.{0} ↑(movα .left x)] [∀ x, Small.{0} ↑(movβ .left x)] [∀ x, Small.{0} ↑(movβ .right x)]
    (x : Player × α × β), Small.{0} ↑(LGame.MulTy.movesSet p movα movβ x) := fun h => by
  let mα : Player → Type → Set Type := fun p _ => match p with | .left => ∅ | .right => Set.univ
  let mβ : Player → Unit → Set Unit := fun _ _ => Set.univ
  have hs : Small.{0} ↑(LGame.MulTy.movesSet .left mα mβ (.left, Unit, ())) :=
    @h Type Unit .left mα mβ (fun _ => small_empty) (fun _ => inferInstance) (fun _ => inferInstance)
      (.left, Unit, ())
  have h2 : Small.{0} ↑(Prod.fst '' LGame.MulTy.movesSet .left mα mβ (.left, Unit, ())) := small_image _ _
  apply notSmallType
  refine small_subset (s := Prod.fst '' LGame.MulTy.movesSet .left mα mβ (.left, Unit, ()))
    (fun t _ => ⟨(t, ()), ?_, rfl⟩)
  simp [LGame.MulTy.movesSet, mα, mβ]

-- `LGame.stoppingTime_induction`
theorem p1_34 : ¬ drop0% LGame.stoppingTime_induction 2 := fun h => by
  have := h .left (fun q _ => if q = .left then 0 else ⊤) (fun x => by simp)
  have h2 := this .left 0
  rw [LGame.stoppingTime_of_eq rfl] at h2
  simp at h2

-- `Nimber.IsRing.eval_eq_of_lt`
theorem p1_35 : ¬ drop0% Nimber.IsRing.eval_eq_of_lt 6 := fun h => by
  obtain ⟨x, hc⟩ : ∃ x, IsAlgClosed x := ⟨_, IsAlgClosed.omega (x := 1) one_ne_zero⟩
  have := @h 2 _ hc.toIsRing (by rw [hc.leastNoRoots_eq_top]; exact le_top) (X + C x)
    (by rw [degree_X_add_C]; norm_num)
  simp [oeval, List.range_succ, coeff_X, coeff_C] at this
  have h' := congrArg val this
  simp at h'
  have h0 : val x = 0 := by have := h'.symm; rwa [_root_.add_eq_zero, and_self] at this
  exact hc.ne_zero (by simpa using congrArg of h0)

-- `Nimber.IsRing.pow_degree_leastNoRoots`
theorem p1_36 : ¬ drop0% Nimber.IsRing.pow_degree_leastNoRoots 4 := fun h => by
  have ht : leastNoRoots (∗2) ≠ ⊤ := fun e =>
    absurd ((isAlgClosed_iff_leastNoRoots_eq_top IsRing.two).2 e).omega0_le
      (by rw [of.le_iff_le]; exact not_le.2 (by simpa using Ordinal.natCast_lt_omega0 2))
  have := (@h (∗2) IsRing.two ht 0)
  simp at this
  exact lt_irrefl _ this.one_lt

-- `Nimber.exists_isRing_between'`
theorem p1_37 : ¬ drop0% Nimber.exists_isRing_between' 1 := fun h => by
  obtain ⟨l, hl, hle, -⟩ := @h 0
  exact absurd (hl.one_lt.trans_le hle) (by simp)

-- helper: ∗2 < ∗3
theorem lt23 : (∗2 : Nimber) < ∗3 := by rw [of.lt_iff_lt]; exact_mod_cast (show (2:ℕ) < 3 by decide)

-- helper: constant polynomials with small coefficient
theorem coeffC_lt (c x : Nimber) (k : ℕ) (hc : c < x) : (C c).coeff k < x := by
  rw [coeff_C]; split_ifs
  · exact hc
  · exact lt_of_le_of_lt _root_.zero_le hc

-- helper: ∗2 + 1 = ∗3
theorem two_add_one : ∗2 + 1 = ∗3 := by
  have := IsGroup.two.add_eq_of_lt (y := 1) (by simp)
  rw [← this]; simp; norm_num

-- `Nimber.IsRing.eval_lt`
theorem p1_38 : ¬ drop0% Nimber.IsRing.eval_lt 2 := fun h => by
  have := @h (∗3) 1 (X + C (∗2)) (fun k => by
    rcases k with _ | _ | k <;> simp [coeff_X, coeff_C] <;> simpa using lt23) (by simp)
  simp at this
  rw [add_comm, two_add_one] at this; exact lt_irrefl _ this

-- `Nimber.IsGroup.coeff_sum_lt`
theorem p1_39 : ¬ drop0% Nimber.IsGroup.coeff_sum_lt 4 := fun h => by
  have := @h (∗3) (Fin 2) ![C 1, C (∗2)] Finset.univ (fun y _ k => by fin_cases y <;> exact coeffC_lt _ _ _ (by simpa using lt23)) 0
  simp [Fin.sum_univ_two] at this
  rw [add_comm, two_add_one] at this; exact lt_irrefl _ this

-- `Nimber.IsRing.leastNoRoots_eq_of_not_isField`
theorem p1_40 : ¬ drop0% Nimber.IsRing.leastNoRoots_eq_of_not_isField 2 := fun h => by
  have hc := IsAlgClosed.omega (x := 1) one_ne_zero
  have := @h _ hc.toIsRing
  rw [hc.leastNoRoots_eq_top] at this
  exact WithTop.top_ne_coe this

-- `SignExpansion.ceil_apply_of_lt_sInf`
theorem p1_41 : ¬ drop0% SignExpansion.ceil_apply_of_lt_sInf 2 := fun h => by
  have h0 := @h (fun o => if o = 0 then 0 else 1) 0
  have h1 := @h (fun o => if o = 0 then 0 else 1) 1
  simp at h0 h1
  have := SignExpansion.apply_eq_zero_of_le (o := 0) (o' := 1) (by simp) h0
  rw [h1] at this; exact absurd this (by decide)

-- `SignExpansion.floor_lt_ceil_of_not_isUpperSet`
theorem p1_42 : ¬ drop0% SignExpansion.floor_lt_ceil_of_not_isUpperSet 1 := fun h => by
  have := @h ⇑(⊤ : SignExpansion)
  have hu := SignExpansion.isUpperSet_preimage_singleton_zero ⊤
  rw [SignExpansion.ceil_of_isUpperSet hu, SignExpansion.floor_of_isUpperSet hu] at this
  exact lt_irrefl _ this

-- `Nimber.IsField.mul_eq_of_lt'`
theorem p1_43 : ¬ drop0% Nimber.IsField.mul_eq_of_lt' 5 := fun h => by
  have hw : ((∗2 : Nimber)⁻¹) < ∗Ordinal.omega0 := IsField.omega0.inv_lt
    (by rw [of.lt_iff_lt]; simpa using Ordinal.natCast_lt_omega0 2)
  have := @h 2 Ordinal.omega0 (val (∗2 : Nimber)⁻¹) IsRing.two IsField.omega0 (by simpa using val.lt_iff_lt.2 hw)
  simp at this
  rcases eq_or_ne (val (∗2 : Nimber)⁻¹) 0 with h0 | h0
  · rw [h0] at this; simp at this
  · have h2 : (2 : Ordinal) * 1 ≤ 2 * val (∗2 : Nimber)⁻¹ := by gcongr; exact Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 h0)
    rw [this, mul_one] at h2
    exact absurd h2 (not_le.2 one_lt_two)

-- helper: 2 ^ 2 = 4 for ordinals
theorem pow22 : (2 : Ordinal) ^ (2 : ℕ) = 4 := by
  rw [pow_two]
  have : ((2 : ℕ) : Ordinal) * ((2 : ℕ) : Ordinal) = ((4 : ℕ) : Ordinal) := by
    rw [← Ordinal.natCast_mul]
  simpa using this

-- helper: 3 ^ 2 ≠ 5 for ordinals
theorem pow32 : (3 : Ordinal) ^ (2 : ℕ) ≠ 5 := fun e => by
  rw [pow_two] at e
  have : ((3 : ℕ) : Ordinal) * ((3 : ℕ) : Ordinal) = ((5 : ℕ) : Ordinal) := by simpa using e
  rw [← Ordinal.natCast_mul, Nat.cast_inj] at this
  norm_num at this

-- helper: ∗4 + 1 = ∗5
theorem four_add_one : ∗4 + 1 = ∗5 := by
  have h4 : IsGroup (∗4) := by
    have := IsGroup.two.pow 2; simp only [val_of] at this; rwa [pow22] at this
  have := h4.add_eq_of_lt (y := 1) (by simp)
  rw [← this]; simp; norm_num

-- `Nimber.IsAlgClosed.pow_eq`
theorem p1_44 : ¬ drop0% Nimber.IsAlgClosed.pow_eq 2 := fun h => by
  have h3 := @h 2 (∗3)
  have h2 := @h 2 (∗2)
  have e : (∗3 : Nimber) ^ 2 = ∗5 := by
    rw [← two_add_one, CharTwo.add_sq, h2, one_pow, ← four_add_one]; simp; exact pow22
  rw [h3] at e
  simp at e
  exact pow32 e

end

section
open IGame Nimber Polynomial Cardinal

-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.surjective_f`
theorem p1_45 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.surjective_f 7 := fun H => by
  have : IsWellOrder Unit emptyRelation := Subsingleton.isWellOrder _
  have eta : Order.IsEta #Unit Unit := by rw [Cardinal.mk_eq_one]; exact Order.IsEta.one
  have hord : (#Unit).ord = Ordinal.type (@emptyRelation Unit) := by
    rw [Cardinal.mk_eq_one, Cardinal.ord_one, Ordinal.type_unit]
  have := @H Unit Unit _ _ emptyRelation _ (fun _ _ => True) eta hord eta rfl
  exact irrefl_of (fun _ _ : Unit => True) () trivial

-- helper: a strictly monotone map from Fin 2 has two distinct values, so some value is not minimal
theorem fin2_aux {F : Fin 2 → ℚ} (hm : StrictMono F) (H : ∀ z a, ¬ WellOrderingRel z (F a)) : False := by
  rcases trichotomous_of WellOrderingRel (F 0) (F 1) with h | h | h
  · exact H _ _ h
  · exact (hm (show (0 : Fin 2) < 1 by decide)).ne h
  · exact H _ _ h

-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.not_lt_f`
theorem p1_46 : ¬ drop0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.not_lt_f 12 := fun H => by
  have eta : Order.IsEta #(Fin 2) ℚ := Order.IsEta.Rat.isEta_aleph0.mono (by simpa using (nat_lt_aleph0 2).le)
  have hord : (#(Fin 2)).ord = Ordinal.type (α := Fin 2) (· < ·) := by simp
  have hm := (priv% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.strictMono_f)
    (α := Fin 2) (β := ℚ) (r := (· < ·)) (s := WellOrderingRel) (h := eta) (hord := hord)
  exact fin2_aux hm (fun z a => @H (Fin 2) ℚ _ _ (· < ·) _ WellOrderingRel _ eta hord z a)

-- `Nimber.IsField.mul_eq_of_lt`
theorem p1_47 : ¬ drop0% Nimber.IsField.mul_eq_of_lt 3 := fun H => by
  have h2ω : (∗2 : Nimber) < ∗Ordinal.omega0 := by
    rw [of.lt_iff_lt]; simpa using Ordinal.natCast_lt_omega0 2
  have e1 : ∗(Ordinal.omega0 + 1) = ∗Ordinal.omega0 + 1 := by
    simpa using IsGroup.omega0.add_eq_of_lt (y := 1) (lt_of_le_of_lt (by simp) h2ω)
  have e2 : ∗(Ordinal.omega0 * 2) = ∗Ordinal.omega0 * ∗2 := by
    simpa using IsRing.omega0.mul_eq_of_lt IsGroup.omega0 le_rfl h2ω (fun z hz => IsField.omega0.inv_lt hz)
  have g : IsGroup (∗(Ordinal.omega0 * 2)) := by simpa using IsGroup.omul IsGroup.omega0 IsGroup.two
  have e3 : ∗(Ordinal.omega0 * 2 + 2) = ∗(Ordinal.omega0 * 2) + ∗2 := by
    simpa using g.add_eq_of_lt (y := ∗2) (lt_of_lt_of_le h2ω (by
      rw [of.le_iff_le]; exact Ordinal.le_mul_left _ (by norm_num)))
  have := @H (∗(Ordinal.omega0 + 1)) (∗Ordinal.omega0) (∗2) IsField.omega0
    (by rw [of.le_iff_le]; exact le_self_add) h2ω
  rw [e1, add_mul, one_mul, ← e2, ← e3, ← e1] at this
  simp at this
  have e4 : (Ordinal.omega0.{0} + 1) * 2 = Ordinal.omega0 * 2 + 1 := by
    rw [Ordinal.mul_two, Ordinal.mul_two, _root_.add_assoc, ← _root_.add_assoc 1, Ordinal.one_add_omega0,
      ← _root_.add_assoc]
  rw [e4] at this
  exact one_lt_two.ne (add_left_cancel this)

end

end Probe1
