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

namespace Probe2
open IGame Set

theorem notSmallUniv : ¬ Small.{0} (Set.univ : Set Surreal.{0}) := by
  intro h
  have h2 : Small.{0} Surreal.{0} := (small_univ_iff).1 h
  have : Small.{0} Ordinal.{0} :=
    small_of_injective (f := fun o : Ordinal.{0} => NatOrdinal.toSurreal (NatOrdinal.of o))
      (fun a b hab => by simpa using hab)
  exact not_small_ordinal.{0, 0} this

theorem small0 : SignExpansion.Small 0 := SignExpansion.small_iff_length_ne_top.2 (by simp)

theorem smallEmpty : Small.{0} (∅ : Set Surreal.{0}) := @Countable.toSmall _ Set.countable_empty.to_subtype

theorem notNumYS : ¬ Numeric !{{IGame.star} | ∅} := by
  intro hn
  exact not_numeric_star (Numeric.of_mem_moves (p := .left) (x := !{{IGame.star} | ∅}) (by simp))

theorem notNumUp : ¬ Numeric IGame.up := by
  intro hn
  exact not_numeric_star (Numeric.of_mem_moves (p := .right) (x := IGame.up) (by simp [IGame.up]))

-- `SignExpansion.apply_lt_pred_apply_iff` idx 1: necessary (pred 0 has length ⊤, not small)
theorem p2_1 : ¬ indep0% SignExpansion.apply_lt_pred_apply_iff 1 := fun h =>
  absurd (@h (@SignExpansion.pred 0 small0) 0)
    (by rw [SignExpansion.small_iff_length_ne_top, SignExpansion.length_pred]; simp)

-- `SignExpansion.pred_apply_ne_apply_iff` idx 1: necessary (pred 0 is not small)
theorem p2_2 : ¬ indep0% SignExpansion.pred_apply_ne_apply_iff 1 := fun h =>
  absurd (@h (@SignExpansion.pred 0 small0) 0)
    (by rw [SignExpansion.small_iff_length_ne_top, SignExpansion.length_pred]; simp)

theorem one_ne_bot : Simplicity.of ((1 : NatOrdinal) : SignExpansion) ≠ ⊥ :=
  ne_bot_of_gt (NatOrdinal.of_toSignExpansion_lt_iff.2 zero_lt_one)

-- `_private.CombinatorialGames.SignExpansion.Simplicity.0.Simplicity.sSup_apply_of_mem` idx 3: necessary (s = ∅)
theorem p2_3 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Simplicity.«0».Simplicity.sSup_apply_of_mem 3 := by
  intro h
  obtain ⟨o, ho⟩ : ∃ o, Simplicity.of ((1 : NatOrdinal) : SignExpansion) o ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact one_ne_bot (DFunLike.ext _ _ fun o => by rw [Simplicity.bot_apply]; exact hc o)
  have := @h _ ∅ (Set.pairwise_empty _) o ho
  rw [Simplicity.sSup_empty, Simplicity.bot_apply] at this
  exact ho this.symm

-- `Simplicity.sSup_of_not_bddAbove` idx 1: necessary (s = {of 1})
theorem p2_4 : ¬ drop0% Simplicity.sSup_of_not_bddAbove 1 := by
  intro h
  have h1 := @h {Simplicity.of ((1 : NatOrdinal) : SignExpansion)}
  have h2 := (Simplicity.isLUB_sSup_of_bddAbove (bddAbove_singleton (a := Simplicity.of ((1 : NatOrdinal) : SignExpansion)))).unique (isLUB_singleton (a := Simplicity.of ((1 : NatOrdinal) : SignExpansion)))
  exact one_ne_bot (h2 ▸ h1)

-- `Surreal.lt_trunc_iff_lt` idx 3: necessary (o = 0, x = 1, y = 0)
theorem p2_5 : ¬ drop0% Surreal.lt_trunc_iff_lt 3 := by
  intro h
  have hb := Surreal.birthday_trunc_le 0 (1 : Surreal.{0})
  have h0 : Surreal.trunc 0 (1 : Surreal.{0}) = 0 :=
    Surreal.birthday_eq_zero.1 (nonpos_iff_eq_zero.1 hb)
  have := (@h 1 0 0).2 zero_lt_one
  rw [h0] at this
  exact lt_irrefl _ this

-- `IGame.Fits.antisymm` idx 2: necessary (0 fits 1, 0 ≉ 1)
theorem p2_6 : ¬ drop0% IGame.Fits.antisymm 2 := by
  intro h
  have := @h 0 1 (by simp [IGame.Fits])
  exact absurd this (by game_cmp)

-- `Surreal.mk_eq` idx 3: necessary (x = 0, y = {⋆ | } ≈ 0 is not numeric)
theorem p2_7 : ¬ indep0% Surreal.mk_eq 3 := fun h =>
  notNumYS (@h 0 !{{IGame.star} | ∅} Numeric.zero (by game_cmp))

-- `Surreal.mk_add` idx 2: necessary (x = ⋆)
theorem p2_8 : ¬ indep0% Surreal.mk_add 2 := fun h => not_numeric_star (@h IGame.star 0 Numeric.zero)

-- `Surreal.ofSets_le_ofSets_iff'` idx 2: necessary (left set = all surreals, not small)
theorem p2_9 : ¬ indep0% Surreal.ofSets_le_ofSets_iff' 2 := fun h =>
  notSmallUniv (@h (fun p => Player.cases univ ∅ p) (fun _ => ∅) smallEmpty smallEmpty smallEmpty
    (by simp) (by simp))

-- `Surreal.birthday_ofSets_le'` idx 1: necessary (left set = all surreals)
theorem p2_10 : ¬ indep0% Surreal.birthday_ofSets_le' 1 := fun h =>
  notSmallUniv (@h (fun p => Player.cases univ ∅ p) smallEmpty (by simp))

-- `Surreal.birthday_ofSets_le` idx 2: necessary (s = all surreals)
theorem p2_11 : ¬ indep0% Surreal.birthday_ofSets_le 2 := fun h =>
  notSmallUniv (@h univ ∅ smallEmpty (by simp))

-- `Surreal.Cut.birthday_of_numeric` idx 1: necessary (⊥ is not numeric)
theorem p2_12 : ¬ indep0% Surreal.Cut.birthday_of_numeric 1 := fun h => by
  have := h ⊥
  rw [Surreal.Cut.numeric_iff_birthday, Surreal.Cut.birthday_bot] at this
  exact this Order.isSuccPrelimit_bot

open Classical in
theorem starInv : IGame.star⁻¹ = 0 := by
  show (if 0 < IGame.star then _ else if IGame.star < 0 then _ else 0) = 0
  rw [ite_cond_eq_false _ _ (eq_false (by game_cmp)), ite_cond_eq_false _ _ (eq_false (by game_cmp))]

-- `IGame.Numeric.inv_nonpos` idx 1: necessary (x = ⋆, ⋆⁻¹ = 0)
theorem p2_13 : ¬ drop0% IGame.Numeric.inv_nonpos 1 := fun h => by
  have := (@h IGame.star).1 (by rw [starInv])
  exact absurd this (by game_cmp)

-- `IGame.Numeric.mul_nonpos_of_nonpos_of_nonneg` idx 5: necessary (x = y = -1)
theorem p2_14 : ¬ drop0% IGame.Numeric.mul_nonpos_of_nonpos_of_nonneg 5 := fun h =>
  absurd (@h (-1) (-1) _ _ (by game_cmp)) (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.mk_lt_mk_of_ne'` idx 1: necessary (x = ↑)
theorem p2_15 : ¬ indep0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.mk_lt_mk_of_ne' 1 := fun h =>
  notNumUp (@h IGame.up (by game_cmp) IGame.star (by simp [IGame.up]))

-- `Real.mem_moves_right_toIGame_of_lt` idx 2: necessary (q = 0, x = 0)
theorem p2_16 : ¬ drop0% Real.mem_moves_right_toIGame_of_lt 2 := fun h =>
  absurd (@h 0 0) (by simp)

-- `_private.CombinatorialGames.Surreal.Leading.0.Surreal.leadingTerm_mono'` idx 2: removable (leadingTerm is monotone)
theorem p2_17 : drop% _private.CombinatorialGames.Surreal.Leading.«0».Surreal.leadingTerm_mono' 2 :=
  fun h => Surreal.leadingTerm_mono h

-- `_private.CombinatorialGames.Surreal.Real.0.Real.mul_toIGame_lt_dyadic'` idx 3: removable (sibling without sign hypotheses)
theorem p2_18 : drop% _private.CombinatorialGames.Surreal.Real.«0».Real.mul_toIGame_lt_dyadic' 3 :=
  fun _ h => (priv% _private.CombinatorialGames.Surreal.Real.«0».Real.mul_toIGame_lt_dyadic) _ h

-- `_private.CombinatorialGames.Surreal.Division.0.numeric_option_inv` idx 4: removable (x⁻¹ is numeric)
theorem p2_19 : drop% _private.CombinatorialGames.Surreal.Division.«0».numeric_option_inv 4 :=
  fun _ _ _ _ hy => Numeric.of_mem_moves hy



local notation "ωI" => NatOrdinal.toIGame (NatOrdinal.of Ordinal.omega0)

theorem notShortOmega : ¬ Short ωI := fun _ => lt_irrefl _ (Short.lt_omega0 ωI)

-- `Dyadic.upper_le_of_lt` idx 2: necessary (x = 0, y = 1/2)
theorem p2_20 : ¬ drop0% Dyadic.upper_le_of_lt 2 := fun h =>
  absurd (@h 0 Dyadic.half (by decide)) (by
    rw [← Dyadic.toRat_le_toRat_iff, Dyadic.coe_upper]; norm_num)

-- `IGame.toDyadic_sub` idx 4: necessary (y = ω is numeric, not short)
theorem p2_21 : ¬ indep0% IGame.toDyadic_sub 4 := fun h =>
  notShortOmega (@h 0 ωI Short.zero Numeric.zero inferInstance)

-- `_private.CombinatorialGames.Surreal.Dyadic.0.IGame.equiv_dyadic` idx 1: necessary (x = ω)
theorem p2_22 : ¬ drop0% _private.CombinatorialGames.Surreal.Dyadic.«0».IGame.equiv_dyadic 1 := fun h => by
  obtain ⟨q, hq⟩ := @h ωI inferInstance
  exact not_le_of_gt (Short.lt_omega0 (q : IGame)) hq.le

-- `Surreal.wlog_eq` idx 4: necessary (x = 0, y = 1, r = 1)
theorem p2_23 : ¬ drop0% Surreal.wlog_eq 4 := fun h => by
  have := @h 0 1 1 one_ne_zero (fun s hs => by
    have : (0 : Surreal) < s := by exact_mod_cast (zero_lt_one.trans hs)
    exact (mul_pos this (Surreal.wpow_pos _)).le)
  rw [Surreal.wlog_zero] at this
  exact zero_ne_one this

-- `IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg'` idx 7: necessary (x = y = 0, r = -1, s = -2)
theorem p2_24 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg' 7 := fun h => by
  have := @h 0 0 _ _ (-1) (-2) (by decide)
  rw [← Surreal.mk_lt_mk] at this
  simp at this

-- `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow` idx 10: necessary (x = 0, y = z = 1, r = 0, s = 1, t = -1)
theorem p2_25 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow 10 := fun h => by
  have := @h 0 1 1 _ _ _ 0 1 (-1) one_pos (by game_cmp) (by game_cmp)
  rw [← Surreal.mk_lt_mk] at this
  simp at this

-- `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow'` idx 10: necessary (x = 0, y = z = 1, r = 0, s = 1, t = -1)
theorem p2_26 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow' 10 := fun h => by
  have := @h 0 1 1 _ _ _ 0 1 (-1) (by decide) (by game_cmp) (by game_cmp)
  rw [← Surreal.mk_lt_mk] at this
  simp at this

-- `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow'` idx 12: removable (s ω^y already exceeds r ω^x and t ω^z > 0)
theorem p2_27 : drop% IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow' 12 := by
  intro x y z _ _ _ r s t hs ht hx
  have h1 := IGame.Numeric.mul_wpow_lt_mul_wpow_of_pos' r hs hx
  rw [← Surreal.mk_lt_mk] at h1 ⊢
  simp at h1 ⊢
  have ht' : (0 : Surreal) < t := by exact_mod_cast ht
  have := mul_pos ht' (Surreal.wpow_pos (Surreal.mk z))
  linarith




-- `Surreal.Cut.mem_right_of_toSurreal_lt` idx 3: necessary (x = leftSurreal 0, y = -1)
theorem p2_28 : ¬ drop0% Surreal.Cut.mem_right_of_toSurreal_lt 3 := fun h => by
  have := @h (Surreal.Cut.leftSurreal 0) inferInstance (-1)
  rw [Surreal.Cut.mem_right_leftSurreal] at this
  exact absurd this (by norm_num)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P1_of_P3` idx 7: necessary (x₁ = x₂ = y₁ = y₃ = 0, x₃ = y₂ = 1)
theorem p2_29 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P1_of_P3 7 := fun h => by
  have := @h 0 0 1 0 1 0 (by
    show Game.mk _ + Game.mk _ < Game.mk _ + Game.mk _
    rw [← Game.mk_add, ← Game.mk_add, Game.mk_lt_mk]; game_cmp)
  change Game.mk _ < Game.mk _ at this
  rw [Game.mk_lt_mk] at this
  exact absurd this (by unfold mulOption; game_cmp)

theorem ih1 : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH1) (-1) 1 := by
  intro p q x₁ x₂ y' h₁ h₂ _
  have e₁ : x₁ = 0 := by cases p <;> simp at h₁; simp_all
  have e₂ : x₂ = 0 := by cases q <;> simp at h₂; simp_all
  subst e₁ e₂
  exact ⟨fun _ => rfl, fun h => absurd h (lt_irrefl _)⟩

-- `_private.CombinatorialGames.Surreal.Multiplication.0.P3_of_IH1` idx 8: necessary (x = 1, y = -1, a = b = d = 0)
theorem p2_30 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».P3_of_IH1 8 := fun h => by
  have := @h 1 (-1) 0 0 0 inferInstance ih1 (by simp) (by simp)
  change Game.mk _ + Game.mk _ < Game.mk _ + Game.mk _ at this
  rw [← Game.mk_add, ← Game.mk_add, Game.mk_lt_mk] at this
  exact absurd this (by game_cmp)

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt_mul_of_equiv` idx 6: necessary (x₁ = x₂ = 1, y = ⋆, a = b = 0)
theorem p2_31 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt_mul_of_equiv 6 := fun h => by
  have := @h 1 1 IGame.star 0 0 inferInstance .rfl (by simp) (by simp)
  rw [Game.mk_lt_mk] at this
  exact absurd this (by unfold mulOption; game_cmp)

theorem numX : Numeric !{{0, -1} | ∅} := by
  rw [numeric_def]
  refine ⟨by simp, ?_⟩
  intro p y hy
  cases p <;> simp at hy
  rcases hy with rfl | rfl <;> infer_instance

-- `_private.CombinatorialGames.Surreal.Pow.0.Surreal.mk_lt_mk_of_ne` idx 6: necessary (x = {0, -1 | } ≈ 1, y = -1)
theorem p2_32 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».Surreal.mk_lt_mk_of_ne 6 := fun h => by
  have := @h !{{0, -1} | ∅} numX (by game_cmp) (fun y hy hy0 => by
    simp at hy
    rcases hy with rfl | rfl <;> exact absurd hy0 (by game_cmp)) (-1) (by simp)
  have e1 : ∀ i, @Surreal.mk !{{0, -1} | ∅} i = 1 := fun i => by
    rw [← Surreal.mk_one]; exact Surreal.mk_eq (by game_cmp)
  rw [e1] at this
  dsimp only at this
  rw [show ∀ i, @Surreal.mk (-1) i = -1 from fun i => by rw [← Surreal.mk_one, ← Surreal.mk_neg]] at this
  rw [ArchimedeanClass.mk_neg] at this
  exact lt_irrefl _ this

theorem notSmallIio : ¬ Small.{0} (Set.Iio (0 : Surreal.{0})) := by
  intro h
  have hn : ∀ o : Ordinal.{0}, (0 : Surreal) ≤ NatOrdinal.toSurreal (NatOrdinal.of o) := fun o => by
    rw [← NatOrdinal.toSurreal_zero]
    exact NatOrdinal.toSurreal.monotone _root_.zero_le
  have : Small.{0} Ordinal.{0} := small_of_injective
    (f := fun o : Ordinal.{0} =>
      (⟨-(NatOrdinal.toSurreal (NatOrdinal.of o) + 1), by
        have := hn o; simp only [Set.mem_Iio]; linarith⟩ : Set.Iio (0 : Surreal.{0})))
    (fun a b hab => by
      simp only [Subtype.mk.injEq, neg_inj, add_left_inj] at hab
      simpa using hab)
  exact not_small_ordinal.{0, 0} this

-- `Surreal.birthday_ofSets_le_of_btwn'` idx 2: necessary (left set = all negative surreals, z = 0)
theorem p2_33 : ¬ indep0% Surreal.birthday_ofSets_le_of_btwn' 2 := fun h =>
  notSmallIio (@h (fun p => Player.cases (Iio 0) ∅ p) 0 smallEmpty (by simp) (fun _ hx => hx) (by simp))



-- `_private.CombinatorialGames.Surreal.Division.0.instNumericHDivIGameOfInv` idx 2: necessary (x = ⋆, y = 1: the option mulOption ⋆ 1⁻¹ 0 0 is both a left and a right option of ⋆ * 1⁻¹)
theorem p2_34 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».instNumericHDivIGameOfInv 2 := fun h => by
  have hn := @h IGame.star 1 (Numeric.inv 1)
  rw [IGame.div_eq_mul_inv] at hn
  have hz := zero_mem_moves_left_inv (x := 1) (by game_cmp)
  have h1 : mulOption IGame.star 1⁻¹ 0 0 ∈ (IGame.star * 1⁻¹).moves (.left * .left) :=
    mulOption_mem_moves_mul (by simp [IGame.star]) hz
  have h2 : mulOption IGame.star 1⁻¹ 0 0 ∈ (IGame.star * 1⁻¹).moves (.right * .left) :=
    mulOption_mem_moves_mul (by simp [IGame.star]) hz
  exact lt_irrefl _ (Numeric.left_lt_right h1 h2)

-- `_private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.wpow_lt_mulOption` idx 13: necessary (x = y = w = 0, z = 1, r = 1, s = 2)
theorem p2_35 : ¬ drop0% _private.CombinatorialGames.Surreal.Pow.«0».IGame.Numeric.wpow_lt_mulOption 13 := fun h => by
  have := @h 0 0 1 0 Numeric.zero Numeric.zero inferInstance Numeric.zero 1 2 (by decide) (by decide)
    (by game_cmp) (Numeric.wpow_add_equiv _ _) (Numeric.wpow_add_equiv _ _)
  unfold mulOption at this
  rw [← Surreal.mk_lt_mk] at this
  simp [Surreal.mk_wpow] at this
  have h1 : (1 : Surreal) < ω^ (1 : Surreal) := by
    simpa using (Surreal.wpow_lt_wpow (x := 0) (y := 1)).2 one_pos
  linarith


theorem mkTwo (x : IGame) : Game.mk (x * 2) = Game.mk (x + x) := by
  rw [← one_add_one_eq_two, Game.mk_eq_mk.2 (mul_add_equiv x 1 1)]
  simp

-- `IGame.Numeric.lt_div_iff_of_neg` idx 3: necessary (x = ↓ + ⋆, y = 0, z = -2: x ‖ 0 but -2x = ⇑ > 0)
theorem p2_36 : ¬ drop0% IGame.Numeric.lt_div_iff_of_neg 3 := fun h => by
  have hz : (-2 : IGame) < 0 := by game_cmp
  have := (@h (-IGame.up + IGame.star) 0 (-2) Numeric.zero inferInstance hz).2
  rw [IGame.zero_div] at this
  refine absurd (this ?_) (by game_cmp)
  rw [← Game.mk_lt_mk, mul_neg, Game.mk_neg, mkTwo, ← Game.mk_neg, Game.mk_lt_mk]
  game_cmp

-- `IGame.Numeric.equiv_inv_of_mul_eq_one` idx 2: necessary (x = ½ + ⋆, y = 2: x * 2 ≈ 1 but x ≉ ½ ≈ 2⁻¹)
theorem p2_37 : ¬ drop0% IGame.Numeric.equiv_inv_of_mul_eq_one 2 := fun h => by
  have h1 : (IGame.half + IGame.star) * 2 ≈ 1 := by
    rw [← Game.mk_eq_mk, mkTwo, Game.mk_eq_mk]; game_cmp
  have h2 := @h (IGame.half + IGame.star) 2 inferInstance h1
  have h3 : (2 : IGame)⁻¹ ≈ IGame.half := by
    rw [← Surreal.mk_eq_mk, IGame.mk_half]; simp; exact_mod_cast Surreal.mk_natCast 2
  exact absurd (h2.trans h3) (by game_cmp)

open Classical in
theorem invY : (IGame.half + !{{1} | {-1}})⁻¹ = 0 := by
  show (if 0 < IGame.half + !{{1} | {-1}} then _ else if IGame.half + !{{1} | {-1}} < 0 then _ else 0) = 0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by game_cmp)), ite_eq_right_of_eq_false _ _ (eq_false (by game_cmp))]

-- `IGame.Numeric.equiv_inv_of_mul_eq_one` idx 3: necessary (x = 2, y = ½ ± 1: 2y ≈ 1 but y ‖ 0, so y⁻¹ = 0)
theorem p2_38 : ¬ drop0% IGame.Numeric.equiv_inv_of_mul_eq_one 3 := fun h => by
  have h1 : (2 : IGame) * (IGame.half + !{{1} | {-1}}) ≈ (1 : IGame) := by
    have hp : (!{{1} | {-1}} : IGame) + !{{1} | {-1}} ≈ 0 := by game_cmp
    rw [mul_comm, ← Game.mk_eq_mk, mkTwo]
    have e : Game.mk ((IGame.half + !{{1} | {-1}}) + (IGame.half + !{{1} | {-1}}))
        = Game.mk (IGame.half + IGame.half) + Game.mk (!{{1} | {-1}} + !{{1} | {-1}}) := by
      simp only [Game.mk_add]; abel
    rw [e, Game.mk_eq_mk.2 hp, Game.mk_eq_mk.2 half_add_half_equiv_one]
    simp
  have h2 := @h 2 (IGame.half + !{{1} | {-1}}) inferInstance h1
  rw [invY] at h2
  exact absurd h2 (by game_cmp)
end Probe2
