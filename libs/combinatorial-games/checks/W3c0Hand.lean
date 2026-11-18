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

namespace W3c0

section
open IGame


noncomputable abbrev ωI : IGame.{0} := NatOrdinal.toIGame (NatOrdinal.of Ordinal.omega0)
theorem notShortOmega : ¬ Short ωI := fun _ => lt_irrefl _ (Short.lt_omega0 ωI)

theorem notEquivStar (y : IGame) [Numeric y] : ¬ ⋆ ≈ y := fun h => by
  rcases Numeric.le_total y 0 with hy | hy
  · exact zero_lf_star (h.1.trans hy)
  · exact star_lf_zero (hy.trans h.2)

-- `Dyadic.lower_eq_of_den_eq_one` idx 1: necessary (x = -1/2: lower x = -1, num - 1 = -2)
theorem w3_1 : ¬ drop0% Dyadic.lower_eq_of_den_eq_one 1 := fun h => by
  have := congrArg Dyadic.toRat (@h (-Dyadic.half))
  rw [Dyadic.coe_lower] at this
  norm_num at this
-- `Dyadic.upper_eq_of_den_eq_one` idx 1: necessary (x = 1/2: upper x = 1, num + 1 = 2)
theorem w3_2 : ¬ drop0% Dyadic.upper_eq_of_den_eq_one 1 := fun h => by
  have := congrArg Dyadic.toRat (@h Dyadic.half)
  rw [Dyadic.coe_upper] at this
  norm_num at this
-- `Dyadic.lower_add_le_of_den_le` idx 2: necessary (x = 1/2, y = 0)
theorem w3_3 : ¬ drop0% Dyadic.lower_add_le_of_den_le 2 := fun h => by
  have := @h Dyadic.half 0
  rw [← Dyadic.toRat_le_toRat_iff] at this
  simp [Dyadic.coe_lower] at this
  norm_num at this
-- `Dyadic.lower_add_le_of_den_ge` idx 2: necessary (x = 0, y = 1/2)
theorem w3_4 : ¬ drop0% Dyadic.lower_add_le_of_den_ge 2 := fun h => by
  have := @h 0 Dyadic.half
  rw [← Dyadic.toRat_le_toRat_iff] at this
  simp [Dyadic.coe_lower] at this
  norm_num at this
-- `Dyadic.le_upper_add_of_den_le` idx 2: necessary (x = 1/2, y = 0)
theorem w3_5 : ¬ drop0% Dyadic.le_upper_add_of_den_le 2 := fun h => by
  have := @h Dyadic.half 0
  rw [← Dyadic.toRat_le_toRat_iff] at this
  simp [Dyadic.coe_upper] at this
  norm_num at this
-- `Dyadic.le_upper_add_of_den_ge` idx 2: necessary (x = 0, y = 1/2)
theorem w3_6 : ¬ drop0% Dyadic.le_upper_add_of_den_ge 2 := fun h => by
  have := @h 0 Dyadic.half
  rw [← Dyadic.toRat_le_toRat_iff] at this
  simp [Dyadic.coe_upper] at this
  norm_num at this
-- `Dyadic.toIGame_of_den_eq_one` idx 1: necessary (x = 1/2: toIGame = ½ ≠ 1)
theorem w3_7 : ¬ drop0% Dyadic.toIGame_of_den_eq_one 1 := fun h => by
  have := @h Dyadic.half
  rw [← Dyadic.toIGame_intCast, Dyadic.toIGame_inj] at this
  have := congrArg Dyadic.toRat this
  norm_num at this
-- `Dyadic.toIGame_of_den_ne_one` idx 1: necessary (x = 0: 0 has no left move, {lower 0 | upper 0} has one)
theorem w3_8 : ¬ drop0% Dyadic.toIGame_of_den_ne_one 1 := fun h => by
  have := congrArg (moves Player.left) (@h 0)
  simp at this
-- `_private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.lower_lt_aux` idx 1: removable (every Dyadic toIGame is numeric; follows from public toIGame_lt_toIGame and lower_lt)
theorem w3_9 : drop% _private.CombinatorialGames.Surreal.Dyadic.«0».Dyadic.lower_lt_aux 1 := by
  intro x; exact Dyadic.toIGame_lt_toIGame.2 (Dyadic.lower_lt x)
-- `_private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.lt_upper_aux` idx 1: removable (every Dyadic toIGame is numeric; follows from public toIGame_lt_toIGame and lt_upper)
theorem w3_10 : drop% _private.CombinatorialGames.Surreal.Dyadic.«0».Dyadic.lt_upper_aux 1 := by
  intro x; exact Dyadic.toIGame_lt_toIGame.2 (Dyadic.lt_upper x)
-- `_private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.toIGame_lt_toIGame_aux` idx 2: removable (Numeric instance derivable (IGame.Numeric.dyadic); follows from public toIGame_lt_toIGame)
theorem w3_11 : drop% _private.CombinatorialGames.Surreal.Dyadic.«0».Dyadic.toIGame_lt_toIGame_aux 2 := by
  intro x y _ h; exact Dyadic.toIGame_lt_toIGame.2 h
-- `_private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.toIGame_lt_toIGame_aux` idx 3: removable (Numeric instance derivable (IGame.Numeric.dyadic); follows from public toIGame_lt_toIGame)
theorem w3_12 : drop% _private.CombinatorialGames.Surreal.Dyadic.«0».Dyadic.toIGame_lt_toIGame_aux 3 := by
  intro x y _ h; exact Dyadic.toIGame_lt_toIGame.2 h
-- `_private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.toIGame_lt_toIGame_aux` idx 4: necessary (x = y = 0)
theorem w3_13 : ¬ drop0% _private.CombinatorialGames.Surreal.Dyadic.«0».Dyadic.toIGame_lt_toIGame_aux 4 := fun h =>
  lt_irrefl _ (@h 0 0 _ _)
-- `_private.CombinatorialGames.Surreal.Dyadic.0.IGame.equiv_dyadic` idx 2: necessary (x = ⋆ (short, not equivalent to any numeric game))
theorem w3_14 : ¬ drop0% _private.CombinatorialGames.Surreal.Dyadic.«0».IGame.equiv_dyadic 2 := fun h => by
  obtain ⟨q, hq⟩ := @h ⋆ inferInstance
  exact notEquivStar _ hq
-- `IGame.equiv_toIGame_toDyadic` idx 1: necessary (x = ω (numeric, not short))
theorem w3_15 : ¬ indep0% IGame.equiv_toIGame_toDyadic 1 := fun h => notShortOmega (@h ωI inferInstance)
-- `IGame.toIGame_toDyadic_equiv` idx 1: necessary (x = ω (numeric, not short))
theorem w3_16 : ¬ indep0% IGame.toIGame_toDyadic_equiv 1 := fun h => notShortOmega (@h ωI inferInstance)
-- `Game.ratCast_toDyadic` idx 1: necessary (x = ω (numeric, not short))
theorem w3_17 : ¬ indep0% Game.ratCast_toDyadic 1 := fun h => notShortOmega (@h ωI inferInstance)
-- `Surreal.ratCast_toDyadic` idx 1: necessary (x = ω (numeric, not short))
theorem w3_18 : ¬ indep0% Surreal.ratCast_toDyadic 1 := fun h => notShortOmega (@h ωI inferInstance)
-- `IGame.equiv_toIGame_iff_toDyadic_eq` idx 1: necessary (x = ω (numeric, not short))
theorem w3_19 : ¬ indep0% IGame.equiv_toIGame_iff_toDyadic_eq 1 := fun h => notShortOmega (@h ωI inferInstance 0)
-- `IGame.toIGame_equiv_iff_eq_toDyadic` idx 1: necessary (x = ω (numeric, not short))
theorem w3_20 : ¬ indep0% IGame.toIGame_equiv_iff_eq_toDyadic 1 := fun h => notShortOmega (@h ωI inferInstance 0)
-- `IGame.toDyadic_neg` idx 1: necessary (x = ω (numeric, not short))
theorem w3_21 : ¬ indep0% IGame.toDyadic_neg 1 := fun h => notShortOmega (@h ωI inferInstance)
-- `IGame.toDyadic_add` idx 2: necessary (x = ω (numeric, not short), y = 0)
theorem w3_22 : ¬ indep0% IGame.toDyadic_add 2 := fun h => notShortOmega (@h ωI 0 inferInstance Short.zero Numeric.zero)
-- `IGame.toDyadic_add` idx 3: necessary (x = ⋆ (short, not numeric), y = 0)
theorem w3_23 : ¬ indep0% IGame.toDyadic_add 3 := fun h => not_numeric_star (@h ⋆ 0 inferInstance Short.zero Numeric.zero)
-- `IGame.toDyadic_add` idx 4: necessary (x = 0, y = ω (numeric, not short))
theorem w3_24 : ¬ indep0% IGame.toDyadic_add 4 := fun h => notShortOmega (@h 0 ωI Short.zero Numeric.zero inferInstance)
-- `IGame.toDyadic_add` idx 5: necessary (x = 0, y = ⋆ (short, not numeric))
theorem w3_25 : ¬ indep0% IGame.toDyadic_add 5 := fun h => not_numeric_star (@h 0 ⋆ Short.zero Numeric.zero inferInstance)
-- `IGame.toDyadic_sub` idx 2: necessary (x = ω (numeric, not short), y = 0)
theorem w3_26 : ¬ indep0% IGame.toDyadic_sub 2 := fun h => notShortOmega (@h ωI 0 inferInstance Short.zero Numeric.zero)
-- `IGame.toDyadic_sub` idx 3: necessary (x = ⋆ (short, not numeric), y = 0)
theorem w3_27 : ¬ indep0% IGame.toDyadic_sub 3 := fun h => not_numeric_star (@h ⋆ 0 inferInstance Short.zero Numeric.zero)
-- `IGame.toDyadic_sub` idx 5: necessary (x = 0, y = ⋆ (short, not numeric))
theorem w3_28 : ¬ indep0% IGame.toDyadic_sub 5 := fun h => not_numeric_star (@h 0 ⋆ Short.zero Numeric.zero inferInstance)
-- `IGame.toDyadic_mul` idx 2: necessary (x = ω (numeric, not short), y = 0)
theorem w3_29 : ¬ indep0% IGame.toDyadic_mul 2 := fun h => notShortOmega (@h ωI 0 inferInstance Short.zero Numeric.zero)
-- `IGame.toDyadic_mul` idx 3: necessary (x = ⋆ (short, not numeric), y = 0)
theorem w3_30 : ¬ indep0% IGame.toDyadic_mul 3 := fun h => not_numeric_star (@h ⋆ 0 inferInstance Short.zero Numeric.zero)
-- `IGame.toDyadic_mul` idx 4: necessary (x = 0, y = ω (numeric, not short))
theorem w3_31 : ¬ indep0% IGame.toDyadic_mul 4 := fun h => notShortOmega (@h 0 ωI Short.zero Numeric.zero inferInstance)
-- `IGame.toDyadic_mul` idx 5: necessary (x = 0, y = ⋆ (short, not numeric))
theorem w3_32 : ¬ indep0% IGame.toDyadic_mul 5 := fun h => not_numeric_star (@h 0 ⋆ Short.zero Numeric.zero inferInstance)
end

section
open IGame SurrealHahnSeries


theorem notSmallSurreal : ¬ Small.{0} (Set.univ : Set Surreal.{0}) := by
  rw [small_univ_iff]; intro h
  exact not_small_ordinal.{0} (small_of_injective (f := fun o : NatOrdinal.{0} => NatOrdinal.toSurreal o)
    NatOrdinal.toSurreal.injective)

noncomputable def natInd : Surreal.{0} → ℝ := Set.indicator (Set.range (Nat.cast : ℕ → Surreal.{0})) (fun _ => 1)

theorem natInd_small : Small.{0} (Function.support natInd) :=
  small_subset (s := Set.range (Nat.cast : ℕ → Surreal.{0}))
    (Function.support_subset_iff'.2 (fun x hx => Set.indicator_of_notMem hx _))

theorem natInd_mem (n : ℕ) : (n : Surreal.{0}) ∈ Function.support natInd := by
  rw [Function.mem_support, natInd, Set.indicator_of_mem (Set.mem_range_self n)]; exact one_ne_zero

theorem natInd_notWF : ¬ (Function.support natInd).WellFoundedOn (fun x1 x2 => x1 > x2) := fun hwf => by
  have key : ∀ a : Function.support natInd, ∀ n : ℕ, (a : Surreal) ≠ n := fun a =>
    WellFounded.induction hwf (C := fun a : Function.support natInd => ∀ n : ℕ, (a : Surreal) ≠ n) a
      (fun a ih n ha => ih ⟨((n + 1 : ℕ) : Surreal), natInd_mem (n + 1)⟩
        (by show ((n + 1 : ℕ) : Surreal) > a.1; rw [ha]; exact_mod_cast Nat.lt_succ_self n) (n + 1) rfl)
  exact key ⟨0, by simpa using natInd_mem 0⟩ 0 (by simp)

-- a TermSeq of length o, constant coefficient c, exponents d - i
noncomputable def seqG (o : Ordinal.{0}) (c : ℝ) (hc : c ≠ 0) (d : Surreal.{0}) : TermSeq.{0} where
  length := o
  exp := fun i => d - NatOrdinal.toSurreal (NatOrdinal.of i.1)
  coeff := fun _ => c
  exp_strictAnti := fun a b hab => sub_lt_sub_left
    (NatOrdinal.toSurreal.lt_iff_lt.2 (show NatOrdinal.of a.1 < NatOrdinal.of b.1 from hab)) d
  coeff_ne_zero := fun _ => hc

-- the indicator of the negated ordinals: well-founded support for >, not small
noncomputable def negOrd : NatOrdinal.{0} → Surreal.{0} := fun o => -NatOrdinal.toSurreal o
noncomputable def ordInd : Surreal.{0} → ℝ := Set.indicator (Set.range negOrd) (fun _ => 1)
theorem ordInd_supp : Function.support ordInd = Set.range negOrd := by
  ext x; by_cases hx : x ∈ Set.range negOrd <;> simp [ordInd, hx]
theorem ordInd_wf : (Function.support ordInd).WellFoundedOn (fun x1 x2 => x1 > x2) := by
  rw [ordInd_supp, Set.wellFoundedOn_range]
  exact Subrelation.wf (fun {a b} hab => NatOrdinal.toSurreal.lt_iff_lt.1 (neg_lt_neg_iff.1 hab)) wellFounded_lt
theorem ordInd_notSmall : ¬ Small.{0} (Function.support ordInd) := fun hs => by
  rw [ordInd_supp] at hs
  have : Small.{0} NatOrdinal.{0} := small_of_injective (f := fun o => (⟨negOrd o, Set.mem_range_self o⟩ : Set.range negOrd))
    (fun a b hab => NatOrdinal.toSurreal.injective (neg_inj.1 (congrArg Subtype.val hab)))
  exact not_small_ordinal.{0} this

theorem one_len_pos : 0 < (1 : SurrealHahnSeries.{0}).length :=
  pos_iff_ne_zero.2 (by rw [Ne, length_eq_zero]; exact one_ne_zero)

theorem two_len : 1 < ((seqG 2 1 one_ne_zero 0 : TermSeq) : SurrealHahnSeries.{0}).length := by
  rw [TermSeq.length_coe]; exact one_lt_two

theorem coeffIdx_ne {x : SurrealHahnSeries.{0}} {i : Ordinal.{0}} (h : i < x.length) : x.coeffIdx i ≠ 0 := by
  rw [Ne, coeffIdx_eq_zero_iff, not_le]; exact h

-- `SurrealHahnSeries.coeff_mk` idx 1: necessary (f = indicator of the negated ordinals: support well-founded for >, not small)
theorem w3_33 : ¬ indep0% SurrealHahnSeries.coeff_mk 1 := fun h => ordInd_notSmall (h ordInd ordInd_wf)
noncomputable abbrev X2 : SurrealHahnSeries.{0} := ((seqG 2 1 one_ne_zero 0 : TermSeq) : SurrealHahnSeries.{0})
theorem X2_1 : (1 : Ordinal.{0}) < X2.length := two_len
theorem X2_0 : (0 : Ordinal.{0}) < X2.length := zero_lt_one.trans two_len
noncomputable abbrev e0 : X2.support := X2.exp ⟨0, X2_0⟩
noncomputable abbrev e1 : X2.support := X2.exp ⟨1, X2_1⟩
theorem e10 : (e1 : Surreal) < e0 := exp_lt_exp_iff.2 (Subtype.mk_lt_mk.2 zero_lt_one)
theorem trunc1 : X2.truncIdx 1 = X2.trunc e1 := truncIdx_of_lt X2_1
theorem c0 : X2.coeff e0 ≠ 0 := by rw [coeff_exp]; exact coeffIdx_ne X2_0
theorem c1 : X2.coeff e1 ≠ 0 := by rw [coeff_exp]; exact coeffIdx_ne X2_1

-- `SurrealHahnSeries.coeff_mk` idx 2: necessary (f = indicator of ℕ ⊆ Surreal: small support, not well-founded for >)
theorem w3_34 : ¬ indep0% SurrealHahnSeries.coeff_mk 2 := fun h => natInd_notWF (h natInd natInd_small)
-- `SurrealHahnSeries.support_mk` idx 1: necessary (f = indicator of the negated ordinals: support well-founded for >, not small)
theorem w3_35 : ¬ indep0% SurrealHahnSeries.support_mk 1 := fun h => ordInd_notSmall (h ordInd ordInd_wf)
-- `SurrealHahnSeries.support_mk` idx 2: necessary (f = indicator of ℕ ⊆ Surreal: small support, not well-founded for >)
theorem w3_36 : ¬ indep0% SurrealHahnSeries.support_mk 2 := fun h => natInd_notWF (h natInd natInd_small)
-- `SurrealHahnSeries.ext` idx 2: necessary (x = 0, y = 1)
theorem w3_37 : ¬ drop0% SurrealHahnSeries.ext 2 := fun h => zero_ne_one (@h 0 1)
-- `SurrealHahnSeries.coeff_single_of_ne` idx 2: necessary (x = y = 0, r = 1)
theorem w3_38 : ¬ drop0% SurrealHahnSeries.coeff_single_of_ne 2 := fun h => by
  have := @h 0 0 1; rw [coeff_single_self] at this; exact one_ne_zero this
-- `SurrealHahnSeries.coeff_trunc_of_lt` idx 3: necessary (x = 1, i = j = 0)
theorem w3_39 : ¬ drop0% SurrealHahnSeries.coeff_trunc_of_lt 3 := fun h => by
  have := @h 1 0 0; rw [coeff_trunc_of_ge le_rfl] at this; simp at this
-- `SurrealHahnSeries.coeff_trunc_of_ge` idx 3: necessary (x = 1, i = -1, j = 0)
theorem w3_40 : ¬ drop0% SurrealHahnSeries.coeff_trunc_of_ge 3 := fun h => by
  have := @h 1 (-1) 0; rw [coeff_trunc_of_lt neg_one_lt_zero] at this; simp at this
-- `SurrealHahnSeries.coeff_trunc_eq_zero` idx 3: necessary (x = 1, i = 0, j = -1)
theorem w3_41 : ¬ drop0% SurrealHahnSeries.coeff_trunc_eq_zero 3 := fun h => by
  have := @h 1 0 (-1); rw [coeff_trunc_of_lt neg_one_lt_zero] at this; simp at this
-- `SurrealHahnSeries.coeff_trunc_of_mem` idx 3: necessary (x = 1, i = j = 0)
theorem w3_42 : ¬ drop0% SurrealHahnSeries.coeff_trunc_of_mem 3 := fun h => by
  have := @h 1 0 0; rw [coeff_trunc_of_ge le_rfl] at this; simp at this
-- `SurrealHahnSeries.trunc_single_of_ge` idx 3: necessary (i = 0, j = -1, r = 1)
theorem w3_43 : ¬ drop0% SurrealHahnSeries.trunc_single_of_ge 3 := fun h => by
  have := congrArg (coeff · 0) (@h 0 (-1) 1)
  simp only [coeff_trunc_of_lt neg_one_lt_zero, coeff_single_self, coeff_zero] at this; simp at this
-- `SurrealHahnSeries.trunc_single_of_lt` idx 3: necessary (i = j = 0, r = 1)
theorem w3_44 : ¬ drop0% SurrealHahnSeries.trunc_single_of_lt 3 := fun h => by
  have := congrArg (coeff · 0) (@h 0 0 1)
  simp only [coeff_trunc_of_ge le_rfl, coeff_single_self] at this; simp at this
-- `SurrealHahnSeries.trunc_eq_self` idx 2: necessary (x = 1, i = 0)
theorem w3_45 : ¬ drop0% SurrealHahnSeries.trunc_eq_self 2 := fun h => by
  have := congrArg (coeff · 0) (@h 1 0)
  simp only [coeff_trunc_of_ge le_rfl] at this; simp at this
-- `SurrealHahnSeries.trunc_eq_trunc` idx 3: necessary (x = 1, i = 0, j = -1 (H vacuous))
theorem w3_46 : ¬ drop0% SurrealHahnSeries.trunc_eq_trunc 3 := fun h => by
  have := congrArg (coeff · 0) (@h 1 0 (-1) (fun k hk hk' => absurd (hk.trans_le hk') (by norm_num)))
  simp only [coeff_trunc_of_ge le_rfl, coeff_trunc_of_lt neg_one_lt_zero] at this; simp at this
-- `SurrealHahnSeries.trunc_eq_trunc` idx 4: necessary (x = 1, i = -1, j = 0)
theorem w3_47 : ¬ drop0% SurrealHahnSeries.trunc_eq_trunc 4 := fun h => by
  have := congrArg (coeff · 0) (@h 1 (-1) 0 (by norm_num))
  simp only [coeff_trunc_of_ge le_rfl, coeff_trunc_of_lt neg_one_lt_zero] at this; simp at this
-- `SurrealHahnSeries.trunc_add_single` idx 2: necessary (x = 1, i = 1)
theorem w3_48 : ¬ drop0% SurrealHahnSeries.trunc_add_single 2 := fun h => by
  have := congrArg (coeff · 0) (@h 1 1)
  simp only [coeff_add_apply, coeff_trunc_of_ge zero_le_one, coeff_single_of_ne one_ne_zero] at this
  simp at this
-- `SurrealHahnSeries.length_mono` idx 2: necessary (x = 1, y = 0)
theorem w3_49 : ¬ drop0% SurrealHahnSeries.length_mono 2 := fun h =>
  one_len_pos.not_ge (by simpa using @h 1 0)
-- `SurrealHahnSeries.eq_exp_of_mem_support` idx 2: necessary (x = 0 (no exponents), i = 0)
theorem w3_50 : ¬ drop0% SurrealHahnSeries.eq_exp_of_mem_support 2 := fun h => by
  obtain ⟨j, _⟩ := @h 0 0
  have := j.2; simp at this
-- `SurrealHahnSeries.exp_congr` idx 2: necessary (x = 1, y = 0)
theorem w3_51 : ¬ indep0% SurrealHahnSeries.exp_congr 2 := fun h => one_ne_zero (@h 1 0 ⟨0, one_len_pos⟩)
-- `SurrealHahnSeries.coeffIdx_of_ge` idx 2: necessary (x = 1, i = 0)
theorem w3_52 : ¬ drop0% SurrealHahnSeries.coeffIdx_of_ge 2 := fun h =>
  one_len_pos.not_ge (coeffIdx_eq_zero_iff.1 (@h 1 0))
-- `SurrealHahnSeries.truncIdx_of_ge` idx 2: necessary (x = 1, i = 0)
theorem w3_53 : ¬ drop0% SurrealHahnSeries.truncIdx_of_ge 2 := fun h =>
  one_len_pos.not_ge (truncIdx_eq_self_iff.1 (@h 1 0))
-- `SurrealHahnSeries.support_truncIdx_ssubset` idx 2: necessary (x = 0)
theorem w3_54 : ¬ drop0% SurrealHahnSeries.support_truncIdx_ssubset 2 := fun h => by
  have := @h 0 0; simp at this
-- `SurrealHahnSeries.length_trunc_lt` idx 2: necessary (x = 0)
theorem w3_55 : ¬ drop0% SurrealHahnSeries.length_trunc_lt 2 := fun h => by
  have := @h 0 0; simp at this
-- `SurrealHahnSeries.truncIdx_ne` idx 2: necessary (x = 0)
theorem w3_56 : ¬ drop0% SurrealHahnSeries.truncIdx_ne 2 := fun h => by
  have := @h 0 0; simp at this
-- `SurrealHahnSeries.coeff_truncIdx_of_lt` idx 4: necessary (x = 1, i = 0, j = first exponent)
theorem w3_57 : ¬ drop0% SurrealHahnSeries.coeff_truncIdx_of_lt 4 := fun h => by
  have := @h 1 0 ((1 : SurrealHahnSeries.{0}).exp ⟨(0 : Ordinal.{0}), one_len_pos⟩) one_len_pos
  rw [truncIdx_of_lt one_len_pos, coeff_trunc_of_ge le_rfl, coeff_exp] at this
  exact coeffIdx_ne one_len_pos this.symm
-- `SurrealHahnSeries.coeff_truncIdx_of_ge` idx 4: necessary (x of length 2, i = 1, j = first exponent)
theorem w3_58 : ¬ drop0% SurrealHahnSeries.coeff_truncIdx_of_ge 4 := fun h => by
  have := @h X2 1 e0 X2_1
  rw [trunc1, coeff_trunc_of_lt e10] at this
  exact c0 this
-- `SurrealHahnSeries.coeff_truncIdx_of_mem` idx 5: necessary (x = 1, i = 0, j = k = first exponent)
theorem w3_59 : ¬ drop0% SurrealHahnSeries.coeff_truncIdx_of_mem 5 := fun h => by
  have := @h 1 0 _ ((1 : SurrealHahnSeries.{0}).exp ⟨(0 : Ordinal.{0}), one_len_pos⟩) le_rfl
  rw [truncIdx_of_lt one_len_pos, coeff_trunc_of_ge le_rfl, coeff_exp] at this
  exact coeffIdx_ne one_len_pos this.symm
-- `SurrealHahnSeries.coeff_truncIdx_of_mem` idx 4: necessary (x of length 2, i = 1, j = first, k = second exponent)
theorem w3_60 : ¬ drop0% SurrealHahnSeries.coeff_truncIdx_of_mem 4 := fun h => by
  have := @h X2 1 e0 e1 (by rw [mem_support_iff, trunc1, coeff_trunc_of_lt e10]; exact c0)
  rw [trunc1, coeff_trunc_of_ge le_rfl] at this
  exact c1 this.symm
-- `SurrealHahnSeries.trunc_truncIdx_of_mem` idx 4: necessary (x of length 2, i = 1, a = first exponent, b = second exponent - 1)
theorem w3_61 : ¬ drop0% SurrealHahnSeries.trunc_truncIdx_of_mem 4 := fun h => by
  have := congrArg (coeff · (e1 : Surreal)) (@h X2 1 e0 (e1 - 1) (by rw [mem_support_iff, trunc1, coeff_trunc_of_lt e10]; exact c0))
  simp only [coeff_trunc_of_lt (sub_one_lt (e1 : Surreal)), trunc1, coeff_trunc_of_ge le_rfl] at this
  exact c1 this.symm
-- `SurrealHahnSeries.trunc_truncIdx_of_mem` idx 5: necessary (x of length 2, i = 1, a = b = second exponent - 1)
theorem w3_62 : ¬ drop0% SurrealHahnSeries.trunc_truncIdx_of_mem 5 := fun h => by
  have := congrArg (coeff · (e1 : Surreal)) (@h X2 1 (e1 - 1) (e1 - 1) le_rfl)
  simp only [coeff_trunc_of_lt (sub_one_lt (e1 : Surreal)), trunc1, coeff_trunc_of_ge le_rfl] at this
  exact c1 this.symm
-- `SurrealHahnSeries.term_of_ge` idx 2: necessary (x = 1, i = 0)
theorem w3_63 : ¬ drop0% SurrealHahnSeries.term_of_ge 2 := fun h =>
  one_len_pos.not_ge (term_eq_zero.1 (@h 1 0))

-- TermSeq
theorem s1lt : (0 : Ordinal.{0}) < (seqG 1 1 one_ne_zero 0).length := zero_lt_one
-- `SurrealHahnSeries.TermSeq.ext` idx 2: necessary (s = 0, t of length 1)
theorem w3_64 : ¬ drop0% SurrealHahnSeries.TermSeq.ext 2 := fun h => by
  have := congrArg TermSeq.length (@h 0 (seqG 1 1 one_ne_zero 0) (fun i hs _ => by simp at hs) (fun i hs _ => by simp at hs))
  simp [seqG] at this
-- `SurrealHahnSeries.TermSeq.ext` idx 3: necessary (length 1, same coefficient, exponents 0 and 1)
theorem w3_65 : ¬ drop0% SurrealHahnSeries.TermSeq.ext 3 := fun h => by
  have := @h (seqG 1 1 one_ne_zero 0) (seqG 1 1 one_ne_zero 1) rfl (fun _ _ _ => rfl)
  have := congrArg (fun s : TermSeq => (s : SurrealHahnSeries).coeff (0 - NatOrdinal.toSurreal (NatOrdinal.of 0))) this
  rw [show (0 : Surreal) - NatOrdinal.toSurreal (NatOrdinal.of 0) = (seqG 1 1 one_ne_zero 0).exp ⟨0, s1lt⟩ from rfl,
    TermSeq.coeff_coe, TermSeq.coeff_coe_of_notMem] at this
  · exact one_ne_zero this
  · rintro ⟨i, hi⟩
    simp only [seqG] at hi
    have hi0 : (i : Ordinal.{0}) = 0 := Order.lt_one_iff.1 i.2
    rw [hi0, sub_left_inj] at hi; exact one_ne_zero hi
-- `SurrealHahnSeries.TermSeq.ext` idx 4: necessary (length 1, same exponent, coefficients 1 and 2)
theorem w3_66 : ¬ drop0% SurrealHahnSeries.TermSeq.ext 4 := fun h => by
  have := @h (seqG 1 1 one_ne_zero 0) (seqG 1 2 two_ne_zero 0) rfl (fun _ _ _ => rfl)
  have := congrArg (fun s : TermSeq => (s : SurrealHahnSeries).coeff (0 - NatOrdinal.toSurreal (NatOrdinal.of 0))) this
  rw [show (0 : Surreal) - NatOrdinal.toSurreal (NatOrdinal.of 0) = (seqG 1 1 one_ne_zero 0).exp ⟨0, s1lt⟩ from rfl,
    TermSeq.coeff_coe] at this
  rw [show (seqG 1 1 one_ne_zero 0).exp ⟨0, s1lt⟩ = (seqG 1 2 two_ne_zero 0).exp ⟨0, s1lt⟩ from rfl, TermSeq.coeff_coe] at this
  exact absurd this (by show (1:ℝ) ≠ 2; norm_num)
-- `SurrealHahnSeries.TermSeq.coeff_coe_of_notMem` idx 2: necessary (s of length 1, x = its exponent)
theorem w3_67 : ¬ drop0% SurrealHahnSeries.TermSeq.coeff_coe_of_notMem 2 := fun h => by
  have := @h (seqG 1 1 one_ne_zero 0) ((seqG 1 1 one_ne_zero 0).exp ⟨0, s1lt⟩)
  rw [TermSeq.coeff_coe] at this; exact one_ne_zero this
-- `SurrealHahnSeries.TermSeq.coeffIdx_coe_of_ge` idx 2: necessary (s of length 1, i = 0)
theorem w3_68 : ¬ drop0% SurrealHahnSeries.TermSeq.coeffIdx_coe_of_ge 2 := fun h => by
  have := @h (seqG 1 1 one_ne_zero 0) 0
  rw [TermSeq.coeffIdx_coe_of_lt s1lt] at this; exact one_ne_zero this
-- `SurrealHahnSeries.TermSeq.term_coe_of_ge` idx 2: necessary (s of length 1, i = 0)
theorem w3_69 : ¬ drop0% SurrealHahnSeries.TermSeq.term_coe_of_ge 2 := fun h => by
  have := term_eq_zero.1 (@h (seqG 1 1 one_ne_zero 0) 0)
  rw [TermSeq.length_coe] at this; exact s1lt.not_ge this

-- misc
-- `Set.IsWF.to_subtype` idx 3: necessary (α = Unit with < always true, s = univ)
theorem w3_70 : ¬ drop0% Set.IsWF.to_subtype 3 := fun h => by
  have hw : WellFounded (fun a b : (Set.univ : Set Unit) => True) := by
    have := @h Unit ⟨fun _ _ => True⟩ Set.univ
    first | exact this.wf | exact this | exact this.1
  exact hw.induction (C := fun _ => False) ⟨(), trivial⟩ (fun y ih => ih y trivial)
-- `instSubsingletonRelIsoOfIsWellOrder_combinatorialGames` idx 4: necessary (α = β = Bool, r = s = empty relation: id and not are distinct isos)
theorem w3_71 : ¬ drop0% instSubsingletonRelIsoOfIsWellOrder_combinatorialGames 4 := fun h => by
  have := (@h Bool Bool (fun _ _ => False) (fun _ _ => False)).elim (RelIso.refl _)
    ⟨⟨not, not, Bool.not_not, Bool.not_not⟩, Iff.rfl⟩
  have := congrArg (fun e => e true) this
  simp at this

-- Leading
-- `_private.CombinatorialGames.Surreal.Leading.0.Surreal.stdPart_eq'` idx 3: necessary (x = y = 0, r = 1)
theorem w3_72 : ¬ drop0% _private.CombinatorialGames.Surreal.Leading.«0».Surreal.stdPart_eq' 3 := fun h => by
  have := @h 0 0 1 (fun s hs => mul_nonneg (by exact_mod_cast (zero_lt_one.trans hs).le) (Surreal.wpow_pos _).le)
  simp at this
-- `_private.CombinatorialGames.Surreal.Leading.0.Surreal.stdPart_eq'` idx 4: necessary (x = y = 0, r = -1)
theorem w3_73 : ¬ drop0% _private.CombinatorialGames.Surreal.Leading.«0».Surreal.stdPart_eq' 4 := fun h => by
  have := @h 0 0 (-1) (fun s hs => mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (hs.trans (by norm_num : (-1:ℝ) < 0)).le) (Surreal.wpow_pos _).le)
  simp at this
-- `Surreal.wlog_eq` idx 3: necessary (x = 0, y = 1, r = 0)
theorem w3_74 : ¬ drop0% Surreal.wlog_eq 3 := fun h => by
  have := @h 0 1 0 (fun s hs => mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hs.le) (Surreal.wpow_pos _).le)
    (fun s hs => mul_nonneg (by exact_mod_cast hs.le) (Surreal.wpow_pos _).le)
  rw [Surreal.wlog_zero] at this; exact zero_ne_one this
-- `Surreal.wlog_eq` idx 5: necessary (x = 0, y = 1, r = -1)
theorem w3_75 : ¬ drop0% Surreal.wlog_eq 5 := fun h => by
  have := @h 0 1 (-1) (by norm_num) (fun s hs => mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (hs.trans (by norm_num : (-1:ℝ) < 0)).le) (Surreal.wpow_pos _).le)
  rw [Surreal.wlog_zero] at this; exact zero_ne_one this
-- `Surreal.leadingCoeff_eq` idx 3: necessary (x = ω^0, y = 1, r = 0)
theorem w3_76 : ¬ drop0% Surreal.leadingCoeff_eq 3 := fun h => by
  have := @h (ω^ (0 : Surreal)) 1 0
    (fun s hs => (mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hs.le) (Surreal.wpow_pos _).le).trans (Surreal.wpow_pos _).le)
    (fun s hs => (Surreal.wpow_lt_mul_wpow hs zero_lt_one).le)
  simp at this
-- `Surreal.leadingCoeff_eq` idx 4: necessary (x = y = 0, r = 1)
theorem w3_77 : ¬ drop0% Surreal.leadingCoeff_eq 4 := fun h => by
  have := @h 0 0 1 one_ne_zero (fun s hs => mul_nonneg (by exact_mod_cast (zero_lt_one.trans hs).le) (Surreal.wpow_pos _).le)
  simp at this
-- `Surreal.leadingCoeff_eq` idx 5: necessary (x = y = 0, r = -1)
theorem w3_78 : ¬ drop0% Surreal.leadingCoeff_eq 5 := fun h => by
  have := @h 0 0 (-1) (by norm_num) (fun s hs => mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (hs.trans (by norm_num : (-1:ℝ) < 0)).le) (Surreal.wpow_pos _).le)
  simp at this
-- `Surreal.leadingTerm_eq` idx 3: necessary (x = ω^0, y = 1, r = 0)
theorem w3_79 : ¬ drop0% Surreal.leadingTerm_eq 3 := fun h => by
  have := @h (ω^ (0 : Surreal)) 1 0
    (fun s hs => (mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hs.le) (Surreal.wpow_pos _).le).trans (Surreal.wpow_pos _).le)
    (fun s hs => (Surreal.wpow_lt_mul_wpow hs zero_lt_one).le)
  simp at this
-- `Surreal.leadingTerm_eq` idx 4: necessary (x = y = 0, r = 1)
theorem w3_80 : ¬ drop0% Surreal.leadingTerm_eq 4 := fun h => by
  have := @h 0 0 1 one_ne_zero (fun s hs => mul_nonneg (by exact_mod_cast (zero_lt_one.trans hs).le) (Surreal.wpow_pos _).le)
  simp at this
-- `Surreal.leadingTerm_eq` idx 5: necessary (x = y = 0, r = -1)
theorem w3_81 : ¬ drop0% Surreal.leadingTerm_eq 5 := fun h => by
  have := @h 0 0 (-1) (by norm_num) (fun s hs => mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (hs.trans (by norm_num : (-1:ℝ) < 0)).le) (Surreal.wpow_pos _).le)
  simp at this
end

end W3c0
