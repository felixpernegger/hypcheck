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

namespace W2c3
open SignExpansion

-- helper: top sign expansion is not small
theorem topNS : ¬ (⊤ : SignExpansion.{0}).Small := by
  rw [small_iff_length_ne_top, length_top]; exact fun h => h rfl

-- helper: function zero at 0 and s elsewhere
noncomputable def g (s : SignType) : NatOrdinal.{0} → SignType := fun b => if b = 0 then 0 else s

theorem g_zero (s : SignType) : g s 0 = 0 := by simp [g]

theorem g_ne (s : SignType) {b : NatOrdinal.{0}} (hb : b ≠ 0) : g s b = s := by simp [g, hb]

theorem gNot {s : SignType} (hs : s ≠ 0) : ¬ IsUpperSet (g s ⁻¹' {0}) := by
  intro h
  have := @h 0 1 zero_le (by simp [g])
  simp [g] at this
  exact hs this

theorem g_sInf (s : SignType) : sInf (g s ⁻¹' {0}) = 0 :=
  le_antisymm (csInf_le' (by simp [g])) zero_le

theorem g_next {s : SignType} : g s (sInf {b | sInf (g s ⁻¹' {0}) < b ∧ g s b ≠ 0}) = s := by
  by_cases hs : s = 0
  · subst hs; simp [g]
  have hne : ({b | sInf (g s ⁻¹' {0}) < b ∧ g s b ≠ 0} : Set NatOrdinal.{0}).Nonempty :=
    ⟨1, by rw [g_sInf]; exact ⟨zero_lt_one, by rw [g_ne s one_ne_zero]; exact hs⟩⟩
  have hm := csInf_mem hne
  apply g_ne
  have := hm.1
  rw [g_sInf] at this
  simp only [g_sInf]
  exact this.ne'

-- helper: sInf of the empty set of ordinals
theorem sInfE : sInf (∅ : Set NatOrdinal.{0}) = 0 := Ordinal.sInf_empty

-- helper: the one-sign expansion +
noncomputable abbrev pl : SignExpansion.{0} := NatOrdinal.toSignExpansion 1

theorem pl0 : pl 0 = 1 := NatOrdinal.toSignExpansion_apply_of_lt zero_lt_one

theorem pl1 : pl 1 = 0 := NatOrdinal.toSignExpansion_apply_of_le le_rfl

end W2c3

open SignExpansion W2c3

-- `Pi.Lex.neg_le_neg_iff`
theorem c_1 : drop% Pi.Lex.neg_le_neg_iff 2 := by
  intro α _ x y
  simp only [le_iff_lt_or_eq]
  exact or_congr Pi.Lex.neg_lt_neg_iff (by rw [neg_inj, eq_comm])

-- `Pi.Lex.neg_le_iff`
theorem c_2 : drop% Pi.Lex.neg_le_iff 2 := by
  intro α _ x y
  simpa using c_1 (x := x) (y := -y)

-- `Pi.Lex.le_neg_iff`
theorem c_3 : drop% Pi.Lex.le_neg_iff 2 := by
  intro α _ x y
  simpa using c_1 (x := -x) (y := y)

-- `SignExpansion.coe_mk`
theorem c_4 : ¬ indep0% SignExpansion.coe_mk 1 := fun h => gNot one_ne_zero (h (g 1))

-- `SignExpansion.ext`
theorem c_5 : ¬ drop0% SignExpansion.ext 2 := fun h => by
  have := congrArg (fun x : SignExpansion.{0} => x 0) (@h 0 ⊤)
  simp at this

-- `SignExpansion.mk_eq_mk`
theorem c_6 : ¬ indep0% SignExpansion.mk_eq_mk 2 := fun h =>
  gNot one_ne_zero (@h (g 1) ⇑(0 : SignExpansion.{0}) (0 : SignExpansion.{0}).2)

-- `SignExpansion.mk_eq_mk`
theorem c_7 : ¬ indep0% SignExpansion.mk_eq_mk 3 := fun h =>
  gNot one_ne_zero (@h ⇑(0 : SignExpansion.{0}) (g 1) (0 : SignExpansion.{0}).2)

-- `SignExpansion.apply_eq_zero_of_le`
theorem c_8 : ¬ drop0% SignExpansion.apply_eq_zero_of_le 3 := fun h => by
  have := @h pl 1 0 pl1
  rw [pl0] at this; exact one_ne_zero this

-- `SignExpansion.Small.coe_length`
theorem c_9 : ¬ indep0% SignExpansion.Small.coe_length 1 := fun h => topNS (h ⊤)

-- `SignExpansion.Small.length_eq`
theorem c_10 : indep% SignExpansion.Small.length_eq 1 := by
  intro x o ho
  exact small_iff_length_ne_top.2 (by rw [ho]; exact WithTop.coe_ne_top)

-- `SignExpansion.Small.length_eq`
theorem c_11 : ¬ drop0% SignExpansion.Small.length_eq 3 := fun h => by
  have := Small.zero
  have h1 := @h 0 Small.zero 1
  have h0 := Small.length_eq (x := (0 : SignExpansion.{0})) (o := 0) (by simp)
  rw [h0] at h1; exact zero_ne_one h1

-- `SignExpansion.neg_mk`
theorem c_12 : ¬ indep0% SignExpansion.neg_mk 1 := fun h => gNot one_ne_zero (h (g 1))

-- `SignExpansion.Small.neg`
theorem c_13 : ¬ drop0% SignExpansion.Small.neg 1 := fun h => topNS (by simpa using h ⊥)

-- `SignExpansion.Small.length_neg`
theorem c_14 : ¬ indep0% SignExpansion.Small.length_neg 1 := fun h => topNS (h ⊤)

-- `SignExpansion.trunc_apply_of_coe_lt`
theorem c_15 : ¬ drop0% SignExpansion.trunc_apply_of_coe_lt 3 := fun h => by
  have := @h ⊤ 0 0
  simp at this

-- `SignExpansion.trunc_apply_of_le_coe`
theorem c_16 : ¬ drop0% SignExpansion.trunc_apply_of_le_coe 3 := fun h => by
  have := @h ⊤ ⊤ 0
  simp at this

-- `SignExpansion.trunc_of_length_le`
theorem c_17 : ¬ drop0% SignExpansion.trunc_of_length_le 2 := fun h => by
  have := congrArg (fun x : SignExpansion.{0} => x 0) (@h ⊤ 0)
  simp at this

-- `_private.CombinatorialGames.SignExpansion.Basic.0.SignExpansion.floor_of_eq_neg_one`
theorem c_18 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Basic.«0».SignExpansion.floor_of_eq_neg_one 1 := fun h => by
  have := @h ⇑(⊥ : SignExpansion.{0}) (by simp) 1
  have he : (⇑(⊥ : SignExpansion.{0})) ⁻¹' {0} = ∅ := by ext; simp
  rw [floor_coe, he, sInfE] at this
  simp at this

-- `_private.CombinatorialGames.SignExpansion.Basic.0.SignExpansion.floor_of_eq_neg_one`
theorem c_19 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Basic.«0».SignExpansion.floor_of_eq_neg_one 2 := fun h => by
  have h1 := @h (g 1) (gNot one_ne_zero) 0
  have h2 := (priv% _private.CombinatorialGames.SignExpansion.Basic.«0».SignExpansion.floor_of_eq_one) (gNot one_ne_zero) g_next 0
  rw [h1] at h2
  simp [g_sInf] at h2

-- `_private.CombinatorialGames.SignExpansion.Basic.0.SignExpansion.floor_of_eq_one`
theorem c_20 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Basic.«0».SignExpansion.floor_of_eq_one 1 := fun h => by
  have := @h ⇑(⊤ : SignExpansion.{0}) (by simp) 0
  have he : (⇑(⊤ : SignExpansion.{0})) ⁻¹' {0} = ∅ := by ext; simp
  rw [floor_coe, he, sInfE] at this
  simp at this

-- `_private.CombinatorialGames.SignExpansion.Basic.0.SignExpansion.floor_of_eq_one`
theorem c_21 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Basic.«0».SignExpansion.floor_of_eq_one 2 := fun h => by
  have h1 := @h (g (-1)) (gNot (by decide)) 0
  have h2 := (priv% _private.CombinatorialGames.SignExpansion.Basic.«0».SignExpansion.floor_of_eq_neg_one) (gNot (by decide)) g_next 0
  rw [h1] at h2
  simp [g_sInf] at h2

-- `SignExpansion.floor_of_isUpperSet`
theorem c_22 : ¬ indep0% SignExpansion.floor_of_isUpperSet 1 := fun h => gNot one_ne_zero (@h (g 1))

-- `SignExpansion.floor_apply_of_lt_sInf`
theorem c_23 : ¬ drop0% SignExpansion.floor_apply_of_lt_sInf 2 := fun h => by
  have hf : ⇑(floor (g 1)) = g 1 := funext fun a => @h (g 1) a
  exact gNot one_ne_zero (hf ▸ (floor (g 1)).2)

-- `SignExpansion.ceil_of_isUpperSet`
theorem c_24 : ¬ indep0% SignExpansion.ceil_of_isUpperSet 1 := fun h => gNot one_ne_zero (@h (g 1))

-- `SignExpansion.lt_ceil_of_not_isUpperSet`
theorem c_25 : ¬ drop0% SignExpansion.lt_ceil_of_not_isUpperSet 1 := fun h => by
  have := @h ⇑(0 : SignExpansion.{0})
  rw [ceil_coe] at this
  exact lt_irrefl _ this
-- `_private.CombinatorialGames.SignExpansion.Basic.0.SignExpansion.succFun_ne_zero`
theorem c_26 : ¬ indep0% _private.CombinatorialGames.SignExpansion.Basic.«0».SignExpansion.succFun_ne_zero 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.coe_succ`
theorem c_27 : ¬ indep0% SignExpansion.coe_succ 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.succ_apply_ne_zero`
theorem c_28 : ¬ indep0% SignExpansion.succ_apply_ne_zero 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.length_succ`
theorem c_29 : ¬ indep0% SignExpansion.length_succ 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.succ_apply_of_lt`
theorem c_30 : ¬ indep0% SignExpansion.succ_apply_of_lt 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.succ_apply_smallLength`
theorem c_31 : ¬ indep0% SignExpansion.succ_apply_smallLength 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.lt_succ`
theorem c_32 : ¬ indep0% SignExpansion.lt_succ 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.apply_lt_succ_apply_iff`
theorem c_33 : ¬ indep0% SignExpansion.apply_lt_succ_apply_iff 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.succ_apply_lt_apply_iff`
theorem c_34 : ¬ indep0% SignExpansion.succ_apply_lt_apply_iff 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.succ_apply_eq_apply_iff`
theorem c_35 : ¬ indep0% SignExpansion.succ_apply_eq_apply_iff 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.succ_apply_ne_apply_iff`
theorem c_36 : ¬ indep0% SignExpansion.succ_apply_ne_apply_iff 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.apply_le_succ_apply_iff`
theorem c_37 : ¬ indep0% SignExpansion.apply_le_succ_apply_iff 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.succ_apply_le_apply_iff`
theorem c_38 : ¬ indep0% SignExpansion.succ_apply_le_apply_iff 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.covBy_succ`
theorem c_39 : ¬ indep0% SignExpansion.covBy_succ 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.coe_pred`
theorem c_40 : ¬ indep0% SignExpansion.coe_pred 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.pred_apply_ne_zero`
theorem c_41 : ¬ indep0% SignExpansion.pred_apply_ne_zero 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.length_pred`
theorem c_42 : ¬ indep0% SignExpansion.length_pred 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.pred_apply_of_lt`
theorem c_43 : ¬ indep0% SignExpansion.pred_apply_of_lt 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.pred_apply_smallLength`
theorem c_44 : ¬ indep0% SignExpansion.pred_apply_smallLength 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.pred_lt`
theorem c_45 : ¬ indep0% SignExpansion.pred_lt 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.pred_apply_lt_apply_iff`
theorem c_46 : ¬ indep0% SignExpansion.pred_apply_lt_apply_iff 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.pred_apply_eq_apply_iff`
theorem c_47 : ¬ indep0% SignExpansion.pred_apply_eq_apply_iff 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.pred_apply_le_apply_iff`
theorem c_48 : ¬ indep0% SignExpansion.pred_apply_le_apply_iff 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.apply_le_pred_apply_iff`
theorem c_49 : ¬ indep0% SignExpansion.apply_le_pred_apply_iff 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.pred_covBy`
theorem c_50 : ¬ indep0% SignExpansion.pred_covBy 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.succ_neg`
theorem c_51 : ¬ indep0% SignExpansion.succ_neg 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.pred_neg`
theorem c_52 : ¬ indep0% SignExpansion.pred_neg 1 := fun h =>
  topNS (by first | exact @h ⊤ | exact @h ⊤ 0 | exact @h ⊤ 0 (by simp))

-- `SignExpansion.succ_apply_of_gt`
theorem c_53 : indep% SignExpansion.succ_apply_of_gt 1 := by
  intro x o ho
  exact small_iff_length_ne_top.2 (ne_top_of_lt ho)

-- `SignExpansion.pred_apply_of_gt`
theorem c_54 : indep% SignExpansion.pred_apply_of_gt 1 := by
  intro x o ho
  exact small_iff_length_ne_top.2 (ne_top_of_lt ho)

-- `SignExpansion.pred_apply_of_eq`
theorem c_55 : indep% SignExpansion.pred_apply_of_eq 1 := by
  intro x o ho
  exact small_iff_length_ne_top.2 (by rw [ho]; exact WithTop.coe_ne_top)

-- `SignExpansion.succ_apply_of_eq`
theorem c_56 : ¬ drop0% SignExpansion.succ_apply_of_eq 3 := fun h => by
  have := Small.zero
  have h1 := @h 0 Small.zero 1
  rw [succ_apply_of_gt (by simp)] at h1
  exact absurd h1 (by decide)

-- `SignExpansion.succ_apply_of_gt`
theorem c_57 : ¬ drop0% SignExpansion.succ_apply_of_gt 3 := fun h => by
  have := Small.zero
  have h1 := @h 0 Small.zero 0
  rw [succ_apply_of_eq (by simp)] at h1
  exact absurd h1 (by decide)

-- `SignExpansion.pred_apply_of_eq`
theorem c_58 : ¬ drop0% SignExpansion.pred_apply_of_eq 3 := fun h => by
  have := Small.zero
  have h1 := @h 0 Small.zero 1
  have h2 := (apply_lt_pred_apply_iff (x := (0 : SignExpansion.{0})) (o := 1)).2 (by simp)
  rw [h1] at h2
  exact absurd h2 (by decide)

-- `SignExpansion.pred_apply_of_gt`
theorem c_59 : ¬ drop0% SignExpansion.pred_apply_of_gt 3 := fun h => by
  have := Small.zero
  have h1 := @h 0 Small.zero 0
  rw [succ_apply_of_eq (by simp)] at h1
  exact absurd h1 (by decide)

-- `NatOrdinal.toSignExpansion_apply_of_lt`
theorem c_60 : ¬ drop0% NatOrdinal.toSignExpansion_apply_of_lt 2 := fun h => by
  have h1 := @h 0 0
  rw [NatOrdinal.toSignExpansion_apply_of_le le_rfl] at h1
  exact absurd h1 (by decide)

-- `NatOrdinal.toSignExpansion_apply_of_le`
theorem c_61 : ¬ drop0% NatOrdinal.toSignExpansion_apply_of_le 2 := fun h => by
  have h1 := @h 1 0
  rw [NatOrdinal.toSignExpansion_apply_of_lt zero_lt_one] at h1
  exact absurd h1 (by decide)

namespace W2c3

-- helper: minus as a sign expansion
noncomputable abbrev mi : SignExpansion.{0} := -pl

theorem mi0 : mi 0 = -1 := by simp [mi, pl0]

-- helper: two simplicity elements that differ at 0 have no common upper bound
theorem nbS : ¬ BddAbove ({Simplicity.of pl, Simplicity.of mi} : Set Simplicity.{0}) := by
  rintro ⟨z, hz⟩
  have h1 := Simplicity.apply_eq_of_le (o := 0) (hz (Set.mem_insert _ _)) (by simp [pl0])
  have h2 := Simplicity.apply_eq_of_le (o := 0) (hz (Set.mem_insert_of_mem _ rfl)) (by simp [mi0])
  simp [pl0, mi0] at h1 h2
  rw [← h1] at h2; exact absurd h2 (by decide)

-- helper: of pl is not below of mi (and conversely)
theorem plmi : ¬ Simplicity.of pl ≤ Simplicity.of mi := fun h => by
  have := Simplicity.apply_eq_of_le (o := 0) h (by simp [pl0])
  simp [pl0, mi0] at this

theorem mipl : ¬ Simplicity.of mi ≤ Simplicity.of pl := fun h => by
  have := Simplicity.apply_eq_of_le (o := 0) h (by simp [mi0])
  simp [pl0, mi0] at this

-- helper: of top is not below bottom
theorem topbot : ¬ Simplicity.of (⊤ : SignExpansion.{0}) ≤ ⊥ := fun h => by
  have := Simplicity.apply_eq_of_le (o := 0) h (by simp)
  simp at this

theorem lenpl : pl.length = 1 := by simp [pl]

theorem lenmi : mi.length = 1 := by simp [mi, lenpl]

end W2c3

-- `_private.CombinatorialGames.SignExpansion.Simplicity.0.WithTop.isLUB_of_coe_preimage`
theorem c_62 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Simplicity.«0».WithTop.isLUB_of_coe_preimage 4 := fun h => by
  have := (@h Unit _ () {⊤} (by constructor <;> intro a _ <;> exact le_of_eq (Subsingleton.elim _ _))).1 rfl
  simp at this

-- `_private.CombinatorialGames.SignExpansion.Simplicity.0.WithTop.isGLB_sInf_of_nonempty`
theorem c_63 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Simplicity.«0».WithTop.isGLB_sInf_of_nonempty 3 := fun h => by
  have := (@h Bool _ ⟨fun _ => true⟩ {((false : Bool) : WithTop Bool)}).1 rfl
  classical
  change (dite _ _ _) ≤ _ at this
  split_ifs at this
  · simp at this
  · exact absurd this (by decide)

-- `Simplicity.ext`
theorem c_64 : ¬ drop0% Simplicity.ext 2 := fun h => topbot (le_of_eq (@h _ ⊥))

-- `Simplicity.le_trunc_of_le_of_length_le`
theorem c_65 : ¬ drop0% Simplicity.le_trunc_of_le_of_length_le 3 := fun h => by
  have H := @h (Simplicity.of ⊤) ⊥ ⊤ le_top
  have := Simplicity.apply_eq_of_le (o := 0) H (by simp)
  simp at this

-- `Simplicity.le_trunc_of_le_of_length_le`
theorem c_66 : ¬ drop0% Simplicity.le_trunc_of_le_of_length_le 4 := fun h => by
  have H := @h (Simplicity.of ⊤) (Simplicity.of ⊤) 0 le_rfl
  have := Simplicity.apply_eq_of_le (o := 0) H (by simp)
  simp at this

-- `Simplicity.apply_eq_of_le`
theorem c_67 : ¬ drop0% Simplicity.apply_eq_of_le 3 := fun h => by
  have := @h (Simplicity.of ⊤) ⊥ 0 (by simp)
  simp at this

-- `Simplicity.apply_eq_of_le`
theorem c_68 : ¬ drop0% Simplicity.apply_eq_of_le 4 := fun h => by
  have := @h ⊥ (Simplicity.of ⊤) 0 bot_le
  simp at this

-- `Simplicity.le_of_le_of_length_le`
theorem c_69 : ¬ drop0% Simplicity.le_of_le_of_length_le 3 := fun h =>
  plmi (@h _ _ (Simplicity.of mi) le_rfl (by simp [lenmi]))

-- `Simplicity.le_of_le_of_length_le`
theorem c_70 : ¬ drop0% Simplicity.le_of_le_of_length_le 4 := fun h =>
  plmi (@h _ _ (Simplicity.of pl) le_rfl (by simp [lenmi]))

-- `Simplicity.le_of_le_of_length_le`
theorem c_71 : ¬ drop0% Simplicity.le_of_le_of_length_le 5 := fun h => by
  have H := @h (Simplicity.of pl) ⊥ (Simplicity.of pl) le_rfl bot_le
  have := Simplicity.apply_eq_of_le (o := 0) H (by simp [pl0])
  simp [pl0] at this

-- `Simplicity.le_or_ge_of_le`
theorem c_72 : ¬ drop0% Simplicity.le_or_ge_of_le 3 := fun h =>
  (@h (Simplicity.of pl) (Simplicity.of mi) (Simplicity.of mi) le_rfl).elim plmi mipl

-- `Simplicity.le_or_ge_of_le`
theorem c_73 : ¬ drop0% Simplicity.le_or_ge_of_le 4 := fun h =>
  (@h (Simplicity.of pl) (Simplicity.of mi) (Simplicity.of pl) le_rfl).elim plmi mipl

-- `Simplicity.eq_or_length_lt_of_le`
theorem c_74 : ¬ drop0% Simplicity.eq_or_length_lt_of_le 2 := fun h => by
  rcases @h (Simplicity.of pl) ⊥ with H | H
  · have := congrArg (fun x : Simplicity.{0} => x 0) H
    simp [pl0] at this
  · simp [lenpl] at H

-- `_private.CombinatorialGames.SignExpansion.Simplicity.0.Simplicity.sInf_eq_of_mem`
theorem c_75 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Simplicity.«0».Simplicity.sInf_eq_of_mem 2 := fun h => by
  have H := @h ∅ (Simplicity.of ⊤)
  have := congrArg (fun x : Simplicity.{0} => x 0) H
  simp at this

-- `Simplicity.isGLB_sInf_of_nonempty`
theorem c_76 : ¬ drop0% Simplicity.isGLB_sInf_of_nonempty 1 := fun h => by
  have H := (@h ∅).2 (show Simplicity.of ⊤ ∈ lowerBounds ∅ by simp)
  rw [Simplicity.sInf_empty] at H
  exact topbot H

-- `_private.CombinatorialGames.SignExpansion.Simplicity.0.Simplicity.sSup_apply_of_mem`
theorem c_77 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Simplicity.«0».Simplicity.sSup_apply_of_mem 2 := fun h => by
  have H := @h (Simplicity.of pl) {Simplicity.of pl, Simplicity.of mi} (Set.mem_insert _ _) 0 (by simp [pl0])
  rw [Simplicity.sSup_of_not_bddAbove nbS] at H
  simp [pl0] at H

-- `_private.CombinatorialGames.SignExpansion.Simplicity.0.Simplicity.sSup_apply_of_mem`
theorem c_78 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Simplicity.«0».Simplicity.sSup_apply_of_mem 5 := fun h => by
  have hc : IsChain (· ≤ ·) ({⊥, Simplicity.of pl} : Set Simplicity.{0}) := IsChain.pair bot_le
  have H1 := @h ⊥ _ hc (Set.mem_insert _ _) 0
  have H2 := (priv% _private.CombinatorialGames.SignExpansion.Simplicity.«0».Simplicity.sSup_apply_of_mem) hc (Set.mem_insert_of_mem _ rfl) (o := 0) (by simp [pl0])
  rw [H1] at H2
  simp [pl0] at H2

-- `_private.CombinatorialGames.SignExpansion.Simplicity.0.Simplicity.exists_of_sSup_apply_ne_zero`
theorem c_79 : drop% _private.CombinatorialGames.SignExpansion.Simplicity.«0».Simplicity.exists_of_sSup_apply_ne_zero 1 := by
  intro s o ho
  by_cases hs : IsChain (· ≤ ·) s
  · exact (priv% _private.CombinatorialGames.SignExpansion.Simplicity.«0».Simplicity.exists_of_sSup_apply_ne_zero) hs ho
  · rw [Simplicity.sSup_of_not_bddAbove (by rwa [← Simplicity.isChain_iff_bddAbove])] at ho
    exact absurd (Simplicity.bot_apply o) ho

-- `_private.CombinatorialGames.SignExpansion.Simplicity.0.Simplicity.isLUB_sSup_of_isChain`
theorem c_80 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Simplicity.«0».Simplicity.isLUB_sSup_of_isChain 1 := fun h =>
  nbS (@h _).bddAbove

-- `Simplicity.isLUB_sSup_of_bddAbove`
theorem c_81 : ¬ drop0% Simplicity.isLUB_sSup_of_bddAbove 1 := fun h =>
  nbS (@h _).bddAbove

-- `Simplicity.sup_of_le_right`
theorem c_82 : ¬ drop0% Simplicity.sup_of_le_right 2 := fun h => by
  have H := @h (Simplicity.of pl) (Simplicity.of mi)
  rw [← Simplicity.sSup_pair, Simplicity.sSup_of_not_bddAbove nbS] at H
  have := congrArg (fun x : Simplicity.{0} => x 0) H
  simp [mi0] at this

-- `Simplicity.sup_of_le_left`
theorem c_83 : ¬ drop0% Simplicity.sup_of_le_left 2 := fun h => by
  have H := @h (Simplicity.of pl) (Simplicity.of mi)
  rw [← Simplicity.sSup_pair, Simplicity.sSup_of_not_bddAbove nbS] at H
  have := congrArg (fun x : Simplicity.{0} => x 0) H
  simp [pl0] at this

namespace W2c3

-- helper: ZMod 4 with the order -2 < -1 < 0 < 1 (translation is not monotone)
def M4 : Type := Fin 4

instance : AddCommGroup M4 := inferInstanceAs (AddCommGroup (Fin 4))

def m4f (a : M4) : ℤ := ![0, 1, -2, -1] (show Fin 4 from a)

theorem m4f_inj : Function.Injective m4f := by
  intro a b
  exact (by decide : ∀ a b : Fin 4, ![(0 : ℤ), 1, -2, -1] a = ![(0 : ℤ), 1, -2, -1] b → a = b) a b

instance : LinearOrder M4 := LinearOrder.lift' m4f m4f_inj

-- helper: truncation at 0 is 0
theorem tr0 (x : Surreal.{0}) : Surreal.trunc 0 x = 0 := by
  rw [← Surreal.birthday_eq_zero, Surreal.birthday_trunc]; simp

-- helper: a surreal with birthday below 1 is 0
theorem bz {z : Surreal.{0}} (h : z.birthday < 1) : z = 0 := by
  rw [← Surreal.birthday_eq_zero]
  exact Order.lt_one_iff.1 h

theorem tr1 {x : Surreal.{0}} (h : x.birthday ≤ 1) : Surreal.trunc 1 x = x :=
  Surreal.trunc_eq_self_iff.2 h

end W2c3

open W2c3

-- `sign_sub_eq_of_notMem_Icc`
theorem c_84 : ¬ drop0% sign_sub_eq_of_notMem_Icc 3 := fun h => by
  have := @h M4 _ _ (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (by decide) (fun hm => absurd hm.1 (by decide))
  revert this; decide

-- `_private.CombinatorialGames.SignExpansion.Surreal.0.Surreal.trunc_lt_of_lt`
theorem c_85 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Surreal.«0».Surreal.trunc_lt_of_lt 3 := fun h => by
  have := @h (-1) 0 0 (by simp)
  rw [tr0] at this; exact lt_irrefl _ this

-- `_private.CombinatorialGames.SignExpansion.Surreal.0.Surreal.trunc_lt_of_lt`
theorem c_86 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Surreal.«0».Surreal.trunc_lt_of_lt 4 := fun h => by
  have := @h 0 0 1 (by simp)
  rw [tr1 (by simp)] at this; exact lt_irrefl _ this

-- `_private.CombinatorialGames.SignExpansion.Surreal.0.Surreal.lt_trunc_of_lt`
theorem c_87 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Surreal.«0».Surreal.lt_trunc_of_lt 3 := fun h => by
  have := @h 1 0 0 (by simp)
  rw [tr0] at this; exact lt_irrefl _ this

-- `_private.CombinatorialGames.SignExpansion.Surreal.0.Surreal.lt_trunc_of_lt`
theorem c_88 : ¬ drop0% _private.CombinatorialGames.SignExpansion.Surreal.«0».Surreal.lt_trunc_of_lt 4 := fun h => by
  have := @h 0 0 1 (by simp)
  rw [tr1 (by simp)] at this; exact lt_irrefl _ this

-- `Surreal.trunc_lt_iff_lt`
theorem c_89 : ¬ drop0% Surreal.trunc_lt_iff_lt 3 := fun h => by
  have := (@h (-1) 0 0).2 (by simp)
  rw [tr0] at this; exact lt_irrefl _ this

-- `Surreal.trunc_le_iff_le`
theorem c_90 : ¬ drop0% Surreal.trunc_le_iff_le 3 := fun h => by
  have := (@h 1 0 0).1 (by rw [tr0])
  exact (not_le.2 zero_lt_one) this

-- `Surreal.le_trunc_iff_le`
theorem c_91 : ¬ drop0% Surreal.le_trunc_iff_le 3 := fun h => by
  have := (@h (-1) 0 0).1 (by rw [tr0])
  exact (not_le.2 neg_one_lt_zero) this

-- `Surreal.trunc_eq_of_birthday_le_of_forall_lt_gt_iff`
theorem c_92 : ¬ drop0% Surreal.trunc_eq_of_birthday_le_of_forall_lt_gt_iff 4 := fun h => by
  have := @h (-1) 0 1 (by simp) (fun z hz => by rw [bz hz]; simp)
  rw [tr1 (by simp)] at this; simp at this

-- `Surreal.trunc_eq_of_birthday_le_of_forall_lt_gt_iff`
theorem c_93 : ¬ drop0% Surreal.trunc_eq_of_birthday_le_of_forall_lt_gt_iff 5 := fun h => by
  have := @h 1 0 1 (by simp) (fun z hz => by rw [bz hz]; simp)
  rw [tr1 (by simp)] at this; simp at this

-- `Surreal.trunc_eq_of_birthday_le_of_forall_le_ge_iff`
theorem c_94 : ¬ drop0% Surreal.trunc_eq_of_birthday_le_of_forall_le_ge_iff 4 := fun h => by
  have := @h 1 0 1 (by simp) (fun z hz => by rw [bz hz]; simp)
  rw [tr1 (by simp)] at this; simp at this

-- `Surreal.trunc_eq_of_birthday_le_of_forall_le_ge_iff`
theorem c_95 : ¬ drop0% Surreal.trunc_eq_of_birthday_le_of_forall_le_ge_iff 5 := fun h => by
  have := @h (-1) 0 1 (by simp) (fun z hz => by rw [bz hz]; simp)
  rw [tr1 (by simp)] at this; simp at this
