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

namespace W1c5
open Order Cardinal

theorem notEtaEmpty {c : Cardinal.{0}} (hc : c ≠ 0) : ¬ IsEta c Empty := fun h => by
  have hc' : 0 < c := pos_iff_ne_zero.2 hc
  obtain ⟨z, -⟩ := h (s := ∅) (t := ∅) (by simpa using hc') (by simpa using hc') (by simp)
  exact z.elim

instance countQ : Countable ℚ :=
  Function.Injective.countable (f := fun q : ℚ => (q.num, q.den))
    (fun a b h => Rat.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
noncomputable instance encQ : Encodable ℚ := Encodable.ofCountable ℚ
theorem mkQ : #ℚ = aleph0 := Cardinal.mk_eq_aleph0 ℚ

theorem etaQ : IsEta aleph0 ℚ := IsEta.Rat.isEta_aleph0
theorem etaQQ : IsEta #ℚ ℚ := by rw [mkQ]; exact etaQ
theorem etaUU : IsEta #Unit Unit := by simpa using (IsEta.one : IsEta 1 Unit)

-- a well order on a countable type with a0 on top (type omega + 1)
noncomputable def phiG {α : Type} [Encodable α] [DecidableEq α] (a0 : α) (a : α) : WithTop ℕ :=
  if a = a0 then ⊤ else (Encodable.encode a : WithTop ℕ)

theorem phiG_inj {α : Type} [Encodable α] [DecidableEq α] (a0 : α) : Function.Injective (phiG a0) := by
  intro a b h; unfold phiG at h
  split_ifs at h with h1 h2 h2 <;> simp_all [Encodable.encode_injective.eq_iff]

def rG {α : Type} [Encodable α] [DecidableEq α] (a0 : α) : α → α → Prop := fun a b => phiG a0 a < phiG a0 b

instance rG_wo {α : Type} [Encodable α] [DecidableEq α] (a0 : α) : IsWellOrder α (rG a0) :=
  (RelEmbedding.preimage ⟨phiG a0, phiG_inj a0⟩ (· < ·)).isWellOrder

theorem rG_lt {α : Type} [Encodable α] [DecidableEq α] (a0 a : α) (ha : a ≠ a0) : rG a0 a a0 := by
  simp [rG, phiG, ha]

theorem rQ_card : aleph0 ≤ #{y : ℚ // rG 0 y 0} := by
  rw [← Cardinal.mk_nat]
  refine mk_le_of_injective (f := fun n : ℕ => (⟨(n : ℚ) + 1, rG_lt _ _ (by positivity)⟩ : {y : ℚ // rG 0 y 0})) ?_
  intro a b h; simpa using congrArg Subtype.val h

theorem rQ_hord : (#ℚ).ord ≠ Ordinal.type (rG (0 : ℚ)) := fun hord => by
  have := (priv% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.card_subtype_lt) hord (0 : ℚ)
  rw [mkQ] at this
  exact absurd rQ_card (not_le.2 this)

theorem hordFin {α : Type} [Fintype α] (r : α → α → Prop) [IsWellOrder α r] : (#α).ord = Ordinal.type r := by
  rw [Ordinal.type_fintype, Cardinal.mk_fintype, Cardinal.ord_natCast]

theorem notEtaUnit {c : Cardinal.{0}} (hc : 1 < c) : ¬ IsEta c Unit := fun h => by
  obtain ⟨z, -, hz⟩ := h (s := ∅) (t := {()}) (by simpa using hc.trans' zero_lt_one) (by simpa using hc) (by simp)
  exact lt_irrefl _ (hz () rfl)

theorem notEtaBoolUnit : ¬ IsEta #Bool Unit :=
  notEtaUnit (Cardinal.one_lt_iff_nontrivial.2 inferInstance)

theorem notEtaZ : ¬ IsEta aleph0 ℤ := fun h => by
  obtain ⟨z, h1, h2⟩ := h (s := {0}) (t := {1}) (by simp) (by simp) (by simp)
  have := h1 0 rfl; have := h2 1 rfl; omega

theorem noIsoNQ (e : ℕ ≃o ℚ) : False := by
  have h : e (e.symm (e 0 - 1)) < e 0 := by rw [e.apply_symm_apply]; linarith
  exact Nat.not_lt_zero _ (e.lt_iff_lt.1 h)

theorem noSurjNQ (F : ℕ → ℚ) (hm : StrictMono F) (hs : Function.Surjective F) : False := by
  obtain ⟨n, hn⟩ := hs (F 0 - 1)
  have : F n < F 0 := by rw [hn]; linarith
  exact Nat.not_lt_zero n (hm.lt_iff_lt.1 this)

theorem notDenseBool : ¬ DenselyOrdered Bool := fun h => by
  obtain ⟨a, h1, h2⟩ := h.dense false true (by decide)
  cases a <;> simp_all

theorem notNoMaxUnit : ¬ NoMaxOrder Unit := fun h => by
  obtain ⟨a, ha⟩ := h.exists_gt (); exact lt_irrefl _ ha

theorem notNoMinUnit : ¬ NoMinOrder Unit := fun h => by
  obtain ⟨a, ha⟩ := h.exists_lt (); exact lt_irrefl _ ha

theorem notInfUnit : ¬ Infinite Unit := fun h => not_finite Unit

theorem notSmallType : ¬ Small.{0} (Set.univ : Set Type) := by
  rw [small_univ_iff]; exact not_small_type.{0, 0}

theorem iSupN : ⨆ i : NatOrdinal.{0}, i = 0 := by
  rw [ciSup_of_not_bddAbove]
  · exact csSup_empty
  · rintro ⟨a, ha⟩; exact (Order.lt_succ a).not_ge (ha ⟨Order.succ a, rfl⟩)

theorem iSupNim : ⨆ i : Nimber.{0}, i = 0 := by
  rw [ciSup_of_not_bddAbove]
  · exact csSup_empty
  · rintro ⟨a, ha⟩; exact (Order.lt_succ a).not_ge (ha ⟨Order.succ a, rfl⟩)

theorem wtopSup (s : Set (WithTop NatOrdinal.{0})) (hs : ∀ a : NatOrdinal.{0}, (a : WithTop _) ∈ s) :
    ¬ sSup s < ⊤ := fun h => by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 h.ne
  have := le_sSup (hs (Order.succ a))
  rw [← ha] at this
  exact (Order.lt_succ a).not_ge (WithTop.coe_le_coe.1 this)

theorem one_lt_two_nim : (1 : Nimber.{0}) < Nimber.of 2 := Nimber.one_lt_of.2 one_lt_two

end W1c5
open W1c5 Order Cardinal

-- `Order.IsEta.dual`
theorem w5_1 : ¬ drop0% Order.IsEta.dual 3 := fun h => notEtaEmpty one_ne_zero (h (α := Empty) (c := 1))
-- `Order.IsEta.exists_between`
theorem w5_2 : ¬ drop0% Order.IsEta.exists_between 3 := fun h => by
  obtain ⟨z, -⟩ := h (α := Empty) (c := 1) (s := ∅) (t := ∅) (by simp) (by simp) (by simp)
  exact z.elim
-- `Order.IsEta.exists_between`
theorem w5_3 : ¬ drop0% Order.IsEta.exists_between 6 := fun h => by
  obtain ⟨z, hz, -⟩ := h etaQ (s := Set.univ) (t := ∅) (by simp [aleph0_pos]) (by simp)
  exact lt_irrefl z (hz z trivial)
-- `Order.IsEta.exists_between`
theorem w5_4 : ¬ drop0% Order.IsEta.exists_between 7 := fun h => by
  obtain ⟨z, -, hz⟩ := h etaQ (s := ∅) (t := Set.univ) (by simp [aleph0_pos]) (by simp)
  exact lt_irrefl z (hz z trivial)
-- `Order.IsEta.exists_between`
theorem w5_5 : ¬ drop0% Order.IsEta.exists_between 8 := fun h => by
  obtain ⟨z, h1, h2⟩ := h etaQ (s := {0}) (t := {0}) (by simp) (by simp)
  exact lt_asymm (h1 0 rfl) (h2 0 rfl)
-- `Order.IsEta.mono`
theorem w5_6 : ¬ drop0% Order.IsEta.mono 4 := fun h => notEtaEmpty one_ne_zero (h (α := Empty) (c := 1) le_rfl)
-- `Order.IsEta.mono`
theorem w5_7 : ¬ drop0% Order.IsEta.mono 5 := fun h =>
  notEtaEmpty one_ne_zero (h (α := Empty) (c := 0) (c' := 1) IsEta.zero)
-- `Order.IsEta.one`
theorem w5_8 : ¬ drop0% Order.IsEta.one 2 := fun h => notEtaEmpty one_ne_zero (h (α := Empty))
-- `Order.IsEta.nonempty`
theorem w5_9 : ¬ drop0% Order.IsEta.nonempty 3 := fun h =>
  (h (α := Empty) (c := 0) IsEta.zero).elim fun z => z.elim
-- `Order.IsEta.nonempty`
theorem w5_10 : ¬ drop0% Order.IsEta.nonempty 4 := fun h =>
  (h (α := Empty) (c := 1) one_ne_zero).elim fun z => z.elim
-- `Order.IsEta.denselyOrdered`
theorem w5_11 : ¬ drop0% Order.IsEta.denselyOrdered 3 := fun h =>
  notDenseBool (h (α := Bool) (c := 1) IsEta.one)
-- `Order.IsEta.denselyOrdered`
theorem w5_12 : ¬ drop0% Order.IsEta.denselyOrdered 4 := fun h =>
  notDenseBool (h (α := Bool) (c := 2) one_lt_two)
-- `Order.IsEta.noMaxOrder`
theorem w5_13 : ¬ drop0% Order.IsEta.noMaxOrder 3 := fun h =>
  notNoMaxUnit (h (α := Unit) (c := 1) IsEta.one)
-- `Order.IsEta.noMaxOrder`
theorem w5_14 : ¬ drop0% Order.IsEta.noMaxOrder 4 := fun h =>
  notNoMaxUnit (h (α := Unit) (c := 2) one_lt_two)
-- `Order.IsEta.noMinOrder`
theorem w5_15 : ¬ drop0% Order.IsEta.noMinOrder 3 := fun h =>
  notNoMinUnit (h (α := Unit) (c := 1) IsEta.one)
-- `Order.IsEta.noMinOrder`
theorem w5_16 : ¬ drop0% Order.IsEta.noMinOrder 4 := fun h =>
  notNoMinUnit (h (α := Unit) (c := 2) one_lt_two)
-- `Order.IsEta.infinite`
theorem w5_17 : ¬ drop0% Order.IsEta.infinite 3 := fun h =>
  notInfUnit (h (α := Unit) (c := 1) IsEta.one)
-- `Order.IsEta.infinite`
theorem w5_18 : ¬ drop0% Order.IsEta.infinite 4 := fun h =>
  notInfUnit (h (α := Unit) (c := 2) one_lt_two)
-- `Order.IsEta.infinite`: the order is nonempty by IsEta.nonempty
theorem w5_19 : drop% Order.IsEta.infinite 5 := fun hc h =>
  have := h.nonempty (zero_lt_one.trans hc).ne'
  h.infinite hc
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.of_isEta_iso`
theorem w5_20 : ¬ drop0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.of_isEta_iso 6 := fun h =>
  notEtaEmpty one_ne_zero (h (α := Empty) (β := Empty) (c := 1) (OrderIso.refl _))
-- `Order.IsEta.orderType_eq`
theorem w5_21 : ¬ drop0% Order.IsEta.orderType_eq 5 := fun h =>
  notEtaEmpty one_ne_zero ((h (α := Unit) (β := Empty) (c := 1)) ▸ (IsEta.one : IsEta 1 Unit))
-- `Order.IsEta.aleph0`
theorem w5_22 : ¬ drop0% Order.IsEta.aleph0 2 := fun h =>
  notEtaEmpty aleph0_ne_zero (@h Empty _ ⟨fun a => a.elim⟩ _ _)
-- `Order.IsEta.aleph0`
theorem w5_23 : ¬ drop0% Order.IsEta.aleph0 3 := fun h => by
  obtain ⟨z, h1, h2⟩ := h (α := ℤ) (s := {0}) (t := {1}) (by simp) (by simp) (by simp)
  have := h1 0 rfl; have := h2 1 rfl; omega
-- `Order.IsEta.aleph0`
theorem w5_24 : ¬ drop0% Order.IsEta.aleph0 4 := fun h => by
  obtain ⟨z, h1, -⟩ := h (α := WithTop ℚ) (s := {⊤}) (t := ∅) (by simp) (by simp [aleph0_pos]) (by simp)
  exact not_top_lt (h1 ⊤ rfl)
-- `Order.IsEta.aleph0`
theorem w5_25 : ¬ drop0% Order.IsEta.aleph0 5 := fun h => by
  obtain ⟨z, -, h2⟩ := h (α := WithBot ℚ) (s := ∅) (t := {⊥}) (by simp [aleph0_pos]) (by simp) (by simp)
  exact not_lt_bot (h2 ⊥ rfl)

-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.card_subtype_lt`
theorem w5_26 : ¬ drop0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.card_subtype_lt 3 := fun H => by
  have := H (δ := ℚ) (t := rG 0) 0
  rw [mkQ] at this
  exact absurd rQ_card (not_le.2 this)
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.mk_lo_lt`
theorem w5_27 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.mk_lo_lt 4 := fun H => by
  have := H (α := Unit) (β := Unit) (r := fun _ _ => True) () (fun _ _ => ())
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.mk_lo_lt`
theorem w5_28 : ¬ drop0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.mk_lo_lt 5 := fun H => by
  have h1 := H (α := ℚ) (β := ℚ) (r := rG 0) 0 (fun y _ => y)
  rw [mkQ] at h1
  refine absurd ?_ (not_le.2 h1)
  rw [← Cardinal.mk_nat]
  refine mk_le_of_injective (f := fun n : ℕ => ⟨-((n : ℚ) + 1), ⟨⟨-((n : ℚ) + 1), rG_lt _ _ (by
    have : (0 : ℚ) < n + 1 := by positivity
    linarith), by
    have : (0 : ℚ) < n + 1 := by positivity
    linarith⟩, rfl⟩⟩) ?_
  intro a b h; simpa using congrArg Subtype.val h
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.mk_hi_lt`
theorem w5_29 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.mk_hi_lt 4 := fun H => by
  have := H (α := Unit) (β := Unit) (r := fun _ _ => True) () (fun _ _ => ())
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.mk_hi_lt`
theorem w5_30 : ¬ drop0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.mk_hi_lt 5 := fun H => by
  have h1 := H (α := ℚ) (β := ℚ) (r := rG 0) 0 (fun y _ => y)
  rw [mkQ] at h1
  refine absurd ?_ (not_le.2 h1)
  rw [← Cardinal.mk_nat]
  refine mk_le_of_injective (f := fun n : ℕ => ⟨((n : ℚ) + 1), ⟨⟨((n : ℚ) + 1), rG_lt _ _ (by positivity),
    by positivity⟩, rfl⟩⟩) ?_
  intro a b h; simpa using congrArg Subtype.val h
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_def`
theorem w5_31 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_def 5 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq Unit
  have := H (α := Unit) (β := Unit) (r := fun _ _ => True) (s := s) (h := etaUU) ()
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_def`
theorem w5_32 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_def 7 := fun H => by
  obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq Unit
  have := H (α := Unit) (β := Unit) (r := r) (s := fun _ _ => True) (h := etaUU) (hord := hord) ()
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_def`
theorem w5_33 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_def 8 := fun H => by
  obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq Unit
  exact notEtaEmpty (mk_ne_zero Unit) (H (α := Unit) (β := Empty) (r := r) (s := WellOrderingRel) (hord := hord) ())
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_def`
theorem w5_34 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_def 9 := fun H =>
  rQ_hord (H (α := ℚ) (β := ℚ) (r := rG 0) (s := WellOrderingRel) (h := etaQQ) 0)

-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_mem`
theorem w5_35 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_mem 5 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq Unit
  have := H (α := Unit) (β := Unit) (r := fun _ _ => True) (s := s) (h := etaUU) ()
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_mem`
theorem w5_36 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_mem 7 := fun H => by
  obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq Unit
  have := H (α := Unit) (β := Unit) (r := r) (s := fun _ _ => True) (h := etaUU) (hord := hord) ()
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_mem`
theorem w5_37 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_mem 8 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq Unit
  exact notEtaBoolUnit (H (α := Bool) (β := Unit) (r := (· < ·)) (s := s) (hord := hordFin _) false)
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_mem`
theorem w5_38 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_mem 9 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq ℚ
  exact rQ_hord (H (α := ℚ) (β := ℚ) (r := rG 0) (s := s) (h := etaQQ) 0)
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_sep`
theorem w5_39 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_sep 5 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq Unit
  have := H (α := Unit) (β := Unit) (r := fun _ _ => True) (s := s) (h := etaUU) () () ()
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_sep`
theorem w5_40 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_sep 7 := fun H => by
  obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq Unit
  have := H (α := Unit) (β := Unit) (r := r) (s := fun _ _ => True) (h := etaUU) (hord := hord) () () ()
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_sep`
theorem w5_41 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_sep 8 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq Unit
  exact notEtaBoolUnit (H (α := Bool) (β := Unit) (r := (· < ·)) (s := s) (hord := hordFin _) false () ())
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_sep`
theorem w5_42 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_sep 9 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq ℚ
  exact rQ_hord (H (α := ℚ) (β := ℚ) (r := rG 0) (s := s) (h := etaQQ) 0 0 0)
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.strictMono_f`
theorem w5_43 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.strictMono_f 5 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq Unit
  have := H (α := Unit) (β := Unit) (r := fun _ _ => True) (s := s) (h := etaUU) 
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.strictMono_f`
theorem w5_44 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.strictMono_f 7 := fun H => by
  obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq Unit
  have := H (α := Unit) (β := Unit) (r := r) (s := fun _ _ => True) (h := etaUU) (hord := hord) 
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.strictMono_f`
theorem w5_45 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.strictMono_f 8 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq Unit
  exact notEtaBoolUnit (H (α := Bool) (β := Unit) (r := (· < ·)) (s := s) (hord := hordFin _) )
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.strictMono_f`
theorem w5_46 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.strictMono_f 9 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq ℚ
  exact rQ_hord (H (α := ℚ) (β := ℚ) (r := rG 0) (s := s) (h := etaQQ) )
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.not_lt_f`
theorem w5_47 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.not_lt_f 5 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq Unit
  have := H (α := Unit) (β := Unit) (r := fun _ _ => True) (s := s) (h := etaUU) (z := ()) ()
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.not_lt_f`
theorem w5_48 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.not_lt_f 7 := fun H => by
  obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq Unit
  have := H (α := Unit) (β := Unit) (r := r) (s := fun _ _ => True) (h := etaUU) (hord := hord) (z := ()) ()
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.not_lt_f`
theorem w5_49 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.not_lt_f 8 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq Unit
  exact notEtaBoolUnit (H (α := Bool) (β := Unit) (r := (· < ·)) (s := s) (hord := hordFin _) (z := ()) false)
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.not_lt_f`
theorem w5_50 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.not_lt_f 9 := fun H => by
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq ℚ
  exact rQ_hord (H (α := ℚ) (β := ℚ) (r := rG 0) (s := s) (h := etaQQ) (z := 0) 0)
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.surjective_f`
theorem w5_51 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.surjective_f 5 := fun H => by
  obtain ⟨s, hs, hords⟩ := Cardinal.exists_ord_eq Unit
  have := H (α := Unit) (β := Unit) (r := fun _ _ => True) (s := s) (h := etaUU) etaUU hords rfl
  exact irrefl_of (fun _ _ : Unit => True) () trivial
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.surjective_f`
theorem w5_52 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.surjective_f 8 := fun H => by
  obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq ℚ
  obtain ⟨s, hs, hords⟩ := Cardinal.exists_ord_eq ℤ
  have := H (α := ℚ) (β := ℤ) (r := r) (s := s) (hord := hord) etaQQ hords (mkQ.trans mk_int.symm)
  rw [mkQ] at this
  exact notEtaZ this
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.surjective_f`
theorem w5_53 : ¬ indep0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.surjective_f 9 := fun H => by
  obtain ⟨s, hs, hords⟩ := Cardinal.exists_ord_eq ℚ
  exact rQ_hord (H (α := ℚ) (β := ℚ) (r := rG 0) (s := s) (h := etaQQ) etaQQ hords rfl)
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.surjective_f`
theorem w5_54 : ¬ drop0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.surjective_f 10 := fun H => by
  obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq ℕ
  obtain ⟨s, hs, hords⟩ := Cardinal.exists_ord_eq ℚ
  have hη : IsEta #ℕ ℚ := by rw [Cardinal.mk_nat]; exact etaQ
  have hsurj := H (α := ℕ) (β := ℚ) (r := r) (s := s) (h := hη) (hord := hord) hords (by rw [Cardinal.mk_nat, mkQ])
  have hm := (priv% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.strictMono_f) (h := hη) (hord := hord) (s := s)
  exact noSurjNQ _ hm hsurj
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.surjective_f`
theorem w5_55 : ¬ drop0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.surjective_f 12 := fun H => by
  obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq Unit
  obtain ⟨s, hs, hords⟩ := Cardinal.exists_ord_eq ℚ
  have hη : IsEta #Unit ℚ := by simpa using (IsEta.one : IsEta 1 ℚ)
  have hsurj := H (α := Unit) (β := ℚ) (r := r) (s := s) (h := hη) (hord := hord) etaUU hords
  obtain ⟨u, hu⟩ := hsurj 0
  obtain ⟨v, hv⟩ := hsurj 1
  have : (0 : ℚ) = 1 := by rw [← hu, ← hv]
  exact zero_ne_one this
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_sep`
theorem w5_56 : ¬ drop0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_sep 12 := fun H => by
  have hη : IsEta #Bool ℚ := etaQ.mono (Cardinal.mk_le_aleph0)
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq ℚ
  exact lt_irrefl _ (H (α := Bool) (β := ℚ) (r := (· > ·)) (s := s) (h := hη) (hord := hordFin _) false _ _
    ⟨⟨true, by decide, by decide⟩, rfl⟩)
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_sep`
theorem w5_57 : ¬ drop0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_sep 14 := fun H => by
  have hη : IsEta #Bool ℚ := etaQ.mono (Cardinal.mk_le_aleph0)
  obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq ℚ
  exact lt_irrefl _ (H (α := Bool) (β := ℚ) (r := (· < ·)) (s := s) (h := hη) (hord := hordFin _) true _
    ⟨⟨false, by decide, by decide⟩, rfl⟩ _)
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.f_mem`: the hypothesis always holds by the private lemma f_sep
theorem w5_70 : drop% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_mem 11 := fun a =>
  (priv% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_mem) a
    ((priv% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_sep) a)
-- `Order.OrderType.type_le_type_of_isEta`
theorem w5_71 : ¬ drop0% Order.OrderType.type_le_type_of_isEta 4 := fun H => by
  obtain ⟨e⟩ := OrderType.type_le_type_iff.1 (H (α := Unit) (β := Empty))
  exact (e ()).elim
-- `Order.OrderType.type_eq_type_of_isEta`
theorem w5_72 : ¬ drop0% Order.OrderType.type_eq_type_of_isEta 4 := fun H => by
  obtain ⟨e⟩ := OrderType.type_eq_type.1 (H (α := ℕ) (β := ℚ) etaQQ (by rw [Cardinal.mk_nat, mkQ]))
  exact noIsoNQ e
-- `Order.OrderType.type_eq_type_of_isEta`
theorem w5_73 : ¬ drop0% Order.OrderType.type_eq_type_of_isEta 5 := fun H => by
  obtain ⟨e⟩ := OrderType.type_eq_type.1 (H (α := ℚ) (β := ℕ) etaQQ (by rw [Cardinal.mk_nat, mkQ]))
  exact noIsoNQ e.symm
-- `Order.OrderType.type_eq_type_of_isEta`
theorem w5_74 : ¬ drop0% Order.OrderType.type_eq_type_of_isEta 6 := fun H => by
  obtain ⟨e⟩ := OrderType.type_eq_type.1 (H (α := Unit) (β := ℚ) etaUU etaQQ)
  have : (0 : ℚ) = 1 := e.symm.injective (Subsingleton.elim _ _)
  exact zero_ne_one this

-- `Nat.pow_log_eq_self_iff`
theorem w5_80 : ¬ drop0% Nat.pow_log_eq_self_iff 2 := fun H =>
  absurd ((H (b := 0) (n := 0)).2 ⟨1, rfl⟩) (by simp)
-- `Dyadic.coe_mkRat`
theorem w5_81 : ¬ indep0% Dyadic.coe_mkRat 2 := fun H => by
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (H 0 (n := 3))
  cases k with
  | zero => simp at hk
  | succ k => rw [pow_succ] at hk; omega
-- `Dyadic.eq_mkRat_of_den_le`
theorem w5_82 : ¬ indep0% Dyadic.eq_mkRat_of_den_le 3 := fun H => by
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (H (x := ((0 : ℕ) : Dyadic)) (n := 3) (by simp))
  cases k with
  | zero => simp at hk
  | succ k => rw [pow_succ] at hk; omega
-- `_private.CombinatorialGames.Mathlib.Small.0.small_level`
theorem w5_83 : ¬ ∀ {α : Type 1} (r : α → α → Prop) (x : α) (n : ℕ),
    Small.{0} ↑((priv% _private.CombinatorialGames.Mathlib.Small.«0».level) r x n) := fun H => by
  have hs := H (fun _ _ : Type => True) PUnit 1
  apply notSmallType
  refine @small_subset _ _ _ ?_ hs
  intro y _
  change y ∈ ⋃₀ ((fun x => {y | (fun _ _ : Type => True) x y}) '' {PUnit})
  exact ⟨_, ⟨PUnit, rfl, rfl⟩, trivial⟩
-- `_private.CombinatorialGames.Mathlib.Small.0.small_sUnion_level`
theorem w5_84 : ¬ ∀ {α : Type 1} (r : α → α → Prop) (x : α),
    Small.{0} ↑(⋃₀ Set.range ((priv% _private.CombinatorialGames.Mathlib.Small.«0».level) r x)) := fun H => by
  have hs := H (fun _ _ : Type => True) PUnit
  apply notSmallType
  refine @small_subset _ _ _ ?_ hs
  intro y _
  refine ⟨_, ⟨1, rfl⟩, ?_⟩
  change y ∈ ⋃₀ ((fun x => {y | (fun _ _ : Type => True) x y}) '' {PUnit})
  exact ⟨_, ⟨PUnit, rfl, rfl⟩, trivial⟩
-- `small_transGen`
theorem w5_85 : ¬ ∀ {α : Type 1} (r : α → α → Prop) (x : α), Small.{0} { y // Relation.TransGen r x y } :=
  fun H => notSmallType (@small_of_injective _ _ (H (fun _ _ : Type => True) PUnit)
    (fun y => ⟨y.1, .single trivial⟩) (fun a b h => Subtype.ext (by simpa using h)))
-- `small_transGen'`
theorem w5_86 : ¬ ∀ {α : Type 1} (r : α → α → Prop) (x : α), Small.{0} { y // Relation.TransGen r y x } :=
  fun H => notSmallType (@small_of_injective _ _ (H (fun _ _ : Type => True) PUnit)
    (fun y => ⟨y.1, .single trivial⟩) (fun a b h => Subtype.ext (by simpa using h)))
-- `small_reflTransGen`
theorem w5_87 : ¬ ∀ {α : Type 1} (r : α → α → Prop) (x : α), Small.{0} { y // Relation.ReflTransGen r x y } :=
  fun H => notSmallType (@small_of_injective _ _ (H (fun _ _ : Type => True) PUnit)
    (fun y => ⟨y.1, .single trivial⟩) (fun a b h => Subtype.ext (by simpa using h)))
-- `small_reflTransGen'`
theorem w5_88 : ¬ ∀ {α : Type 1} (r : α → α → Prop) (x : α), Small.{0} { y // Relation.ReflTransGen r y x } :=
  fun H => notSmallType (@small_of_injective _ _ (H (fun _ _ : Type => True) PUnit)
    (fun y => ⟨y.1, .single trivial⟩) (fun a b h => Subtype.ext (by simpa using h)))
-- `small_of_image`
theorem w5_89 : ¬ ∀ {α : Type 1} {β : Type} {f : α → β} {s : Set α} [Small.{0} ↑(f '' s)], Small.{0} ↑s :=
  fun H => notSmallType (@H Type Unit (fun _ => ()) Set.univ (small_self _))
-- `small_of_image`
theorem w5_90 : ¬ ∀ {α : Type 1} {β : Type 1} {f : α → β} {s : Set α}, Set.InjOn f s → Small.{0} ↑s :=
  fun H => notSmallType (@H Type Type id Set.univ (fun _ _ _ _ h => h))
-- `small_image_iff`
theorem w5_91 : ¬ ∀ {α : Type 1} {β : Type} {f : α → β} {s : Set α}, Small.{0} ↑(f '' s) ↔ Small.{0} ↑s :=
  fun H => notSmallType ((@H Type Unit (fun _ => ()) Set.univ).1 (small_self _))
-- `NatOrdinal.withTop_iSup_coe_lt`
theorem w5_92 : ¬ ∀ {ι : Type 1} (f : ι → NatOrdinal.{0}), ⨆ i, (f i : WithTop NatOrdinal.{0}) < ⊤ :=
  fun H => wtopSup (Set.range fun i : NatOrdinal.{0} => (i : WithTop NatOrdinal.{0})) (fun a => ⟨a, rfl⟩) (H (ι := NatOrdinal.{0}) (fun i => i))
-- `NatOrdinal.withTop_sSup_coe_lt`
theorem w5_93 : ¬ drop0% NatOrdinal.withTop_sSup_coe_lt 1 := fun H =>
  wtopSup (WithTop.some '' Set.univ) (fun a => ⟨a, trivial, rfl⟩) (H Set.univ)
-- `NatOrdinal.withTop_iSup_lt_top_iff_of_forall_lt`
theorem w5_94 : ¬ drop0% NatOrdinal.withTop_iSup_lt_top_iff_of_forall_lt 2 := fun H => by
  have := (H (f := fun _ : True => (⊤ : WithTop NatOrdinal.{0}))).2
    (small_subset (s := {⊤}) (by rintro _ ⟨_, rfl⟩; rfl))
  simp at this
-- `NatOrdinal.withTop_sSup_lt_top_iff_of_forall_lt`
theorem w5_95 : ¬ drop0% NatOrdinal.withTop_sSup_lt_top_iff_of_forall_lt 1 := fun H => by
  have := (H (s := {⊤})).2 inferInstance
  simp at this
-- `NatOrdinal.withTop_iSup_lt_top`
theorem w5_96 : ¬ ∀ {ι : Type 1} {f : ι → WithTop NatOrdinal.{0}}, ⨆ i, f i < ⊤ ↔ ∀ i, f i < ⊤ :=
  fun H => wtopSup (Set.range fun i : NatOrdinal.{0} => (i : WithTop NatOrdinal.{0})) (fun a => ⟨a, rfl⟩)
    ((H (ι := NatOrdinal.{0}) (f := fun i => (i : WithTop NatOrdinal.{0}))).2 (fun i => WithTop.coe_lt_top i))
-- `NatOrdinal.withTop_sSup_lt_top`
theorem w5_97 : ¬ drop0% NatOrdinal.withTop_sSup_lt_top 1 := fun H =>
  wtopSup (Set.range fun i : NatOrdinal.{0} => (i : WithTop NatOrdinal.{0})) (fun a => ⟨a, rfl⟩) ((H (s := Set.range (fun i : NatOrdinal.{0} => (i : WithTop NatOrdinal.{0})))).2
    (by rintro _ ⟨i, rfl⟩; exact WithTop.coe_lt_top i))
-- `_private.CombinatorialGames.NatOrdinal.AddMonoidAlgebra.0.Ordinal.natCast_toNat`
theorem w5_98 : ¬ drop0% _private.CombinatorialGames.NatOrdinal.AddMonoidAlgebra.«0».Ordinal.natCast_toNat 1 := fun H => by
  have := H (o := Ordinal.omega0.{0})
  exact (Ordinal.natCast_lt_omega0 _).ne this
-- `_private.CombinatorialGames.NatOrdinal.AddMonoidAlgebra.0.Finsupp.mapRange_single_add`
theorem w5_99 : ¬ drop0% _private.CombinatorialGames.NatOrdinal.AddMonoidAlgebra.«0».Finsupp.mapRange_single_add 10 := fun H => by
  have := congrArg (· ()) (H (M := ℕ) (N := ℕ) (α := Unit) (f := fun x => x ^ 2) (g := Finsupp.single () 1)
    (hf := by simp) (a := ()) (b := 1))
  simp at this

-- `NatOrdinal.lt_iSup_iff`
theorem w5_100 : ¬ ∀ {ι : Type 1} (f : ι → NatOrdinal.{0}) {x : NatOrdinal.{0}}, x < ⨆ i, f i ↔ ∃ i, x < f i :=
  fun H => by
    have := (H (ι := NatOrdinal.{0}) (fun i => i) (x := 0)).2 ⟨1, zero_lt_one⟩
    rw [iSupN] at this; exact lt_irrefl _ this
-- `NatOrdinal.apply_omega0_of_isNormal`
theorem w5_101 : ¬ drop0% NatOrdinal.apply_omega0_of_isNormal 1 := fun H => by
  have := @H (fun o => if o < Ordinal.omega0 then (0 : NatOrdinal) else 1)
  simp [Ordinal.natCast_lt_omega0] at this
-- `NatOrdinal.iSup_eq_zero_iff`
theorem w5_102 : ¬ ∀ {ι : Type 1} {f : ι → NatOrdinal.{0}}, ⨆ i, f i = 0 ↔ ∀ i, f i = 0 :=
  fun H => one_ne_zero ((H (ι := NatOrdinal.{0}) (f := fun i => i)).1 iSupN 1)
-- `NatOrdinal.induction`
theorem w5_103 : ¬ drop0% NatOrdinal.induction 2 := fun H => @H (fun _ => False) 0
-- `NatOrdinal.eq_natCast_of_le_natCast`
theorem w5_104 : ¬ drop0% NatOrdinal.eq_natCast_of_le_natCast 2 := fun H => by
  obtain ⟨c, hc⟩ := @H (NatOrdinal.of Ordinal.omega0) 0
  exact (Ordinal.natCast_lt_omega0 c).ne' (NatOrdinal.of.injective hc)
-- `NatOrdinal.le_iSup`
theorem w5_105 : ¬ ∀ {ι : Type 1} (f : ι → NatOrdinal.{0}) (i : ι), f i ≤ iSup f :=
  fun H => absurd ((H (ι := NatOrdinal.{0}) (fun i => i) 1).trans_eq iSupN) (not_le.2 zero_lt_one)
-- `NatOrdinal.iSup_le_iff`
theorem w5_106 : ¬ ∀ {ι : Type 1} {f : ι → NatOrdinal.{0}} {a : NatOrdinal.{0}}, ⨆ i, f i ≤ a ↔ ∀ i, f i ≤ a :=
  fun H => absurd ((H (ι := NatOrdinal.{0}) (f := fun i => i) (a := 0)).1 iSupN.le 1) (not_le.2 zero_lt_one)
-- `_private.CombinatorialGames.NatOrdinal.Basic.0.NatOrdinal.iSup_add_of_monotone`
theorem w5_107 : ¬ drop0% _private.CombinatorialGames.NatOrdinal.Basic.«0».NatOrdinal.iSup_add_of_monotone 3 := fun H => by
  have h := H (a := 1) (b := 1) (fun x => if x = 0 then 1 else 0)
  simp only [ciSup_unique, NatOrdinal.Iio_one_default_eq, zero_add, add_zero, max_self] at h
  have h2 : (1 : NatOrdinal.{0}) ≤ ⨆ x : Set.Iio ((1 : NatOrdinal.{0}) + 1), (fun x : NatOrdinal.{0} => if x = 0 then (1 : NatOrdinal.{0}) else 0) x := by
    refine le_trans ?_ (le_ciSup (NatOrdinal.bddAbove_of_small _) ⟨0, show (0 : NatOrdinal.{0}) < 1 + 1 from add_pos zero_lt_one zero_lt_one⟩)
    simp
  rw [h] at h2
  simp at h2
-- `NatOrdinal.mul_add_le₃`
theorem w5_108 : ¬ drop0% NatOrdinal.mul_add_le₃ 6 := fun H => by
  have := H (a := 0) (a' := 1) (b := 1) (b' := 0) (c := 1) (c' := 0) zero_le_one zero_le_one
  simp at this
-- `NatOrdinal.mul_add_le₃`
theorem w5_109 : ¬ drop0% NatOrdinal.mul_add_le₃ 7 := fun H => by
  have := H (a := 1) (a' := 0) (b := 0) (b' := 1) (c := 1) (c' := 0) zero_le_one zero_le_one
  simp at this
-- `NatOrdinal.mul_add_le₃`
theorem w5_110 : ¬ drop0% NatOrdinal.mul_add_le₃ 8 := fun H => by
  have := H (a := 1) (a' := 0) (b := 1) (b' := 0) (c := 0) (c' := 1) zero_le_one zero_le_one
  simp at this
-- `NatOrdinal.wpow_le_iff`
theorem w5_111 : ¬ drop0% NatOrdinal.wpow_le_iff 2 := fun H => by
  have := (H (x := 0) (y := 0)).2 (fun z hz => absurd hz (not_lt_bot (a := z)))
  simp at this
-- `NatOrdinal.of_natCast_opow_mul_natCast_add_of_lt`
theorem w5_112 : ¬ drop0% NatOrdinal.of_natCast_opow_mul_natCast_add_of_lt 3 := fun H => by
  have := H (x := 0) (y := Ordinal.omega0) (m := 2) 1
  simp [Ordinal.one_add_omega0] at this
-- `NatOrdinal.of_natCast_opow_mul_natCast_add_of_lt'`
theorem w5_113 : ¬ drop0% NatOrdinal.of_natCast_opow_mul_natCast_add_of_lt' 3 := fun H => by
  have := H (x := 0) (y := Ordinal.omega0) (m := 2) 1
  simp [Ordinal.one_add_omega0] at this
-- `NatOrdinal.of_natCast_opow_add_of_lt`
theorem w5_114 : ¬ drop0% NatOrdinal.of_natCast_opow_add_of_lt 3 := fun H => by
  have := H (x := 0) (y := Ordinal.omega0) (m := 2)
  simp [Ordinal.one_add_omega0] at this
-- `NatOrdinal.of_natCast_opow_add_of_lt'`
theorem w5_115 : ¬ drop0% NatOrdinal.of_natCast_opow_add_of_lt' 3 := fun H => by
  have := H (x := 0) (y := Ordinal.omega0) (m := 2)
  simp [Ordinal.one_add_omega0] at this
-- `NatOrdinal.mul_lt_wpow_wpow`
theorem w5_116 : ¬ drop0% NatOrdinal.mul_lt_wpow_wpow 3 := fun H => by
  have := H (x := ω^ ω^ (0 : NatOrdinal.{0})) (y := 1) (z := 0) (by simp)
  simp at this
-- `NatOrdinal.mul_lt_wpow_wpow`
theorem w5_117 : ¬ drop0% NatOrdinal.mul_lt_wpow_wpow 4 := fun H => by
  have := H (y := ω^ ω^ (0 : NatOrdinal.{0})) (x := 1) (z := 0) (by simp)
  simp at this
-- `Nimber.iSup_eq_zero_iff`
theorem w5_118 : ¬ ∀ {ι : Type 1} {f : ι → Nimber.{0}}, ⨆ i, f i = 0 ↔ ∀ i, f i = 0 :=
  fun H => one_ne_zero ((H (ι := Nimber.{0}) (f := fun i => i)).1 iSupNim 1)
-- `Nimber.lt_iSup_iff`
theorem w5_119 : ¬ ∀ {ι : Type 1} (f : ι → Nimber.{0}) {x : Nimber.{0}}, x < ⨆ i, f i ↔ ∃ i, x < f i :=
  fun H => by
    have := (H (ι := Nimber.{0}) (fun i => i) (x := 0)).2 ⟨1, zero_lt_one⟩
    rw [iSupNim] at this; exact lt_irrefl _ this
-- `Nimber.eq_natCast_of_le_natCast`
theorem w5_120 : ¬ drop0% Nimber.eq_natCast_of_le_natCast 2 := fun H => by
  obtain ⟨c, hc⟩ := @H (Nimber.of Ordinal.omega0) 0
  exact (Ordinal.natCast_lt_omega0 c).ne' (Nimber.of.injective hc)
-- `Nimber.induction`
theorem w5_121 : ¬ drop0% Nimber.induction 2 := fun H => @H (fun _ => False) 0
-- `Nimber.le_iSup`
theorem w5_122 : ¬ ∀ {ι : Type 1} (f : ι → Nimber.{0}) (i : ι), f i ≤ iSup f :=
  fun H => absurd ((H (ι := Nimber.{0}) (fun i => i) 1).trans_eq iSupNim) (not_le.2 zero_lt_one)
-- `Nimber.iSup_le_iff`
theorem w5_123 : ¬ ∀ {ι : Type 1} {f : ι → Nimber.{0}} {a : Nimber.{0}}, ⨆ i, f i ≤ a ↔ ∀ i, f i ≤ a :=
  fun H => absurd ((H (ι := Nimber.{0}) (f := fun i => i) (a := 0)).1 iSupNim.le 1) (not_le.2 zero_lt_one)
-- `_private.CombinatorialGames.Nimber.Field.0.Nimber.mul_ne_of_lt`
theorem w5_124 : ¬ drop0% _private.CombinatorialGames.Nimber.Field.«0».Nimber.mul_ne_of_lt 3 := fun H =>
  H (a := 0) (b := 1) (a' := 0) (b' := 0) zero_lt_one (by simp)
-- `_private.CombinatorialGames.Nimber.Field.0.Nimber.mul_ne_of_lt`
theorem w5_125 : ¬ drop0% _private.CombinatorialGames.Nimber.Field.«0».Nimber.mul_ne_of_lt 5 := fun H =>
  H (a := 1) (b := 0) (a' := 0) zero_lt_one (b' := 0) (by simp)
-- `_private.CombinatorialGames.Nimber.Field.0.Nimber.cons_mem_invSet`
theorem w5_126 : ¬ drop0% _private.CombinatorialGames.Nimber.Field.«0».Nimber.cons_mem_invSet 3 := fun H => by
  have h := H (a := 1) (b := 0) (a' := 0) zero_lt_one ((priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.zero_mem_invSet) 1)
  simp only [mul_zero, add_zero, mul_one] at h
  have hrec : ∀ x ∈ (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invSet) 1, x = 0 := fun x hx =>
    (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invSet_recOn) 1 rfl (fun _ ha ha0 => absurd (Nimber.lt_one_iff.1 ha) ha0) x hx
  have := hrec _ h
  exact (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invAux_ne_zero) 0 this
-- `_private.CombinatorialGames.Nimber.Field.0.Nimber.cons_mem_invSet`
theorem w5_127 : ¬ drop0% _private.CombinatorialGames.Nimber.Field.«0».Nimber.cons_mem_invSet 4 := fun H => by
  have h := H (a := 0) (b := 0) (a' := 1) one_ne_zero ((priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.zero_mem_invSet) 0)
  simp only [mul_zero, add_zero, mul_one] at h
  have hrec : ∀ x ∈ (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invSet) 0, x = 0 := fun x hx =>
    (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invSet_recOn) 0 rfl (fun a' ha _ => absurd ha (not_lt_bot (a := a'))) x hx
  have := hrec _ h
  exact (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invAux_ne_zero) 1 this
-- `_private.CombinatorialGames.Nimber.Field.0.Nimber.invSet_recOn`
theorem w5_128 : ¬ drop0% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invSet_recOn 2 := fun H =>
  @H (fun _ => False) 0 (fun a' ha => absurd ha (not_lt_bot (a := a'))) 0 ((priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.zero_mem_invSet) 0)
-- `_private.CombinatorialGames.Nimber.Field.0.Nimber.invSet_recOn`
theorem w5_129 : ¬ drop0% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invSet_recOn 5 := fun H =>
  one_ne_zero (@H (fun x => x = 0) 0 rfl (fun a' ha => absurd ha (not_lt_bot (a := a'))) 1)
-- `_private.CombinatorialGames.Nimber.Field.0.Nimber.mem_invSet_of_lt_invAux`
theorem w5_130 : ¬ drop0% _private.CombinatorialGames.Nimber.Field.«0».Nimber.mem_invSet_of_lt_invAux 2 := fun H =>
  (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invAux_notMem_invSet) 0 H
-- `_private.CombinatorialGames.Nimber.Field.0.Nimber.inv_eq_invAux`
theorem w5_131 : ¬ drop0% _private.CombinatorialGames.Nimber.Field.«0».Nimber.inv_eq_invAux 1 := fun H =>
  (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invAux_ne_zero) 0 ((H (a := 0)).symm.trans inv_zero)
-- `NatNimber.induction`
theorem w5_132 : ¬ drop0% NatNimber.induction 2 := fun H => @H (fun _ => False) 0
-- `Nimber.IsRing.opow_omega0`
theorem w5_133 : ¬ drop0% Nimber.IsRing.opow_omega0 1 := fun H =>
  (H (x := 1)).ne_one (by simp)
-- `_private.CombinatorialGames.Nimber.NatOrdinal.0.Ordinal.isPrincipal_mul_opow_omega0`: the cases x = 0 and x = 1 are trivial
theorem w5_134 : drop% _private.CombinatorialGames.Nimber.NatOrdinal.«0».Ordinal.isPrincipal_mul_opow_omega0 1 := by
  intro x
  rcases lt_or_ge 1 x with hx | hx
  · exact (priv% _private.CombinatorialGames.Nimber.NatOrdinal.«0».Ordinal.isPrincipal_mul_opow_omega0) hx
  · rcases eq_or_lt_of_le hx with rfl | h0
    swap
    · rw [Order.lt_one_iff] at h0; subst h0
      rw [Ordinal.zero_opow Ordinal.omega0_ne_zero]
      intro a b ha; simp at ha
    · rw [Ordinal.one_opow]
      intro a b ha hb
      rw [Order.lt_one_iff] at ha hb
      subst ha; subst hb; simp

-- `_private.CombinatorialGames.Nimber.Field.0.Nimber.invSet_recOn`
theorem w5_135 : ¬ drop0% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invSet_recOn 3 := fun H => by
  have hm := (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.cons_mem_invSet) one_ne_zero one_lt_two_nim ((priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.zero_mem_invSet) (Nimber.of 2))
  have := @H (fun x => x = 0) (Nimber.of 2) rfl _ hm
  simp only [mul_zero, add_zero, mul_one] at this
  exact (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invAux_ne_zero) 1 this
-- `_private.CombinatorialGames.Nimber.Field.0.Nimber.cons_mem_invSet`
theorem w5_136 : ¬ drop0% _private.CombinatorialGames.Nimber.Field.«0».Nimber.cons_mem_invSet 5 := fun H => by
  obtain ⟨x, hx⟩ := (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invSet_nonempty) (Nimber.of 2)
  have hi : (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invAux) (1 : Nimber.{0}) ≠ 0 := (priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invAux_ne_zero) 1
  have hc : Nimber.of 2 + 1 ≠ 0 := fun h => one_lt_two_nim.ne' (Nimber.add_eq_zero.1 h)
  apply hx
  have hm := H (a := Nimber.of 2) (a' := 1) (b := (x * ((priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invAux) (1 : Nimber.{0}))⁻¹ + 1) * (Nimber.of 2 + 1)⁻¹)
    one_ne_zero one_lt_two_nim
  have e1 : (Nimber.of 2 + 1) * ((x * ((priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invAux) (1 : Nimber.{0}))⁻¹ + 1) * (Nimber.of 2 + 1)⁻¹) =
      x * ((priv% _private.CombinatorialGames.Nimber.Field.«0».Nimber.invAux) (1 : Nimber.{0}))⁻¹ + 1 := by
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  rw [e1, add_comm, add_assoc, Nimber.add_self, add_zero, mul_comm, mul_assoc, inv_mul_cancel₀ hi, mul_one] at hm
  exact hm
-- `_private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.surjective_f`
theorem w5_137 : ¬ drop0% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.surjective_f 11 := fun H => by
  obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq ℚ
  have hsurj := H (α := ℚ) (β := ℚ) (r := r) (s := rG 0) (h := etaQQ) (hord := hord) etaQQ rfl
  obtain ⟨a, ha⟩ := hsurj 0
  have hmem := (priv% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_mem) (h := etaQQ) (hord := hord) (s := rG 0) a
    ((priv% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f_sep) (h := etaQQ) (hord := hord) (s := rG 0) a)
  rw [ha] at hmem
  have hU := (priv% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.mk_hi_lt) hord a (fun y (_ : r y a) => (priv% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.f) etaQQ hord (rG (0 : ℚ)) y)
  obtain ⟨z, hz0, hzU⟩ := etaQQ.exists_between (s := {0}) (by rw [mkQ]; simp) hU
    (fun x hx y hy => by rw [Set.mem_singleton_iff.1 hx]; exact hmem.2 y hy)
  have := (priv% _private.CombinatorialGames.Mathlib.EtaSet.«0».Order.IsEta.not_lt_f) (h := etaQQ) (hord := hord) (s := rG 0) (z := z) a
    ⟨fun x hx => (hmem.1 x hx).trans (hz0 0 rfl), hzU⟩
  rw [ha] at this
  exact this (rG_lt _ _ (hz0 0 rfl).ne')