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

namespace W2c1
open Nimber Ordinal Set

theorem two_add_one : ∗2 + 1 = ∗3 := by
  have := IsGroup.two.add_eq_of_lt (y := 1) (by simp)
  rw [← this]; simp; norm_num

theorem notGroup3 : ¬ IsGroup (∗3) := by
  intro h
  have := h.add_lt (y := ∗2) (z := 1) (by rw [of.lt_iff_lt]; exact_mod_cast (show (2:ℕ) < 3 by decide)) (by simp)
  rw [two_add_one] at this; exact lt_irrefl _ this

theorem three_add_two : ∗3 + ∗2 = 1 := by
  rw [← two_add_one, _root_.add_comm (∗2), _root_.add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem two_ne_one : (∗2 : Nimber.{0}) ≠ 1 := by
  rw [← of_one, Ne, of.eq_iff_eq]; exact_mod_cast (show (2:ℕ) ≠ 1 by decide)

theorem two_ne_zero' : (∗2 : Nimber.{0}) ≠ 0 := IsGroup.two.ne_zero

theorem two_lt_three : (∗2 : Nimber.{0}) < ∗3 := by
  rw [of.lt_iff_lt]; exact_mod_cast (show (2:ℕ) < 3 by decide)

theorem three_ne : (∗3 : Nimber.{0}) ≠ 0 ∧ (∗3 : Nimber.{0}) ≠ 1 ∧ (∗3 : Nimber.{0}) ≠ ∗2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (IsGroup.two.zero_lt.trans two_lt_three).ne'
  · rw [← of_one, Ne, of.eq_iff_eq]; exact_mod_cast (show (3:ℕ) ≠ 1 by decide)
  · rw [Ne, of.eq_iff_eq]; exact_mod_cast (show (3:ℕ) ≠ 2 by decide)

theorem lt_three {y : Nimber.{0}} (h : y < ∗3) : y = 0 ∨ y = 1 ∨ y = ∗2 := by
  rcases lt_or_ge y (∗2) with h2 | h2
  · rcases lt_two_iff.1 h2 with h | h <;> simp [h]
  · right; right
    apply le_antisymm _ h2
    cases y with | of y
    rw [of.lt_iff_lt] at h; rw [of.le_iff_le]
    have h3 : (3:Ordinal) = 2 + 1 := by norm_num
    rw [h3] at h; exact Order.lt_add_one_iff.1 h

theorem two_mul_two : ∗2 * ∗2 = (∗3 : Nimber.{0}) := by
  apply le_antisymm
  · apply mul_le_of_forall_ne
    intro a ha b hb
    rcases lt_two_iff.1 ha with rfl | rfl <;> rcases lt_two_iff.1 hb with rfl | rfl
    · simp; exact three_ne.1.symm
    · simp
    · simp
    · simp only [_root_.one_mul, _root_.mul_one, CharTwo.add_self_eq_zero, _root_.zero_add]
      exact three_ne.2.1.symm
  · by_contra hlt
    rcases lt_three (not_le.1 hlt) with h | h | h
    · exact two_ne_zero' (mul_self_eq_zero.1 h)
    · have : (∗2 + 1) * (∗2 + 1) = (0 : Nimber.{0}) := by
        calc (∗2 + 1) * (∗2 + 1) = ∗2 * ∗2 + (∗2 + ∗2) + 1 := by ring
          _ = 0 := by rw [h, CharTwo.add_self_eq_zero, _root_.add_zero, CharTwo.add_self_eq_zero]
      have := mul_self_eq_zero.1 this
      exact two_ne_one (Nimber.add_eq_zero.1 this)
    · exact two_ne_one (mul_left_cancel₀ two_ne_zero' (h.trans (mul_one _).symm))

theorem inv_two : (∗2 : Nimber.{0})⁻¹ = ∗3 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← two_add_one, mul_add, two_mul_two, mul_one, three_add_two]

theorem omega_mul_two : ∗ω * ∗2 = (∗(ω * 2) : Nimber.{0}) :=
  (IsField.mul_eq_of_lt IsField.omega0.toIsRing IsField.omega0 le_rfl
    (by rw [of.lt_iff_lt]; exact_mod_cast Ordinal.natCast_lt_omega0 2)).symm

theorem omega_two_ne : ω * 2 ≠ (ω : Ordinal.{0}) := by
  intro h
  have : ω * 1 < ω * 2 := mul_lt_mul_of_pos_left (by exact_mod_cast (show (1:ℕ) < 2 by decide)) omega0_pos
  rw [mul_one, h] at this; exact lt_irrefl _ this

theorem unb_field : ¬ BddAbove {x : Nimber.{0} | IsField x} :=
  not_bddAbove_iff_isCofinal.2 isClub_ofPred_isField.isCofinal

theorem three_mul_two : ∗3 * ∗2 = (1 : Nimber.{0}) := by
  rw [← two_add_one, add_mul, two_mul_two, _root_.one_mul, three_add_two]

theorem one_lt_two'' : (1 : Nimber.{0}) < ∗2 := IsRing.two.one_lt
theorem one_lt_three : (1 : Nimber.{0}) < ∗3 := one_lt_two''.trans two_lt_three

theorem five_ne : (∗((3 : Ordinal.{0}) + 2)) ≠ 1 := by
  rw [← of_one, Ne, of.eq_iff_eq]; exact_mod_cast (show (3 + 2 : ℕ) ≠ 1 by decide)

theorem inv01 {a : Ordinal.{0}} (ha : a < 2) : (∗a)⁻¹ < ∗2 := by
  rcases lt_two_iff.1 (of.lt_iff_lt.2 ha) with h | h <;> rw [h] <;> simp [one_lt_two'']

theorem two_omega_ne : ∗2 * ∗ω ≠ (∗ω : Nimber.{0}) := by
  rw [_root_.mul_comm, omega_mul_two, Ne, of.eq_iff_eq]; exact omega_two_ne

theorem two_mul_omega : (2 : Ordinal.{0}) * ω = ω := Ordinal.natCast_mul_omega0 (n := 2) (by decide)

theorem sSup_field : sSup {x : Nimber.{0} | IsField x} = 0 := by
  rw [csSup_of_not_bddAbove unb_field, csSup_empty]; rfl

theorem sInf_empty' : sInf (∅ : Set Nimber.{0}) = 0 := Ordinal.sInf_empty

theorem notSmallAll (S : Set Nimber.{0}) (h : ∀ x, x ∈ S) : ¬ Small.{0} S := fun hs =>
  not_small_ordinal.{0, 0} (@small_of_surjective _ _ hs (fun x : S => Nimber.val x.1)
    (fun y => ⟨⟨∗y, h _⟩, rfl⟩))

theorem natClosed (s : Set ℕ) : DirSupClosed s := fun d hds hne _ a ha => hds (by
  have := Nat.sSup_mem hne ⟨a, ha.1⟩; rwa [(isLUB_csSup hne ⟨a, ha.1⟩).unique ha] at this)

def zsucc (p : ℤ ×ₗ ℤ) : ℤ ×ₗ ℤ := toLex ((ofLex p).1, (ofLex p).2 + 1)

theorem zsucc_le_iff {a b : ℤ ×ₗ ℤ} : zsucc a ≤ b ↔ a < b := by
  simp only [zsucc, Prod.Lex.le_iff, Prod.Lex.lt_iff, ofLex_toLex]; omega

@[reducible] def zzSucc : SuccOrder (ℤ ×ₗ ℤ) := SuccOrder.ofSuccLeIff zsucc zsucc_le_iff

theorem lt_four {y : Nimber.{0}} (h : y < ∗4) : y = 0 ∨ y = 1 ∨ y = ∗2 ∨ y = ∗3 := by
  rcases lt_or_ge y (∗3) with h3 | h3
  · rcases lt_three h3 with h | h | h <;> simp [h]
  · right; right; right
    apply le_antisymm _ h3
    cases y with | of y
    rw [of.lt_iff_lt] at h; rw [of.le_iff_le]
    have h4 : (4:Ordinal) = 3 + 1 := by norm_num
    rw [h4] at h; exact Order.lt_add_one_iff.1 h

theorem three_lt_four : (∗3 : Nimber.{0}) < ∗4 := by
  rw [of.lt_iff_lt]; exact_mod_cast (show (3:ℕ) < 4 by decide)
theorem two_lt_four : (∗2 : Nimber.{0}) < ∗4 := two_lt_three.trans three_lt_four
theorem one_lt_four : (1 : Nimber.{0}) < ∗4 := one_lt_two''.trans two_lt_four
theorem zero_lt_four : (0 : Nimber.{0}) < ∗4 := zero_lt_one.trans one_lt_four
theorem one_add_two : 1 + ∗2 = (∗3 : Nimber.{0}) := by rw [_root_.add_comm, two_add_one]
theorem two_add_three : ∗2 + ∗3 = (1 : Nimber.{0}) := by rw [_root_.add_comm, three_add_two]
theorem three_add_one : ∗3 + 1 = (∗2 : Nimber.{0}) := by
  rw [← two_add_one, _root_.add_assoc, CharTwo.add_self_eq_zero, _root_.add_zero]
theorem one_add_three : 1 + ∗3 = (∗2 : Nimber.{0}) := by rw [_root_.add_comm, three_add_one]
theorem two_mul_three : ∗2 * ∗3 = (1 : Nimber.{0}) := by rw [_root_.mul_comm, three_mul_two]
theorem three_mul_three : ∗3 * ∗3 = (∗2 : Nimber.{0}) := by
  rw [← two_add_one]
  calc (∗2 + 1) * (∗2 + 1) = ∗2 * ∗2 + (∗2 + ∗2) + (1 : Nimber.{0}) := by ring
    _ = ∗2 := by rw [two_mul_two, CharTwo.add_self_eq_zero, _root_.add_zero, three_add_one]
theorem inv_three : (∗3 : Nimber.{0})⁻¹ = ∗2 := inv_eq_of_mul_eq_one_right three_mul_two

theorem field4 : IsField (∗4 : Nimber.{0}) where
  add_lt y z hy hz := by
    rcases lt_four hy with rfl | rfl | rfl | rfl <;> rcases lt_four hz with rfl | rfl | rfl | rfl <;>
      simp [two_add_one, three_add_two, one_add_two, two_add_three, three_add_one, one_add_three,
        zero_lt_four, one_lt_four, two_lt_four, three_lt_four] <;>
      first | exact_mod_cast (show (2:ℕ) < 4 by decide) | exact_mod_cast (show (3:ℕ) < 4 by decide)
  ne_zero := zero_lt_four.ne'
  mul_lt y z hy hz := by
    rcases lt_four hy with rfl | rfl | rfl | rfl <;> rcases lt_four hz with rfl | rfl | rfl | rfl <;>
      simp [two_mul_two, two_mul_three, three_mul_two, three_mul_three,
        zero_lt_four, one_lt_four, two_lt_four, three_lt_four] <;>
      first | exact_mod_cast (show (2:ℕ) < 4 by decide) | exact_mod_cast (show (3:ℕ) < 4 by decide)
  ne_one := one_lt_four.ne'
  inv_lt' y hy0 hy := by
    rcases lt_four hy with rfl | rfl | rfl | rfl
    · exact absurd rfl hy0
    · simpa using one_lt_four
    · rw [inv_two]; exact three_lt_four
    · rw [inv_three]; exact two_lt_four

theorem four_mul {z : Nimber.{0}} (hz : z < ∗4) : ∗(4 * val z) = ∗4 * z := by
  simpa using IsField.mul_eq_of_lt field4.toIsRing field4 le_rfl hz

theorem two_mul_four : ∗2 * ∗4 = (∗(4 * 2) : Nimber.{0}) := by
  rw [_root_.mul_comm, ← four_mul two_lt_four, val_of]

theorem g8 : IsGroup (∗(4 * 2 : Ordinal.{0})) := IsGroup.omul' field4.toIsGroup IsGroup.two

theorem eight_mul_two : ∗(4 * 2) * ∗2 = (∗(4 * 3) : Nimber.{0}) := by
  rw [← two_mul_four, _root_.mul_comm (∗2), _root_.mul_assoc, two_mul_two, ← four_mul three_lt_four,
    val_of]

end W2c1

open Nimber Ordinal Set W2c1

-- `Ordinal.log_eq_zero'`
theorem c_1 : ¬ drop0% Ordinal.log_eq_zero' 2 := fun h => by
  rcases log_eq_zero_iff.1 (@h 2 2) with h1 | h1
  · exact absurd h1 (not_le.2 one_lt_two)
  · exact lt_irrefl _ h1

-- `Nimber.IsGroup.add_lt`
theorem c_2 : ¬ drop0% Nimber.IsGroup.add_lt 1 := fun h => by
  have := @h (∗3) (∗2) 1 two_lt_three one_lt_three; rw [two_add_one] at this; exact lt_irrefl _ this

-- `Nimber.IsGroup.add_lt`
theorem c_3 : ¬ drop0% Nimber.IsGroup.add_lt 4 := fun h => by
  have := @h 1 IsGroup.one 1 0 zero_lt_one; simp at this

-- `Nimber.IsGroup.sum_lt`
theorem c_4 : ¬ drop0% Nimber.IsGroup.sum_lt 5 := fun h => by
  have := @h 1 IsGroup.one Unit {()} (fun _ => 1); simp at this

-- `Nimber.IsGroup.sSup`
theorem c_5 : ¬ drop0% Nimber.IsGroup.sSup 1 := fun h => by
  have := @h {∗3} (singleton_nonempty _) bddAbove_singleton
  rw [csSup_singleton] at this; exact notGroup3 this

-- `Nimber.IsGroup.sSup`
theorem c_6 : ¬ drop0% Nimber.IsGroup.sSup 2 := fun h => by
  have := @h ∅ (by simp) bddAbove_empty
  exact this.ne_zero (by rw [csSup_empty]; rfl)

-- `Nimber.IsGroup.sSup`
theorem c_7 : ¬ drop0% Nimber.IsGroup.sSup 3 := fun h => by
  have := @h {x | IsField x} (fun x hx => hx.toIsGroup) ⟨∗2, IsField.two⟩
  exact this.ne_zero sSup_field

-- `Nimber.IsGroup.iSup`
theorem c_8 : ¬ drop0% Nimber.IsGroup.iSup 1 := fun h => by
  have := @h False (fun _ => 1) (fun i => i.elim) ⟨1, by rintro _ ⟨i, _⟩; exact i.elim⟩
  rw [ciSup_of_empty] at this; exact this.ne_zero rfl

-- `Nimber.IsGroup.iSup`
theorem c_9 : ¬ drop0% Nimber.IsGroup.iSup 3 := fun h => by
  have := @h True ⟨trivial⟩ (fun _ => ∗3) ⟨∗3, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  simp only [ciSup_const] at this; exact notGroup3 this

-- `Nimber.IsGroup.iSup`
theorem c_10 : ¬ ∀ {ι : Type 1} [Nonempty ι] {f : ι → Nimber.{0}}, (∀ i, (f i).IsGroup) →
    (⨆ i, f i).IsGroup := fun h => by
  have := @h {x : Nimber.{0} // IsField x} ⟨⟨∗2, IsField.two⟩⟩ Subtype.val (fun i => i.2.toIsGroup)
  rw [iSup, Subtype.range_coe_subtype] at this; exact this.ne_zero sSup_field

-- `Nimber.IsGroup.le_add_self`
theorem c_11 : ¬ drop0% Nimber.IsGroup.le_add_self 2 := fun h => by
  have := @h (∗3) (∗2) two_lt_three; rw [three_add_two] at this
  exact absurd this (not_le.2 one_lt_three)

-- `Nimber.IsGroup.mul_add_eq_of_lt'`
theorem c_12 : ¬ drop0% Nimber.IsGroup.mul_add_eq_of_lt' 2 := fun h => by
  have := @h 3 2 (of.lt_iff_lt.1 two_lt_three) 1
  rw [_root_.mul_one, three_add_two] at this; exact five_ne this

-- `Nimber.IsGroup.mul_add_eq_of_lt`
theorem c_13 : ¬ drop0% Nimber.IsGroup.mul_add_eq_of_lt 2 := fun h => by
  have := @h (∗3) (∗2) two_lt_three 1
  simp only [val_of, _root_.mul_one] at this; rw [three_add_two] at this; exact five_ne this

-- `Nimber.IsGroup.add_eq_of_lt`
theorem c_14 : ¬ drop0% Nimber.IsGroup.add_eq_of_lt 2 := fun h => by
  have := @h (∗3) (∗2) two_lt_three
  simp only [val_of] at this; rw [three_add_two] at this; exact five_ne this

-- `Nimber.IsGroup.add_eq_of_lt'`
theorem c_15 : ¬ drop0% Nimber.IsGroup.add_eq_of_lt' 2 := fun h => by
  have := @h 3 2 (of.lt_iff_lt.1 two_lt_three)
  rw [three_add_two] at this; exact five_ne (by rw [this]; rfl)

-- `Nimber.add_lt_of_log_eq`
theorem c_16 : ¬ drop0% Nimber.add_lt_of_log_eq 4 := fun h => by
  have := @h 1 2 one_ne_zero two_ne_zero
  rw [log_one_right, opow_zero, of_one, _root_.add_comm, two_add_one] at this
  exact absurd this (not_lt.2 one_lt_three.le)

-- `Nimber.IsGroup.opow`
theorem c_17 : ¬ drop0% Nimber.IsGroup.opow 1 := fun h => by
  have := @h (∗3) 1; simp only [val_of, opow_one] at this; exact notGroup3 this

-- `Nimber.IsGroup.opow'`
theorem c_18 : ¬ drop0% Nimber.IsGroup.opow' 1 := fun h => by
  have := @h 3 1; simp only [opow_one] at this; exact notGroup3 this

-- `Nimber.IsGroup.omul`
theorem c_19 : ¬ drop0% Nimber.IsGroup.omul 2 := fun h => by
  have := @h (∗3) 1 IsGroup.one; simp only [val_of, val_one, _root_.mul_one] at this; exact notGroup3 this

-- `Nimber.IsGroup.omul`
theorem c_20 : ¬ drop0% Nimber.IsGroup.omul 3 := fun h => by
  have := @h 1 (∗3) IsGroup.one; simp only [val_of, val_one, _root_.one_mul] at this; exact notGroup3 this

-- `Nimber.IsGroup.omul'`
theorem c_21 : ¬ drop0% Nimber.IsGroup.omul' 2 := fun h => by
  have := @h 3 1 (by rw [of_one]; exact IsGroup.one); simp only [_root_.mul_one] at this; exact notGroup3 this

-- `Nimber.IsGroup.omul'`
theorem c_22 : ¬ drop0% Nimber.IsGroup.omul' 3 := fun h => by
  have := @h 1 3 (by rw [of_one]; exact IsGroup.one); simp only [_root_.one_mul] at this; exact notGroup3 this

-- `Nimber.IsGroup.pow`
theorem c_23 : ¬ drop0% Nimber.IsGroup.pow 1 := fun h => by
  have := @h (∗3) 1; simp only [val_of, pow_one] at this; exact notGroup3 this

-- `Nimber.IsGroup.pow'`
theorem c_24 : ¬ drop0% Nimber.IsGroup.pow' 1 := fun h => by
  have := @h 3 1; simp only [pow_one] at this; exact notGroup3 this

-- `Nimber.IsRing.mul_lt`
theorem c_25 : ¬ drop0% Nimber.IsRing.mul_lt 1 := fun h => by
  have := @h (∗3) (∗2) (∗2) two_lt_three two_lt_three; rw [two_mul_two] at this; exact lt_irrefl _ this

-- `Nimber.IsRing.mul_lt`
theorem c_26 : ¬ drop0% Nimber.IsRing.mul_lt 4 := fun h => by
  have := @h (∗2) IsRing.two (∗2) 1 one_lt_two''; rw [_root_.mul_one] at this; exact lt_irrefl _ this

-- `Nimber.IsRing.mul_lt`
theorem c_27 : ¬ drop0% Nimber.IsRing.mul_lt 5 := fun h => by
  have := @h (∗2) IsRing.two 1 (∗2) one_lt_two''; rw [_root_.one_mul] at this; exact lt_irrefl _ this

-- `Nimber.IsRing.pow_lt`
theorem c_28 : ¬ drop0% Nimber.IsRing.pow_lt 2 := fun h => by
  have := @h 1 0 0 zero_lt_one; simp at this

-- `Nimber.IsRing.pow_lt`
theorem c_29 : ¬ drop0% Nimber.IsRing.pow_lt 4 := fun h => by
  have := @h (∗2) (∗2) IsRing.two 1; rw [pow_one] at this; exact lt_irrefl _ this

-- `Nimber.IsRing.sSup`
theorem c_30 : ¬ drop0% Nimber.IsRing.sSup 1 := fun h => by
  have := @h {1} (singleton_nonempty _) bddAbove_singleton
  rw [csSup_singleton] at this; exact lt_irrefl _ this.one_lt

-- `Nimber.IsRing.sSup`
theorem c_31 : ¬ drop0% Nimber.IsRing.sSup 2 := fun h => by
  have := @h ∅ (by simp) bddAbove_empty
  exact this.ne_zero (by rw [csSup_empty]; rfl)

-- `Nimber.IsRing.sSup`
theorem c_32 : ¬ drop0% Nimber.IsRing.sSup 3 := fun h => by
  have := @h {x | IsField x} (fun x hx => hx.toIsRing) ⟨∗2, IsField.two⟩
  exact this.ne_zero sSup_field

-- `Nimber.IsRing.iSup`
theorem c_33 : ¬ drop0% Nimber.IsRing.iSup 1 := fun h => by
  have := @h False (fun _ => 1) (fun i => i.elim) ⟨1, by rintro _ ⟨i, _⟩; exact i.elim⟩
  rw [ciSup_of_empty] at this; exact this.ne_zero rfl

-- `Nimber.IsRing.iSup`
theorem c_34 : ¬ drop0% Nimber.IsRing.iSup 3 := fun h => by
  have := @h True ⟨trivial⟩ (fun _ => 1) ⟨1, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  simp only [ciSup_const] at this; exact lt_irrefl _ this.one_lt

-- `Nimber.IsRing.iSup`
theorem c_35 : ¬ ∀ {ι : Type 1} [Nonempty ι] {f : ι → Nimber.{0}}, (∀ i, (f i).IsRing) →
    (⨆ i, f i).IsRing := fun h => by
  have := @h {x : Nimber.{0} // IsField x} ⟨⟨∗2, IsField.two⟩⟩ Subtype.val (fun i => i.2.toIsRing)
  rw [iSup, Subtype.range_coe_subtype] at this; exact this.ne_zero sSup_field

-- `Nimber.IsGroup.exists_mul_of_not_isRing`
theorem c_36 : ¬ drop0% Nimber.IsGroup.exists_mul_of_not_isRing 2 := fun h => by
  obtain ⟨y, hy, z, hz, e⟩ := @h (∗2) IsGroup.two two_ne_one
  rcases lt_two_iff.1 hy with rfl | rfl <;> rcases lt_two_iff.1 hz with rfl | rfl <;> simp at e
  all_goals first | exact two_ne_zero' e.symm | exact two_ne_one e.symm

-- `Nimber.IsGroup.mul_eq_of_lt'`
theorem c_37 : ¬ drop0% Nimber.IsGroup.mul_eq_of_lt' 9 := fun h => by
  have := @h 2 2 2 ω IsGroup.two IsGroup.two IsGroup.two le_rfl le_rfl (fun a ha => inv01 ha)
    (fun a b ha hb => IsRing.two.mul_lt (of.lt_iff_lt.2 ha) (of.lt_iff_lt.2 hb))
  rw [two_mul_omega, _root_.mul_comm, omega_mul_two, val_of] at this; exact omega_two_ne this.symm

-- `Nimber.IsGroup.mul_eq_of_lt`
theorem c_38 : ¬ drop0% Nimber.IsGroup.mul_eq_of_lt 9 := fun h => by
  have := @h (∗2) (∗2) (∗2) (∗ω) IsGroup.two IsGroup.two IsGroup.two le_rfl le_rfl
    (fun a ha => by rcases lt_two_iff.1 ha with rfl | rfl <;> simp [one_lt_two''])
    (fun a b ha hb => IsRing.two.mul_lt ha hb)
  simp only [val_of] at this
  rw [two_mul_omega] at this; exact two_omega_ne this.symm

-- `Nimber.IsRing.mul_eq_of_lt'`
theorem c_39 : ¬ drop0% Nimber.IsRing.mul_eq_of_lt' 6 := fun h => by
  have := @h 2 2 ω IsRing.two IsGroup.two le_rfl (fun a ha => inv01 ha)
  rw [two_mul_omega, _root_.mul_comm, omega_mul_two, val_of] at this; exact omega_two_ne this.symm

-- `Nimber.IsRing.mul_eq_of_lt`
theorem c_40 : ¬ drop0% Nimber.IsRing.mul_eq_of_lt 6 := fun h => by
  have := @h (∗2) (∗2) (∗ω) IsRing.two IsGroup.two le_rfl
    (fun a ha => by rcases lt_two_iff.1 ha with rfl | rfl <;> simp [one_lt_two''])
  simp only [val_of] at this
  rw [two_mul_omega] at this; exact two_omega_ne this.symm

-- `Nimber.IsField.inv_lt'`
theorem c_41 : ¬ drop0% Nimber.IsField.inv_lt' 1 := fun h => by
  have := @h (∗3) (∗2) two_ne_zero' two_lt_three; rw [inv_two] at this; exact lt_irrefl _ this

-- `Nimber.IsField.inv_lt'`
theorem c_42 : ¬ drop0% Nimber.IsField.inv_lt' 4 := fun h => by
  have := @h (∗2) IsField.two (∗2) two_ne_zero'; rw [inv_two] at this
  exact lt_asymm this two_lt_three

-- `Nimber.IsField.inv_lt`
theorem c_43 : ¬ drop0% Nimber.IsField.inv_lt 2 := fun h => by
  have := @h (∗3) (∗2) two_lt_three; rw [inv_two] at this; exact lt_irrefl _ this

-- `Nimber.IsField.inv_lt`
theorem c_44 : ¬ drop0% Nimber.IsField.inv_lt 3 := fun h => by
  have := @h (∗2) (∗2) IsField.two; rw [inv_two] at this; exact lt_asymm this two_lt_three

-- `Nimber.IsField.div_lt`
theorem c_45 : ¬ drop0% Nimber.IsField.div_lt 3 := fun h => by
  have := @h (∗3) 1 (∗2) one_lt_three two_lt_three; rw [one_div, inv_two] at this; exact lt_irrefl _ this

-- `Nimber.IsField.div_lt`
theorem c_46 : ¬ drop0% Nimber.IsField.div_lt 4 := fun h => by
  have := @h (∗2) (∗2) 1 IsField.two one_lt_two''; rw [_root_.div_one] at this; exact lt_irrefl _ this

-- `Nimber.IsField.div_lt`
theorem c_47 : ¬ drop0% Nimber.IsField.div_lt 5 := fun h => by
  have := @h (∗2) 1 (∗2) IsField.two one_lt_two''; rw [one_div, inv_two] at this
  exact lt_asymm this two_lt_three

-- `Nimber.IsField.sSup`
theorem c_48 : ¬ drop0% Nimber.IsField.sSup 2 := fun h => by
  have := @h ∅ (by simp) bddAbove_empty
  exact this.ne_zero (by rw [csSup_empty]; rfl)

-- `Nimber.IsField.sSup`
theorem c_49 : ¬ drop0% Nimber.IsField.sSup 3 := fun h => by
  have := @h {x | IsField x} (fun x hx => hx) ⟨∗2, IsField.two⟩
  exact this.ne_zero sSup_field

-- `Nimber.IsField.iSup`
theorem c_50 : ¬ drop0% Nimber.IsField.iSup 1 := fun h => by
  have := @h False (fun _ => 1) (fun i => i.elim) ⟨1, by rintro _ ⟨i, _⟩; exact i.elim⟩
  rw [ciSup_of_empty] at this; exact this.ne_zero rfl

-- `Nimber.IsField.iSup`
theorem c_51 : ¬ drop0% Nimber.IsField.iSup 3 := fun h => by
  have := @h True ⟨trivial⟩ (fun _ => 1) ⟨1, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  simp only [ciSup_const] at this; exact lt_irrefl _ this.one_lt

-- `Nimber.IsField.iSup`
theorem c_52 : ¬ ∀ {ι : Type 1} [Nonempty ι] {f : ι → Nimber.{0}}, (∀ i, (f i).IsField) →
    (⨆ i, f i).IsField := fun h => by
  have := @h {x : Nimber.{0} // IsField x} ⟨⟨∗2, IsField.two⟩⟩ Subtype.val (fun i => i.2)
  rw [iSup, Subtype.range_coe_subtype] at this; exact this.ne_zero sSup_field

-- `Nimber.IsField.mul_eq_of_lt`
theorem c_53 : ¬ drop0% Nimber.IsField.mul_eq_of_lt 6 := fun h => by
  have := @h (∗2) (∗2) (∗ω) IsRing.two IsField.two le_rfl
  simp only [val_of] at this
  rw [two_mul_omega] at this; exact two_omega_ne this.symm

-- `Nimber.IsField.mul_eq_of_lt'`
theorem c_54 : ¬ drop0% Nimber.IsField.mul_eq_of_lt' 6 := fun h => by
  have := @h 2 2 ω IsRing.two IsField.two le_rfl
  rw [two_mul_omega, _root_.mul_comm, omega_mul_two, val_of] at this; exact omega_two_ne this.symm

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Basic.0.Nimber.inv_lt_of_not_isField_aux`
theorem c_55 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Basic.«0».Nimber.inv_lt_of_not_isField_aux 2 := fun h => by
  have := (@h (∗2) IsRing.two).1; rw [inv_two] at this; exact lt_asymm this two_lt_three

-- `Nimber.IsRing.inv_lt_of_not_isField`
theorem c_56 : ¬ drop0% Nimber.IsRing.inv_lt_of_not_isField 3 := fun h => by
  have := @h (∗2) (∗2) IsRing.two (by rw [inv_two]; exact two_lt_three)
  rw [inv_two] at this; exact lt_asymm this two_lt_three

-- `Nimber.IsRing.inv_le_of_not_isField`
theorem c_57 : ¬ drop0% Nimber.IsRing.inv_le_of_not_isField 3 := fun h => by
  have := @h (∗2) (∗2) IsRing.two (by rw [inv_two]; exact two_lt_three.le)
  rw [inv_two] at this; exact not_le.2 two_lt_three this

-- `Nimber.IsRing.inv_lt_self_of_not_isField`
theorem c_58 : ¬ drop0% Nimber.IsRing.inv_lt_self_of_not_isField 2 := fun h => by
  have := @h (∗2) IsRing.two; rw [inv_two] at this; exact lt_asymm this two_lt_three

-- `Nimber.IsField.opow_mul_eq_of_lt'`
theorem c_59 : ¬ drop0% Nimber.IsField.opow_mul_eq_of_lt' 2 := fun h => by
  have := @h 3 2 1 (of.lt_iff_lt.1 two_lt_three)
  simp only [opow_one, pow_one] at this; rw [three_mul_two, val_one] at this
  exact absurd this (by exact_mod_cast (show (3 * 2 : ℕ) ≠ 1 by decide))

-- `Nimber.IsField.opow_mul_eq_of_lt'`
theorem c_60 : ¬ drop0% Nimber.IsField.opow_mul_eq_of_lt' 4 := fun h => by
  have := @h 2 ω IsField.two 1
  simp only [opow_one, pow_one] at this
  rw [two_mul_omega, _root_.mul_comm, omega_mul_two, val_of] at this
  exact omega_two_ne this.symm

-- `Nimber.IsField.opow_mul_eq_of_lt`
theorem c_61 : ¬ drop0% Nimber.IsField.opow_mul_eq_of_lt 2 := fun h => by
  have := @h (∗3) (∗2) 1 two_lt_three
  simp only [val_of, opow_one] at this; rw [three_mul_two, ← of_one, of.eq_iff_eq] at this
  exact absurd this (by exact_mod_cast (show (3 * 2 : ℕ) ≠ 1 by decide))

-- `Nimber.IsField.opow_mul_eq_of_lt`
theorem c_62 : ¬ drop0% Nimber.IsField.opow_mul_eq_of_lt 4 := fun h => by
  have := @h (∗2) (∗ω) IsField.two 1
  simp only [val_of, opow_one] at this
  rw [two_mul_omega] at this; exact two_omega_ne this.symm

-- `Nimber.IsField.pow_mul_eq_of_lt'`
theorem c_63 : ¬ drop0% Nimber.IsField.pow_mul_eq_of_lt' 2 := fun h => by
  have := @h 3 2 1 (of.lt_iff_lt.1 two_lt_three)
  simp only [opow_one, pow_one] at this; rw [three_mul_two, val_one] at this
  exact absurd this (by exact_mod_cast (show (3 * 2 : ℕ) ≠ 1 by decide))

-- `Nimber.IsField.pow_mul_eq_of_lt'`
theorem c_64 : ¬ drop0% Nimber.IsField.pow_mul_eq_of_lt' 4 := fun h => by
  have := @h 2 ω IsField.two 1
  simp only [opow_one, pow_one] at this
  rw [two_mul_omega, _root_.mul_comm, omega_mul_two, val_of] at this
  exact omega_two_ne this.symm

-- `Nimber.IsField.pow_mul_eq_of_lt`
theorem c_65 : ¬ drop0% Nimber.IsField.pow_mul_eq_of_lt 2 := fun h => by
  have := @h (∗3) (∗2) 1 two_lt_three
  simp only [val_of, pow_one] at this; rw [three_mul_two, ← of_one, of.eq_iff_eq] at this
  exact absurd this (by exact_mod_cast (show (3 * 2 : ℕ) ≠ 1 by decide))

-- `Nimber.IsField.pow_mul_eq_of_lt`
theorem c_66 : ¬ drop0% Nimber.IsField.pow_mul_eq_of_lt 4 := fun h => by
  have := @h (∗2) (∗ω) IsField.two 1
  simp only [val_of, pow_one] at this
  rw [two_mul_omega] at this; exact two_omega_ne this.symm

-- `Nimber.IsField.opow_log_eq_of_isGroup`
theorem c_67 : ¬ drop0% Nimber.IsField.opow_log_eq_of_isGroup 2 := fun h => by
  have := @h 1 (∗2) IsGroup.two (fun z w hz _ => by
    obtain rfl : z = 0 := by simpa using hz
    simpa using IsGroup.two.zero_lt)
  rw [val_one, one_opow, of_one] at this; exact two_ne_one this.symm

-- `Nimber.IsField.opow_log_eq_of_isGroup`
theorem c_68 : ¬ drop0% Nimber.IsField.opow_log_eq_of_isGroup 4 := fun h => by
  have := @h (∗ω) (∗2) IsField.omega0 IsGroup.two
  simp only [val_of] at this
  rw [log_eq_zero (by exact_mod_cast Ordinal.natCast_lt_omega0 2), opow_zero, of_one] at this
  exact two_ne_one this.symm

-- `Nimber.IsField.opow_log_eq_of_isRing`
theorem c_69 : ¬ drop0% Nimber.IsField.opow_log_eq_of_isRing 2 := fun h => by
  have := @h 1 (∗2) IsRing.two one_lt_two''.le
  rw [val_one, one_opow, of_one] at this; exact two_ne_one this.symm

-- `Nimber.IsField.opow_log_eq_of_isRing`
theorem c_70 : ¬ drop0% Nimber.IsField.opow_log_eq_of_isRing 3 := fun h => by
  have := @h (∗2) (∗3) IsField.two two_lt_three.le
  simp only [val_of] at this
  exact notGroup3 (this ▸ IsGroup.two_opow _)

-- `Nimber.IsField.opow_log_eq_of_isRing`
theorem c_71 : ¬ drop0% Nimber.IsField.opow_log_eq_of_isRing 4 := fun h => by
  have := @h (∗ω) (∗2) IsField.omega0 IsRing.two
  simp only [val_of] at this
  rw [log_eq_zero (by exact_mod_cast Ordinal.natCast_lt_omega0 2), opow_zero, of_one] at this
  exact two_ne_one this.symm

-- `Nimber.IsField.mul_lt_opow_of_left_lt`
theorem c_72 : ¬ drop0% Nimber.IsField.mul_lt_opow_of_left_lt 4 := fun h => by
  have := @h (∗3) (∗2) (∗2) 1 two_lt_three (by simpa using two_lt_three)
  simp only [val_of, opow_one] at this; rw [two_mul_two] at this; exact lt_irrefl _ this

-- `Nimber.IsField.mul_lt_opow_of_left_lt`
theorem c_73 : ¬ drop0% Nimber.IsField.mul_lt_opow_of_left_lt 5 := fun h => by
  have := @h (∗2) (∗2) 1 1 IsField.two (by simpa using one_lt_two'')
  simp only [val_of, opow_one, _root_.mul_one] at this; exact lt_irrefl _ this

-- `Nimber.IsField.mul_lt_opow_of_left_lt`
theorem c_74 : ¬ drop0% Nimber.IsField.mul_lt_opow_of_left_lt 6 := fun h => by
  have := @h (∗2) 1 (∗2) 0 IsField.two one_lt_two''
  simp only [val_of, opow_zero, _root_.one_mul, of_one] at this; exact lt_asymm this one_lt_two''

-- `Nimber.IsField.mul_lt_opow_of_right_lt`
theorem c_75 : ¬ drop0% Nimber.IsField.mul_lt_opow_of_right_lt 4 := fun h => by
  have := @h (∗3) (∗2) (∗2) 1 (by simpa using two_lt_three) two_lt_three
  simp only [val_of, opow_one] at this; rw [two_mul_two] at this; exact lt_irrefl _ this

-- `Nimber.IsField.mul_lt_opow_of_right_lt`
theorem c_76 : ¬ drop0% Nimber.IsField.mul_lt_opow_of_right_lt 5 := fun h => by
  have := @h (∗2) (∗2) 1 1 IsField.two one_lt_two''
  simp only [val_of, opow_one, _root_.mul_one] at this; exact lt_irrefl _ this

-- `Nimber.IsField.mul_lt_opow_of_right_lt`
theorem c_77 : ¬ drop0% Nimber.IsField.mul_lt_opow_of_right_lt 6 := fun h => by
  have := @h (∗2) 1 (∗2) 1 IsField.two (by simpa using one_lt_two'')
  simp only [val_of, opow_one, _root_.one_mul] at this; exact lt_irrefl _ this

-- `Nimber.IsField.mul_lt_pow_of_left_lt`
theorem c_78 : ¬ drop0% Nimber.IsField.mul_lt_pow_of_left_lt 4 := fun h => by
  have := @h (∗3) (∗2) (∗2) 1 two_lt_three (by simpa using two_lt_three)
  simp only [val_of, pow_one] at this; rw [two_mul_two] at this; exact lt_irrefl _ this

-- `Nimber.IsField.mul_lt_pow_of_left_lt`
theorem c_79 : ¬ drop0% Nimber.IsField.mul_lt_pow_of_left_lt 5 := fun h => by
  have := @h (∗2) (∗2) 1 1 IsField.two (by simpa using one_lt_two'')
  simp only [val_of, pow_one, _root_.mul_one] at this; exact lt_irrefl _ this

-- `Nimber.IsField.mul_lt_pow_of_left_lt`
theorem c_80 : ¬ drop0% Nimber.IsField.mul_lt_pow_of_left_lt 6 := fun h => by
  have := @h (∗2) 1 (∗2) 0 IsField.two one_lt_two''
  simp only [val_of, pow_zero, _root_.one_mul, of_one] at this; exact lt_asymm this one_lt_two''

-- `Nimber.IsField.mul_lt_pow_of_right_lt`
theorem c_81 : ¬ drop0% Nimber.IsField.mul_lt_pow_of_right_lt 4 := fun h => by
  have := @h (∗3) (∗2) (∗2) 1 (by simpa using two_lt_three) two_lt_three
  simp only [val_of, pow_one] at this; rw [two_mul_two] at this; exact lt_irrefl _ this

-- `Nimber.IsField.mul_lt_pow_of_right_lt`
theorem c_82 : ¬ drop0% Nimber.IsField.mul_lt_pow_of_right_lt 5 := fun h => by
  have := @h (∗2) (∗2) 1 1 IsField.two one_lt_two''
  simp only [val_of, pow_one, _root_.mul_one] at this; exact lt_irrefl _ this

-- `Nimber.IsField.mul_lt_pow_of_right_lt`
theorem c_83 : ¬ drop0% Nimber.IsField.mul_lt_pow_of_right_lt 6 := fun h => by
  have := @h (∗2) 1 (∗2) 1 IsField.two (by simpa using one_lt_two'')
  simp only [val_of, pow_one, _root_.one_mul] at this; exact lt_irrefl _ this

-- `Subfield.small_closure`
theorem c_84 : ¬ ∀ {R : Type 1} (s : Set R) [DivisionRing R], Small.{0} (Subfield.closure s) := fun h =>
  notSmallAll _ (fun x => Subfield.subset_closure (mem_univ x)) (@h Nimber.{0} univ _)

-- `Subfield.small_closure'`
theorem c_85 : ¬ ∀ {R : Type 1} (s : Set R) [DivisionRing R], Small.{0} ((Subfield.closure s : Set R)) :=
  fun h => notSmallAll _ (fun x => Subfield.subset_closure (mem_univ x)) (@h Nimber.{0} univ _)

-- `Nimber.isGroup_sInf_compl`
theorem c_90 : ¬ drop0% Nimber.isGroup_sInf_compl 1 := fun h => by
  have := @h ⊤; simp only [AddSubgroup.coe_top, compl_univ] at this; exact this.ne_zero sInf_empty'

-- `Nimber.isLowerSet_addSubgroupClosure`
theorem c_91 : ¬ drop0% Nimber.isLowerSet_addSubgroupClosure 1 := fun h => by
  have := (@h {∗2}) one_lt_two''.le (AddSubgroup.subset_closure (mem_singleton _))
  obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.1 this
  rw [zsmul_eq_mul] at hn
  have hr : (n : Nimber.{0}) ∈ range (Int.cast : ℤ → Nimber.{0}) := ⟨n, rfl⟩
  rw [CharTwo.range_intCast] at hr
  simp only [mem_insert_iff, mem_singleton_iff] at hr
  rcases hr with hr | hr
  · rw [hr] at hn; simp at hn
  · rw [hr, _root_.one_mul] at hn; exact two_ne_one hn

-- `Nimber.small_addSubgroupClosure`
theorem c_92 : ¬ drop0% Nimber.small_addSubgroupClosure 1 := fun h =>
  notSmallAll _ (fun x => AddSubgroup.subset_closure (mem_univ x)) (@h univ)

-- `Nimber.IsGroup.lt_groupClosure_iff`
theorem c_93 : ¬ drop0% Nimber.IsGroup.lt_groupClosure_iff 2 := fun h =>
  lt_irrefl _ ((@h (∗3) (∗3)).1 (lt_of_le_of_ne (le_groupClosure _)
    (fun e => notGroup3 (e ▸ IsGroup.groupClosure _))))

-- `Nimber.groupClosure_of_not_isGroup`
theorem c_94 : ¬ drop0% Nimber.groupClosure_of_not_isGroup 1 := fun h => by
  have := @h 1 one_ne_zero
  rw [IsGroup.one.groupClosure_eq, val_one, log_one_right, _root_.zero_add, opow_one] at this
  exact two_ne_one this.symm

-- `Nimber.groupClosure_of_not_isGroup`
theorem c_95 : ¬ drop0% Nimber.groupClosure_of_not_isGroup 2 := fun h => by
  have := @h 0 (fun g => g.ne_zero rfl)
  have hle : groupClosure (0 : Nimber.{0}) ≤ 1 := IsGroup.one.groupClosure_le_iff.2 (by simp)
  rw [this, val_zero, log_zero_right, _root_.zero_add, opow_one] at hle
  exact not_le.2 one_lt_two'' hle

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Closure.0.Nimber.exists_isGroup_le`
theorem c_96 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Closure.«0».Nimber.exists_isGroup_le 1 := fun h => by
  obtain ⟨y, hy, hle⟩ := @h 0; exact hy.ne_zero (le_antisymm hle (by simp))

-- `Nimber.exists_isGroup_between`
theorem c_97 : ¬ drop0% Nimber.exists_isGroup_between 1 := fun h => by
  obtain ⟨y, hy, -, -, hle, -⟩ := @h 0; exact hy.ne_zero (le_antisymm hle (by simp))

-- `Nimber.exists_isGroup_between'`
theorem c_98 : ¬ drop0% Nimber.exists_isGroup_between' 1 := fun h => by
  obtain ⟨y, hy, hle, -⟩ := @h 0; exact hy.ne_zero (le_antisymm hle (by simp))

-- `Nimber.IsGroup.mem_range_enumGroup`
theorem c_99 : ¬ drop0% Nimber.IsGroup.mem_range_enumGroup 1 := fun h =>
  notGroup3 (mem_range_enumGroup_iff.1 (@h (∗3)))

-- `Nimber.isRing_sInf_compl`
theorem c_100 : ¬ drop0% Nimber.isRing_sInf_compl 1 := fun h => by
  have := @h ⊤; simp only [Subring.coe_top, compl_univ] at this; exact this.ne_zero sInf_empty'

-- `Nimber.small_subringClosure`
theorem c_102 : ¬ drop0% Nimber.small_subringClosure 1 := fun h =>
  notSmallAll _ (fun x => Subring.subset_closure (mem_univ x)) (@h univ)

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Closure.0.Nimber.exists_isRing_le`
theorem c_103 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Closure.«0».Nimber.exists_isRing_le 1 := fun h => by
  obtain ⟨y, hy, hle⟩ := @h 1; exact not_le.2 hy.one_lt hle

-- `Nimber.exists_isRing_between`
theorem c_104 : ¬ drop0% Nimber.exists_isRing_between 1 := fun h => by
  obtain ⟨y, hy, -, -, hle, -⟩ := @h 1; exact not_le.2 hy.one_lt hle

-- `Nimber.IsRing.mem_range_enumRing`
theorem c_105 : ¬ drop0% Nimber.IsRing.mem_range_enumRing 1 := fun h =>
  lt_irrefl _ (mem_range_enumRing_iff.1 (@h 1)).one_lt

-- `Nimber.isField_sInf_compl`
theorem c_106 : ¬ drop0% Nimber.isField_sInf_compl 1 := fun h => by
  have := @h ⊤; simp only [Subfield.coe_top, compl_univ] at this; exact this.ne_zero sInf_empty'

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Closure.0.Nimber.exists_isField_le`
theorem c_108 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Closure.«0».Nimber.exists_isField_le 1 := fun h => by
  obtain ⟨y, hy, hle⟩ := @h 1; exact not_le.2 hy.one_lt hle

-- `Nimber.exists_isField_between`
theorem c_109 : ¬ drop0% Nimber.exists_isField_between 1 := fun h => by
  obtain ⟨y, hy, -, -, hle, -⟩ := @h 1; exact not_le.2 hy.one_lt hle

-- `Nimber.exists_isField_between'`
theorem c_110 : ¬ drop0% Nimber.exists_isField_between' 1 := fun h => by
  obtain ⟨y, hy, hle, -⟩ := @h 1; exact not_le.2 hy.one_lt hle

-- `Nimber.IsField.mem_range_enumField`
theorem c_111 : ¬ drop0% Nimber.IsField.mem_range_enumField 1 := fun h =>
  lt_irrefl _ (mem_range_enumField_iff.1 (@h 1)).one_lt

-- `IsClub.exists_between_closure`
theorem c_88 : ¬ drop0% IsClub.exists_between_closure 8 := fun h => by
  obtain ⟨l, hl, hl0, -⟩ := @h ℕ _ _ _ _ {n | 1 ≤ n} ⟨natClosed _, fun x => ⟨x + 1, by simp, by omega⟩⟩ 0
    (fun n => n + 1) (fun n => by omega) (fun n => by simp)
  simp at hl; omega

-- `IsClub.exists_between_closure`
theorem c_89 : ¬ drop0% IsClub.exists_between_closure 11 := fun h => by
  obtain ⟨l, hl, hl1, hlt⟩ := @h ℕ _ _ _ _ {n | Even n}
    ⟨natClosed _, fun x => ⟨2 * x, ⟨x, two_mul x⟩, by omega⟩⟩ 1 ⟨0, ⟨0, rfl⟩, by omega⟩ id (fun _ => le_rfl)
  simp only [id, Order.succ_eq_add_one] at hlt
  obtain rfl : l = 1 := by omega
  exact Nat.not_even_one hl

-- `IsClub.exists_between_closure`
theorem c_87 : ¬ ∀ {α : Type 1} [LinearOrder α] [WellFoundedLT α] [NoMaxOrder α] [SuccOrder α] {s : Set α}
    {x : α}, (∃ y ∈ s, y ≤ x) → ∀ {c : α → α}, (∀ x, x ≤ c x) → (∀ x, c x ∈ s) →
    ∃ l ∈ s, l ≤ x ∧ x < c (Order.succ l) := fun h => by
  classical
  obtain ⟨l, hl, hlx, hx⟩ := @h Ordinal.{0} _ _ _ _ {o | o ≠ ω} ω ⟨0, omega0_pos.ne, omega0_pos.le⟩
    (fun o => if o = ω then Order.succ ω else o)
    (fun o => by split_ifs with e <;> simp [e, Order.le_succ])
    (fun o => by
      split_ifs with e
      · exact (Order.lt_succ ω).ne'
      · exact e)
  have hl' : l < ω := lt_of_le_of_ne hlx hl
  have hs : Order.succ l < ω := isSuccLimit_omega0.succ_lt hl'
  simp only [hs.ne, ite_false] at hx
  exact lt_asymm hs hx

-- `Nimber.IsField.mul_eq_of_lt'`
theorem c_112 : ¬ drop0% Nimber.IsField.mul_eq_of_lt' 3 := fun h => by
  have h2 : (2 : Ordinal.{0}) < ω := by exact_mod_cast Ordinal.natCast_lt_omega0 2
  have h1 : (1 : Nimber.{0}) < ∗ω := by
    rw [← of_one, of.lt_iff_lt]; exact_mod_cast Ordinal.natCast_lt_omega0 1
  have := @h (ω + 1) ω 2 IsField.omega0 le_self_add h2
  have e1 : ∗(ω + 1) = ∗ω + (1 : Nimber.{0}) := by
    have := IsGroup.omega0.add_eq_of_lt h1
    simpa using this
  have e2 : ∗ω * ∗2 + ∗2 = (∗(ω * 2 + 2) : Nimber.{0}) := by
    rw [omega_mul_two]
    have := IsGroup.omega0.mul_add_eq_of_lt (y := ∗2) (of.lt_iff_lt.2 h2) 2
    simpa using this.symm
  have e3 : (ω + 1) * 2 = ω * 2 + (1 : Ordinal.{0}) := by
    rw [Ordinal.mul_two, Ordinal.mul_two, _root_.add_assoc, ← _root_.add_assoc 1 ω 1, one_add_omega0,
      _root_.add_assoc]
  have e4 : (∗ω + 1) * ∗2 = (∗(ω * 2 + 2) : Nimber.{0}) := by
    rw [_root_.add_mul (∗ω : Nimber.{0}) 1 (∗2), _root_.one_mul, e2]
  rw [e1, e4, val_of, e3] at this
  have := add_left_cancel this
  exact absurd this (by exact_mod_cast (show (1 : ℕ) ≠ 2 by decide))

-- `IsClub.exists_between_closure`
theorem c_86 : ¬ drop0% IsClub.exists_between_closure 2 := fun h => by
  classical
  have hs : IsClub {p : ℤ ×ₗ ℤ | (ofLex p).1 ≠ 0} := by
    refine ⟨fun d hds hne _ a ha => ?_, fun p => ⟨toLex (|(ofLex p).1| + 1, 0), ?_, ?_⟩⟩
    · by_contra hna
      simp only [mem_setOf_eq, not_not] at hna
      have hnot : toLex ((0 : ℤ), (ofLex a).2 - 1) ∉ upperBounds d := fun hub => by
        have := ha.2 hub
        rw [Prod.Lex.le_iff] at this; simp only [ofLex_toLex] at this; omega
      simp only [upperBounds, mem_setOf_eq, not_forall, not_le] at hnot
      obtain ⟨e, he, hlt⟩ := hnot
      have hea := ha.1 he
      have hes : (ofLex e).1 ≠ 0 := hds he
      rw [Prod.Lex.lt_iff] at hlt; rw [Prod.Lex.le_iff] at hea; simp only [ofLex_toLex] at hlt
      omega
    · have := abs_nonneg (ofLex p).1; simp only [mem_setOf_eq, ofLex_toLex]; omega
    · have := le_abs_self (ofLex p).1; rw [Prod.Lex.le_iff]; simp only [ofLex_toLex]; left; omega
  obtain ⟨l, hl, hlx, hxc⟩ := @h (ℤ ×ₗ ℤ) _ _ zzSucc _ hs (toLex (0, 0)) ⟨toLex (-1, 0), by simp,
      by rw [Prod.Lex.le_iff]; simp⟩
    (fun p => if (ofLex p).1 = 0 then toLex (1, 0) else p)
    (fun p => by
      split_ifs with e
      · rw [Prod.Lex.le_iff]; simp only [ofLex_toLex]; omega
      · exact le_rfl)
    (fun p => by
      split_ifs with e
      · simp
      · exact e)
  have hl' : (ofLex l).1 ≠ 0 := hl
  have e1 : @Order.succ (ℤ ×ₗ ℤ) _ zzSucc l = zsucc l := rfl
  rw [e1] at hxc
  have e2 : (ofLex (zsucc l)).1 ≠ 0 := by simpa [zsucc] using hl'
  simp only [e2, ite_false] at hxc
  rw [Prod.Lex.lt_iff] at hxc; rw [Prod.Lex.le_iff] at hlx
  simp only [zsucc, ofLex_toLex] at hxc hlx
  omega

-- `Nimber.IsGroup.mul_le_of_forall_lt`
theorem c_113 : ¬ drop0% Nimber.IsGroup.mul_le_of_forall_lt 1 := fun h => by
  have h45 : (∗4 : Nimber.{0}) < ∗5 := by rw [of.lt_iff_lt]; exact_mod_cast (show (4:ℕ) < 5 by decide)
  have := @h (∗5) (∗2) (∗4) (fun l hl => (field4.mul_lt two_lt_four hl).trans h45)
    (fun r hr => by
      rcases lt_two_iff.1 hr with rfl | rfl
      · simpa using zero_lt_four.trans h45
      · simpa using h45)
    (fun r hr l hl => (field4.mul_lt (hr.trans two_lt_four) hl).trans h45)
  rw [two_mul_four, of.le_iff_le] at this
  exact absurd this (by exact_mod_cast (show ¬ (4 * 2 : ℕ) ≤ 5 by decide))

-- `Nimber.IsGroup.mul_eq_of_lt'`
theorem c_114 : ¬ drop0% Nimber.IsGroup.mul_eq_of_lt' 11 := fun h => by
  have := @h (4 * 2) 4 4 2 g8 field4.toIsGroup field4.toIsGroup
    (by exact_mod_cast (show (4:ℕ) ≤ 4 * 2 by decide)) le_rfl
    (by exact_mod_cast (show (2:ℕ) < 4 by decide)) (fun a ha => field4.inv_lt (of.lt_iff_lt.2 ha))
  rw [eight_mul_two, val_of] at this
  exact absurd this (by exact_mod_cast (show (4 * 2 * 2 : ℕ) ≠ 4 * 3 by decide))

-- `Nimber.IsGroup.mul_eq_of_lt`
theorem c_115 : ¬ drop0% Nimber.IsGroup.mul_eq_of_lt 11 := fun h => by
  have := @h (∗(4 * 2)) (∗4) (∗4) (∗2) g8 field4.toIsGroup field4.toIsGroup
    (by rw [of.le_iff_le]; exact_mod_cast (show (4:ℕ) ≤ 4 * 2 by decide)) le_rfl two_lt_four
    (fun a ha => field4.inv_lt ha)
  rw [eight_mul_two] at this; simp only [val_of] at this; rw [of.eq_iff_eq] at this
  exact absurd this (by exact_mod_cast (show (4 * 2 * 2 : ℕ) ≠ 4 * 3 by decide))
