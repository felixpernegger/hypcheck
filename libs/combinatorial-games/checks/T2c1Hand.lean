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

namespace T2c1
open Nimber Polynomial Ordinal

-- in a finite nimber field some t^2 + t misses a value a (so X^2 + X + a has no root)
theorem asq {y : Nimber.{0}} (hy : IsField y) [Finite (Set.Iio y)] :
    ∃ a < y, ∀ t < y, t ^ 2 + t ≠ a := by
  by_contra! H
  let f : Set.Iio y → Set.Iio y := fun t => ⟨t.1 ^ 2 + t.1, hy.add_lt (hy.pow_lt t.2) t.2⟩
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨t, ht, e⟩ := H a.1 a.2
    exact ⟨⟨t, ht⟩, Subtype.ext e⟩
  have hi := Finite.injective_iff_surjective.2 hs
  have h01 : f ⟨0, hy.zero_lt⟩ = f ⟨1, hy.one_lt⟩ := by
    apply Subtype.ext; simp [f, CharTwo.add_self_eq_zero]
  have := congrArg Subtype.val (hi h01)
  simp at this

-- below a natural nimber there are finitely many nimbers
theorem finIio (N : ℕ) : Finite (Set.Iio (∗(N : Ordinal.{0}))) := by
  have hs : Set.Iio (∗(N : Ordinal.{0})) ⊆ (fun k : ℕ => ∗(k : Ordinal.{0})) '' Set.Iio N := by
    intro t ht
    have h1 : val t < N := ht
    obtain ⟨k, hk⟩ := Ordinal.lt_omega0.1 (h1.trans (natCast_lt_omega0 N))
    refine ⟨k, ?_, ?_⟩
    · rw [hk] at h1; exact_mod_cast h1
    · simp [← hk]
  exact (((Set.finite_Iio N).image _).subset hs).to_subtype

noncomputable def C3 : Nimber.{0}[X] := X ^ 3 + X + 1

theorem two0 : (2 : Nimber.{0}) = 0 := by
  rw [← one_add_one_eq_two]; exact CharTwo.add_self_eq_zero 1

theorem step {y : Nimber.{0}} (hy : IsField y) [Finite (Set.Iio y)]
    (hr : ∀ r < y, ¬ C3.IsRoot r) :
    IsField (∗(val y ^ 2)) ∧ ∀ r < ∗(val y ^ 2), ¬ C3.IsRoot r := by
  obtain ⟨a, ha, hA⟩ := asq hy
  have hQ : leastNoRoots y ≤ ((X ^ 2 + X + C a : Nimber.{0}[X])) := by
    apply leastNoRoots_le_of_not_isRoot
    · have : (X ^ 2 + X + C a : Nimber.{0}[X]).degree = 2 := by compute_degree!
      rw [this]; decide
    · exact hy.coeff_add_lt (hy.coeff_add_lt (coeff_X_pow_lt 2 hy.one_lt) (coeff_X_lt hy.one_lt))
        (coeff_C_lt ha)
    · intro r hr' h
      apply hA r hr'
      simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C] at h
      linear_combination h - a * two0
  have ht : leastNoRoots y ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hQ
  have hdeg : (y.leastNoRoots.untop ht).natDegree = 2 := by
    have h1 := hy.one_lt_natDegree_leastNoRoots ht
    have h2 : (y.leastNoRoots.untop ht).natDegree ≤ (X ^ 2 + X + C a : Nimber.{0}[X]).natDegree :=
      Lex.natDegree_mono ((WithTop.untop_le_iff ht).2 hQ)
    have : (X ^ 2 + X + C a : Nimber.{0}[X]).natDegree = 2 := by compute_degree!
    omega
  have hF := hy.pow_natDegree_leastNoRoots ht
  rw [hdeg] at hF
  refine ⟨hF, ?_⟩
  have hX2 : (.some (X ^ 2) : WithTop Nimber.{0}[X]) ≤ leastNoRoots y := hy.X_sq_lt_leastNoRoots.le
  have rep : ∀ z < ∗(val y ^ 2), ∃ b < y, ∃ a < y, z = b * y + a := by
    intro z hz
    obtain ⟨p, hpd, hpk, rfl⟩ := eq_oeval_of_lt_pow hy.ne_zero hz
    rw [← hy.eval_eq_of_lt hX2 hpd hpk]
    have : p.degree ≤ 1 := by
      have : p.degree < 2 := by exact_mod_cast hpd
      exact Order.le_of_lt_succ this
    rw [eq_X_add_C_of_degree_le_one this]
    exact ⟨_, hpk 1, _, hpk 0, by simp⟩
  have hyy : y < ∗(val y ^ 2) := by
    rw [← of_val y, of.lt_iff_lt]  
    simpa using lt_self_pow₀ hy.one_lt_val (by norm_num : 1 < 2)
  intro r hr0 hroot
  obtain ⟨b, hb, a, ha, rfl⟩ := rep r hr0
  obtain ⟨c, hc, e, he, hce⟩ := rep (y * y) (hF.mul_lt hyy hyy)
  have hroot' : (b * y + a) ^ 3 + (b * y + a) + 1 = 0 := by
    simpa [C3, IsRoot] using hroot
  have key : ((b * c) ^ 2 + ((b * c) * a + b ^ 2 * e + a ^ 2) + 1) * (b * y + a)
      + ((b * c) * ((b * c) * a + b ^ 2 * e + a ^ 2) + 1) = 0 := by
    linear_combination hroot' - (b * c + (b * y + a)) * b ^ 2 * hce
      - (b * c + (b * y + a)) * (a * b * y - a * b * c) * two0
  have hP : b * c < y := hy.mul_lt hb hc
  have hQ' : (b * c) * a + b ^ 2 * e + a ^ 2 < y :=
    hy.add_lt (hy.add_lt (hy.mul_lt hP ha) (hy.mul_lt (hy.pow_lt hb) he)) (hy.pow_lt ha)
  by_cases hD : (b * c) ^ 2 + ((b * c) * a + b ^ 2 * e + a ^ 2) + 1 = 0
  · rw [hD, zero_mul, zero_add] at key
    apply hr (b * c) hP
    simp only [C3, IsRoot, eval_add, eval_pow, eval_X, eval_one]
    linear_combination (b * c) * hD - key + two0
  · have hr1 : (b * y + a) * ((b * c) ^ 2 + ((b * c) * a + b ^ 2 * e + a ^ 2) + 1)
        = (b * c) * ((b * c) * a + b ^ 2 * e + a ^ 2) + 1 := by
      linear_combination key - ((b * c) * ((b * c) * a + b ^ 2 * e + a ^ 2) + 1) * two0
    have hr2 : b * y + a = ((b * c) * ((b * c) * a + b ^ 2 * e + a ^ 2) + 1) *
        ((b * c) ^ 2 + ((b * c) * a + b ^ 2 * e + a ^ 2) + 1)⁻¹ := (eq_mul_inv_iff_mul_eq₀ hD).2 hr1
    apply hr _ _ hroot
    rw [hr2]
    exact hy.mul_lt (hy.add_lt (hy.mul_lt hP hQ') hy.one_lt)
      (hy.inv_lt (hy.add_lt (hy.add_lt (hy.pow_lt hP) hQ') hy.one_lt))

-- the nimbers ∗(2^2^n)
noncomputable def Y (n : ℕ) : Nimber.{0} := ∗((2 ^ 2 ^ n : ℕ) : Ordinal.{0})

theorem Y_succ (n : ℕ) : Y (n + 1) = ∗(val (Y n) ^ 2) := by
  simp only [Y, val_of]
  congr 1
  rw [pow_succ, pow_mul]
  push_cast
  rfl

-- ∗(2^2^n) is a field and X^3 + X + 1 has no root below it
theorem mainY (n : ℕ) : IsField (Y n) ∧ ∀ r < Y n, ¬ C3.IsRoot r := by
  induction n with
  | zero =>
    have : Y 0 = ∗2 := by simp [Y]
    rw [this]
    refine ⟨IsField.two, fun r hr h => ?_⟩
    rcases Nimber.lt_two_iff.1 hr with rfl | rfl <;>
      simp [C3, IsRoot, CharTwo.add_self_eq_zero] at h
  | succ n ih =>
    have : Finite (Set.Iio (Y n)) := finIio _
    rw [Y_succ]
    exact step ih.1 ih.2

end T2c1

section
open Nimber Polynomial Ordinal T2c1

-- `Nimber.IsAlgClosed.omega` idx 1: necessary (x = 0: X^3 + X + 1 has no root below ∗ω)
theorem t2c1_1 : ¬ drop0% Nimber.IsAlgClosed.omega 1 := by
  intro h
  have hA : IsAlgClosed (∗ω : Nimber.{0}) := by simpa [Ordinal.omega_zero] using @h 0
  have hd : C3.degree = 3 := by unfold C3; compute_degree!
  obtain ⟨r, hr, hroot⟩ := hA.exists_root (p := C3) (by rw [hd]; decide)
    (hA.coeff_add_lt (hA.coeff_add_lt (coeff_X_pow_lt 3 hA.one_lt) (coeff_X_lt hA.one_lt))
      (coeff_one_lt hA.one_lt))
  have h1 : val r < ω := hr
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.1 h1
  have hlt : r < Y m := by
    show val r < ((2 ^ 2 ^ m : ℕ) : Ordinal.{0})
    rw [hm, Nat.cast_lt]
    calc m < 2 ^ m := Nat.lt_two_pow_self
      _ ≤ 2 ^ 2 ^ m := Nat.pow_le_pow_right (by norm_num) Nat.lt_two_pow_self.le
  exact (mainY m).2 r hlt hroot

end

namespace T2c1
open Polynomial IntermediateField

-- a real cube root of 2 (as the supremum of x with x^3 ≤ 2)
theorem cbrt2 : ∃ x : ℝ, x ^ 3 = 2 := by
  let S : Set ℝ := {x | x ^ 3 ≤ 2}
  have hne : S.Nonempty := ⟨1, by norm_num [S]⟩
  have hub2 : ∀ x ∈ S, x ≤ 2 := by
    intro x hx
    simp only [S, Set.mem_ofPred_eq] at hx
    by_contra h; push Not at h
    nlinarith [sq_nonneg x, sq_nonneg (x - 2)]
  have hbdd : BddAbove S := ⟨2, hub2⟩
  have h1 : 1 ≤ sSup S := le_csSup hbdd (by norm_num [S])
  have h2 : sSup S ≤ 2 := csSup_le hne hub2
  set s := sSup S
  refine ⟨s, le_antisymm ?_ ?_⟩
  · by_contra h; push Not at h
    have hε : 0 < (s ^ 3 - 2) / 12 := by linarith
    have hεs : (s ^ 3 - 2) / 12 ≤ s / 2 := by nlinarith [sq_nonneg s]
    have hlow : 2 ≤ (s - (s ^ 3 - 2) / 12) ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg ((s ^ 3 - 2) / 12)) (by linarith : (0:ℝ) ≤ 3 * s - (s ^ 3 - 2) / 12),
        mul_nonneg (mul_nonneg hε.le (by linarith : (0:ℝ) ≤ 2 - s)) (by linarith : (0:ℝ) ≤ 2 + s)]
    have hub : ∀ x ∈ S, x ≤ s - (s ^ 3 - 2) / 12 := by
      intro x hx
      simp only [S, Set.mem_ofPred_eq] at hx
      by_contra hlt; push Not at hlt
      have : (s - (s ^ 3 - 2) / 12) ^ 3 < x ^ 3 :=
        (Odd.strictMono_pow (by decide : Odd 3)) hlt
      linarith
    have := csSup_le hne hub
    linarith
  · by_contra h; push Not at h
    have hε : 0 < (2 - s ^ 3) / 19 := by linarith
    have hε1 : (2 - s ^ 3) / 19 ≤ 1 := by nlinarith [sq_nonneg s]
    have hmem : (s + (2 - s ^ 3) / 19) ^ 3 ≤ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hε.le hε.le) (by linarith : (0:ℝ) ≤ 1 - (2 - s ^ 3) / 19),
        mul_nonneg (mul_nonneg hε.le hε.le) (by linarith : (0:ℝ) ≤ 2 - s),
        mul_nonneg hε.le (by nlinarith : (0:ℝ) ≤ 4 - s ^ 2)]
    have := le_csSup hbdd (show s + (2 - s ^ 3) / 19 ∈ S from hmem)
    linarith

-- 2 has no rational cube root
theorem noRatCbrt (q : ℚ) : q ^ 3 ≠ 2 := by
  intro hq
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have h1 : (q.num : ℚ) ^ 3 = 2 * (q.den : ℚ) ^ 3 := by
    rw [← Rat.mul_den_eq_num, mul_pow, hq]
  have h2 : q.num ^ 3 = 2 * (q.den : ℤ) ^ 3 := by exact_mod_cast h1
  have hn : (2 : ℤ) ∣ q.num := Int.prime_two.dvd_of_dvd_pow (n := 3) ⟨_, h2⟩
  obtain ⟨k, hk⟩ := hn
  have h3 : (q.den : ℤ) ^ 3 = 2 * (2 * k ^ 3) := by rw [hk] at h2; ring_nf; ring_nf at h2; linarith
  have hdd : (2 : ℤ) ∣ (q.den : ℤ) := Int.prime_two.dvd_of_dvd_pow (n := 3) ⟨_, h3⟩
  have hcop := q.reduced
  have ha : (2 : ℕ) ∣ q.num.natAbs := by
    rw [hk, Int.natAbs_mul]; exact Dvd.dvd.mul_right (by decide) _
  have hb : (2 : ℕ) ∣ q.den := by exact_mod_cast hdd
  have := Nat.dvd_gcd ha hb
  rw [hcop] at this
  omega

end T2c1

section
open Polynomial IntermediateField T2c1

-- `IntermediateField.finrank_fixedField_eq_index` idx 7: necessary (E = ℚ(∛2) inside ℝ, H = ⊤)
theorem t2c1_2 : ¬ drop0% IntermediateField.finrank_fixedField_eq_index 7 := by
  intro h
  obtain ⟨α, hα⟩ := cbrt2
  have hint : IsIntegral ℚ α := ⟨X ^ 3 - C 2, monic_X_pow_sub_C _ (by norm_num), by simp [hα]⟩
  have := adjoin.finiteDimensional hint
  have h1 := @h ℚ ℚ⟮α⟯ _ _ _ ⊤ inferInstance
  rw [Subgroup.index_top, IntermediateField.finrank_eq_one_iff] at h1
  have hG := IsGalois.of_fixedField_eq_bot ℚ ℚ⟮α⟯ h1
  set a : ℚ⟮α⟯ := AdjoinSimple.gen ℚ α
  have h2c : ((2 : ℚ⟮α⟯) : ℝ) = 2 := by rw [← IntermediateField.algebraMap_apply, map_ofNat]
  have ha3 : a ^ 3 = 2 := Subtype.ext (by rw [IntermediateField.coe_pow, h2c]; simp [a, hα])
  have hdvd : minpoly ℚ a ∣ X ^ 3 - C 2 := minpoly.dvd ℚ a (by simp [ha3])
  have hspl := hG.to_normal.splits a
  have hsep : (minpoly ℚ a).Separable := Algebra.IsSeparable.isSeparable ℚ a
  have hcard := card_rootSet_eq_natDegree hsep hspl
  have key : ∀ b : (minpoly ℚ a).rootSet ℚ⟮α⟯, (b : ℚ⟮α⟯) = a := by
    intro b
    have hb := (mem_rootSet.1 b.2).2
    have hb3 : (b : ℚ⟮α⟯) ^ 3 = 2 := by
      obtain ⟨q, hq⟩ := hdvd
      have := congrArg (aeval (b : ℚ⟮α⟯)) hq
      simp only [map_sub, map_pow, aeval_X, aeval_C, map_mul, hb, zero_mul] at this
      simpa [sub_eq_zero] using this
    apply Subtype.ext
    have h3 : ((b : ℚ⟮α⟯) : ℝ) ^ 3 = α ^ 3 := by
      rw [hα, ← IntermediateField.coe_pow, hb3, h2c]
    exact (Odd.strictMono_pow (by decide : Odd 3)).injective h3
  have hle : Fintype.card ((minpoly ℚ a).rootSet ℚ⟮α⟯) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro b c
    exact Subtype.ext ((key b).trans (key c).symm)
  have hpos := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := ℚ) a)
  have hdeg : (minpoly ℚ a).natDegree = 1 := by omega
  obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.1 hdeg
  have hq' : (q : ℝ) = α := by
    have := congrArg (fun z : ℚ⟮α⟯ => (z : ℝ)) hq
    simpa [a] using this
  exact noRatCbrt q (by exact_mod_cast (show (q : ℝ) ^ 3 = 2 by rw [hq', hα]))

end

namespace T2c1
open Polynomial IntermediateField

abbrev E2 := AlgebraicClosure (ZMod 2)

theorem perMul {x : E2} {m : ℕ} (h : x ^ 2 ^ m = x) (k : ℕ) : x ^ 2 ^ (m * k) = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

theorem perMod {x : E2} {m : ℕ} (h : x ^ 2 ^ m = x) (a : ℕ) : x ^ 2 ^ a = x ^ 2 ^ (a % m) := by
  conv_lhs => rw [← Nat.mod_add_div a m, add_comm, pow_add, pow_mul, perMul h]

theorem perDvd {x : E2} {m n : ℕ} (h : x ^ 2 ^ m = x) (hd : m ∣ n) : x ^ 2 ^ n = x := by
  obtain ⟨k, rfl⟩ := hd; exact perMul h k

-- every element of the algebraic closure of F2 lies in a finite field
theorem period (x : E2) : ∃ d, 0 < d ∧ x ^ 2 ^ d = x := by
  have hi : IsIntegral (ZMod 2) x := Algebra.IsIntegral.isIntegral x
  have := adjoin.finiteDimensional hi
  have : Finite (ZMod 2)⟮x⟯ := Module.finite_of_finite (ZMod 2)
  let _ : Fintype (ZMod 2)⟮x⟯ := Fintype.ofFinite _
  have hc : Fintype.card (ZMod 2)⟮x⟯ = 2 ^ Module.finrank (ZMod 2) (ZMod 2)⟮x⟯ := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  refine ⟨Module.finrank (ZMod 2) (ZMod 2)⟮x⟯, Module.finrank_pos, ?_⟩
  rw [← hc]
  classical
  have key : ∀ y : (ZMod 2)⟮x⟯, y ^ Fintype.card (ZMod 2)⟮x⟯ = y := by
    intro y
    by_cases hy : y = 0
    · subst hy; exact zero_pow Fintype.card_ne_zero
    · have h1 := pow_card_eq_one (x := Units.mk0 y hy)
      rw [Fintype.card_units] at h1
      have h2 : y ^ (Fintype.card (ZMod 2)⟮x⟯ - 1) = 1 := by
        have := congrArg Units.val h1; simpa using this
      have hpos : 0 < Fintype.card (ZMod 2)⟮x⟯ := Fintype.card_pos
      calc y ^ Fintype.card (ZMod 2)⟮x⟯ = y ^ (Fintype.card (ZMod 2)⟮x⟯ - 1 + 1) := by
            rw [Nat.sub_add_cancel hpos]
        _ = y := by rw [pow_succ, h2, one_mul]
  have := congrArg Subtype.val (key (AdjoinSimple.gen (ZMod 2) x))
  simpa using this

-- product of the odd numbers up to 2N+1, the levels L N = 2^N * O N and exponents A N = O N ^ 2^N
def O (N : ℕ) : ℕ := ∏ i ∈ Finset.range (N + 1), (2 * i + 1)
def L (N : ℕ) : ℕ := 2 ^ N * O N
def A (N : ℕ) : ℕ := O N ^ 2 ^ N

theorem O_succ (N : ℕ) : O (N + 1) = O N * (2 * (N + 1) + 1) := Finset.prod_range_succ _ _

theorem O_odd (N : ℕ) : Odd (O N) := by
  induction N with
  | zero => simp [O]
  | succ N ih => rw [O_succ]; exact ih.mul (by simp)

theorem O_ge (N : ℕ) : 2 * N + 1 ≤ O N := by
  cases N with
  | zero => simp [O]
  | succ N =>
    rw [O_succ]
    have := (O_odd N).pos
    nlinarith

theorem dvd_O {u N : ℕ} (hu : Odd u) (h : u ≤ 2 * N + 1) : u ∣ O N := by
  obtain ⟨i, rfl⟩ := hu
  exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega))

theorem oddPow {u : ℕ} (hu : Odd u) (k : ℕ) : ∃ t, u ^ 2 ^ k = 1 + 2 ^ (k + 1) * t := by
  induction k with
  | zero => obtain ⟨t, rfl⟩ := hu; exact ⟨t, by ring⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t + 2 ^ k * t ^ 2, by rw [pow_succ, pow_mul, ht]; ring⟩

theorem L_dvd_succ (N : ℕ) : L N ∣ L (N + 1) := by
  unfold L; rw [O_succ, pow_succ]
  exact Nat.mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_right _ _)

theorem L_dvd {N M : ℕ} (h : N ≤ M) : L N ∣ L M := by
  induction M, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ M _ ih => exact ih.trans (L_dvd_succ M)

theorem O_dvd_L (N : ℕ) : O N ∣ L N := dvd_mul_left _ _
theorem O_dvd_A (N : ℕ) : O N ∣ A N := dvd_pow_self _ (by positivity)

theorem A_compat_succ (N : ℕ) : A (N + 1) ≡ A N [MOD L N] := by
  have hcop : Nat.Coprime (2 ^ N) (O N) :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).2 (O_odd N))
  apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).1
  constructor
  · obtain ⟨t, ht⟩ := oddPow (O_odd (N + 1)) (N + 1)
    obtain ⟨s, hs⟩ := oddPow (O_odd N) N
    unfold A; rw [ht, hs]
    have e1 : 1 + 2 ^ (N + 1 + 1) * t = 1 + 2 ^ N * (4 * t) := by ring
    have e2 : 1 + 2 ^ (N + 1) * s = 1 + 2 ^ N * (2 * s) := by ring
    rw [e1, e2]; unfold Nat.ModEq; simp [Nat.add_mul_mod_self_left]
  · have h1 : O N ∣ A (N + 1) := Nat.dvd_trans (by rw [O_succ]; exact dvd_mul_right _ _) (O_dvd_A _)
    exact (Nat.modEq_zero_iff_dvd.2 h1).trans (Nat.modEq_zero_iff_dvd.2 (O_dvd_A N)).symm

theorem A_compat {N M : ℕ} (h : N ≤ M) : A M ≡ A N [MOD L N] := by
  induction M, h using Nat.le_induction with
  | base => rfl
  | succ M hNM ih => exact ((A_compat_succ M).of_dvd (L_dvd hNM)).trans ih

theorem periodL (x : E2) : ∃ N, x ^ 2 ^ L N = x := by
  obtain ⟨d, hd, h⟩ := period x
  obtain ⟨k, u, hu, hdu⟩ := Nat.exists_eq_two_pow_mul_odd hd.ne'
  refine ⟨d, perDvd h ?_⟩
  have hk : 2 ^ k ≤ d := Nat.le_of_dvd hd ⟨u, hdu⟩
  have hu' : u ≤ d := Nat.le_of_dvd hd ⟨2 ^ k, by rw [hdu, mul_comm]⟩
  have hk' : k ≤ d := (Nat.lt_two_pow_self).le.trans hk
  nth_rw 1 [hdu]; unfold L
  exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 hk') (dvd_O hu (by omega))

open Classical in
noncomputable def sN (x : E2) : ℕ := Nat.find (periodL x)

noncomputable def sig (x : E2) : E2 := x ^ 2 ^ A (sN x)

theorem sig_eq {x : E2} {M : ℕ} (h : x ^ 2 ^ L M = x) : sig x = x ^ 2 ^ A M := by
  classical
  have h0 : x ^ 2 ^ L (sN x) = x := Nat.find_spec (periodL x)
  unfold sig
  calc x ^ 2 ^ A (sN x) = x ^ 2 ^ (A (sN x) % L (sN x)) := perMod h0 _
    _ = x ^ 2 ^ (A (max (sN x) M) % L (sN x)) := by rw [A_compat (le_max_left (sN x) M)]
    _ = x ^ 2 ^ A (max (sN x) M) := (perMod h0 _).symm
    _ = x ^ 2 ^ (A (max (sN x) M) % L M) := perMod h _
    _ = x ^ 2 ^ (A M % L M) := by rw [A_compat (le_max_right (sN x) M)]
    _ = x ^ 2 ^ A M := (perMod h _).symm

theorem zmod2_pow (c : ZMod 2) (n : ℕ) : c ^ 2 ^ n = c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, ih]
    have h2 : ∀ d : ZMod 2, d ^ 2 = d := by decide
    exact h2 c

theorem common (x y : E2) : ∃ M, x ^ 2 ^ L M = x ∧ y ^ 2 ^ L M = y := by
  obtain ⟨Nx, hx⟩ := periodL x
  obtain ⟨Ny, hy⟩ := periodL y
  exact ⟨max Nx Ny, perDvd hx (L_dvd (le_max_left _ _)), perDvd hy (L_dvd (le_max_right _ _))⟩

noncomputable def sigH : E2 →ₐ[ZMod 2] E2 where
  toFun := sig
  map_one' := by unfold sig; simp
  map_mul' x y := by
    obtain ⟨M, hx, hy⟩ := common x y
    rw [sig_eq hx, sig_eq hy, sig_eq (show (x * y) ^ 2 ^ L M = x * y by rw [mul_pow, hx, hy]),
      mul_pow]
  map_zero' := by unfold sig; simp
  map_add' x y := by
    obtain ⟨M, hx, hy⟩ := common x y
    rw [sig_eq hx, sig_eq hy,
      sig_eq (show (x + y) ^ 2 ^ L M = x + y by rw [add_pow_char_pow, hx, hy]),
      add_pow_char_pow]
  commutes' c := by
    obtain ⟨M, hx⟩ := periodL (algebraMap (ZMod 2) E2 c)
    show sig _ = _
    rw [sig_eq hx, ← map_pow, zmod2_pow]

noncomputable def sigma : Gal(E2/ZMod 2) :=
  AlgEquiv.ofBijective sigH (Algebra.IsAlgebraic.algHom_bijective sigH)

theorem sigma_apply (x : E2) : sigma x = sig x := rfl

noncomputable def phiH : E2 →ₐ[ZMod 2] E2 where
  toFun x := x ^ 2
  map_one' := by simp
  map_mul' x y := by simp [mul_pow]
  map_zero' := by simp
  map_add' x y := by simpa using add_pow_char_pow x y 2 1
  commutes' c := by simpa using (congrArg (algebraMap (ZMod 2) E2) (zmod2_pow c 1)).symm.trans (map_pow _ _ _) |>.symm

noncomputable def phi : Gal(E2/ZMod 2) :=
  AlgEquiv.ofBijective phiH (Algebra.IsAlgebraic.algHom_bijective phiH)

theorem phi_pow_apply (k : ℕ) (x : E2) : (phi ^ k) x = x ^ 2 ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, ih]; show (x ^ 2) ^ 2 ^ k = _; rw [← pow_mul, ← pow_succ']

theorem two0E : (2 : E2) = 0 := CharTwo.two_eq_zero

theorem fixK (n : ℤ) (y : E2) (h : (phi ^ n) y = y) : y ^ 2 ^ n.natAbs = y := by
  cases n with
  | ofNat k => rw [Int.ofNat_eq_natCast, zpow_natCast, phi_pow_apply] at h; simpa using h
  | negSucc k =>
    rw [zpow_negSucc] at h
    have := congrArg (phi ^ (k + 1)) h
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, phi_pow_apply] at this
    simpa using this.symm

theorem sepP (m : ℕ) (hm : 0 < m) : (X ^ 2 ^ m - X : E2[X]).Separable := by
  rw [separable_def, derivative_sub, derivative_X_pow, derivative_X]
  have : ((2 ^ m : ℕ) : E2) = 0 := by push_cast; rw [two0E, zero_pow hm.ne']
  rw [this, C_0, zero_mul, zero_sub]
  exact isCoprime_one_right.neg_right

theorem degP (m : ℕ) (hm : 0 < m) : (X ^ 2 ^ m - X : E2[X]).natDegree = 2 ^ m := by
  rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [Nat.one_lt_two_pow hm.ne']

open Classical in
theorem cardP (m : ℕ) (hm : 0 < m) : (X ^ 2 ^ m - X : E2[X]).roots.toFinset.card = 2 ^ m := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots (sepP m hm)),
    IsAlgClosed.card_roots_eq_natDegree, degP m hm]

open Classical in
theorem sigma_not_mem : sigma ∉ Subgroup.zpowers phi := by
  rintro ⟨n, hn⟩
  simp only at hn
  by_cases hK : n.natAbs = 0
  · have : n = 0 := Int.natAbs_eq_zero.1 hK
    subst this
    rw [zpow_zero] at hn
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_root (X ^ 2 + X + 1 : E2[X]) (by
      rw [show (X ^ 2 + X + 1 : E2[X]).degree = 2 by compute_degree!]; decide)
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hw
    have h4 : w ^ 2 ^ 2 = w := by linear_combination (w ^ 2 + w) * hw - (w ^ 3 + w ^ 2 + w) * two0E
    have hL : w ^ 2 ^ L 1 = w := perDvd h4 (by decide)
    have h1 : sigma w = w := by rw [← hn]; rfl
    rw [sigma_apply, sig_eq hL, perMod h4, show A 1 % 2 = 1 by decide] at h1
    have : (1 : E2) = 0 := by linear_combination hw - h1 - w * two0E
    exact one_ne_zero this
  · set K := n.natAbs
    have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    have hOpos : 0 < O K := (O_odd K).pos
    have hsub : (X ^ 2 ^ O K - X : E2[X]).roots.toFinset ⊆ (X ^ 2 ^ K - X : E2[X]).roots.toFinset := by
      intro y hy
      have hne : (X ^ 2 ^ O K - X : E2[X]) ≠ 0 := by
        intro h0; have := degP (O K) hOpos; rw [h0] at this; simp at this; exact (Nat.two_pow_pos _).ne this
      rw [Multiset.mem_toFinset, mem_roots hne] at hy
      simp only [IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero] at hy
      have hL : y ^ 2 ^ L K = y := perDvd hy (O_dvd_L K)
      have hs : sigma y = y := by
        rw [sigma_apply, sig_eq hL, perMod hy, Nat.mod_eq_zero_of_dvd (O_dvd_A K)]; simp
      have hp : (phi ^ n) y = y := by rw [hn]; exact hs
      have hy2 := fixK n y hp
      have hne2 : (X ^ 2 ^ K - X : E2[X]) ≠ 0 := by
        intro h0; have := degP K hKpos; rw [h0] at this; simp at this; exact (Nat.two_pow_pos _).ne this
      rw [Multiset.mem_toFinset, mem_roots hne2]
      simp only [IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]; exact hy2
    have h1 := Finset.card_le_card hsub
    rw [cardP _ hOpos] at h1
    have h2 : (X ^ 2 ^ K - X : E2[X]).roots.toFinset.card ≤ 2 ^ K :=
      (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (degP K hKpos).le)
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans h2)
    have := O_ge K
    omega

-- the Frobenius powers fix only F2
theorem fixed_bot : fixedField (Subgroup.zpowers phi) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_fixedField_iff] at hx
  have h2 : x ^ 2 = x := hx phi (Subgroup.mem_zpowers phi)
  have : x * (x - 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 this with h0 | h1
  · rw [h0]; exact zero_mem _
  · rw [sub_eq_zero.1 h1]; exact one_mem _

end T2c1

section
open IntermediateField T2c1

-- `IntermediateField.finrank_fixedField_eq_index` idx 6: necessary (E = algebraic closure of F2, H = powers of Frobenius: fixed field F2, but H is not everything)
theorem t2c1_3 : ¬ drop0% IntermediateField.finrank_fixedField_eq_index 6 := by
  intro h
  have h1 := @h (ZMod 2) E2 _ _ _ (Subgroup.zpowers phi) inferInstance
  rw [fixed_bot, IntermediateField.finrank_bot] at h1
  have := Subgroup.index_eq_one.1 h1.symm
  exact sigma_not_mem (this ▸ Subgroup.mem_top sigma)

end
