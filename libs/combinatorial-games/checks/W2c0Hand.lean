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

namespace W2c0
open Nimber Polynomial Ordinal Order Set

-- helper: Ici a is a club in the ordinals
theorem clubIci (a : Ordinal.{0}) : IsClub (Ici a) :=
  ⟨DirSupClosed.Ici a, fun b => ⟨max a b, Set.mem_Ici.2 (le_max_left _ _), le_max_right _ _⟩⟩

-- helper: the integers are not well-founded
theorem notWfZ : ¬ WellFoundedLT ℤ := fun h => by
  obtain ⟨m, -, hm⟩ := (@wellFounded_lt ℤ _ h).has_min Set.univ ⟨0, trivial⟩
  exact hm (m - 1) trivial (by omega)

-- helper: Fin 2 is not a regular cardinal order
theorem notRegFin2 : ¬ IsRegularCardinalOrder (Fin 2) := fun h => by
  have := h.type_lt_le_ord_cof
  rw [Order.cof_eq_one] at this
  simp at this

-- `InitialSeg.le_of_strictMono`
theorem c_1 : ¬ drop0% InitialSeg.le_of_strictMono 4 := fun h => by
  have := h (InitialSeg.refl (α := ℤ) (· < ·)) (g := fun x => x - 1) (fun a b hab => by simp; omega) 0
  simp at this

-- `Order.enum_le_of_strictMono`
theorem c_2 : ¬ indep0% Order.enum_le_of_strictMono 2 := fun h =>
  notWfZ (@h ℤ _ Set.univ (fun b => ⟨b, trivial, le_rfl⟩) 1 0 (fun z => ⟨z.1, trivial⟩)
    (fun a b hab => hab) (by norm_num))

-- `Order.enum_le_of_strictMono`
theorem c_3 : ¬ indep0% Order.enum_le_of_strictMono 3 := fun h =>
  notRegFin2 (@h (Fin 2) _ _ Set.univ (fun b => ⟨b, trivial, le_rfl⟩) 1 0 (fun z => ⟨z.1, trivial⟩)
    (fun a b hab => hab) (by decide))

-- `Order.enum_le_of_strictMono`
theorem c_4 : ¬ drop0% Order.enum_le_of_strictMono 9 := fun h => by
  have := @h ℕ _ _ _ Set.univ (fun b => ⟨b, trivial, le_rfl⟩) 2 1 (fun _ => ⟨0, trivial⟩) (by norm_num)
  rw [Order.enum_univ] at this
  exact absurd (Subtype.coe_le_coe.2 this) (by simp)

-- `Ordinal.enum_lt_of_lt_ord_cof`
theorem c_5 : ¬ indep0% Ordinal.enum_lt_of_lt_ord_cof 1 := fun h => by
  have := @h (Iio 1) 1 0 (fun a ha => ⟨a, ha, le_rfl, ha⟩) (by simp)
  obtain ⟨b, hb, hle⟩ := this 1
  exact absurd (lt_of_lt_of_le hb hle) (lt_irrefl _)

-- `Ordinal.enum_lt_of_lt_ord_cof`
theorem c_6 : ¬ drop0% Ordinal.enum_lt_of_lt_ord_cof 4 := fun h => by
  have := @h (Ici 1) (clubIci 1).isCofinal 1 0 (by simp)
  have h2 := (Order.enum (Ici 1) (clubIci 1).isCofinal 0).2
  rw [Set.mem_Ici] at h2
  exact absurd (h2.trans_lt this) (lt_irrefl _)

-- `Ordinal.enum_ord_cof_le`
theorem c_7 : ¬ indep0% Ordinal.enum_ord_cof_le 1 := fun h => by
  have := @h (Iio ω) ω (fun a ha => ⟨a, ha, le_rfl, ha⟩) isSuccLimit_omega0
  obtain ⟨b, hb, hle⟩ := this.isCofinal ω
  exact absurd (lt_of_lt_of_le hb hle) (lt_irrefl _)

-- `Ordinal.enum_ord_cof_le`
theorem c_8 : ¬ drop0% Ordinal.enum_ord_cof_le 3 := fun h => by
  have h1 := @h (Ici (ω + 1)) (clubIci _) ω isSuccLimit_omega0
  have h2 := (Order.enum (Ici (ω + 1)) (clubIci (ω + 1)).isCofinal ((Ordinal.cof ω).ord)).2
  rw [Set.mem_Ici] at h2
  exact absurd (h2.trans h1) (by simp)

-- `Ordinal.enum_ord_cof_le`
theorem c_9 : ¬ drop0% Ordinal.enum_ord_cof_le 4 := fun h => by
  have h1 := @h (Ici 1) (clubIci _) 0 (fun a ha => by simp at ha)
  have h2 := (Order.enum (Ici 1) (clubIci 1).isCofinal ((0 : Ordinal).cof.ord)).2
  rw [Set.mem_Ici] at h2
  exact absurd (h2.trans h1) (by simp)

-- `Nimber.card_algClosure`
theorem c_10 : ¬ drop0% Nimber.card_algClosure 1 := fun h => by
  have hω := (IsAlgClosed.algClosure (0 : Nimber.{0})).omega0_le
  have h1 : ω ≤ val (algClosure 0) := by rw [← of.le_iff_le]; simpa using hω
  have h2 := Ordinal.card_le_card h1
  rw [h (x := 0)] at h2
  simp at h2

-- `Nimber.enumAlgClosed_omega`
theorem c_11 : ¬ drop0% Nimber.enumAlgClosed_omega 1 := fun h => by
  have h1 := h (x := 0)
  rw [Ordinal.omega_zero] at h1
  have h2 := (IsAlgClosed.enumAlgClosed 0).omega0_le
  have h3 := isNormal_enumAlgClosed.strictMono (Ordinal.omega0_pos)
  rw [h1] at h3
  exact absurd (h2.trans_lt h3) (lt_irrefl _)


-- helper: 2 ^ 2 = 4 for ordinals
theorem pow22 : (2 : Ordinal) ^ (2 : ℕ) = 4 := by
  rw [pow_two]
  have : ((2 : ℕ) : Ordinal) * ((2 : ℕ) : Ordinal) = ((4 : ℕ) : Ordinal) := by
    rw [← Ordinal.natCast_mul]
  simpa using this

-- helper: ∗3 is not a group
theorem notGroup3 : ¬ IsGroup (∗3 : Nimber.{0}) := by
  intro h
  have e : ∗2 + 1 = ∗3 := by
    have := IsGroup.two.add_eq_of_lt (y := 1) (by simp)
    rw [← this]; simp; norm_num
  have := h.add_lt (y := ∗2) (z := 1) (by rw [of.lt_iff_lt]; exact_mod_cast (show (2:ℕ) < 3 by decide)) (by simp)
  rw [e] at this; exact lt_irrefl _ this

-- helper: nimbers below ∗2
theorem lt_two {a : Nimber} (ha : a < ∗2) : a = 0 ∨ a = 1 := by
  rw [← succ_one, Order.lt_succ_iff, Nimber.le_one_iff] at ha
  exact ha

-- helper: ∗2 * ∗2 ≤ ∗3
theorem two_mul_two_le : (∗2 : Nimber.{0}) * ∗2 ≤ ∗3 := by
  apply mul_le_of_forall_ne
  intro a ha b hb
  have h23 : (∗2 : Nimber.{0}) ≠ ∗3 := by
    rw [ne_eq, of.apply_eq_iff_eq]; exact_mod_cast (show (2:ℕ) ≠ 3 by decide)
  have h13 : (1 : Nimber.{0}) ≠ ∗3 := by
    intro e; have := congrArg val e; simp at this
  have h03 : (0 : Nimber.{0}) ≠ ∗3 := by
    intro e; have := congrArg val e; simp at this
  rcases lt_two ha with rfl | rfl <;> rcases lt_two hb with rfl | rfl <;> simp [CharTwo.add_self_eq_zero] <;> assumption

-- helper: 1 ≠ ∗2
theorem one_ne_two : (1 : Nimber.{0}) ≠ ∗2 := by
  intro e; have := congrArg val e; simp at this

-- helper: ∗2 * ∗2 ≠ 1
theorem two_mul_two_ne_one : (∗2 : Nimber.{0}) * ∗2 ≠ 1 := by
  have := mul_ne_of_ne (a := ∗2) (b := ∗2) (a' := 1) (b' := 1) one_ne_two one_ne_two
  simpa [CharTwo.add_self_eq_zero] using this.symm

-- helper: (∗2)² < ∗(2²)
theorem two_sq_lt : (∗2 : Nimber.{0}) ^ 2 < ∗((2 : Ordinal) ^ (2 : ℕ)) := by
  rw [pow_two, pow22]
  apply two_mul_two_le.trans_lt
  rw [of.lt_iff_lt]; exact_mod_cast (show (3:ℕ) < 4 by decide)

-- helper: ∗2 is not algebraically closed
theorem notAC2 : ¬ IsAlgClosed (∗2 : Nimber.{0}) := fun hc =>
  absurd hc.omega0_le (by rw [of.le_iff_le]; exact not_le.2 (by simpa using Ordinal.natCast_lt_omega0 2))

-- helper: the least polynomial without roots below ∗2 exists
theorem ht2 : leastNoRoots (∗2 : Nimber.{0}) ≠ ⊤ := fun e =>
  notAC2 ((isAlgClosed_iff_leastNoRoots_eq_top IsRing.two).2 e)

-- helper: the first algebraically closed nimber
noncomputable def T : Nimber.{0} := algClosure 0
theorem hT : IsAlgClosed T := IsAlgClosed.algClosure 0

-- helper: the field generated by T and one more element
noncomputable def F : Nimber.{0} := fieldClosure (succ T)
theorem hF : IsField F := IsField.fieldClosure _
theorem T_lt_F : T < F := (lt_succ T).trans_le (le_fieldClosure _)
theorem sqrtT : √T = F := hT.sqrt_eq
theorem lnrF : leastNoRoots F = .some (X ^ 2 + C T) := hT.leastNoRoots_fieldClosure_succ

-- helper: F is not perfect
theorem notPerfF : ¬ PerfectField hF.toSubfield := by
  rw [hF.perfectField_iff_leastNoRoots, lnrF, WithTop.coe_le_coe, not_le, Lex.lt_def]
  refine ⟨1, fun k hk => ?_, ?_⟩
  · simp [coeff_X, coeff_C, coeff_X_pow]
    rw [if_neg (by omega), if_neg (by omega)]
  · simp [coeff_X, coeff_C, coeff_X_pow]

-- helper: T is perfect
theorem perfT : PerfectField hT.toIsField.toSubfield :=
  hT.toIsField.perfectField_of_le_algClosure_zero le_rfl

-- helper: the square root of an algebraically closed t is not below t
theorem sqrt_not_lt {t : Nimber} (ht : IsAlgClosed t) : ¬ √t < t := fun h => by
  have := ht.mul_lt h h
  rw [sqrt_mul_sqrt_self] at this
  exact lt_irrefl _ this

-- `Nimber.IsRing.eval_eq_of_lt`
theorem c_16 : ¬ drop0% Nimber.IsRing.eval_eq_of_lt 3 := fun h => by
  have := @h 3 (∗2) IsRing.two (X ^ 2) (by rw [degree_X_pow]; norm_num) (coeff_X_pow_lt 2 (by simp))
  rw [eval_pow, eval_X, oeval_X_pow, val_of] at this
  exact two_sq_lt.ne this

-- `Nimber.IsRing.eval_eq_of_lt`
theorem c_17 : ¬ drop0% Nimber.IsRing.eval_eq_of_lt 5 := fun h => by
  have h0 : (↑((X : Nimber[X]) ^ 0) : WithTop Nimber[X]) ≤ leastNoRoots (∗2) :=
    (WithTop.coe_le_coe.2 (Lex.X_pow_le_X_pow_iff.2 (by norm_num))).trans IsField.two.X_sq_lt_leastNoRoots.le
  have := @h 0 (∗2) IsRing.two h0 (X ^ 2) (coeff_X_pow_lt 2 (by simp))
  rw [eval_pow, eval_X, oeval_X_pow, val_of] at this
  exact two_sq_lt.ne this

-- `Nimber.IsRing.pow_mul_eq`
theorem c_18 : ¬ drop0% Nimber.IsRing.pow_mul_eq 4 := fun h => by
  have := @h 2 (∗2) 1 IsRing.two (by simp)
  rw [mul_one, val_one, mul_one, val_of] at this
  exact two_sq_lt.ne this

-- `Nimber.IsRing.pow_mul_eq`
theorem c_19 : ¬ drop0% Nimber.IsRing.pow_mul_eq 5 := fun h => by
  have := @h 1 (∗2) (∗2) IsRing.two IsField.two.X_sq_lt_leastNoRoots.le
  rw [pow_one, pow_one, val_of, ← pow_two, ← pow_two] at this
  exact two_sq_lt.ne this

-- `Nimber.IsRing.pow_eq`
theorem c_20 : ¬ drop0% Nimber.IsRing.pow_eq 3 := fun h => by
  have := @h 2 (∗2) IsRing.two
  rw [val_of] at this
  exact two_sq_lt.ne this


-- helper: succ ∗2 = ∗3
theorem succ_two : Order.succ (∗2 : Nimber.{0}) = ∗3 := two_add_one_eq_three (R := Ordinal)

-- helper: nimbers below ∗3
theorem lt_three {a : Nimber.{0}} (ha : a < ∗3) : a = 0 ∨ a = 1 ∨ a = ∗2 := by
  rw [← succ_two, Order.lt_succ_iff] at ha
  rcases ha.lt_or_eq with h | h
  · rcases lt_two h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem two_lt_three : (∗2 : Nimber.{0}) < ∗3 := by
  rw [← succ_two]; exact Order.lt_succ _

theorem two_ne_zero' : (∗2 : Nimber.{0}) ≠ 0 := IsGroup.two.ne_zero

-- helper: the linear polynomial ∗2 X + 1 has no root below ∗3
theorem lnr3 : leastNoRoots (∗3 : Nimber.{0}) ≤ ↑(C (∗2) * X + 1 : Nimber[X]) := by
  have hd : (C (∗2) * X + 1 : Nimber.{0}[X]).degree = 1 := by
    rw [← C_1, degree_linear two_ne_zero']
  apply leastNoRoots_le_of_not_isRoot
  · rw [hd]; exact zero_lt_one
  · intro k
    rcases k with _ | _ | k
    · simp
    · simpa [coeff_one] using two_lt_three
    · simp [coeff_one] <;> exact (IsGroup.two.zero_lt).trans two_lt_three
  · intro r hr hroot
    rcases lt_three hr with rfl | rfl | rfl
    · simp at hroot
    · simp [CharTwo.add_eq_zero] at hroot
    · simp [CharTwo.add_eq_zero] at hroot
      exact two_mul_two_ne_one hroot

theorem ht3 : leastNoRoots (∗3 : Nimber.{0}) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top lnr3

theorem hdeg3 : ((leastNoRoots (∗3 : Nimber.{0})).untop ht3).degree = ((1 : ℕ) : WithBot ℕ) := by
  apply le_antisymm
  · have h1 : (leastNoRoots (∗3 : Nimber.{0})).untop ht3 ≤ C (∗2) * X + 1 :=
      WithTop.coe_le_coe.1 (by rw [WithTop.coe_untop]; exact lnr3)
    have h2 := Lex.degree_mono h1
    rw [← C_1, degree_linear two_ne_zero'] at h2
    simpa using h2
  · simpa using one_le_degree_leastNoRoots ht3

theorem hnat3 : ((leastNoRoots (∗3 : Nimber.{0})).untop ht3).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some hdeg3

theorem notField3 : ¬ IsField (∗3 : Nimber.{0}) := fun h => notGroup3 h.toIsGroup

-- `Polynomial.aeval_toSubring`
theorem c_12 : ¬ indep0% Polynomial.aeval_toSubring 7 := fun h => by
  have := @h ℚ ℚ _ _ _ (C (1/2 : ℚ)) ⊥ 0
  have hm := this (coeff_mem_coeffs (p := C (1/2 : ℚ)) (n := 0) (by simp))
  simp only [coeff_C_zero, SetLike.mem_coe, Subring.mem_bot] at hm
  obtain ⟨n, hn⟩ := hm
  have h2 : ((2 * n : ℤ) : ℚ) = 1 := by push_cast; rw [hn]; norm_num
  norm_cast at h2
  omega

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.0.Nimber.IsField.eval_eq_of_lt`
theorem c_13 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.«0».Nimber.IsField.eval_eq_of_lt 3 := fun h => by
  have := @h 3 (∗2) IsField.two (X ^ 2) (by rw [degree_X_pow]; norm_num) (coeff_X_pow_lt 2 (by simp))
  rw [eval_pow, eval_X, oeval_X_pow, val_of] at this
  exact two_sq_lt.ne this

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.0.Nimber.IsField.eval_eq_of_lt`
theorem c_14 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.«0».Nimber.IsField.eval_eq_of_lt 5 := fun h => by
  have h0 : (↑((X : Nimber[X]) ^ 0) : WithTop Nimber[X]) ≤ leastNoRoots (∗2) :=
    (WithTop.coe_le_coe.2 (Lex.X_pow_le_X_pow_iff.2 (by norm_num))).trans IsField.two.X_sq_lt_leastNoRoots.le
  have := @h 0 (∗2) IsField.two h0 (X ^ 2) (coeff_X_pow_lt 2 (by simp))
  rw [eval_pow, eval_X, oeval_X_pow, val_of] at this
  exact two_sq_lt.ne this

-- helper: X + C t evaluated at t does not match its ordinal evaluation
theorem evalXT : eval T (X + C T) ≠ oeval T (X + C T) := by
  intro e
  have e2 : oeval T (X + C T) = ∗(val T * 1 + val T) := by
    have := oeval_C_mul_X_pow_add (n := 1) (p := C T) (by rw [degree_C hT.ne_zero]; norm_num) T 1
    simpa [add_comm] using this
  rw [e2] at e
  simp [CharTwo.add_self_eq_zero] at e
  have := congrArg val e
  simp at this
  exact hT.ne_zero (by simpa using congrArg of this.symm)

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.0.Nimber.IsField.eval_eq_of_lt`
theorem c_15 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.«0».Nimber.IsField.eval_eq_of_lt 6 := fun h =>
  evalXT (@h 2 T hT.toIsField (by rw [hT.leastNoRoots_eq_top]; exact le_top) (X + C T)
    (by rw [degree_X_add_C]; norm_num))


-- helper: X² + X + 1 has no root below ∗2
theorem noRoot2 : ∀ r < (∗2 : Nimber.{0}), ¬ (X ^ 2 + X + 1 : Nimber[X]).IsRoot r := by
  intro r hr hroot
  rcases lt_two hr with rfl | rfl <;> simp [CharTwo.add_self_eq_zero] at hroot

theorem coeffQ2 : ∀ k, (X ^ 2 + X + 1 : Nimber.{0}[X]).coeff k < ∗2 :=
  IsGroup.two.coeff_add_lt (IsGroup.two.coeff_add_lt (coeff_X_pow_lt 2 (by simp)) (coeff_X_lt (by simp)))
    (coeff_one_lt (by simp))

theorem degQ2 : (X ^ 2 + X + 1 : Nimber.{0}[X]).degree = 2 := by compute_degree!

-- `Nimber.IsAlgClosed.exists_root'`
theorem c_21 : ¬ drop0% Nimber.IsAlgClosed.exists_root' 1 := fun h => by
  obtain ⟨r, hr, hroot⟩ := @h (∗2) (X ^ 2 + X + 1) (by rw [degQ2]; norm_num) coeffQ2
  exact noRoot2 r hr hroot

-- `Nimber.IsAlgClosed.exists_root'`
theorem c_22 : ¬ drop0% Nimber.IsAlgClosed.exists_root' 3 := fun h => by
  obtain ⟨r, -, hroot⟩ := @h T hT (C 1) (coeff_C_lt hT.one_lt)
  simp at hroot

-- `Nimber.IsAlgClosed.exists_root'`
theorem c_23 : ¬ drop0% Nimber.IsAlgClosed.exists_root' 4 := fun h => by
  obtain ⟨r, hr, hroot⟩ := @h T hT (X + C T) (by rw [degree_X_add_C]; exact zero_lt_one)
  simp [CharTwo.add_eq_zero] at hroot
  exact lt_irrefl _ (hroot ▸ hr)

-- `Nimber.IsAlgClosed.exists_root`
theorem c_24 : ¬ drop0% Nimber.IsAlgClosed.exists_root 1 := fun h => by
  obtain ⟨r, hr, hroot⟩ := @h (∗2) (X ^ 2 + X + 1) (by rw [degQ2]; decide) coeffQ2
  exact noRoot2 r hr hroot

-- `Nimber.IsAlgClosed.exists_root`
theorem c_25 : ¬ drop0% Nimber.IsAlgClosed.exists_root 3 := fun h => by
  obtain ⟨r, -, hroot⟩ := @h T hT (C 1) (coeff_C_lt hT.one_lt)
  simp at hroot

-- `Nimber.IsAlgClosed.exists_root`
theorem c_26 : ¬ drop0% Nimber.IsAlgClosed.exists_root 4 := fun h => by
  obtain ⟨r, hr, hroot⟩ := @h T hT (X + C T) (by rw [degree_X_add_C]; decide)
  simp [CharTwo.add_eq_zero] at hroot
  exact lt_irrefl _ (hroot ▸ hr)

-- `Nimber.IsAlgClosed.leastNoRoots_eq_top`
theorem c_27 : ¬ drop0% Nimber.IsAlgClosed.leastNoRoots_eq_top 1 := fun h => ht2 (@h (∗2))

-- `Nimber.isAlgClosed_iff_leastNoRoots_eq_top`
theorem c_28 : ¬ drop0% Nimber.isAlgClosed_iff_leastNoRoots_eq_top 1 := fun h => by
  have := (@h 0).2 leastNoRoots_zero
  exact absurd this.one_lt (by simp)

-- `Nimber.IsAlgClosed.sSup`
theorem c_29 : ¬ drop0% Nimber.IsAlgClosed.sSup 1 := fun h => by
  have := @h {∗2} (Set.singleton_nonempty _) bddAbove_singleton
  rw [csSup_singleton] at this
  exact notAC2 this

-- `Nimber.IsAlgClosed.sSup`
theorem c_30 : ¬ drop0% Nimber.IsAlgClosed.sSup 2 := fun h => by
  have := @h ∅ (fun x hx => absurd hx (Set.notMem_empty x)) bddAbove_empty
  rw [csSup_empty] at this
  exact absurd this.one_lt (by simp)

-- helper: the algebraically closed nimbers are unbounded
theorem notBddAC : ¬ BddAbove {x : Nimber.{0} | IsAlgClosed x} := fun ⟨b, hb⟩ =>
  absurd ((lt_succ b).trans_le ((le_algClosure _).trans (hb (IsAlgClosed.algClosure (succ b))))) (lt_irrefl _)

-- helper: the closures algClosure x are unbounded
theorem notBddRange : ¬ BddAbove (range (algClosure : Nimber.{0} → Nimber.{0})) := fun ⟨b, hb⟩ =>
  absurd ((lt_succ b).trans_le ((le_algClosure _).trans (hb ⟨succ b, rfl⟩))) (lt_irrefl _)

-- `Nimber.IsAlgClosed.sSup`
theorem c_31 : ¬ drop0% Nimber.IsAlgClosed.sSup 3 := fun h => by
  have := @h {x | IsAlgClosed x} (fun x hx => hx) ⟨T, hT⟩
  rw [csSup_of_not_bddAbove notBddAC, csSup_empty] at this
  exact absurd this.one_lt (by simp)

-- `Nimber.IsAlgClosed.iSup`
theorem c_32 : ¬ drop0% Nimber.IsAlgClosed.iSup 1 := fun h => by
  have := @h False (fun i => i.elim) (fun i => i.elim) ⟨0, by rintro _ ⟨i, _⟩; exact i.elim⟩
  rw [ciSup_of_empty] at this
  exact absurd this.one_lt (by simp)

-- `Nimber.IsAlgClosed.iSup`
theorem c_33 : ¬ ∀ {ι : Type 1} [Nonempty ι] {f : ι → Nimber.{0}}, (∀ i, IsAlgClosed (f i)) →
    IsAlgClosed (⨆ i, f i) := fun h => by
  have := @h Nimber.{0} ⟨0⟩ algClosure IsAlgClosed.algClosure
  rw [ciSup_of_not_bddAbove notBddRange, csSup_empty] at this
  exact absurd this.one_lt (by simp)

-- `Nimber.IsAlgClosed.eval_eq_of_lt`
theorem c_34 : ¬ drop0% Nimber.IsAlgClosed.eval_eq_of_lt 1 := fun h => by
  have := @h (∗2) (X ^ 2) (coeff_X_pow_lt 2 (by simp))
  rw [eval_pow, eval_X, oeval_X_pow, val_of] at this
  exact two_sq_lt.ne this

-- `Nimber.IsAlgClosed.eval_eq_of_lt`
theorem c_35 : ¬ drop0% Nimber.IsAlgClosed.eval_eq_of_lt 3 := fun h => evalXT (@h T hT (X + C T))

-- `Nimber.IsAlgClosed.pow_mul_eq`
theorem c_36 : ¬ drop0% Nimber.IsAlgClosed.pow_mul_eq 3 := fun h => by
  have := @h 2 (∗2) 1 (by simp)
  rw [mul_one, val_one, mul_one, val_of] at this
  exact two_sq_lt.ne this

-- `Nimber.IsAlgClosed.ofMonic`
theorem c_38 : ¬ drop0% Nimber.IsAlgClosed.ofMonic 1 := fun h => by
  have := @h 0 (fun p hm _ hc => absurd (hc p.natDegree) (by rw [hm.coeff_natDegree]; simp))
  exact absurd this.one_lt (by simp)

-- `Nimber.IsAlgClosed.ofMonic`
theorem c_39 : ¬ drop0% Nimber.IsAlgClosed.ofMonic 2 := fun h => notAC2 (@h (∗2) IsField.two)

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.0.Nimber.IsField.isRoot_leastNoRoots`
theorem c_40 : ¬ indep0% _private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.«0».Nimber.IsField.isRoot_leastNoRoots 2 :=
  fun h => @h T hT.toIsField hT.leastNoRoots_eq_top

-- `Nimber.IsRing.isRoot_leastNoRoots`
theorem c_41 : ¬ indep0% Nimber.IsRing.isRoot_leastNoRoots 2 := fun h => @h T hT.toIsRing hT.leastNoRoots_eq_top

-- `Nimber.IsRing.isRoot_leastNoRoots_of_eq`
theorem c_42 : ¬ drop0% Nimber.IsRing.isRoot_leastNoRoots_of_eq 3 := fun h => by
  have := @h (∗2) IsRing.two 1
  simp at this

-- `Nimber.IsRing.pow_degree_leastNoRoots`
theorem c_43 : ¬ drop0% Nimber.IsRing.pow_degree_leastNoRoots 1 := fun h => by
  have := @h (∗3) ht3 1 hdeg3
  rw [pow_one, of_val] at this
  exact notGroup3 this.toIsGroup

-- `Nimber.IsRing.pow_degree_leastNoRoots`
theorem c_44 : ¬ indep0% Nimber.IsRing.pow_degree_leastNoRoots 2 := fun h => @h T hT.toIsRing 0 hT.leastNoRoots_eq_top

-- `Nimber.IsField.pow_degree_leastNoRoots`
theorem c_45 : ¬ drop0% Nimber.IsField.pow_degree_leastNoRoots 1 := fun h => by
  have := @h (∗3) ht3 1 hdeg3
  rw [pow_one, of_val] at this
  exact notField3 this

-- `Nimber.IsField.pow_degree_leastNoRoots`
theorem c_46 : ¬ indep0% Nimber.IsField.pow_degree_leastNoRoots 2 := fun h => @h T hT.toIsField 0 hT.leastNoRoots_eq_top

-- `Nimber.IsField.pow_degree_leastNoRoots`
theorem c_47 : ¬ drop0% Nimber.IsField.pow_degree_leastNoRoots 4 := fun h => by
  have := @h (∗2) IsField.two ht2 0
  rw [pow_zero] at this
  exact absurd this.one_lt (by simp)

-- `Nimber.IsField.pow_natDegree_leastNoRoots`
theorem c_48 : ¬ drop0% Nimber.IsField.pow_natDegree_leastNoRoots 1 := fun h => by
  have := @h (∗3) ht3
  rw [hnat3, pow_one, of_val] at this
  exact notField3 this

-- `Nimber.IsField.pow_natDegree_leastNoRoots`
theorem c_49 : ¬ indep0% Nimber.IsField.pow_natDegree_leastNoRoots 2 := fun h => @h T hT.toIsField hT.leastNoRoots_eq_top

-- `Nimber.IsField.pow_degree_leastNoRoots_eq_adjoin`
theorem c_50 : ¬ indep0% Nimber.IsField.pow_degree_leastNoRoots_eq_adjoin 1 := fun h => notField3 (@h (∗3) ht3 1 hdeg3)

-- `Nimber.IsField.pow_degree_leastNoRoots_eq_adjoin`
theorem c_51 : ¬ indep0% Nimber.IsField.pow_degree_leastNoRoots_eq_adjoin 2 := fun h =>
  @h T hT.toIsField 0 hT.leastNoRoots_eq_top

-- `Nimber.IsField.pow_degree_leastNoRoots_eq_adjoin`
theorem c_52 : ¬ indep0% Nimber.IsField.pow_degree_leastNoRoots_eq_adjoin 4 := fun h => by
  have h1 := @h (∗2) IsField.two ht2 0
  have h2 := degree_leastNoRoots_pos ht2
  rw [h1] at h2
  exact absurd h2 (by simp)

-- helper: ∗3 < fieldClosure (succ ∗3)
theorem three_lt_fc : (∗3 : Nimber.{0}) < fieldClosure (succ (∗3)) := (lt_succ _).trans_le (le_fieldClosure _)

-- `Nimber.IsField.fieldClosure_succ_eq_pow_degree_leastNoRoots`
theorem c_53 : ¬ drop0% Nimber.IsField.fieldClosure_succ_eq_pow_degree_leastNoRoots 1 := fun h => by
  have := @h (∗3) 1 ⟨ht3, hdeg3⟩
  rw [pow_one, of_val] at this
  exact absurd three_lt_fc (by rw [this]; exact lt_irrefl _)

-- `Nimber.IsField.fieldClosure_succ_eq_pow_degree_leastNoRoots`
theorem c_54 : ¬ drop0% Nimber.IsField.fieldClosure_succ_eq_pow_degree_leastNoRoots 3 := fun h => by
  have := @h (∗2) IsField.two 0
  have h2 : (∗2 : Nimber.{0}) < fieldClosure (succ (∗2)) := (lt_succ _).trans_le (le_fieldClosure _)
  rw [this, pow_zero] at h2
  exact absurd h2 (by simp)

-- `Nimber.IsField.fieldClosure_succ_eq_pow_natDegree_leastNoRoots`
theorem c_55 : ¬ drop0% Nimber.IsField.fieldClosure_succ_eq_pow_natDegree_leastNoRoots 1 := fun h => by
  have := @h (∗3) ht3
  rw [hnat3, pow_one, of_val] at this
  exact absurd three_lt_fc (by rw [this]; exact lt_irrefl _)

-- `Nimber.IsField.fieldClosure_succ_eq_pow_natDegree_leastNoRoots`
theorem c_56 : ¬ indep0% Nimber.IsField.fieldClosure_succ_eq_pow_natDegree_leastNoRoots 2 := fun h =>
  @h T hT.toIsField hT.leastNoRoots_eq_top

-- `Nimber.IsAlgClosed.isRing_opow_omega0`
theorem c_57 : ¬ drop0% Nimber.IsAlgClosed.isRing_opow_omega0 1 := fun h => by
  have := @h 0
  rw [val_zero, Ordinal.zero_opow Ordinal.omega0_ne_zero, of_zero] at this
  exact absurd this.one_lt (by simp)

-- `Nimber.IsField.degree_leastNoRoots_le_of_isField_pow`
theorem c_58 : ¬ drop0% Nimber.IsField.degree_leastNoRoots_le_of_isField_pow 2 := fun h => by
  obtain ⟨ht, -⟩ := @h T 1 hT.toIsField (by rw [pow_one, of_val]; exact hT.toIsField)
  exact ht hT.leastNoRoots_eq_top

-- `Nimber.IsField.degree_leastNoRoots_le_of_isField_pow`
theorem c_59 : ¬ drop0% Nimber.IsField.degree_leastNoRoots_le_of_isField_pow 4 := fun h => by
  obtain ⟨ht, -⟩ := @h T 0 (by norm_num) hT.toIsField
  exact ht hT.leastNoRoots_eq_top


-- helper: algClosure 0 is not algebraic over fieldClosure 0
theorem notAlgT : ¬ IsAlgebraic (IsField.fieldClosure (0 : Nimber.{0})).toSubfield (algClosure 0) := fun h =>
  lt_irrefl _ (lt_algClosure_iff_isAlgebraic.2 h)

-- helper: nimbers above algClosure 0 are not algebraic over fieldClosure 0
theorem notAlg_of_le {y : Nimber.{0}} (hy : T ≤ y) :
    ¬ IsAlgebraic (IsField.fieldClosure (0 : Nimber.{0})).toSubfield y := fun h =>
  absurd ((lt_algClosure_iff_isAlgebraic.2 h).trans_le hy) (lt_irrefl _)

-- helper: succ T is not a field
theorem notFieldSuccT : ¬ IsField (succ T) := fun h => by
  have e : T + 1 = succ T := by
    rw [← hT.toIsGroup.add_eq_of_lt hT.one_lt]; simp; rfl
  have := h.toIsGroup.add_lt (lt_succ T) (hT.one_lt.trans (lt_succ T))
  rw [e] at this
  exact lt_irrefl _ this

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.0.Nimber.isAlgebraic_of_not_isField`
theorem c_61 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.«0».Nimber.isAlgebraic_of_not_isField 2 := fun h =>
  notAlg_of_le (lt_succ T).le (@h 0 (succ T) notFieldSuccT)

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.0.Nimber.isAlgebraic_of_not_isField`
theorem c_62 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.«0».Nimber.isAlgebraic_of_not_isField 3 := fun h =>
  notAlgT (@h 0 (algClosure 0) le_rfl)

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.0.Nimber.isAlgebraic_of_leastNoRoots`
theorem c_63 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.«0».Nimber.isAlgebraic_of_leastNoRoots 2 := fun h =>
  notAlg_of_le T_lt_F.le (@h 0 F (by rw [lnrF]; exact WithTop.coe_ne_top))

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.0.Nimber.isAlgebraic_of_leastNoRoots`
theorem c_64 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.«0».Nimber.isAlgebraic_of_leastNoRoots 3 := fun h =>
  notAlgT (@h 0 (algClosure 0) le_rfl)

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.0.Nimber.isAlgebraic_of_lt`
theorem c_65 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.«0».Nimber.isAlgebraic_of_lt 2 := fun h =>
  notAlgT (@h 0 (algClosure 0))

-- `Nimber.IsAlgClosed.algClosure_le_iff`
theorem c_66 : ¬ drop0% Nimber.IsAlgClosed.algClosure_le_iff 2 := fun h => by
  have := (@h 0 0).2 le_rfl
  exact absurd (hT.zero_lt.trans_le this) (lt_irrefl _)

-- `Nimber.IsAlgClosed.lt_algClosure_iff`
theorem c_67 : ¬ drop0% Nimber.IsAlgClosed.lt_algClosure_iff 2 := fun h =>
  lt_irrefl _ ((@h 0 0).1 hT.zero_lt)

-- `Nimber.IsAlgClosed.algClosure_eq`
theorem c_68 : ¬ drop0% Nimber.IsAlgClosed.algClosure_eq 1 := fun h => hT.ne_zero (@h 0)

-- `Nimber.exists_isAlgClosed_between`
theorem c_69 : ¬ drop0% Nimber.exists_isAlgClosed_between 1 := fun h => by
  obtain ⟨l, hl, u, hu, hle, -⟩ := @h 0
  exact absurd (hl.zero_lt.trans_le hle) (lt_irrefl _)

-- `Nimber.exists_isAlgClosed_between'`
theorem c_70 : ¬ drop0% Nimber.exists_isAlgClosed_between' 1 := fun h => by
  obtain ⟨l, hl, hle, -⟩ := @h 0
  exact absurd (hl.zero_lt.trans_le hle) (lt_irrefl _)

-- `Nimber.IsAlgClosed.mem_range_enumAlgClosed`
theorem c_71 : ¬ drop0% Nimber.IsAlgClosed.mem_range_enumAlgClosed 1 := fun h => by
  obtain ⟨z, hz⟩ := @h 0
  have := IsAlgClosed.enumAlgClosed z
  rw [hz] at this
  exact absurd this.one_lt (by simp)

-- `Nimber.IsField.sqrt_lt`
theorem c_72 : ¬ drop0% Nimber.IsField.sqrt_lt 3 := fun h =>
  sqrt_not_lt hT (@h T T hT.toIsField (by rw [hT.leastNoRoots_eq_top]; exact WithTop.coe_lt_top _))

-- `Nimber.IsField.sqrt_lt`
theorem c_73 : ¬ drop0% Nimber.IsField.sqrt_lt 4 := fun h => by
  have := @h F T hF T_lt_F
  rw [sqrtT] at this
  exact lt_irrefl _ this

-- `Nimber.IsField.sqrt_lt'`
theorem c_74 : ¬ indep0% Nimber.IsField.sqrt_lt' 2 := fun h =>
  notField3 (@h (∗3) 0 ((IsGroup.two.zero_lt).trans two_lt_three))

-- `Nimber.IsField.sqrt_lt'`
theorem c_75 : ¬ drop0% Nimber.IsField.sqrt_lt' 3 := fun h =>
  sqrt_not_lt hT (@h T T hT.toIsField perfT)

-- `Nimber.IsField.sqrt_lt'`
theorem c_76 : ¬ drop0% Nimber.IsField.sqrt_lt' 4 := fun h => by
  have := @h F T hF T_lt_F
  rw [sqrtT] at this
  exact lt_irrefl _ this

-- `Nimber.IsAlgClosed.sqrt_lt`
theorem c_77 : ¬ drop0% Nimber.IsAlgClosed.sqrt_lt 2 := fun h => by
  have := @h F T T_lt_F
  rw [sqrtT] at this
  exact lt_irrefl _ this

-- `Nimber.IsAlgClosed.sqrt_lt`
theorem c_78 : ¬ drop0% Nimber.IsAlgClosed.sqrt_lt 3 := fun h => sqrt_not_lt hT (@h T T hT)

-- `Nimber.IsField.X_sq_add_C_le_leastNoRoots`
theorem c_79 : ¬ drop0% Nimber.IsField.X_sq_add_C_le_leastNoRoots 1 := fun h => by
  have h1 := (@h (∗3) 0 (fun z hz => absurd hz (by simp))).trans lnr3
  rw [WithTop.coe_le_coe] at h1
  apply absurd h1
  rw [not_le]
  apply Lex.lt_of_degree_lt
  rw [← C_1, degree_linear two_ne_zero']
  simp

-- `Nimber.IsField.X_sq_add_C_le_leastNoRoots`
theorem c_80 : ¬ drop0% Nimber.IsField.X_sq_add_C_le_leastNoRoots 3 := fun h => by
  have h1 := @h F hF F
  rw [lnrF, WithTop.coe_le_coe] at h1
  apply absurd h1
  rw [not_le, Lex.lt_def]
  refine ⟨0, fun k hk => ?_, ?_⟩
  · simp [coeff_C, Nat.pos_iff_ne_zero.1 hk]
  · simpa using T_lt_F

-- helper: ∗2 ≤ algClosure 0
theorem two_le_T : (∗2 : Nimber.{0}) ≤ T :=
  le_trans (by rw [of.le_iff_le]; exact (by simpa using (Ordinal.natCast_lt_omega0 2).le)) hT.omega0_le

-- `Nimber.IsField.perfectField_of_btwn`
theorem c_81 : ¬ indep0% Nimber.IsField.perfectField_of_btwn 2 := fun h => by
  have := @h 0 (∗2) IsField.two (by simp) two_le_T
  exact absurd this.one_lt (by simp)

-- `Nimber.IsField.perfectField_of_btwn`
theorem c_82 : ¬ indep0% Nimber.IsField.perfectField_of_btwn 3 := fun h => by
  have h3 : (∗3 : Nimber.{0}) ≤ algClosure (∗2) :=
    le_trans (by rw [of.le_iff_le]; exact (by simpa using (Ordinal.natCast_lt_omega0 3).le))
      (IsAlgClosed.algClosure _).omega0_le
  exact notField3 (@h (∗2) (∗3) IsField.two (IsField.two.perfectField_of_le_algClosure_zero two_le_T)
    two_lt_three.le h3)

-- `Nimber.IsField.perfectField_of_btwn`
theorem c_83 : ¬ drop0% Nimber.IsField.perfectField_of_btwn 4 := fun h =>
  notPerfF (@h F F hF hF le_rfl (le_algClosure F))

-- `Nimber.IsField.perfectField_of_btwn`
theorem c_84 : ¬ drop0% Nimber.IsField.perfectField_of_btwn 5 := fun h => by
  have hA := IsAlgClosed.algClosure F
  have : _root_.IsAlgClosed hA.toIsField.toSubfield := hA.isAlgClosed
  exact notPerfF (@h (algClosure F) F hA.toIsField hF inferInstance
    ((le_algClosure F).trans (le_algClosure _)))

-- `Nimber.IsField.perfectField_of_btwn`
theorem c_85 : ¬ drop0% Nimber.IsField.perfectField_of_btwn 6 := fun h =>
  notPerfF (@h T F hT.toIsField hF perfT T_lt_F.le)

-- `Nimber.IsField.perfectField_of_le_algClosure_zero`
theorem c_86 : ¬ drop0% Nimber.IsField.perfectField_of_le_algClosure_zero 2 := fun h => notPerfF (@h F hF)

-- `Nimber.IsField.leastNoRoots_eq_of_not_perfectField`
theorem c_87 : ¬ drop0% Nimber.IsField.leastNoRoots_eq_of_not_perfectField 2 := fun h => by
  have := @h T hT.toIsField
  rw [hT.leastNoRoots_eq_top] at this
  exact WithTop.top_ne_coe this

-- `Nimber.IsField.sq_lt_self_of_not_perfectField`
theorem c_88 : ¬ drop0% Nimber.IsField.sq_lt_self_of_not_perfectField 2 := fun h => by
  have := @h (∗2) IsField.two
  rw [pow_two] at this
  have h2 : (∗2 * ∗2 : Nimber.{0}) < succ 1 := by rw [succ_one]; exact this
  rcases Nimber.le_one_iff.1 (Order.lt_succ_iff.1 h2) with e | e
  · exact two_ne_zero' (mul_self_eq_zero.1 e)
  · exact two_mul_two_ne_one e

-- helper: T < T²
theorem T_lt_sq : T < T ^ 2 := by
  rw [hT.pow_eq, ← of_val T, of.lt_iff_lt, val_of]
  exact lt_self_pow₀ hT.one_lt_val (by norm_num)

-- `Nimber.IsField.sqrt_lt_of_not_perfectField`
theorem c_89 : ¬ indep0% Nimber.IsField.sqrt_lt_of_not_perfectField 2 := fun h =>
  notField3 (@h (∗3) 0 (pos_iff_ne_zero.2 (pow_ne_zero 2 (by simp))))

-- `Nimber.IsField.sqrt_lt_of_not_perfectField`
theorem c_90 : ¬ drop0% Nimber.IsField.sqrt_lt_of_not_perfectField 3 := fun h =>
  sqrt_not_lt hT (@h T T hT.toIsField T_lt_sq)

-- `Nimber.IsField.sqrt_lt_of_not_perfectField`
theorem c_91 : ¬ drop0% Nimber.IsField.sqrt_lt_of_not_perfectField 4 := fun h => by
  have := @h F ((succ F) ^ 2) hF notPerfF
  rw [sqrt_sq] at this
  exact absurd this (not_lt.2 (le_succ F))

-- `Nimber.IsField.sqrt_le_of_not_perfectField`
theorem c_92 : ¬ drop0% Nimber.IsField.sqrt_le_of_not_perfectField 3 := fun h => by
  have := @h T T hT.toIsField T_lt_sq.le
  rw [sqrtT] at this
  exact absurd this (not_le.2 T_lt_F)

-- `Nimber.IsField.sqrt_le_of_not_perfectField`
theorem c_93 : ¬ drop0% Nimber.IsField.sqrt_le_of_not_perfectField 4 := fun h => by
  have := @h F ((succ F) ^ 2) hF notPerfF
  rw [sqrt_sq] at this
  exact absurd this (not_le.2 (lt_succ F))


-- helper: leastNoRoots ∗2 ≤ X² + X + 1
theorem lnr2 : leastNoRoots (∗2 : Nimber.{0}) ≤ ↑(X ^ 2 + X + 1 : Nimber[X]) :=
  leastNoRoots_le_of_not_isRoot (by rw [degQ2]; norm_num) coeffQ2 noRoot2

theorem hnat2 : ((leastNoRoots (∗2 : Nimber.{0})).untop ht2).natDegree = 2 := by
  have h1 : (leastNoRoots (∗2 : Nimber.{0})).untop ht2 ≤ X ^ 2 + X + 1 :=
    WithTop.coe_le_coe.1 (by rw [WithTop.coe_untop]; exact lnr2)
  have h2 := Lex.natDegree_mono h1
  have h3 : (X ^ 2 + X + 1 : Nimber.{0}[X]).natDegree = 2 := natDegree_eq_of_degree_eq_some degQ2
  have h4 := IsField.two.one_lt_natDegree_leastNoRoots ht2
  omega

-- helper: ∗4 is a field
theorem field4 : IsField (∗4 : Nimber.{0}) := by
  have := IsField.two.fieldClosure_succ_eq_pow_natDegree_leastNoRoots ht2
  rw [hnat2, val_of, pow22] at this
  rw [← this]; exact IsField.fieldClosure _

-- `Nimber.IsField.sq_le_fieldClosure_succ`
theorem c_60 : ¬ drop0% Nimber.IsField.sq_le_fieldClosure_succ 1 := fun h => by
  have h1 := @h (∗3)
  have h2 : fieldClosure (succ (∗3 : Nimber.{0})) ≤ ∗4 :=
    field4.fieldClosure_le_iff.2 (le_of_eq (three_add_one_eq_four (R := Ordinal)))
  have h3 := (h1.trans h2)
  rw [val_of, of.le_iff_le, pow_two] at h3
  have : ((3 : ℕ) : Ordinal) * ((3 : ℕ) : Ordinal) ≤ ((4 : ℕ) : Ordinal) := by simpa using h3
  rw [← Ordinal.natCast_mul, Nat.cast_le] at this
  norm_num at this

-- helper: S = succ T, a non-field just above T
theorem T_add_one : T + 1 = succ T := by
  rw [← hT.toIsGroup.add_eq_of_lt hT.one_lt]; simp; rfl

theorem two_lt_T : (∗2 : Nimber.{0}) < T :=
  lt_of_lt_of_le (by rw [of.lt_iff_lt]; simpa using Ordinal.natCast_lt_omega0 2) hT.omega0_le

-- helper: the linear polynomial ∗2 X + T has no root below succ T
theorem lnrS : leastNoRoots (succ T) ≤ ↑(C (∗2) * X + C T : Nimber.{0}[X]) := by
  apply leastNoRoots_le_of_not_isRoot
  · rw [degree_linear two_ne_zero']; exact zero_lt_one
  · intro k
    rcases k with _ | _ | k
    · simpa using lt_succ T
    · simpa using two_lt_T.trans (lt_succ T)
    · simp <;> exact hT.zero_lt.trans (lt_succ T)
  · intro r hr hroot
    simp [CharTwo.add_eq_zero] at hroot
    rcases (Order.lt_succ_iff.1 hr).lt_or_eq with hr | rfl
    · exact absurd hroot (hT.mul_lt two_lt_T hr).ne
    · have e : (∗2 + 1) * T = 0 := by rw [_root_.add_mul, hroot, one_mul, CharTwo.add_self_eq_zero]
      rcases mul_eq_zero.1 e with e | e
      · exact one_ne_two ((CharTwo.add_eq_zero.1 e).symm)
      · exact hT.ne_zero e

theorem htS : leastNoRoots (succ T) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top lnrS

-- helper: succ T is not a root of its least polynomial without roots
theorem notRootS : ¬ ((leastNoRoots (succ T)).untop htS).IsRoot (succ T) := by
  have h1 : (leastNoRoots (succ T)).untop htS ≤ C (∗2) * X + C T :=
    WithTop.coe_le_coe.1 (by rw [WithTop.coe_untop]; exact lnrS)
  have key := (Lex.forall_le_linear (P := fun p => 0 < p.degree → (∀ k, p.coeff k < succ T) →
    (∀ r < succ T, ¬ p.IsRoot r) → ¬ p.IsRoot (succ T)) (x := ∗2) (y := T)).2 ⟨?_, ?_⟩ _ h1
    (degree_leastNoRoots_pos htS) (coeff_leastNoRoots_lt htS) (fun r hr => not_isRoot_leastNoRoots_of_lt htS hr)
  · exact key
  · intro b hb _ hc hnr hroot
    rcases hb.lt_or_eq with hb | rfl
    · apply hnr (b / ∗2) ((hT.toIsField.div_lt hb two_lt_T).trans (lt_succ T))
      simp [CharTwo.add_eq_zero, mul_div_cancel₀ _ two_ne_zero']
    · simp [CharTwo.add_eq_zero] at hroot
      rw [← T_add_one, mul_add, mul_one, CharTwo.add_eq_iff_eq_add] at hroot
      have e : (∗2 + 1) * T = ∗2 := by
        rw [_root_.add_mul, one_mul, hroot, add_comm, ← _root_.add_assoc, CharTwo.add_self_eq_zero, zero_add]
      have hne : (∗2 + 1 : Nimber.{0}) ≠ 0 := fun e0 => one_ne_two ((CharTwo.add_eq_zero.1 e0).symm)
      have hTe : T = ∗2 / (∗2 + 1) := eq_div_of_mul_eq hne (by rw [mul_comm]; exact e)
      have hlt : ∗2 / (∗2 + 1) < T :=
        hT.toIsField.div_lt two_lt_T (hT.toIsGroup.add_lt two_lt_T hT.one_lt)
      rw [← hTe] at hlt
      exact lt_irrefl _ hlt
  · intro a ha b hd hc hnr hroot
    rcases lt_two ha with rfl | rfl
    · exact absurd hd (by simpa using (degree_C_le (a := b)))
    · exact hnr b (hc 0 |>.trans_eq' (by simp)) (by simp [CharTwo.add_self_eq_zero])

-- `_private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.0.Nimber.IsField.isRoot_leastNoRoots`
theorem c_94 : ¬ drop0% _private.CombinatorialGames.Nimber.SimplestExtension.Algebraic.«0».Nimber.IsField.isRoot_leastNoRoots 1 :=
  fun h => notRootS (@h (succ T) htS)

-- `Nimber.IsRing.isRoot_leastNoRoots`
theorem c_95 : ¬ drop0% Nimber.IsRing.isRoot_leastNoRoots 1 := fun h => notRootS (@h (succ T) htS)

-- `Nimber.IsRing.isRoot_leastNoRoots_of_eq`
theorem c_96 : ¬ drop0% Nimber.IsRing.isRoot_leastNoRoots_of_eq 1 := fun h =>
  notRootS (@h (succ T) _ (WithTop.coe_untop _ htS).symm)


-- `Nimber.IsAlgClosed.pow_mul_eq`
theorem c_37 : ¬ drop0% Nimber.IsAlgClosed.pow_mul_eq 4 := fun h => by
  have hG : IsField (of (val F ^ ω)) := hT.isField_fieldClosure_succ_pow_omega0
  have hTF : val T < val F := val.lt_iff_lt.2 T_lt_F
  have hF1 : 1 < val F := hT.one_lt_val.trans hTF
  have hTG : T < of (val F ^ ω) := by
    rw [← of_val T, of.lt_iff_lt]
    exact hTF.trans_le (Ordinal.left_le_opow _ Ordinal.omega0_pos)
  have e1 := hG.toIsRing.mul_eq_of_lt hG.toIsGroup le_rfl hTG (fun z hz => hG.inv_lt hz)
  have e2 := @h 1 T (of (val F ^ ω)) hT
  rw [pow_one, pow_one, mul_comm, ← e1] at e2
  have e3 := congrArg val e2
  simp only [val_of] at e3
  have hw : val F ^ ω = val F * val F ^ ω := by
    rw [← Ordinal.opow_one_add, Ordinal.one_add_omega0]
  have h1 : val T * val F ^ ω ≤ val F ^ ω := by
    calc val T * val F ^ ω ≤ val F * val F ^ ω := by gcongr
      _ = val F ^ ω := hw.symm
  have h2 : val F ^ ω < val F ^ ω * val T := by
    calc val F ^ ω = val F ^ ω * 1 := (mul_one _).symm
      _ < val F ^ ω * val T :=
        (mul_lt_mul_iff_of_pos_left (Ordinal.opow_pos _ (zero_lt_one.trans hF1))).2 hT.one_lt_val
  rw [e3] at h2
  exact absurd (h2.trans_le h1) (lt_irrefl _)

end W2c0
