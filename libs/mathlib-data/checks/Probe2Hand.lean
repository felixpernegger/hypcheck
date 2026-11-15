import Lean.Elab.Command
import Mathlib
-- hypkit toolkit header: drop%/indep%/drop0%/indep0% state T' and ∀ indep, Hᵢ straight from the library.
-- Agents copy this file unchanged as the start of their output file (scripts/verify.sh checks it).
-- No `xs[i]!` here: libraries may declare a `]!` token (Foundation does), which breaks that syntax.


set_option linter.unusedVariables false

open Lean Meta Elab Term

/-- `_private.M.«0».x` ↦ `_private.M.0.x`: all-digit string components become numeric. -/
def hcFixName : Name → Name
  | .str p s => if !s.isEmpty && s.all Char.isDigit then .num (hcFixName p) s.toNat! else .str (hcFixName p) s
  | .num p k => .num (hcFixName p) k
  | .anonymous => .anonymous

/-- The constant named by `T`: a public name (resolved as usual) or a private one written in full
as `_private.Mod.«0».x` (private names are not reachable by their short name from another module). -/
def hcConst (T : Ident) : TermElabM Name := do
  let n := hcFixName T.getId
  if isPrivateName n then
    unless (← getEnv).contains n do throwError "unknown private constant {n}"
    return n
  realizeGlobalConstNoOverloadWithInfo T

/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    unless or (decide (dep.size > 1)) (body.containsFVar x.fvarId!) do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    unless or (decide (dep.size > 1)) (body.containsFVar x.fvarId!) do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

namespace Probe2
open Set TopologicalSpace

-- `Multiset.induction_on_multiset_quot` idx 4: necessary (p := fun _ => False, s = 0)
theorem p2_1 : ¬ drop0% Multiset.induction_on_multiset_quot 4 :=
  fun h => @h Unit (fun _ _ => True) (fun _ => False) 0

-- `Disjoint.notMem_of_mem_left_multiset` idx 5: necessary (s = 0, t = {0}, a = 0)
theorem p2_2 : ¬ drop0% Disjoint.notMem_of_mem_left_multiset 5 :=
  fun h => @h ℕ 0 {0} (by simp) 0 (by simp)

-- `Disjoint.notMem_of_mem_right_multiset` idx 5: necessary (s = {0}, t = 0, a = 0)
theorem p2_3 : ¬ drop0% Disjoint.notMem_of_mem_right_multiset 5 :=
  fun h => @h ℕ {0} 0 (by simp) 0 (by simp)

-- `Multiset.mem_cons_of_mem` idx 4: necessary (a = 0, b = 1, s = 0)
theorem p2_4 : ¬ drop0% Multiset.mem_cons_of_mem 4 :=
  fun h => absurd (@h ℕ 0 1 0) (by simp)

-- `Nat.Prime.factorization_pow` idx 2: necessary (p = 4, k = 1: factorization 4 at 4 is 0, single 4 1 at 4 is 1)
theorem p2_5 : ¬ drop0% Nat.Prime.factorization_pow 2 :=
  fun h => absurd (congrArg (· 4) (@h 4 1)) (by
    simp [Nat.factorization_eq_zero_of_not_prime 4 (p := 4) (by decide)])

-- `Nat.multiplicity_eq_factorization` idx 2: necessary (n = p = 4: multiplicity 1, factorization 0)
theorem p2_6 : ¬ drop0% Nat.multiplicity_eq_factorization 2 :=
  fun h => absurd (@h 4 4) (by
    rw [Nat.factorization_eq_zero_of_not_prime 4 (p := 4) (by decide), multiplicity_self (by decide)]; simp)

-- `Nat.nth_mem_of_lt_card` idx 2: necessary (p = fun _ => True: set univ is infinite)
theorem p2_7 : ¬ indep0% Nat.nth_mem_of_lt_card 2 :=
  fun h => Set.infinite_univ (by simpa [Set.ofPred] using @h (fun _ => True) 0)

-- `PFun.ext` idx 4: necessary (f = fun _ => Part.none, g = fun _ => Part.some ())
theorem p2_8 : ¬ drop0% PFun.ext 4 :=
  fun h => absurd (congrFun (@h Unit Unit (fun _ => Part.none) (fun _ => Part.some ())) ())
    (fun e => Part.some_ne_none () e.symm)

-- `PFun.get_prodMap` idx 7: necessary (f = g = fun _ => Part.none: prodMap not defined)
theorem p2_9 : ¬ indep0% PFun.get_prodMap 7 :=
  fun h => (h (α := Unit) (β := Unit) (γ := Unit) (δ := Unit) (fun _ => Part.none) (fun _ => Part.none) ((), ())).1

-- `PrimeMultiset.prod_ofPNatMultiset` idx 1: necessary (v = {1}: 1 is not prime)
theorem p2_10 : ¬ indep0% PrimeMultiset.prod_ofPNatMultiset 1 :=
  fun h => PNat.not_prime_one (h {1} 1 (by simp))

-- `Part.get_eq_get_of_eq` idx 4: necessary (a = Part.some (), b = Part.none)
theorem p2_11 : ¬ indep0% Part.get_eq_get_of_eq 4 :=
  fun h => Part.some_ne_none () (@h Unit (Part.some ()) trivial Part.none)

-- `Computation.length_think` idx 2: necessary (s = Computation.empty does not terminate)
theorem p2_12 : ¬ indep0% Computation.length_think 2 :=
  fun h => Computation.not_terminates_empty (h (Computation.empty ℕ))

-- `Computation.bind_congr` idx 7: necessary (s1 = s2 = pure 0, f1 = pure, f2 = fun _ => pure 1)
theorem p2_13 : ¬ drop0% Computation.bind_congr 7 := fun h => by
  have := @h ℕ ℕ (Computation.pure 0) (Computation.pure 0) Computation.pure (fun _ => Computation.pure 1) (Computation.Equiv.refl _)
  simp only [Computation.ret_bind] at this
  have h0 := (this 0).mp (Computation.ret_mem 0)
  exact absurd (Computation.mem_unique h0 (Computation.ret_mem 1)) (by decide)

-- `Semiquot.liftOn_ofMem` idx 6: necessary (q = pure 0, f = id, a = 1)
theorem p2_14 : ¬ drop0% Semiquot.liftOn_ofMem 6 := fun h => by
  have := @h ℕ ℕ (pure 0) id (fun a ha b hb => by simp_all [Semiquot.mem_pure]) 1
  simp [Semiquot.liftOn_ofMem _ _ _ 0 (Semiquot.mem_pure_self 0)] at this

-- `Set.even_card_insert_iff` idx 4: necessary (s = {0}ᶜ in Nat, a = 0: both ncard 0, Even 0 but not Odd 0)
theorem p2_15 : ¬ drop0% Set.even_card_insert_iff 4 := fun h => by
  have hs : ({0}ᶜ : Set ℕ).Infinite := (Set.finite_singleton 0).infinite_compl
  have := @h ℕ {0}ᶜ 0 (by simp)
  rw [hs.ncard, (hs.mono (Set.subset_insert _ _)).ncard] at this
  simp at this

-- `Set.encard_iUnion_of_finite` idx 2: necessary (iota = Nat, s i = {i}: encard univ = top, finsum with infinite support = 0)
theorem p2_16 : ¬ drop0% Set.encard_iUnion_of_finite 2 := fun h => by
  have := @h ℕ ℕ (fun i => {i}) (fun i j hij => Set.disjoint_singleton.mpr hij)
  have hsup : (Function.support fun i : ℕ => ({i} : Set ℕ).encard).Infinite := by
    simpa [Function.support] using Set.infinite_univ
  rw [finsum_of_infinite_support hsup] at this
  simp at this

-- `Set.Countable.nonempty_encodable` idx 2: necessary (s = univ in Real)
theorem p2_17 : ¬ drop0% Set.Countable.nonempty_encodable 2 := fun h => by
  obtain ⟨e⟩ := @h ℝ Set.univ
  exact Cardinal.not_countable_real (Set.countable_coe_iff.mp (@Encodable.countable _ e))

-- `Set.countable_iff_exists_subset_range` idx 1: necessary (alpha = Empty, s = empty set: no f : Nat -> Empty)
theorem p2_18 : ¬ drop0% Set.countable_iff_exists_subset_range 1 :=
  fun h => ((@h Empty ∅).mp Set.countable_empty).elim fun f _ => (f 0).elim

-- `Set.Countable.image` idx 3: necessary (s = univ in Real, f = id)
theorem p2_19 : ¬ drop0% Set.Countable.image 3 :=
  fun h => Cardinal.not_countable_real (by simpa using @h ℝ ℝ Set.univ id)

-- `Set.Countable.insert` idx 3: necessary (s = univ in Real)
theorem p2_20 : ¬ drop0% Set.Countable.insert 3 :=
  fun h => Cardinal.not_countable_real (by simpa using @h ℝ Set.univ 0)

-- `Set.countable_ofPred_finite_subset` idx 2: necessary (s = univ in Real: singletons inject Real)
theorem p2_21 : ¬ drop0% Set.countable_ofPred_finite_subset 2 := fun h => by
  have := (@h ℝ Set.univ).preimage (f := fun x : ℝ => ({x} : Set ℝ)) Set.singleton_injective
  exact Cardinal.not_countable_real (by convert this; ext x; simp)

-- `Set.Infinite.inter_of_finite_diff` idx 4: necessary (s = univ in Nat, t = empty)
theorem p2_22 : ¬ drop0% Set.Infinite.inter_of_finite_diff 4 :=
  fun h => by simpa using @h ℕ Set.univ ∅ Set.infinite_univ

-- `Set.eq_finite_iUnion_of_finite_subset_iUnion` idx 5: necessary (s = fun _ => empty, t = {0})
theorem p2_23 : ¬ drop0% Set.eq_finite_iUnion_of_finite_subset_iUnion 5 := fun h => by
  obtain ⟨I, -, σ, -, hsub, heq⟩ := @h ℕ Unit (fun _ => ∅) {0} (Set.finite_singleton 0)
  have h0 : (0 : ℕ) ∈ ({0} : Set ℕ) := rfl
  rw [heq, Set.mem_iUnion] at h0
  obtain ⟨i, hi⟩ := h0
  exact hsub i hi

-- `Set.infinite_of_not_bddAbove` idx 2: necessary (Unit ⊕ Unit with the sum order, s = univ: finite, not bounded above)
theorem p2_24 : ¬ drop0% Set.infinite_of_not_bddAbove 2 := fun h => by
  have hnb : ¬ BddAbove (Set.univ : Set (Unit ⊕ Unit)) := by
    rintro ⟨x, hx⟩
    have h1 := hx (Set.mem_univ (Sum.inl ()))
    have h2 := hx (Set.mem_univ (Sum.inr ()))
    cases x <;> simp_all
  exact @h (Unit ⊕ Unit) _ _ Set.univ hnb Set.finite_univ

-- `Set.image_diff_of_injOn` idx 5: necessary (s = {0,1}, t = {1}, f = fun _ => 0)
theorem p2_25 : ¬ drop0% Set.image_diff_of_injOn 5 := fun h => by
  have := Set.ext_iff.mp (@h ℕ ℕ {0, 1} (fun _ => 0) {1} (by simp)) 0
  simp at this

-- `Set.LeftInvOn.congr_left` idx 6: necessary (f = id, f1' = f2' = fun _ => 0, s = t = univ)
theorem p2_26 : ¬ drop0% Set.LeftInvOn.congr_left 6 := fun h => by
  have := @h ℕ ℕ Set.univ id (fun _ => 0) (fun _ => 0) Set.univ (Set.mapsTo_univ _ _) (Set.eqOn_refl _ _)
  exact absurd (this (Set.mem_univ 1)) (by simp)

-- `Function.Semiconj.injOn_range` idx 6: necessary (fa = fb = fun _ => 0, f = id on Nat)
theorem p2_27 : ¬ drop0% Function.Semiconj.injOn_range 6 := fun h => by
  have := @h ℕ ℕ (fun _ => 0) (fun _ => 0) id (fun _ => rfl) (Set.injOn_id _)
  exact absurd (this ⟨0, rfl⟩ ⟨1, rfl⟩ rfl) (by decide)

-- `Function.Semiconj.injOn_range` idx 7: necessary (fa = succ, fb = fun _ => 1, f = fun n => min n 1)
theorem p2_28 : ¬ drop0% Function.Semiconj.injOn_range 7 := fun h => by
  have := @h ℕ ℕ Nat.succ (fun _ => 1) (fun n => min n 1) (fun x => by simp) Nat.succ_injective
  exact absurd (this ⟨0, rfl⟩ ⟨1, rfl⟩ rfl) (by decide)

-- `Set.MapsTo.extendDomain` idx 8: necessary (alpha = beta = Unit, p = True, g = 1, s = univ, t = empty)
theorem p2_29 : ¬ drop0% Set.MapsTo.extendDomain 8 := fun h => by
  have := @h Unit Unit (fun _ => True) _ (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm 1 Set.univ ∅
  have h1 := this (x := ()) ⟨(), Set.mem_univ _, rfl⟩
  simp at h1

-- `Set.range_ite_const` idx 7: necessary (p = fun _ => True on Unit, x = 0, y = 1)
theorem p2_30 : ¬ drop0% Set.range_ite_const 7 := fun h => by
  have := Set.ext_iff.mp (@h Unit ℕ (fun _ => True) _ 0 1 ⟨(), trivial⟩) 1
  simp at this

-- `Set.surjOn_iUnion₂` idx 7: necessary (s = empty, t = fun _ _ => univ, f = id)
theorem p2_31 : ¬ drop0% Set.surjOn_iUnion₂ 7 := fun h => by
  have := @h ℕ ℕ True (fun _ => True) ∅ (fun _ _ => Set.univ) id
  have h1 := this (show (0 : ℕ) ∈ _ by simp)
  simp at h1

-- `Set.BijOn.iInter_congr` idx 9: necessary (h = id on Unit, f = fun _ => empty, g = fun _ => univ)
theorem p2_32 : ¬ drop0% Set.BijOn.iInter_congr 9 := fun h => by
  have := @h ℕ Unit Unit Set.univ Set.univ (fun _ => ∅) (fun _ => Set.univ) id (Set.bijOn_id _)
  simp at this
  exact Set.empty_ne_univ this

-- `Set.iInter_const` idx 2: necessary (iota = False, s = empty: intersection is univ)
theorem p2_33 : ¬ drop0% Set.iInter_const 2 := fun h => by
  have := @h ℕ False ∅
  simp at this

-- `Set.image2_distrib_subset_right` idx 15: necessary (f = g = f1 = f2 = fun _ _ => 0, g' = fun _ _ => 1, all sets univ)
theorem p2_34 : ¬ drop0% Set.image2_distrib_subset_right 15 := fun h => by
  have := @h ℕ ℕ ℕ ℕ ℕ ℕ ℕ Set.univ Set.univ Set.univ (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ _ => 1)
  have h1 := this (Set.mem_image2_of_mem (Set.mem_image2_of_mem (Set.mem_univ 0) (Set.mem_univ 0)) (Set.mem_univ 0))
  simp at h1

-- `Set.biUnion_diff_biUnion_eq` idx 5: necessary (s = {0}, t = {1}, f = fun _ => univ)
theorem p2_35 : ¬ drop0% Set.biUnion_diff_biUnion_eq 5 := fun h => by
  have := Set.ext_iff.mp (@h ℕ ℕ {0} {1} (fun _ => Set.univ)) 0
  simp at this

-- `Set.prod_subset_prod_iff_right` idx 5: necessary (s = empty, t = univ, t1 = empty)
theorem p2_36 : ¬ drop0% Set.prod_subset_prod_iff_right 5 := fun h => by
  have := @h ℕ ℕ ∅ Set.univ ∅
  simp at this

-- `Monotone.set_prod` idx 7: necessary (alpha = Bool, f = fun _ => univ, g x = if x then empty else univ)
theorem p2_37 : ¬ drop0% Monotone.set_prod 7 := fun h => by
  have := @h Bool ℕ ℕ _ (fun _ => Set.univ) (fun x => if x then ∅ else Set.univ) monotone_const
  have h1 := this (show false ≤ true by decide)
  have h2 := h1 (show ((0 : ℕ), (0 : ℕ)) ∈ _ by simp)
  simp at h2

-- `Set.pi_image_pi_of_subset` idx 6: necessary (iota = alpha i = Unit, s1 = univ, s2 = empty, C = fun _ => {univ}: empty set only on the right)
theorem p2_38 : ¬ drop0% Set.pi_image_pi_of_subset 6 := fun h => by
  have heq := @h Unit (fun _ => Unit) Set.univ ∅ (fun _ => {Set.univ}) (fun _ => Set.singleton_nonempty _)
  have h1 : (∅ : Set (Unit → Unit)) ∈ Set.univ.pi '' (∅ : Set Unit).pi (fun _ => ({Set.univ} : Set (Set Unit))) :=
    ⟨fun _ => ∅, by simp, by ext x; simp⟩
  rw [← heq] at h1
  obtain ⟨t, ht, he⟩ := h1
  have hm : (fun _ : Unit => ()) ∈ Set.univ.pi t := fun i _ => by
    have := ht i trivial
    simp at this
    simp [this]
  rw [he] at hm
  exact hm

-- `Set.iUnionLift_of_mem` idx 7: necessary (alpha = Bool, S = fun _ => {true}, T = univ, x = true)
theorem p2_39 : ¬ indep0% Set.iUnionLift_of_mem 7 := fun h => by
  have := @h Bool True True (fun _ => {true}) (fun _ _ => trivial) (fun _ _ _ _ _ => rfl) Set.univ
    ⟨true, Set.mem_univ _⟩ trivial rfl
  have h1 := this (Set.mem_univ false)
  simp at h1

-- `Function.Injective.sumElim` idx 6: necessary (alpha = Empty, beta = Bool, gamma = True, g constant)
theorem p2_40 : ¬ drop0% Function.Injective.sumElim 6 := fun h => by
  have := @h Empty Bool True Empty.elim (fun _ => trivial) (fun e => e.elim) (fun e => e.elim)
  exact absurd (@this (Sum.inr true) (Sum.inr false) rfl) (by simp)

-- `List.Vector.mem_cons_of_mem` idx 5: necessary (a = 0, a' = 1, v = nil)
theorem p2_41 : ¬ drop0% List.Vector.mem_cons_of_mem 5 :=
  fun h => absurd (@h ℕ 0 0 1 List.Vector.nil) (by simp)

-- `WType.infinite_of_nonempty_of_isEmpty` idx 4: necessary (alpha = Unit, beta = fun _ => Empty: WType is finite)
theorem p2_42 : ¬ drop0% WType.infinite_of_nonempty_of_isEmpty 4 := fun h => by
  have hf : Finite (WType fun _ : Unit => Empty) := Finite.of_injective (fun _ => ()) (by
    rintro ⟨⟨⟩, f⟩ ⟨⟨⟩, g⟩ -
    congr; funext e; exact e.elim)
  have hi := @h Unit (fun _ => Empty) () () _
  exact not_finite (WType fun _ : Unit => Empty)

-- `ZMod.natCast_comp_val` idx 3: necessary (n = 0, R = Int, at -1: natAbs gives 1, cast gives -1)
theorem p2_43 : ¬ drop0% ZMod.natCast_comp_val 3 :=
  fun h => absurd (congrFun (@h 0 ℤ _) (-1)) (by decide)

-- `Nat.chineseRemainderOfList_perm` idx 6: removable (if some s i = 0 with i in l, both values are congruent to a i mod 0, so both equal a i)
theorem p2_44 : drop% Nat.chineseRemainderOfList_perm 6 := by
  intro ι a s l l' hl co
  by_cases hs : ∀ i ∈ l, s i ≠ 0
  · exact Nat.chineseRemainderOfList_perm a s hl hs co
  · push Not at hs
    obtain ⟨i, hi, h0⟩ := hs
    have e1 := (Nat.chineseRemainderOfList a s l co).prop i hi
    have e2 := (Nat.chineseRemainderOfList a s l' (co.perm hl fun {x y} => Nat.coprime_comm.mpr)).prop i (hl.mem_iff.mp hi)
    rw [h0, Nat.modEq_zero_iff] at e1 e2
    exact e1.trans e2.symm

-- `Nat.Prime.dvd_choose_iff` idx 5: removable (if k < n then choose k n = 0 and i = k gives p | k - k = 0, so both sides hold)
theorem p2_45 : drop% Nat.Prime.dvd_choose_iff 5 := by
  intro p k n hp hn
  by_cases hk : n ≤ k
  · exact Nat.Prime.dvd_choose_iff hp hn hk
  · push Not at hk
    rw [Nat.choose_eq_zero_of_lt hk]
    exact ⟨fun _ => ⟨k, hk, by simp⟩, fun _ => dvd_zero p⟩

-- `Nat.length_digitsAppend` idx 2: removable (if b <= 1 then n < b^l forces n = 0 (and l = 0 when b = 0); digitsAppend is replicate l 0)
theorem p2_46 : drop% Nat.length_digitsAppend 2 := by
  intro n b l hn
  rcases Nat.lt_or_ge 1 b with hb | hb
  · exact Nat.length_digitsAppend hb l hn
  · interval_cases b
    · rcases l with _ | l
      · simp at hn; subst hn; simp [Nat.digitsAppend]
      · simp at hn
    · simp at hn; subst hn; simp [Nat.digitsAppend]

-- `Set.ncard_le_ncard_iff_ncard_diff_le_ncard_diff` idx 3: removable (if s is infinite, s.ncard = 0 and s \ t is infinite (t finite), so both sides hold)
theorem p2_47 : drop% Set.ncard_le_ncard_iff_ncard_diff_le_ncard_diff 3 := by
  intro α s t ht
  by_cases hs : s.Finite
  · exact Set.ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff hs ht
  · rw [Set.Infinite.ncard hs, Set.Infinite.ncard (Set.Infinite.sdiff hs ht)]
    simp

-- `_private.Mathlib.Data.QPF.Multivariate.Constructions.Cofix.0.MvQPF.Cofix.bisim_aux` idx 5: removable (the public MvQPF.Cofix.bisim_rel is exactly the statement without h')
theorem p2_48 : drop% _private.Mathlib.Data.QPF.Multivariate.Constructions.Cofix.«0».MvQPF.Cofix.bisim_aux 5 :=
  fun r h => MvQPF.Cofix.bisim_rel r h

-- `Nat.nth_add_eq_sub` idx 4: removable (if nth p n = 0 (p 0 and n = 0 forces m = 0, or finite with card <= n) the shifted predicate also has nth 0, and 0 - m = 0)
theorem p2_49 : drop% Nat.nth_add_eq_sub 4 := by
  intro p m n h0
  by_cases h : Nat.nth p n = 0
  · rw [h, Nat.zero_sub]
    rw [Nat.nth_eq_zero] at h ⊢
    rcases h with ⟨hp0, rfl⟩ | ⟨hf, hle⟩
    · have hm : m = 0 := by
        by_contra hm
        exact h0 0 (Nat.pos_of_ne_zero hm) hp0
      subst hm
      left; simpa using hp0
    · right
      have hfq : (Set.ofPred fun i => p (i + m)).Finite :=
        Set.Finite.preimage (f := fun i => i + m) (fun a _ b _ hab => by simpa using hab) hf
      refine ⟨hfq, le_trans ?_ hle⟩
      apply Finset.card_le_card_of_injOn (fun i => i + m)
      · intro a ha
        simpa [Set.ofPred] using ha
      · intro a _ b _ hab
        simpa using hab
  · exact Nat.nth_add_eq_sub h0 h

-- `Nat.nth_eq_zero_mono` idx 4: necessary (p = (· = 1), a = 1, b = 0: nth p 1 = 0, nth p 0 = 1)
theorem p2_50 : ¬ drop0% Nat.nth_eq_zero_mono 4 := fun h => by
  have h1 : Nat.nth (fun n => n = 1) 0 = 1 := by
    have := Nat.nth_count (p := fun n => n = 1) (n := 1) rfl
    simpa [Nat.count_succ] using this
  have hf : (Set.ofPred fun n : ℕ => n = 1).Finite := by
    simp [Set.ofPred]
  have h2 : Nat.nth (fun n => n = 1) 1 = 0 :=
    Nat.nth_eq_zero.mpr (Or.inr ⟨hf, by simp⟩)
  have := @h (fun n => n = 1) (by decide) 1 0 h2
  omega

def PF2 : PFunctor := ⟨Bool, fun _ => Unit⟩

-- `PFunctor.M.IsBisimulation.tail` idx 2: necessary (F = Bool streams, R x _ := head x = true, a = true, f = f' = constant false stream)
theorem p2_51 : ¬ drop0% PFunctor.M.IsBisimulation.tail 2 := fun h => by
  let g : Bool → PF2 Bool := fun b => ⟨b, fun _ => b⟩
  let c : PF2.M := PFunctor.M.corec g false
  have e : PFunctor.M.dest c = PF2.map (PFunctor.M.corec g) (g false) := PFunctor.M.dest_corec _ _
  have hc : c.head = (false : PF2.A) := by
    rw [← PFunctor.M.mk_dest c, PFunctor.M.head_mk, e]; rfl
  have := @h PF2 (fun x _ => x.head = (true : PF2.A)) true (fun _ => c) (fun _ => c)
    (by rw [PFunctor.M.head_mk]; rfl) ()
  rw [hc] at this
  exact Bool.false_ne_true this

-- `List.Vector.mapAccumr₂_bisim_tail` idx 12: necessary (n = 1, f1 outputs 0, f2 outputs 1)
theorem p2_52 : ¬ drop0% List.Vector.mapAccumr₂_bisim_tail 12 := fun h => by
  have := @h ℕ ℕ ℕ ℕ ℕ 1 ⟨[0], rfl⟩ ⟨[0], rfl⟩ (fun _ _ s => (s, 0)) (fun _ _ s => (s, 1)) 0 0
  exact absurd this (by decide)

-- `MulAction.minimalPeriod_pos` idx 6: necessary (Multiplicative Int acting on itself, a = ofAdd 1, b = 1: orderOf = 0)
theorem p2_53 : ¬ drop0% MulAction.minimalPeriod_pos 6 := fun h => by
  have ho : orderOf (Multiplicative.ofAdd (1 : ℤ)) = 0 := by
    rw [orderOf_eq_zero_iff']
    intro n hn he
    have := congrArg Multiplicative.toAdd he
    simp at this
    omega
  have hne := @h (Multiplicative ℤ) (Multiplicative ℤ) _ (Multiplicative.ofAdd 1) _ 1
  exact hne.out ho

-- `Finsupp.multinomial_of_support_subset` idx 3: necessary (sigma = Bool, d = 1 everywhere, s = empty: 1 vs 2)
theorem p2_54 : ¬ drop0% Finsupp.multinomial_of_support_subset 3 := fun h => by
  let d : Bool →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)
  have := @h Bool d ∅
  rw [Finsupp.multinomial_eq_of_support_subset (s := Finset.univ) (Finset.subset_univ _)] at this
  have hs := Nat.multinomial_spec (Finset.univ : Finset Bool) d
  rw [← this, Nat.multinomial_empty] at hs
  simp [d] at hs

-- `Finset.sum_pow_eq_sum_piAntidiag_of_commute` idx 6: necessary (R = 2x2 Nat matrices, f true = E11, f false = E12 do not commute)
theorem p2_55 : ¬ indep0% Finset.sum_pow_eq_sum_piAntidiag_of_commute 6 := fun h => by
  let f : Bool → Matrix (Fin 2) (Fin 2) ℕ := fun b => if b then !![1, 0; 0, 0] else !![0, 1; 0, 0]
  have := @h Bool (Matrix (Fin 2) (Fin 2) ℕ) _ _ Finset.univ f 0
  have hc := this (x := true) (by simp) (y := false) (by simp) (by decide)
  have := congrFun (congrFun hc 0) 1
  simp [f, Matrix.mul_apply, Fin.sum_univ_two] at this

-- `Ordnode.Valid'.node4L` idx 10: necessary (l = r = nil, x = 0, y = 1, m = node 1 nil 5 nil: result not ordered)
theorem p2_56 : ¬ drop0% Ordnode.Valid'.node4L 10 := fun h => by
  have := @h ℕ _ Ordnode.nil 0 (Ordnode.node 1 Ordnode.nil 5 Ordnode.nil) 1 Ordnode.nil ⊥ ⊤
    (Ordnode.valid'_nil (by simp [Ordnode.Bounded])) (Ordnode.valid'_nil (by simp [Ordnode.Bounded]))
    (by decide) (Or.inl ⟨rfl, rfl, by decide⟩)
  have h2 := this.ord
  simp [Ordnode.node4L, Ordnode.node', Ordnode.Bounded] at h2

-- `Set.iUnionLift_unary` idx 10: necessary (alpha = beta = Bool (beta : Type, not Sort 0), S = univ, u = negation, ui = id, ubeta = id)
theorem p2_57 : ¬ (∀ {α : Type} {ι : Prop} {β : Type} {S : ι → Set α} {f : (i : ι) → ↑(S i) → β}
    {hf : ∀ (i j : ι) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩} {T : Set α}
    (hT' : T = Set.iUnion S) (u : ↑T → ↑T) (ui : (i : ι) → ↑(S i) → ↑(S i)) (uβ : β → β),
    (∀ (i : ι) (x : ↑(S i)), f i (ui i x) = uβ (f i x)) →
      ∀ (x : ↑T), Set.iUnionLift S f hf T (le_of_eq hT') (u x) = uβ (Set.iUnionLift S f hf T (le_of_eq hT') x)) :=
  fun h => by
  have := @h Bool True Bool (fun _ => Set.univ) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ (by simp)
    (fun x => ⟨!x.val, Set.mem_univ _⟩) (fun _ x => x) id (fun _ _ => rfl) ⟨true, Set.mem_univ _⟩
  rw [Set.iUnionLift_of_mem _ (i := trivial) (Set.mem_univ _), Set.iUnionLift_of_mem _ (i := trivial) (Set.mem_univ _)] at this
  simp at this

/-- Closed sets of the reals: the closed set of points at distance at least 1/(n+1) from 0
(for `true`), resp. the point 0 (for `false`). -/
noncomputable def clF (n : ℕ) (b : Bool) : Closeds ℝ :=
  if b then ⟨{x | 1 / ((n : ℝ) + 1) ≤ |x|}, isClosed_le continuous_const continuous_abs⟩
  else ⟨{0}, isClosed_singleton⟩

-- `iSup_iInf_eq_of_finite` idx 4: necessary (alpha = Closeds Real, iota = Nat, f n true = {x | 1/(n+1) <= |x|}, f n false = {0}: left side bottom, 0 in right side)
theorem p2_58 : ¬ (∀ {α : Type} {ι : Type} {κ : ι → Type} [Order.Coframe α] {f : (a : ι) → κ a → α},
    ⨆ a, ⨅ b, f a b = ⨅ g : (∀ a, κ a), ⨆ a, f a (g a)) := fun h => by
  have hL : (⨆ n, ⨅ b, clF n b) = ⊥ := by
    refine iSup_eq_bot.mpr fun n => eq_bot_iff.mpr ?_
    refine le_trans (le_inf (iInf_le _ true) (iInf_le _ false)) ?_
    rw [← SetLike.coe_subset_coe, Closeds.coe_inf, Closeds.coe_bot]
    rintro x ⟨h1, h2⟩
    simp [clF] at h1 h2
    subst h2
    simp at h1
    have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    linarith
  have hR : (0 : ℝ) ∈ (⨅ g : (ℕ → Bool), ⨆ n, clF n (g n)) := by
    rw [Closeds.mem_iInf]
    intro g
    by_cases hg : ∃ n, g n = false
    · obtain ⟨n, hn⟩ := hg
      apply le_iSup (fun n => clF n (g n)) n
      simp [clF, hn]
    · have hg' : ∀ n, g n = true := fun n => by
        by_contra hc; exact hg ⟨n, by simpa using hc⟩
      have hsub : ∀ n : ℕ, (1 / ((n : ℝ) + 1)) ∈ (⨆ n, clF n (g n)) := fun n => by
        apply le_iSup (fun n => clF n (g n)) n
        simp only [clF, hg' n, ite_true]
        show 1 / ((n : ℝ) + 1) ≤ |1 / ((n : ℝ) + 1)|
        exact le_abs_self _
      exact (⨆ n, clF n (g n)).isClosed.mem_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
        (Filter.Eventually.of_forall hsub)
  have := @h (Closeds ℝ) ℕ (fun _ => Bool) _ clF
  rw [hL] at this
  rw [← this, ← SetLike.mem_coe, Closeds.coe_bot] at hR
  exact hR


end Probe2
