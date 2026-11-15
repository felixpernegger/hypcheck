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

namespace Probe1
/-- drop1%: like drop0% but all universe parameters set to 1 (for Sort-polymorphic refutations). -/
elab "drop1% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.one
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

theorem notWF {β : Type*} {r : β → β → Prop} (f : ℕ → β) (hf : ∀ n, r (f (n+1)) (f n)) :
    ¬ WellFounded r := by
  intro h
  obtain ⟨m, ⟨n, rfl⟩, hm⟩ := h.has_min (Set.range f) ⟨f 0, 0, rfl⟩
  exact hm _ ⟨n+1, rfl⟩ (hf n)

/-- Extended naturals with max as multiplication (one is 0, zero is top): trivial units, not cancellative. -/
def MaxN := ℕ∞

def toM (n : ℕ∞) : MaxN := n
def ofM (a : MaxN) : ℕ∞ := a

noncomputable instance : CommMonoidWithZero MaxN where
  mul a b := toM (max (ofM a) (ofM b))
  one := toM 0
  zero := toM ⊤
  mul_assoc a b c := max_assoc (ofM a) (ofM b) (ofM c)
  one_mul a := max_eq_right (by simp : (0:ℕ∞) ≤ ofM a)
  mul_one a := max_eq_left (by simp : (0:ℕ∞) ≤ ofM a)
  zero_mul a := max_eq_left (le_top : ofM a ≤ ⊤)
  mul_zero a := max_eq_right (le_top : ofM a ≤ ⊤)
  mul_comm a b := max_comm (ofM a) (ofM b)

@[simp] theorem ofM_toM (n : ℕ∞) : ofM (toM n) = n := rfl
@[simp] theorem ofM_zero : ofM 0 = ⊤ := rfl
@[simp] theorem ofM_one : ofM 1 = 0 := rfl
@[simp] theorem ofM_mul (a b : MaxN) : ofM (a * b) = max (ofM a) (ofM b) := rfl
theorem ofM_inj {a b : MaxN} : ofM a = ofM b ↔ a = b := Iff.rfl

theorem maxN_dvd (a b : MaxN) : a ∣ b ↔ ofM a ≤ ofM b := by
  constructor
  · rintro ⟨c, rfl⟩; simp
  · intro h; exact ⟨b, ofM_inj.1 (by simp [h])⟩

instance : Subsingleton MaxNˣ := ⟨fun u v => by
  have key : ∀ w : MaxNˣ, w = 1 := fun w => by
    apply Units.ext
    have h1 := congrArg ofM w.val_inv
    simp only [ofM_mul, ofM_one] at h1
    have h2 : ofM (w : MaxN) ≤ 0 := h1 ▸ le_max_left _ _
    exact ofM_inj.1 (by simpa using h2)
  rw [key u, key v]⟩

theorem maxN_prime (n : ℕ∞) (h0 : n ≠ 0) (ht : n ≠ ⊤) : Prime (toM n) := by
  refine ⟨fun e => ht (by simpa using congrArg ofM e), fun hu => h0 ?_, fun a b hab => ?_⟩
  · simpa using congrArg ofM (isUnit_iff_eq_one.1 hu)
  · rw [maxN_dvd] at hab; rw [maxN_dvd, maxN_dvd]
    simpa using hab

/-- ℕ as a conditionally complete lattice whose junk supremum of an unbounded set depends on the set. -/
def J := ℕ

def toJ (n : ℕ) : J := n
def ofJ (a : J) : ℕ := a

instance : Lattice J := inferInstanceAs (Lattice ℕ)

open Classical in
noncomputable instance : ConditionallyCompleteLattice J :=
  { (inferInstance : Lattice J) with
    sSup := fun s : Set J => if s.Nonempty ∧ BddAbove s then toJ (sSup (α := ℕ) s) else
      if toJ 7 ∈ s then toJ 1 else toJ 0
    sInf := fun s : Set J => toJ (sInf (α := ℕ) s)
    isLUB_csSup := fun s hn hb => by
      show IsLUB s (if s.Nonempty ∧ BddAbove s then toJ (sSup (α := ℕ) s) else
        if toJ 7 ∈ s then toJ 1 else toJ 0)
      rw [if_pos ⟨hn, hb⟩]; exact isLUB_csSup (α := ℕ) hn hb
    isGLB_csInf := fun s hn hb => isGLB_csInf (α := ℕ) hn hb }

open Classical in
theorem sSupJ (s : Set J) (hs : ¬ BddAbove s) : sSup s = if toJ 7 ∈ s then toJ 1 else toJ 0 := by
  classical
  show (if _ then _ else _) = _
  rw [if_neg (fun h => hs h.2)]

theorem leJ {a b : J} : a ≤ b ↔ ofJ a ≤ ofJ b := Iff.rfl
@[simp] theorem ofJ_toJ (n : ℕ) : ofJ (toJ n) = n := rfl
theorem toJ_inj {a b : ℕ} : toJ a = toJ b ↔ a = b := Iff.rfl

end Probe1
open Probe1

-- `DFinsupp.instIsCancelAdd` idx 3: necessary
theorem p1_1 : ¬ drop0% DFinsupp.instIsCancelAdd 3 := fun h => by
  have := @h Unit (fun _ => ℕ∞) _
  have := add_left_cancel (a := DFinsupp.single (β := fun _ : Unit => ℕ∞) () ⊤) (b := 0) (c := DFinsupp.single () 1)
    (DFinsupp.ext fun i => by simp)
  have := DFunLike.congr_fun this ()
  simp at this


-- `DFinsupp.Colex.isBotZeroClass` idx 5: necessary
theorem p1_3 : ¬ drop0% DFinsupp.Colex.isBotZeroClass 5 := fun h => by
  have := @h Unit (fun _ => ℤ) _ _ _
  have h1 : toColex (DFinsupp.single (β := fun _ : Unit => ℤ) () (-1)) < 0 := by
    rw [DFinsupp.colex_lt_iff_of_unique]; simp
  exact lt_irrefl _ (lt_of_lt_of_le h1 (this.isBot_zero _))

-- `DFinsupp.Lex.wellFounded` idx 7: necessary
theorem p1_4 : ¬ drop0% DFinsupp.Lex.wellFounded 7 := fun h => by
  have := @h Bool (fun _ => ℕ) _ (fun _ _ => False) (fun _ a b => a < b) (fun _ _ h => Nat.not_lt_zero _ h)
    (fun _ => wellFounded_lt)
  have h1 : DFinsupp.Lex (fun _ _ => False) (fun _ a b => a < b) (DFinsupp.single true 1 : Π₀ _ : Bool, ℕ)
      (DFinsupp.single false 1) := ⟨false, fun _ h => h.elim, by simp⟩
  have h2 : DFinsupp.Lex (fun _ _ => False) (fun _ a b => a < b) (DFinsupp.single false 1 : Π₀ _ : Bool, ℕ)
      (DFinsupp.single true 1) := ⟨true, fun _ h => h.elim, by simp⟩
  exact @WellFounded.asymmetric _ _ this _ _ h1 h2

-- `Pi.Colex.wellFoundedLT` idx 5: necessary
theorem p1_5 : ¬ drop0% Pi.Colex.wellFoundedLT 5 := fun h => by
  have := @wellFounded_lt _ _ (@h Unit (fun _ => ℤ) _ _ _)
  exact notWF (fun n => toColex (fun _ => -(n:ℤ))) (fun n => by
    rw [Pi.Colex.lt_iff_of_unique]; simp) this

-- `Function.wellFoundedLT` idx 2: necessary
theorem p1_6 : ¬ drop0% Function.wellFoundedLT 2 := fun h => by
  have := @wellFounded_lt _ _ (@h ℕ ℕ _ _)
  refine notWF (fun n => fun k => if n ≤ k then 1 else 0) (fun n => ?_) this
  refine Pi.lt_def.2 ⟨fun k => ?_, n, by simp⟩
  dsimp only; split_ifs <;> omega

-- `ENat.nat_induction` idx 4: necessary
theorem p1_7 : ¬ drop0% ENat.nat_induction 4 := fun h =>
  absurd (@h (fun x => x ≠ ⊤) ⊤ (by simp) (by intro n _; simp)) (by simp)

-- `ENat.coe_iSup` idx 2: necessary
theorem p1_8 : ¬ drop1% ENat.coe_iSup 2 := fun h => by
  have := @h ℕ id
  have h2 : ¬ BddAbove (Set.range (id : ℕ → ℕ)) := by
    rintro ⟨b, hb⟩; exact absurd (hb ⟨b+1, rfl⟩) (by simp)
  rw [(ENat.iSup_coe_eq_top).2 h2] at this
  simp at this

-- `ENat.mul_right_strictMono` idx 2: necessary
theorem p1_9 : ¬ drop0% ENat.mul_right_strictMono 2 := fun h => by
  have := @h ⊤ (by simp) 1 2 (show (1:ℕ∞) < 2 by norm_num)
  simp at this

-- `EReal.induction₂` idx 5: necessary
theorem p1_10 : ¬ drop0% EReal.induction₂ 5 := fun h => by
  have := @h (fun x y => ¬ (x = ⊤ ∧ y = ⊥)) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) ⊤ ⊥
  simp at this

-- `EReal.induction₂_symm` idx 8: necessary
theorem p1_11 : ¬ drop0% EReal.induction₂_symm 8 := fun h => by
  have := @h (fun x y => x = ⊤ ∨ x = ⊥ ∨ y = ⊤ ∨ y = ⊥) (by intro x y; tauto) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) 0 0
  simp at this

-- `_private.Mathlib.Data.EReal.Inv.0.EReal.exists_lt_mul_right_of_nonneg` idx 3: necessary
theorem p1_12 : ¬ drop0% _private.Mathlib.Data.EReal.Inv.«0».EReal.exists_lt_mul_right_of_nonneg 3 := fun h => by
  obtain ⟨b, hb, -⟩ := @h (-1) (-1) 0 le_rfl (by norm_num)
  simp only [Set.mem_Ioo] at hb
  exact absurd (hb.1.trans hb.2) (by norm_num)

-- `EReal.induction₂_neg_left` idx 2: necessary
theorem p1_13 : ¬ drop0% EReal.induction₂_neg_left 2 := fun h => by
  have := @h (fun x y => y ≠ ⊤ ∨ (x ≠ ⊤ ∧ x ≠ ⊥))
    (by intro x y hxy; rcases hxy with h | ⟨h1, h2⟩
        · exact Or.inl h
        · right; constructor
          · intro e; apply h2; rw [← neg_neg x, e]; rfl
          · intro e; apply h1; rw [← neg_neg x, e]; rfl)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) ⊤ ⊤
  simp at this

-- `Finmap.erase_union_singleton` idx 6: necessary
theorem p1_14 : ¬ drop0% Finmap.erase_union_singleton 6 := fun h => by
  have := congrArg (Finmap.lookup 0) (@h ℕ (fun _ => ℕ) _ 0 0 ∅)
  simp at this

-- `Finset.erase_insert` idx 4: necessary
theorem p1_15 : ¬ drop0% Finset.erase_insert 4 := fun h => absurd (@h ℕ _ 0 {0}) (by decide)

-- `Finset.card_bij'` idx 9: necessary
theorem p1_16 : ¬ drop0% Finset.card_bij' 9 := fun h => by
  have := @h ℕ ℕ {0} {0, 1} (fun _ _ => 0) (fun _ _ => 0) (by simp) (by simp) (by simp)
  simp at this

-- `Finset.fold_cons` idx 9: necessary
theorem p1_17 : ¬ indep0% Finset.fold_cons 9 := fun h =>
  absurd (@h ℕ ℕ (· + ·) _ _ id 0 {0} 0) (by decide)

-- `Finset.fold_ite'` idx 4: necessary
theorem p1_18 : ¬ indep0% Finset.fold_ite' 4 := fun h => by
  have := (@h ℕ ℕ (fun a b => (a + b) / 2) ⟨fun a b => by simp [Nat.add_comm]⟩ id 0 ∅ id (by simp)
    (fun _ => True) _).assoc 0 0 2
  simp at this

-- `Finset.map_perm` idx 3: necessary
theorem p1_19 : ¬ drop0% Finset.map_perm 3 := fun h => by
  have := @h ℕ {0} (Equiv.swap 0 1)
  simp at this

-- `Finset.Nontrivial.not_subset_singleton` idx 3: necessary
theorem p1_20 : ¬ drop0% Finset.Nontrivial.not_subset_singleton 3 := fun h =>
  @h ℕ ∅ 0 (Finset.empty_subset _)

-- `Finset.cons_ne_empty` idx 3: necessary
theorem p1_21 : ¬ indep0% Finset.cons_ne_empty 3 := fun h => absurd (@h ℕ {0} 0) (by simp)

-- `Finset.coe_cons` idx 3: necessary
theorem p1_22 : ¬ indep0% Finset.coe_cons 3 := fun h => absurd (@h ℕ 0 {0}) (by simp)

-- `Finset.subset_inter` idx 5: necessary
theorem p1_23 : ¬ drop0% Finset.subset_inter 5 := fun h => absurd (@h ℕ _ {0} ∅ {0}) (by decide)

-- `Finset.comp_inf'_eq_inf'_comp` idx 9: necessary
theorem p1_24 : ¬ drop0% Finset.comp_inf'_eq_inf'_comp 9 := fun h => by
  have := @h ℕ ℕ ℕ _ _ {0, 1} (by simp) id (fun x => 5 - x)
  simp at this

-- `Finset.sup'_mono` idx 6: necessary
theorem p1_25 : ¬ indep0% Finset.sup'_mono 6 := fun h =>
  absurd (@h ℕ ℕ _ id {0} ∅ (by simp)) (by simp)

-- `Finset.inf'_apply` idx 5: necessary
theorem p1_26 : ¬ indep0% Finset.inf'_apply 5 := fun h =>
  absurd (@h ℕ ℕ (fun _ => ℕ) _ ∅ (fun _ _ => 0) 0) (by simp)

-- `Finset.isGreatest_max'` idx 3: necessary
theorem p1_27 : ¬ indep0% Finset.isGreatest_max' 3 := fun h =>
  absurd (@h ℕ _ ∅) (by simp)

-- `Set.IsWF.add` idx 7: necessary
theorem p1_28 : ¬ drop0% Set.IsWF.add 7 := fun h => by
  have := @h ℤ {0} Set.univ _ _ _ Set.isWF_singleton
  simp only [Set.singleton_add, zero_add, Set.image_id'] at this
  rw [Set.isWF_univ_iff] at this
  exact notWF (fun n => -(n:ℤ)) (fun n => by simp) this

-- `Finset.image₂_image₂_image₂_comm` idx 24: necessary
theorem p1_29 : ¬ drop0% Finset.image₂_image₂_image₂_comm 24 := fun h => by
  have := @h ℕ ℕ ℕ ℕ ℕ ℕ ℕ _ _ {0} {0} ℕ ℕ {0} {0} _ _ _ (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0)
  simp at this

-- `Multiset.noncommFoldr_coe` idx 4: necessary
theorem p1_30 : ¬ indep0% Multiset.noncommFoldr_coe 4 := fun h => by
  have hp := @h ℕ (List ℕ) List.cons [0, 1] []
  have := @hp 0 (by simp) 1 (by simp) (by decide) []
  simp at this

-- `Finset.noncommSum_induction` idx 5: necessary
theorem p1_31 : ¬ indep0% Finset.noncommSum_induction 5 := fun h => by
  have hp := @h ℕ (FreeAddMonoid ℕ) _ {0, 1} FreeAddMonoid.of (fun _ => True) (by simp) trivial (by simp)
  have := hp (show 0 ∈ _ by simp) (show 1 ∈ _ by simp) (by decide)
  have := congrArg FreeAddMonoid.toList this.eq
  simp at this

-- `Finset.noncommSum_addCommute` idx 7: necessary
theorem p1_32 : ¬ drop0% Finset.noncommSum_addCommute 7 := fun h => by
  have := @h ℕ (FreeAddMonoid ℕ) _ {0} (fun _ => FreeAddMonoid.of 0) (by simp) (FreeAddMonoid.of 1)
  rw [Finset.noncommSum_singleton] at this
  have := congrArg FreeAddMonoid.toList this.eq
  simp at this

-- `Finset.piecewise_mem_Icc_of_mem_of_mem` idx 9: necessary
theorem p1_33 : ¬ drop0% Finset.piecewise_mem_Icc_of_mem_of_mem 9 := fun h => by
  have := (@h Unit {()} (fun _ => inferInstance) (fun _ => ℕ) (fun _ => 5) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => inferInstance) ⟨le_rfl, le_rfl⟩).2 ()
  simp at this

-- `Finset.product_subset_product_left` idx 5: necessary
theorem p1_34 : ¬ drop0% Finset.product_subset_product_left 5 := fun h =>
  absurd (@h ℕ ℕ {0} ∅ {0}) (by decide)

-- `Finset.pairwiseDisjoint_disjUnion` idx 8: necessary
theorem p1_35 : ¬ drop0% Finset.pairwiseDisjoint_disjUnion 8 := fun h => by
  have := @h ℕ ℕ {0, 1} (fun _ => ∅) (fun _ => {0}) (fun _ => by simp) (by simp [Set.Pairwise])
    (by simp [Set.PairwiseDisjoint, Set.Pairwise])
  have := this (x := 0) (by simp) (y := 1) (by simp) (by decide)
  simp at this

-- `Finsupp.Colex.addRightMono` idx 5: necessary
theorem p1_36 : ¬ drop0% Finsupp.Colex.addRightMono 5 := fun h => by
  have := @h Unit (Fin 3) _ _ _
  have h12 : toColex (Finsupp.single () (1 : Fin 3)) ≤ toColex (Finsupp.single () 2) := by
    rw [Finsupp.Colex.le_iff_of_unique]; simp
  have := add_le_add_left h12 (toColex (Finsupp.single () (1 : Fin 3)))
  rw [Finsupp.Colex.le_iff_of_unique] at this
  simp at this

-- `Finsupp.DegLex.wellFoundedLT` idx 2: necessary
theorem p1_37 : ¬ drop0% Finsupp.DegLex.wellFoundedLT 2 := fun h => by
  have := @wellFounded_lt _ _ (@h ℕ _)
  exact notWF (fun n => toDegLex (Finsupp.single n 1)) (fun n => Finsupp.DegLex.single_strictAnti (Nat.lt_succ_self n)) this

-- `Finsupp.tsub_apply` idx 4: necessary
theorem p1_38 : ¬ indep0% Finsupp.tsub_apply 4 := fun h => by
  have := @h Unit ℤ _ _ _ _ 0 0 ()
  have : (0:ℤ) ≤ 0 + -1 := le_self_add
  norm_num at this

-- `Finsupp.Lex.wellFounded'` idx 6: necessary
theorem p1_39 : ¬ drop0% Finsupp.Lex.wellFounded' 6 := fun h => by
  have := @h Unit ℕ _ (fun _ _ => False) (fun a b => 0 < b ∧ b < a) (fun n hn => by omega)
    ⟨fun a b _ _ => rfl⟩ ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩
  refine notWF (fun n => Finsupp.single () (n+1)) (fun n => ?_) this
  rw [Finsupp.lex_def]
  exact ⟨(), fun _ h => h.elim, by simp⟩

-- `Finsupp.Colex.wellFoundedLT` idx 8: necessary
theorem p1_40 : ¬ drop0% Finsupp.Colex.wellFoundedLT 8 := fun h => by
  have := @wellFounded_lt _ _ (@h Unit ℚ≥0 _ _ _ _ _ _)
  refine notWF (fun n => toColex (Finsupp.single () (1 / ((n:ℚ≥0) + 1)))) (fun n => ?_) this
  rw [Finsupp.Colex.lt_iff_of_unique]
  change (Finsupp.single () (1 / (((n+1:ℕ):ℚ≥0) + 1))) () < (Finsupp.single () (1 / ((n:ℚ≥0) + 1))) ()
  rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
  gcongr
  push_cast; linarith

-- `Finsupp.Colex.wellFoundedLT_of_finite` idx 4: necessary
theorem p1_41 : ¬ drop0% Finsupp.Colex.wellFoundedLT_of_finite 4 := fun h => by
  have := @wellFounded_lt _ _ (@h ℤ ℕ _ _ _ _)
  exact notWF (fun n => toColex (Finsupp.single (-(n:ℤ)) 1))
    (fun n => Finsupp.Colex.single_strictMono (by omega)) this

-- `not_injective_infinite_finite` idx 3: necessary
theorem p1_42 : ¬ drop1% not_injective_infinite_finite 3 := fun h => @h ℕ ℕ _ id Function.injective_id

-- `Set.Finite.exists_ge` idx 3: necessary
theorem p1_43 : ¬ drop0% Set.Finite.exists_ge 3 := fun h => by
  obtain ⟨M, hM⟩ := @h (Unit ⊕ Unit) _ _ {Sum.inl (), Sum.inr ()} (Set.toFinite _)
  have h1 := hM (Sum.inl ()) (by simp)
  have h2 := hM (Sum.inr ()) (by simp)
  cases M <;> simp at h1 h2

-- `Finite.ciSup_prod` idx 3: necessary
theorem p1_44 : ¬ drop0% Finite.ciSup_prod 3 := fun h => by
  let f : ℕ × Bool → J := fun p => if p.2 then toJ (p.1 + 8) else if p.1 = 0 then toJ 7 else toJ 0
  have e := @h J ℕ Bool _ _ f
  have hg : ∀ i, (⨆ b, f (i, b)) = toJ (i + 8) := fun i =>
    le_antisymm (ciSup_le fun b => by
        rw [leJ]
        cases b
        · by_cases hi : i = 0 <;> simp [f, hi]
        · simp [f])
      (le_ciSup_of_le (Set.finite_range _).bddAbove true (by simp [f]))
  simp only [hg] at e
  have hL : ¬ BddAbove (Set.range f) := by
    rintro ⟨b, hb⟩
    have := leJ.1 (hb ⟨(ofJ b, true), rfl⟩)
    simp [f] at this
  have hR : ¬ BddAbove (Set.range fun i => toJ (i + 8)) := by
    rintro ⟨b, hb⟩
    have := leJ.1 (hb ⟨ofJ b, rfl⟩)
    simp at this
  rw [iSup, iSup, sSupJ _ hL, sSupJ _ hR, if_pos ⟨((0 : ℕ), false), rfl⟩, if_neg] at e
  · exact absurd (toJ_inj.1 e) (by decide)
  · rintro ⟨i, hi⟩
    exact absurd (toJ_inj.1 hi) (by omega)

-- `Fintype.piFinset_update_eq_filter_piFinset_mem` idx 8: necessary
theorem p1_45 : ¬ drop0% Fintype.piFinset_update_eq_filter_piFinset_mem 8 := fun h => by
  have e := @h Unit _ _ (fun _ => ℕ) _ (fun _ => ∅) () {0}
  have hm : (fun _ => (0:ℕ)) ∈ Fintype.piFinset (Function.update (fun _ => (∅ : Finset ℕ)) () {0}) := by
    simp [Fintype.mem_piFinset]
  rw [e] at hm
  simp [Fintype.mem_piFinset] at hm

-- `Holor.cprankMax_sum` idx 7: necessary
theorem p1_46 : ¬ drop0% Holor.cprankMax_sum 7 := fun h => by
  have := @h ℕ [] _ ℕ 0 {0} (fun _ => fun _ => 1)
  simp only [Finset.sum_singleton, mul_zero] at this
  have h0 : ∀ x : Holor ℕ [], Holor.CPRankMax 0 x → x = 0 := by
    intro x hx; cases hx; rfl
  have := congrFun (h0 _ this) ⟨[], List.Forall₂.nil⟩
  change (1:ℕ) = 0 at this; omega

-- `List.IsChain.prefix` idx 4: necessary
theorem p1_47 : ¬ drop0% List.IsChain.prefix 4 := fun h => by
  have := @h ℕ (fun _ _ => False) [0, 1] [0, 1] (List.prefix_refl _)
  simp at this

-- `List.prev_next` idx 3: necessary
theorem p1_48 : ¬ drop0% List.prev_next 3 := fun h =>
  absurd (@h ℕ _ [0, 1, 0] 1 (by decide)) (by decide)

-- `List.Forall₂.get` idx 8: removable
theorem p1_49 : indep% List.Forall₂.get 8 := by
  intro α β R x y h i hx
  rw [← h.length_eq]; exact hx

-- `List.foldl_range_eq_of_range_eq` idx 5: necessary
theorem p1_50 : ¬ drop0% List.foldl_range_eq_of_range_eq 5 := fun h => by
  have e := @h ℕ ℕ ℕ (fun a _ => a) (fun _ _ => 0) 1
  have hm : (0:ℕ) ∈ Set.range (List.foldl (fun _ _ => 0) 1 : List ℕ → ℕ) := ⟨[0], rfl⟩
  rw [← e] at hm
  obtain ⟨l, hl⟩ := hm
  have : ∀ l : List ℕ, List.foldl (fun a _ => a) 1 l = 1 := by
    intro l; induction l with
    | nil => rfl
    | cons x xs ih => simpa using ih
  rw [this] at hl; exact absurd hl (by decide)

-- `mem_list_primes_of_dvd_prod` idx 2: necessary
theorem p1_51 : ¬ drop0% mem_list_primes_of_dvd_prod 2 := fun h => by
  have := @h MaxN _ _ (toM 1) (maxN_prime 1 (by simp) (by simp)) [toM 2]
    (by simpa using maxN_prime 2 (by simp) (by simp))
    (by rw [List.prod_singleton, maxN_dvd]; simp)
  rw [List.mem_singleton, ← ofM_inj] at this
  simp at this

-- `List.SortedGE.map_ofDual` idx 3: necessary
theorem p1_52 : ¬ drop0% List.SortedGE.map_ofDual 3 := fun h => by
  have := (@h ℕ _ [OrderDual.toDual 0, OrderDual.toDual 1] : Monotone _) (a := (0 : Fin 2)) (b := 1) (by decide)
  exact absurd this (by decide)

-- `Matrix.smul_mul` idx 10: necessary
theorem p1_53 : ¬ drop0% Matrix.smul_mul 10 := fun h => by
  have := @h Unit Unit Unit ℕ ℕ _ ⟨fun _ _ => 1⟩ _ _ _ 2 (fun _ _ => 1) (fun _ _ => 1)
  have := congrFun (congrFun this ()) ()
  revert this
  decide

-- `Multiset.card_erase_of_mem` idx 4: necessary
theorem p1_54 : ¬ drop0% Multiset.card_erase_of_mem 4 := fun h => absurd (@h ℕ _ 0 {1}) (by decide)

-- `Multiset.cons_sub_of_le` idx 5: necessary
theorem p1_55 : ¬ drop0% Multiset.cons_sub_of_le 5 := fun h => absurd (@h ℕ _ 0 0 {0}) (by decide)

-- `Multiset.notMem_mono` idx 5: necessary
theorem p1_56 : ¬ drop0% Multiset.notMem_mono 5 := fun h =>
  @h ℕ {0} {0} 0 (Multiset.Subset.refl _) (by simp)

-- `Multiset.ndunion_eq_union` idx 4: necessary
theorem p1_57 : ¬ drop0% Multiset.ndunion_eq_union 4 := fun h => absurd (@h ℕ _ {0, 0} 0) (by decide)

-- the statement's Finset zero is the pointwise one
open scoped Pointwise

-- `Finset.mem_dfinsupp_iff_of_support_subset` idx 8: necessary
theorem p1_2 : ¬ drop0% Finset.mem_dfinsupp_iff_of_support_subset 8 := fun h => by
  have := @h Unit (fun _ => ℕ) _ _ ∅ 0 _ (DFinsupp.single () {1})
  simp [Finset.mem_dfinsupp_iff] at this
