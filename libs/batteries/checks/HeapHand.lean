import Lean.Elab.Command
-- add the library modules your rows need here (e.g. `import Init`, `import Std.Sat.AIG.CNF`); avoid `import Lean`/`import Std` (1.5 GB)
import Init
import Batteries.Data.BinaryHeap.Lemmas

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
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

/-! Heap cluster hand file (wave W1). Reusable pieces defined below:
- models (each a Nat synonym with numerals): Cy (cyclic comparison on 0, 1, 2, oriented but not
  transitive; 3 and above compared as usual, above 0, 1, 2), No (distinct values compare as less,
  not oriented), Lt (everything compares as less);
- decision procedures: decISub (subtree relation, via the fuel function sbF and the lemmas
  isub_le, isub_inv, isub_step, sbF_iff), decChildren, decTopDown, decBelow, decParent, decPGC,
  decExceptAt, decBottomUp, the copied binHeapWF instance, decMemHeap;
- hUpF with hUpF_eq: a fuel copy of the upward sift, since the library's well-founded definition
  does not reduce in the kernel (the downward sift and the pop loop do reduce).
Refutations were emitted by the generator in the scratch folder (gen.py). -/

open Batteries Batteries.BinaryHeap

/-- InSubtree relation (private) as an abbreviation. -/
abbrev ISub : Nat → Nat → Prop := priv% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.InSubtree

/-- Bounded Bool decision for the subtree relation. -/
def sbF (j : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | f+1, k => k == j || (decide (j < k) && sbF j f ((k-1)/2))

theorem isub_le {j k : Nat} (h : ISub j k) : j ≤ k :=
  (priv% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.InSubtree.le) h

theorem isub_refl (j : Nat) : ISub j j := by
  have r := priv% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.InSubtree.refl
  exact r

theorem isub_inv {j k : Nat} (h : ISub j k) : k = j ∨ (j < k ∧ ISub j ((k-1)/2)) := by
  induction h with
  | refl => exact .inl rfl
  | @left m h ih =>
    right; have := isub_le h; refine ⟨by omega, ?_⟩
    have e : (2 * m + 1 - 1) / 2 = m := by omega
    rw [e]; exact h
  | @right m h ih =>
    right; have := isub_le h; refine ⟨by omega, ?_⟩
    have e : (2 * m + 2 - 1) / 2 = m := by omega
    rw [e]; exact h

theorem isub_step {j k : Nat} (hjk : j < k) (h : ISub j ((k-1)/2)) : ISub j k := by
  by_cases hk : k % 2 = 0
  · have e : k = 2 * ((k - 1) / 2) + 2 := by omega
    rw [e]; exact (priv% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.InSubtree.right) h
  · have e : k = 2 * ((k - 1) / 2) + 1 := by omega
    rw [e]; exact (priv% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.InSubtree.left) h

theorem sbF_iff (j : Nat) : ∀ f k, k < f → (sbF j f k = true ↔ ISub j k)
  | 0, k, h => by omega
  | f+1, k, h => by
    simp only [sbF, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨hjk, hs⟩)
      · exact isub_refl _
      · exact isub_step hjk ((sbF_iff j f _ (by omega)).mp hs)
    · intro hs
      rcases isub_inv hs with e | ⟨hjk, hs'⟩
      · exact .inl e
      · exact .inr ⟨hjk, (sbF_iff j f _ (by omega)).mpr hs'⟩

instance decISub (j k : Nat) : Decidable (ISub j k) :=
  decidable_of_iff _ (sbF_iff j (k+1) k (Nat.lt_succ_self k))

instance decChildren {α} {sz} [Ord α] (a : Vector α sz) (i : Fin sz) : Decidable (WF.Children a i) :=
  inferInstanceAs (Decidable ((∀ _ : 2 * i.val + 1 < sz, (compare a[i] a[2 * i.val + 1]).isGE) ∧
    (∀ _ : 2 * i.val + 1 + 1 < sz, (compare a[i] a[2 * i.val + 1 + 1]).isGE)))

instance decTopDown {α} {sz} [Ord α] (a : Vector α sz) : Decidable (WF.TopDown a) :=
  inferInstanceAs (Decidable (∀ i : Fin sz, WF.Children a i))

instance decBelow {α} {sz} [Ord α] (a : Vector α sz) (i : Nat) :
    Decidable ((priv% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Below) a i) :=
  inferInstanceAs (Decidable (∀ j : Fin sz, i < j.val → WF.Children a j))

instance decParent {α} {sz} [Ord α] (a : Vector α sz) (i : Fin sz) :
    Decidable ((priv% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Parent) a i) :=
  inferInstanceAs (Decidable (∀ _ : 0 < i.val, (compare (a[(i.val - 1)/2]'(by omega)) a[i]).isGE))

instance decPGC {α} {sz} [Ord α] (a : Vector α sz) (i : Fin sz) :
    Decidable ((priv% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ParentGeChildren) a i) :=
  inferInstanceAs (Decidable ((∀ _ : 2 * i.val + 1 < sz, (compare (a[(i.val - 1)/2]'(by omega)) a[2 * i.val + 1]).isGE) ∧
    (∀ _ : 2 * i.val + 1 + 1 < sz, (compare (a[(i.val - 1)/2]'(by omega)) a[2 * i.val + 1 + 1]).isGE)))

instance decExceptAt {α} {sz} [Ord α] (a : Vector α sz) (i : Fin sz) :
    Decidable ((priv% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ExceptAt) a i) :=
  inferInstanceAs (Decidable (∀ j : Fin sz, i ≠ j →
    (priv% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Parent) a j))

instance decBottomUp {α} {sz} [Ord α] (a : Vector α sz) :
    Decidable ((priv% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.BottomUp) a) :=
  inferInstanceAs (Decidable (∀ i : Fin sz,
    (priv% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Parent) a i))

/-- Decidable heap well-formedness (copied from the batdec source). -/
noncomputable instance HypCheckDec.binHeapWF {α} [Ord α] (h : Batteries.BinaryHeap α) :
    Decidable h.WF :=
  inferInstanceAs (Decidable (∀ i : Fin h.size, (∀ _ : 2 * i.val + 1 < h.size,
    (compare h.vector[i] h.vector[2 * i.val + 1]).isGE) ∧ (∀ _ : 2 * i.val + 1 + 1 < h.size,
    (compare h.vector[i] h.vector[2 * i.val + 1 + 1]).isGE)))

/-- Model Cy: cyclic comparison on 0, 1, 2 (oriented, reflexive, not transitive); values from 3 on
are compared as usual and lie above 0, 1, 2. -/
def Cy := Nat
instance : OfNat Cy n := ⟨(n : Nat)⟩
instance : DecidableEq Cy := inferInstanceAs (DecidableEq Nat)
def cmpCy (a b : Nat) : Ordering :=
  if a < 3 ∧ b < 3 then
    (if a = b then .eq else if (a + 1) % 3 = b then .lt else .gt)
  else compare a b
instance : Ord Cy := ⟨cmpCy⟩

/-- Model No: every two distinct values compare as less (not oriented). -/
def No := Nat
instance : OfNat No n := ⟨(n : Nat)⟩
instance : DecidableEq No := inferInstanceAs (DecidableEq Nat)
instance : Ord No := ⟨fun a b => if a = b then .eq else .lt⟩


/-- Model Lt: every comparison is less (not reflexive, not oriented). -/
def Lt := Nat
instance : OfNat Lt n := ⟨(n : Nat)⟩
instance : DecidableEq Lt := inferInstanceAs (DecidableEq Nat)
instance : Ord Lt := ⟨fun _ _ => .lt⟩

/-- Decidable heap membership through the list of the underlying array. -/
instance decMemHeap {α} [Ord α] [DecidableEq α] (x : α) (h : Batteries.BinaryHeap α) : Decidable (x ∈ h) :=
  decidable_of_iff (x ∈ h.arr.toList) (by simp [Batteries.BinaryHeap.mem_def])

/-- Fuel copy of the upward sift (kernel-reducible). -/
def hUpF {α} {sz} [Ord α] : Nat → Vector α sz → Fin sz → Vector α sz
  | 0, a, _ => a
  | _+1, a, ⟨0, _⟩ => a
  | f+1, a, ⟨i'+1, hi⟩ =>
    if (compare a[i'/2] a[i'+1]).isLT then hUpF f (a.swap (i'+1) (i'/2)) ⟨i'/2, by omega⟩ else a

theorem hUpF_eq {α} {sz} [Ord α] : ∀ (f : Nat) (a : Vector α sz) (i : Fin sz), i.val < f →
    heapifyUp a i = hUpF f a i
  | 0, a, i, h => by omega
  | f+1, a, ⟨0, _⟩, _ => by rw [heapifyUp]; rfl
  | f+1, a, ⟨i'+1, hi⟩, h => by
    rw [heapifyUp, hUpF]
    by_cases hc : (compare a[i'/2] a[i'+1]).isLT = true
    · rw [if_pos hc, if_pos (by simpa using hc)]; exact hUpF_eq f _ _ (by simp at h ⊢; omega)
    · rw [if_neg hc, if_neg (by simpa using hc)]

-- `Batteries.BinaryHeap.maxChild_ge_left` (hypothesis 8, hleft, dependent): removable, derivable from hmc: maxChild only returns a child index, so j = 2i+1 or 2i+2 and j < sz give 2i+1 < sz
theorem r1 : indep% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.maxChild_ge_left 8 := by
  intro α sz _ _ a i j hmc
  have h := (priv% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.maxChild_isChild) hmc
  have := j.isLt
  omega

-- `Batteries.BinaryHeap.max_ge_all` (hypothesis 7, h_ne, dependent): removable, derivable from h_in: y ∈ heap means y is in the underlying array, which is therefore nonempty
theorem r2 : indep% Batteries.BinaryHeap.max_ge_all 7 := by
  intro α y _ _ heap hwf h_in
  rw [mem_def, Array.mem_iff_getElem] at h_in
  obtain ⟨i, hi, _⟩ := h_in
  simp only [size]; omega

-- `Batteries.BinaryHeap.WF.parent_ge_subtree` (hypothesis 8, hj, dependent): removable, derivable from hk and hsub: InSubtree j k gives j ≤ k, and k < sz
theorem r3 : indep% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.parent_ge_subtree 8 := by
  intro α sz k j _ _ a hk hwf_below hsub
  have := isub_le hsub
  omega

-- `Batteries.BinaryHeap.WF.TopDown.root_ge_all` (hypothesis 6, hne, dependent): removable, derivable from k : Fin sz, which already forces 0 < sz
theorem r4 : indep% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.TopDown.root_ge_all 6 := by
  intro α sz _ _ a hwf k
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt

-- `Batteries.BinaryHeap.maxChild_ge_right` (hypothesis 3, inst): Ord always lt, a=#v[0,0,0], i=0: maxChild picks 2 and compare a[2] a[2] = lt
theorem c1 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.maxChild_ge_right 3 := fun h =>
  absurd (@h (Lt) (3) _ (#v[0, 0, 0]) (⟨0, by decide⟩) (⟨2, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.of_swap_maxChild` (hypothesis 3, inst): non-oriented Ord (distinct = lt), a=#v[0,1,0], i=0, j=2
theorem c2 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.WF.Children.of_swap_maxChild 3 := fun h =>
  absurd (@h (No) (3) _ (#v[0, 1, 0]) (⟨0, by decide⟩) (⟨2, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.of_swap_maxChild` (hypothesis 7, hmaxChild): Nat, a=#v[0,1], i=j=0
theorem c3 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.WF.Children.of_swap_maxChild 7 := fun h =>
  absurd (@h (Nat) (2) _ _ (#v[0, 1]) (⟨0, by decide⟩) (⟨0, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.of_swap_maxChild` (hypothesis 8, h_ge): Nat, a=#v[1,0], i=0, j=1
theorem c4 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.WF.Children.of_swap_maxChild 8 := fun h =>
  absurd (@h (Nat) (2) _ _ (#v[1, 0]) (⟨0, by decide⟩) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.of_ge_maxChild` (hypothesis 5, inst): cyclic Ord, a=#v[0,2,1], i=0, j=1: 0>2>1 but 0<1
theorem c5 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.WF.Children.of_ge_maxChild 5 := fun h =>
  absurd (@h (Cy) (3) (⟨0, by decide⟩) (⟨1, by decide⟩) _ (#v[0, 2, 1]) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.of_ge_maxChild` (hypothesis 7, hmaxChild): Nat, a=#v[0,1], i=j=0
theorem c6 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.WF.Children.of_ge_maxChild 7 := fun h =>
  absurd (@h (Nat) (2) (⟨0, by decide⟩) (⟨0, by decide⟩) _ _ (#v[0, 1]) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.of_ge_maxChild` (hypothesis 8, h_ge): Nat, a=#v[0,1], i=0, j=1
theorem c7 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.WF.Children.of_ge_maxChild 8 := fun h =>
  absurd (@h (Nat) (2) (⟨0, by decide⟩) (⟨1, by decide⟩) _ _ (#v[0, 1]) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_getElem_of_not_inSubtree'` (hypothesis 6, hk): Nat, sz=2, k=2, i=1, a=#v[0,1]: 2 not in the subtree of 1 and 2 ≥ sz
theorem c8 : ¬ indep0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_getElem_of_not_inSubtree' 6 := fun h =>
  absurd (@h (Nat) (2) (2) _ (#v[0, 1]) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_get_of_not_child` (hypothesis 6, hki): Nat, v=#v[0,5,1,4,3,0,0,9], i=0, k=1: sifting 0 down brings 9 below position 1
theorem c9 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_get_of_not_child 6 := fun h =>
  absurd (@h (Nat) (8) (⟨1, by decide⟩) (⟨0, by decide⟩) _ (#v[0, 5, 1, 4, 3, 0, 0, 9]) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_get_of_not_child` (hypothesis 7, hwf): Nat, v=#v[0,1,0,0], k=0, i=3
theorem c10 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_get_of_not_child 7 := fun h =>
  absurd (@h (Nat) (4) (⟨0, by decide⟩) (⟨3, by decide⟩) _ (#v[0, 1, 0, 0]) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_get_of_not_child` (hypothesis 8, hleft_ne): Nat, v=#v[1,0,0,5], k=0, i=1
theorem c11 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_get_of_not_child 8 := fun h =>
  absurd (@h (Nat) (4) (⟨0, by decide⟩) (⟨1, by decide⟩) _ (#v[1, 0, 0, 5]) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_get_of_not_child` (hypothesis 9, hright_ne): Nat, v=#v[1,0,0,0,0,5], k=0, i=2
theorem c12 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_get_of_not_child 9 := fun h =>
  absurd (@h (Nat) (6) (⟨0, by decide⟩) (⟨2, by decide⟩) _ (#v[1, 0, 0, 0, 0, 5]) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_swap_children_of_lt` (hypothesis 7, hchild): Nat, a=#v[5,1,0,0], i=0, j=3, k=1
theorem c13 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_swap_children_of_lt 7 := fun h =>
  absurd (@h (Nat) (4) _ (#v[5, 1, 0, 0]) (⟨0, by decide⟩) (⟨3, by decide⟩) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_swap_children_of_lt` (hypothesis 8, hik): Nat, a=#v[1,0,0], i=0, j=1, k=0
theorem c14 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_swap_children_of_lt 8 := fun h =>
  absurd (@h (Nat) (3) _ (#v[1, 0, 0]) (⟨0, by decide⟩) (⟨1, by decide⟩) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_swap_children_of_lt` (hypothesis 9, hkj): Nat, a=#v[0,5,1,4,3,0,0,9], i=0, j=k=1
theorem c15 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_swap_children_of_lt 9 := fun h =>
  absurd (@h (Nat) (8) _ (#v[0, 5, 1, 4, 3, 0, 0, 9]) (⟨0, by decide⟩) (⟨1, by decide⟩) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_swap_children_of_lt` (hypothesis 10, hwf): Nat, a=#v[0,0,0,1], i=0, j=2, k=1
theorem c16 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_swap_children_of_lt 10 := fun h =>
  absurd (@h (Nat) (4) _ (#v[0, 0, 0, 1]) (⟨0, by decide⟩) (⟨2, by decide⟩) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_children_of_ge_subtree` (hypothesis 6, hj_child): Nat, b=#v[0,9,1,4,3,0,0,8], j=0, k=1
theorem c17 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_children_of_ge_subtree 6 := fun h =>
  absurd (@h (Nat) (8) _ (#v[0, 9, 1, 4, 3, 0, 0, 8]) (⟨0, by decide⟩) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_children_of_ge_subtree` (hypothesis 7, hge_subtree): Nat, b=#v[1,0,0,5], j=1, k=0
theorem c18 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_children_of_ge_subtree 7 := fun h =>
  absurd (@h (Nat) (4) _ (#v[1, 0, 0, 5]) (⟨1, by decide⟩) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_children_of_ge_subtree` (hypothesis 8, hwf_k): Nat, b=#v[1,0,2], j=1, k=0
theorem c19 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_children_of_ge_subtree 8 := fun h =>
  absurd (@h (Nat) (3) _ (#v[1, 0, 2]) (⟨1, by decide⟩) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_set_of_le_preserves_children` (hypothesis 4, inst): cyclic Ord, v=#v[0,2], i=1, x=1
theorem c20 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_set_of_le_preserves_children 4 := fun h =>
  absurd (@h (Cy) (2) (1) _ (#v[0, 2]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_set_of_le_preserves_children` (hypothesis 7, htd): Nat, v=#v[0,5], i=1, x=3
theorem c21 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_set_of_le_preserves_children 7 := fun h =>
  absurd (@h (Nat) (2) (3) _ _ (#v[0, 5]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_set_of_le_preserves_children` (hypothesis 8, h_ge): Nat, v=#v[5,0], i=1, x=9
theorem c22 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_set_of_le_preserves_children 8 := fun h =>
  absurd (@h (Nat) (2) (9) _ _ (#v[5, 0]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_children_swap` (hypothesis 3, inst): non-oriented Ord, a=#v[0,1,0], i=0, j=2
theorem c23 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_children_swap 3 := fun h =>
  absurd (@h (No) (3) _ (#v[0, 1, 0]) (⟨0, by decide⟩) (⟨2, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_children_swap` (hypothesis 7, hmaxChild): Nat, a=#v[0,1,5], i=0, j=1
theorem c24 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_children_swap 7 := fun h =>
  absurd (@h (Nat) (3) _ _ (#v[0, 1, 5]) (⟨0, by decide⟩) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_children_swap` (hypothesis 8, h_ge): Nat, a=#v[5,1,0], i=0, j=1
theorem c25 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_children_swap 8 := fun h =>
  absurd (@h (Nat) (3) _ _ (#v[5, 1, 0]) (⟨0, by decide⟩) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_children_swap` (hypothesis 9, hbelow): Nat, a=#v[0,1,0,5], i=0, j=1
theorem c26 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_children_swap 9 := fun h =>
  absurd (@h (Nat) (4) _ _ (#v[0, 1, 0, 5]) (⟨0, by decide⟩) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_wf` (hypothesis 3, inst): non-oriented Ord, a=#v[0,1,0], i=0
theorem c27 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_wf 3 := fun h =>
  absurd (@h (No) (3) _ (#v[0, 1, 0]) (⟨0, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyDown_wf` (hypothesis 6, hbelow): Nat, a=#v[0,0,0,5], i=0
theorem c28 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyDown_wf 6 := fun h =>
  absurd (@h (Nat) (4) _ _ (#v[0, 0, 0, 5]) (⟨0, by decide⟩)) (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyUp_bottomUp` (hypothesis 4, inst): non-oriented Ord, a=#v[0,1], i=1
theorem c29 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyUp_bottomUp 4 := fun h => by
  have := @h (No) (2) (⟨1, by decide⟩) _ (#v[0, 1]) (by decide +kernel) (by decide +kernel)
  rw [hUpF_eq 10 _ _ (by decide)] at this
  exact absurd this (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyUp_bottomUp` (hypothesis 6, h_exc): Nat, a=#v[0,0,1], i=1
theorem c30 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyUp_bottomUp 6 := fun h => by
  have := @h (Nat) (3) (⟨1, by decide⟩) _ _ (#v[0, 0, 1]) (by decide +kernel)
  rw [hUpF_eq 10 _ _ (by decide)] at this
  exact absurd this (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyUp_bottomUp` (hypothesis 7, h_clp): Nat, a=#v[0,5,0,3], i=1
theorem c31 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyUp_bottomUp 7 := fun h => by
  have := @h (Nat) (4) (⟨1, by decide⟩) _ _ (#v[0, 5, 0, 3]) (by decide +kernel)
  rw [hUpF_eq 10 _ _ (by decide)] at this
  exact absurd this (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyUp_topDown` (hypothesis 4, inst): non-oriented Ord, a=#v[0,1], i=1
theorem c32 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyUp_topDown 4 := fun h => by
  have := @h (No) (2) (⟨1, by decide⟩) _ (#v[0, 1]) (by decide +kernel) (by decide +kernel)
  rw [hUpF_eq 10 _ _ (by decide)] at this
  exact absurd this (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyUp_topDown` (hypothesis 6, hexcept): Nat, a=#v[0,0,1], i=1
theorem c33 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyUp_topDown 6 := fun h => by
  have := @h (Nat) (3) (⟨1, by decide⟩) _ _ (#v[0, 0, 1]) (by decide +kernel)
  rw [hUpF_eq 10 _ _ (by decide)] at this
  exact absurd this (by decide +kernel)

-- `Batteries.BinaryHeap.heapifyUp_topDown` (hypothesis 7, hchildren): Nat, a=#v[0,5,0,3], i=1
theorem c34 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.heapifyUp_topDown 7 := fun h => by
  have := @h (Nat) (4) (⟨1, by decide⟩) _ _ (#v[0, 5, 0, 3]) (by decide +kernel)
  rw [hUpF_eq 10 _ _ (by decide)] at this
  exact absurd this (by decide +kernel)

-- `Batteries.BinaryHeap.mkHeap.loop_wf` (hypothesis 4, inst): non-oriented Ord, a=#v[0,1,0], n=1
theorem c35 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.mkHeap.loop_wf 4 := fun h =>
  absurd (@h (No) (3) (1) _ (#v[0, 1, 0]) (by decide) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.mkHeap.loop_wf` (hypothesis 7, hinv): Nat, a=#v[0,1], n=0
theorem c36 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.mkHeap.loop_wf 7 := fun h =>
  absurd (@h (Nat) (2) (0) _ _ (#v[0, 1]) (by decide)) (by decide +kernel)

-- `Batteries.BinaryHeap.mkHeap_wf` (hypothesis 3, inst): non-oriented Ord, a=#v[0,1,0]
theorem c37 : ¬ drop0% Batteries.BinaryHeap.mkHeap_wf 3 := fun h =>
  absurd (@h (No) (3) _ (#v[0, 1, 0])) (by decide +kernel)

-- `Batteries.BinaryHeap.insert_wf` (hypothesis 3, inst): non-oriented Ord, heap [0], x=1
theorem c38 : ¬ drop0% Batteries.BinaryHeap.insert_wf 3 := fun h => by
  have := @h (No) (1) _ (⟨#[0]⟩) (by decide +kernel)
  simp only [BinaryHeap.insert] at this
  rw [hUpF_eq 10 _ _ (by decide)] at this
  exact absurd this (by decide +kernel)

-- `Batteries.BinaryHeap.insert_wf` (hypothesis 5, h_wf): Nat, heap [0,1], x=0
theorem c39 : ¬ drop0% Batteries.BinaryHeap.insert_wf 5 := fun h => by
  have := @h (Nat) (0) _ _ (⟨#[0, 1]⟩)
  simp only [BinaryHeap.insert] at this
  rw [hUpF_eq 10 _ _ (by decide)] at this
  exact absurd this (by decide +kernel)

-- `Batteries.BinaryHeap.max_ge_all` (hypothesis 3, inst): cyclic Ord, heap [0,2,0,1], y=1
theorem c40 : ¬ drop0% Batteries.BinaryHeap.max_ge_all 3 := fun h =>
  absurd (@h (Cy) (1) _ (⟨#[0, 2, 0, 1]⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.max_ge_all` (hypothesis 5, hwf): Nat, heap [0,1], y=1
theorem c41 : ¬ drop0% Batteries.BinaryHeap.max_ge_all 5 := fun h =>
  absurd (@h (Nat) (1) _ _ (⟨#[0, 1]⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.max_ge_all` (hypothesis 6, h_in): Nat, heap [0], y=1
theorem c42 : ¬ drop0% Batteries.BinaryHeap.max_ge_all 6 := fun h =>
  absurd (@h (Nat) (1) _ _ (⟨#[0]⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.popMax_wf` (hypothesis 2, inst): cyclic Ord, heap [2,1,2,0]: popMax leaves [0,1,2]
theorem c43 : ¬ drop0% Batteries.BinaryHeap.popMax_wf 2 := fun h =>
  absurd (@h (Cy) _ (⟨#[2, 1, 2, 0]⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.popMax_wf` (hypothesis 4, h_wf): Nat, heap [0,0,0,5,0]
theorem c44 : ¬ drop0% Batteries.BinaryHeap.popMax_wf 4 := fun h =>
  absurd (@h (Nat) _ _ (⟨#[0, 0, 0, 5, 0]⟩)) (by decide +kernel)

-- `Batteries.BinaryHeap.replaceMax_wf` (hypothesis 3, inst): cyclic Ord, heap [2,1,2], x=0
theorem c45 : ¬ drop0% Batteries.BinaryHeap.replaceMax_wf 3 := fun h =>
  absurd (@h (Cy) (0) _ (⟨#[2, 1, 2]⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.replaceMax_wf` (hypothesis 5, h_wf): Nat, heap [0,0,0,5], x=0
theorem c46 : ¬ drop0% Batteries.BinaryHeap.replaceMax_wf 5 := fun h =>
  absurd (@h (Nat) (0) _ _ (⟨#[0, 0, 0, 5]⟩)) (by decide +kernel)

-- `Batteries.BinaryHeap.insertExtractMax_wf` (hypothesis 3, inst): cyclic Ord on 0,1,2 with 3 on top, heap [3,2,1], x=0
theorem c47 : ¬ drop0% Batteries.BinaryHeap.insertExtractMax_wf 3 := fun h =>
  absurd (@h (Cy) (0) _ (⟨#[3, 2, 1]⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.mem_of_mem_popMax` (hypothesis 4, h): Nat, empty heap, x=0
theorem c48 : ¬ drop0% Batteries.BinaryHeap.mem_of_mem_popMax 4 := fun h =>
  absurd (@h (Nat) (0) _ (⟨#[]⟩)) (by decide +kernel)

-- `Batteries.BinaryHeap.decreaseKey_wf` (hypothesis 3, inst): cyclic Ord, heap [0,2], i=1, x=1
theorem c49 : ¬ drop0% Batteries.BinaryHeap.decreaseKey_wf 3 := fun h =>
  absurd (@h (Cy) (1) _ (⟨#[0, 2]⟩) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.decreaseKey_wf` (hypothesis 7, h_ge): Nat, heap [5,0], i=1, x=9
theorem c50 : ¬ drop0% Batteries.BinaryHeap.decreaseKey_wf 7 := fun h =>
  absurd (@h (Nat) (9) _ _ (⟨#[5, 0]⟩) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.increaseKey_wf` (hypothesis 3, inst): cyclic Ord, heap [0,2], i=0, x=1
theorem c51 : ¬ drop0% Batteries.BinaryHeap.increaseKey_wf 3 := fun h => by
  have := @h (Cy) (1) _ (⟨#[0, 2]⟩) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel)
  simp only [BinaryHeap.increaseKey] at this
  rw [hUpF_eq 10 _ _ (by decide)] at this
  exact absurd this (by decide +kernel)

-- `Batteries.BinaryHeap.increaseKey_wf` (hypothesis 6, h_wf): Nat, heap [0,5], i=0, x=0
theorem c52 : ¬ drop0% Batteries.BinaryHeap.increaseKey_wf 6 := fun h => by
  have := @h (Nat) (0) _ _ (⟨#[0, 5]⟩) (⟨0, by decide⟩) (by decide +kernel)
  simp only [BinaryHeap.increaseKey] at this
  rw [hUpF_eq 10 _ _ (by decide)] at this
  exact absurd this (by decide +kernel)

-- `Batteries.BinaryHeap.increaseKey_wf` (hypothesis 7, h_ge): Nat, heap [5,3], i=0, x=0
theorem c53 : ¬ drop0% Batteries.BinaryHeap.increaseKey_wf 7 := fun h => by
  have := @h (Nat) (0) _ _ (⟨#[5, 3]⟩) (⟨0, by decide⟩) (by decide +kernel)
  simp only [BinaryHeap.increaseKey] at this
  rw [hUpF_eq 10 _ _ (by decide)] at this
  exact absurd this (by decide +kernel)

-- `Batteries.BinaryHeap.toSortedArray.loop_sorted` (hypothesis 2, inst): cyclic Ord, heap [0,2,0,1], out empty
theorem c54 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.toSortedArray.loop_sorted 2 := fun h =>
  absurd (@h (Cy) _ (⟨#[0, 2, 0, 1]⟩) (#[]) (by decide +kernel) (by decide +kernel) (by intro x hx; simp at hx)) (by decide +kernel)

-- `Batteries.BinaryHeap.toSortedArray.loop_sorted` (hypothesis 5, hwf): Nat, heap [0,1], out empty
theorem c55 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.toSortedArray.loop_sorted 5 := fun h =>
  absurd (@h (Nat) _ _ (⟨#[0, 1]⟩) (#[]) (by decide +kernel) (by intro x hx; simp at hx)) (by decide +kernel)

-- `Batteries.BinaryHeap.toSortedArray.loop_sorted` (hypothesis 6, h_out_sorted): Nat, heap empty, out [0,1]
theorem c56 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.toSortedArray.loop_sorted 6 := fun h =>
  absurd (@h (Nat) _ _ (⟨#[]⟩) (#[0, 1]) (by decide +kernel) (by intro x _ y hy; simp [Batteries.BinaryHeap.mem_def] at hy)) (by decide +kernel)

-- `Batteries.BinaryHeap.toSortedArray.loop_sorted` (hypothesis 7, h_heap_le_out): Nat, heap [1], out [0]
theorem c57 : ¬ drop0% _private.Batteries.Data.BinaryHeap.Lemmas.«0».Batteries.BinaryHeap.toSortedArray.loop_sorted 7 := fun h =>
  absurd (@h (Nat) _ _ (⟨#[1]⟩) (#[0]) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.toSortedArray_sorted` (hypothesis 2, inst): cyclic Ord, heap [0,2,0,1]
theorem c58 : ¬ drop0% Batteries.BinaryHeap.toSortedArray_sorted 2 := fun h =>
  absurd (@h (Cy) _ (⟨#[0, 2, 0, 1]⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.congr` (hypothesis 6, hwf): Nat, a=b=#v[0,1], k=0
theorem c59 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Children.congr 6 := fun h =>
  absurd (@h (Nat) (2) _ (#v[0, 1]) (#v[0, 1]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.congr` (hypothesis 7, hk): Nat, a=#v[1,1], b=#v[0,1], k=0
theorem c60 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Children.congr 7 := fun h =>
  absurd (@h (Nat) (2) _ (#v[1, 1]) (#v[0, 1]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.congr` (hypothesis 8, hl): Nat, a=#v[0,0], b=#v[0,1], k=0
theorem c61 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Children.congr 8 := fun h =>
  absurd (@h (Nat) (2) _ (#v[0, 0]) (#v[0, 1]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.congr` (hypothesis 9, hr): Nat, a=#v[0,0,0], b=#v[0,0,1], k=0
theorem c62 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Children.congr 9 := fun h =>
  absurd (@h (Nat) (3) _ (#v[0, 0, 0]) (#v[0, 0, 1]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.InSubtree.not_of_lt` (hypothesis 2, hlt): j=k=0
theorem c63 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.InSubtree.not_of_lt 2 := fun h =>
  absurd (@h (0) (0)) (by decide +kernel)

-- `Batteries.BinaryHeap.InSubtree.trans` (hypothesis 3, hij): i=1, j=k=0
theorem c64 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.InSubtree.trans 3 := fun h =>
  absurd (@h (1) (0) (0) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.InSubtree.trans` (hypothesis 4, hjk): i=j=1, k=0
theorem c65 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.InSubtree.trans 4 := fun h =>
  absurd (@h (1) (1) (0) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.InSubtree.of_child` (hypothesis 2, h): i=1, j=0
theorem c66 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.InSubtree.of_child 2 := fun h =>
  absurd (@h (0) (1)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Below.of_le` (hypothesis 6, hij): Nat, a=#v[0,0,0,1], i=1, j=0
theorem c67 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Below.of_le 6 := fun h =>
  absurd (@h (Nat) (4) (1) (0) (#v[0, 0, 0, 1]) _ (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Below.of_le` (hypothesis 7, hbelow): Nat, a=#v[0,0,0,1], i=j=0
theorem c68 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Below.of_le 7 := fun h =>
  absurd (@h (Nat) (4) (0) (0) (#v[0, 0, 0, 1]) _ (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Below.swap` (hypothesis 6, hbelow): Nat, a=#v[0,0,0,0,0,1], i=0, j=1
theorem c69 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Below.swap 6 := fun h =>
  absurd (@h (Nat) (6) _ (#v[0, 0, 0, 0, 0, 1]) (⟨0, by decide⟩) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Below.swap` (hypothesis 7, hij): Nat, a=#v[0,0,0,1], i=1, j=0
theorem c70 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Below.swap 7 := fun h =>
  absurd (@h (Nat) (4) _ (#v[0, 0, 0, 1]) (⟨1, by decide⟩) (⟨0, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.set_of_ne` (hypothesis 7, hwf): Nat, v=#v[0,1,0,0], i=3, k=0, x=0
theorem c71 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Children.set_of_ne 7 := fun h =>
  absurd (@h (Nat) (4) (0) _ (#v[0, 1, 0, 0]) (⟨3, by decide⟩) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.set_of_ne` (hypothesis 8, hki): Nat, v=#v[1,1], i=k=0, x=0
theorem c72 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Children.set_of_ne 8 := fun h =>
  absurd (@h (Nat) (2) (0) _ (#v[1, 1]) (⟨0, by decide⟩) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.set_of_ne` (hypothesis 9, hleft_ne): Nat, v=#v[1,0], i=1, k=0, x=5
theorem c73 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Children.set_of_ne 9 := fun h =>
  absurd (@h (Nat) (2) (5) _ (#v[1, 0]) (⟨1, by decide⟩) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.set_of_ne` (hypothesis 10, hright_ne): Nat, v=#v[1,0,0], i=2, k=0, x=5
theorem c74 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Children.set_of_ne 10 := fun h =>
  absurd (@h (Nat) (3) (5) _ (#v[1, 0, 0]) (⟨2, by decide⟩) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.set_of_ge_child` (hypothesis 7, hwf): Nat, v=#v[0,1,0], k=0, i=2, x=0
theorem c75 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Children.set_of_ge_child 7 := fun h =>
  absurd (@h (Nat) (3) (0) _ (#v[0, 1, 0]) (⟨0, by decide⟩) (⟨2, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.set_of_ge_child` (hypothesis 8, h_child): Nat, v=#v[1,1], k=i=0, x=0
theorem c76 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Children.set_of_ge_child 8 := fun h =>
  absurd (@h (Nat) (2) (0) _ (#v[1, 1]) (⟨0, by decide⟩) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Children.set_of_ge_child` (hypothesis 9, h_ge): Nat, v=#v[1,0], k=0, i=1, x=5
theorem c77 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Children.set_of_ge_child 9 := fun h =>
  absurd (@h (Nat) (2) (5) _ (#v[1, 0]) (⟨0, by decide⟩) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.TopDown.below_of_set` (hypothesis 6, htd): Nat, v=#v[0,0,0,1], i=0, x=0
theorem c78 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.TopDown.below_of_set 6 := fun h =>
  absurd (@h (Nat) (4) (0) _ (#v[0, 0, 0, 1]) (⟨0, by decide⟩)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.TopDown.of_root_and_below` (hypothesis 5, a): Nat, a=#v[0,1]
theorem c79 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.TopDown.of_root_and_below 5 := fun h =>
  absurd (@h (Nat) (2) _ (#v[0, 1]) (by decide)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.TopDown.children_and_below` (hypothesis 4, htd): Nat, a=#v[0,1], i=0
theorem c80 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.TopDown.children_and_below 4 := fun h =>
  absurd (@h (Nat) (2) _ (#v[0, 1]) (⟨0, by decide⟩)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.parent_ge_subtree` (hypothesis 5, inst): cyclic Ord, a=#v[0,2,0,1], j=0, k=3
theorem c81 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.parent_ge_subtree 5 := fun h =>
  absurd (@h (Cy) (4) (3) (0) _ (#v[0, 2, 0, 1]) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.parent_ge_subtree` (hypothesis 7, hk): Nat, sz=1, a=#v[0], j=0, k=1 (1 is in the subtree of 0)
theorem c82 : ¬ indep0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.parent_ge_subtree 7 := fun h =>
  absurd (@h (Nat) (1) (1) (0) _ _ (#v[0]) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.parent_ge_subtree` (hypothesis 9, hwf_at): Nat, a=#v[0,1], j=0, k=1
theorem c83 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.parent_ge_subtree 9 := fun h =>
  absurd (@h (Nat) (2) (1) (0) _ _ (#v[0, 1]) (by decide) (by decide) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.parent_ge_subtree` (hypothesis 10, hwf_below): Nat, a=#v[1,0,0,5], j=0, k=3
theorem c84 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.parent_ge_subtree 10 := fun h =>
  absurd (@h (Nat) (4) (3) (0) _ _ (#v[1, 0, 0, 5]) (by decide) (by decide) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.parent_ge_subtree` (hypothesis 11, hsub): Nat, a=#v[1,0], j=1, k=0
theorem c85 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.parent_ge_subtree 11 := fun h =>
  absurd (@h (Nat) (2) (0) (1) _ _ (#v[1, 0]) (by decide) (by decide) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ge_subtree_of_modify` (hypothesis 4, inst): cyclic Ord, v=0, a=b=#v[2,1], j=0, m=1
theorem c86 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ge_subtree_of_modify 4 := fun h =>
  absurd (@h (Cy) (2) (0) _ (#v[2, 1]) (#v[2, 1]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ge_subtree_of_modify` (hypothesis 8, hge): Nat, v=0, a=#v[5,3], b=#v[0,3], j=0, m=1
theorem c87 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ge_subtree_of_modify 8 := fun h =>
  absurd (@h (Nat) (2) (0) _ _ (#v[5, 3]) (#v[0, 3]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ge_subtree_of_modify` (hypothesis 9, hwf_at): Nat, v=5, a=b=#v[5,9], j=0, m=1
theorem c88 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ge_subtree_of_modify 9 := fun h =>
  absurd (@h (Nat) (2) (5) _ _ (#v[5, 9]) (#v[5, 9]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ge_subtree_of_modify` (hypothesis 10, hwf_below): Nat, v=5, a=b=#v[5,0,0,9], j=0, m=3
theorem c89 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ge_subtree_of_modify 10 := fun h =>
  absurd (@h (Nat) (4) (5) _ _ (#v[5, 0, 0, 9]) (#v[5, 0, 0, 9]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (⟨3, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ge_subtree_of_modify` (hypothesis 11, hge_new): Nat, v=5, a=#v[5], b=#v[9], j=m=0
theorem c90 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ge_subtree_of_modify 11 := fun h =>
  absurd (@h (Nat) (1) (5) _ _ (#v[5]) (#v[9]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (⟨0, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ge_subtree_of_modify` (hypothesis 12, hunchanged): Nat, v=5, a=#v[5,0], b=#v[5,9], j=0, m=1
theorem c91 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ge_subtree_of_modify 12 := fun h =>
  absurd (@h (Nat) (2) (5) _ _ (#v[5, 0]) (#v[5, 9]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ge_subtree_of_modify` (hypothesis 14, a): Nat, v=0, a=b=#v[9,0], j=1, m=0
theorem c92 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ge_subtree_of_modify 14 := fun h =>
  absurd (@h (Nat) (2) (0) _ _ (#v[9, 0]) (#v[9, 0]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (⟨0, by decide⟩)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.TopDown.parent_ge_subtree_of_set` (hypothesis 4, inst): cyclic Ord, v=#v[0,2], i=1, x=1, m=1
theorem c93 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.TopDown.parent_ge_subtree_of_set 4 := fun h =>
  absurd (@h (Cy) (2) (1) _ (#v[0, 2]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.TopDown.parent_ge_subtree_of_set` (hypothesis 7, htd): Nat, v=#v[0,5], i=1, x=5, m=1
theorem c94 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.TopDown.parent_ge_subtree_of_set 7 := fun h =>
  absurd (@h (Nat) (2) (5) _ _ (#v[0, 5]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.TopDown.parent_ge_subtree_of_set` (hypothesis 8, h_le): Nat, v=#v[5,0], i=1, x=9, m=1
theorem c95 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.TopDown.parent_ge_subtree_of_set 8 := fun h =>
  absurd (@h (Nat) (2) (9) _ _ (#v[5, 0]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.TopDown.parent_ge_subtree_of_set` (hypothesis 11, hsub): Nat, v=#v[9,5,0,0], i=3, x=0, m=0
theorem c96 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.TopDown.parent_ge_subtree_of_set 11 := fun h =>
  absurd (@h (Nat) (4) (0) _ _ (#v[9, 5, 0, 0]) (⟨3, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel) (⟨0, by decide⟩)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.swap_preserves_ge_subtree` (hypothesis 3, inst): cyclic Ord, a=#v[0,0,0,2,0,0,0,1], i=0, j=1, k=7
theorem c97 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.swap_preserves_ge_subtree 3 := fun h =>
  absurd (@h (Cy) (8) _ (#v[0, 0, 0, 2, 0, 0, 0, 1]) (⟨0, by decide⟩) (⟨1, by decide⟩) (⟨7, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.swap_preserves_ge_subtree` (hypothesis 8, h_ij): Nat, a=#v[0,5], i=j=0, k=1
theorem c98 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.swap_preserves_ge_subtree 8 := fun h =>
  absurd (@h (Nat) (2) _ _ (#v[0, 5]) (⟨0, by decide⟩) (⟨0, by decide⟩) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.swap_preserves_ge_subtree` (hypothesis 9, h_ge): Nat, a=#v[5,0], i=0, j=k=1
theorem c99 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.swap_preserves_ge_subtree 9 := fun h =>
  absurd (@h (Nat) (2) _ _ (#v[5, 0]) (⟨0, by decide⟩) (⟨1, by decide⟩) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.swap_preserves_ge_subtree` (hypothesis 10, hbelow): Nat, a=#v[0,0,0,5], i=0, j=1, k=3
theorem c100 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.swap_preserves_ge_subtree 10 := fun h =>
  absurd (@h (Nat) (4) _ _ (#v[0, 0, 0, 5]) (⟨0, by decide⟩) (⟨1, by decide⟩) (⟨3, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.swap_preserves_ge_subtree` (hypothesis 11, hsub): Nat, a=#v[0,0,5], i=0, j=1, k=2
theorem c101 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.swap_preserves_ge_subtree 11 := fun h =>
  absurd (@h (Nat) (3) _ _ (#v[0, 0, 5]) (⟨0, by decide⟩) (⟨1, by decide⟩) (⟨2, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ExceptAt.swap_parent` (hypothesis 3, inst): cyclic Ord, a=#v[2,0,1], i=1
theorem c102 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ExceptAt.swap_parent 3 := fun h =>
  absurd (@h (Cy) (3) _ (#v[2, 0, 1]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ExceptAt.swap_parent` (hypothesis 6, h_ge): Nat, a=#v[5,0], i=1
theorem c103 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ExceptAt.swap_parent 6 := fun h =>
  absurd (@h (Nat) (2) _ _ (#v[5, 0]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ExceptAt.swap_parent` (hypothesis 7, hexcept): Nat, a=#v[0,5,9], i=1
theorem c104 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ExceptAt.swap_parent 7 := fun h =>
  absurd (@h (Nat) (3) _ _ (#v[0, 5, 9]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ExceptAt.swap_parent` (hypothesis 8, hchildren): Nat, a=#v[0,5,0,3], i=1
theorem c105 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ExceptAt.swap_parent 8 := fun h =>
  absurd (@h (Nat) (4) _ _ (#v[0, 5, 0, 3]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ParentGeChildren.swap_parent` (hypothesis 3, inst): cyclic Ord, a=#v[2,0,1], i=1
theorem c106 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ParentGeChildren.swap_parent 3 := fun h =>
  absurd (@h (Cy) (3) _ (#v[2, 0, 1]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ParentGeChildren.swap_parent` (hypothesis 6, h_ge): Nat, a=#v[5,0], i=1
theorem c107 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ParentGeChildren.swap_parent 6 := fun h =>
  absurd (@h (Nat) (2) _ _ (#v[5, 0]) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ParentGeChildren.swap_parent` (hypothesis 7, hexcept): Nat, a=#v[0,5,9], i=1
theorem c108 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ParentGeChildren.swap_parent 7 := fun h =>
  absurd (@h (Nat) (3) _ _ (#v[0, 5, 9]) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.BottomUp.of_exceptAt_root` (hypothesis 5, hexcept): Nat, a=#v[0,1]
theorem c109 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.BottomUp.of_exceptAt_root 5 := fun h =>
  absurd (@h (Nat) (2) _ (#v[0, 1]) (by decide)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.BottomUp.of_parent_and_exceptAt` (hypothesis 5, hexcept): Nat, a=#v[0,1], i=0
theorem c110 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.BottomUp.of_parent_and_exceptAt 5 := fun h =>
  absurd (@h (Nat) (2) _ (#v[0, 1]) (⟨0, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.BottomUp.of_parent_and_exceptAt` (hypothesis 6, hparent): Nat, a=#v[0,1], i=1
theorem c111 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.BottomUp.of_parent_and_exceptAt 6 := fun h =>
  absurd (@h (Nat) (2) _ (#v[0, 1]) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ExceptAt.set_of_ge` (hypothesis 4, inst): cyclic Ord, v=#v[0,2], i=0, x=1
theorem c112 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ExceptAt.set_of_ge 4 := fun h =>
  absurd (@h (Cy) (2) (1) _ (#v[0, 2]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ExceptAt.set_of_ge` (hypothesis 7, hbu): Nat, v=#v[0,5], i=0, x=0
theorem c113 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ExceptAt.set_of_ge 7 := fun h =>
  absurd (@h (Nat) (2) (0) _ _ (#v[0, 5]) (⟨0, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ExceptAt.set_of_ge` (hypothesis 8, h_ge): Nat, v=#v[5,3], i=0, x=0
theorem c114 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ExceptAt.set_of_ge 8 := fun h =>
  absurd (@h (Nat) (2) (0) _ _ (#v[5, 3]) (⟨0, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ParentGeChildren.set_of_ge` (hypothesis 4, inst): cyclic Ord, v=#v[0,2], i=0, x=1
theorem c115 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ParentGeChildren.set_of_ge 4 := fun h =>
  absurd (@h (Cy) (2) (1) _ (#v[0, 2]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ParentGeChildren.set_of_ge` (hypothesis 7, hbu): Nat, v=#v[0,5], i=0, x=0
theorem c116 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ParentGeChildren.set_of_ge 7 := fun h =>
  absurd (@h (Nat) (2) (0) _ _ (#v[0, 5]) (⟨0, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.ParentGeChildren.set_of_ge` (hypothesis 8, h_ge): Nat, v=#v[5,3], i=0, x=0
theorem c117 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.ParentGeChildren.set_of_ge 8 := fun h =>
  absurd (@h (Nat) (2) (0) _ _ (#v[5, 3]) (⟨0, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.TopDown.below_of_swap_pop` (hypothesis 4, hwf): Nat, a=#v[0,0,0,5,0]
theorem c118 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.TopDown.below_of_swap_pop 4 := fun h =>
  absurd (@h (Nat) (5) _ (#v[0, 0, 0, 5, 0]) (by decide)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.children_split` (hypothesis 6, hchildren_i): Nat, a=#v[0,1], lo=i=k=0
theorem c119 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.children_split 6 := fun h =>
  absurd (@h (Nat) (2) _ (#v[0, 1]) (0) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (⟨0, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.children_split` (hypothesis 7, hbelow_i): Nat, a=#v[0,0,0,1], lo=i=0, k=1
theorem c120 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.children_split 7 := fun h =>
  absurd (@h (Nat) (4) _ (#v[0, 0, 0, 1]) (0) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel) (⟨1, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.children_split` (hypothesis 8, hrange): Nat, a=#v[0,1], lo=0, i=1, k=0
theorem c121 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.children_split 8 := fun h =>
  absurd (@h (Nat) (2) _ (#v[0, 1]) (0) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (⟨0, by decide⟩) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.children_split` (hypothesis 10, a): Nat, a=#v[0,1], lo=i=1, k=0
theorem c122 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.children_split 10 := fun h =>
  absurd (@h (Nat) (2) _ (#v[0, 1]) (1) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel) (by decide +kernel) (⟨0, by decide⟩)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.TopDown.of_children_below_and_above` (hypothesis 5, hchildren_i): Nat, a=#v[0,1], i=0
theorem c123 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.TopDown.of_children_below_and_above 5 := fun h =>
  absurd (@h (Nat) (2) _ (#v[0, 1]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.TopDown.of_children_below_and_above` (hypothesis 6, hbelow_i): Nat, a=#v[0,0,0,1], i=0
theorem c124 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.TopDown.of_children_below_and_above 6 := fun h =>
  absurd (@h (Nat) (4) _ (#v[0, 0, 0, 1]) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.TopDown.of_children_below_and_above` (hypothesis 7, habove): Nat, a=#v[0,1], i=1
theorem c125 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.TopDown.of_children_below_and_above 7 := fun h =>
  absurd (@h (Nat) (2) _ (#v[0, 1]) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Below.of_children_below_and_between` (hypothesis 6, hchildren_j): Nat, a=#v[0,0,0,1], i=0, j=1
theorem c126 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Below.of_children_below_and_between 6 := fun h =>
  absurd (@h (Nat) (4) _ (#v[0, 0, 0, 1]) (⟨0, by decide⟩) (⟨1, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Below.of_children_below_and_between` (hypothesis 7, hbelow_j): Nat, a=#v[0,0,0,1], i=j=0
theorem c127 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Below.of_children_below_and_between 7 := fun h =>
  absurd (@h (Nat) (4) _ (#v[0, 0, 0, 1]) (⟨0, by decide⟩) (⟨0, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Batteries.BinaryHeap.WF.Below.of_children_below_and_between` (hypothesis 8, hbetween): Nat, a=#v[0,0,0,1], i=0, j=2
theorem c128 : ¬ drop0% _private.Batteries.Data.BinaryHeap.WF.«0».Batteries.BinaryHeap.WF.Below.of_children_below_and_between 8 := fun h =>
  absurd (@h (Nat) (4) _ (#v[0, 0, 0, 1]) (⟨0, by decide⟩) (⟨2, by decide⟩) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

