import Lean.Elab.Command
-- add the library modules your rows need here (e.g. `import Init`, `import Std.Sat.AIG.CNF`); avoid `import Lean`/`import Std` (1.5 GB)
import Init
import Batteries.Data.Array.Scan
import Batteries.Data.Array.Basic
import Batteries.Data.Char.Basic
import Batteries.Data.DList.Basic
import Batteries.Data.Fin.Fold
import Batteries.Data.Fin.Coding
import Batteries.Data.Float.Lemmas
import Batteries.Data.List.Scan
import Batteries.Data.List.Lemmas
import Batteries.Data.List.Count
import Batteries.Data.List.Perm
import Batteries.Data.Nat.Digits
import Batteries.Data.Nat.Lemmas
import Batteries.Data.String.Lemmas
import Batteries.Data.UnionFind.Lemmas
import Batteries.Data.Vector.Lemmas
import Batteries.Data.Vector.Basic

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


/-! ### part L1 -/
section
/- models -/
def BT := Nat
instance : BEq BT := ⟨fun _ _ => true⟩
instance : DecidableEq BT := inferInstanceAs (DecidableEq Nat)
instance : OfNat BT n := ⟨(n : Nat)⟩
def BF := Nat
instance : BEq BF := ⟨fun _ _ => false⟩
instance : DecidableEq BF := inferInstanceAs (DecidableEq Nat)
instance : OfNat BF n := ⟨(n : Nat)⟩

/-- left projection: associative, no identity -/
def LP := Nat
instance : Add LP := ⟨fun a _ => a⟩
instance : Mul LP := ⟨fun a _ => a⟩
instance : Zero LP := ⟨(0 : Nat)⟩
instance : One LP := ⟨(0 : Nat)⟩
instance : DecidableEq LP := inferInstanceAs (DecidableEq Nat)
instance : OfNat LP n := ⟨(n : Nat)⟩
instance : Std.Associative (α := LP) (· + ·) := ⟨fun _ _ _ => rfl⟩
instance : Std.Associative (α := LP) (· * ·) := ⟨fun _ _ _ => rfl⟩

/-- identity 0 for +, 1 for *, not associative -/
structure NA where n : Nat deriving DecidableEq
instance : OfNat NA n := ⟨⟨n⟩⟩
instance : Add NA := ⟨fun a b => if a.n = 0 then b else if b.n = 0 then a else ⟨2 * a.n + b.n⟩⟩
instance : Mul NA := ⟨fun a b => if a.n = 1 then b else if b.n = 1 then a else ⟨2 * a.n + b.n⟩⟩
instance : Zero NA := ⟨⟨0⟩⟩
instance : One NA := ⟨⟨1⟩⟩
instance : Std.LawfulIdentity (α := NA) (· + ·) 0 where
  left_id a := by show (if (0:Nat) = 0 then a else _) = a; simp
  right_id a := by
    cases a with | mk n => show (if n = 0 then (⟨0⟩ : NA) else if (0:Nat) = 0 then ⟨n⟩ else _) = ⟨n⟩; by_cases h : n = 0 <;> simp_all
instance : Std.LawfulIdentity (α := NA) (· * ·) 1 where
  left_id a := by show (if (1:Nat) = 1 then a else _) = a; simp
  right_id a := by
    cases a with | mk n => show (if n = 1 then (⟨1⟩ : NA) else if (1:Nat) = 1 then ⟨n⟩ else _) = ⟨n⟩; by_cases h : n = 1 <;> simp_all

-- `List.prod_one_cons`
theorem c1 : ¬ drop0% List.prod_one_cons 3 := fun h => absurd (h (α := LP) (l := [1])) (by decide)
-- `List.prod_concat`
theorem c2 : ¬ drop0% List.prod_concat 3 := fun h => absurd (h (α := LP) (l := []) (a := 1)) (by decide)
-- `List.prod_concat`
theorem c3 : ¬ drop0% List.prod_concat 4 := fun h => absurd (h (α := NA) (l := [2, 2]) (a := 2)) (by decide)
-- `List.sum_concat`
theorem c4 : ¬ drop0% List.sum_concat 3 := fun h => absurd (h (α := LP) (l := []) (a := 1)) (by decide)
-- `List.sum_concat`
theorem c5 : ¬ drop0% List.sum_concat 4 := fun h => absurd (h (α := NA) (l := [2, 2]) (a := 2)) (by decide)
-- `List.prod_flatten`
theorem c6 : ¬ drop0% List.prod_flatten 3 := fun h => absurd (h (α := LP) (l := [[], [1]])) (by decide)
-- `List.prod_flatten`
theorem c7 : ¬ drop0% List.prod_flatten 4 := fun h => absurd (h (α := NA) (l := [[2, 2], [2]])) (by decide)
-- `List.sum_flatten`
theorem c8 : ¬ drop0% List.sum_flatten 4 := fun h => absurd (h (α := NA) (l := [[2, 2], [2]])) (by decide)
-- `List.partialSums_cons`
theorem d0 : ¬ drop0% List.partialSums_cons 4 := fun h => absurd (h (α := NA) (a := 2) (l := [2, 2])) (by decide)
-- `List.partialSums_cons`
theorem d1 : ¬ drop0% List.partialSums_cons 5 := fun h => absurd (h (α := LP) (a := 1) (l := [])) (by decide)
-- `List.partialSums_append`
theorem d2 : ¬ drop0% List.partialSums_append 3 := fun h => absurd (h (α := NA) (l₁ := [2]) (l₂ := [2, 2])) (by decide)
-- `List.getElem_partialSums`
theorem d3 : ¬ drop0% List.getElem_partialSums 4 := fun h => absurd (h (α := NA) (l := [2, 2, 2]) (i := 3) (by decide)) (by decide)
-- `List.getElem_partialSums`
theorem d4 : ¬ drop0% List.getElem_partialSums 5 := fun h => absurd (h (α := LP) (l := [1]) (i := 1) (by decide)) (by decide)
-- `List.getElem?_partialSums`
theorem d5 : ¬ drop0% List.getElem?_partialSums 4 := fun h => absurd (h (α := NA) (l := [2, 2, 2]) (i := 3)) (by decide)
-- `List.getElem?_partialSums`
theorem d6 : ¬ drop0% List.getElem?_partialSums 5 := fun h => absurd (h (α := LP) (l := [1]) (i := 1)) (by decide)
-- `List.partialProds_cons`
theorem d7 : ¬ drop0% List.partialProds_cons 4 := fun h => absurd (h (α := NA) (a := 2) (l := [2, 2])) (by decide)
-- `List.partialProds_cons`
theorem d8 : ¬ drop0% List.partialProds_cons 5 := fun h => absurd (h (α := LP) (a := 1) (l := [])) (by decide)
-- `List.partialProds_append`
theorem d9 : ¬ drop0% List.partialProds_append 3 := fun h => absurd (h (α := NA) (l₁ := [2]) (l₂ := [2, 2])) (by decide)
-- `List.partialProds_append`
theorem d10 : ¬ drop0% List.partialProds_append 4 := fun h => absurd (h (α := LP) (l₁ := [1]) (l₂ := [2])) (by decide)
-- `List.getElem_partialProds`
theorem d11 : ¬ drop0% List.getElem_partialProds 4 := fun h => absurd (h (α := NA) (l := [2, 2, 2]) (i := 3) (by decide)) (by decide)
-- `List.getElem_partialProds`
theorem d12 : ¬ drop0% List.getElem_partialProds 5 := fun h => absurd (h (α := LP) (l := [1]) (i := 1) (by decide)) (by decide)
-- `List.getElem?_partialProds`
theorem d13 : ¬ drop0% List.getElem?_partialProds 4 := fun h => absurd (h (α := NA) (l := [2, 2, 2]) (i := 3)) (by decide)
-- `List.getElem?_partialProds`
theorem d14 : ¬ drop0% List.getElem?_partialProds 5 := fun h => absurd (h (α := LP) (l := [1]) (i := 1)) (by decide)
end


/-! ### part L2 -/
section
def BL := Nat
instance : BEq BL := ⟨fun a b => Nat.ble a b⟩
instance : DecidableEq BL := inferInstanceAs (DecidableEq Nat)
instance : OfNat BL n := ⟨(n : Nat)⟩

-- `List.fst_idxToSigmaCount`
theorem e1 : ¬ indep0% List.fst_idxToSigmaCount 2 := fun h => absurd (@ReflBEq.rfl BF _ (h (α := BF) (xs := [0]) (i := ⟨0, by decide⟩)) 0) (by decide)
-- `List.snd_idxToSigmaCount`
theorem e2 : ¬ indep0% List.snd_idxToSigmaCount 2 := fun h => absurd (@ReflBEq.rfl BF _ (h (α := BF) (xs := [0]) (i := ⟨0, by decide⟩)) 0) (by decide)
-- `List.coe_snd_idxToSigmaCount`
theorem e3 : ¬ indep0% List.coe_snd_idxToSigmaCount 2 := fun h => absurd (@ReflBEq.rfl BF _ (h (α := BF) (xs := [0]) (i := ⟨0, by decide⟩)) 0) (by decide)
-- `List.sigmaCountToIdx_idxToSigmaCount`
theorem e4 : ¬ indep0% List.sigmaCountToIdx_idxToSigmaCount 2 := fun h => absurd (@ReflBEq.rfl BF _ (h (α := BF) (xs := [0]) (i := ⟨0, by decide⟩)) 0) (by decide)
-- `List.idxToSigmaCount_sigmaCountToIdx`
theorem e5 : ¬ indep0% List.idxToSigmaCount_sigmaCountToIdx 2 := fun h => absurd (@LawfulBEq.eq_of_beq BT _ (h (α := BT) (xs := [0]) (xc := ⟨0, ⟨0, by decide⟩⟩)) 0 1 rfl) (by decide)
-- `List.surjective_sigmaCountToIdx`
theorem e6 : ¬ drop0% List.surjective_sigmaCountToIdx 2 := fun h => by
  obtain ⟨⟨x, i⟩, _⟩ := h (α := BF) (xs := [0]) ⟨0, by decide⟩
  exact absurd i.2 (by simp [List.count])
-- `List.injective_sigmaCountToIdx`
theorem e7 : ¬ drop0% List.injective_sigmaCountToIdx 2 := fun h => by
  have := @h BT _ [0, 1] ⟨0, ⟨0, by decide⟩⟩ ⟨1, ⟨0, by decide⟩⟩ (by decide)
  exact absurd (congrArg Sigma.fst this) (by decide)
-- `List.Perm.diff_left`
theorem e8 : ¬ drop0% List.Perm.diff_left 4 := fun h =>
  absurd (h (α := BL) [2, 0] (List.Perm.swap (1 : BL) 2 [])) (by decide)
-- `List.Perm.diff`
theorem e9 : ¬ drop0% List.Perm.diff 2 := fun h =>
  absurd (h (α := BL) (List.Perm.refl [2, 0]) (List.Perm.swap (1 : BL) 2 [])) (by decide)
-- `List.disjoint_take_drop`
theorem e10 : ¬ drop0% List.disjoint_take_drop 4 := fun h =>
  h (α := Nat) (l := [1, 1]) (m := 1) (n := 1) (Nat.le_refl 1) (a := 1) (by decide) (by decide)
-- `List.Nodup.perm_iff_eq_of_sublist`
theorem e11 : ¬ drop0% List.Nodup.perm_iff_eq_of_sublist 4 := fun h =>
  absurd ((h (α := Nat) (l₁ := [1, 2]) (l₂ := [2, 1]) (l := [1, 2, 1]) (by decide) (by decide)).1
    (List.Perm.swap 2 1 [])) (by decide)

-- `List.nil_diff`
theorem f1 : drop% List.nil_diff 2 := by
  intro α _ l; induction l <;> simp_all [List.diff]
-- `List.diff_append`
theorem f2 : drop% List.diff_append 2 := by
  intro α _ l₁ l₂ l₃
  induction l₂ generalizing l₁ with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append, List.diff]; split <;> simp [ih]
-- `List.diff_sublist`
theorem f3 : drop% List.diff_sublist 2 := by
  intro α _ l₁ l₂
  induction l₂ generalizing l₁ with
  | nil => exact List.Sublist.refl _
  | cons a l ih => simp only [List.diff]; split
                   · exact (ih _).trans List.erase_sublist
                   · exact ih _
-- `List.diff_subset`
theorem f4 : drop% List.diff_subset 2 := fun l₁ l₂ => (f3 l₁ l₂).subset
-- `List.Sublist.erase_diff_erase_sublist`
theorem f5 : drop% List.Sublist.erase_diff_erase_sublist 6 := by
  intro α _ _ a l₁ l₂
  by_cases h : a ∈ l₁
  · rw [(List.perm_cons_erase h).diff_left l₂, List.diff_cons]; exact List.Sublist.refl _
  · rw [List.erase_of_not_mem h, ← List.diff_erase]; exact List.erase_sublist
-- helper: membership test is invariant under permutation, for any BEq
theorem elemPerm {α} [BEq α] {a : α} {t₁ t₂ : List α} (p : t₁.Perm t₂) : t₁.elem a = t₂.elem a := by
  induction p with
  | nil => rfl
  | cons x _ ih => cases hx : a == x <;> simp [List.elem, hx, ih]
  | swap x y l => cases hx : a == x <;> cases hy : a == y <;> simp [List.elem, hx, hy]
  | trans _ _ i1 i2 => exact i1.trans i2
-- `List.Perm.inter_left`
theorem f6 : drop% List.Perm.inter_left 4 := by
  intro α t₁ t₂ _ l p
  show List.inter l t₁ = List.inter l t₂
  exact List.filter_congr fun a _ => elemPerm p
-- `List.Perm.inter`
theorem f7 : drop% List.Perm.inter 2 := by
  intro α _ l₁ l₂ t₁ t₂ p₁ p₂
  rw [← f6 l₂ p₂]
  exact p₁.filter _
-- `List.Perm.union_left`
theorem f8 : drop% List.Perm.union_left 4 := by
  intro α t₁ t₂ _ l h
  show List.union l t₁ |>.Perm (List.union l t₂)
  induction l with
  | nil => exact h
  | cons a l ih =>
    simp only [List.union, List.foldr] at ih ⊢
    simp only [List.insert, elemPerm (a := a) ih]
    split
    · exact ih
    · exact ih.cons a
end


/-! ### part S4 -/
section
open String
noncomputable instance HypCheckDec.substrValidFor (l m r : List Char) (s : Substring.Raw) :
    Decidable (Substring.Raw.ValidFor l m r s) :=
  decidable_of_iff (s.str = String.ofList (l ++ m ++ r) ∧ s.startPos = ⟨String.utf8Len l⟩ ∧
      s.stopPos = ⟨String.utf8Len l + String.utf8Len m⟩)
    ⟨fun ⟨h1, h2, h3⟩ => by cases s; cases h1; cases h2; cases h3; exact .mk,
     fun h => by cases h; exact ⟨rfl, rfl, rfl⟩⟩
/-- helper: a raw position that is no prefix length is not valid -/
theorem notValid {s : String} {p : String.Pos.Raw}
    (h : ∀ k, k ≤ s.toList.length → p.1 ≠ String.utf8Len (s.toList.take k)) : ¬ p.Valid s := by
  intro hv
  obtain ⟨cs, cs', h1, h2⟩ := hv.exists
  have e : s.toList = cs ++ cs' := by rw [← h1]; simp
  have : s.toList.take cs.length = cs := by rw [e]; simp
  exact h cs.length (by rw [e]; simp) (by rw [h2, this])
/-- helper: position 1 of the empty string is invalid -/
theorem nv1 : ¬ (⟨1⟩ : String.Pos.Raw).Valid "" := notValid (by simp)
/-- helper: the substring with start 1 of the empty string is invalid -/
theorem nsv : ¬ (⟨"", ⟨1⟩, ⟨1⟩⟩ : Substring.Raw).Valid := fun h => nv1 h.startValid
/-- helper: no substring decomposition with nonempty middle has empty underlying string -/
theorem noVF {l r : List Char} : ¬ Substring.Raw.ValidFor l ['a'] r ⟨"", ⟨0⟩, ⟨0⟩⟩ := fun h => by
  have := congrArg (·.length) (congrArg String.toList h.str); simp at this
/-- helper: a valid substring from a concrete decomposition -/
theorem vOf {l m r : List Char} {s : Substring.Raw} (h : Substring.Raw.ValidFor l m r s) : s.Valid :=
  h.valid

-- `String.Pos.Raw.Valid.intro`
theorem s1 : ¬ drop0% String.Pos.Raw.Valid.intro 2 := fun h => nv1 (h (s := "") (p := ⟨1⟩))
-- `String.valid_next`
theorem s2 : ¬ drop0% String.valid_next 2 := fun h => by
  have := h (s := String.ofList ['😀']) (p := ⟨1⟩) (by decide +kernel)
  rw [show String.Pos.Raw.next (String.ofList ['😀']) ⟨1⟩ = ⟨2⟩ by decide +kernel] at this
  exact notValid (by simp; decide) this
-- `String.valid_next`
theorem s3 : ¬ drop0% String.valid_next 3 := fun h => by
  have := h (s := "") (p := ⟨0⟩) String.Pos.Raw.valid_zero
  rw [show String.Pos.Raw.next "" ⟨0⟩ = ⟨1⟩ by decide +kernel] at this
  exact nv1 this
-- `String.Legacy.Iterator.ValidFor.valid`
theorem s4 : ¬ drop0% String.Legacy.Iterator.ValidFor.valid 3 := fun h =>
  nv1 (h (l := []) (r := []) (it := ⟨"", ⟨1⟩⟩))
-- `String.Legacy.Iterator.Valid.validFor`
theorem s5 : ¬ drop0% String.Legacy.Iterator.Valid.validFor 1 := fun h => by
  obtain ⟨l, r, h⟩ := h (it := ⟨"", ⟨1⟩⟩)
  exact nv1 h.valid
-- `String.Legacy.Iterator.Valid.next`
theorem s6 : ¬ drop0% String.Legacy.Iterator.Valid.next 1 := fun h => by
  have := h (it := ⟨String.ofList ['😀'], ⟨1⟩⟩) (by decide +kernel)
  rw [show String.Legacy.Iterator.next ⟨String.ofList ['😀'], ⟨1⟩⟩ = ⟨String.ofList ['😀'], ⟨2⟩⟩ by decide +kernel] at this
  exact notValid (by simp; decide) this
-- `String.Legacy.Iterator.Valid.next`
theorem s7 : ¬ drop0% String.Legacy.Iterator.Valid.next 2 := fun h => by
  have := h (it := ⟨"", ⟨0⟩⟩) String.Pos.Raw.valid_zero
  rw [show String.Legacy.Iterator.next ⟨"", ⟨0⟩⟩ = ⟨"", ⟨1⟩⟩ by decide +kernel] at this
  exact nv1 this
-- `String.Legacy.Iterator.Valid.setCurr`
theorem s8 : ¬ drop0% String.Legacy.Iterator.Valid.setCurr 2 := fun h => by
  have := h (it := ⟨"", ⟨1⟩⟩) (c := 'a')
  rw [show String.Legacy.Iterator.setCurr ⟨"", ⟨1⟩⟩ 'a' = ⟨"", ⟨1⟩⟩ by decide +kernel] at this
  exact nv1 this
-- `String.Legacy.Iterator.Valid.prevn`
theorem s9 : ¬ drop0% String.Legacy.Iterator.Valid.prevn 1 := fun h =>
  nv1 (h (it := ⟨"", ⟨1⟩⟩) 0)
-- `Substring.Raw.Valid.startValid`
theorem t1 : ¬ drop0% Substring.Raw.Valid.startValid 1 := fun h => nv1 (h (s := ⟨"", ⟨1⟩, ⟨1⟩⟩))
-- `Substring.Raw.Valid.stopValid`
theorem t2 : ¬ drop0% Substring.Raw.Valid.stopValid 1 := fun h => nv1 (h (s := ⟨"", ⟨1⟩, ⟨1⟩⟩))
-- `Substring.Raw.ValidFor.valid`
theorem t3 : ¬ drop0% Substring.Raw.ValidFor.valid 4 := fun h =>
  nsv (h (l := []) (m := []) (r := []) (s := ⟨"", ⟨1⟩, ⟨1⟩⟩))
-- `Substring.Raw.Valid.valid`
theorem t4 : ¬ drop0% Substring.Raw.Valid.valid 4 := fun h =>
  nsv (h (l := []) (m := []) (r := []) (s := ⟨"", ⟨1⟩, ⟨1⟩⟩))
-- `Substring.Raw.Valid.validFor`
theorem t5 : ¬ drop0% Substring.Raw.Valid.validFor 1 := fun h => by
  obtain ⟨l, m, r, h⟩ := h (s := ⟨"", ⟨1⟩, ⟨1⟩⟩)
  exact nsv h.valid
-- `Substring.Raw.ValidFor.prevn`
theorem t6 : ¬ drop0% Substring.Raw.ValidFor.prevn 5 := fun h =>
  absurd (h (l := []) (r := []) (m₁ := ['é']) (m₂ := []) (s := ⟨"", ⟨0⟩, ⟨0⟩⟩) 1) (by decide +kernel)
-- `Substring.Raw.Valid.prevn`
theorem t7 : ¬ drop0% Substring.Raw.Valid.prevn 4 := fun h =>
  absurd (h (m₁ := ['é']) (m₂ := []) (s := ⟨"", ⟨0⟩, ⟨0⟩⟩) Substring.Raw.Valid_default 1) (by decide +kernel)
-- `Substring.Raw.ValidFor.extract'`
theorem t8 : ¬ drop0% Substring.Raw.ValidFor.extract' 8 := fun h => by
  obtain ⟨l', r', h⟩ := h (l := []) (r := []) (ml := []) (mm := ['a']) (mr := []) (s := ⟨"", ⟨0⟩, ⟨0⟩⟩)
    (b := ⟨0⟩) (e := ⟨1⟩) (by decide +kernel)
  rw [show (⟨"", ⟨0⟩, ⟨0⟩⟩ : Substring.Raw).extract ⟨0⟩ ⟨1⟩ = ⟨"", ⟨0⟩, ⟨0⟩⟩ by rfl] at h
  exact noVF h
-- `Substring.Raw.ValidFor.extract'`
theorem t9 : ¬ drop0% Substring.Raw.ValidFor.extract' 9 := fun h => by
  obtain ⟨l', r', h⟩ := h (l := []) (r := []) (ml := []) (mm := ['a']) (mr := []) (s := ⟨"a", ⟨0⟩, ⟨1⟩⟩)
    (b := ⟨1⟩) (e := ⟨0⟩) (by decide +kernel)
  rw [show (⟨"a", ⟨0⟩, ⟨1⟩⟩ : Substring.Raw).extract ⟨1⟩ ⟨0⟩ = ⟨"", ⟨0⟩, ⟨0⟩⟩ by rfl] at h
  exact noVF h
-- `Substring.Raw.ValidFor.extract`
theorem t10 : ¬ drop0% Substring.Raw.ValidFor.extract 9 := fun h => by
  obtain ⟨l', r', h⟩ := h (l := []) (r := []) (m := ['a']) (ml := []) (mm := ['a']) (mr := [])
    (s := ⟨"", ⟨0⟩, ⟨0⟩⟩) (b := ⟨0⟩) (e := ⟨1⟩) (by decide +kernel)
  rw [show (⟨"", ⟨0⟩, ⟨0⟩⟩ : Substring.Raw).extract ⟨0⟩ ⟨1⟩ = ⟨"", ⟨0⟩, ⟨0⟩⟩ by rfl] at h
  exact noVF h
-- `Substring.Raw.ValidFor.extract`
theorem t11 : ¬ drop0% Substring.Raw.ValidFor.extract 10 := fun h => by
  obtain ⟨l', r', h⟩ := h (l := []) (r := []) (m := ['a']) (ml := []) (mm := ['a']) (mr := [])
    (s := ⟨"a", ⟨0⟩, ⟨1⟩⟩) (b := ⟨1⟩) (e := ⟨0⟩) (by decide +kernel)
  rw [show (⟨"a", ⟨0⟩, ⟨1⟩⟩ : Substring.Raw).extract ⟨1⟩ ⟨0⟩ = ⟨"", ⟨0⟩, ⟨0⟩⟩ by rfl] at h
  exact noVF h
-- `String.Legacy.Iterator.Valid.prev`
theorem s10 : ¬ drop0% String.Legacy.Iterator.Valid.prev 1 := fun h => by
  have := h (it := ⟨"", ⟨2⟩⟩)
  rw [show String.Legacy.Iterator.prev ⟨"", ⟨2⟩⟩ = ⟨"", ⟨1⟩⟩ by decide +kernel] at this
  exact nv1 this
-- `Substring.Raw.Valid.drop`
theorem t12 : ¬ drop0% Substring.Raw.Valid.drop 1 := fun h => by
  have := h (s := ⟨"", ⟨1⟩, ⟨1⟩⟩) 0
  rw [show Substring.Raw.drop ⟨"", ⟨1⟩, ⟨1⟩⟩ 0 = ⟨"", ⟨1⟩, ⟨1⟩⟩ by rfl] at this
  exact nsv this
-- `Substring.Raw.Valid.take`
theorem t13 : ¬ drop0% Substring.Raw.Valid.take 1 := fun h => by
  have := h (s := ⟨"", ⟨1⟩, ⟨1⟩⟩) 0
  rw [show Substring.Raw.take ⟨"", ⟨1⟩, ⟨1⟩⟩ 0 = ⟨"", ⟨1⟩, ⟨1⟩⟩ by rfl] at this
  exact nsv this
-- `Substring.Raw.Valid.takeWhile`
theorem t14 : ¬ drop0% Substring.Raw.Valid.takeWhile 2 := fun h => by
  have := h (fun _ => true) (s := ⟨"", ⟨1⟩, ⟨1⟩⟩)
  rw [show Substring.Raw.takeWhile ⟨"", ⟨1⟩, ⟨1⟩⟩ (fun _ => true) = ⟨"", ⟨1⟩, ⟨1⟩⟩ by
    simp only [Substring.Raw.takeWhile]; rw [Substring.Raw.takeWhileAux]; simp] at this
  exact nsv this
-- `Substring.Raw.Valid.dropWhile`
theorem t15 : ¬ drop0% Substring.Raw.Valid.dropWhile 2 := fun h => by
  have := h (fun _ => true) (s := ⟨"", ⟨1⟩, ⟨1⟩⟩)
  rw [show Substring.Raw.dropWhile ⟨"", ⟨1⟩, ⟨1⟩⟩ (fun _ => true) = ⟨"", ⟨1⟩, ⟨1⟩⟩ by
    simp only [Substring.Raw.dropWhile]; rw [Substring.Raw.takeWhileAux]; simp] at this
  exact nsv this
-- `Substring.Raw.Valid.data_drop`
theorem t16 : ¬ drop0% Substring.Raw.Valid.data_drop 1 := fun h =>
  absurd (h (s := ⟨"éa", ⟨0⟩, ⟨1⟩⟩) 1) (by decide +kernel)
-- `Substring.Raw.Valid.data_takeWhile`
theorem t17 : ¬ drop0% Substring.Raw.Valid.data_takeWhile 2 := fun h =>
  absurd (h (fun _ => true) (s := ⟨"éa", ⟨0⟩, ⟨1⟩⟩)) (by decide +kernel)
-- `Substring.Raw.Valid.data_dropWhile`
theorem t18 : ¬ drop0% Substring.Raw.Valid.data_dropWhile 2 := fun h =>
  absurd (h (fun c => c == 'é') (s := ⟨"éa", ⟨0⟩, ⟨1⟩⟩)) (by decide +kernel)
/-- helper: the substring "éa" from 0 to 2 is valid -/
theorem vea : (⟨"éa", ⟨0⟩, ⟨2⟩⟩ : Substring.Raw).Valid :=
  vOf (l := []) (m := ['é']) (r := ['a']) (by decide +kernel)
-- `Substring.Raw.Valid.extract`
theorem t19 : ¬ drop0% Substring.Raw.Valid.extract 3 := fun h => by
  have := h (s := ⟨"éa", ⟨0⟩, ⟨1⟩⟩) (b := ⟨0⟩) (e := ⟨2⟩)
    (by rw [show (⟨"éa", ⟨0⟩, ⟨1⟩⟩ : Substring.Raw).toString = "éa" by decide +kernel]; exact vea)
  rw [show (⟨"éa", ⟨0⟩, ⟨1⟩⟩ : Substring.Raw).extract ⟨0⟩ ⟨2⟩ = ⟨"éa", ⟨0⟩, ⟨1⟩⟩ by rfl] at this
  exact notValid (by simp; decide +kernel) this.stopValid
-- `Substring.Raw.Valid.extract`
theorem t20 : ¬ drop0% Substring.Raw.Valid.extract 4 := fun h => by
  have := h (s := ⟨"é", ⟨0⟩, ⟨2⟩⟩) (b := ⟨1⟩) (e := ⟨2⟩)
    (vOf (l := []) (m := ['é']) (r := []) (by decide +kernel))
  rw [show (⟨"é", ⟨0⟩, ⟨2⟩⟩ : Substring.Raw).extract ⟨1⟩ ⟨2⟩ = ⟨"é", ⟨1⟩, ⟨2⟩⟩ by rfl] at this
  exact notValid (by simp; decide +kernel) this.startValid
-- `Substring.Raw.Valid.toString_extract`
theorem t21 : ¬ drop0% Substring.Raw.Valid.toString_extract 3 := fun h => by
  have := h (s := ⟨"éa", ⟨0⟩, ⟨1⟩⟩) (b := ⟨0⟩) (e := ⟨2⟩)
    (by rw [show (⟨"éa", ⟨0⟩, ⟨1⟩⟩ : Substring.Raw).toString = "éa" by decide +kernel]; exact vea)
  exact absurd this (by decide +kernel)
-- `Substring.Raw.Valid.toString_extract`
theorem t22 : ¬ drop0% Substring.Raw.Valid.toString_extract 4 := fun h =>
  absurd (h (s := ⟨"éa", ⟨0⟩, ⟨2⟩⟩) (b := ⟨0⟩) (e := ⟨1⟩) vea) (by decide +kernel)

-- `Substring.Raw.Valid.data_take`
theorem t23 : ¬ drop0% Substring.Raw.Valid.data_take 1 := fun h =>
  absurd (h (s := ⟨"ab", ⟨1⟩, ⟨0⟩⟩) 1) (by decide +kernel)
-- `String.Legacy.Iterator.Valid.remainingBytes_le`
theorem r1 : drop% String.Legacy.Iterator.Valid.remainingBytes_le 1 := by
  intro ⟨s, i⟩; exact Nat.sub_le _ _
-- `String.Legacy.Iterator.ValidFor.prevn`
theorem r2 : drop% String.Legacy.Iterator.ValidFor.prevn 5 := by
  intro l r it h n
  induction n generalizing l r it with
  | zero => simpa [String.Legacy.Iterator.prevn] using h
  | succ n ih =>
    simp only [String.Legacy.Iterator.prevn]
    match l, h with
    | [], h => simpa using ih h.prev_nil
    | a :: l, h => simpa using ih h.prev
end


/-! ### part S5 -/
section
open String

/-- helper: what extract.go₂ returns is a prefix whose inner positions miss the stop -/
theorem hcG2 : ∀ (cs : List Char) (i e : String.Pos.Raw), ∃ t, cs = String.Pos.Raw.extract.go₂ cs i e ++ t ∧
    ∀ m₁ c m₂, String.Pos.Raw.extract.go₂ cs i e = m₁ ++ c :: m₂ → i.byteIdx + utf8Len m₁ ≠ e.byteIdx
  | [], i, e => ⟨[], by simp [String.Pos.Raw.extract.go₂]⟩
  | c :: cs, i, e => by
    by_cases h : i = e
    · exact ⟨c :: cs, by simp [String.Pos.Raw.extract.go₂, h]⟩
    · obtain ⟨t, ht, hm⟩ := hcG2 cs (i + c) e
      refine ⟨t, by simp [String.Pos.Raw.extract.go₂, h]; exact ht, ?_⟩
      intro m₁ d m₂ hm₁
      simp only [String.Pos.Raw.extract.go₂, h, ite_false] at hm₁
      match m₁, hm₁ with
      | [], hm₁ =>
        intro he; exact h (String.Pos.Raw.ext (by simpa using he))
      | d' :: m₁', hm₁ =>
        simp only [List.cons_append, List.cons.injEq] at hm₁
        have := hm m₁' d m₂ hm₁.2
        simp only [utf8Len_cons, String.Pos.Raw.byteIdx_add_char] at this ⊢
        rw [← hm₁.1]; omega

/-- helper: extract.go₁ finds its start at a prefix length -/
theorem hcG1 : ∀ (cs : List Char) (i b e : String.Pos.Raw), String.Pos.Raw.extract.go₁ cs i b e ≠ [] →
    ∃ l t, cs = l ++ String.Pos.Raw.extract.go₁ cs i b e ++ t ∧ b.byteIdx = i.byteIdx + utf8Len l ∧
    ∀ m₁ c m₂, String.Pos.Raw.extract.go₁ cs i b e = m₁ ++ c :: m₂ → b.byteIdx + utf8Len m₁ ≠ e.byteIdx
  | [], i, b, e, hne => by simp [String.Pos.Raw.extract.go₁] at hne
  | c :: cs, i, b, e, hne => by
    by_cases h : i = b
    · subst h
      obtain ⟨t, ht, hm⟩ := hcG2 (c :: cs) i e
      simp only [String.Pos.Raw.extract.go₁, ite_true]
      exact ⟨[], t, by simpa using ht, by simp, hm⟩
    · simp only [String.Pos.Raw.extract.go₁, h, ite_false] at hne ⊢
      obtain ⟨l, t, h1, h2, h3⟩ := hcG1 cs (i + c) b e hne
      refine ⟨c :: l, t, by simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h1 ⊢; exact h1, ?_, h3⟩
      simp only [utf8Len_cons, String.Pos.Raw.byteIdx_add_char] at h2 ⊢; omega

/-- helper: a substring with nonempty toString sits at a prefix of its string -/
theorem hcK (s : Substring.Raw) (hne : s.toString.toList ≠ []) :
    ∃ l t, s.str.toList = l ++ s.toString.toList ++ t ∧ s.startPos.byteIdx = utf8Len l ∧
    ∀ m₁ c m₂, s.toString.toList = m₁ ++ c :: m₂ → s.startPos.byteIdx + utf8Len m₁ ≠ s.stopPos.byteIdx := by
  obtain ⟨str, b, e⟩ := s
  simp only [Substring.Raw.toString, String.Pos.Raw.extract] at hne ⊢
  split at hne
  · simp at hne
  · rename_i hbe
    simp only [hbe, ite_false, String.toList_ofList] at hne ⊢
    obtain ⟨l, t, h1, h2, h3⟩ := hcG1 str.toList 0 b e hne
    exact ⟨l, t, h1, by simpa using h2, h3⟩

/-- helper: the canonical valid substring with the same string and start -/
theorem hcV (s : Substring.Raw) (hne : s.toString.toList ≠ []) :
    ∃ l t, Substring.Raw.ValidFor l s.toString.toList t
      ⟨s.str, s.startPos, ⟨s.startPos.byteIdx + utf8Len s.toString.toList⟩⟩ ∧
    ∀ m₁ c m₂, s.toString.toList = m₁ ++ c :: m₂ → s.startPos.byteIdx + utf8Len m₁ ≠ s.stopPos.byteIdx := by
  obtain ⟨l, t, h1, h2, h3⟩ := hcK s hne
  exact ⟨l, t, .of_eq _ h1 h2 (by simp [h2]), h3⟩

-- `Substring.Raw.Valid.get`
theorem u1 : drop% Substring.Raw.Valid.get 4 := by
  intro m₁ c m₂ s e
  obtain ⟨l, t, hv, -⟩ := hcV s (by simp [e])
  rw [e] at hv
  obtain ⟨str, b, st⟩ := s
  exact hv.get
-- `Substring.Raw.Valid.front`
theorem u2 : drop% Substring.Raw.Valid.front 3 := by
  intro c m s e
  exact u1 (m₁ := []) e
-- `Substring.Raw.Valid.prev`
theorem u3 : drop% Substring.Raw.Valid.prev 4 := by
  intro m₁ c m₂ s e
  obtain ⟨l, t, hv, -⟩ := hcV s (by simp [e])
  rw [e] at hv
  obtain ⟨str, b, st⟩ := s
  exact hv.prev
-- `Substring.Raw.Valid.next`
theorem u4 : drop% Substring.Raw.Valid.next 4 := by
  intro m₁ c m₂ s e
  obtain ⟨l, t, hv, hne⟩ := hcV s (by simp [e])
  have hne := hne m₁ c m₂ e
  rw [e] at hv
  obtain ⟨str, b, st⟩ := s
  have := hv.next
  simp only [Substring.Raw.next] at this ⊢
  have h1 : ¬ (⟨utf8Len m₁⟩ : String.Pos.Raw).offsetBy b = st := by
    intro h; apply hne; rw [← h]; simp [String.Pos.Raw.offsetBy]
  have h2 : ¬ (⟨utf8Len m₁⟩ : String.Pos.Raw).offsetBy b = ⟨b.byteIdx + utf8Len (m₁ ++ c :: m₂)⟩ := by
    intro h; have := congrArg String.Pos.Raw.byteIdx h
    simp [String.Pos.Raw.offsetBy] at this; have := c.utf8Size_pos; omega
  rw [if_neg h2] at this; rw [if_neg h1]; exact this
-- `Substring.Raw.Valid.prevn`
theorem u5 : drop% Substring.Raw.Valid.prevn 3 := by
  intro m₂ m₁ s e n
  by_cases hne : s.toString.toList = []
  · rw [hne] at e
    obtain ⟨h1, -⟩ : m₁.reverse = [] ∧ m₂ = [] := List.append_eq_nil_iff.1 e.symm
    obtain rfl : m₁ = [] := List.reverse_eq_nil_iff.1 h1
    obtain ⟨str, b, st⟩ := s
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Substring.Raw.prevn] at ih ⊢
      rw [show (⟨str, b, st⟩ : Substring.Raw).prev ⟨utf8Len []⟩ = ⟨utf8Len []⟩ by
        simp [Substring.Raw.prev, String.Pos.Raw.offsetBy]]
      simp
  · obtain ⟨l, t, hv, -⟩ := hcV s hne
    rw [e] at hv
    obtain ⟨str, b, st⟩ := s
    have key : ∀ n p, (⟨str, b, st⟩ : Substring.Raw).prevn n p =
        (⟨str, b, ⟨b.byteIdx + utf8Len (m₁.reverse ++ m₂)⟩⟩ : Substring.Raw).prevn n p := by
      intro n; induction n with
      | zero => intro p; rfl
      | succ n ih => intro p; exact ih _
    rw [key]; exact hv.prevn n
end


/-! ### part U1 -/
section
open Batteries
/-- three singleton classes -/
def hcP3 : UnionFind := UnionFind.empty.push.push.push
/-- node 0 linked below node 1 (rank 1), node 2 alone -/
def hcL3 : UnionFind := hcP3.link ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩ (by decide +kernel)
/-- helper: a three-node union-find from a parent/rank table with all ranks below parents -/
def hcMk (a : Array UFNode) (h3 : a.size = 3)
    (hp : ∀ i, i < 3 → UnionFind.parentD a i < 3)
    (hr : ∀ i, i < 3 → UnionFind.parentD a i ≠ i → UnionFind.rankD a i < UnionFind.rankD a (UnionFind.parentD a i)) :
    UnionFind where
  arr := a
  parentD_lt {i} h := h3 ▸ hp i (h3 ▸ h)
  rankD_lt {i} h := by
    by_cases hi : i < 3
    · exact hr i hi h
    · exact absurd (by simp [UnionFind.parentD, h3, hi]) h
/-- chain 2 → 0 → 1 -/
def hcM1 : UnionFind := hcMk #[{ parent := 1, rank := 1 }, { parent := 1, rank := 2 }, { parent := 0, rank := 0 }]
  rfl (by decide) (by decide)
/-- 0 → 2, 1 alone -/
def hcM2 : UnionFind := hcMk #[{ parent := 2, rank := 0 }, { parent := 1, rank := 1 }, { parent := 2, rank := 1 }]
  rfl (by decide) (by decide)

-- `Batteries.UnionFind.setParentBump_rankD_lt`
theorem v1 : ¬ drop0% Batteries.UnionFind.setParentBump_rankD_lt 4 := fun h => by
  have := @h #[{ parent := 1, rank := 0 }, { parent := 2, rank := 1 }, { parent := 2, rank := 1 }]
    #[{ parent := 0, rank := 0 }, { parent := 2, rank := 0 }, { parent := 2, rank := 1 }] ⟨0, by decide⟩ ⟨1, by decide⟩
    (by decide) 1 (by decide +kernel) (by decide +kernel)
    (fun {j} => match j with
      | 0 => by decide +kernel | 1 => by decide +kernel | 2 => by decide +kernel
      | j+3 => by simp [UnionFind.rankD])
  exact absurd (this (by decide +kernel)) (by decide +kernel)
-- `Batteries.UnionFind.setParentBump_rankD_lt`
theorem v2 : ¬ drop0% Batteries.UnionFind.setParentBump_rankD_lt 5 := fun h => by
  have := @h #[{ parent := 1, rank := 1 }, { parent := 1, rank := 0 }]
    #[{ parent := 0, rank := 1 }, { parent := 1, rank := 0 }] ⟨0, by decide⟩ ⟨1, by decide⟩
    (by decide) 0 (by decide +kernel) (by decide +kernel)
    (fun {j} => match j with
      | 0 => by decide +kernel | 1 => by decide +kernel
      | j+2 => by simp [UnionFind.rankD])
  exact absurd (this (by decide +kernel)) (by decide +kernel)
-- `Batteries.UnionFind.setParentBump_rankD_lt`
theorem v3 : ¬ drop0% Batteries.UnionFind.setParentBump_rankD_lt 7 := fun h => by
  have := @h #[{ parent := 0, rank := 0 }, { parent := 0, rank := 1 }]
    #[{ parent := 0, rank := 0 }, { parent := 0, rank := 1 }] ⟨0, by decide⟩ ⟨1, by decide⟩
    (by decide) (by decide) 1 (by decide +kernel)
    (fun {j} => by simp)
  exact absurd (this (by decide +kernel)) (by decide +kernel)
-- `Batteries.UnionFind.setParentBump_rankD_lt`
theorem v4 : ¬ drop0% Batteries.UnionFind.setParentBump_rankD_lt 8 := fun h => by
  have := @h #[{ parent := 1, rank := 1 }, { parent := 1, rank := 0 }]
    #[{ parent := 0, rank := 0 }, { parent := 1, rank := 0 }] ⟨0, by decide⟩ ⟨0, by decide⟩
    (by decide) (by decide) 0 (by decide +kernel)
    (fun {j} => match j with
      | 0 => by decide +kernel | 1 => by decide +kernel
      | j+2 => by simp [UnionFind.rankD])
  exact absurd (this (by decide +kernel)) (by decide +kernel)
-- `Batteries.UnionFind.setParentBump_rankD_lt`
theorem v5 : ¬ drop0% Batteries.UnionFind.setParentBump_rankD_lt 9 := fun h => by
  have := @h #[{ parent := 0, rank := 0 }, { parent := 0, rank := 1 }]
    #[{ parent := 0, rank := 1 }, { parent := 0, rank := 0 }] ⟨0, by decide⟩ ⟨0, by decide⟩
    (by decide) (by decide) 1 (by decide +kernel) (by decide +kernel)
  exact absurd (this (by decide +kernel)) (by decide +kernel)
-- `Batteries.UnionFind.setParentBump_rankD_lt`
theorem v6 : ¬ drop0% Batteries.UnionFind.setParentBump_rankD_lt 10 := fun h => by
  have := @h #[{ parent := 0, rank := 0 }, { parent := 0, rank := 1 }]
    #[{ parent := 0, rank := 0 }, { parent := 0, rank := 1 }] ⟨0, by decide⟩ ⟨1, by decide⟩
    (by decide) (by decide) 2 (by decide +kernel) (by decide +kernel) (fun {j} => by simp)
  exact absurd this (by decide +kernel)
-- `Batteries.UnionFind.setParent_rankD_lt`
theorem v7 : ¬ drop0% Batteries.UnionFind.setParent_rankD_lt 3 := fun h =>
  absurd (@h #[{ parent := 0, rank := 1 }, { parent := 0, rank := 0 }] ⟨0, by decide⟩ ⟨1, by decide⟩ 0
    (by decide +kernel) (by decide +kernel)) (by decide +kernel)
-- `Batteries.UnionFind.setParent_rankD_lt`
theorem v8 : ¬ drop0% Batteries.UnionFind.setParent_rankD_lt 5 := fun h =>
  absurd (@h #[{ parent := 0, rank := 0 }, { parent := 0, rank := 1 }] ⟨0, by decide⟩ ⟨1, by decide⟩
    (by decide) 1 (by decide +kernel)) (by decide +kernel)
-- `Batteries.UnionFind.arr_link`
theorem v9 : ¬ indep0% Batteries.UnionFind.arr_link 3 := fun h =>
  absurd (h (self := hcL3) (x := ⟨0, by decide +kernel⟩) (y := ⟨0, by decide +kernel⟩)) (by decide +kernel)
-- `Batteries.UnionFind.parent_link`
theorem v10 : ¬ indep0% Batteries.UnionFind.parent_link 3 := fun h =>
  absurd (h (i := 0) (self := hcL3) (x := ⟨0, by decide +kernel⟩) (y := ⟨0, by decide +kernel⟩)) (by decide +kernel)
-- `Batteries.UnionFind.root_link`
theorem v11 : ¬ indep0% Batteries.UnionFind.root_link 4 := fun h =>
  absurd (h (self := hcL3) (x := ⟨1, by decide +kernel⟩) (y := ⟨0, by decide +kernel⟩) (by decide +kernel))
    (by decide +kernel)
-- `Batteries.UnionFind.equiv_link`
theorem v12 : ¬ indep0% Batteries.UnionFind.equiv_link 6 := fun h =>
  absurd (h (a := 0) (b := 0) (self := hcL3) (x := ⟨1, by decide +kernel⟩) (y := ⟨0, by decide +kernel⟩)
    (by decide +kernel)) (by decide +kernel)
-- `Batteries.UnionFind.root_link`
theorem v13 : ¬ drop0% Batteries.UnionFind.root_link 3 := fun h => by
  obtain ⟨r, -, hr⟩ := h (self := hcL3) (x := ⟨0, by decide +kernel⟩) (y := ⟨2, by decide +kernel⟩)
    (by decide +kernel)
  have := hr 0
  rw [if_neg (by decide +kernel)] at this
  exact absurd this (by decide +kernel)
-- `Batteries.UnionFind.equiv_link`
theorem v14 : ¬ drop0% Batteries.UnionFind.equiv_link 5 := fun h => by
  have := h (a := 1) (b := 2) (self := hcL3) (x := ⟨0, by decide +kernel⟩) (y := ⟨2, by decide +kernel⟩)
    (by decide +kernel)
  simp only [UnionFind.Equiv] at this
  exact absurd this (by decide +kernel)
-- `Batteries.UnionFind.root_link.go`
theorem v15 : ¬ drop0% _private.Batteries.Data.UnionFind.Lemmas.«0».Batteries.UnionFind.root_link.go 3 := fun h =>
  absurd (h (self := hcL3) (x := ⟨0, by decide +kernel⟩) (y := ⟨2, by decide +kernel⟩) (by decide +kernel)
    (m := hcM1) (fun i => by
      match i with
      | 0 | 1 | 2 => decide +kernel
      | i+3 =>
        have h1 : ¬ (i + 3 < 3) := by omega
        simp [hcM1, hcMk, hcL3, hcP3, UnionFind.parent, UnionFind.parentD, UnionFind.link, UnionFind.linkAux, h1, List.size_toArray]) 2)
    (by decide +kernel)
-- `Batteries.UnionFind.root_link.go`
theorem v16 : ¬ drop0% _private.Batteries.Data.UnionFind.Lemmas.«0».Batteries.UnionFind.root_link.go 4 := fun h =>
  absurd (h (self := hcL3) (x := ⟨2, by decide +kernel⟩) (y := ⟨0, by decide +kernel⟩) (by decide +kernel)
    (m := hcM2) (fun i => by
      match i with
      | 0 | 1 | 2 => decide +kernel
      | i+3 =>
        have h1 : ¬ (i + 3 < 3) := by omega
        simp [hcM2, hcMk, hcL3, hcP3, UnionFind.parent, UnionFind.parentD, UnionFind.link, UnionFind.linkAux, h1, List.size_toArray]) 0)
    (by decide +kernel)
end


/-! ### part F1 -/
section
/-- counter monad whose bind keeps the left count (not lawful) -/
def KL (α : Type) := Nat × α
instance : Monad KL where
  pure a := (0, a)
  bind x g := (x.1, (g x.2).2)
/-- equality setoid on Fin 2 -/
def hcEqS : Setoid (Fin 2) := ⟨(· = ·), ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
instance : DecidableRel hcEqS.r := fun a b => decEq a b

-- `Fin.encodeSubtype_zero_pos`
theorem w1 : ¬ indep0% Fin.encodeSubtype_zero_pos 3 := fun h => h (n := 0) (P := fun _ => False)
-- `Fin.encodeSubtype_succ_pos`
theorem w2 : ¬ indep0% Fin.encodeSubtype_succ_pos 3 := fun h =>
  absurd (h (n := 1) (P := fun j => j = 1) (i := 0) rfl) (by decide)
-- `Fin.encodeSubtype_succ_pos`
theorem w3 : ¬ indep0% Fin.encodeSubtype_succ_pos 5 := fun h =>
  absurd (h (n := 1) (P := fun j => j = 0) rfl (i := 0)) (by decide)
-- `Fin.encodeSubtype_succ_neg`
theorem w4 : ¬ indep0% Fin.encodeSubtype_succ_neg 3 := fun h =>
  h (n := 1) (P := fun _ => True) (i := 0) trivial trivial
-- `Fin.encodeSubtype_succ_neg`
theorem w5 : ¬ indep0% Fin.encodeSubtype_succ_neg 5 := fun h =>
  h (n := 1) (P := fun _ => False) id (i := 0)
-- `Fin.getRepr_eq_getRepr_of_equiv`
theorem w6 : ¬ drop0% Fin.getRepr_eq_getRepr_of_equiv 5 := fun h => by
  have e := h hcEqS (x := 0) (y := 1)
  have h0 : (0 : Fin 2) = Fin.getRepr hcEqS 0 := Fin.equiv_getRepr hcEqS 0
  have h1 : (1 : Fin 2) = Fin.getRepr hcEqS 1 := Fin.equiv_getRepr hcEqS 1
  exact absurd (h0.trans (e.trans h1.symm)) (by decide)
-- `Fin.dfoldrM_loop_succ`
theorem w7 : ¬ indep0% Fin.dfoldrM_loop_succ 4 := fun h =>
  absurd (h (m := Id) (n := 0) (α := fun _ => Nat) (i := 0) (f := fun _ x => pure x)) (by decide)
-- `Fin.dfoldrM_loop`
theorem w8 : ¬ indep0% Fin.dfoldrM_loop 4 := fun h =>
  absurd (h (m := Id) (n := 0) (α := fun _ => Nat) (i := 1) (f := fun _ x => pure x)) (by decide)
-- `Fin.dfoldlM_loop_lt`
theorem w9 : ¬ indep0% Fin.dfoldlM_loop_lt 6 := fun h =>
  absurd (h (m := Id) (n := 0) (α := fun _ => Nat) (i := 0) (f := fun _ x => pure x)) (by decide)
-- `Fin.dfoldlM_loop`
theorem w10 : ¬ indep0% Fin.dfoldlM_loop 6 := fun h =>
  absurd (h (m := Id) (n := 0) (α := fun _ => Nat) (i := 1) (f := fun _ x => pure x)) (by decide)
-- `Fin.dfoldrM_loop`
theorem w11 : ¬ drop0% Fin.dfoldrM_loop 6 := fun h =>
  absurd (congrArg Prod.fst (h (m := KL) (n := 0) (α := fun _ => Nat) (i := 0) (h := by decide)
    (f := fun _ x => ((5 : Nat), x)) 0)) (by decide)
-- `Fin.dfoldrM_succ`
theorem w12 : ¬ drop0% Fin.dfoldrM_succ 4 := fun h =>
  absurd (congrArg Prod.fst (h (m := KL) (n := 0) (α := fun _ => Nat)
    (f := fun _ x => ((5 : Nat), x)) 0)) (by decide)
-- `Fin.dfoldrM_eq_foldrM`
theorem w13 : drop% Fin.dfoldrM_eq_foldrM 4 := by
  intros
  rename_i m n α _ f x
  have key : ∀ i (h : i < n + 1) y, Fin.dfoldrM.loop n (fun _ => α) f i h y =
      (priv% _private.Init.Data.Fin.Fold.«0».Fin.foldrM.loop) n f ⟨i, Nat.le_of_lt_succ h⟩ y := by
    intro i; induction i with
    | zero => intro h y; exact ((priv% _private.Init.Data.Fin.Fold.«0».Fin.foldrM_loop_zero) f y).symm
    | succ i ih =>
      intro h y
      rw [(priv% _private.Init.Data.Fin.Fold.«0».Fin.foldrM_loop_succ) f y (Nat.lt_of_succ_lt_succ h)]
      simp only [Fin.dfoldrM.loop]; congr; funext z; exact ih _ z
  exact key n _ x
end


/-! ### part M1 -/
section
/-- drop1% T i: drop% T i with all universe parameters of `T` set to `1` (refutations needing `Type`). -/
elab "drop1% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.one
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body
-- `Char.toNat_ofNatAux`
theorem x1 : ¬ indep0% Char.toNat_ofNatAux 1 := fun h => absurd (h (n := 0xD800)) (by decide)
-- `Char.val_ofNat`
theorem x2 : ¬ drop0% Char.val_ofNat 1 := fun h => absurd (h (n := 0xD800)) (by decide)
-- `Char.of_all_eq_true_aux`
theorem x3 : ¬ indep0% _private.Batteries.Data.Char.Basic.«0».Char.of_all_eq_true_aux 3 := fun h =>
  absurd (h (p := fun _ => true) (Char.all_eq_true_iff_forall_eq_true.2 fun _ => rfl) 0xD800) (by decide)
-- `Char.of_any_eq_false_aux`
theorem x4 : ¬ indep0% _private.Batteries.Data.Char.Basic.«0».Char.of_any_eq_false_aux 3 := fun h =>
  absurd (h (p := fun _ => false) (Bool.eq_false_iff.2 fun e => by
    obtain ⟨c, hc⟩ := Char.any_eq_true_iff_exists_eq_true.1 e; simp at hc) 0xD800) (by decide)
-- `Batteries.DList.toList_mk`
theorem x5 : ¬ indep0% Batteries.DList.toList_mk 2 := fun h =>
  absurd (h (f := fun (_ : List Nat) => ([] : List Nat)) [0]) (by decide)
-- `Nat.recDiagAux_zero_right`
theorem x6 : ¬ drop1% Nat.recDiagAux_zero_right 5 := fun h =>
  absurd (h (motive := fun _ _ => Nat) (fun _ => 0) (fun _ => 1) (fun _ _ k => k) 0) (by decide)
-- `Nat.toFinDigits_of_ne_zero`
theorem x7 : indep% Nat.toFinDigits_of_ne_zero 3 := by
  intros; exact ⟨by omega⟩
-- `Nat.toFinDigits_eq_append`
theorem x8 : indep% Nat.toFinDigits_eq_append 4 := by
  intros; exact ⟨by omega⟩
-- `Nat.toFinDigits_ofFinDigits`
theorem x9 : drop% Nat.toFinDigits_ofFinDigits 1 := by
  intro base l hl
  by_cases h : 2 ≤ base
  · exact Nat.toFinDigits_ofFinDigits h hl
  · cases l with
    | nil => simp [Nat.toFinDigits_zero]
    | cons d l => exact absurd (hl d (by simp)) (by have := d.2; omega)
end


/-! ### part V1 -/
section
-- `Vector.USize.succ_toNat_of_lt`
theorem y1 : drop% _private.Batteries.Data.Vector.Basic.«0».Vector.USize.succ_toNat_of_lt 4 := by
  intro start stop n h_lt h_su
  have h1 := USize.lt_iff_toNat_lt.mp h_lt
  have h2 := stop.toNat_lt_size
  have hs : (2:Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, USize.toNat_one, hs, Nat.mod_eq_of_lt (by omega)]
-- `Vector.USize.succ_toNat_of_lt`
theorem y2 : drop% _private.Batteries.Data.Vector.Basic.«0».Vector.USize.succ_toNat_of_lt 5 := by
  intro start stop n h_lt h_stop
  have h1 := USize.lt_iff_toNat_lt.mp h_lt
  have h2 := stop.toNat_lt_size
  have hs : (2:Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, USize.toNat_one, hs, Nat.mod_eq_of_lt (by omega)]
-- `Vector.USize.succ_toNat_of_lt`
theorem y3 : ¬ drop0% _private.Batteries.Data.Vector.Basic.«0».Vector.USize.succ_toNat_of_lt 3 := fun h => by
  have := h (start := USize.ofNat (USize.size - 1)) (stop := 0) (n := 0) (by simp) USize.size_pos
  have hs : (2:Nat) ^ System.Platform.numBits = USize.size := rfl
  have h1 : 1 < USize.size := by cases System.Platform.numBits_eq <;> simp_all [USize.size]
  have h0 : (USize.ofNat (USize.size - 1)).toNat = USize.size - 1 := by
    exact USize.toNat_ofNat_of_lt' (by omega)
  rw [USize.toNat_add, h0, hs, USize.toNat_one, Nat.sub_add_cancel (by omega), Nat.mod_self] at this
  omega
-- `Vector.scanlM_empty`
theorem y4 : drop% Vector.scanlM_empty 5 := by
  intros; rw [Vector.scanlM, Vector.scanlM.loop]; rfl
-- `Vector.scanrM_empty`
theorem y5 : drop% Vector.scanrM_empty 5 := by
  intros; rw [Vector.scanrM, Vector.scanrM.loop]; rfl
end


/-! ### part Fl -/
section
open Float.Model
/-- tiny float format: 2 exponent bits, 2 mantissa bits (5 bits in total) -/
abbrev hcF : Float.Model.Format := { mantissaBitsWithoutImplicit := 2, exponentBits := 2 }
/-- helper: the canonical NaN is valid -/
theorem hcNaNValid : hcF.Valid (UnpackedFloat.packedNaN hcF) := ⟨fun _ _ => rfl⟩
example : UnpackedFloat.packedNaN hcF = 14#5 := by decide +kernel
/-- helper: the non-canonical NaN pattern 13 unpacks to NaN -/
theorem hcU13 : UnpackedFloat.unpack hcF 13#5 = UnpackedFloat.notANumber := by rfl

-- `Float.Model.UnpackedFloat.pack_unpack_of_valid`
theorem z1 : ¬ drop0% Float.Model.UnpackedFloat.pack_unpack_of_valid 2 := fun h =>
  absurd (h (spec := hcF) (b := 13#5)) (by decide +kernel)
-- `Float.Model.UnpackedFloat.unpack_inj_of_valid`
theorem z2 : ¬ drop0% Float.Model.UnpackedFloat.unpack_inj_of_valid 3 := fun h =>
  absurd ((h (spec := hcF) (b := 13#5) (b' := UnpackedFloat.packedNaN hcF) hcNaNValid).1 (by rw [UnpackedFloat.unpack_packedNaN, hcU13]))
    (by decide +kernel)
-- `Float.Model.UnpackedFloat.unpack_inj_of_valid`
theorem z3 : ¬ drop0% Float.Model.UnpackedFloat.unpack_inj_of_valid 4 := fun h =>
  absurd ((h (spec := hcF) (b := UnpackedFloat.packedNaN hcF) (b' := 13#5) hcNaNValid).1 (by rw [UnpackedFloat.unpack_packedNaN, hcU13]))
    (by decide +kernel)
-- `Float.Model.UnpackedFloat.unpack_eq_notANumber_iff_of_valid`
theorem z4 : ¬ drop0% Float.Model.UnpackedFloat.unpack_eq_notANumber_iff_of_valid 2 := fun h =>
  absurd ((h (spec := hcF) (b := 13#5)).1 hcU13) (by decide +kernel)
-- `Float.Model.UnpackedFloat.isNaN_unpack_iff_of_valid`
theorem z5 : ¬ drop0% Float.Model.UnpackedFloat.isNaN_unpack_iff_of_valid 2 := fun h =>
  absurd ((h (spec := hcF) (b := 13#5)).1 (by simp only [UnpackedFloat.isNaN_iff]; exact hcU13)) (by decide +kernel)
end


/-! ### part Fl2 -/
section
open Float.Model UnpackedFloat
/-- helper: an invalid bit pattern is a non-canonical NaN, so it unpacks to NaN -/
theorem hcNaN {spec : Float.Model.Format} {b : BitVec spec.numBits} (hv : ¬ spec.Valid b) : UnpackedFloat.unpack spec b = notANumber := by
  have this : unpackExponent b = -1#_ ∧ unpackMantissa b ≠ 0#_ := by
    refine Classical.byContradiction fun hc => hv ⟨fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  simp [UnpackedFloat.unpack, this]
/-- helper: signed zeros are valid -/
theorem hcZV {spec : Float.Model.Format} {s : Sign} : spec.Valid (packedZero spec s) := ⟨by simp [packedZero]⟩
-- `Float.Model.UnpackedFloat.unpack_eq_zero_iff_of_valid`
theorem z6 : drop% Float.Model.UnpackedFloat.unpack_eq_zero_iff_of_valid 3 := by
  intro spec sign b
  by_cases hv : spec.Valid b
  · exact unpack_eq_zero_iff_of_valid hv
  · rw [hcNaN hv]
    constructor
    · intro h; cases h
    · rintro rfl; exact absurd hcZV hv
-- `Float.Model.UnpackedFloat.unpack_beq_unpack_iff`
theorem z7 : drop% Float.Model.UnpackedFloat.unpack_beq_unpack_iff 3 := by
  intro spec b b' hb'
  by_cases hb : spec.Valid b
  · exact unpack_beq_unpack_iff hb hb'
  · rw [beq_iff_ne_notANumber_and_eq, hcNaN hb]
    simp only [ne_eq, not_true, false_and, false_iff]
    rintro ⟨-, -, h | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · subst h; exact hb hb'
    · exact hb hcZV
    · exact hb hcZV
-- `Float.Model.UnpackedFloat.unpack_beq_unpack_iff`
theorem z8 : drop% Float.Model.UnpackedFloat.unpack_beq_unpack_iff 4 := by
  intro spec b b' hb
  by_cases hb' : spec.Valid b'
  · exact unpack_beq_unpack_iff hb hb'
  · rw [beq_iff_ne_notANumber_and_eq, hcNaN hb']
    simp only [ne_eq, not_true, false_and, and_false, false_iff]
    rintro ⟨-, -, h | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
    · subst h; exact hb' hb
    · exact hb' hcZV
    · exact hb' hcZV
end


/-! ### part A1 -/
section
-- `Vector.scanlM_map`
theorem a1 : drop% Vector.scanlM_map 7 := by
  intros
  rename_i m _ _ _ n _ init f g as
  have key : ∀ k i (hi : i ≤ n) (acc : Vector _ i) cur, n - i = k →
      Vector.scanlM.loop g (as.map f) cur i hi acc = Vector.scanlM.loop (g · <| f ·) as cur i hi acc := by
    intro k; induction k with
    | zero => intro i hi acc cur hk; rw [Vector.scanlM.loop, Vector.scanlM.loop]; simp [show ¬ i < n by omega]
    | succ k ih =>
      intro i hi acc cur hk
      rw [Vector.scanlM.loop, Vector.scanlM.loop]
      simp only [show i < n by omega, dite_true, Vector.getElem_map]
      congr 1; funext x; exact ih _ _ _ _ (by omega)
  exact key _ 0 _ _ _ rfl
-- `Vector.scanrM_map`
theorem a2 : drop% Vector.scanrM_map 7 := by
  intros
  rename_i m _ _ _ n _ init f g as
  have key : ∀ i (hi : i ≤ n) (acc : Vector _ (n - i)) cur,
      Vector.scanrM.loop g (as.map f) cur i hi acc = Vector.scanrM.loop (fun a b => g (f a) b) as cur i hi acc := by
    intro i; induction i with
    | zero => intro hi acc cur; rw [Vector.scanrM.loop, Vector.scanrM.loop]; simp
    | succ i ih =>
      intro hi acc cur
      rw [Vector.scanrM.loop, Vector.scanrM.loop]
      simp only [show 0 < i + 1 by omega, dite_true, Vector.getElem_map]
      congr 1; funext x; exact ih _ _ _
  exact key _ _ _ _
-- `Array.scanlM_map`
theorem a3 : drop% Array.scanlM_map 6 := by
  intros
  rename_i m _ _ _ _ init f g as
  have key : ∀ k start stop (h1 : stop ≤ (as.map f).size) (h2 : stop ≤ as.size) acc cur, stop - start = k →
      Array.scanlM.loop g cur (as.map f) start stop h1 acc =
        Array.scanlM.loop (g · <| f ·) cur as start stop h2 acc := by
    intro k; induction k with
    | zero =>
      intro start stop h1 h2 acc cur hk
      rw [Array.scanlM.loop, Array.scanlM.loop]; simp [show ¬ start < stop by omega]
    | succ k ih =>
      intro start stop h1 h2 acc cur hk
      rw [Array.scanlM.loop, Array.scanlM.loop]
      simp only [show start < stop by omega, dite_true, Array.getElem_map]
      congr 1; funext x; exact ih _ _ _ _ _ _ (by omega)
  unfold Array.scanlM
  simp only [Array.size_map]
  exact key _ _ _ _ _ _ _ rfl
-- `Array.scanrM_map`
theorem a4 : drop% Array.scanrM_map 6 := by
  intros
  rename_i m _ _ _ _ init f g as
  have key : ∀ start stop (h1 : start ≤ (as.map f).size) (h2 : start ≤ as.size) acc cur,
      Array.scanrM.loop g cur (as.map f) start stop h1 acc =
        Array.scanrM.loop (fun a b => g (f a) b) cur as start stop h2 acc := by
    intro start; induction start with
    | zero =>
      intro stop h1 h2 acc cur
      rw [Array.scanrM.loop, Array.scanrM.loop]; simp
    | succ k ih =>
      intro stop h1 h2 acc cur
      rw [Array.scanrM.loop, Array.scanrM.loop]
      by_cases h : stop < k + 1
      · simp only [h, dite_true, Array.getElem_map]
        congr 1; funext x; exact ih _ _ _ _ _
      · simp [h]
  unfold Array.scanrM
  simp only [Array.size_map]
  exact key _ _ _ _ _ _
end


/-! ### part A2 -/
section
-- `Array.scanlM_extract`
theorem b1 : drop% Array.scanlM_extract 7 := by
  intros
  rename_i m _ _ start stop init _ f as
  have key : ∀ k i (h1 : (as.extract start stop).size ≤ (as.extract start stop).size)
      (h2 : min stop as.size ≤ as.size) acc cur, (as.extract start stop).size - i = k →
      Array.scanlM.loop f cur (as.extract start stop) i (as.extract start stop).size h1 acc =
        Array.scanlM.loop f cur as (start + i) (min stop as.size) h2 acc := by
    intro k; induction k with
    | zero =>
      intro i h1 h2 acc cur hk
      have := Array.size_extract (xs := as) (start := start) (stop := stop)
      rw [Array.scanlM.loop, Array.scanlM.loop]
      rw [dif_neg (show ¬ i < (as.extract start stop).size by omega),
        dif_neg (show ¬ start + i < min stop as.size by omega)]
    | succ k ih =>
      intro i h1 h2 acc cur hk
      have := Array.size_extract (xs := as) (start := start) (stop := stop)
      rw [Array.scanlM.loop, Array.scanlM.loop]
      simp only [show i < (as.extract start stop).size by omega, show start + i < min stop as.size by omega,
        dite_true, Array.getElem_extract]
      congr 1; funext x; rw [ih _ _ _ _ _ (by omega)]; rfl
  unfold Array.scanlM
  simp only [Nat.zero_min, Nat.min_self]
  by_cases hs : start ≤ as.size
  · rw [Nat.min_eq_left hs]; exact key _ 0 _ _ _ _ rfl
  · have := Array.size_extract (xs := as) (start := start) (stop := stop)
    rw [Array.scanlM.loop, Array.scanlM.loop]
    rw [dif_neg (show ¬ 0 < (as.extract start stop).size by omega),
      dif_neg (show ¬ min start as.size < min stop as.size by omega)]
-- `Subarray.scanlM_eq_scanlM_extract`
theorem b2 : drop% Subarray.scanlM_eq_scanlM_extract 5 := by
  intros
  simp only [Subarray.scanlM]
  exact b1.symm
-- `Array.scanrM_extract`
theorem b3 : drop% Array.scanrM_extract 7 := by
  intros
  rename_i m _ _ stop start init _ f as
  have key : ∀ i (h1 : i ≤ (as.extract stop start).size) (h2 : stop + i ≤ as.size) acc cur,
      Array.scanrM.loop f cur (as.extract stop start) i 0 h1 acc =
        Array.scanrM.loop f cur as (stop + i) stop h2 acc := by
    intro i; induction i with
    | zero =>
      intro h1 h2 acc cur
      rw [Array.scanrM.loop, Array.scanrM.loop, dif_neg (by omega), dif_neg (by omega)]
    | succ i ih =>
      intro h1 h2 acc cur
      have := Array.size_extract (xs := as) (start := stop) (stop := start)
      rw [Array.scanrM.loop, Array.scanrM.loop, dif_pos (by omega), dif_pos (by omega)]
      simp only [Array.getElem_extract, Nat.add_sub_cancel]
      congr 1; funext x; exact ih _ _ _ _
  have := Array.size_extract (xs := as) (start := stop) (stop := start)
  unfold Array.scanrM
  simp only [Nat.min_self]
  by_cases hs : stop ≤ min start as.size
  · have e : min start as.size = stop + (as.extract stop start).size := by omega
    simp only [e]
    exact key _ _ _ _ _
  · rw [Array.scanrM.loop, Array.scanrM.loop, dif_neg (by omega), dif_neg (by omega)]
-- `Subarray.scanrM_eq_scanrM_extract`
theorem b4 : drop% Subarray.scanrM_eq_scanrM_extract 5 := by
  intros
  simp only [Subarray.scanrM]
  exact b3.symm
end


/-! ### part A3 -/
section
-- `Array.scanlM_loop_eq_scanlMFast_loop`
theorem p1 : ¬ indep0% _private.Batteries.Data.Array.Basic.«0».Array.scanlM_loop_eq_scanlMFast_loop 7 := fun h =>
  absurd (h (m := Id) (β := Nat) (α := Nat) (f := fun b _ => b) (init := 0) (as := Array.replicate USize.size 0)
    (start := 0) (stop := 0) (h_start := Nat.zero_le _) (h_stop := Nat.zero_le _) (acc := #[]) :
    (Array.replicate USize.size 0).size < USize.size) (by simp)
-- `Array.scanlM_eq_scanlMFast`
theorem p2 : ¬ drop0% _private.Batteries.Data.Array.Basic.«0».Array.scanlM_eq_scanlMFast 7 := fun h => by
  have e := h (m := Option) (β := Nat) (α := Nat) (f := fun _ _ => none) (init := 0)
    (as := Array.replicate USize.size 0) (start := 0) (stop := USize.size)
  have hs := USize.size_pos
  rw [Array.scanlM, Array.scanlM.loop, dif_pos (by simp; omega)] at e
  conv at e => rhs; whnf
  rw [(priv% _private.Batteries.Data.Array.Basic.«0».Array.scanlMFast.loop.eq_1), dif_neg] at e
  · exact absurd e (by simp)
  · rw [USize.lt_iff_toNat_lt]; simp
-- `Array.scanlM_loop_eq_scanlMFast_loop`
theorem p3 : ¬ drop0% _private.Batteries.Data.Array.Basic.«0».Array.scanlM_loop_eq_scanlMFast_loop 10 := fun h => by
  have h1 : 1 < USize.size := by cases System.Platform.numBits_eq <;> simp_all [USize.size]
  have e := h (m := Option) (β := Nat) (α := Nat) (f := fun _ _ => none) (init := 0) (as := #[0])
    (h_size := h1) (start := USize.size) (stop := 1) (h_stop := Nat.le_refl _) (acc := #[])
  rw [Array.scanlM.loop, dif_neg (by omega)] at e
  rw [(priv% _private.Batteries.Data.Array.Basic.«0».Array.scanlMFast.loop.eq_1), dif_pos] at e
  · exact absurd e (by simp)
  · rw [USize.lt_iff_toNat_lt]; simp [USize.toNat_ofNat']
end
