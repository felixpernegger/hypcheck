import Std
import Lean

/-!
Hand pass `HashLemma` (hand14): non-instance (and a few instance) hypotheses of hash map/set
theorems in `Std.Data.{DHashMap,HashMap,HashSet,ExtDHashMap,ExtHashMap,ExtHashSet}` and the
internal `Std.DHashMap.Internal.Raw₀`/`Raw` lemmas. For hypothesis `hᵢ` of theorem `T` each
declaration proves `¬T'` (`¬ drop0% T i`, universes set to `0`) or `T'` (`drop% T i`).

148 necessary, 2 removable, 0 independent (of 150).

Hash maps do not evaluate (bucket indices go through the opaque `System.Platform.numBits`), so
no proof here computes a hash: either the library's own simp lemmas evaluate tiny maps
("lemma-based evaluation"), or the bucket index is left opaque and the proof case-splits on it.

Reusable models and toolkit (namespace `HashLemmaHand`):
* `P`: `Nat` keys compared modulo 2 (`⟨0⟩ == ⟨2⟩`), `hash` of `n % 2`; `EquivBEq` and
  `LawfulHashable` but not `LawfulBEq`, so every library lemma still applies (`P.beq_def` is the
  simp lemma for `==`). Refutes `[LawfulBEq α]` and dropped distinctness/membership premises whose
  failure needs two equal-but-different keys (stored key ≠ looked-up key).
* `W`: counting monad `Nat × α` (`pure` counts one step, `bind` adds counts); not lawful. On an
  empty map `foldM`/`forM`/`forIn` bind once per bucket, the `toArray`/`toList` side does not;
  `decide +kernel` evaluates both counters (empty maps involve no hashing).
* `rawS_toList`, `hashS_toList` (`{x}.toList = [x]` for raw/plain hash sets over `P`),
  `rawS_inner_toList`, `hashS_inner_toList`, `rawD_toList` (entry lists of singletons).
* `constBeq0_eq`, `constBeq_eq`: `==` on well-formed (raw) maps is the list model
  `Const.beqModel` of the entry lists, so `==` of two singletons evaluates by `simp`.
* Bucket toolkit for non-well-formed internal maps: `idx2` (with two buckets the index is `0` or
  `1`), `mkIdx_size2`/`mkIdx_size1` (rewrite `mkIdx` on a literal array of size 2/1),
  `isHashSelf_one`, `wf_single`, `wf_empty1` (one-bucket maps are well-formed),
  `getValue?_toListModel_bucket` (bucket lookup = model lookup, `LawfulHashable` + hash-self only). Pattern: case-split
  `idx2 (hash k)`, put the entry in the *other* bucket, `simp [Def, mkIdx_size2, h0]`, `decide`.

Removable (2):
* `m.WF` of `Std.DHashMap.Raw.toListRev_keysIter` (keysIter, toList and keys are all read off the
  bucket list without well-formedness);
* `[PartialEquivBEq α]` of `Std.DHashMap.Internal.Raw₀.Const.beq_eq_beqModel`: with `LawfulHashable`
  alone, keys `==` to `a` sit only in `a`'s bucket of a hash-self array, so bucket lookup is model
  lookup (`getValue?_toListModel_bucket`, which needs no `PartialEquivBEq`).

The generated part comes from `runs/hand14/scratch_HashLemma/gen.py` (binder lists in
`binders.out`). Run with the lean4 repo's stage1 binary: `lean checks/HashLemmaHand.lean`.
-/

open Lean Meta Elab Term in
/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
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

open Lean Meta Elab Term in
/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
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

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace HashLemmaHand

/-- Keys compared modulo 2: EquivBEq and LawfulHashable, not LawfulBEq (⟨0⟩ == ⟨2⟩). -/
structure P where n : Nat
deriving DecidableEq, Inhabited

instance : BEq P := ⟨fun a b => a.n % 2 == b.n % 2⟩
instance : Hashable P := ⟨fun a => hash (a.n % 2)⟩

@[simp] theorem P.beq_def (a b : P) : (a == b) = (a.n % 2 == b.n % 2) := rfl

instance : EquivBEq P where
  rfl := by simp
  symm := by simp; omega
  trans := by simp; omega

instance : LawfulHashable P where
  hash_eq {a b} h := by
    simp at h
    show hash (a.n % 2) = hash (b.n % 2)
    rw [h]

end HashLemmaHand

namespace HashLemmaHand

/-- Counting monad: pure counts one step, bind adds the counts (not lawful: pure_bind fails). -/
def W (α : Type) := Nat × α

instance : Monad W where
  pure a := (1, a)
  bind x f := (x.1 + (f x.2).1, (f x.2).2)

/-- The singleton raw hash set {x} over P lists exactly x. -/
theorem rawS_toList (x : P) : ((∅ : Std.HashSet.Raw P).insert x).toList = [x] := by
  have := Std.HashSet.Raw.toList_insert_perm (m := (∅ : Std.HashSet.Raw P)) Std.HashSet.Raw.WF.empty (k := x)
  simpa [Std.HashSet.Raw.toList_empty] using this

end HashLemmaHand

namespace HashLemmaHand
open Std

/-- Raw₀.Const.beq of well-formed maps is the list model Const.beqModel of their entry lists. -/
theorem constBeq0_eq {α β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [BEq β]
    {d₁ d₂ : DHashMap.Internal.Raw₀ α (fun _ => β)} (h₁ : d₁.1.WF) (h₂ : d₂.1.WF) :
    DHashMap.Internal.Raw₀.Const.beq d₁ d₂ = Std.Internal.List.Const.beqModel d₁.1.toList d₂.1.toList := by
  rw [DHashMap.Internal.Raw₀.Const.beq_eq_beqModel (DHashMap.Internal.Raw.WF.out h₁)
    (DHashMap.Internal.Raw.WF.out h₂)]
  simp [DHashMap.Internal.Raw.toList_eq_toListModel]

/-- Raw.Const.beq of well-formed raw maps is the list model Const.beqModel of their entry lists. -/
theorem constBeq_eq {α β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [BEq β]
    {d₁ d₂ : DHashMap.Raw α (fun _ => β)} (h₁ : d₁.WF) (h₂ : d₂.WF) :
    DHashMap.Raw.Const.beq d₁ d₂ = Std.Internal.List.Const.beqModel d₁.toList d₂.toList := by
  rw [DHashMap.Internal.Raw.Const.beq_eq h₁ h₂, constBeq0_eq h₁ h₂]

/-- Entry list of a singleton raw dependent map. -/
theorem rawD_toList {α : Type} {β : α → Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (k : α) (v : β k) : ((∅ : DHashMap.Raw α β).insert k v).toList = [⟨k, v⟩] := by
  have := DHashMap.Raw.toList_insert_perm (m := (∅ : DHashMap.Raw α β)) DHashMap.Raw.WF.empty (k := k) (v := v)
  simpa [DHashMap.Raw.toList_empty] using this

/-- Entry list of the inner map of a singleton raw hash set over P. -/
theorem rawS_inner_toList (x : P) :
    ((∅ : HashSet.Raw P).insert x).inner.inner.toList = [⟨x, ()⟩] := by
  have hw : ((∅ : HashSet.Raw P).insert x).inner.inner.WF := HashSet.Raw.WF.empty.insert.out.out
  have hk := DHashMap.Raw.map_fst_toList_eq_keys hw
  have : ((∅ : HashSet.Raw P).insert x).inner.inner.keys = [x] := rawS_toList x
  rw [this] at hk
  generalize ((∅ : HashSet.Raw P).insert x).inner.inner.toList = l at hk
  match l, hk with
  | [⟨a, ()⟩], h => simp at h; simp [h]

/-- The singleton hash set {x} over P lists exactly x. -/
theorem hashS_toList (x : P) : ((∅ : HashSet P).insert x).toList = [x] := by
  have := HashSet.toList_insert_perm (m := (∅ : HashSet P)) (k := x)
  simpa [HashSet.toList_empty] using this

/-- Entry list of the inner map of a singleton hash set over P. -/
theorem hashS_inner_toList (x : P) :
    ((∅ : HashSet P).insert x).inner.inner.1.toList = [⟨x, ()⟩] := by
  have hk := DHashMap.map_fst_toList_eq_keys (m := ((∅ : HashSet P).insert x).inner.inner)
  have : ((∅ : HashSet P).insert x).inner.inner.keys = [x] := hashS_toList x
  rw [this] at hk
  change List.map Sigma.fst ((∅ : HashSet P).insert x).inner.inner.1.toList = [x] at hk
  generalize ((∅ : HashSet P).insert x).inner.inner.1.toList = l at hk
  match l, hk with
  | [⟨a, ()⟩], h => simp at h; simp [h]

end HashLemmaHand

namespace HashLemmaHand
open Std DHashMap.Internal

/-- With two buckets, the bucket index of any hash is 0 or 1 (no platform arithmetic). -/
theorem idx2 (x : UInt64) :
    (mkIdx 2 (by decide) x).1.toNat = 0 ∨ (mkIdx 2 (by decide) x).1.toNat = 1 := by
  have := (mkIdx 2 (by decide) x).2; omega

/-- Rewrites the bucket index on a literal two-bucket array to the canonical mkIdx 2. -/
theorem mkIdx_size2 {γ : Type} {bs : Array γ} (hs : bs.size = 2) (p : 0 < bs.size) (x : UInt64) :
    (mkIdx bs.size p x).1.toNat = (mkIdx 2 (by decide) x).1.toNat := by
  have : ∀ n (p : 0 < n), n = 2 → (mkIdx n p x).1.toNat = (mkIdx 2 (by decide) x).1.toNat := by
    rintro n p rfl; rfl
  exact this _ p hs

/-- With one bucket, every bucket index is 0. -/
theorem mkIdx_size1 {γ : Type} {bs : Array γ} (hs : bs.size = 1) (p : 0 < bs.size) (x : UInt64) :
    (mkIdx bs.size p x).1.toNat = 0 := by
  have := (mkIdx bs.size p x).2; omega

/-- A one-bucket array is always hash-self. -/
theorem isHashSelf_one {α : Type} {β : α → Type} [BEq α] [Hashable α] (l : AssocList α β) :
    IsHashSelf #[l] :=
  ⟨fun i hi => ⟨fun h p _ => by
    have := mkIdx_size1 (bs := #[l]) rfl h (hash p.1)
    simp at hi; omega⟩⟩

/-- The one-bucket raw maps {0 ↦ 0} and ∅ over Nat are well-formed. -/
theorem wf_single : DHashMap.Internal.Raw.WFImp (⟨1, #[.cons 0 0 .nil]⟩ : DHashMap.Raw Nat (fun _ => Nat)) :=
  ⟨isHashSelf_one _, by decide, by simp [toListModel]⟩
theorem wf_empty1 : DHashMap.Internal.Raw.WFImp (⟨0, #[.nil]⟩ : DHashMap.Raw Nat (fun _ => Nat)) :=
  ⟨isHashSelf_one _, by decide, by simp [toListModel]⟩

open Std.Internal.List in
/-- Bucket lookup equals lookup in the whole model for hash-self buckets, with only
LawfulHashable (no PartialEquivBEq): keys == a can only sit in a's own bucket. -/
theorem getValue?_toListModel_bucket.{u, v} {α : Type u} {β : Type v} [BEq α] [Hashable α] [LawfulHashable α]
    (bs : Array (AssocList α (fun _ => β))) (h : 0 < bs.size) (hs : IsHashSelf bs) (a : α) :
    getValue? a (toListModel bs) = getValue? a (bucket bs h a).toList := by
  have hi := (mkIdx bs.size h (hash a)).2
  obtain ⟨l₁, l₂, h₁, h₂, -⟩ := Array.exists_of_uset (d := AssocList.nil) hi
  have hb : bucket bs h a = bs[(mkIdx bs.size h (hash a)).1] := rfl
  rw [hb, toListModel, h₁, List.flatMap_append, List.flatMap_cons, getValue?_append, getValue?_append]
  have c₁ : containsKey a (l₁.flatMap AssocList.toList) = false := by
    apply containsKey_flatMap_eq_false
    intro j hj
    rw [List.getElem_append_left' (l₂ := bs[(mkIdx bs.size h (hash a)).1] :: l₂), List.getElem_of_eq h₁.symm]
    apply (hs.hashes_to j _).containsKey_eq_false h a
    omega
  have c₂ : containsKey a (l₂.flatMap AssocList.toList) = false := by
    apply containsKey_flatMap_eq_false
    intro j hj
    rw [← List.getElem_cons_succ bs[(mkIdx bs.size h (hash a)).1] _ _ (by simp; omega)]
    rw [List.getElem_append_right' l₁, List.getElem_of_eq h₁.symm]
    apply (hs.hashes_to (j + 1 + l₁.length) _).containsKey_eq_false h a
    omega
  rw [getValue?_eq_none.2 c₁, getValue?_eq_none.2 c₂]
  simp

end HashLemmaHand

open Std HashLemmaHand

/-! ## Generated refutations (lemma-based evaluation of tiny maps) -/

-- `Std.ExtDHashMap.get!_ofList_of_mem`: l = [(0,0),(0,1)], k = k' = 0, v = 0: the later value 1 wins
theorem ExtDHashMap_getB_ofList_of_mem_h11 : ¬ drop0% Std.ExtDHashMap.get!_ofList_of_mem 11 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ ([⟨0, 0⟩, ⟨0, 1⟩]) (0) (0) (by simp) (0) _ (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.get!_insert] at this

-- `Std.ExtHashMap.getKey!_ofList_of_mem`: keys mod 2 (model P), l = [0, 2] (equal keys), k = k' = 0: the stored key is the other one
theorem ExtHashMap_getKeyB_ofList_of_mem_h11 : ¬ drop0% Std.ExtHashMap.getKey!_ofList_of_mem 11 := fun h => by
  have := @h (P) (Nat) inferInstance inferInstance _ _ _ ([(⟨0⟩, 0), (⟨2⟩, 0)]) (⟨0⟩) (⟨0⟩) (by simp) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKey!_insert] at this

-- `Std.ExtDHashMap.get!_ofList_of_mem`: l = [(0,0)], k = k' = 0, v = 1
theorem ExtDHashMap_getB_ofList_of_mem_h12 : ¬ drop0% Std.ExtDHashMap.get!_ofList_of_mem 12 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ ([⟨0, 0⟩]) (0) (0) (by simp) (1) _ (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.get!_insert] at this

-- `Std.ExtHashMap.getElem_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtHashMap_getElem_ofList_of_mem_h9 : ¬ drop0% Std.ExtHashMap.getElem_ofList_of_mem 9 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(1, 1), (0, 0)]) (1) (0) (1) (by simp) (by simp) (by simp [Std.ExtHashMap.ofList_eq_foldl])
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getElem_insert] at this

-- `Std.ExtHashMap.getKey!_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtHashMap_getKeyB_ofList_of_contains_eq_false_h9 : ¬ drop0% Std.ExtHashMap.getKey!_ofList_of_contains_eq_false 9 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ _ ([(1, 1)]) (1)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKey!_insert] at this

-- `Std.ExtHashMap.getKeyD_ofList_of_mem`: keys mod 2 (model P), l = [0, 2] (equal keys), k = k' = 0: the stored key is the other one
theorem ExtHashMap_getKeyD_ofList_of_mem_h11 : ¬ drop0% Std.ExtHashMap.getKeyD_ofList_of_mem 11 := fun h => by
  have := @h (P) (Nat) inferInstance inferInstance _ _ ([(⟨0⟩, 0), (⟨2⟩, 0)]) (⟨0⟩) (⟨0⟩) (⟨1⟩) (by simp) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKeyD_insert] at this

-- `Std.ExtHashMap.getKey_ofList_of_mem`: keys mod 2 (model P), l = [0, 2] (equal keys), k = k' = 0: the stored key is the other one
theorem ExtHashMap_getKey_ofList_of_mem_h10 : ¬ drop0% Std.ExtHashMap.getKey_ofList_of_mem 10 := fun h => by
  have := @h (P) (Nat) inferInstance inferInstance _ _ ([(⟨0⟩, 0), (⟨2⟩, 0)]) (⟨0⟩) (⟨0⟩) (by simp) (by simp) (by simp [Std.ExtHashMap.ofList_eq_foldl])
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKey_insert] at this

-- `Std.ExtHashSet.get!_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtHashSet_getB_ofList_of_contains_eq_false_h8 : ¬ drop0% Std.ExtHashSet.get!_ofList_of_contains_eq_false 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance _ _ _ ([1]) (1)
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.get!_insert] at this

-- `Std.ExtHashSet.get!_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtHashSet_getB_ofList_of_mem_h9 : ¬ drop0% Std.ExtHashSet.get!_ofList_of_mem 9 := fun h => by
  have := @h (Nat) inferInstance inferInstance _ _ _ ([1, 0]) (1) (0) (by simp) (by simp)
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.get!_insert] at this

-- `Std.ExtHashSet.get!_ofList_of_mem`: keys mod 2 (model P), l = [0, 2] (equal keys), k = k' = 2: the stored key is the other one
theorem ExtHashSet_getB_ofList_of_mem_h10 : ¬ drop0% Std.ExtHashSet.get!_ofList_of_mem 10 := fun h => by
  have := @h (P) inferInstance inferInstance _ _ _ ([⟨0⟩, ⟨2⟩]) (⟨2⟩) (⟨2⟩) (by simp) (by simp)
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.get!_insert] at this

-- `Std.ExtHashSet.get?_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtHashSet_getQ_ofList_of_contains_eq_false_h7 : ¬ drop0% Std.ExtHashSet.get?_ofList_of_contains_eq_false 7 := fun h => by
  have := @h (Nat) inferInstance inferInstance _ _ ([1]) (1)
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.get?_insert] at this

-- `Std.ExtHashSet.get?_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtHashSet_getQ_ofList_of_mem_h8 : ¬ drop0% Std.ExtHashSet.get?_ofList_of_mem 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance _ _ ([1, 0]) (1) (0) (by simp) (by simp)
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.get?_insert] at this

-- `Std.ExtHashSet.get?_ofList_of_mem`: keys mod 2 (model P), l = [0, 2] (equal keys), k = k' = 2: the stored key is the other one
theorem ExtHashSet_getQ_ofList_of_mem_h9 : ¬ drop0% Std.ExtHashSet.get?_ofList_of_mem 9 := fun h => by
  have := @h (P) inferInstance inferInstance _ _ ([⟨0⟩, ⟨2⟩]) (⟨2⟩) (⟨2⟩) (by simp) (by simp)
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.get?_insert] at this

-- `Std.ExtHashSet.getD_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtHashSet_getD_ofList_of_contains_eq_false_h8 : ¬ drop0% Std.ExtHashSet.getD_ofList_of_contains_eq_false 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance _ _ ([1]) (1) (0)
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.getD_insert] at this

-- `Std.ExtHashSet.getD_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtHashSet_getD_ofList_of_mem_h9 : ¬ drop0% Std.ExtHashSet.getD_ofList_of_mem 9 := fun h => by
  have := @h (Nat) inferInstance inferInstance _ _ ([1, 0]) (1) (0) (0) (by simp) (by simp)
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.getD_insert] at this

-- `Std.ExtHashSet.getD_ofList_of_mem`: keys mod 2 (model P), l = [0, 2] (equal keys), k = k' = 2: the stored key is the other one
theorem ExtHashSet_getD_ofList_of_mem_h10 : ¬ drop0% Std.ExtHashSet.getD_ofList_of_mem 10 := fun h => by
  have := @h (P) inferInstance inferInstance _ _ ([⟨0⟩, ⟨2⟩]) (⟨2⟩) (⟨2⟩) (⟨1⟩) (by simp) (by simp)
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.getD_insert] at this

-- `Std.ExtHashSet.get_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtHashSet_get_ofList_of_mem_h8 : ¬ drop0% Std.ExtHashSet.get_ofList_of_mem 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance _ _ ([1, 0]) (1) (0) (by simp) (by simp) (by simp [Std.ExtHashSet.ofList_eq_foldl])
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.get_insert] at this

-- `Std.ExtHashSet.get_ofList_of_mem`: keys mod 2 (model P), l = [0, 2] (equal keys), k = k' = 2: the stored key is the other one
theorem ExtHashSet_get_ofList_of_mem_h9 : ¬ drop0% Std.ExtHashSet.get_ofList_of_mem 9 := fun h => by
  have := @h (P) inferInstance inferInstance _ _ ([⟨0⟩, ⟨2⟩]) (⟨2⟩) (⟨2⟩) (by simp) (by simp) (by simp [Std.ExtHashSet.ofList_eq_foldl])
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.get_insert] at this

-- `Std.ExtHashSet.get_ofList_of_mem`: keys mod 2 (model P), l = [2], k = k' = 0: 0 ∉ l but the stored key is 2
theorem ExtHashSet_get_ofList_of_mem_h10 : ¬ drop0% Std.ExtHashSet.get_ofList_of_mem 10 := fun h => by
  have := @h (P) inferInstance inferInstance _ _ ([⟨2⟩]) (⟨0⟩) (⟨0⟩) (by simp) (by simp) (by simp [Std.ExtHashSet.ofList_eq_foldl])
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.get_insert] at this

-- `Std.ExtHashSet.size_ofList`: l = [0, 0] (repeated key): size 1 ≠ 2
theorem ExtHashSet_size_ofList_h6 : ¬ drop0% Std.ExtHashSet.size_ofList 6 := fun h => by
  have := @h (Nat) inferInstance inferInstance _ _ ([0, 0])
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.size_insert] at this

-- `Std.ExtDHashMap.get!_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtDHashMap_getB_ofList_of_contains_eq_false_h8 : ¬ drop0% Std.ExtDHashMap.get!_ofList_of_contains_eq_false 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ ([⟨1, 1⟩]) (1) _
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.get!_insert] at this

-- `Std.ExtDHashMap.getD_ofList_of_mem`: l = [(0,0),(0,1)], k = k' = 0, v = 0: the later value 1 wins
theorem ExtDHashMap_getD_ofList_of_mem_h11 : ¬ drop0% Std.ExtDHashMap.getD_ofList_of_mem 11 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ ([⟨0, 0⟩, ⟨0, 1⟩]) (0) (0) (by simp) (0) (0) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getD_insert] at this

-- `Std.ExtDHashMap.getD_ofList_of_mem`: l = [(0,0)], k = k' = 0, v = 1
theorem ExtDHashMap_getD_ofList_of_mem_h12 : ¬ drop0% Std.ExtDHashMap.getD_ofList_of_mem 12 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ ([⟨0, 0⟩]) (0) (0) (by simp) (1) (0) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getD_insert] at this

-- `Std.ExtDHashMap.get_ofList_of_mem`: l = [(0,0),(0,1)], k = k' = 0, v = 0: the later value 1 wins
theorem ExtDHashMap_get_ofList_of_mem_h10 : ¬ drop0% Std.ExtDHashMap.get_ofList_of_mem 10 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ ([⟨0, 0⟩, ⟨0, 1⟩]) (0) (0) (by simp) (0) (by simp) (by simp [Std.ExtDHashMap.ofList_eq_foldl])
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.get_insert] at this

-- `Std.ExtDHashMap.get_ofList_of_mem`: l = [(0,0)], k = k' = 0, v = 1
theorem ExtDHashMap_get_ofList_of_mem_h11 : ¬ drop0% Std.ExtDHashMap.get_ofList_of_mem 11 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ ([⟨0, 0⟩]) (0) (0) (by simp) (1) (by simp) (by simp [Std.ExtDHashMap.ofList_eq_foldl])
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.get_insert] at this

-- `Std.ExtHashMap.getD_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtHashMap_getD_ofList_of_contains_eq_false_h9 : ¬ drop0% Std.ExtHashMap.getD_ofList_of_contains_eq_false 9 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(1, 1)]) (1) (0)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getD_insert] at this

-- `Std.ExtHashMap.getD_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtHashMap_getD_ofList_of_mem_h9 : ¬ drop0% Std.ExtHashMap.getD_ofList_of_mem 9 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(1, 1), (0, 0)]) (1) (0) (1) (0) (by simp) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getD_insert] at this

-- `Std.ExtHashMap.getD_ofList_of_mem`: l = [(0,0),(0,1)], k = k' = 0, v = 0: the later value 1 wins
theorem ExtHashMap_getD_ofList_of_mem_h12 : ¬ drop0% Std.ExtHashMap.getD_ofList_of_mem 12 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(0, 0), (0, 1)]) (0) (0) (by simp) (0) (0) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getD_insert] at this

-- `Std.ExtHashMap.getD_ofList_of_mem`: l = [(0,0)], k = k' = 0, v = 1
theorem ExtHashMap_getD_ofList_of_mem_h13 : ¬ drop0% Std.ExtHashMap.getD_ofList_of_mem 13 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(0, 0)]) (0) (0) (by simp) (1) (0) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getD_insert] at this

-- `Std.ExtHashMap.getElem!_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtHashMap_getElemB_ofList_of_contains_eq_false_h9 : ¬ drop0% Std.ExtHashMap.getElem!_ofList_of_contains_eq_false 9 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(1, 1)]) (1) _
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getElem!_insert] at this

-- `Std.ExtHashMap.getElem!_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtHashMap_getElemB_ofList_of_mem_h9 : ¬ drop0% Std.ExtHashMap.getElem!_ofList_of_mem 9 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(1, 1), (0, 0)]) (1) (0) (1) _ (by simp) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getElem!_insert] at this

-- `Std.ExtHashMap.getElem!_ofList_of_mem`: l = [(0,0),(0,1)], k = k' = 0, v = 0: the later value 1 wins
theorem ExtHashMap_getElemB_ofList_of_mem_h12 : ¬ drop0% Std.ExtHashMap.getElem!_ofList_of_mem 12 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(0, 0), (0, 1)]) (0) (0) (by simp) (0) _ (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getElem!_insert] at this

-- `Std.ExtHashMap.getElem!_ofList_of_mem`: l = [(0,0)], k = k' = 0, v = 1
theorem ExtHashMap_getElemB_ofList_of_mem_h13 : ¬ drop0% Std.ExtHashMap.getElem!_ofList_of_mem 13 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(0, 0)]) (0) (0) (by simp) (1) _ (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getElem!_insert] at this

-- `Std.ExtHashMap.getElem?_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtHashMap_getElemQ_ofList_of_contains_eq_false_h8 : ¬ drop0% Std.ExtHashMap.getElem?_ofList_of_contains_eq_false 8 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(1, 1)]) (1)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getElem?_insert] at this

-- `Std.ExtHashMap.getElem?_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtHashMap_getElemQ_ofList_of_mem_h9 : ¬ drop0% Std.ExtHashMap.getElem?_ofList_of_mem 9 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(1, 1), (0, 0)]) (1) (0) (1) (by simp) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getElem?_insert] at this

-- `Std.ExtHashMap.getElem?_ofList_of_mem`: l = [(0,0),(0,1)], k = k' = 0, v = 0: the later value 1 wins
theorem ExtHashMap_getElemQ_ofList_of_mem_h11 : ¬ drop0% Std.ExtHashMap.getElem?_ofList_of_mem 11 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(0, 0), (0, 1)]) (0) (0) (by simp) (0) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getElem?_insert] at this

-- `Std.ExtHashMap.getElem?_ofList_of_mem`: l = [(0,0)], k = k' = 0, v = 1
theorem ExtHashMap_getElemQ_ofList_of_mem_h12 : ¬ drop0% Std.ExtHashMap.getElem?_ofList_of_mem 12 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(0, 0)]) (0) (0) (by simp) (1) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getElem?_insert] at this

-- `Std.ExtHashMap.getElem_ofList_of_mem`: l = [(0,0),(0,1)], k = k' = 0, v = 0: the later value 1 wins
theorem ExtHashMap_getElem_ofList_of_mem_h11 : ¬ drop0% Std.ExtHashMap.getElem_ofList_of_mem 11 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(0, 0), (0, 1)]) (0) (0) (by simp) (0) (by simp) (by simp [Std.ExtHashMap.ofList_eq_foldl])
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getElem_insert] at this

-- `Std.ExtHashMap.getElem_ofList_of_mem`: l = [(0,0)], k = k' = 0, v = 1
theorem ExtHashMap_getElem_ofList_of_mem_h12 : ¬ drop0% Std.ExtHashMap.getElem_ofList_of_mem 12 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(0, 0)]) (0) (0) (by simp) (1) (by simp) (by simp [Std.ExtHashMap.ofList_eq_foldl])
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getElem_insert] at this

-- `Std.ExtHashMap.getKey!_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtHashMap_getKeyB_ofList_of_mem_h10 : ¬ drop0% Std.ExtHashMap.getKey!_ofList_of_mem 10 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ _ ([(1, 1), (0, 0)]) (1) (0) (by simp) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKey!_insert] at this

-- `Std.ExtHashMap.getKey!_ofList_of_mem`: keys mod 2 (model P), l = [2], k = k' = 0: 0 ∉ l but the stored key is 2
theorem ExtHashMap_getKeyB_ofList_of_mem_h12 : ¬ drop0% Std.ExtHashMap.getKey!_ofList_of_mem 12 := fun h => by
  have := @h (P) (Nat) inferInstance inferInstance _ _ _ ([(⟨2⟩, 0)]) (⟨0⟩) (⟨0⟩) (by simp) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKey!_insert] at this

-- `Std.ExtHashMap.getKey?_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtHashMap_getKeyQ_ofList_of_contains_eq_false_h8 : ¬ drop0% Std.ExtHashMap.getKey?_ofList_of_contains_eq_false 8 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(1, 1)]) (1)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKey?_insert] at this

-- `Std.ExtHashMap.getKey?_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtHashMap_getKeyQ_ofList_of_mem_h9 : ¬ drop0% Std.ExtHashMap.getKey?_ofList_of_mem 9 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(1, 1), (0, 0)]) (1) (0) (by simp) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKey?_insert] at this

-- `Std.ExtHashMap.getKey?_ofList_of_mem`: keys mod 2 (model P), l = [0, 2] (equal keys), k = k' = 0: the stored key is the other one
theorem ExtHashMap_getKeyQ_ofList_of_mem_h10 : ¬ drop0% Std.ExtHashMap.getKey?_ofList_of_mem 10 := fun h => by
  have := @h (P) (Nat) inferInstance inferInstance _ _ ([(⟨0⟩, 0), (⟨2⟩, 0)]) (⟨0⟩) (⟨0⟩) (by simp) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKey?_insert] at this

-- `Std.ExtHashMap.getKey?_ofList_of_mem`: keys mod 2 (model P), l = [2], k = k' = 0: 0 ∉ l but the stored key is 2
theorem ExtHashMap_getKeyQ_ofList_of_mem_h11 : ¬ drop0% Std.ExtHashMap.getKey?_ofList_of_mem 11 := fun h => by
  have := @h (P) (Nat) inferInstance inferInstance _ _ ([(⟨2⟩, 0)]) (⟨0⟩) (⟨0⟩) (by simp) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKey?_insert] at this

-- `Std.ExtHashMap.getKeyD_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtHashMap_getKeyD_ofList_of_contains_eq_false_h9 : ¬ drop0% Std.ExtHashMap.getKeyD_ofList_of_contains_eq_false 9 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(1, 1)]) (1) (0)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKeyD_insert] at this

-- `Std.ExtHashMap.getKeyD_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtHashMap_getKeyD_ofList_of_mem_h10 : ¬ drop0% Std.ExtHashMap.getKeyD_ofList_of_mem 10 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(1, 1), (0, 0)]) (1) (0) (0) (by simp) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKeyD_insert] at this

-- `Std.ExtHashMap.getKeyD_ofList_of_mem`: keys mod 2 (model P), l = [2], k = k' = 0: 0 ∉ l but the stored key is 2
theorem ExtHashMap_getKeyD_ofList_of_mem_h12 : ¬ drop0% Std.ExtHashMap.getKeyD_ofList_of_mem 12 := fun h => by
  have := @h (P) (Nat) inferInstance inferInstance _ _ ([(⟨2⟩, 0)]) (⟨0⟩) (⟨0⟩) (⟨1⟩) (by simp) (by simp)
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKeyD_insert] at this

-- `Std.ExtHashMap.getKey_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtHashMap_getKey_ofList_of_mem_h9 : ¬ drop0% Std.ExtHashMap.getKey_ofList_of_mem 9 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(1, 1), (0, 0)]) (1) (0) (by simp) (by simp) (by simp [Std.ExtHashMap.ofList_eq_foldl])
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKey_insert] at this

-- `Std.ExtHashMap.getKey_ofList_of_mem`: keys mod 2 (model P), l = [2], k = k' = 0: 0 ∉ l but the stored key is 2
theorem ExtHashMap_getKey_ofList_of_mem_h11 : ¬ drop0% Std.ExtHashMap.getKey_ofList_of_mem 11 := fun h => by
  have := @h (P) (Nat) inferInstance inferInstance _ _ ([(⟨2⟩, 0)]) (⟨0⟩) (⟨0⟩) (by simp) (by simp) (by simp [Std.ExtHashMap.ofList_eq_foldl])
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.getKey_insert] at this

-- `Std.ExtHashMap.size_ofList`: l = [0, 0] (repeated key): size 1 ≠ 2
theorem ExtHashMap_size_ofList_h7 : ¬ drop0% Std.ExtHashMap.size_ofList 7 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance _ _ ([(0, 0), (0, 0)])
  simp [Std.ExtHashMap.ofList_eq_foldl, Std.ExtHashMap.size_insert] at this

-- `Std.ExtDHashMap.get?_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtDHashMap_getQ_ofList_of_contains_eq_false_h7 : ¬ drop0% Std.ExtDHashMap.get?_ofList_of_contains_eq_false 7 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ ([⟨1, 1⟩]) (1)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.get?_insert] at this

-- `Std.ExtDHashMap.get?_ofList_of_mem`: l = [(0,0),(0,1)], k = k' = 0, v = 0: the later value 1 wins
theorem ExtDHashMap_getQ_ofList_of_mem_h10 : ¬ drop0% Std.ExtDHashMap.get?_ofList_of_mem 10 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ ([⟨0, 0⟩, ⟨0, 1⟩]) (0) (0) (by simp) (0) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.get?_insert] at this

-- `Std.ExtDHashMap.get?_ofList_of_mem`: l = [(0,0)], k = k' = 0, v = 1
theorem ExtDHashMap_getQ_ofList_of_mem_h11 : ¬ drop0% Std.ExtDHashMap.get?_ofList_of_mem 11 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ ([⟨0, 0⟩]) (0) (0) (by simp) (1) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.get?_insert] at this

-- `Std.ExtDHashMap.getD_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtDHashMap_getD_ofList_of_contains_eq_false_h8 : ¬ drop0% Std.ExtDHashMap.getD_ofList_of_contains_eq_false 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ ([⟨1, 1⟩]) (1) (0)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getD_insert] at this

-- `Std.ExtDHashMap.getKey!_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtDHashMap_getKeyB_ofList_of_contains_eq_false_h9 : ¬ drop0% Std.ExtDHashMap.getKey!_ofList_of_contains_eq_false 9 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ _ _ ([⟨1, 1⟩]) (1)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKey!_insert] at this

-- `Std.ExtDHashMap.getKey!_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtDHashMap_getKeyB_ofList_of_mem_h10 : ¬ drop0% Std.ExtDHashMap.getKey!_ofList_of_mem 10 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ _ _ ([⟨1, 1⟩, ⟨0, 0⟩]) (1) (0) (by simp) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKey!_insert] at this

-- `Std.ExtDHashMap.getKey!_ofList_of_mem`: keys mod 2 (model P), l = [0, 2] (equal keys), k = k' = 0: the stored key is the other one
theorem ExtDHashMap_getKeyB_ofList_of_mem_h11 : ¬ drop0% Std.ExtDHashMap.getKey!_ofList_of_mem 11 := fun h => by
  have := @h (P) inferInstance inferInstance (fun _ => Nat) _ _ _ ([⟨⟨0⟩, 0⟩, ⟨⟨2⟩, 0⟩]) (⟨0⟩) (⟨0⟩) (by simp) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKey!_insert] at this

-- `Std.ExtDHashMap.getKey!_ofList_of_mem`: keys mod 2 (model P), l = [2], k = k' = 0: 0 ∉ l but the stored key is 2
theorem ExtDHashMap_getKeyB_ofList_of_mem_h12 : ¬ drop0% Std.ExtDHashMap.getKey!_ofList_of_mem 12 := fun h => by
  have := @h (P) inferInstance inferInstance (fun _ => Nat) _ _ _ ([⟨⟨2⟩, 0⟩]) (⟨0⟩) (⟨0⟩) (by simp) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKey!_insert] at this

-- `Std.ExtDHashMap.getKey?_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtDHashMap_getKeyQ_ofList_of_contains_eq_false_h8 : ¬ drop0% Std.ExtDHashMap.getKey?_ofList_of_contains_eq_false 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ _ ([⟨1, 1⟩]) (1)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKey?_insert] at this

-- `Std.ExtDHashMap.getKey?_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtDHashMap_getKeyQ_ofList_of_mem_h9 : ¬ drop0% Std.ExtDHashMap.getKey?_ofList_of_mem 9 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ _ ([⟨1, 1⟩, ⟨0, 0⟩]) (1) (0) (by simp) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKey?_insert] at this

-- `Std.ExtDHashMap.getKey?_ofList_of_mem`: keys mod 2 (model P), l = [0, 2] (equal keys), k = k' = 0: the stored key is the other one
theorem ExtDHashMap_getKeyQ_ofList_of_mem_h10 : ¬ drop0% Std.ExtDHashMap.getKey?_ofList_of_mem 10 := fun h => by
  have := @h (P) inferInstance inferInstance (fun _ => Nat) _ _ ([⟨⟨0⟩, 0⟩, ⟨⟨2⟩, 0⟩]) (⟨0⟩) (⟨0⟩) (by simp) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKey?_insert] at this

-- `Std.ExtDHashMap.getKey?_ofList_of_mem`: keys mod 2 (model P), l = [2], k = k' = 0: 0 ∉ l but the stored key is 2
theorem ExtDHashMap_getKeyQ_ofList_of_mem_h11 : ¬ drop0% Std.ExtDHashMap.getKey?_ofList_of_mem 11 := fun h => by
  have := @h (P) inferInstance inferInstance (fun _ => Nat) _ _ ([⟨⟨2⟩, 0⟩]) (⟨0⟩) (⟨0⟩) (by simp) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKey?_insert] at this

-- `Std.ExtDHashMap.getKeyD_ofList_of_contains_eq_false`: l = [(1,1)], k = 1, fallback = 0: the key is present
theorem ExtDHashMap_getKeyD_ofList_of_contains_eq_false_h9 : ¬ drop0% Std.ExtDHashMap.getKeyD_ofList_of_contains_eq_false 9 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ _ ([⟨1, 1⟩]) (1) (0)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKeyD_insert] at this

-- `Std.ExtDHashMap.getKeyD_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtDHashMap_getKeyD_ofList_of_mem_h10 : ¬ drop0% Std.ExtDHashMap.getKeyD_ofList_of_mem 10 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ _ ([⟨1, 1⟩, ⟨0, 0⟩]) (1) (0) (0) (by simp) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKeyD_insert] at this

-- `Std.ExtDHashMap.getKeyD_ofList_of_mem`: keys mod 2 (model P), l = [0, 2] (equal keys), k = k' = 0: the stored key is the other one
theorem ExtDHashMap_getKeyD_ofList_of_mem_h11 : ¬ drop0% Std.ExtDHashMap.getKeyD_ofList_of_mem 11 := fun h => by
  have := @h (P) inferInstance inferInstance (fun _ => Nat) _ _ ([⟨⟨0⟩, 0⟩, ⟨⟨2⟩, 0⟩]) (⟨0⟩) (⟨0⟩) (⟨1⟩) (by simp) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKeyD_insert] at this

-- `Std.ExtDHashMap.getKeyD_ofList_of_mem`: keys mod 2 (model P), l = [2], k = k' = 0: 0 ∉ l but the stored key is 2
theorem ExtDHashMap_getKeyD_ofList_of_mem_h12 : ¬ drop0% Std.ExtDHashMap.getKeyD_ofList_of_mem 12 := fun h => by
  have := @h (P) inferInstance inferInstance (fun _ => Nat) _ _ ([⟨⟨2⟩, 0⟩]) (⟨0⟩) (⟨0⟩) (⟨1⟩) (by simp) (by simp)
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKeyD_insert] at this

-- `Std.ExtDHashMap.getKey_ofList_of_mem`: l = [(1,1),(0,0)], k = 1, k' = 0: lookup of 0 gives 0, not 1
theorem ExtDHashMap_getKey_ofList_of_mem_h9 : ¬ drop0% Std.ExtDHashMap.getKey_ofList_of_mem 9 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ _ ([⟨1, 1⟩, ⟨0, 0⟩]) (1) (0) (by simp) (by simp) (by simp [Std.ExtDHashMap.ofList_eq_foldl])
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKey_insert] at this

-- `Std.ExtDHashMap.getKey_ofList_of_mem`: keys mod 2 (model P), l = [0, 2] (equal keys), k = k' = 0: the stored key is the other one
theorem ExtDHashMap_getKey_ofList_of_mem_h10 : ¬ drop0% Std.ExtDHashMap.getKey_ofList_of_mem 10 := fun h => by
  have := @h (P) inferInstance inferInstance (fun _ => Nat) _ _ ([⟨⟨0⟩, 0⟩, ⟨⟨2⟩, 0⟩]) (⟨0⟩) (⟨0⟩) (by simp) (by simp) (by simp [Std.ExtDHashMap.ofList_eq_foldl])
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKey_insert] at this

-- `Std.ExtDHashMap.getKey_ofList_of_mem`: keys mod 2 (model P), l = [2], k = k' = 0: 0 ∉ l but the stored key is 2
theorem ExtDHashMap_getKey_ofList_of_mem_h11 : ¬ drop0% Std.ExtDHashMap.getKey_ofList_of_mem 11 := fun h => by
  have := @h (P) inferInstance inferInstance (fun _ => Nat) _ _ ([⟨⟨2⟩, 0⟩]) (⟨0⟩) (⟨0⟩) (by simp) (by simp) (by simp [Std.ExtDHashMap.ofList_eq_foldl])
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.getKey_insert] at this

-- `Std.ExtDHashMap.size_ofList`: l = [0, 0] (repeated key): size 1 ≠ 2
theorem ExtDHashMap_size_ofList_h7 : ¬ drop0% Std.ExtDHashMap.size_ofList 7 := fun h => by
  have := @h (Nat) inferInstance inferInstance (fun _ => Nat) _ _ ([⟨0, 0⟩, ⟨0, 0⟩])
  simp [Std.ExtDHashMap.ofList_eq_foldl, Std.ExtDHashMap.size_insert] at this

-- `Std.ExtHashSet.get!_ofList_of_mem`: keys mod 2 (model P), l = [2], k = k' = 0: 0 ∉ l but the stored key is 2
theorem ExtHashSet_getB_ofList_of_mem_h11 : ¬ drop0% Std.ExtHashSet.get!_ofList_of_mem 11 := fun h => by
  have := @h (P) inferInstance inferInstance _ _ _ ([⟨2⟩]) (⟨0⟩) (⟨0⟩) (by simp) (by simp)
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.get!_insert] at this

-- `Std.ExtHashSet.get?_ofList_of_mem`: keys mod 2 (model P), l = [2], k = k' = 0: 0 ∉ l but the stored key is 2
theorem ExtHashSet_getQ_ofList_of_mem_h10 : ¬ drop0% Std.ExtHashSet.get?_ofList_of_mem 10 := fun h => by
  have := @h (P) inferInstance inferInstance _ _ ([⟨2⟩]) (⟨0⟩) (⟨0⟩) (by simp) (by simp)
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.get?_insert] at this

-- `Std.ExtHashSet.getD_ofList_of_mem`: keys mod 2 (model P), l = [2], k = k' = 0: 0 ∉ l but the stored key is 2
theorem ExtHashSet_getD_ofList_of_mem_h11 : ¬ drop0% Std.ExtHashSet.getD_ofList_of_mem 11 := fun h => by
  have := @h (P) inferInstance inferInstance _ _ ([⟨2⟩]) (⟨0⟩) (⟨0⟩) (⟨1⟩) (by simp) (by simp)
  simp [Std.ExtHashSet.ofList_eq_foldl, Std.ExtHashSet.getD_insert] at this

-- `Std.ExtHashSet.mem_congr`: m = {0}, a = 0, b = 1
theorem ExtHashSet_mem_congr_h8 : ¬ drop0% Std.ExtHashSet.mem_congr 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance ((∅ : ExtHashSet Nat).insert 0) _ _ (0) (1)
  simp at this

-- `Std.ExtHashMap.getElem?_congr`: m = {0 ↦ 0}, a = 0, b = 1
theorem ExtHashMap_getElemQ_congr_h9 : ¬ drop0% Std.ExtHashMap.getElem?_congr 9 := fun h => by
  have := @h (Nat) (Nat) inferInstance inferInstance ((∅ : ExtHashMap Nat Nat).insert 0 0) _ _ (0) (1)
  simp [ExtHashMap.getElem?_insert] at this

-- `Std.HashSet.get?_eq_some`: keys mod 2 (model P), m = {0}, k = 2: get? 2 = some 0
theorem HashSet_getQ_eq_some_h4 : ¬ drop0% Std.HashSet.get?_eq_some 4 := fun h => by
  have := @h (P) inferInstance inferInstance ((∅ : HashSet P).insert ⟨0⟩) (⟨2⟩) (by simp)
  simp [HashSet.get?_insert] at this

-- `Std.HashSet.get?_eq_some`: m = ∅, k = 0
theorem HashSet_getQ_eq_some_h6 : ¬ drop0% Std.HashSet.get?_eq_some 6 := fun h => by
  have := @h (Nat) inferInstance inferInstance (∅) _ (0)
  simp at this

-- `Std.ExtHashSet.get?_eq_some`: m = ∅, k = 0
theorem ExtHashSet_getQ_eq_some_h6 : ¬ drop0% Std.ExtHashSet.get?_eq_some 6 := fun h => by
  have := @h (Nat) inferInstance inferInstance (∅) _ (0)
  simp at this

-- `Std.HashSet.get!_eq_of_mem`: keys mod 2 (model P), m = {0}, k = 2: get! 2 = 0
theorem HashSet_getB_eq_of_mem_h4 : ¬ drop0% Std.HashSet.get!_eq_of_mem 4 := fun h => by
  have := @h (P) inferInstance inferInstance ((∅ : HashSet P).insert ⟨0⟩) _ (⟨2⟩) (by simp)
  simp [HashSet.get!_insert] at this

-- `Std.HashSet.get!_eq_of_mem`: m = ∅, k = 1: get! 1 = default = 0
theorem HashSet_getB_eq_of_mem_h7 : ¬ drop0% Std.HashSet.get!_eq_of_mem 7 := fun h => by
  have := @h (Nat) inferInstance inferInstance (∅) _ _ (1)
  simp at this

-- `Std.HashSet.getD_eq_of_mem`: keys mod 2 (model P), m = {0}, k = 2: getD 2 _ = 0
theorem HashSet_getD_eq_of_mem_h4 : ¬ drop0% Std.HashSet.getD_eq_of_mem 4 := fun h => by
  have := @h (P) inferInstance inferInstance ((∅ : HashSet P).insert ⟨0⟩) (⟨2⟩) (⟨1⟩) (by simp)
  simp [HashSet.getD_insert] at this

-- `Std.HashSet.getD_eq_of_mem`: m = ∅, k = 1, fallback = 0
theorem HashSet_getD_eq_of_mem_h7 : ¬ drop0% Std.HashSet.getD_eq_of_mem 7 := fun h => by
  have := @h (Nat) inferInstance inferInstance (∅) _ (1) (0)
  simp at this

-- `Std.HashSet.Equiv.of_forall_contains_eq`: keys mod 2 (model P), m₁ = {0}, m₂ = {2}: same membership, but get? 0 differs
theorem HashSet_Equiv_of_forall_contains_eq_h5 : ¬ drop0% Std.HashSet.Equiv.of_forall_contains_eq 5 := fun h => by
  have := @h (P) inferInstance inferInstance ((∅ : HashSet P).insert ⟨0⟩) ((∅ : HashSet P).insert ⟨2⟩) (by intro k; simp [HashSet.contains_insert])
  have := this.get?_eq (k := ⟨0⟩)
  simp [HashSet.get?_insert] at this

-- `Std.HashSet.Equiv.of_forall_contains_eq`: m₁ = ∅, m₂ = {0}
theorem HashSet_Equiv_of_forall_contains_eq_h6 : ¬ drop0% Std.HashSet.Equiv.of_forall_contains_eq 6 := fun h => by
  have := @h (Nat) inferInstance inferInstance (∅) ((∅ : HashSet Nat).insert 0) _
  have := this.contains_eq (k := 0)
  simp at this

-- `Std.HashSet.Equiv.of_forall_get?_eq`: m₁ = ∅, m₂ = {0}
theorem HashSet_Equiv_of_forall_getQ_eq_h7 : ¬ drop0% Std.HashSet.Equiv.of_forall_get?_eq 7 := fun h => by
  have := @h (Nat) inferInstance inferInstance (∅) ((∅ : HashSet Nat).insert 0) _ _
  have := this.contains_eq (k := 0)
  simp at this

-- `Std.HashSet.equiv_of_beq`: m₁ = ∅, m₂ = {0}
theorem HashSet_equiv_of_beq_h6 : ¬ drop0% Std.HashSet.equiv_of_beq 6 := fun h => by
  have := @h (Nat) inferInstance inferInstance (∅) ((∅ : HashSet Nat).insert 0) _
  have := this.contains_eq (k := 0)
  simp at this

-- `Std.HashSet.equiv_iff_forall_mem_iff`: keys mod 2 (model P), m₁ = {0}, m₂ = {2}: same membership, but get? 0 differs
theorem HashSet_equiv_iff_forall_mem_iff_h5 : ¬ drop0% Std.HashSet.equiv_iff_forall_mem_iff 5 := fun h => by
  have := @h (P) inferInstance inferInstance ((∅ : HashSet P).insert ⟨0⟩) ((∅ : HashSet P).insert ⟨2⟩)
  have := (this.2 fun k => by simp [HashSet.mem_insert]).get?_eq (k := ⟨0⟩)
  simp [HashSet.get?_insert] at this

-- `Std.HashSet.get?_insertMany_list_of_mem`: m = ∅, l = [1], k = 1
theorem HashSet_getQ_insertMany_list_of_mem_h8 : ¬ drop0% Std.HashSet.get?_insertMany_list_of_mem 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance (∅) _ _ ([1]) (1)
  simp [HashSet.insertMany_list_singleton, HashSet.get?_insert] at this

-- `Std.HashSet.get?_diff_of_mem_right`: m₁ = {1}, m₂ = ∅, k = 1
theorem HashSet_getQ_diff_of_mem_right_h8 : ¬ drop0% Std.HashSet.get?_diff_of_mem_right 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance ((∅ : HashSet Nat).insert 1) (∅) _ _ (1)
  simp [HashSet.get?_diff, HashSet.get?_insert] at this

-- `Std.HashSet.get?_inter_of_mem_right`: m₁ = {1}, m₂ = ∅, k = 1
theorem HashSet_getQ_inter_of_mem_right_h8 : ¬ drop0% Std.HashSet.get?_inter_of_mem_right 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance ((∅ : HashSet Nat).insert 1) (∅) _ _ (1)
  simp [HashSet.get?_inter, HashSet.get?_insert] at this

-- `Std.HashSet.get!_insertMany_list_of_mem`: m = ∅, l = [1], k = 1
theorem HashSet_getB_insertMany_list_of_mem_h9 : ¬ drop0% Std.HashSet.get!_insertMany_list_of_mem 9 := fun h => by
  have := @h (Nat) inferInstance inferInstance (∅) _ _ _ ([1]) (1)
  simp [HashSet.insertMany_list_singleton, HashSet.get!_insert] at this

-- `Std.HashSet.get!_diff_of_mem_right`: m₁ = {1}, m₂ = ∅, k = 1
theorem HashSet_getB_diff_of_mem_right_h9 : ¬ drop0% Std.HashSet.get!_diff_of_mem_right 9 := fun h => by
  have := @h (Nat) inferInstance inferInstance ((∅ : HashSet Nat).insert 1) (∅) _ _ _ (1)
  simp [HashSet.get!_diff, HashSet.get!_insert] at this

-- `Std.HashSet.get!_inter_of_mem_right`: m₁ = {1}, m₂ = ∅, k = 1
theorem HashSet_getB_inter_of_mem_right_h9 : ¬ drop0% Std.HashSet.get!_inter_of_mem_right 9 := fun h => by
  have := @h (Nat) inferInstance inferInstance ((∅ : HashSet Nat).insert 1) (∅) _ _ _ (1)
  simp [HashSet.get!_inter, HashSet.get!_insert] at this

-- `Std.HashSet.getD_insertMany_list_of_mem`: m = ∅, l = [1], k = 1
theorem HashSet_getD_insertMany_list_of_mem_h9 : ¬ drop0% Std.HashSet.getD_insertMany_list_of_mem 9 := fun h => by
  have := @h (Nat) inferInstance inferInstance (∅) _ _ ([1]) (1) (0)
  simp [HashSet.insertMany_list_singleton, HashSet.getD_insert] at this

-- `Std.HashSet.getD_diff_of_mem_right`: m₁ = {1}, m₂ = ∅, k = 1
theorem HashSet_getD_diff_of_mem_right_h9 : ¬ drop0% Std.HashSet.getD_diff_of_mem_right 9 := fun h => by
  have := @h (Nat) inferInstance inferInstance ((∅ : HashSet Nat).insert 1) (∅) _ _ (1) (0)
  simp [HashSet.getD_diff, HashSet.getD_insert] at this

-- `Std.HashSet.getD_inter_of_mem_right`: m₁ = {1}, m₂ = ∅, k = 1
theorem HashSet_getD_inter_of_mem_right_h9 : ¬ drop0% Std.HashSet.getD_inter_of_mem_right 9 := fun h => by
  have := @h (Nat) inferInstance inferInstance ((∅ : HashSet Nat).insert 1) (∅) _ _ (1) (0)
  simp [HashSet.getD_inter, HashSet.getD_insert] at this

-- `Std.HashSet.not_mem_diff_of_mem_right`: m₁ = {0}, m₂ = ∅, k = 0
theorem HashSet_not_mem_diff_of_mem_right_h8 : ¬ drop0% Std.HashSet.not_mem_diff_of_mem_right 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance ((∅ : HashSet Nat).insert 0) (∅) _ _ (0)
  simp [HashSet.mem_diff_iff] at this

-- `Std.HashSet.isEmpty_diff_left`: m₁ = {0}, m₂ = ∅
theorem HashSet_isEmpty_diff_left_h7 : ¬ drop0% Std.HashSet.isEmpty_diff_left 7 := fun h => by
  have := @h (Nat) inferInstance inferInstance ((∅ : HashSet Nat).insert 0) (∅) _ _
  rw [HashSet.isEmpty_diff_iff] at this
  simpa using this 0

-- `Std.HashSet.isEmpty_inter_left`: m₁ = m₂ = {0}
theorem HashSet_isEmpty_inter_left_h7 : ¬ drop0% Std.HashSet.isEmpty_inter_left 7 := fun h => by
  have := @h (Nat) inferInstance inferInstance ((∅ : HashSet Nat).insert 0) ((∅ : HashSet Nat).insert 0) _ _
  rw [HashSet.isEmpty_inter_iff] at this
  simpa using this 0

-- `Std.HashSet.isEmpty_inter_right`: m₁ = m₂ = {0}
theorem HashSet_isEmpty_inter_right_h7 : ¬ drop0% Std.HashSet.isEmpty_inter_right 7 := fun h => by
  have := @h (Nat) inferInstance inferInstance ((∅ : HashSet Nat).insert 0) ((∅ : HashSet Nat).insert 0) _ _
  rw [HashSet.isEmpty_inter_iff] at this
  simpa using this 0

-- `Std.HashSet.mem_of_get?_eq_some`: m = ∅, k = k' = 0
theorem HashSet_mem_of_getQ_eq_some_h8 : ¬ drop0% Std.HashSet.mem_of_get?_eq_some 8 := fun h => by
  have := @h (Nat) inferInstance inferInstance (∅) _ _ (0) (0)
  simp at this

-- `Std.DHashMap.Equiv.mem_iff`: m₁ = ∅, m₂ = {0 ↦ 0}, k = 0
theorem DHashMap_Equiv_mem_iff_h9 : ¬ drop0% Std.DHashMap.Equiv.mem_iff 9 := fun h => by
  have := @h (Nat) (fun _ => Nat) inferInstance inferInstance (∅) ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0) _ _ (0)
  simp at this

-- `Std.DHashMap.Raw.Equiv.mem_iff`: m₁ = ∅, m₂ = {0 ↦ 0}, k = 0
theorem DHashMap_Raw_Equiv_mem_iff_h11 : ¬ drop0% Std.DHashMap.Raw.Equiv.mem_iff 11 := fun h => by
  have := @h (Nat) (fun _ => Nat) _ _ (∅) ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0) _ _ (0) (by exact DHashMap.Raw.WF.empty) (by exact DHashMap.Raw.WF.empty.insert)
  simp [DHashMap.Raw.mem_insert DHashMap.Raw.WF.empty] at this

-- `Std.HashSet.Raw.get!_congr`: m = {1}, k = 1, k' = 0
theorem HashSet_Raw_getB_congr_h10 : ¬ drop0% Std.HashSet.Raw.get!_congr 10 := fun h => by
  have := @h (Nat) ((∅ : HashSet.Raw Nat).insert 1) _ _ _ _ _ (by exact HashSet.Raw.WF.empty.insert) (1) (0)
  simp [HashSet.Raw.get!_insert HashSet.Raw.WF.empty] at this

-- `Std.HashSet.Raw.getD_congr`: m = {1}, k = 1, k' = 0
theorem HashSet_Raw_getD_congr_h10 : ¬ drop0% Std.HashSet.Raw.getD_congr 10 := fun h => by
  have := @h (Nat) ((∅ : HashSet.Raw Nat).insert 1) _ _ _ _ (by exact HashSet.Raw.WF.empty.insert) (1) (0) (2)
  simp [HashSet.Raw.getD_insert HashSet.Raw.WF.empty] at this

-- `Std.HashSet.Raw.get?_congr`: m = {1}, k = 1, k' = 0
theorem HashSet_Raw_getQ_congr_h9 : ¬ drop0% Std.HashSet.Raw.get?_congr 9 := fun h => by
  have := @h (Nat) ((∅ : HashSet.Raw Nat).insert 1) _ _ _ _ (by exact HashSet.Raw.WF.empty.insert) (1) (0)
  simp [HashSet.Raw.get?_insert HashSet.Raw.WF.empty] at this

-- `Std.HashSet.Raw.mem_congr`: m = {0}, a = 0, b = 1
theorem HashSet_Raw_mem_congr_h9 : ¬ drop0% Std.HashSet.Raw.mem_congr 9 := fun h => by
  have := @h (Nat) ((∅ : HashSet.Raw Nat).insert 0) _ _ _ _ (by exact HashSet.Raw.WF.empty.insert) (0) (1)
  simp [HashSet.Raw.mem_insert HashSet.Raw.WF.empty] at this

-- `Std.HashMap.Raw.getD_congr`: m = {0 ↦ 1}, a = 0, b = 1, fallback = 0
theorem HashMap_Raw_getD_congr_h11 : ¬ drop0% Std.HashMap.Raw.getD_congr 11 := fun h => by
  have := @h (Nat) (Nat) ((∅ : HashMap.Raw Nat Nat).insert 0 1) _ _ _ _ (by exact HashMap.Raw.WF.empty.insert) (0) (1) (0)
  simp [HashMap.Raw.getD_insert HashMap.Raw.WF.empty] at this

-- `Std.HashMap.Raw.getElem!_congr`: m = {0 ↦ 1}, a = 0, b = 1
theorem HashMap_Raw_getElemB_congr_h11 : ¬ drop0% Std.HashMap.Raw.getElem!_congr 11 := fun h => by
  have := @h (Nat) (Nat) ((∅ : HashMap.Raw Nat Nat).insert 0 1) _ _ _ _ _ (by exact HashMap.Raw.WF.empty.insert) (0) (1)
  simp [HashMap.Raw.getElem!_insert HashMap.Raw.WF.empty] at this

-- `Std.HashSet.Raw.contains_of_mem_toArray`: m = ∅, k = 0
theorem HashSet_Raw_contains_of_mem_toArray_h8 : ¬ drop0% Std.HashSet.Raw.contains_of_mem_toArray 8 := fun h => by
  have := @h (Nat) (∅) _ _ _ _ (by exact HashSet.Raw.WF.empty) (0)
  simp at this

-- `Std.HashSet.Raw.insertMany_ind`: motive = False, m = ∅, l = []
theorem HashSet_Raw_insertMany_ind_h8 : ¬ drop0% Std.HashSet.Raw.insertMany_ind 8 := fun h => by
  have := @h (Nat) _ _ (List Nat) _ (fun _ => False) (∅) ([]) (by intro _ _ h; exact h)
  exact this

-- `Std.HashSet.Raw.mem_toList`: keys mod 2 (model P), m = {0}, k = 2: 2 ∈ m but toList = [0]
theorem HashSet_Raw_mem_toList_h4 : ¬ drop0% Std.HashSet.Raw.mem_toList 4 := fun h => by
  have := @h (P) ((∅ : HashSet.Raw P).insert ⟨0⟩) _ _ (by exact HashSet.Raw.WF.empty.insert) (⟨2⟩)
  simp [rawS_toList, HashSet.Raw.mem_insert HashSet.Raw.WF.empty] at this

-- `Std.HashSet.Raw.mem_toArray`: keys mod 2 (model P), m = {0}, k = 2: 2 ∈ m but toArray = #[0]
theorem HashSet_Raw_mem_toArray_h4 : ¬ drop0% Std.HashSet.Raw.mem_toArray 4 := fun h => by
  have := @h (P) ((∅ : HashSet.Raw P).insert ⟨0⟩) _ _ (⟨2⟩) (by exact HashSet.Raw.WF.empty.insert)
  rw [← Array.mem_toList_iff, HashSet.Raw.toList_toArray HashSet.Raw.WF.empty.insert] at this
  simp [rawS_toList, HashSet.Raw.mem_insert HashSet.Raw.WF.empty] at this

-- `Std.HashSet.Raw.all_eq_false_iff_exists_mem_getElem`: keys mod 2 (model P), m = {0}, p x = (x.n == 0): all p = true, but 2 ∈ m with p 2 = false
theorem HashSet_Raw_all_eq_false_iff_exists_mem_getElem_h4 : ¬ drop0% Std.HashSet.Raw.all_eq_false_iff_exists_mem_getElem 4 := fun h => by
  have := @h (P) ((∅ : HashSet.Raw P).insert ⟨0⟩) _ _ (fun x => x.n == 0) (by exact HashSet.Raw.WF.empty.insert)
  rw [← HashSet.Raw.all_toList HashSet.Raw.WF.empty.insert, rawS_toList] at this
  have := this.2 ⟨⟨2⟩, (by simp [HashSet.Raw.mem_insert HashSet.Raw.WF.empty]), rfl⟩
  simp at this

-- `Std.HashSet.Raw.all_eq_true_iff_forall_mem`: keys mod 2 (model P), m = {0}, p x = (x.n == 0): all p = true, but 2 ∈ m with p 2 = false
theorem HashSet_Raw_all_eq_true_iff_forall_mem_h4 : ¬ drop0% Std.HashSet.Raw.all_eq_true_iff_forall_mem 4 := fun h => by
  have := @h (P) ((∅ : HashSet.Raw P).insert ⟨0⟩) _ _ (fun x => x.n == 0) (by exact HashSet.Raw.WF.empty.insert)
  rw [← HashSet.Raw.all_toList HashSet.Raw.WF.empty.insert, rawS_toList] at this
  have := this.1 rfl ⟨2⟩ (by simp [HashSet.Raw.mem_insert HashSet.Raw.WF.empty])
  simp at this

-- `Std.HashSet.Raw.any_eq_true_iff_exists_mem`: keys mod 2 (model P), m = {0}, p x = (x.n == 2): any p = false, but 2 ∈ m with p 2 = true
theorem HashSet_Raw_any_eq_true_iff_exists_mem_h4 : ¬ drop0% Std.HashSet.Raw.any_eq_true_iff_exists_mem 4 := fun h => by
  have := @h (P) ((∅ : HashSet.Raw P).insert ⟨0⟩) _ _ (fun x => x.n == 2) (by exact HashSet.Raw.WF.empty.insert)
  rw [← HashSet.Raw.any_toList HashSet.Raw.WF.empty.insert, rawS_toList] at this
  have := this.2 ⟨⟨2⟩, (by simp [HashSet.Raw.mem_insert HashSet.Raw.WF.empty]), rfl⟩
  simp at this

-- `Std.HashSet.Raw.any_eq_false_iff_forall_mem`: keys mod 2 (model P), m = {0}, p x = (x.n == 2): any p = false, but 2 ∈ m with p 2 = true
theorem HashSet_Raw_any_eq_false_iff_forall_mem_h4 : ¬ drop0% Std.HashSet.Raw.any_eq_false_iff_forall_mem 4 := fun h => by
  have := @h (P) ((∅ : HashSet.Raw P).insert ⟨0⟩) _ _ (fun x => x.n == 2) (by exact HashSet.Raw.WF.empty.insert)
  rw [← HashSet.Raw.any_toList HashSet.Raw.WF.empty.insert, rawS_toList] at this
  have := this.1 rfl ⟨2⟩ (by simp [HashSet.Raw.mem_insert HashSet.Raw.WF.empty])
  simp at this

-- `Std.HashSet.Raw.equiv_iff_forall_mem_iff`: keys mod 2 (model P), m₁ = {0}, m₂ = {2}: same membership, toList [0] vs [2]
theorem HashSet_Raw_equiv_iff_forall_mem_iff_h7 : ¬ drop0% Std.HashSet.Raw.equiv_iff_forall_mem_iff 7 := fun h => by
  have := @h (P) _ _ ((∅ : HashSet.Raw P).insert ⟨0⟩) ((∅ : HashSet.Raw P).insert ⟨2⟩) (by exact HashSet.Raw.WF.empty.insert) (by exact HashSet.Raw.WF.empty.insert)
  have := (this.2 fun k => by simp [HashSet.Raw.mem_insert HashSet.Raw.WF.empty]).toList_perm
  simp [rawS_toList] at this

-- `Std.HashMap.Raw.mem_toList_iff_getElem?_eq_some`: keys mod 2 (model P), m = {0 ↦ 0}, k = 2, v = 0: m[2]? = some 0 but (2, 0) ∉ toList
theorem HashMap_Raw_mem_toList_iff_getElemQ_eq_some_h5 : ¬ drop0% Std.HashMap.Raw.mem_toList_iff_getElem?_eq_some 5 := fun h => by
  have := @h (P) (Nat) ((∅ : HashMap.Raw P Nat).insert ⟨0⟩ 0) _ _ (by exact HashMap.Raw.WF.empty.insert) (⟨2⟩) (0)
  rw [HashMap.Raw.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some HashMap.Raw.WF.empty.insert] at this
  simp [HashMap.Raw.getKey?_insert HashMap.Raw.WF.empty, HashMap.Raw.getElem?_insert HashMap.Raw.WF.empty] at this

-- `Std.HashSet.Raw.foldM_eq_foldlM_toArray`: m = ∅ in the counting monad W (pure counts 1): the bucket fold binds once per bucket
theorem HashSet_Raw_foldM_eq_foldlM_toArray_h7 : ¬ drop0% Std.HashSet.Raw.foldM_eq_foldlM_toArray 7 := fun h => by
  have := @h (Nat) _ _ ((∅ : HashSet.Raw Nat)) (Nat) (W) _ (fun d _ => pure d) (0) (by exact HashSet.Raw.WF.empty)
  exact absurd (congrArg Prod.fst this) (by decide +kernel)

-- `Std.HashSet.Raw.forIn_eq_forIn_toArray`: m = ∅ in the counting monad W (pure counts 1): the bucket loop binds once per bucket
theorem HashSet_Raw_forIn_eq_forIn_toArray_h7 : ¬ drop0% Std.HashSet.Raw.forIn_eq_forIn_toArray 7 := fun h => by
  have := @h (Nat) _ _ ((∅ : HashSet.Raw Nat)) (Nat) (W) _ (fun _ d => pure (.yield d)) (0) (by exact HashSet.Raw.WF.empty)
  exact absurd (congrArg Prod.fst this) (by decide +kernel)

-- `Std.HashSet.Raw.forM_eq_forM_toArray`: m = ∅ in the counting monad W (pure counts 1): the bucket loop binds once per bucket
theorem HashSet_Raw_forM_eq_forM_toArray_h6 : ¬ drop0% Std.HashSet.Raw.forM_eq_forM_toArray 6 := fun h => by
  have := @h (Nat) _ _ ((∅ : HashSet.Raw Nat)) (W) _ (fun _ => pure ⟨⟩) (by exact HashSet.Raw.WF.empty)
  exact absurd (congrArg Prod.fst this) (by decide +kernel)

-- `Std.DHashMap.Raw.foldM_eq_foldlM_toArray`: m = ∅ in the counting monad W (pure counts 1): the bucket fold binds once per bucket
theorem DHashMap_Raw_foldM_eq_foldlM_toArray_h8 : ¬ drop0% Std.DHashMap.Raw.foldM_eq_foldlM_toArray 8 := fun h => by
  have := @h (Nat) (fun _ => Nat) _ _ ((∅ : DHashMap.Raw Nat (fun _ => Nat))) (Nat) (W) _ (fun d _ _ => pure d) (0) (by exact DHashMap.Raw.WF.empty)
  exact absurd (congrArg Prod.fst this) (by decide +kernel)

-- `Std.DHashMap.Raw.forIn_eq_forIn_toArray`: m = ∅ in the counting monad W (pure counts 1): the bucket loop binds once per bucket
theorem DHashMap_Raw_forIn_eq_forIn_toArray_h8 : ¬ drop0% Std.DHashMap.Raw.forIn_eq_forIn_toArray 8 := fun h => by
  have := @h (Nat) (fun _ => Nat) _ _ ((∅ : DHashMap.Raw Nat (fun _ => Nat))) (Nat) (W) _ (fun _ _ d => pure (.yield d)) (0) (by exact DHashMap.Raw.WF.empty)
  exact absurd (congrArg Prod.fst this) (by decide +kernel)

-- `Std.DHashMap.Raw.forM_eq_forM_toArray`: m = ∅ in the counting monad W (pure counts 1): the bucket loop binds once per bucket
theorem DHashMap_Raw_forM_eq_forM_toArray_h7 : ¬ drop0% Std.DHashMap.Raw.forM_eq_forM_toArray 7 := fun h => by
  have := @h (Nat) (fun _ => Nat) _ _ ((∅ : DHashMap.Raw Nat (fun _ => Nat))) (W) _ (fun _ _ => pure ⟨⟩) (by exact DHashMap.Raw.WF.empty)
  exact absurd (congrArg Prod.fst this) (by decide +kernel)

-- `Std.HashMap.Raw.foldM_eq_foldlM_toArray`: m = ∅ in the counting monad W (pure counts 1): the bucket fold binds once per bucket
theorem HashMap_Raw_foldM_eq_foldlM_toArray_h8 : ¬ drop0% Std.HashMap.Raw.foldM_eq_foldlM_toArray 8 := fun h => by
  have := @h (Nat) (Nat) _ _ ((∅ : HashMap.Raw Nat Nat)) (Nat) (W) _ (fun d _ _ => pure d) (0) (by exact HashMap.Raw.WF.empty)
  exact absurd (congrArg Prod.fst this) (by decide +kernel)

-- `Std.HashMap.Raw.forIn_eq_forIn_toArray`: m = ∅ in the counting monad W (pure counts 1): the bucket loop binds once per bucket
theorem HashMap_Raw_forIn_eq_forIn_toArray_h8 : ¬ drop0% Std.HashMap.Raw.forIn_eq_forIn_toArray 8 := fun h => by
  have := @h (Nat) (Nat) _ _ ((∅ : HashMap.Raw Nat Nat)) (Nat) (W) _ (fun _ _ d => pure (.yield d)) (0) (by exact HashMap.Raw.WF.empty)
  exact absurd (congrArg Prod.fst this) (by decide +kernel)

-- `Std.HashMap.Raw.forM_eq_forM_toArray`: m = ∅ in the counting monad W (pure counts 1): the bucket loop binds once per bucket
theorem HashMap_Raw_forM_eq_forM_toArray_h7 : ¬ drop0% Std.HashMap.Raw.forM_eq_forM_toArray 7 := fun h => by
  have := @h (Nat) (Nat) _ _ ((∅ : HashMap.Raw Nat Nat)) (W) _ (fun _ _ => pure ⟨⟩) (by exact HashMap.Raw.WF.empty)
  exact absurd (congrArg Prod.fst this) (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.foldRevM_eq_foldrM_toArray`: one empty bucket in the counting monad W (pure counts 1)
theorem DHashMap_Internal_Raw0_foldRevM_eq_foldrM_toArray_h6 : ¬ drop0% Std.DHashMap.Internal.Raw₀.foldRevM_eq_foldrM_toArray 6 := fun h => by
  have := @h (Nat) (fun _ => Nat) (⟨⟨0, #[.nil]⟩, by decide⟩) (Nat) (W) _ (fun d _ _ => pure d) (0)
  exact absurd (congrArg Prod.fst this) (by decide +kernel)

/-! ## Hand-written refutations: `==` on maps, empty raw maps, bucket placement -/

open DHashMap.Internal

-- `Std.HashSet.Raw.beq_iff_equiv`: keys mod 2 (model P), m₁ = {0}, m₂ = {2}: m₁ == m₂ (lookups agree up to ==), but toList [0] vs [2] are not permutations.
theorem HashSet_Raw_beq_iff_equiv_h5 : ¬ drop0% Std.HashSet.Raw.beq_iff_equiv 5 := fun h => by
  have := @h P _ _ ((∅ : HashSet.Raw P).insert ⟨0⟩) ((∅ : HashSet.Raw P).insert ⟨2⟩) HashSet.Raw.WF.empty.insert HashSet.Raw.WF.empty.insert
  have hb : (((∅ : HashSet.Raw P).insert ⟨0⟩) == ((∅ : HashSet.Raw P).insert ⟨2⟩)) = true := by
    show DHashMap.Raw.Const.beq _ _ = true
    rw [constBeq_eq HashSet.Raw.WF.empty.insert.out.out HashSet.Raw.WF.empty.insert.out.out,
      rawS_inner_toList, rawS_inner_toList]
    simp [Std.Internal.List.Const.beqModel, Std.Internal.List.getValue?]
  have := (this.1 hb).toList_perm
  simp [rawS_toList] at this

-- `Std.HashMap.Raw.beq_iff_equiv`: values mod 2 (model P as β), m₁ = {0 ↦ 0}, m₂ = {0 ↦ 2}: m₁ == m₂, but m₁[0]? ≠ m₂[0]?.
theorem HashMap_Raw_beq_iff_equiv_h8 : ¬ drop0% Std.HashMap.Raw.beq_iff_equiv 8 := fun h => by
  have := @h Nat _ _ P ((∅ : HashMap.Raw Nat P).insert 0 ⟨0⟩) ((∅ : HashMap.Raw Nat P).insert 0 ⟨2⟩) _ _ HashMap.Raw.WF.empty.insert HashMap.Raw.WF.empty.insert
  have hb : (((∅ : HashMap.Raw Nat P).insert 0 ⟨0⟩) == ((∅ : HashMap.Raw Nat P).insert 0 ⟨2⟩)) = true := by
    show DHashMap.Raw.Const.beq _ _ = true
    rw [constBeq_eq HashMap.Raw.WF.empty.insert.out HashMap.Raw.WF.empty.insert.out]
    show Std.Internal.List.Const.beqModel ((∅ : DHashMap.Raw Nat (fun _ => P)).insert 0 ⟨0⟩).toList ((∅ : DHashMap.Raw Nat (fun _ => P)).insert 0 ⟨2⟩).toList = true
    rw [rawD_toList, rawD_toList]
    simp [Std.Internal.List.Const.beqModel, Std.Internal.List.getValue?]
  have := (this.1 hb).getElem?_eq HashMap.Raw.WF.empty.insert HashMap.Raw.WF.empty.insert (k := 0)
  simp [HashMap.Raw.getElem?_insert HashMap.Raw.WF.empty] at this

-- `Std.HashSet.beq_iff_equiv`: keys mod 2 (model P), m₁ = {0}, m₂ = {2}: m₁ == m₂, but get? 0 differs.
theorem HashSet_beq_iff_equiv_h5 : ¬ drop0% Std.HashSet.beq_iff_equiv 5 := fun h => by
  have := @h P inferInstance inferInstance ((∅ : HashSet P).insert ⟨0⟩) ((∅ : HashSet P).insert ⟨2⟩)
  have hb : (((∅ : HashSet P).insert ⟨0⟩) == ((∅ : HashSet P).insert ⟨2⟩)) = true := by
    have e := constBeq0_eq (d₁ := ⟨((∅ : HashSet P).insert ⟨0⟩).inner.inner.1, ((∅ : HashSet P).insert ⟨0⟩).inner.inner.2.size_buckets_pos⟩)
      (d₂ := ⟨((∅ : HashSet P).insert ⟨2⟩).inner.inner.1, ((∅ : HashSet P).insert ⟨2⟩).inner.inner.2.size_buckets_pos⟩)
      ((∅ : HashSet P).insert ⟨0⟩).inner.inner.2 ((∅ : HashSet P).insert ⟨2⟩).inner.inner.2
    dsimp only at e
    rw [hashS_inner_toList, hashS_inner_toList] at e
    exact e.trans (by simp [Std.Internal.List.Const.beqModel, Std.Internal.List.getValue?])
  have := (this.1 hb).get?_eq (k := ⟨0⟩)
  simp [HashSet.get?_insert] at this

open Std.Iterators in
-- `Std.DHashMap.Raw.toListRev_keysIter`: removable; keysIter lists the keys of `toList`, and both `toList` and `keys` are read off the bucket list without well-formedness (`toList_eq_toListModel`, `keys_eq_keys_toListModel`).
theorem DHashMap_Raw_toListRev_keysIter_h7 : drop% Std.DHashMap.Raw.toListRev_keysIter 7 := by
  intro α β m _ _ _ _
  simp [Iter.toListRev_eq, DHashMap.Raw.keysIter, Iter.toList_map, DHashMap.Raw.toList_iter,
    DHashMap.Internal.Raw.toList_eq_toListModel, DHashMap.Internal.Raw.keys_eq_keys_toListModel,
    Std.Internal.List.keys_eq_map]

-- `Std.DHashMap.Internal.Raw.isEmpty_eq_isEmpty`: raw map with size field 1 and no buckets: isEmpty = false, empty model.
theorem DHashMap_Internal_Raw_isEmpty_eq_isEmpty_h5 : ¬ drop0% Std.DHashMap.Internal.Raw.isEmpty_eq_isEmpty 5 := fun h => by
  have := @h Nat (fun _ => Nat) _ _ ⟨1, #[]⟩
  exact absurd this (by decide)

-- `Std.HashMap.Raw.empty_equiv_iff_isEmpty`: raw map with size field 1 and no buckets: equivalent to ∅ (empty model) but isEmpty = false.
theorem HashMap_Raw_empty_equiv_iff_isEmpty_h7 : ¬ drop0% Std.HashMap.Raw.empty_equiv_iff_isEmpty 7 := fun h => by
  have := @h Nat Nat _ _ ⟨⟨1, #[]⟩⟩ _ _
  have e : (∅ : HashMap.Raw Nat Nat).Equiv ⟨⟨1, #[]⟩⟩ := ⟨⟨by decide +kernel⟩⟩
  exact absurd (this.1 e) (by decide)


-- `Std.DHashMap.Internal.Raw₀.get!_eq_getValueCast!`: two buckets, entry 0 ↦ 1 placed in the bucket 0 does not hash to (case split on the index): get! 0 = 0, model gives 1.
theorem DHashMap_Internal_Raw0_getB_eq_getValueCastB_h6 : ¬ drop0% Std.DHashMap.Internal.Raw₀.get!_eq_getValueCast! 6 := fun h => by
  rcases idx2 (hash (0 : Nat)) with h0 | h0
  · have := @h Nat (fun _ => Nat) _ _ _ ⟨⟨1, #[.nil, .cons 0 1 .nil]⟩, by decide⟩ 0 _
    simp [Raw₀.get!, mkIdx_size2, h0] at this
    exact absurd this (by decide)
  · have := @h Nat (fun _ => Nat) _ _ _ ⟨⟨1, #[.cons 0 1 .nil, .nil]⟩, by decide⟩ 0 _
    simp [Raw₀.get!, mkIdx_size2, h0] at this
    exact absurd this (by decide)

-- `Std.DHashMap.Internal.Raw₀.getKey!_eq_getKey!`: two buckets, entry 1 ↦ 0 placed in the wrong bucket: getKey! 1 = default 0, model gives 1.
theorem DHashMap_Internal_Raw0_getKeyB_eq_getKeyB_h8 : ¬ drop0% Std.DHashMap.Internal.Raw₀.getKey!_eq_getKey! 8 := fun h => by
  rcases idx2 (hash (1 : Nat)) with h0 | h0
  · have := @h Nat (fun _ => Nat) _ _ _ _ _ ⟨⟨1, #[.nil, .cons 1 0 .nil]⟩, by decide⟩ 1
    simp [Raw₀.getKey!, mkIdx_size2, h0] at this
    exact absurd this (by decide)
  · have := @h Nat (fun _ => Nat) _ _ _ _ _ ⟨⟨1, #[.cons 1 0 .nil, .nil]⟩, by decide⟩ 1
    simp [Raw₀.getKey!, mkIdx_size2, h0] at this
    exact absurd this (by decide)

-- `Std.DHashMap.Internal.Raw₀.contains_of_mem_keysArray`: two buckets, entry 0 ↦ 1 in the wrong bucket: 0 ∈ keysArray, contains 0 = false.
theorem DHashMap_Internal_Raw0_contains_of_mem_keysArray_h7 : ¬ drop0% Std.DHashMap.Internal.Raw₀.contains_of_mem_keysArray 7 := fun h => by
  rcases idx2 (hash (0 : Nat)) with h0 | h0
  · have := @h Nat (fun _ => Nat) ⟨⟨1, #[.nil, .cons 0 1 .nil]⟩, by decide⟩ _ _ _ _ 0 (by decide +kernel)
    simp [Raw₀.contains, mkIdx_size2, h0] at this
  · have := @h Nat (fun _ => Nat) ⟨⟨1, #[.cons 0 1 .nil, .nil]⟩, by decide⟩ _ _ _ _ 0 (by decide +kernel)
    simp [Raw₀.contains, mkIdx_size2, h0] at this

-- `Std.DHashMap.Internal.Raw₀.Const.toListModel_modify`: two buckets, entry 0 ↦ 1 in the wrong bucket: modify 0 (· + 1) changes nothing, the model modifies.
theorem DHashMap_Internal_Raw0_Const_toListModel_modify_h7 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.toListModel_modify 7 := fun h => by
  rcases idx2 (hash (0 : Nat)) with h0 | h0
  · have := @h Nat Nat ⟨⟨1, #[.nil, .cons 0 1 .nil]⟩, by decide⟩ _ _ _ _ 0 (· + 1)
    simp [Raw₀.Const.modify, mkIdx_size2, h0] at this
    exact absurd this (by decide)
  · have := @h Nat Nat ⟨⟨1, #[.cons 0 1 .nil, .nil]⟩, by decide⟩ _ _ _ _ 0 (· + 1)
    simp [Raw₀.Const.modify, mkIdx_size2, h0] at this
    exact absurd this (by decide)

-- `Std.DHashMap.Internal.Raw₀.toListModel_modify`: two buckets, entry 0 ↦ 1 in the wrong bucket: modify 0 (· + 1) changes nothing, the model modifies.
theorem DHashMap_Internal_Raw0_toListModel_modify_h6 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_modify 6 := fun h => by
  rcases idx2 (hash (0 : Nat)) with h0 | h0
  · have := @h Nat (fun _ => Nat) _ _ _ ⟨⟨1, #[.nil, .cons 0 1 .nil]⟩, by decide⟩ 0 (· + 1)
    simp [Raw₀.modify, mkIdx_size2, h0] at this
    exact absurd this (by decide)
  · have := @h Nat (fun _ => Nat) _ _ _ ⟨⟨1, #[.cons 0 1 .nil, .nil]⟩, by decide⟩ 0 (· + 1)
    simp [Raw₀.modify, mkIdx_size2, h0] at this
    exact absurd this (by decide)

-- `Std.DHashMap.Internal.Raw₀.Const.wfImp_getThenInsertIfNew?`: one empty bucket with size field 5: after inserting 0 the size is 6 but the model has 1 entry.
theorem DHashMap_Internal_Raw0_Const_wfImp_getThenInsertIfNewQ_h9 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.wfImp_getThenInsertIfNew? 9 := fun h => by
  have := (@h Nat Nat _ _ _ _ ⟨⟨5, #[.nil]⟩, by decide⟩ 0 0).size_eq
  simp [Raw₀.Const.getThenInsertIfNew?, mkIdx_size1] at this
  rw [(Raw₀.toListModel_expandIfNecessary _).length_eq] at this
  exact absurd this (by decide)

-- `Std.DHashMap.Internal.Raw₀.wfImp_erase`: one empty bucket with size field 5: erase 0 keeps size 5 with an empty model.
theorem DHashMap_Internal_Raw0_wfImp_erase_h8 : ¬ drop0% Std.DHashMap.Internal.Raw₀.wfImp_erase 8 := fun h => by
  have := (@h Nat (fun _ => Nat) _ _ _ _ ⟨⟨5, #[.nil]⟩, by decide⟩ 0).size_eq
  simp [Raw₀.erase, mkIdx_size1] at this
  exact absurd this (by decide)

-- `Std.DHashMap.Internal.Raw₀.isHashSelf_reinsertAux`: two buckets, entry 0 ↦ 1 in the wrong bucket: reinserting 0 leaves the stale entry, so not hash-self.
theorem DHashMap_Internal_Raw0_isHashSelf_reinsertAux_h9 : ¬ drop0% Std.DHashMap.Internal.Raw₀.isHashSelf_reinsertAux 9 := fun h => by
  rcases idx2 (hash (0 : Nat)) with h0 | h0
  · have := @h Nat (fun _ => Nat) _ _ _ _ ⟨#[.nil, .cons 0 1 .nil], by decide⟩ 0 0
    simp [Raw₀.reinsertAux, mkIdx_size2, h0] at this
    have := (this.hashes_to 1 (by simp)).hash_self (by simp) ⟨0, 1⟩ (by simp)
    simp [mkIdx_size2, h0] at this
  · have := @h Nat (fun _ => Nat) _ _ _ _ ⟨#[.cons 0 1 .nil, .nil], by decide⟩ 0 0
    simp [Raw₀.reinsertAux, mkIdx_size2, h0] at this
    have := (this.hashes_to 0 (by simp)).hash_self (by simp) ⟨0, 1⟩ (by simp)
    simp [mkIdx_size2, h0] at this

-- `Std.DHashMap.Internal.Raw₀.toListModel_diff`: m₁ = one bucket {0 ↦ 0}, m₂ = two buckets with 0 ↦ 1 in the wrong bucket: diff keeps 0 (contains fails), the model removes it.
theorem DHashMap_Internal_Raw0_toListModel_diff_h9 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_diff 9 := fun h => by
  rcases idx2 (hash (0 : Nat)) with h0 | h0
  · have := @h Nat (fun _ => Nat) _ _ _ _ ⟨⟨1, #[.cons 0 0 .nil]⟩, by decide⟩ ⟨⟨1, #[.nil, .cons 0 1 .nil]⟩, by decide⟩ wf_single
    simp [Raw₀.diff, Raw₀.filter, Raw₀.contains, toListModel, mkIdx_size2, h0] at this
    have := (AssocList.toList_filter.symm.trans (List.Perm.of_eq this)).eq_nil
    simp [mkIdx_size2, h0] at this
  · have := @h Nat (fun _ => Nat) _ _ _ _ ⟨⟨1, #[.cons 0 0 .nil]⟩, by decide⟩ ⟨⟨1, #[.cons 0 1 .nil, .nil]⟩, by decide⟩ wf_single
    simp [Raw₀.diff, Raw₀.filter, Raw₀.contains, toListModel, mkIdx_size2, h0] at this
    have := (AssocList.toList_filter.symm.trans (List.Perm.of_eq this)).eq_nil
    simp [mkIdx_size2, h0] at this

-- `Std.DHashMap.Internal.Raw₀.toListModel_interSmallerFnₘ`: m = sofar = one empty bucket, l = [⟨0, 0⟩], k = 0: LHS model [] vs l.
theorem DHashMap_Internal_Raw0_toListModel_interSmallerFnm_h12 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_interSmallerFnₘ 12 := fun h => by
  have := @h Nat (fun _ => Nat) _ _ _ _ ⟨⟨0, #[.nil]⟩, by decide⟩ ⟨⟨0, #[.nil]⟩, by decide⟩ [⟨0, 0⟩] wf_empty1 wf_empty1 0
  simp [Raw₀.interSmallerFnₘ, Raw₀.getEntry?ₘ, bucket, mkIdx_size1] at this
  exact absurd this (by decide)

-- `Std.DHashMap.Internal.Raw₀.toListModel_interSmallerₘ`: m₁ = two buckets with 0 ↦ 1 in the wrong bucket, m₂ = {0 ↦ 0}: the lookup in m₁ fails, result empty; model gives [⟨0, 1⟩].
theorem DHashMap_Internal_Raw0_toListModel_interSmallerm_h8 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_interSmallerₘ 8 := fun h => by
  rcases idx2 (hash (0 : Nat)) with h0 | h0
  · have := @h Nat (fun _ => Nat) _ _ _ _ ⟨⟨1, #[.nil, .cons 0 1 .nil]⟩, by decide⟩ ⟨1, #[.cons 0 0 .nil]⟩
    simp [Raw₀.interSmallerₘ, DHashMap.Raw.fold, DHashMap.Raw.foldM, AssocList.foldlM, Raw₀.interSmallerFnₘ, Raw₀.getEntry?ₘ, bucket, mkIdx_size2, h0,
      Raw₀.toListModel_buckets_emptyWithCapacity] at this
    exact absurd this (by decide)
  · have := @h Nat (fun _ => Nat) _ _ _ _ ⟨⟨1, #[.cons 0 1 .nil, .nil]⟩, by decide⟩ ⟨1, #[.cons 0 0 .nil]⟩
    simp [Raw₀.interSmallerₘ, DHashMap.Raw.fold, DHashMap.Raw.foldM, AssocList.foldlM, Raw₀.interSmallerFnₘ, Raw₀.getEntry?ₘ, bucket, mkIdx_size2, h0,
      Raw₀.toListModel_buckets_emptyWithCapacity] at this
    exact absurd this (by decide)

-- `Std.DHashMap.Internal.Raw₀.Const.get!_eq_getValue!`: two buckets, entry 0 ↦ 1 placed in the bucket 0 does not hash to (case split on the index): get! 0 = 0, model gives 1.
theorem DHashMap_Internal_Raw0_Const_getB_eq_getValueB_h8 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.get!_eq_getValue! 8 := fun h => by
  rcases idx2 (hash (0 : Nat)) with h0 | h0
  · have := @h Nat Nat _ _ _ _ _ ⟨⟨1, #[.nil, .cons 0 1 .nil]⟩, by decide⟩ 0
    simp [Raw₀.Const.get!, mkIdx_size2, h0] at this
    exact absurd this (by decide)
  · have := @h Nat Nat _ _ _ _ _ ⟨⟨1, #[.cons 0 1 .nil, .nil]⟩, by decide⟩ 0
    simp [Raw₀.Const.get!, mkIdx_size2, h0] at this
    exact absurd this (by decide)

-- `Std.HashSet.instPureForInOfLawfulMonad`: forIn over the empty set in the counting monad W binds once per bucket, forIn over its (empty) toList does not.
theorem HashSet_instPureForInOfLawfulMonad_h5 : ¬ drop0% Std.HashSet.instPureForInOfLawfulMonad 5 := fun h => by
  have := (@h Nat inferInstance inferInstance W _).forIn_eq (∅ : HashSet Nat) 0 (fun _ d => pure (.yield d))
  exact absurd (congrArg Prod.fst this) (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.Const.beq_eq_beqModel`: removable; under `LawfulHashable` a key `== a` can only sit in `a`'s own bucket of a hash-self array, so bucket lookup equals model lookup without `PartialEquivBEq` (`getValue?_toListModel_bucket`), and sizes and `all` are read off the model.
theorem DHashMap_Internal_Raw0_Const_beq_eq_beqModel_h3 : drop% Std.DHashMap.Internal.Raw₀.Const.beq_eq_beqModel 3 := by
  intro α β _ _ _ _ m₁ m₂ h₁ h₂
  simp only [Raw₀.Const.beq, Std.Internal.List.Const.beqModel, h₁.size_eq, h₂.size_eq, Raw.all_eq_all_toListModel]
  congr 1
  apply List.all_congr rfl
  intro x
  rw [Raw₀.Const.get?_eq_get?ₘ, Raw₀.Const.get?ₘ, AssocList.get?_eq, ← getValue?_toListModel_bucket _ _ h₂.buckets_hash_self]
