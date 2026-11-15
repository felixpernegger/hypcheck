import Lean
import Std

/-!
Hand pass HashInst (hand14): 140 instance hypotheses [EquivBEq α] / [LawfulHashable α] of Std hash map/set
theorems (DHashMap internals, HashMap/HashSet, their Raw and Ext variants). For hypothesis i of theorem T each
declaration proves ¬T' (necessary, `¬ drop0% T i`) or T' (removable, `drop% T i`, universes kept).

99 necessary, 41 removable, 0 independent, 0 unresolved.

## Reusable toolkit (namespace HashInstHand; copy the section "Bucket arithmetic" to "Literal maps" and the
## macro hm_eval)

Bucket arithmetic, valid for numBits = 32 and 64 (no case split needed by users):
* mkIdx_toNat k (hk : k < 32): (mkIdx (2^k) h x).1.toNat = (scrambleHash x).toNat % 2^k.
* Pow2 n := n = 1 ∨ 2 ∨ 4 ∨ 8 ∨ 16 (decidable side condition); mkIdx_eq (rewrites mkIdx to an explicit
  USize.ofNat), mkIdx_toNat' (toNat form), idx_lt, usize_toNat_ofNat_small.
* scr_small: scrambleHash is the identity below 2^16, so a key with hash n < 2^16 lands in bucket n % size.
* The empty map has 16 buckets: nil16, raw0_empty_val, raw0_empty, dr_empty / dm_empty / hm_empty / hs_empty /
  hmr_empty / hsr_empty (the raw map under ∅ of each wrapper).

Evaluation of Raw₀ operations on a raw map with explicit buckets ⟨⟨s, bs⟩, h⟩ (side condition Pow2 bs.size):
contains_eval, insertIfNew_eval, insert_eval, erase_eval, getKey?_eval, getKey_eval, getKeyD_eval, getKey!_eval,
getEntry?_eval, cget?_eval, cgetD_eval, cget!_eval, cget_eval, calter_eval, cmodify_eval (Const versions),
expand_id (no resize while s*4/3 ≤ bs.size), forInStep_nil/cons, forIn_raw (for/all/any/fold over a raw map),
filter_0/1/2 (AssocList.filter on ≤ 2 entries), hm_getElem?/!, hmr_getElem?/!/getElem (m[a]? etc. unfolded),
hsr_ofList2 / hmr_ofList2, hs_union / hs_inter.
* Tactic hm_eval: unfolds the public operations (HashSet/HashMap/DHashMap and Raw variants: insert, insertIfNew,
  erase, contains, ∈, get?/get!/getD/get, getKey?/getKey!/getKeyD/getKey, m[a]?/m[a]!/m[a], alter, modify, size,
  isEmpty, toArray, keys, all, ofList, unitOfList, insertMany, ∪, ∩, ∅) to Raw₀ and evaluates them with the
  lemmas above plus the model simp lemmas. Typical use: `fun h => absurd (h (m := …) … proofs-by-hm_eval)
  (by hm_eval)`; see the examples after the macro.

Models (each its own structure on Nat, deriving DecidableEq and Inhabited, default ⟨0⟩):
| model | a == b              | hash a | EquivBEq | LawfulHashable | other                       |
|-------|---------------------|--------|----------|----------------|-----------------------------|
| NB    | false               | 0      | ✗        | ✓              | not reflexive               |
| AB    | true                | n      | ✓        | ✗              | keys 0 and 1 in buckets 0/1 |
| NS    | a ≤ b               | 0      | ✗        | ✓              | ReflBEq, transitive         |
| NT    | a ≤ b+1 ∧ b ≤ a+1   | 0      | ✗        | ✓              | ReflBEq, symmetric          |
Each has simp lemmas M.beq_def, M.hash_def, M.default_def and M.broken : ∀ [EquivBEq M] [LawfulHashable M], False.

Literal maps: since Raw.WF has the constructor wf (0 < size → (∀ [EquivBEq] [LawfulHashable], WFImp m) → WF m), in
a broken model EVERY raw map with buckets is well-formed (wf_vac). So counterexamples may use arbitrary size fields,
duplicate keys, or keys in the wrong bucket: hsr / hs / hmr / hm (HashSet.Raw / HashSet / HashMap.Raw / HashMap
from a size field and a bucket array; hs and hm take M.broken), hsr_wf / hmr_wf, b1 (one-entry bucket), NS4 / AB2
(small sets for union/intersection).

Instance-free facts (for removable proofs; the BEq of expand/toListModel/IsHashSelf is irrelevant, so lemmas
needing PartialEquivBEq or lawful instances are borrowed through falseBEq / hashBEq):
* tlm_expandIfNecessary, tlm_expand (perm), ihs_expand (IsHashSelf after a resize), ihs_congr.
* mem_tlm_insertIfNew / mem_tlm_insert (new entries are (a, b) or old), mem_tlm_set, mem_tlm_uset,
  mem_tlm_of_bucket, tlm_insertListIfNewUnit / tlm_insertList (invariants through ofList), hs_ofList_keys,
  hm_ofList_entries, hsr_ofList_keys, hmr_ofList_entries, hs/hm/hsr/hmr_ofList_raw (ofList as insertList on 16
  empty buckets), raw0_getKey?_some, raw0_cget?_some, raw0_getKey_mem, raw0_cget_mem (a found key is a stored entry
  with key == query), raw0_contains_false, raw0_size_insert(IfNew)(_of), size_insertList(IfNewUnit)_le/_eq,
  tlm_insert(IfNew)_ne_nil, contains_of_mem_ihs, contains_expand_cons, raw0_contains_insert(IfNew)_self,
  raw0_contains_cmodify, pw_unique (in a list without ==-related pairs, ==-related members are equal).

## Verdicts
* Necessary (99): EquivBEq rows refuted with NB/NS/NT, LawfulHashable rows with AB, mostly on literal maps (size
  field 1 without keys, a key in the wrong bucket, two keys in one bucket), or on ofList/∅ maps evaluated by hm_eval;
  union/intersection rows use the size-dependent branch choice (filter vs interSmaller) and NS's asymmetry.
  Raw₀.Const.beq_eq_beqModel uses genuinely well-formed AB maps (WFImp proved).
* Removable (41): isSome_get?/getElem?_iff_mem (any instances), ExtHashSet.emptyWithCapacity_eq, size_le_size_
  insertMany, size_ofList(_le), filterMap_equiv_map, ExtHashSet/ExtHashMap.ofList_eq_empty_iff (any instances);
  with EquivBEq kept: the ..._ofList_of_contains_eq_false getters, get/getKey/getElem_ofList_of_mem (Raw),
  mem_insert_self (Raw), HashMap.Raw.mem_modify; with LawfulHashable kept: Raw₀.toListModel_containsThenInsert;
  Raw₀.wfImp_filter without LawfulHashable.

Run with the lean4 repo's stage1 binary (`runs/hand14/lean.sh checks/HashInstHand.lean`, ~15 s).
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

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

open Std Std.DHashMap.Internal

namespace HashInstHand

/-! ## Bucket arithmetic (valid for `numBits = 32` and `64`) -/

universe u v w w'

theorem mkIdx_toNat (k : Nat) (hk : k < 32) (h : 0 < 2^k) (x : UInt64) :
    (mkIdx (2^k) h x).1.toNat = (scrambleHash x).toNat % 2^k := by
  have hs : 2^k < USize.size := by
    have : 2^k < 2^32 := Nat.pow_lt_pow_right (by decide) hk
    have := USize.le_size; omega
  have h1 : 1 ≤ 2^k := h
  unfold mkIdx
  simp only
  rw [USize.toNat_and, USize.toNat_sub_of_le, USize.toNat_ofNat_of_lt' hs]
  · simp only [UInt64.toNat_toUSize, USize.toNat_one]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    cases System.Platform.numBits_eq with
    | inl h' => rw [h']; exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
    | inr h' => rw [h']; exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
  · simp [USize.le_iff_toNat_le, Nat.mod_eq_of_lt hs]; omega

theorem usize_toNat_ofNat_small (c : Nat) (h : c < 4294967296) : (USize.ofNat c).toNat = c :=
  USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le h USize.le_size)

/-- Bucket counts the toolkit evaluates (the initial count is 16). -/
abbrev Pow2 (n : Nat) : Prop := n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16

theorem idx_lt {n : Nat} (h : 0 < n) (x : UInt64) (hsz : Pow2 n) :
    (USize.ofNat ((scrambleHash x).toNat % n)).toNat = (scrambleHash x).toNat % n :=
  usize_toNat_ofNat_small _ (by have := Nat.mod_lt (scrambleHash x).toNat h; omega)

theorem mkIdx_eq (sz : Nat) (h : 0 < sz) (x : UInt64) (hsz : Pow2 sz) :
    mkIdx sz h x = ⟨USize.ofNat ((scrambleHash x).toNat % sz), by
      rw [idx_lt h x hsz]; exact Nat.mod_lt _ h⟩ := by
  apply Subtype.ext
  apply USize.toNat_inj.mp
  rw [idx_lt h x hsz]
  rcases hsz with rfl | rfl | rfl | rfl | rfl
  · exact mkIdx_toNat 0 (by decide) h x
  · exact mkIdx_toNat 1 (by decide) h x
  · exact mkIdx_toNat 2 (by decide) h x
  · exact mkIdx_toNat 3 (by decide) h x
  · exact mkIdx_toNat 4 (by decide) h x

theorem mkIdx_toNat' (sz : Nat) (h : 0 < sz) (x : UInt64) (hsz : Pow2 sz) :
    (mkIdx sz h x).1.toNat = (scrambleHash x).toNat % sz := by
  rw [mkIdx_eq _ _ _ hsz]; exact idx_lt h x hsz

/-- `scrambleHash` is the identity on hashes below `2^16`. -/
theorem scr_small (x : UInt64) (h : x.toNat < 65536) : (scrambleHash x).toNat = x.toNat := by
  have h1 : x >>> 32 = 0 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    simp; omega
  have h2 : x >>> 16 = 0 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    simp; omega
  simp [scrambleHash, h1, h2]

/-! ## Evaluating `Raw₀` operations on a raw map with explicit buckets -/

section Eval
variable {α : Type u} {β : α → Type v}

/-- Index of the bucket of `a` in `bs`. -/
abbrev ix [Hashable α] (bs : Array (AssocList α β)) (a : α) : Nat := (scrambleHash (hash a)).toNat % bs.size

theorem contains_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size}
    (a : α) (hsz : Pow2 bs.size) :
    Raw₀.contains (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a = (bs[ix bs a]'(Nat.mod_lt _ h)).contains a := by
  unfold Raw₀.contains; dsimp only; rw [mkIdx_eq _ _ _ hsz]
  simp only [Array.ugetElem_eq_getElem, idx_lt h _ hsz]

theorem insertIfNew_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size}
    (a : α) (b : β a) (hsz : Pow2 bs.size) :
    Raw₀.insertIfNew (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a b =
      if (bs[ix bs a]'(Nat.mod_lt _ h)).contains a then ⟨⟨s, bs⟩, h⟩
      else Raw₀.expandIfNecessary ⟨⟨s + 1, bs.set (ix bs a)
        (AssocList.cons a b (bs[ix bs a]'(Nat.mod_lt _ h))) (Nat.mod_lt _ h)⟩, by simpa using h⟩ := by
  unfold Raw₀.insertIfNew; dsimp only; rw [mkIdx_eq _ _ _ hsz]
  simp only [Array.ugetElem_eq_getElem, Array.uset_eq_set, idx_lt h _ hsz]

theorem insert_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size}
    (a : α) (b : β a) (hsz : Pow2 bs.size) :
    Raw₀.insert (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a b =
      if (bs[ix bs a]'(Nat.mod_lt _ h)).contains a then
        ⟨⟨s, bs.set (ix bs a) ((bs[ix bs a]'(Nat.mod_lt _ h)).replace a b) (Nat.mod_lt _ h)⟩, by simpa using h⟩
      else Raw₀.expandIfNecessary ⟨⟨s + 1, bs.set (ix bs a)
        (AssocList.cons a b (bs[ix bs a]'(Nat.mod_lt _ h))) (Nat.mod_lt _ h)⟩, by simpa using h⟩ := by
  unfold Raw₀.insert; dsimp only; rw [mkIdx_eq _ _ _ hsz]
  simp only [Array.ugetElem_eq_getElem, Array.uset_eq_set, idx_lt h _ hsz, Array.set_set]

theorem erase_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size}
    (a : α) (hsz : Pow2 bs.size) :
    Raw₀.erase (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a =
      if (bs[ix bs a]'(Nat.mod_lt _ h)).contains a then
        ⟨⟨s - 1, bs.set (ix bs a) ((bs[ix bs a]'(Nat.mod_lt _ h)).erase a) (Nat.mod_lt _ h)⟩, by simpa using h⟩
      else ⟨⟨s, bs⟩, h⟩ := by
  unfold Raw₀.erase; dsimp only; rw [mkIdx_eq _ _ _ hsz]
  simp only [Array.ugetElem_eq_getElem, Array.uset_eq_set, idx_lt h _ hsz, Array.set_set]

theorem getKey?_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size}
    (a : α) (hsz : Pow2 bs.size) :
    Raw₀.getKey? (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a = (bs[ix bs a]'(Nat.mod_lt _ h)).getKey? a := by
  unfold Raw₀.getKey?; dsimp only; rw [mkIdx_eq _ _ _ hsz]
  simp only [Array.ugetElem_eq_getElem, idx_lt h _ hsz]

theorem getKey_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size}
    (a : α) (hsz : Pow2 bs.size) (hc) :
    Raw₀.getKey (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a hc =
      (bs[ix bs a]'(Nat.mod_lt _ h)).getKey a (by rw [← contains_eval a hsz]; exact hc) := by
  simp only [Raw₀.getKey, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]

theorem getKeyD_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size}
    (a fb : α) (hsz : Pow2 bs.size) :
    Raw₀.getKeyD (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a fb = (bs[ix bs a]'(Nat.mod_lt _ h)).getKeyD a fb := by
  simp only [Raw₀.getKeyD, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]

theorem getKey!_eval [BEq α] [Hashable α] [Inhabited α] {s : Nat} {bs : Array (AssocList α β)}
    {h : 0 < bs.size} (a : α) (hsz : Pow2 bs.size) :
    Raw₀.getKey! (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a = (bs[ix bs a]'(Nat.mod_lt _ h)).getKey! a := by
  simp only [Raw₀.getKey!, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]

section Const
variable {γ : Type v}

theorem cget?_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α (fun _ => γ))} {h : 0 < bs.size}
    (a : α) (hsz : Pow2 bs.size) :
    Raw₀.Const.get? (⟨⟨s, bs⟩, h⟩ : Raw₀ α (fun _ => γ)) a = (bs[ix bs a]'(Nat.mod_lt _ h)).get? a := by
  unfold Raw₀.Const.get?; dsimp only; rw [mkIdx_eq _ _ _ hsz]
  simp only [Array.ugetElem_eq_getElem, idx_lt h _ hsz]

theorem cgetD_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α (fun _ => γ))} {h : 0 < bs.size}
    (a : α) (fb : γ) (hsz : Pow2 bs.size) :
    Raw₀.Const.getD (⟨⟨s, bs⟩, h⟩ : Raw₀ α (fun _ => γ)) a fb = (bs[ix bs a]'(Nat.mod_lt _ h)).getD a fb := by
  simp only [Raw₀.Const.getD, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]

theorem cget!_eval [BEq α] [Hashable α] [Inhabited γ] {s : Nat} {bs : Array (AssocList α (fun _ => γ))}
    {h : 0 < bs.size} (a : α) (hsz : Pow2 bs.size) :
    Raw₀.Const.get! (⟨⟨s, bs⟩, h⟩ : Raw₀ α (fun _ => γ)) a = (bs[ix bs a]'(Nat.mod_lt _ h)).get! a := by
  simp only [Raw₀.Const.get!, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]

theorem cget_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α (fun _ => γ))} {h : 0 < bs.size}
    (a : α) (hsz : Pow2 bs.size) (hc) :
    Raw₀.Const.get (⟨⟨s, bs⟩, h⟩ : Raw₀ α (fun _ => γ)) a hc =
      (bs[ix bs a]'(Nat.mod_lt _ h)).get a (by rw [← contains_eval a hsz]; exact hc) := by
  simp only [Raw₀.Const.get, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]

theorem calter_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α (fun _ => γ))} {h : 0 < bs.size}
    (a : α) (f : Option γ → Option γ) (hsz : Pow2 bs.size) :
    Raw₀.Const.alter (⟨⟨s, bs⟩, h⟩ : Raw₀ α (fun _ => γ)) a f =
      if (bs[ix bs a]'(Nat.mod_lt _ h)).contains a then
        ⟨⟨if (AssocList.Const.alter a f (bs[ix bs a]'(Nat.mod_lt _ h))).contains a then s else s - 1,
          bs.set (ix bs a) (AssocList.Const.alter a f (bs[ix bs a]'(Nat.mod_lt _ h))) (Nat.mod_lt _ h)⟩,
          by simpa using h⟩
      else match f none with
        | none => ⟨⟨s, bs⟩, h⟩
        | some b => Raw₀.expandIfNecessary ⟨⟨s + 1, bs.set (ix bs a)
            (AssocList.cons a b (bs[ix bs a]'(Nat.mod_lt _ h))) (Nat.mod_lt _ h)⟩, by simpa using h⟩ := by
  unfold Raw₀.Const.alter; dsimp only; rw [mkIdx_eq _ _ _ hsz]
  simp only [Array.ugetElem_eq_getElem, Array.uset_eq_set, idx_lt h _ hsz, Array.set_set]
  rfl

theorem cmodify_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α (fun _ => γ))} {h : 0 < bs.size}
    (a : α) (f : γ → γ) (hsz : Pow2 bs.size) :
    Raw₀.Const.modify (⟨⟨s, bs⟩, h⟩ : Raw₀ α (fun _ => γ)) a f =
      if (bs[ix bs a]'(Nat.mod_lt _ h)).contains a then
        ⟨⟨s, bs.set (ix bs a) (AssocList.Const.modify a f (bs[ix bs a]'(Nat.mod_lt _ h))) (Nat.mod_lt _ h)⟩,
          by simpa using h⟩
      else ⟨⟨s, bs⟩, h⟩ := by
  unfold Raw₀.Const.modify; dsimp only; rw [mkIdx_eq _ _ _ hsz]
  simp only [Array.ugetElem_eq_getElem, Array.uset_eq_set, idx_lt h _ hsz, Array.set_set]

end Const

theorem getEntry?_eval [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size}
    (a : α) (hsz : Pow2 bs.size) :
    Raw₀.getEntry? (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a = (bs[ix bs a]'(Nat.mod_lt _ h)).getEntry? a := by
  simp only [Raw₀.getEntry?, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]

theorem filter_0 (f : (a : α) → β a → Bool) : AssocList.filter f .nil = .nil := rfl
theorem filter_1 (f : (a : α) → β a → Bool) (k : α) (v : β k) :
    AssocList.filter f (.cons k v .nil) = bif f k v then .cons k v .nil else .nil := by
  show (bif f k v then _ else _) = _; cases f k v <;> rfl
theorem filter_2 (f : (a : α) → β a → Bool) (k : α) (v : β k) (k' : α) (v' : β k') :
    AssocList.filter f (.cons k v (.cons k' v' .nil)) =
      bif f k' v' then .cons k' v' (bif f k v then .cons k v .nil else .nil)
      else (bif f k v then .cons k v .nil else .nil) := by
  show (bif f k v then _ else _) = _; cases f k v <;> (show (bif f k' v' then _ else _) = _; cases f k' v' <;> rfl)

theorem forInStep_nil {δ : Type w} {m : Type w → Type w'} [Monad m] (init : δ)
    (f : (a : α) → β a → δ → m (ForInStep δ)) :
    (AssocList.nil : AssocList α β).forInStep init f = pure (.yield init) := rfl

theorem forInStep_cons {δ : Type w} {m : Type w → Type w'} [Monad m] (k : α) (v : β k) (t : AssocList α β)
    (init : δ) (f : (a : α) → β a → δ → m (ForInStep δ)) :
    (AssocList.cons k v t).forInStep init f = (do
      match ← f k v init with
      | .done d => pure (.done d)
      | .yield d => t.forInStep d f) := rfl

theorem forIn_raw {δ : Type w} {m : Type w → Type w'} [Monad m] (r : DHashMap.Raw α β) (init : δ)
    (f : (a : α) × β a → δ → m (ForInStep δ)) :
    forIn r init f = ForIn.forIn r.buckets init (fun bucket acc => bucket.forInStep acc (fun a b acc => f ⟨a, b⟩ acc)) :=
  rfl

theorem expand_id [BEq α] [Hashable α] (s : Nat) (bs : Array (AssocList α β)) (hm)
    (h : s * 4 / 3 ≤ bs.size) : Raw₀.expandIfNecessary (⟨⟨s, bs⟩, hm⟩ : Raw₀ α β) = ⟨⟨s, bs⟩, hm⟩ := by
  unfold Raw₀.expandIfNecessary; dsimp only; rw [ite_eq_left_iff.mpr]; intro h'; exact absurd h h'

end Eval

/-! ## The empty map: 16 empty buckets -/

section Empty
variable {α : Type u} {β : α → Type v}

/-- 16 empty buckets. -/
abbrev nil16 : Array (AssocList α β) :=
  #[.nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil]

theorem raw0_empty_val : (Raw₀.emptyWithCapacity 8 : Raw₀ α β).1 = ⟨0, nil16⟩ := by
  have : Nat.nextPowerOfTwo 10 = 16 := by decide +kernel
  show DHashMap.Raw.mk 0 (Array.replicate (Nat.nextPowerOfTwo (8*4/3)) .nil) = _
  rw [show 8*4/3 = 10 by rfl, this]; rfl

theorem raw0_empty : (Raw₀.emptyWithCapacity 8 : Raw₀ α β) = ⟨⟨0, nil16⟩, by simp [nil16]⟩ :=
  Subtype.ext raw0_empty_val

theorem dr_empty [BEq α] [Hashable α] : (∅ : DHashMap.Raw α β) = ⟨0, nil16⟩ := raw0_empty_val
theorem dm_empty [BEq α] [Hashable α] : (∅ : DHashMap α β).inner = ⟨0, nil16⟩ := raw0_empty_val
theorem hm_empty {β : Type v} [BEq α] [Hashable α] : (∅ : HashMap α β).inner.inner = ⟨0, nil16⟩ :=
  raw0_empty_val
theorem hs_empty [BEq α] [Hashable α] : (∅ : HashSet α).inner.inner.inner = ⟨0, nil16⟩ := raw0_empty_val
theorem hmr_empty {β : Type v} [BEq α] [Hashable α] : (∅ : HashMap.Raw α β).inner = ⟨0, nil16⟩ :=
  raw0_empty_val
theorem hsr_empty [BEq α] [Hashable α] : (∅ : HashSet.Raw α).inner.inner = ⟨0, nil16⟩ := raw0_empty_val

/-- Every raw map with buckets is well-formed when the instances are not both lawful. -/
theorem wf_vac [BEq α] [Hashable α] (hn : ∀ [EquivBEq α] [LawfulHashable α], False)
    (r : DHashMap.Raw α β) (h : 0 < r.buckets.size) : r.WF :=
  .wf h (fun {_ _} => hn.elim)

end Empty

/-! ## Models -/

/-- `NB`: `==` is always `false`, hash `0`. `LawfulHashable` ✓, `EquivBEq` ✗ (not reflexive). -/
structure NB where n : Nat deriving DecidableEq, Inhabited
instance : BEq NB := ⟨fun _ _ => false⟩
instance : Hashable NB := ⟨fun _ => 0⟩
instance : LawfulHashable NB := ⟨fun _ _ _ => rfl⟩
@[simp] theorem NB.beq_def (a b : NB) : (a == b) = false := rfl
@[simp] theorem NB.default_def : (default : NB) = ⟨0⟩ := rfl
@[simp] theorem NB.hash_def (a : NB) : hash a = 0 := rfl
theorem NB.broken : ∀ [EquivBEq NB] [LawfulHashable NB], False := fun {h _} => by
  exact Bool.false_ne_true ((NB.beq_def ⟨0⟩ ⟨0⟩).symm.trans (@ReflBEq.rfl NB _ _ ⟨0⟩))

/-- `AB`: `==` is always `true`, hash `n`. `EquivBEq` ✓, `LawfulHashable` ✗. -/
structure AB where n : Nat deriving DecidableEq, Inhabited
instance : BEq AB := ⟨fun _ _ => true⟩
instance : Hashable AB := ⟨fun a => UInt64.ofNat a.n⟩
instance : EquivBEq AB where
  symm _ := rfl
  trans _ _ := rfl
  rfl := rfl
@[simp] theorem AB.beq_def (a b : AB) : (a == b) = true := rfl
@[simp] theorem AB.default_def : (default : AB) = ⟨0⟩ := rfl
@[simp] theorem AB.hash_def (n : Nat) : hash (AB.mk n) = UInt64.ofNat n := rfl
theorem AB.broken : ∀ [EquivBEq AB] [LawfulHashable AB], False := fun {_ h} => by
  have := @LawfulHashable.hash_eq AB _ _ h ⟨0⟩ ⟨1⟩ rfl; simp at this

/-- `NS`: `a == b ↔ a ≤ b` (reflexive, transitive, not symmetric), hash `0`.
`LawfulHashable` ✓, `ReflBEq` ✓, `EquivBEq` ✗. -/
structure NS where n : Nat deriving DecidableEq, Inhabited
instance : BEq NS := ⟨fun a b => decide (a.n ≤ b.n)⟩
instance : Hashable NS := ⟨fun _ => 0⟩
instance : LawfulHashable NS := ⟨fun _ _ _ => rfl⟩
instance : ReflBEq NS := ⟨by intro a; show decide (a.n ≤ a.n) = true; simp⟩
@[simp] theorem NS.beq_def (a b : Nat) : (NS.mk a == NS.mk b) = decide (a ≤ b) := rfl
@[simp] theorem NS.default_def : (default : NS) = ⟨0⟩ := rfl
@[simp] theorem NS.hash_def (a : NS) : hash a = 0 := rfl
theorem NS.broken : ∀ [EquivBEq NS] [LawfulHashable NS], False := fun {h _} => by
  have := @PartialEquivBEq.symm NS _ _ ⟨0⟩ ⟨1⟩ rfl; simp at this

/-- `NT`: `a == b ↔ |a - b| ≤ 1` (reflexive, symmetric, not transitive), hash `0`.
`LawfulHashable` ✓, `ReflBEq` ✓, `EquivBEq` ✗. -/
structure NT where n : Nat deriving DecidableEq, Inhabited
instance : BEq NT := ⟨fun a b => decide (a.n ≤ b.n + 1 ∧ b.n ≤ a.n + 1)⟩
instance : Hashable NT := ⟨fun _ => 0⟩
instance : LawfulHashable NT := ⟨fun _ _ _ => rfl⟩
instance : ReflBEq NT := ⟨by intro a; show decide _ = true; simp⟩
@[simp] theorem NT.beq_def (a b : Nat) : (NT.mk a == NT.mk b) = decide (a ≤ b + 1 ∧ b ≤ a + 1) := rfl
@[simp] theorem NT.default_def : (default : NT) = ⟨0⟩ := rfl
@[simp] theorem NT.hash_def (a : NT) : hash a = 0 := rfl
theorem NT.broken : ∀ [EquivBEq NT] [LawfulHashable NT], False := fun {h _} => by
  have := @PartialEquivBEq.trans NT _ _ ⟨0⟩ ⟨1⟩ ⟨2⟩ rfl rfl; simp at this

section Unfold
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
theorem hm_getElem? (m : HashMap α β) (a : α) : m[a]? = DHashMap.Const.get? m.inner a := rfl
theorem hm_getElem! [Inhabited β] (m : HashMap α β) (a : α) : m[a]! = DHashMap.Const.get! m.inner a := rfl
theorem hmr_getElem? (m : HashMap.Raw α β) (a : α) : m[a]? = DHashMap.Raw.Const.get? m.inner a := rfl
theorem hmr_getElem! [Inhabited β] (m : HashMap.Raw α β) (a : α) : m[a]! = DHashMap.Raw.Const.get! m.inner a := rfl
theorem hmr_getElem (m : HashMap.Raw α β) (a : α) (h : a ∈ m) :
    m[a]'h = DHashMap.Raw.Const.get m.inner a h := rfl
theorem hsr_ofList2 (a b : α) : HashSet.Raw.ofList [a, b] = ((∅ : HashSet.Raw α).insert a).insert b := by
  rw [HashSet.Raw.ofList_cons, HashSet.Raw.insertMany_list_singleton (.insert .empty)]
theorem hmr_ofList2 (a b : α) (x y : β) :
    HashMap.Raw.ofList [(a, x), (b, y)] = ((∅ : HashMap.Raw α β).insert a x).insert b y := by
  rw [HashMap.Raw.ofList_cons, HashMap.Raw.insertMany_list_singleton (.insert .empty)]
theorem hs_union (m₁ m₂ : HashSet α) : m₁ ∪ m₂ = HashSet.union m₁ m₂ := rfl
theorem hs_inter (m₁ m₂ : HashSet α) : m₁ ∩ m₂ = HashSet.inter m₁ m₂ := rfl
end Unfold

/-- Unfold the public operations to `Raw₀` ones and evaluate them on explicit buckets. -/
macro "hm_eval" : tactic => `(tactic| (
  try simp only [HashSet.ofList_cons, HashSet.ofList_singleton, HashSet.insertMany_cons, HashSet.insertMany_nil,
    HashMap.ofList_cons, HashMap.ofList_singleton, HashMap.insertMany_cons, HashMap.insertMany_nil,
    HashMap.unitOfList_cons, HashMap.unitOfList_singleton, HashMap.insertManyIfNewUnit_cons,
    HashMap.insertManyIfNewUnit_nil, HashSet.Raw.ofList_singleton, HashMap.Raw.ofList_singleton, hsr_ofList2,
    hmr_ofList2]
  try simp only [hs_union, hs_inter, HashSet.union, HashSet.inter, HashMap.union, HashMap.inter, DHashMap.union,
    DHashMap.inter, Raw₀.union, Raw₀.inter, Array.set!]
  try simp only [HashSet.insert, HashSet.contains, HashSet.erase, HashSet.get?, HashSet.size, HashSet.isEmpty,
    HashSet.Raw.insert, HashSet.Raw.contains, HashSet.Raw.erase, HashSet.Raw.get?, HashSet.Raw.size,
    HashSet.Raw.isEmpty, HashSet.Raw.toArray, HashSet.Raw.all, HashMap.Raw.all, HashSet.Raw.get, HashMap.Raw.getKey, DHashMap.Raw.getKey, DHashMap.Raw.forIn, HashMap.Raw.keysArray, HashSet.toArray, HashMap.keysArray, DHashMap.keysArray,
    HashMap.insertIfNew, HashMap.insert, HashMap.contains, HashMap.erase, HashMap.size, HashMap.isEmpty,
    HashMap.Raw.insertIfNew, HashMap.Raw.insert, HashMap.Raw.contains, HashMap.Raw.erase, HashMap.Raw.size,
    HashMap.Raw.isEmpty,
    DHashMap.insertIfNew, DHashMap.insert, DHashMap.contains, DHashMap.erase, DHashMap.size, DHashMap.isEmpty,
    DHashMap.Raw.insertIfNew, DHashMap.Raw.insert, DHashMap.Raw.contains, DHashMap.Raw.erase,
    DHashMap.Raw.isEmpty, DHashMap.Raw.keysArray, DHashMap.Raw.all,
    HashSet.get!, HashSet.getD, HashSet.Raw.get!, HashSet.Raw.getD, HashSet.get, HashMap.getKey?, HashMap.getKey!,
    HashMap.getKeyD, HashMap.getKey, HashMap.getD, HashMap.get?, HashMap.get!, HashMap.alter, HashMap.modify,
    HashMap.Raw.getKey?, HashMap.Raw.getKey!, HashMap.Raw.getKeyD, HashMap.Raw.getD, HashMap.Raw.get?,
    HashMap.Raw.get!, HashMap.Raw.alter, HashMap.Raw.modify, HashMap.keysArray, HashMap.Raw.keys,
    DHashMap.getKey?, DHashMap.getKey!, DHashMap.getKeyD, DHashMap.getKey, DHashMap.Const.get?, DHashMap.Const.get!,
    DHashMap.Const.getD, DHashMap.Const.alter, DHashMap.Const.modify, DHashMap.Raw.getKey?, DHashMap.Raw.getKey!,
    DHashMap.Raw.getKeyD, DHashMap.Raw.Const.get?, DHashMap.Raw.Const.get!, DHashMap.Raw.Const.getD,
    DHashMap.Raw.Const.alter, DHashMap.Raw.Const.modify, hm_getElem?, hm_getElem!, hmr_getElem?, hmr_getElem!, hmr_getElem, DHashMap.Raw.Const.get,
    HashMap.Raw.toArray, DHashMap.Raw.Const.toArray, DHashMap.Raw.toArray,
    HashSet.mem_iff_contains, HashSet.Raw.mem_iff_contains, HashMap.mem_iff_contains,
    HashMap.Raw.mem_iff_contains, DHashMap.mem_iff_contains, DHashMap.Raw.mem_iff_contains,
    hs_empty, hm_empty, dm_empty, hsr_empty, hmr_empty, dr_empty]
  simp (disch := first | decide | simp) [contains_eval, insertIfNew_eval, insert_eval, erase_eval,
    getKey?_eval, getKey_eval, getKeyD_eval, getKey!_eval, cget?_eval, cgetD_eval, cget!_eval,
    cget_eval, calter_eval, cmodify_eval, getEntry?_eval, raw0_empty, Raw₀.insertMany, Raw₀.insertManyIfNew,
    Raw₀.filter, Raw₀.interSmaller, Raw₀.interSmallerFn, computeSize, filter_0, filter_1, filter_2,
    AssocList.getEntry?, AssocList.get?, AssocList.getD, AssocList.get!, AssocList.getKeyD,
    AssocList.getKey!, AssocList.Const.alter, AssocList.Const.modify, expand_id, forInStep_nil, forInStep_cons, AssocList.getKey, forIn_raw,
    Std.Internal.List.getKey, Std.Internal.List.getKey?, Std.Internal.List.containsKey,
    Std.Internal.List.getValue?, Std.Internal.List.getValue!, Std.Internal.List.getValueD, Std.Internal.List.getKey!,
    Std.Internal.List.getKeyD, Std.Internal.List.getValue, Std.Internal.List.getEntry?, ix, nil16, scr_small, AssocList.contains, AssocList.getKey?, AssocList.replace, AssocList.erase,
    DHashMap.Raw.fold, DHashMap.Raw.foldM, AssocList.foldl, AssocList.foldlM, DHashMap.Raw.keys,
    DHashMap.Raw.Internal.foldRev, DHashMap.Raw.Internal.foldRevM, AssocList.foldrM, AssocList.foldr, toListModel]))

/-! ## Literal maps (well-formed by `wf_vac` in the broken models) -/

section Lit
variable {α : Type u}

/-- A one-key bucket. -/
abbrev b1 {β : Type v} (k : α) (v : β) : AssocList α (fun _ => β) := .cons k v .nil

/-- Hash set (raw / bundled) with size field `s` and buckets `bs`. -/
abbrev hsr (s : Nat) (bs : Array (AssocList α (fun _ => Unit))) : HashSet.Raw α := ⟨⟨⟨s, bs⟩⟩⟩
abbrev hs [BEq α] [Hashable α] (hn : ∀ [EquivBEq α] [LawfulHashable α], False)
    (s : Nat) (bs : Array (AssocList α (fun _ => Unit))) (h : 0 < bs.size) : HashSet α :=
  ⟨⟨⟨⟨s, bs⟩, wf_vac hn _ h⟩⟩⟩
theorem hsr_wf [BEq α] [Hashable α] (hn : ∀ [EquivBEq α] [LawfulHashable α], False)
    (s : Nat) (bs : Array (AssocList α (fun _ => Unit))) (h : 0 < bs.size) : (hsr s bs).WF :=
  ⟨⟨wf_vac hn _ h⟩⟩

/-- Hash map (raw / bundled) with size field `s` and buckets `bs`. -/
abbrev hmr {β : Type v} (s : Nat) (bs : Array (AssocList α (fun _ => β))) : HashMap.Raw α β := ⟨⟨s, bs⟩⟩
abbrev hm {β : Type v} [BEq α] [Hashable α] (hn : ∀ [EquivBEq α] [LawfulHashable α], False)
    (s : Nat) (bs : Array (AssocList α (fun _ => β))) (h : 0 < bs.size) : HashMap α β :=
  ⟨⟨⟨s, bs⟩, wf_vac hn _ h⟩⟩
theorem hmr_wf {β : Type v} [BEq α] [Hashable α] (hn : ∀ [EquivBEq α] [LawfulHashable α], False)
    (s : Nat) (bs : Array (AssocList α (fun _ => β))) (h : 0 < bs.size) : (hmr s bs).WF :=
  ⟨wf_vac hn _ h⟩

end Lit

end HashInstHand

open HashInstHand

/-! ## `HashSet.Raw` lemmas on an arbitrary well-formed map -/

-- `Std.HashSet.Raw.contains_of_mem_toArray`: NB, the key 0 is never found.
theorem HashSet.Raw.contains_of_mem_toArray_h4 : ¬ drop0% Std.HashSet.Raw.contains_of_mem_toArray 4 :=
  fun h => absurd (h (m := hsr 1 #[b1 (NB.mk 0) ()]) (hsr_wf NB.broken _ _ (by decide)) (k := ⟨0⟩)
    (by hm_eval)) (by hm_eval)

-- `Std.HashSet.Raw.contains_of_mem_toArray`: AB, the key 0 sits in bucket 1 of 2.
theorem HashSet.Raw.contains_of_mem_toArray_h5 : ¬ drop0% Std.HashSet.Raw.contains_of_mem_toArray 5 :=
  fun h => absurd (h (m := hsr 1 #[.nil, b1 (AB.mk 0) ()]) (hsr_wf AB.broken _ _ (by decide)) (k := ⟨0⟩)
    (by hm_eval)) (by hm_eval)

-- `Std.HashSet.Raw.isEmpty_eq_false_iff_exists_mem`: NB; a raw map with size field 1 and no keys (well-formed vacuously, the model is not lawful).
theorem HashSet.Raw.isEmpty_eq_false_iff_exists_mem_h4 :
    ¬ drop0% Std.HashSet.Raw.isEmpty_eq_false_iff_exists_mem 4 := fun h => by
  obtain ⟨a, ha⟩ := (h (m := hsr 1 #[(.nil : AssocList NB _)]) (hsr_wf NB.broken _ _ (by decide))).mp (by hm_eval)
  revert ha; hm_eval

-- `Std.HashSet.Raw.isEmpty_eq_false_iff_exists_mem`: AB; a raw map with size field 1 and no keys (well-formed vacuously, the model is not lawful).
theorem HashSet.Raw.isEmpty_eq_false_iff_exists_mem_h5 :
    ¬ drop0% Std.HashSet.Raw.isEmpty_eq_false_iff_exists_mem 5 := fun h => by
  obtain ⟨a, ha⟩ := (h (m := hsr 1 #[(.nil : AssocList AB _)]) (hsr_wf AB.broken _ _ (by decide))).mp (by hm_eval)
  revert ha; hm_eval

-- `Std.HashSet.Raw.isEmpty_iff_forall_not_mem`: NB; a raw map with size field 1 and no keys (well-formed vacuously, the model is not lawful).
theorem HashSet.Raw.isEmpty_iff_forall_not_mem_h4 : ¬ drop0% Std.HashSet.Raw.isEmpty_iff_forall_not_mem 4 :=
  fun h => absurd ((h (m := hsr 1 #[(.nil : AssocList NB _)]) (hsr_wf NB.broken _ _ (by decide))).mpr
    (fun a => by hm_eval)) (by hm_eval)

-- `Std.HashSet.Raw.isEmpty_iff_forall_not_mem`: AB; a raw map with size field 1 and no keys (well-formed vacuously, the model is not lawful).
theorem HashSet.Raw.isEmpty_iff_forall_not_mem_h5 : ¬ drop0% Std.HashSet.Raw.isEmpty_iff_forall_not_mem 5 :=
  fun h => absurd ((h (m := hsr 1 #[(.nil : AssocList AB _)]) (hsr_wf AB.broken _ _ (by decide))).mpr
    (fun a => by hm_eval)) (by hm_eval)

-- `Std.HashSet.Raw.isEmpty_toArray`: NB; a raw map with size field 1 and no keys (well-formed vacuously, the model is not lawful).
theorem HashSet.Raw.isEmpty_toArray_h4 : ¬ drop0% Std.HashSet.Raw.isEmpty_toArray 4 :=
  fun h => absurd (h (m := hsr 1 #[(.nil : AssocList NB _)]) (hsr_wf NB.broken _ _ (by decide))) (by hm_eval)

-- `Std.HashSet.Raw.isEmpty_toArray`: AB; a raw map with size field 1 and no keys (well-formed vacuously, the model is not lawful).
theorem HashSet.Raw.isEmpty_toArray_h5 : ¬ drop0% Std.HashSet.Raw.isEmpty_toArray 5 :=
  fun h => absurd (h (m := hsr 1 #[(.nil : AssocList AB _)]) (hsr_wf AB.broken _ _ (by decide))) (by hm_eval)

-- `Std.HashSet.Raw.size_toArray`: NB; a raw map with size field 1 and no keys (well-formed vacuously, the model is not lawful).
theorem HashSet.Raw.size_toArray_h4 : ¬ drop0% Std.HashSet.Raw.size_toArray 4 :=
  fun h => absurd (h (m := hsr 1 #[(.nil : AssocList NB _)]) (hsr_wf NB.broken _ _ (by decide))) (by hm_eval)

-- `Std.HashSet.Raw.size_toArray`: AB; a raw map with size field 1 and no keys (well-formed vacuously, the model is not lawful).
theorem HashSet.Raw.size_toArray_h5 : ¬ drop0% Std.HashSet.Raw.size_toArray 5 :=
  fun h => absurd (h (m := hsr 1 #[(.nil : AssocList AB _)]) (hsr_wf AB.broken _ _ (by decide))) (by hm_eval)

-- `Std.HashSet.Raw.mem_congr`: NS, m = {1}, a = 0, b = 1.
theorem HashSet.Raw.mem_congr_h4 : ¬ drop0% Std.HashSet.Raw.mem_congr 4 :=
  fun h => absurd ((h (m := hsr 1 #[b1 (NS.mk 1) ()]) (hsr_wf NS.broken _ _ (by decide)) (a := ⟨0⟩) (b := ⟨1⟩)
    (by decide)).mpr (by hm_eval)) (by hm_eval)

-- `Std.HashSet.Raw.mem_congr`: AB, 0 in bucket 0 of 2; a = 0, b = 1.
theorem HashSet.Raw.mem_congr_h5 : ¬ drop0% Std.HashSet.Raw.mem_congr 5 :=
  fun h => absurd ((h (m := hsr 1 #[b1 (AB.mk 0) (), .nil]) (hsr_wf AB.broken _ _ (by decide)) (a := ⟨0⟩)
    (b := ⟨1⟩) rfl).mp (by hm_eval)) (by hm_eval)

-- `Std.HashSet.Raw.mem_erase`: NS, m = {1}, erase 0 keeps 1, but 0 == 1.
theorem HashSet.Raw.mem_erase_h4 : ¬ drop0% Std.HashSet.Raw.mem_erase 4 :=
  fun h => absurd ((h (m := hsr 1 #[b1 (NS.mk 1) ()]) (hsr_wf NS.broken _ _ (by decide)) (k := ⟨0⟩)
    (a := ⟨1⟩)).mp (by hm_eval)).1 (by decide)

-- `Std.HashSet.Raw.mem_erase`: AB, 0 in bucket 0 of 2; erasing 1 looks in bucket 1.
theorem HashSet.Raw.mem_erase_h5 : ¬ drop0% Std.HashSet.Raw.mem_erase 5 :=
  fun h => absurd ((h (m := hsr 1 #[b1 (AB.mk 0) (), .nil]) (hsr_wf AB.broken _ _ (by decide)) (k := ⟨1⟩)
    (a := ⟨0⟩)).mp (by hm_eval)).1 (by decide)

-- `Std.HashSet.Raw.mem_insert`: NT, m = {0}; inserting 1 is a no-op (0 == 1), 1 == 2 but not 0 == 2.
theorem HashSet.Raw.mem_insert_h4 : ¬ drop0% Std.HashSet.Raw.mem_insert 4 :=
  fun h => absurd ((h (m := hsr 1 #[b1 (NT.mk 0) ()]) (hsr_wf NT.broken _ _ (by decide)) (k := ⟨1⟩)
    (a := ⟨2⟩)).mpr (Or.inl (by decide))) (by hm_eval)

-- `Std.HashSet.Raw.mem_insert`: AB, two empty buckets; 0 goes to bucket 0, 1 looks in bucket 1.
theorem HashSet.Raw.mem_insert_h5 : ¬ drop0% Std.HashSet.Raw.mem_insert 5 :=
  fun h => absurd ((h (m := hsr 0 #[(.nil : AssocList AB _), .nil]) (hsr_wf AB.broken _ _ (by decide)) (k := ⟨0⟩)
    (a := ⟨1⟩)).mpr (Or.inl rfl)) (by hm_eval)

-- `Std.HashSet.Raw.mem_insert_self`: NB, no key is ever found.
theorem HashSet.Raw.mem_insert_self_h4 : ¬ drop0% Std.HashSet.Raw.mem_insert_self 4 :=
  fun h => absurd (h (m := hsr 0 #[(.nil : AssocList NB _)]) (hsr_wf NB.broken _ _ (by decide)) (k := ⟨0⟩))
    (by hm_eval)

-- `Std.HashSet.Raw.all_eq_true_iff_forall_mem_get`: NB, m = {0}, p = false; nothing is found.
theorem HashSet.Raw.all_eq_true_iff_forall_mem_get_h4 :
    ¬ drop0% Std.HashSet.Raw.all_eq_true_iff_forall_mem_get 4 :=
  fun h => absurd ((h (m := hsr 1 #[b1 (NB.mk 0) ()]) (p := fun _ => false) (hsr_wf NB.broken _ _ (by decide))).mpr
    (fun a ha => by revert ha; hm_eval)) (by hm_eval)

-- `Std.HashSet.Raw.all_eq_true_iff_forall_mem_get`: AB, one bucket [0, 1]; get always returns 0.
theorem HashSet.Raw.all_eq_true_iff_forall_mem_get_h5 :
    ¬ drop0% Std.HashSet.Raw.all_eq_true_iff_forall_mem_get 5 :=
  fun h => absurd ((h (m := hsr 2 #[.cons (AB.mk 0) () (b1 (AB.mk 1) ())]) (p := fun x => x.n == 0)
    (hsr_wf AB.broken _ _ (by decide))).mpr (fun a ha => by hm_eval)) (by hm_eval)

-- `Std.HashSet.Raw.all_eq_false_iff_exists_mem_get`: NB, m = {0}, p = false; nothing is found.
theorem HashSet.Raw.all_eq_false_iff_exists_mem_get_h4 :
    ¬ drop0% Std.HashSet.Raw.all_eq_false_iff_exists_mem_get 4 := fun h => by
  obtain ⟨a, ha, -⟩ := (h (m := hsr 1 #[b1 (NB.mk 0) ()]) (p := fun _ => false)
    (hsr_wf NB.broken _ _ (by decide))).mp (by hm_eval)
  revert ha; hm_eval

-- `Std.HashSet.Raw.all_eq_false_iff_exists_mem_get`: AB, one bucket [0, 1]; get always returns 0.
theorem HashSet.Raw.all_eq_false_iff_exists_mem_get_h5 :
    ¬ drop0% Std.HashSet.Raw.all_eq_false_iff_exists_mem_get 5 := fun h => by
  obtain ⟨a, ha, hp⟩ := (h (m := hsr 2 #[.cons (AB.mk 0) () (b1 (AB.mk 1) ())]) (p := fun x => x.n == 0)
    (hsr_wf AB.broken _ _ (by decide))).mp (by hm_eval)
  revert hp; hm_eval

/-! ## `HashMap` lemmas on an arbitrary map -/

-- `Std.HashMap.Raw.mem_alter_of_beq`: AB, two empty buckets; key 0 goes to bucket 0, 1 looks in bucket 1.
theorem HashMap.Raw.mem_alter_of_beq_h6 : ¬ drop0% Std.HashMap.Raw.mem_alter_of_beq 6 :=
  fun h => absurd ((h (m := hmr 0 #[(.nil : AssocList AB (fun _ => Nat)), .nil]) (k := ⟨0⟩) (k' := ⟨1⟩)
    (f := fun _ => some 0) (hmr_wf AB.broken _ _ (by decide)) rfl).mpr (by hm_eval)) (by hm_eval)

-- `Std.HashMap.mem_alter_of_beq`: NS, m = {1 ↦ 0}, k = 0, k' = 1, f = none: 0 is not found, 1 stays.
theorem HashMap.mem_alter_of_beq_h5 : ¬ drop0% Std.HashMap.mem_alter_of_beq 5 :=
  fun h => absurd ((h (m := hm NS.broken 1 #[b1 (NS.mk 1) (0 : Nat)] (by decide)) (k := ⟨0⟩) (k' := ⟨1⟩)
    (f := fun _ => none) (by decide)).mp (by hm_eval)) (by hm_eval)

-- `Std.HashMap.getElem?_alter_self`: NB, inserting 1 under key 1 is invisible.
theorem HashMap.getElem?_alter_self_h5 : ¬ drop0% Std.HashMap.getElem?_alter_self 5 :=
  fun h => absurd (h (m := hm NB.broken 0 #[(.nil : AssocList NB (fun _ => Nat))] (by decide)) (k := ⟨1⟩)
     (f := fun _ => some 1)) (by hm_eval)

-- `Std.HashMap.Raw.getElem?_alter_self`: AB, one bucket [0 ↦ 0, 1 ↦ 1]; removing key 0 exposes 1 ↦ 1.
theorem HashMap.Raw.getElem?_alter_self_h6 : ¬ drop0% Std.HashMap.Raw.getElem?_alter_self 6 :=
  fun h => absurd (h (m := hmr 2 #[.cons (AB.mk 0) (0 : Nat) (b1 (AB.mk 1) 1)]) (k := ⟨0⟩) 
    (f := fun _ => none) (hmr_wf AB.broken _ _ (by decide))) (by hm_eval)

-- `Std.HashMap.getElem!_alter_self`: NB, inserting 1 under key 1 is invisible.
theorem HashMap.getElem!_alter_self_h5 : ¬ drop0% Std.HashMap.getElem!_alter_self 5 :=
  fun h => absurd (h (m := hm NB.broken 0 #[(.nil : AssocList NB (fun _ => Nat))] (by decide)) (k := ⟨1⟩)
     (f := fun _ => some 1)) (by hm_eval)

-- `Std.HashMap.Raw.getElem!_alter_self`: AB, one bucket [0 ↦ 0, 1 ↦ 1]; removing key 0 exposes 1 ↦ 1.
theorem HashMap.Raw.getElem!_alter_self_h6 : ¬ drop0% Std.HashMap.Raw.getElem!_alter_self 6 :=
  fun h => absurd (h (m := hmr 2 #[.cons (AB.mk 0) (0 : Nat) (b1 (AB.mk 1) 1)]) (k := ⟨0⟩) 
    (f := fun _ => none) (hmr_wf AB.broken _ _ (by decide))) (by hm_eval)

-- `Std.HashMap.getD_alter_self`: NB, inserting 1 under key 1 is invisible.
theorem HashMap.getD_alter_self_h5 : ¬ drop0% Std.HashMap.getD_alter_self 5 :=
  fun h => absurd (h (m := hm NB.broken 0 #[(.nil : AssocList NB (fun _ => Nat))] (by decide)) (k := ⟨1⟩)
    (fallback := 5) (f := fun _ => some 1)) (by hm_eval)

-- `Std.HashMap.Raw.getD_alter_self`: AB, one bucket [0 ↦ 0, 1 ↦ 1]; removing key 0 exposes 1 ↦ 1.
theorem HashMap.Raw.getD_alter_self_h6 : ¬ drop0% Std.HashMap.Raw.getD_alter_self 6 :=
  fun h => absurd (h (m := hmr 2 #[.cons (AB.mk 0) (0 : Nat) (b1 (AB.mk 1) 1)]) (k := ⟨0⟩) (fallback := 5)
    (f := fun _ => none) (hmr_wf AB.broken _ _ (by decide))) (by hm_eval)

-- `Std.HashMap.getKey?_alter_self`: NB, inserting 1 under key 1 is invisible.
theorem HashMap.getKey?_alter_self_h5 : ¬ drop0% Std.HashMap.getKey?_alter_self 5 :=
  fun h => absurd (h (m := hm NB.broken 0 #[(.nil : AssocList NB (fun _ => Nat))] (by decide)) (k := ⟨1⟩)
     (f := fun _ => some 1)) (by hm_eval)

-- `Std.HashMap.Raw.getKey?_alter_self`: AB, one bucket [0 ↦ 0, 1 ↦ 1]; removing key 0 exposes 1 ↦ 1.
theorem HashMap.Raw.getKey?_alter_self_h6 : ¬ drop0% Std.HashMap.Raw.getKey?_alter_self 6 :=
  fun h => absurd (h (m := hmr 2 #[.cons (AB.mk 0) (0 : Nat) (b1 (AB.mk 1) 1)]) (k := ⟨0⟩) 
    (f := fun _ => none) (hmr_wf AB.broken _ _ (by decide))) (by hm_eval)

-- `Std.HashMap.getKey!_alter_self`: NB, inserting 1 under key 1 is invisible.
theorem HashMap.getKey!_alter_self_h5 : ¬ drop0% Std.HashMap.getKey!_alter_self 5 :=
  fun h => absurd (h (m := hm NB.broken 0 #[(.nil : AssocList NB (fun _ => Nat))] (by decide)) (k := ⟨1⟩)
     (f := fun _ => some 1)) (by hm_eval)

-- `Std.HashMap.Raw.getKey!_alter_self`: AB, one bucket [0 ↦ 0, 1 ↦ 1]; removing key 0 exposes 1 ↦ 1.
theorem HashMap.Raw.getKey!_alter_self_h6 : ¬ drop0% Std.HashMap.Raw.getKey!_alter_self 6 :=
  fun h => absurd (h (m := hmr 2 #[.cons (AB.mk 0) (0 : Nat) (b1 (AB.mk 1) 1)]) (k := ⟨0⟩) 
    (f := fun _ => none) (hmr_wf AB.broken _ _ (by decide))) (by hm_eval)

-- `Std.HashMap.getKeyD_alter_self`: NB, inserting 1 under key 1 is invisible.
theorem HashMap.getKeyD_alter_self_h5 : ¬ drop0% Std.HashMap.getKeyD_alter_self 5 :=
  fun h => absurd (h (m := hm NB.broken 0 #[(.nil : AssocList NB (fun _ => Nat))] (by decide)) (k := ⟨1⟩)
    (fallback := ⟨5⟩) (f := fun _ => some 1)) (by hm_eval)

-- `Std.HashMap.Raw.getKeyD_alter_self`: AB, one bucket [0 ↦ 0, 1 ↦ 1]; removing key 0 exposes 1 ↦ 1.
theorem HashMap.Raw.getKeyD_alter_self_h6 : ¬ drop0% Std.HashMap.Raw.getKeyD_alter_self 6 :=
  fun h => absurd (h (m := hmr 2 #[.cons (AB.mk 0) (0 : Nat) (b1 (AB.mk 1) 1)]) (k := ⟨0⟩) (fallback := ⟨5⟩)
    (f := fun _ => none) (hmr_wf AB.broken _ _ (by decide))) (by hm_eval)


-- `Std.HashMap.Raw.mem_insert`: NT, m = {1 ↦ 0}; inserting 0 replaces key 1 by 0, and 1 == 2 but not 0 ==
-- 2.
theorem HashMap.Raw.mem_insert_h5 : ¬ drop0% Std.HashMap.Raw.mem_insert 5 :=
  fun h => absurd ((h (m := hmr 1 #[b1 (NT.mk 1) (0 : Nat)]) (hmr_wf NT.broken _ _ (by decide)) (k := ⟨0⟩)
    (a := ⟨2⟩) (v := 0)).mpr (Or.inr (by hm_eval))) (by hm_eval)

-- `Std.HashMap.Raw.mem_insert`: AB, two empty buckets; 0 goes to bucket 0, 1 looks in bucket 1.
theorem HashMap.Raw.mem_insert_h6 : ¬ drop0% Std.HashMap.Raw.mem_insert 6 :=
  fun h => absurd ((h (m := hmr 0 #[(.nil : AssocList AB (fun _ => Nat)), .nil]) (hmr_wf AB.broken _ _ (by decide))
    (k := ⟨0⟩) (a := ⟨1⟩) (v := 0)).mpr (Or.inl rfl)) (by hm_eval)

-- `Std.HashMap.Raw.mem_insert_self`: NB, no key is ever found.
theorem HashMap.Raw.mem_insert_self_h5 : ¬ drop0% Std.HashMap.Raw.mem_insert_self 5 :=
  fun h => absurd (h (m := hmr 0 #[(.nil : AssocList NB (fun _ => Nat))]) (hmr_wf NB.broken _ _ (by decide))
    (k := ⟨0⟩) (v := 0)) (by hm_eval)

-- `Std.HashMap.Raw.isEmpty_toArray`: NB; a raw map with size field 1 and no keys (well-formed vacuously, the model is not lawful).
theorem HashMap.Raw.isEmpty_toArray_h5 : ¬ drop0% Std.HashMap.Raw.isEmpty_toArray 5 :=
  fun h => absurd (h (m := hmr 1 #[(.nil : AssocList NB (fun _ => Nat))]) (hmr_wf NB.broken _ _ (by decide)))
    (by hm_eval)

-- `Std.HashMap.Raw.isEmpty_toArray`: AB; a raw map with size field 1 and no keys (well-formed vacuously, the model is not lawful).
theorem HashMap.Raw.isEmpty_toArray_h6 : ¬ drop0% Std.HashMap.Raw.isEmpty_toArray 6 :=
  fun h => absurd (h (m := hmr 1 #[(.nil : AssocList AB (fun _ => Nat))]) (hmr_wf AB.broken _ _ (by decide)))
    (by hm_eval)

-- `Std.HashMap.Raw.size_toArray`: NB; a raw map with size field 1 and no keys (well-formed vacuously, the model is not lawful).
theorem HashMap.Raw.size_toArray_h5 : ¬ drop0% Std.HashMap.Raw.size_toArray 5 :=
  fun h => absurd (h (m := hmr 1 #[(.nil : AssocList NB (fun _ => Nat))]) (hmr_wf NB.broken _ _ (by decide)))
    (by hm_eval)

-- `Std.HashMap.Raw.size_toArray`: AB; a raw map with size field 1 and no keys (well-formed vacuously, the model is not lawful).
theorem HashMap.Raw.size_toArray_h6 : ¬ drop0% Std.HashMap.Raw.size_toArray 6 :=
  fun h => absurd (h (m := hmr 1 #[(.nil : AssocList AB (fun _ => Nat))]) (hmr_wf AB.broken _ _ (by decide)))
    (by hm_eval)

-- `Std.HashMap.Raw.nodup_keys`: NB, one bucket holding key 0 twice.
theorem HashMap.Raw.nodup_keys_h5 : ¬ drop0% Std.HashMap.Raw.nodup_keys 5 :=
  fun h => absurd (h (m := hmr 2 #[.cons (NB.mk 0) (0 : Nat) (b1 (NB.mk 0) 0)]) (hmr_wf NB.broken _ _ (by decide)))
    (by hm_eval)

-- `Std.HashMap.Raw.nodup_keys`: AB, one bucket holding key 0 twice.
theorem HashMap.Raw.nodup_keys_h6 : ¬ drop0% Std.HashMap.Raw.nodup_keys 6 :=
  fun h => absurd (h (m := hmr 2 #[.cons (AB.mk 0) (0 : Nat) (b1 (AB.mk 0) 0)]) (hmr_wf AB.broken _ _ (by decide)))
    (by hm_eval)

-- `Std.HashMap.Raw.empty_equiv_iff_isEmpty`: NB; a map with size field 0 holding one key (well-formed vacuously, the model is not lawful).
theorem HashMap.Raw.empty_equiv_iff_isEmpty_h5 : ¬ drop0% Std.HashMap.Raw.empty_equiv_iff_isEmpty 5 := fun h => by
  have := ((h (m := hmr 0 #[b1 (NB.mk 0) (0 : Nat)]) (hmr_wf NB.broken _ _ (by decide))).mpr (by hm_eval)).inner.impl
  simp [hmr_empty, toListModel] at this

-- `Std.HashMap.Raw.empty_equiv_iff_isEmpty`: AB; a map with size field 0 holding one key (well-formed vacuously, the model is not lawful).
theorem HashMap.Raw.empty_equiv_iff_isEmpty_h6 : ¬ drop0% Std.HashMap.Raw.empty_equiv_iff_isEmpty 6 := fun h => by
  have := ((h (m := hmr 0 #[b1 (AB.mk 0) (0 : Nat)]) (hmr_wf AB.broken _ _ (by decide))).mpr (by hm_eval)).inner.impl
  simp [hmr_empty, toListModel] at this

-- `Std.HashSet.empty_equiv_iff_isEmpty`: NB; a map with size field 0 holding one key (well-formed vacuously, the model is not lawful).
theorem HashSet.empty_equiv_iff_isEmpty_h4 : ¬ drop0% Std.HashSet.empty_equiv_iff_isEmpty 4 := fun h => by
  have := ((h (m := hs NB.broken 0 #[b1 (NB.mk 0) ()] (by decide))).mpr (by hm_eval)).inner.inner.inner.impl
  simp [hs_empty, toListModel] at this

-- `Std.HashSet.empty_equiv_iff_isEmpty`: AB; a map with size field 0 holding one key (well-formed vacuously, the model is not lawful).
theorem HashSet.empty_equiv_iff_isEmpty_h5 : ¬ drop0% Std.HashSet.empty_equiv_iff_isEmpty 5 := fun h => by
  have := ((h (m := hs AB.broken 0 #[b1 (AB.mk 0) ()] (by decide))).mpr (by hm_eval)).inner.inner.inner.impl
  simp [hs_empty, toListModel] at this

-- `Std.HashSet.Equiv.mem_iff`: NS, the same key 0 in bucket 0 resp. bucket 1 of 2.
theorem HashSet.Equiv.mem_iff_h5 : ¬ drop0% Std.HashSet.Equiv.mem_iff 5 :=
  fun h => absurd ((h (m₁ := hs NS.broken 1 #[b1 (NS.mk 0) (), .nil] (by decide))
    (m₂ := hs NS.broken 1 #[.nil, b1 (NS.mk 0) ()] (by decide)) (k := ⟨0⟩)
    ⟨⟨⟨⟨by simp [toListModel]⟩⟩⟩⟩).mp (by hm_eval)) (by hm_eval)

-- `Std.HashSet.Equiv.mem_iff`: AB, the same key 0 in bucket 0 resp. bucket 1 of 2.
theorem HashSet.Equiv.mem_iff_h6 : ¬ drop0% Std.HashSet.Equiv.mem_iff 6 :=
  fun h => absurd ((h (m₁ := hs AB.broken 1 #[b1 (AB.mk 0) (), .nil] (by decide))
    (m₂ := hs AB.broken 1 #[.nil, b1 (AB.mk 0) ()] (by decide)) (k := ⟨0⟩)
    ⟨⟨⟨⟨by simp [toListModel]⟩⟩⟩⟩).mp (by hm_eval)) (by hm_eval)

/-! ## `HashMap.get?/get!` of `insert`/`erase` -/

-- `Std.HashMap.get?_insert`: NT, m = {2 ↦ 0}; inserting 1 replaces key 2, so 3 is no longer found.
theorem HashMap.get?_insert_h5 : ¬ drop0% Std.HashMap.get?_insert 5 :=
  fun h => absurd (h (m := hm NT.broken 1 #[b1 (NT.mk 2) (0 : Nat)] (by decide)) (k := ⟨1⟩) (a := ⟨3⟩) (v := 1))
    (by hm_eval)

-- `Std.HashMap.get?_insert`: AB, two empty buckets; key 0 goes to bucket 0, 1 looks in bucket 1.
theorem HashMap.get?_insert_h6 : ¬ drop0% Std.HashMap.get?_insert 6 :=
  fun h => absurd (h (m := hm AB.broken 0 #[(.nil : AssocList AB (fun _ => Nat)), .nil] (by decide)) (k := ⟨0⟩)
    (a := ⟨1⟩) (v := 1)) (by hm_eval)

-- `Std.HashMap.get!_insert`: NT, m = {2 ↦ 5}; inserting 1 replaces key 2, so 3 is no longer found.
theorem HashMap.get!_insert_h5 : ¬ drop0% Std.HashMap.get!_insert 5 :=
  fun h => absurd (h (m := hm NT.broken 1 #[b1 (NT.mk 2) (5 : Nat)] (by decide)) (k := ⟨1⟩) (a := ⟨3⟩) (v := 1))
    (by hm_eval)

-- `Std.HashMap.get!_insert`: AB, two empty buckets; key 0 goes to bucket 0, 1 looks in bucket 1.
theorem HashMap.get!_insert_h6 : ¬ drop0% Std.HashMap.get!_insert 6 :=
  fun h => absurd (h (m := hm AB.broken 0 #[(.nil : AssocList AB (fun _ => Nat)), .nil] (by decide)) (k := ⟨0⟩)
    (a := ⟨1⟩) (v := 1)) (by hm_eval)

-- `Std.HashMap.get?_erase`: NS, m = {1 ↦ 0}; erasing 0 keeps 1 although 0 == 1.
theorem HashMap.get?_erase_h5 : ¬ drop0% Std.HashMap.get?_erase 5 :=
  fun h => absurd (h (m := hm NS.broken 1 #[b1 (NS.mk 1) (0 : Nat)] (by decide)) (k := ⟨0⟩) (a := ⟨1⟩))
    (by hm_eval)

-- `Std.HashMap.get?_erase`: AB, key 0 in bucket 0 of 2; erasing 1 looks in bucket 1.
theorem HashMap.get?_erase_h6 : ¬ drop0% Std.HashMap.get?_erase 6 :=
  fun h => absurd (h (m := hm AB.broken 1 #[b1 (AB.mk 0) (0 : Nat), .nil] (by decide)) (k := ⟨1⟩) (a := ⟨0⟩))
    (by hm_eval)

-- `Std.HashMap.get!_erase`: NS, m = {1 ↦ 5}; erasing 0 keeps 1 although 0 == 1.
theorem HashMap.get!_erase_h5 : ¬ drop0% Std.HashMap.get!_erase 5 :=
  fun h => absurd (h (m := hm NS.broken 1 #[b1 (NS.mk 1) (5 : Nat)] (by decide)) (k := ⟨0⟩) (a := ⟨1⟩))
    (by hm_eval)

-- `Std.HashMap.get!_erase`: AB, key 0 ↦ 5 in bucket 0 of 2; erasing 1 looks in bucket 1.
theorem HashMap.get!_erase_h6 : ¬ drop0% Std.HashMap.get!_erase 6 :=
  fun h => absurd (h (m := hm AB.broken 1 #[b1 (AB.mk 0) (5 : Nat), .nil] (by decide)) (k := ⟨1⟩) (a := ⟨0⟩))
    (by hm_eval)

/-! ## `ofList` / `insertMany` -/

-- `Std.HashSet.get?_ofList_of_mem`: NT, l = [0, 2]; key 1 finds 2 (stored first) instead of 0.
theorem HashSet.get?_ofList_of_mem_h3 : ¬ drop0% Std.HashSet.get?_ofList_of_mem 3 :=
  fun h => absurd ((@h NT inferInstance inferInstance) (l := [NT.mk 0, NT.mk 2]) (k := ⟨0⟩) (k' := ⟨1⟩)  (by decide) (by decide) (by simp))
    (by hm_eval)

-- `Std.HashSet.get?_ofList_of_mem`: AB, l = [0]; key 1 looks in bucket 1.
theorem HashSet.get?_ofList_of_mem_h4 : ¬ drop0% Std.HashSet.get?_ofList_of_mem 4 :=
  fun h => absurd ((@h AB inferInstance inferInstance) (l := [AB.mk 0]) (k := ⟨0⟩) (k' := ⟨1⟩)  rfl (by simp) (by simp)) (by hm_eval)

-- `Std.HashSet.get?_ofList_of_contains_eq_false`: NS, l = [2], k = 3: not 3 == 2, but the stored 2 == 3.
theorem HashSet.get?_ofList_of_contains_eq_false_h3 : ¬ drop0% Std.HashSet.get?_ofList_of_contains_eq_false 3 :=
  fun h => absurd ((@h NS inferInstance inferInstance) (l := [NS.mk 2]) (k := ⟨3⟩)  (by decide)) (by hm_eval)

-- `Std.HashSet.get!_ofList_of_mem`: NT, l = [0, 2]; key 1 finds 2 (stored first) instead of 0.
theorem HashSet.get!_ofList_of_mem_h3 : ¬ drop0% Std.HashSet.get!_ofList_of_mem 3 :=
  fun h => absurd ((@h NT inferInstance inferInstance) (l := [NT.mk 0, NT.mk 2]) (k := ⟨0⟩) (k' := ⟨1⟩)  (by decide) (by decide) (by simp))
    (by hm_eval)

-- `Std.HashSet.get!_ofList_of_mem`: AB, l = [2]; key 1 looks in bucket 1.
theorem HashSet.get!_ofList_of_mem_h4 : ¬ drop0% Std.HashSet.get!_ofList_of_mem 4 :=
  fun h => absurd ((@h AB inferInstance inferInstance) (l := [AB.mk 2]) (k := ⟨2⟩) (k' := ⟨1⟩)  rfl (by simp) (by simp)) (by hm_eval)

-- `Std.HashSet.get!_ofList_of_contains_eq_false`: NS, l = [2], k = 3: not 3 == 2, but the stored 2 == 3.
theorem HashSet.get!_ofList_of_contains_eq_false_h3 : ¬ drop0% Std.HashSet.get!_ofList_of_contains_eq_false 3 :=
  fun h => absurd ((@h NS inferInstance inferInstance) (l := [NS.mk 2]) (k := ⟨3⟩)  (by decide)) (by hm_eval)

-- `Std.HashSet.getD_ofList_of_mem`: NT, l = [0, 2]; key 1 finds 2 (stored first) instead of 0.
theorem HashSet.getD_ofList_of_mem_h3 : ¬ drop0% Std.HashSet.getD_ofList_of_mem 3 :=
  fun h => absurd ((@h NT inferInstance inferInstance) (l := [NT.mk 0, NT.mk 2]) (k := ⟨0⟩) (k' := ⟨1⟩) (fallback := ⟨5⟩) (by decide) (by decide) (by simp))
    (by hm_eval)

-- `Std.HashSet.getD_ofList_of_mem`: AB, l = [0]; key 1 looks in bucket 1.
theorem HashSet.getD_ofList_of_mem_h4 : ¬ drop0% Std.HashSet.getD_ofList_of_mem 4 :=
  fun h => absurd ((@h AB inferInstance inferInstance) (l := [AB.mk 0]) (k := ⟨0⟩) (k' := ⟨1⟩) (fallback := ⟨5⟩) rfl (by simp) (by simp)) (by hm_eval)

-- `Std.HashSet.getD_ofList_of_contains_eq_false`: NS, l = [2], k = 3: not 3 == 2, but the stored 2 == 3.
theorem HashSet.getD_ofList_of_contains_eq_false_h3 : ¬ drop0% Std.HashSet.getD_ofList_of_contains_eq_false 3 :=
  fun h => absurd ((@h NS inferInstance inferInstance) (l := [NS.mk 2]) (k := ⟨3⟩) (fallback := ⟨5⟩) (by decide)) (by hm_eval)

-- `Std.HashSet.mem_ofList`: NS, l = [0], k = 1: the stored 0 == 1, but not 1 == 0.
theorem HashSet.mem_ofList_h3 : ¬ drop0% Std.HashSet.mem_ofList 3 :=
  fun h => absurd (((@h NS inferInstance inferInstance) (l := [NS.mk 0]) (k := ⟨1⟩)).mp (by hm_eval)) (by decide)

-- `Std.HashSet.mem_ofList`: AB, l = [0], k = 1 looks in bucket 1.
theorem HashSet.mem_ofList_h4 : ¬ drop0% Std.HashSet.mem_ofList 4 :=
  fun h => absurd (((@h AB inferInstance inferInstance) (l := [AB.mk 0]) (k := ⟨1⟩)).mpr rfl) (by hm_eval)

-- `Std.HashSet.mem_insertMany_list`: NS, m = ∅, l = [0], k = 1: the stored 0 == 1, but not 1 == 0.
theorem HashSet.mem_insertMany_list_h4 : ¬ drop0% Std.HashSet.mem_insertMany_list 4 :=
  fun h => absurd ((h (m := (∅ : HashSet NS)) (l := [NS.mk 0]) (k := ⟨1⟩)).mp (by hm_eval)) (by hm_eval)

-- `Std.HashSet.mem_insertMany_list`: AB, m = ∅, l = [0], k = 1 looks in bucket 1.
theorem HashSet.mem_insertMany_list_h5 : ¬ drop0% Std.HashSet.mem_insertMany_list 5 :=
  fun h => absurd ((h (m := (∅ : HashSet AB)) (l := [AB.mk 0]) (k := ⟨1⟩)).mpr (Or.inr rfl)) (by hm_eval)

-- `Std.HashSet.Raw.get_ofList_of_mem`: NT, l = [0, 2]; key 1 finds 2 (stored first) instead of 0.
theorem HashSet.Raw.get_ofList_of_mem_h3 : ¬ drop0% Std.HashSet.Raw.get_ofList_of_mem 3 :=
  fun h => absurd (h (l := [NT.mk 0, NT.mk 2]) (k := ⟨0⟩) (k' := ⟨1⟩) (by decide) (by decide) (by simp)
    (h' := by hm_eval)) (by hm_eval)

-- `Std.HashMap.getElem?_unitOfList`: NS, l = [0], k = 1: the stored 0 == 1, but not 1 == 0.
theorem HashMap.getElem?_unitOfList_h3 : ¬ drop0% Std.HashMap.getElem?_unitOfList 3 :=
  fun h => absurd ((@h NS inferInstance inferInstance) (l := [NS.mk 0]) (k := ⟨1⟩)) (by hm_eval)

-- `Std.HashMap.getElem?_unitOfList`: AB, l = [0], k = 1 looks in bucket 1.
theorem HashMap.getElem?_unitOfList_h4 : ¬ drop0% Std.HashMap.getElem?_unitOfList 4 :=
  fun h => absurd ((@h AB inferInstance inferInstance) (l := [AB.mk 0]) (k := ⟨1⟩)) (by hm_eval)

-- `Std.HashMap.Raw.getElem_ofList_of_mem`: NT, l = [(0, 0), (2, 1)]; key 1 finds 2 ↦ 1.
theorem HashMap.Raw.getElem_ofList_of_mem_h4 : ¬ drop0% Std.HashMap.Raw.getElem_ofList_of_mem 4 :=
  fun h => absurd (h (l := [(NT.mk 0, (0 : Nat)), (NT.mk 2, 1)]) (k := ⟨0⟩) (k' := ⟨1⟩) (v := 0) (by decide)
    (by decide) (by simp) (h := by hm_eval)) (by hm_eval)

-- `Std.HashMap.Raw.getKey_ofList_of_mem`: NT, l = [(0, 0), (2, 1)]; key 1 finds 2.
theorem HashMap.Raw.getKey_ofList_of_mem_h4 : ¬ drop0% Std.HashMap.Raw.getKey_ofList_of_mem 4 :=
  fun h => absurd (h (l := [(NT.mk 0, (0 : Nat)), (NT.mk 2, 1)]) (k := ⟨0⟩) (k' := ⟨1⟩) (by decide)
    (by decide) (by simp) (h' := by hm_eval)) (by hm_eval)

-- `Std.HashMap.getElem?_ofList_of_mem`: NT, l = [(0, 0), (2, 1)]; key 1 finds 2 ↦ 1 (stored first).
theorem HashMap.getElem?_ofList_of_mem_h4 : ¬ drop0% Std.HashMap.getElem?_ofList_of_mem 4 :=
  fun h => absurd ((@h NT Nat inferInstance inferInstance) (l := [(NT.mk 0, (0 : Nat)), (NT.mk 2, 1)]) (k := ⟨0⟩) (k' := ⟨1⟩) (v := 0) 
    (by decide) (by decide) (by simp)) (by hm_eval)

-- `Std.HashMap.getElem?_ofList_of_mem`: AB, l = [(0, 1)]; key 1 looks in bucket 1.
theorem HashMap.getElem?_ofList_of_mem_h5 : ¬ drop0% Std.HashMap.getElem?_ofList_of_mem 5 :=
  fun h => absurd ((@h AB Nat inferInstance inferInstance) (l := [(AB.mk 0, (1 : Nat))]) (k := ⟨0⟩) (k' := ⟨1⟩) (v := 1)  rfl (by simp) (by simp))
    (by hm_eval)

-- `Std.HashMap.getElem?_ofList_of_contains_eq_false`: NS, l = [(2, 7)], k = 3: not 3 == 2, but the stored 2
-- == 3.
theorem HashMap.getElem?_ofList_of_contains_eq_false_h4 : ¬ drop0% Std.HashMap.getElem?_ofList_of_contains_eq_false 4 :=
  fun h => absurd ((@h NS Nat inferInstance inferInstance) (l := [(NS.mk 2, (7 : Nat))]) (k := ⟨3⟩)  (by decide)) (by hm_eval)

-- `Std.HashMap.getElem!_ofList_of_mem`: NT, l = [(0, 0), (2, 1)]; key 1 finds 2 ↦ 1 (stored first).
theorem HashMap.getElem!_ofList_of_mem_h4 : ¬ drop0% Std.HashMap.getElem!_ofList_of_mem 4 :=
  fun h => absurd ((@h NT Nat inferInstance inferInstance) (l := [(NT.mk 0, (0 : Nat)), (NT.mk 2, 1)]) (k := ⟨0⟩) (k' := ⟨1⟩) (v := 0) 
    (by decide) (by decide) (by simp)) (by hm_eval)

-- `Std.HashMap.getElem!_ofList_of_mem`: AB, l = [(0, 1)]; key 1 looks in bucket 1.
theorem HashMap.getElem!_ofList_of_mem_h5 : ¬ drop0% Std.HashMap.getElem!_ofList_of_mem 5 :=
  fun h => absurd ((@h AB Nat inferInstance inferInstance) (l := [(AB.mk 0, (1 : Nat))]) (k := ⟨0⟩) (k' := ⟨1⟩) (v := 1)  rfl (by simp) (by simp))
    (by hm_eval)

-- `Std.HashMap.getElem!_ofList_of_contains_eq_false`: NS, l = [(2, 7)], k = 3: not 3 == 2, but the stored 2
-- == 3.
theorem HashMap.getElem!_ofList_of_contains_eq_false_h4 : ¬ drop0% Std.HashMap.getElem!_ofList_of_contains_eq_false 4 :=
  fun h => absurd ((@h NS Nat inferInstance inferInstance) (l := [(NS.mk 2, (7 : Nat))]) (k := ⟨3⟩)  (by decide)) (by hm_eval)

-- `Std.HashMap.getD_ofList_of_mem`: NT, l = [(0, 0), (2, 1)]; key 1 finds 2 ↦ 1 (stored first).
theorem HashMap.getD_ofList_of_mem_h4 : ¬ drop0% Std.HashMap.getD_ofList_of_mem 4 :=
  fun h => absurd ((@h NT Nat inferInstance inferInstance) (l := [(NT.mk 0, (0 : Nat)), (NT.mk 2, 1)]) (k := ⟨0⟩) (k' := ⟨1⟩) (v := 0) (fallback := 5)
    (by decide) (by decide) (by simp)) (by hm_eval)

-- `Std.HashMap.getD_ofList_of_mem`: AB, l = [(0, 1)]; key 1 looks in bucket 1.
theorem HashMap.getD_ofList_of_mem_h5 : ¬ drop0% Std.HashMap.getD_ofList_of_mem 5 :=
  fun h => absurd ((@h AB Nat inferInstance inferInstance) (l := [(AB.mk 0, (1 : Nat))]) (k := ⟨0⟩) (k' := ⟨1⟩) (v := 1) (fallback := 5) rfl (by simp) (by simp))
    (by hm_eval)

-- `Std.HashMap.getD_ofList_of_contains_eq_false`: NS, l = [(2, 7)], k = 3: not 3 == 2, but the stored 2 ==
-- 3.
theorem HashMap.getD_ofList_of_contains_eq_false_h4 : ¬ drop0% Std.HashMap.getD_ofList_of_contains_eq_false 4 :=
  fun h => absurd ((@h NS Nat inferInstance inferInstance) (l := [(NS.mk 2, (7 : Nat))]) (k := ⟨3⟩) (fallback := 5) (by decide)) (by hm_eval)

-- `Std.HashMap.getKey?_ofList_of_mem`: NT, l = [(0, 0), (2, 1)]; key 1 finds 2 ↦ 1 (stored first).
theorem HashMap.getKey?_ofList_of_mem_h4 : ¬ drop0% Std.HashMap.getKey?_ofList_of_mem 4 :=
  fun h => absurd ((@h NT Nat inferInstance inferInstance) (l := [(NT.mk 0, (0 : Nat)), (NT.mk 2, 1)]) (k := ⟨0⟩) (k' := ⟨1⟩) 
    (by decide) (by decide) (by simp)) (by hm_eval)

-- `Std.HashMap.getKey?_ofList_of_mem`: AB, l = [(0, 1)]; key 1 looks in bucket 1.
theorem HashMap.getKey?_ofList_of_mem_h5 : ¬ drop0% Std.HashMap.getKey?_ofList_of_mem 5 :=
  fun h => absurd ((@h AB Nat inferInstance inferInstance) (l := [(AB.mk 0, (1 : Nat))]) (k := ⟨0⟩) (k' := ⟨1⟩)  rfl (by simp) (by simp))
    (by hm_eval)

-- `Std.HashMap.getKey?_ofList_of_contains_eq_false`: NS, l = [(2, 7)], k = 3: not 3 == 2, but the stored 2
-- == 3.
theorem HashMap.getKey?_ofList_of_contains_eq_false_h4 : ¬ drop0% Std.HashMap.getKey?_ofList_of_contains_eq_false 4 :=
  fun h => absurd ((@h NS Nat inferInstance inferInstance) (l := [(NS.mk 2, (7 : Nat))]) (k := ⟨3⟩)  (by decide)) (by hm_eval)

-- `Std.HashMap.getKey!_ofList_of_mem`: NT, l = [(0, 0), (2, 1)]; key 1 finds 2 ↦ 1 (stored first).
theorem HashMap.getKey!_ofList_of_mem_h4 : ¬ drop0% Std.HashMap.getKey!_ofList_of_mem 4 :=
  fun h => absurd ((@h NT Nat inferInstance inferInstance) (l := [(NT.mk 0, (0 : Nat)), (NT.mk 2, 1)]) (k := ⟨0⟩) (k' := ⟨1⟩) 
    (by decide) (by decide) (by simp)) (by hm_eval)

-- `Std.HashMap.getKey!_ofList_of_mem`: AB, l = [(2, 1)]; key 1 looks in bucket 1.
theorem HashMap.getKey!_ofList_of_mem_h5 : ¬ drop0% Std.HashMap.getKey!_ofList_of_mem 5 :=
  fun h => absurd ((@h AB Nat inferInstance inferInstance) (l := [(AB.mk 2, (1 : Nat))]) (k := ⟨2⟩) (k' := ⟨1⟩)  rfl (by simp) (by simp))
    (by hm_eval)

-- `Std.HashMap.getKey!_ofList_of_contains_eq_false`: NS, l = [(2, 7)], k = 3: not 3 == 2, but the stored 2
-- == 3.
theorem HashMap.getKey!_ofList_of_contains_eq_false_h4 : ¬ drop0% Std.HashMap.getKey!_ofList_of_contains_eq_false 4 :=
  fun h => absurd ((@h NS Nat inferInstance inferInstance) (l := [(NS.mk 2, (7 : Nat))]) (k := ⟨3⟩)  (by decide)) (by hm_eval)

-- `Std.HashMap.getKeyD_ofList_of_mem`: NT, l = [(0, 0), (2, 1)]; key 1 finds 2 ↦ 1 (stored first).
theorem HashMap.getKeyD_ofList_of_mem_h4 : ¬ drop0% Std.HashMap.getKeyD_ofList_of_mem 4 :=
  fun h => absurd ((@h NT Nat inferInstance inferInstance) (l := [(NT.mk 0, (0 : Nat)), (NT.mk 2, 1)]) (k := ⟨0⟩) (k' := ⟨1⟩) (fallback := ⟨5⟩)
    (by decide) (by decide) (by simp)) (by hm_eval)

-- `Std.HashMap.getKeyD_ofList_of_mem`: AB, l = [(0, 1)]; key 1 looks in bucket 1.
theorem HashMap.getKeyD_ofList_of_mem_h5 : ¬ drop0% Std.HashMap.getKeyD_ofList_of_mem 5 :=
  fun h => absurd ((@h AB Nat inferInstance inferInstance) (l := [(AB.mk 0, (1 : Nat))]) (k := ⟨0⟩) (k' := ⟨1⟩) (fallback := ⟨5⟩) rfl (by simp) (by simp))
    (by hm_eval)

-- `Std.HashMap.getKeyD_ofList_of_contains_eq_false`: NS, l = [(2, 7)], k = 3: not 3 == 2, but the stored 2
-- == 3.
theorem HashMap.getKeyD_ofList_of_contains_eq_false_h4 : ¬ drop0% Std.HashMap.getKeyD_ofList_of_contains_eq_false 4 :=
  fun h => absurd ((@h NS Nat inferInstance inferInstance) (l := [(NS.mk 2, (7 : Nat))]) (k := ⟨3⟩) (fallback := ⟨5⟩) (by decide)) (by hm_eval)

/-! ## Internal lemmas with a well-formed map (`Raw.WFImp`) -/

-- `Std.DHashMap.Internal.Raw₀.Const.beq_eq_beqModel`: AB, m₁ = {0 ↦ 0} in bucket 0 of 2, m₂ = {1 ↦ 0} in bucket 1
-- of 2 (both WFImp): beq looks up 0 in bucket 0 of m₂ and fails, the list model finds 1 == 0.
theorem Raw₀.Const.beq_eq_beqModel_h5 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.beq_eq_beqModel 5 := fun h => by
  have w₁ : Raw.WFImp (⟨1, #[b1 (AB.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw AB (fun _ => Nat)) :=
    ⟨⟨fun i hi => ⟨fun h0 p hp => by
      rw [mkIdx_toNat' _ _ _ (by decide)]
      match i, hi with
      | 0, _ => simp at hp; subst hp; simp (disch := simp) [scr_small]
      | 1, _ => simp at hp⟩⟩, by simp [toListModel], by simp [toListModel]⟩
  have w₂ : Raw.WFImp (⟨1, #[.nil, b1 (AB.mk 1) (0 : Nat)]⟩ : DHashMap.Raw AB (fun _ => Nat)) :=
    ⟨⟨fun i hi => ⟨fun h0 p hp => by
      rw [mkIdx_toNat' _ _ _ (by decide)]
      match i, hi with
      | 0, _ => simp at hp
      | 1, _ => simp at hp; subst hp; simp (disch := simp) [scr_small]⟩⟩, by simp [toListModel], by simp [toListModel]⟩
  have := h (α := AB) (β := Nat) (m₁ := ⟨_, by decide⟩) (m₂ := ⟨_, by decide⟩) w₁ w₂
  revert this
  simp only [Raw₀.Const.beq]
  hm_eval
  simp [Std.Internal.List.Const.beqModel, Std.Internal.List.getValue?]

/-! ## Union and intersection -/

namespace HashInstHand
abbrev NS4 (s : Nat) (k : Nat) : HashSet NS := hs NS.broken s #[b1 (NS.mk k) (), .nil, .nil, .nil] (by simp)
abbrev AB2 (s : Nat) (k : Nat) (i : Nat) : HashSet AB :=
  hs AB.broken s (if i = 0 then #[b1 (AB.mk k) (), .nil] else #[.nil, b1 (AB.mk k) ()]) (by split <;> simp)
end HashInstHand


-- `Std.HashSet.inter_union_equiv_empty_iff`: NS (a == b iff a ≤ b), m₁ = {1}, m₂ = {5}, m₃ = {0} with size fields
-- 1, 1, 0 (4 buckets): m₂ ∪ m₃ = {0, 5} meets m₁ via filter (0 == 1), while m₁ ∩ m₂ (filter: not 5 == 1) and
-- m₁ ∩ m₃ (interSmaller: not 1 == 0) are empty.
theorem HashSet.inter_union_equiv_empty_iff_h3 : ¬ drop0% Std.HashSet.inter_union_equiv_empty_iff 3 := fun h => by
  have := ((h (m₁ := NS4 1 1) (m₂ := NS4 1 5) (m₃ := NS4 0 0)).mpr
    ⟨⟨⟨⟨⟨by hm_eval⟩⟩⟩⟩, ⟨⟨⟨⟨by hm_eval⟩⟩⟩⟩⟩).inner.inner.inner.impl
  revert this; hm_eval

-- `Std.HashSet.inter_union_equiv_empty_iff`: AB, m₁ = {0} in bucket 0, m₂ = {1} in bucket 1, m₃ = {2} misplaced in
-- bucket 1 (size fields 0, 1, 0; 2 buckets): m₂ ∪ m₃ puts 2 into bucket 0, which then meets m₁; m₁ ∩ m₂ and
-- m₁ ∩ m₃ find bucket 0 empty.
theorem HashSet.inter_union_equiv_empty_iff_h4 : ¬ drop0% Std.HashSet.inter_union_equiv_empty_iff 4 := fun h => by
  have := ((h (m₁ := AB2 0 0 0) (m₂ := AB2 1 1 1) (m₃ := AB2 0 2 1)).mpr
    ⟨⟨⟨⟨⟨by hm_eval⟩⟩⟩⟩, ⟨⟨⟨⟨by hm_eval⟩⟩⟩⟩⟩).inner.inner.inner.impl
  revert this; hm_eval

-- `Std.HashSet.union_inter_equiv_empty_iff`: NS, m₁ = {5}, m₂ = {0}, m₃ = {1} with size fields 1, 0, 0 (4 buckets):
-- (m₁ ∪ m₂) ∩ m₃ finds 0 == 1 (interSmaller), while m₁ ∩ m₃ (interSmaller: not 5 == 1) and m₂ ∩ m₃ (filter:
-- not 1 == 0) are empty.
theorem HashSet.union_inter_equiv_empty_iff_h3 : ¬ drop0% Std.HashSet.union_inter_equiv_empty_iff 3 := fun h => by
  have := ((h (m₁ := NS4 1 5) (m₂ := NS4 0 0) (m₃ := NS4 0 1)).mpr
    ⟨⟨⟨⟨⟨by hm_eval⟩⟩⟩⟩, ⟨⟨⟨⟨by hm_eval⟩⟩⟩⟩⟩).inner.inner.inner.impl
  revert this; hm_eval

-- `Std.HashSet.union_inter_equiv_empty_iff`: AB, m₁ = {2} misplaced in bucket 1, m₂ = {1} in bucket 1, m₃ = {0} in
-- bucket 0 (size fields 1, 1, 0; 2 buckets): m₁ ∪ m₂ puts 2 into bucket 0, where m₃'s key 0 finds it; m₁ ∩ m₃ and
-- m₂ ∩ m₃ find bucket 0 empty.
theorem HashSet.union_inter_equiv_empty_iff_h4 : ¬ drop0% Std.HashSet.union_inter_equiv_empty_iff 4 := fun h => by
  have := ((h (m₁ := AB2 1 2 1) (m₂ := AB2 1 1 1) (m₃ := AB2 0 0 0)).mpr
    ⟨⟨⟨⟨⟨by hm_eval⟩⟩⟩⟩, ⟨⟨⟨⟨by hm_eval⟩⟩⟩⟩⟩).inner.inner.inner.impl
  revert this; hm_eval

/-! ## Removable instance hypotheses -/

namespace HashInstHand
section Removable
variable {α : Type u} {β : α → Type v}

theorem assoc_isSome_getKey? [BEq α] (l : AssocList α β) (a : α) : (l.getKey? a).isSome = l.contains a := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    simp only [AssocList.getKey?, AssocList.contains]
    cases k == a <;> simp only [ite_true, Bool.false_eq_true, ite_false, Option.isSome_some, Bool.true_or,
      Bool.false_or, ih]

theorem assoc_isSome_get? {γ : Type v} [BEq α] (l : AssocList α (fun _ => γ)) (a : α) :
    (l.get? a).isSome = l.contains a := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    simp only [AssocList.get?, AssocList.contains]
    cases k == a <;> simp only [cond_true, cond_false, Option.isSome_some, Bool.true_or, Bool.false_or, ih]

theorem raw0_isSome_getKey? [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    (m.getKey? a).isSome = m.contains a := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.getKey? Raw₀.contains; dsimp only
  generalize mkIdx bs.size h (hash a) = i
  obtain ⟨i, hi⟩ := i
  exact assoc_isSome_getKey? _ a

theorem raw0_isSome_cget? {γ : Type v} [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (a : α) :
    (Raw₀.Const.get? m a).isSome = m.contains a := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.Const.get? Raw₀.contains; dsimp only
  generalize mkIdx bs.size h (hash a) = i
  obtain ⟨i, hi⟩ := i
  exact assoc_isSome_get? _ a

theorem raw0_size_insertIfNew [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    m.1.size ≤ (m.insertIfNew a b).1.size ∧ (m.insertIfNew a b).1.size ≤ m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.insertIfNew; dsimp only
  generalize mkIdx bs.size h (hash a) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  split <;> simp [Raw₀.size_expandIfNecessary]

theorem raw0_size_insert [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    m.1.size ≤ (m.insert a b).1.size ∧ (m.insert a b).1.size ≤ m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.insert; dsimp only
  generalize mkIdx bs.size h (hash a) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  split <;> simp [Raw₀.size_expandIfNecessary]


/-- The entries of a bucket are entries of the map. -/
theorem mem_tlm_of_bucket (bs : Array (AssocList α β)) (i : Nat) (hi : i < bs.size) (p : (a : α) × β a)
    (hp : p ∈ (bs[i]).toList) : p ∈ toListModel bs := by
  unfold toListModel
  exact List.mem_flatMap.mpr ⟨bs[i], Array.getElem_mem_toList hi, hp⟩

/-- An always-false BEq, which is a PartialEquivBEq (used to borrow lemmas whose statement ignores BEq). -/
abbrev falseBEq (α : Type u) : BEq α := ⟨fun _ _ => false⟩
instance falsePEq : @PartialEquivBEq α (falseBEq α) := @PartialEquivBEq.mk α (falseBEq α) (fun h => h) (fun h _ => h)

theorem tlm_expandIfNecessary [BEq α] [Hashable α] (m : Raw₀ α β) :
    List.Perm (toListModel m.expandIfNecessary.1.buckets) (toListModel m.1.buckets) :=
  @Raw₀.toListModel_expandIfNecessary α β (falseBEq α) _ falsePEq m

theorem mem_tlm_uset [BEq α] [Hashable α] (bs : Array (AssocList α β)) (i : USize) (hi : i.toNat < bs.size)
    (d : AssocList α β) (p : (a : α) × β a) (hp : p ∈ toListModel (bs.uset i d hi)) :
    p ∈ d.toList ∨ p ∈ toListModel bs := by
  obtain ⟨l, h₁, h₂, -⟩ := exists_bucket_of_uset bs i hi d
  rcases List.mem_append.mp (h₂.mem_iff.mp hp) with h | h
  · exact Or.inl h
  · exact Or.inr (h₁.mem_iff.mpr (List.mem_append_right _ h))

theorem mem_tlm_set (bs : Array (AssocList α β)) (j : Nat) (hj : j < bs.size) (d : AssocList α β)
    (p : (a : α) × β a) (hp : p ∈ toListModel (bs.set j d hj)) : p ∈ d.toList ∨ p ∈ toListModel bs := by
  unfold toListModel at *
  obtain ⟨c, hc, hpc⟩ := List.mem_flatMap.mp hp
  rw [Array.toList_set] at hc
  rcases List.mem_or_eq_of_mem_set hc with h | h
  · exact Or.inr (List.mem_flatMap.mpr ⟨c, h, hpc⟩)
  · exact Or.inl (h ▸ hpc)

/-- After insertIfNew a b, every entry is (a, b) or an old entry. -/
theorem mem_tlm_insertIfNew [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) (p : (a : α) × β a)
    (hp : p ∈ toListModel (m.insertIfNew a b).1.buckets) : p = ⟨a, b⟩ ∨ p ∈ toListModel m.1.buckets := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  revert hp
  unfold Raw₀.insertIfNew; dsimp only
  generalize mkIdx bs.size h (hash a) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  split
  · exact Or.inr
  · intro hp
    rcases mem_tlm_uset bs i hi _ p ((tlm_expandIfNecessary _).mem_iff.mp hp) with h' | h'
    · simp only [AssocList.toList_cons, List.mem_cons] at h'
      rcases h' with h' | h'
      · exact Or.inl h'
      · exact Or.inr (mem_tlm_of_bucket bs _ hi p (by simpa using h'))
    · exact Or.inr h'

theorem mem_replaceEntry [BEq α] (a : α) (b : β a) (l : List ((a : α) × β a)) (p : (a : α) × β a)
    (hp : p ∈ Std.Internal.List.replaceEntry a b l) : p = ⟨a, b⟩ ∨ p ∈ l := by
  induction l with
  | nil => simp [Std.Internal.List.replaceEntry] at hp
  | cons q t ih =>
    rw [Std.Internal.List.replaceEntry_cons] at hp
    cases hq : q.1 == a <;> simp only [hq, cond_true, cond_false] at hp
    · rcases List.mem_cons.mp hp with h' | h'
      · exact Or.inr (h' ▸ List.mem_cons_self)
      · rcases ih h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (List.mem_cons_of_mem _ h'')
    · rcases List.mem_cons.mp hp with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')

/-- After insert a b, every entry is (a, b) or an old entry. -/
theorem mem_tlm_insert [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) (p : (a : α) × β a)
    (hp : p ∈ toListModel (m.insert a b).1.buckets) : p = ⟨a, b⟩ ∨ p ∈ toListModel m.1.buckets := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  revert hp
  unfold Raw₀.insert; dsimp only
  generalize mkIdx bs.size h (hash a) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  split
  · intro hp
    simp only [Array.uset_eq_set, Array.set_set, Array.ugetElem_eq_getElem] at hp
    rcases mem_tlm_set bs _ hi _ p hp with h' | h'
    · rw [AssocList.toList_replace] at h'
      rcases mem_replaceEntry a b _ p h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (mem_tlm_of_bucket bs _ hi p (by simpa using h''))
    · exact Or.inr h'
  · intro hp
    rcases mem_tlm_uset bs i hi _ p ((tlm_expandIfNecessary _).mem_iff.mp hp) with h' | h'
    · simp only [AssocList.toList_cons, List.mem_cons] at h'
      rcases h' with h' | h'
      · exact Or.inl h'
      · exact Or.inr (mem_tlm_of_bucket bs _ hi p (by simpa using h'))
    · exact Or.inr h'

theorem mem_of_getKey? [BEq α] (l : AssocList α β) (a x : α) (h : l.getKey? a = some x) :
    ∃ p ∈ l.toList, p.1 = x ∧ (x == a) = true := by
  induction l with
  | nil => simp [AssocList.getKey?] at h
  | cons k v t ih =>
    simp only [AssocList.getKey?] at h
    split at h
    · cases h; exact ⟨⟨_, v⟩, by simp, rfl, by assumption⟩
    · obtain ⟨p, hp, h1, h2⟩ := ih h
      exact ⟨p, by simp [hp], h1, h2⟩

theorem mem_of_cget? {γ : Type v} [BEq α] (l : AssocList α (fun _ => γ)) (a : α) (x : γ) (h : l.get? a = some x) :
    ∃ p ∈ l.toList, p.2 = x ∧ (p.1 == a) = true := by
  induction l with
  | nil => simp [AssocList.get?] at h
  | cons k v t ih =>
    simp only [AssocList.get?] at h
    cases hk : k == a <;> simp only [hk, cond_true, cond_false] at h
    · obtain ⟨p, hp, h1, h2⟩ := ih h
      exact ⟨p, by simp [hp], h1, h2⟩
    · cases h; exact ⟨⟨k, _⟩, by simp, rfl, hk⟩

theorem raw0_getKey?_some [BEq α] [Hashable α] (m : Raw₀ α β) (a x : α) (h : m.getKey? a = some x) :
    ∃ p ∈ toListModel m.1.buckets, p.1 = x ∧ (x == a) = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  revert h
  unfold Raw₀.getKey?; dsimp only
  generalize mkIdx bs.size hb (hash a) = i
  obtain ⟨i, hi⟩ := i
  intro h
  obtain ⟨p, hp, h1, h2⟩ := mem_of_getKey? _ a x h
  exact ⟨p, mem_tlm_of_bucket bs _ hi p (by simpa using hp), h1, h2⟩

theorem raw0_cget?_some {γ : Type v} [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (a : α) (x : γ)
    (h : Raw₀.Const.get? m a = some x) : ∃ p ∈ toListModel m.1.buckets, p.2 = x ∧ (p.1 == a) = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  revert h
  unfold Raw₀.Const.get?; dsimp only
  generalize mkIdx bs.size hb (hash a) = i
  obtain ⟨i, hi⟩ := i
  intro h
  obtain ⟨p, hp, h1, h2⟩ := mem_of_cget? _ a x h
  exact ⟨p, mem_tlm_of_bucket bs _ hi p (by simpa using hp), h1, h2⟩

/-- Entries of a map built by insertListIfNewUnit satisfy any property of the start map and the list. -/
theorem tlm_insertListIfNewUnit [BEq α] [Hashable α] (P : ((_ : α) × Unit) → Prop) (l : List α) :
    ∀ (m : Raw₀ α (fun _ => Unit)), (∀ p ∈ toListModel m.1.buckets, P p) → (∀ a ∈ l, P ⟨a, ()⟩) →
      ∀ p ∈ toListModel (Raw₀.Const.insertListIfNewUnitₘ m l).1.buckets, P p := by
  induction l with
  | nil => intro m hm _; exact hm
  | cons hd tl ih =>
    intro m hm hl
    refine ih (m.insertIfNew hd ()) (fun p hp => ?_) (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    rcases mem_tlm_insertIfNew m hd () p hp with h | h
    · exact h ▸ hl hd List.mem_cons_self
    · exact hm p h

/-- Entries of a map built by Const.insertListₘ satisfy any property of the start map and the list. -/
theorem tlm_insertList {γ : Type v} [BEq α] [Hashable α] (P : ((_ : α) × γ) → Prop) (l : List (α × γ)) :
    ∀ (m : Raw₀ α (fun _ => γ)), (∀ p ∈ toListModel m.1.buckets, P p) → (∀ a ∈ l, P ⟨a.1, a.2⟩) →
      ∀ p ∈ toListModel (Raw₀.Const.insertListₘ m l).1.buckets, P p := by
  induction l with
  | nil => intro m hm _; exact hm
  | cons hd tl ih =>
    intro m hm hl
    refine ih (m.insert hd.1 hd.2) (fun p hp => ?_) (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    rcases mem_tlm_insert m hd.1 hd.2 p hp with h | h
    · exact h ▸ hl hd List.mem_cons_self
    · exact hm p h

theorem hs_ofList_raw [BEq α] [Hashable α] (l : List α) :
    (HashSet.ofList l).inner.inner.1 = (Raw₀.Const.insertListIfNewUnitₘ (Raw₀.emptyWithCapacity 8) l).1 := by
  show (Raw₀.Const.insertManyIfNewUnit _ l).1.1 = _
  rw [Raw₀.Const.insertManyIfNewUnit_eq_insertListIfNewUnitₘ]; rfl

theorem hm_ofList_raw {γ : Type v} [BEq α] [Hashable α] (l : List (α × γ)) :
    (HashMap.ofList l).inner.1 = (Raw₀.Const.insertListₘ (Raw₀.emptyWithCapacity 8) l).1 := by
  show (Raw₀.Const.insertMany _ l).1.1 = _
  rw [Raw₀.Const.insertMany_eq_insertListₘ]; rfl

/-- The keys of ofList l are elements of l. -/
theorem hs_ofList_keys [BEq α] [Hashable α] (l : List α) :
    ∀ p ∈ toListModel (HashSet.ofList l).inner.inner.1.buckets, p.1 ∈ l := by
  rw [hs_ofList_raw]
  exact tlm_insertListIfNewUnit (fun p => p.1 ∈ l) l _ (by simp) (fun a ha => ha)

/-- The entries of ofList l are elements of l. -/
theorem hm_ofList_entries {γ : Type v} [BEq α] [Hashable α] (l : List (α × γ)) :
    ∀ p ∈ toListModel (HashMap.ofList l).inner.1.buckets, (p.1, p.2) ∈ l := by
  rw [hm_ofList_raw]
  exact tlm_insertList (fun p => (p.1, p.2) ∈ l) l _ (by simp) (fun a ha => ha)

theorem hs_getKey?_ofList_none [BEq α] [Hashable α] [EquivBEq α] (l : List α) (k : α)
    (hc : l.contains k = false) :
    Raw₀.getKey? ⟨(HashSet.ofList l).inner.inner.1, (HashSet.ofList l).inner.inner.2.size_buckets_pos⟩ k = none := by
  cases hg : Raw₀.getKey? _ k with
  | none => rfl
  | some x =>
    obtain ⟨p, hp, h1, h2⟩ := raw0_getKey?_some _ k x hg
    have hx := hs_ofList_keys l p hp
    rw [h1] at hx
    have : l.contains k = true := List.contains_iff_exists_mem_beq.mpr ⟨x, hx, BEq.symm h2⟩
    simp_all

theorem hm_getKey?_ofList_none {γ : Type v} [BEq α] [Hashable α] [EquivBEq α] (l : List (α × γ)) (k : α)
    (hc : (l.map Prod.fst).contains k = false) :
    Raw₀.getKey? ⟨(HashMap.ofList l).inner.1, (HashMap.ofList l).inner.2.size_buckets_pos⟩ k = none := by
  cases hg : Raw₀.getKey? _ k with
  | none => rfl
  | some x =>
    obtain ⟨p, hp, h1, h2⟩ := raw0_getKey?_some _ k x hg
    have hx := hm_ofList_entries l p hp
    have : (l.map Prod.fst).contains k = true :=
      List.contains_iff_exists_mem_beq.mpr ⟨x, List.mem_map.mpr ⟨_, hx, h1⟩, BEq.symm h2⟩
    simp_all

theorem hm_cget?_ofList_none {γ : Type v} [BEq α] [Hashable α] [EquivBEq α] (l : List (α × γ)) (k : α)
    (hc : (l.map Prod.fst).contains k = false) :
    Raw₀.Const.get? ⟨(HashMap.ofList l).inner.1, (HashMap.ofList l).inner.2.size_buckets_pos⟩ k = none := by
  cases hg : Raw₀.Const.get? _ k with
  | none => rfl
  | some x =>
    obtain ⟨p, hp, h1, h2⟩ := raw0_cget?_some _ k x hg
    have hx := hm_ofList_entries l p hp
    have : (l.map Prod.fst).contains k = true :=
      List.contains_iff_exists_mem_beq.mpr ⟨p.1, List.mem_map.mpr ⟨_, hx, rfl⟩, BEq.symm h2⟩
    simp_all

theorem raw0_contains_false [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (h : ∀ p ∈ toListModel m.1.buckets, (p.1 == a) = false) : m.contains a = false := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.contains; dsimp only
  generalize mkIdx bs.size hb (hash a) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  rw [AssocList.contains_eq, Bool.eq_false_iff]
  intro hc
  obtain ⟨p, hp, hpa⟩ := Std.Internal.List.containsKey_eq_true_iff_exists_mem.mp hc
  have := h p (mem_tlm_of_bucket bs _ hi p (by simpa using hp))
  simp_all

theorem raw0_size_insertIfNew_of [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a)
    (hc : m.contains a = false) : (m.insertIfNew a b).1.size = m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  revert hc
  unfold Raw₀.insertIfNew Raw₀.contains; dsimp only
  generalize mkIdx bs.size h (hash a) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  intro hc
  rw [if_neg (by rw [hc]; decide)]
  simp [Raw₀.size_expandIfNecessary]

theorem raw0_size_insert_of [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a)
    (hc : m.contains a = false) : (m.insert a b).1.size = m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  revert hc
  unfold Raw₀.insert Raw₀.contains; dsimp only
  generalize mkIdx bs.size h (hash a) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  intro hc
  rw [if_neg (by rw [hc]; decide)]
  simp [Raw₀.size_expandIfNecessary]

theorem size_insertListIfNewUnit_le [BEq α] [Hashable α] (l : List α) :
    ∀ (m : Raw₀ α (fun _ => Unit)), (Raw₀.Const.insertListIfNewUnitₘ m l).1.size ≤ m.1.size + l.length := by
  induction l with
  | nil => intro m; exact Nat.le_refl _
  | cons hd tl ih =>
    intro m
    have := ih (m.insertIfNew hd ())
    have := (raw0_size_insertIfNew m hd ()).2
    show (Raw₀.Const.insertListIfNewUnitₘ (m.insertIfNew hd ()) tl).1.size ≤ _
    simp only [List.length_cons]; omega

theorem size_insertList_le {γ : Type v} [BEq α] [Hashable α] (l : List (α × γ)) :
    ∀ (m : Raw₀ α (fun _ => γ)), (Raw₀.Const.insertListₘ m l).1.size ≤ m.1.size + l.length := by
  induction l with
  | nil => intro m; exact Nat.le_refl _
  | cons hd tl ih =>
    intro m
    have := ih (m.insert hd.1 hd.2)
    have := (raw0_size_insert m hd.1 hd.2).2
    show (Raw₀.Const.insertListₘ (m.insert hd.1 hd.2) tl).1.size ≤ _
    simp only [List.length_cons]; omega

theorem size_insertListIfNewUnit_eq [BEq α] [Hashable α] (l : List α)
    (hl : l.Pairwise (fun a b => (a == b) = false)) :
    ∀ (m : Raw₀ α (fun _ => Unit)), (∀ p ∈ toListModel m.1.buckets, ∀ y ∈ l, (p.1 == y) = false) →
      (Raw₀.Const.insertListIfNewUnitₘ m l).1.size = m.1.size + l.length := by
  induction l with
  | nil => intro m _; rfl
  | cons hd tl ih =>
    intro m hm
    have hl' := List.pairwise_cons.mp hl
    have h1 := raw0_size_insertIfNew_of m hd () (raw0_contains_false m hd (fun p hp => hm p hp hd List.mem_cons_self))
    have h2 := ih hl'.2 (m.insertIfNew hd ()) (fun p hp y hy => by
      rcases mem_tlm_insertIfNew m hd () p hp with h | h
      · subst h; exact hl'.1 y hy
      · exact hm p h y (List.mem_cons_of_mem _ hy))
    show (Raw₀.Const.insertListIfNewUnitₘ (m.insertIfNew hd ()) tl).1.size = _
    simp only [List.length_cons]; omega

theorem size_insertList_eq {γ : Type v} [BEq α] [Hashable α] (l : List (α × γ))
    (hl : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    ∀ (m : Raw₀ α (fun _ => γ)), (∀ p ∈ toListModel m.1.buckets, ∀ y ∈ l, (p.1 == y.1) = false) →
      (Raw₀.Const.insertListₘ m l).1.size = m.1.size + l.length := by
  induction l with
  | nil => intro m _; rfl
  | cons hd tl ih =>
    intro m hm
    have hl' := List.pairwise_cons.mp hl
    have h1 := raw0_size_insert_of m hd.1 hd.2 (raw0_contains_false m hd.1 (fun p hp => hm p hp hd List.mem_cons_self))
    have h2 := ih hl'.2 (m.insert hd.1 hd.2) (fun p hp y hy => by
      rcases mem_tlm_insert m hd.1 hd.2 p hp with h | h
      · subst h; exact hl'.1 y hy
      · exact hm p h y (List.mem_cons_of_mem _ hy))
    show (Raw₀.Const.insertListₘ (m.insert hd.1 hd.2) tl).1.size = _
    simp only [List.length_cons]; omega

theorem hsr_ofList_raw [BEq α] [Hashable α] (l : List α) :
    (HashSet.Raw.ofList l).inner.inner = (Raw₀.Const.insertListIfNewUnitₘ (Raw₀.emptyWithCapacity 8) l).1 := by
  show DHashMap.Raw.Const.insertManyIfNewUnit ∅ l = _
  unfold DHashMap.Raw.Const.insertManyIfNewUnit
  rw [dif_pos (show 0 < (∅ : DHashMap.Raw α (fun _ => Unit)).buckets.size from (Raw₀.emptyWithCapacity 8).2)]
  rw [Raw₀.Const.insertManyIfNewUnit_eq_insertListIfNewUnitₘ]; rfl

theorem hmr_ofList_raw {γ : Type v} [BEq α] [Hashable α] (l : List (α × γ)) :
    (HashMap.Raw.ofList l).inner = (Raw₀.Const.insertListₘ (Raw₀.emptyWithCapacity 8) l).1 := by
  show DHashMap.Raw.Const.insertMany ∅ l = _
  unfold DHashMap.Raw.Const.insertMany
  rw [dif_pos (show 0 < (∅ : DHashMap.Raw α (fun _ => γ)).buckets.size from (Raw₀.emptyWithCapacity 8).2)]
  rw [Raw₀.Const.insertMany_eq_insertListₘ]; rfl

theorem mem_of_getKey [BEq α] (l : AssocList α β) (a : α) (h : l.contains a = true) :
    ∃ p ∈ l.toList, p.1 = l.getKey a h ∧ (p.1 == a) = true := by
  induction l with
  | nil => simp [AssocList.contains] at h
  | cons k v t ih =>
    by_cases hk : (k == a) = true
    · exact ⟨⟨k, v⟩, by simp, by simp [AssocList.getKey, hk], hk⟩
    · have ht : t.contains a = true := by simp_all [AssocList.contains]
      obtain ⟨p, hp, h1, h2⟩ := ih ht
      refine ⟨p, by simp [hp], ?_, h2⟩
      rw [h1]; simp [AssocList.getKey, hk]

theorem mem_of_cget {γ : Type v} [BEq α] (l : AssocList α (fun _ => γ)) (a : α) (h : l.contains a = true) :
    ∃ p ∈ l.toList, p.2 = l.get a h ∧ (p.1 == a) = true := by
  induction l with
  | nil => simp [AssocList.contains] at h
  | cons k v t ih =>
    by_cases hk : (k == a) = true
    · exact ⟨⟨k, v⟩, by simp, by simp [AssocList.get, hk], hk⟩
    · have ht : t.contains a = true := by simp_all [AssocList.contains]
      obtain ⟨p, hp, h1, h2⟩ := ih ht
      refine ⟨p, by simp [hp], ?_, h2⟩
      rw [h1]; simp [AssocList.get, hk]

theorem raw0_getKey_mem [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (h : m.contains a = true) :
    ∃ p ∈ toListModel m.1.buckets, p.1 = m.getKey a h ∧ (p.1 == a) = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  obtain ⟨p, hp, h1, h2⟩ := mem_of_getKey (bs[(mkIdx bs.size hb (hash a)).1]'(mkIdx bs.size hb (hash a)).2) a h
  exact ⟨p, mem_tlm_of_bucket bs _ (mkIdx bs.size hb (hash a)).2 p (by simpa using hp), h1, h2⟩

theorem raw0_cget_mem {γ : Type v} [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (a : α) (h : m.contains a = true) :
    ∃ p ∈ toListModel m.1.buckets, p.2 = Raw₀.Const.get m a h ∧ (p.1 == a) = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  obtain ⟨p, hp, h1, h2⟩ := mem_of_cget (bs[(mkIdx bs.size hb (hash a)).1]'(mkIdx bs.size hb (hash a)).2) a h
  exact ⟨p, mem_tlm_of_bucket bs _ (mkIdx bs.size hb (hash a)).2 p (by simpa using hp), h1, h2⟩

/-- In a list without ==-related pairs, ==-related members are equal. -/
theorem pw_unique {γ : Type w} [BEq α] [PartialEquivBEq α] (f : γ → α) (l : List γ)
    (hl : l.Pairwise (fun a b => (f a == f b) = false)) (x y : γ) (hx : x ∈ l) (hy : y ∈ l)
    (hxy : (f x == f y) = true) : x = y := by
  induction l with
  | nil => simp at hx
  | cons c t ih =>
    have hl' := List.pairwise_cons.mp hl
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · have := hl'.1 y hy'; simp_all
    · have := hl'.1 x hx'; have := BEq.symm hxy; simp_all
    · exact ih hl'.2 hx' hy'

theorem hsr_ofList_keys [BEq α] [Hashable α] (l : List α) :
    ∀ p ∈ toListModel (HashSet.Raw.ofList l).inner.inner.buckets, p.1 ∈ l := by
  rw [hsr_ofList_raw]
  exact tlm_insertListIfNewUnit (fun p => p.1 ∈ l) l _ (by simp) (fun a ha => ha)

theorem hmr_ofList_entries {γ : Type v} [BEq α] [Hashable α] (l : List (α × γ)) :
    ∀ p ∈ toListModel (HashMap.Raw.ofList l).inner.buckets, (p.1, p.2) ∈ l := by
  rw [hmr_ofList_raw]
  exact tlm_insertList (fun p => (p.1, p.2) ∈ l) l _ (by simp) (fun a ha => ha)

theorem dr_getKey_eq [BEq α] [Hashable α] (m : DHashMap.Raw α β) (a : α) (h : a ∈ m) :
    ∃ hb hc, m.getKey a h = Raw₀.getKey ⟨m, hb⟩ a hc := ⟨_, _, rfl⟩

theorem dr_cget_eq {γ : Type v} [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => γ)) (a : α) (h : a ∈ m) :
    ∃ hb hc, DHashMap.Raw.Const.get m a h = Raw₀.Const.get ⟨m, hb⟩ a hc := ⟨_, _, rfl⟩

theorem tlm_insertIfNew_ne_nil [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    toListModel (m.insertIfNew a b).1.buckets ≠ [] := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.insertIfNew; dsimp only
  generalize mkIdx bs.size h (hash a) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  split
  · rename_i hc
    rw [AssocList.contains_eq] at hc
    obtain ⟨p, hp, -⟩ := Std.Internal.List.containsKey_eq_true_iff_exists_mem.mp hc
    exact List.ne_nil_of_mem (mem_tlm_of_bucket bs _ hi p (by simpa using hp))
  · obtain ⟨l, -, h₂, -⟩ := exists_bucket_of_uset bs i hi (AssocList.cons a b bs[i])
    exact List.ne_nil_of_mem (a := ⟨a, b⟩) ((tlm_expandIfNecessary _).mem_iff.mpr (h₂.mem_iff.mpr (by simp)))

theorem tlm_insert_ne_nil [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    toListModel (m.insert a b).1.buckets ≠ [] := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.insert; dsimp only
  generalize mkIdx bs.size h (hash a) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  split
  · rename_i hc
    simp only [Array.uset_eq_set, Array.set_set, Array.ugetElem_eq_getElem] at hc ⊢
    have hne : ∃ k v t, bs[i.toNat] = AssocList.cons k v t := by
      cases hb : bs[i.toNat] with
      | nil => rw [hb] at hc; simp [AssocList.contains] at hc
      | cons k v t => exact ⟨k, v, t, rfl⟩
    obtain ⟨k, v, t, hb⟩ := hne
    have : ∃ q, q ∈ (AssocList.replace a b bs[i.toNat]).toList := by
      rw [hb]; simp only [AssocList.replace]; cases k == a <;> simp
    obtain ⟨q, hq⟩ := this
    refine List.ne_nil_of_mem (a := q) ?_
    unfold toListModel
    exact List.mem_flatMap.mpr ⟨_, by rw [Array.toList_set]; exact List.mem_set hi _, hq⟩
  · obtain ⟨l, -, h₂, -⟩ := exists_bucket_of_uset bs i hi (AssocList.cons a b bs[i])
    exact List.ne_nil_of_mem (a := ⟨a, b⟩) ((tlm_expandIfNecessary _).mem_iff.mpr (h₂.mem_iff.mpr (by simp)))

theorem tlm_insertListIfNewUnit_ne_nil [BEq α] [Hashable α] (tl : List α) :
    ∀ (m : Raw₀ α (fun _ => Unit)) (hd : α), toListModel (Raw₀.Const.insertListIfNewUnitₘ m (hd :: tl)).1.buckets ≠ [] := by
  induction tl with
  | nil => intro m hd; exact tlm_insertIfNew_ne_nil m hd ()
  | cons hd' tl ih => intro m hd; exact ih (m.insertIfNew hd ()) hd'

theorem tlm_insertList_ne_nil {γ : Type v} [BEq α] [Hashable α] (tl : List (α × γ)) :
    ∀ (m : Raw₀ α (fun _ => γ)) (hd : α × γ), toListModel (Raw₀.Const.insertListₘ m (hd :: tl)).1.buckets ≠ [] := by
  induction tl with
  | nil => intro m hd; exact tlm_insert_ne_nil m hd.1 hd.2
  | cons hd' tl ih => intro m hd; exact ih (m.insert hd.1 hd.2) hd'

theorem mkIdx_val_congr {sz sz' : Nat} (e : sz = sz') (h : 0 < sz) (h' : 0 < sz') (x : UInt64) :
    (mkIdx sz h x).1 = (mkIdx sz' h' x).1 := by subst e; rfl

theorem assoc_contains_cmodify {γ : Type v} [BEq α] [EquivBEq α] (k : α) (f : γ → γ)
    (l : AssocList α (fun _ => γ)) (a : α) : (AssocList.Const.modify k f l).contains a = l.contains a := by
  induction l with
  | nil => rfl
  | cons x v t ih =>
    simp only [AssocList.Const.modify]
    by_cases hx : (x == k) = true
    · simp only [hx, ite_true, AssocList.contains]
      congr 1
      cases hka : k == a <;> cases hxa : x == a <;> try rfl
      · exact absurd (BEq.trans (BEq.symm hx) hxa) (by simp [hka])
      · exact absurd (BEq.trans hx hka) (by simp [hxa])
    · simp only [hx, Bool.false_eq_true, ite_false, AssocList.contains, ih]

theorem raw0_contains_set {γ : Type v} [BEq α] [Hashable α] (s : Nat) (bs : Array (AssocList α (fun _ => γ)))
    (j : Nat) (hj : j < bs.size) (X : AssocList α (fun _ => γ)) (hX : ∀ a, X.contains a = (bs[j]).contains a)
    (h1 : 0 < (bs.set j X hj).size) (h2 : 0 < bs.size) (a : α) :
    Raw₀.contains ⟨⟨s, bs.set j X hj⟩, h1⟩ a = Raw₀.contains ⟨⟨s, bs⟩, h2⟩ a := by
  have hs : (bs.set j X hj).size = bs.size := Array.size_set ..
  unfold Raw₀.contains; dsimp only
  rw [show mkIdx (bs.set j X hj).size h1 (hash a) =
      ⟨(mkIdx bs.size h2 (hash a)).1, by rw [hs]; exact (mkIdx bs.size h2 (hash a)).2⟩ from
    Subtype.ext (mkIdx_val_congr hs _ _ _)]
  generalize mkIdx bs.size h2 (hash a) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  simp only [Array.ugetElem_eq_getElem, Array.getElem_set]
  split
  · subst_vars; exact hX a
  · rfl

theorem raw0_contains_cmodify {γ : Type v} [BEq α] [EquivBEq α] [Hashable α] (m : Raw₀ α (fun _ => γ))
    (k k' : α) (f : γ → γ) : (Raw₀.Const.modify m k f).contains k' = m.contains k' := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.Const.modify; dsimp only
  generalize mkIdx bs.size h (hash k) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  split
  · simp only [Array.uset_eq_set, Array.set_set, Array.ugetElem_eq_getElem]
    exact raw0_contains_set s bs _ hi _ (assoc_contains_cmodify k f _) _ h k'
  · rfl

/-- BEq by hash equality: lawful for any Hashable (used to borrow isHashSelf_expand). -/
abbrev hashBEq (α : Type u) [Hashable α] : BEq α := ⟨fun a b => hash a == hash b⟩
theorem hashBEq_equiv [Hashable α] : @EquivBEq α (hashBEq α) :=
  @EquivBEq.mk α (hashBEq α)
    (@PartialEquivBEq.mk α (hashBEq α)
      (fun {a b} h => by
        change (hash a == hash b) = true at h; change (hash b == hash a) = true
        simp only [beq_iff_eq] at *; exact h.symm)
      (fun {a b c} h₁ h₂ => by
        change (hash a == hash b) = true at h₁; change (hash b == hash c) = true at h₂
        change (hash a == hash c) = true
        simp only [beq_iff_eq] at *; exact h₁.trans h₂))
    (@ReflBEq.mk α (hashBEq α) (fun {a} => by change (hash a == hash a) = true; simp))
theorem hashBEq_lawful [Hashable α] : @LawfulHashable α (hashBEq α) _ :=
  @LawfulHashable.mk α (hashBEq α) _ (fun a b h => by
    change (hash a == hash b) = true at h; simpa using h)

theorem ihs_congr [Hashable α] (i₁ i₂ : BEq α) (bs : Array (AssocList α β)) (h : @IsHashSelf α β i₁ _ bs) :
    @IsHashSelf α β i₂ _ bs :=
  @IsHashSelf.mk α β i₂ _ bs (fun i hi =>
    @List.HashesTo.mk α β i₂ _ _ i _ (fun h0 p hp =>
      @List.HashesTo.hash_self α β i₁ _ _ i _ (@IsHashSelf.hashes_to α β i₁ _ bs h i hi) h0 p hp))

theorem ihs_expand [BEq α] [Hashable α] (buckets : { d : Array (AssocList α β) // 0 < d.size }) :
    IsHashSelf (Raw₀.expand buckets).1 :=
  ihs_congr (hashBEq α) _ _ (@Raw₀.isHashSelf_expand α β (hashBEq α) _ hashBEq_lawful hashBEq_equiv buckets)

theorem tlm_expand [BEq α] [Hashable α] (buckets : { d : Array (AssocList α β) // 0 < d.size }) :
    List.Perm (toListModel (Raw₀.expand buckets).1) (toListModel buckets.1) :=
  @Raw₀.toListModel_expand α β (falseBEq α) _ falsePEq buckets

theorem contains_of_mem_ihs [BEq α] [ReflBEq α] [Hashable α] (s : Nat) (bs : Array (AssocList α β))
    (h : 0 < bs.size) (hs : IsHashSelf bs) (p : (a : α) × β a) (hp : p ∈ toListModel bs) :
    Raw₀.contains ⟨⟨s, bs⟩, h⟩ p.1 = true := by
  obtain ⟨c, hc, hpc⟩ := List.mem_flatMap.mp hp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  have hj' : j < bs.size := by simpa using hj
  have hx := (hs.hashes_to j hj').hash_self h p (by simpa using hpc)
  unfold Raw₀.contains; dsimp only
  revert hx
  generalize mkIdx bs.size h (hash p.1) = I
  obtain ⟨i, hi⟩ := I
  intro hx
  dsimp only at hx ⊢
  simp only [Array.ugetElem_eq_getElem, AssocList.contains_eq]
  subst hx
  exact Std.Internal.List.containsKey_of_mem (by simpa using hpc)

theorem contains_expand_cons [BEq α] [ReflBEq α] [Hashable α] (s : Nat) (bs : Array (AssocList α β))
    (h : 0 < bs.size) (a : α) (b : β a) (i : USize) (hi : i.toNat < bs.size)
    (hI : mkIdx bs.size h (hash a) = ⟨i, hi⟩) (h' : 0 < (bs.uset i (AssocList.cons a b bs[i]) hi).size) :
    (Raw₀.expandIfNecessary ⟨⟨s, bs.uset i (AssocList.cons a b bs[i]) hi⟩, h'⟩).contains a = true := by
  unfold Raw₀.expandIfNecessary; dsimp only
  split
  · unfold Raw₀.contains; dsimp only
    rw [show mkIdx (bs.uset i (AssocList.cons a b bs[i]) hi).size h' (hash a) = ⟨i, by simpa using hi⟩ from
      Subtype.ext ((mkIdx_val_congr (by simp) _ h _).trans (congrArg Subtype.val hI))]
    simp [AssocList.contains]
  · generalize hE : Raw₀.expand ⟨bs.uset i (AssocList.cons a b bs[i]) hi, _⟩ = E
    obtain ⟨b', hb'⟩ := E
    have hs := ihs_expand (β := β) ⟨bs.uset i (AssocList.cons a b bs[i]) hi, h'⟩
    have hp := tlm_expand (β := β) ⟨bs.uset i (AssocList.cons a b bs[i]) hi, h'⟩
    rw [hE] at hs hp
    obtain ⟨l, -, h₂, -⟩ := exists_bucket_of_uset bs i hi (AssocList.cons a b bs[i])
    exact contains_of_mem_ihs s b' hb' hs ⟨a, b⟩ (hp.mem_iff.mpr (h₂.mem_iff.mpr (by simp)))

theorem raw0_contains_insertIfNew_self [BEq α] [ReflBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insertIfNew a b).contains a = true := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.insertIfNew; dsimp only
  generalize hI : mkIdx bs.size h (hash a) = I
  obtain ⟨i, hi⟩ := I
  dsimp only
  split
  · rename_i hc
    unfold Raw₀.contains; dsimp only; rw [hI]; exact hc
  · exact contains_expand_cons _ bs h a b i hi hI _

theorem raw0_contains_insert_self [BEq α] [EquivBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insert a b).contains a = true := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.insert; dsimp only
  generalize hI : mkIdx bs.size h (hash a) = I
  obtain ⟨i, hi⟩ := I
  dsimp only
  split
  · rename_i hc
    simp only [Array.uset_eq_set, Array.set_set, Array.ugetElem_eq_getElem] at hc ⊢
    unfold Raw₀.contains; dsimp only
    rw [show mkIdx (bs.set i.toNat (AssocList.replace a b bs[i.toNat]) hi).size (by simpa using h) (hash a) =
        ⟨i, by simpa using hi⟩ from
      Subtype.ext ((mkIdx_val_congr (by simp) _ h _).trans (congrArg Subtype.val hI))]
    simp only [Array.ugetElem_eq_getElem, Array.getElem_set_self, AssocList.contains_eq, AssocList.toList_replace,
      Std.Internal.List.containsKey_replaceEntry]
    simpa [AssocList.contains_eq] using hc
  · exact contains_expand_cons _ bs h a b i hi hI _

end Removable
end HashInstHand

-- `Std.HashSet.isSome_get?_iff_mem`: removable: get? and contains search the same bucket with the same BEq, for any
-- instances.
theorem HashSet.isSome_get?_iff_mem_h4 : drop% Std.HashSet.isSome_get?_iff_mem 4 := by
  intro α _ _ m _ a
  rw [HashSet.mem_iff_contains]
  exact iff_of_eq (congrArg (· = true) (raw0_isSome_getKey? ⟨m.inner.inner.1, m.inner.inner.2.size_buckets_pos⟩ a))

-- `Std.HashSet.isSome_get?_iff_mem`: removable: get? and contains search the same bucket with the same BEq, for any
-- instances.
theorem HashSet.isSome_get?_iff_mem_h5 : drop% Std.HashSet.isSome_get?_iff_mem 5 := by
  intro α _ _ m _ a
  rw [HashSet.mem_iff_contains]
  exact iff_of_eq (congrArg (· = true) (raw0_isSome_getKey? ⟨m.inner.inner.1, m.inner.inner.2.size_buckets_pos⟩ a))

-- `Std.HashMap.isSome_getElem?_iff_mem`: removable: m[a]? and contains search the same bucket with the same BEq,
-- for any instances.
theorem HashMap.isSome_getElem?_iff_mem_h5 : drop% Std.HashMap.isSome_getElem?_iff_mem 5 := by
  intro α β _ _ m _ a
  rw [HashMap.mem_iff_contains]
  exact iff_of_eq (congrArg (· = true) (raw0_isSome_cget? ⟨m.inner.1, m.inner.2.size_buckets_pos⟩ a))

-- `Std.HashMap.isSome_getElem?_iff_mem`: removable: m[a]? and contains search the same bucket with the same BEq,
-- for any instances.
theorem HashMap.isSome_getElem?_iff_mem_h6 : drop% Std.HashMap.isSome_getElem?_iff_mem 6 := by
  intro α β _ _ m _ a
  rw [HashMap.mem_iff_contains]
  exact iff_of_eq (congrArg (· = true) (raw0_isSome_cget? ⟨m.inner.1, m.inner.2.size_buckets_pos⟩ a))

-- `Std.ExtHashSet.emptyWithCapacity_eq`: removable: both maps have no entries, so they are equivalent for any
-- instances.
theorem ExtHashSet.emptyWithCapacity_eq_h3 : drop% Std.ExtHashSet.emptyWithCapacity_eq 3 := by
  intro α _ _ _ c
  show ExtHashSet.mk (ExtHashMap.mk (ExtDHashMap.mk (DHashMap.emptyWithCapacity c))) =
    ExtHashSet.mk (ExtHashMap.mk (ExtDHashMap.mk (DHashMap.emptyWithCapacity 8)))
  exact congrArg _ (congrArg _ (congrArg ExtDHashMap.mk' (Quotient.sound ⟨⟨by
    show List.Perm (toListModel (Raw₀.emptyWithCapacity c : Raw₀ α _).1.buckets)
      (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets)
    simp⟩⟩)))

-- `Std.ExtHashSet.emptyWithCapacity_eq`: removable: both maps have no entries, so they are equivalent for any
-- instances.
theorem ExtHashSet.emptyWithCapacity_eq_h4 : drop% Std.ExtHashSet.emptyWithCapacity_eq 4 := by
  intro α _ _ _ c
  show ExtHashSet.mk (ExtHashMap.mk (ExtDHashMap.mk (DHashMap.emptyWithCapacity c))) =
    ExtHashSet.mk (ExtHashMap.mk (ExtDHashMap.mk (DHashMap.emptyWithCapacity 8)))
  exact congrArg _ (congrArg _ (congrArg ExtDHashMap.mk' (Quotient.sound ⟨⟨by
    show List.Perm (toListModel (Raw₀.emptyWithCapacity c : Raw₀ α _).1.buckets)
      (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets)
    simp⟩⟩)))

-- `Std.HashSet.Raw.size_le_size_insertMany`: removable: insertIfNew never decreases the size field (any instances).
theorem HashSet.Raw.size_le_size_insertMany_h6 : drop% Std.HashSet.Raw.size_le_size_insertMany 6 := by
  intro α m _ _ ρ _ _ h l
  have hb : 0 < m.inner.inner.buckets.size := h.out.out.size_buckets_pos
  show m.inner.inner.size ≤ (DHashMap.Raw.Const.insertManyIfNewUnit m.inner.inner l).size
  simp only [DHashMap.Raw.Const.insertManyIfNewUnit, hb, dite_true]
  exact (Raw₀.Const.insertManyIfNewUnit ⟨m.inner.inner, hb⟩ l).2 (fun m'' => m.inner.inner.size ≤ m''.1.size)
    (fun h' => Nat.le_trans h' (raw0_size_insertIfNew _ _ _).1) (Nat.le_refl _)

-- `Std.HashSet.Raw.size_le_size_insertMany`: removable: insertIfNew never decreases the size field (any instances).
theorem HashSet.Raw.size_le_size_insertMany_h7 : drop% Std.HashSet.Raw.size_le_size_insertMany 7 := by
  intro α m _ _ ρ _ _ h l
  have hb : 0 < m.inner.inner.buckets.size := h.out.out.size_buckets_pos
  show m.inner.inner.size ≤ (DHashMap.Raw.Const.insertManyIfNewUnit m.inner.inner l).size
  simp only [DHashMap.Raw.Const.insertManyIfNewUnit, hb, dite_true]
  exact (Raw₀.Const.insertManyIfNewUnit ⟨m.inner.inner, hb⟩ l).2 (fun m'' => m.inner.inner.size ≤ m''.1.size)
    (fun h' => Nat.le_trans h' (raw0_size_insertIfNew _ _ _).1) (Nat.le_refl _)

-- `Std.HashMap.Raw.size_le_size_insertMany`: removable: insert never decreases the size field (any instances).
theorem HashMap.Raw.size_le_size_insertMany_h7 : drop% Std.HashMap.Raw.size_le_size_insertMany 7 := by
  intro α β m _ _ ρ _ _ h l
  have hb : 0 < m.inner.buckets.size := h.out.size_buckets_pos
  show m.inner.size ≤ (DHashMap.Raw.Const.insertMany m.inner l).size
  simp only [DHashMap.Raw.Const.insertMany, hb, dite_true]
  exact (Raw₀.Const.insertMany ⟨m.inner, hb⟩ l).2 (fun m'' => m.inner.size ≤ m''.1.size)
    (fun h' => Nat.le_trans h' (raw0_size_insert _ _ _).1) (Nat.le_refl _)

-- `Std.HashMap.Raw.size_le_size_insertMany`: removable: insert never decreases the size field (any instances).
theorem HashMap.Raw.size_le_size_insertMany_h8 : drop% Std.HashMap.Raw.size_le_size_insertMany 8 := by
  intro α β m _ _ ρ _ _ h l
  have hb : 0 < m.inner.buckets.size := h.out.size_buckets_pos
  show m.inner.size ≤ (DHashMap.Raw.Const.insertMany m.inner l).size
  simp only [DHashMap.Raw.Const.insertMany, hb, dite_true]
  exact (Raw₀.Const.insertMany ⟨m.inner, hb⟩ l).2 (fun m'' => m.inner.size ≤ m''.1.size)
    (fun h' => Nat.le_trans h' (raw0_size_insert _ _ _).1) (Nat.le_refl _)

-- `Std.HashMap.Raw.filterMap_equiv_map`: removable: both sides have the same entries (toListModel_filterMap and
-- toListModel_map hold for any instances).
theorem HashMap.Raw.filterMap_equiv_map_h6 : drop% Std.HashMap.Raw.filterMap_equiv_map 6 := by
  intro α β γ _ _ m _ f h
  have hb : 0 < m.inner.buckets.size := h.out.size_buckets_pos
  refine ⟨⟨?_⟩⟩
  simp only [HashMap.Raw.filterMap, HashMap.Raw.map, DHashMap.Raw.filterMap, DHashMap.Raw.map, hb, dite_true]
  refine Raw₀.toListModel_filterMap.trans (List.Perm.trans ?_ Raw₀.toListModel_map.symm)
  simp

-- `Std.HashMap.Raw.filterMap_equiv_map`: removable: both sides have the same entries (toListModel_filterMap and
-- toListModel_map hold for any instances).
theorem HashMap.Raw.filterMap_equiv_map_h7 : drop% Std.HashMap.Raw.filterMap_equiv_map 7 := by
  intro α β γ _ _ m _ f h
  have hb : 0 < m.inner.buckets.size := h.out.size_buckets_pos
  refine ⟨⟨?_⟩⟩
  simp only [HashMap.Raw.filterMap, HashMap.Raw.map, DHashMap.Raw.filterMap, DHashMap.Raw.map, hb, dite_true]
  refine Raw₀.toListModel_filterMap.trans (List.Perm.trans ?_ Raw₀.toListModel_map.symm)
  simp

-- `Std.HashSet.get?_ofList_of_contains_eq_false`: removable: with EquivBEq a key found for k is an element x of l
-- with x == k, so k == x and l.contains k; bucket placement does not matter.
theorem HashSet.get?_ofList_of_contains_eq_false_h4 : drop% Std.HashSet.get?_ofList_of_contains_eq_false 4 := by
  intro α _ _ _ l k hc
  exact hs_getKey?_ofList_none l k hc

-- `Std.HashSet.get!_ofList_of_contains_eq_false`: removable: with EquivBEq a key found for k is an element x of l
-- with x == k, so k == x and l.contains k; bucket placement does not matter.
theorem HashSet.get!_ofList_of_contains_eq_false_h4 : drop% Std.HashSet.get!_ofList_of_contains_eq_false 4 := by
  intro α _ _ _ _ l k hc
  show Raw₀.getKey! ⟨_, (HashSet.ofList l).inner.inner.2.size_buckets_pos⟩ k = default
  rw [Raw₀.getKey!_eq_getKey!ₘ]; unfold Raw₀.getKey!ₘ
  rw [← Raw₀.getKey?_eq_getKey?ₘ, hs_getKey?_ofList_none l k hc]; rfl

-- `Std.HashSet.getD_ofList_of_contains_eq_false`: removable: with EquivBEq a key found for k is an element x of l
-- with x == k, so k == x and l.contains k; bucket placement does not matter.
theorem HashSet.getD_ofList_of_contains_eq_false_h4 : drop% Std.HashSet.getD_ofList_of_contains_eq_false 4 := by
  intro α _ _ _ l k fb hc
  show Raw₀.getKeyD ⟨_, (HashSet.ofList l).inner.inner.2.size_buckets_pos⟩ k fb = fb
  rw [Raw₀.getKeyD_eq_getKeyDₘ]; unfold Raw₀.getKeyDₘ
  rw [← Raw₀.getKey?_eq_getKey?ₘ, hs_getKey?_ofList_none l k hc]; rfl

-- `Std.HashMap.getElem?_ofList_of_contains_eq_false`: removable: with EquivBEq an entry found for k has a key x in
-- l with x == k, so k == x and the key list contains k; bucket placement does not matter.
theorem HashMap.getElem?_ofList_of_contains_eq_false_h5 :
    drop% Std.HashMap.getElem?_ofList_of_contains_eq_false 5 := by
  intro α β _ _ _ l k hc
  exact hm_cget?_ofList_none l k hc

-- `Std.HashMap.getElem!_ofList_of_contains_eq_false`: removable: with EquivBEq an entry found for k has a key x in
-- l with x == k, so k == x and the key list contains k; bucket placement does not matter.
theorem HashMap.getElem!_ofList_of_contains_eq_false_h5 :
    drop% Std.HashMap.getElem!_ofList_of_contains_eq_false 5 := by
  intro α β _ _ _ l k _ hc
  show Raw₀.Const.get! ⟨_, (HashMap.ofList l).inner.2.size_buckets_pos⟩ k = default
  rw [Raw₀.Const.get!_eq_get!ₘ]; unfold Raw₀.Const.get!ₘ
  rw [← Raw₀.Const.get?_eq_get?ₘ, hm_cget?_ofList_none l k hc]; rfl

-- `Std.HashMap.getD_ofList_of_contains_eq_false`: removable: with EquivBEq an entry found for k has a key x in l
-- with x == k, so k == x and the key list contains k; bucket placement does not matter.
theorem HashMap.getD_ofList_of_contains_eq_false_h5 : drop% Std.HashMap.getD_ofList_of_contains_eq_false 5 := by
  intro α β _ _ _ l k fb hc
  show Raw₀.Const.getD ⟨_, (HashMap.ofList l).inner.2.size_buckets_pos⟩ k fb = fb
  rw [Raw₀.Const.getD_eq_getDₘ]; unfold Raw₀.Const.getDₘ
  rw [← Raw₀.Const.get?_eq_get?ₘ, hm_cget?_ofList_none l k hc]; rfl

-- `Std.HashMap.getKey?_ofList_of_contains_eq_false`: removable: with EquivBEq a key found for k is a key x of l
-- with x == k, so k == x and the key list contains k; bucket placement does not matter.
theorem HashMap.getKey?_ofList_of_contains_eq_false_h5 :
    drop% Std.HashMap.getKey?_ofList_of_contains_eq_false 5 := by
  intro α β _ _ _ l k hc
  exact hm_getKey?_ofList_none l k hc

-- `Std.HashMap.getKey!_ofList_of_contains_eq_false`: removable: with EquivBEq a key found for k is a key x of l
-- with x == k, so k == x and the key list contains k; bucket placement does not matter.
theorem HashMap.getKey!_ofList_of_contains_eq_false_h5 :
    drop% Std.HashMap.getKey!_ofList_of_contains_eq_false 5 := by
  intro α β _ _ _ _ l k hc
  show Raw₀.getKey! ⟨_, (HashMap.ofList l).inner.2.size_buckets_pos⟩ k = default
  rw [Raw₀.getKey!_eq_getKey!ₘ]; unfold Raw₀.getKey!ₘ
  rw [← Raw₀.getKey?_eq_getKey?ₘ, hm_getKey?_ofList_none l k hc]; rfl

-- `Std.HashMap.getKeyD_ofList_of_contains_eq_false`: removable: with EquivBEq a key found for k is a key x of l
-- with x == k, so k == x and the key list contains k; bucket placement does not matter.
theorem HashMap.getKeyD_ofList_of_contains_eq_false_h5 :
    drop% Std.HashMap.getKeyD_ofList_of_contains_eq_false 5 := by
  intro α β _ _ _ l k fb hc
  show Raw₀.getKeyD ⟨_, (HashMap.ofList l).inner.2.size_buckets_pos⟩ k fb = fb
  rw [Raw₀.getKeyD_eq_getKeyDₘ]; unfold Raw₀.getKeyDₘ
  rw [← Raw₀.getKey?_eq_getKey?ₘ, hm_getKey?_ofList_none l k hc]; rfl

-- `Std.HashSet.Raw.size_ofList_le`: removable: each insertIfNew adds at most one to the size field (any instances).
theorem HashSet.Raw.size_ofList_le_h3 : drop% Std.HashSet.Raw.size_ofList_le 3 := by
  intro α _ _ _ l
  show (HashSet.Raw.ofList l).inner.inner.size ≤ _
  rw [hsr_ofList_raw]
  simpa using size_insertListIfNewUnit_le l (Raw₀.emptyWithCapacity 8)

-- `Std.HashSet.Raw.size_ofList`: removable: for a list without ==-related pairs (earlier == later is false), no
-- inserted element finds an earlier one, so each insertIfNew adds one (any instances).
theorem HashSet.Raw.size_ofList_h3 : drop% Std.HashSet.Raw.size_ofList 3 := by
  intro α _ _ _ l hl
  show (HashSet.Raw.ofList l).inner.inner.size = _
  rw [hsr_ofList_raw]
  simpa using size_insertListIfNewUnit_eq l hl (Raw₀.emptyWithCapacity 8) (by simp)

-- `Std.HashSet.Raw.size_ofList_le`: removable: each insertIfNew adds at most one to the size field (any instances).
theorem HashSet.Raw.size_ofList_le_h4 : drop% Std.HashSet.Raw.size_ofList_le 4 := by
  intro α _ _ _ l
  show (HashSet.Raw.ofList l).inner.inner.size ≤ _
  rw [hsr_ofList_raw]
  simpa using size_insertListIfNewUnit_le l (Raw₀.emptyWithCapacity 8)

-- `Std.HashSet.Raw.size_ofList`: removable: for a list without ==-related pairs (earlier == later is false), no
-- inserted element finds an earlier one, so each insertIfNew adds one (any instances).
theorem HashSet.Raw.size_ofList_h4 : drop% Std.HashSet.Raw.size_ofList 4 := by
  intro α _ _ _ l hl
  show (HashSet.Raw.ofList l).inner.inner.size = _
  rw [hsr_ofList_raw]
  simpa using size_insertListIfNewUnit_eq l hl (Raw₀.emptyWithCapacity 8) (by simp)

-- `Std.HashMap.Raw.size_ofList_le`: removable: each insert adds at most one to the size field (any instances).
theorem HashMap.Raw.size_ofList_le_h4 : drop% Std.HashMap.Raw.size_ofList_le 4 := by
  intro α β _ _ _ l
  show (HashMap.Raw.ofList l).inner.size ≤ _
  rw [hmr_ofList_raw]
  simpa using size_insertList_le l (Raw₀.emptyWithCapacity 8)

-- `Std.HashMap.Raw.size_ofList`: removable: for a list without ==-related keys (earlier == later is false), no
-- inserted key finds an earlier one, so each insert adds one (any instances).
theorem HashMap.Raw.size_ofList_h4 : drop% Std.HashMap.Raw.size_ofList 4 := by
  intro α β _ _ _ l hl
  show (HashMap.Raw.ofList l).inner.size = _
  rw [hmr_ofList_raw]
  simpa using size_insertList_eq l hl (Raw₀.emptyWithCapacity 8) (by simp)

-- `Std.HashMap.Raw.size_ofList_le`: removable: each insert adds at most one to the size field (any instances).
theorem HashMap.Raw.size_ofList_le_h5 : drop% Std.HashMap.Raw.size_ofList_le 5 := by
  intro α β _ _ _ l
  show (HashMap.Raw.ofList l).inner.size ≤ _
  rw [hmr_ofList_raw]
  simpa using size_insertList_le l (Raw₀.emptyWithCapacity 8)

-- `Std.HashMap.Raw.size_ofList`: removable: for a list without ==-related keys (earlier == later is false), no
-- inserted key finds an earlier one, so each insert adds one (any instances).
theorem HashMap.Raw.size_ofList_h5 : drop% Std.HashMap.Raw.size_ofList 5 := by
  intro α β _ _ _ l hl
  show (HashMap.Raw.ofList l).inner.size = _
  rw [hmr_ofList_raw]
  simpa using size_insertList_eq l hl (Raw₀.emptyWithCapacity 8) (by simp)

-- `Std.HashSet.Raw.get_ofList_of_mem`: removable: with EquivBEq the returned key x is an element of l with x == k',
-- hence x == k, and the list has no ==-related pairs, so x = k; bucket placement does not matter.
theorem HashSet.Raw.get_ofList_of_mem_h4 : drop% Std.HashSet.Raw.get_ofList_of_mem 4 := by
  intro α _ _ _ l k k' hkk hl hk h'
  obtain ⟨hb, hc, he⟩ := dr_getKey_eq (HashSet.Raw.ofList l).inner.inner k' h'
  show DHashMap.Raw.getKey _ k' h' = k
  rw [he]
  obtain ⟨p, hp, h1, h2⟩ := raw0_getKey_mem ⟨_, hb⟩ k' hc
  rw [← h1]
  exact pw_unique id l hl p.1 k (hsr_ofList_keys l p hp) hk (BEq.trans h2 (BEq.symm hkk))

-- `Std.HashMap.Raw.getKey_ofList_of_mem`: removable: with EquivBEq the returned key x is a key of l with x == k',
-- hence x == k, and the keys are pairwise not ==-related, so x = k; bucket placement does not matter.
theorem HashMap.Raw.getKey_ofList_of_mem_h5 : drop% Std.HashMap.Raw.getKey_ofList_of_mem 5 := by
  intro α β _ _ _ l k k' hkk hl hk h'
  obtain ⟨hb, hc, he⟩ := dr_getKey_eq (HashMap.Raw.ofList l).inner k' h'
  show DHashMap.Raw.getKey _ k' h' = k
  rw [he]
  obtain ⟨p, hp, h1, h2⟩ := raw0_getKey_mem ⟨_, hb⟩ k' hc
  rw [← h1]
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hk
  have := pw_unique Prod.fst l hl (p.1, p.2) w (hmr_ofList_entries l p hp) hw (BEq.trans h2 (BEq.symm hkk))
  rw [← this]

-- `Std.HashMap.Raw.getElem_ofList_of_mem`: removable: with EquivBEq the returned entry (x, w) is in l with x == k',
-- hence x == k, and the keys are pairwise not ==-related, so (x, w) = (k, v); bucket placement does not matter.
theorem HashMap.Raw.getElem_ofList_of_mem_h5 : drop% Std.HashMap.Raw.getElem_ofList_of_mem 5 := by
  intro α β _ _ _ l k k' hkk v hl hk h'
  obtain ⟨hb, hc, he⟩ := dr_cget_eq (HashMap.Raw.ofList l).inner k' h'
  show DHashMap.Raw.Const.get _ k' h' = v
  rw [he]
  obtain ⟨p, hp, h1, h2⟩ := raw0_cget_mem ⟨_, hb⟩ k' hc
  rw [← h1]
  have := pw_unique Prod.fst l hl (p.1, p.2) (k, v) (hmr_ofList_entries l p hp) hk (BEq.trans h2 (BEq.symm hkk))
  exact congrArg Prod.snd this

-- `Std.ExtHashSet.ofList_eq_empty_iff`: removable: ofList [] is ∅ by definition, and inserting into any map leaves
-- an entry, so ofList (hd :: tl) has entries and is not equivalent to ∅ (any instances).
theorem ExtHashSet.ofList_eq_empty_iff_h3 : drop% Std.ExtHashSet.ofList_eq_empty_iff 3 := by
  intro α _ _ _ l
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases l with
  | nil => rfl
  | cons hd tl =>
    exfalso
    have h' := Quotient.exact (congrArg (fun s : ExtHashSet α => s.inner.inner.inner) h)
    have p := h'.inner.impl
    have hr : (DHashMap.Const.unitOfList (hd :: tl)).inner =
        (Raw₀.Const.insertListIfNewUnitₘ (Raw₀.emptyWithCapacity 8) (hd :: tl)).1 := hs_ofList_raw (hd :: tl)
    rw [hr] at p
    exact tlm_insertListIfNewUnit_ne_nil tl _ hd (List.Perm.eq_nil (p.trans (by
      show List.Perm (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets) []
      simp)))

-- `Std.ExtHashSet.ofList_eq_empty_iff`: removable: ofList [] is ∅ by definition, and inserting into any map leaves
-- an entry, so ofList (hd :: tl) has entries and is not equivalent to ∅ (any instances).
theorem ExtHashSet.ofList_eq_empty_iff_h4 : drop% Std.ExtHashSet.ofList_eq_empty_iff 4 := by
  intro α _ _ _ l
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases l with
  | nil => rfl
  | cons hd tl =>
    exfalso
    have h' := Quotient.exact (congrArg (fun s : ExtHashSet α => s.inner.inner.inner) h)
    have p := h'.inner.impl
    have hr : (DHashMap.Const.unitOfList (hd :: tl)).inner =
        (Raw₀.Const.insertListIfNewUnitₘ (Raw₀.emptyWithCapacity 8) (hd :: tl)).1 := hs_ofList_raw (hd :: tl)
    rw [hr] at p
    exact tlm_insertListIfNewUnit_ne_nil tl _ hd (List.Perm.eq_nil (p.trans (by
      show List.Perm (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets) []
      simp)))

-- `Std.ExtHashMap.ofList_eq_empty_iff`: removable: ofList [] is ∅ by definition, and inserting into any map leaves
-- an entry, so ofList (hd :: tl) has entries and is not equivalent to ∅ (any instances).
theorem ExtHashMap.ofList_eq_empty_iff_h4 : drop% Std.ExtHashMap.ofList_eq_empty_iff 4 := by
  intro α β _ _ _ l
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases l with
  | nil => rfl
  | cons hd tl =>
    exfalso
    have h' := Quotient.exact (congrArg (fun s : ExtHashMap α β => s.inner.inner) h)
    have p := h'.inner.impl
    have hr : (DHashMap.Const.ofList (hd :: tl)).inner =
        (Raw₀.Const.insertListₘ (Raw₀.emptyWithCapacity 8) (hd :: tl)).1 := hm_ofList_raw (hd :: tl)
    rw [hr] at p
    exact tlm_insertList_ne_nil tl _ hd (List.Perm.eq_nil (p.trans (by
      show List.Perm (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets) []
      simp)))

-- `Std.ExtHashMap.ofList_eq_empty_iff`: removable: ofList [] is ∅ by definition, and inserting into any map leaves
-- an entry, so ofList (hd :: tl) has entries and is not equivalent to ∅ (any instances).
theorem ExtHashMap.ofList_eq_empty_iff_h5 : drop% Std.ExtHashMap.ofList_eq_empty_iff 5 := by
  intro α β _ _ _ l
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases l with
  | nil => rfl
  | cons hd tl =>
    exfalso
    have h' := Quotient.exact (congrArg (fun s : ExtHashMap α β => s.inner.inner) h)
    have p := h'.inner.impl
    have hr : (DHashMap.Const.ofList (hd :: tl)).inner =
        (Raw₀.Const.insertListₘ (Raw₀.emptyWithCapacity 8) (hd :: tl)).1 := hm_ofList_raw (hd :: tl)
    rw [hr] at p
    exact tlm_insertList_ne_nil tl _ hd (List.Perm.eq_nil (p.trans (by
      show List.Perm (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets) []
      simp)))

-- `Std.DHashMap.Internal.Raw₀.wfImp_filter`: removable: filtering keeps every entry in its bucket (so bucket
-- placement is preserved without LawfulHashable), recomputes the size, and keeps keys distinct.
theorem Raw₀.wfImp_filter_h5 : drop% Std.DHashMap.Internal.Raw₀.wfImp_filter 5 := by
  intro α β _ _ _ m f h
  rw [Raw₀.filter_eq_filterₘ]
  refine ⟨?_, by simp [Raw₀.filterₘ, computeSize_eq], h.distinct.filter.perm Raw₀.toListModel_filterₘ⟩
  refine ⟨fun i hi => ⟨fun h0 p hp => ?_⟩⟩
  simp only [Raw₀.filterₘ, withComputedSize, updateAllBuckets, Array.getElem_map] at hp ⊢
  have hs : (m.filterₘ f).1.buckets.size = m.1.buckets.size := by
    simp [Raw₀.filterₘ, withComputedSize, updateAllBuckets]
  have hi' : i < m.1.buckets.size := hs ▸ hi
  have hp' : p ∈ (m.1.buckets[i]).toList := (List.mem_filter.mp (AssocList.toList_filter.mem_iff.mp hp)).1
  refine (congrArg USize.toNat (mkIdx_val_congr hs h0 (hs ▸ h0) _)).trans ?_
  exact (h.buckets_hash_self.hashes_to i hi').hash_self _ p hp'

-- `Std.HashMap.Raw.mem_modify`: removable: modify only replaces the first key x with x == k by k, and with EquivBEq
-- x == k' iff k == k', so every bucket answers contains as before; bucket placement does not matter.
theorem HashMap.Raw.mem_modify_h6 : drop% Std.HashMap.Raw.mem_modify 6 := by
  intro α β _ _ m _ k k' f h
  have hb : 0 < m.inner.buckets.size := h.out.size_buckets_pos
  rw [HashMap.Raw.mem_iff_contains, HashMap.Raw.mem_iff_contains]
  show DHashMap.Raw.contains (DHashMap.Raw.Const.modify m.inner k f) k' = true ↔ DHashMap.Raw.contains m.inner k' = true
  simp only [DHashMap.Raw.Const.modify, DHashMap.Raw.contains, hb, dite_true]
  have hb' : 0 < (Raw₀.Const.modify ⟨m.inner, hb⟩ k f).1.buckets.size := (Raw₀.Const.modify ⟨m.inner, hb⟩ k f).2
  rw [dif_pos hb']
  exact iff_of_eq (congrArg (· = true) (raw0_contains_cmodify ⟨m.inner, hb⟩ k k' f))

-- `Std.HashSet.Raw.mem_insert_self`: removable: insertIfNew either finds a key == k in k's bucket or puts k there;
-- a resize rehashes every key into the bucket of its own hash, where contains k finds it (k == k by EquivBEq).
theorem HashSet.Raw.mem_insert_self_h5 : drop% Std.HashSet.Raw.mem_insert_self 5 := by
  intro α m _ _ _ h k
  have hb : 0 < m.inner.inner.buckets.size := h.out.out.size_buckets_pos
  rw [HashSet.Raw.mem_iff_contains]
  show DHashMap.Raw.contains (DHashMap.Raw.insertIfNew m.inner.inner k ()) k = true
  simp only [DHashMap.Raw.insertIfNew, DHashMap.Raw.contains, hb, dite_true]
  rw [dif_pos (Raw₀.insertIfNew ⟨m.inner.inner, hb⟩ k ()).2]
  exact raw0_contains_insertIfNew_self ⟨m.inner.inner, hb⟩ k ()

-- `Std.HashMap.Raw.mem_insert_self`: removable: insert either replaces a key == k in k's bucket by k or puts k there;
-- a resize rehashes every key into the bucket of its own hash, where contains k finds it (k == k by EquivBEq).
theorem HashMap.Raw.mem_insert_self_h6 : drop% Std.HashMap.Raw.mem_insert_self 6 := by
  intro α β m _ _ _ h k v
  have hb : 0 < m.inner.buckets.size := h.out.size_buckets_pos
  rw [HashMap.Raw.mem_iff_contains]
  show DHashMap.Raw.contains (DHashMap.Raw.insert m.inner k v) k = true
  simp only [DHashMap.Raw.insert, DHashMap.Raw.contains, hb, dite_true]
  rw [dif_pos (Raw₀.insert ⟨m.inner, hb⟩ k v).2]
  exact raw0_contains_insert_self ⟨m.inner, hb⟩ k v

-- `Std.DHashMap.Internal.Raw₀.toListModel_containsThenInsert`: removable: with LawfulHashable and IsHashSelf every
-- key == a sits in a's bucket, so the bucket-local contains/replace agree with containsKey/replaceEntry on the whole
-- list, and a resize only permutes the entries; EquivBEq is not needed.
theorem Raw₀.toListModel_containsThenInsert_h4 :
    drop% Std.DHashMap.Internal.Raw₀.toListModel_containsThenInsert 4 := by
  intro α β _ _ _ m h a b
  rw [Raw₀.containsThenInsert_eq_insertₘ, ← Raw₀.insert_eq_insertₘ]
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have hihs := h.buckets_hash_self
  simp only at hihs
  unfold Raw₀.insert; dsimp only
  generalize hI : mkIdx bs.size hb (hash a) = I
  obtain ⟨i, hi⟩ := I
  dsimp only
  -- the entries outside a's bucket have no key == a
  obtain ⟨l, hl₁, -, hl₃⟩ := exists_bucket_of_uset bs i hi .nil
  have hl : Std.Internal.List.containsKey a l = false := hl₃ hihs a (by rw [hI])
  have key : ∀ (l₁ l₂ : List (AssocList α β)), bs.toList = l₁ ++ bs[i] :: l₂ →
      Std.Internal.List.containsKey a (l₁.flatMap AssocList.toList) = false ∧
      Std.Internal.List.containsKey a (l₂.flatMap AssocList.toList) = false := by
    intro l₁ l₂ e
    have hp : List.Perm (l₁.flatMap AssocList.toList ++ l₂.flatMap AssocList.toList) l := by
      have : List.Perm (bs[i].toList ++ (l₁.flatMap AssocList.toList ++ l₂.flatMap AssocList.toList))
          (bs[i.toNat].toList ++ l) := by
        refine List.Perm.trans ?_ hl₁
        unfold toListModel; rw [e]
        simp only [List.flatMap_append, List.flatMap_cons, Array.ugetElem_eq_getElem]
        exact List.perm_append_comm_assoc _ _ _
      exact (List.perm_append_left_iff _).mp this
    have hf : ∀ e ∈ l₁.flatMap AssocList.toList ++ l₂.flatMap AssocList.toList, (e.1 == a) = false := by
      intro e he
      have := hp.mem_iff.mp he
      rw [Bool.eq_false_iff]; intro hea
      have : Std.Internal.List.containsKey a l = true :=
        Std.Internal.List.containsKey_eq_true_iff_exists_mem.mpr ⟨e, this, hea⟩
      simp_all
    constructor <;> rw [Bool.eq_false_iff] <;> intro hc <;>
      obtain ⟨e, he, hea⟩ := Std.Internal.List.containsKey_eq_true_iff_exists_mem.mp hc <;>
      simp_all
  split
  · rename_i hc
    obtain ⟨l₁, l₂, e₁, -, e₂⟩ := Array.exists_of_uset (d := AssocList.replace a b bs[i]) hi
    simp only [Array.ugetElem_eq_getElem, Array.uset_eq_set] at hc e₁ e₂ key ⊢
    simp only [Array.set_set]
    obtain ⟨k₁, k₂⟩ := key l₁ l₂ e₁
    have hB : Std.Internal.List.containsKey a bs[i.toNat].toList = true := by rwa [← AssocList.contains_eq]
    have ht : toListModel bs = l₁.flatMap AssocList.toList ++ (bs[i.toNat].toList ++ l₂.flatMap AssocList.toList) := by
      unfold toListModel; rw [e₁]; simp
    rw [ht, Std.Internal.List.insertEntry_of_containsKey (by simp [Std.Internal.List.containsKey_append, hB]),
      Std.Internal.List.replaceEntry_append_of_containsKey_left_eq_false k₁,
      Std.Internal.List.replaceEntry_append_of_containsKey_left hB]
    unfold toListModel; rw [e₂]; simp [AssocList.toList_replace]
  · rename_i hc
    obtain ⟨l₁, l₂, e₁, -, e₂⟩ := Array.exists_of_uset (d := AssocList.cons a b bs[i]) hi
    simp only [Array.ugetElem_eq_getElem] at hc e₁ e₂ key ⊢
    obtain ⟨k₁, k₂⟩ := key l₁ l₂ e₁
    have hB : Std.Internal.List.containsKey a bs[i.toNat].toList = false := by
      rw [← AssocList.contains_eq]; simpa using hc
    have ht : toListModel bs = l₁.flatMap AssocList.toList ++ (bs[i.toNat].toList ++ l₂.flatMap AssocList.toList) := by
      unfold toListModel; rw [e₁]; simp
    rw [ht, Std.Internal.List.insertEntry_of_containsKey_eq_false (by simp [Std.Internal.List.containsKey_append, hB, k₁, k₂])]
    refine (tlm_expandIfNecessary _).trans ?_
    show List.Perm (toListModel (bs.uset i (AssocList.cons a b bs[i.toNat]) hi)) _
    unfold toListModel; rw [e₂]
    simp only [List.flatMap_append, List.flatMap_cons, AssocList.toList_cons, List.cons_append]
    exact List.perm_middle
