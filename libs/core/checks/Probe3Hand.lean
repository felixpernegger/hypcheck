import Lean
import Std

set_option maxErrors 10000
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

/-! ## Phase 1 additions: more models, ill-formed literals, the tactic `refute_dep` -/

namespace HashInstHand

instance : OfNat NB n := ⟨⟨n⟩⟩
instance : OfNat AB n := ⟨⟨n⟩⟩
instance : OfNat NS n := ⟨⟨n⟩⟩
instance : OfNat NT n := ⟨⟨n⟩⟩
@[simp] theorem NB.ofNat_def (n : Nat) : (OfNat.ofNat n : NB) = NB.mk n := rfl
@[simp] theorem AB.ofNat_def (n : Nat) : (OfNat.ofNat n : AB) = AB.mk n := rfl
@[simp] theorem NS.ofNat_def (n : Nat) : (OfNat.ofNat n : NS) = NS.mk n := rfl
@[simp] theorem NT.ofNat_def (n : Nat) : (OfNat.ofNat n : NT) = NT.mk n := rfl

theorem NB.notEquiv : ¬ EquivBEq NB := fun h => @NB.broken h _
theorem NS.notEquiv : ¬ EquivBEq NS := fun h => @NS.broken h _
theorem NT.notEquiv : ¬ EquivBEq NT := fun h => @NT.broken h _
theorem AB.notLH : ¬ LawfulHashable AB := fun h => @AB.broken _ h
theorem NT.notPEquiv : ¬ PartialEquivBEq NT := fun h => by
  have := @PartialEquivBEq.trans NT _ h ⟨0⟩ ⟨1⟩ ⟨2⟩ rfl rfl; simp at this
theorem NB.notRefl : ¬ ReflBEq NB := fun h =>
  Bool.false_ne_true ((NB.beq_def ⟨0⟩ ⟨0⟩).symm.trans (@ReflBEq.rfl NB _ h ⟨0⟩))

/-- `HB`: `a == b ↔ a/2 = b/2`, hash `a/2`. `EquivBEq` ✓, `LawfulHashable` ✓, `LawfulBEq` ✗. -/
structure HB where n : Nat deriving DecidableEq, Inhabited
instance : BEq HB := ⟨fun a b => a.n / 2 == b.n / 2⟩
instance : Hashable HB := ⟨fun a => UInt64.ofNat (a.n / 2)⟩
instance : OfNat HB n := ⟨⟨n⟩⟩
instance : EquivBEq HB where
  rfl := by simp [BEq.beq]
  symm h := by simp_all [BEq.beq]
  trans h1 h2 := by simp_all [BEq.beq]
instance : LawfulHashable HB := ⟨fun a b h => by simp_all [BEq.beq, hash]⟩
@[simp] theorem HB.ofNat_def (n : Nat) : (OfNat.ofNat n : HB) = HB.mk n := rfl
@[simp] theorem HB.beq_def (a b : Nat) : (HB.mk a == HB.mk b) = (a / 2 == b / 2) := rfl
theorem HB.notLawful : ¬ LawfulBEq HB := fun h => by
  have := @LawfulBEq.eq_of_beq HB _ h ⟨0⟩ ⟨1⟩ (by decide); simp at this

/-- `cmpT`: equal ↦ `.eq`, else `.lt` (not oriented, so not `TransCmp`). -/
def cmpT (a b : Nat) : Ordering := if a = b then .eq else .lt
/-- `cmpE`: always `.eq` (`TransCmp` ✓, `LawfulEqCmp` ✗). -/
def cmpE (_ _ : Nat) : Ordering := .eq
instance : Std.TransCmp cmpE where
  eq_swap := rfl
  isLE_trans _ _ := rfl
instance : Std.LawfulEqCmp cmpT where
  compare_self := by simp [cmpT]
  eq_of_compare h := by unfold cmpT at h; split at h <;> simp_all
theorem cmpT.notOriented : ¬ Std.OrientedCmp cmpT := fun h => by
  have := @Std.OrientedCmp.eq_swap _ cmpT h 0 1; simp [cmpT] at this
theorem cmpT.notTrans : ¬ Std.TransCmp cmpT := fun h => cmpT.notOriented h.toOrientedCmp
theorem cmpE.notLawfulEq : ¬ Std.LawfulEqCmp cmpE := fun h => by
  have := @Std.LawfulEqCmp.eq_of_compare _ cmpE h 0 1 rfl; simp at this
theorem cmpE.notLawfulBEq : ¬ Std.LawfulBEqCmp cmpE := fun h => by
  have := (@Std.LawfulBEqCmp.compare_eq_iff_beq _ _ cmpE h 0 1).1 rfl; simp at this

/-- `OT`: `Ord` by `cmpT` (not `OrientedOrd`/`TransOrd`). -/
structure OT where n : Nat deriving DecidableEq, Inhabited
instance : Ord OT := ⟨fun a b => cmpT a.n b.n⟩
instance : OfNat OT n := ⟨⟨n⟩⟩
@[simp] theorem OT.ofNat_def (n : Nat) : (OfNat.ofNat n : OT) = OT.mk n := rfl
instance : Std.LawfulEqOrd OT where
  compare_self := by simp [compare, cmpT]
  eq_of_compare {a b} h := by
    cases a; cases b; simp only [compare, cmpT] at h; split at h <;> simp_all
theorem OT.notOriented : ¬ Std.OrientedOrd OT := fun h => by
  have := @Std.OrientedCmp.eq_swap _ _ h ⟨0⟩ ⟨1⟩; simp [compare, cmpT] at this
theorem OT.notTrans : ¬ Std.TransOrd OT := fun h => OT.notOriented h.toOrientedCmp

/-- `OE`: `Ord` always `.eq`, `BEq` = `DecidableEq` (`TransOrd` ✓, `LawfulEqOrd` ✗, `LawfulBEqOrd` ✗). -/
structure OE where n : Nat deriving DecidableEq, Inhabited
instance : Ord OE := ⟨fun _ _ => .eq⟩
instance : OfNat OE n := ⟨⟨n⟩⟩
@[simp] theorem OE.ofNat_def (n : Nat) : (OfNat.ofNat n : OE) = OE.mk n := rfl
instance : Std.TransOrd OE where
  eq_swap := rfl
  isLE_trans _ _ := rfl
theorem OE.notLawfulEq : ¬ Std.LawfulEqOrd OE := fun h => by
  have := @Std.LawfulEqCmp.eq_of_compare _ _ h ⟨0⟩ ⟨1⟩ rfl; simp at this
theorem OE.notLawfulBEq : ¬ Std.LawfulBEqOrd OE := fun h => by
  have := (@Std.LawfulBEqCmp.compare_eq_iff_beq _ _ _ h ⟨0⟩ ⟨1⟩).1 rfl; simp at this

/-- `cmpH`: compare halves (`TransCmp` ✓, `LawfulEqCmp` ✗, but keys of different halves differ). -/
def cmpH (a b : Nat) : Ordering := compare (a / 2) (b / 2)
instance : Std.TransCmp cmpH where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := fun a b : Nat => compare a b)
  isLE_trans h1 h2 := Std.TransCmp.isLE_trans (cmp := fun a b : Nat => compare a b) h1 h2
theorem cmpH.notLawfulEq : ¬ Std.LawfulEqCmp cmpH := fun h => by
  have := @Std.LawfulEqCmp.eq_of_compare _ cmpH h 0 1 (by decide); simp at this
theorem cmpH.notLawfulBEq : ¬ Std.LawfulBEqCmp cmpH := fun h => by
  have := (@Std.LawfulBEqCmp.compare_eq_iff_beq _ _ cmpH h 0 1).1 (by decide); simp at this
/-- `cmpL`: always `.lt` (not oriented). -/
def cmpL (_ _ : Nat) : Ordering := .lt
theorem cmpL.notOriented : ¬ Std.OrientedCmp cmpL := fun h => by
  have := @Std.OrientedCmp.eq_swap _ cmpL h 0 1; simp [cmpL] at this
theorem cmpL.notTrans : ¬ Std.TransCmp cmpL := fun h => cmpL.notOriented h.toOrientedCmp

/-- `OH`: `Ord` by `cmpH`, `BEq` = `DecidableEq` (`TransOrd` ✓, `LawfulEqOrd` ✗, `LawfulBEqOrd` ✗). -/
structure OH where n : Nat deriving DecidableEq, Inhabited
instance : Ord OH := ⟨fun a b => cmpH a.n b.n⟩
instance : OfNat OH n := ⟨⟨n⟩⟩
@[simp] theorem OH.ofNat_def (n : Nat) : (OfNat.ofNat n : OH) = OH.mk n := rfl
instance : Std.TransOrd OH where
  eq_swap {a b} := Std.OrientedCmp.eq_swap (cmp := cmpH) (a := a.n) (b := b.n)
  isLE_trans {a b c} h1 h2 := Std.TransCmp.isLE_trans (cmp := cmpH) (a := a.n) (b := b.n) (c := c.n) h1 h2
theorem OH.notLawfulEq : ¬ Std.LawfulEqOrd OH := fun h => by
  have := @Std.LawfulEqCmp.eq_of_compare _ _ h ⟨0⟩ ⟨1⟩ (by decide); simp at this
theorem OH.notLawfulBEq : ¬ Std.LawfulBEqOrd OH := fun h => by
  have := (@Std.LawfulBEqCmp.compare_eq_iff_beq _ _ _ h ⟨0⟩ ⟨1⟩).1 (by decide); simp at this

/-! Ill-formed literals: wrong size field (trees), no buckets / wrong size field (hash maps). -/

section Bad
open Std.DTreeMap.Internal
variable {α : Type u} {β : α → Type v}

theorem implBad_notBalanced (k : α) (v : β k) : ¬ (Impl.inner 0 k v .leaf .leaf : Impl α β).Balanced :=
  fun h => by rw [Impl.balanced_inner_iff] at h; simp [Impl.size] at h
theorem implBad_notWF {_ : Ord α} (k : α) (v : β k) : ¬ (Impl.inner 0 k v .leaf .leaf : Impl α β).WF :=
  fun h => implBad_notBalanced k v h.balanced
theorem dtrBad_notWF {cmp : α → α → Ordering} (k : α) (v : β k) :
    ¬ (⟨Impl.inner 0 k v .leaf .leaf⟩ : Std.DTreeMap.Raw α β cmp).WF :=
  fun h => @implBad_notWF _ _ ⟨cmp⟩ k v h.out
theorem tmrBad_notWF {β : Type v} {cmp : α → α → Ordering} (k : α) (v : β) :
    ¬ (⟨⟨Impl.inner 0 k v .leaf .leaf⟩⟩ : Std.TreeMap.Raw α β cmp).WF :=
  fun h => dtrBad_notWF (β := fun _ => β) k v h.out
theorem tsrBad_notWF {cmp : α → α → Ordering} (k : α) :
    ¬ (⟨⟨⟨Impl.inner 0 k () .leaf .leaf⟩⟩⟩ : Std.TreeSet.Raw α cmp).WF :=
  fun h => tmrBad_notWF k () h.out

theorem implUnord_notOrdered : ¬ (Impl.inner 2 1 1 .leaf (.inner 1 0 0 .leaf .leaf) : Impl Nat (fun _ => Nat)).Ordered := by
  simp [Impl.Ordered, Impl.toListModel]; decide

theorem drBad_notWF [BEq α] [Hashable α] : ¬ (⟨0, #[]⟩ : Std.DHashMap.Raw α β).WF :=
  fun h => by have := Std.DHashMap.Raw.WF.size_buckets_pos _ h; simp at this
theorem hmrBad_notWF {β : Type v} [BEq α] [Hashable α] : ¬ (⟨⟨0, #[]⟩⟩ : Std.HashMap.Raw α β).WF :=
  fun h => drBad_notWF h.out
theorem hsrBad_notWF [BEq α] [Hashable α] : ¬ (⟨⟨⟨0, #[]⟩⟩⟩ : Std.HashSet.Raw α).WF :=
  fun h => hmrBad_notWF h.out
/-- Size field 1 over 16 empty buckets (`Raw₀`), lawful keys. -/
theorem r0Bad_notWFImp [BEq α] [Hashable α] :
    ¬ Raw.WFImp (⟨1, nil16⟩ : Std.DHashMap.Raw α β) := fun h => by
  have := h.size_eq; simp [nil16, toListModel] at this
/-- The same raw map as a `Raw₀`. -/
abbrev r0Bad : Raw₀ α β := ⟨⟨1, nil16⟩, by simp [nil16]⟩
theorem r0Bad_notWF {_ : BEq α} {_ : Hashable α} {e : EquivBEq α} {l : LawfulHashable α} :
    ¬ (r0Bad : Raw₀ α β).val.WF := fun h => r0Bad_notWFImp (Std.DHashMap.Internal.Raw.WF.out h)
theorem r0Bad_notWFImp' {_ : BEq α} {_ : Hashable α} : ¬ Raw.WFImp (r0Bad : Raw₀ α β).val := r0Bad_notWFImp

/-- 16 buckets, key `k` in bucket 0 (right for hash 0), size field 0: not `WFImp`, but `k` is found. -/
abbrev oneKey16 (k : α) (v : β k) : Array (AssocList α β) :=
  #[.cons k v .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil]
abbrev r1Bad (k : α) (v : β k) : Raw₀ α β := ⟨⟨0, oneKey16 k v⟩, by simp⟩
/-- One key in bucket 0, correct size field (well-formed by `wf_vac` in the broken models). -/
abbrev r1Good (k : α) (v : β k) : Raw₀ α β := ⟨⟨1, oneKey16 k v⟩, by simp⟩
theorem r1Bad_notWFImp {_ : BEq α} {_ : Hashable α} (k : α) (v : β k) :
    ¬ Raw.WFImp (r1Bad k v).val := fun h => by
  have := h.size_eq; simp [toListModel] at this
theorem r1Bad_notWF {_ : BEq α} {_ : Hashable α} {e : EquivBEq α} {l : LawfulHashable α} (k : α) (v : β k) :
    ¬ (r1Bad k v).val.WF := fun h => r1Bad_notWFImp k v (Std.DHashMap.Internal.Raw.WF.out h)
theorem dr1Bad_notWF {_ : BEq α} {_ : Hashable α} {e : EquivBEq α} {l : LawfulHashable α} (k : α) (v : β k) :
    ¬ (⟨0, oneKey16 k v⟩ : Std.DHashMap.Raw α β).WF := @r1Bad_notWF α β _ _ e l k v
theorem hmr1Bad_notWF {β : Type v} {_ : BEq α} {_ : Hashable α} {e : EquivBEq α} {l : LawfulHashable α}
    (k : α) (v : β) : ¬ (⟨⟨0, oneKey16 (β := fun _ => β) k v⟩⟩ : Std.HashMap.Raw α β).WF :=
  fun h => @dr1Bad_notWF α (fun _ => β) _ _ e l k v h.out
theorem hsr1Bad_notWF {_ : BEq α} {_ : Hashable α} {e : EquivBEq α} {l : LawfulHashable α} (k : α) :
    ¬ (⟨⟨⟨0, oneKey16 (β := fun _ => Unit) k ()⟩⟩⟩ : Std.HashSet.Raw α).WF :=
  fun h => @hmr1Bad_notWF α Unit _ _ e l k () h.out
@[simp] theorem nat_hash_def (n : Nat) : hash n = UInt64.ofNat n := rfl
@[simp] theorem HB.hash_def (n : Nat) : hash (HB.mk n) = UInt64.ofNat (n / 2) := rfl

end Bad



/-! Extensional tree maps are quotients: two `mk`s whose entry lists differ in length are different, for any
`cmp` (no `TransCmp` needed). Used for `t ≠ ∅` premises under the comparison models. -/
section ExtTree
variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering}
theorem extd_mk_ne {t₁ t₂ : Std.DTreeMap α β cmp} (h : t₁.1.toListModel.length ≠ t₂.1.toListModel.length) :
    Std.ExtDTreeMap.mk t₁ ≠ Std.ExtDTreeMap.mk t₂ := fun e =>
  h (Quotient.exact (congrArg Std.ExtDTreeMap.inner e)).inner.impl.length_eq
theorem extd_ofList_ne_empty (l : List ((a : α) × β a))
    (h : (Std.DTreeMap.ofList l cmp).1.toListModel.length ≠ 0) : Std.ExtDTreeMap.ofList l cmp ≠ ∅ :=
  extd_mk_ne (t₁ := Std.DTreeMap.ofList l cmp) (t₂ := Std.DTreeMap.empty) h
theorem extdc_ofList_ne_empty {β : Type v} (l : List (α × β))
    (h : (Std.DTreeMap.Const.ofList l cmp).1.toListModel.length ≠ 0) : Std.ExtDTreeMap.Const.ofList l cmp ≠ ∅ :=
  extd_mk_ne (t₁ := Std.DTreeMap.Const.ofList l cmp) (t₂ := Std.DTreeMap.empty) h
theorem extm_ofList_ne_empty {β : Type v} (l : List (α × β))
    (h : (Std.DTreeMap.Const.ofList l cmp).1.toListModel.length ≠ 0) : Std.ExtTreeMap.ofList l cmp ≠ ∅ :=
  fun e => extdc_ofList_ne_empty l h (congrArg Std.ExtTreeMap.inner e)
theorem exts_ofList_ne_empty (l : List α)
    (h : (Std.DTreeMap.Const.unitOfList l cmp).1.toListModel.length ≠ 0) : Std.ExtTreeSet.ofList l cmp ≠ ∅ :=
  fun e => extd_mk_ne (t₁ := Std.DTreeMap.Const.unitOfList l cmp) (t₂ := Std.DTreeMap.empty) h
    (congrArg Std.ExtTreeMap.inner (congrArg Std.ExtTreeSet.inner e))
end ExtTree

/-! Plain `DHashMap.Raw` operations on a raw map with explicit buckets, as `Raw₀` operations (for `hm_eval_raw`). -/
section RawLit
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem dr_insert_lit (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) (a : α) (b : β a) :
    (⟨s, bs⟩ : Std.DHashMap.Raw α β).insert a b = (Raw₀.insert ⟨⟨s, bs⟩, h⟩ a b).1 := by
  simp [Std.DHashMap.Raw.insert, h]
theorem dr_insertIfNew_lit (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) (a : α) (b : β a) :
    (⟨s, bs⟩ : Std.DHashMap.Raw α β).insertIfNew a b = (Raw₀.insertIfNew ⟨⟨s, bs⟩, h⟩ a b).1 := by
  simp [Std.DHashMap.Raw.insertIfNew, h]
theorem dr_contains_lit (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) (a : α) :
    (⟨s, bs⟩ : Std.DHashMap.Raw α β).contains a = Raw₀.contains ⟨⟨s, bs⟩, h⟩ a := by
  simp [Std.DHashMap.Raw.contains, h]
theorem dr_erase_lit (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) (a : α) :
    (⟨s, bs⟩ : Std.DHashMap.Raw α β).erase a = (Raw₀.erase ⟨⟨s, bs⟩, h⟩ a).1 := by
  simp [Std.DHashMap.Raw.erase, h]
theorem dr_insertMany_lit (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) (l : List ((a : α) × β a)) :
    (⟨s, bs⟩ : Std.DHashMap.Raw α β).insertMany l = (Raw₀.insertMany ⟨⟨s, bs⟩, h⟩ l).1 := by
  simp [Std.DHashMap.Raw.insertMany, h]
end RawLit

/-- `hm_eval` for plain raw maps: rewrite raw operations on explicit buckets to `Raw₀` ones, innermost first. -/
macro "hm_eval_raw" : tactic => `(tactic| (
  simp (disch := first | decide | simp [nil16]) only [Std.DHashMap.Raw.ofList, Std.DHashMap.Raw.mem_iff_contains,
    dr_empty, dr_insert_lit, dr_insertIfNew_lit, dr_contains_lit, dr_erase_lit, dr_insertMany_lit]
  hm_eval))

end HashInstHand

namespace RefuteDep
open Lean Meta Elab Tactic Term

/-- Run `tac` on `g` within `hb` thousand heartbeats; return the remaining goals, or `none` on failure. -/
def runOn (g : MVarId) (tac : TSyntax `tactic) (hb : Nat) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  let r ← withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
    tryCatchRuntimeEx (some <$> Term.withoutErrToSorry (Tactic.run g (evalTactic tac))) (fun e => do
      if (← IO.getEnv "REFUTE_DEBUG").isSome then
        IO.eprintln s!"  closer {tac.raw.prettyPrint.pretty 60} failed: {(← e.toMessageData.toString).take 200}"
      pure none)
  let r ← match r with
    | some gs => if (← instantiateMVars (mkMVar g)).hasSorry then pure none else pure (some gs)
    | none => pure none
  if r.isNone then s.restore
  return r

def closes (g : MVarId) (tac : TSyntax `tactic) (hb : Nat) : TacticM Bool := do
  let s ← saveState
  -- run on a fresh goal with the instantiated statement (assigned metavariables in the goal type confuse
  -- elaboration of lemma applications), then transfer the proof
  let ty ← instantiateMVars (← g.getType)
  let g2 ← g.withContext <| mkFreshExprMVar ty
  match ← runOn g2.mvarId! tac hb with
  | some [] =>
    let pf ← instantiateMVars g2
    if pf.hasExprMVar then
      if (← IO.getEnv "REFUTE_DEBUG").isSome then
        IO.eprintln s!"  closer {tac.raw.prettyPrint.pretty 60} left mvars in proof of {← ppExpr ty}"
      s.restore; return false
    g.assign pf; return true
  | some gs =>
    if (← IO.getEnv "REFUTE_DEBUG").isSome then
      IO.eprintln s!"  closer {tac.raw.prettyPrint.pretty 60} left {gs.length} goals, first: {← ppExpr (← gs.head!.getType)}"
    s.restore; return false
  | none => s.restore; return false

/-- Elaborate `stx` at type `ty`; succeed only without new unassigned metavariables. -/
def elabAt (stx : Term) (ty : Expr) : TacticM (Option Expr) := do
  let s ← saveState
  let r ← withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 400000 }) do
    tryCatchRuntimeEx (do
      let e ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTermEnsuringType stx ty
      let e ← instantiateMVars e
      if e.hasExprMVar || e.hasSorry then return none
      return some e) (fun _ => pure none)
  if r.isNone then s.restore
  return r

def typeCands : TacticM (Array Term) := return #[← `(Nat), ← `(fun _ => Nat), ← `(Bool), ← `(Unit)]

def dataCands : TacticM (Array Term) := return #[
  ← `(inferInstance), ← `(∅), ← `(0), ← `(1), ← `(2), ← `(true), ← `(false), ← `(none), ← `(some 0), ← `(()),
  ← `([]), ← `([0]), ← `([0, 1]), ← `([(0, 0)]), ← `([(0, 0), (1, 1)]), ← `([⟨0, 0⟩]), ← `([⟨0, 0⟩, ⟨1, 1⟩]),
  ← `(.ofList [0]), ← `(.ofList [0, 1]), ← `(.ofList [(0, 0)]), ← `(.ofList [(0, 0), (1, 1)]),
  ← `(.ofList [⟨0, 0⟩]), ← `(.ofList [⟨0, 0⟩, ⟨1, 1⟩]),
  ← `(.ofList [⟨0, ()⟩]), ← `(.ofList [(0, ())]), ← `(Std.ExtDHashMap.Const.insertManyIfNewUnit ∅ [0]),
  ← `(.ofList [0] _), ← `(.ofList [0, 1] _), ← `(.ofList [(0, 0)] _), ← `(.ofList [(0, 0), (1, 1)] _),
  ← `(.ofList [⟨0, 0⟩] _), ← `(.ofList [⟨0, 0⟩, ⟨1, 1⟩] _),
  ← `(.leaf), ← `(.inner 1 0 0 .leaf .leaf), ← `(.inner 2 0 0 .leaf (.inner 1 1 1 .leaf .leaf)),
  ← `(Std.DHashMap.Internal.Raw₀.emptyWithCapacity), ← `(HashInstHand.r0Bad),
  ← `(HashInstHand.r1Good 0 0), ← `(HashInstHand.r1Bad 0 0),
  ← `((Std.DHashMap.Internal.Raw₀.emptyWithCapacity).insert 0 0),
  ← `(((Std.DHashMap.Internal.Raw₀.emptyWithCapacity).insert 0 0).insert 1 1),
  ← `(fun _ => true), ← `(fun _ => false), ← `(fun _ _ => true), ← `(fun _ _ => false),
  ← `(fun _ => none), ← `(fun _ _ => none), ← `(fun _ => some 0), ← `(fun _ _ => some 0),
  ← `(fun _ => 0), ← `(fun _ _ => 0), ← `(fun _ _ _ => 0), ← `(id), ← `(compare), ← `(default)]

/-- Closers with their budget (thousands of heartbeats) and the goal shapes they are tried on. -/
def propTacs : TacticM (Array (TSyntax `tactic × Nat × List String)) := return #[
  (← `(tactic| rfl), 1000, ["eq", "equiv", "other"]), (← `(tactic| trivial), 500, ["other"]),
  (← `(tactic| decide), 1000, ["eq", "mem", "neg", "other"]),
  (← `(tactic| (first | apply Std.DHashMap.Raw.Equiv.refl | apply Std.HashMap.Raw.Equiv.refl | apply Std.HashSet.Raw.Equiv.refl | apply Std.DHashMap.Equiv.refl | apply Std.HashMap.Equiv.refl | apply Std.HashSet.Equiv.refl)), 1000, ["equiv"]),
  (← `(tactic| (first | apply Std.DHashMap.Raw.WF.empty | apply Std.DHashMap.Raw.WF.emptyWithCapacity | apply Std.DHashMap.Raw.WF.ofList | apply Std.HashMap.Raw.WF.empty | apply Std.HashMap.Raw.WF.emptyWithCapacity | apply Std.HashMap.Raw.WF.ofList | apply Std.HashSet.Raw.WF.empty | apply Std.HashSet.Raw.WF.emptyWithCapacity | apply Std.HashSet.Raw.WF.ofList | apply Std.DHashMap.Raw.WF.emptyWithCapacity₀)), 1000, ["wf"]),
  (← `(tactic| (apply Std.DHashMap.Raw.WF.insert₀ <;> first | apply Std.DHashMap.Raw.WF.emptyWithCapacity₀ | (apply Std.DHashMap.Raw.WF.insert₀ <;> apply Std.DHashMap.Raw.WF.emptyWithCapacity₀))), 1000, ["wf"]),
  (← `(tactic| ((first | apply HashInstHand.wf_vac | (constructor; apply HashInstHand.wf_vac) | (constructor; constructor; apply HashInstHand.wf_vac)) <;> (first | exact Subtype.property _ | exact HashInstHand.NB.broken | exact HashInstHand.AB.broken | exact HashInstHand.NS.broken | exact HashInstHand.NT.broken | decide | simp [HashInstHand.nil16] | simp [HashInstHand.dr_empty, HashInstHand.raw0_empty_val]))), 2000, ["wf"]),
  (← `(tactic| (simp only [Std.DTreeMap.Internal.Impl.BalanceLErasePrecond, Std.DTreeMap.Internal.Impl.BalanceLPrecond, Std.DTreeMap.Internal.Impl.BalancedAtRoot, Std.DTreeMap.Internal.Impl.size, Std.DTreeMap.Internal.delta, Std.DTreeMap.Internal.ratio] <;> first | done | omega | decide)), 1000, ["other"]),
  (← `(tactic| (first | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩ | exact ⟨2, by decide, by decide⟩ | (refine ⟨0, ?_, ?_⟩ <;> simp [Std.DTreeMap.Internal.Impl.mem_iff_contains, Std.DTreeMap.Internal.Impl.contains] <;> decide) | (refine ⟨1, ?_, ?_⟩ <;> simp [Std.DTreeMap.Internal.Impl.mem_iff_contains, Std.DTreeMap.Internal.Impl.contains] <;> decide))), 2000, ["other"]),
  (← `(tactic| (first | exact Std.DTreeMap.Internal.Impl.Balanced.leaf | (simp [Std.DTreeMap.Internal.Impl.balanced_inner_iff, Std.DTreeMap.Internal.Impl.size, Std.DTreeMap.Internal.Impl.BalancedAtRoot, Std.DTreeMap.Internal.Impl.Balanced.leaf] <;> first | done | (constructor <;> done) | omega) | (apply Std.DTreeMap.Internal.Impl.WF.balanced; (first | exact @Std.DTreeMap.Internal.Impl.WF.insertMany _ _ (id _) _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _))))), 2000, ["wf"]),
  (← `(tactic| (first | (simp [Std.DTreeMap.Internal.Impl.Ordered, Std.DTreeMap.Internal.Impl.toListModel] <;> decide) | (apply Std.DTreeMap.Internal.Impl.WF.ordered; (first | exact @Std.DTreeMap.Internal.Impl.WF.insertMany _ _ (id _) _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _))))), 2000, ["wf"]),
  (← `(tactic| (first | exact ⟨List.Perm.refl _⟩ | (constructor; simp [Std.DTreeMap.Internal.Impl.toListModel]; done) | (constructor; simp [Std.DTreeMap.Internal.Impl.toListModel]; exact List.Perm.swap _ _ _))), 1000, ["equiv"]),
  (← `(tactic| ((repeat (first | apply Std.TreeSet.Raw.WF.mk | apply Std.TreeMap.Raw.WF.mk | apply Std.DTreeMap.Raw.WF.mk)); (first | exact @Std.DTreeMap.Internal.Impl.WF.insertMany _ _ (id _) _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact @Std.DTreeMap.Internal.Impl.WF.constInsertMany _ (id _) _ _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact @Std.DTreeMap.Internal.Impl.WF.constInsertManyIfNewUnit _ (id _) _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _)))), 2000, ["wf"]),
  (← `(tactic| ((first | apply HashInstHand.extd_ofList_ne_empty | apply HashInstHand.extdc_ofList_ne_empty | apply HashInstHand.extm_ofList_ne_empty | apply HashInstHand.exts_ofList_ne_empty) <;> decide +kernel)), 2000, ["neg"]),
  (← `(tactic| decide +kernel), 2000, ["eq", "mem", "neg", "other"]),
  (← `(tactic| simp), 2000, ["eq", "mem", "neg", "wf", "equiv", "other"]),
  (← `(tactic| (hm_eval <;> decide)), 3000, ["eq", "mem", "neg", "other"]),
  (← `(tactic| (hm_eval_raw <;> decide)), 3000, ["eq", "mem", "neg", "other"]),
  (← `(tactic| simp_all), 2000, ["eq", "neg", "other"])]

/-- Shape of a premise, to pick the closers worth trying. -/
def shapeOf (ty : Expr) : MetaM String := do
  if ty.isAppOfArity ``Not 1 then return "neg"
  match ty.getAppFn.constName? with
  | some n =>
    let s := n.toString
    if n == ``Eq then return "eq"
    if n == ``Ne then return "neg"
    if n == ``Membership.mem then return "mem"
    if s.endsWith ".WF" || s.endsWith "WFImp" || s.endsWith ".Balanced" || s.endsWith ".Ordered" then return "wf"
    if s.endsWith ".Equiv" then return "equiv"
    return "other"
  | none => return "other"

/-- Strategies: a tactic on `¬ H` that picks the model (by unification), or `skip`. -/
def strategies : TacticM (Array (TSyntax `tactic)) := return #[
  ← `(tactic| exact HashInstHand.NS.notEquiv), ← `(tactic| exact HashInstHand.NT.notEquiv),
  ← `(tactic| exact HashInstHand.NB.notEquiv), ← `(tactic| exact HashInstHand.AB.notLH),
  ← `(tactic| exact HashInstHand.HB.notLawful), ← `(tactic| exact HashInstHand.NT.notPEquiv),
  ← `(tactic| exact HashInstHand.NB.notRefl),
  ← `(tactic| exact HashInstHand.cmpT.notTrans), ← `(tactic| exact HashInstHand.cmpT.notOriented),
  ← `(tactic| exact HashInstHand.cmpE.notLawfulEq), ← `(tactic| exact HashInstHand.cmpE.notLawfulBEq),
  ← `(tactic| exact HashInstHand.OT.notTrans), ← `(tactic| exact HashInstHand.OT.notOriented),
  ← `(tactic| exact HashInstHand.OE.notLawfulEq), ← `(tactic| exact HashInstHand.OE.notLawfulBEq),
  ← `(tactic| exact HashInstHand.cmpH.notLawfulEq), ← `(tactic| exact HashInstHand.cmpH.notLawfulBEq),
  ← `(tactic| exact HashInstHand.OH.notLawfulEq), ← `(tactic| exact HashInstHand.OH.notLawfulBEq),
  ← `(tactic| exact HashInstHand.cmpL.notTrans),
  ← `(tactic| apply HashInstHand.implBad_notWF), ← `(tactic| apply HashInstHand.implBad_notBalanced), ← `(tactic| exact HashInstHand.implUnord_notOrdered),
  ← `(tactic| apply HashInstHand.dtrBad_notWF), ← `(tactic| apply HashInstHand.tmrBad_notWF),
  ← `(tactic| apply HashInstHand.tsrBad_notWF),
  ← `(tactic| apply HashInstHand.dr1Bad_notWF), ← `(tactic| apply HashInstHand.hmr1Bad_notWF),
  ← `(tactic| apply HashInstHand.hsr1Bad_notWF), ← `(tactic| apply HashInstHand.r1Bad_notWF),
  ← `(tactic| apply HashInstHand.r1Bad_notWFImp),
  ← `(tactic| exact HashInstHand.drBad_notWF), ← `(tactic| exact HashInstHand.hmrBad_notWF),
  ← `(tactic| exact HashInstHand.hsrBad_notWF),
  ← `(tactic| apply HashInstHand.r0Bad_notWF), ← `(tactic| apply HashInstHand.r0Bad_notWFImp'),
  ← `(tactic| skip)]

partial def search (gs : List MVarId) (fuel : IO.Ref Nat) (failed : IO.Ref (Std.HashSet Expr)) (dataC : Array Term) (propC : Array (TSyntax `tactic × Nat × List String))
    (dbg : IO.Ref Nat) (prev : Array Expr := #[]) : TacticM Bool := do
  let gs ← gs.filterM fun g => return !(← g.isAssigned)
  if gs.isEmpty then return true
  if (← fuel.get) == 0 then
    if (← dbg.get) > 0 then dbg.set 0; IO.eprintln "refute_dep: out of fuel"
    return false
  -- a Prop goal without unassigned metavariables first (prunes early)
  let mut ready : Option MVarId := none
  let mut firstData : Option MVarId := none
  for g in gs do
    let ty ← instantiateMVars (← g.getType)
    if ← isProp ty then
      if !ty.hasExprMVar && ready.isNone then ready := some g
    else if firstData.isNone then firstData := some g
  -- most constrained first: a data goal of the Prop goal with the fewest open data goals
  let dataGs ← gs.filterM fun g => return !(← isProp (← instantiateMVars (← g.getType)))
  let mut best : Option (Array MVarId) := none
  if ready.isNone then
    for g in gs do
      let ty ← instantiateMVars (← g.getType)
      if ← isProp ty then
        let ms := (← getMVars ty).filter (dataGs.contains ·)
        if !ms.isEmpty && (match best with | some b => decide (ms.size < b.size) | none => true) then best := some ms
  let mut constrained : Option MVarId := (best.bind fun ms => dataGs.find? (ms.contains ·))
  -- but its type's open goals (e.g. the key type) first
  if let some c := constrained then
    let cty ← instantiateMVars (← c.getType)
    if let some t := (← getMVars cty).find? (dataGs.contains ·) then constrained := some t
  let pick := ready <|> constrained <|> firstData <|> gs.head?
  let some g := pick | return false
  let rest := gs.filter (· != g)
  let ty ← instantiateMVars (← g.getType)
  if ← isProp ty then
    if (← failed.get).contains ty then return false
    fuel.modify (· - 1)
    -- class premises (e.g. `[LawfulHashable α]` among the independent binders): instance search only
    if (← isClass? ty).isSome then
      let r ← withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 50000000 }) <|
        tryCatchRuntimeEx (synthInstance? ty) (fun e => do
          if (← IO.getEnv "REFUTE_DEBUG").isSome then
            IO.eprintln s!"  synthInstance {← ppExpr ty} threw: {(← e.toMessageData.toString).take 300}"
          pure none)
      if let some inst := r then
        let s ← saveState
        g.assign inst
        if ← search rest fuel failed dataC propC dbg prev then return true
        s.restore
      if (← dbg.get) > 0 then
        dbg.modify (· - 1); IO.eprintln s!"refute_dep: no instance for premise {← ppExpr ty}; synthPendingDepth {(← (read : MetaM Meta.Context)).synthPendingDepth}, local instances {(← getLocalInstances).size}"
      return false
    if (← failed.get).contains ty then return false
    let mut closed := false
    let shape ← shapeOf ty
    for (tac, hb, shapes) in propC do
      unless shapes.contains shape do continue
      let s ← saveState
      if ← closes g tac hb then
        closed := true
        if ← search rest fuel failed dataC propC dbg prev then return true
      s.restore
    unless closed do failed.modify (·.insert ty)
    if (← dbg.get) > 0 && !closed then
      dbg.modify (· - 1); IO.eprintln s!"refute_dep: no closer for {← ppExpr ty}"
    return false
  -- instances
  if (← isClass? ty).isSome && !ty.hasExprMVar then
    let some inst ← (try synthInstance? ty catch _ => pure none)
      | if (← dbg.get) > 0 then dbg.modify (· - 1); IO.eprintln s!"refute_dep: no instance {← ppExpr ty}"
        return false
    g.assign inst
    return ← search rest fuel failed dataC propC dbg prev
  let isTy := (← whnf (← inferType ty)).isSort && (← forallTelescopeReducing ty fun _ b => return b.isSort)
  -- values already given to other binders of the same type (e.g. `t₂ := t₁` for an `Equiv` premise)
  unless isTy do
    for e in prev do
      let s ← saveState
      if (← isDefEq (← inferType e) ty) && (← isDefEq (mkMVar g) e) then
        if ← search rest fuel failed dataC propC dbg prev then return true
      s.restore
  let cands ← if isTy then typeCands else pure dataC
  if (← dbg.get) > 0 then
    let mut okc := #[]
    for c in cands do
      let s ← saveState
      if (← elabAt c ty).isSome then okc := okc.push c
      s.restore
    dbg.modify (· - 1); IO.eprintln s!"refute_dep: candidates for {← ppExpr ty}: {okc.size} {okc.map (·.raw.prettyPrint.pretty)}"
  for c in cands do
    let s ← saveState
    if let some e ← elabAt c ty then
      if ← isDefEq (mkMVar g) e then
        if ← search rest fuel failed dataC propC dbg (if isTy then prev else prev.push e) then return true
    s.restore
  return false

/-- `refute_dep`: proves `¬ ∀ xs, H` by a model for `H`'s law (or an ill-formed literal) and small values.
`refute_dep?` also logs Prop goals that no closer proved. -/
syntax (name := refuteDep) "refute_dep" : tactic
syntax (name := refuteDepDbg) "refute_dep?" : tactic
@[tactic refuteDep, tactic refuteDepDbg] def evalRefuteDep : Tactic := fun stx => do
  let dbg ← IO.mkRef (if stx.isOfKind ``refuteDepDbg then 400 else 0)
  let g ← getMainGoal
  let some (h, g') ← observing? g.intro1 | throwError "refute_dep: goal is not a negation"
  g'.withContext do
    let hty ← instantiateMVars (← h.getType)
    let dataC ← dataCands
    let propC ← propTacs
    -- `h` ends in a class (`… → EquivBEq α`), so it would be a local instance and send instance search into
    -- loops; search in a context without it (only the final term mentions `h`).
    let lctx := (← getLCtx).erase h
    let linsts := (← getLocalInstances).filter (·.fvar != mkFVar h)
    withLCtx lctx linsts do
    for strat in ← strategies do
      let s ← saveState
      let (xs, _, H) ← forallMetaTelescopeReducing hty
      -- instance binders come out synthetic, which unification does not assign
      for x in xs do x.mvarId!.setKind .natural
      let neg ← mkFreshExprMVar (mkNot H)
      let fuel ← IO.mkRef 400
      let failed ← IO.mkRef ({} : Std.HashSet Expr)
      if let some new ← runOn neg.mvarId! strat 400 then
        g'.assign (mkApp neg (mkAppN (mkFVar h) xs))
        -- a free container type `ρ` of `[ForIn m ρ e]` (`insertMany` and friends) has no type candidate: use `List e`
        for x in xs do
          let t ← instantiateMVars (← inferType x)
          if t.isAppOfArity ``ForIn 3 && (t.getArg! 1).isMVar then
            try discard <| isDefEq (t.getArg! 1) (← mkAppM ``List #[t.getArg! 2]) catch _ => pure ()
        let goals := xs.toList.map (·.mvarId!) ++ new
        if ← search goals fuel failed dataC propC dbg then
          let v ← instantiateMVars (mkMVar g')
          unless v.hasExprMVar || v.hasSorry do
            replaceMainGoal []
            return
          if (← dbg.get) > 0 then
            let ms ← getMVars v
            IO.eprintln s!"refute_dep: search succeeded with {strat.raw.prettyPrint.pretty 60} but the term has sorry {v.hasSorry}, {ms.size} mvars: {← ms.toList.take 3 |>.mapM fun m => do ppExpr (← m.getType)}" 
      s.restore
    throwError "refute_dep: no counterexample found"

end RefuteDep

/-!
Probe3 (2026-11-09): hand verdicts for 50 random open Std.Data tree-map rows.
Models: cmpT/OT (equal ↦ eq, else lt: inserting three keys rotates the first one off the search path),
cmpG (equal ↦ eq, else gt; mirror of cmpT), cmpN (near-equality, oriented but not transitive), cmpL,
cmpH; ill-ordered `Impl` literals with lawful `compare`; a bind-counting non-lawful monad CM; OB
(lawful `compare`, `BEq` always true). Removable rows are structural lookups that never use the laws.
-/

open Std Std.DTreeMap.Internal HashInstHand

namespace P3
def tT (l : List Nat) : DTreeMap Nat (fun _ => Nat) cmpT := DTreeMap.ofList (l.map fun k => ⟨k, k+10⟩) cmpT
def tc (l : List (Nat × Nat)) : DTreeMap Nat (fun _ => Nat) compare := DTreeMap.ofList (l.map fun p => ⟨p.1, p.2⟩) compare
def rT (l : List Nat) : DTreeMap.Raw Nat (fun _ => Nat) cmpT := ⟨(tT l).inner⟩
theorem rT_wf (l : List Nat) : (rT l).WF := ⟨(tT l).wf⟩
def cmpG (a b : Nat) : Ordering := if a = b then .eq else .gt
instance : Std.LawfulEqCmp cmpG where
  compare_self := by simp [cmpG]
  eq_of_compare h := by unfold cmpG at h; split at h <;> simp_all
def cmpN (a b : Nat) : Ordering := if a ≤ b + 1 ∧ b ≤ a + 1 then .eq else compare a b
def tG : DTreeMap Nat (fun _ => Nat) cmpG := DTreeMap.ofList [⟨1,1⟩,⟨2,2⟩] cmpG
def tG3 : DTreeMap Nat (fun _ => Nat) cmpG := DTreeMap.ofList [⟨3,13⟩,⟨2,12⟩,⟨1,11⟩] cmpG
-- unordered literals (lawful `compare`): 5 in the left subtree of 1; 3 left of 5 missing; 0 right of 1
def unordA : Impl Nat (fun _ => Nat) := .inner 2 1 1 (.inner 1 5 5 .leaf .leaf) .leaf
def unordB : Impl Nat (fun _ => Nat) := .inner 2 5 5 .leaf (.inner 1 3 3 .leaf .leaf)
def unordC : Impl Nat (fun _ => Nat) := .inner 2 1 1 .leaf (.inner 1 0 0 .leaf .leaf)
-- bind-counting monad (not lawful: `pure x >>= f` counts one bind)
def CM (α : Type) : Type := Nat × α
instance : Monad CM where
  pure a := (0, a)
  bind x f := ((f x.2).1 + x.1 + 1, (f x.2).2)
-- lawful `compare`, but `BEq` always true
structure OB where n : Nat deriving DecidableEq
instance : Ord OB := ⟨fun a b => compare a.n b.n⟩
instance : BEq OB := ⟨fun _ _ => true⟩
instance : Std.TransOrd OB where
  eq_swap {a b} := Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering)) (a := a.n) (b := b.n)
  isLE_trans {a b c} h1 h2 := Std.TransCmp.isLE_trans (cmp := (compare : Nat → Nat → Ordering)) (a := a.n) (b := b.n) (c := c.n) h1 h2
theorem tT123 : (tT [1,2,3]).inner = .inner 3 2 12 (.inner 1 3 13 .leaf .leaf) (.inner 1 1 11 .leaf .leaf) := by rfl
theorem altA : Impl.Const.alter! 5 id unordA = unordA := by rfl
theorem gG : tG.inner = .inner 2 1 1 .leaf (.inner 1 2 2 .leaf .leaf) := by rfl
theorem gG2 : @Impl.erase! Nat (fun _ => Nat) ⟨cmpG⟩ 2 (.inner 2 1 1 .leaf (.inner 1 2 2 .leaf .leaf)) = .inner 1 1 1 .leaf .leaf := by rfl
end P3
open P3

namespace P3R
variable {α : Type u} {β : α → Type v}

theorem minKey?_isNone (t : Impl α β) : t.minKey?.isNone = t.isEmpty := by
  induction t with
  | leaf => simp [Impl.minKey?, Impl.isEmpty]
  | inner sz k v l r ihl ihr =>
    cases l with
    | leaf => simp [Impl.minKey?, Impl.isEmpty]
    | inner sz' k' v' l' r' => rw [Impl.minKey?]; exact ihl

theorem maxKey?_isSome (t : Impl α β) : t.maxKey?.isSome = !t.isEmpty := by
  induction t with
  | leaf => simp [Impl.maxKey?, Impl.isEmpty]
  | inner sz k v l r ihl ihr =>
    cases r with
    | leaf => simp [Impl.maxKey?, Impl.isEmpty]
    | inner sz' k' v' l' r' => rw [Impl.maxKey?]; exact ihr

theorem cmodify_isEmpty {β : Type v} [Ord α] (k : α) (f : β → β) (t : Impl α (fun _ => β)) :
    (Impl.Const.modify k f t).isEmpty = t.isEmpty := by
  cases t with
  | leaf => rfl
  | inner sz k' v' l r => unfold Impl.Const.modify; split <;> rfl

theorem cget?_eq [Ord α] [LawfulEqOrd α] {β : Type v} (a : α) (t : Impl α (fun _ => β)) :
    Impl.Const.get? t a = t.get? a := by
  induction t with
  | leaf => rfl
  | inner _ k v l r ihl ihr =>
    simp only [Impl.Const.get?, Impl.get?]
    split <;> split <;> simp_all

theorem cget_eq [Ord α] {β : Type v} [Inhabited β] (a : α) (t : Impl α (fun _ => β)) :
    ∀ h, Impl.Const.get t a h = Impl.Const.get! t a := by
  induction t with
  | leaf => intro h; exact absurd h (by simp [Impl.mem_iff_contains, Impl.contains])
  | inner _ k v l r ihl ihr =>
    intro h
    simp only [Impl.Const.get, Impl.Const.get!]
    split <;> split <;> simp_all

theorem getKey!_default [Ord α] [Inhabited α] (a : α) (t : Impl α β) :
    Impl.contains a t = false → t.getKey! a = default := by
  induction t with
  | leaf => intro _; rfl
  | inner _ k v l r ihl ihr =>
    intro h
    cases hc : compare a k <;> simp_all [Impl.contains, Impl.getKey!]

theorem get?_getD [Ord α] {β : Type v} (a : α) (fb : β) (t : Impl α (fun _ => β)) :
    Impl.contains a t = true → Impl.Const.get? t a = some (Impl.Const.getD t a fb) := by
  induction t with
  | leaf => intro h; simp [Impl.contains] at h
  | inner _ k v l r ihl ihr =>
    intro h
    cases hc : compare a k <;> simp_all [Impl.contains, Impl.Const.get?, Impl.Const.getD]

theorem cget!_map {β : Type v} {γ : Type w} [Ord α] [LawfulEqOrd α] [Inhabited γ] (f : α → β → γ) (k : α)
    (t : Impl α (fun _ => β)) :
    Impl.Const.get! (Impl.map (γ := fun _ => γ) f t) k = ((Impl.Const.get? t k).map (f k)).get! := by
  induction t with
  | leaf => rfl
  | inner _ k' v l r ihl ihr =>
    simp only [Impl.map, Impl.Const.get!, Impl.Const.get?]
    cases hc : compare k k' with
    | lt => simpa [hc] using ihl
    | gt => simpa [hc] using ihr
    | eq => have := compare_eq_iff_eq.mp hc; subst this; simp [hc]
end P3R

/-! ## Necessary -/

-- `Std.DTreeMap.mem_ofList` (idx 3, necessary): cmpT, l = [1,2,3]: 1 rotated off the search path
theorem n_mem_ofList : ¬ (drop0% Std.DTreeMap.mem_ofList 3) := fun H => by
  have := (@H Nat (fun _ => Nat) cmpT _ _ [⟨1,1⟩,⟨2,2⟩,⟨3,3⟩] 1).2 (by decide)
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.Const.mem_unitOfList` (idx 2, necessary): cmpT, l = [1,2,3], k = 1
theorem n_mem_unitOfList_raw : ¬ (drop0% Std.DTreeMap.Raw.Const.mem_unitOfList 2) := fun H => by
  have := (@H Nat cmpT _ _ [1,2,3] 1).2 (by decide)
  revert this; decide +kernel

-- `Std.DTreeMap.getKeyD_maxKeyD` (idx 4, necessary): cmpT, t = [1,2,3]: max key 1 is unreachable
theorem n_getKeyD_maxKeyD : ¬ (drop0% Std.DTreeMap.getKeyD_maxKeyD 4) := fun H => by
  have := @H Nat (fun _ => Nat) cmpT (tT [1,2,3]) (by decide +kernel) 0 7
  simp only [DTreeMap.maxKeyD, DTreeMap.getKeyD, tT123, Impl.maxKeyD] at this
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.Const.getKey!_insertManyIfNewUnit_empty_list_of_mem` (idx 2, necessary): Ord cmpT, l = [1,2,3], k = k' = 1
theorem n_getKey!_insertManyIfNewUnit : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.getKey!_insertManyIfNewUnit_empty_list_of_mem 2) := fun H => by
  have := @H Nat ⟨cmpT⟩ _ [1,2,3] 1 1 (by decide) (by decide) (by decide)
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.distinct_keys_toList` (idx 4, necessary): Ord cmpT, ofList [1,2,3,1] holds 1 twice
theorem n_distinct_keys_toList : ¬ (drop0% Std.DTreeMap.Internal.Impl.distinct_keys_toList 4) := fun H => by
  have := @H Nat (fun _ => Nat) ⟨cmpT⟩ (tT [1,2,3,1]).inner (tT [1,2,3,1]).wf
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.ordered_keys_toList` (idx 4, necessary): Ord cmpT, ofList [1,2,3,1] holds 1 twice
theorem n_ordered_keys_toList : ¬ (drop0% Std.DTreeMap.Internal.Impl.ordered_keys_toList 4) := fun H => by
  have := @H Nat (fun _ => Nat) ⟨cmpT⟩ (tT [1,2,3,1]).inner (tT [1,2,3,1]).wf
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.contains_of_contains_map` (idx 9, necessary): t = leaf
theorem n_contains_of_contains_map : ¬ (drop0% Std.DTreeMap.Internal.Impl.contains_of_contains_map 9) := fun H => by
  have := @H Nat (fun _ => Nat) instOrdNat .leaf (fun _ => Nat) _ (fun _ v => v) 0 Impl.WF.empty
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.get!_diff!_of_contains_eq_false_left` (idx 11, necessary): m₁ = {0 ↦ 1}, m₂ = leaf, k = 0
theorem n_get!_diff!_left : ¬ (drop0% Std.DTreeMap.Internal.Impl.get!_diff!_of_contains_eq_false_left 11) := fun H => by
  have := @H Nat (fun _ => Nat) instOrdNat (tc [(0,1)]).inner .leaf _ _ (tc [(0,1)]).wf Impl.WF.empty 0 _
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.Equiv.eraseMany_list` (idx 8, necessary): t₁ = leaf, t₂ = {0 ↦ 1}, l = []
theorem n_eraseMany_list : ¬ (drop0% Std.DTreeMap.Internal.Impl.Equiv.eraseMany_list 8) := fun H => by
  have := @H Nat (fun _ => Nat) instOrdNat .leaf (tc [(0,1)]).inner _ Impl.WF.empty (tc [(0,1)]).wf []
  have := this.1.length_eq
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.Equiv.inter!_right` (idx 10, necessary): m₁ = m₂ = {0 ↦ 1}, m₃ = leaf
theorem n_inter!_right : ¬ (drop0% Std.DTreeMap.Internal.Impl.Equiv.inter!_right 10) := fun H => by
  have := @H Nat (fun _ => Nat) instOrdNat (tc [(0,1)]).inner (tc [(0,1)]).inner .leaf _ (tc [(0,1)]).wf (tc [(0,1)]).wf Impl.WF.empty
  have := this.1.length_eq
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.getKey!_union_of_contains_eq_false_right` (idx 10, necessary): m₁ = leaf, m₂ = {1 ↦ 1}, k = 1
theorem n_getKey!_union_right : ¬ (drop0% Std.DTreeMap.Internal.Impl.getKey!_union_of_contains_eq_false_right 10) := fun H => by
  have := @H Nat (fun _ => Nat) instOrdNat .leaf (tc [(1,1)]).inner _ _ Impl.WF.empty (tc [(1,1)]).wf 1
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.get!_of_isEmpty` (idx 9, necessary): t = {0 ↦ 1}, a = 0
theorem n_get!_of_isEmpty : ¬ (drop0% Std.DTreeMap.Raw.get!_of_isEmpty 9) := fun H => by
  have := @H Nat (fun _ => Nat) compare ⟨(tc [(0,1)]).inner⟩ _ _ ⟨(tc [(0,1)]).wf⟩ 0 _
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.Const.get?_eq_some_iff_exists_compare_eq_eq_and_mem_toArray` (idx 4, necessary): cmpT, t = [1,2,3], k = 1 unreachable
theorem n_get?_iff_toArray : ¬ (drop0% Std.DTreeMap.Raw.Const.get?_eq_some_iff_exists_compare_eq_eq_and_mem_toArray 4) := fun H => by
  have := (@H Nat cmpT Nat (rT [1,2,3]) (rT_wf _) 1 11).2 ⟨1, rfl, by decide +kernel⟩
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.Const.getD_alter_self` (idx 4, necessary): cmpL (never eq), t = ∅, f = some 1
theorem n_getD_alter_self : ¬ (drop0% Std.DTreeMap.Raw.Const.getD_alter_self 4) := fun H => by
  have := @H Nat cmpL Nat ∅ Std.DTreeMap.Raw.WF.empty 0 0 (fun _ => some 1)
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.Equiv.constGetD_eq` (idx 5, necessary): cmpT, ofList [1,2,3] vs ofList [3,2,1] (same entries, 1 reachable only in the second)
theorem n_constGetD_eq : ¬ (drop0% Std.DTreeMap.Raw.Equiv.constGetD_eq 5) := fun H => by
  have := @H Nat cmpT Nat (rT [1,2,3]) (rT [3,2,1]) 1 0 (rT_wf _) (rT_wf _) ⟨⟨by decide +kernel⟩⟩
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.Const.equiv_of_beq` (idx 5, necessary): cmpT, [1↦11,2,3,1↦11] vs [1↦99,2,3,1↦11]: only the reachable copies are compared
theorem n_equiv_of_beq : ¬ (drop0% Std.DTreeMap.Raw.Const.equiv_of_beq 5) := fun H => by
  have := @H Nat cmpT Nat ⟨(DTreeMap.ofList [⟨1,11⟩,⟨2,12⟩,⟨3,13⟩,⟨1,11⟩] cmpT).inner⟩
    ⟨(DTreeMap.ofList [⟨1,99⟩,⟨2,12⟩,⟨3,13⟩,⟨1,11⟩] cmpT).inner⟩ _ _ _
    ⟨(DTreeMap.ofList _ cmpT).wf⟩ ⟨(DTreeMap.ofList _ cmpT).wf⟩ (by decide +kernel)
  have := this.1.1
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.minKeyD_eq_iff_mem_and_forall` (idx 6, necessary): ill-ordered t (5 left of 1), km = 5
theorem n_minKeyD_eq_iff : ¬ (drop0% Std.DTreeMap.Internal.Impl.minKeyD_eq_iff_mem_and_forall 6) := fun H => by
  have := ((@H Nat (fun _ => Nat) instOrdNat unordA _ _ rfl 5 0).1 (by simp [unordA, Impl.minKeyD])).1
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.Const.get?_erase!` (idx 5, necessary): ill-ordered t (0 right of 1), erase 1, look up 0
theorem n_get?_erase! : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.get?_erase! 5) := fun H => by
  have := @H Nat instOrdNat Nat unordC _ 1 0
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.Const.minKey?_alter!_eq_self` (idx 5, necessary): ill-ordered t (5 left of 1), k = 5, f = id
theorem n_minKey?_alter! : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.minKey?_alter!_eq_self 5) := fun H => by
  have := ((@H Nat instOrdNat Nat unordA _ 5 id).1 (by rw [altA]; simp [unordA, Impl.minKey?])).1
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.getKey!_union!` (idx 8, necessary): m₁ = {7}, ill-ordered m₂ (3 right of 5): inserting 7 rotates 3 to the root
theorem n_getKey!_union! : ¬ (drop0% Std.DTreeMap.Internal.Impl.getKey!_union! 8) := fun H => by
  have := @H Nat (fun _ => Nat) instOrdNat (tc [(7,7)]).inner unordB _ _ (tc [(7,7)]).wf 3
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.getKey?_diff` (idx 7, necessary): m₁ = {0,1,2}, ill-ordered m₂ (0 right of 1): erasing m₂'s keys removes 0
theorem n_getKey?_diff : ¬ (drop0% Std.DTreeMap.Internal.Impl.getKey?_diff 7) := fun H => by
  have := @H Nat (fun _ => Nat) instOrdNat (tc [(0,0),(1,1),(2,2)]).inner unordC _ (tc _).wf 0
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.isEmpty_union!_inter!` (idx 8, necessary): m₁ = {5}, ill-ordered m₂ (0 right of 1), m₃ = {0}
theorem n_isEmpty_union!_inter! : ¬ (drop0% Std.DTreeMap.Internal.Impl.isEmpty_union!_inter! 8) := fun H => by
  have := @H Nat (fun _ => Nat) instOrdNat (tc [(5,5)]).inner unordC _ (tc [(0,0)]).inner (tc _).wf (tc _).wf
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.Const.toListModel_insertMany!_list` (idx 8, necessary): ill-ordered t (0 right of 1), insert (0,7): duplicate key 0
theorem n_toListModel_insertMany! : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.toListModel_insertMany!_list 8) := fun H => by
  have := (@H Nat Nat instOrdNat _ _ _ [(0,7)] unordC).length_eq
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.get?_union_of_not_mem_right` (idx 7, necessary): ill-ordered t₁ (0 right of 1), t₂ = {5}: rotation makes 0 reachable
theorem n_get?_union_right : ¬ (drop0% Std.DTreeMap.Raw.get?_union_of_not_mem_right 7) := fun H => by
  have := @H Nat (fun _ => Nat) compare ⟨unordC⟩ ⟨(tc [(5,5)]).inner⟩ _ _ ⟨(tc _).wf⟩ 0 (by decide +kernel)
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.get?_insert` (idx 4, necessary): Ord cmpT, t = [1,2], insert 3: 1 rotated off the path
theorem n_get?_insert : ¬ (drop0% Std.DTreeMap.Internal.Impl.get?_insert 4) := fun H => by
  have := @H Nat (fun _ => Nat) ⟨cmpT⟩ (tT [1,2]).inner (inferInstanceAs (Std.LawfulEqCmp cmpT)) (tT [1,2]).wf 1 3 13
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.getD_insertIfNew!` (idx 4, necessary): Ord cmpT, t = [1,2], insertIfNew 3: 1 rotated off the path
theorem n_getD_insertIfNew! : ¬ (drop0% Std.DTreeMap.Internal.Impl.getD_insertIfNew! 4) := fun H => by
  have := @H Nat (fun _ => Nat) ⟨cmpT⟩ (tT [1,2]).inner (inferInstanceAs (Std.LawfulEqCmp cmpT)) (tT [1,2]).wf 3 1 0 13
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.Const.getKey!_alter` (idx 4, necessary): Ord cmpT, t = [1,2], alter 3 to some 0: 1 rotated off the path
theorem n_getKey!_alter : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.getKey!_alter 4) := fun H => by
  have := @H Nat ⟨cmpT⟩ Nat (tT [1,2]).inner _ (tT [1,2]).wf 3 1 (fun _ => some 0)
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.maxKeyD_erase!_le_maxKeyD` (idx 4, necessary): Ord cmpG (unequal ↦ gt), t = [1,2], erase 2
theorem n_maxKeyD_erase! : ¬ (drop0% Std.DTreeMap.Internal.Impl.maxKeyD_erase!_le_maxKeyD 4) := fun H => by
  have := @H Nat (fun _ => Nat) ⟨cmpG⟩ tG.inner tG.wf 2 (by decide +kernel) 0
  simp only [gG, gG2, Impl.maxKeyD] at this
  revert this; decide +kernel

-- `Std.DTreeMap.not_mem_inter_of_not_mem_left` (idx 5, necessary): cmpT, t₁ = [1,2,3] (1 unreachable), t₂ = [5,6,1]: filtering rebuilds t₁ as {1}
theorem n_not_mem_inter : ¬ (drop0% Std.DTreeMap.not_mem_inter_of_not_mem_left 5) := fun H => by
  have := @H Nat (fun _ => Nat) cmpT (tT [1,2,3]) (tT [5,6,1]) 1 (by decide +kernel)
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.Equiv.of_forall_mem_unit_iff` (idx 3, necessary): Ord cmpH (halves), {0} vs {1}
theorem n_of_forall_mem_unit_iff : ¬ (drop0% Std.DTreeMap.Internal.Impl.Equiv.of_forall_mem_unit_iff 3) := fun H => by
  have := @H Nat ⟨cmpH⟩ (inferInstanceAs (Std.TransCmp cmpH)) (.inner 1 0 () .leaf .leaf) (.inner 1 1 () .leaf .leaf)
    (DTreeMap.Const.unitOfList [0] cmpH).wf (DTreeMap.Const.unitOfList [1] cmpH).wf (fun _ => Iff.rfl)
  have := this.1
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.minView_kv_eq_minView!` (idx 8, necessary): dependent; l = leaf, r of size 3
theorem n_minView : ¬ (indep0% Std.DTreeMap.Internal.Impl.minView_kv_eq_minView! 8) := fun H => by
  have := @H Nat (fun _ => Nat) 0 0 .leaf (tc [(0,0),(1,1),(2,2)]).inner .leaf (tc _).wf.balanced
  revert this; simp only [Impl.BalancedAtRoot]; decide +kernel

-- `Std.DTreeMap.Internal.Impl.get!_diff_of_contains_right` (idx 5, necessary): Ord cmpT, m₁ = [1,3,2,1], m₂ = [3,2,1], k = 1
theorem n_get!_diff_right : ¬ (drop0% Std.DTreeMap.Internal.Impl.get!_diff_of_contains_right 5) := fun H => by
  have := @H Nat (fun _ => Nat) ⟨cmpT⟩ (tT [1,3,2,1]).inner (tT [3,2,1]).inner (inferInstanceAs (Std.LawfulEqCmp cmpT)) (tT _).wf (tT _).wf 1 _ (by decide +kernel)
  revert this; decide +kernel

-- `Std.DTreeMap.Const.get!_inter_of_not_mem_right` (idx 5, necessary): cmpT, t₁ = [1,3,2,1], t₂ = [3,2,1], k = 3
theorem n_get!_inter_right : ¬ (drop0% Std.DTreeMap.Const.get!_inter_of_not_mem_right 5) := fun H => by
  have := @H Nat cmpT Nat (tT [1,3,2,1]) (tT [3,2,1]) _ 3 (by decide +kernel)
  revert this; decide +kernel

-- `Std.DTreeMap.Const.get_insertMany_list_of_mem` (idx 4, necessary): cmpN (near-equality), ∅ with [(0,20),(2,22)], k = 2, k' = 1 finds 0
theorem n_get_insertMany : ¬ (drop0% Std.DTreeMap.Const.get_insertMany_list_of_mem 4) := fun H => by
  have := @H Nat cmpN Nat ∅ [(0,20),(2,22)] 2 1 (by decide) 22 (by decide) (by decide) (by decide +kernel)
  revert this; decide +kernel

-- `Std.DTreeMap.get!_erase` (idx 4, necessary): cmpG, t = [3,2,1], erase 2 makes 3 reachable
theorem n_get!_erase : ¬ (drop0% Std.DTreeMap.get!_erase 4) := fun H => by
  have := @H Nat (fun _ => Nat) cmpG tG3 _ 2 3 _
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.forM_eq_forM_keys` (idx 6, necessary): bind-counting monad CM, one-node tree
theorem n_forM_keys : ¬ (drop0% Std.DTreeMap.Raw.forM_eq_forM_keys 6) := fun H => by
  have := congrArg Prod.fst (@H Nat (fun _ => Nat) compare ⟨.inner 1 0 0 .leaf .leaf⟩ CM _ (fun _ => ((0 : Nat), ⟨⟩)))
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.getEntryₘ_eq_getEntry` (idx 5, necessary): OB (BEq always true), t = {0,1}, k = 1
theorem n_getEntryₘ : ¬ (drop0% Std.DTreeMap.Internal.Impl.getEntryₘ_eq_getEntry 5) := fun H => by
  have := congrArg (fun e => e.1.n) (@H OB (fun _ => Unit) _ _ _ ⟨1⟩ (DTreeMap.ofList [⟨⟨0⟩, ()⟩, ⟨⟨1⟩, ()⟩] compare).inner
    (by decide +kernel) (by decide +kernel) (DTreeMap.ofList _ compare).wf.ordered)
  revert this; decide +kernel

/-! ## Removable -/

-- `Std.DTreeMap.isNone_minKey?_eq_isEmpty` (idx 4, removable): structural, no comparison involved
theorem r_isNone_minKey? : drop% Std.DTreeMap.isNone_minKey?_eq_isEmpty 4 := by
  intro α β cmp t
  exact P3R.minKey?_isNone t.inner

-- `Std.DTreeMap.Raw.Const.isSome_maxKey?_modify` (idx 7, removable): modify keeps the shape; maxKey? is structural
theorem r_isSome_maxKey?_modify : drop% Std.DTreeMap.Raw.Const.isSome_maxKey?_modify 7 := by
  intro α cmp β t _ k f
  letI : Ord α := ⟨cmp⟩
  exact (P3R.maxKey?_isSome (Impl.Const.modify k f t.inner)).trans (congrArg (!·) (P3R.cmodify_isEmpty k f t.inner))

-- `Std.DTreeMap.Raw.Const.get?_eq_get?` (idx 6, removable): both follow the same search path
theorem r_get?_eq_get? : drop% Std.DTreeMap.Raw.Const.get?_eq_get? 6 := by
  intro α cmp β t _ _ a
  letI : Ord α := ⟨cmp⟩
  exact P3R.cget?_eq a t.inner

-- `Std.DTreeMap.Internal.Impl.Const.get_eq_get!` (idx 6, removable): both follow the same search path
theorem r_get_eq_get! : drop% Std.DTreeMap.Internal.Impl.Const.get_eq_get! 6 := by
  intro α instOrd β t _ _ a h
  exact P3R.cget_eq a t h

-- `Std.DTreeMap.Raw.getKey!_eq_default` (idx 4, removable): contains and getKey! follow the same search path
theorem r_getKey!_eq_default : drop% Std.DTreeMap.Raw.getKey!_eq_default 4 := by
  intro α β cmp t _ hwf a ha
  letI : Ord α := ⟨cmp⟩
  exact P3R.getKey!_default a t.inner (Bool.eq_false_iff.mpr ha)

-- `Std.DTreeMap.Const.get?_eq_some_getD_of_contains` (idx 4, removable): contains, get? and getD follow the same search path
theorem r_get?_eq_some_getD : drop% Std.DTreeMap.Const.get?_eq_some_getD_of_contains 4 := by
  intro α cmp β t a fb h
  letI : Ord α := ⟨cmp⟩
  exact P3R.get?_getD a fb t.inner h

-- `Std.DTreeMap.Const.get!_map` (idx 5, removable): map keeps the shape; LawfulEqCmp makes the found key equal k
theorem r_get!_map : drop% Std.DTreeMap.Const.get!_map 5 := by
  intro α cmp β γ t _ _ f k
  letI : Ord α := ⟨cmp⟩
  exact P3R.cget!_map f k t.inner

-- `Std.DTreeMap.size_right_le_size_union` (idx 5, removable): union inserts into the larger map, and insert/insertIfNew never shrink (SizedBalancedTree bounds)
theorem r_size_union : drop% Std.DTreeMap.size_right_le_size_union 5 := by
  intro α β cmp t₁ t₂
  letI : Ord α := ⟨cmp⟩
  change t₂.inner.size ≤ (Impl.union t₁.inner t₂.inner t₁.wf.balanced t₂.wf.balanced).size
  unfold Impl.union; split
  · exact (t₂.inner.insertManyIfNew t₁.inner _).2 (P := fun t => t₂.inner.size ≤ t.size) (Nat.le_refl _)
      (fun t'' a b h ih => Nat.le_trans ih (t''.insertIfNew a b h).lb_le_size_impl)
  · exact (t₁.inner.insertMany t₂.inner _).2 (P := fun t => t₂.inner.size ≤ t.size) (by omega)
      (fun t'' a b h ih => Nat.le_trans ih (t''.insert a b h).lb_le_size_impl)

-- `Std.DTreeMap.Const.getKey_unitOfList_of_mem` (idx 9, removable): dependent; from the library's getKey?_unitOfList_of_mem
theorem r_getKey_unitOfList : indep% Std.DTreeMap.Const.getKey_unitOfList_of_mem 9 := by
  intro α cmp _ l k k' h1 h2 h3
  have := DTreeMap.Const.getKey?_unitOfList_of_mem h1 h2 h3
  exact DTreeMap.mem_iff_isSome_getKey?.2 (by rw [this]; rfl)


-- `Std.DTreeMap.Internal.Impl.alter_eq_alterₘ` (idx 9, removable): the library proof without Ordered (it only passes Ordered to the induction hypotheses)
theorem r_alter_eq_alterₘ : drop% Std.DTreeMap.Internal.Impl.alter_eq_alterₘ 9 := by
  intro α β _ _ _ t a f htb
  rw [Impl.alterₘ]
  induction t with
  | leaf =>
    simp only [Impl.alter, Impl.updateCell, Cell.alter, Cell.empty_inner, Cell.ofOption]
    cases f none
    · simp
    · simp
  | inner sz k v l r ihl ihr =>
    rw [Impl.alter, Impl.updateCell]
    split <;> rename_i heq <;> simp only [heq]
    · simp [ihl htb.left]
    · simp [ihr htb.right]
    · apply Eq.symm
      simp [Cell.alter, Cell.ofOption, cast]
      cases h₁ : f _ <;> rfl

-- `Std.DTreeMap.Internal.Impl.Const.isEmpty_insertManyIfNewUnit_empty_list` (idx 2, removable): the first insertion into empty gives size 1, and insertIfNew never shrinks
theorem r_isEmpty_insertManyIfNewUnit : drop% Std.DTreeMap.Internal.Impl.Const.isEmpty_insertManyIfNewUnit_empty_list 2 := by
  intro α instOrd l
  cases l with
  | nil => rfl
  | cons hd tl =>
    rw [Impl.Const.insertManyIfNewUnit_empty_list_cons]
    have h1 : 1 ≤ ((@Impl.empty α (fun _ => Unit)).insertIfNew hd () Impl.WF.empty.balanced).1.size := Nat.le_refl _
    have := (Impl.Const.insertManyIfNewUnit ((@Impl.empty α (fun _ => Unit)).insertIfNew hd () Impl.WF.empty.balanced).1 tl
      Impl.WF.empty.insertIfNew.balanced).2 (P := fun t => 1 ≤ t.size) h1
      (fun t'' a h ih => Nat.le_trans ih (t''.insertIfNew a () h).lb_le_size_impl)
    revert this
    generalize (Impl.Const.insertManyIfNewUnit ((@Impl.empty α (fun _ => Unit)).insertIfNew hd () Impl.WF.empty.balanced).1 tl
      Impl.WF.empty.insertIfNew.balanced).1 = r
    intro this
    cases r with
    | leaf => simp [Impl.size] at this
    | inner => rfl

-- `Std.DTreeMap.Raw.Const.getD_alter_self` (idx 5, necessary): right child with size field 0 makes balanceL! panic (returns leaf) after inserting 3
theorem n_getD_alter_self_wf : ¬ (drop0% Std.DTreeMap.Raw.Const.getD_alter_self 5) := fun H => by
  have := @H Nat compare Nat ⟨.inner 2 10 10 (.inner 1 5 5 .leaf .leaf) (.inner 0 20 20 .leaf .leaf)⟩ _ 3 0 (fun _ => some 7)
  revert this; decide +kernel


namespace P3R
theorem noEq_insert {α : Type u} {β : Type v} [Ord α] (P : α → Prop) (a : α) (b : β) :
    ∀ (t : Impl α (fun _ => β)) (hb : t.Balanced), (∀ p ∈ t.toListModel, P p.1) → P a →
      ∀ p ∈ (t.insert a b hb).impl.toListModel, P p.1
  | .leaf, _, _, ha => by simp [Impl.insert, ha]
  | .inner sz k v l r, hb, ht, ha => by
      have ihl := noEq_insert P a b l hb.left (fun p hp => ht p (by simp [hp])) ha
      have ihr := noEq_insert P a b r hb.right (fun p hp => ht p (by simp [hp])) ha
      simp only [Impl.toListModel_inner, List.mem_append, List.mem_cons] at ht
      rw [Impl.insert]
      split
      · simp only [Impl.toListModel_balanceL, List.mem_append, List.mem_cons]
        rintro p (hp | hp | hp)
        · exact ihl p hp
        · subst hp; exact ht _ (Or.inr (Or.inl rfl))
        · exact ht p (Or.inr (Or.inr hp))
      · simp only [Impl.toListModel_balanceR, List.mem_append, List.mem_cons]
        rintro p (hp | hp | hp)
        · exact ht p (Or.inl hp)
        · subst hp; exact ht _ (Or.inr (Or.inl rfl))
        · exact ihr p hp
      · simp only [Impl.toListModel_inner, List.mem_append, List.mem_cons]
        rintro p (hp | hp | hp)
        · exact ht p (Or.inl hp)
        · subst hp; exact ha
        · exact ht p (Or.inr (Or.inr hp))

theorem noEq_fold {α : Type u} {β : Type v} [Ord α] (P : α → Prop) :
    ∀ (l : List (α × β)) (t : Impl α (fun _ => β)) (hb : t.Balanced), (∀ p ∈ t.toListModel, P p.1) →
      (∀ q ∈ l, P q.1) → ∀ p ∈ (l.foldl (init := t) fun acc ⟨k, v⟩ => acc.insert! k v).toListModel, P p.1
  | [], t, _, ht, _ => ht
  | (a, b) :: l, t, hb, ht, hl => by
      simp only [List.foldl_cons]
      have e : Impl.insert! a b t = (t.insert a b hb).impl := Impl.insert_eq_insert!.symm
      rw [e]
      exact noEq_fold P l _ (t.insert a b hb).balanced_impl
        (noEq_insert P a b t hb ht (hl _ (List.mem_cons_self ..))) (fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem getD_noEq {α : Type u} {β : Type v} [Ord α] (k : α) (fb : β) :
    ∀ t : Impl α (fun _ => β), (∀ p ∈ t.toListModel, compare k p.1 ≠ .eq) → Impl.Const.getD t k fb = fb
  | .leaf, _ => rfl
  | .inner sz k' v l r, ht => by
      simp only [Impl.toListModel_inner, List.mem_append, List.mem_cons] at ht
      have hl := getD_noEq k fb l (fun p hp => ht p (Or.inl hp))
      have hr := getD_noEq k fb r (fun p hp => ht p (Or.inr (Or.inr hp)))
      have hk := ht ⟨k', v⟩ (Or.inr (Or.inl rfl))
      cases hc : compare k k' <;> simp_all [Impl.Const.getD]
end P3R

-- `Std.DTreeMap.Const.getD_ofList_of_contains_eq_false` (idx 3, removable): keys of ofList come from l; LawfulBEqCmp turns contains = false into cmp k key ≠ eq on every key
theorem r_getD_ofList : drop% Std.DTreeMap.Const.getD_ofList_of_contains_eq_false 3 := by
  intro α cmp β _ _ l k fb h
  letI : Ord α := ⟨cmp⟩
  apply P3R.getD_noEq k fb
  show ∀ p ∈ (Impl.Const.ofList l).toListModel, cmp k p.1 ≠ .eq
  rw [Impl.Const.ofList_eq_insertMany, Impl.Const.insertMany_eq_foldl]
  refine P3R.noEq_fold (fun a => cmp k a ≠ .eq) l _ Impl.balanced_empty (by simp [Impl.empty]) ?_
  intro q hq heq
  have h2 := Std.LawfulBEqCmp.compare_eq_iff_beq.1 heq
  simp [List.contains_eq_any_beq] at h
  exact absurd h2 (by simpa using h q.1 q.2 hq)
