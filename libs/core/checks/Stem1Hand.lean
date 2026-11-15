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

/-! ## Probe2 helpers: set operations on literal maps -/

namespace Probe2
open Std Std.DHashMap.Internal HashInstHand
universe u v
variable {α : Type u} {β : Type v}

-- rfl unfoldings of the set-operation notations
theorem hm_inter [BEq α] [Hashable α] (m₁ m₂ : HashMap α β) : m₁ ∩ m₂ = HashMap.inter m₁ m₂ := rfl
theorem hm_diff [BEq α] [Hashable α] (m₁ m₂ : HashMap α β) : m₁ \ m₂ = HashMap.diff m₁ m₂ := rfl
theorem hmr_inter [BEq α] [Hashable α] (m₁ m₂ : HashMap.Raw α β) :
    m₁ ∩ m₂ = ⟨DHashMap.Raw.inter m₁.inner m₂.inner⟩ := rfl
theorem hmr_diff [BEq α] [Hashable α] (m₁ m₂ : HashMap.Raw α β) :
    m₁ \ m₂ = ⟨DHashMap.Raw.diff m₁.inner m₂.inner⟩ := rfl
theorem hmr_union [BEq α] [Hashable α] (m₁ m₂ : HashMap.Raw α β) :
    m₁ ∪ m₂ = ⟨DHashMap.Raw.union m₁.inner m₂.inner⟩ := rfl
theorem hsr_inter [BEq α] [Hashable α] (m₁ m₂ : HashSet.Raw α) :
    m₁ ∩ m₂ = ⟨⟨DHashMap.Raw.inter m₁.inner.inner m₂.inner.inner⟩⟩ := rfl
theorem hsr_diff [BEq α] [Hashable α] (m₁ m₂ : HashSet.Raw α) :
    m₁ \ m₂ = ⟨⟨DHashMap.Raw.diff m₁.inner.inner m₂.inner.inner⟩⟩ := rfl

theorem drn_inter [BEq α] [Hashable α] {γ : α → Type v} (m₁ m₂ : DHashMap.Raw α γ) :
    m₁ ∩ m₂ = DHashMap.Raw.inter m₁ m₂ := rfl
theorem drn_diff [BEq α] [Hashable α] {γ : α → Type v} (m₁ m₂ : DHashMap.Raw α γ) :
    m₁ \ m₂ = DHashMap.Raw.diff m₁ m₂ := rfl
theorem drn_union [BEq α] [Hashable α] {γ : α → Type v} (m₁ m₂ : DHashMap.Raw α γ) :
    m₁ ∪ m₂ = DHashMap.Raw.union m₁ m₂ := rfl

section
variable {γ : α → Type v} [BEq α] [Hashable α]
-- set operations of raw maps with buckets are the Raw₀ ones
theorem dr_inter_lit (s₁ s₂ : Nat) (bs₁ bs₂ : Array (AssocList α γ)) (h₁ : 0 < bs₁.size) (h₂ : 0 < bs₂.size) :
    DHashMap.Raw.inter ⟨s₁, bs₁⟩ ⟨s₂, bs₂⟩ = (Raw₀.inter ⟨⟨s₁, bs₁⟩, h₁⟩ ⟨⟨s₂, bs₂⟩, h₂⟩).1 := by
  simp [DHashMap.Raw.inter, h₁, h₂]
theorem dr_diff_lit (s₁ s₂ : Nat) (bs₁ bs₂ : Array (AssocList α γ)) (h₁ : 0 < bs₁.size) (h₂ : 0 < bs₂.size) :
    DHashMap.Raw.diff ⟨s₁, bs₁⟩ ⟨s₂, bs₂⟩ = (Raw₀.diff ⟨⟨s₁, bs₁⟩, h₁⟩ ⟨⟨s₂, bs₂⟩, h₂⟩).1 := by
  simp [DHashMap.Raw.diff, h₁, h₂]
theorem dr_union_lit (s₁ s₂ : Nat) (bs₁ bs₂ : Array (AssocList α γ)) (h₁ : 0 < bs₁.size) (h₂ : 0 < bs₂.size) :
    DHashMap.Raw.union ⟨s₁, bs₁⟩ ⟨s₂, bs₂⟩ = (Raw₀.union ⟨⟨s₁, bs₁⟩, h₁⟩ ⟨⟨s₂, bs₂⟩, h₂⟩).1 := by
  simp [DHashMap.Raw.union, h₁, h₂]
omit [BEq α] [Hashable α] in
theorem dr_filter_lit (f : (a : α) → γ a → Bool) (s : Nat) (bs : Array (AssocList α γ)) (h : 0 < bs.size) :
    DHashMap.Raw.filter f ⟨s, bs⟩ = (Raw₀.filter f ⟨⟨s, bs⟩, h⟩).1 := by
  simp [DHashMap.Raw.filter, h]
end

end Probe2

open Probe2 HashInstHand Std Std.DHashMap.Internal in
/-- `hm_eval` plus the set operations (∩, \, ∪) and filter, on bundled and literal raw maps. -/
macro "hm_eval2" : tactic => `(tactic| (
  try simp only [hm_inter, hm_diff, hmr_inter, hmr_diff, hmr_union, hsr_inter, hsr_diff, HashMap.diff,
    DHashMap.diff, HashMap.filter, DHashMap.filter, HashMap.Raw.filter,
    Raw₀.diff, drn_inter, drn_diff, drn_union, Raw₀.eraseManyEntries]
  try simp (disch := first | decide | simp [nil16]) only [Std.DHashMap.Raw.ofList, Std.DHashMap.Raw.mem_iff_contains,
    dr_empty, dr_insert_lit, dr_insertIfNew_lit, dr_contains_lit, dr_erase_lit, dr_insertMany_lit,
    dr_inter_lit, dr_diff_lit, dr_union_lit, dr_filter_lit]
  hm_eval))

/-- `hm_eval2` repeated, for operations whose arguments become literals only after an inner evaluation. -/
macro "hm_eval3" : tactic => `(tactic| (hm_eval2 <;> (try hm_eval2) <;> (try hm_eval2)))



/-! ## Stem1 helpers -/

universe u v
namespace Probe2
open Std Std.DHashMap.Internal
universe w
section Gen
variable {α : Type u} {β : α → Type v}

theorem mkIdx_val_congr {n n' : Nat} (e : n = n') (h : 0 < n) (h' : 0 < n') (x : UInt64) :
    (mkIdx n h x).1 = (mkIdx n' h' x).1 := by subst e; rfl

theorem mkIdx_set_toNat {γ : Type w} (bs : Array γ) (i : Nat) (v : γ) (hi : i < bs.size)
    (h : 0 < (bs.set i v hi).size) (x : UInt64) :
    (mkIdx (bs.set i v hi).size h x).1.toNat = (mkIdx bs.size (by simpa using h) x).1.toNat :=
  congrArg USize.toNat (mkIdx_val_congr (by simp) h _ x)

theorem contains_gen [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size} (a : α) :
    Raw₀.contains (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a =
      (bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).contains a := by
  unfold Raw₀.contains; simp only [Array.ugetElem_eq_getElem]

theorem erase_gen [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size} (a : α) :
    Raw₀.erase (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a =
      if (bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).contains a then
        ⟨⟨s - 1, bs.set (mkIdx bs.size h (hash a)).1.toNat
          ((bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).erase a)
          (mkIdx bs.size h (hash a)).2⟩, by simpa using h⟩
      else ⟨⟨s, bs⟩, h⟩ := by
  unfold Raw₀.erase; simp only [Array.ugetElem_eq_getElem, Array.uset_eq_set, Array.set_set]

theorem assoc_contains_of_contains_erase [BEq α] (l : AssocList α β) (k a : α)
    (h : (l.erase k).contains a = true) : l.contains a = true := by
  induction l with
  | nil => exact h
  | cons k' v t ih =>
    simp only [AssocList.erase] at h
    cases hk : (k' == k) <;> simp only [hk, cond_true, cond_false, AssocList.contains] at h
    · rcases Bool.or_eq_true_iff.mp h with h | h
      · simp only [AssocList.contains, h, Bool.true_or]
      · simp only [AssocList.contains, ih h, Bool.or_true]
    · simp only [AssocList.contains, h, Bool.or_true]

theorem raw0_contains_of_contains_erase [BEq α] [Hashable α] (m : Raw₀ α β) (k a : α)
    (h : (m.erase k).contains a = true) : m.contains a = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [erase_gen] at h
  split at h
  · rw [contains_gen] at h ⊢
    simp only [mkIdx_set_toNat] at h
    simp only [Array.getElem_set] at h
    split at h
    · rename_i hi
      have := assoc_contains_of_contains_erase _ k a h
      simp only [hi] at this
      exact this
    · exact h
  · exact h
end Gen

namespace Probe2
open Std Std.DHashMap.Internal
section GenC
variable {α : Type u} {γ : Type v}
theorem cget!_gen [BEq α] [Hashable α] [Inhabited γ] {s : Nat} {bs : Array (AssocList α (fun _ => γ))}
    {h : 0 < bs.size} (a : α) :
    Raw₀.Const.get! (⟨⟨s, bs⟩, h⟩ : Raw₀ α (fun _ => γ)) a =
      (bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).get! a := rfl


theorem assoc_cget!_none [BEq α] [Inhabited γ] (l : AssocList α (fun _ => γ)) (k : α) (h : l.contains k = false) :
    l.get! k = default := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.get!, h.1, cond_false]; exact ih h.2
end GenC
end Probe2

open Std Std.DHashMap.Internal HashInstHand Probe2
namespace S1
universe w'
variable {α : Type u} {β : α → Type v}
theorem ck_any [BEq α] (a : α) (l : List ((a : α) × β a)) :
    Std.Internal.List.containsKey a l = l.any (fun p => p.1 == a) := by
  induction l with
  | nil => rfl
  | cons p t ih => simp [Std.Internal.List.containsKey, ih]
theorem al_map_contains [BEq α] {γ : α → Type w} (f : (a : α) → β a → γ a) (a : α) (l : AssocList α β) :
    (AssocList.map f l).contains a = l.contains a := by
  simp only [AssocList.contains_eq, ck_any, (AssocList.toList_map (f := f) (l := l)).any_eq, List.any_map]
  rfl
theorem map_idx {γ : Type w} {δ : Type w'} (bs : Array γ) (g : γ → δ) (h' : 0 < (bs.map g).size) (h : 0 < bs.size)
    (x : UInt64) : (bs.map g)[(mkIdx (bs.map g).size h' x).1.toNat]'(mkIdx _ h' x).2 =
      g (bs[(mkIdx bs.size h x).1.toNat]'(mkIdx _ h x).2) := by
  have e := mkIdx_val_congr (Array.size_map ..) h' h x
  simp only [Array.getElem_map, e]
theorem raw0_map_contains [BEq α] [Hashable α] {γ : α → Type w} (m : Raw₀ α β) (f : (a : α) → β a → γ a) (a : α) :
    (Raw₀.map f m).contains a = m.contains a := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  show Raw₀.contains ⟨⟨s, bs.map (AssocList.map f)⟩, by simpa using h⟩ a = _
  rw [contains_gen, contains_gen, map_idx _ _ _ h, al_map_contains]
theorem dr_map_contains [BEq α] [Hashable α] {γ : α → Type w} (m : DHashMap.Raw α β) (f : (a : α) → β a → γ a) (a : α) :
    (DHashMap.Raw.map f m).contains a = m.contains a := by
  rcases m with ⟨s, bs⟩
  by_cases h : 0 < bs.size
  · have := raw0_map_contains ⟨⟨s, bs⟩, h⟩ f a
    simp only [DHashMap.Raw.map, h, dite_true]
    unfold DHashMap.Raw.contains
    rw [dif_pos (Raw₀.map f ⟨⟨s, bs⟩, h⟩).2, dif_pos h]
    exact this
  · simp only [DHashMap.Raw.map, h, dite_false, DHashMap.Raw.contains_empty]
    simp [DHashMap.Raw.contains, h]
theorem dm_map_contains [BEq α] [Hashable α] {γ : α → Type w} (m : DHashMap α β) (f : (a : α) → β a → γ a) (a : α) :
    (DHashMap.map f m).contains a = m.contains a := by
  exact raw0_map_contains ⟨m.1, m.2.size_buckets_pos⟩ f a
abbrev f16 {α : Type u} {β : α → Type v} (b : AssocList α β) : Array (AssocList α β) :=
  #[b, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil]
theorem dr_ins0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0 = ⟨1, f16 (.cons 0 0 .nil)⟩ := by
  simp only [dr_empty]; hm_eval_raw
theorem hmr_ins0 : (∅ : HashMap.Raw Nat Nat).insert 0 0 = hmr 1 (f16 (b1 0 0)) := by
  simp only [HashMap.Raw.insert, hmr_empty]; hm_eval_raw
theorem hsr_ins0 : (∅ : HashSet.Raw Nat).insert 0 = hsr 1 (f16 (b1 0 ())) := by
  simp only [HashSet.Raw.insert, HashMap.Raw.insertIfNew, hsr_empty]; hm_eval_raw
end S1

namespace S1
variable {α : Type u} {β : α → Type v}
theorem nil16_get (i : Nat) (h : i < (nil16 : Array (AssocList α β)).size) : (nil16 : Array (AssocList α β))[i] = .nil := by
  have := Array.getElem_mem h
  generalize (nil16 : Array (AssocList α β))[i] = x at this ⊢
  simpa [nil16] using this
theorem raw0_nil16_contains [BEq α] [Hashable α] (s : Nat) (h : 0 < (nil16 : Array (AssocList α β)).size) (k : α) :
    Raw₀.contains (⟨⟨s, nil16⟩, h⟩ : Raw₀ α β) k = false := by
  rw [contains_gen, nil16_get]; rfl
theorem dr_nil16_contains [BEq α] [Hashable α] (s : Nat) (k : α) :
    (⟨s, nil16⟩ : DHashMap.Raw α β).contains k = false := by
  simp only [DHashMap.Raw.contains]; rw [dif_pos (by simp [nil16])]; exact raw0_nil16_contains _ _ _
end S1

namespace S1
section R
variable {α : Type u} {β : α → Type v}
theorem expand_size [BEq α] [Hashable α] (m : Raw₀ α β) : (Raw₀.expandIfNecessary m).1.size = m.1.size := by
  obtain ⟨⟨s, bs⟩, h⟩ := m; unfold Raw₀.expandIfNecessary; dsimp only; split <;> rfl
theorem insertIfNew_size_ge [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    m.1.size ≤ (m.insertIfNew a b).1.size := by
  obtain ⟨⟨s, bs⟩, h⟩ := m; unfold Raw₀.insertIfNew; dsimp only; split
  · exact Nat.le_refl _
  · rw [expand_size]; exact Nat.le_succ _
theorem raw0_imnu_isEmpty [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (m : Raw₀ α (fun _ => Unit)) (l : ρ)
    (h : (Raw₀.Const.insertManyIfNewUnit m l).1.1.isEmpty = true) : m.1.isEmpty = true := by
  have := (Raw₀.Const.insertManyIfNewUnit m l).2 (fun m' => m.1.size ≤ m'.1.size)
    (fun h => Nat.le_trans h (insertIfNew_size_ge _ _ _)) (Nat.le_refl _)
  simp only [DHashMap.Raw.isEmpty, beq_iff_eq] at h ⊢; omega
theorem dm_imnu [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (m : DHashMap α (fun _ => Unit)) (l : ρ)
    (h : (DHashMap.Const.insertManyIfNewUnit m l).isEmpty = true) : m.isEmpty = true :=
  raw0_imnu_isEmpty ⟨m.1, m.2.size_buckets_pos⟩ l h
theorem dr_imnu [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (m : DHashMap.Raw α (fun _ => Unit)) (l : ρ)
    (h : (DHashMap.Raw.Const.insertManyIfNewUnit m l).isEmpty = true) : m.isEmpty = true := by
  unfold DHashMap.Raw.Const.insertManyIfNewUnit at h; split at h
  · exact raw0_imnu_isEmpty ⟨m, _⟩ l h
  · exact h
-- alter on a key that is absent adds exactly one entry (no laws needed)
theorem assoc_getCast?_none [BEq α] [LawfulBEq α] (l : AssocList α β) (k : α) (h : l.contains k = false) :
    l.getCast? k = none := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.getCast?, h.1]; exact ih h.2
theorem raw0_alter_size [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k : α) (f : Option (β k) → Option (β k))
    (hc : m.contains k = false) (hs : (f (m.get? k)).isSome = true) : (m.alter k f).1.size = m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  rw [contains_gen] at hc
  have hg : Raw₀.get? (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) k = none := by
    unfold Raw₀.get?; simp only [Array.ugetElem_eq_getElem]; exact assoc_getCast?_none _ _ hc
  rw [hg] at hs
  unfold Raw₀.alter; simp only [Array.ugetElem_eq_getElem, hc, Bool.false_eq_true, ite_false]
  split
  · rename_i e; rw [e] at hs; simp at hs
  · rw [expand_size]
end R
section C
variable {α : Type u} {γ : Type v}
theorem assoc_cget?_none' [BEq α] (l : AssocList α (fun _ => γ)) (k : α) (h : l.contains k = false) :
    l.get? k = none := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.get?, h.1, cond_false]; exact ih h.2
theorem raw0_calter_size [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (k : α) (f : Option γ → Option γ)
    (hc : m.contains k = false) (hs : (f (Raw₀.Const.get? m k)).isSome = true) :
    (Raw₀.Const.alter m k f).1.size = m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  rw [contains_gen] at hc
  have hg : Raw₀.Const.get? (⟨⟨s, bs⟩, h⟩ : Raw₀ α (fun _ => γ)) k = none := by
    unfold Raw₀.Const.get?; simp only [Array.ugetElem_eq_getElem]; exact assoc_cget?_none' _ _ hc
  rw [hg] at hs
  unfold Raw₀.Const.alter; simp only [Array.ugetElem_eq_getElem, hc, Bool.false_eq_true, ite_false]
  split
  · rename_i e; rw [e] at hs; simp at hs
  · rw [expand_size]
theorem dm_calter_size [BEq α] [Hashable α] (m : DHashMap α (fun _ => γ)) (k : α) (f : Option γ → Option γ)
    (hc : ¬ k ∈ m) (hs : (f (DHashMap.Const.get? m k)).isSome = true) :
    (DHashMap.Const.alter m k f).size = m.size + 1 :=
  raw0_calter_size ⟨m.1, m.2.size_buckets_pos⟩ k f (Bool.eq_false_iff.mpr hc) hs
end C
end S1

namespace S1
section D
variable {α : Type u} {β : α → Type v}
theorem al_filter_contains [BEq α] (f : (a : α) → β a → Bool) (a : α) (l : AssocList α β)
    (h : (l.filter f).contains a = true) : l.contains a = true := by
  simp only [AssocList.contains_eq, ck_any, (AssocList.toList_filter (f := f) (l := l)).any_eq, List.any_filter] at h ⊢
  simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨x, hx, -, hx2⟩ := h; exact ⟨x, hx, hx2⟩
theorem raw0_filter_contains [BEq α] [Hashable α] (f : (a : α) → β a → Bool) (m : Raw₀ α β) (k : α)
    (h : (Raw₀.filter f m).contains k = true) : m.contains k = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have e : Raw₀.filter f ⟨⟨s, bs⟩, hb⟩ =
      ⟨⟨computeSize (bs.map (AssocList.filter f)), bs.map (AssocList.filter f)⟩, by simpa using hb⟩ := rfl
  rw [e, contains_gen, map_idx _ _ _ hb] at h
  rw [contains_gen]; exact al_filter_contains _ _ _ h
theorem raw0_diff_contains [BEq α] [Hashable α] (m₁ m₂ : Raw₀ α β) (k : α)
    (h : (Raw₀.diff m₁ m₂).contains k = true) : m₁.contains k = true := by
  unfold Raw₀.diff at h; split at h
  · exact raw0_filter_contains _ _ _ h
  · exact (Raw₀.eraseManyEntries m₁ m₂.1).2 (fun m => m.contains k = true → m₁.contains k = true)
      (fun hP h' => hP (raw0_contains_of_contains_erase _ _ _ h')) id h
theorem raw0_diff_nc [BEq α] [Hashable α] (m₁ m₂ : Raw₀ α β) (k : α) (h : m₁.contains k = false) :
    (Raw₀.diff m₁ m₂).contains k = false := by
  cases e : (Raw₀.diff m₁ m₂).contains k
  · rfl
  · rw [raw0_diff_contains _ _ _ e] at h; cases h
theorem assoc_getKey!_none [BEq α] [Inhabited α] (l : AssocList α β) (k : α) (h : l.contains k = false) :
    l.getKey! k = default := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.getKey!, h.1]; exact ih h.2
theorem assoc_getCast!_none [BEq α] [LawfulBEq α] (l : AssocList α β) (k : α) [Inhabited (β k)]
    (h : l.contains k = false) : l.getCast! k = default := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.getCast!, h.1]; exact ih h.2
theorem raw0_getKey!_nc [BEq α] [Hashable α] [Inhabited α] (m : Raw₀ α β) (k : α) (h : m.contains k = false) :
    m.getKey! k = default := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; exact assoc_getKey!_none _ _ h
theorem raw0_get!_nc [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k : α) [Inhabited (β k)]
    (h : m.contains k = false) : m.get! k = default := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; exact assoc_getCast!_none _ _ h
-- raw diff: when m₁ has buckets, the result is m₁ or a Raw₀ diff of it
theorem dr_diff_nc [BEq α] [Hashable α] (m₁ m₂ : DHashMap.Raw α β) (k : α) (h₁ : 0 < m₁.buckets.size)
    (h : ¬ k ∈ m₁) : ∃ h' : 0 < (m₁ \ m₂).buckets.size, Raw₀.contains ⟨m₁ \ m₂, h'⟩ k = false := by
  have hc : Raw₀.contains ⟨m₁, h₁⟩ k = false := by
    simpa [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, h₁] using h
  by_cases h₂ : 0 < m₂.buckets.size
  · have e : m₁ \ m₂ = (Raw₀.diff ⟨m₁, h₁⟩ ⟨m₂, h₂⟩).1 := by
      show DHashMap.Raw.diff _ _ = _; simp [DHashMap.Raw.diff, h₁, h₂]
    rw [e]; exact ⟨(Raw₀.diff ⟨m₁, h₁⟩ ⟨m₂, h₂⟩).2, raw0_diff_nc _ _ _ hc⟩
  · have e : m₁ \ m₂ = m₁ := by
      show DHashMap.Raw.diff _ _ = _; simp [DHashMap.Raw.diff, h₁, h₂]
    rw [e]; exact ⟨h₁, hc⟩
end D
section DC
variable {α : Type u} {γ : Type v}
theorem raw0_cget!_nc [BEq α] [Hashable α] [Inhabited γ] (m : Raw₀ α (fun _ => γ)) (k : α)
    (h : m.contains k = false) : Raw₀.Const.get! m k = default := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; rw [cget!_gen]; exact assoc_cget!_none _ _ h
theorem dm_cget!_diff [BEq α] [Hashable α] [Inhabited γ] (m₁ m₂ : DHashMap α (fun _ => γ)) (k : α) (h : ¬ k ∈ m₁) :
    DHashMap.Const.get! (m₁.diff m₂) k = default :=
  raw0_cget!_nc _ _ (raw0_diff_nc _ _ _ (Bool.eq_false_iff.mpr h))
theorem hs_get!_diff [BEq α] [Hashable α] [Inhabited α] (m₁ m₂ : HashSet α) (k : α) (h : ¬ k ∈ m₁) :
    (m₁ \ m₂).get! k = default :=
  raw0_getKey!_nc _ _ (raw0_diff_nc _ _ _ (Bool.eq_false_iff.mpr h))
theorem drc_get!_diff [BEq α] [Hashable α] [Inhabited γ] (m₁ m₂ : DHashMap.Raw α (fun _ => γ)) (h₁ : m₁.WF) (k : α)
    (h : ¬ k ∈ m₁) : DHashMap.Raw.Const.get! (m₁.diff m₂) k = default := by
  obtain ⟨h', hc⟩ := dr_diff_nc m₁ m₂ k h₁.size_buckets_pos h
  show DHashMap.Raw.Const.get! (m₁ \ m₂) k = default
  unfold DHashMap.Raw.Const.get!; rw [dif_pos h']; exact raw0_cget!_nc _ _ hc
theorem hsr_get!_diff [BEq α] [Hashable α] [Inhabited α] (m₁ m₂ : HashSet.Raw α) (h₁ : m₁.WF) (k : α)
    (h : ¬ k ∈ m₁) : (m₁ \ m₂).get! k = default := by
  obtain ⟨h', hc⟩ := dr_diff_nc m₁.inner.inner m₂.inner.inner k h₁.out.out.size_buckets_pos h
  show DHashMap.Raw.getKey! (m₁.inner.inner \ m₂.inner.inner) k = default
  unfold DHashMap.Raw.getKey!; rw [dif_pos h']; exact raw0_getKey!_nc _ _ hc
end DC
theorem dr_get!_diff {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulBEq α] (m₁ m₂ : DHashMap.Raw α β)
    (h₁ : m₁.WF) (k : α) [Inhabited (β k)] (h : ¬ k ∈ m₁) : (m₁ \ m₂).get! k = default := by
  obtain ⟨h', hc⟩ := dr_diff_nc m₁ m₂ k h₁.size_buckets_pos h
  unfold DHashMap.Raw.get!; rw [dif_pos h']; exact raw0_get!_nc _ _ hc
end S1

namespace S1
/-- `NE`: `a == b ↔ a ≠ b` (irreflexive, symmetric), hash `0`. `LawfulHashable` ✓, `EquivBEq` ✗. -/
structure NE where n : Nat deriving DecidableEq, Inhabited
instance : BEq NE := ⟨fun a b => decide (a.n ≠ b.n)⟩
instance : Hashable NE := ⟨fun _ => 0⟩
instance : LawfulHashable NE := ⟨fun _ _ _ => rfl⟩
@[simp] theorem NE.beq_def (a b : NE) : (a == b) = decide (a.n ≠ b.n) := rfl
@[simp] theorem NE.hash_def (a : NE) : hash a = 0 := rfl
theorem NE.broken : ∀ [EquivBEq NE] [LawfulHashable NE], False := fun {h _} => by
  exact absurd ((NE.beq_def ⟨0⟩ ⟨0⟩).symm.trans (@ReflBEq.rfl NE _ _ ⟨0⟩)) (by decide)
section G
variable {α : Type u} {β : α → Type v}
theorem assoc_getKey?_some [BEq α] [EquivBEq α] (l : AssocList α β) (a a' : α) (h : l.getKey? a = some a') :
    (a' == a) = true ∧ l.contains a' = true := by
  induction l with
  | nil => cases h
  | cons k v t ih =>
    simp only [AssocList.getKey?] at h
    split at h
    · rename_i hk; cases h; exact ⟨hk, by simp [AssocList.contains]⟩
    · obtain ⟨h1, h2⟩ := ih h; exact ⟨h1, by simp only [AssocList.contains, h2, Bool.or_true]⟩
theorem raw0_contains_of_getKey? [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) (a a' : α)
    (h : m.getKey? a = some a') : m.contains a' = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have e : Raw₀.getKey? (⟨⟨s, bs⟩, hb⟩ : Raw₀ α β) a =
      (bs[(mkIdx bs.size hb (hash a)).1.toNat]'(mkIdx bs.size hb (hash a)).2).getKey? a := by
    unfold Raw₀.getKey?; simp only [Array.ugetElem_eq_getElem]
  rw [e] at h
  obtain ⟨h1, h2⟩ := assoc_getKey?_some _ _ _ h
  have hh : hash a' = hash a := hash_eq h1
  rw [contains_gen]; simp only [hh]; exact h2
end G
end S1

namespace S1
-- AB literal with key 1 in its own bucket (1 of 2): WFImp holds although AB is not LawfulHashable
theorem ab_wfimp : Raw.WFImp (⟨1, #[.nil, b1 (AB.mk 1) (0 : Nat)]⟩ : DHashMap.Raw AB (fun _ => Nat)) where
  buckets_hash_self := ⟨fun i hi => by
    match i, hi with
    | 0, _ => exact List.hashesTo_nil
    | 1, _ =>
      refine List.hashesTo_cons (fun h' => ?_) List.hashesTo_nil
      rw [mkIdx_toNat' _ h' _ (by decide)]; decide⟩
  size_eq := by simp [toListModel]
  distinct := ⟨by simp [toListModel]⟩
end S1

namespace S1
section K
variable {α : Type u} {β : α → Type v}
theorem lgk_append [BEq α] (a : α) (l₁ l₂ : List ((a : α) × β a)) :
    Std.Internal.List.getKey? a (l₁ ++ l₂) = (Std.Internal.List.getKey? a l₁).or (Std.Internal.List.getKey? a l₂) := by
  induction l₁ with
  | nil => rfl
  | cons p t ih => simp only [List.cons_append, Std.Internal.List.getKey?]; split <;> simp [ih]
theorem lgk_none [BEq α] (a : α) (l : List ((a : α) × β a)) (h : ∀ p ∈ l, (p.1 == a) = false) :
    Std.Internal.List.getKey? a l = none := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    simp only [Std.Internal.List.getKey?, h p (by simp), Bool.false_eq_true, ite_false]
    exact ih (fun q hq => h q (by simp [hq]))
theorem flat_getKey [BEq α] (a : α) (L : List (AssocList α β)) (t : Nat) (ht : t < L.length)
    (hno : ∀ t' (h' : t' < L.length), t' ≠ t → ∀ p ∈ (L[t']).toList, (p.1 == a) = false) :
    Std.Internal.List.getKey? a (L.flatMap AssocList.toList) = Std.Internal.List.getKey? a (L[t]).toList := by
  induction L generalizing t with
  | nil => simp at ht
  | cons b L ih =>
    rw [List.flatMap_cons, lgk_append]
    cases t with
    | zero =>
      rw [lgk_none a (L.flatMap AssocList.toList)]
      · simp
      · intro p hp
        simp only [List.mem_flatMap] at hp
        obtain ⟨b', hb', hp⟩ := hp
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'
        exact hno (j + 1) (by simp; omega) (by omega) p hp
    | succ s =>
      rw [lgk_none a b.toList (hno 0 (by simp) (by omega))]
      simp only [Option.none_or, List.getElem_cons_succ]
      exact ih s (by simp at ht; omega) (fun t' h' ne p hp => hno (t' + 1) (by simp; omega) (by omega) p hp)
theorem getKeyDm_noequiv [BEq α] [Hashable α] [LawfulHashable α] (m : Raw₀ α β) (hm : Raw.WFImp m.1) (a fb : α) :
    m.getKeyDₘ a fb = Std.Internal.List.getKeyD a (toListModel m.1.buckets) fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [Std.Internal.List.getKeyD_eq_getKey?]
  show ((bucket bs hb a).getKey? a).getD fb = _
  rw [bucket_eq, AssocList.getKey?_eq, toListModel]
  congr 1
  simp only [Array.ugetElem_eq_getElem]
  have hi := (mkIdx bs.size hb (hash a)).2
  rw [flat_getKey a bs.toList (mkIdx bs.size hb (hash a)).1.toNat (by simpa using hi)]
  · simp
  · intro t' h' ne p hp
    cases e : (p.1 == a)
    · rfl
    · exfalso; apply ne
      have h2 := (hm.buckets_hash_self.hashes_to t' (by simpa using h')).hash_self hb p (by simpa using hp)
      rw [← h2, hash_eq e]
end K
end S1

open Std Std.DHashMap.Internal HashInstHand Probe2 S1

namespace Stem1V

-- `Std.DHashMap.Internal.Raw₀.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (EquivBEq α unused)
theorem s0 : drop% Std.DHashMap.Internal.Raw₀.contains_map 6 :=
  by intros; apply raw0_map_contains

-- `Std.DHashMap.Raw.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (EquivBEq α unused)
theorem s1 : drop% Std.DHashMap.Raw.contains_map 6 :=
  by intros; apply dr_map_contains

-- `Std.DHashMap.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (EquivBEq α unused)
theorem s2 : drop% Std.DHashMap.contains_map 6 :=
  by intros; apply dm_map_contains

-- `Std.HashMap.Raw.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (EquivBEq α unused)
theorem s3 : drop% Std.HashMap.Raw.contains_map 6 :=
  by intros; apply dr_map_contains

-- `Std.HashMap.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (EquivBEq α unused)
theorem s4 : drop% Std.HashMap.contains_map 6 :=
  by intros; apply dm_map_contains

-- `Std.DHashMap.Internal.Raw₀.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (LawfulHashable α unused)
theorem s5 : drop% Std.DHashMap.Internal.Raw₀.contains_map 7 :=
  by intros; apply raw0_map_contains

-- `Std.DHashMap.Raw.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (LawfulHashable α unused)
theorem s6 : drop% Std.DHashMap.Raw.contains_map 7 :=
  by intros; apply dr_map_contains

-- `Std.DHashMap.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (LawfulHashable α unused)
theorem s7 : drop% Std.DHashMap.contains_map 7 :=
  by intros; apply dm_map_contains

-- `Std.HashMap.Raw.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (LawfulHashable α unused)
theorem s8 : drop% Std.HashMap.Raw.contains_map 7 :=
  by intros; apply dr_map_contains

-- `Std.HashMap.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (LawfulHashable α unused)
theorem s9 : drop% Std.HashMap.contains_map 7 :=
  by intros; apply dm_map_contains

-- `Std.DHashMap.Internal.Raw₀.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (m.val.WF unused)
theorem s10 : drop% Std.DHashMap.Internal.Raw₀.contains_map 10 :=
  by intros; apply raw0_map_contains

-- `Std.DHashMap.Raw.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (m.WF unused)
theorem s11 : drop% Std.DHashMap.Raw.contains_map 10 :=
  by intros; apply dr_map_contains

-- `Std.HashMap.Raw.contains_map`: removable: map keeps the bucket array (AssocList.map only reverses each bucket), so contains is unchanged for any BEq/Hashable and any raw map (m.WF unused)
theorem s12 : drop% Std.HashMap.Raw.contains_map 10 :=
  by intros; apply dr_map_contains

-- `Std.DHashMap.Raw.Equiv.contains_eq`: NS: key 0 in bucket 0 vs bucket 1 of two (same entry list, so Equiv); contains 0 is true in the first, false in the second
theorem s13 : ¬ drop0% Std.DHashMap.Raw.Equiv.contains_eq 6 :=
  fun h =>
  absurd (h (m₁ := ⟨0, #[b1 (NS.mk 0) (0 : Nat), .nil]⟩) (m₂ := ⟨0, #[.nil, b1 (NS.mk 0) (0 : Nat)]⟩) (k := ⟨0⟩)
    (wf_vac NS.broken _ (by decide)) (wf_vac NS.broken _ (by decide)) ⟨by simp [toListModel]⟩) (by hm_eval_raw)

-- `Std.HashMap.Equiv.contains_eq`: NS: key 0 in bucket 0 vs bucket 1 of two (same entry list, so Equiv); contains 0 is true in the first, false in the second
theorem s14 : ¬ drop0% Std.HashMap.Equiv.contains_eq 6 :=
  fun h =>
  absurd (h (m₁ := hm NS.broken 0 #[b1 (NS.mk 0) (0 : Nat), .nil] (by decide))
    (m₂ := hm NS.broken 0 #[.nil, b1 (NS.mk 0) (0 : Nat)] (by decide)) (k := ⟨0⟩) ⟨⟨⟨by simp [toListModel]⟩⟩⟩) (by hm_eval)

-- `Std.HashMap.Raw.Equiv.contains_eq`: NS: key 0 in bucket 0 vs bucket 1 of two (same entry list, so Equiv); contains 0 is true in the first, false in the second
theorem s15 : ¬ drop0% Std.HashMap.Raw.Equiv.contains_eq 6 :=
  fun h =>
  absurd (h (m₁ := hmr 0 #[b1 (NS.mk 0) (0 : Nat), .nil]) (m₂ := hmr 0 #[.nil, b1 (NS.mk 0) (0 : Nat)]) (k := ⟨0⟩)
    (hmr_wf NS.broken _ _ (by decide)) (hmr_wf NS.broken _ _ (by decide)) ⟨⟨by simp [toListModel]⟩⟩) (by hm_eval)

-- `Std.HashSet.Equiv.contains_eq`: NS: key 0 in bucket 0 vs bucket 1 of two (same entry list, so Equiv); contains 0 is true in the first, false in the second
theorem s16 : ¬ drop0% Std.HashSet.Equiv.contains_eq 5 :=
  fun h =>
  absurd (h (m₁ := hs NS.broken 0 #[b1 (NS.mk 0) (), .nil] (by decide))
    (m₂ := hs NS.broken 0 #[.nil, b1 (NS.mk 0) ()] (by decide)) (k := ⟨0⟩) ⟨⟨⟨⟨by simp [toListModel]⟩⟩⟩⟩) (by hm_eval)

-- `Std.HashSet.Raw.Equiv.contains_eq`: NS: key 0 in bucket 0 vs bucket 1 of two (same entry list, so Equiv); contains 0 is true in the first, false in the second
theorem s17 : ¬ drop0% Std.HashSet.Raw.Equiv.contains_eq 5 :=
  fun h =>
  absurd (h (m₁ := hsr 0 #[b1 (NS.mk 0) (), .nil]) (m₂ := hsr 0 #[.nil, b1 (NS.mk 0) ()]) (k := ⟨0⟩)
    (hsr_wf NS.broken _ _ (by decide)) (hsr_wf NS.broken _ _ (by decide)) ⟨⟨⟨by simp [toListModel]⟩⟩⟩) (by hm_eval)

-- `Std.DHashMap.Raw.Equiv.contains_eq`: AB: key 0 in bucket 0 vs bucket 1 of two (same entry list, so Equiv); contains 0 is true in the first, false in the second
theorem s18 : ¬ drop0% Std.DHashMap.Raw.Equiv.contains_eq 7 :=
  fun h =>
  absurd (h (m₁ := ⟨0, #[b1 (AB.mk 0) (0 : Nat), .nil]⟩) (m₂ := ⟨0, #[.nil, b1 (AB.mk 0) (0 : Nat)]⟩) (k := ⟨0⟩)
    (wf_vac AB.broken _ (by decide)) (wf_vac AB.broken _ (by decide)) ⟨by simp [toListModel]⟩) (by hm_eval_raw)

-- `Std.HashMap.Equiv.contains_eq`: AB: key 0 in bucket 0 vs bucket 1 of two (same entry list, so Equiv); contains 0 is true in the first, false in the second
theorem s19 : ¬ drop0% Std.HashMap.Equiv.contains_eq 7 :=
  fun h =>
  absurd (h (m₁ := hm AB.broken 0 #[b1 (AB.mk 0) (0 : Nat), .nil] (by decide))
    (m₂ := hm AB.broken 0 #[.nil, b1 (AB.mk 0) (0 : Nat)] (by decide)) (k := ⟨0⟩) ⟨⟨⟨by simp [toListModel]⟩⟩⟩) (by hm_eval)

-- `Std.HashMap.Raw.Equiv.contains_eq`: AB: key 0 in bucket 0 vs bucket 1 of two (same entry list, so Equiv); contains 0 is true in the first, false in the second
theorem s20 : ¬ drop0% Std.HashMap.Raw.Equiv.contains_eq 7 :=
  fun h =>
  absurd (h (m₁ := hmr 0 #[b1 (AB.mk 0) (0 : Nat), .nil]) (m₂ := hmr 0 #[.nil, b1 (AB.mk 0) (0 : Nat)]) (k := ⟨0⟩)
    (hmr_wf AB.broken _ _ (by decide)) (hmr_wf AB.broken _ _ (by decide)) ⟨⟨by simp [toListModel]⟩⟩) (by hm_eval)

-- `Std.HashSet.Equiv.contains_eq`: AB: key 0 in bucket 0 vs bucket 1 of two (same entry list, so Equiv); contains 0 is true in the first, false in the second
theorem s21 : ¬ drop0% Std.HashSet.Equiv.contains_eq 6 :=
  fun h =>
  absurd (h (m₁ := hs AB.broken 0 #[b1 (AB.mk 0) (), .nil] (by decide))
    (m₂ := hs AB.broken 0 #[.nil, b1 (AB.mk 0) ()] (by decide)) (k := ⟨0⟩) ⟨⟨⟨⟨by simp [toListModel]⟩⟩⟩⟩) (by hm_eval)

-- `Std.HashSet.Raw.Equiv.contains_eq`: AB: key 0 in bucket 0 vs bucket 1 of two (same entry list, so Equiv); contains 0 is true in the first, false in the second
theorem s22 : ¬ drop0% Std.HashSet.Raw.Equiv.contains_eq 6 :=
  fun h =>
  absurd (h (m₁ := hsr 0 #[b1 (AB.mk 0) (), .nil]) (m₂ := hsr 0 #[.nil, b1 (AB.mk 0) ()]) (k := ⟨0⟩)
    (hsr_wf AB.broken _ _ (by decide)) (hsr_wf AB.broken _ _ (by decide)) ⟨⟨⟨by simp [toListModel]⟩⟩⟩) (by hm_eval)

-- `Std.HashMap.Equiv.contains_eq`: lawful Nat: m1 = ∅, m2 = {0}; contains 0 differs
theorem s23 : ¬ drop0% Std.HashMap.Equiv.contains_eq 9 :=
  fun h => by
  have := h (m₁ := (∅ : HashMap Nat Nat)) (m₂ := (∅ : HashMap Nat Nat).insert 0 0) (k := 0)
  simp at this

-- `Std.HashMap.Raw.Equiv.contains_eq`: lawful Nat: m1 = ∅, m2 = {0}; contains 0 differs
theorem s24 : ¬ drop0% Std.HashMap.Raw.Equiv.contains_eq 11 :=
  fun h => by
  have := h (m₁ := (∅ : HashMap.Raw Nat Nat)) (m₂ := (∅ : HashMap.Raw Nat Nat).insert 0 0) (k := 0) .empty (.insert .empty)
  simp [HashMap.Raw.contains_insert HashMap.Raw.WF.empty] at this

-- `Std.HashSet.Equiv.contains_eq`: lawful Nat: m1 = ∅, m2 = {0}; contains 0 differs
theorem s25 : ¬ drop0% Std.HashSet.Equiv.contains_eq 8 :=
  fun h => by
  have := h (m₁ := (∅ : HashSet Nat)) (m₂ := (∅ : HashSet Nat).insert 0) (k := 0)
  simp at this

-- `Std.HashSet.Raw.Equiv.contains_eq`: lawful Nat: m1 = ∅, m2 = {0}; contains 0 differs
theorem s26 : ¬ drop0% Std.HashSet.Raw.Equiv.contains_eq 10 :=
  fun h => by
  have := h (m₁ := (∅ : HashSet.Raw Nat)) (m₂ := (∅ : HashSet.Raw Nat).insert 0) (k := 0) .empty (.insert .empty)
  simp [HashSet.Raw.contains_insert HashSet.Raw.WF.empty] at this

-- `Std.DHashMap.Raw.Equiv.contains_eq`: lawful Nat: m₁ has key 0 misplaced in bucket 1 of 2 (not WF), m₂ = ∅.insert 0 (WF); same entries, so Equiv, but contains 0 differs
theorem s27 : ¬ drop0% Std.DHashMap.Raw.Equiv.contains_eq 9 :=
  fun h => by
  have := h (m₁ := ⟨0, #[.nil, .cons 0 0 .nil]⟩) (m₂ := ⟨1, f16 (.cons 0 0 .nil)⟩) (k := 0) (dr_ins0 ▸ DHashMap.Raw.WF.insert .empty)
    ⟨by simp [toListModel]⟩
  revert this; hm_eval_raw

-- `Std.DHashMap.Raw.Equiv.contains_eq`: lawful Nat: m₂ has key 0 misplaced in bucket 1 of 2 (not WF), m₁ = ∅.insert 0 (WF); same entries, so Equiv, but contains 0 differs
theorem s28 : ¬ drop0% Std.DHashMap.Raw.Equiv.contains_eq 10 :=
  fun h => by
  have := h (m₂ := ⟨0, #[.nil, .cons 0 0 .nil]⟩) (m₁ := ⟨1, f16 (.cons 0 0 .nil)⟩) (k := 0) (dr_ins0 ▸ DHashMap.Raw.WF.insert .empty)
    ⟨by simp [toListModel]⟩
  revert this; hm_eval_raw

-- `Std.HashMap.Raw.Equiv.contains_eq`: lawful Nat: m₁ has key 0 misplaced in bucket 1 of 2 (not WF), m₂ = ∅.insert 0 (WF); same entries, so Equiv, but contains 0 differs
theorem s29 : ¬ drop0% Std.HashMap.Raw.Equiv.contains_eq 9 :=
  fun h => by
  have := h (m₁ := hmr 0 #[.nil, b1 0 0]) (m₂ := hmr 1 (f16 (b1 0 0))) (k := 0) (hmr_ins0 ▸ .insert .empty)
    ⟨⟨by simp [toListModel]⟩⟩
  revert this; hm_eval

-- `Std.HashMap.Raw.Equiv.contains_eq`: lawful Nat: m₂ has key 0 misplaced in bucket 1 of 2 (not WF), m₁ = ∅.insert 0 (WF); same entries, so Equiv, but contains 0 differs
theorem s30 : ¬ drop0% Std.HashMap.Raw.Equiv.contains_eq 10 :=
  fun h => by
  have := h (m₂ := hmr 0 #[.nil, b1 0 0]) (m₁ := hmr 1 (f16 (b1 0 0))) (k := 0) (hmr_ins0 ▸ .insert .empty)
    ⟨⟨by simp [toListModel]⟩⟩
  revert this; hm_eval

-- `Std.HashSet.Raw.Equiv.contains_eq`: lawful Nat: m₁ has key 0 misplaced in bucket 1 of 2 (not WF), m₂ = ∅.insert 0 (WF); same entries, so Equiv, but contains 0 differs
theorem s31 : ¬ drop0% Std.HashSet.Raw.Equiv.contains_eq 8 :=
  fun h => by
  have := h (m₁ := hsr 0 #[.nil, b1 0 ()]) (m₂ := hsr 1 (f16 (b1 0 ()))) (k := 0) (hsr_ins0 ▸ HashSet.Raw.WF.insert HashSet.Raw.WF.empty)
    ⟨⟨⟨by simp [toListModel]⟩⟩⟩
  revert this; hm_eval

-- `Std.HashSet.Raw.Equiv.contains_eq`: lawful Nat: m₂ has key 0 misplaced in bucket 1 of 2 (not WF), m₁ = ∅.insert 0 (WF); same entries, so Equiv, but contains 0 differs
theorem s32 : ¬ drop0% Std.HashSet.Raw.Equiv.contains_eq 9 :=
  fun h => by
  have := h (m₂ := hsr 0 #[.nil, b1 0 ()]) (m₁ := hsr 1 (f16 (b1 0 ()))) (k := 0) (hsr_ins0 ▸ HashSet.Raw.WF.insert HashSet.Raw.WF.empty)
    ⟨⟨⟨by simp [toListModel]⟩⟩⟩
  revert this; hm_eval

-- `Std.DHashMap.Internal.Raw₀.size_alter_eq_add_one`: lawful Nat: m = ∅, f = const none; alter changes nothing, size 0 ≠ 1
theorem s33 : ¬ drop0% Std.DHashMap.Internal.Raw₀.size_alter_eq_add_one 10 :=
  fun h => by
  have := h (m := (Raw₀.emptyWithCapacity : Raw₀ Nat (fun _ => Nat))) (k := 0) (f := fun _ => none) DHashMap.Raw.WF.emptyWithCapacity₀ (by simp [Raw₀.contains_emptyWithCapacity])
  simp [Std.DHashMap.Internal.Raw₀.size_alter _ DHashMap.Raw.WF.emptyWithCapacity₀, Raw₀.size_emptyWithCapacity] at this

-- `Std.DHashMap.Raw.size_alter_eq_add_one`: lawful Nat: m = ∅, f = const none; alter changes nothing, size 0 ≠ 1
theorem s34 : ¬ drop0% Std.DHashMap.Raw.size_alter_eq_add_one 10 :=
  fun h => by
  have := h (m := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (k := 0) (f := fun _ => none) DHashMap.Raw.WF.empty (by simp)
  simp [Std.DHashMap.Raw.size_alter DHashMap.Raw.WF.empty] at this

-- `Std.DHashMap.size_alter_eq_add_one`: lawful Nat: m = ∅, f = const none; alter changes nothing, size 0 ≠ 1
theorem s35 : ¬ drop0% Std.DHashMap.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (m := (∅ : DHashMap Nat (fun _ => Nat))) (k := 0) (f := fun _ => none) (by simp)
  simp [Std.DHashMap.size_alter] at this

-- `Std.ExtDHashMap.size_alter_eq_add_one`: lawful Nat: m = ∅, f = const none; alter changes nothing, size 0 ≠ 1
theorem s36 : ¬ drop0% Std.ExtDHashMap.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (m := (∅ : ExtDHashMap Nat (fun _ => Nat))) (k := 0) (f := fun _ => none) (by simp)
  simp [Std.ExtDHashMap.size_alter] at this

-- `Std.DHashMap.Const.size_alter_eq_add_one`: lawful Nat: m = ∅, f = const none; alter changes nothing, size 0 ≠ 1
theorem s37 : ¬ drop0% Std.DHashMap.Const.size_alter_eq_add_one 10 :=
  fun h => by
  have := h (m := (∅ : DHashMap Nat (fun _ => Nat))) (k := 0) (f := fun _ => none) (by simp)
  simp [Std.DHashMap.Const.size_alter] at this

-- `Std.DHashMap.Internal.Raw₀.Const.size_alter_eq_add_one`: lawful Nat: m = ∅, f = const none; alter changes nothing, size 0 ≠ 1
theorem s38 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.size_alter_eq_add_one 11 :=
  fun h => by
  have := h (m := (Raw₀.emptyWithCapacity : Raw₀ Nat (fun _ => Nat))) (k := 0) (f := fun _ => none) DHashMap.Raw.WF.emptyWithCapacity₀ (by simp [Raw₀.contains_emptyWithCapacity])
  simp [Std.DHashMap.Internal.Raw₀.Const.size_alter _ DHashMap.Raw.WF.emptyWithCapacity₀, Raw₀.size_emptyWithCapacity] at this

-- `Std.DHashMap.Raw.Const.size_alter_eq_add_one`: lawful Nat: m = ∅, f = const none; alter changes nothing, size 0 ≠ 1
theorem s39 : ¬ drop0% Std.DHashMap.Raw.Const.size_alter_eq_add_one 10 :=
  fun h => by
  have := h (m := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (k := 0) (f := fun _ => none) DHashMap.Raw.WF.empty (by simp)
  simp [Std.DHashMap.Raw.Const.size_alter DHashMap.Raw.WF.empty] at this

-- `Std.ExtDHashMap.Const.size_alter_eq_add_one`: lawful Nat: m = ∅, f = const none; alter changes nothing, size 0 ≠ 1
theorem s40 : ¬ drop0% Std.ExtDHashMap.Const.size_alter_eq_add_one 10 :=
  fun h => by
  have := h (m := (∅ : ExtDHashMap Nat (fun _ => Nat))) (k := 0) (f := fun _ => none) (by simp)
  simp [Std.ExtDHashMap.Const.size_alter] at this

-- `Std.ExtHashMap.size_alter_eq_add_one`: lawful Nat: m = ∅, f = const none; alter changes nothing, size 0 ≠ 1
theorem s41 : ¬ drop0% Std.ExtHashMap.size_alter_eq_add_one 10 :=
  fun h => by
  have := h (m := (∅ : ExtHashMap Nat Nat)) (k := 0) (f := fun _ => none) (by simp)
  simp [Std.ExtHashMap.size_alter] at this

-- `Std.HashMap.Raw.size_alter_eq_add_one`: lawful Nat: m = ∅, f = const none; alter changes nothing, size 0 ≠ 1
theorem s42 : ¬ drop0% Std.HashMap.Raw.size_alter_eq_add_one 10 :=
  fun h => by
  have := h (m := (∅ : HashMap.Raw Nat Nat)) (k := 0) (f := fun _ => none) HashMap.Raw.WF.empty (by simp)
  simp [Std.HashMap.Raw.size_alter HashMap.Raw.WF.empty] at this

-- `Std.HashMap.size_alter_eq_add_one`: lawful Nat: m = ∅, f = const none; alter changes nothing, size 0 ≠ 1
theorem s43 : ¬ drop0% Std.HashMap.size_alter_eq_add_one 10 :=
  fun h => by
  have := h (m := (∅ : HashMap Nat Nat)) (k := 0) (f := fun _ => none) (by simp)
  simp [Std.HashMap.size_alter] at this

-- `Std.DHashMap.Internal.Raw₀.Const.size_alter_eq_add_one`: lawful Nat: m = {0 ↦ 0}, k = 0, f = const some 0; alter replaces, size stays 1 ≠ 2
theorem s44 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.size_alter_eq_add_one 10 :=
  fun h => by
  have := h (m := (Raw₀.emptyWithCapacity : Raw₀ Nat (fun _ => Nat)).insert 0 0) (k := 0) (f := fun _ => some 0) (DHashMap.Raw.WF.insert₀ DHashMap.Raw.WF.emptyWithCapacity₀) (by simp [Raw₀.get?_insert _ DHashMap.Raw.WF.emptyWithCapacity₀, Raw₀.Const.get?_insert _ DHashMap.Raw.WF.emptyWithCapacity₀])
  simp [Std.DHashMap.Internal.Raw₀.Const.size_alter _ (DHashMap.Raw.WF.insert₀ DHashMap.Raw.WF.emptyWithCapacity₀), Raw₀.contains_insert _ DHashMap.Raw.WF.emptyWithCapacity₀, Raw₀.size_insert _ DHashMap.Raw.WF.emptyWithCapacity₀, Raw₀.size_emptyWithCapacity] at this

-- `Std.DHashMap.Internal.Raw₀.size_alter_eq_add_one`: lawful Nat: m = {0 ↦ 0}, k = 0, f = const some 0; alter replaces, size stays 1 ≠ 2
theorem s45 : ¬ drop0% Std.DHashMap.Internal.Raw₀.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (m := (Raw₀.emptyWithCapacity : Raw₀ Nat (fun _ => Nat)).insert 0 0) (k := 0) (f := fun _ => some 0) (DHashMap.Raw.WF.insert₀ DHashMap.Raw.WF.emptyWithCapacity₀) (by simp [Raw₀.get?_insert _ DHashMap.Raw.WF.emptyWithCapacity₀, Raw₀.Const.get?_insert _ DHashMap.Raw.WF.emptyWithCapacity₀])
  simp [Std.DHashMap.Internal.Raw₀.size_alter _ (DHashMap.Raw.WF.insert₀ DHashMap.Raw.WF.emptyWithCapacity₀), Raw₀.contains_insert _ DHashMap.Raw.WF.emptyWithCapacity₀, Raw₀.size_insert _ DHashMap.Raw.WF.emptyWithCapacity₀, Raw₀.size_emptyWithCapacity] at this

-- `Std.DHashMap.Const.size_alter_eq_add_one`: lawful Nat: m = {0 ↦ 0}, k = 0, f = const some 0; alter replaces, size stays 1 ≠ 2
theorem s46 : ¬ drop0% Std.DHashMap.Const.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (m := (∅ : DHashMap Nat (fun _ => Nat)).insert 0 0) (k := 0) (f := fun _ => some 0) (by simp)
  simp [Std.DHashMap.Const.size_alter] at this

-- `Std.DHashMap.Raw.Const.size_alter_eq_add_one`: lawful Nat: m = {0 ↦ 0}, k = 0, f = const some 0; alter replaces, size stays 1 ≠ 2
theorem s47 : ¬ drop0% Std.DHashMap.Raw.Const.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (m := (∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0) (k := 0) (f := fun _ => some 0) (DHashMap.Raw.WF.insert DHashMap.Raw.WF.empty) (by simp [Std.DHashMap.Raw.Const.get?_insert DHashMap.Raw.WF.empty])
  simp [Std.DHashMap.Raw.Const.size_alter (DHashMap.Raw.WF.insert DHashMap.Raw.WF.empty), Std.DHashMap.Raw.mem_insert DHashMap.Raw.WF.empty, Std.DHashMap.Raw.size_insert DHashMap.Raw.WF.empty] at this

-- `Std.DHashMap.Raw.size_alter_eq_add_one`: lawful Nat: m = {0 ↦ 0}, k = 0, f = const some 0; alter replaces, size stays 1 ≠ 2
theorem s48 : ¬ drop0% Std.DHashMap.Raw.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (m := (∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0) (k := 0) (f := fun _ => some 0) (DHashMap.Raw.WF.insert DHashMap.Raw.WF.empty) (by simp [Std.DHashMap.Raw.get?_insert DHashMap.Raw.WF.empty])
  simp [Std.DHashMap.Raw.size_alter (DHashMap.Raw.WF.insert DHashMap.Raw.WF.empty), Std.DHashMap.Raw.mem_insert DHashMap.Raw.WF.empty, Std.DHashMap.Raw.size_insert DHashMap.Raw.WF.empty] at this

-- `Std.DHashMap.size_alter_eq_add_one`: lawful Nat: m = {0 ↦ 0}, k = 0, f = const some 0; alter replaces, size stays 1 ≠ 2
theorem s49 : ¬ drop0% Std.DHashMap.size_alter_eq_add_one 8 :=
  fun h => by
  have := h (m := (∅ : DHashMap Nat (fun _ => Nat)).insert 0 0) (k := 0) (f := fun _ => some 0) (by simp)
  simp [Std.DHashMap.size_alter] at this

-- `Std.ExtDHashMap.Const.size_alter_eq_add_one`: lawful Nat: m = {0 ↦ 0}, k = 0, f = const some 0; alter replaces, size stays 1 ≠ 2
theorem s50 : ¬ drop0% Std.ExtDHashMap.Const.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (m := (∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0) (k := 0) (f := fun _ => some 0) (by simp)
  simp [Std.ExtDHashMap.Const.size_alter] at this

-- `Std.ExtDHashMap.size_alter_eq_add_one`: lawful Nat: m = {0 ↦ 0}, k = 0, f = const some 0; alter replaces, size stays 1 ≠ 2
theorem s51 : ¬ drop0% Std.ExtDHashMap.size_alter_eq_add_one 8 :=
  fun h => by
  have := h (m := (∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0) (k := 0) (f := fun _ => some 0) (by simp)
  simp [Std.ExtDHashMap.size_alter] at this

-- `Std.ExtHashMap.size_alter_eq_add_one`: lawful Nat: m = {0 ↦ 0}, k = 0, f = const some 0; alter replaces, size stays 1 ≠ 2
theorem s52 : ¬ drop0% Std.ExtHashMap.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (m := (∅ : ExtHashMap Nat Nat).insert 0 0) (k := 0) (f := fun _ => some 0) (by simp)
  simp [Std.ExtHashMap.size_alter] at this

-- `Std.HashMap.Raw.size_alter_eq_add_one`: lawful Nat: m = {0 ↦ 0}, k = 0, f = const some 0; alter replaces, size stays 1 ≠ 2
theorem s53 : ¬ drop0% Std.HashMap.Raw.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (m := (∅ : HashMap.Raw Nat Nat).insert 0 0) (k := 0) (f := fun _ => some 0) (HashMap.Raw.WF.insert HashMap.Raw.WF.empty) (by simp [Std.HashMap.Raw.getElem?_insert HashMap.Raw.WF.empty])
  simp [Std.HashMap.Raw.size_alter (HashMap.Raw.WF.insert HashMap.Raw.WF.empty), Std.HashMap.Raw.mem_insert HashMap.Raw.WF.empty, Std.HashMap.Raw.size_insert HashMap.Raw.WF.empty] at this

-- `Std.HashMap.size_alter_eq_add_one`: lawful Nat: m = {0 ↦ 0}, k = 0, f = const some 0; alter replaces, size stays 1 ≠ 2
theorem s54 : ¬ drop0% Std.HashMap.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (m := (∅ : HashMap Nat Nat).insert 0 0) (k := 0) (f := fun _ => some 0) (by simp)
  simp [Std.HashMap.size_alter] at this

-- `Std.DHashMap.Raw.Const.size_alter_eq_add_one`: lawful Nat: m = raw map without buckets (not WF); alter returns ∅, size 0 ≠ 1
theorem s55 : ¬ drop0% Std.DHashMap.Raw.Const.size_alter_eq_add_one 8 :=
  fun h => by
  have := h (m := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (k := 0) (f := fun _ => some 0) (by simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains]) (by rfl)
  simp [DHashMap.Raw.Const.alter, DHashMap.Raw.size] at this

-- `Std.DHashMap.Raw.size_alter_eq_add_one`: lawful Nat: m = raw map without buckets (not WF); alter returns ∅, size 0 ≠ 1
theorem s56 : ¬ drop0% Std.DHashMap.Raw.size_alter_eq_add_one 8 :=
  fun h => by
  have := h (m := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (k := 0) (f := fun _ => some 0) (by simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains]) (by rfl)
  simp [DHashMap.Raw.alter, DHashMap.Raw.size] at this

-- `Std.HashMap.Raw.size_alter_eq_add_one`: lawful Nat: m = raw map without buckets (not WF); alter returns ∅, size 0 ≠ 1
theorem s57 : ¬ drop0% Std.HashMap.Raw.size_alter_eq_add_one 8 :=
  fun h => by
  have := h (m := (⟨⟨0, #[]⟩⟩ : HashMap.Raw Nat Nat)) (k := 0) (f := fun _ => some 0) (by simp [HashMap.Raw.mem_iff_contains, HashMap.Raw.contains, DHashMap.Raw.contains]) (by rfl)
  simp [HashMap.Raw.alter, DHashMap.Raw.Const.alter, HashMap.Raw.size, DHashMap.Raw.size] at this

-- `Std.HashMap.Raw.isEmpty_of_isEmpty_insertManyIfNewUnit`: lawful Nat: m = {0}, l = []; m is not empty
theorem s58 : ¬ drop0% Std.HashMap.Raw.isEmpty_of_isEmpty_insertManyIfNewUnit 10 :=
  fun h => by
  have := h (m := (∅ : HashMap.Raw Nat Unit).insert 0 ()) (HashMap.Raw.WF.insert HashMap.Raw.WF.empty) (l := ([] : List Nat))
  simp [HashMap.Raw.isEmpty_insert HashMap.Raw.WF.empty] at this

-- `Std.HashMap.isEmpty_of_isEmpty_insertManyIfNewUnit`: lawful Nat: m = {0}, l = []; m is not empty
theorem s59 : ¬ drop0% Std.HashMap.isEmpty_of_isEmpty_insertManyIfNewUnit 9 :=
  fun h => by
  have := h (m := (∅ : HashMap Nat Unit).insert 0 ()) (l := ([] : List Nat))
  simp at this

-- `Std.DHashMap.Const.isEmpty_of_isEmpty_insertManyIfNewUnit`: lawful Nat: m = {0}, l = []; m is not empty
theorem s60 : ¬ drop0% Std.DHashMap.Const.isEmpty_of_isEmpty_insertManyIfNewUnit 9 :=
  fun h => by
  have := h (m := (∅ : DHashMap Nat (fun _ => Unit)).insert 0 ()) (l := ([] : List Nat))
  simp at this

-- `Std.DHashMap.Internal.Raw₀.Const.isEmpty_of_isEmpty_insertManyIfNewUnit`: lawful Nat: m = {0}, l = []; m is not empty
theorem s61 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.isEmpty_of_isEmpty_insertManyIfNewUnit 10 :=
  fun h => by
  have := h (m := (Raw₀.emptyWithCapacity : Raw₀ Nat (fun _ => Unit)).insert 0 ()) (DHashMap.Raw.WF.insert₀ DHashMap.Raw.WF.emptyWithCapacity₀) (l := ([] : List Nat))
  simp [Raw₀.isEmpty_insert _ DHashMap.Raw.WF.emptyWithCapacity₀] at this

-- `Std.DHashMap.Raw.Const.isEmpty_of_isEmpty_insertManyIfNewUnit`: lawful Nat: m = {0}, l = []; m is not empty
theorem s62 : ¬ drop0% Std.DHashMap.Raw.Const.isEmpty_of_isEmpty_insertManyIfNewUnit 10 :=
  fun h => by
  have := h (m := (∅ : DHashMap.Raw Nat (fun _ => Unit)).insert 0 ()) (DHashMap.Raw.WF.insert DHashMap.Raw.WF.empty) (l := ([] : List Nat))
  simp [DHashMap.Raw.isEmpty_insert DHashMap.Raw.WF.empty] at this

-- `Std.DHashMap.Const.get!_diff_of_not_mem_left`: lawful Nat: m1 = {0 ↦ 1}, m2 = ∅, k = 0; get! k = 1, not default 0
theorem s63 : ¬ drop0% Std.DHashMap.Const.get!_diff_of_not_mem_left 10 :=
  fun h => by
  have := h (m₁ := (∅ : DHashMap Nat (fun _ => Nat)).insert 0 1) (m₂ := (∅ : DHashMap Nat (fun _ => Nat))) (k := 0)
  rw [Std.DHashMap.Const.get!_diff] at this; simp [] at this

-- `Std.DHashMap.Raw.Const.get!_diff_of_not_mem_left`: lawful Nat: m1 = {0 ↦ 1}, m2 = ∅, k = 0; get! k = 1, not default 0
theorem s64 : ¬ drop0% Std.DHashMap.Raw.Const.get!_diff_of_not_mem_left 12 :=
  fun h => by
  have := h (m₁ := (∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 1) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (DHashMap.Raw.WF.insert DHashMap.Raw.WF.empty) DHashMap.Raw.WF.empty (k := 0)
  rw [Std.DHashMap.Raw.Const.get!_diff (DHashMap.Raw.WF.insert DHashMap.Raw.WF.empty) DHashMap.Raw.WF.empty] at this; simp [] at this

-- `Std.DHashMap.Raw.get!_diff_of_not_mem_left`: lawful Nat: m1 = {0 ↦ 1}, m2 = ∅, k = 0; get! k = 1, not default 0
theorem s65 : ¬ drop0% Std.DHashMap.Raw.get!_diff_of_not_mem_left 11 :=
  fun h => by
  have := h (m₁ := (∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 1) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (DHashMap.Raw.WF.insert DHashMap.Raw.WF.empty) DHashMap.Raw.WF.empty (k := 0)
  rw [Std.DHashMap.Raw.get!_diff (DHashMap.Raw.WF.insert DHashMap.Raw.WF.empty) DHashMap.Raw.WF.empty] at this; simp [] at this

-- `Std.DHashMap.get!_diff_of_not_mem_left`: lawful Nat: m1 = {0 ↦ 1}, m2 = ∅, k = 0; get! k = 1, not default 0
theorem s66 : ¬ drop0% Std.DHashMap.get!_diff_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := (∅ : DHashMap Nat (fun _ => Nat)).insert 0 1) (m₂ := (∅ : DHashMap Nat (fun _ => Nat))) (k := 0)
  rw [Std.DHashMap.get!_diff] at this; simp [] at this

-- `Std.ExtDHashMap.Const.get!_diff_of_not_mem_left`: lawful Nat: m1 = {0 ↦ 1}, m2 = ∅, k = 0; get! k = 1, not default 0
theorem s67 : ¬ drop0% Std.ExtDHashMap.Const.get!_diff_of_not_mem_left 10 :=
  fun h => by
  have := h (m₁ := (∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 1) (m₂ := (∅ : ExtDHashMap Nat (fun _ => Nat))) (k := 0)
  rw [Std.ExtDHashMap.Const.get!_diff] at this; simp [] at this

-- `Std.ExtDHashMap.get!_diff_of_not_mem_left`: lawful Nat: m1 = {0 ↦ 1}, m2 = ∅, k = 0; get! k = 1, not default 0
theorem s68 : ¬ drop0% Std.ExtDHashMap.get!_diff_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := (∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 1) (m₂ := (∅ : ExtDHashMap Nat (fun _ => Nat))) (k := 0)
  rw [Std.ExtDHashMap.get!_diff] at this; simp [] at this

-- `Std.ExtHashMap.get!_diff_of_not_mem_left`: lawful Nat: m1 = {0 ↦ 1}, m2 = ∅, k = 0; get! k = 1, not default 0
theorem s69 : ¬ drop0% Std.ExtHashMap.get!_diff_of_not_mem_left 10 :=
  fun h => by
  have := h (m₁ := (∅ : ExtHashMap Nat Nat).insert 0 1) (m₂ := (∅ : ExtHashMap Nat Nat)) (k := 0)
  rw [Std.ExtHashMap.get!_diff] at this; simp [] at this

-- `Std.ExtHashSet.get!_diff_of_not_mem_left`: lawful Nat: m1 = {1}, m2 = ∅, k = 1; get! k = 1, not default 0
theorem s70 : ¬ drop0% Std.ExtHashSet.get!_diff_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := (∅ : ExtHashSet Nat).insert 1) (m₂ := (∅ : ExtHashSet Nat)) (k := 1)
  rw [Std.ExtHashSet.get!_diff] at this; simp [Std.ExtHashSet.get!_insert] at this

-- `Std.HashSet.Raw.get!_diff_of_not_mem_left`: lawful Nat: m1 = {1}, m2 = ∅, k = 1; get! k = 1, not default 0
theorem s71 : ¬ drop0% Std.HashSet.Raw.get!_diff_of_not_mem_left 11 :=
  fun h => by
  have := h (m₁ := (∅ : HashSet.Raw Nat).insert 1) (m₂ := (∅ : HashSet.Raw Nat)) (HashSet.Raw.WF.insert HashSet.Raw.WF.empty) HashSet.Raw.WF.empty (k := 1)
  rw [Std.HashSet.Raw.get!_diff (HashSet.Raw.WF.insert HashSet.Raw.WF.empty) HashSet.Raw.WF.empty] at this; simp [Std.HashSet.Raw.get!_insert HashSet.Raw.WF.empty] at this

-- `Std.HashSet.get!_diff_of_not_mem_left`: lawful Nat: m1 = {1}, m2 = ∅, k = 1; get! k = 1, not default 0
theorem s72 : ¬ drop0% Std.HashSet.get!_diff_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := (∅ : HashSet Nat).insert 1) (m₂ := (∅ : HashSet Nat)) (k := 1)
  rw [Std.HashSet.get!_diff] at this; simp [Std.HashSet.get!_insert] at this

-- `Std.DHashMap.Internal.List.hashesTo_cons`: size 2, i = 0, k = 0, l = [⟨1, 0⟩]: key 1 hashes to bucket 1, so l does not hash to 0
theorem s73 : ¬ drop0% Std.DHashMap.Internal.List.hashesTo_cons 10 :=
  fun h => by
  have := (h (β := fun _ => Nat) (l := [⟨1, 0⟩]) (i := 0) (size := 2) (k := 0) (v := 0)
    (fun h' => by rw [mkIdx_toNat' 2 h' _ (by decide)]; decide)).hash_self (by decide) ⟨1, 0⟩ (by simp)
  rw [mkIdx_toNat' 2 _ _ (by decide)] at this
  revert this; decide

-- `Std.DHashMap.Internal.List.hashesTo_cons`: size 1, i = 1, l = []: every key hashes to bucket 0 ≠ 1
theorem s74 : ¬ drop0% Std.DHashMap.Internal.List.hashesTo_cons 9 :=
  fun h => by
  have := (h (β := fun _ => Nat) (l := []) (i := 1) (size := 1) (k := 0) (v := 0) List.hashesTo_nil).hash_self Nat.one_pos ⟨0, 0⟩ (by simp)
  rw [mkIdx_toNat' 1 _ _ (by decide)] at this; omega

-- `Std.DHashMap.Raw.Const.get!_diff_of_not_mem_left`: lawful Nat: m1 = raw map without buckets (not WF), m2 = {0 ↦ 1} (sets: {1}); Raw.diff then returns m2, so get! is 1, not default
theorem s75 : ¬ drop0% Std.DHashMap.Raw.Const.get!_diff_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 1)
    (.insert .empty) (k := 0) (by simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains])
  simp only [SDiff.sdiff, DHashMap.Raw.diff, Nat.lt_irrefl, List.size_toArray, List.length_nil, dite_false] at this
  simp [DHashMap.Raw.Const.get!_insert DHashMap.Raw.WF.empty] at this

-- `Std.DHashMap.Raw.get!_diff_of_not_mem_left`: lawful Nat: m1 = raw map without buckets (not WF), m2 = {0 ↦ 1} (sets: {1}); Raw.diff then returns m2, so get! is 1, not default
theorem s76 : ¬ drop0% Std.DHashMap.Raw.get!_diff_of_not_mem_left 7 :=
  fun h => by
  have := h (m₁ := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 1)
    (.insert .empty) (k := 0) (by simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains])
  simp only [SDiff.sdiff, DHashMap.Raw.diff, Nat.lt_irrefl, List.size_toArray, List.length_nil, dite_false] at this
  simp [DHashMap.Raw.get!_insert DHashMap.Raw.WF.empty] at this

-- `Std.HashSet.Raw.get!_diff_of_not_mem_left`: lawful Nat: m1 = raw map without buckets (not WF), m2 = {0 ↦ 1} (sets: {1}); Raw.diff then returns m2, so get! is 1, not default
theorem s77 : ¬ drop0% Std.HashSet.Raw.get!_diff_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := (⟨⟨⟨0, #[]⟩⟩⟩ : HashSet.Raw Nat)) (m₂ := (∅ : HashSet.Raw Nat).insert 1)
    (.insert .empty) (k := 1) (by simp [HashSet.Raw.mem_iff_contains, HashSet.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains])
  simp only [SDiff.sdiff, HashSet.Raw.diff, HashMap.Raw.diff, DHashMap.Raw.diff, Nat.lt_irrefl, List.size_toArray, List.length_nil, dite_false] at this
  simp [HashSet.Raw.get!_insert HashSet.Raw.WF.empty] at this

-- `Std.DHashMap.Internal.Raw₀.size_filter_key_eq_size_iff`: NB (== always false): one entry, size field 1; nothing is a member, so the right side holds, but filtering by false gives size 0 ≠ 1
theorem s78 : ¬ drop0% Std.DHashMap.Internal.Raw₀.size_filter_key_eq_size_iff 5 :=
  fun h => by
  have := (h (m := ⟨⟨1, #[b1 (NB.mk 0) (0 : Nat)]⟩, by decide⟩) (f := fun _ => false) (wf_vac NB.broken _ (by decide))).mpr
    (fun k hk => by revert hk; hm_eval)
  revert this; hm_eval

-- `Std.DHashMap.Raw.size_filter_key_eq_size_iff`: NB (== always false): one entry, size field 1; nothing is a member, so the right side holds, but filtering by false gives size 0 ≠ 1
theorem s79 : ¬ drop0% Std.DHashMap.Raw.size_filter_key_eq_size_iff 5 :=
  fun h => by
  have := (h (m := ⟨1, #[b1 (NB.mk 0) (0 : Nat)]⟩) (f := fun _ => false) (wf_vac NB.broken _ (by decide))).mpr
    (fun k hk => by revert hk; hm_eval_raw)
  revert this; hm_eval2

-- `Std.DHashMap.size_filter_key_eq_size_iff`: NB (== always false): one entry, size field 1; nothing is a member, so the right side holds, but filtering by false gives size 0 ≠ 1
theorem s80 : ¬ drop0% Std.DHashMap.size_filter_key_eq_size_iff 5 :=
  fun h => by
  have := (h (m := ⟨⟨1, #[b1 (NB.mk 0) (0 : Nat)]⟩, wf_vac NB.broken _ (by decide)⟩) (f := fun _ => false)).mpr
    (fun k hk => by revert hk; hm_eval)
  revert this; simp only [DHashMap.filter, DHashMap.size]; hm_eval

-- `Std.DHashMap.Internal.Raw₀.size_filter_key_eq_size_iff`: AB (== always true, hash n): key 0 with size field 0; filtering by false keeps size 0, but 0 is a member and f 0 = false
theorem s81 : ¬ drop0% Std.DHashMap.Internal.Raw₀.size_filter_key_eq_size_iff 6 :=
  fun h => by
  have := (h (m := ⟨⟨0, #[b1 (AB.mk 0) (0 : Nat)]⟩, by decide⟩) (f := fun _ => false) (wf_vac AB.broken _ (by decide))).mp
    (by hm_eval)
  have := this ⟨0⟩ (by hm_eval)
  simp at this

-- `Std.DHashMap.Raw.size_filter_key_eq_size_iff`: AB (== always true, hash n): key 0 with size field 0; filtering by false keeps size 0, but 0 is a member and f 0 = false
theorem s82 : ¬ drop0% Std.DHashMap.Raw.size_filter_key_eq_size_iff 6 :=
  fun h => by
  have := (h (m := ⟨0, #[b1 (AB.mk 0) (0 : Nat)]⟩) (f := fun _ => false) (wf_vac AB.broken _ (by decide))).mp
    (by hm_eval2)
  have := this ⟨0⟩ (by hm_eval_raw)
  simp at this

-- `Std.DHashMap.size_filter_key_eq_size_iff`: AB (== always true, hash n): key 0 with size field 0; filtering by false keeps size 0, but 0 is a member and f 0 = false
theorem s83 : ¬ drop0% Std.DHashMap.size_filter_key_eq_size_iff 6 :=
  fun h => by
  have := (h (m := ⟨⟨0, #[b1 (AB.mk 0) (0 : Nat)]⟩, wf_vac AB.broken _ (by decide)⟩) (f := fun _ => false)).mp
    (by simp only [DHashMap.filter, DHashMap.size]; hm_eval)
  have := this ⟨0⟩ (by hm_eval)
  simp at this

-- `Std.DHashMap.Internal.Raw₀.size_filter_key_eq_size_iff`: lawful Nat: 16 empty buckets with size field 1 (not WF); no members, but filtering recomputes size 0 ≠ 1
theorem s84 : ¬ drop0% Std.DHashMap.Internal.Raw₀.size_filter_key_eq_size_iff 8 :=
  fun h => by
  have := (h (m := (r0Bad : Raw₀ Nat (fun _ => Nat))) (f := fun _ => false)).mpr
    (fun k hk => by simp [raw0_nil16_contains] at hk)
  revert this; hm_eval

-- `Std.DHashMap.Raw.size_filter_key_eq_size_iff`: lawful Nat: 16 empty buckets with size field 1 (not WF); no members, but filtering recomputes size 0 ≠ 1
theorem s85 : ¬ drop0% Std.DHashMap.Raw.size_filter_key_eq_size_iff 8 :=
  fun h => by
  have := (h (m := (⟨1, nil16⟩ : DHashMap.Raw Nat (fun _ => Nat))) (f := fun _ => false)).mpr
    (fun k hk => by simp [DHashMap.Raw.mem_iff_contains, dr_nil16_contains] at hk)
  revert this; hm_eval2

-- `Std.DHashMap.Const.isEmpty_of_isEmpty_insertManyIfNewUnit`: removable: insertIfNew never lowers the size field (expandIfNecessary keeps it), so an empty result means size 0 before; a raw map without buckets is returned unchanged (EquivBEq α unused)
theorem s86 : drop% Std.DHashMap.Const.isEmpty_of_isEmpty_insertManyIfNewUnit 6 :=
  by intros; rename_i hh; exact dm_imnu _ _ hh

-- `Std.DHashMap.Internal.Raw₀.Const.isEmpty_of_isEmpty_insertManyIfNewUnit`: removable: insertIfNew never lowers the size field (expandIfNecessary keeps it), so an empty result means size 0 before; a raw map without buckets is returned unchanged (EquivBEq α unused)
theorem s87 : drop% Std.DHashMap.Internal.Raw₀.Const.isEmpty_of_isEmpty_insertManyIfNewUnit 6 :=
  by intros; rename_i hh; exact raw0_imnu_isEmpty _ _ hh

-- `Std.DHashMap.Raw.Const.isEmpty_of_isEmpty_insertManyIfNewUnit`: removable: insertIfNew never lowers the size field (expandIfNecessary keeps it), so an empty result means size 0 before; a raw map without buckets is returned unchanged (EquivBEq α unused)
theorem s88 : drop% Std.DHashMap.Raw.Const.isEmpty_of_isEmpty_insertManyIfNewUnit 6 :=
  by intros; rename_i hh; exact dr_imnu _ _ hh

-- `Std.HashMap.Raw.isEmpty_of_isEmpty_insertManyIfNewUnit`: removable: insertIfNew never lowers the size field (expandIfNecessary keeps it), so an empty result means size 0 before; a raw map without buckets is returned unchanged (EquivBEq α unused)
theorem s89 : drop% Std.HashMap.Raw.isEmpty_of_isEmpty_insertManyIfNewUnit 6 :=
  by intros; rename_i hh; exact dr_imnu _ _ hh

-- `Std.HashMap.isEmpty_of_isEmpty_insertManyIfNewUnit`: removable: insertIfNew never lowers the size field (expandIfNecessary keeps it), so an empty result means size 0 before; a raw map without buckets is returned unchanged (EquivBEq α unused)
theorem s90 : drop% Std.HashMap.isEmpty_of_isEmpty_insertManyIfNewUnit 6 :=
  by intros; rename_i hh; exact dm_imnu _ _ hh

-- `Std.DHashMap.Const.isEmpty_of_isEmpty_insertManyIfNewUnit`: removable: insertIfNew never lowers the size field (expandIfNecessary keeps it), so an empty result means size 0 before; a raw map without buckets is returned unchanged (LawfulHashable α unused)
theorem s91 : drop% Std.DHashMap.Const.isEmpty_of_isEmpty_insertManyIfNewUnit 7 :=
  by intros; rename_i hh; exact dm_imnu _ _ hh

-- `Std.DHashMap.Internal.Raw₀.Const.isEmpty_of_isEmpty_insertManyIfNewUnit`: removable: insertIfNew never lowers the size field (expandIfNecessary keeps it), so an empty result means size 0 before; a raw map without buckets is returned unchanged (LawfulHashable α unused)
theorem s92 : drop% Std.DHashMap.Internal.Raw₀.Const.isEmpty_of_isEmpty_insertManyIfNewUnit 7 :=
  by intros; rename_i hh; exact raw0_imnu_isEmpty _ _ hh

-- `Std.HashMap.Raw.isEmpty_of_isEmpty_insertManyIfNewUnit`: removable: insertIfNew never lowers the size field (expandIfNecessary keeps it), so an empty result means size 0 before; a raw map without buckets is returned unchanged (LawfulHashable α unused)
theorem s93 : drop% Std.HashMap.Raw.isEmpty_of_isEmpty_insertManyIfNewUnit 7 :=
  by intros; rename_i hh; exact dr_imnu _ _ hh

-- `Std.HashMap.isEmpty_of_isEmpty_insertManyIfNewUnit`: removable: insertIfNew never lowers the size field (expandIfNecessary keeps it), so an empty result means size 0 before; a raw map without buckets is returned unchanged (LawfulHashable α unused)
theorem s94 : drop% Std.HashMap.isEmpty_of_isEmpty_insertManyIfNewUnit 7 :=
  by intros; rename_i hh; exact dm_imnu _ _ hh

-- `Std.DHashMap.Internal.Raw₀.Const.isEmpty_of_isEmpty_insertManyIfNewUnit`: removable: insertIfNew never lowers the size field (expandIfNecessary keeps it), so an empty result means size 0 before; a raw map without buckets is returned unchanged (m.val.WF unused)
theorem s95 : drop% Std.DHashMap.Internal.Raw₀.Const.isEmpty_of_isEmpty_insertManyIfNewUnit 8 :=
  by intros; rename_i hh; exact raw0_imnu_isEmpty _ _ hh

-- `Std.DHashMap.Raw.Const.isEmpty_of_isEmpty_insertManyIfNewUnit`: removable: insertIfNew never lowers the size field (expandIfNecessary keeps it), so an empty result means size 0 before; a raw map without buckets is returned unchanged (m.WF unused)
theorem s96 : drop% Std.DHashMap.Raw.Const.isEmpty_of_isEmpty_insertManyIfNewUnit 8 :=
  by intros; rename_i hh; exact dr_imnu _ _ hh

-- `Std.HashMap.Raw.isEmpty_of_isEmpty_insertManyIfNewUnit`: removable: insertIfNew never lowers the size field (expandIfNecessary keeps it), so an empty result means size 0 before; a raw map without buckets is returned unchanged (m.WF unused)
theorem s97 : drop% Std.HashMap.Raw.isEmpty_of_isEmpty_insertManyIfNewUnit 8 :=
  by intros; rename_i hh; exact dr_imnu _ _ hh

-- `Std.DHashMap.Const.size_alter_eq_add_one`: removable: with contains k = false the bucket lookup gives none, so alter takes the insert branch with size + 1 (expandIfNecessary keeps the size); no laws or WF needed (EquivBEq α unused)
theorem s98 : drop% Std.DHashMap.Const.size_alter_eq_add_one 5 :=
  by intros; apply dm_calter_size <;> assumption

-- `Std.DHashMap.Internal.Raw₀.Const.size_alter_eq_add_one`: removable: with contains k = false the bucket lookup gives none, so alter takes the insert branch with size + 1 (expandIfNecessary keeps the size); no laws or WF needed (EquivBEq α unused)
theorem s99 : drop% Std.DHashMap.Internal.Raw₀.Const.size_alter_eq_add_one 4 :=
  by intros; apply raw0_calter_size <;> assumption

-- `Std.HashMap.size_alter_eq_add_one`: removable: with contains k = false the bucket lookup gives none, so alter takes the insert branch with size + 1 (expandIfNecessary keeps the size); no laws or WF needed (EquivBEq α unused)
theorem s100 : drop% Std.HashMap.size_alter_eq_add_one 5 :=
  by intros; apply dm_calter_size <;> assumption

-- `Std.DHashMap.Const.size_alter_eq_add_one`: removable: with contains k = false the bucket lookup gives none, so alter takes the insert branch with size + 1 (expandIfNecessary keeps the size); no laws or WF needed (LawfulHashable α unused)
theorem s101 : drop% Std.DHashMap.Const.size_alter_eq_add_one 6 :=
  by intros; apply dm_calter_size <;> assumption

-- `Std.DHashMap.Internal.Raw₀.Const.size_alter_eq_add_one`: removable: with contains k = false the bucket lookup gives none, so alter takes the insert branch with size + 1 (expandIfNecessary keeps the size); no laws or WF needed (LawfulHashable α unused)
theorem s102 : drop% Std.DHashMap.Internal.Raw₀.Const.size_alter_eq_add_one 5 :=
  by intros; apply raw0_calter_size <;> assumption

-- `Std.HashMap.size_alter_eq_add_one`: removable: with contains k = false the bucket lookup gives none, so alter takes the insert branch with size + 1 (expandIfNecessary keeps the size); no laws or WF needed (LawfulHashable α unused)
theorem s103 : drop% Std.HashMap.size_alter_eq_add_one 6 :=
  by intros; apply dm_calter_size <;> assumption

-- `Std.DHashMap.Internal.Raw₀.Const.size_alter_eq_add_one`: removable: with contains k = false the bucket lookup gives none, so alter takes the insert branch with size + 1 (expandIfNecessary keeps the size); no laws or WF needed (m.val.WF unused)
theorem s104 : drop% Std.DHashMap.Internal.Raw₀.Const.size_alter_eq_add_one 7 :=
  by intros; apply raw0_calter_size <;> assumption

-- `Std.DHashMap.Internal.Raw₀.size_alter_eq_add_one`: removable: with contains k = false the bucket lookup gives none, so alter takes the insert branch with size + 1 (expandIfNecessary keeps the size); no laws or WF needed (m.val.WF unused)
theorem s105 : drop% Std.DHashMap.Internal.Raw₀.size_alter_eq_add_one 6 :=
  by intros; apply raw0_alter_size <;> assumption

-- `Std.DHashMap.Const.get!_diff_of_not_mem_left`: removable: diff only filters or erases inside the buckets of m1 (raw: returns m1 when m2 has no buckets), so a key absent from its bucket in m1 stays absent and get! falls back to default (EquivBEq α unused)
theorem s106 : drop% Std.DHashMap.Const.get!_diff_of_not_mem_left 6 :=
  by intros; apply dm_cget!_diff <;> assumption

-- `Std.DHashMap.Raw.Const.get!_diff_of_not_mem_left`: removable: diff only filters or erases inside the buckets of m1 (raw: returns m1 when m2 has no buckets), so a key absent from its bucket in m1 stays absent and get! falls back to default (EquivBEq α unused)
theorem s107 : drop% Std.DHashMap.Raw.Const.get!_diff_of_not_mem_left 6 :=
  by intros; apply drc_get!_diff <;> assumption

-- `Std.HashSet.Raw.get!_diff_of_not_mem_left`: removable: diff only filters or erases inside the buckets of m1 (raw: returns m1 when m2 has no buckets), so a key absent from its bucket in m1 stays absent and get! falls back to default (EquivBEq α unused)
theorem s108 : drop% Std.HashSet.Raw.get!_diff_of_not_mem_left 6 :=
  by intros; apply hsr_get!_diff <;> assumption

-- `Std.HashSet.get!_diff_of_not_mem_left`: removable: diff only filters or erases inside the buckets of m1 (raw: returns m1 when m2 has no buckets), so a key absent from its bucket in m1 stays absent and get! falls back to default (EquivBEq α unused)
theorem s109 : drop% Std.HashSet.get!_diff_of_not_mem_left 5 :=
  by intros; apply hs_get!_diff <;> assumption

-- `Std.DHashMap.Const.get!_diff_of_not_mem_left`: removable: diff only filters or erases inside the buckets of m1 (raw: returns m1 when m2 has no buckets), so a key absent from its bucket in m1 stays absent and get! falls back to default (LawfulHashable α unused)
theorem s110 : drop% Std.DHashMap.Const.get!_diff_of_not_mem_left 7 :=
  by intros; apply dm_cget!_diff <;> assumption

-- `Std.DHashMap.Raw.Const.get!_diff_of_not_mem_left`: removable: diff only filters or erases inside the buckets of m1 (raw: returns m1 when m2 has no buckets), so a key absent from its bucket in m1 stays absent and get! falls back to default (LawfulHashable α unused)
theorem s111 : drop% Std.DHashMap.Raw.Const.get!_diff_of_not_mem_left 7 :=
  by intros; apply drc_get!_diff <;> assumption

-- `Std.HashSet.Raw.get!_diff_of_not_mem_left`: removable: diff only filters or erases inside the buckets of m1 (raw: returns m1 when m2 has no buckets), so a key absent from its bucket in m1 stays absent and get! falls back to default (LawfulHashable α unused)
theorem s112 : drop% Std.HashSet.Raw.get!_diff_of_not_mem_left 7 :=
  by intros; apply hsr_get!_diff <;> assumption

-- `Std.HashSet.get!_diff_of_not_mem_left`: removable: diff only filters or erases inside the buckets of m1 (raw: returns m1 when m2 has no buckets), so a key absent from its bucket in m1 stays absent and get! falls back to default (LawfulHashable α unused)
theorem s113 : drop% Std.HashSet.get!_diff_of_not_mem_left 6 :=
  by intros; apply hs_get!_diff <;> assumption

-- `Std.DHashMap.Raw.Const.get!_diff_of_not_mem_left`: removable: diff only filters or erases inside the buckets of m1 (raw: returns m1 when m2 has no buckets), so a key absent from its bucket in m1 stays absent and get! falls back to default (m₂.WF unused)
theorem s114 : drop% Std.DHashMap.Raw.Const.get!_diff_of_not_mem_left 10 :=
  by intros; apply drc_get!_diff <;> assumption

-- `Std.DHashMap.Raw.get!_diff_of_not_mem_left`: removable: diff only filters or erases inside the buckets of m1 (raw: returns m1 when m2 has no buckets), so a key absent from its bucket in m1 stays absent and get! falls back to default (m₂.WF unused)
theorem s115 : drop% Std.DHashMap.Raw.get!_diff_of_not_mem_left 8 :=
  by intros; apply dr_get!_diff <;> assumption

-- `Std.HashSet.Raw.get!_diff_of_not_mem_left`: removable: diff only filters or erases inside the buckets of m1 (raw: returns m1 when m2 has no buckets), so a key absent from its bucket in m1 stays absent and get! falls back to default (m₂.WF unused)
theorem s116 : drop% Std.HashSet.Raw.get!_diff_of_not_mem_left 9 :=
  by intros; apply hsr_get!_diff <;> assumption

-- `Std.DHashMap.Internal.Raw₀.contains_of_getKey?_eq_some`: removable: with EquivBEq and LawfulHashable, a key a' found in the bucket of a satisfies a' == a, so it hashes to the same bucket and is found there by reflexivity; no WF needed
theorem s117 : drop% Std.DHashMap.Internal.Raw₀.contains_of_getKey?_eq_some 9 :=
  by
  intros; apply raw0_contains_of_getKey?; assumption

-- `Std.DHashMap.Internal.Raw₀.contains_of_getKey?_eq_some`: NE (a == b iff a ≠ b, hash 0): bucket [1]; getKey? 0 = some 1, but contains 1 is false (1 == 1 is false)
theorem s118 : ¬ drop0% Std.DHashMap.Internal.Raw₀.contains_of_getKey?_eq_some 5 :=
  fun h => by
  have := h (m := ⟨⟨0, #[b1 (NE.mk 1) (0 : Nat)]⟩, by decide⟩) (a := ⟨0⟩) (a' := ⟨1⟩) (wf_vac NE.broken _ (by decide)) (by hm_eval)
  revert this; hm_eval

-- `Std.DHashMap.Internal.Raw₀.contains_of_getKey?_eq_some`: AB (== always true, hash n): key 1 misplaced in bucket 0 of 2; getKey? 0 = some 1, contains 1 looks in bucket 1 and fails
theorem s119 : ¬ drop0% Std.DHashMap.Internal.Raw₀.contains_of_getKey?_eq_some 6 :=
  fun h => by
  have := h (m := ⟨⟨0, #[b1 (AB.mk 1) (0 : Nat), .nil]⟩, by decide⟩) (a := ⟨0⟩) (a' := ⟨1⟩) (wf_vac AB.broken _ (by decide)) (by hm_eval)
  revert this; hm_eval

-- `Std.DHashMap.Internal.Raw₀.getKeyDₘ_eq_getKeyD`: lawful Nat: key 0 misplaced in bucket 1 of 2 (not WFImp); bucket lookup gives fallback 1, the list model gives 0
theorem s120 : ¬ drop0% Std.DHashMap.Internal.Raw₀.getKeyDₘ_eq_getKeyD 7 :=
  fun h => by
  have := h (m := ⟨⟨1, #[.nil, .cons 0 0 .nil]⟩, by decide⟩) (β := fun _ => Nat) (a := 0) (fallback := 1)
  rw [show ∀ (m : Raw₀ Nat (fun _ => Nat)) a fb, m.getKeyDₘ a fb = (m.getKey? a).getD fb from fun _ _ _ => rfl] at this
  revert this; hm_eval
-- getKeyD_diff: h (12) lawful Nat m1 = m2 = {0}

-- `Std.DHashMap.Internal.Raw₀.getKeyD_diff_of_contains_eq_false_right`: lawful Nat: m1 = m2 = {0}, k = 0, fallback 1; the diff is empty so getKeyD gives 1, m1 gives 0
theorem s121 : ¬ drop0% Std.DHashMap.Internal.Raw₀.getKeyD_diff_of_contains_eq_false_right 12 :=
  fun h => by
  have e : (Raw₀.emptyWithCapacity : Raw₀ Nat (fun _ => Nat)).insert 0 0 = ⟨⟨1, f16 (.cons 0 0 .nil)⟩, by decide⟩ := by
    simp only [raw0_empty]; hm_eval
  have := h (m₁ := ⟨⟨1, f16 (.cons 0 0 .nil)⟩, by decide⟩) (m₂ := ⟨⟨1, f16 (.cons 0 0 .nil)⟩, by decide⟩)
    (e ▸ DHashMap.Raw.WF.insert₀ DHashMap.Raw.WF.emptyWithCapacity₀) (e ▸ DHashMap.Raw.WF.insert₀ DHashMap.Raw.WF.emptyWithCapacity₀) (k := 0) (fallback := 1)
  revert this; hm_eval2
-- 6 (EquivBEq): NS, m1 = {0} size 2, m2 = {1} size 1; diff erases 1, which removes 0

-- `Std.DHashMap.Internal.Raw₀.getKeyD_diff_of_contains_eq_false_right`: NS (a ≤ b): m1 = {0} with size field 2, m2 = {1}; m2 does not contain 0 (1 ≤ 0 fails), but erasing 1 from m1 removes 0 (0 ≤ 1), so getKeyD 0 gives the fallback
theorem s122 : ¬ drop0% Std.DHashMap.Internal.Raw₀.getKeyD_diff_of_contains_eq_false_right 6 :=
  fun h => by
  have := h (m₁ := ⟨⟨2, #[b1 (NS.mk 0) (5 : Nat)]⟩, by decide⟩) (m₂ := ⟨⟨1, #[b1 (NS.mk 1) (0 : Nat)]⟩, by decide⟩)
    (wf_vac NS.broken _ (by decide)) (wf_vac NS.broken _ (by decide)) (k := ⟨0⟩) (fallback := ⟨7⟩) (by hm_eval)
  revert this; hm_eval2
-- 7 (LawfulHashable): AB, m1 has key 1 misplaced in bucket 0 of 2, m2 = {1} in bucket 1, both size 1; filter drops 1

-- `Std.DHashMap.Internal.Raw₀.getKeyD_diff_of_contains_eq_false_right`: AB: m1 has key 1 misplaced in bucket 0 of 2, m2 = {1} in bucket 1, sizes 1; m2 does not contain 0 (bucket 0 empty), but the filter branch drops 1, so getKeyD 0 gives the fallback instead of 1
theorem s123 : ¬ drop0% Std.DHashMap.Internal.Raw₀.getKeyD_diff_of_contains_eq_false_right 7 :=
  fun h => by
  have := h (m₁ := ⟨⟨1, #[b1 (AB.mk 1) (5 : Nat), .nil]⟩, by decide⟩) (m₂ := ⟨⟨1, #[.nil, b1 (AB.mk 1) (0 : Nat)]⟩, by decide⟩)
    (wf_vac AB.broken _ (by decide)) (wf_vac AB.broken _ (by decide)) (k := ⟨0⟩) (fallback := ⟨7⟩) (by hm_eval)
  revert this; hm_eval2
-- 9 (m₂.WF): lawful Nat, m1 = {0} (WF, size 1), m2 has 0 misplaced in bucket 1 of 2 with size field 0; diff erases m2's entries, removing 0

-- `Std.DHashMap.Internal.Raw₀.getKeyD_diff_of_contains_eq_false_right`: lawful Nat: m1 = {0} (WF), m2 has 0 misplaced in bucket 1 of 2 with size field 0; m2.contains 0 is false, but the erase branch erases 0 from m1
theorem s124 : ¬ drop0% Std.DHashMap.Internal.Raw₀.getKeyD_diff_of_contains_eq_false_right 9 :=
  fun h => by
  have e : (Raw₀.emptyWithCapacity : Raw₀ Nat (fun _ => Nat)).insert 0 0 = ⟨⟨1, f16 (.cons 0 0 .nil)⟩, by decide⟩ := by
    simp only [raw0_empty]; hm_eval
  have := h (m₁ := ⟨⟨1, f16 (.cons 0 0 .nil)⟩, by decide⟩) (m₂ := ⟨⟨0, #[.nil, .cons 0 0 .nil]⟩, by decide⟩)
    (e ▸ DHashMap.Raw.WF.insert₀ DHashMap.Raw.WF.emptyWithCapacity₀) (k := 0) (fallback := 1) (by hm_eval)
  revert this; hm_eval2

-- `Std.DHashMap.Internal.Raw₀.getKeyDₘ_eq_getKeyD`: AB (== always true, hash n): key 1 alone in bucket 1 of 2 (WFImp holds); getKeyDₘ 0 looks in bucket 0 and gives the fallback, the list model finds 1
theorem s125 : ¬ drop0% Std.DHashMap.Internal.Raw₀.getKeyDₘ_eq_getKeyD 5 :=
  fun h => by
  have := h (m := ⟨⟨1, #[.nil, b1 (AB.mk 1) (0 : Nat)]⟩, by decide⟩) ab_wfimp (a := ⟨0⟩) (fallback := ⟨7⟩)
  rw [show ∀ (m : Raw₀ AB (fun _ => Nat)) a fb, m.getKeyDₘ a fb = (m.getKey? a).getD fb from fun _ _ _ => rfl] at this
  revert this; hm_eval

-- `Std.DHashMap.Internal.Raw₀.getKeyD_diff_of_contains_eq_false_right`: HB (a/2, EquivBEq and LawfulHashable hold): m1 has bucket [0, 1] (both equal to 0, not WF), m2 = empty; the filter branch reverses the bucket, so getKeyD 0 gives 1 instead of 0
theorem s126 : ¬ drop0% Std.DHashMap.Internal.Raw₀.getKeyD_diff_of_contains_eq_false_right 8 :=
  fun h => by
  have := h (β := fun _ => Nat) (m₁ := ⟨⟨0, #[.cons (HB.mk 0) (0 : Nat) (.cons (HB.mk 1) 0 .nil)]⟩, by decide⟩)
    (m₂ := (Raw₀.emptyWithCapacity : Raw₀ HB (fun _ => Nat))) DHashMap.Raw.WF.emptyWithCapacity₀ (k := ⟨0⟩) (fallback := ⟨7⟩) (by simp only [raw0_empty]; hm_eval)
  revert this; simp only [raw0_empty]; hm_eval2

-- `Std.DHashMap.Internal.Raw₀.getKeyDₘ_eq_getKeyD`: removable: with LawfulHashable and IsHashSelf (from WFImp) every entry whose key is == a lies in the bucket of a, and toListModel keeps bucket order, so the bucket lookup equals the list lookup; EquivBEq unused
theorem s127 : drop% Std.DHashMap.Internal.Raw₀.getKeyDₘ_eq_getKeyD 4 :=
  by intros; apply getKeyDm_noequiv; assumption

end Stem1V
