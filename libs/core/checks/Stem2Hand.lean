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

/-! # Stem2 hand verdicts (helpers from Probe3/Probe4 plus new ones) -/
open Std HashInstHand Std.DTreeMap.Internal

-- tree WF closer for ofList / insertMany literals
macro "twf" : tactic => `(tactic| ((repeat (first | apply Std.TreeSet.Raw.WF.mk | apply Std.TreeMap.Raw.WF.mk | apply Std.DTreeMap.Raw.WF.mk)); (first | exact @Std.DTreeMap.Internal.Impl.WF.insertMany _ _ (id _) _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact @Std.DTreeMap.Internal.Impl.WF.constInsertMany _ (id _) _ _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact @Std.DTreeMap.Internal.Impl.WF.constInsertManyIfNewUnit _ (id _) _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _))))

def cmpG (a b : Nat) : Ordering := if a = b then .eq else .gt
def cmpGt (_ _ : Nat) : Ordering := .gt
def cmpR (a b : Nat) : Ordering := if a % 3 = b % 3 then .eq else if b % 3 = (a+1) % 3 then .lt else .gt
def cmp01 (a b : Nat) : Ordering := if a = 0 ∧ b = 1 then .eq else compare a b


-- Stem2 helpers
-- bind-counting monad (not lawful: pure x >>= f counts one bind)
def CM (α : Type) : Type := Nat × α
instance : Monad CM where
  pure a := (0, a)
  bind x f := ((f x.2).1 + x.1 + 1, (f x.2).2)
-- lawful compare, but BEq always true
structure OB where n : Nat deriving DecidableEq
instance : Ord OB := ⟨fun a b => compare a.n b.n⟩
instance : BEq OB := ⟨fun _ _ => true⟩
instance : Std.TransOrd OB where
  eq_swap {a b} := Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering)) (a := a.n) (b := b.n)
  isLE_trans {a b c} h1 h2 := Std.TransCmp.isLE_trans (cmp := (compare : Nat → Nat → Ordering)) (a := a.n) (b := b.n) (c := c.n) h1 h2
instance : Std.LawfulEqOrd OB where
  compare_self {a} := Std.ReflCmp.compare_self (cmp := (compare : Nat → Nat → Ordering)) (a := a.n)
  eq_of_compare {a b} h := by cases a; cases b; simp only [compare] at h; simp [Nat.compare_eq_eq.mp h]
instance : BEq OT := ⟨fun a b => a.n == b.n⟩
instance : Std.LawfulBEqOrd OT where
  compare_eq_iff_beq {a b} := by cases a; cases b; simp [compare, cmpT, BEq.beq]
-- not reflexive: everything compares eq to 1, lt otherwise
def cmpZ (_ b : Nat) : Ordering := if b = 1 then .eq else .lt
instance : BEq OH := ⟨fun a b => a.n / 2 == b.n / 2⟩
instance : Std.LawfulBEqOrd OH where
  compare_eq_iff_beq {a b} := by
    show compare (a.n / 2) (b.n / 2) = .eq ↔ (a.n / 2 == b.n / 2) = true
    simp [Nat.compare_eq_eq]
theorem OB.notLawfulBEq : ¬ Std.LawfulBEqOrd OB := fun h => by
  have := (@Std.LawfulBEqCmp.compare_eq_iff_beq _ _ _ h ⟨0⟩ ⟨1⟩).2 rfl
  exact absurd this (by decide)
-- near-equality (oriented, not transitive)
def cmpN (a b : Nat) : Ordering := if a ≤ b + 1 ∧ b ≤ a + 1 then .eq else compare a b
structure ON where n : Nat deriving DecidableEq
instance : Ord ON := ⟨fun a b => cmpN a.n b.n⟩

section S2Rem
open Std.DTreeMap.Internal
universe u_s v_s w_s
variable {α : Type u_s} {β : α → Type v_s}
-- helper: the key returned by getKey compares equal to the query, on any tree
theorem s2h_gk_cmp (o : Ord α) : ∀ (t : Impl α β) (k : α) (h : t.contains k = true), compare k (t.getKey k h) = .eq
  | .leaf, k, h => by simp [Impl.contains] at h
  | .inner _ k' _ l r, k, h => by
    unfold Impl.getKey; split
    · exact s2h_gk_cmp o l k _
    · exact s2h_gk_cmp o r k _
    · assumption
-- helper
theorem s2h_gk_eq (o : Ord α) (t : Impl α β) (k : α) (h : t.contains k = true)
    (hl : ∀ a b : α, compare a b = .eq → a = b) : t.getKey k h = k := (hl _ _ (s2h_gk_cmp o t k h)).symm
-- helper: getKey! after modify, on any tree (lawful equality only)
theorem s2h_gkm (o : Ord α) [Std.LawfulEqOrd α] [Inhabited α] (k : α) (f : β k → β k) :
    ∀ t : Impl α β, (Impl.modify k f t).getKey! k = if t.contains k then k else default
  | .leaf => by simp [Impl.modify, Impl.getKey!, Impl.contains, panicWithPosWithDecl, panicWithPos, panic, panicCore]
  | .inner sz k' v' l r => by
    simp only [Impl.modify, Impl.contains]
    split
    · rename_i h; simp only [Impl.getKey!, h]; exact s2h_gkm o k f l
    · rename_i h; simp only [Impl.getKey!, h]; exact s2h_gkm o k f r
    · rename_i h; simp [Impl.getKey!, Std.ReflCmp.compare_self, h]
-- helper
theorem s2h_gkm1 (o : Ord α) [Std.LawfulEqOrd α] [Inhabited α] (k : α) (f : β k → β k) (t : Impl α β)
    (h : t.contains k = true) : (Impl.modify k f t).getKey! k = k := by rw [s2h_gkm, h]; rfl
-- helper
theorem s2h_gkm0 (o : Ord α) [Std.LawfulEqOrd α] [Inhabited α] (k : α) (f : β k → β k) (t : Impl α β)
    (h : ¬ t.contains k = true) : (Impl.modify k f t).getKey! k = default := by rw [s2h_gkm]; simp [h]
-- helper
theorem s2h_mk_inner (sz : Nat) (k : α) (v : β k) (l r : Impl α β) :
    (Impl.inner sz k v l r).minKey? = l.minKey?.or (some k) := by
  cases l with
  | leaf => simp [Impl.minKey?]
  | inner sz' k' v' l' r' =>
    have : ∀ (t : Impl α β), t ≠ .leaf → t.minKey?.isSome := by
      intro t; induction t with
      | leaf => simp
      | inner _ _ _ l _ ih _ => cases l with
        | leaf => simp [Impl.minKey?]
        | inner => simp only [Impl.minKey?]; exact fun _ => ih (by simp)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (this (.inner sz' k' v' l' r') (by simp))
    simp only [Impl.minKey?] at hx ⊢; simp [hx]
-- helper: Const.modify keeps minKey? under lawful equality, on any tree
theorem s2h_mkm {β : Type v_s} (o : Ord α) [Std.LawfulEqOrd α] (k : α) (f : β → β) :
    ∀ t : Impl α (fun _ => β), (Impl.Const.modify k f t).minKey? = t.minKey?
  | .leaf => rfl
  | .inner sz k' v' l r => by
    simp only [Impl.Const.modify]
    split
    · rw [s2h_mk_inner, s2h_mk_inner, s2h_mkm o k f l]
    · rw [s2h_mk_inner, s2h_mk_inner]
    · rename_i h; have := Std.compare_eq_iff_eq.mp h; subst this; rw [s2h_mk_inner, s2h_mk_inner]
-- helper: structural minKey?
def s2h_mkS : Impl α β → Option α
  | .leaf => none
  | .inner _ k _ l _ => (s2h_mkS l).or (some k)
-- helper
theorem s2h_mkS_eq : ∀ t : Impl α β, t.minKey? = s2h_mkS t
  | .leaf => by simp [Impl.minKey?, s2h_mkS]
  | .inner sz k v l r => by rw [s2h_mk_inner, s2h_mkS_eq l]; rfl
-- helper: getKey! after Const.modify, on any tree with compare k k = .eq
theorem s2h_gkmc {β : Type v_s} (o : Ord α) [Inhabited α] (k : α) (f : β → β) (hr : compare k k = .eq) :
    ∀ t : Impl α (fun _ => β), (Impl.Const.modify k f t).getKey! k = if t.contains k then k else default
  | .leaf => by simp [Impl.Const.modify, Impl.getKey!, Impl.contains, panicWithPosWithDecl, panic, panicCore]
  | .inner sz k' v' l r => by
    simp only [Impl.Const.modify, Impl.contains]
    split
    · rename_i h; simp only [Impl.getKey!, h]; exact s2h_gkmc o k f hr l
    · rename_i h; simp only [Impl.getKey!, h]; exact s2h_gkmc o k f hr r
    · rename_i h; simp [Impl.getKey!, hr, h]
-- helper
theorem s2h_gkmc1 {β : Type v_s} (o : Ord α) [Inhabited α] (k : α) (f : β → β) (hr : compare k k = .eq)
    (t : Impl α (fun _ => β)) (h : t.contains k = true) : (Impl.Const.modify k f t).getKey! k = k := by
  rw [s2h_gkmc o k f hr, h]; rfl
-- helper
theorem s2h_gkmc0 {β : Type v_s} (o : Ord α) [Inhabited α] (k : α) (f : β → β) (hr : compare k k = .eq)
    (t : Impl α (fun _ => β)) (h : ¬ t.contains k = true) : (Impl.Const.modify k f t).getKey! k = default := by
  rw [s2h_gkmc o k f hr]; simp [h]
-- helper
theorem s2h_mk2 (sz sz' : Nat) (k k' : α) (v : β k) (v' : β k') (r r' : Impl α β) (h) :
    (Impl.inner sz k v (Impl.inner sz' k' v' .leaf r') r).minKey h = k' := by
  rw [Impl.minKey.eq_def]; simp only []; rw [Impl.minKey.eq_def]
-- helper: filterMap! on any tree is balanced and filters the entry list
theorem s2h_fm {γ : α → Type w_s} (o : Ord α) (f : (a : α) → β a → Option (γ a)) :
    ∀ t : Impl α β, (t.filterMap! f).Balanced ∧
      (t.filterMap! f).toListModel = t.toListModel.filterMap fun x => (f x.1 x.2).map (⟨x.1, ·⟩)
  | .leaf => ⟨.leaf, rfl⟩
  | .inner sz k v l r => by
    obtain ⟨hl, el⟩ := s2h_fm o f l
    obtain ⟨hr, er⟩ := s2h_fm o f r
    simp only [Impl.filterMap!, Impl.toListModel_inner, List.filterMap_append]
    cases h : f k v with
    | none =>
      simp only []
      rw [← Impl.link2_eq_link2! hl hr]
      exact ⟨(Impl.link2 _ _ hl hr).balanced_impl, by rw [Impl.toListModel_link2, el, er]; simp [h]⟩
    | some v' =>
      simp only []
      rw [← Impl.link_eq_link! hl hr]
      exact ⟨(Impl.link _ _ _ _ hl hr).balanced_impl, by rw [Impl.toListModel_link, el, er]; simp [h]⟩
-- helper
theorem s2h_fm_perm {γ : α → Type w_s} (o : Ord α) (f : (a : α) → β a → Option (γ a)) (t₁ t₂ : Impl α β)
    (hp : t₁.toListModel.Perm t₂.toListModel) : (t₁.filterMap! f).toListModel.Perm (t₂.filterMap! f).toListModel := by
  rw [(s2h_fm o f t₁).2, (s2h_fm o f t₂).2]; exact hp.filterMap _
-- helper: a balanced tree is nonempty iff its size is positive
theorem s2h_pos (t : Impl α β) (hb : t.Balanced) : t.isEmpty = false ↔ 0 < t.size := by
  cases t with
  | leaf => simp [Impl.isEmpty, Impl.size]
  | inner sz k v l r =>
    rw [Impl.balanced_inner_iff] at hb; obtain ⟨-, -, -, h⟩ := hb
    simp [Impl.isEmpty, Impl.size]; omega
-- helper
theorem s2h_leaf (t : Impl α β) (hb : t.Balanced) (h : t.size = 0) : t = .leaf := by
  cases t with
  | leaf => rfl
  | inner sz k v l r =>
    rw [Impl.balanced_inner_iff] at hb; obtain ⟨-, -, -, h'⟩ := hb
    simp [Impl.size] at h; omega
-- helper: insertMany! into a balanced tree stays balanced and does not shrink (any Ord)
theorem s2h_im (o : Ord α) (t : Impl α β) (hb : t.Balanced) {ρ : Type w_s} [ForIn Id ρ ((a : α) × β a)] (l : ρ) :
    (t.insertMany! l).1.Balanced ∧ t.size ≤ (t.insertMany! l).1.size :=
  (t.insertMany! l).2 (P := fun x => x.Balanced ∧ t.size ≤ x.size) ⟨hb, Nat.le_refl _⟩ (fun t'' a b ⟨h1, h2⟩ => by
    rw [← Impl.insert_eq_insert! (h := h1)]
    exact ⟨(Impl.insert a b t'' h1).balanced_impl, Nat.le_trans h2 (Impl.insert a b t'' h1).lb_le_size_impl⟩)
-- helper
theorem s2h_imn (o : Ord α) (t : Impl α β) (hb : t.Balanced) {ρ : Type w_s} [ForIn Id ρ ((a : α) × β a)] (l : ρ) :
    (t.insertManyIfNew! l).1.Balanced ∧ t.size ≤ (t.insertManyIfNew! l).1.size :=
  (t.insertManyIfNew! l).2 (P := fun x => x.Balanced ∧ t.size ≤ x.size) ⟨hb, Nat.le_refl _⟩ (fun t'' a b ⟨h1, h2⟩ => by
    rw [← Impl.insertIfNew_eq_insertIfNew! (h := h1)]
    exact ⟨(Impl.insertIfNew a b t'' h1).balanced_impl, Nat.le_trans h2 (Impl.insertIfNew a b t'' h1).lb_le_size_impl⟩)
end S2Rem

-- helper: the unordered set literal {1, hidden 0} answers contains like {1}
theorem s2h_cont (k : Nat) : Impl.contains k (.inner 2 1 () .leaf (.inner 1 0 () .leaf .leaf) : Impl Nat (fun _ => Unit))
    = Impl.contains k (Std.TreeSet.Raw.ofList [1] compare).inner.inner.inner := by
  show _ = Impl.contains k (.inner 1 1 () .leaf .leaf)
  simp only [Impl.contains]
  cases h : compare k 1 <;> simp only []
  have : compare k 0 = .gt := by rw [Nat.compare_eq_gt] at h ⊢; omega
  simp [this]

-- helper: under cmpT, {1,2} and {0,1,2} answer contains alike
theorem s2h_cont2 (k : Nat) : (Std.TreeSet.Raw.ofList [1, 2] cmpT).contains k = (Std.TreeSet.Raw.ofList [0, 1, 2] cmpT).contains k := by
  show @Impl.contains _ _ ⟨cmpT⟩ k (.inner 2 1 () (.inner 1 2 () .leaf .leaf) .leaf) =
    @Impl.contains _ _ ⟨cmpT⟩ k (.inner 3 1 () (.inner 1 2 () .leaf .leaf) (.inner 1 0 () .leaf .leaf))
  by_cases h1 : k = 1 <;> by_cases h2 : k = 2 <;> simp [Impl.contains, compare, cmpT, h1, h2]

-- `Std.DTreeMap.Internal.Impl.foldrM_eq_foldrM_toArray` (binder 6)
theorem s2_0 : ¬ (drop0% Std.DTreeMap.Internal.Impl.foldrM_eq_foldrM_toArray 6) := fun h => by
  have := congrArg Prod.fst (h (α := Nat) (β := fun _ => Nat) (t := .inner 1 0 0 .leaf .leaf) (f := fun _ _ _ => ((0 : Nat), (0 : Nat))) (m := CM) (δ := Nat) (init := 0))
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.Const.foldrM_eq_foldrM_toArray` (binder 7)
theorem s2_1 : ¬ (drop0% Std.DTreeMap.Raw.Const.foldrM_eq_foldrM_toArray 7) := fun h => by
  have := congrArg Prod.fst (h (α := Nat) (β := Nat) (cmp := compare) (t := ⟨.inner 1 0 0 .leaf .leaf⟩) (f := fun _ _ _ => ((0 : Nat), (0 : Nat))) (m := CM) (δ := Nat) (init := 0))
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.foldrM_eq_foldrM_toArray` (binder 7)
theorem s2_2 : ¬ (drop0% Std.DTreeMap.Raw.foldrM_eq_foldrM_toArray 7) := fun h => by
  have := congrArg Prod.fst (h (α := Nat) (β := fun _ => Nat) (cmp := compare) (t := ⟨.inner 1 0 0 .leaf .leaf⟩) (f := fun _ _ _ => ((0 : Nat), (0 : Nat))) (m := CM) (δ := Nat) (init := 0))
  revert this; decide +kernel

-- `Std.DTreeMap.foldrM_eq_foldrM_toArray` (binder 7)
theorem s2_3 : ¬ (drop0% Std.DTreeMap.foldrM_eq_foldrM_toArray 7) := fun h => by
  have := congrArg Prod.fst (h (α := Nat) (β := fun _ => Nat) (cmp := compare) (t := .ofList [⟨0, 0⟩]) (f := fun _ _ _ => ((0 : Nat), (0 : Nat))) (m := CM) (δ := Nat) (init := 0))
  revert this; decide +kernel

-- `Std.TreeMap.Raw.foldrM_eq_foldrM_toArray` (binder 7)
theorem s2_4 : ¬ (drop0% Std.TreeMap.Raw.foldrM_eq_foldrM_toArray 7) := fun h => by
  have := congrArg Prod.fst (h (α := Nat) (β := Nat) (cmp := compare) (t := ⟨⟨.inner 1 0 0 .leaf .leaf⟩⟩) (f := fun _ _ _ => ((0 : Nat), (0 : Nat))) (m := CM) (δ := Nat) (init := 0))
  revert this; decide +kernel

-- `Std.TreeSet.Raw.foldrM_eq_foldrM_toArray` (binder 6)
theorem s2_5 : ¬ (drop0% Std.TreeSet.Raw.foldrM_eq_foldrM_toArray 6) := fun h => by
  have := congrArg Prod.fst (h (α := Nat) (cmp := compare) (t := ⟨⟨⟨.inner 1 0 () .leaf .leaf⟩⟩⟩) (f := fun _ _ => ((0 : Nat), (0 : Nat))) (m := CM) (δ := Nat) (init := 0))
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.Const.getKey?_ofList_of_mem` (binder 9)
theorem s2_6 : ¬ (drop0% Std.DTreeMap.Raw.Const.getKey?_ofList_of_mem 9) := fun h => by
  have := h (β := Nat) (cmp := compare) (l := []) (k := 0) (k' := 0) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKey?_ofList_of_mem` (binder 9)
theorem s2_7 : ¬ (drop0% Std.TreeMap.Raw.getKey?_ofList_of_mem 9) := fun h => by
  have := h (β := Nat) (cmp := compare) (l := []) (k := 0) (k' := 0) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.getKey?_ofList_of_mem` (binder 9)
theorem s2_8 : ¬ (drop0% Std.DTreeMap.Raw.getKey?_ofList_of_mem 9) := fun h => by
  have := h (β := fun _ => Nat) (cmp := compare) (l := []) (k := 0) (k' := 0) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.getKey?_ofList_of_mem` (binder 8)
theorem s2_9 : ¬ (drop0% Std.DTreeMap.Const.getKey?_ofList_of_mem 8) := fun h => by
  have := h (β := Nat) (cmp := cmpH) (l := [(0, 0), (1, 1)]) (k := 0) (k' := 0) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getKey?_ofList_of_mem` (binder 8)
theorem s2_10 : ¬ (drop0% Std.DTreeMap.Raw.Const.getKey?_ofList_of_mem 8) := fun h => by
  have := h (β := Nat) (cmp := cmpH) (l := [(0, 0), (1, 1)]) (k := 0) (k' := 0) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.getKey?_ofList_of_mem` (binder 8)
theorem s2_11 : ¬ (drop0% Std.DTreeMap.Raw.getKey?_ofList_of_mem 8) := fun h => by
  have := h (β := fun _ => Nat) (cmp := cmpH) (l := [⟨0, 0⟩, ⟨1, 1⟩]) (k := 0) (k' := 0) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.ExtDTreeMap.Const.getKey?_ofList_of_mem` (binder 8)
theorem s2_12 : ¬ (drop0% Std.ExtDTreeMap.Const.getKey?_ofList_of_mem 8) := fun h => by
  have := h (β := Nat) (cmp := cmpH) (l := [(0, 0), (1, 1)]) (k := 0) (k' := 0) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.ExtTreeMap.getKey?_ofList_of_mem` (binder 8)
theorem s2_13 : ¬ (drop0% Std.ExtTreeMap.getKey?_ofList_of_mem 8) := fun h => by
  have := h (β := Nat) (cmp := cmpH) (l := [(0, 0), (1, 1)]) (k := 0) (k' := 0) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKey?_ofList_of_mem` (binder 8)
theorem s2_14 : ¬ (drop0% Std.TreeMap.Raw.getKey?_ofList_of_mem 8) := fun h => by
  have := h (β := Nat) (cmp := cmpH) (l := [(0, 0), (1, 1)]) (k := 0) (k' := 0) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.getKey?_ofList_of_mem` (binder 8)
theorem s2_15 : ¬ (drop0% Std.TreeMap.getKey?_ofList_of_mem 8) := fun h => by
  have := h (β := Nat) (cmp := cmpH) (l := [(0, 0), (1, 1)]) (k := 0) (k' := 0) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.getKey?_ofList_of_mem` (binder 3)
theorem s2_16 : ¬ (drop0% Std.DTreeMap.Const.getKey?_ofList_of_mem 3) := fun h => by
  have := h (β := Nat) (cmp := cmpT) (l := [(0, 0), (1, 1), (2, 2), (3, 3)]) (k := 0) (k' := 0) (by decide) (by decide +kernel) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getKey?_ofList_of_mem` (binder 3)
theorem s2_17 : ¬ (drop0% Std.DTreeMap.Raw.Const.getKey?_ofList_of_mem 3) := fun h => by
  have := h (β := Nat) (cmp := cmpT) (l := [(0, 0), (1, 1), (2, 2), (3, 3)]) (k := 0) (k' := 0) (by decide) (by decide +kernel) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.getKey?_ofList_of_mem` (binder 3)
theorem s2_18 : ¬ (drop0% Std.DTreeMap.Raw.getKey?_ofList_of_mem 3) := fun h => by
  have := h (β := fun _ => Nat) (cmp := cmpT) (l := [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 3⟩]) (k := 0) (k' := 0) (by decide) (by decide +kernel) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.getKey?_ofList_of_mem` (binder 3)
theorem s2_19 : ¬ (drop0% Std.DTreeMap.getKey?_ofList_of_mem 3) := fun h => by
  have := h (β := fun _ => Nat) (cmp := cmpT) (l := [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 3⟩]) (k := 0) (k' := 0) (by decide) (by decide +kernel) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKey?_ofList_of_mem` (binder 3)
theorem s2_20 : ¬ (drop0% Std.TreeMap.Raw.getKey?_ofList_of_mem 3) := fun h => by
  have := h (β := Nat) (cmp := cmpT) (l := [(0, 0), (1, 1), (2, 2), (3, 3)]) (k := 0) (k' := 0) (by decide) (by decide +kernel) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.getKey?_ofList_of_mem` (binder 3)
theorem s2_21 : ¬ (drop0% Std.TreeMap.getKey?_ofList_of_mem 3) := fun h => by
  have := h (β := Nat) (cmp := cmpT) (l := [(0, 0), (1, 1), (2, 2), (3, 3)]) (k := 0) (k' := 0) (by decide) (by decide +kernel) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getKey?_ofList_of_mem` (binder 7)
theorem s2_22 : ¬ (drop0% Std.DTreeMap.Raw.Const.getKey?_ofList_of_mem 7) := fun h => by
  have := h (β := Nat) (cmp := compare) (l := [(0, 0)]) (k := 0) (k' := 1) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.getKey?_ofList_of_mem` (binder 7)
theorem s2_23 : ¬ (drop0% Std.DTreeMap.Raw.getKey?_ofList_of_mem 7) := fun h => by
  have := h (β := fun _ => Nat) (cmp := compare) (l := [⟨0, 0⟩]) (k := 0) (k' := 1) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKey?_ofList_of_mem` (binder 7)
theorem s2_24 : ¬ (drop0% Std.TreeMap.Raw.getKey?_ofList_of_mem 7) := fun h => by
  have := h (β := Nat) (cmp := compare) (l := [(0, 0)]) (k := 0) (k' := 1) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.getKey!_modify_self` (binder 2)
theorem s2_25 : ¬ (drop0% Std.DTreeMap.Const.getKey!_modify_self 2) := fun h => by
  have := h (α := Nat) (β := Nat) (t := Std.DTreeMap.Const.ofList [(1, 0)] cmpZ) (k := 2) (f := id)
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.Const.getKey!_modify_self` (binder 2)
theorem s2_26 : ¬ (drop0% Std.DTreeMap.Raw.Const.getKey!_modify_self 2) := fun h => by
  have := h (α := Nat) (β := Nat) (t := Std.DTreeMap.Raw.Const.ofList [(1, 0)] cmpZ) (by twf) (k := 2) (f := id)
  revert this; decide +kernel

-- `Std.TreeMap.Raw.getKey!_modify_self` (binder 4)
theorem s2_27 : ¬ (drop0% Std.TreeMap.Raw.getKey!_modify_self 4) := fun h => by
  have := h (α := Nat) (β := Nat) (t := .ofList [(1, 0)] cmpZ) (by twf) (k := 2) (f := id)
  revert this; decide +kernel

-- `Std.TreeMap.getKey!_modify_self` (binder 4)
theorem s2_28 : ¬ (drop0% Std.TreeMap.getKey!_modify_self 4) := fun h => by
  have := h (α := Nat) (β := Nat) (t := .ofList [(1, 0)] cmpZ) (k := 2) (f := id)
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.Const.getKey!_modify_self` (binder 2)
theorem s2_29 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.getKey!_modify_self 2) := fun h => by
  have := h (α := Nat) (β := Nat) (instOrd := ⟨cmpZ⟩) (t := (Std.DTreeMap.Const.ofList [(1, 0)] cmpZ).inner) (Std.DTreeMap.Const.ofList [(1, 0)] cmpZ).wf (k := 2) (f := id)
  revert this; decide +kernel

-- `Std.DTreeMap.Const.minKey?_modify_eq_minKey?` (binder 5)
theorem s2_30 : ¬ (drop0% Std.DTreeMap.Const.minKey?_modify_eq_minKey? 5) := fun h => by
  have := h (α := Nat) (β := Nat) (t := Std.DTreeMap.Const.ofList [(1, 0)] cmpH) (k := 0) (f := id)
  revert this; simp only [Std.TreeMap.minKey?, Std.DTreeMap.minKey?, Std.DTreeMap.Raw.minKey?, Std.TreeMap.Raw.minKey?, Std.ExtTreeMap.minKey?, Std.ExtDTreeMap.minKey?, s2h_mkS_eq]; decide +kernel

-- `Std.DTreeMap.Raw.Const.minKey?_modify_eq_minKey?` (binder 5)
theorem s2_31 : ¬ (drop0% Std.DTreeMap.Raw.Const.minKey?_modify_eq_minKey? 5) := fun h => by
  have := h (α := Nat) (β := Nat) (t := Std.DTreeMap.Raw.Const.ofList [(1, 0)] cmpH) (by twf) (k := 0) (f := id)
  revert this; simp only [Std.TreeMap.minKey?, Std.DTreeMap.minKey?, Std.DTreeMap.Raw.minKey?, Std.TreeMap.Raw.minKey?, Std.ExtTreeMap.minKey?, Std.ExtDTreeMap.minKey?, s2h_mkS_eq]; decide +kernel

-- `Std.ExtDTreeMap.Const.minKey?_modify_eq_minKey?` (binder 5)
theorem s2_32 : ¬ (drop0% Std.ExtDTreeMap.Const.minKey?_modify_eq_minKey? 5) := fun h => by
  have := h (α := Nat) (β := Nat) (t := Std.ExtDTreeMap.Const.ofList [(1, 0)] cmpH) (k := 0) (f := id)
  revert this; simp only [Std.TreeMap.minKey?, Std.DTreeMap.minKey?, Std.DTreeMap.Raw.minKey?, Std.TreeMap.Raw.minKey?, Std.ExtTreeMap.minKey?, Std.ExtDTreeMap.minKey?, s2h_mkS_eq]; decide +kernel

-- `Std.ExtTreeMap.minKey?_modify_eq_minKey?` (binder 5)
theorem s2_33 : ¬ (drop0% Std.ExtTreeMap.minKey?_modify_eq_minKey? 5) := fun h => by
  have := h (α := Nat) (β := Nat) (t := .ofList [(1, 0)] cmpH) (k := 0) (f := id)
  revert this; simp only [Std.TreeMap.minKey?, Std.DTreeMap.minKey?, Std.DTreeMap.Raw.minKey?, Std.TreeMap.Raw.minKey?, Std.ExtTreeMap.minKey?, Std.ExtDTreeMap.minKey?, s2h_mkS_eq]; decide +kernel

-- `Std.TreeMap.Raw.minKey?_modify_eq_minKey?` (binder 5)
theorem s2_34 : ¬ (drop0% Std.TreeMap.Raw.minKey?_modify_eq_minKey? 5) := fun h => by
  have := h (α := Nat) (β := Nat) (t := .ofList [(1, 0)] cmpH) (by twf) (k := 0) (f := id)
  revert this; simp only [Std.TreeMap.minKey?, Std.DTreeMap.minKey?, Std.DTreeMap.Raw.minKey?, Std.TreeMap.Raw.minKey?, Std.ExtTreeMap.minKey?, Std.ExtDTreeMap.minKey?, s2h_mkS_eq]; decide +kernel

-- `Std.TreeMap.minKey?_modify_eq_minKey?` (binder 5)
theorem s2_35 : ¬ (drop0% Std.TreeMap.minKey?_modify_eq_minKey? 5) := fun h => by
  have := h (α := Nat) (β := Nat) (t := .ofList [(1, 0)] cmpH) (k := 0) (f := id)
  revert this; simp only [Std.TreeMap.minKey?, Std.DTreeMap.minKey?, Std.DTreeMap.Raw.minKey?, Std.TreeMap.Raw.minKey?, Std.ExtTreeMap.minKey?, Std.ExtDTreeMap.minKey?, s2h_mkS_eq]; decide +kernel

-- `Std.DTreeMap.Internal.Impl.Const.minKey?_modify_eq_minKey?` (binder 5)
theorem s2_36 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.minKey?_modify_eq_minKey? 5) := fun h => by
  have := h (α := OH) (β := Nat) (t := (Std.DTreeMap.Const.ofList [((1 : OH), (0 : Nat))] compare).inner) (Std.DTreeMap.Const.ofList [((1 : OH), (0 : Nat))] compare).wf (k := 0) (f := id)
  revert this; simp only [Std.TreeMap.minKey?, Std.DTreeMap.minKey?, Std.DTreeMap.Raw.minKey?, Std.TreeMap.Raw.minKey?, Std.ExtTreeMap.minKey?, Std.ExtDTreeMap.minKey?, s2h_mkS_eq]; decide +kernel

-- `Std.DTreeMap.Internal.Impl.getKey_eq` (binder 4)
theorem s2_37 : (drop% Std.DTreeMap.Internal.Impl.getKey_eq 4) := by
  intros; exact s2h_gk_eq _ _ _ _ (fun _ _ h => Std.LawfulEqCmp.eq_of_compare h)

-- `Std.DTreeMap.Internal.Impl.getKey_eq` (binder 6)
theorem s2_38 : (drop% Std.DTreeMap.Internal.Impl.getKey_eq 6) := by
  intros; exact s2h_gk_eq _ _ _ _ (fun _ _ h => Std.LawfulEqCmp.eq_of_compare h)

-- `Std.DTreeMap.Raw.getKey_eq` (binder 4)
theorem s2_39 : (drop% Std.DTreeMap.Raw.getKey_eq 4) := by
  intros; exact s2h_gk_eq _ _ _ _ (fun _ _ h => Std.LawfulEqCmp.eq_of_compare h)

-- `Std.DTreeMap.Raw.getKey_eq` (binder 6)
theorem s2_40 : (drop% Std.DTreeMap.Raw.getKey_eq 6) := by
  intros; exact s2h_gk_eq _ _ _ _ (fun _ _ h => Std.LawfulEqCmp.eq_of_compare h)

-- `Std.TreeMap.Raw.getKey_eq` (binder 4)
theorem s2_41 : (drop% Std.TreeMap.Raw.getKey_eq 4) := by
  intros; exact s2h_gk_eq _ _ _ _ (fun _ _ h => Std.LawfulEqCmp.eq_of_compare h)

-- `Std.TreeMap.Raw.getKey_eq` (binder 6)
theorem s2_42 : (drop% Std.TreeMap.Raw.getKey_eq 6) := by
  intros; exact s2h_gk_eq _ _ _ _ (fun _ _ h => Std.LawfulEqCmp.eq_of_compare h)

-- `Std.DTreeMap.getKey_eq` (binder 4)
theorem s2_43 : (drop% Std.DTreeMap.getKey_eq 4) := by
  intros; exact s2h_gk_eq _ _ _ _ (fun _ _ h => Std.LawfulEqCmp.eq_of_compare h)

-- `Std.TreeMap.getKey_eq` (binder 4)
theorem s2_44 : (drop% Std.TreeMap.getKey_eq 4) := by
  intros; exact s2h_gk_eq _ _ _ _ (fun _ _ h => Std.LawfulEqCmp.eq_of_compare h)

-- `Std.DTreeMap.Internal.Impl.getKey!_modify_self` (binder 4)
theorem s2_45 : (drop% Std.DTreeMap.Internal.Impl.getKey!_modify_self 4) := by
  intros; split
  · rename_i hm; exact s2h_gkm1 _ _ _ _ hm
  · rename_i hm; exact s2h_gkm0 _ _ _ _ hm

-- `Std.DTreeMap.Internal.Impl.getKey!_modify_self` (binder 6)
theorem s2_46 : (drop% Std.DTreeMap.Internal.Impl.getKey!_modify_self 6) := by
  intros; split
  · rename_i hm; exact s2h_gkm1 _ _ _ _ hm
  · rename_i hm; exact s2h_gkm0 _ _ _ _ hm

-- `Std.DTreeMap.Raw.getKey!_modify_self` (binder 4)
theorem s2_47 : (drop% Std.DTreeMap.Raw.getKey!_modify_self 4) := by
  intros; split
  · rename_i hm; exact s2h_gkm1 _ _ _ _ hm
  · rename_i hm; exact s2h_gkm0 _ _ _ _ hm

-- `Std.DTreeMap.Raw.getKey!_modify_self` (binder 6)
theorem s2_48 : (drop% Std.DTreeMap.Raw.getKey!_modify_self 6) := by
  intros; split
  · rename_i hm; exact s2h_gkm1 _ _ _ _ hm
  · rename_i hm; exact s2h_gkm0 _ _ _ _ hm

-- `Std.DTreeMap.getKey!_modify_self` (binder 4)
theorem s2_49 : (drop% Std.DTreeMap.getKey!_modify_self 4) := by
  intros; split
  · rename_i hm; exact s2h_gkm1 _ _ _ _ hm
  · rename_i hm; exact s2h_gkm0 _ _ _ _ hm

-- `Std.DTreeMap.Internal.Impl.Const.minKey?_modify_eq_minKey?` (binder 4)
theorem s2_50 : (drop% Std.DTreeMap.Internal.Impl.Const.minKey?_modify_eq_minKey? 4) := by
  intros; exact s2h_mkm _ _ _ _

-- `Std.DTreeMap.Internal.Impl.Const.minKey?_modify_eq_minKey?` (binder 6)
theorem s2_51 : (drop% Std.DTreeMap.Internal.Impl.Const.minKey?_modify_eq_minKey? 6) := by
  intros; exact s2h_mkm _ _ _ _

-- `Std.DTreeMap.Const.minKey?_modify_eq_minKey?` (binder 4)
theorem s2_52 : (drop% Std.DTreeMap.Const.minKey?_modify_eq_minKey? 4) := by
  intros; exact s2h_mkm _ _ _ _

-- `Std.DTreeMap.Raw.Const.minKey?_modify_eq_minKey?` (binder 4)
theorem s2_53 : (drop% Std.DTreeMap.Raw.Const.minKey?_modify_eq_minKey? 4) := by
  intros; exact s2h_mkm _ _ _ _

-- `Std.DTreeMap.Raw.Const.minKey?_modify_eq_minKey?` (binder 6)
theorem s2_54 : (drop% Std.DTreeMap.Raw.Const.minKey?_modify_eq_minKey? 6) := by
  intros; exact s2h_mkm _ _ _ _

-- `Std.TreeMap.Raw.minKey?_modify_eq_minKey?` (binder 4)
theorem s2_55 : (drop% Std.TreeMap.Raw.minKey?_modify_eq_minKey? 4) := by
  intros; exact s2h_mkm _ _ _ _

-- `Std.TreeMap.Raw.minKey?_modify_eq_minKey?` (binder 6)
theorem s2_56 : (drop% Std.TreeMap.Raw.minKey?_modify_eq_minKey? 6) := by
  intros; exact s2h_mkm _ _ _ _

-- `Std.TreeMap.minKey?_modify_eq_minKey?` (binder 4)
theorem s2_57 : (drop% Std.TreeMap.minKey?_modify_eq_minKey? 4) := by
  intros; exact s2h_mkm _ _ _ _

-- `Std.DTreeMap.Equiv.filterMap` (binder 6)
theorem s2_58 : ¬ (drop0% Std.DTreeMap.Equiv.filterMap 6) := fun h => by
  have := @h Nat (fun _ => Nat) (fun _ => Nat) compare ∅ (.ofList [⟨0, 0⟩]) (fun _ v => some v)
  exact absurd this.1.1.length_eq (by decide +kernel)

-- `Std.TreeSet.Raw.get?_insertMany_list_of_not_mem_of_mem` (binder 11)
theorem s2_59 : ¬ (drop0% Std.TreeSet.Raw.get?_insertMany_list_of_not_mem_of_mem 11) := fun h => by
  have := @h Nat compare ∅ _ (by twf) [] 0 0 rfl (by decide +kernel) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get?_insertMany_list_of_not_mem_of_mem` (binder 10)
theorem s2_60 : ¬ (drop0% Std.TreeSet.Raw.get?_insertMany_list_of_not_mem_of_mem 10) := fun h => by
  have := @h Nat cmpH ∅ _ (by twf) [1, 0] 0 0 rfl (by decide +kernel) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get?_insertMany_list_of_not_mem_of_mem` (binder 9)
theorem s2_61 : ¬ (drop0% Std.TreeSet.Raw.get?_insertMany_list_of_not_mem_of_mem 9) := fun h => by
  have := @h Nat cmpH (.ofList [1] cmpH) _ (by twf) [0] 0 0 rfl (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get?_insertMany_list_of_not_mem_of_mem` (binder 8)
theorem s2_62 : ¬ (drop0% Std.TreeSet.Raw.get?_insertMany_list_of_not_mem_of_mem 8) := fun h => by
  have := @h Nat compare ∅ _ (by twf) [0] 0 1 (by decide +kernel) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get?_insertMany_list_of_not_mem_of_mem` (binder 4)
theorem s2_63 : ¬ (drop0% Std.TreeSet.Raw.get?_insertMany_list_of_not_mem_of_mem 4) := fun h => by
  have := @h Nat compare ⟨⟨⟨.inner 1 5 () .leaf (.inner 0 9 () .leaf .leaf)⟩⟩⟩ _ [1] 1 1 rfl (by decide +kernel) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.minKey?_insert_le_self` (binder 9)
theorem s2_64 : ¬ (drop0% Std.DTreeMap.Raw.minKey?_insert_le_self 9) := fun h => by
  have := @h Nat (fun _ => Nat) compare ∅ _ (by twf) 0 0 5
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.getD_diff!_of_contains_eq_false_right` (binder 10)
theorem s2_65 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.getD_diff!_of_contains_eq_false_right 10) := fun h => by
  have := @h Nat _ Nat (Std.DTreeMap.Const.ofList [(0, 1)] compare).inner (Std.DTreeMap.Const.ofList [(0, 1)] compare).inner _ (Std.DTreeMap.Const.ofList [(0, 1)] compare).wf (Std.DTreeMap.Const.ofList [(0, 1)] compare).wf 0 7
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.Equiv.of_forall_contains_eq` (binder 8)
theorem s2_66 : ¬ (drop0% Std.TreeSet.Raw.Equiv.of_forall_contains_eq 8) := fun h => by
  have := @h Nat compare ∅ (.ofList [0]) _ _ (by twf) (by twf)
  exact absurd this.1.1.1.1.length_eq (by decide +kernel)

-- `Std.TreeSet.Raw.Equiv.of_forall_contains_eq` (binder 5)
theorem s2_67 : ¬ (drop0% Std.TreeSet.Raw.Equiv.of_forall_contains_eq 5) := fun h => by
  have := @h Nat cmpH (.ofList [0] cmpH) (.ofList [1] cmpH) _ (by twf) (by twf) (fun k => rfl)
  exact absurd this.1.1.1.1 (by decide +kernel)

-- `Std.TreeSet.Raw.get?_insertMany_list_of_not_mem_of_mem` (binder 3)
theorem s2_68 : ¬ (drop0% Std.TreeSet.Raw.get?_insertMany_list_of_not_mem_of_mem 3) := fun h => by
  have := h (cmp := cmpT) (t := ∅) (l := [0, 1, 2, 3]) (k := 0) (k' := 0) (by twf) rfl (by decide +kernel) (by decide +kernel) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem` (binder 3)
theorem s2_69 : ¬ (drop0% Std.TreeSet.get?_insertMany_list_of_not_mem_of_mem 3) := fun h => by
  have := h (cmp := cmpT) (t := ∅) (l := [0, 1, 2, 3]) (k := 0) (k' := 0) rfl (by decide +kernel) (by decide +kernel) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem` (binder 9)
theorem s2_70 : ¬ (drop0% Std.ExtTreeSet.get?_insertMany_list_of_not_mem_of_mem 9) := fun h => by
  have := h (cmp := cmpH) (t := ∅) (l := [1, 0]) (k := 0) (k' := 0) rfl (by simp) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.minKey?_insert_le_self` (binder 9)
theorem s2_71 : ¬ (drop0% Std.TreeMap.Raw.minKey?_insert_le_self 9) := fun h => by
  have := @h Nat Nat compare ∅ _ (by twf) 0 0 5
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.minKey?_insert_le_self` (binder 9)
theorem s2_72 : ¬ (drop0% Std.DTreeMap.Internal.Impl.minKey?_insert_le_self 9) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (t := .leaf) Impl.WF.empty (k := 0) (v := 0) (kmi := 5)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.getD_diff!_of_contains_eq_false_right` (binder 11)
theorem s2_73 : ¬ (drop0% Std.DTreeMap.Internal.Impl.getD_diff!_of_contains_eq_false_right 11) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (m₁ := (Std.DTreeMap.ofList [⟨0, 1⟩] compare).inner) (m₂ := (Std.DTreeMap.ofList [⟨0, 1⟩] compare).inner) (Std.DTreeMap.ofList [⟨0, 1⟩] compare).wf (Std.DTreeMap.ofList [⟨0, 1⟩] compare).wf (k := 0) (fallback := 7)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.getD_diff!_of_contains_eq_false_right` (binder 6)
theorem s2_74 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.getD_diff!_of_contains_eq_false_right 6) := fun h => by
  have := h (α := Nat) (β := Nat) (m₁ := .inner 1 1 1 .leaf (.inner 1 0 7 .leaf .leaf)) (m₂ := (Std.DTreeMap.Const.ofList [(5, 5)] compare).inner) (Std.DTreeMap.Const.ofList [(5, 5)] compare).wf (k := 0) (fallback := 3) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.getD_diff!_of_contains_eq_false_right` (binder 7)
theorem s2_75 : ¬ (drop0% Std.DTreeMap.Internal.Impl.getD_diff!_of_contains_eq_false_right 7) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (m₁ := .inner 1 1 1 .leaf (.inner 1 0 7 .leaf .leaf)) (m₂ := (Std.DTreeMap.ofList [⟨5, 5⟩] compare).inner) (Std.DTreeMap.ofList [⟨5, 5⟩] compare).wf (k := 0) (fallback := 3) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.getD_diff!_of_contains_eq_false_right` (binder 7)
theorem s2_76 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.getD_diff!_of_contains_eq_false_right 7) := fun h => by
  have := h (α := Nat) (β := Nat) (m₁ := (Std.DTreeMap.Const.ofList [(0, 7), (5, 5)] compare).inner) (m₂ := .inner 1 1 1 .leaf (.inner 1 0 0 .leaf .leaf)) (Std.DTreeMap.Const.ofList [(0, 7), (5, 5)] compare).wf (k := 0) (fallback := 3) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.getD_diff!_of_contains_eq_false_right` (binder 8)
theorem s2_77 : ¬ (drop0% Std.DTreeMap.Internal.Impl.getD_diff!_of_contains_eq_false_right 8) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (m₁ := (Std.DTreeMap.ofList [⟨0, 7⟩, ⟨5, 5⟩] compare).inner) (m₂ := .inner 1 1 1 .leaf (.inner 1 0 0 .leaf .leaf)) (Std.DTreeMap.ofList [⟨0, 7⟩, ⟨5, 5⟩] compare).wf (k := 0) (fallback := 3) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.isEmpty_union!` (binder 7)
theorem s2_78 : ¬ (drop0% Std.DTreeMap.Internal.Impl.isEmpty_union! 7) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (m₁ := (Std.DTreeMap.ofList [⟨1, 1⟩] compare).inner) (m₂ := .inner 1 5 5 .leaf (.inner 0 9 9 .leaf .leaf)) (Std.DTreeMap.ofList [⟨1, 1⟩] compare).wf
  revert this; decide +kernel

-- `Std.DTreeMap.Internal.Impl.isEmpty_union!` (binder 6)
theorem s2_79 : ¬ (drop0% Std.DTreeMap.Internal.Impl.isEmpty_union! 6) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (m₁ := .inner 2 5 5 .leaf (.inner 0 9 9 .leaf .leaf)) (m₂ := (Std.DTreeMap.ofList [⟨1, 1⟩] compare).inner) (Std.DTreeMap.ofList [⟨1, 1⟩] compare).wf
  revert this; decide +kernel

-- `Std.DTreeMap.Raw.Equiv.filterMap` (binder 8)
theorem s2_80 : ¬ (drop0% Std.DTreeMap.Raw.Equiv.filterMap 8) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (γ := fun _ => Nat) (cmp := compare) (t₁ := ∅) (t₂ := .ofList [⟨0, 0⟩]) (by twf) (by twf) (fun _ v => some v)
  exact absurd this.1.1.length_eq (by decide +kernel)

-- `Std.TreeMap.Raw.Equiv.filterMap` (binder 8)
theorem s2_81 : ¬ (drop0% Std.TreeMap.Raw.Equiv.filterMap 8) := fun h => by
  have := h (α := Nat) (β := Nat) (γ := Nat) (cmp := compare) (t₁ := ∅) (t₂ := .ofList [(0, 0)]) (by twf) (by twf) (fun _ v => some v)
  exact absurd this.1.1.1.length_eq (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Equiv.filterMap` (binder 8)
theorem s2_82 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Equiv.filterMap 8) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (γ := fun _ => Nat) (t₁ := .leaf) (t₂ := (Std.DTreeMap.ofList [⟨0, 0⟩] compare).inner) Impl.WF.empty (Std.DTreeMap.ofList [⟨0, 0⟩] compare).wf (f := fun _ v => some v)
  exact absurd this.1.length_eq (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.WF.filterMap` (binder 7)
theorem s2_83 : ¬ (drop0% Std.DTreeMap.Internal.Impl.WF.filterMap 7) := fun h => by
  have := (h (α := Nat) (β := fun _ => Nat) (γ := fun _ => Nat) (t := (Std.DTreeMap.ofList [⟨0, 0⟩, ⟨1, 1⟩] cmpT).inner) (h := (@Std.DTreeMap.Internal.Impl.WF.balanced _ _ (id _) _ (Std.DTreeMap.ofList [⟨0, 0⟩, ⟨1, 1⟩] cmpT).wf)) (f := fun _ v => some v)).ordered
  revert this; unfold Impl.Ordered; decide +kernel

-- `Std.DTreeMap.Raw.WF.filterMap` (binder 6)
theorem s2_84 : ¬ (drop0% Std.DTreeMap.Raw.WF.filterMap 6) := fun h => by
  have := (h (α := Nat) (β := fun _ => Nat) (cmp := compare) (t := ⟨(Std.DTreeMap.ofList [⟨0, 0⟩, ⟨1, 1⟩] cmpT).inner⟩) (f := fun _ v => some v)).out.ordered
  revert this; unfold Impl.Ordered; decide +kernel

-- `Std.TreeMap.Raw.WF.filterMap` (binder 6)
theorem s2_85 : ¬ (drop0% Std.TreeMap.Raw.WF.filterMap 6) := fun h => by
  have := (h (α := Nat) (β := Nat) (cmp := compare) (t := ⟨⟨(Std.DTreeMap.ofList [⟨0, 0⟩, ⟨1, 1⟩] cmpT).inner⟩⟩) (f := fun _ v => some v)).out.out.ordered
  revert this; unfold Impl.Ordered; decide +kernel

-- `Std.DTreeMap.Internal.Impl.WF.filterMap` (binder 5)
theorem s2_86 : (indep% Std.DTreeMap.Internal.Impl.WF.filterMap 5) := fun h => h.balanced

-- `Std.TreeSet.Raw.Equiv.getKey_eq` (binder 6)
theorem s2_87 : ¬ (indep0% Std.TreeSet.Raw.Equiv.getKey_eq 6) := by refute_dep

-- `Std.TreeSet.Raw.Equiv.getKey_eq` (binder 7)
theorem s2_88 : ¬ (indep0% Std.TreeSet.Raw.Equiv.getKey_eq 7) := fun h => tsrBad_notWF 0 (h (cmp := compare) (t₁ := ⟨⟨⟨.inner 0 0 () .leaf .leaf⟩⟩⟩) (t₂ := .ofList [0]) (k := 0) (hk := by decide +kernel) (by twf) ⟨⟨⟨⟨by decide +kernel⟩⟩⟩⟩)

-- `Std.TreeSet.Raw.Equiv.getKey_eq` (binder 8)
theorem s2_89 : ¬ (indep0% Std.TreeSet.Raw.Equiv.getKey_eq 8) := fun h => tsrBad_notWF 0 (h (cmp := compare) (t₂ := ⟨⟨⟨.inner 0 0 () .leaf .leaf⟩⟩⟩) (t₁ := .ofList [0]) (k := 0) (hk := by decide +kernel) (by twf) ⟨⟨⟨⟨by decide +kernel⟩⟩⟩⟩)

-- `Std.TreeSet.Raw.Equiv.getKey_eq` (binder 9)
theorem s2_90 : ¬ (indep0% Std.TreeSet.Raw.Equiv.getKey_eq 9) := fun h => by
  have := h (cmp := compare) (t₁ := .ofList [0]) (t₂ := ∅) (k := 0) (hk := by decide +kernel) (by twf) (by twf)
  exact absurd this.1.1.1.1.length_eq (by decide +kernel)

-- `Std.DTreeMap.Raw.Equiv.getKey_eq` (binder 8)
theorem s2_91 : ¬ (indep0% Std.DTreeMap.Raw.Equiv.getKey_eq 8) := fun h => dtrBad_notWF 0 0 (h (α := Nat) (β := fun _ => Nat) (cmp := compare) (t₁ := ⟨.inner 0 0 (0 : Nat) .leaf .leaf⟩) (t₂ := .ofList ([⟨0, 0⟩] : List ((_ : Nat) × Nat))) (k := 0) (hk := by decide +kernel) (by twf) ⟨⟨by decide +kernel⟩⟩)

-- `Std.DTreeMap.Raw.Equiv.getKey_eq` (binder 9)
theorem s2_92 : ¬ (indep0% Std.DTreeMap.Raw.Equiv.getKey_eq 9) := fun h => dtrBad_notWF 0 0 (h (α := Nat) (β := fun _ => Nat) (cmp := compare) (t₂ := ⟨.inner 0 0 (0 : Nat) .leaf .leaf⟩) (t₁ := .ofList ([⟨0, 0⟩] : List ((_ : Nat) × Nat))) (k := 0) (hk := by decide +kernel) (by twf) ⟨⟨by decide +kernel⟩⟩)

-- `Std.DTreeMap.Raw.Equiv.getKey_eq` (binder 10)
theorem s2_93 : ¬ (indep0% Std.DTreeMap.Raw.Equiv.getKey_eq 10) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (cmp := compare) (t₁ := .ofList ([⟨0, 0⟩] : List ((_ : Nat) × Nat))) (t₂ := ∅) (k := 0) (hk := by decide +kernel) (by twf) (by twf)
  exact absurd this.1.1.length_eq (by decide +kernel)

-- `Std.TreeMap.Raw.Equiv.getKey_eq` (binder 8)
theorem s2_94 : ¬ (indep0% Std.TreeMap.Raw.Equiv.getKey_eq 8) := fun h => tmrBad_notWF 0 0 (h (α := Nat) (β := Nat) (cmp := compare) (t₁ := ⟨⟨.inner 0 0 0 .leaf .leaf⟩⟩) (t₂ := .ofList [(0, 0)]) (k := 0) (hk := by decide +kernel) (by twf) ⟨⟨⟨by decide +kernel⟩⟩⟩)

-- `Std.TreeMap.Raw.Equiv.getKey_eq` (binder 9)
theorem s2_95 : ¬ (indep0% Std.TreeMap.Raw.Equiv.getKey_eq 9) := fun h => tmrBad_notWF 0 0 (h (α := Nat) (β := Nat) (cmp := compare) (t₂ := ⟨⟨.inner 0 0 0 .leaf .leaf⟩⟩) (t₁ := .ofList [(0, 0)]) (k := 0) (hk := by decide +kernel) (by twf) ⟨⟨⟨by decide +kernel⟩⟩⟩)

-- `Std.TreeMap.Raw.Equiv.getKey_eq` (binder 10)
theorem s2_96 : ¬ (indep0% Std.TreeMap.Raw.Equiv.getKey_eq 10) := fun h => by
  have := h (α := Nat) (β := Nat) (cmp := compare) (t₁ := .ofList [(0, 0)]) (t₂ := ∅) (k := 0) (hk := by decide +kernel) (by twf) (by twf)
  exact absurd this.1.1.1.length_eq (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Equiv.getKey_eq` (binder 8)
theorem s2_97 : ¬ (indep0% Std.DTreeMap.Internal.Impl.Equiv.getKey_eq 8) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (t₁ := (Std.DTreeMap.ofList [⟨0, 0⟩] compare).inner) (t₂ := .leaf) (Std.DTreeMap.ofList [⟨0, 0⟩] compare).wf Impl.WF.empty (k := 0) (by decide +kernel)
  exact absurd this.1.length_eq (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.get_insertMany!_list_of_mem` (binder 5)
theorem s2_98 : ¬ (indep0% Std.DTreeMap.Internal.Impl.get_insertMany!_list_of_mem 5) := fun h => OH.notLawfulEq (h (α := OH) (β := fun _ => Nat) (t := .leaf) (l := [⟨⟨0⟩, 0⟩]) (k := ⟨0⟩) (k' := ⟨0⟩) (v := 0) (h' := by decide +kernel) Impl.WF.empty rfl (by simp) (by simp))

-- `Std.DTreeMap.Internal.Impl.toListModel_alter` (binder 4)
theorem s2_99 : ¬ (indep0% Std.DTreeMap.Internal.Impl.toListModel_alter 4) := fun h => OH.notLawfulEq (h (α := OH) (β := fun _ => Nat) (t := .leaf) (a := ⟨0⟩) (f := id) Impl.Balanced.leaf (by simp [Impl.Ordered, Impl.toListModel]))

-- `Std.DTreeMap.Internal.Impl.toListModel_alter` (binder 6)
theorem s2_100 : ¬ (indep0% Std.DTreeMap.Internal.Impl.toListModel_alter 6) := fun h => OB.notLawfulBEq (h (α := OB) (β := fun _ => Nat) (t := .leaf) (a := ⟨0⟩) (f := id) Impl.Balanced.leaf (by simp [Impl.Ordered, Impl.toListModel]))

-- `Std.DTreeMap.Internal.Impl.Const.toListModel_alter` (binder 10)
theorem s2_101 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.toListModel_alter 10) := fun h => by
  have := h (α := Nat) (β := Nat) (t := (Std.DTreeMap.Const.ofList [(0, 0), (1, 1)] cmpT).inner) (a := 1) (f := fun _ => none) (@Std.DTreeMap.Internal.Impl.WF.balanced _ _ (id _) _ (Std.DTreeMap.Const.ofList [(0, 0), (1, 1)] cmpT).wf)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.toListModel_alter` (binder 11)
theorem s2_102 : ¬ (drop0% Std.DTreeMap.Internal.Impl.toListModel_alter 11) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (t := (Std.DTreeMap.ofList [⟨0, 0⟩, ⟨1, 1⟩] cmpT).inner) (a := 1) (f := fun _ => none) (@Std.DTreeMap.Internal.Impl.WF.balanced _ _ (id _) _ (Std.DTreeMap.ofList [⟨0, 0⟩, ⟨1, 1⟩] cmpT).wf)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.toListModel_alter` (binder 5)
theorem s2_103 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.toListModel_alter 5) := fun h => by
  have := h (α := OB) (β := Nat) (t := (Std.DTreeMap.Const.ofList [((⟨0⟩ : OB), (0 : Nat)), (⟨1⟩, 1)] compare).inner) (a := ⟨1⟩) (f := fun _ => none) (Std.DTreeMap.Const.ofList [((⟨0⟩ : OB), (0 : Nat)), (⟨1⟩, 1)] compare).wf.balanced (Std.DTreeMap.Const.ofList [((⟨0⟩ : OB), (0 : Nat)), (⟨1⟩, 1)] compare).wf.ordered
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.toListModel_alter` (binder 3)
theorem s2_104 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.toListModel_alter 3) := fun h => by
  have := h (α := OT) (β := Nat) (t := (Std.DTreeMap.Const.ofList [((0 : OT), (0 : Nat)), (1, 1), (2, 2)] compare).inner) (a := 0) (f := fun _ => none) (@Std.DTreeMap.Internal.Impl.WF.balanced _ _ (id _) _ (Std.DTreeMap.Const.ofList [((0 : OT), (0 : Nat)), (1, 1), (2, 2)] compare).wf) (by unfold Impl.Ordered; decide +kernel)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.toListModel_alter` (binder 3)
theorem s2_105 : ¬ (drop0% Std.DTreeMap.Internal.Impl.toListModel_alter 3) := fun h => by
  have := h (α := OT) (β := fun _ => Nat) (t := (Std.DTreeMap.ofList ([⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩] : List ((_ : OT) × Nat)) compare).inner) (a := 0) (f := fun _ => none) (@Std.DTreeMap.Internal.Impl.WF.balanced _ _ (id _) _ (Std.DTreeMap.ofList ([⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩] : List ((_ : OT) × Nat)) compare).wf) (by unfold Impl.Ordered; decide +kernel)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.get_insertMany!_list_of_mem` (binder 12)
theorem s2_106 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.get_insertMany!_list_of_mem 12) := fun h => by
  have := h (α := Nat) (β := Nat) (t := (Std.DTreeMap.Const.ofList [(0, 5)] compare).inner) (l := []) (k := 0) (k' := 0) (v := 9) (h' := by decide +kernel) (Std.DTreeMap.Const.ofList [(0, 5)] compare).wf rfl (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.get_insertMany!_list_of_mem` (binder 13)
theorem s2_107 : ¬ (drop0% Std.DTreeMap.Internal.Impl.get_insertMany!_list_of_mem 13) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (t := (Std.DTreeMap.ofList [⟨0, 5⟩] compare).inner) (l := []) (k := 0) (k' := 0) (v := 9) (h' := by decide +kernel) (Std.DTreeMap.ofList [⟨0, 5⟩] compare).wf rfl (by decide)
  simp only [cast_eq] at this; exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.get_insertMany!_list_of_mem` (binder 11)
theorem s2_108 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.get_insertMany!_list_of_mem 11) := fun h => by
  have := h (α := Nat) (β := Nat) (t := .leaf) (l := [(0, 1), (0, 2)]) (k := 0) (k' := 0) (v := 1) (h' := by decide +kernel) Impl.WF.empty rfl (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.get_insertMany!_list_of_mem` (binder 12)
theorem s2_109 : ¬ (drop0% Std.DTreeMap.Internal.Impl.get_insertMany!_list_of_mem 12) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (t := .leaf) (l := [⟨0, 1⟩, ⟨0, 2⟩]) (k := 0) (k' := 0) (v := 1) (h' := by decide +kernel) Impl.WF.empty rfl (by decide)
  simp only [cast_eq] at this; exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.get_insertMany!_list_of_mem` (binder 9)
theorem s2_110 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.get_insertMany!_list_of_mem 9) := fun h => by
  have := h (α := Nat) (β := Nat) (t := (Std.DTreeMap.Const.ofList [(1, 5)] compare).inner) (l := [(0, 9)]) (k := 0) (k' := 1) (v := 9) (h' := by decide +kernel) (Std.DTreeMap.Const.ofList [(1, 5)] compare).wf (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.Equiv.of_forall_contains_eq` (binder 6)
theorem s2_111 : ¬ (drop0% Std.TreeSet.Raw.Equiv.of_forall_contains_eq 6) := fun h => by
  have := h (cmp := compare) (t₁ := ⟨⟨⟨.inner 2 1 () .leaf (.inner 1 0 () .leaf .leaf)⟩⟩⟩) (t₂ := Std.TreeSet.Raw.ofList [1] compare) (by twf) (fun k => s2h_cont k)
  exact absurd this.1.1.1.1.length_eq (by decide +kernel)

-- `Std.TreeSet.Raw.Equiv.of_forall_contains_eq` (binder 7)
theorem s2_112 : ¬ (drop0% Std.TreeSet.Raw.Equiv.of_forall_contains_eq 7) := fun h => by
  have := h (cmp := compare) (t₂ := ⟨⟨⟨.inner 2 1 () .leaf (.inner 1 0 () .leaf .leaf)⟩⟩⟩) (t₁ := Std.TreeSet.Raw.ofList [1] compare) (by twf) (fun k => (s2h_cont k).symm)
  exact absurd this.1.1.1.1.length_eq (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.entryAtIdx?_eq_some_entryAtIdx` (binder 3)
theorem s2_113 : ¬ (indep0% Std.DTreeMap.Internal.Impl.entryAtIdx?_eq_some_entryAtIdx 3) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (t := .inner 2 0 0 .leaf .leaf) (i := 0) (by decide)
  rw [Impl.balanced_inner_iff] at this; simp [Impl.size] at this

-- `Std.DTreeMap.Internal.Impl.Const.getKey!_modify_self` (binder 5)
theorem s2_114 : (drop% Std.DTreeMap.Internal.Impl.Const.getKey!_modify_self 5) := by
  intros; split
  · rename_i hm; exact s2h_gkmc1 _ _ _ Std.ReflCmp.compare_self _ hm
  · rename_i hm; exact s2h_gkmc0 _ _ _ Std.ReflCmp.compare_self _ hm

-- `Std.DTreeMap.Raw.Const.getKey!_modify_self` (binder 5)
theorem s2_115 : (drop% Std.DTreeMap.Raw.Const.getKey!_modify_self 5) := by
  intros; split
  · rename_i hm; exact s2h_gkmc1 _ _ _ Std.ReflCmp.compare_self _ hm
  · rename_i hm; exact s2h_gkmc0 _ _ _ Std.ReflCmp.compare_self _ hm

-- `Std.TreeMap.Raw.getKey!_modify_self` (binder 5)
theorem s2_116 : (drop% Std.TreeMap.Raw.getKey!_modify_self 5) := by
  intros; split
  · rename_i hm; exact s2h_gkmc1 _ _ _ Std.ReflCmp.compare_self _ hm
  · rename_i hm; exact s2h_gkmc0 _ _ _ Std.ReflCmp.compare_self _ hm

-- `Std.TreeSet.Equiv.min_eq` (binder 4)
theorem s2_117 : ¬ (drop0% Std.TreeSet.Equiv.min_eq 4) := fun h => by
  have := @h Nat cmpT (.ofList [0, 1] cmpT) (.ofList [1, 0] cmpT) (by decide +kernel) ⟨⟨⟨⟨by decide +kernel⟩⟩⟩⟩
  have e1 : ∀ p, (TreeSet.ofList [0, 1] cmpT).min p = 1 := fun p => s2h_mk2 (β := fun _ => Unit) 2 1 0 1 () () .leaf .leaf p
  have e2 : ∀ p, (TreeSet.ofList [1, 0] cmpT).min p = 0 := fun p => s2h_mk2 (β := fun _ => Unit) 2 1 1 0 () () .leaf .leaf p
  rw [e1, e2] at this; exact absurd this (by decide)

-- `Std.TreeSet.Raw.Equiv.of_forall_contains_eq` (binder 4)
theorem s2_118 : ¬ (drop0% Std.TreeSet.Raw.Equiv.of_forall_contains_eq 4) := fun h => by
  have := h (cmp := cmpT) (t₁ := .ofList [1, 2] cmpT) (t₂ := .ofList [0, 1, 2] cmpT) (by twf) (by twf) (fun k => s2h_cont2 k)
  exact absurd this.1.1.1.1.length_eq (by decide +kernel)

-- `Std.TreeSet.Equiv.of_forall_contains_eq` (binder 4)
theorem s2_119 : ¬ (drop0% Std.TreeSet.Equiv.of_forall_contains_eq 4) := fun h => by
  have := h (cmp := cmpT) (t₁ := .ofList [1, 2] cmpT) (t₂ := .ofList [0, 1, 2] cmpT) (fun k => s2h_cont2 k)
  exact absurd this.1.1.1.1.length_eq (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.get_insertMany!_list_of_mem` (binder 13)
theorem s2_120 : (indep% Std.DTreeMap.Internal.Impl.Const.get_insertMany!_list_of_mem 13) := by
  intro α o β t _ hwf l k k' hk v hd hm
  rw [Std.DTreeMap.Internal.Impl.Const.contains_eq_isSome_get? (hwf.constInsertMany! (l := l)), Std.DTreeMap.Internal.Impl.Const.get?_insertMany!_list_of_mem hwf hk hd hm]; rfl

-- `Std.DTreeMap.Internal.Impl.get_insertMany!_list_of_mem` (binder 14)
theorem s2_121 : (indep% Std.DTreeMap.Internal.Impl.get_insertMany!_list_of_mem 14) := by
  intro α β o t _ _ hwf l k k' hk v hd hm
  show Impl.contains _ _ = true
  rw [Std.DTreeMap.Internal.Impl.contains_eq_isSome_get? (hwf.insertMany! (l := l)), Std.DTreeMap.Internal.Impl.get?_insertMany!_list_of_mem hwf hk hd hm]; rfl

-- `Std.DTreeMap.Internal.Impl.Const.get_insertMany!_list_of_mem` (binder 5)
theorem s2_122 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.get_insertMany!_list_of_mem 5) := fun h => by
  have := h (α := Nat) (β := Nat) (t := .inner 2 0 10 .leaf (.inner 1 0 30 .leaf .leaf)) (l := [(0, 20), (1, 21)]) (k := 0) (k' := 0) (v := 20) (h' := by decide +kernel) rfl (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.get_insertMany!_list_of_mem` (binder 6)
theorem s2_123 : ¬ (drop0% Std.DTreeMap.Internal.Impl.get_insertMany!_list_of_mem 6) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (t := .inner 2 0 10 .leaf (.inner 1 0 30 .leaf .leaf)) (l := [⟨0, 20⟩, ⟨1, 21⟩]) (k := 0) (k' := 0) (v := 20) (h' := by decide +kernel) rfl (by decide) (by decide)
  simp only [cast_eq] at this; exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.getD_diff!_of_contains_eq_false_right` (binder 5)
theorem s2_124 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.getD_diff!_of_contains_eq_false_right 5) := fun h => by
  have := h (α := OT) (β := Nat) (m₁ := (Std.DTreeMap.Const.ofList [((2 : OT), (12 : Nat)), (0, 10), (3, 13), (1, 11), (4, 14)] compare).inner) (m₂ := (Std.DTreeMap.Const.ofList [((1 : OT), (11 : Nat)), (3, 13), (0, 10), (2, 12)] compare).inner) (Std.DTreeMap.Const.ofList [((2 : OT), (12 : Nat)), (0, 10), (3, 13), (1, 11), (4, 14)] compare).wf (Std.DTreeMap.Const.ofList [((1 : OT), (11 : Nat)), (3, 13), (0, 10), (2, 12)] compare).wf (k := 1) (fallback := 99) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.getD_diff!_of_contains_eq_false_right` (binder 5)
theorem s2_125 : ¬ (drop0% Std.DTreeMap.Internal.Impl.getD_diff!_of_contains_eq_false_right 5) := fun h => by
  have := h (α := OT) (β := fun _ => Nat) (m₁ := (Std.DTreeMap.ofList ([⟨2, 12⟩, ⟨0, 10⟩, ⟨3, 13⟩, ⟨1, 11⟩, ⟨4, 14⟩] : List ((_ : OT) × Nat)) compare).inner) (m₂ := (Std.DTreeMap.ofList ([⟨1, 11⟩, ⟨3, 13⟩, ⟨0, 10⟩, ⟨2, 12⟩] : List ((_ : OT) × Nat)) compare).inner) (Std.DTreeMap.ofList ([⟨2, 12⟩, ⟨0, 10⟩, ⟨3, 13⟩, ⟨1, 11⟩, ⟨4, 14⟩] : List ((_ : OT) × Nat)) compare).wf (Std.DTreeMap.ofList ([⟨1, 11⟩, ⟨3, 13⟩, ⟨0, 10⟩, ⟨2, 12⟩] : List ((_ : OT) × Nat)) compare).wf (k := 1) (fallback := 99) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.getKey_eq` (binder 5)
theorem s2_126 : ¬ (drop0% Std.DTreeMap.Raw.getKey_eq 5) := fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (cmp := cmpH) (t := .ofList ([⟨1, 1⟩] : List ((_ : Nat) × Nat)) cmpH) (k := 0) (by twf) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKey_eq` (binder 5)
theorem s2_127 : ¬ (drop0% Std.TreeMap.Raw.getKey_eq 5) := fun h => by
  have := h (α := Nat) (β := Nat) (cmp := cmpH) (t := .ofList [(1, 1)] cmpH) (k := 0) (by twf) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.get_insertMany!_list_of_mem` (binder 4)
theorem s2_128 : ¬ (drop0% Std.DTreeMap.Internal.Impl.Const.get_insertMany!_list_of_mem 4) := fun h => by
  have := h (α := ON) (β := Nat) (t := .leaf) (l := [(⟨2⟩, 2), (⟨0⟩, 0)]) (k := ⟨0⟩) (k' := ⟨1⟩) (v := 0) (h' := by decide +kernel) Impl.WF.empty (by decide) (by decide) (by simp)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Equiv.filterMap` (binder 6)
theorem s2_129 : (drop% Std.DTreeMap.Raw.Equiv.filterMap 6) := by
  intro α β γ cmp t₁ t₂ _ he f; exact ⟨⟨s2h_fm_perm ⟨cmp⟩ f _ _ he.1.1⟩⟩

-- `Std.DTreeMap.Raw.Equiv.filterMap` (binder 7)
theorem s2_130 : (drop% Std.DTreeMap.Raw.Equiv.filterMap 7) := by
  intro α β γ cmp t₁ t₂ _ he f; exact ⟨⟨s2h_fm_perm ⟨cmp⟩ f _ _ he.1.1⟩⟩

-- `Std.TreeMap.Raw.Equiv.filterMap` (binder 6)
theorem s2_131 : (drop% Std.TreeMap.Raw.Equiv.filterMap 6) := by
  intro α β γ cmp t₁ t₂ _ he f; exact ⟨⟨⟨s2h_fm_perm ⟨cmp⟩ (fun a b => f a b) _ _ he.1.1.1⟩⟩⟩

-- `Std.TreeMap.Raw.Equiv.filterMap` (binder 7)
theorem s2_132 : (drop% Std.TreeMap.Raw.Equiv.filterMap 7) := by
  intro α β γ cmp t₁ t₂ _ he f; exact ⟨⟨⟨s2h_fm_perm ⟨cmp⟩ (fun a b => f a b) _ _ he.1.1.1⟩⟩⟩

-- `Std.DTreeMap.Internal.Impl.isEmpty_union!` (binder 5)
theorem s2_133 : (drop% Std.DTreeMap.Internal.Impl.isEmpty_union! 5) := by
  intro α β o m₁ m₂ h₁ h₂
  have b₁ := h₁.balanced; have b₂ := h₂.balanced
  unfold Impl.union!
  split
  · rename_i hs
    by_cases hz : m₂.size = 0
    · have e2 := s2h_leaf m₂ b₂ hz; have e1 := s2h_leaf m₁ b₁ (by omega); subst e1 e2; rfl
    · have ⟨hb, hsz⟩ := s2h_imn o m₂ b₂ m₁
      rw [(s2h_pos _ hb).2 (by omega), (s2h_pos m₂ b₂).2 (by omega)]; simp
  · rename_i hs
    have ⟨hb, hsz⟩ := s2h_im o m₁ b₁ m₂
    rw [(s2h_pos _ hb).2 (by omega), (s2h_pos m₁ b₁).2 (by omega)]; simp
