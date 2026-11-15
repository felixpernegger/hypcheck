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

/-! # Toolkit helpers collected from the merged probe and wave files (A0 and the A1 fold-in, 2026-11-09).
Each part below is the helper code of one file (verdicts removed, exact duplicates of earlier parts removed).
Namespaces are kept as in the source file: `Probe2`, `P3`, `P3R`, `S1`, `HashInstHand`, or top level. -/

/-! ## From `checks/Probe1Hand.lean` -/
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
namespace Probe1
open Std Std.DHashMap.Internal HashInstHand
abbrev E0 : Raw₀ Nat (fun _ => Nat) := Raw₀.emptyWithCapacity
abbrev E1 : Raw₀ Nat (fun _ => Nat) := E0.insert 0 5
theorem E0wf : E0.1.WF := Std.DHashMap.Raw.WF.emptyWithCapacity₀
theorem E1wf : E1.1.WF := Std.DHashMap.Raw.WF.insert₀ Std.DHashMap.Raw.WF.emptyWithCapacity₀
abbrev dm {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (hn : ∀ [EquivBEq α] [LawfulHashable α], False)
    (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) : DHashMap α β := ⟨⟨s, bs⟩, wf_vac hn _ h⟩
structure CM (α : Type) where
  n : Nat
  v : α
instance : Monad CM where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.n + (f x.v).n + 1, (f x.v).v⟩
@[simp] theorem r0_of_empty {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (h) :
    (⟨∅, h⟩ : Raw₀ α β) = ⟨⟨0, nil16⟩, by simp [nil16]⟩ := Subtype.ext dr_empty
theorem get?_eval {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] [Hashable α] {s : Nat}
    {bs : Array (AssocList α β)} {h : 0 < bs.size} (a : α) (hsz : Pow2 bs.size) :
    Raw₀.get? (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a = (bs[ix bs a]'(Nat.mod_lt _ h)).getCast? a := by
  unfold Raw₀.get?; dsimp only; rw [mkIdx_eq _ _ _ hsz]
  simp only [Array.ugetElem_eq_getElem, idx_lt h _ hsz]
-- model: BEq by halves, hash the number itself (EquivBEq, not LawfulHashable)
structure HN where n : Nat deriving DecidableEq, Inhabited
instance : BEq HN := ⟨fun a b => a.n / 2 == b.n / 2⟩
instance : Hashable HN := ⟨fun a => UInt64.ofNat a.n⟩
instance : EquivBEq HN where
  symm {a b} h := by simp_all [BEq.beq]
  trans {a b c} h₁ h₂ := by simp_all [BEq.beq]
  rfl {a} := by simp [BEq.beq]
theorem HN.notLH : ¬ LawfulHashable HN := fun h => by
  have := @LawfulHashable.hash_eq HN _ _ h ⟨0⟩ ⟨1⟩ (by decide)
  revert this; decide
abbrev NE : DHashMap.Raw Nat (fun _ => Nat) := ⟨0, #[]⟩
abbrev N1 : DHashMap.Raw Nat (fun _ => Nat) := (∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 5
theorem N1wf : N1.WF := Std.DHashMap.Raw.WF.insert Std.DHashMap.Raw.WF.empty
theorem al_getKey?_of_contains {α : Type u} {β : α → Type v} [BEq α] [Inhabited α] (l : AssocList α β) (a : α)
    (h : l.contains a = true) : l.getKey? a = some (l.getKey! a) := by
  induction l with
  | nil => simp [AssocList.contains] at h
  | cons k v t ih =>
    simp only [AssocList.getKey?, AssocList.getKey!, AssocList.contains] at *
    split <;> simp_all
theorem size_insertListIfNewUnit_ge {α : Type u} [BEq α] [Hashable α] (l : List α) :
    ∀ (m : Raw₀ α (fun _ => Unit)), m.1.size ≤ (Raw₀.Const.insertListIfNewUnitₘ m l).1.size := by
  induction l with
  | nil => intro m; exact Nat.le_refl _
  | cons hd tl ih =>
    intro m
    have := ih (m.insertIfNew hd ())
    have := (raw0_size_insertIfNew m hd ()).1
    show _ ≤ (Raw₀.Const.insertListIfNewUnitₘ (m.insertIfNew hd ()) tl).1.size
    omega
theorem ck_filterMap {α : Type u} {β : α → Type v} {γ : α → Type w} [BEq α] (f : (a : α) → β a → Option (γ a))
    (k : α) : ∀ l : List ((a : α) × β a),
    Std.Internal.List.containsKey k (l.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) = true →
      Std.Internal.List.containsKey k l = true
  | [], h => by simp at h
  | p :: t, h => by
    rw [List.filterMap_cons] at h
    rw [Std.Internal.List.containsKey_cons]
    cases hf : f p.1 p.2 with
    | none => simp only [hf, Option.map_none] at h; simp [ck_filterMap f k t h]
    | some c =>
      simp only [hf, Option.map_some, Std.Internal.List.containsKey_cons, Bool.or_eq_true] at h
      rcases h with h | h
      · simp [h]
      · simp [ck_filterMap f k t h]
theorem al_contains_filterMap {α : Type u} {β : α → Type v} {γ : α → Type w} [BEq α] [EquivBEq α]
    (f : (a : α) → β a → Option (γ a)) (k : α) (l : AssocList α β)
    (h : (l.filterMap f).contains k = true) : l.contains k = true := by
  rw [AssocList.contains_eq] at *
  rw [Std.Internal.List.containsKey_of_perm AssocList.toList_filterMap] at h
  exact ck_filterMap f k _ h
abbrev M1 : Raw₀ Nat (fun _ => Nat) := ((Raw₀.emptyWithCapacity : Raw₀ Nat (fun _ => Nat)).insert 0 5).insert 1 6
theorem M1wf : M1.1.WF := Std.DHashMap.Raw.WF.insert₀ (Std.DHashMap.Raw.WF.insert₀ Std.DHashMap.Raw.WF.emptyWithCapacity₀)
abbrev M2 : Raw₀ Nat (fun _ => Nat) := ⟨⟨0, #[b1 1 0, .nil]⟩, by decide⟩
theorem M2_contains (a : Nat) : M2.contains a = false := by
  rw [contains_eval a (by decide)]
  have h1 : ix (#[b1 1 0, .nil] : Array (AssocList Nat (fun _ => Nat))) 1 = 1 := by simp (disch := decide) [ix, scr_small]
  have hlt : ix (#[b1 1 0, .nil] : Array (AssocList Nat (fun _ => Nat))) a < 2 := Nat.mod_lt _ (by decide)
  have key : ∀ (i : Nat) (hi : i < 2), i = ix (#[b1 1 0, .nil] : Array (AssocList Nat (fun _ => Nat))) a →
      ((#[b1 1 0, .nil] : Array (AssocList Nat (fun _ => Nat)))[i]'(by simpa using hi)).contains a = false := by
    intro i hi hia
    match i, hi with
    | 0, _ =>
      by_cases ha : a = 1
      · subst ha; rw [h1] at hia; cases hia
      · simp [AssocList.contains] <;> omega
    | 1, _ => simp [AssocList.contains]
  exact key _ hlt rfl
theorem al_getKeyD_of_contains {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] (l : AssocList α β) (a fb : α)
    (h : l.contains a = true) : l.getKeyD a fb = a := by
  induction l with
  | nil => simp [AssocList.contains] at h
  | cons k v t ih =>
    simp only [AssocList.getKeyD, AssocList.contains] at *
    split
    · next hk => exact eq_of_beq hk
    · next hk =>
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact absurd h hk
      · exact ih h
theorem r0_getKeyD_of_contains {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β)
    (a fb : α) (h : m.contains a = true) : m.getKeyD a fb = a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKeyD; unfold Raw₀.contains at h; dsimp only at *
  exact al_getKeyD_of_contains _ _ _ h
theorem contains_expand_of_mem {α : Type u} {β : α → Type v} [BEq α] [ReflBEq α] [Hashable α] (s : Nat)
    (bs : Array (AssocList α β)) (h : 0 < bs.size) (p : (a : α) × β a) (hp : p ∈ toListModel bs) :
    Raw₀.contains ⟨⟨s, (Raw₀.expand ⟨bs, h⟩).1⟩, (Raw₀.expand ⟨bs, h⟩).2⟩ p.1 = true :=
  contains_of_mem_ihs s _ _ (ihs_expand ⟨bs, h⟩) p ((tlm_expand ⟨bs, h⟩).mem_iff.mpr hp)
theorem mem_tlm_uset_of {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (bs : Array (AssocList α β)) (i : USize)
    (hi : i.toNat < bs.size) (d : AssocList α β) (hd : ∀ q ∈ (bs[i.toNat]).toList, q ∈ d.toList)
    (p : (a : α) × β a) (hp : p ∈ toListModel bs) : p ∈ toListModel (bs.uset i d hi) := by
  obtain ⟨l, h₁, h₂, -⟩ := exists_bucket_of_uset bs i hi d
  rw [h₂.mem_iff]; rw [h₁.mem_iff] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact List.mem_append_left _ (hd p hp)
  · exact List.mem_append_right _ hp
abbrev P2m : Raw₀ Nat (fun _ => Nat) := ⟨⟨10, #[.nil, .cons 0 5 .nil]⟩, by decide⟩
theorem P2_contains : (P2m.insert 1 7).contains 0 = true := by
  unfold Raw₀.insert; dsimp only
  generalize hI : mkIdx _ _ (hash (1:Nat)) = I
  obtain ⟨i, hi⟩ := I
  have hi1 : i.toNat = 1 := by
    have := congrArg (fun x => x.1.toNat) hI
    simp only at this
    rw [mkIdx_toNat' _ _ _ (by decide)] at this
    simp (disch := decide) [scr_small] at this
    omega
  dsimp only
  split
  · rename_i hc
    simp [Array.ugetElem_eq_getElem, hi1, AssocList.contains] at hc
  · unfold Raw₀.expandIfNecessary; dsimp only
    rw [if_neg (by simp; decide)]
    exact contains_expand_of_mem 11 _ _ ⟨0, 5⟩ (mem_tlm_uset_of _ _ _ _
      (fun q hq => by simp only [Array.ugetElem_eq_getElem, AssocList.toList] at hq ⊢; exact List.mem_cons_of_mem _ hq)
      _ (by simp [toListModel]))
abbrev P39m : Raw₀ NS (fun _ => Nat) := ⟨⟨10, #[.nil, b1 2 0]⟩, by decide⟩
theorem P39_contains : (P39m.insertIfNew 3 0).contains 2 = true := by
  unfold Raw₀.insertIfNew; dsimp only
  generalize hI : mkIdx _ _ (hash (3:NS)) = I
  obtain ⟨i, hi⟩ := I
  have hi1 : i.toNat = 0 := by
    have := congrArg (fun x => x.1.toNat) hI
    simp only at this
    rw [mkIdx_toNat' _ _ _ (by decide)] at this
    simp (disch := decide) [scr_small] at this
    omega
  dsimp only
  split
  · rename_i hc
    simp [Array.ugetElem_eq_getElem, hi1, AssocList.contains] at hc
  · unfold Raw₀.expandIfNecessary; dsimp only
    rw [if_neg (by simp; decide)]
    exact contains_expand_of_mem 11 _ _ ⟨2, 0⟩ (mem_tlm_uset_of _ _ _ _
      (fun q hq => by simp only [Array.ugetElem_eq_getElem, AssocList.toList] at hq ⊢; exact List.mem_cons_of_mem _ hq)
      _ (by simp [toListModel]))
theorem al_contains_congr {α : Type u} {β : α → Type v} [BEq α] [PartialEquivBEq α] (l : AssocList α β) {a b : α}
    (h : (a == b) = true) : l.contains a = l.contains b := by
  induction l with
  | nil => rfl
  | cons k v t ih => simp only [AssocList.contains]; rw [BEq.congr_right h, ih]
theorem r0_contains_congr {α : Type u} {β : α → Type v} [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (m : Raw₀ α β) {a b : α} (h : (a == b) = true) : m.contains a = m.contains b := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.contains; dsimp only
  rw [hash_eq h]
  exact al_contains_congr _ h
theorem r0_exists_of_contains {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (h : m.contains a = true) : ∃ p ∈ toListModel m.1.buckets, (p.1 == a) = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.contains at h; dsimp only at h ⊢
  revert h
  generalize mkIdx bs.size hb (hash a) = I
  obtain ⟨i, hi⟩ := I
  intro h
  simp only [Array.ugetElem_eq_getElem] at h
  rw [AssocList.contains_eq, Std.Internal.List.containsKey_eq_true_iff_exists_mem] at h
  obtain ⟨p, hp, hpa⟩ := h
  exact ⟨p, mem_tlm_of_bucket bs _ _ p hp, hpa⟩
theorem eraseList_contains {α : Type u} {β : α → Type v} [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (k : α) : ∀ (ks : List α) (m : Raw₀ α β), m.1.WF → ((∃ x ∈ ks, (x == k) = true) ∨ m.contains k = false) →
      (m.eraseListₘ ks).contains k = false
  | [], m, _, h => by
    rcases h with ⟨x, hx, _⟩ | h
    · cases hx
    · exact h
  | x :: xs, m, hw, h => by
    show (Raw₀.eraseListₘ (m.erase x) xs).contains k = false
    apply eraseList_contains k xs (m.erase x) (Std.DHashMap.Raw.WF.erase₀ hw)
    rcases h with ⟨y, hy, hyk⟩ | h
    · rcases List.mem_cons.mp hy with rfl | hy
      · right; rw [Raw₀.contains_erase _ hw, hyk]; rfl
      · left; exact ⟨y, hy, hyk⟩
    · right; rw [Raw₀.contains_erase _ hw, h]; simp
end Probe1

/-! ## From `checks/Probe2Hand.lean` -/
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
namespace Probe2
open Std Std.PRange
-- Z: Option whose bind always fails; pure a >>= f = none, so not lawful (from ItMonadIterHand)
def Z (α : Type) : Type := Option α
instance Z.monad : Monad Z where
  pure a := (some a : Option _)
  map f x := Option.map f (x : Option _)
  bind _ _ := (none : Option _)
theorem Z.not_lawful : ¬ LawfulMonad Z := fun h => by
  have := @pure_bind Z _ h _ _ 0 (fun a => (some a : Option Nat))
  cases this
-- M0: one point, succMany? constantly none; every order relation empty (from RangeDepAHand)
inductive M0 | pt deriving DecidableEq
instance : UpwardEnumerable M0 := { succ? := fun a => some a, succMany? := fun _ _ => none }
instance : LT M0 := ⟨fun _ _ => False⟩
instance : DecidableLT M0 := fun _ _ => isFalse id
instance : Least? M0 := ⟨some .pt⟩
instance : LawfulUpwardEnumerableLT M0 := ⟨fun _ _ => ⟨False.elim, fun ⟨_, h⟩ => nomatch h⟩⟩
instance : Rxo.IsAlwaysFinite M0 := ⟨fun _ _ => ⟨0, trivial⟩⟩
theorem M0.not_LUE : ¬ LawfulUpwardEnumerable M0 := fun h => nomatch h.succMany?_zero .pt
end Probe2
namespace Probe2
open Std Std.Iterators Std.Iterators.Types
-- well-founded relations are irreflexive (from OpABHand)
theorem wf_irrefl {α : Sort u} {r : α → α → Prop} (h : WellFounded r) (a : α) : ¬ r a a := by
  have := h.apply a
  induction this with
  | intro x _ ih => exact fun hx => ih x hx hx
theorem not_finite_of_skip {α β : Type} {m : Type → Type} [Iterator α m β]
    (it : IterM (α := α) m β) (h : it.IsPlausibleStep (.skip it)) : ¬ Finite α m :=
  fun hf => wf_irrefl hf.wf it ⟨_, rfl, h⟩
-- LP: an iterator that skips to itself (from OpABHand)
structure LP (β : Type) where u : Unit
instance LP.inst {m : Type → Type} [Pure m] {β : Type} : Iterator (LP β) m β where
  IsPlausibleStep it s := s = .skip it
  step it := pure (.deflate ⟨.skip it, rfl⟩)
def LP.it {m : Type → Type} {β : Type} : IterM (α := LP β) m β := ⟨⟨()⟩⟩
end Probe2
namespace Probe2
open Std
-- OL: compare always lt, == always false (lawful BEq-compare link, not oriented)
structure OL where n : Nat deriving DecidableEq, Inhabited
instance : Ord OL := ⟨fun _ _ => .lt⟩
instance : BEq OL := ⟨fun _ _ => false⟩
instance : Std.LawfulBEqOrd OL := ⟨by intro a b; show Ordering.lt = .eq ↔ false = true; simp⟩
-- R3: rock-paper-scissors on n % 3 (0 < 1 < 2 < 0); == is equality mod 3; oriented, not transitive
structure R3 where n : Nat deriving DecidableEq, Inhabited
def r3cmp (a b : Nat) : Ordering :=
  if a % 3 = b % 3 then .eq else if b % 3 = (a % 3 + 1) % 3 then .lt else .gt
instance : Ord R3 := ⟨fun a b => r3cmp a.n b.n⟩
instance : BEq R3 := ⟨fun a b => a.n % 3 == b.n % 3⟩
instance : Std.LawfulBEqOrd R3 := ⟨by
  intro a b; show r3cmp a.n b.n = .eq ↔ (a.n % 3 == b.n % 3) = true
  unfold r3cmp; split <;> simp_all; split <;> simp⟩
end Probe2
namespace Probe2
open Std Std.DHashMap.Internal HashInstHand
universe w
section Free
variable {α : Type u} {β : α → Type v}
export HashInstHand (mem_tlm_of_bucket)
export HashInstHand (falseBEq)
export HashInstHand (tlm_expandIfNecessary)
export HashInstHand (mem_tlm_uset)
export HashInstHand (mem_tlm_set)
export HashInstHand (mem_tlm_insertIfNew)
export HashInstHand (tlm_insertListIfNewUnit)
export HashInstHand (hs_ofList_raw)
export HashInstHand (hs_ofList_keys)
export HashInstHand (mem_of_getKey)
export HashInstHand (raw0_getKey_mem)
export HashInstHand (pw_unique)
theorem dm_getKey_eq [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (h : a ∈ m) :
    ∃ hb hc, m.getKey a h = Raw₀.getKey ⟨m.1, hb⟩ a hc := ⟨_, _, rfl⟩
end Free
end Probe2
namespace Probe2
open Std Std.DHashMap.Internal
theorem assoc_getKeyD {α : Type u} {β : α → Type v} [BEq α] (l : AssocList α β) (a fb : α) :
    l.getKeyD a fb = (l.getKey? a).getD fb := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    simp only [AssocList.getKeyD, AssocList.getKey?]
    split <;> simp_all
end Probe2
namespace Probe2
open Std Std.DHashMap.Internal
universe w
section Gen
variable {α : Type u} {β : α → Type v}
export HashInstHand (mkIdx_val_congr)
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
end Probe2
namespace Probe2
open Std Std.DHashMap.Internal
section GenC
variable {α : Type u} {γ : Type v}
theorem cmodify_gen [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α (fun _ => γ))} {h : 0 < bs.size}
    (a : α) (f : γ → γ) :
    Raw₀.Const.modify (⟨⟨s, bs⟩, h⟩ : Raw₀ α (fun _ => γ)) a f =
      if (bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).contains a then
        ⟨⟨s, bs.set (mkIdx bs.size h (hash a)).1.toNat
          (AssocList.Const.modify a f (bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2))
          (mkIdx bs.size h (hash a)).2⟩, by simpa using h⟩
      else ⟨⟨s, bs⟩, h⟩ := by
  unfold Raw₀.Const.modify; simp only [Array.ugetElem_eq_getElem, Array.uset_eq_set, Array.set_set]
theorem cget!_gen [BEq α] [Hashable α] [Inhabited γ] {s : Nat} {bs : Array (AssocList α (fun _ => γ))}
    {h : 0 < bs.size} (a : α) :
    Raw₀.Const.get! (⟨⟨s, bs⟩, h⟩ : Raw₀ α (fun _ => γ)) a =
      (bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).get! a := rfl
theorem cget?_gen [BEq α] [Hashable α] {s : Nat} {bs : Array (AssocList α (fun _ => γ))}
    {h : 0 < bs.size} (a : α) :
    Raw₀.Const.get? (⟨⟨s, bs⟩, h⟩ : Raw₀ α (fun _ => γ)) a =
      (bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).get? a := by
  unfold Raw₀.Const.get?; simp only [Array.ugetElem_eq_getElem]
theorem assoc_cget!_modify [BEq α] [EquivBEq α] [Inhabited γ] (l : AssocList α (fun _ => γ)) (k : α)
    (f : γ → γ) : (AssocList.Const.modify k f l).get! k = ((l.get? k).map f).get! := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.Const.modify, AssocList.get?]
    cases hk : (k' == k)
    · simp only [Bool.false_eq_true, ite_false, cond_false, AssocList.get!, hk]; exact ih
    · simp only [hk, ite_true, cond_true, AssocList.get!, BEq.refl, Option.map_some, Option.get!_some]
theorem assoc_cget?_none [BEq α] (l : AssocList α (fun _ => γ)) (k : α) (h : l.contains k = false) :
    l.get? k = none := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.get?, h.1, cond_false]; exact ih h.2
theorem assoc_cget!_none [BEq α] [Inhabited γ] (l : AssocList α (fun _ => γ)) (k : α) (h : l.contains k = false) :
    l.get! k = default := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.get!, h.1, cond_false]; exact ih h.2
theorem raw0_cget!_cmodify [BEq α] [Hashable α] [EquivBEq α] [Inhabited γ] (m : Raw₀ α (fun _ => γ)) (k : α)
    (f : γ → γ) : Raw₀.Const.get! (Raw₀.Const.modify m k f) k = ((Raw₀.Const.get? m k).map f).get! := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [cmodify_gen, cget?_gen]
  split
  · rw [cget!_gen]; simp only [mkIdx_set_toNat, Array.getElem_set_self]; exact assoc_cget!_modify _ _ _
  · rename_i hc
    rw [cget!_gen, assoc_cget?_none _ _ (by simpa using hc), assoc_cget!_none _ _ (by simpa using hc)]; rfl
end GenC
end Probe2
namespace Probe2
open Std Std.Internal.List
section MinMax
variable {α : Type u} {β : α → Type v}
theorem minKey?_mem' [Ord α] [TransOrd α] (L : List ((a : α) × β a)) (w : α) (h : minKey? L = some w) :
    w ∈ L.map Sigma.fst := by
  induction L generalizing w with
  | nil => rw [(minKey?_eq_none_iff_isEmpty (l := ([] : List ((a : α) × β a)))).mpr rfl] at h; cases h
  | cons e t ih =>
    rw [minKey?_cons] at h
    cases ht : minKey? t with
    | none => simp only [ht, Option.some.injEq] at h; subst h; simp
    | some w' =>
      simp only [ht, Option.some.injEq] at h
      split at h
      · subst h; simp
      · subst h; exact List.mem_cons_of_mem _ (ih w' ht)
theorem minKey?_le' [Ord α] [TransOrd α] (L : List ((a : α) × β a)) (w : α) (h : minKey? L = some w) :
    ∀ x ∈ L.map Sigma.fst, (compare w x).isLE := by
  induction L generalizing w with
  | nil => rw [(minKey?_eq_none_iff_isEmpty (l := ([] : List ((a : α) × β a)))).mpr rfl] at h; cases h
  | cons e t ih =>
    rw [minKey?_cons] at h
    intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    cases ht : minKey? t with
    | none =>
      simp only [ht, Option.some.injEq] at h; subst h
      rcases hx with rfl | hx
      · simp [ReflCmp.compare_self]
      · simp [minKey?_eq_none_iff_isEmpty] at ht; subst ht; simp at hx
    | some w' =>
      simp only [ht, Option.some.injEq] at h
      split at h
      · rename_i hle; subst h
        rcases hx with rfl | hx
        · simp [ReflCmp.compare_self]
        · exact TransCmp.isLE_trans hle (ih w' ht x hx)
      · rename_i hle; subst h
        rcases hx with rfl | hx
        · rw [OrientedCmp.lt_of_not_isLE hle]; rfl
        · exact ih w' ht x hx
theorem keys_replaceEntry [BEq α] (k : α) (v : β k) (l : List ((a : α) × β a)) :
    ∀ x ∈ l.map Sigma.fst, x ∈ (replaceEntry k v l).map Sigma.fst ∨
      ((x == k) = true ∧ k ∈ (replaceEntry k v l).map Sigma.fst) := by
  induction l with
  | nil => simp
  | cons e t ih =>
    obtain ⟨k', v'⟩ := e
    intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    rw [replaceEntry_cons]
    split
    · rename_i hb
      rcases hx with rfl | hx
      · exact Or.inr ⟨hb, by simp⟩
      · exact Or.inl (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hx)
    · rcases hx with rfl | hx
      · exact Or.inl (by simp)
      · rcases ih x hx with h | ⟨hb, hk⟩
        · exact Or.inl (by simp only [List.map_cons, List.mem_cons]; exact Or.inr h)
        · exact Or.inr ⟨hb, by simp only [List.map_cons, List.mem_cons]; exact Or.inr hk⟩
end MinMax
end Probe2
namespace Probe2
open Std Std.DHashMap.Internal
theorem raw0_contains_tlm {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (h : m.contains a = true) : Std.Internal.List.containsKey a (toListModel m.1.buckets) = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen, AssocList.contains_eq] at h
  obtain ⟨p, hp, hpa⟩ := Std.Internal.List.containsKey_eq_true_iff_exists_mem.mp h
  exact Std.Internal.List.containsKey_eq_true_iff_exists_mem.mpr ⟨p, mem_tlm_of_bucket bs _ _ p hp, hpa⟩
end Probe2
open Lean Elab Tactic Meta in
/-- Unfold one step of the private `Raw₀.expand.go` (hash map resize loop) in the goal. -/
elab "unfold_expand_go" : tactic => do
  let n := (Name.mkNum `_private.Std.Data.DHashMap.Internal.Defs 0) ++ `Std.DHashMap.Internal.Raw₀.expand.go
  liftMetaTactic fun g => do return [(← unfoldTarget g n)]
open HashInstHand Std Std.DHashMap.Internal in
/-- `hm_eval` through one resize: evaluates `expandIfNecessary` on a literal bucket array (Pow2 sizes). -/
macro "hm_expand" : tactic => `(tactic| (
  hm_eval
  simp (config := {decide := true}) only [Raw₀.expandIfNecessary, Raw₀.expand, ite_false]
  repeat (unfold_expand_go; simp (config := {decide := true}) (disch := first | decide | simp) only [dite_true,
    dite_false, Array.size_set, List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_irrefl,
    Array.getElem_set, AssocList.foldl, AssocList.foldlM, Raw₀.reinsertAux, mkIdx_eq])
  simp (disch := first | decide | simp) [Array.propagateMark, Array.replicate, List.replicate, AssocList.foldlM,
    mkIdx_eq, scr_small, Array.uset_eq_set, idx_lt]
  hm_eval))
open Probe2 HashInstHand
open Std Std.DHashMap.Internal
namespace Probe2V
end Probe2V

/-! ## From `checks/Probe3Hand.lean` -/
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

/-! ## From `checks/Probe4Hand.lean` -/
open Std HashInstHand Std.DTreeMap.Internal
-- tree WF closer for ofList / insertMany literals
macro "twf" : tactic => `(tactic| ((repeat (first | apply Std.TreeSet.Raw.WF.mk | apply Std.TreeMap.Raw.WF.mk | apply Std.DTreeMap.Raw.WF.mk)); (first | exact @Std.DTreeMap.Internal.Impl.WF.insertMany _ _ (id _) _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact @Std.DTreeMap.Internal.Impl.WF.constInsertMany _ (id _) _ _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact @Std.DTreeMap.Internal.Impl.WF.constInsertManyIfNewUnit _ (id _) _ (id _) _ _ _ (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _) | exact (@Std.DTreeMap.Internal.Impl.WF.empty _ (id _) _))))
export P3 (cmpG)
def cmpGt (_ _ : Nat) : Ordering := .gt
def cmpR (a b : Nat) : Ordering := if a % 3 = b % 3 then .eq else if b % 3 = (a+1) % 3 then .lt else .gt
def cmp01 (a b : Nat) : Ordering := if a = 0 ∧ b = 1 then .eq else compare a b
section P4Rem
open Std.DTreeMap.Internal
universe u_a v_b
variable {α : Type u_a} {β : α → Type v_b}
-- helper: maxKeyD does not depend on the fallback for a nonempty tree
theorem p4h_maxKeyD_fb (t : Impl α β) (h : t.isEmpty = false) (a b : α) : t.maxKeyD a = t.maxKeyD b := by
  induction t with
  | leaf => simp [Impl.isEmpty] at h
  | inner sz k v l r ihl ihr =>
    cases r with
    | leaf => simp [Impl.maxKeyD]
    | inner sz' k' v' l' r' => simp only [Impl.maxKeyD]; exact ihr rfl
-- helper
theorem p4h_maxKeyD_inner (sz : Nat) (k : α) (v : β k) (l r : Impl α β) (fb : α) :
    (Impl.inner sz k v l r).maxKeyD fb = r.maxKeyD k := by
  cases r with
  | leaf => simp [Impl.maxKeyD]
  | inner => simp only [Impl.maxKeyD]; exact p4h_maxKeyD_fb _ rfl _ _
-- helper
theorem p4h_maxKeyD_modify [Ord α] [LawfulEqOrd α] (k : α) (f : β k → β k) (t : Impl α β) (fb : α) :
    (t.modify k f).maxKeyD fb = t.maxKeyD fb := by
  induction t generalizing fb with
  | leaf => rfl
  | inner sz k' v' l r ihl ihr =>
    simp only [Impl.modify]
    split
    · simp only [p4h_maxKeyD_inner]
    · simp only [p4h_maxKeyD_inner]; exact ihr _
    · rename_i h; have := compare_eq_iff_eq.mp h; subst this; simp only [p4h_maxKeyD_inner]
-- helper
theorem p4h_maxKey?_isSome (t : Impl α β) : t.maxKey?.isSome = !t.isEmpty := by
  induction t with
  | leaf => simp [Impl.maxKey?, Impl.isEmpty]
  | inner sz k v l r ihl ihr =>
    cases r with
    | leaf => simp [Impl.maxKey?, Impl.isEmpty]
    | inner => simp only [Impl.maxKey?]; exact ihr
-- helper
theorem p4h_isEmpty_cmodify {β : Type v_b} [Ord α] (k : α) (f : β → β) (t : Impl α (fun _ => β)) :
    (Impl.Const.modify k f t).isEmpty = t.isEmpty := by
  cases t with
  | leaf => rfl
  | inner sz k' v' l r => simp only [Impl.Const.modify]; split <;> rfl
-- helper
theorem p4h_getKey!_of_contains [Ord α] [Inhabited α] (t : Impl α β) (a : α) (h : t.contains a = false) :
    t.getKey! a = default := by
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.getKey!]
    split <;> simp_all
-- helper
theorem p4h_isSome_getKey? [Ord α] (t : Impl α β) (a : α) : (t.getKey? a).isSome = t.contains a := by
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    simp only [Impl.contains, Impl.getKey?]
    split <;> simp_all
end P4Rem
section P4Diff
open Std.DTreeMap.Internal
universe u_c v_d
variable {α : Type u_c} {β : α → Type v_d}
-- helper: search-based contains respects cmp-equality on any tree
theorem p4h_contains_congr [Ord α] [Std.TransOrd α] (t : Impl α β) {a b : α} (hab : compare a b = .eq) :
    t.contains a = t.contains b := by
  induction t with
  | leaf => rfl
  | inner sz q v l r ihl ihr =>
    simp only [Impl.contains]
    rw [Std.TransCmp.congr_left hab]
    split <;> first | rfl | assumption
-- helper: a key found by search occurs in the entry list
theorem p4h_contains_mem [Ord α] [Std.OrientedOrd α] (t : Impl α β) {k : α} (h : t.contains k = true) :
    ∃ e ∈ t.toListModel, compare e.1 k = .eq := by
  induction t with
  | leaf => simp [Impl.contains] at h
  | inner sz q v l r ihl ihr =>
    simp only [Impl.contains] at h
    split at h
    · obtain ⟨e, he, hc⟩ := ihl h; exact ⟨e, by simp [Impl.toListModel_inner, he], hc⟩
    · obtain ⟨e, he, hc⟩ := ihr h; exact ⟨e, by simp [Impl.toListModel_inner, he], hc⟩
    · rename_i hq; exact ⟨⟨q, v⟩, by simp [Impl.toListModel_inner], Std.OrientedCmp.eq_symm hq⟩
-- helper: erasing a list of keys from a well-formed tree
theorem p4h_foldl_erase [Ord α] [Std.TransOrd α] (l : List ((a : α) × β a)) (acc : Impl α β) (hacc : acc.WF) {k : α}
    (h : acc.contains k = false ∨ ∃ e ∈ l, compare e.1 k = .eq) :
    (l.foldl (fun acc p => acc.erase! p.1) acc).contains k = false := by
  induction l generalizing acc with
  | nil => simpa using h
  | cons e es ih =>
    simp only [List.foldl_cons]
    apply ih _ hacc.erase!
    rw [Impl.contains_erase! hacc]
    by_cases he : compare e.1 k = .eq
    · left; simp [he]
    · rcases h with h | ⟨e', he', hc⟩
      · left; simp [h]
      · rcases List.mem_cons.1 he' with rfl | he'
        · exact absurd hc he
        · right; exact ⟨e', he', hc⟩
-- helper: the difference never contains a key of the right tree (right tree arbitrary)
theorem p4h_diff!_contains [Ord α] [Std.TransOrd α] (m₁ m₂ : Impl α β) (h₁ : m₁.WF) {k : α}
    (hk : m₂.contains k = true) : (m₁.diff! m₂).contains k = false := by
  unfold Impl.diff!
  split
  · apply Bool.eq_false_iff.2
    intro hc
    obtain ⟨hm, hf⟩ := (Impl.contains_filter!_key_iff (f := fun a => !m₂.contains a) h₁).1 hc
    rw [p4h_contains_congr m₂ (Impl.compare_getKey_self h₁ hm), hk] at hf
    exact Bool.false_ne_true hf
  · rw [Impl.eraseManyEntries!_impl_eq_foldl, Impl.foldl_eq_foldl]
    obtain ⟨e, he, hc⟩ := p4h_contains_mem m₂ hk
    exact p4h_foldl_erase _ _ h₁ (Or.inr ⟨e, he, hc⟩)
-- helper: lookups on a tree that does not contain the key (any tree)
theorem p4h_cget!_of_contains {γ : Type v_d} [Ord α] [Inhabited γ] (t : Impl α (fun _ => γ)) (a : α)
    (h : t.contains a = false) : Impl.Const.get! t a = default := by
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.Const.get!]
    split <;> simp_all
end P4Diff

/-! ## From `checks/Stem1Hand.lean` -/
namespace Probe2
open Std Std.DHashMap.Internal HashInstHand
universe u v
variable {α : Type u} {β : Type v}
section
variable {γ : α → Type v} [BEq α] [Hashable α]
end
end Probe2
universe u v
namespace Probe2
open Std Std.DHashMap.Internal
universe w
section Gen
variable {α : Type u} {β : α → Type v}
export HashInstHand (mkIdx_val_congr)
end Gen
namespace Probe2
open Std Std.DHashMap.Internal
section GenC
variable {α : Type u} {γ : Type v}
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
end Stem1V
end Probe2

/-! ## From `checks/Stem2Hand.lean` -/
open Std HashInstHand Std.DTreeMap.Internal
export P3 (cmpG)
export P3 (CM)
export P3 (OB)
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
export P3 (cmpN)
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

/-! ## From `checks/Stem3Hand.lean` -/
open Std HashInstHand Std.DTreeMap.Internal
open Std.DHashMap.Internal
macro "wfx" : tactic => `(tactic| first | twf | exact DTreeMap.wf _)
-- cmpT and OT agree with their DecidableEq BEq
instance : Std.LawfulBEqCmp cmpT where
  compare_eq_iff_beq {a b} := by simp [cmpT]
instance : Std.LawfulBEqOrd OT where
  compare_eq_iff_beq {a b} := by cases a; cases b; simp [compare, cmpT]
-- structural (kernel-reducible) models of Impl.minKey? and Impl.maxKeyD
def mnD {α : Type u} {β : α → Type v} : Impl α β → α → α
  | .leaf, fb => fb
  | .inner _ k _ l _, _ => mnD l k
def mk? {α : Type u} {β : α → Type v} : Impl α β → Option α
  | .leaf => none
  | .inner _ k _ l _ => some (mnD l k)
theorem mk?_eq {α : Type u} {β : α → Type v} (t : Impl α β) : t.minKey? = mk? t := by
  induction t with
  | leaf => simp [Impl.minKey?, mk?]
  | inner _ k _ l r ihl _ => cases l <;> simp_all [Impl.minKey?, mk?, mnD]
def mxD {α : Type u} {β : α → Type v} : Impl α β → α → α
  | .leaf, fb => fb
  | .inner _ k _ _ r, _ => mxD r k
theorem mxD_eq {α : Type u} {β : α → Type v} (t : Impl α β) (fb : α) : t.maxKeyD fb = mxD t fb := by
  induction t generalizing fb with
  | leaf => simp [Impl.maxKeyD, mxD]
  | inner _ k _ l r _ ihr => cases r <;> simp_all [Impl.maxKeyD, mxD]
-- removable helpers: isEmpty is structural, and get?/get!/contains follow one search path
theorem i_maxD {α : Type u} {β : α → Type v} (t : Impl α β) (he : t.isEmpty = true) (fb : α) :
    t.maxKeyD fb = fb := by
  cases t with | leaf => simp [Impl.maxKeyD] | inner => cases he
theorem i_minS {α : Type u} {β : α → Type v} (t : Impl α β) : t.minKey?.isSome = !t.isEmpty := by
  induction t with
  | leaf => simp [Impl.minKey?, Impl.isEmpty]
  | inner _ k _ l r ihl _ => cases l <;> simp_all [Impl.minKey?, Impl.isEmpty]
theorem i_getE {α : Type u} {β : Type v} {_ : Ord α} (t : Impl α (fun _ => β)) (he : t.isEmpty = true) (a : α) :
    Impl.Const.get? t a = none := by
  cases t with | leaf => rfl | inner => cases he
theorem i_getD! {α : Type u} {β : Type v} {_ : Ord α} [Inhabited β] (k : α) (t : Impl α (fun _ => β))
    (h : Impl.contains k t = false) : Impl.Const.get! t k = default := by
  induction t with
  | leaf => simp [Impl.Const.get!, panicWithPosWithDecl, panicWithPos, panic, panicCore]
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.Const.get!]
    split <;> simp_all
-- min?_keys: the key min fold and the entry min fold agree under LawfulOrderOrd and a left-leaning min
theorem mk_fold {α : Type u} {β : α → Type v} [Ord α] [LE α] [Min α] [LawfulOrderOrd α] [LawfulOrderLeftLeaningMin α]
    (as : List ((a : α) × β a)) (a : (a : α) × β a) :
    (as.foldl (fun x y => if (compare x.1 y.1).isLE then x else y) a).1 = (as.map Sigma.fst).foldl min a.1 := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, List.map_cons]; rw [ih]; congr 1
    split <;> rename_i h
    · exact (LawfulOrderLeftLeaningMin.min_eq_left _ _ ((LawfulOrderOrd.isLE_compare _ _).1 h)).symm
    · exact (LawfulOrderLeftLeaningMin.min_eq_right _ _ (fun h' => h ((LawfulOrderOrd.isLE_compare _ _).2 h'))).symm
-- one-bucket raw map with key k and size field 0: insertManyIfNewUnit [k] keeps it empty when k == k
theorem imu0 {α : Type u} [BEq α] [Hashable α] (k : α) (hk : (k == k) = true)
    (h : 0 < (#[AssocList.cons k () .nil] : Array (AssocList α (fun _ => Unit))).size) :
    (Raw₀.Const.insertManyIfNewUnit (⟨⟨0, #[.cons k () .nil]⟩, h⟩ : Raw₀ α (fun _ => Unit)) [k]).1.1.isEmpty = true := by
  show (Raw₀.insertIfNew (⟨⟨0, #[.cons k () .nil]⟩, h⟩ : Raw₀ α (fun _ => Unit)) k ()).1.isEmpty = true
  rw [insertIfNew_eval _ _ (Or.inl rfl)]
  simp [hk]
  rfl

/-! ## From `checks/W1c0Hand.lean` -/
/-! # W1c0 helpers -/
/-- `hm_expand` after an evaluation pass that already ran (`hm_eval_raw`/`hm_eval`): one resize. -/
macro "w1c0_expand" : tactic => `(tactic| (
  simp (config := {decide := true}) only [Raw₀.expandIfNecessary, Raw₀.expand, ite_false]
  repeat (unfold_expand_go; simp (config := {decide := true}) (disch := first | decide | simp) only [dite_true,
    dite_false, Array.size_set, List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_irrefl,
    Array.getElem_set, AssocList.foldl, AssocList.foldlM, Raw₀.reinsertAux, mkIdx_eq])
  simp (disch := first | decide | simp) [Array.propagateMark, Array.replicate, List.replicate, AssocList.foldlM,
    mkIdx_eq, scr_small, Array.uset_eq_set, idx_lt]
  hm_eval))
section W1c0Raw
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
theorem w1c0_drc_insertMany_lit (s : Nat) (bs : Array (AssocList α (fun _ => β))) (h : 0 < bs.size) (l : List (α × β)) :
    DHashMap.Raw.Const.insertMany (⟨s, bs⟩ : Std.DHashMap.Raw α (fun _ => β)) l = (Raw₀.Const.insertMany ⟨⟨s, bs⟩, h⟩ l).1 := by
  simp [DHashMap.Raw.Const.insertMany, h]
theorem w1c0_dru_insertMany_lit (s : Nat) (bs : Array (AssocList α (fun _ => Unit))) (h : 0 < bs.size) (l : List α) :
    DHashMap.Raw.Const.insertManyIfNewUnit (⟨s, bs⟩ : Std.DHashMap.Raw α (fun _ => Unit)) l =
      (Raw₀.Const.insertManyIfNewUnit ⟨⟨s, bs⟩, h⟩ l).1 := by
  simp [DHashMap.Raw.Const.insertManyIfNewUnit, h]
end W1c0Raw
/-- `hm_eval_raw` that also unfolds the `Const`/`HashMap.Raw`/`HashSet.Raw` bulk insertions. -/
macro "w1c0_raw" : tactic => `(tactic| (
  try simp only [HashMap.Raw.insertMany, HashSet.Raw.insertMany, HashMap.Raw.insertManyIfNewUnit, HashMap.Raw.size,
    HashSet.Raw.size, HashMap.Raw.getKey, HashMap.Raw.mem_iff_contains, HashSet.Raw.mem_iff_contains, HashMap.Raw.contains,
    HashSet.Raw.contains, hmr_empty, hsr_empty, HashMap.Raw.insert, HashSet.Raw.insert, HashMap.Raw.insertIfNew]
  simp (disch := first | decide | simp [nil16]) only [Std.DHashMap.Raw.ofList, Std.DHashMap.Raw.mem_iff_contains,
    dr_empty, dr_insert_lit, dr_insertIfNew_lit, dr_contains_lit, dr_erase_lit, dr_insertMany_lit,
    w1c0_drc_insertMany_lit, w1c0_dru_insertMany_lit]
  try simp only [Raw₀.Const.insertMany, Raw₀.Const.insertManyIfNewUnit]
  hm_eval))
/-- `CZ`: lawful equality, constant hash 0 (`EquivBEq` ✓, `LawfulHashable` ✓): every key belongs in one bucket. -/
structure CZ where n : Nat deriving DecidableEq, Inhabited
instance : Hashable CZ := ⟨fun _ => 0⟩
instance : LawfulHashable CZ := ⟨fun _ _ _ => rfl⟩
@[simp] theorem CZ.hash_def (a : CZ) : hash a = 0 := rfl
/-- `HZ`: `a == b ↔ a/2 = b/2` (`EquivBEq` ✓), hash 1 for 5 and 0 otherwise (`LawfulHashable` ✗: 4 == 5). -/
structure HZ where n : Nat deriving DecidableEq, Inhabited
instance : BEq HZ := ⟨fun a b => a.n / 2 == b.n / 2⟩
instance : Hashable HZ := ⟨fun a => if a.n = 5 then 1 else 0⟩
instance : EquivBEq HZ where
  symm h := by simp_all [BEq.beq]
  trans h₁ h₂ := by simp_all [BEq.beq]
  rfl := by simp [BEq.beq]
@[simp] theorem HZ.beq_def (a b : Nat) : (HZ.mk a == HZ.mk b) = (a / 2 == b / 2) := rfl
@[simp] theorem HZ.hash_def (n : Nat) : hash (HZ.mk n) = if n = 5 then 1 else 0 := rfl
theorem HZ.broken : ∀ [EquivBEq HZ] [LawfulHashable HZ], False := fun {_ h} => by
  have := @LawfulHashable.hash_eq HZ _ _ h ⟨4⟩ ⟨5⟩ (by decide); simp at this
open S1

/-! ## From `checks/W1c1Hand.lean` -/
/-! # W1c1 helpers -/
-- DHashMap intersection as the function the evaluation tactics unfold (helper, like hm_inter)
theorem w1c1h_dm_inter {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m₁ m₂ : DHashMap α β) :
    m₁ ∩ m₂ = DHashMap.inter m₁ m₂ := rfl
open S1

/-! ## From `checks/W1c2Hand.lean` -/
/-! # W1c2 helpers -/
-- helper: 16 buckets with the given bucket at index 1 (key 0 misplaced there)
abbrev w1c2g16 {α : Type u} {β : α → Type v} (b : AssocList α β) : Array (AssocList α β) :=
  #[.nil, b, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil]
-- helper: the empty raw literal is well-formed
theorem w1c2eWF {β : Nat → Type v} : (⟨0, nil16⟩ : DHashMap.Raw Nat β).WF := (dr_empty (α := Nat) (β := β)) ▸ .empty
-- helper: bundled Const.insertMany as iterated inserts
theorem w1c2dhcIm {α : Type u} {β : Type v} [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) (l : List (α × β)) :
    (DHashMap.Const.insertMany m l).1 = (Raw₀.Const.insertListₘ ⟨m.1, m.2.size_buckets_pos⟩ l).1 := by
  show (Raw₀.Const.insertMany _ l).1.1 = _; rw [Raw₀.Const.insertMany_eq_insertListₘ]
-- helper: raw Const.insertMany as iterated inserts
theorem w1c2dhrcIm {α : Type u} {β : Type v} [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => β)) (h : 0 < m.buckets.size)
    (l : List (α × β)) : DHashMap.Raw.Const.insertMany m l = (Raw₀.Const.insertListₘ ⟨m, h⟩ l).1 := by
  simp only [DHashMap.Raw.Const.insertMany, h, dite_true]; rw [Raw₀.Const.insertMany_eq_insertListₘ]
-- helper: raw insertManyIfNewUnit as iterated insertIfNew
theorem w1c2dhruIm {α : Type u} [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => Unit)) (h : 0 < m.buckets.size)
    (l : List α) : DHashMap.Raw.Const.insertManyIfNewUnit m l = (Raw₀.Const.insertListIfNewUnitₘ ⟨m, h⟩ l).1 := by
  simp only [DHashMap.Raw.Const.insertManyIfNewUnit, h, dite_true]; rw [Raw₀.Const.insertManyIfNewUnit_eq_insertListIfNewUnitₘ]
-- helper: inserting (0,1) into the 2-bucket literal with (0,7) misplaced resizes and puts (0,7) first
theorem w1c2ins : (Raw₀.insert (⟨⟨2, #[.nil, .cons 0 7 .nil]⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat)) 0 1).1 =
    ⟨3, #[.cons 0 7 (.cons 0 1 .nil), .nil, .nil, .nil]⟩ := by
  hm_eval
  simp (config := {decide := true}) only [Raw₀.expandIfNecessary, Raw₀.expand, ite_false]
  repeat (unfold_expand_go; simp (config := {decide := true}) (disch := first | decide | simp) only [dite_true,
    dite_false, Array.size_set, List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_irrefl,
    Array.getElem_set, AssocList.foldl, AssocList.foldlM, Raw₀.reinsertAux, mkIdx_eq])
  simp (disch := first | decide | simp) [Array.propagateMark, Array.replicate, List.replicate, AssocList.foldlM,
    mkIdx_eq, scr_small, Array.uset_eq_set, idx_lt]
open S1

/-! ## From `checks/W1c3Hand.lean` -/
/-! # W1c3 helpers -/
instance : OfNat ON n := ⟨⟨n⟩⟩

/-! ## From `checks/W1c4Hand.lean` -/
/-! # W1c4 helpers -/
-- one-directional comparison: only (0, 1) compares eq, everything else lt; not TransCmp
def c4c (a b : Nat) : Ordering := if b = 1 ∧ a = 0 then .eq else .lt
def c4B : BEq Nat := ⟨fun a b => c4c a b == .eq⟩
theorem c4L : letI := c4B; Std.LawfulBEqCmp c4c := by
  letI := c4B; exact ⟨fun {a b} => by show _ ↔ (c4c a b == .eq) = true; cases c4c a b <;> simp⟩
-- a predicate failing at k, and a test false off k
theorem c4_dj {P : Nat → Prop} {f : Nat → Bool} (k : Nat) (hk : ¬ P k) (hf : ∀ a, a ≠ k → f a = false) :
    ∀ a, P a → f a = false := fun a ha => hf a (fun e => hk (e ▸ ha))
-- order facts from LawfulOrderOrd + LawfulOrderMin (+ left-leaning or LawfulEqOrd)
theorem c4_refl {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] (a : α) : a ≤ a := by
  cases h : compare a a
  · exact (LawfulOrderOrd.isLE_compare a a).1 (by simp [h])
  · exact (LawfulOrderOrd.isLE_compare a a).1 (by simp [h])
  · exact (LawfulOrderOrd.isGE_compare a a).1 (by simp [h])
theorem c4_pre {α : Type u} [Ord α] [LE α] [Min α] [LawfulOrderOrd α] [LawfulOrderMin α]
    [LawfulOrderLeftLeaningMin α] : IsPreorder α where
  le_refl := c4_refl
  le_trans a b c hab hbc :=
    ((LawfulOrderInf.le_min_iff a b c).1 (by rw [LawfulOrderLeftLeaningMin.min_eq_left b c hbc]; exact hab)).2
theorem c4_tr {α : Type u} [Ord α] [LE α] [Min α] [LawfulOrderOrd α] [LawfulOrderMin α]
    [LawfulOrderLeftLeaningMin α] : TransOrd α :=
  haveI := c4_pre (α := α); inferInstance
theorem c4_ll {α : Type u} [Ord α] [LE α] [Min α] [LawfulOrderOrd α] [LawfulOrderMin α] [LawfulEqOrd α] :
    LawfulOrderLeftLeaningMin α where
  min_eq_left a b h := by
    rcases MinEqOr.min_eq_or a b with e | e
    · exact e
    · have hba : b ≤ a := ((LawfulOrderInf.le_min_iff b a b).1 (by rw [e]; exact c4_refl b)).1
      rw [e]; apply LawfulEqOrd.eq_of_compare
      rw [Ordering.eq_eq_iff_isLE_and_isGE, (LawfulOrderOrd.isLE_compare b a).2 hba,
        (LawfulOrderOrd.isGE_compare b a).2 h]; simp
  min_eq_right a b h := by
    rcases MinEqOr.min_eq_or a b with e | e
    · exact absurd ((LawfulOrderInf.le_min_iff a a b).1 (by rw [e]; exact c4_refl a)).2 h
    · exact e
-- a list that is strictly increasing under compare has its head as left-leaning min
theorem c4_fold {α : Type u} [Ord α] [LE α] [Min α] [LawfulOrderOrd α] [LawfulOrderLeftLeaningMin α]
    (a : α) (as : List α) (h : ∀ y ∈ as, compare a y = .lt) : as.foldl min a = a := by
  induction as with
  | nil => rfl
  | cons b bs ih =>
    rw [List.foldl_cons, LawfulOrderLeftLeaningMin.min_eq_left a b
      ((LawfulOrderOrd.isLE_compare a b).1 (by rw [h b (by simp)]; rfl))]
    exact ih (fun y hy => h y (by simp [hy]))
theorem c4_mh {α : Type u} [Ord α] [LE α] [Min α] [LawfulOrderOrd α] [LawfulOrderLeftLeaningMin α]
    (l : List α) (hl : l.Pairwise (fun a b => compare a b = .lt)) : l.min? = l.head? := by
  cases l with
  | nil => rfl
  | cons a as =>
    simp only [List.min?, List.head?]
    rw [c4_fold a as (List.pairwise_cons.1 hl).1]
-- Nat with the order reversed and min = max: lawful min, left-leaning, but compare is not lawful for it
def c4LE : LE Nat := ⟨fun a b => b ≤ a⟩
def c4Mn : Min Nat := ⟨max⟩
theorem c4OM : @LawfulOrderMin Nat c4Mn c4LE :=
  @LawfulOrderMin.mk Nat c4Mn c4LE (@MinEqOr.mk Nat c4Mn (fun a b => (by omega : max a b = a ∨ max a b = b)))
    (@LawfulOrderInf.mk Nat c4Mn c4LE (fun a b c => (by omega : max b c ≤ a ↔ b ≤ a ∧ c ≤ a)))
theorem c4LLr : @LawfulOrderLeftLeaningMin Nat c4Mn c4LE :=
  @LawfulOrderLeftLeaningMin.mk Nat c4Mn c4LE (fun a b (h : b ≤ a) => (by omega : max a b = a))
    (fun a b (h : ¬ b ≤ a) => (by omega : max a b = b))
-- BEq induced by a comparison, and membership in a list up to cmp-equality
def c4bq {α : Type u} (cmp : α → α → Ordering) : BEq α := ⟨fun a b => cmp a b == .eq⟩
theorem c4lb {α : Type u} (cmp : α → α → Ordering) : letI := c4bq cmp; LawfulBEqCmp cmp := by
  letI := c4bq cmp; exact ⟨fun {a b} => by show _ ↔ (cmp a b == .eq) = true; cases cmp a b <;> simp⟩
theorem c4_cont {α : Type u} {cmp : α → α → Ordering} [TransCmp cmp] {L : List α} {k k' : α}
    (k_eq : cmp k k' = .eq) (mem : k ∈ L) : letI := c4bq cmp; L.contains k' = true := by
  letI := c4bq cmp
  rw [List.contains_iff_exists_mem_beq]
  exact ⟨k, mem, by show (cmp k' k == .eq) = true; rw [OrientedCmp.eq_swap (cmp := cmp) (a := k') (b := k), k_eq]; rfl⟩
-- non-transitive comparison table: 0 < 1, 2 < 0, 0 = 3, 2 < 3, otherwise compare
def c4m (a b : Nat) : Ordering :=
  if a = 0 ∧ b = 1 then .lt else if a = 0 ∧ b = 2 then .gt else if a = 0 ∧ b = 3 then .eq
  else if a = 2 ∧ b = 3 then .lt else compare a b

/-! ## From `checks/W1c5Hand.lean` -/
set_option linter.unusedSimpArgs false
namespace W1c5
/-- Nat keys with lawful BEq and constant hash 0: every lookup goes to bucket 0. -/
structure ZH where n : Nat deriving DecidableEq, Inhabited
instance : Hashable ZH := ⟨fun _ => 0⟩
instance : LawfulHashable ZH := ⟨fun _ _ _ => rfl⟩
instance : OfNat ZH n := ⟨⟨n⟩⟩
/-- A key stored in bucket 1 of 2 is never found under ZH. -/
theorem zh_contains {β : ZH → Type v} (s : Nat) (l : AssocList ZH β) (a : ZH) :
    Raw₀.contains (⟨⟨s, #[.nil, l]⟩, by simp⟩ : Raw₀ ZH β) a = false := by
  rw [contains_eval _ (by simp [Pow2])]
  have : ix #[.nil, l] a = 0 := by
    show (scrambleHash 0).toNat % 2 = 0
    rw [scr_small _ (by decide)]; rfl
  simp only [this]; rfl
end W1c5
namespace W1c5
/-- Every ZH bucket array of the form #[l, nil] is hash-self (all keys hash to bucket 0). -/
theorem zh_hs {β : ZH → Type v} (l : AssocList ZH β) : IsHashSelf (#[l, .nil] : Array (AssocList ZH β)) := by
  refine ⟨fun i hi => ⟨fun h p hp => ?_⟩⟩
  rw [mkIdx_toNat' _ _ _ (by simp [Pow2])]
  have : (scrambleHash (hash p.1)).toNat % 2 = 0 := by
    show (scrambleHash 0).toNat % 2 = 0
    rw [scr_small _ (by decide)]; rfl
  rw [show (#[l, AssocList.nil] : Array (AssocList ZH β)).size = 2 from rfl, this]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => simp at hp
theorem zh_wf {β : ZH → Type v} (s : Nat) (l : AssocList ZH β) (hs : s = (toListModel #[l, .nil]).length)
    (hd : Std.Internal.List.DistinctKeys (toListModel #[l, .nil])) :
    (⟨s, #[l, .nil]⟩ : DHashMap.Raw ZH β).WF :=
  .wf (by simp) (fun {_ _} => ⟨zh_hs l, hs, hd⟩)
/-- A bucket array with an entry whose hash index differs from its bucket is not hash-self. -/
theorem not_hs {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (bs : Array (AssocList α β)) (j : Nat)
    (hj : j < bs.size) (p : (a : α) × β a) (hp : p ∈ bs[j].toList) (hsz : Pow2 bs.size)
    (hne : (scrambleHash (hash p.1)).toNat % bs.size ≠ j) : ¬ IsHashSelf bs := by
  intro h
  have := (h.hashes_to j hj).hash_self (by omega) p hp
  rw [mkIdx_toNat' _ _ _ hsz] at this; exact hne this
theorem idx_small (sz : Nat) (h : 0 < sz) (x : UInt64) (hsz : Pow2 sz) (hx : x.toNat < 65536) :
    (mkIdx sz h x).1.toNat = x.toNat % sz := by
  rw [mkIdx_toNat' _ _ _ hsz, scr_small _ hx]
end W1c5
open W1c5
namespace W1c5
abbrev MZ1 : Raw₀ ZH (fun _ => Nat) := ⟨⟨0, #[.nil, b1 (0 : ZH) (0 : Nat)]⟩, by simp⟩
abbrev MZ2 : Raw₀ ZH (fun _ => Nat) := ⟨⟨1, #[b1 (0 : ZH) (0 : Nat), .nil]⟩, by simp⟩
theorem MZ2wf : MZ2.1.WF := zh_wf _ _ rfl (by simp [toListModel])
abbrev MD : Raw₀ Nat (fun _ => Nat) := ⟨⟨2, #[.cons (0 : Nat) (0 : Nat) (b1 0 1)]⟩, by decide⟩
abbrev MU1 : Raw₀ ZH (fun _ => Unit) := ⟨⟨0, #[.nil, b1 (0 : ZH) ()]⟩, by simp⟩
abbrev MU0 : Raw₀ ZH (fun _ => Unit) := ⟨⟨0, #[.nil, .nil]⟩, by simp⟩
theorem MU0wf : MU0.1.WF := zh_wf _ _ rfl (by simp [toListModel])
abbrev MF : Raw₀ ZH (fun _ => Nat) := ⟨⟨1, #[.nil, b1 (0 : ZH) (5 : Nat)]⟩, by simp⟩
theorem nat_hs_nil : IsHashSelf (#[.nil, .nil] : Array (AssocList Nat (fun _ => Nat))) :=
  ⟨fun i hi => ⟨fun _ p hp => by match i, hi with | 0, _ => simp at hp | 1, _ => simp at hp⟩⟩
end W1c5
namespace W1c5
/-- BEq by hash equality: equivalence and lawful hash, for any hash function. -/
abbrev hashBEq' (α : Type u) [Hashable α] : BEq α := ⟨fun a b => hash a == hash b⟩
theorem hashBEq'_equiv (α : Type u) [Hashable α] : @EquivBEq α (hashBEq' α) := by
  letI := hashBEq' α
  exact { rfl := by intro a; simp [BEq.beq]
          symm := by intro a b h; simp_all [BEq.beq]
          trans := by intro a b c h1 h2; simp_all [BEq.beq] }
theorem hashBEq'_lh (α : Type u) [Hashable α] : @LawfulHashable α (hashBEq' α) _ :=
  @LawfulHashable.mk α (hashBEq' α) _ (fun a b h => by simpa [BEq.beq] using h)
theorem hs_expand_aux {α : Type u} {β : α → Type v} [Hashable α]
    (bs : {d : Array (AssocList α β) // 0 < d.size}) (i : Nat) (h : i < (Raw₀.expand bs).1.size)
    (h' : 0 < (Raw₀.expand bs).1.size) (p : (a : α) × β a) (hp : p ∈ ((Raw₀.expand bs).1[i]).toList) :
    (mkIdx _ h' (hash p.1)).1.toNat = i := by
  letI := hashBEq' α; haveI := hashBEq'_lh α; haveI := hashBEq'_equiv α
  exact (Raw₀.isHashSelf_expand.hashes_to i h).hash_self h' p hp
theorem isHashSelf_expand' {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
    (bs : {d : Array (AssocList α β) // 0 < d.size}) : IsHashSelf (Raw₀.expand bs).1 :=
  ⟨fun i h => ⟨fun h' p hp => hs_expand_aux bs i h h' p hp⟩⟩
theorem contains_of_mem_bucket {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulHashable α]
    (bs : Array (AssocList α β)) (hb : 0 < bs.size) (hs : IsHashSelf bs) (k : α) (p : (a : α) × β a)
    (hp : p ∈ toListModel bs) (hk : (p.1 == k) = true) :
    Raw₀.contains (⟨⟨s, bs⟩, hb⟩ : Raw₀ α β) k = true := by
  rw [contains_gen, AssocList.contains_eq]
  have hp' : p ∈ bs.toList.flatMap AssocList.toList := hp
  obtain ⟨l, hl, hpl⟩ := List.mem_flatMap.mp hp'
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hl)
  have hidx := (hs.hashes_to j hj).hash_self hb p hpl
  rw [hash_eq hk] at hidx
  apply Std.Internal.List.containsKey_eq_true_iff_exists_mem.mpr
  refine ⟨p, ?_, hk⟩
  simp only [hidx]; exact hpl
theorem contains_expandIfNecessary {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulHashable α]
    (m : Raw₀ α β) (k : α) (h : m.contains k = true) : m.expandIfNecessary.contains k = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have htlm := Probe2.raw0_contains_tlm _ k h
  obtain ⟨p, hp, hpk⟩ := Std.Internal.List.containsKey_eq_true_iff_exists_mem.mp htlm
  have hperm := tlm_expandIfNecessary (⟨⟨s, bs⟩, hb⟩ : Raw₀ α β)
  unfold Raw₀.expandIfNecessary at hperm ⊢
  dsimp only at hperm ⊢
  split
  · exact h
  · rename_i hn
    simp only [hn] at hperm
    exact contains_of_mem_bucket _ _ (isHashSelf_expand' _) k p (hperm.mem_iff.mpr hp) hpk
theorem assoc_contains_cons {α : Type u} {β : α → Type v} [BEq α] (l : AssocList α β) (a : α) (b : β a) (k : α)
    (h : l.contains k = true) : (AssocList.cons a b l).contains k = true := by
  simp only [AssocList.contains, h, Bool.or_true]
theorem contains_insertIfNew_of {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulHashable α]
    (m : Raw₀ α β) (a : α) (b : β a) (k : α) (h : m.contains k = true) : (m.insertIfNew a b).contains k = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.insertIfNew
  dsimp only
  split
  · exact h
  · apply contains_expandIfNecessary
    rw [contains_gen] at h ⊢
    simp only [Array.uset, mkIdx_set_toNat, Array.getElem_set]
    split
    · rename_i he
      apply assoc_contains_cons
      simp only [Array.ugetElem_eq_getElem]
      simp only [he]; exact h
    · exact h
end W1c5

/-! ## `#binders (drop0% T i)`: one info line `name:kind:isProp|…` per binder of the statement
(kind E explicit, I implicit, C instance, S strict); hygienic names start with `x._@`/`inst._@` and must be
passed positionally. Driver: `runs/stdplan/waves/binders.py`. -/
open Lean Meta Elab Term in
elab "#binders " t:term : command => Lean.Elab.Command.liftTermElabM do
  let e ← elabTerm t none
  let ty ← instantiateMVars e
  forallTelescope ty fun xs _ => do
    let mut s := ""
    for x in xs do
      let d ← x.fvarId!.getDecl
      let bi := match d.binderInfo with | .default => "E" | .implicit => "I" | .instImplicit => "C" | _ => "S"
      s := s ++ s!"{d.userName}:{bi}:{← isProp d.type}|"
    logInfo m!"{s}"

/-! Canonical opens: after `import Tk` in a scratch file, repeat this line. -/
open Std Std.DHashMap.Internal Std.DTreeMap.Internal HashInstHand Probe2 P3 S1

/-! # W2c5 helpers -/
namespace W2c5
structure W5L where n : Nat deriving DecidableEq, Inhabited
instance : Ord W5L := ⟨fun _ _ => .lt⟩
instance : BEq W5L := ⟨fun _ _ => false⟩
instance : Std.LawfulBEqOrd W5L := ⟨fun {_ _} => by show (Ordering.lt = .eq) ↔ (false = true); simp⟩
end W2c5
namespace W2c5
open Std.Internal.List

theorem ck_ex {α} {β : α → Type _} [BEq α] {l : List ((a : α) × β a)} {k : α} :
    containsKey k l = true ↔ ∃ p ∈ l, (p.1 == k) = true :=
  containsKey_eq_true_iff_exists_mem

theorem ck_sub {α} {β : α → Type _} [BEq α] {l l' : List ((a : α) × β a)} {k : α}
    (hs : l'.Sublist l) (h : containsKey k l' = true) : containsKey k l = true := by
  obtain ⟨p, hp, hk⟩ := ck_ex.1 h
  exact ck_ex.2 ⟨p, hs.subset hp, hk⟩

theorem ck_perm {α} {β : α → Type _} [BEq α] {l l' : List ((a : α) × β a)} {k : α}
    (hp : l.Perm l') : containsKey k l = containsKey k l' :=
  Bool.eq_iff_iff.mpr (by simp only [ck_ex, hp.mem_iff])

theorem ckf_congr {α} {β : α → Type _} [BEq α] [PartialEquivBEq α] {k : α} {g : α → Bool}
    (hg : ∀ a b : α, (a == b) = true → g a = g b) :
    ∀ l : List ((a : α) × β a), containsKey k (l.filter (fun p => g p.1)) = (containsKey k l && g k)
  | [] => rfl
  | ⟨k', v⟩ :: t => by
    have ih := ckf_congr (β := β) (k := k) hg t
    rw [List.filter_cons]
    cases h1 : (k' == k) <;> cases h2 : g k' <;>
      simp [containsKey, h1, ih] <;> simp_all [hg k' k h1]

theorem lc_congr {α} [BEq α] [PartialEquivBEq α] {a b : α} (h : (a == b) = true) :
    ∀ l : List α, l.contains a = l.contains b
  | [] => rfl
  | c :: t => by simp [List.contains_cons, lc_congr h t, BEq.congr_left h]

theorem rep_ck {α} {β : α → Type _} [BEq α] {k a : α} {v : β k} :
    ∀ l : List ((a : α) × β a), containsKey a (replaceEntry k v l) = true →
      (k == a) = true ∨ containsKey a l = true
  | [] => by simp
  | ⟨k', v'⟩ :: t => by
    rw [replaceEntry_cons]
    split
    · intro h; simp only [containsKey, Bool.or_eq_true] at h ⊢; rcases h with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · intro h; simp only [containsKey, Bool.or_eq_true] at h ⊢; rcases h with h | h
      · exact .inr (.inl h)
      · rcases rep_ck t h with h | h
        · exact .inl h
        · exact .inr (.inr h)

theorem ins_ck {α} {β : α → Type _} [BEq α] {k a : α} {v : β k} {l : List ((a : α) × β a)}
    (h : containsKey a (insertEntry k v l) = true) : (k == a) = true ∨ containsKey a l = true := by
  unfold insertEntry at h
  split at h
  · exact rep_ck l h
  · simpa [containsKey] using h

theorem rep_has {α} {β : α → Type _} [BEq α] {k a : α} {v : β k} (hka : (k == a) = true) :
    ∀ l : List ((a : α) × β a), containsKey k l = true → containsKey a (replaceEntry k v l) = true
  | [] => by simp
  | ⟨k', v'⟩ :: t => by
    rw [replaceEntry_cons]
    split
    · intro _; simp [containsKey, hka]
    · rename_i hk
      intro h
      simp only [containsKey, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact absurd h hk
      · exact .inr (rep_has hka t h)

theorem fl_map {m : Type _ → Type _} [Monad m] {β γ δ} (g : β → γ) (f : δ → γ → m δ) :
    ∀ (l : List β) (init : δ), (l.map g).foldlM f init = l.foldlM (fun s a => f s (g a)) init
  | [], _ => rfl
  | a :: l, init => by
    simp only [List.map_cons, List.foldlM_cons]
    congr; funext s; exact fl_map g f l s

theorem fr_map {m : Type _ → Type _} [Monad m] {β γ δ} (g : β → γ) (f : γ → δ → m δ)
    (l : List β) (init : δ) : (l.map g).foldrM f init = l.foldrM (fun a s => f (g a) s) init := by
  simp only [List.foldrM, ← List.map_reverse, fl_map]

theorem foldl_mem {σ} (f : σ → σ → σ) (hf : ∀ a b, f a b = a ∨ f a b = b) :
    ∀ (x : σ) (xs : List σ), xs.foldl f x ∈ x :: xs
  | x, [] => by simp
  | x, y :: ys => by
    rw [List.foldl_cons]
    rcases hf x y with h | h
    · rw [h]; have := foldl_mem f hf x ys
      exact (List.mem_cons.1 this).elim (fun e => by rw [e]; exact List.mem_cons_self) (fun e => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ e))
    · rw [h]; exact List.mem_cons_of_mem _ (foldl_mem f hf y ys)

theorem mk_mem {α} {β : α → Type _} [Ord α] {l : List ((a : α) × β a)} {k : α}
    (h : minKey? l = some k) : ∃ e ∈ l, e.1 = k := by
  simp only [minKey?, minEntry?, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  refine ⟨e, ?_, rfl⟩
  match l, he with
  | x :: xs, he =>
    simp only [List.min?_cons', Option.some.injEq] at he
    subst he
    exact foldl_mem _ (fun a b => by
      first
      | (dsimp only [Min.min]; split <;> simp)
      | (show (if _ then a else b) = a ∨ (if _ then a else b) = b; split <;> simp)) x xs

theorem ck_mem {α} {β : α → Type _} [Ord α] [Std.TransOrd α] [BEq α] [Std.LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {e : (a : α) × β a} (h : e ∈ l) : containsKey e.1 l = true :=
  ck_ex.2 ⟨e, h, Std.LawfulBEqCmp.compare_eq_iff_beq.mp (Std.ReflCmp.compare_self (cmp := compare) (a := e.1))⟩

theorem ck_min {α} {β : α → Type _} [o : Ord α] [Std.TransOrd α] [BEq α] [Std.LawfulBEqOrd α]
    (o' : Ord α) {l : List ((a : α) × β a)} {k : α} (h : @minKey? α β o' l = some k) :
    containsKey k l = true := by
  obtain ⟨e, he, rfl⟩ := @mk_mem α β o' l k h
  exact @ck_mem α β o _ _ _ l e he

theorem ex_min {α} {β : α → Type _} (o' : Ord α) {l : List ((a : α) × β a)} (he : l.isEmpty = false) :
    ∃ w, @minKey? α β o' l = some w :=
  Option.isSome_iff_exists.mp (by rw [@isSome_minKey?_eq_not_isEmpty α β o' l, he]; rfl)

theorem ck_minK {α} {β : α → Type _} [o : Ord α] [Std.TransOrd α] [BEq α] [Std.LawfulBEqOrd α]
    (o' : Ord α) {l : List ((a : α) × β a)} (he : l.isEmpty = false) :
    containsKey (@minKey α β o' l he) l = true :=
  @ck_min α β o _ _ _ o' l _ (Option.some_get _).symm

theorem ck_minKD {α} {β : α → Type _} [o : Ord α] [Std.TransOrd α] [BEq α] [Std.LawfulBEqOrd α]
    (o' : Ord α) {l : List ((a : α) × β a)} (he : l.isEmpty = false) (fb : α) :
    containsKey ((@minKey? α β o' l).getD fb) l = true := by
  obtain ⟨w, hw⟩ := ex_min (β := β) o' he
  rw [hw]; exact @ck_min α β o _ _ _ o' l _ hw

theorem ck_minK! {α} {β : α → Type _} [o : Ord α] [Std.TransOrd α] [BEq α] [Std.LawfulBEqOrd α] [Inhabited α]
    (o' : Ord α) {l : List ((a : α) × β a)} (he : l.isEmpty = false) :
    containsKey ((@minKey? α β o' l).get!) l = true := by
  obtain ⟨w, hw⟩ := ex_min (β := β) o' he
  rw [hw]; exact @ck_min α β o _ _ _ o' l _ hw

theorem ckf_false {α} {β : α → Type _} [BEq α] {l : List ((a : α) × β a)} {g : (a : α) × β a → Bool} {k : α}
    (h : containsKey k l = false) : containsKey k (l.filter g) = false := by
  cases h' : containsKey k (l.filter g)
  · rfl
  · exact absurd (ck_sub List.filter_sublist h') (by simp [h])

theorem il_left {α} {β : α → Type _} [BEq α] : ∀ (t l : List ((a : α) × β a)) {k : α},
    containsKey k (insertList l t) = true → containsKey k l = false → containsKey k t = true
  | [], l, k, h1, h2 => by simp only [insertList] at h1; rw [h1] at h2; cases h2
  | ⟨k', v⟩ :: t, l, k, h1, h2 => by
    simp only [insertList] at h1
    cases h3 : containsKey k (insertEntry k' v l)
    · have := il_left t _ h1 h3; simp [containsKey, this]
    · rcases ins_ck h3 with e | e
      · simp [containsKey, e]
      · rw [e] at h2; cases h2

theorem il_right {α} {β : α → Type _} [BEq α] : ∀ (t l : List ((a : α) × β a)) {k : α},
    containsKey k (insertList l t) = true → containsKey k t = false → containsKey k l = true
  | [], l, k, h1, _ => by simpa only [insertList] using h1
  | ⟨k', v⟩ :: t, l, k, h1, h2 => by
    simp only [insertList] at h1
    simp only [containsKey, Bool.or_eq_false_iff] at h2
    rcases ins_ck (il_right t _ h1 h2.2) with e | e
    · rw [h2.1] at e; cases e
    · exact e

theorem ck_fm {α} {β γ : α → Type _} [BEq α] {f : (a : α) → β a → Option (γ a)}
    {l : List ((a : α) × β a)} {k : α}
    (h : containsKey k (l.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) = true) :
    containsKey k l = true := by
  obtain ⟨p, hp, hk⟩ := ck_ex.1 h
  obtain ⟨q, hq, e⟩ := List.mem_filterMap.1 hp
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 e
  exact ck_ex.2 ⟨q, hq, hk⟩

theorem cle {α} {β : α → Type _} [BEq α] [EquivBEq α] : ∀ (l₁ l₂ : List ((a : α) × β a)),
    DistinctKeys l₁ → l₂.length = l₁.length → (∀ a, containsKey a l₁ = true → containsKey a l₂ = true) →
      ∀ a, containsKey a l₂ = true → containsKey a l₁ = true
  | [], l₂, _, hl, _, a, ha => by
    rw [List.length_nil, List.length_eq_zero_iff] at hl; subst hl; simp at ha
  | ⟨k, v⟩ :: t, l₂, hd, hl, hs, a, ha => by
    have ⟨hdt, hkt⟩ := distinctKeys_cons_iff.mp hd
    have hk2 : containsKey k l₂ = true := hs k (by simp [containsKey])
    have hl' : (eraseKey k l₂).length = t.length := by rw [length_eraseKey, hk2]; simp [hl]
    have hs' : ∀ b, containsKey b t = true → containsKey b (eraseKey k l₂) = true := by
      intro b hb
      have hkb : (k == b) = false := by
        cases e : (k == b)
        · rfl
        · rw [containsKey_congr e] at hkt; rw [hkt] at hb; cases hb
      rw [containsKey_eraseKey_of_false hkb]; exact hs b (by simp [containsKey, hb])
    cases e : (k == a)
    · have := cle t _ hdt hl' hs' a (by rw [containsKey_eraseKey_of_false e]; exact ha)
      simp [containsKey, this]
    · simp [containsKey, e]
end W2c5

open W2c5 Std.Internal.List

/-! # W2c5 verdicts -/

-- `Std.Internal.List.Const.alterKey_of_perm` (binder 3): NS (a == b iff a <= b): l = [1, 0] distinct, l' = [0, 1], a = 1, f = some 5; replaceEntry rewrites key 1 in l but key 0 in l'
theorem w2c5_0 : ¬ drop0% Std.Internal.List.Const.alterKey_of_perm 3 :=
   fun h => by
  have := h (α := NS) (β := Nat) (a := 1) (f := fun _ => some 5) (l := [⟨1,0⟩,⟨0,0⟩]) (l' := [⟨0,0⟩,⟨1,0⟩]) ⟨by decide⟩ (by decide)
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.Const.alterKey_of_perm` (binder 8): Nat keys, duplicate key 0 in the list: l = [0:0, 0:1], l' = [0:1, 0:0], f = some 5; alterKey 0 replaces different first entries, results not permutations
theorem w2c5_1 : ¬ drop0% Std.Internal.List.Const.alterKey_of_perm 8 :=
   fun h => by
  have := h (α := Nat) (β := Nat) (a := 0) (f := fun _ => some 5) (l := [⟨0,0⟩,⟨0,1⟩]) (l' := [⟨0,1⟩,⟨0,0⟩]) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.alterKey_of_perm` (binder 8): Nat keys, duplicate key 0 in the list: l = [0:0, 0:1], l' = [0:1, 0:0], f = some 5; alterKey 0 replaces different first entries, results not permutations
theorem w2c5_2 : ¬ drop0% Std.Internal.List.alterKey_of_perm 8 :=
   fun h => by
  have := @h Nat (fun _ => Nat) _ _ 0 (fun _ => some 5) [⟨0,0⟩,⟨0,1⟩] [⟨0,1⟩,⟨0,0⟩] (by decide)
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.apply_eq_true_of_containsKey_filter` (binder 7): Nat keys, duplicate key 0 in the list: l = [0, 0], f true: the filter contains 0 but l is not distinct
theorem w2c5_3 : ¬ indep0% Std.Internal.List.apply_eq_true_of_containsKey_filter 7 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (f := fun _ _ => true) (l := [⟨0,0⟩,⟨0,0⟩]) (k := 0) (by decide)
  exact absurd this.1 (by decide)

-- `Std.Internal.List.assoc_induction` (binder 3): motive = False: the cons step is vacuous, conclusion False
theorem w2c5_4 : ¬ drop0% Std.Internal.List.assoc_induction 3 :=
   fun h =>
  h (α := Nat) (β := fun _ => Nat) (motive := fun _ => False) (fun _ _ _ h => h) []

-- `Std.Internal.List.assoc_induction` (binder 4): motive t = (t = []): nil holds, [0:0] fails
theorem w2c5_5 : ¬ drop0% Std.Internal.List.assoc_induction 4 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (motive := fun t => t = []) rfl [⟨0,0⟩]
  exact absurd this (by decide)

-- `Std.Internal.List.Const.beqModel_congr` (binder 3): NS: l2 = [1:0, 0:1] distinct, l4 = its reverse; getValue? 1 l4 hits key 0 first, beqModel true vs false
theorem w2c5_6 : ¬ drop0% Std.Internal.List.Const.beqModel_congr 3 :=
   fun h => by
  have := h (α := NS) (β := Nat) (l₁ := [⟨1,0⟩,⟨0,1⟩]) (l₂ := [⟨1,0⟩,⟨0,1⟩]) (l₃ := [⟨1,0⟩,⟨0,1⟩]) (l₄ := [⟨0,1⟩,⟨1,0⟩]) ⟨by decide⟩ (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.Const.beqModel_congr` (binder 9): Nat keys, duplicate key 0 in the list: l1 = l3 = [0:0, 0:0], l2 = [0:0, 0:1], l4 = [0:1, 0:0]; beqModel true vs false
theorem w2c5_7 : ¬ drop0% Std.Internal.List.Const.beqModel_congr 9 :=
   fun h => by
  have := h (α := Nat) (β := Nat) (l₁ := [⟨0,0⟩,⟨0,0⟩]) (l₂ := [⟨0,0⟩,⟨0,1⟩]) (l₃ := [⟨0,0⟩,⟨0,0⟩]) (l₄ := [⟨0,1⟩,⟨0,0⟩]) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.beqModel_congr` (binder 9): Nat keys, duplicate key 0 in the list: l1 = l3 = [0:0, 0:0], l2 = [0:0, 0:1], l4 = [0:1, 0:0]; beqModel true vs false
theorem w2c5_8 : ¬ drop0% Std.Internal.List.beqModel_congr 9 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (l₁ := [⟨0,0⟩,⟨0,0⟩]) (l₂ := [⟨0,0⟩,⟨0,1⟩]) (l₃ := [⟨0,0⟩,⟨0,0⟩]) (l₄ := [⟨0,1⟩,⟨0,0⟩]) (by decide) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.Const.beqModel_eq_true_of_perm` (binder 8): Nat keys, duplicate key 0 in the list: l1 = [0:0, 0:1], l2 = reverse; getValue 0 differs, beqModel false
theorem w2c5_9 : ¬ drop0% Std.Internal.List.Const.beqModel_eq_true_of_perm 8 :=
   fun h => by
  have := h (α := Nat) (β := Nat) (l₁ := [⟨0,0⟩,⟨0,1⟩]) (l₂ := [⟨0,1⟩,⟨0,0⟩]) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.beqModel_eq_true_of_perm` (binder 8): Nat keys, duplicate key 0 in the list: l1 = [0:0, 0:1], l2 = reverse; getValue 0 differs, beqModel false
theorem w2c5_10 : ¬ drop0% Std.Internal.List.beqModel_eq_true_of_perm 8 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (l₁ := [⟨0,0⟩,⟨0,1⟩]) (l₂ := [⟨0,1⟩,⟨0,0⟩]) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.beqModel_eq_true_of_perm` (binder 5): value BEq constantly false (not ReflBEq): beqModel [0:0] [0:0] = false
theorem w2c5_11 : ¬ drop0% Std.Internal.List.beqModel_eq_true_of_perm 5 :=
   fun h => by
  have := @h Nat (fun _ => Nat) _ _ (fun _ => ⟨fun _ _ => false⟩) [⟨0,0⟩] [⟨0,0⟩] ⟨by decide⟩ (by decide)
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.DistinctKeys.congr` (binder 6): l = [], l' = [0:0, 0:0]: no permutation, distinct vs not
theorem w2c5_12 : ¬ drop0% Std.Internal.List.DistinctKeys.congr 6 :=
   fun h => by
  have := (h (α := Nat) (β := fun _ => Nat) (l := []) (l' := [⟨0,0⟩,⟨0,0⟩])).mp ⟨by decide⟩
  exact absurd this.1 (by decide)

-- `Std.Internal.List.DistinctKeys.congr` (binder 3): NS: [1, 0] distinct but its permutation [0, 1] is not (0 <= 1)
theorem w2c5_13 : ¬ drop0% Std.Internal.List.DistinctKeys.congr 3 :=
   fun h => by
  have := (h (α := NS) (β := fun _ => Nat) (l := [⟨1,0⟩,⟨0,0⟩]) (l' := [⟨0,0⟩,⟨1,0⟩]) (by decide)).mp ⟨by decide⟩
  exact absurd this.1 (by decide)

-- `Std.Internal.List.congr_filter_containsKey_of_perm` (binder 7): removable: containsKey is permutation invariant for any BEq, so both filters use the same predicate; Perm.filter
theorem w2c5_14 : drop% Std.Internal.List.congr_filter_containsKey_of_perm 7 :=
   by
  intro α β l₁ l₂ l₃ l₄ _ h₁ h₂ _
  have : (fun p : (a : α) × β a => containsKey p.fst l₂) = (fun p => containsKey p.1 l₄) := funext fun p => ck_perm h₂
  rw [this]; exact h₁.filter _

-- `Std.Internal.List.congr_filter_containsKey_of_perm` (binder 10): removable: containsKey is permutation invariant for any BEq, so both filters use the same predicate; Perm.filter
theorem w2c5_15 : drop% Std.Internal.List.congr_filter_containsKey_of_perm 10 :=
   by
  intro α β l₁ l₂ l₃ l₄ _ _ h₁ h₂
  have : (fun p : (a : α) × β a => containsKey p.fst l₂) = (fun p => containsKey p.1 l₄) := funext fun p => ck_perm h₂
  rw [this]; exact h₁.filter _

-- `Std.Internal.List.DistinctKeys.cons` (binder 3): NS: k = 0 not contained in [1] (1 <= 0 false), but 0 == 1 so [0, 1] not distinct
theorem w2c5_16 : ¬ drop0% Std.Internal.List.DistinctKeys.cons 3 :=
   fun h => by
  have := h (α := NS) (β := fun _ => Nat) (l := [⟨1,0⟩]) (k := 0) (v := 0) (by decide) ⟨by decide⟩
  exact absurd this.1 (by decide)

-- `Std.Internal.List.DistinctKeys.cons` (binder 8): Nat keys, duplicate key 0 in the list: l = [0, 0], k = 1
theorem w2c5_17 : ¬ drop0% Std.Internal.List.DistinctKeys.cons 8 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (l := [⟨0,0⟩,⟨0,0⟩]) (k := 1) (v := 0) (by decide)
  exact absurd this.1 (by decide)

-- `Std.Internal.List.DistinctKeys.constAlterKey` (binder 2): NT (|a - b| <= 1): l = [0, 2] distinct, key 1 replaces 0, giving [1, 2] with 1 == 2
theorem w2c5_18 : ¬ drop0% Std.Internal.List.DistinctKeys.constAlterKey 2 :=
   fun h => by
  have := h (α := NT) (β := Nat) (a := 1) (f := fun _ => some 0) (l := [⟨0,0⟩,⟨2,0⟩]) ⟨by decide⟩
  exact absurd this.1 (by decide +kernel)

-- `Std.Internal.List.DistinctKeys.constModifyKey` (binder 3): NT (|a - b| <= 1): l = [0, 2] distinct, key 1 replaces 0, giving [1, 2] with 1 == 2
theorem w2c5_19 : ¬ drop0% Std.Internal.List.DistinctKeys.constModifyKey 3 :=
   fun h => by
  have := h (α := NT) (β := Nat) (a := 1) (f := id) (l := [⟨0,0⟩,⟨2,0⟩]) ⟨by decide⟩
  exact absurd this.1 (by decide +kernel)

-- `Std.Internal.List.containsKey_alterKey` (binder 8): Nat keys, duplicate key 0 in the list: l = [0:0, 0:0], f = none; eraseKey removes one copy, key 0 still present
theorem w2c5_20 : ¬ drop0% Std.Internal.List.containsKey_alterKey 8 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (k := 0) (k' := 0) (f := fun _ => none) (l := [⟨0,0⟩,⟨0,0⟩])
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.containsKey_filter` (binder 7): Nat keys, duplicate key 0 in the list: l = [0:0, 0:1], f keeps value 1; filter keeps 0 but getValueCast? 0 = 0
theorem w2c5_21 : ¬ drop0% Std.Internal.List.containsKey_filter 7 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (f := fun _ v => v == 1) (k := 0) (l := [⟨0,0⟩,⟨0,1⟩])
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.Const.containsKey_filterMap` (binder 2): NS: l = [1:0, 0:1] distinct, k = 1, f keeps value 1; filtered [0:1] contains 1 (0 <= 1), getValue 1 = 0 dropped
theorem w2c5_22 : ¬ drop0% Std.Internal.List.Const.containsKey_filterMap 2 :=
   fun h => by
  have := h (α := NS) (β := Nat) (γ := Nat) (f := fun _ v => if v = 1 then some v else none) (k := 1) (l := [⟨1,0⟩,⟨0,1⟩]) ⟨by decide⟩
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.Const.containsKey_filterMap` (binder 8): Nat keys, duplicate key 0 in the list: l = [0:0, 0:1], f keeps value 1; first value 0 is dropped
theorem w2c5_23 : ¬ drop0% Std.Internal.List.Const.containsKey_filterMap 8 :=
   fun h => by
  have := h (α := Nat) (β := Nat) (γ := Nat) (f := fun _ v => if v = 1 then some v else none) (k := 0) (l := [⟨0,0⟩,⟨0,1⟩])
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.containsKey_filterMap` (binder 8): Nat keys, duplicate key 0 in the list: l = [0:0, 0:1], f keeps value 1; first value 0 is dropped
theorem w2c5_24 : ¬ drop0% Std.Internal.List.containsKey_filterMap 8 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (γ := fun _ => Nat) (f := fun _ v => if v = 1 then some v else none) (k := 0) (l := [⟨0,0⟩,⟨0,1⟩])
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.Const.containsKey_filterMap_iff` (binder 4): NS: l = [1:0, 0:1] distinct, k = 1, f keeps value 1; filtered [0:1] contains 1 (0 <= 1), getValue 1 = 0 dropped
theorem w2c5_25 : ¬ drop0% Std.Internal.List.Const.containsKey_filterMap_iff 4 :=
   fun h => by
  obtain ⟨_, hh⟩ := (h (α := NS) (β := Nat) (γ := Nat) (f := fun _ v => if v = 1 then some v else none) (k := 1) (l := [⟨1,0⟩,⟨0,1⟩]) ⟨by decide⟩).mp (by decide)
  exact absurd hh (by decide +kernel +revert)

-- `Std.Internal.List.Const.containsKey_filterMap_iff` (binder 8): Nat keys, duplicate key 0 in the list: l = [0:0, 0:1], f keeps value 1; first value 0 is dropped
theorem w2c5_26 : ¬ drop0% Std.Internal.List.Const.containsKey_filterMap_iff 8 :=
   fun h => by
  obtain ⟨_, hh⟩ := (h (α := Nat) (β := Nat) (γ := Nat) (f := fun _ v => if v = 1 then some v else none) (k := 0) (l := [⟨0,0⟩,⟨0,1⟩])).mp (by decide)
  exact absurd hh (by decide +kernel +revert)

-- `Std.Internal.List.containsKey_filterMap_iff` (binder 8): Nat keys, duplicate key 0 in the list: l = [0:0, 0:1], f keeps value 1; first value 0 is dropped
theorem w2c5_27 : ¬ drop0% Std.Internal.List.containsKey_filterMap_iff 8 :=
   fun h => by
  obtain ⟨_, hh⟩ := (h (α := Nat) (β := fun _ => Nat) (γ := fun _ => Nat) (f := fun _ v => if v = 1 then some v else none) (k := 0) (l := [⟨0,0⟩,⟨0,1⟩])).mp (by decide)
  exact absurd hh (by decide +kernel +revert)

-- `Std.Internal.List.containsKey_filter_containsKey` (binder 6): removable: containsKey of a filter needs only that some kept entry matches; EquivBEq congruence of the filter predicate gives the formula, no DistinctKeys
theorem w2c5_28 : drop% Std.Internal.List.containsKey_filter_containsKey 6 :=
   by
  intro α β _ _ l₁ l₂ k
  exact ckf_congr (g := fun a => containsKey a l₂) (fun a b h => containsKey_congr h) l₁

-- `Std.Internal.List.containsKey_filter_containsKey_eq_false_of_containsKey_eq_false_left` (binder 3): removable: a filter is a sublist, so a key absent from l1 is absent from the filter (any BEq)
theorem w2c5_29 : drop% Std.Internal.List.containsKey_filter_containsKey_eq_false_of_containsKey_eq_false_left 3 :=
   by
  intros; exact ckf_false ‹_›

-- `Std.Internal.List.containsKey_filter_containsKey_eq_false_of_containsKey_eq_false_left` (binder 6): removable: a filter is a sublist, so a key absent from l1 is absent from the filter (any BEq)
theorem w2c5_30 : drop% Std.Internal.List.containsKey_filter_containsKey_eq_false_of_containsKey_eq_false_left 6 :=
   by
  intros; exact ckf_false ‹_›

-- `Std.Internal.List.containsKey_filter_containsKey_iff` (binder 6): removable: containsKey of a filter needs only that some kept entry matches; EquivBEq congruence of the filter predicate gives the formula, no DistinctKeys
theorem w2c5_31 : drop% Std.Internal.List.containsKey_filter_containsKey_iff 6 :=
   by
  intro α β _ _ l₁ l₂ k
  rw [ckf_congr (g := fun a => containsKey a l₂) (fun a b h => containsKey_congr h) l₁]; simp

-- `Std.Internal.List.containsKey_filter_iff` (binder 7): Nat keys, duplicate key 0 in the list: l = [0:0, 0:1], f keeps value 1; filter keeps 0 but getValueCast? 0 = 0
theorem w2c5_32 : ¬ drop0% Std.Internal.List.containsKey_filter_iff 7 :=
   fun h => by
  obtain ⟨_, hh⟩ := (h (α := Nat) (β := fun _ => Nat) (f := fun _ v => v == 1) (k := 0) (l := [⟨0,0⟩,⟨0,1⟩])).mp (by decide)
  exact absurd hh (by decide +kernel +revert)

-- `Std.Internal.List.containsKey_filter_not_contains` (binder 6): removable: containsKey of a filter needs only that some kept entry matches; EquivBEq congruence of the filter predicate gives the formula, no DistinctKeys
theorem w2c5_33 : drop% Std.Internal.List.containsKey_filter_not_contains 6 :=
   by
  intro α β _ _ l₁ l₂ k
  exact ckf_congr (g := fun a => !List.contains l₂ a) (fun a b h => by rw [lc_congr h l₂]) l₁

-- `Std.Internal.List.containsKey_filter_not_contains_eq_false_left` (binder 3): removable: a filter is a sublist, so a key absent from l1 is absent from the filter (any BEq)
theorem w2c5_34 : drop% Std.Internal.List.containsKey_filter_not_contains_eq_false_left 3 :=
   by
  intros; exact ckf_false ‹_›

-- `Std.Internal.List.containsKey_filter_not_contains_eq_false_left` (binder 6): removable: a filter is a sublist, so a key absent from l1 is absent from the filter (any BEq)
theorem w2c5_35 : drop% Std.Internal.List.containsKey_filter_not_contains_eq_false_left 6 :=
   by
  intros; exact ckf_false ‹_›

-- `Std.Internal.List.containsKey_filter_not_contains_iff` (binder 6): removable: containsKey of a filter needs only that some kept entry matches; EquivBEq congruence of the filter predicate gives the formula, no DistinctKeys
theorem w2c5_36 : drop% Std.Internal.List.containsKey_filter_not_contains_iff 6 :=
   by
  intro α β _ _ l₁ l₂ k
  rw [ckf_congr (g := fun a => !List.contains l₂ a) (fun a b h => by rw [lc_congr h l₂]) l₁]; simp

-- `Std.Internal.List.containsKey_filter_not_contains_map_fst` (binder 6): removable: containsKey of a filter needs only that some kept entry matches; EquivBEq congruence of the filter predicate gives the formula, no DistinctKeys
theorem w2c5_37 : drop% Std.Internal.List.containsKey_filter_not_contains_map_fst 6 :=
   by
  intro α β _ _ l₁ l₂ k
  rw [ckf_congr (g := fun a => !List.contains (l₂.map Sigma.fst) a) (fun a b h => by rw [lc_congr h]) l₁,
    containsKey_eq_contains_map_fst (l := l₂)]

-- `Std.Internal.List.containsKey_filter_not_contains_map_fst_eq_false_left` (binder 3): removable: a filter is a sublist, so a key absent from l1 is absent from the filter (any BEq)
theorem w2c5_38 : drop% Std.Internal.List.containsKey_filter_not_contains_map_fst_eq_false_left 3 :=
   by
  intros; exact ckf_false ‹_›

-- `Std.Internal.List.containsKey_filter_not_contains_map_fst_eq_false_left` (binder 6): removable: a filter is a sublist, so a key absent from l1 is absent from the filter (any BEq)
theorem w2c5_39 : drop% Std.Internal.List.containsKey_filter_not_contains_map_fst_eq_false_left 6 :=
   by
  intros; exact ckf_false ‹_›

-- `Std.Internal.List.containsKey_filter_not_contains_map_fst_iff` (binder 6): removable: containsKey of a filter needs only that some kept entry matches; EquivBEq congruence of the filter predicate gives the formula, no DistinctKeys
theorem w2c5_40 : drop% Std.Internal.List.containsKey_filter_not_contains_map_fst_iff 6 :=
   by
  intro α β _ _ l₁ l₂ k
  rw [ckf_congr (g := fun a => !List.contains (l₂.map Sigma.fst) a) (fun a b h => by rw [lc_congr h]) l₁,
    containsKey_eq_contains_map_fst (l := l₂)]; simp

-- `Std.Internal.List.containsKey_filter_not_contains_map_fst_of_contains_map_fst_right` (binder 6): removable: containsKey of a filter needs only that some kept entry matches; EquivBEq congruence of the filter predicate gives the formula, no DistinctKeys
theorem w2c5_41 : drop% Std.Internal.List.containsKey_filter_not_contains_map_fst_of_contains_map_fst_right 6 :=
   by
  intro α β _ _ l₁ l₂ k h
  rw [ckf_congr (g := fun a => !List.contains (l₂.map Sigma.fst) a) (fun a b h => by rw [lc_congr h]) l₁,
    ← containsKey_eq_contains_map_fst, h]; simp

-- `Std.Internal.List.containsKey_filter_not_contains_of_contains_right` (binder 6): removable: containsKey of a filter needs only that some kept entry matches; EquivBEq congruence of the filter predicate gives the formula, no DistinctKeys
theorem w2c5_42 : drop% Std.Internal.List.containsKey_filter_not_contains_of_contains_right 6 :=
   by
  intro α β _ _ l₁ l₂ k h
  rw [ckf_congr (g := fun a => !List.contains l₂ a) (fun a b h => by rw [lc_congr h l₂]) l₁, h]; simp

-- `Std.Internal.List.containsKey_insertEntry_of_beq` (binder 3): removable: insertEntry either conses k:v or replaceEntry puts k:v where some key matched k; k == a finds it (any BEq)
theorem w2c5_43 : drop% Std.Internal.List.containsKey_insertEntry_of_beq 3 :=
   by
  intro α β _ l k a v h
  unfold insertEntry; split
  · exact rep_has h l ‹_›
  · simp [containsKey, h]

-- `Std.Internal.List.containsKey_maxKey` (binder 7): removable: minKey?/maxKey? is the key of a list element (foldl of an either-or min, any Ord); compare k k = eq gives k == k
theorem w2c5_44 : drop% Std.Internal.List.containsKey_maxKey 7 :=
   by
  intro α β _ _ _ _ l he; exact ck_minK _ he

-- `Std.Internal.List.containsKey_maxKey` (binder 5): Nat compare, BEq constantly false: l = [0:0], maxKey 0 not found
theorem w2c5_45 : ¬ drop0% Std.Internal.List.containsKey_maxKey 5 :=
   fun h => by
  let B : BEq Nat := ⟨fun _ _ => false⟩
  have := @h Nat (fun _ => Nat) _ _ B [⟨0,0⟩] ⟨List.pairwise_singleton _ _⟩ rfl
  exact absurd this (by decide)

-- `Std.Internal.List.containsKey_maxKey` (binder 3): Ord constantly lt, BEq constantly false (LawfulBEqOrd holds, compare not reflexive): l = [0:0], its own key is not found
theorem w2c5_46 : ¬ drop0% Std.Internal.List.containsKey_maxKey 3 :=
   fun h => by
  have := h (α := W5L) (β := fun _ => Nat) (l := [⟨⟨0⟩,0⟩]) ⟨by decide⟩ (he := rfl)
  exact absurd this (by decide)

-- `Std.Internal.List.containsKey_maxKey!` (binder 8): removable: minKey?/maxKey? is the key of a list element (foldl of an either-or min, any Ord); compare k k = eq gives k == k
theorem w2c5_47 : drop% Std.Internal.List.containsKey_maxKey! 8 :=
   by
  intro α β _ _ _ _ _ l he; exact ck_minK! _ he

-- `Std.Internal.List.containsKey_maxKey?` (binder 7): removable: minKey?/maxKey? is the key of a list element (foldl of an either-or min, any Ord); compare k k = eq gives k == k
theorem w2c5_48 : drop% Std.Internal.List.containsKey_maxKey? 7 :=
   by
  intro α β _ _ _ _ l km hkm; exact ck_min _ hkm

-- `Std.Internal.List.containsKey_maxKey?` (binder 3): Ord constantly lt, BEq constantly false (LawfulBEqOrd holds, compare not reflexive): l = [0:0], its own key is not found
theorem w2c5_49 : ¬ drop0% Std.Internal.List.containsKey_maxKey? 3 :=
   fun h => by
  have := h (α := W5L) (β := fun _ => Nat) (l := [⟨⟨0⟩,0⟩]) ⟨by decide⟩ (km := ⟨0⟩) (by decide)
  exact absurd this (by decide)

-- `Std.Internal.List.containsKey_maxKey?_eraseKey` (binder 8): removable: minKey?/maxKey? is the key of a list element (foldl of an either-or min, any Ord); compare k k = eq gives k == k
theorem w2c5_50 : drop% Std.Internal.List.containsKey_maxKey?_eraseKey 8 :=
   by
  intro α β _ _ _ _ k l kme hkme; exact ck_sub sublist_eraseKey (ck_min _ hkme)

-- `Std.Internal.List.containsKey_maxKey?_eraseKey` (binder 3): Ord constantly lt, BEq constantly false (LawfulBEqOrd holds, compare not reflexive): l = [0:0], its own key is not found
theorem w2c5_51 : ¬ drop0% Std.Internal.List.containsKey_maxKey?_eraseKey 3 :=
   fun h => by
  have := h (α := W5L) (β := fun _ => Nat) (k := ⟨0⟩) (l := [⟨⟨0⟩,0⟩]) ⟨by decide⟩ (kme := ⟨0⟩) (by decide)
  exact absurd this (by decide)

-- `Std.Internal.List.containsKey_maxKeyD` (binder 7): removable: minKey?/maxKey? is the key of a list element (foldl of an either-or min, any Ord); compare k k = eq gives k == k
theorem w2c5_52 : drop% Std.Internal.List.containsKey_maxKeyD 7 :=
   by
  intro α β _ _ _ _ l he fb; exact ck_minKD _ he fb

-- `Std.Internal.List.containsKey_maxKeyD` (binder 3): Ord constantly lt, BEq constantly false (LawfulBEqOrd holds, compare not reflexive): l = [0:0], its own key is not found
theorem w2c5_53 : ¬ drop0% Std.Internal.List.containsKey_maxKeyD 3 :=
   fun h => by
  have := h (α := W5L) (β := fun _ => Nat) (l := [⟨⟨0⟩,0⟩]) ⟨by decide⟩ rfl (fallback := ⟨0⟩)
  exact absurd this (by decide)

-- `Std.Internal.List.containsKey_minKey` (binder 7): removable: minKey?/maxKey? is the key of a list element (foldl of an either-or min, any Ord); compare k k = eq gives k == k
theorem w2c5_54 : drop% Std.Internal.List.containsKey_minKey 7 :=
   by
  intro α β _ _ _ _ l he; exact ck_minK _ he

-- `Std.Internal.List.containsKey_minKey!` (binder 8): removable: minKey?/maxKey? is the key of a list element (foldl of an either-or min, any Ord); compare k k = eq gives k == k
theorem w2c5_55 : drop% Std.Internal.List.containsKey_minKey! 8 :=
   by
  intro α β _ _ _ _ _ l he; exact ck_minK! _ he

-- `Std.Internal.List.containsKey_minKey?` (binder 7): removable: minKey?/maxKey? is the key of a list element (foldl of an either-or min, any Ord); compare k k = eq gives k == k
theorem w2c5_56 : drop% Std.Internal.List.containsKey_minKey? 7 :=
   by
  intro α β _ _ _ _ l km hkm; exact ck_min _ hkm

-- `Std.Internal.List.containsKey_minKey?_eraseKey` (binder 8): removable: minKey?/maxKey? is the key of a list element (foldl of an either-or min, any Ord); compare k k = eq gives k == k
theorem w2c5_57 : drop% Std.Internal.List.containsKey_minKey?_eraseKey 8 :=
   by
  intro α β _ _ _ _ k l kme hkme; exact ck_sub sublist_eraseKey (ck_min _ hkme)

-- `Std.Internal.List.containsKey_minKey?_eraseKey` (binder 3): Ord constantly lt, BEq constantly false (LawfulBEqOrd holds, compare not reflexive): l = [0:0], its own key is not found
theorem w2c5_58 : ¬ drop0% Std.Internal.List.containsKey_minKey?_eraseKey 3 :=
   fun h => by
  have := h (α := W5L) (β := fun _ => Nat) (k := ⟨0⟩) (l := [⟨⟨0⟩,0⟩]) ⟨by decide⟩ (kme := ⟨0⟩) (by decide)
  exact absurd this (by decide)

-- `Std.Internal.List.containsKey_minKeyD` (binder 7): removable: minKey?/maxKey? is the key of a list element (foldl of an either-or min, any Ord); compare k k = eq gives k == k
theorem w2c5_59 : drop% Std.Internal.List.containsKey_minKeyD 7 :=
   by
  intro α β _ _ _ _ l he fb; exact ck_minKD _ he fb

-- `Std.Internal.List.containsKey_minKeyD` (binder 3): Ord constantly lt, BEq constantly false (LawfulBEqOrd holds, compare not reflexive): l = [0:0], its own key is not found
theorem w2c5_60 : ¬ drop0% Std.Internal.List.containsKey_minKeyD 3 :=
   fun h => by
  have := h (α := W5L) (β := fun _ => Nat) (l := [⟨⟨0⟩,0⟩]) ⟨by decide⟩ rfl (fallback := ⟨0⟩)
  exact absurd this (by decide)

-- `Std.Internal.List.containsKey_of_beq` (binder 3): NT: l = [0], a = 1, b = 2: 0 == 1, 1 == 2, not 0 == 2
theorem w2c5_61 : ¬ drop0% Std.Internal.List.containsKey_of_beq 3 :=
   fun h => by
  have := h (α := NT) (β := fun _ => Nat) (l := [⟨0,0⟩]) (a := 1) (b := 2) (by decide) (by decide)
  exact absurd this (by decide)

-- `Std.Internal.List.containsKey_of_containsKey_eraseKey` (binder 3): removable: eraseKey is a sublist (sublist_eraseKey)
theorem w2c5_62 : drop% Std.Internal.List.containsKey_of_containsKey_eraseKey 3 :=
   by
  intros; exact ck_sub sublist_eraseKey ‹_›

-- `Std.Internal.List.containsKey_of_containsKey_eraseKey` (binder 7): removable: eraseKey is a sublist (sublist_eraseKey)
theorem w2c5_63 : drop% Std.Internal.List.containsKey_of_containsKey_eraseKey 7 :=
   by
  intros; exact ck_sub sublist_eraseKey ‹_›

-- `Std.Internal.List.containsKey_of_containsKey_filter` (binder 3): removable: filter is a sublist
theorem w2c5_64 : drop% Std.Internal.List.containsKey_of_containsKey_filter 3 :=
   by
  intros; exact ck_sub List.filter_sublist ‹_›

-- `Std.Internal.List.containsKey_of_containsKey_filter` (binder 7): removable: filter is a sublist
theorem w2c5_65 : drop% Std.Internal.List.containsKey_of_containsKey_filter 7 :=
   by
  intros; exact ck_sub List.filter_sublist ‹_›

-- `Std.Internal.List.containsKey_of_containsKey_filter` (binder 8): l = []: conclusion containsKey k [] fails
theorem w2c5_66 : ¬ drop0% Std.Internal.List.containsKey_of_containsKey_filter 8 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (f := fun _ _ => true) (l := []) (k := 0) ⟨by decide⟩
  exact absurd this (by decide)

-- `Std.Internal.List.containsKey_of_containsKey_filterMap` (binder 4): removable: filterMap keeps each entry key, mem_filterMap (any BEq)
theorem w2c5_67 : drop% Std.Internal.List.containsKey_of_containsKey_filterMap 4 :=
   by
  intros; exact ck_fm ‹_›

-- `Std.Internal.List.containsKey_of_containsKey_filterMap` (binder 8): removable: filterMap keeps each entry key, mem_filterMap (any BEq)
theorem w2c5_68 : drop% Std.Internal.List.containsKey_of_containsKey_filterMap 8 :=
   by
  intros; exact ck_fm ‹_›

-- `Std.Internal.List.containsKey_of_containsKey_filterMap` (binder 9): l = []: conclusion containsKey k [] fails
theorem w2c5_69 : ¬ drop0% Std.Internal.List.containsKey_of_containsKey_filterMap 9 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (γ := fun _ => Nat) (f := fun _ _ => none) (l := []) (k := 0) ⟨by decide⟩
  exact absurd this (by decide)

-- `Std.Internal.List.containsKey_of_containsKey_filterMap'` (binder 9): removable: mem_filterMap plus hf and EquivBEq symm/trans; DistinctKeys unused
theorem w2c5_70 : drop% Std.Internal.List.containsKey_of_containsKey_filterMap' 9 :=
   by
  intro α β γ _ _ f hf l k h
  obtain ⟨p, hp, hk⟩ := ck_ex.1 h
  obtain ⟨q, hq, e⟩ := List.mem_filterMap.1 hp
  have := hf q; rw [e] at this; simp only [Option.all_some] at this
  exact ck_ex.2 ⟨q, hq, BEq.trans (BEq.symm this) hk⟩

-- `Std.Internal.List.containsKey_of_containsKey_insertEntry` (binder 3): removable: every entry of insertEntry k v l is from l or is k:v (any BEq)
theorem w2c5_71 : drop% Std.Internal.List.containsKey_of_containsKey_insertEntry 3 :=
   by
  intro α β _ l k a v h₁ h₂
  exact (ins_ck h₁).resolve_left (by simp [h₂])

-- `Std.Internal.List.containsKey_of_containsKey_insertEntryIfNew` (binder 3): removable: insertEntryIfNew is l or k:v :: l (any BEq)
theorem w2c5_72 : drop% Std.Internal.List.containsKey_of_containsKey_insertEntryIfNew 3 :=
   by
  intro α β _ l k a v h₁ h₂
  unfold insertEntryIfNew at h₁; split at h₁
  · exact h₁
  · simpa [containsKey, h₂] using h₁

-- `Std.Internal.List.containsKey_of_containsKey_insertEntryIfNew'` (binder 3): removable: insertEntryIfNew is l or k:v :: l (any BEq)
theorem w2c5_73 : drop% Std.Internal.List.containsKey_of_containsKey_insertEntryIfNew' 3 :=
   by
  intro α β _ l k a v h₁ h₂
  unfold insertEntryIfNew at h₁; split at h₁
  · exact h₁
  · rename_i hc
    simp only [containsKey, Bool.or_eq_true] at h₁
    rcases h₁ with e | e
    · exact absurd ⟨e, by simpa using hc⟩ h₂
    · exact e

-- `Std.Internal.List.containsKey_of_length_eq` (binder 6): Nat keys, duplicate key 0 in the list: l1 = [0, 0], l2 = [0, 1]; same length, l1 keys in l2, key 1 not in l1
theorem w2c5_74 : ¬ drop0% Std.Internal.List.containsKey_of_length_eq 6 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (l₁ := [⟨0,0⟩,⟨0,0⟩]) (l₂ := [⟨0,0⟩,⟨1,0⟩]) ⟨by decide⟩ rfl
    (by intro a ha; simp [Std.Internal.List.containsKey] at ha ⊢; omega) 1 (by decide)
  exact absurd this (by decide)

-- `Std.Internal.List.containsKey_of_length_eq` (binder 7): removable: induction on l1 erasing its head key from l2 (length_eraseKey, containsKey_eraseKey_of_false); EquivBEq and distinct l1 suffice
theorem w2c5_75 : drop% Std.Internal.List.containsKey_of_length_eq 7 :=
   by
  intro α β _ _ l₁ l₂ dl₁ hl hs; exact cle l₁ l₂ dl₁ hl hs

-- `Std.Internal.List.contains_of_contains_insertList_of_contains_eq_false_left` (binder 3): removable: induction on toInsert; every entry of insertEntry is from l or the inserted pair (any BEq)
theorem w2c5_76 : drop% Std.Internal.List.contains_of_contains_insertList_of_contains_eq_false_left 3 :=
   by
  intro α β _ l t k h₁ h₂; exact il_left t l h₁ h₂

-- `Std.Internal.List.contains_of_contains_insertList_of_contains_eq_false_right` (binder 3): removable: induction on toInsert; every entry of insertEntry is from l or the inserted pair (any BEq)
theorem w2c5_77 : drop% Std.Internal.List.contains_of_contains_insertList_of_contains_eq_false_right 3 :=
   by
  intro α β _ l t k h₁ h₂; exact il_right t l h₁ h₂

-- `Std.Internal.List.distinctKeys_interSmaller` (binder 3): NS: l1 = l2 = [1:0, 0:0]; inserting 1 then 0 conses 0 before 1, and 0 == 1
theorem w2c5_78 : ¬ drop0% Std.Internal.List.distinctKeys_interSmaller 3 :=
   fun h => by
  have := h (α := NS) (β := fun _ => Nat) (l₁ := [⟨1,0⟩,⟨0,0⟩]) (l₂ := [⟨1,0⟩,⟨0,0⟩])
  exact absurd this.1 (by decide +kernel)

-- `Std.Internal.List.distinctKeys_interSmallerFn` (binder 3): NS: sofar = [1], inserting key 0 from l = [0] conses it, and 0 == 1
theorem w2c5_79 : ¬ drop0% Std.Internal.List.distinctKeys_interSmallerFn 3 :=
   fun h => by
  have := h (α := NS) (β := fun _ => Nat) [⟨0,0⟩] [⟨1,0⟩] 0 ⟨by decide⟩
  exact absurd this.1 (by decide +kernel)

-- `Std.Internal.List.distinctKeys_of_sublist` (binder 5): l = [], l' = [0, 0]: no sublist relation
theorem w2c5_80 : ¬ drop0% Std.Internal.List.distinctKeys_of_sublist 5 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (l := []) (l' := [⟨0,0⟩,⟨0,0⟩]) ⟨.nil⟩
  exact absurd this.1 (by decide)

-- `Std.Internal.List.distinctKeys_of_sublist` (binder 6): l = l' = [0, 0] (Sublist.refl), not distinct
theorem w2c5_81 : ¬ drop0% Std.Internal.List.distinctKeys_of_sublist 6 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (l := [⟨0,0⟩,⟨0,0⟩]) (l' := [⟨0,0⟩,⟨0,0⟩]) (List.Sublist.refl _)
  exact absurd this.1 (by decide)

-- `Std.Internal.List.distinctKeys_of_sublist_keys` (binder 6): l = [], l' = [0, 0]: no sublist relation
theorem w2c5_82 : ¬ drop0% Std.Internal.List.distinctKeys_of_sublist_keys 6 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (γ := fun _ => Nat) (l := []) (l' := [⟨0,0⟩,⟨0,0⟩]) ⟨.nil⟩
  exact absurd this.1 (by decide)

-- `Std.Internal.List.distinctKeys_of_sublist_keys` (binder 7): l = l' = [0, 0] (Sublist.refl), not distinct
theorem w2c5_83 : ¬ drop0% Std.Internal.List.distinctKeys_of_sublist_keys 7 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (γ := fun _ => Nat) (l := [⟨0,0⟩,⟨0,0⟩]) (l' := [⟨0,0⟩,⟨0,0⟩]) (List.Sublist.refl _)
  exact absurd this.1 (by decide)

-- `Std.Internal.IsStrictCut.eq` (binder 3): cmp = lt, cut = eq: cut 0 = eq but cmp 0 0 = lt
theorem w2c5_84 : ¬ drop0% Std.Internal.IsStrictCut.eq 3 :=
   fun h => by
  have := h (α := Nat) (cmp := fun _ _ => .lt) (cut := fun _ => .eq) 0 (k' := 0) rfl
  exact absurd this (by decide)

-- `Std.Internal.IsStrictCut.eq` (binder 6): instance IsStrictCut compare (fun _ => lt) on Nat, k = k' = 0: cut 0 = lt, compare 0 0 = eq
theorem w2c5_85 : ¬ drop0% Std.Internal.IsStrictCut.eq 6 :=
   fun h => by
  have := h (α := Nat) (cmp := compare) (cut := fun _ => .lt) 0 (k' := 0)
  exact absurd this (by decide)

-- `Std.Internal.List.DistinctKeys.eq_of_mem_of_beq` (binder 3): NS: l = [1:0, 0:0] distinct, a = 0:0, b = 1:0, 0 == 1 but a, b differ
theorem w2c5_86 : ¬ drop0% Std.Internal.List.DistinctKeys.eq_of_mem_of_beq 3 :=
   fun h => by
  have := h (α := NS) (β := fun _ => Nat) (a := ⟨0,0⟩) (b := ⟨1,0⟩) (l := [⟨1,0⟩,⟨0,0⟩]) (by decide) (by decide) (by decide) ⟨by decide⟩
  exact absurd this (by decide)

-- `Std.Internal.List.DistinctKeys.eraseKey` (binder 3): removable: distinctKeys_of_sublist sublist_eraseKey (BEq only)
theorem w2c5_87 : drop% Std.Internal.List.DistinctKeys.eraseKey 3 :=
   by
  intro α β _ l k h; exact distinctKeys_of_sublist sublist_eraseKey h

-- `Std.Internal.List.eraseKey_of_perm` (binder 3): NS: l = [1, 0] distinct, l' = [0, 1], erase 1 removes key 1 from l but key 0 from l'
theorem w2c5_88 : ¬ drop0% Std.Internal.List.eraseKey_of_perm 3 :=
   fun h => by
  have := h (α := NS) (β := fun _ => Nat) (k := 1) (l := [⟨1,0⟩,⟨0,0⟩]) (l' := [⟨0,0⟩,⟨1,0⟩]) ⟨by decide⟩ (by decide)
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.eraseKey_of_perm` (binder 7): Nat keys, duplicate key 0 in the list: l = [0:0, 0:1] and its reverse, erasing 0 leaves different entries
theorem w2c5_89 : ¬ drop0% Std.Internal.List.eraseKey_of_perm 7 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (k := 0) (l := [⟨0,0⟩,⟨0,1⟩]) (l' := [⟨0,1⟩,⟨0,0⟩]) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.eraseList_perm_of_perm_first` (binder 3): NS: l = [1, 0] distinct, l' = [0, 1], erase 1 removes key 1 from l but key 0 from l'
theorem w2c5_90 : ¬ drop0% Std.Internal.List.eraseList_perm_of_perm_first 3 :=
   fun h => by
  have := h (α := NS) (β := fun _ => Nat) (toErase := [1]) (l1 := [⟨1,0⟩,⟨0,0⟩]) (l2 := [⟨0,0⟩,⟨1,0⟩]) (by decide) ⟨by decide⟩
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.eraseList_perm_of_perm_first` (binder 8): Nat keys, duplicate key 0 in the list: l = [0:0, 0:1] and its reverse, erasing 0 leaves different entries
theorem w2c5_91 : ¬ drop0% Std.Internal.List.eraseList_perm_of_perm_first 8 :=
   fun h => by
  have := h (α := Nat) (β := fun _ => Nat) (toErase := [0]) (l1 := [⟨0,0⟩,⟨0,1⟩]) (l2 := [⟨0,1⟩,⟨0,0⟩]) (by decide)
  exact absurd this (by decide +kernel)

-- `Std.Internal.List.find?_eq_none_iff_containsKey_eq_false` (binder 3): removable: find?_eq_none and containsKey_eq_true_iff_exists_mem use the same predicate fst == k
theorem w2c5_92 : drop% Std.Internal.List.find?_eq_none_iff_containsKey_eq_false 3 :=
   by
  intro α β _ l k
  rw [List.find?_eq_none, ← Bool.not_eq_true, ck_ex]; simp

-- `Std.Internal.List.find?_eq_some_iff_getValueCast?_eq_some` (binder 7): removable: both sides look at the first entry with key k; induction with LawfulBEq
theorem w2c5_93 : drop% Std.Internal.List.find?_eq_some_iff_getValueCast?_eq_some 7 :=
   by
  intro α β _ _ l k v
  induction l with
  | nil => simp
  | cons p t ih =>
    obtain ⟨k', v'⟩ := p
    by_cases hk : k' = k
    · subst hk; simp [List.find?_cons, getValueCast?_cons]
    · simp [List.find?_cons, getValueCast?_cons, hk, ih]

-- `Std.Internal.List.find?_map_eq_none_iff_containsKey_eq_false` (binder 2): removable: find?_eq_none and containsKey_eq_true_iff_exists_mem use the same predicate fst == k
theorem w2c5_94 : drop% Std.Internal.List.find?_map_eq_none_iff_containsKey_eq_false 2 :=
   by
  intro α _ β l k
  rw [List.find?_eq_none, ← Bool.not_eq_true, ck_ex]; simp

-- `Std.Internal.List.foldrM_eq_foldrM_keys` (binder 5): removable: foldrM is foldlM over reverse, and foldlM over a map unfolds definitionally (no monad laws)
theorem w2c5_95 : drop% Std.Internal.List.foldrM_eq_foldrM_keys 5 :=
   by
  intro α β δ m' _ l f init; rw [keys_eq_map, fr_map]

-- `Std.Internal.List.foldrM_eq_foldrM_keys'` (binder 5): removable: foldrM is foldlM over reverse, and foldlM over a map unfolds definitionally (no monad laws)
theorem w2c5_96 : drop% Std.Internal.List.foldrM_eq_foldrM_keys' 5 :=
   by
  intro α β δ m' _ l f init; rw [keys_eq_map, fr_map]

-- `Std.Internal.List.foldrM_eq_foldrM_toProd` (binder 5): removable: foldrM is foldlM over reverse, and foldlM over a map unfolds definitionally (no monad laws)
theorem w2c5_97 : drop% Std.Internal.List.foldrM_eq_foldrM_toProd 5 :=
   by
  intro α β δ m' _ l f init; rw [fr_map]

-- `Std.Internal.List.foldrM_eq_foldrM_toProd'` (binder 5): removable: foldrM is foldlM over reverse, and foldlM over a map unfolds definitionally (no monad laws)
theorem w2c5_98 : drop% Std.Internal.List.foldrM_eq_foldrM_toProd' 5 :=
   by
  intro α β δ m' _ l f init; rw [fr_map]

-- `Std.Internal.List.forall_mem_iff_forall_contains_getValueCast` (binder 3): Nat with == constantly false: l = [] distinct, but not LawfulBEq
theorem w2c5_99 : ¬ indep0% Std.Internal.List.forall_mem_iff_forall_contains_getValueCast 3 :=
   fun h => by
  let B : BEq Nat := ⟨fun _ _ => false⟩
  have := @h Nat (fun _ => Nat) B [] (fun _ _ => True) ⟨.nil⟩
  exact absurd (@ReflBEq.rfl Nat B this.toReflBEq 0) (by decide)

-- `Std.Internal.List.forall_mem_iff_forall_contains_getValueCast` (binder 6): Nat keys, duplicate key 0 in the list: l = [0:0, 0:1], p v = (v = 0): right side true, left false
theorem w2c5_100 : ¬ drop0% Std.Internal.List.forall_mem_iff_forall_contains_getValueCast 6 :=
   fun h => by
  have := (h (α := Nat) (β := fun _ => Nat) (l := [⟨0,0⟩,⟨0,1⟩]) (p := fun _ v => v = 0)).mpr (by
    intro a ha
    simp [Std.Internal.List.containsKey] at ha; subst ha; rfl)
  exact absurd (this ⟨0,1⟩ (by decide)) (by decide)

-- `Std.Internal.List.forall_mem_keys_iff_forall_containsKey_getKey` (binder 6): HB (halves): l = [0, 1] (0 == 1), p k = (k = 0); getKey always returns 0, but key 1 is in keys
theorem w2c5_101 : ¬ drop0% Std.Internal.List.forall_mem_keys_iff_forall_containsKey_getKey 6 :=
   fun h => by
  have := (h (α := HB) (β := fun _ => Nat) (l := [⟨⟨0⟩,0⟩,⟨⟨1⟩,0⟩]) (p := fun k => k.n = 0)).mpr (by
    intro k hk
    cases k with | mk n =>
    simp only [Std.Internal.List.containsKey, HB.beq_def] at hk
    simp only [Std.Internal.List.getKey, Std.Internal.List.getKey?]
    simp [HB.beq_def] at hk ⊢; simp [← hk])
  exact absurd (this ⟨1⟩ (by simp [Std.Internal.List.keys])) (by decide)

-- `Std.Internal.List.getEntry!_append_of_containsKey_eq_false` (binder 7): l = [], l' = [0:1], default 0:0: getEntry! 0 gives 0:1 vs default
theorem w2c5_102 : ¬ drop0% Std.Internal.List.getEntry!_append_of_containsKey_eq_false 7 :=
   fun h => by
  have := @h Nat (fun _ => Nat) _ [] [⟨0,1⟩] 0 ⟨⟨0,0⟩⟩
  exact absurd this (by decide)

-- `Std.Internal.List.getEntry!_cons_of_false` (binder 8): k = a = 0, l = [], default 0:0: getEntry! returns 0:1
theorem w2c5_103 : ¬ drop0% Std.Internal.List.getEntry!_cons_of_false 8 :=
   fun h => by
  have := @h Nat (fun _ => Nat) _ [] 0 0 1 ⟨⟨0,0⟩⟩
  exact absurd this (by decide)

-- `Std.Internal.List.getEntry!_cons_of_true` (binder 8): k = 1, a = 0, l = []: getEntry! returns default 0:0, not 1:1
theorem w2c5_104 : ¬ drop0% Std.Internal.List.getEntry!_cons_of_true 8 :=
   fun h => by
  have := @h Nat (fun _ => Nat) _ [] 1 0 1 ⟨⟨0,0⟩⟩
  exact absurd this (by decide)

-- `Std.Internal.IsCut.gt` (binder 3): cmp constant, cut 0 differs from cut 1 (no IsCut instance)
theorem w2c5_105 : ¬ drop0% Std.Internal.IsCut.gt 3 :=
   fun h => by
  have := h (α := Nat) (cmp := fun _ _ => .gt) (cut := fun k => if k = 0 then .gt else .lt) (k := 1) (k' := 0) rfl rfl
  exact absurd this (by decide)

-- `Std.Internal.IsCut.gt` (binder 7): Nat, cmp = compare, cut = compare 5 (a strict cut): the remaining premise holds at k', the conclusion fails at k
theorem w2c5_106 : ¬ drop0% Std.Internal.IsCut.gt 7 :=
   fun h => by
  have := h (α := Nat) (cmp := compare) (cut := compare 5) (k := 9) (k' := 0) rfl
  exact absurd this (by decide)

-- `Std.Internal.IsCut.gt` (binder 6): Nat, cmp = compare, cut = compare 5 (a strict cut): the remaining premise holds at k', the conclusion fails at k
theorem w2c5_107 : ¬ drop0% Std.Internal.IsCut.gt 6 :=
   fun h => by
  have := h (α := Nat) (cmp := compare) (cut := compare 5) (k := 9) (k' := 10) rfl
  exact absurd this (by decide)

-- `Std.Internal.IsStrictCut.gt_of_isGE_of_gt` (binder 6): Nat, cmp = compare, cut = compare 5 (a strict cut): the remaining premise holds at k', the conclusion fails at k
theorem w2c5_108 : ¬ drop0% Std.Internal.IsStrictCut.gt_of_isGE_of_gt 6 :=
   fun h => by
  have := h (α := Nat) (cmp := compare) (cut := compare 5) (k := 9) (k' := 10) rfl
  exact absurd this (by decide)

-- `Std.Internal.IsStrictCut.gt_of_isGE_of_gt` (binder 3): cmp constant, cut 0 differs from cut 1 (no IsCut instance)
theorem w2c5_109 : ¬ drop0% Std.Internal.IsStrictCut.gt_of_isGE_of_gt 3 :=
   fun h => by
  have := h (α := Nat) (cmp := fun _ _ => .gt) (cut := fun k => if k = 0 then .gt else .lt) (k := 1) (k' := 0) rfl rfl
  exact absurd this (by decide)

-- `Std.Internal.IsStrictCut.gt_of_isGE_of_gt` (binder 7): Nat, cmp = compare, cut = compare 5 (a strict cut): the remaining premise holds at k', the conclusion fails at k
theorem w2c5_110 : ¬ drop0% Std.Internal.IsStrictCut.gt_of_isGE_of_gt 7 :=
   fun h => by
  have := h (α := Nat) (cmp := compare) (cut := compare 5) (k := 9) (k' := 0) rfl
  exact absurd this (by decide)

-- `Std.Internal.instIsStrictCutCompare` (binder 2): OT (compare = eq iff equal, else lt): k = 0, k' = 1, the lt field yields compare 0 0 = lt
theorem w2c5_111 : ¬ drop0% Std.Internal.instIsStrictCutCompare 2 :=
   fun h => by
  have := (h (α := OT) (k := ⟨0⟩)).toIsCut.lt (k := ⟨0⟩) (k' := ⟨1⟩) (by decide) (by decide)
  exact absurd this (by decide)

-- `Std.Internal.instIsStrictCutCompareThenGt` (binder 2): OT (compare = eq iff equal, else lt): k = 0, k' = 1, the lt field yields compare 0 0 = lt
theorem w2c5_112 : ¬ drop0% Std.Internal.instIsStrictCutCompareThenGt 2 :=
   fun h => by
  have := (h (α := OT) (k := ⟨0⟩)).toIsCut.lt (k := ⟨0⟩) (k' := ⟨1⟩) (by decide) (by decide)
  exact absurd this (by decide)

-- `Std.Internal.IsCut.lt` (binder 3): cmp constant, cut 0 differs from cut 1 (no IsCut instance)
theorem w2c5_113 : ¬ drop0% Std.Internal.IsCut.lt 3 :=
   fun h => by
  have := h (α := Nat) (cmp := fun _ _ => .lt) (cut := fun k => if k = 0 then .lt else .gt) (k := 1) (k' := 0) rfl rfl
  exact absurd this (by decide)

-- `Std.Internal.IsCut.lt` (binder 7): Nat, cmp = compare, cut = compare 5 (a strict cut): the remaining premise holds at k', the conclusion fails at k
theorem w2c5_114 : ¬ drop0% Std.Internal.IsCut.lt 7 :=
   fun h => by
  have := h (α := Nat) (cmp := compare) (cut := compare 5) (k := 0) (k' := 9) rfl
  exact absurd this (by decide)

-- `Std.Internal.IsCut.lt` (binder 6): Nat, cmp = compare, cut = compare 5 (a strict cut): the remaining premise holds at k', the conclusion fails at k
theorem w2c5_115 : ¬ drop0% Std.Internal.IsCut.lt 6 :=
   fun h => by
  have := h (α := Nat) (cmp := compare) (cut := compare 5) (k := 1) (k' := 0) rfl
  exact absurd this (by decide)

-- `Std.Internal.IsStrictCut.lt_of_isLE_of_lt` (binder 6): Nat, cmp = compare, cut = compare 5 (a strict cut): the remaining premise holds at k', the conclusion fails at k
theorem w2c5_116 : ¬ drop0% Std.Internal.IsStrictCut.lt_of_isLE_of_lt 6 :=
   fun h => by
  have := h (α := Nat) (cmp := compare) (cut := compare 5) (k := 1) (k' := 0) rfl
  exact absurd this (by decide)

-- `Std.Internal.IsStrictCut.lt_of_isLE_of_lt` (binder 3): cmp constant, cut 0 differs from cut 1 (no IsCut instance)
theorem w2c5_117 : ¬ drop0% Std.Internal.IsStrictCut.lt_of_isLE_of_lt 3 :=
   fun h => by
  have := h (α := Nat) (cmp := fun _ _ => .lt) (cut := fun k => if k = 0 then .lt else .gt) (k := 1) (k' := 0) rfl rfl
  exact absurd this (by decide)

-- `Std.Internal.IsStrictCut.lt_of_isLE_of_lt` (binder 7): Nat, cmp = compare, cut = compare 5 (a strict cut): the remaining premise holds at k', the conclusion fails at k
theorem w2c5_118 : ¬ drop0% Std.Internal.IsStrictCut.lt_of_isLE_of_lt 7 :=
   fun h => by
  have := h (α := Nat) (cmp := compare) (cut := compare 5) (k := 0) (k' := 9) rfl
  exact absurd this (by decide)

-- `Std.Internal.IsStrictCut.toIsCut` (binder 3): cmp = lt, cut 0 = lt, cut 1 = gt: the lt field fails
theorem w2c5_119 : ¬ drop0% Std.Internal.IsStrictCut.toIsCut 3 :=
   fun h => by
  have := (h (α := Nat) (cmp := fun _ _ => .lt) (cut := fun k => if k = 0 then .lt else .gt)).lt (k := 1) (k' := 0) rfl rfl
  exact absurd this (by decide)
