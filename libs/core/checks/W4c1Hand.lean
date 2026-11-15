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

/-! # W4c1 helpers -/
set_option Elab.async false
set_option linter.unusedSimpArgs false
/-- Evaluates a hash-map union/inter/diff of literals, allowing one resize (copy of W2c0's union macro). -/
macro "w4c1b_ev" : tactic => `(tactic| (
  try simp only [Union.union, Inter.inter, SDiff.sdiff, HashSet.union, HashSet.Raw.union, HashMap.union, HashMap.Raw.union,
    DHashMap.union, HashSet.inter, HashSet.Raw.inter, HashMap.inter, HashMap.Raw.inter, DHashMap.inter,
    HashSet.diff, HashSet.Raw.diff, HashMap.diff, HashMap.Raw.diff, DHashMap.diff, drn_union]
  try simp only [HashSet.mem_iff_contains, HashMap.mem_iff_contains, DHashMap.mem_iff_contains, HashSet.Raw.mem_iff_contains,
    HashMap.Raw.mem_iff_contains, Std.DHashMap.Raw.mem_iff_contains, HashSet.contains, HashMap.contains, DHashMap.contains,
    HashSet.Raw.contains, HashMap.Raw.contains, HashSet.isEmpty, HashMap.isEmpty, DHashMap.isEmpty, HashSet.Raw.isEmpty,
    HashMap.Raw.isEmpty]
  try simp (disch := decide) only [dr_union_lit, hmr_empty, hsr_empty, dr_empty, dr_insert_lit]
  simp (config := {decide := true}) only [Raw₀.union, ite_false, ite_true]
  hm_expand))
namespace W4c1B
variable {α : Type u} [BEq α] [Hashable α]
-- a bucket that does not contain a returns the fallback (no instance needed)
theorem al_getD {γ : Type v} (l : AssocList α (fun _ => γ)) (a : α) (f : γ) (h : l.contains a = false) :
    l.getD a f = f := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.getD, h.1, cond_false]; exact ih h.2
theorem al_getKeyD {β : α → Type v} (l : AssocList α β) (a f : α) (h : l.contains a = false) :
    l.getKeyD a f = f := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.getKeyD, h.1]; exact ih h.2
theorem al_getCastD [LawfulBEq α] {β : α → Type v} (l : AssocList α β) (a : α) (f : β a) (h : l.contains a = false) :
    l.getCastD a f = f := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.getCastD, h.1]; exact ih h.2
theorem r0c_getD {γ : Type v} (m : Raw₀ α (fun _ => γ)) (a : α) (f : γ) (h : m.contains a = false) :
    Raw₀.Const.getD m a f = f := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h
  unfold Raw₀.Const.getD; simp only [Array.ugetElem_eq_getElem]; exact al_getD _ _ _ h
theorem r0_getKeyD {β : α → Type v} (m : Raw₀ α β) (a f : α) (h : m.contains a = false) :
    Raw₀.getKeyD m a f = f := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h
  unfold Raw₀.getKeyD; simp only [Array.ugetElem_eq_getElem]; exact al_getKeyD _ _ _ h
theorem r0_getD [LawfulBEq α] {β : α → Type v} (m : Raw₀ α β) (a : α) (f : β a) (h : m.contains a = false) :
    Raw₀.getD m a f = f := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h
  unfold Raw₀.getD; simp only [Array.ugetElem_eq_getElem]; exact al_getCastD _ _ _ h
theorem drc_getD {γ : Type v} (m : DHashMap.Raw α (fun _ => γ)) (a : α) (f : γ) (h : m.contains a = false) :
    DHashMap.Raw.Const.getD m a f = f := by
  unfold DHashMap.Raw.Const.getD; split
  · rename_i hb; unfold DHashMap.Raw.contains at h; rw [dif_pos hb] at h; exact r0c_getD _ _ _ h
  · rfl
theorem dr_getKeyD {β : α → Type v} (m : DHashMap.Raw α β) (a f : α) (h : m.contains a = false) :
    DHashMap.Raw.getKeyD m a f = f := by
  unfold DHashMap.Raw.getKeyD; split
  · rename_i hb; unfold DHashMap.Raw.contains at h; rw [dif_pos hb] at h; exact r0_getKeyD _ _ _ h
  · rfl
theorem dr_getD [LawfulBEq α] {β : α → Type v} (m : DHashMap.Raw α β) (a : α) (f : β a) (h : m.contains a = false) :
    DHashMap.Raw.getD m a f = f := by
  unfold DHashMap.Raw.getD; split
  · rename_i hb; unfold DHashMap.Raw.contains at h; rw [dif_pos hb] at h; exact r0_getD _ _ _ h
  · rfl
end W4c1B
namespace W4c1B
variable {α : Type u} [BEq α] [Hashable α]
-- filtering or erasing a bucket never makes a key appear (no instance needed)
theorem ck_any {β : α → Type v} (L : List ((a : α) × β a)) (k : α) :
    Std.Internal.List.containsKey k L = L.any (fun p => p.1 == k) := by
  induction L with
  | nil => rfl
  | cons p t ih => simp only [Std.Internal.List.containsKey, List.any_cons, ih]
theorem al_filter {β : α → Type v} (f : (a : α) → β a → Bool) (l : AssocList α β) (k : α)
    (h : (l.filter f).contains k = true) : l.contains k = true := by
  rw [AssocList.contains_eq, ck_any] at h ⊢
  rw [AssocList.toList_filter.any_eq] at h
  simp only [List.any_eq_true, List.mem_filter] at h ⊢
  obtain ⟨p, ⟨hp, _⟩, he⟩ := h; exact ⟨p, hp, he⟩
theorem mkIdx_map_toNat {γ δ : Type w} (bs : Array γ) (g : γ → δ) (h : 0 < (bs.map g).size) (x : UInt64) :
    (mkIdx (bs.map g).size h x).1.toNat = (mkIdx bs.size (by simpa using h) x).1.toNat :=
  congrArg USize.toNat (mkIdx_val_congr (by simp) h _ x)
theorem al_erase {β : α → Type v} (l : AssocList α β) (a k : α)
    (h : (l.erase a).contains k = true) : l.contains k = true := by
  induction l with
  | nil => exact h
  | cons k' v t ih =>
    simp only [AssocList.erase] at h
    cases hb : k' == a
    · rw [hb, Bool.cond_false] at h
      simp only [AssocList.contains, Bool.or_eq_true] at h ⊢; exact h.imp id ih
    · rw [hb, Bool.cond_true] at h
      simp only [AssocList.contains, Bool.or_eq_true]; exact Or.inr h
theorem r0_filter_nc {β : α → Type v} (f : (a : α) → β a → Bool) (m : Raw₀ α β) (k : α)
    (h : m.contains k = false) : (Raw₀.filter f m).contains k = false := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h
  unfold Raw₀.filter
  rw [contains_gen]
  apply Bool.eq_false_iff.2; intro h'
  simp only [Array.getElem_map, mkIdx_map_toNat] at h'
  rw [al_filter _ _ _ h'] at h; exact Bool.noConfusion h
theorem r0_erase_nc {β : α → Type v} (m : Raw₀ α β) (a k : α) (h : m.contains k = false) :
    (m.erase a).contains k = false := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [erase_gen]; split
  · rw [contains_gen] at h ⊢
    apply Bool.eq_false_iff.2; intro h'
    simp only [mkIdx_set_toNat, Array.getElem_set] at h'
    split at h'
    · rename_i he
      have := al_erase _ _ _ h'
      simp only [he] at this
      rw [this] at h; exact Bool.noConfusion h
    · rw [h'] at h; exact Bool.noConfusion h
  · exact h
theorem r0_diff_nc {β : α → Type v} (m₁ m₂ : Raw₀ α β) (k : α) (h : m₁.contains k = false) :
    (Raw₀.diff m₁ m₂).contains k = false := by
  unfold Raw₀.diff; split
  · exact r0_filter_nc _ _ _ h
  · exact (Raw₀.eraseManyEntries m₁ m₂.1).2 (fun m => m.contains k = false) (fun h' => r0_erase_nc _ _ _ h') h
theorem dr_nmd {β : α → Type v} (m₁ m₂ : DHashMap.Raw α β) (hw : m₁.WF) (k : α) (hn : ¬ k ∈ m₁) :
    ¬ k ∈ m₁ \ m₂ := by
  have hb := DHashMap.Raw.WF.size_buckets_pos _ hw
  simp only [DHashMap.Raw.mem_iff_contains, Bool.not_eq_true] at hn ⊢
  show (DHashMap.Raw.diff m₁ m₂).contains k = false
  unfold DHashMap.Raw.diff; rw [dif_pos hb]; split
  · unfold DHashMap.Raw.contains at hn ⊢; rw [dif_pos hb] at hn
    rw [dif_pos (Raw₀.diff ⟨m₁, hb⟩ ⟨m₂, ‹_›⟩).2]; exact r0_diff_nc _ _ _ hn
  · exact hn
theorem hmr_nmd {β : Type v} (m₁ m₂ : HashMap.Raw α β) (hw : m₁.WF) (k : α) (hn : ¬ k ∈ m₁) : ¬ k ∈ m₁ \ m₂ :=
  dr_nmd m₁.inner m₂.inner hw.out k hn
theorem hsr_nmd (m₁ m₂ : HashSet.Raw α) (hw : m₁.WF) (k : α) (hn : ¬ k ∈ m₁) : ¬ k ∈ m₁ \ m₂ :=
  hmr_nmd m₁.inner m₂.inner hw.out k hn
theorem dh_nmd {β : α → Type v} (m₁ m₂ : DHashMap α β) (k : α) (hn : ¬ k ∈ m₁) : ¬ k ∈ m₁ \ m₂ := by
  simp only [DHashMap.mem_iff_contains, Bool.not_eq_true] at hn ⊢
  exact r0_diff_nc _ _ _ hn
theorem hm_nmd {β : Type v} (m₁ m₂ : HashMap α β) (k : α) (hn : ¬ k ∈ m₁) : ¬ k ∈ m₁ \ m₂ :=
  dh_nmd m₁.inner m₂.inner k hn
theorem hs_nmd (m₁ m₂ : HashSet α) (k : α) (hn : ¬ k ∈ m₁) : ¬ k ∈ m₁ \ m₂ :=
  hm_nmd m₁.inner m₂.inner k hn
end W4c1B
namespace W4c1B
variable {α : Type u} [BEq α] [Hashable α]
-- an empty WF m₁ has size 0, so diff / inter take the filter branch, whose size is at most m₁.size
theorem r0_ied [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : Raw₀ α β) (h₁ : m₁.1.WF)
    (h : m₁.1.isEmpty = true) : (m₁.diff m₂).1.isEmpty = true := by
  obtain ⟨m₁, hb⟩ := m₁
  have hs : m₁.size = 0 := by simpa [DHashMap.Raw.isEmpty] using h
  have e : (Raw₀.diff ⟨m₁, hb⟩ m₂).1 = m₁.filter (fun k _ => !m₂.contains k) := by
    unfold Raw₀.diff DHashMap.Raw.filter; rw [if_pos (by simp [hs]), dif_pos hb]
  have : (m₁.filter (fun k (_ : β k) => !m₂.contains k)).size ≤ m₁.size := DHashMap.Raw.size_filter_le_size h₁
  rw [e]; simp only [DHashMap.Raw.isEmpty, beq_iff_eq]; omega
theorem r0_iil [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : Raw₀ α β) (h₁ : m₁.1.WF)
    (h : m₁.1.isEmpty = true) : (m₁.inter m₂).1.isEmpty = true := by
  obtain ⟨m₁, hb⟩ := m₁
  have hs : m₁.size = 0 := by simpa [DHashMap.Raw.isEmpty] using h
  have e : (Raw₀.inter ⟨m₁, hb⟩ m₂).1 = m₁.filter (fun k _ => m₂.contains k) := by
    unfold Raw₀.inter DHashMap.Raw.filter; rw [if_pos (by simp [hs]), dif_pos hb]
  have : (m₁.filter (fun k (_ : β k) => m₂.contains k)).size ≤ m₁.size := DHashMap.Raw.size_filter_le_size h₁
  rw [e]; simp only [DHashMap.Raw.isEmpty, beq_iff_eq]; omega
theorem dr_ied [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : DHashMap.Raw α β) (h₁ : m₁.WF)
    (h : m₁.isEmpty = true) : (m₁ \ m₂).isEmpty = true := by
  have hb := DHashMap.Raw.WF.size_buckets_pos _ h₁
  show (DHashMap.Raw.diff m₁ m₂).isEmpty = true
  unfold DHashMap.Raw.diff; rw [dif_pos hb]; split
  · exact r0_ied ⟨m₁, hb⟩ _ h₁ h
  · exact h
theorem dr_iil [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : DHashMap.Raw α β) (h₁ : m₁.WF)
    (h : m₁.isEmpty = true) : (m₁ ∩ m₂).isEmpty = true := by
  have hb := DHashMap.Raw.WF.size_buckets_pos _ h₁
  show (DHashMap.Raw.inter m₁ m₂).isEmpty = true
  unfold DHashMap.Raw.inter; rw [dif_pos hb]; split
  · exact r0_iil ⟨m₁, hb⟩ _ h₁ h
  · exact h
theorem hmr_ied [EquivBEq α] [LawfulHashable α] {β : Type v} (m₁ m₂ : HashMap.Raw α β) (h₁ : m₁.WF)
    (h : m₁.isEmpty = true) : (m₁ \ m₂).isEmpty = true := dr_ied m₁.inner m₂.inner h₁.out h
theorem hmr_iil [EquivBEq α] [LawfulHashable α] {β : Type v} (m₁ m₂ : HashMap.Raw α β) (h₁ : m₁.WF)
    (h : m₁.isEmpty = true) : (m₁ ∩ m₂).isEmpty = true := dr_iil m₁.inner m₂.inner h₁.out h
theorem hsr_ied [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashSet.Raw α) (h₁ : m₁.WF)
    (h : m₁.isEmpty = true) : (m₁ \ m₂).isEmpty = true := hmr_ied m₁.inner m₂.inner h₁.out h
theorem hsr_iil [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashSet.Raw α) (h₁ : m₁.WF)
    (h : m₁.isEmpty = true) : (m₁ ∩ m₂).isEmpty = true := hmr_iil m₁.inner m₂.inner h₁.out h
end W4c1B
namespace W4c1B
variable {α : Type u} [BEq α] [Hashable α]
-- an empty WF m₂ contains nothing: the filter branch empties every bucket, the fold branch folds over no entries
theorem r0_iir [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : Raw₀ α β) (h₂ : m₂.1.WF)
    (h : m₂.1.isEmpty = true) : (m₁.inter m₂).1.isEmpty = true := by
  have hc : ∀ k, m₂.contains k = false := fun k => by
    have := DHashMap.Raw.contains_of_isEmpty (a := k) h₂ h
    simpa [DHashMap.Raw.contains, m₂.2] using this
  unfold Raw₀.inter; split
  · obtain ⟨⟨s, bs⟩, hb⟩ := m₁
    unfold Raw₀.filter
    simp only [DHashMap.Raw.isEmpty, beq_iff_eq]
    have hz : ∀ l : AssocList α β, (l.filter (fun k _ => m₂.contains k)).length = 0 := by
      intro l; rw [AssocList.length_eq, AssocList.toList_filter.length_eq]; simp [hc]
    unfold computeSize; rw [Array.foldl_map]; simp only [hz, Nat.add_zero]
    exact Array.foldl_induction (motive := fun _ d => d = 0) rfl (fun _ _ h => h)
  · unfold Raw₀.interSmaller
    rw [DHashMap.Raw.fold_eq_foldl_toList h₂]
    have : m₂.1.toList = [] := by rw [← List.isEmpty_iff, DHashMap.Raw.isEmpty_toList h₂]; exact h
    rw [this]; rfl
theorem dr_iir [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : DHashMap.Raw α β) (h₂ : m₂.WF)
    (h : m₂.isEmpty = true) : (m₁ ∩ m₂).isEmpty = true := by
  have hb := DHashMap.Raw.WF.size_buckets_pos _ h₂
  show (DHashMap.Raw.inter m₁ m₂).isEmpty = true
  unfold DHashMap.Raw.inter; split
  · exact r0_iir _ ⟨m₂, hb⟩ h₂ h
  · exact h
theorem hmr_iir [EquivBEq α] [LawfulHashable α] {β : Type v} (m₁ m₂ : HashMap.Raw α β) (h₂ : m₂.WF)
    (h : m₂.isEmpty = true) : (m₁ ∩ m₂).isEmpty = true := dr_iir m₁.inner m₂.inner h₂.out h
theorem hsr_iir [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashSet.Raw α) (h₂ : m₂.WF)
    (h : m₂.isEmpty = true) : (m₁ ∩ m₂).isEmpty = true := hmr_iir m₁.inner m₂.inner h₂.out h
end W4c1B
namespace W4c1B
variable {α : Type u} [BEq α] [Hashable α]
-- (copy of W2c0.contains_insert_of) insert keeps every found key, on arbitrary raw maps
theorem contains_insert_of [EquivBEq α] [LawfulHashable α] {β : α → Type v}
    (m : Raw₀ α β) (a : α) (b : β a) (k : α) (h : m.contains k = true) : (m.insert a b).contains k = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.insert
  dsimp only
  split
  · rw [contains_gen] at h ⊢
    simp only [Array.uset, mkIdx_set_toNat, Array.getElem_set]
    split
    · rename_i he
      simp only [Array.ugetElem_eq_getElem]
      rw [AssocList.contains_eq, AssocList.toList_replace, Std.Internal.List.containsKey_replaceEntry, ← AssocList.contains_eq]
      simp only [he]; exact h
    · exact h
  · apply W1c5.contains_expandIfNecessary
    rw [contains_gen] at h ⊢
    simp only [Array.uset, mkIdx_set_toNat, Array.getElem_set]
    split
    · rename_i he
      apply W1c5.assoc_contains_cons
      simp only [Array.ugetElem_eq_getElem]
      simp only [he]; exact h
    · exact h
-- insert / insertIfNew make their own key found
theorem ins_self [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insert a b).contains a = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.insert
  dsimp only
  split
  · rename_i hc
    rw [contains_gen]
    simp only [Array.uset, mkIdx_set_toNat, Array.getElem_set, if_true, Array.ugetElem_eq_getElem]
    rw [AssocList.contains_eq, AssocList.toList_replace, Std.Internal.List.containsKey_replaceEntry, ← AssocList.contains_eq]
    simpa [Array.ugetElem_eq_getElem] using hc
  · apply W1c5.contains_expandIfNecessary
    rw [contains_gen]
    simp only [Array.uset, mkIdx_set_toNat, Array.getElem_set, if_true]
    simp [AssocList.contains]
theorem insIfNew_self [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insertIfNew a b).contains a = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.insertIfNew
  dsimp only
  split
  · rename_i hc; rw [contains_gen]; simpa [Array.ugetElem_eq_getElem] using hc
  · apply W1c5.contains_expandIfNecessary
    rw [contains_gen]
    simp only [Array.uset, mkIdx_set_toNat, Array.getElem_set, if_true]
    simp [AssocList.contains]
theorem r0_cc [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m : Raw₀ α β) (a b : α) (hab : (a == b) = true)
    (h : m.contains a = true) : m.contains b = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h ⊢
  rw [← LawfulHashable.hash_eq a b hab]
  rw [AssocList.contains_eq, ck_any] at h ⊢
  simp only [List.any_eq_true] at h ⊢
  obtain ⟨p, hp, he⟩ := h; exact ⟨p, hp, BEq.trans he hab⟩
theorem mem_tlm {β : α → Type v} (m : Raw₀ α β) (k : α) (h : m.contains k = true) :
    ∃ p ∈ toListModel m.1.buckets, (p.1 == k) = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen, AssocList.contains_eq, ck_any] at h
  simp only [List.any_eq_true] at h
  obtain ⟨p, hp, he⟩ := h
  exact ⟨p, List.mem_flatMap.2 ⟨_, Array.getElem_mem_toList _, hp⟩, he⟩
theorem ilin_keep [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m : Raw₀ α β) (L : List ((a : α) × β a)) (k : α)
    (h : m.contains k = true) : (Raw₀.insertListIfNewₘ m L).contains k = true := by
  induction L generalizing m with
  | nil => exact h
  | cons hd tl ih => exact ih _ (W1c5.contains_insertIfNew_of _ _ _ _ h)
theorem ilm_keep [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m : Raw₀ α β) (L : List ((a : α) × β a)) (k : α)
    (h : m.contains k = true) : (Raw₀.insertListₘ m L).contains k = true := by
  induction L generalizing m with
  | nil => exact h
  | cons hd tl ih => exact ih _ (contains_insert_of _ _ _ _ h)
theorem ilin_mem [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m : Raw₀ α β) (L : List ((a : α) × β a))
    (p : (a : α) × β a) (hp : p ∈ L) : (Raw₀.insertListIfNewₘ m L).contains p.1 = true := by
  induction L generalizing m with
  | nil => cases hp
  | cons hd tl ih =>
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ilin_keep (m.insertIfNew _ _) tl _ (insIfNew_self _ _ _)
    · exact ih _ hp
theorem ilm_mem [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m : Raw₀ α β) (L : List ((a : α) × β a))
    (p : (a : α) × β a) (hp : p ∈ L) : (Raw₀.insertListₘ m L).contains p.1 = true := by
  induction L generalizing m with
  | nil => cases hp
  | cons hd tl ih =>
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ilm_keep (m.insert _ _) tl _ (ins_self _ _ _)
    · exact ih _ hp
-- a key found in either map is found in the union, for arbitrary (also ill-formed) maps with buckets
theorem r0_mul [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : Raw₀ α β) (k : α)
    (h : m₁.contains k = true) : (m₁.union m₂).contains k = true := by
  rw [Raw₀.union_eq_unionₘ]; unfold Raw₀.unionₘ; split
  · obtain ⟨p, hp, he⟩ := mem_tlm m₁ k h; exact r0_cc _ _ _ he (ilin_mem _ _ _ hp)
  · exact ilm_keep _ _ _ h
theorem r0_mur [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : Raw₀ α β) (k : α)
    (h : m₂.contains k = true) : (m₁.union m₂).contains k = true := by
  rw [Raw₀.union_eq_unionₘ]; unfold Raw₀.unionₘ; split
  · exact ilin_keep _ _ _ h
  · obtain ⟨p, hp, he⟩ := mem_tlm m₂ k h; exact r0_cc _ _ _ he (ilm_mem _ _ _ hp)
theorem dr_mul [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : DHashMap.Raw α β) (k : α)
    (h : k ∈ m₁) : k ∈ m₁ ∪ m₂ := by
  simp only [DHashMap.Raw.mem_iff_contains] at h ⊢
  show (DHashMap.Raw.union m₁ m₂).contains k = true
  unfold DHashMap.Raw.contains at h; split at h
  · rename_i h1; unfold DHashMap.Raw.union; rw [dif_pos h1]; split
    · rename_i h2; unfold DHashMap.Raw.contains; rw [dif_pos (Raw₀.union ⟨m₁, h1⟩ ⟨m₂, h2⟩).2]; exact r0_mul _ _ _ h
    · unfold DHashMap.Raw.contains; rw [dif_pos h1]; exact h
  · cases h
theorem dr_mur [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : DHashMap.Raw α β) (k : α)
    (h : k ∈ m₂) : k ∈ m₁ ∪ m₂ := by
  simp only [DHashMap.Raw.mem_iff_contains] at h ⊢
  show (DHashMap.Raw.union m₁ m₂).contains k = true
  unfold DHashMap.Raw.contains at h; split at h
  · rename_i h2; unfold DHashMap.Raw.union; split
    · rename_i h1; unfold DHashMap.Raw.contains; rw [dif_pos (Raw₀.union ⟨m₁, h1⟩ ⟨m₂, h2⟩).2]; exact r0_mur _ _ _ h
    · unfold DHashMap.Raw.contains; rw [dif_pos h2]; exact h
  · cases h
theorem hmr_mul [EquivBEq α] [LawfulHashable α] {β : Type v} (m₁ m₂ : HashMap.Raw α β) (k : α) (h : k ∈ m₁) :
    k ∈ m₁ ∪ m₂ := dr_mul m₁.inner m₂.inner k h
theorem hmr_mur [EquivBEq α] [LawfulHashable α] {β : Type v} (m₁ m₂ : HashMap.Raw α β) (k : α) (h : k ∈ m₂) :
    k ∈ m₁ ∪ m₂ := dr_mur m₁.inner m₂.inner k h
theorem hsr_mul [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashSet.Raw α) (k : α) (h : k ∈ m₁) :
    k ∈ m₁ ∪ m₂ := hmr_mul m₁.inner m₂.inner k h
theorem hsr_mur [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashSet.Raw α) (k : α) (h : k ∈ m₂) :
    k ∈ m₁ ∪ m₂ := hmr_mur m₁.inner m₂.inner k h
end W4c1B
namespace W4c1B
variable {α : Type u} [BEq α] [Hashable α]
theorem al_filter_ex {β : α → Type v} (f : (a : α) → β a → Bool) (l : AssocList α β) (k : α)
    (h : (l.filter f).contains k = true) : ∃ p ∈ l.toList, f p.1 p.2 = true ∧ (p.1 == k) = true := by
  rw [AssocList.contains_eq, ck_any, AssocList.toList_filter.any_eq] at h
  simp only [List.any_eq_true, List.mem_filter] at h
  obtain ⟨p, ⟨hp, hf⟩, he⟩ := h; exact ⟨p, hp, hf, he⟩
theorem al_getEntry {β : α → Type v} (l : AssocList α β) (a : α) (e : (a : α) × β a)
    (h : l.getEntry? a = some e) : (e.1 == a) = true := by
  induction l with
  | nil => cases h
  | cons k v t ih =>
    simp only [AssocList.getEntry?] at h
    split at h
    · cases h; assumption
    · exact ih h
theorem r0_getEntry {β : α → Type v} (m : Raw₀ α β) (a : α) (e : (a : α) × β a)
    (h : m.getEntry? a = some e) : (e.1 == a) = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getEntry? at h; simp only [Array.ugetElem_eq_getElem] at h
  exact al_getEntry _ _ _ h
-- k ∉ m₂ (m₂ WF) ⇒ k ∉ m₁ ∩ m₂ for an arbitrary m₁ with buckets
theorem r0_nmi [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : Raw₀ α β) (h₂ : m₂.1.WF) (k : α)
    (hn : m₂.contains k = false) : (m₁.inter m₂).contains k = false := by
  unfold Raw₀.inter; split
  · obtain ⟨⟨s, bs⟩, hb⟩ := m₁
    unfold Raw₀.filter; rw [contains_gen]
    apply Bool.eq_false_iff.2; intro h'
    simp only [Array.getElem_map, mkIdx_map_toNat] at h'
    obtain ⟨p, -, hf, he⟩ := al_filter_ex _ _ _ h'
    rw [r0_cc _ _ _ he hf] at hn; exact Bool.noConfusion hn
  · unfold Raw₀.interSmaller
    rw [DHashMap.Raw.fold_eq_foldl_toList h₂]
    have hL : ∀ q ∈ m₂.1.toList, m₂.contains q.1 = true := by
      intro q hq
      have h1 : q.1 ∈ m₂.1.keys := by
        rw [← DHashMap.Raw.map_fst_toList_eq_keys h₂]; exact List.mem_map_of_mem hq
      have := DHashMap.Raw.contains_keys h₂ (k := q.1)
      have h3 : m₂.1.keys.contains q.1 = true := List.elem_eq_true_of_mem h1
      rw [this] at h3
      simpa [DHashMap.Raw.contains, m₂.2] using h3
    suffices H : ∀ (L : List ((a : α) × β a)) (s : Raw₀ α β), (∀ q ∈ L, m₂.contains q.1 = true) → s.1.WF →
        (∀ k, s.contains k = true → m₂.contains k = true) → ∀ k,
        (L.foldl (fun sofar q => Raw₀.interSmallerFn m₁ sofar q.1) s).contains k = true → m₂.contains k = true by
      apply Bool.eq_false_iff.2; intro h'
      have := H _ _ hL DHashMap.Raw.WF.emptyWithCapacity₀
        (fun k hk => by rw [Raw₀.contains_emptyWithCapacity] at hk; exact Bool.noConfusion hk) k h'
      rw [this] at hn; exact Bool.noConfusion hn
    intro L; induction L with
    | nil => intro s _ _ hs; exact hs
    | cons q t ih =>
      intro s hq hw hs; simp only [List.foldl_cons]
      apply ih _ (fun q' h => hq q' (List.mem_cons_of_mem _ h))
      · unfold Raw₀.interSmallerFn; split
        · exact DHashMap.Raw.WF.insert₀ hw
        · exact hw
      · intro k hk; unfold Raw₀.interSmallerFn at hk; split at hk
        · rename_i e he
          rw [Raw₀.contains_insert _ hw] at hk
          rcases Bool.or_eq_true_iff.1 hk with hk | hk
          · exact r0_cc _ _ _ (BEq.trans (BEq.symm (r0_getEntry _ _ _ he)) hk) (hq q List.mem_cons_self)
          · exact hs k hk
        · exact hs k hk
theorem dr_nmi [EquivBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : DHashMap.Raw α β) (h₂ : m₂.WF) (k : α)
    (hn : ¬ k ∈ m₂) : ¬ k ∈ m₁ ∩ m₂ := by
  have hb := DHashMap.Raw.WF.size_buckets_pos _ h₂
  simp only [DHashMap.Raw.mem_iff_contains, Bool.not_eq_true] at hn ⊢
  show (DHashMap.Raw.inter m₁ m₂).contains k = false
  unfold DHashMap.Raw.contains at hn; rw [dif_pos hb] at hn
  unfold DHashMap.Raw.inter; split
  · rename_i h1
    unfold DHashMap.Raw.contains; rw [dif_pos (Raw₀.inter ⟨m₁, h1⟩ ⟨m₂, hb⟩).2]; exact r0_nmi _ _ h₂ _ hn
  · unfold DHashMap.Raw.contains; rw [dif_pos hb]; exact hn
theorem hmr_nmi [EquivBEq α] [LawfulHashable α] {β : Type v} (m₁ m₂ : HashMap.Raw α β) (h₂ : m₂.WF) (k : α)
    (hn : ¬ k ∈ m₂) : ¬ k ∈ m₁ ∩ m₂ := dr_nmi m₁.inner m₂.inner h₂.out k hn
theorem hsr_nmi [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashSet.Raw α) (h₂ : m₂.WF) (k : α)
    (hn : ¬ k ∈ m₂) : ¬ k ∈ m₁ ∩ m₂ := hmr_nmi m₁.inner m₂.inner h₂.out k hn
end W4c1B



namespace W4c1A
open Std Std.DHashMap.Internal Probe2
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
-- insert never lowers the size field (no laws needed)
theorem ins_ge [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    m.1.size ≤ (m.insert a b).1.size := by
  obtain ⟨⟨s, bs⟩, h⟩ := m; unfold Raw₀.insert; dsimp only; split
  · exact Nat.le_refl _
  · rw [expand_size]; exact Nat.le_succ _
theorem im_ge [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (m : Raw₀ α β) (l : ρ) :
    m.1.size ≤ (m.insertMany l).1.1.size :=
  (m.insertMany l).2 (fun m' => m.1.size ≤ m'.1.size) (fun h => Nat.le_trans h (ins_ge _ _ _)) (Nat.le_refl _)
theorem cim_ge [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × γ)] (m : Raw₀ α (fun _ => γ)) (l : ρ) :
    m.1.size ≤ (Raw₀.Const.insertMany m l).1.1.size :=
  (Raw₀.Const.insertMany m l).2 (fun m' => m.1.size ≤ m'.1.size) (fun h => Nat.le_trans h (ins_ge _ _ _)) (Nat.le_refl _)
theorem cimu_ge [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (m : Raw₀ α (fun _ => Unit)) (l : ρ) :
    m.1.size ≤ (Raw₀.Const.insertManyIfNewUnit m l).1.1.size :=
  (Raw₀.Const.insertManyIfNewUnit m l).2 (fun m' => m.1.size ≤ m'.1.size)
    (fun h => Nat.le_trans h (insertIfNew_size_ge _ _ _)) (Nat.le_refl _)
-- lookups in a bucket that does not contain the key
theorem a_getKey?_none [BEq α] (l : AssocList α β) (k : α) (h : l.contains k = false) : l.getKey? k = none := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.getKey?, h.1]; exact ih h.2
theorem a_cget?_some [BEq α] (l : AssocList α (fun _ => γ)) (k : α) (fb : γ) (h : l.contains k = true) :
    l.get? k = some (l.getD k fb) := by
  induction l with
  | nil => cases h
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_true] at h
    cases hk : (k' == k) <;> simp_all [AssocList.get?, AssocList.getD]
theorem a_getKey?_some [BEq α] (l : AssocList α β) (k : α) (fb : α) (h : l.contains k = true) :
    l.getKey? k = some (l.getKeyD k fb) := by
  induction l with
  | nil => cases h
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_true] at h
    cases hk : (k' == k) <;> simp_all [AssocList.getKey?, AssocList.getKeyD]
theorem a_getCast?_some [BEq α] [LawfulBEq α] (l : AssocList α β) (k : α) (fb : β k) (h : l.contains k = true) :
    l.getCast? k = some (l.getCastD k fb) := by
  induction l with
  | nil => cases h
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_true] at h
    cases hk : (k' == k) <;> simp_all [AssocList.getCast?, AssocList.getCastD]
end

section
variable {α : Type u} {β : α → Type v} {γ : Type v}
theorem cce_dr [BEq α] [Hashable α] (m : DHashMap.Raw α β) (k a : α) (h : (m.erase k).contains a = true) :
    m.contains a = true := by
  unfold DHashMap.Raw.erase at h
  split at h
  · rename_i hb
    simp only [DHashMap.Raw.contains, (Raw₀.erase ⟨m, hb⟩ k).2, dite_true] at h
    simp only [DHashMap.Raw.contains, hb, dite_true]
    exact raw0_contains_of_contains_erase ⟨m, hb⟩ k a h
  · exact h
theorem im_dr [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (m : DHashMap.Raw α β) (l : ρ) :
    m.size ≤ (m.insertMany l).size := by
  unfold DHashMap.Raw.insertMany; split
  · exact im_ge ⟨m, ‹_›⟩ l
  · exact Nat.le_refl _
theorem im_drc [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × γ)] (m : DHashMap.Raw α (fun _ => γ)) (l : ρ) :
    m.size ≤ (DHashMap.Raw.Const.insertMany m l).size := by
  unfold DHashMap.Raw.Const.insertMany; split
  · exact cim_ge ⟨m, ‹_›⟩ l
  · exact Nat.le_refl _
theorem im_dru [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (m : DHashMap.Raw α (fun _ => Unit)) (l : ρ) :
    m.size ≤ (DHashMap.Raw.Const.insertManyIfNewUnit m l).size := by
  unfold DHashMap.Raw.Const.insertManyIfNewUnit; split
  · exact cimu_ge ⟨m, ‹_›⟩ l
  · exact Nat.le_refl _
-- Raw₀ lookups of an absent / present key
theorem r0c_get?_nc [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (k : α) (h : m.contains k = false) :
    Raw₀.Const.get? m k = none := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; rw [cget?_gen]; exact assoc_cget?_none _ _ h
theorem r0_getKey?_nc [BEq α] [Hashable α] (m : Raw₀ α β) (k : α) (h : m.contains k = false) :
    m.getKey? k = none := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.getKey?; simp only [Array.ugetElem_eq_getElem]; exact a_getKey?_none _ _ h
theorem r0_get?_nc [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k : α) (h : m.contains k = false) :
    m.get? k = none := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.get?; simp only [Array.ugetElem_eq_getElem]; exact assoc_getCast?_none _ _ h
theorem r0c_get?_c [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (k : α) (fb : γ) (h : m.contains k = true) :
    Raw₀.Const.get? m k = some (Raw₀.Const.getD m k fb) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.Const.get? Raw₀.Const.getD; simp only [Array.ugetElem_eq_getElem]
  exact a_cget?_some _ _ _ h
theorem r0_getKey?_c [BEq α] [Hashable α] (m : Raw₀ α β) (k : α) (fb : α) (h : m.contains k = true) :
    m.getKey? k = some (m.getKeyD k fb) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.getKey? Raw₀.getKeyD; simp only [Array.ugetElem_eq_getElem]
  exact a_getKey?_some _ _ _ h
theorem r0_get?_c [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k : α) (fb : β k) (h : m.contains k = true) :
    m.get? k = some (m.getD k fb) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.get? Raw₀.getD; simp only [Array.ugetElem_eq_getElem]
  exact a_getCast?_some _ _ _ h
-- the same on raw maps (no buckets: nothing is found)
theorem drc_get?_nc [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => γ)) (k : α) (h : ¬ k ∈ m) :
    DHashMap.Raw.Const.get? m k = none := by
  unfold DHashMap.Raw.Const.get?; split
  · rename_i hb; exact r0c_get?_nc _ k (by simpa [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, hb] using h)
  · rfl
theorem drc_get!_nc [BEq α] [Hashable α] [Inhabited γ] (m : DHashMap.Raw α (fun _ => γ)) (k : α) (h : ¬ k ∈ m) :
    DHashMap.Raw.Const.get! m k = default := by
  unfold DHashMap.Raw.Const.get!; split
  · rename_i hb; exact raw0_cget!_nc _ k (by simpa [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, hb] using h)
  · rfl
theorem dr_getKey?_nc [BEq α] [Hashable α] (m : DHashMap.Raw α β) (k : α) (h : ¬ k ∈ m) :
    m.getKey? k = none := by
  unfold DHashMap.Raw.getKey?; split
  · rename_i hb; exact r0_getKey?_nc _ k (by simpa [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, hb] using h)
  · rfl
theorem dr_getKey!_nc [BEq α] [Hashable α] [Inhabited α] (m : DHashMap.Raw α β) (k : α) (h : ¬ k ∈ m) :
    m.getKey! k = default := by
  unfold DHashMap.Raw.getKey!; split
  · rename_i hb; exact raw0_getKey!_nc _ k (by simpa [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, hb] using h)
  · rfl
theorem dr_get?_nc [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k : α) (h : ¬ k ∈ m) :
    m.get? k = none := by
  unfold DHashMap.Raw.get?; split
  · rename_i hb; exact r0_get?_nc _ k (by simpa [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, hb] using h)
  · rfl
theorem dr_get!_nc [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k : α) [Inhabited (β k)] (h : ¬ k ∈ m) :
    m.get! k = default := by
  unfold DHashMap.Raw.get!; split
  · rename_i hb; exact raw0_get!_nc _ k (by simpa [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, hb] using h)
  · rfl
theorem drc_get?_c [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => γ)) (k : α) (fb : γ) (h : k ∈ m) :
    DHashMap.Raw.Const.get? m k = some (DHashMap.Raw.Const.getD m k fb) := by
  unfold DHashMap.Raw.Const.get? DHashMap.Raw.Const.getD; split
  · rename_i hb; exact r0c_get?_c _ k fb (by simpa [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, hb] using h)
  · rename_i hb; simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, hb] at h
theorem dr_getKey?_c [BEq α] [Hashable α] (m : DHashMap.Raw α β) (k : α) (fb : α) (h : k ∈ m) :
    m.getKey? k = some (m.getKeyD k fb) := by
  unfold DHashMap.Raw.getKey? DHashMap.Raw.getKeyD; split
  · rename_i hb; exact r0_getKey?_c _ k fb (by simpa [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, hb] using h)
  · rename_i hb; simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, hb] at h
theorem dr_get?_c [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k : α) (fb : β k) (h : k ∈ m) :
    m.get? k = some (m.getD k fb) := by
  unfold DHashMap.Raw.get? DHashMap.Raw.getD; split
  · rename_i hb; exact r0_get?_c _ k fb (by simpa [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, hb] using h)
  · rename_i hb; simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, hb] at h
end
section
variable {α : Type u} {β : α → Type v}
-- set-operation notation as the functions the evaluation tactics unfold
theorem u_dm_union [BEq α] [Hashable α] (m₁ m₂ : DHashMap α β) : m₁ ∪ m₂ = DHashMap.union m₁ m₂ := rfl
theorem u_dm_inter [BEq α] [Hashable α] (m₁ m₂ : DHashMap α β) : m₁ ∩ m₂ = DHashMap.inter m₁ m₂ := rfl
theorem u_dm_diff [BEq α] [Hashable α] (m₁ m₂ : DHashMap α β) : m₁ \ m₂ = DHashMap.diff m₁ m₂ := rfl
theorem u_hm_union {γ : Type v} [BEq α] [Hashable α] (m₁ m₂ : HashMap α γ) : m₁ ∪ m₂ = HashMap.union m₁ m₂ := rfl
theorem u_hs_union [BEq α] [Hashable α] (m₁ m₂ : HashSet α) : m₁ ∪ m₂ = HashSet.union m₁ m₂ := rfl
theorem u_hs_inter [BEq α] [Hashable α] (m₁ m₂ : HashSet α) : m₁ ∩ m₂ = HashSet.inter m₁ m₂ := rfl
theorem u_hs_diff [BEq α] [Hashable α] (m₁ m₂ : HashSet α) : m₁ \ m₂ = HashSet.diff m₁ m₂ := rfl
theorem u_hsr_union [BEq α] [Hashable α] (m₁ m₂ : HashSet.Raw α) : m₁ ∪ m₂ = HashSet.Raw.union m₁ m₂ := rfl
end
section
variable {α : Type u} {β : α → Type v}
theorem dgetD_eval [BEq α] [Hashable α] [LawfulBEq α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size}
    (a : α) (fb : β a) (hsz : Pow2 bs.size) :
    Raw₀.getD (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a fb = (bs[ix bs a]'(Nat.mod_lt _ h)).getCastD a fb := by
  simp only [Raw₀.getD, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]
end
section
variable {α : Type u} {β : α → Type v}
-- insertIfNew either keeps the entries or adds one (up to order), under any BEq/Hashable
theorem tlm_iin [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    List.Perm (toListModel (m.insertIfNew a b).1.buckets)
      (if m.contains a then toListModel m.1.buckets else ⟨a, b⟩ :: toListModel m.1.buckets) := by
  rw [Raw₀.insertIfNew_eq_insertIfNewₘ, Raw₀.contains_eq_containsₘ]; unfold Raw₀.insertIfNewₘ
  split
  · exact .refl _
  · refine (tlm_expandIfNecessary _).trans ?_
    obtain ⟨l, h1, h2, -⟩ := exists_bucket_of_update m.1.buckets m.2 a (fun l => l.cons a b)
    exact h2.trans (by simpa using (List.Perm.cons ⟨a, b⟩ h1.symm))
theorem keys_iin [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => Unit)) (hb : 0 < m.buckets.size) (a : α) :
    (m.insertIfNew a ()).keys.Perm (if m.contains a then m.keys else a :: m.keys) := by
  have e1 : m.insertIfNew a () = (Raw₀.insertIfNew ⟨m, hb⟩ a ()).1 := by simp [DHashMap.Raw.insertIfNew, hb]
  have e2 : m.contains a = Raw₀.contains ⟨m, hb⟩ a := by simp [DHashMap.Raw.contains, hb]
  rw [e1, e2, Raw.keys_eq_keys_toListModel, Raw.keys_eq_keys_toListModel]
  have := (tlm_iin ⟨m, hb⟩ a ()).map Sigma.fst
  split <;> simp_all [Std.Internal.List.keys_eq_map]
end
end W4c1A

namespace W4c1A
open Std Std.DHashMap.Internal Probe2
section
variable {α : Type u} {β : α → Type v}
theorem a_getEntry_mem [BEq α] (l : AssocList α β) (a : α) (e : (a : α) × β a) (h : l.getEntry? a = some e) :
    e ∈ l.toList ∧ (e.1 == a) = true := by
  induction l with
  | nil => cases h
  | cons k v t ih =>
    simp only [AssocList.getEntry?] at h
    split at h
    · cases h; exact ⟨by simp, by assumption⟩
    · obtain ⟨h1, h2⟩ := ih h; exact ⟨by simp [h1], h2⟩
theorem a_contains_of_mem [BEq α] (l : AssocList α β) (q : (a : α) × β a) (k : α) (hq : q ∈ l.toList)
    (hk : (q.1 == k) = true) : l.contains k = true := by
  induction l with
  | nil => simp at hq
  | cons k' v t ih =>
    simp only [AssocList.toList_cons, List.mem_cons] at hq
    simp only [AssocList.contains, Bool.or_eq_true]
    rcases hq with rfl | hq
    · exact Or.inl hk
    · exact Or.inr (ih hq)
-- x is stored (as itself) in its hash bucket of m
def D [BEq α] [Hashable α] (m : Raw₀ α β) (x : α) : Prop :=
  ∃ q ∈ (m.1.buckets[(mkIdx m.1.buckets.size m.2 (hash x)).1.toNat]'(mkIdx m.1.buckets.size m.2 (hash x)).2).toList, q.1 = x
theorem D_of_getEntry [BEq α] [Hashable α] [LawfulHashable α] (m : Raw₀ α β) (k : α) (e : (a : α) × β a)
    (h : m.getEntry? k = some e) : D m e.1 := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have h' : (bs[(mkIdx bs.size hb (hash k)).1.toNat]'(mkIdx bs.size hb (hash k)).2).getEntry? k = some e := by
    unfold Raw₀.getEntry? at h; simpa only [Array.ugetElem_eq_getElem] using h
  obtain ⟨h1, h2⟩ := a_getEntry_mem _ _ _ h'
  have hh : hash e.1 = hash k := LawfulHashable.hash_eq _ _ h2
  exact ⟨e, by simp only [D, hh]; exact h1, rfl⟩
theorem contains_of_D [BEq α] [Hashable α] [LawfulHashable α] (m : Raw₀ α β) (x k : α) (hD : D m x)
    (hx : (x == k) = true) : m.contains k = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  obtain ⟨q, hq, rfl⟩ := hD
  rw [contains_gen]
  have hh : hash q.1 = hash k := LawfulHashable.hash_eq _ _ hx
  simp only [hh] at hq
  exact a_contains_of_mem _ q k hq hx
theorem fold_D [BEq α] [Hashable α] [LawfulHashable α] (m₁ : Raw₀ α β) :
    ∀ (l : List ((a : α) × β a)) (acc : Raw₀ α β), (∀ p ∈ toListModel acc.1.buckets, D m₁ p.1) →
      ∀ p ∈ toListModel (l.foldl (fun a b => Raw₀.interSmallerFn m₁ a b.1) acc).1.buckets, D m₁ p.1
  | [], acc, h => h
  | b :: l, acc, h => by
    simp only [List.foldl_cons]
    apply fold_D m₁ l
    intro p hp
    unfold Raw₀.interSmallerFn at hp
    split at hp
    · rename_i e he
      rcases mem_tlm_insert _ _ _ p hp with rfl | hp'
      · exact D_of_getEntry m₁ b.1 e he
      · exact h p hp'
    · exact h p hp
-- the intersection only contains keys of m₁ (needs LawfulHashable only)
theorem ni_r0 [BEq α] [Hashable α] [LawfulHashable α] (m₁ m₂ : Raw₀ α β) (k : α)
    (h : (Raw₀.inter m₁ m₂).contains k = true) : m₁.contains k = true := by
  unfold Raw₀.inter at h
  split at h
  · exact raw0_filter_contains _ _ _ h
  · unfold Raw₀.interSmaller at h
    rw [Raw.fold_eq_foldl_toListModel] at h
    have ht := raw0_contains_tlm _ k h
    obtain ⟨p, hp, hpk⟩ := Std.Internal.List.containsKey_eq_true_iff_exists_mem.mp ht
    refine contains_of_D m₁ p.1 k (fold_D m₁ _ _ ?_ p hp) hpk
    intro q hq
    simp [Raw₀.emptyWithCapacity, toListModel] at hq
    obtain ⟨a, ⟨-, rfl⟩, hq⟩ := hq
    simp at hq
theorem ni_dr [BEq α] [Hashable α] [LawfulHashable α] (m₁ m₂ : DHashMap.Raw α β) (h₁ : 0 < m₁.buckets.size)
    (k : α) (hn : ¬ k ∈ m₁) : ¬ k ∈ m₁ ∩ m₂ := by
  intro hk; apply hn
  have e : m₁ ∩ m₂ = DHashMap.Raw.inter m₁ m₂ := rfl
  rw [e] at hk; unfold DHashMap.Raw.inter at hk; simp only [h₁, dite_true] at hk
  split at hk
  · rename_i h₂
    simp only [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, h₁, (Raw₀.inter ⟨m₁, h₁⟩ ⟨m₂, h₂⟩).2, dite_true] at hk ⊢
    exact ni_r0 _ _ _ hk
  · exact hk
end
end W4c1A



namespace W4c1
theorem drw : (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)).WF := dr_ins0 ▸ .insert .empty
theorem hsrw : (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat).WF := hsr_ins0 ▸ .insert .empty
theorem dsw : (⟨1, f16 (b1 0 ())⟩ : DHashMap.Raw Nat (fun _ => Unit)).WF := hsrw.out.out
theorem u_dm_diff {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m₁ m₂ : DHashMap α β) : m₁ \ m₂ = DHashMap.diff m₁ m₂ := rfl
end W4c1
namespace W4c1
theorem get!_eval {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] [Hashable α] {s : Nat}
    {bs : Array (AssocList α β)} {h : 0 < bs.size} (a : α) [Inhabited (β a)] (hsz : Pow2 bs.size) :
    Raw₀.get! (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a = (bs[ix bs a]'(Nat.mod_lt _ h)).getCast! a := by
  simp only [Raw₀.get!, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]
end W4c1
/-- Evaluates lookups on literal hash maps (plain, Raw, dependent `get?`/`get!`). -/
macro "w4_ev" : tactic => `(tactic| first
  | (hm_eval; done) | (hm_eval; decide) | (hm_eval_raw; done) | (hm_eval_raw; decide)
  | (simp (disch := first | decide | simp) only [DHashMap.Raw.get!, DHashMap.Raw.get?, DHashMap.get?, DHashMap.get!,
      W4c1.get!_eval, Probe1.get?_eval]
     simp [ix, scr_small, f16, Std.Internal.List.getValueCast?, Std.Internal.List.getValueCast!,
      Std.Internal.List.getEntry?, AssocList.getCast?, AssocList.getCast!]
     try decide))

/-- Like w4c1b_ev, but tolerates goals closed before the last step. Evaluates a hash-map union/inter/diff of literals, allowing one resize (copy of W2c0's union macro). -/
macro "w4_uev" : tactic => `(tactic| (
  try simp only [Union.union, Inter.inter, SDiff.sdiff, HashSet.union, HashSet.Raw.union, HashMap.union, HashMap.Raw.union,
    DHashMap.union, HashSet.inter, HashSet.Raw.inter, HashMap.inter, HashMap.Raw.inter, DHashMap.inter,
    HashSet.diff, HashSet.Raw.diff, HashMap.diff, HashMap.Raw.diff, DHashMap.diff, drn_union]
  try simp only [HashSet.mem_iff_contains, HashMap.mem_iff_contains, DHashMap.mem_iff_contains, HashSet.Raw.mem_iff_contains,
    HashMap.Raw.mem_iff_contains, Std.DHashMap.Raw.mem_iff_contains, HashSet.contains, HashMap.contains, DHashMap.contains,
    HashSet.Raw.contains, HashMap.Raw.contains, HashSet.isEmpty, HashMap.isEmpty, DHashMap.isEmpty, HashSet.Raw.isEmpty,
    HashMap.Raw.isEmpty]
  try simp (disch := decide) only [dr_union_lit, hmr_empty, hsr_empty, dr_empty, dr_insert_lit]
  all_goals try simp (config := {decide := true}) only [Raw₀.union, ite_false, ite_true]
  all_goals (first | (hm_eval; done) | hm_expand)))
namespace W4c1
variable {α : Type u} [BEq α] [Hashable α]
-- lookups of a key that is not a member return none (no instances; bundled and set wrappers)
theorem dhc_nc {γ : Type v} (m : DHashMap α (fun _ => γ)) (k : α) (h : ¬ k ∈ m) : DHashMap.Const.get? m k = none :=
  W4c1A.r0c_get?_nc _ k (by simpa [DHashMap.mem_iff_contains, DHashMap.contains] using h)
theorem hsr_nc (m : HashSet.Raw α) (k : α) (h : ¬ k ∈ m) : m.get? k = none := W4c1A.dr_getKey?_nc m.inner.inner k h
theorem hs_nc (m : HashSet α) (k : α) (h : ¬ k ∈ m) : m.get? k = none := by
  unfold HashSet.get? HashMap.getKey? DHashMap.getKey?; exact W4c1A.r0_getKey?_nc _ k (by simpa [HashSet.mem_iff_contains, HashSet.contains, HashMap.contains, DHashMap.contains] using h)
-- diff: the result's buckets are sub-buckets of m₁'s
theorem dhc_gd {γ : Type v} (m₁ m₂ : DHashMap α (fun _ => γ)) (k : α) (hn : ¬ k ∈ m₁) :
    DHashMap.Const.get? (m₁.diff m₂) k = none := dhc_nc _ k (W4c1B.dh_nmd m₁ m₂ k hn)
theorem drc_gd {γ : Type v} (m₁ m₂ : DHashMap.Raw α (fun _ => γ)) (h₁ : m₁.WF) (k : α) (hn : ¬ k ∈ m₁) :
    DHashMap.Raw.Const.get? (m₁ \ m₂) k = none := W4c1A.drc_get?_nc _ k (W4c1B.dr_nmd m₁ m₂ h₁ k hn)
theorem dr_gd [LawfulBEq α] {β : α → Type v} (m₁ m₂ : DHashMap.Raw α β) (h₁ : m₁.WF) (k : α) (hn : ¬ k ∈ m₁) :
    (m₁ \ m₂).get? k = none := W4c1A.dr_get?_nc _ k (W4c1B.dr_nmd m₁ m₂ h₁ k hn)
theorem hsr_gd (m₁ m₂ : HashSet.Raw α) (h₁ : m₁.WF) (k : α) (hn : ¬ k ∈ m₁) : (m₁ \ m₂).get? k = none :=
  hsr_nc _ k (W4c1B.hsr_nmd m₁ m₂ h₁ k hn)
theorem hs_gd (m₁ m₂ : HashSet α) (k : α) (hn : ¬ k ∈ m₁) : (m₁ \ m₂).get? k = none :=
  hs_nc _ k (W4c1B.hs_nmd m₁ m₂ k hn)
-- inter, key not in m₁ (only LawfulHashable, m₁ with buckets)
theorem dh_nil [LawfulHashable α] {β : α → Type v} (m₁ m₂ : DHashMap α β) (k : α) (hn : ¬ k ∈ m₁) : ¬ k ∈ m₁ ∩ m₂ := by
  intro h; apply hn
  simp only [DHashMap.mem_iff_contains, DHashMap.contains] at h ⊢
  exact W4c1A.ni_r0 _ _ k h
theorem dhc_gil [LawfulHashable α] {γ : Type v} (m₁ m₂ : DHashMap α (fun _ => γ)) (k : α) (hn : ¬ k ∈ m₁) :
    DHashMap.Const.get? (m₁.inter m₂) k = none := dhc_nc _ k (dh_nil m₁ m₂ k hn)
theorem hs_gil [LawfulHashable α] (m₁ m₂ : HashSet α) (k : α) (hn : ¬ k ∈ m₁) : (m₁ ∩ m₂).get? k = none :=
  hs_nc _ k (dh_nil m₁.inner.inner m₂.inner.inner k hn)
theorem drc_gil [LawfulHashable α] {γ : Type v} (m₁ m₂ : DHashMap.Raw α (fun _ => γ)) (h₁ : m₁.WF) (k : α) (hn : ¬ k ∈ m₁) :
    DHashMap.Raw.Const.get? (m₁ ∩ m₂) k = none :=
  W4c1A.drc_get?_nc _ k (W4c1A.ni_dr m₁ m₂ (DHashMap.Raw.WF.size_buckets_pos _ h₁) k hn)
theorem dr_gil [LawfulBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : DHashMap.Raw α β) (h₁ : m₁.WF) (k : α) (hn : ¬ k ∈ m₁) :
    (m₁ ∩ m₂).get? k = none :=
  W4c1A.dr_get?_nc _ k (W4c1A.ni_dr m₁ m₂ (DHashMap.Raw.WF.size_buckets_pos _ h₁) k hn)
theorem hsr_gil [LawfulHashable α] (m₁ m₂ : HashSet.Raw α) (h₁ : m₁.WF) (k : α) (hn : ¬ k ∈ m₁) : (m₁ ∩ m₂).get? k = none :=
  hsr_nc _ k (W4c1A.ni_dr m₁.inner.inner m₂.inner.inner (DHashMap.Raw.WF.size_buckets_pos _ h₁.out.out) k hn)
-- inter, key not in m₂ (m₁ need not be WF)
theorem drc_gir [EquivBEq α] [LawfulHashable α] {γ : Type v} (m₁ m₂ : DHashMap.Raw α (fun _ => γ)) (h₂ : m₂.WF) (k : α)
    (hn : ¬ k ∈ m₂) : DHashMap.Raw.Const.get? (m₁ ∩ m₂) k = none := W4c1A.drc_get?_nc _ k (W4c1B.dr_nmi m₁ m₂ h₂ k hn)
theorem dr_gir [LawfulBEq α] [LawfulHashable α] {β : α → Type v} (m₁ m₂ : DHashMap.Raw α β) (h₂ : m₂.WF) (k : α)
    (hn : ¬ k ∈ m₂) : (m₁ ∩ m₂).get? k = none := W4c1A.dr_get?_nc _ k (W4c1B.dr_nmi m₁ m₂ h₂ k hn)
theorem hsr_gir [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashSet.Raw α) (h₂ : m₂.WF) (k : α) (hn : ¬ k ∈ m₂) :
    (m₁ ∩ m₂).get? k = none := hsr_nc _ k (W4c1B.hsr_nmi m₁ m₂ h₂ k hn)
-- filter keeps a sub-bucket of every bucket
theorem dr_mf {β : α → Type v} (f : (a : α) → β a → Bool) (m : DHashMap.Raw α β) (k : α) (h : k ∈ m.filter f) : k ∈ m := by
  simp only [DHashMap.Raw.mem_iff_contains] at h ⊢
  unfold DHashMap.Raw.filter at h; split at h
  · rename_i hb; unfold DHashMap.Raw.contains at h ⊢; rw [dif_pos hb]
    rw [dif_pos (Raw₀.filter f ⟨m, hb⟩).2] at h; exact raw0_filter_contains f ⟨m, hb⟩ k h
  · simp [DHashMap.Raw.contains_empty] at h
theorem hmr_mf {β : Type v} (f : α → β → Bool) (m : HashMap.Raw α β) (k : α) (h : k ∈ m.filter f) : k ∈ m := dr_mf _ m.inner k h
theorem hsr_mf (f : α → Bool) (m : HashSet.Raw α) (k : α) (h : k ∈ m.filter f) : k ∈ m := dr_mf _ m.inner.inner k h
theorem dh_mf {β : α → Type v} (f : (a : α) → β a → Bool) (m : DHashMap α β) (k : α) (h : k ∈ m.filter f) : k ∈ m := by
  simp only [DHashMap.mem_iff_contains, DHashMap.contains] at h ⊢
  exact raw0_filter_contains f _ k h
theorem hm_mf {β : Type v} (f : α → β → Bool) (m : HashMap α β) (k : α) (h : k ∈ m.filter f) : k ∈ m := dh_mf _ m.inner k h
theorem hs_mf (f : α → Bool) (m : HashSet α) (k : α) (h : k ∈ m.filter f) : k ∈ m := dh_mf _ m.inner.inner k h
end W4c1

namespace W4c1
-- copy of checks/Probe1Hand.lean p43 (diff filters/erases by keys of the well-formed m₁; m₂ need not be WF)
theorem dr_nmdr : drop% Std.DHashMap.Raw.not_mem_diff_of_mem_right 9 := by
  intro α β _ _ m₁ m₂ _ _ h₁ k hk hk'
  rw [DHashMap.Raw.mem_iff_contains] at hk hk'
  have hb₁ := h₁.size_buckets_pos
  rcases Nat.eq_zero_or_pos m₂.buckets.size with h0 | hb₂
  · simp [DHashMap.Raw.contains, h0] at hk
  simp only [DHashMap.Raw.contains, hb₂, dite_true] at hk
  simp only [SDiff.sdiff, DHashMap.Raw.diff, hb₁, hb₂, dite_true] at hk'
  simp only [DHashMap.Raw.contains] at hk'
  rw [dif_pos (Raw₀.diff _ _).2] at hk'
  unfold Raw₀.diff at hk'
  split at hk'
  · have hf := (Raw₀.contains_filter_key_iff (m := ⟨m₁, hb₁⟩) (f := fun a => !Raw₀.contains ⟨m₂, hb₂⟩ a) h₁).mp hk'
    obtain ⟨hc, hf⟩ := hf
    have := Probe1.r0_contains_congr ⟨m₂, hb₂⟩ (Raw₀.getKey_beq (m := ⟨m₁, hb₁⟩) h₁ hc)
    simp [this, hk] at hf
  · rw [Raw₀.eraseMany_eq_eraseListₘ_toListModel] at hk'
    obtain ⟨p, hp, hpk⟩ := Probe1.r0_exists_of_contains ⟨m₂, hb₂⟩ k hk
    have := Probe1.eraseList_contains k _ ⟨m₁, hb₁⟩ h₁ (Or.inl ⟨p.1, List.mem_map_of_mem hp, hpk⟩)
    rw [this] at hk'
    cases hk'
end W4c1



/-! # W4c1 verdicts -/

-- `Std.DHashMap.Const.get!_of_isEmpty` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 1 finds it
theorem w4c1_0 : ¬ drop0% Std.DHashMap.Const.get!_of_isEmpty 5 :=
  fun h => by
  have := h (m := (hm NS.broken 0 #[b1 (NS.mk 1) (1 : Nat), .nil] (by decide) : HashMap NS Nat).inner) (a := (NS.mk 1)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Internal.Raw₀.Const.get!_of_isEmpty` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 1 finds it
theorem w4c1_1 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.get!_of_isEmpty 5 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (NS.mk 1) (1 : Nat), .nil]⟩, by decide⟩ : Raw₀ NS (fun _ => Nat))) (h := (wf_vac NS.broken _ (by decide))) (a := (NS.mk 1)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.Const.get!_of_isEmpty` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 1 finds it
theorem w4c1_2 : ¬ drop0% Std.DHashMap.Raw.Const.get!_of_isEmpty 5 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (NS.mk 1) (1 : Nat), .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (h := (wf_vac NS.broken _ (by decide))) (a := (NS.mk 1)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.HashSet.Raw.get!_of_isEmpty` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 1 finds it
theorem w4c1_3 : ¬ drop0% Std.HashSet.Raw.get!_of_isEmpty 5 :=
  fun h => by
  have := h (m := (hsr 0 #[b1 (NS.mk 1) (), .nil] : HashSet.Raw NS)) (h := (hsr_wf NS.broken _ _ (by decide))) (a := (NS.mk 1)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.HashSet.get!_of_isEmpty` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 1 finds it
theorem w4c1_4 : ¬ drop0% Std.HashSet.get!_of_isEmpty 5 :=
  fun h => by
  have := h (m := (hs NS.broken 0 #[b1 (NS.mk 1) (), .nil] (by decide) : HashSet NS)) (a := (NS.mk 1)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Const.get!_of_isEmpty` (binder 6): AB (== always true, hash n; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_5 : ¬ drop0% Std.DHashMap.Const.get!_of_isEmpty 6 :=
  fun h => by
  have := h (m := (hm AB.broken 0 #[b1 (AB.mk 1) (1 : Nat), .nil] (by decide) : HashMap AB Nat).inner) (a := (AB.mk 0)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Internal.Raw₀.Const.get!_of_isEmpty` (binder 6): AB (== always true, hash n; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_6 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.get!_of_isEmpty 6 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (AB.mk 1) (1 : Nat), .nil]⟩, by decide⟩ : Raw₀ AB (fun _ => Nat))) (h := (wf_vac AB.broken _ (by decide))) (a := (AB.mk 0)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.Const.get!_of_isEmpty` (binder 6): AB (== always true, hash n; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_7 : ¬ drop0% Std.DHashMap.Raw.Const.get!_of_isEmpty 6 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (AB.mk 1) (1 : Nat), .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (h := (wf_vac AB.broken _ (by decide))) (a := (AB.mk 0)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.HashSet.Raw.get!_of_isEmpty` (binder 6): AB (== always true, hash n; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_8 : ¬ drop0% Std.HashSet.Raw.get!_of_isEmpty 6 :=
  fun h => by
  have := h (m := (hsr 0 #[b1 (AB.mk 1) (), .nil] : HashSet.Raw AB)) (h := (hsr_wf AB.broken _ _ (by decide))) (a := (AB.mk 0)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.HashSet.get!_of_isEmpty` (binder 6): AB (== always true, hash n; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_9 : ¬ drop0% Std.HashSet.get!_of_isEmpty 6 :=
  fun h => by
  have := h (m := (hs AB.broken 0 #[b1 (AB.mk 1) (), .nil] (by decide) : HashSet AB)) (a := (AB.mk 0)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Internal.Raw₀.Const.get!_of_isEmpty` (binder 8): lawful Nat, not WF: m has size field 0 and the entry 0 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_10 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.get!_of_isEmpty 8 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (⟨⟨0, #[b1 (0 : Nat) (1 : Nat), .nil]⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat))) (a := (0 : Nat)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Internal.Raw₀.get!_of_isEmpty` (binder 6): lawful Nat, not WF: m has size field 0 and the entry 0 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_11 : ¬ drop0% Std.DHashMap.Internal.Raw₀.get!_of_isEmpty 6 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (⟨⟨0, #[b1 (0 : Nat) (1 : Nat), .nil]⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat))) (a := (0 : Nat)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.Const.get!_of_isEmpty` (binder 8): lawful Nat, not WF: m has size field 0 and the entry 0 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_12 : ¬ drop0% Std.DHashMap.Raw.Const.get!_of_isEmpty 8 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (⟨0, #[b1 (0 : Nat) (1 : Nat), .nil]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (a := (0 : Nat)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.get!_of_isEmpty` (binder 6): lawful Nat, not WF: m has size field 0 and the entry 0 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_13 : ¬ drop0% Std.DHashMap.Raw.get!_of_isEmpty 6 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (⟨0, #[b1 (0 : Nat) (1 : Nat), .nil]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (a := (0 : Nat)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.HashSet.Raw.get!_of_isEmpty` (binder 7): lawful Nat, not WF: m has size field 0 and the entry 0 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_14 : ¬ drop0% Std.HashSet.Raw.get!_of_isEmpty 7 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (hsr 0 #[b1 (0 : Nat) (), .nil] : HashSet.Raw Nat)) (a := (0 : Nat)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Const.get!_of_isEmpty` (binder 9): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry (default 7 via a local Inhabited instance)
theorem w4c1_15 : ¬ drop0% Std.DHashMap.Const.get!_of_isEmpty 9 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (⟨⟨1, f16 (.cons 0 0 .nil)⟩, W4c1.drw⟩ : DHashMap Nat (fun _ => Nat))) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Internal.Raw₀.Const.get!_of_isEmpty` (binder 10): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry (default 7 via a local Inhabited instance)
theorem w4c1_16 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.get!_of_isEmpty 10 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (⟨⟨1, f16 (.cons 0 0 .nil)⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat))) (h := W4c1.drw) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Internal.Raw₀.get!_of_isEmpty` (binder 9): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry (default 7 via a local Inhabited instance)
theorem w4c1_17 : ¬ drop0% Std.DHashMap.Internal.Raw₀.get!_of_isEmpty 9 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (⟨⟨1, f16 (.cons 0 0 .nil)⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat))) (h := W4c1.drw) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.Const.get!_of_isEmpty` (binder 10): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry (default 7 via a local Inhabited instance)
theorem w4c1_18 : ¬ drop0% Std.DHashMap.Raw.Const.get!_of_isEmpty 10 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h := W4c1.drw) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.get!_of_isEmpty` (binder 9): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry (default 7 via a local Inhabited instance)
theorem w4c1_19 : ¬ drop0% Std.DHashMap.Raw.get!_of_isEmpty 9 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h := W4c1.drw) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.DHashMap.get!_of_isEmpty` (binder 8): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry (default 7 via a local Inhabited instance)
theorem w4c1_20 : ¬ drop0% Std.DHashMap.get!_of_isEmpty 8 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (⟨⟨1, f16 (.cons 0 0 .nil)⟩, W4c1.drw⟩ : DHashMap Nat (fun _ => Nat))) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.HashSet.Raw.get!_of_isEmpty` (binder 9): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry (default 7 via a local Inhabited instance)
theorem w4c1_21 : ¬ drop0% Std.HashSet.Raw.get!_of_isEmpty 9 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat)) (h := W4c1.hsrw) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.HashSet.get!_of_isEmpty` (binder 8): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry (default 7 via a local Inhabited instance)
theorem w4c1_22 : ¬ drop0% Std.HashSet.get!_of_isEmpty 8 :=
  fun h => by
  letI : Inhabited Nat := ⟨7⟩
  have := h (m := (⟨⟨⟨⟨1, f16 (b1 0 ())⟩, W4c1.dsw⟩⟩⟩ : HashSet Nat)) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Const.get?_diff_of_not_mem_left` (binder 6): removable: diff only filters m₁ or erases from it, so its buckets are sub-buckets of m₁; a key not in m₁ is not found (bucket-level, no instance needed; m₁ has buckets by m₁.WF / bundling)
theorem w4c1_23 : drop% Std.DHashMap.Const.get?_diff_of_not_mem_left 6 :=
  by intros; apply W4c1.dhc_gd <;> assumption

-- `Std.DHashMap.Raw.Const.get?_diff_of_not_mem_left` (binder 6): removable: diff only filters m₁ or erases from it, so its buckets are sub-buckets of m₁; a key not in m₁ is not found (bucket-level, no instance needed; m₁ has buckets by m₁.WF / bundling)
theorem w4c1_24 : drop% Std.DHashMap.Raw.Const.get?_diff_of_not_mem_left 6 :=
  by intros; apply W4c1.drc_gd <;> assumption

-- `Std.HashSet.Raw.get?_diff_of_not_mem_left` (binder 5): removable: diff only filters m₁ or erases from it, so its buckets are sub-buckets of m₁; a key not in m₁ is not found (bucket-level, no instance needed; m₁ has buckets by m₁.WF / bundling)
theorem w4c1_25 : drop% Std.HashSet.Raw.get?_diff_of_not_mem_left 5 :=
  by intros; apply W4c1.hsr_gd <;> assumption

-- `Std.HashSet.get?_diff_of_not_mem_left` (binder 5): removable: diff only filters m₁ or erases from it, so its buckets are sub-buckets of m₁; a key not in m₁ is not found (bucket-level, no instance needed; m₁ has buckets by m₁.WF / bundling)
theorem w4c1_26 : drop% Std.HashSet.get?_diff_of_not_mem_left 5 :=
  by intros; apply W4c1.hs_gd <;> assumption

-- `Std.DHashMap.Const.get?_diff_of_not_mem_left` (binder 7): removable: diff only filters m₁ or erases from it, so its buckets are sub-buckets of m₁; a key not in m₁ is not found (bucket-level, no instance needed; m₁ has buckets by m₁.WF / bundling)
theorem w4c1_27 : drop% Std.DHashMap.Const.get?_diff_of_not_mem_left 7 :=
  by intros; apply W4c1.dhc_gd <;> assumption

-- `Std.DHashMap.Raw.Const.get?_diff_of_not_mem_left` (binder 7): removable: diff only filters m₁ or erases from it, so its buckets are sub-buckets of m₁; a key not in m₁ is not found (bucket-level, no instance needed; m₁ has buckets by m₁.WF / bundling)
theorem w4c1_28 : drop% Std.DHashMap.Raw.Const.get?_diff_of_not_mem_left 7 :=
  by intros; apply W4c1.drc_gd <;> assumption

-- `Std.HashSet.Raw.get?_diff_of_not_mem_left` (binder 6): removable: diff only filters m₁ or erases from it, so its buckets are sub-buckets of m₁; a key not in m₁ is not found (bucket-level, no instance needed; m₁ has buckets by m₁.WF / bundling)
theorem w4c1_29 : drop% Std.HashSet.Raw.get?_diff_of_not_mem_left 6 :=
  by intros; apply W4c1.hsr_gd <;> assumption

-- `Std.HashSet.get?_diff_of_not_mem_left` (binder 6): removable: diff only filters m₁ or erases from it, so its buckets are sub-buckets of m₁; a key not in m₁ is not found (bucket-level, no instance needed; m₁ has buckets by m₁.WF / bundling)
theorem w4c1_30 : drop% Std.HashSet.get?_diff_of_not_mem_left 6 :=
  by intros; apply W4c1.hs_gd <;> assumption

-- `Std.DHashMap.Raw.Const.get?_diff_of_not_mem_left` (binder 8): lawful Nat: m1 has no buckets (not WF); Raw.diff returns the other map {0} (WF), so the lookup of k = 0 finds 0
theorem w4c1_31 : ¬ drop0% Std.DHashMap.Raw.Const.get?_diff_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h₂ := W4c1.drw) (k := 0) (not_mem := (by simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains]))
  first | (have e : DHashMap.Raw.diff (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat)) (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this) | (have e : ((⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat)) \ (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.Const.get?_diff_of_not_mem_left` (binder 9): removable: diff only filters m₁ or erases from it, so its buckets are sub-buckets of m₁; a key not in m₁ is not found (bucket-level, no instance needed; m₁ has buckets by m₁.WF / bundling)
theorem w4c1_32 : drop% Std.DHashMap.Raw.Const.get?_diff_of_not_mem_left 9 :=
  by intros; apply W4c1.drc_gd <;> assumption

-- `Std.DHashMap.Raw.get?_diff_of_not_mem_left` (binder 7): lawful Nat: m1 has no buckets (not WF); Raw.diff returns the other map {0} (WF), so the lookup of k = 0 finds 0
theorem w4c1_33 : ¬ drop0% Std.DHashMap.Raw.get?_diff_of_not_mem_left 7 :=
  fun h => by
  have := h (m₁ := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h₂ := W4c1.drw) (k := 0) (not_mem := (by simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains]))
  first | (have e : DHashMap.Raw.diff (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat)) (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this) | (have e : ((⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat)) \ (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.get?_diff_of_not_mem_left` (binder 8): removable: diff only filters m₁ or erases from it, so its buckets are sub-buckets of m₁; a key not in m₁ is not found (bucket-level, no instance needed; m₁ has buckets by m₁.WF / bundling)
theorem w4c1_34 : drop% Std.DHashMap.Raw.get?_diff_of_not_mem_left 8 :=
  by intros; apply W4c1.dr_gd <;> assumption

-- `Std.HashSet.Raw.get?_diff_of_not_mem_left` (binder 8): removable: diff only filters m₁ or erases from it, so its buckets are sub-buckets of m₁; a key not in m₁ is not found (bucket-level, no instance needed; m₁ has buckets by m₁.WF / bundling)
theorem w4c1_35 : drop% Std.HashSet.Raw.get?_diff_of_not_mem_left 8 :=
  by intros; apply W4c1.hsr_gd <;> assumption

-- `Std.DHashMap.Const.get?_diff_of_not_mem_left` (binder 9): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ \ m₂ finds 0
theorem w4c1_36 : ¬ drop0% Std.DHashMap.Const.get?_diff_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap Nat (fun _ => Nat))) (k := 0)
  rw [DHashMap.Const.get?_diff] at this; simp [DHashMap.mem_insert, DHashMap.contains_insert, DHashMap.size_insert, DHashMap.mem_diff_iff, DHashMap.mem_inter_iff, DHashMap.mem_union_iff, DHashMap.isEmpty_insert, DHashMap.Const.get?_diff, DHashMap.Const.get?_inter, DHashMap.Const.get?_union, DHashMap.Const.get?_insert, DHashMap.Const.get?_empty] at this

-- `Std.DHashMap.Raw.Const.get?_diff_of_not_mem_left` (binder 11): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ \ m₂ finds 0
theorem w4c1_37 : ¬ drop0% Std.DHashMap.Raw.Const.get?_diff_of_not_mem_left 11 :=
  fun h => by
  have w0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).WF := .empty
  have w1 : ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := w1) (h₂ := w0) (k := 0)
  simp [DHashMap.Raw.mem_insert, DHashMap.Raw.contains_insert, DHashMap.Raw.size_insert, DHashMap.Raw.mem_diff_iff, DHashMap.Raw.mem_inter_iff, DHashMap.Raw.mem_union_iff, DHashMap.Raw.isEmpty_insert, DHashMap.Raw.Const.get?_diff, DHashMap.Raw.Const.get?_inter, DHashMap.Raw.Const.get?_union, DHashMap.Raw.Const.get?_insert, DHashMap.Raw.Const.get?_empty, w0, w1] at this

-- `Std.DHashMap.Raw.get?_diff_of_not_mem_left` (binder 10): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ \ m₂ finds 0
theorem w4c1_38 : ¬ drop0% Std.DHashMap.Raw.get?_diff_of_not_mem_left 10 :=
  fun h => by
  have w0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).WF := .empty
  have w1 : ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := w1) (h₂ := w0) (k := 0)
  simp [DHashMap.Raw.mem_insert, DHashMap.Raw.contains_insert, DHashMap.Raw.size_insert, DHashMap.Raw.mem_diff_iff, DHashMap.Raw.mem_inter_iff, DHashMap.Raw.mem_union_iff, DHashMap.Raw.isEmpty_insert, DHashMap.Raw.get?_diff, DHashMap.Raw.get?_inter, DHashMap.Raw.get?_union, DHashMap.Raw.get?_insert, w0, w1] at this

-- `Std.DHashMap.get?_diff_of_not_mem_left` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ \ m₂ finds 0
theorem w4c1_39 : ¬ drop0% Std.DHashMap.get?_diff_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap Nat (fun _ => Nat))) (k := 0)
  simp [DHashMap.mem_insert, DHashMap.contains_insert, DHashMap.size_insert, DHashMap.mem_diff_iff, DHashMap.mem_inter_iff, DHashMap.mem_union_iff, DHashMap.isEmpty_insert, DHashMap.get?_diff, DHashMap.get?_inter, DHashMap.get?_union, DHashMap.get?_insert] at this

-- `Std.ExtDHashMap.Const.get?_diff_of_not_mem_left` (binder 9): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ \ m₂ finds 0
theorem w4c1_40 : ¬ drop0% Std.ExtDHashMap.Const.get?_diff_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : ExtDHashMap Nat (fun _ => Nat))) (k := 0)
  rw [ExtDHashMap.Const.get?_diff] at this; simp [ExtDHashMap.mem_insert, ExtDHashMap.contains_insert, ExtDHashMap.size_insert, ExtDHashMap.mem_diff_iff, ExtDHashMap.mem_inter_iff, ExtDHashMap.mem_union_iff, ExtDHashMap.Const.get?_diff, ExtDHashMap.Const.get?_inter, ExtDHashMap.Const.get?_union, ExtDHashMap.Const.get?_insert, ExtDHashMap.Const.get?_empty] at this

-- `Std.ExtDHashMap.get?_diff_of_not_mem_left` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ \ m₂ finds 0
theorem w4c1_41 : ¬ drop0% Std.ExtDHashMap.get?_diff_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : ExtDHashMap Nat (fun _ => Nat))) (k := 0)
  simp [ExtDHashMap.mem_insert, ExtDHashMap.contains_insert, ExtDHashMap.size_insert, ExtDHashMap.mem_diff_iff, ExtDHashMap.mem_inter_iff, ExtDHashMap.mem_union_iff, ExtDHashMap.get?_diff, ExtDHashMap.get?_inter, ExtDHashMap.get?_union, ExtDHashMap.get?_insert] at this

-- `Std.ExtHashMap.get?_diff_of_not_mem_left` (binder 9): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ \ m₂ finds 0
theorem w4c1_42 : ¬ drop0% Std.ExtHashMap.get?_diff_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtHashMap Nat Nat).insert 0 0)) (m₂ := (∅ : ExtHashMap Nat Nat)) (k := 0)
  simp [ExtHashMap.mem_insert, ExtHashMap.contains_insert, ExtHashMap.size_insert, ExtHashMap.mem_diff_iff, ExtHashMap.mem_inter_iff, ExtHashMap.mem_union_iff, ExtHashMap.get?_diff, ExtHashMap.getElem?_inter, ExtHashMap.getElem?_union, ExtHashMap.getElem?_insert] at this

-- `Std.ExtHashSet.get?_diff_of_not_mem_left` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ \ m₂ finds 0
theorem w4c1_43 : ¬ drop0% Std.ExtHashSet.get?_diff_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtHashSet Nat).insert 0)) (m₂ := (∅ : ExtHashSet Nat)) (k := 0)
  simp [ExtHashSet.mem_insert, ExtHashSet.contains_insert, ExtHashSet.size_insert, ExtHashSet.mem_diff_iff, ExtHashSet.mem_inter_iff, ExtHashSet.mem_union_iff, ExtHashSet.get?_diff, ExtHashSet.get?_inter, ExtHashSet.get?_union, ExtHashSet.get?_insert] at this

-- `Std.HashSet.Raw.get?_diff_of_not_mem_left` (binder 10): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ \ m₂ finds 0
theorem w4c1_44 : ¬ drop0% Std.HashSet.Raw.get?_diff_of_not_mem_left 10 :=
  fun h => by
  have w0 : (∅ : HashSet.Raw Nat).WF := .empty
  have w1 : ((∅ : HashSet.Raw Nat).insert 0).WF := .insert .empty
  have := h (m₁ := ((∅ : HashSet.Raw Nat).insert 0)) (m₂ := (∅ : HashSet.Raw Nat)) (h₁ := w1) (h₂ := w0) (k := 0)
  simp [HashSet.Raw.mem_insert, HashSet.Raw.contains_insert, HashSet.Raw.size_insert, HashSet.Raw.mem_diff_iff, HashSet.Raw.mem_inter_iff, HashSet.Raw.mem_union_iff, HashSet.Raw.isEmpty_insert, HashSet.Raw.get?_diff, HashSet.Raw.get?_inter, HashSet.Raw.get?_union, HashSet.Raw.get?_insert, w0, w1] at this

-- `Std.HashSet.get?_diff_of_not_mem_left` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ \ m₂ finds 0
theorem w4c1_45 : ¬ drop0% Std.HashSet.get?_diff_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := ((∅ : HashSet Nat).insert 0)) (m₂ := (∅ : HashSet Nat)) (k := 0)
  simp [HashSet.mem_insert, HashSet.contains_insert, HashSet.size_insert, HashSet.mem_diff_iff, HashSet.mem_inter_iff, HashSet.mem_union_iff, HashSet.isEmpty_insert, HashSet.get?_diff, HashSet.get?_inter, HashSet.get?_union, HashSet.get?_insert] at this

-- `Std.DHashMap.Const.get?_inter_of_not_mem_left` (binder 6): removable: inter either filters m₁ or inserts entries found in m₁ (fold invariant), so a key not in m₁ is not in m₁ ∩ m₂; only LawfulHashable and buckets of m₁ needed
theorem w4c1_46 : drop% Std.DHashMap.Const.get?_inter_of_not_mem_left 6 :=
  by intros; apply W4c1.dhc_gil <;> assumption

-- `Std.DHashMap.Raw.Const.get?_inter_of_not_mem_left` (binder 6): removable: inter either filters m₁ or inserts entries found in m₁ (fold invariant), so a key not in m₁ is not in m₁ ∩ m₂; only LawfulHashable and buckets of m₁ needed
theorem w4c1_47 : drop% Std.DHashMap.Raw.Const.get?_inter_of_not_mem_left 6 :=
  by intros; apply W4c1.drc_gil <;> assumption

-- `Std.HashSet.Raw.get?_inter_of_not_mem_left` (binder 5): removable: inter either filters m₁ or inserts entries found in m₁ (fold invariant), so a key not in m₁ is not in m₁ ∩ m₂; only LawfulHashable and buckets of m₁ needed
theorem w4c1_48 : drop% Std.HashSet.Raw.get?_inter_of_not_mem_left 5 :=
  by intros; apply W4c1.hsr_gil <;> assumption

-- `Std.HashSet.get?_inter_of_not_mem_left` (binder 5): removable: inter either filters m₁ or inserts entries found in m₁ (fold invariant), so a key not in m₁ is not in m₁ ∩ m₂; only LawfulHashable and buckets of m₁ needed
theorem w4c1_49 : drop% Std.HashSet.get?_inter_of_not_mem_left 5 :=
  by intros; apply W4c1.hs_gil <;> assumption

-- `Std.DHashMap.Const.get?_inter_of_not_mem_left` (binder 7): AB (== always true, hash n; WF vacuous): m₁ has key 0 misplaced in bucket 1 and size field 2, so 0 ∉ m₁; m₂ = {1} is smaller, so inter folds over m₂, finds 0 in bucket 1 of m₁ and inserts it into a fresh map in its own bucket 0, where k = 0 finds it
theorem w4c1_50 : ¬ drop0% Std.DHashMap.Const.get?_inter_of_not_mem_left 7 :=
  fun h => by
  have := h (m₁ := (hm AB.broken 2 #[.nil, b1 (AB.mk 0) (0 : Nat)] (by decide) : HashMap AB Nat).inner) (m₂ := (hm AB.broken 1 #[.nil, b1 (AB.mk 1) (0 : Nat)] (by decide) : HashMap AB Nat).inner) (k := (AB.mk 0)) (not_mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_inter, W4c1A.u_hs_inter, HashSet.inter, DHashMap.inter] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.Const.get?_inter_of_not_mem_left` (binder 7): AB (== always true, hash n; WF vacuous): m₁ has key 0 misplaced in bucket 1 and size field 2, so 0 ∉ m₁; m₂ = {1} is smaller, so inter folds over m₂, finds 0 in bucket 1 of m₁ and inserts it into a fresh map in its own bucket 0, where k = 0 finds it
theorem w4c1_51 : ¬ drop0% Std.DHashMap.Raw.Const.get?_inter_of_not_mem_left 7 :=
  fun h => by
  have := h (m₁ := (⟨2, #[.nil, b1 (AB.mk 0) (0 : Nat)]⟩ : DHashMap.Raw AB (fun _ => Nat))) (m₂ := (⟨1, #[.nil, b1 (AB.mk 1) (0 : Nat)]⟩ : DHashMap.Raw AB (fun _ => Nat))) (h₁ := (wf_vac AB.broken _ (by decide))) (h₂ := (wf_vac AB.broken _ (by decide))) (k := (AB.mk 0)) (not_mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_inter, W4c1A.u_hs_inter, HashSet.inter, DHashMap.inter] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.Raw.get?_inter_of_not_mem_left` (binder 6): AB (== always true, hash n; WF vacuous): m₁ has key 0 misplaced in bucket 1 and size field 2, so 0 ∉ m₁; m₂ = {1} is smaller, so inter folds over m₂, finds 0 in bucket 1 of m₁ and inserts it into a fresh map in its own bucket 0, where k = 0 finds it
theorem w4c1_52 : ¬ drop0% Std.HashSet.Raw.get?_inter_of_not_mem_left 6 :=
  fun h => by
  have := h (m₁ := (hsr 2 #[.nil, b1 (AB.mk 0) ()] : HashSet.Raw AB)) (m₂ := (hsr 1 #[.nil, b1 (AB.mk 1) ()] : HashSet.Raw AB)) (h₁ := (hsr_wf AB.broken _ _ (by decide))) (h₂ := (hsr_wf AB.broken _ _ (by decide))) (k := (AB.mk 0)) (not_mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_inter, W4c1A.u_hs_inter, HashSet.inter, DHashMap.inter] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.get?_inter_of_not_mem_left` (binder 6): AB (== always true, hash n; WF vacuous): m₁ has key 0 misplaced in bucket 1 and size field 2, so 0 ∉ m₁; m₂ = {1} is smaller, so inter folds over m₂, finds 0 in bucket 1 of m₁ and inserts it into a fresh map in its own bucket 0, where k = 0 finds it
theorem w4c1_53 : ¬ drop0% Std.HashSet.get?_inter_of_not_mem_left 6 :=
  fun h => by
  have := h (m₁ := (hs AB.broken 2 #[.nil, b1 (AB.mk 0) ()] (by decide) : HashSet AB)) (m₂ := (hs AB.broken 1 #[.nil, b1 (AB.mk 1) ()] (by decide) : HashSet AB)) (k := (AB.mk 0)) (not_mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_inter, W4c1A.u_hs_inter, HashSet.inter, DHashMap.inter] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.Const.get?_inter_of_not_mem_left` (binder 8): lawful Nat: m1 has no buckets (not WF); Raw.inter returns the other map {0} (WF), so the lookup of k = 0 finds 0
theorem w4c1_54 : ¬ drop0% Std.DHashMap.Raw.Const.get?_inter_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h₂ := W4c1.drw) (k := 0) (not_mem := (by simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains]))
  first | (have e : DHashMap.Raw.inter (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat)) (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this) | (have e : ((⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat)) ∩ (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.Const.get?_inter_of_not_mem_left` (binder 9): removable: inter either filters m₁ or inserts entries found in m₁ (fold invariant), so a key not in m₁ is not in m₁ ∩ m₂; only LawfulHashable and buckets of m₁ needed
theorem w4c1_55 : drop% Std.DHashMap.Raw.Const.get?_inter_of_not_mem_left 9 :=
  by intros; apply W4c1.drc_gil <;> assumption

-- `Std.DHashMap.Raw.get?_inter_of_not_mem_left` (binder 7): lawful Nat: m1 has no buckets (not WF); Raw.inter returns the other map {0} (WF), so the lookup of k = 0 finds 0
theorem w4c1_56 : ¬ drop0% Std.DHashMap.Raw.get?_inter_of_not_mem_left 7 :=
  fun h => by
  have := h (m₁ := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h₂ := W4c1.drw) (k := 0) (not_mem := (by simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains]))
  first | (have e : DHashMap.Raw.inter (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat)) (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this) | (have e : ((⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat)) ∩ (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.get?_inter_of_not_mem_left` (binder 8): removable: inter either filters m₁ or inserts entries found in m₁ (fold invariant), so a key not in m₁ is not in m₁ ∩ m₂; only LawfulHashable and buckets of m₁ needed
theorem w4c1_57 : drop% Std.DHashMap.Raw.get?_inter_of_not_mem_left 8 :=
  by intros; apply W4c1.dr_gil <;> assumption

-- `Std.HashSet.Raw.get?_inter_of_not_mem_left` (binder 7): lawful Nat: m1 has no buckets (not WF); Raw.inter returns the other map {0} (WF), so the lookup of k = 0 finds 0
theorem w4c1_58 : ¬ drop0% Std.HashSet.Raw.get?_inter_of_not_mem_left 7 :=
  fun h => by
  have := h (m₁ := (hsr 0 #[] : HashSet.Raw Nat)) (m₂ := (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat)) (h₂ := W4c1.hsrw) (k := 0) (not_mem := (by simp [HashSet.Raw.mem_iff_contains, HashSet.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains]))
  first | (have e : HashSet.Raw.inter (hsr 0 #[] : HashSet.Raw Nat) (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat) = (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat) := rfl; rw [e] at this) | (have e : ((hsr 0 #[] : HashSet.Raw Nat) ∩ (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat)) = (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat) := rfl; rw [e] at this)
  exact absurd this (by w4_ev)

-- `Std.HashSet.Raw.get?_inter_of_not_mem_left` (binder 8): removable: inter either filters m₁ or inserts entries found in m₁ (fold invariant), so a key not in m₁ is not in m₁ ∩ m₂; only LawfulHashable and buckets of m₁ needed
theorem w4c1_59 : drop% Std.HashSet.Raw.get?_inter_of_not_mem_left 8 :=
  by intros; apply W4c1.hsr_gil <;> assumption

-- `Std.DHashMap.Const.get?_inter_of_not_mem_left` (binder 9): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_60 : ¬ drop0% Std.DHashMap.Const.get?_inter_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (k := 0)
  rw [DHashMap.Const.get?_inter] at this; simp [DHashMap.mem_insert, DHashMap.contains_insert, DHashMap.size_insert, DHashMap.mem_diff_iff, DHashMap.mem_inter_iff, DHashMap.mem_union_iff, DHashMap.isEmpty_insert, DHashMap.Const.get?_diff, DHashMap.Const.get?_inter, DHashMap.Const.get?_union, DHashMap.Const.get?_insert, DHashMap.Const.get?_empty] at this

-- `Std.DHashMap.Raw.Const.get?_inter_of_not_mem_left` (binder 11): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_61 : ¬ drop0% Std.DHashMap.Raw.Const.get?_inter_of_not_mem_left 11 :=
  fun h => by
  have w0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).WF := .empty
  have w1 : ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (m₂ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (h₁ := w1) (h₂ := w1) (k := 0)
  simp [DHashMap.Raw.mem_insert, DHashMap.Raw.contains_insert, DHashMap.Raw.size_insert, DHashMap.Raw.mem_diff_iff, DHashMap.Raw.mem_inter_iff, DHashMap.Raw.mem_union_iff, DHashMap.Raw.isEmpty_insert, DHashMap.Raw.Const.get?_diff, DHashMap.Raw.Const.get?_inter, DHashMap.Raw.Const.get?_union, DHashMap.Raw.Const.get?_insert, DHashMap.Raw.Const.get?_empty, w0, w1] at this

-- `Std.DHashMap.Raw.get?_inter_of_not_mem_left` (binder 10): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_62 : ¬ drop0% Std.DHashMap.Raw.get?_inter_of_not_mem_left 10 :=
  fun h => by
  have w0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).WF := .empty
  have w1 : ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (m₂ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (h₁ := w1) (h₂ := w1) (k := 0)
  simp [DHashMap.Raw.mem_insert, DHashMap.Raw.contains_insert, DHashMap.Raw.size_insert, DHashMap.Raw.mem_diff_iff, DHashMap.Raw.mem_inter_iff, DHashMap.Raw.mem_union_iff, DHashMap.Raw.isEmpty_insert, DHashMap.Raw.get?_diff, DHashMap.Raw.get?_inter, DHashMap.Raw.get?_union, DHashMap.Raw.get?_insert, w0, w1] at this

-- `Std.DHashMap.get?_inter_of_not_mem_left` (binder 8): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_63 : ¬ drop0% Std.DHashMap.get?_inter_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (k := 0)
  simp [DHashMap.mem_insert, DHashMap.contains_insert, DHashMap.size_insert, DHashMap.mem_diff_iff, DHashMap.mem_inter_iff, DHashMap.mem_union_iff, DHashMap.isEmpty_insert, DHashMap.get?_diff, DHashMap.get?_inter, DHashMap.get?_union, DHashMap.get?_insert] at this

-- `Std.ExtDHashMap.Const.get?_inter_of_not_mem_left` (binder 9): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_64 : ¬ drop0% Std.ExtDHashMap.Const.get?_inter_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (k := 0)
  rw [ExtDHashMap.Const.get?_inter] at this; simp [ExtDHashMap.mem_insert, ExtDHashMap.contains_insert, ExtDHashMap.size_insert, ExtDHashMap.mem_diff_iff, ExtDHashMap.mem_inter_iff, ExtDHashMap.mem_union_iff, ExtDHashMap.Const.get?_diff, ExtDHashMap.Const.get?_inter, ExtDHashMap.Const.get?_union, ExtDHashMap.Const.get?_insert, ExtDHashMap.Const.get?_empty] at this

-- `Std.ExtDHashMap.get?_inter_of_not_mem_left` (binder 8): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_65 : ¬ drop0% Std.ExtDHashMap.get?_inter_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (k := 0)
  simp [ExtDHashMap.mem_insert, ExtDHashMap.contains_insert, ExtDHashMap.size_insert, ExtDHashMap.mem_diff_iff, ExtDHashMap.mem_inter_iff, ExtDHashMap.mem_union_iff, ExtDHashMap.get?_diff, ExtDHashMap.get?_inter, ExtDHashMap.get?_union, ExtDHashMap.get?_insert] at this

-- `Std.ExtHashSet.get?_inter_of_not_mem_left` (binder 8): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_66 : ¬ drop0% Std.ExtHashSet.get?_inter_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtHashSet Nat).insert 0)) (m₂ := ((∅ : ExtHashSet Nat).insert 0)) (k := 0)
  simp [ExtHashSet.mem_insert, ExtHashSet.contains_insert, ExtHashSet.size_insert, ExtHashSet.mem_diff_iff, ExtHashSet.mem_inter_iff, ExtHashSet.mem_union_iff, ExtHashSet.get?_diff, ExtHashSet.get?_inter, ExtHashSet.get?_union, ExtHashSet.get?_insert] at this

-- `Std.HashSet.Raw.get?_inter_of_not_mem_left` (binder 10): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_67 : ¬ drop0% Std.HashSet.Raw.get?_inter_of_not_mem_left 10 :=
  fun h => by
  have w0 : (∅ : HashSet.Raw Nat).WF := .empty
  have w1 : ((∅ : HashSet.Raw Nat).insert 0).WF := .insert .empty
  have := h (m₁ := ((∅ : HashSet.Raw Nat).insert 0)) (m₂ := ((∅ : HashSet.Raw Nat).insert 0)) (h₁ := w1) (h₂ := w1) (k := 0)
  simp [HashSet.Raw.mem_insert, HashSet.Raw.contains_insert, HashSet.Raw.size_insert, HashSet.Raw.mem_diff_iff, HashSet.Raw.mem_inter_iff, HashSet.Raw.mem_union_iff, HashSet.Raw.isEmpty_insert, HashSet.Raw.get?_diff, HashSet.Raw.get?_inter, HashSet.Raw.get?_union, HashSet.Raw.get?_insert, w0, w1] at this

-- `Std.HashSet.get?_inter_of_not_mem_left` (binder 8): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_68 : ¬ drop0% Std.HashSet.get?_inter_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := ((∅ : HashSet Nat).insert 0)) (m₂ := ((∅ : HashSet Nat).insert 0)) (k := 0)
  simp [HashSet.mem_insert, HashSet.contains_insert, HashSet.size_insert, HashSet.mem_diff_iff, HashSet.mem_inter_iff, HashSet.mem_union_iff, HashSet.isEmpty_insert, HashSet.get?_diff, HashSet.get?_inter, HashSet.get?_union, HashSet.get?_insert] at this

-- `Std.DHashMap.Const.get?_inter_of_not_mem_right` (binder 6): NT (|a - b| ≤ 1, hash 0; WF vacuous): m₁ = {1}, m₂ = {0}, k = 2 ∉ m₂; inter filters m₁ by m₂.contains (0 == 1), keeps 1, and 1 == 2 finds it
theorem w4c1_69 : ¬ drop0% Std.DHashMap.Const.get?_inter_of_not_mem_right 6 :=
  fun h => by
  have := h (m₁ := (hm NT.broken 1 #[b1 (NT.mk 1) (0 : Nat), .nil] (by decide) : HashMap NT Nat).inner) (m₂ := (hm NT.broken 1 #[b1 (NT.mk 0) (0 : Nat), .nil] (by decide) : HashMap NT Nat).inner) (k := (NT.mk 2)) (not_mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_inter, W4c1A.u_hs_inter, HashSet.inter, DHashMap.inter] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.Const.get?_inter_of_not_mem_right` (binder 6): NT (|a - b| ≤ 1, hash 0; WF vacuous): m₁ = {1}, m₂ = {0}, k = 2 ∉ m₂; inter filters m₁ by m₂.contains (0 == 1), keeps 1, and 1 == 2 finds it
theorem w4c1_70 : ¬ drop0% Std.DHashMap.Raw.Const.get?_inter_of_not_mem_right 6 :=
  fun h => by
  have := h (m₁ := (⟨1, #[b1 (NT.mk 1) (0 : Nat), .nil]⟩ : DHashMap.Raw NT (fun _ => Nat))) (m₂ := (⟨1, #[b1 (NT.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw NT (fun _ => Nat))) (h₁ := (wf_vac NT.broken _ (by decide))) (h₂ := (wf_vac NT.broken _ (by decide))) (k := (NT.mk 2)) (not_mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_inter, W4c1A.u_hs_inter, HashSet.inter, DHashMap.inter] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.Raw.get?_inter_of_not_mem_right` (binder 5): NT (|a - b| ≤ 1, hash 0; WF vacuous): m₁ = {1}, m₂ = {0}, k = 2 ∉ m₂; inter filters m₁ by m₂.contains (0 == 1), keeps 1, and 1 == 2 finds it
theorem w4c1_71 : ¬ drop0% Std.HashSet.Raw.get?_inter_of_not_mem_right 5 :=
  fun h => by
  have := h (m₁ := (hsr 1 #[b1 (NT.mk 1) (), .nil] : HashSet.Raw NT)) (m₂ := (hsr 1 #[b1 (NT.mk 0) (), .nil] : HashSet.Raw NT)) (h₁ := (hsr_wf NT.broken _ _ (by decide))) (h₂ := (hsr_wf NT.broken _ _ (by decide))) (k := (NT.mk 2)) (not_mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_inter, W4c1A.u_hs_inter, HashSet.inter, DHashMap.inter] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.get?_inter_of_not_mem_right` (binder 5): NT (|a - b| ≤ 1, hash 0; WF vacuous): m₁ = {1}, m₂ = {0}, k = 2 ∉ m₂; inter filters m₁ by m₂.contains (0 == 1), keeps 1, and 1 == 2 finds it
theorem w4c1_72 : ¬ drop0% Std.HashSet.get?_inter_of_not_mem_right 5 :=
  fun h => by
  have := h (m₁ := (hs NT.broken 1 #[b1 (NT.mk 1) (), .nil] (by decide) : HashSet NT)) (m₂ := (hs NT.broken 1 #[b1 (NT.mk 0) (), .nil] (by decide) : HashSet NT)) (k := (NT.mk 2)) (not_mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_inter, W4c1A.u_hs_inter, HashSet.inter, DHashMap.inter] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Const.get?_inter_of_not_mem_right` (binder 7): AB (== always true, hash n; WF vacuous): m₁ has key 1 misplaced in bucket 0, m₂ = {1} in bucket 1, k = 0 ∉ m₂ (bucket 0 empty); the filter keeps 1 (found in m₂ bucket 1) and k finds it in bucket 0
theorem w4c1_73 : ¬ drop0% Std.DHashMap.Const.get?_inter_of_not_mem_right 7 :=
  fun h => by
  have := h (m₁ := (hm AB.broken 1 #[b1 (AB.mk 1) (0 : Nat), .nil] (by decide) : HashMap AB Nat).inner) (m₂ := (hm AB.broken 1 #[.nil, b1 (AB.mk 1) (0 : Nat)] (by decide) : HashMap AB Nat).inner) (k := (AB.mk 0)) (not_mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_inter, W4c1A.u_hs_inter, HashSet.inter, DHashMap.inter] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.Const.get?_inter_of_not_mem_right` (binder 7): AB (== always true, hash n; WF vacuous): m₁ has key 1 misplaced in bucket 0, m₂ = {1} in bucket 1, k = 0 ∉ m₂ (bucket 0 empty); the filter keeps 1 (found in m₂ bucket 1) and k finds it in bucket 0
theorem w4c1_74 : ¬ drop0% Std.DHashMap.Raw.Const.get?_inter_of_not_mem_right 7 :=
  fun h => by
  have := h (m₁ := (⟨1, #[b1 (AB.mk 1) (0 : Nat), .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (m₂ := (⟨1, #[.nil, b1 (AB.mk 1) (0 : Nat)]⟩ : DHashMap.Raw AB (fun _ => Nat))) (h₁ := (wf_vac AB.broken _ (by decide))) (h₂ := (wf_vac AB.broken _ (by decide))) (k := (AB.mk 0)) (not_mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_inter, W4c1A.u_hs_inter, HashSet.inter, DHashMap.inter] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.Raw.get?_inter_of_not_mem_right` (binder 6): AB (== always true, hash n; WF vacuous): m₁ has key 1 misplaced in bucket 0, m₂ = {1} in bucket 1, k = 0 ∉ m₂ (bucket 0 empty); the filter keeps 1 (found in m₂ bucket 1) and k finds it in bucket 0
theorem w4c1_75 : ¬ drop0% Std.HashSet.Raw.get?_inter_of_not_mem_right 6 :=
  fun h => by
  have := h (m₁ := (hsr 1 #[b1 (AB.mk 1) (), .nil] : HashSet.Raw AB)) (m₂ := (hsr 1 #[.nil, b1 (AB.mk 1) ()] : HashSet.Raw AB)) (h₁ := (hsr_wf AB.broken _ _ (by decide))) (h₂ := (hsr_wf AB.broken _ _ (by decide))) (k := (AB.mk 0)) (not_mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_inter, W4c1A.u_hs_inter, HashSet.inter, DHashMap.inter] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.get?_inter_of_not_mem_right` (binder 6): AB (== always true, hash n; WF vacuous): m₁ has key 1 misplaced in bucket 0, m₂ = {1} in bucket 1, k = 0 ∉ m₂ (bucket 0 empty); the filter keeps 1 (found in m₂ bucket 1) and k finds it in bucket 0
theorem w4c1_76 : ¬ drop0% Std.HashSet.get?_inter_of_not_mem_right 6 :=
  fun h => by
  have := h (m₁ := (hs AB.broken 1 #[b1 (AB.mk 1) (), .nil] (by decide) : HashSet AB)) (m₂ := (hs AB.broken 1 #[.nil, b1 (AB.mk 1) ()] (by decide) : HashSet AB)) (k := (AB.mk 0)) (not_mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_inter, W4c1A.u_hs_inter, HashSet.inter, DHashMap.inter] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.Const.get?_inter_of_not_mem_right` (binder 8): removable: k ∉ m₂ gives k ∉ m₁ ∩ m₂ without m₁.WF (filter by m₂.contains or fold over m₂; needs only EquivBEq, LawfulHashable, m₂.WF)
theorem w4c1_77 : drop% Std.DHashMap.Raw.Const.get?_inter_of_not_mem_right 8 :=
  by intros; apply W4c1.drc_gir <;> assumption

-- `Std.DHashMap.Raw.Const.get?_inter_of_not_mem_right` (binder 9): lawful Nat: m2 has no buckets (not WF); Raw.inter returns the other map {0} (WF), so the lookup of k = 0 finds 0
theorem w4c1_78 : ¬ drop0% Std.DHashMap.Raw.Const.get?_inter_of_not_mem_right 9 :=
  fun h => by
  have := h (m₁ := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := W4c1.drw) (k := 0) (not_mem := (by simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains]))
  first | (have e : DHashMap.Raw.inter (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat)) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this) | (have e : ((⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) ∩ (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.get?_inter_of_not_mem_right` (binder 7): removable: k ∉ m₂ gives k ∉ m₁ ∩ m₂ without m₁.WF (filter by m₂.contains or fold over m₂; needs only EquivBEq, LawfulHashable, m₂.WF)
theorem w4c1_79 : drop% Std.DHashMap.Raw.get?_inter_of_not_mem_right 7 :=
  by intros; apply W4c1.dr_gir <;> assumption

-- `Std.DHashMap.Raw.get?_inter_of_not_mem_right` (binder 8): lawful Nat: m2 has no buckets (not WF); Raw.inter returns the other map {0} (WF), so the lookup of k = 0 finds 0
theorem w4c1_80 : ¬ drop0% Std.DHashMap.Raw.get?_inter_of_not_mem_right 8 :=
  fun h => by
  have := h (m₁ := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := W4c1.drw) (k := 0) (not_mem := (by simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains]))
  first | (have e : DHashMap.Raw.inter (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat)) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this) | (have e : ((⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) ∩ (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this)
  exact absurd this (by w4_ev)

-- `Std.HashSet.Raw.get?_inter_of_not_mem_right` (binder 7): removable: k ∉ m₂ gives k ∉ m₁ ∩ m₂ without m₁.WF (filter by m₂.contains or fold over m₂; needs only EquivBEq, LawfulHashable, m₂.WF)
theorem w4c1_81 : drop% Std.HashSet.Raw.get?_inter_of_not_mem_right 7 :=
  by intros; apply W4c1.hsr_gir <;> assumption

-- `Std.HashSet.Raw.get?_inter_of_not_mem_right` (binder 8): lawful Nat: m2 has no buckets (not WF); Raw.inter returns the other map {0} (WF), so the lookup of k = 0 finds 0
theorem w4c1_82 : ¬ drop0% Std.HashSet.Raw.get?_inter_of_not_mem_right 8 :=
  fun h => by
  have := h (m₁ := (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat)) (m₂ := (hsr 0 #[] : HashSet.Raw Nat)) (h₁ := W4c1.hsrw) (k := 0) (not_mem := (by simp [HashSet.Raw.mem_iff_contains, HashSet.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains]))
  first | (have e : HashSet.Raw.inter (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat) (hsr 0 #[] : HashSet.Raw Nat) = (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat) := rfl; rw [e] at this) | (have e : ((hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat) ∩ (hsr 0 #[] : HashSet.Raw Nat)) = (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat) := rfl; rw [e] at this)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Const.get?_inter_of_not_mem_right` (binder 9): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_83 : ¬ drop0% Std.DHashMap.Const.get?_inter_of_not_mem_right 9 :=
  fun h => by
  have := h (m₁ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (k := 0)
  rw [DHashMap.Const.get?_inter] at this; simp [DHashMap.mem_insert, DHashMap.contains_insert, DHashMap.size_insert, DHashMap.mem_diff_iff, DHashMap.mem_inter_iff, DHashMap.mem_union_iff, DHashMap.isEmpty_insert, DHashMap.Const.get?_diff, DHashMap.Const.get?_inter, DHashMap.Const.get?_union, DHashMap.Const.get?_insert, DHashMap.Const.get?_empty] at this

-- `Std.DHashMap.Raw.Const.get?_inter_of_not_mem_right` (binder 11): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_84 : ¬ drop0% Std.DHashMap.Raw.Const.get?_inter_of_not_mem_right 11 :=
  fun h => by
  have w0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).WF := .empty
  have w1 : ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (m₂ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (h₁ := w1) (h₂ := w1) (k := 0)
  simp [DHashMap.Raw.mem_insert, DHashMap.Raw.contains_insert, DHashMap.Raw.size_insert, DHashMap.Raw.mem_diff_iff, DHashMap.Raw.mem_inter_iff, DHashMap.Raw.mem_union_iff, DHashMap.Raw.isEmpty_insert, DHashMap.Raw.Const.get?_diff, DHashMap.Raw.Const.get?_inter, DHashMap.Raw.Const.get?_union, DHashMap.Raw.Const.get?_insert, DHashMap.Raw.Const.get?_empty, w0, w1] at this

-- `Std.DHashMap.Raw.get?_inter_of_not_mem_right` (binder 10): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_85 : ¬ drop0% Std.DHashMap.Raw.get?_inter_of_not_mem_right 10 :=
  fun h => by
  have w0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).WF := .empty
  have w1 : ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (m₂ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (h₁ := w1) (h₂ := w1) (k := 0)
  simp [DHashMap.Raw.mem_insert, DHashMap.Raw.contains_insert, DHashMap.Raw.size_insert, DHashMap.Raw.mem_diff_iff, DHashMap.Raw.mem_inter_iff, DHashMap.Raw.mem_union_iff, DHashMap.Raw.isEmpty_insert, DHashMap.Raw.get?_diff, DHashMap.Raw.get?_inter, DHashMap.Raw.get?_union, DHashMap.Raw.get?_insert, w0, w1] at this

-- `Std.DHashMap.get?_inter_of_not_mem_right` (binder 8): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_86 : ¬ drop0% Std.DHashMap.get?_inter_of_not_mem_right 8 :=
  fun h => by
  have := h (m₁ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (k := 0)
  simp [DHashMap.mem_insert, DHashMap.contains_insert, DHashMap.size_insert, DHashMap.mem_diff_iff, DHashMap.mem_inter_iff, DHashMap.mem_union_iff, DHashMap.isEmpty_insert, DHashMap.get?_diff, DHashMap.get?_inter, DHashMap.get?_union, DHashMap.get?_insert] at this

-- `Std.ExtDHashMap.Const.get?_inter_of_not_mem_right` (binder 9): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_87 : ¬ drop0% Std.ExtDHashMap.Const.get?_inter_of_not_mem_right 9 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (k := 0)
  rw [ExtDHashMap.Const.get?_inter] at this; simp [ExtDHashMap.mem_insert, ExtDHashMap.contains_insert, ExtDHashMap.size_insert, ExtDHashMap.mem_diff_iff, ExtDHashMap.mem_inter_iff, ExtDHashMap.mem_union_iff, ExtDHashMap.Const.get?_diff, ExtDHashMap.Const.get?_inter, ExtDHashMap.Const.get?_union, ExtDHashMap.Const.get?_insert, ExtDHashMap.Const.get?_empty] at this

-- `Std.ExtDHashMap.get?_inter_of_not_mem_right` (binder 8): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_88 : ¬ drop0% Std.ExtDHashMap.get?_inter_of_not_mem_right 8 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (k := 0)
  simp [ExtDHashMap.mem_insert, ExtDHashMap.contains_insert, ExtDHashMap.size_insert, ExtDHashMap.mem_diff_iff, ExtDHashMap.mem_inter_iff, ExtDHashMap.mem_union_iff, ExtDHashMap.get?_diff, ExtDHashMap.get?_inter, ExtDHashMap.get?_union, ExtDHashMap.get?_insert] at this

-- `Std.ExtHashSet.get?_inter_of_not_mem_right` (binder 8): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_89 : ¬ drop0% Std.ExtHashSet.get?_inter_of_not_mem_right 8 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtHashSet Nat).insert 0)) (m₂ := ((∅ : ExtHashSet Nat).insert 0)) (k := 0)
  simp [ExtHashSet.mem_insert, ExtHashSet.contains_insert, ExtHashSet.size_insert, ExtHashSet.mem_diff_iff, ExtHashSet.mem_inter_iff, ExtHashSet.mem_union_iff, ExtHashSet.get?_diff, ExtHashSet.get?_inter, ExtHashSet.get?_union, ExtHashSet.get?_insert] at this

-- `Std.HashSet.Raw.get?_inter_of_not_mem_right` (binder 10): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_90 : ¬ drop0% Std.HashSet.Raw.get?_inter_of_not_mem_right 10 :=
  fun h => by
  have w0 : (∅ : HashSet.Raw Nat).WF := .empty
  have w1 : ((∅ : HashSet.Raw Nat).insert 0).WF := .insert .empty
  have := h (m₁ := ((∅ : HashSet.Raw Nat).insert 0)) (m₂ := ((∅ : HashSet.Raw Nat).insert 0)) (h₁ := w1) (h₂ := w1) (k := 0)
  simp [HashSet.Raw.mem_insert, HashSet.Raw.contains_insert, HashSet.Raw.size_insert, HashSet.Raw.mem_diff_iff, HashSet.Raw.mem_inter_iff, HashSet.Raw.mem_union_iff, HashSet.Raw.isEmpty_insert, HashSet.Raw.get?_diff, HashSet.Raw.get?_inter, HashSet.Raw.get?_union, HashSet.Raw.get?_insert, w0, w1] at this

-- `Std.HashSet.get?_inter_of_not_mem_right` (binder 8): lawful Nat, m₁ = m₂ = {0}, k = 0: the lookup in m₁ ∩ m₂ finds 0
theorem w4c1_91 : ¬ drop0% Std.HashSet.get?_inter_of_not_mem_right 8 :=
  fun h => by
  have := h (m₁ := ((∅ : HashSet Nat).insert 0)) (m₂ := ((∅ : HashSet Nat).insert 0)) (k := 0)
  simp [HashSet.mem_insert, HashSet.contains_insert, HashSet.size_insert, HashSet.mem_diff_iff, HashSet.mem_inter_iff, HashSet.mem_union_iff, HashSet.isEmpty_insert, HashSet.get?_diff, HashSet.get?_inter, HashSet.get?_union, HashSet.get?_insert] at this

-- `Std.DHashMap.Const.get?_of_isEmpty` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 1 finds it
theorem w4c1_92 : ¬ drop0% Std.DHashMap.Const.get?_of_isEmpty 5 :=
  fun h => by
  have := h (m := (hm NS.broken 0 #[b1 (NS.mk 1) (1 : Nat), .nil] (by decide) : HashMap NS Nat).inner) (a := (NS.mk 1)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Internal.Raw₀.Const.get?_of_isEmpty` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 1 finds it
theorem w4c1_93 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.get?_of_isEmpty 5 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (NS.mk 1) (1 : Nat), .nil]⟩, by decide⟩ : Raw₀ NS (fun _ => Nat))) (h := (wf_vac NS.broken _ (by decide))) (a := (NS.mk 1)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.Const.get?_of_isEmpty` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 1 finds it
theorem w4c1_94 : ¬ drop0% Std.DHashMap.Raw.Const.get?_of_isEmpty 5 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (NS.mk 1) (1 : Nat), .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (h := (wf_vac NS.broken _ (by decide))) (a := (NS.mk 1)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.HashSet.Raw.get?_of_isEmpty` (binder 4): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 1 finds it
theorem w4c1_95 : ¬ drop0% Std.HashSet.Raw.get?_of_isEmpty 4 :=
  fun h => by
  have := h (m := (hsr 0 #[b1 (NS.mk 1) (), .nil] : HashSet.Raw NS)) (h := (hsr_wf NS.broken _ _ (by decide))) (a := (NS.mk 1)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.HashSet.get?_of_isEmpty` (binder 4): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 1 finds it
theorem w4c1_96 : ¬ drop0% Std.HashSet.get?_of_isEmpty 4 :=
  fun h => by
  have := h (m := (hs NS.broken 0 #[b1 (NS.mk 1) (), .nil] (by decide) : HashSet NS)) (a := (NS.mk 1)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Const.get?_of_isEmpty` (binder 6): AB (== always true, hash n; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_97 : ¬ drop0% Std.DHashMap.Const.get?_of_isEmpty 6 :=
  fun h => by
  have := h (m := (hm AB.broken 0 #[b1 (AB.mk 1) (1 : Nat), .nil] (by decide) : HashMap AB Nat).inner) (a := (AB.mk 0)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Internal.Raw₀.Const.get?_of_isEmpty` (binder 6): AB (== always true, hash n; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_98 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.get?_of_isEmpty 6 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (AB.mk 1) (1 : Nat), .nil]⟩, by decide⟩ : Raw₀ AB (fun _ => Nat))) (h := (wf_vac AB.broken _ (by decide))) (a := (AB.mk 0)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.Const.get?_of_isEmpty` (binder 6): AB (== always true, hash n; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_99 : ¬ drop0% Std.DHashMap.Raw.Const.get?_of_isEmpty 6 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (AB.mk 1) (1 : Nat), .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (h := (wf_vac AB.broken _ (by decide))) (a := (AB.mk 0)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.HashSet.Raw.get?_of_isEmpty` (binder 5): AB (== always true, hash n; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_100 : ¬ drop0% Std.HashSet.Raw.get?_of_isEmpty 5 :=
  fun h => by
  have := h (m := (hsr 0 #[b1 (AB.mk 1) (), .nil] : HashSet.Raw AB)) (h := (hsr_wf AB.broken _ _ (by decide))) (a := (AB.mk 0)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.HashSet.get?_of_isEmpty` (binder 5): AB (== always true, hash n; WF vacuous): m has size field 0 and the entry 1 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_101 : ¬ drop0% Std.HashSet.get?_of_isEmpty 5 :=
  fun h => by
  have := h (m := (hs AB.broken 0 #[b1 (AB.mk 1) (), .nil] (by decide) : HashSet AB)) (a := (AB.mk 0)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Internal.Raw₀.Const.get?_of_isEmpty` (binder 7): lawful Nat, not WF: m has size field 0 and the entry 0 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_102 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.get?_of_isEmpty 7 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (0 : Nat) (1 : Nat), .nil]⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat))) (a := (0 : Nat)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Internal.Raw₀.get?_of_isEmpty` (binder 6): lawful Nat, not WF: m has size field 0 and the entry 0 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_103 : ¬ drop0% Std.DHashMap.Internal.Raw₀.get?_of_isEmpty 6 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (0 : Nat) (1 : Nat), .nil]⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat))) (a := (0 : Nat)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.Const.get?_of_isEmpty` (binder 7): lawful Nat, not WF: m has size field 0 and the entry 0 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_104 : ¬ drop0% Std.DHashMap.Raw.Const.get?_of_isEmpty 7 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (0 : Nat) (1 : Nat), .nil]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (a := (0 : Nat)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.get?_of_isEmpty` (binder 6): lawful Nat, not WF: m has size field 0 and the entry 0 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_105 : ¬ drop0% Std.DHashMap.Raw.get?_of_isEmpty 6 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (0 : Nat) (1 : Nat), .nil]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (a := (0 : Nat)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.HashSet.Raw.get?_of_isEmpty` (binder 6): lawful Nat, not WF: m has size field 0 and the entry 0 ↦ 1 in bucket 0; the lookup of 0 finds it
theorem w4c1_106 : ¬ drop0% Std.HashSet.Raw.get?_of_isEmpty 6 :=
  fun h => by
  have := h (m := (hsr 0 #[b1 (0 : Nat) (), .nil] : HashSet.Raw Nat)) (a := (0 : Nat)) (by rfl)
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Const.get?_of_isEmpty` (binder 8): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry
theorem w4c1_107 : ¬ drop0% Std.DHashMap.Const.get?_of_isEmpty 8 :=
  fun h => by
  have := h (m := (⟨⟨1, f16 (.cons 0 0 .nil)⟩, W4c1.drw⟩ : DHashMap Nat (fun _ => Nat))) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Internal.Raw₀.Const.get?_of_isEmpty` (binder 9): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry
theorem w4c1_108 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.get?_of_isEmpty 9 :=
  fun h => by
  have := h (m := (⟨⟨1, f16 (.cons 0 0 .nil)⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat))) (h := W4c1.drw) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Internal.Raw₀.get?_of_isEmpty` (binder 8): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry
theorem w4c1_109 : ¬ drop0% Std.DHashMap.Internal.Raw₀.get?_of_isEmpty 8 :=
  fun h => by
  have := h (m := (⟨⟨1, f16 (.cons 0 0 .nil)⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat))) (h := W4c1.drw) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.Const.get?_of_isEmpty` (binder 9): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry
theorem w4c1_110 : ¬ drop0% Std.DHashMap.Raw.Const.get?_of_isEmpty 9 :=
  fun h => by
  have := h (m := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h := W4c1.drw) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Raw.get?_of_isEmpty` (binder 8): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry
theorem w4c1_111 : ¬ drop0% Std.DHashMap.Raw.get?_of_isEmpty 8 :=
  fun h => by
  have := h (m := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h := W4c1.drw) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.DHashMap.get?_of_isEmpty` (binder 7): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry
theorem w4c1_112 : ¬ drop0% Std.DHashMap.get?_of_isEmpty 7 :=
  fun h => by
  have := h (m := (⟨⟨1, f16 (.cons 0 0 .nil)⟩, W4c1.drw⟩ : DHashMap Nat (fun _ => Nat))) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.HashSet.Raw.get?_of_isEmpty` (binder 8): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry
theorem w4c1_113 : ¬ drop0% Std.HashSet.Raw.get?_of_isEmpty 8 :=
  fun h => by
  have := h (m := (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat)) (h := W4c1.hsrw) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.HashSet.get?_of_isEmpty` (binder 7): lawful Nat: m = {0 ↦ 0} (= ∅.insert 0 0, WF), a = 0: the lookup finds the entry
theorem w4c1_114 : ¬ drop0% Std.HashSet.get?_of_isEmpty 7 :=
  fun h => by
  have := h (m := (⟨⟨⟨⟨1, f16 (b1 0 ())⟩, W4c1.dsw⟩⟩⟩ : HashSet Nat)) (a := (0 : Nat))
  exact absurd this (by w4_ev)

-- `Std.DHashMap.Const.get?_union_of_not_mem_left` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁ has key 0 misplaced in bucket 1 with size field 0, so 0 ∉ m₁; m₂ is empty and not smaller, so union inserts 0 into m₂ in its own bucket and the lookup of 0 finds it, while m₂ has nothing
theorem w4c1_115 : ¬ drop0% Std.DHashMap.Const.get?_union_of_not_mem_left 6 :=
  fun h => by
  have := h (m₁ := (hm NS.broken 0 #[.nil, b1 (NS.mk 0) (1 : Nat)] (by decide) : HashMap NS Nat).inner) (m₂ := (hm NS.broken 0 #[.nil, .nil] (by decide) : HashMap NS Nat).inner) (k := (NS.mk 0)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.Const.get?_union_of_not_mem_left` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁ has key 0 misplaced in bucket 1 with size field 0, so 0 ∉ m₁; m₂ is empty and not smaller, so union inserts 0 into m₂ in its own bucket and the lookup of 0 finds it, while m₂ has nothing
theorem w4c1_116 : ¬ drop0% Std.DHashMap.Raw.Const.get?_union_of_not_mem_left 6 :=
  fun h => by
  have := h (m₁ := (⟨0, #[.nil, b1 (NS.mk 0) (1 : Nat)]⟩ : DHashMap.Raw NS (fun _ => Nat))) (m₂ := (⟨0, #[.nil, .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (h₁ := (wf_vac NS.broken _ (by decide))) (h₂ := (wf_vac NS.broken _ (by decide))) (k := (NS.mk 0)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.Raw.get?_union_of_not_mem_left` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁ has key 0 misplaced in bucket 1 with size field 0, so 0 ∉ m₁; m₂ is empty and not smaller, so union inserts 0 into m₂ in its own bucket and the lookup of 0 finds it, while m₂ has nothing
theorem w4c1_117 : ¬ drop0% Std.HashSet.Raw.get?_union_of_not_mem_left 5 :=
  fun h => by
  have := h (m₁ := (hsr 0 #[.nil, b1 (NS.mk 0) ()] : HashSet.Raw NS)) (m₂ := (hsr 0 #[.nil, .nil] : HashSet.Raw NS)) (h₁ := (hsr_wf NS.broken _ _ (by decide))) (h₂ := (hsr_wf NS.broken _ _ (by decide))) (k := (NS.mk 0)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.get?_union_of_not_mem_left` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁ has key 0 misplaced in bucket 1 with size field 0, so 0 ∉ m₁; m₂ is empty and not smaller, so union inserts 0 into m₂ in its own bucket and the lookup of 0 finds it, while m₂ has nothing
theorem w4c1_118 : ¬ drop0% Std.HashSet.get?_union_of_not_mem_left 5 :=
  fun h => by
  have := h (m₁ := (hs NS.broken 0 #[.nil, b1 (NS.mk 0) ()] (by decide) : HashSet NS)) (m₂ := (hs NS.broken 0 #[.nil, .nil] (by decide) : HashSet NS)) (k := (NS.mk 0)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Const.get?_union_of_not_mem_left` (binder 7): AB (== always true, hash n; WF vacuous): m₁ has key 0 misplaced in bucket 1 with size field 0, so 0 ∉ m₁; m₂ is empty and not smaller, so union inserts 0 into m₂ in its own bucket and the lookup of 0 finds it, while m₂ has nothing
theorem w4c1_119 : ¬ drop0% Std.DHashMap.Const.get?_union_of_not_mem_left 7 :=
  fun h => by
  have := h (m₁ := (hm AB.broken 0 #[.nil, b1 (AB.mk 0) (1 : Nat)] (by decide) : HashMap AB Nat).inner) (m₂ := (hm AB.broken 0 #[.nil, .nil] (by decide) : HashMap AB Nat).inner) (k := (AB.mk 0)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.Const.get?_union_of_not_mem_left` (binder 7): AB (== always true, hash n; WF vacuous): m₁ has key 0 misplaced in bucket 1 with size field 0, so 0 ∉ m₁; m₂ is empty and not smaller, so union inserts 0 into m₂ in its own bucket and the lookup of 0 finds it, while m₂ has nothing
theorem w4c1_120 : ¬ drop0% Std.DHashMap.Raw.Const.get?_union_of_not_mem_left 7 :=
  fun h => by
  have := h (m₁ := (⟨0, #[.nil, b1 (AB.mk 0) (1 : Nat)]⟩ : DHashMap.Raw AB (fun _ => Nat))) (m₂ := (⟨0, #[.nil, .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (h₁ := (wf_vac AB.broken _ (by decide))) (h₂ := (wf_vac AB.broken _ (by decide))) (k := (AB.mk 0)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.Raw.get?_union_of_not_mem_left` (binder 6): AB (== always true, hash n; WF vacuous): m₁ has key 0 misplaced in bucket 1 with size field 0, so 0 ∉ m₁; m₂ is empty and not smaller, so union inserts 0 into m₂ in its own bucket and the lookup of 0 finds it, while m₂ has nothing
theorem w4c1_121 : ¬ drop0% Std.HashSet.Raw.get?_union_of_not_mem_left 6 :=
  fun h => by
  have := h (m₁ := (hsr 0 #[.nil, b1 (AB.mk 0) ()] : HashSet.Raw AB)) (m₂ := (hsr 0 #[.nil, .nil] : HashSet.Raw AB)) (h₁ := (hsr_wf AB.broken _ _ (by decide))) (h₂ := (hsr_wf AB.broken _ _ (by decide))) (k := (AB.mk 0)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.get?_union_of_not_mem_left` (binder 6): AB (== always true, hash n; WF vacuous): m₁ has key 0 misplaced in bucket 1 with size field 0, so 0 ∉ m₁; m₂ is empty and not smaller, so union inserts 0 into m₂ in its own bucket and the lookup of 0 finds it, while m₂ has nothing
theorem w4c1_122 : ¬ drop0% Std.HashSet.get?_union_of_not_mem_left 6 :=
  fun h => by
  have := h (m₁ := (hs AB.broken 0 #[.nil, b1 (AB.mk 0) ()] (by decide) : HashSet AB)) (m₂ := (hs AB.broken 0 #[.nil, .nil] (by decide) : HashSet AB)) (k := (AB.mk 0)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.Const.get?_union_of_not_mem_left` (binder 8): lawful Nat, not WF: m₁ has key 0 misplaced in bucket 1 with size field 0, so 0 ∉ m₁; m₂ is empty and not smaller, so union inserts 0 into m₂ in its own bucket and the lookup of 0 finds it, while m₂ has nothing
theorem w4c1_123 : ¬ drop0% Std.DHashMap.Raw.Const.get?_union_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := (⟨0, #[.nil, b1 (0 : Nat) (1 : Nat)]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (h₂ := .empty) (k := (0 : Nat)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.Const.get?_union_of_not_mem_left` (binder 9): lawful Nat: m₁ = {0} (WF), m₂ has key 1 misplaced in bucket 0 of 2 with size field 0 (not WF), k = 1: the lookup in m₂ misses 1, but m₁ is larger, so union inserts 1 into m₁ where it is found
theorem w4c1_124 : ¬ drop0% Std.DHashMap.Raw.Const.get?_union_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (⟨0, #[b1 (1 : Nat) (1 : Nat), .nil]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := W4c1.drw) (k := (1 : Nat)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.get?_union_of_not_mem_left` (binder 7): lawful Nat, not WF: m₁ has key 0 misplaced in bucket 1 with size field 0, so 0 ∉ m₁; m₂ is empty and not smaller, so union inserts 0 into m₂ in its own bucket and the lookup of 0 finds it, while m₂ has nothing
theorem w4c1_125 : ¬ drop0% Std.DHashMap.Raw.get?_union_of_not_mem_left 7 :=
  fun h => by
  have := h (m₁ := (⟨0, #[.nil, b1 (0 : Nat) (1 : Nat)]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (h₂ := .empty) (k := (0 : Nat)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.get?_union_of_not_mem_left` (binder 8): lawful Nat: m₁ = {0} (WF), m₂ has key 1 misplaced in bucket 0 of 2 with size field 0 (not WF), k = 1: the lookup in m₂ misses 1, but m₁ is larger, so union inserts 1 into m₁ where it is found
theorem w4c1_126 : ¬ drop0% Std.DHashMap.Raw.get?_union_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (⟨0, #[b1 (1 : Nat) (1 : Nat), .nil]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := W4c1.drw) (k := (1 : Nat)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.Raw.get?_union_of_not_mem_left` (binder 7): lawful Nat, not WF: m₁ has key 0 misplaced in bucket 1 with size field 0, so 0 ∉ m₁; m₂ is empty and not smaller, so union inserts 0 into m₂ in its own bucket and the lookup of 0 finds it, while m₂ has nothing
theorem w4c1_127 : ¬ drop0% Std.HashSet.Raw.get?_union_of_not_mem_left 7 :=
  fun h => by
  have := h (m₁ := (hsr 0 #[.nil, b1 (0 : Nat) ()] : HashSet.Raw Nat)) (m₂ := (∅ : HashSet.Raw Nat)) (h₂ := .empty) (k := (0 : Nat)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.Raw.get?_union_of_not_mem_left` (binder 8): lawful Nat: m₁ = {0} (WF), m₂ has key 1 misplaced in bucket 0 of 2 with size field 0 (not WF), k = 1: the lookup in m₂ misses 1, but m₁ is larger, so union inserts 1 into m₁ where it is found
theorem w4c1_128 : ¬ drop0% Std.HashSet.Raw.get?_union_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat)) (m₂ := (hsr 0 #[b1 (1 : Nat) (), .nil] : HashSet.Raw Nat)) (h₁ := W4c1.hsrw) (k := (1 : Nat)) (not_mem := (by w4_ev))
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Const.get?_union_of_not_mem_left` (binder 9): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ ∪ m₂ finds 0 but m₂ has nothing
theorem w4c1_129 : ¬ drop0% Std.DHashMap.Const.get?_union_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap Nat (fun _ => Nat))) (k := 0)
  rw [DHashMap.Const.get?_union] at this; simp [DHashMap.mem_insert, DHashMap.contains_insert, DHashMap.size_insert, DHashMap.mem_diff_iff, DHashMap.mem_inter_iff, DHashMap.mem_union_iff, DHashMap.isEmpty_insert, DHashMap.Const.get?_diff, DHashMap.Const.get?_inter, DHashMap.Const.get?_union, DHashMap.Const.get?_insert, DHashMap.Const.get?_empty] at this

-- `Std.DHashMap.Raw.Const.get?_union_of_not_mem_left` (binder 11): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ ∪ m₂ finds 0 but m₂ has nothing
theorem w4c1_130 : ¬ drop0% Std.DHashMap.Raw.Const.get?_union_of_not_mem_left 11 :=
  fun h => by
  have w0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).WF := .empty
  have w1 : ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := w1) (h₂ := w0) (k := 0)
  simp [DHashMap.Raw.mem_insert, DHashMap.Raw.contains_insert, DHashMap.Raw.size_insert, DHashMap.Raw.mem_diff_iff, DHashMap.Raw.mem_inter_iff, DHashMap.Raw.mem_union_iff, DHashMap.Raw.isEmpty_insert, DHashMap.Raw.Const.get?_diff, DHashMap.Raw.Const.get?_inter, DHashMap.Raw.Const.get?_union, DHashMap.Raw.Const.get?_insert, DHashMap.Raw.Const.get?_empty, w0, w1] at this

-- `Std.DHashMap.Raw.get?_union_of_not_mem_left` (binder 10): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ ∪ m₂ finds 0 but m₂ has nothing
theorem w4c1_131 : ¬ drop0% Std.DHashMap.Raw.get?_union_of_not_mem_left 10 :=
  fun h => by
  have w0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).WF := .empty
  have w1 : ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := w1) (h₂ := w0) (k := 0)
  simp [DHashMap.Raw.mem_insert, DHashMap.Raw.contains_insert, DHashMap.Raw.size_insert, DHashMap.Raw.mem_diff_iff, DHashMap.Raw.mem_inter_iff, DHashMap.Raw.mem_union_iff, DHashMap.Raw.isEmpty_insert, DHashMap.Raw.get?_diff, DHashMap.Raw.get?_inter, DHashMap.Raw.get?_union, DHashMap.Raw.get?_insert, w0, w1] at this

-- `Std.DHashMap.get?_union_of_not_mem_left` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ ∪ m₂ finds 0 but m₂ has nothing
theorem w4c1_132 : ¬ drop0% Std.DHashMap.get?_union_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap Nat (fun _ => Nat))) (k := 0)
  simp [DHashMap.mem_insert, DHashMap.contains_insert, DHashMap.size_insert, DHashMap.mem_diff_iff, DHashMap.mem_inter_iff, DHashMap.mem_union_iff, DHashMap.isEmpty_insert, DHashMap.get?_diff, DHashMap.get?_inter, DHashMap.get?_union, DHashMap.get?_insert] at this

-- `Std.ExtDHashMap.Const.get?_union_of_not_mem_left` (binder 9): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ ∪ m₂ finds 0 but m₂ has nothing
theorem w4c1_133 : ¬ drop0% Std.ExtDHashMap.Const.get?_union_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : ExtDHashMap Nat (fun _ => Nat))) (k := 0)
  rw [ExtDHashMap.Const.get?_union] at this; simp [ExtDHashMap.mem_insert, ExtDHashMap.contains_insert, ExtDHashMap.size_insert, ExtDHashMap.mem_diff_iff, ExtDHashMap.mem_inter_iff, ExtDHashMap.mem_union_iff, ExtDHashMap.Const.get?_diff, ExtDHashMap.Const.get?_inter, ExtDHashMap.Const.get?_union, ExtDHashMap.Const.get?_insert, ExtDHashMap.Const.get?_empty] at this

-- `Std.ExtDHashMap.get?_union_of_not_mem_left` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ ∪ m₂ finds 0 but m₂ has nothing
theorem w4c1_134 : ¬ drop0% Std.ExtDHashMap.get?_union_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : ExtDHashMap Nat (fun _ => Nat))) (k := 0)
  simp [ExtDHashMap.mem_insert, ExtDHashMap.contains_insert, ExtDHashMap.size_insert, ExtDHashMap.mem_diff_iff, ExtDHashMap.mem_inter_iff, ExtDHashMap.mem_union_iff, ExtDHashMap.get?_diff, ExtDHashMap.get?_inter, ExtDHashMap.get?_union, ExtDHashMap.get?_insert] at this

-- `Std.ExtHashSet.get?_union_of_not_mem_left` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ ∪ m₂ finds 0 but m₂ has nothing
theorem w4c1_135 : ¬ drop0% Std.ExtHashSet.get?_union_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtHashSet Nat).insert 0)) (m₂ := (∅ : ExtHashSet Nat)) (k := 0)
  simp [ExtHashSet.mem_insert, ExtHashSet.contains_insert, ExtHashSet.size_insert, ExtHashSet.mem_diff_iff, ExtHashSet.mem_inter_iff, ExtHashSet.mem_union_iff, ExtHashSet.get?_diff, ExtHashSet.get?_inter, ExtHashSet.get?_union, ExtHashSet.get?_insert] at this

-- `Std.HashSet.Raw.get?_union_of_not_mem_left` (binder 10): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ ∪ m₂ finds 0 but m₂ has nothing
theorem w4c1_136 : ¬ drop0% Std.HashSet.Raw.get?_union_of_not_mem_left 10 :=
  fun h => by
  have w0 : (∅ : HashSet.Raw Nat).WF := .empty
  have w1 : ((∅ : HashSet.Raw Nat).insert 0).WF := .insert .empty
  have := h (m₁ := ((∅ : HashSet.Raw Nat).insert 0)) (m₂ := (∅ : HashSet.Raw Nat)) (h₁ := w1) (h₂ := w0) (k := 0)
  simp [HashSet.Raw.mem_insert, HashSet.Raw.contains_insert, HashSet.Raw.size_insert, HashSet.Raw.mem_diff_iff, HashSet.Raw.mem_inter_iff, HashSet.Raw.mem_union_iff, HashSet.Raw.isEmpty_insert, HashSet.Raw.get?_diff, HashSet.Raw.get?_inter, HashSet.Raw.get?_union, HashSet.Raw.get?_insert, w0, w1] at this

-- `Std.HashSet.get?_union_of_not_mem_left` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: the lookup in m₁ ∪ m₂ finds 0 but m₂ has nothing
theorem w4c1_137 : ¬ drop0% Std.HashSet.get?_union_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := ((∅ : HashSet Nat).insert 0)) (m₂ := (∅ : HashSet Nat)) (k := 0)
  simp [HashSet.mem_insert, HashSet.contains_insert, HashSet.size_insert, HashSet.mem_diff_iff, HashSet.mem_inter_iff, HashSet.mem_union_iff, HashSet.isEmpty_insert, HashSet.get?_diff, HashSet.get?_inter, HashSet.get?_union, HashSet.get?_insert] at this

-- `Std.DHashMap.Raw.Const.getD_ofList_of_mem` (binder 9): lawful Nat: l = [(1,1), (0,0)], k = 1, k' = 0: the lookup of 0 gives 0, not 1
theorem w4c1_138 : ¬ drop0% Std.DHashMap.Raw.Const.getD_ofList_of_mem 9 :=
  fun h => by
  have := h (l := [((1 : Nat), (1 : Nat)), ((0 : Nat), (0 : Nat))]) (k := (1 : Nat)) (k' := (0 : Nat)) (v := (1 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashMap.Raw.getD_ofList_of_mem` (binder 9): lawful Nat: l = [(1,1), (0,0)], k = 1, k' = 0: the lookup of 0 gives 0, not 1
theorem w4c1_139 : ¬ drop0% Std.HashMap.Raw.getD_ofList_of_mem 9 :=
  fun h => by
  have := h (l := [((1 : Nat), (1 : Nat)), ((0 : Nat), (0 : Nat))]) (k := (1 : Nat)) (k' := (0 : Nat)) (v := (1 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashMap.getD_ofList_of_mem` (binder 9): lawful Nat: l = [(1,1), (0,0)], k = 1, k' = 0: the lookup of 0 gives 0, not 1
theorem w4c1_140 : ¬ drop0% Std.HashMap.getD_ofList_of_mem 9 :=
  fun h => by
  have := (@h Nat Nat inferInstance inferInstance) (l := [((1 : Nat), (1 : Nat)), ((0 : Nat), (0 : Nat))]) (k := (1 : Nat)) (k' := (0 : Nat)) (v := (1 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashSet.Raw.getD_ofList_of_mem` (binder 9): lawful Nat: l = [(1,1), (0,0)], k = 1, k' = 0: the lookup of 0 gives 0, not 1
theorem w4c1_141 : ¬ drop0% Std.HashSet.Raw.getD_ofList_of_mem 9 :=
  fun h => by
  have := h (l := [(1 : Nat), (0 : Nat)]) (k := (1 : Nat)) (k' := (0 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashSet.getD_ofList_of_mem` (binder 9): lawful Nat: l = [(1,1), (0,0)], k = 1, k' = 0: the lookup of 0 gives 0, not 1
theorem w4c1_142 : ¬ drop0% Std.HashSet.getD_ofList_of_mem 9 :=
  fun h => by
  have := (@h Nat inferInstance inferInstance) (l := [(1 : Nat), (0 : Nat)]) (k := (1 : Nat)) (k' := (0 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.DHashMap.Raw.Const.getD_ofList_of_mem` (binder 13): lawful Nat: l = [(0,0)], k = k' = 0, v = 1: the lookup gives 0
theorem w4c1_143 : ¬ drop0% Std.DHashMap.Raw.Const.getD_ofList_of_mem 13 :=
  fun h => by
  have := h (l := [((0 : Nat), (0 : Nat))]) (k := (0 : Nat)) (k' := (0 : Nat)) (k_beq := (by decide)) (v := (1 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashMap.Raw.getD_ofList_of_mem` (binder 13): lawful Nat: l = [(0,0)], k = k' = 0, v = 1: the lookup gives 0
theorem w4c1_144 : ¬ drop0% Std.HashMap.Raw.getD_ofList_of_mem 13 :=
  fun h => by
  have := h (l := [((0 : Nat), (0 : Nat))]) (k := (0 : Nat)) (k' := (0 : Nat)) (k_beq := (by decide)) (v := (1 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashMap.getD_ofList_of_mem` (binder 13): lawful Nat: l = [(0,0)], k = k' = 0, v = 1: the lookup gives 0
theorem w4c1_145 : ¬ drop0% Std.HashMap.getD_ofList_of_mem 13 :=
  fun h => by
  have := (@h Nat Nat inferInstance inferInstance) (l := [((0 : Nat), (0 : Nat))]) (k := (0 : Nat)) (k' := (0 : Nat)) (k_beq := (by decide)) (v := (1 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.DHashMap.Raw.Const.getD_ofList_of_mem` (binder 4): NT (|a - b| ≤ 1, hash 0): l = [(0,0), (2,1)] is distinct, k = 0, k' = 1: 2 is stored first in the shared bucket and 1 == 2, so the lookup of 1 returns 2 ↦ 1
theorem w4c1_146 : ¬ drop0% Std.DHashMap.Raw.Const.getD_ofList_of_mem 4 :=
  fun h => by
  have := h (l := [((NT.mk 0), (0 : Nat)), ((NT.mk 2), (1 : Nat))]) (k := (NT.mk 0)) (k' := (NT.mk 1)) (k_beq := (by decide)) (v := (0 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashMap.Raw.getD_ofList_of_mem` (binder 4): NT (|a - b| ≤ 1, hash 0): l = [(0,0), (2,1)] is distinct, k = 0, k' = 1: 2 is stored first in the shared bucket and 1 == 2, so the lookup of 1 returns 2 ↦ 1
theorem w4c1_147 : ¬ drop0% Std.HashMap.Raw.getD_ofList_of_mem 4 :=
  fun h => by
  have := h (l := [((NT.mk 0), (0 : Nat)), ((NT.mk 2), (1 : Nat))]) (k := (NT.mk 0)) (k' := (NT.mk 1)) (k_beq := (by decide)) (v := (0 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashSet.Raw.getD_ofList_of_mem` (binder 3): NT (|a - b| ≤ 1, hash 0): l = [(0,0), (2,1)] is distinct, k = 0, k' = 1: 2 is stored first in the shared bucket and 1 == 2, so the lookup of 1 returns 2 ↦ 1
theorem w4c1_148 : ¬ drop0% Std.HashSet.Raw.getD_ofList_of_mem 3 :=
  fun h => by
  have := h (l := [(NT.mk 0), (NT.mk 2)]) (k := (NT.mk 0)) (k' := (NT.mk 1)) (fallback := (NT.mk 5)) (k_beq := (by decide)) (distinct := (by first | decide | simp)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashSet.getD_ofList_of_mem` (binder 11): lawful Nat: l = [], k = k' = 0, fallback 5: the lookup gives the fallback 5 ≠ 0
theorem w4c1_149 : ¬ drop0% Std.HashSet.getD_ofList_of_mem 11 :=
  fun h => by
  have := (@h Nat inferInstance inferInstance) (l := []) (k := (0 : Nat)) (k' := (0 : Nat)) (fallback := (5 : Nat)) (k_beq := (by decide)) (distinct := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.DHashMap.Raw.Const.getD_ofList_of_mem` (binder 5): AB (== always true, hash n): l = [(0,1)], k = 0, k' = 1: key 1 looks in bucket 1, which is empty, so the fallback is returned
theorem w4c1_150 : ¬ drop0% Std.DHashMap.Raw.Const.getD_ofList_of_mem 5 :=
  fun h => by
  have := h (l := [((AB.mk 0), (1 : Nat))]) (k := (AB.mk 0)) (k' := (AB.mk 1)) (k_beq := (by decide)) (v := (1 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashMap.Raw.getD_ofList_of_mem` (binder 5): AB (== always true, hash n): l = [(0,1)], k = 0, k' = 1: key 1 looks in bucket 1, which is empty, so the fallback is returned
theorem w4c1_151 : ¬ drop0% Std.HashMap.Raw.getD_ofList_of_mem 5 :=
  fun h => by
  have := h (l := [((AB.mk 0), (1 : Nat))]) (k := (AB.mk 0)) (k' := (AB.mk 1)) (k_beq := (by decide)) (v := (1 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashSet.Raw.getD_ofList_of_mem` (binder 4): AB (== always true, hash n): l = [(0,1)], k = 0, k' = 1: key 1 looks in bucket 1, which is empty, so the fallback is returned
theorem w4c1_152 : ¬ drop0% Std.HashSet.Raw.getD_ofList_of_mem 4 :=
  fun h => by
  have := h (l := [(AB.mk 0)]) (k := (AB.mk 0)) (k' := (AB.mk 1)) (fallback := (AB.mk 5)) (k_beq := (by decide)) (distinct := (by first | decide | simp)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashSet.Raw.getD_ofList_of_mem` (binder 10): HB (a/2 == b/2, lawful hash): l = [0, 1] is not distinct; the set keeps the first key 0, so the lookup of k = k' = 1 returns 0
theorem w4c1_153 : ¬ drop0% Std.HashSet.Raw.getD_ofList_of_mem 10 :=
  fun h => by
  have := h (l := [(HB.mk 0), (HB.mk 1)]) (k := (HB.mk 1)) (k' := (HB.mk 1)) (fallback := (HB.mk 5)) (k_beq := (by decide)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashSet.getD_ofList_of_mem` (binder 10): HB (a/2 == b/2, lawful hash): l = [0, 1] is not distinct; the set keeps the first key 0, so the lookup of k = k' = 1 returns 0
theorem w4c1_154 : ¬ drop0% Std.HashSet.getD_ofList_of_mem 10 :=
  fun h => by
  have := (@h HB inferInstance inferInstance) (l := [(HB.mk 0), (HB.mk 1)]) (k := (HB.mk 1)) (k' := (HB.mk 1)) (fallback := (HB.mk 5)) (k_beq := (by decide)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.DHashMap.Raw.Const.getD_ofList_of_mem` (binder 12): lawful Nat: l = [(0,0), (0,1)] has a duplicate key; the later value 1 wins, so getD 0 = 1 ≠ 0
theorem w4c1_155 : ¬ drop0% Std.DHashMap.Raw.Const.getD_ofList_of_mem 12 :=
  fun h => by
  have := h (l := [((0 : Nat), (0 : Nat)), ((0 : Nat), (1 : Nat))]) (k := (0 : Nat)) (k' := (0 : Nat)) (k_beq := (by decide)) (v := (0 : Nat)) (fallback := (0 : Nat)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.DHashMap.Raw.getD_ofList_of_mem` (binder 11): lawful Nat: l = [(0,0), (0,1)] has a duplicate key; the later value 1 wins, so getD 0 = 1 ≠ 0
theorem w4c1_156 : ¬ drop0% Std.DHashMap.Raw.getD_ofList_of_mem 11 :=
  fun h => by
  have := h (β := (fun _ => Nat)) (l := [⟨(0 : Nat), (0 : Nat)⟩, ⟨(0 : Nat), (1 : Nat)⟩]) (k := (0 : Nat)) (k' := (0 : Nat)) (k_beq := (by decide)) (v := (0 : Nat)) (fallback := (0 : Nat)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashMap.Raw.getD_ofList_of_mem` (binder 12): lawful Nat: l = [(0,0), (0,1)] has a duplicate key; the later value 1 wins, so getD 0 = 1 ≠ 0
theorem w4c1_157 : ¬ drop0% Std.HashMap.Raw.getD_ofList_of_mem 12 :=
  fun h => by
  have := h (l := [((0 : Nat), (0 : Nat)), ((0 : Nat), (1 : Nat))]) (k := (0 : Nat)) (k' := (0 : Nat)) (k_beq := (by decide)) (v := (0 : Nat)) (fallback := (0 : Nat)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.HashMap.getD_ofList_of_mem` (binder 12): lawful Nat: l = [(0,0), (0,1)] has a duplicate key; the later value 1 wins, so getD 0 = 1 ≠ 0
theorem w4c1_158 : ¬ drop0% Std.HashMap.getD_ofList_of_mem 12 :=
  fun h => by
  have := (@h Nat Nat inferInstance inferInstance) (l := [((0 : Nat), (0 : Nat)), ((0 : Nat), (1 : Nat))]) (k := (0 : Nat)) (k' := (0 : Nat)) (k_beq := (by decide)) (v := (0 : Nat)) (fallback := (0 : Nat)) (mem := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.DHashMap.Raw.getD_ofList_of_mem` (binder 12): lawful Nat: l = [(0,0)], k = k' = 0, v = 1: the lookup gives 0
theorem w4c1_159 : ¬ drop0% Std.DHashMap.Raw.getD_ofList_of_mem 12 :=
  fun h => by
  have := h (β := (fun _ => Nat)) (l := [⟨(0 : Nat), (0 : Nat)⟩]) (k := (0 : Nat)) (k' := (0 : Nat)) (k_beq := (by decide)) (v := (1 : Nat)) (fallback := (0 : Nat)) (distinct := (by first | decide | simp))
  revert this; first | (simp; done) | (w4_ev; done) | (hm_eval_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList]; hm_eval_raw; done) | (hm_eval2; done) | (w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.ofList, dr_empty]; w1c0_raw; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c0_drc_insertMany_lit]; simp only [Raw₀.Const.insertMany]; hm_eval; decide) | (hm_eval_raw; simp (disch := first | decide | simp) only [DHashMap.Raw.getD, W4c1A.dgetD_eval]; simp (config := {decide := true}) [ix, scr_small, f16, Std.Internal.List.getValueCastD, AssocList.getCastD]; done) | (simp only [DHashMap.Raw.Const.ofList, dr_empty]; simp (disch := first | decide | simp [nil16]) only [w1c2dhrcIm]; simp only [Raw₀.Const.insertListₘ]; w4_ev; done)

-- `Std.DHashMap.Equiv.isEmpty_eq` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_160 : ¬ drop0% Std.DHashMap.Equiv.isEmpty_eq 6 :=
  fun h => by
  have := h (m₁ := (hm NS.broken 1 #[.nil, .nil] (by decide) : HashMap NS Nat).inner) (m₂ := (hm NS.broken 0 #[.nil, .nil] (by decide) : HashMap NS Nat).inner) (h := ⟨⟨by first | rfl | simp [toListModel]⟩⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.DHashMap.Raw.Equiv.isEmpty_eq` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_161 : ¬ drop0% Std.DHashMap.Raw.Equiv.isEmpty_eq 6 :=
  fun h => by
  have := h (m₁ := (⟨1, #[.nil, .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (m₂ := (⟨0, #[.nil, .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (h₁ := (wf_vac NS.broken _ (by decide))) (h₂ := (wf_vac NS.broken _ (by decide))) (h := ⟨by first | rfl | simp [toListModel]⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashMap.Equiv.isEmpty_eq` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_162 : ¬ drop0% Std.HashMap.Equiv.isEmpty_eq 6 :=
  fun h => by
  have := h (m₁ := (hm NS.broken 1 #[.nil, .nil] (by decide) : HashMap NS Nat)) (m₂ := (hm NS.broken 0 #[.nil, .nil] (by decide) : HashMap NS Nat)) (h := ⟨⟨⟨by first | rfl | simp [toListModel]⟩⟩⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashMap.Raw.Equiv.isEmpty_eq` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_163 : ¬ drop0% Std.HashMap.Raw.Equiv.isEmpty_eq 6 :=
  fun h => by
  have := h (m₁ := (hmr 1 #[.nil, .nil] : HashMap.Raw NS Nat)) (m₂ := (hmr 0 #[.nil, .nil] : HashMap.Raw NS Nat)) (h₁ := (hmr_wf NS.broken _ _ (by decide))) (h₂ := (hmr_wf NS.broken _ _ (by decide))) (h := ⟨⟨by first | rfl | simp [toListModel]⟩⟩)
  exact absurd this (by (try simp only [hmr_empty]); decide +kernel)

-- `Std.HashSet.Equiv.isEmpty_eq` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_164 : ¬ drop0% Std.HashSet.Equiv.isEmpty_eq 5 :=
  fun h => by
  have := h (m₁ := (hs NS.broken 1 #[.nil, .nil] (by decide) : HashSet NS)) (m₂ := (hs NS.broken 0 #[.nil, .nil] (by decide) : HashSet NS)) (h := ⟨⟨⟨⟨by first | rfl | simp [toListModel]⟩⟩⟩⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashSet.Raw.Equiv.isEmpty_eq` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_165 : ¬ drop0% Std.HashSet.Raw.Equiv.isEmpty_eq 5 :=
  fun h => by
  have := h (m₁ := (hsr 1 #[.nil, .nil] : HashSet.Raw NS)) (m₂ := (hsr 0 #[.nil, .nil] : HashSet.Raw NS)) (h₁ := (hsr_wf NS.broken _ _ (by decide))) (h₂ := (hsr_wf NS.broken _ _ (by decide))) (h := ⟨⟨⟨by first | rfl | simp [toListModel]⟩⟩⟩)
  exact absurd this (by (try simp only [hsr_empty]); decide +kernel)

-- `Std.DHashMap.Equiv.isEmpty_eq` (binder 7): AB (== always true, hash n; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_166 : ¬ drop0% Std.DHashMap.Equiv.isEmpty_eq 7 :=
  fun h => by
  have := h (m₁ := (hm AB.broken 1 #[.nil, .nil] (by decide) : HashMap AB Nat).inner) (m₂ := (hm AB.broken 0 #[.nil, .nil] (by decide) : HashMap AB Nat).inner) (h := ⟨⟨by first | rfl | simp [toListModel]⟩⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.DHashMap.Raw.Equiv.isEmpty_eq` (binder 7): AB (== always true, hash n; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_167 : ¬ drop0% Std.DHashMap.Raw.Equiv.isEmpty_eq 7 :=
  fun h => by
  have := h (m₁ := (⟨1, #[.nil, .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (m₂ := (⟨0, #[.nil, .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (h₁ := (wf_vac AB.broken _ (by decide))) (h₂ := (wf_vac AB.broken _ (by decide))) (h := ⟨by first | rfl | simp [toListModel]⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashMap.Equiv.isEmpty_eq` (binder 7): AB (== always true, hash n; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_168 : ¬ drop0% Std.HashMap.Equiv.isEmpty_eq 7 :=
  fun h => by
  have := h (m₁ := (hm AB.broken 1 #[.nil, .nil] (by decide) : HashMap AB Nat)) (m₂ := (hm AB.broken 0 #[.nil, .nil] (by decide) : HashMap AB Nat)) (h := ⟨⟨⟨by first | rfl | simp [toListModel]⟩⟩⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashMap.Raw.Equiv.isEmpty_eq` (binder 7): AB (== always true, hash n; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_169 : ¬ drop0% Std.HashMap.Raw.Equiv.isEmpty_eq 7 :=
  fun h => by
  have := h (m₁ := (hmr 1 #[.nil, .nil] : HashMap.Raw AB Nat)) (m₂ := (hmr 0 #[.nil, .nil] : HashMap.Raw AB Nat)) (h₁ := (hmr_wf AB.broken _ _ (by decide))) (h₂ := (hmr_wf AB.broken _ _ (by decide))) (h := ⟨⟨by first | rfl | simp [toListModel]⟩⟩)
  exact absurd this (by (try simp only [hmr_empty]); decide +kernel)

-- `Std.HashSet.Equiv.isEmpty_eq` (binder 6): AB (== always true, hash n; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_170 : ¬ drop0% Std.HashSet.Equiv.isEmpty_eq 6 :=
  fun h => by
  have := h (m₁ := (hs AB.broken 1 #[.nil, .nil] (by decide) : HashSet AB)) (m₂ := (hs AB.broken 0 #[.nil, .nil] (by decide) : HashSet AB)) (h := ⟨⟨⟨⟨by first | rfl | simp [toListModel]⟩⟩⟩⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashSet.Raw.Equiv.isEmpty_eq` (binder 6): AB (== always true, hash n; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_171 : ¬ drop0% Std.HashSet.Raw.Equiv.isEmpty_eq 6 :=
  fun h => by
  have := h (m₁ := (hsr 1 #[.nil, .nil] : HashSet.Raw AB)) (m₂ := (hsr 0 #[.nil, .nil] : HashSet.Raw AB)) (h₁ := (hsr_wf AB.broken _ _ (by decide))) (h₂ := (hsr_wf AB.broken _ _ (by decide))) (h := ⟨⟨⟨by first | rfl | simp [toListModel]⟩⟩⟩)
  exact absurd this (by (try simp only [hsr_empty]); decide +kernel)

-- `Std.DHashMap.Equiv.isEmpty_eq` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅ (not equivalent): sizes / emptiness differ
theorem w4c1_172 : ¬ drop0% Std.DHashMap.Equiv.isEmpty_eq 8 :=
  fun h => by
  have := h (m₁ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap Nat (fun _ => Nat)))
  simp [DHashMap.mem_insert, DHashMap.contains_insert, DHashMap.size_insert, DHashMap.mem_diff_iff, DHashMap.mem_inter_iff, DHashMap.mem_union_iff, DHashMap.isEmpty_insert] at this

-- `Std.DHashMap.Raw.Equiv.isEmpty_eq` (binder 10): lawful Nat, m₁ = {0}, m₂ = ∅ (not equivalent): sizes / emptiness differ
theorem w4c1_173 : ¬ drop0% Std.DHashMap.Raw.Equiv.isEmpty_eq 10 :=
  fun h => by
  have w0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).WF := .empty
  have w1 : ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := w1) (h₂ := w0)
  simp [DHashMap.Raw.mem_insert, DHashMap.Raw.contains_insert, DHashMap.Raw.size_insert, DHashMap.Raw.mem_diff_iff, DHashMap.Raw.mem_inter_iff, DHashMap.Raw.mem_union_iff, DHashMap.Raw.isEmpty_insert, w0, w1] at this

-- `Std.HashMap.Equiv.isEmpty_eq` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅ (not equivalent): sizes / emptiness differ
theorem w4c1_174 : ¬ drop0% Std.HashMap.Equiv.isEmpty_eq 8 :=
  fun h => by
  have := h (m₁ := ((∅ : HashMap Nat Nat).insert 0 0)) (m₂ := (∅ : HashMap Nat Nat))
  simp [HashMap.mem_insert, HashMap.contains_insert, HashMap.size_insert, HashMap.mem_diff_iff, HashMap.mem_inter_iff, HashMap.mem_union_iff, HashMap.isEmpty_insert] at this

-- `Std.HashMap.Raw.Equiv.isEmpty_eq` (binder 10): lawful Nat, m₁ = {0}, m₂ = ∅ (not equivalent): sizes / emptiness differ
theorem w4c1_175 : ¬ drop0% Std.HashMap.Raw.Equiv.isEmpty_eq 10 :=
  fun h => by
  have w0 : (∅ : HashMap.Raw Nat Nat).WF := .empty
  have w1 : ((∅ : HashMap.Raw Nat Nat).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : HashMap.Raw Nat Nat).insert 0 0)) (m₂ := (∅ : HashMap.Raw Nat Nat)) (h₁ := w1) (h₂ := w0)
  simp [HashMap.Raw.mem_insert, HashMap.Raw.contains_insert, HashMap.Raw.size_insert, HashMap.Raw.mem_diff_iff, HashMap.Raw.mem_inter_iff, HashMap.Raw.mem_union_iff, HashMap.Raw.isEmpty_insert, w0, w1] at this

-- `Std.HashSet.Equiv.isEmpty_eq` (binder 7): lawful Nat, m₁ = {0}, m₂ = ∅ (not equivalent): sizes / emptiness differ
theorem w4c1_176 : ¬ drop0% Std.HashSet.Equiv.isEmpty_eq 7 :=
  fun h => by
  have := h (m₁ := ((∅ : HashSet Nat).insert 0)) (m₂ := (∅ : HashSet Nat))
  simp [HashSet.mem_insert, HashSet.contains_insert, HashSet.size_insert, HashSet.mem_diff_iff, HashSet.mem_inter_iff, HashSet.mem_union_iff, HashSet.isEmpty_insert] at this

-- `Std.HashSet.Raw.Equiv.isEmpty_eq` (binder 9): lawful Nat, m₁ = {0}, m₂ = ∅ (not equivalent): sizes / emptiness differ
theorem w4c1_177 : ¬ drop0% Std.HashSet.Raw.Equiv.isEmpty_eq 9 :=
  fun h => by
  have w0 : (∅ : HashSet.Raw Nat).WF := .empty
  have w1 : ((∅ : HashSet.Raw Nat).insert 0).WF := .insert .empty
  have := h (m₁ := ((∅ : HashSet.Raw Nat).insert 0)) (m₂ := (∅ : HashSet.Raw Nat)) (h₁ := w1) (h₂ := w0)
  simp [HashSet.Raw.mem_insert, HashSet.Raw.contains_insert, HashSet.Raw.size_insert, HashSet.Raw.mem_diff_iff, HashSet.Raw.mem_inter_iff, HashSet.Raw.mem_union_iff, HashSet.Raw.isEmpty_insert, w0, w1] at this

-- `Std.DHashMap.Raw.Equiv.isEmpty_eq` (binder 8): lawful Nat: m₁ has 16 empty buckets and size field 1 (not WF), the other is ∅: equivalent, sizes differ
theorem w4c1_178 : ¬ drop0% Std.DHashMap.Raw.Equiv.isEmpty_eq 8 :=
  fun h => by
  have := h (m₁ := (⟨1, nil16⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (h₂ := .empty) (h := ⟨by first | (simp [dr_empty, toListModel, nil16]; done) | (simp only [dr_empty]; rfl) | (rw [dr_empty]; decide)⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.DHashMap.Raw.Equiv.isEmpty_eq` (binder 9): lawful Nat: m₂ has 16 empty buckets and size field 1 (not WF), the other is ∅: equivalent, sizes differ
theorem w4c1_179 : ¬ drop0% Std.DHashMap.Raw.Equiv.isEmpty_eq 9 :=
  fun h => by
  have := h (m₁ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (⟨1, nil16⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := .empty) (h := ⟨by first | (simp [dr_empty, toListModel, nil16]; done) | (simp only [dr_empty]; rfl) | (rw [dr_empty]; decide)⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashMap.Raw.Equiv.isEmpty_eq` (binder 8): lawful Nat: m₁ has 16 empty buckets and size field 1 (not WF), the other is ∅: equivalent, sizes differ
theorem w4c1_180 : ¬ drop0% Std.HashMap.Raw.Equiv.isEmpty_eq 8 :=
  fun h => by
  have := h (m₁ := (hmr 1 nil16 : HashMap.Raw Nat Nat)) (m₂ := (∅ : HashMap.Raw Nat Nat)) (h₂ := .empty) (h := ⟨⟨by first | (simp [hmr_empty, toListModel, nil16]; done) | (simp only [hmr_empty]; rfl) | (rw [hmr_empty]; decide)⟩⟩)
  exact absurd this (by (try simp only [hmr_empty]); decide +kernel)

-- `Std.HashMap.Raw.Equiv.isEmpty_eq` (binder 9): lawful Nat: m₂ has 16 empty buckets and size field 1 (not WF), the other is ∅: equivalent, sizes differ
theorem w4c1_181 : ¬ drop0% Std.HashMap.Raw.Equiv.isEmpty_eq 9 :=
  fun h => by
  have := h (m₁ := (∅ : HashMap.Raw Nat Nat)) (m₂ := (hmr 1 nil16 : HashMap.Raw Nat Nat)) (h₁ := .empty) (h := ⟨⟨by first | (simp [hmr_empty, toListModel, nil16]; done) | (simp only [hmr_empty]; rfl) | (rw [hmr_empty]; decide)⟩⟩)
  exact absurd this (by (try simp only [hmr_empty]); decide +kernel)

-- `Std.HashSet.Raw.Equiv.isEmpty_eq` (binder 8): lawful Nat: m₂ has 16 empty buckets and size field 1 (not WF), the other is ∅: equivalent, sizes differ
theorem w4c1_182 : ¬ drop0% Std.HashSet.Raw.Equiv.isEmpty_eq 8 :=
  fun h => by
  have := h (m₁ := (∅ : HashSet.Raw Nat)) (m₂ := (hsr 1 nil16 : HashSet.Raw Nat)) (h₁ := .empty) (h := ⟨⟨⟨by first | (simp [hsr_empty, toListModel, nil16]; done) | (simp only [hsr_empty]; rfl) | (rw [hsr_empty]; decide)⟩⟩⟩)
  exact absurd this (by (try simp only [hsr_empty]); decide +kernel)

-- `Std.DHashMap.Const.length_toList` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_183 : ¬ drop0% Std.DHashMap.Const.length_toList 5 :=
  fun h => by
  have := h (m := (hm NS.broken 0 #[b1 (NS.mk 0) (0 : Nat), .nil] (by decide) : HashMap NS Nat).inner)
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.length_toList` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_184 : ¬ drop0% Std.DHashMap.Internal.Raw₀.length_toList 5 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (NS.mk 0) (0 : Nat), .nil]⟩, by decide⟩ : Raw₀ NS (fun _ => Nat))) (h := (wf_vac NS.broken _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.Const.length_toList` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_185 : ¬ drop0% Std.DHashMap.Raw.Const.length_toList 5 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (NS.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (h := (wf_vac NS.broken _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.length_toList` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_186 : ¬ drop0% Std.DHashMap.Raw.length_toList 5 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (NS.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (h := (wf_vac NS.broken _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.length_toList` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_187 : ¬ drop0% Std.DHashMap.length_toList 5 :=
  fun h => by
  have := h (m := (hm NS.broken 0 #[b1 (NS.mk 0) (0 : Nat), .nil] (by decide) : HashMap NS Nat).inner)
  exact absurd this (by decide +kernel)

-- `Std.HashMap.Raw.length_toList` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_188 : ¬ drop0% Std.HashMap.Raw.length_toList 5 :=
  fun h => by
  have := h (m := (hmr 0 #[b1 (NS.mk 0) (0 : Nat), .nil] : HashMap.Raw NS Nat)) (h := (hmr_wf NS.broken _ _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.HashMap.length_toList` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_189 : ¬ drop0% Std.HashMap.length_toList 5 :=
  fun h => by
  have := h (m := (hm NS.broken 0 #[b1 (NS.mk 0) (0 : Nat), .nil] (by decide) : HashMap NS Nat))
  exact absurd this (by decide +kernel)

-- `Std.HashSet.Raw.length_toList` (binder 4): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_190 : ¬ drop0% Std.HashSet.Raw.length_toList 4 :=
  fun h => by
  have := h (m := (hsr 0 #[b1 (NS.mk 0) (), .nil] : HashSet.Raw NS)) (h := (hsr_wf NS.broken _ _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.HashSet.length_toList` (binder 4): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_191 : ¬ drop0% Std.HashSet.length_toList 4 :=
  fun h => by
  have := h (m := (hs NS.broken 0 #[b1 (NS.mk 0) (), .nil] (by decide) : HashSet NS))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Const.length_toList` (binder 6): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_192 : ¬ drop0% Std.DHashMap.Const.length_toList 6 :=
  fun h => by
  have := h (m := (hm AB.broken 0 #[b1 (AB.mk 0) (0 : Nat), .nil] (by decide) : HashMap AB Nat).inner)
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.Const.length_toList` (binder 6): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_193 : ¬ drop0% Std.DHashMap.Raw.Const.length_toList 6 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (AB.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (h := (wf_vac AB.broken _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.length_toList` (binder 6): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_194 : ¬ drop0% Std.DHashMap.Raw.length_toList 6 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (AB.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (h := (wf_vac AB.broken _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.length_toList` (binder 6): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_195 : ¬ drop0% Std.DHashMap.length_toList 6 :=
  fun h => by
  have := h (m := (hm AB.broken 0 #[b1 (AB.mk 0) (0 : Nat), .nil] (by decide) : HashMap AB Nat).inner)
  exact absurd this (by decide +kernel)

-- `Std.HashMap.Raw.length_toList` (binder 6): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_196 : ¬ drop0% Std.HashMap.Raw.length_toList 6 :=
  fun h => by
  have := h (m := (hmr 0 #[b1 (AB.mk 0) (0 : Nat), .nil] : HashMap.Raw AB Nat)) (h := (hmr_wf AB.broken _ _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.HashMap.length_toList` (binder 6): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_197 : ¬ drop0% Std.HashMap.length_toList 6 :=
  fun h => by
  have := h (m := (hm AB.broken 0 #[b1 (AB.mk 0) (0 : Nat), .nil] (by decide) : HashMap AB Nat))
  exact absurd this (by decide +kernel)

-- `Std.HashSet.Raw.length_toList` (binder 5): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_198 : ¬ drop0% Std.HashSet.Raw.length_toList 5 :=
  fun h => by
  have := h (m := (hsr 0 #[b1 (AB.mk 0) (), .nil] : HashSet.Raw AB)) (h := (hsr_wf AB.broken _ _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.HashSet.length_toList` (binder 5): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_199 : ¬ drop0% Std.HashSet.length_toList 5 :=
  fun h => by
  have := h (m := (hs AB.broken 0 #[b1 (AB.mk 0) (), .nil] (by decide) : HashSet AB))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.Const.length_toList` (binder 7): lawful Nat, not WF: m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_200 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.length_toList 7 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (0 : Nat) (0 : Nat), .nil]⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.length_toList` (binder 7): lawful Nat, not WF: m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_201 : ¬ drop0% Std.DHashMap.Internal.Raw₀.length_toList 7 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (0 : Nat) (0 : Nat), .nil]⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.Const.length_toList` (binder 7): lawful Nat, not WF: m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_202 : ¬ drop0% Std.DHashMap.Raw.Const.length_toList 7 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (0 : Nat) (0 : Nat), .nil]⟩ : DHashMap.Raw Nat (fun _ => Nat)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.length_toList` (binder 7): lawful Nat, not WF: m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_203 : ¬ drop0% Std.DHashMap.Raw.length_toList 7 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (0 : Nat) (0 : Nat), .nil]⟩ : DHashMap.Raw Nat (fun _ => Nat)))
  exact absurd this (by decide +kernel)

-- `Std.HashMap.Raw.length_toList` (binder 7): lawful Nat, not WF: m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_204 : ¬ drop0% Std.HashMap.Raw.length_toList 7 :=
  fun h => by
  have := h (m := (hmr 0 #[b1 (0 : Nat) (0 : Nat), .nil] : HashMap.Raw Nat Nat))
  exact absurd this (by decide +kernel)

-- `Std.HashSet.Raw.length_toList` (binder 6): lawful Nat, not WF: m has one entry in bucket 0 and size field 0; toList has length 1 ≠ 0
theorem w4c1_205 : ¬ drop0% Std.HashSet.Raw.length_toList 6 :=
  fun h => by
  have := h (m := (hsr 0 #[b1 (0 : Nat) (), .nil] : HashSet.Raw Nat))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.mem_of_mem_filter` (binder 5): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_206 : drop% Std.DHashMap.Raw.mem_of_mem_filter 5 :=
  by intros; apply W4c1.dr_mf <;> assumption

-- `Std.DHashMap.mem_of_mem_filter` (binder 5): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_207 : drop% Std.DHashMap.mem_of_mem_filter 5 :=
  by intros; apply W4c1.dh_mf <;> assumption

-- `Std.HashMap.Raw.mem_of_mem_filter` (binder 5): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_208 : drop% Std.HashMap.Raw.mem_of_mem_filter 5 :=
  by intros; apply W4c1.hmr_mf <;> assumption

-- `Std.HashMap.mem_of_mem_filter` (binder 5): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_209 : drop% Std.HashMap.mem_of_mem_filter 5 :=
  by intros; apply W4c1.hm_mf <;> assumption

-- `Std.HashSet.Raw.mem_of_mem_filter` (binder 4): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_210 : drop% Std.HashSet.Raw.mem_of_mem_filter 4 :=
  by intros; apply W4c1.hsr_mf <;> assumption

-- `Std.HashSet.mem_of_mem_filter` (binder 4): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_211 : drop% Std.HashSet.mem_of_mem_filter 4 :=
  by intros; apply W4c1.hs_mf <;> assumption

-- `Std.DHashMap.Raw.mem_of_mem_filter` (binder 10): lawful Nat, m = ∅, k = 0: 0 ∉ ∅
theorem w4c1_212 : ¬ drop0% Std.DHashMap.Raw.mem_of_mem_filter 10 :=
  fun h => by
  have w0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).WF := .empty
  have w1 : ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0).WF := .insert .empty
  have := h (m := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (f := (fun _ _ => true)) (k := 0) (h := w0)
  simp [DHashMap.Raw.mem_insert, DHashMap.Raw.contains_insert, DHashMap.Raw.size_insert, DHashMap.Raw.mem_diff_iff, DHashMap.Raw.mem_inter_iff, DHashMap.Raw.mem_union_iff, DHashMap.Raw.isEmpty_insert, w0, w1] at this

-- `Std.DHashMap.mem_of_mem_filter` (binder 9): lawful Nat, m = ∅, k = 0: 0 ∉ ∅
theorem w4c1_213 : ¬ drop0% Std.DHashMap.mem_of_mem_filter 9 :=
  fun h => by
  have := h (m := (∅ : DHashMap Nat (fun _ => Nat))) (f := (fun _ _ => true)) (k := 0)
  simp [DHashMap.mem_insert, DHashMap.contains_insert, DHashMap.size_insert, DHashMap.mem_diff_iff, DHashMap.mem_inter_iff, DHashMap.mem_union_iff, DHashMap.isEmpty_insert] at this

-- `Std.ExtDHashMap.mem_of_mem_filter` (binder 9): lawful Nat, m = ∅, k = 0: 0 ∉ ∅
theorem w4c1_214 : ¬ drop0% Std.ExtDHashMap.mem_of_mem_filter 9 :=
  fun h => by
  have := h (m := (∅ : ExtDHashMap Nat (fun _ => Nat))) (f := (fun _ _ => true)) (k := 0)
  simp [ExtDHashMap.mem_insert, ExtDHashMap.contains_insert, ExtDHashMap.size_insert, ExtDHashMap.mem_diff_iff, ExtDHashMap.mem_inter_iff, ExtDHashMap.mem_union_iff] at this

-- `Std.ExtHashMap.mem_of_mem_filter` (binder 9): lawful Nat, m = ∅, k = 0: 0 ∉ ∅
theorem w4c1_215 : ¬ drop0% Std.ExtHashMap.mem_of_mem_filter 9 :=
  fun h => by
  have := h (m := (∅ : ExtHashMap Nat Nat)) (f := (fun _ _ => true)) (k := 0)
  simp [ExtHashMap.mem_insert, ExtHashMap.contains_insert, ExtHashMap.size_insert, ExtHashMap.mem_diff_iff, ExtHashMap.mem_inter_iff, ExtHashMap.mem_union_iff] at this

-- `Std.ExtHashSet.mem_of_mem_filter` (binder 8): lawful Nat, m = ∅, k = 0: 0 ∉ ∅
theorem w4c1_216 : ¬ drop0% Std.ExtHashSet.mem_of_mem_filter 8 :=
  fun h => by
  have := h (m := (∅ : ExtHashSet Nat)) (f := (fun _ => true)) (k := 0)
  simp [ExtHashSet.mem_insert, ExtHashSet.contains_insert, ExtHashSet.size_insert, ExtHashSet.mem_diff_iff, ExtHashSet.mem_inter_iff, ExtHashSet.mem_union_iff] at this

-- `Std.HashMap.Raw.mem_of_mem_filter` (binder 10): lawful Nat, m = ∅, k = 0: 0 ∉ ∅
theorem w4c1_217 : ¬ drop0% Std.HashMap.Raw.mem_of_mem_filter 10 :=
  fun h => by
  have w0 : (∅ : HashMap.Raw Nat Nat).WF := .empty
  have w1 : ((∅ : HashMap.Raw Nat Nat).insert 0 0).WF := .insert .empty
  have := h (m := (∅ : HashMap.Raw Nat Nat)) (f := (fun _ _ => true)) (k := 0) (h := w0)
  simp [HashMap.Raw.mem_insert, HashMap.Raw.contains_insert, HashMap.Raw.size_insert, HashMap.Raw.mem_diff_iff, HashMap.Raw.mem_inter_iff, HashMap.Raw.mem_union_iff, HashMap.Raw.isEmpty_insert, w0, w1] at this

-- `Std.HashMap.mem_of_mem_filter` (binder 9): lawful Nat, m = ∅, k = 0: 0 ∉ ∅
theorem w4c1_218 : ¬ drop0% Std.HashMap.mem_of_mem_filter 9 :=
  fun h => by
  have := h (m := (∅ : HashMap Nat Nat)) (f := (fun _ _ => true)) (k := 0)
  simp [HashMap.mem_insert, HashMap.contains_insert, HashMap.size_insert, HashMap.mem_diff_iff, HashMap.mem_inter_iff, HashMap.mem_union_iff, HashMap.isEmpty_insert] at this

-- `Std.HashSet.Raw.mem_of_mem_filter` (binder 9): lawful Nat, m = ∅, k = 0: 0 ∉ ∅
theorem w4c1_219 : ¬ drop0% Std.HashSet.Raw.mem_of_mem_filter 9 :=
  fun h => by
  have w0 : (∅ : HashSet.Raw Nat).WF := .empty
  have w1 : ((∅ : HashSet.Raw Nat).insert 0).WF := .insert .empty
  have := h (m := (∅ : HashSet.Raw Nat)) (f := (fun _ => true)) (k := 0) (h := w0)
  simp [HashSet.Raw.mem_insert, HashSet.Raw.contains_insert, HashSet.Raw.size_insert, HashSet.Raw.mem_diff_iff, HashSet.Raw.mem_inter_iff, HashSet.Raw.mem_union_iff, HashSet.Raw.isEmpty_insert, w0, w1] at this

-- `Std.DHashMap.Raw.mem_of_mem_filter` (binder 6): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_220 : drop% Std.DHashMap.Raw.mem_of_mem_filter 6 :=
  by intros; apply W4c1.dr_mf <;> assumption

-- `Std.DHashMap.mem_of_mem_filter` (binder 6): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_221 : drop% Std.DHashMap.mem_of_mem_filter 6 :=
  by intros; apply W4c1.dh_mf <;> assumption

-- `Std.HashMap.Raw.mem_of_mem_filter` (binder 6): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_222 : drop% Std.HashMap.Raw.mem_of_mem_filter 6 :=
  by intros; apply W4c1.hmr_mf <;> assumption

-- `Std.HashMap.mem_of_mem_filter` (binder 6): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_223 : drop% Std.HashMap.mem_of_mem_filter 6 :=
  by intros; apply W4c1.hm_mf <;> assumption

-- `Std.HashSet.Raw.mem_of_mem_filter` (binder 5): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_224 : drop% Std.HashSet.Raw.mem_of_mem_filter 5 :=
  by intros; apply W4c1.hsr_mf <;> assumption

-- `Std.HashSet.mem_of_mem_filter` (binder 5): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_225 : drop% Std.HashSet.mem_of_mem_filter 5 :=
  by intros; apply W4c1.hs_mf <;> assumption

-- `Std.DHashMap.Raw.mem_of_mem_filter` (binder 9): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_226 : drop% Std.DHashMap.Raw.mem_of_mem_filter 9 :=
  by intros; apply W4c1.dr_mf <;> assumption

-- `Std.HashMap.Raw.mem_of_mem_filter` (binder 9): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_227 : drop% Std.HashMap.Raw.mem_of_mem_filter 9 :=
  by intros; apply W4c1.hmr_mf <;> assumption

-- `Std.HashSet.Raw.mem_of_mem_filter` (binder 8): removable: filter keeps a sub-bucket of each bucket (and is ∅ without buckets), so membership in the filter implies membership (no instance or WF needed)
theorem w4c1_228 : drop% Std.HashSet.Raw.mem_of_mem_filter 8 :=
  by intros; apply W4c1.hsr_mf <;> assumption

-- `Std.DHashMap.Raw.not_mem_diff_of_mem_right` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁ = {0}, m₂ = {1}, k = 1 ∈ m₂; diff filters m₁ by m₂.contains (1 ≤ 0 is false), so 0 stays and 0 ≤ 1 finds it
theorem w4c1_229 : ¬ drop0% Std.DHashMap.Raw.not_mem_diff_of_mem_right 6 :=
  fun h => by
  have := h (m₁ := (⟨1, #[b1 (NS.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (m₂ := (⟨1, #[b1 (NS.mk 1) (0 : Nat), .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (h₁ := (wf_vac NS.broken _ (by decide))) (h₂ := (wf_vac NS.broken _ (by decide))) (k := (NS.mk 1)) (mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_diff, W4c1A.u_hs_diff, HashSet.diff, DHashMap.diff] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.not_mem_diff_of_mem_right` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁ = {0}, m₂ = {1}, k = 1 ∈ m₂; diff filters m₁ by m₂.contains (1 ≤ 0 is false), so 0 stays and 0 ≤ 1 finds it
theorem w4c1_230 : ¬ drop0% Std.DHashMap.not_mem_diff_of_mem_right 6 :=
  fun h => by
  have := h (m₁ := (hm NS.broken 1 #[b1 (NS.mk 0) (0 : Nat), .nil] (by decide) : HashMap NS Nat).inner) (m₂ := (hm NS.broken 1 #[b1 (NS.mk 1) (0 : Nat), .nil] (by decide) : HashMap NS Nat).inner) (k := (NS.mk 1)) (mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_diff, W4c1A.u_hs_diff, HashSet.diff, DHashMap.diff] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashMap.Raw.not_mem_diff_of_mem_right` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁ = {0}, m₂ = {1}, k = 1 ∈ m₂; diff filters m₁ by m₂.contains (1 ≤ 0 is false), so 0 stays and 0 ≤ 1 finds it
theorem w4c1_231 : ¬ drop0% Std.HashMap.Raw.not_mem_diff_of_mem_right 6 :=
  fun h => by
  have := h (m₁ := (hmr 1 #[b1 (NS.mk 0) (0 : Nat), .nil] : HashMap.Raw NS Nat)) (m₂ := (hmr 1 #[b1 (NS.mk 1) (0 : Nat), .nil] : HashMap.Raw NS Nat)) (h₁ := (hmr_wf NS.broken _ _ (by decide))) (h₂ := (hmr_wf NS.broken _ _ (by decide))) (k := (NS.mk 1)) (mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_diff, W4c1A.u_hs_diff, HashSet.diff, DHashMap.diff] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashMap.not_mem_diff_of_mem_right` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁ = {0}, m₂ = {1}, k = 1 ∈ m₂; diff filters m₁ by m₂.contains (1 ≤ 0 is false), so 0 stays and 0 ≤ 1 finds it
theorem w4c1_232 : ¬ drop0% Std.HashMap.not_mem_diff_of_mem_right 6 :=
  fun h => by
  have := h (m₁ := (hm NS.broken 1 #[b1 (NS.mk 0) (0 : Nat), .nil] (by decide) : HashMap NS Nat)) (m₂ := (hm NS.broken 1 #[b1 (NS.mk 1) (0 : Nat), .nil] (by decide) : HashMap NS Nat)) (k := (NS.mk 1)) (mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_diff, W4c1A.u_hs_diff, HashSet.diff, DHashMap.diff] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.Raw.not_mem_diff_of_mem_right` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁ = {0}, m₂ = {1}, k = 1 ∈ m₂; diff filters m₁ by m₂.contains (1 ≤ 0 is false), so 0 stays and 0 ≤ 1 finds it
theorem w4c1_233 : ¬ drop0% Std.HashSet.Raw.not_mem_diff_of_mem_right 5 :=
  fun h => by
  have := h (m₁ := (hsr 1 #[b1 (NS.mk 0) (), .nil] : HashSet.Raw NS)) (m₂ := (hsr 1 #[b1 (NS.mk 1) (), .nil] : HashSet.Raw NS)) (h₁ := (hsr_wf NS.broken _ _ (by decide))) (h₂ := (hsr_wf NS.broken _ _ (by decide))) (k := (NS.mk 1)) (mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_diff, W4c1A.u_hs_diff, HashSet.diff, DHashMap.diff] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.not_mem_diff_of_mem_right` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁ = {0}, m₂ = {1}, k = 1 ∈ m₂; diff filters m₁ by m₂.contains (1 ≤ 0 is false), so 0 stays and 0 ≤ 1 finds it
theorem w4c1_234 : ¬ drop0% Std.HashSet.not_mem_diff_of_mem_right 5 :=
  fun h => by
  have := h (m₁ := (hs NS.broken 1 #[b1 (NS.mk 0) (), .nil] (by decide) : HashSet NS)) (m₂ := (hs NS.broken 1 #[b1 (NS.mk 1) (), .nil] (by decide) : HashSet NS)) (k := (NS.mk 1)) (mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_diff, W4c1A.u_hs_diff, HashSet.diff, DHashMap.diff] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.not_mem_diff_of_mem_right` (binder 11): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: 0 ∈ m₁ \ m₂
theorem w4c1_235 : ¬ drop0% Std.DHashMap.Raw.not_mem_diff_of_mem_right 11 :=
  fun h => by
  have w0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).WF := .empty
  have w1 : ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := w1) (h₂ := w0) (k := 0)
  simp [DHashMap.Raw.mem_insert, DHashMap.Raw.contains_insert, DHashMap.Raw.size_insert, DHashMap.Raw.mem_diff_iff, DHashMap.Raw.mem_inter_iff, DHashMap.Raw.mem_union_iff, DHashMap.Raw.isEmpty_insert, w0, w1] at this

-- `Std.ExtDHashMap.not_mem_diff_of_mem_right` (binder 9): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: 0 ∈ m₁ \ m₂
theorem w4c1_236 : ¬ drop0% Std.ExtDHashMap.not_mem_diff_of_mem_right 9 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtDHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : ExtDHashMap Nat (fun _ => Nat))) (k := 0)
  simp [ExtDHashMap.mem_insert, ExtDHashMap.contains_insert, ExtDHashMap.size_insert, ExtDHashMap.mem_diff_iff, ExtDHashMap.mem_inter_iff, ExtDHashMap.mem_union_iff] at this

-- `Std.ExtHashMap.not_mem_diff_of_mem_right` (binder 9): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: 0 ∈ m₁ \ m₂
theorem w4c1_237 : ¬ drop0% Std.ExtHashMap.not_mem_diff_of_mem_right 9 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtHashMap Nat Nat).insert 0 0)) (m₂ := (∅ : ExtHashMap Nat Nat)) (k := 0)
  simp [ExtHashMap.mem_insert, ExtHashMap.contains_insert, ExtHashMap.size_insert, ExtHashMap.mem_diff_iff, ExtHashMap.mem_inter_iff, ExtHashMap.mem_union_iff] at this

-- `Std.ExtHashSet.not_mem_diff_of_mem_right` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: 0 ∈ m₁ \ m₂
theorem w4c1_238 : ¬ drop0% Std.ExtHashSet.not_mem_diff_of_mem_right 8 :=
  fun h => by
  have := h (m₁ := ((∅ : ExtHashSet Nat).insert 0)) (m₂ := (∅ : ExtHashSet Nat)) (k := 0)
  simp [ExtHashSet.mem_insert, ExtHashSet.contains_insert, ExtHashSet.size_insert, ExtHashSet.mem_diff_iff, ExtHashSet.mem_inter_iff, ExtHashSet.mem_union_iff] at this

-- `Std.HashMap.Raw.not_mem_diff_of_mem_right` (binder 11): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: 0 ∈ m₁ \ m₂
theorem w4c1_239 : ¬ drop0% Std.HashMap.Raw.not_mem_diff_of_mem_right 11 :=
  fun h => by
  have w0 : (∅ : HashMap.Raw Nat Nat).WF := .empty
  have w1 : ((∅ : HashMap.Raw Nat Nat).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : HashMap.Raw Nat Nat).insert 0 0)) (m₂ := (∅ : HashMap.Raw Nat Nat)) (h₁ := w1) (h₂ := w0) (k := 0)
  simp [HashMap.Raw.mem_insert, HashMap.Raw.contains_insert, HashMap.Raw.size_insert, HashMap.Raw.mem_diff_iff, HashMap.Raw.mem_inter_iff, HashMap.Raw.mem_union_iff, HashMap.Raw.isEmpty_insert, w0, w1] at this

-- `Std.HashSet.Raw.not_mem_diff_of_mem_right` (binder 10): lawful Nat, m₁ = {0}, m₂ = ∅, k = 0: 0 ∈ m₁ \ m₂
theorem w4c1_240 : ¬ drop0% Std.HashSet.Raw.not_mem_diff_of_mem_right 10 :=
  fun h => by
  have w0 : (∅ : HashSet.Raw Nat).WF := .empty
  have w1 : ((∅ : HashSet.Raw Nat).insert 0).WF := .insert .empty
  have := h (m₁ := ((∅ : HashSet.Raw Nat).insert 0)) (m₂ := (∅ : HashSet.Raw Nat)) (h₁ := w1) (h₂ := w0) (k := 0)
  simp [HashSet.Raw.mem_insert, HashSet.Raw.contains_insert, HashSet.Raw.size_insert, HashSet.Raw.mem_diff_iff, HashSet.Raw.mem_inter_iff, HashSet.Raw.mem_union_iff, HashSet.Raw.isEmpty_insert, w0, w1] at this

-- `Std.DHashMap.Raw.not_mem_diff_of_mem_right` (binder 7): AB (== always true, hash n; WF vacuous): m₁ has key 1 misplaced in bucket 0, m₂ = {0}, k = 0; m₂.contains 1 looks in the empty bucket 1, so the filter keeps 1 and k finds it in bucket 0
theorem w4c1_241 : ¬ drop0% Std.DHashMap.Raw.not_mem_diff_of_mem_right 7 :=
  fun h => by
  have := h (m₁ := (⟨1, #[b1 (AB.mk 1) (0 : Nat), .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (m₂ := (⟨1, #[b1 (AB.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (h₁ := (wf_vac AB.broken _ (by decide))) (h₂ := (wf_vac AB.broken _ (by decide))) (k := (AB.mk 0)) (mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_diff, W4c1A.u_hs_diff, HashSet.diff, DHashMap.diff] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.not_mem_diff_of_mem_right` (binder 7): AB (== always true, hash n; WF vacuous): m₁ has key 1 misplaced in bucket 0, m₂ = {0}, k = 0; m₂.contains 1 looks in the empty bucket 1, so the filter keeps 1 and k finds it in bucket 0
theorem w4c1_242 : ¬ drop0% Std.DHashMap.not_mem_diff_of_mem_right 7 :=
  fun h => by
  have := h (m₁ := (hm AB.broken 1 #[b1 (AB.mk 1) (0 : Nat), .nil] (by decide) : HashMap AB Nat).inner) (m₂ := (hm AB.broken 1 #[b1 (AB.mk 0) (0 : Nat), .nil] (by decide) : HashMap AB Nat).inner) (k := (AB.mk 0)) (mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_diff, W4c1A.u_hs_diff, HashSet.diff, DHashMap.diff] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashMap.Raw.not_mem_diff_of_mem_right` (binder 7): AB (== always true, hash n; WF vacuous): m₁ has key 1 misplaced in bucket 0, m₂ = {0}, k = 0; m₂.contains 1 looks in the empty bucket 1, so the filter keeps 1 and k finds it in bucket 0
theorem w4c1_243 : ¬ drop0% Std.HashMap.Raw.not_mem_diff_of_mem_right 7 :=
  fun h => by
  have := h (m₁ := (hmr 1 #[b1 (AB.mk 1) (0 : Nat), .nil] : HashMap.Raw AB Nat)) (m₂ := (hmr 1 #[b1 (AB.mk 0) (0 : Nat), .nil] : HashMap.Raw AB Nat)) (h₁ := (hmr_wf AB.broken _ _ (by decide))) (h₂ := (hmr_wf AB.broken _ _ (by decide))) (k := (AB.mk 0)) (mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_diff, W4c1A.u_hs_diff, HashSet.diff, DHashMap.diff] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashMap.not_mem_diff_of_mem_right` (binder 7): AB (== always true, hash n; WF vacuous): m₁ has key 1 misplaced in bucket 0, m₂ = {0}, k = 0; m₂.contains 1 looks in the empty bucket 1, so the filter keeps 1 and k finds it in bucket 0
theorem w4c1_244 : ¬ drop0% Std.HashMap.not_mem_diff_of_mem_right 7 :=
  fun h => by
  have := h (m₁ := (hm AB.broken 1 #[b1 (AB.mk 1) (0 : Nat), .nil] (by decide) : HashMap AB Nat)) (m₂ := (hm AB.broken 1 #[b1 (AB.mk 0) (0 : Nat), .nil] (by decide) : HashMap AB Nat)) (k := (AB.mk 0)) (mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_diff, W4c1A.u_hs_diff, HashSet.diff, DHashMap.diff] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.Raw.not_mem_diff_of_mem_right` (binder 6): AB (== always true, hash n; WF vacuous): m₁ has key 1 misplaced in bucket 0, m₂ = {0}, k = 0; m₂.contains 1 looks in the empty bucket 1, so the filter keeps 1 and k finds it in bucket 0
theorem w4c1_245 : ¬ drop0% Std.HashSet.Raw.not_mem_diff_of_mem_right 6 :=
  fun h => by
  have := h (m₁ := (hsr 1 #[b1 (AB.mk 1) (), .nil] : HashSet.Raw AB)) (m₂ := (hsr 1 #[b1 (AB.mk 0) (), .nil] : HashSet.Raw AB)) (h₁ := (hsr_wf AB.broken _ _ (by decide))) (h₂ := (hsr_wf AB.broken _ _ (by decide))) (k := (AB.mk 0)) (mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_diff, W4c1A.u_hs_diff, HashSet.diff, DHashMap.diff] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.HashSet.not_mem_diff_of_mem_right` (binder 6): AB (== always true, hash n; WF vacuous): m₁ has key 1 misplaced in bucket 0, m₂ = {0}, k = 0; m₂.contains 1 looks in the empty bucket 1, so the filter keeps 1 and k finds it in bucket 0
theorem w4c1_246 : ¬ drop0% Std.HashSet.not_mem_diff_of_mem_right 6 :=
  fun h => by
  have := h (m₁ := (hs AB.broken 1 #[b1 (AB.mk 1) (), .nil] (by decide) : HashSet AB)) (m₂ := (hs AB.broken 1 #[b1 (AB.mk 0) (), .nil] (by decide) : HashSet AB)) (k := (AB.mk 0)) (mem := (by w4_ev))
  (try simp only [W4c1A.u_dm_diff, W4c1A.u_hs_diff, HashSet.diff, DHashMap.diff] at this)
  revert this; (first | (w4_uev; done) | (w4_uev; w4_ev) | (hm_eval3; done) | (hm_eval3; w4_ev) | (hm_eval2; w4_ev))

-- `Std.DHashMap.Raw.not_mem_diff_of_mem_right` (binder 8): lawful Nat: m₁ has no buckets (not WF); Raw.diff returns m₂ = {0}, which contains k = 0
theorem w4c1_247 : ¬ drop0% Std.DHashMap.Raw.not_mem_diff_of_mem_right 8 :=
  fun h => by
  have := h (m₁ := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h₂ := W4c1.drw) (k := 0) (mem := (by w4_ev))
  first | (have e : DHashMap.Raw.diff (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat)) (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this) | (have e : ((⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat)) \ (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat))) = (⟨1, f16 (.cons 0 0 .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)) := rfl; rw [e] at this)
  exact this (by w4_ev)

-- `Std.HashMap.Raw.not_mem_diff_of_mem_right` (binder 8): lawful Nat: m₁ has no buckets (not WF); Raw.diff returns m₂ = {0}, which contains k = 0
theorem w4c1_248 : ¬ drop0% Std.HashMap.Raw.not_mem_diff_of_mem_right 8 :=
  fun h => by
  have := h (m₁ := (hmr 0 #[] : HashMap.Raw Nat Nat)) (m₂ := (hmr 1 (f16 (b1 0 (0 : Nat))) : HashMap.Raw Nat Nat)) (h₂ := ⟨W4c1.drw⟩) (k := 0) (mem := (by w4_ev))
  first | (have e : HashMap.Raw.diff (hmr 0 #[] : HashMap.Raw Nat Nat) (hmr 1 (f16 (b1 0 (0 : Nat))) : HashMap.Raw Nat Nat) = (hmr 1 (f16 (b1 0 (0 : Nat))) : HashMap.Raw Nat Nat) := rfl; rw [e] at this) | (have e : ((hmr 0 #[] : HashMap.Raw Nat Nat) \ (hmr 1 (f16 (b1 0 (0 : Nat))) : HashMap.Raw Nat Nat)) = (hmr 1 (f16 (b1 0 (0 : Nat))) : HashMap.Raw Nat Nat) := rfl; rw [e] at this)
  exact this (by w4_ev)

-- `Std.HashMap.Raw.not_mem_diff_of_mem_right` (binder 9): removable: if m₁ is not larger, diff filters m₁ by m₂.contains (congruent on == keys for any m₂); otherwise it erases every stored key of m₂ from the WF m₁ (port of Probe1 p43)
theorem w4c1_249 : drop% Std.HashMap.Raw.not_mem_diff_of_mem_right 9 :=
  by
  intro α _ _ _ m₁ m₂ _ _ h₁ k mem
  exact W4c1.dr_nmdr h₁.out mem

-- `Std.HashSet.Raw.not_mem_diff_of_mem_right` (binder 7): lawful Nat: m₁ has no buckets (not WF); Raw.diff returns m₂ = {0}, which contains k = 0
theorem w4c1_250 : ¬ drop0% Std.HashSet.Raw.not_mem_diff_of_mem_right 7 :=
  fun h => by
  have := h (m₁ := (hsr 0 #[] : HashSet.Raw Nat)) (m₂ := (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat)) (h₂ := W4c1.hsrw) (k := 0) (mem := (by w4_ev))
  first | (have e : HashSet.Raw.diff (hsr 0 #[] : HashSet.Raw Nat) (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat) = (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat) := rfl; rw [e] at this) | (have e : ((hsr 0 #[] : HashSet.Raw Nat) \ (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat)) = (hsr 1 (f16 (b1 0 ())) : HashSet.Raw Nat) := rfl; rw [e] at this)
  exact this (by w4_ev)

-- `Std.HashSet.Raw.not_mem_diff_of_mem_right` (binder 8): removable: if m₁ is not larger, diff filters m₁ by m₂.contains (congruent on == keys for any m₂); otherwise it erases every stored key of m₂ from the WF m₁ (port of Probe1 p43)
theorem w4c1_251 : drop% Std.HashSet.Raw.not_mem_diff_of_mem_right 8 :=
  by
  intro α _ _ m₁ m₂ _ _ h₁ k mem
  exact W4c1.dr_nmdr h₁.out.out mem

-- `Std.DHashMap.Equiv.size_eq` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_252 : ¬ drop0% Std.DHashMap.Equiv.size_eq 6 :=
  fun h => by
  have := h (m₁ := (hm NS.broken 1 #[.nil, .nil] (by decide) : HashMap NS Nat).inner) (m₂ := (hm NS.broken 0 #[.nil, .nil] (by decide) : HashMap NS Nat).inner) (h := ⟨⟨by first | rfl | simp [toListModel]⟩⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.DHashMap.Raw.Equiv.size_eq` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_253 : ¬ drop0% Std.DHashMap.Raw.Equiv.size_eq 6 :=
  fun h => by
  have := h (m₁ := (⟨1, #[.nil, .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (m₂ := (⟨0, #[.nil, .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (h₁ := (wf_vac NS.broken _ (by decide))) (h₂ := (wf_vac NS.broken _ (by decide))) (h := ⟨by first | rfl | simp [toListModel]⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashMap.Equiv.size_eq` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_254 : ¬ drop0% Std.HashMap.Equiv.size_eq 6 :=
  fun h => by
  have := h (m₁ := (hm NS.broken 1 #[.nil, .nil] (by decide) : HashMap NS Nat)) (m₂ := (hm NS.broken 0 #[.nil, .nil] (by decide) : HashMap NS Nat)) (h := ⟨⟨⟨by first | rfl | simp [toListModel]⟩⟩⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashMap.Raw.Equiv.size_eq` (binder 6): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_255 : ¬ drop0% Std.HashMap.Raw.Equiv.size_eq 6 :=
  fun h => by
  have := h (m₁ := (hmr 1 #[.nil, .nil] : HashMap.Raw NS Nat)) (m₂ := (hmr 0 #[.nil, .nil] : HashMap.Raw NS Nat)) (h₁ := (hmr_wf NS.broken _ _ (by decide))) (h₂ := (hmr_wf NS.broken _ _ (by decide))) (h := ⟨⟨by first | rfl | simp [toListModel]⟩⟩)
  exact absurd this (by (try simp only [hmr_empty]); decide +kernel)

-- `Std.HashSet.Equiv.size_eq` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_256 : ¬ drop0% Std.HashSet.Equiv.size_eq 5 :=
  fun h => by
  have := h (m₁ := (hs NS.broken 1 #[.nil, .nil] (by decide) : HashSet NS)) (m₂ := (hs NS.broken 0 #[.nil, .nil] (by decide) : HashSet NS)) (h := ⟨⟨⟨⟨by first | rfl | simp [toListModel]⟩⟩⟩⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashSet.Raw.Equiv.size_eq` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_257 : ¬ drop0% Std.HashSet.Raw.Equiv.size_eq 5 :=
  fun h => by
  have := h (m₁ := (hsr 1 #[.nil, .nil] : HashSet.Raw NS)) (m₂ := (hsr 0 #[.nil, .nil] : HashSet.Raw NS)) (h₁ := (hsr_wf NS.broken _ _ (by decide))) (h₂ := (hsr_wf NS.broken _ _ (by decide))) (h := ⟨⟨⟨by first | rfl | simp [toListModel]⟩⟩⟩)
  exact absurd this (by (try simp only [hsr_empty]); decide +kernel)

-- `Std.DHashMap.Equiv.size_eq` (binder 7): AB (== always true, hash n; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_258 : ¬ drop0% Std.DHashMap.Equiv.size_eq 7 :=
  fun h => by
  have := h (m₁ := (hm AB.broken 1 #[.nil, .nil] (by decide) : HashMap AB Nat).inner) (m₂ := (hm AB.broken 0 #[.nil, .nil] (by decide) : HashMap AB Nat).inner) (h := ⟨⟨by first | rfl | simp [toListModel]⟩⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.DHashMap.Raw.Equiv.size_eq` (binder 7): AB (== always true, hash n; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_259 : ¬ drop0% Std.DHashMap.Raw.Equiv.size_eq 7 :=
  fun h => by
  have := h (m₁ := (⟨1, #[.nil, .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (m₂ := (⟨0, #[.nil, .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (h₁ := (wf_vac AB.broken _ (by decide))) (h₂ := (wf_vac AB.broken _ (by decide))) (h := ⟨by first | rfl | simp [toListModel]⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashMap.Equiv.size_eq` (binder 7): AB (== always true, hash n; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_260 : ¬ drop0% Std.HashMap.Equiv.size_eq 7 :=
  fun h => by
  have := h (m₁ := (hm AB.broken 1 #[.nil, .nil] (by decide) : HashMap AB Nat)) (m₂ := (hm AB.broken 0 #[.nil, .nil] (by decide) : HashMap AB Nat)) (h := ⟨⟨⟨by first | rfl | simp [toListModel]⟩⟩⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashMap.Raw.Equiv.size_eq` (binder 7): AB (== always true, hash n; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_261 : ¬ drop0% Std.HashMap.Raw.Equiv.size_eq 7 :=
  fun h => by
  have := h (m₁ := (hmr 1 #[.nil, .nil] : HashMap.Raw AB Nat)) (m₂ := (hmr 0 #[.nil, .nil] : HashMap.Raw AB Nat)) (h₁ := (hmr_wf AB.broken _ _ (by decide))) (h₂ := (hmr_wf AB.broken _ _ (by decide))) (h := ⟨⟨by first | rfl | simp [toListModel]⟩⟩)
  exact absurd this (by (try simp only [hmr_empty]); decide +kernel)

-- `Std.HashSet.Equiv.size_eq` (binder 6): AB (== always true, hash n; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_262 : ¬ drop0% Std.HashSet.Equiv.size_eq 6 :=
  fun h => by
  have := h (m₁ := (hs AB.broken 1 #[.nil, .nil] (by decide) : HashSet AB)) (m₂ := (hs AB.broken 0 #[.nil, .nil] (by decide) : HashSet AB)) (h := ⟨⟨⟨⟨by first | rfl | simp [toListModel]⟩⟩⟩⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashSet.Raw.Equiv.size_eq` (binder 6): AB (== always true, hash n; WF vacuous): m₁, m₂ with two empty buckets and size fields 1, 0: equivalent, sizes differ
theorem w4c1_263 : ¬ drop0% Std.HashSet.Raw.Equiv.size_eq 6 :=
  fun h => by
  have := h (m₁ := (hsr 1 #[.nil, .nil] : HashSet.Raw AB)) (m₂ := (hsr 0 #[.nil, .nil] : HashSet.Raw AB)) (h₁ := (hsr_wf AB.broken _ _ (by decide))) (h₂ := (hsr_wf AB.broken _ _ (by decide))) (h := ⟨⟨⟨by first | rfl | simp [toListModel]⟩⟩⟩)
  exact absurd this (by (try simp only [hsr_empty]); decide +kernel)

-- `Std.DHashMap.Equiv.size_eq` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅ (not equivalent): sizes / emptiness differ
theorem w4c1_264 : ¬ drop0% Std.DHashMap.Equiv.size_eq 8 :=
  fun h => by
  have := h (m₁ := ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap Nat (fun _ => Nat)))
  simp [DHashMap.mem_insert, DHashMap.contains_insert, DHashMap.size_insert, DHashMap.mem_diff_iff, DHashMap.mem_inter_iff, DHashMap.mem_union_iff, DHashMap.isEmpty_insert] at this

-- `Std.DHashMap.Raw.Equiv.size_eq` (binder 10): lawful Nat, m₁ = {0}, m₂ = ∅ (not equivalent): sizes / emptiness differ
theorem w4c1_265 : ¬ drop0% Std.DHashMap.Raw.Equiv.size_eq 10 :=
  fun h => by
  have w0 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).WF := .empty
  have w1 : ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := w1) (h₂ := w0)
  simp [DHashMap.Raw.mem_insert, DHashMap.Raw.contains_insert, DHashMap.Raw.size_insert, DHashMap.Raw.mem_diff_iff, DHashMap.Raw.mem_inter_iff, DHashMap.Raw.mem_union_iff, DHashMap.Raw.isEmpty_insert, w0, w1] at this

-- `Std.HashMap.Equiv.size_eq` (binder 8): lawful Nat, m₁ = {0}, m₂ = ∅ (not equivalent): sizes / emptiness differ
theorem w4c1_266 : ¬ drop0% Std.HashMap.Equiv.size_eq 8 :=
  fun h => by
  have := h (m₁ := ((∅ : HashMap Nat Nat).insert 0 0)) (m₂ := (∅ : HashMap Nat Nat))
  simp [HashMap.mem_insert, HashMap.contains_insert, HashMap.size_insert, HashMap.mem_diff_iff, HashMap.mem_inter_iff, HashMap.mem_union_iff, HashMap.isEmpty_insert] at this

-- `Std.HashMap.Raw.Equiv.size_eq` (binder 10): lawful Nat, m₁ = {0}, m₂ = ∅ (not equivalent): sizes / emptiness differ
theorem w4c1_267 : ¬ drop0% Std.HashMap.Raw.Equiv.size_eq 10 :=
  fun h => by
  have w0 : (∅ : HashMap.Raw Nat Nat).WF := .empty
  have w1 : ((∅ : HashMap.Raw Nat Nat).insert 0 0).WF := .insert .empty
  have := h (m₁ := ((∅ : HashMap.Raw Nat Nat).insert 0 0)) (m₂ := (∅ : HashMap.Raw Nat Nat)) (h₁ := w1) (h₂ := w0)
  simp [HashMap.Raw.mem_insert, HashMap.Raw.contains_insert, HashMap.Raw.size_insert, HashMap.Raw.mem_diff_iff, HashMap.Raw.mem_inter_iff, HashMap.Raw.mem_union_iff, HashMap.Raw.isEmpty_insert, w0, w1] at this

-- `Std.HashSet.Equiv.size_eq` (binder 7): lawful Nat, m₁ = {0}, m₂ = ∅ (not equivalent): sizes / emptiness differ
theorem w4c1_268 : ¬ drop0% Std.HashSet.Equiv.size_eq 7 :=
  fun h => by
  have := h (m₁ := ((∅ : HashSet Nat).insert 0)) (m₂ := (∅ : HashSet Nat))
  simp [HashSet.mem_insert, HashSet.contains_insert, HashSet.size_insert, HashSet.mem_diff_iff, HashSet.mem_inter_iff, HashSet.mem_union_iff, HashSet.isEmpty_insert] at this

-- `Std.HashSet.Raw.Equiv.size_eq` (binder 9): lawful Nat, m₁ = {0}, m₂ = ∅ (not equivalent): sizes / emptiness differ
theorem w4c1_269 : ¬ drop0% Std.HashSet.Raw.Equiv.size_eq 9 :=
  fun h => by
  have w0 : (∅ : HashSet.Raw Nat).WF := .empty
  have w1 : ((∅ : HashSet.Raw Nat).insert 0).WF := .insert .empty
  have := h (m₁ := ((∅ : HashSet.Raw Nat).insert 0)) (m₂ := (∅ : HashSet.Raw Nat)) (h₁ := w1) (h₂ := w0)
  simp [HashSet.Raw.mem_insert, HashSet.Raw.contains_insert, HashSet.Raw.size_insert, HashSet.Raw.mem_diff_iff, HashSet.Raw.mem_inter_iff, HashSet.Raw.mem_union_iff, HashSet.Raw.isEmpty_insert, w0, w1] at this

-- `Std.DHashMap.Raw.Equiv.size_eq` (binder 8): lawful Nat: m₁ has 16 empty buckets and size field 1 (not WF), the other is ∅: equivalent, sizes differ
theorem w4c1_270 : ¬ drop0% Std.DHashMap.Raw.Equiv.size_eq 8 :=
  fun h => by
  have := h (m₁ := (⟨1, nil16⟩ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (h₂ := .empty) (h := ⟨by first | (simp [dr_empty, toListModel, nil16]; done) | (simp only [dr_empty]; rfl) | (rw [dr_empty]; decide)⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.DHashMap.Raw.Equiv.size_eq` (binder 9): lawful Nat: m₂ has 16 empty buckets and size field 1 (not WF), the other is ∅: equivalent, sizes differ
theorem w4c1_271 : ¬ drop0% Std.DHashMap.Raw.Equiv.size_eq 9 :=
  fun h => by
  have := h (m₁ := (∅ : DHashMap.Raw Nat (fun _ => Nat))) (m₂ := (⟨1, nil16⟩ : DHashMap.Raw Nat (fun _ => Nat))) (h₁ := .empty) (h := ⟨by first | (simp [dr_empty, toListModel, nil16]; done) | (simp only [dr_empty]; rfl) | (rw [dr_empty]; decide)⟩)
  exact absurd this (by (try simp only [dr_empty]); decide +kernel)

-- `Std.HashMap.Raw.Equiv.size_eq` (binder 9): lawful Nat: m₂ has 16 empty buckets and size field 1 (not WF), the other is ∅: equivalent, sizes differ
theorem w4c1_272 : ¬ drop0% Std.HashMap.Raw.Equiv.size_eq 9 :=
  fun h => by
  have := h (m₁ := (∅ : HashMap.Raw Nat Nat)) (m₂ := (hmr 1 nil16 : HashMap.Raw Nat Nat)) (h₁ := .empty) (h := ⟨⟨by first | (simp [hmr_empty, toListModel, nil16]; done) | (simp only [hmr_empty]; rfl) | (rw [hmr_empty]; decide)⟩⟩)
  exact absurd this (by (try simp only [hmr_empty]); decide +kernel)

-- `Std.HashSet.Raw.Equiv.size_eq` (binder 7): lawful Nat: m₁ has 16 empty buckets and size field 1 (not WF), the other is ∅: equivalent, sizes differ
theorem w4c1_273 : ¬ drop0% Std.HashSet.Raw.Equiv.size_eq 7 :=
  fun h => by
  have := h (m₁ := (hsr 1 nil16 : HashSet.Raw Nat)) (m₂ := (∅ : HashSet.Raw Nat)) (h₂ := .empty) (h := ⟨⟨⟨by first | (simp [hsr_empty, toListModel, nil16]; done) | (simp only [hsr_empty]; rfl) | (rw [hsr_empty]; decide)⟩⟩⟩)
  exact absurd this (by (try simp only [hsr_empty]); decide +kernel)

-- `Std.HashSet.Raw.Equiv.size_eq` (binder 8): lawful Nat: m₂ has 16 empty buckets and size field 1 (not WF), the other is ∅: equivalent, sizes differ
theorem w4c1_274 : ¬ drop0% Std.HashSet.Raw.Equiv.size_eq 8 :=
  fun h => by
  have := h (m₁ := (∅ : HashSet.Raw Nat)) (m₂ := (hsr 1 nil16 : HashSet.Raw Nat)) (h₁ := .empty) (h := ⟨⟨⟨by first | (simp [hsr_empty, toListModel, nil16]; done) | (simp only [hsr_empty]; rfl) | (rw [hsr_empty]; decide)⟩⟩⟩)
  exact absurd this (by (try simp only [hsr_empty]); decide +kernel)

-- `Std.DHashMap.Const.size_filter_le_size` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_275 : ¬ drop0% Std.DHashMap.Const.size_filter_le_size 5 :=
  fun h => by
  have := h (m := (hm NS.broken 0 #[b1 (NS.mk 0) (0 : Nat), .nil] (by decide) : HashMap NS Nat).inner) (f := (fun _ _ => true))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.Const.size_filter_le_size` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_276 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.size_filter_le_size 5 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (NS.mk 0) (0 : Nat), .nil]⟩, by decide⟩ : Raw₀ NS (fun _ => Nat))) (f := (fun _ _ => true)) (h := (wf_vac NS.broken _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.size_filter_le_size` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_277 : ¬ drop0% Std.DHashMap.Internal.Raw₀.size_filter_le_size 5 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (NS.mk 0) (0 : Nat), .nil]⟩, by decide⟩ : Raw₀ NS (fun _ => Nat))) (f := (fun _ _ => true)) (h := (wf_vac NS.broken _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.Const.size_filter_le_size` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_278 : ¬ drop0% Std.DHashMap.Raw.Const.size_filter_le_size 5 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (NS.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (f := (fun _ _ => true)) (h := (wf_vac NS.broken _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.size_filter_le_size` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_279 : ¬ drop0% Std.DHashMap.Raw.size_filter_le_size 5 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (NS.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw NS (fun _ => Nat))) (f := (fun _ _ => true)) (h := (wf_vac NS.broken _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.size_filter_le_size` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_280 : ¬ drop0% Std.DHashMap.size_filter_le_size 5 :=
  fun h => by
  have := h (m := (hm NS.broken 0 #[b1 (NS.mk 0) (0 : Nat), .nil] (by decide) : HashMap NS Nat).inner) (f := (fun _ _ => true))
  exact absurd this (by decide +kernel)

-- `Std.HashMap.Raw.size_filter_le_size` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_281 : ¬ drop0% Std.HashMap.Raw.size_filter_le_size 5 :=
  fun h => by
  have := h (m := (hmr 0 #[b1 (NS.mk 0) (0 : Nat), .nil] : HashMap.Raw NS Nat)) (f := (fun _ _ => true)) (h := (hmr_wf NS.broken _ _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.HashMap.size_filter_le_size` (binder 5): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_282 : ¬ drop0% Std.HashMap.size_filter_le_size 5 :=
  fun h => by
  have := h (m := (hm NS.broken 0 #[b1 (NS.mk 0) (0 : Nat), .nil] (by decide) : HashMap NS Nat)) (f := (fun _ _ => true))
  exact absurd this (by decide +kernel)

-- `Std.HashSet.Raw.size_filter_le_size` (binder 4): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_283 : ¬ drop0% Std.HashSet.Raw.size_filter_le_size 4 :=
  fun h => by
  have := h (m := (hsr 0 #[b1 (NS.mk 0) (), .nil] : HashSet.Raw NS)) (f := (fun _ => true)) (h := (hsr_wf NS.broken _ _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.HashSet.size_filter_le_size` (binder 4): NS (a == b iff a ≤ b, hash 0; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_284 : ¬ drop0% Std.HashSet.size_filter_le_size 4 :=
  fun h => by
  have := h (m := (hs NS.broken 0 #[b1 (NS.mk 0) (), .nil] (by decide) : HashSet NS)) (f := (fun _ => true))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Const.size_filter_le_size` (binder 6): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_285 : ¬ drop0% Std.DHashMap.Const.size_filter_le_size 6 :=
  fun h => by
  have := h (m := (hm AB.broken 0 #[b1 (AB.mk 0) (0 : Nat), .nil] (by decide) : HashMap AB Nat).inner) (f := (fun _ _ => true))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.Const.size_filter_le_size` (binder 6): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_286 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.size_filter_le_size 6 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (AB.mk 0) (0 : Nat), .nil]⟩, by decide⟩ : Raw₀ AB (fun _ => Nat))) (f := (fun _ _ => true)) (h := (wf_vac AB.broken _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.Const.size_filter_le_size` (binder 6): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_287 : ¬ drop0% Std.DHashMap.Raw.Const.size_filter_le_size 6 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (AB.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (f := (fun _ _ => true)) (h := (wf_vac AB.broken _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.size_filter_le_size` (binder 6): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_288 : ¬ drop0% Std.DHashMap.Raw.size_filter_le_size 6 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (AB.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw AB (fun _ => Nat))) (f := (fun _ _ => true)) (h := (wf_vac AB.broken _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.HashMap.Raw.size_filter_le_size` (binder 6): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_289 : ¬ drop0% Std.HashMap.Raw.size_filter_le_size 6 :=
  fun h => by
  have := h (m := (hmr 0 #[b1 (AB.mk 0) (0 : Nat), .nil] : HashMap.Raw AB Nat)) (f := (fun _ _ => true)) (h := (hmr_wf AB.broken _ _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.HashSet.Raw.size_filter_le_size` (binder 5): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_290 : ¬ drop0% Std.HashSet.Raw.size_filter_le_size 5 :=
  fun h => by
  have := h (m := (hsr 0 #[b1 (AB.mk 0) (), .nil] : HashSet.Raw AB)) (f := (fun _ => true)) (h := (hsr_wf AB.broken _ _ (by decide)))
  exact absurd this (by decide +kernel)

-- `Std.HashSet.size_filter_le_size` (binder 5): AB (== always true, hash n; WF vacuous): m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_291 : ¬ drop0% Std.HashSet.size_filter_le_size 5 :=
  fun h => by
  have := h (m := (hs AB.broken 0 #[b1 (AB.mk 0) (), .nil] (by decide) : HashSet AB)) (f := (fun _ => true))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.Const.size_filter_le_size` (binder 8): lawful Nat, not WF: m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_292 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.size_filter_le_size 8 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (0 : Nat) (0 : Nat), .nil]⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat))) (f := (fun _ _ => true))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.size_filter_le_size` (binder 8): lawful Nat, not WF: m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_293 : ¬ drop0% Std.DHashMap.Internal.Raw₀.size_filter_le_size 8 :=
  fun h => by
  have := h (m := (⟨⟨0, #[b1 (0 : Nat) (0 : Nat), .nil]⟩, by decide⟩ : Raw₀ Nat (fun _ => Nat))) (f := (fun _ _ => true))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.Const.size_filter_le_size` (binder 8): lawful Nat, not WF: m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_294 : ¬ drop0% Std.DHashMap.Raw.Const.size_filter_le_size 8 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (0 : Nat) (0 : Nat), .nil]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (f := (fun _ _ => true))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.size_filter_le_size` (binder 8): lawful Nat, not WF: m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_295 : ¬ drop0% Std.DHashMap.Raw.size_filter_le_size 8 :=
  fun h => by
  have := h (m := (⟨0, #[b1 (0 : Nat) (0 : Nat), .nil]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (f := (fun _ _ => true))
  exact absurd this (by decide +kernel)

-- `Std.HashMap.Raw.size_filter_le_size` (binder 8): lawful Nat, not WF: m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_296 : ¬ drop0% Std.HashMap.Raw.size_filter_le_size 8 :=
  fun h => by
  have := h (m := (hmr 0 #[b1 (0 : Nat) (0 : Nat), .nil] : HashMap.Raw Nat Nat)) (f := (fun _ _ => true))
  exact absurd this (by decide +kernel)

-- `Std.HashSet.Raw.size_filter_le_size` (binder 7): lawful Nat, not WF: m has one entry in bucket 0 and size field 0; filter recomputes size 1 > 0
theorem w4c1_297 : ¬ drop0% Std.HashSet.Raw.size_filter_le_size 7 :=
  fun h => by
  have := h (m := (hsr 0 #[b1 (0 : Nat) (), .nil] : HashSet.Raw Nat)) (f := (fun _ => true))
  exact absurd this (by decide +kernel)
