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

/-! # Toolkit helpers collected from the merged probe and wave files (A0, the A1 fold-in, and the W2-W4 fold-in, 2026-11-09).
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

/-! ## From `checks/W2c0Hand.lean` -/
namespace W2c0
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
-- insert never lowers the size field (no laws, no WF)
theorem ins_size_ge (m : Raw₀ α β) (a : α) (b : β a) : m.1.size ≤ (m.insert a b).1.size := by
  obtain ⟨⟨s, bs⟩, h⟩ := m; unfold Raw₀.insert; dsimp only; split
  · exact Nat.le_refl _
  · rw [expand_size]; exact Nat.le_succ _
theorem r0_im {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (m : Raw₀ α β) (l : ρ)
    (h : (m.insertMany l).1.1.isEmpty = true) : m.1.isEmpty = true := by
  have := (m.insertMany l).2 (fun m' => m.1.size ≤ m'.1.size) (fun h => Nat.le_trans h (ins_size_ge _ _ _)) (Nat.le_refl _)
  simp only [DHashMap.Raw.isEmpty, beq_iff_eq] at h ⊢; omega
theorem dh_im {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (m : DHashMap α β) (l : ρ)
    (h : (m.insertMany l).isEmpty = true) : m.isEmpty = true :=
  r0_im ⟨m.1, m.2.size_buckets_pos⟩ l h
theorem dr_im {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (m : DHashMap.Raw α β) (l : ρ)
    (h : (m.insertMany l).isEmpty = true) : m.isEmpty = true := by
  unfold DHashMap.Raw.insertMany at h; split at h
  · exact r0_im ⟨m, _⟩ l h
  · exact h
end W2c0
namespace W2c0
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
theorem r0c_im {ρ : Type w} [ForIn Id ρ (α × β)] (m : Raw₀ α (fun _ => β)) (l : ρ)
    (h : (Raw₀.Const.insertMany m l).1.1.isEmpty = true) : m.1.isEmpty = true := by
  have := (Raw₀.Const.insertMany m l).2 (fun m' => m.1.size ≤ m'.1.size) (fun h => Nat.le_trans h (ins_size_ge _ _ _)) (Nat.le_refl _)
  simp only [DHashMap.Raw.isEmpty, beq_iff_eq] at h ⊢; omega
theorem dhc_im {ρ : Type w} [ForIn Id ρ (α × β)] (m : DHashMap α (fun _ => β)) (l : ρ)
    (h : (DHashMap.Const.insertMany m l).isEmpty = true) : m.isEmpty = true :=
  r0c_im ⟨m.1, m.2.size_buckets_pos⟩ l h
theorem drc_im {ρ : Type w} [ForIn Id ρ (α × β)] (m : DHashMap.Raw α (fun _ => β)) (l : ρ)
    (h : (DHashMap.Raw.Const.insertMany m l).isEmpty = true) : m.isEmpty = true := by
  unfold DHashMap.Raw.Const.insertMany at h; split at h
  · exact r0c_im ⟨m, _⟩ l h
  · exact h
theorem hm_im {ρ : Type w} [ForIn Id ρ (α × β)] (m : HashMap α β) (l : ρ)
    (h : (m.insertMany l).isEmpty = true) : m.isEmpty = true := dhc_im m.inner l h
theorem hmr_im {ρ : Type w} [ForIn Id ρ (α × β)] (m : HashMap.Raw α β) (l : ρ)
    (h : (m.insertMany l).isEmpty = true) : m.isEmpty = true := drc_im m.inner l h
theorem hs_im {ρ : Type w} [ForIn Id ρ α] (m : HashSet α) (l : ρ)
    (h : (m.insertMany l).isEmpty = true) : m.isEmpty = true := dm_imnu m.inner.inner l h
theorem hsr_im {ρ : Type w} [ForIn Id ρ α] (m : HashSet.Raw α) (l : ρ)
    (h : (m.insertMany l).isEmpty = true) : m.isEmpty = true := dr_imnu m.inner.inner l h
end W2c0
/-- Evaluates membership in a union of literal hash maps whose larger side resizes once. -/
macro "w2c0_union" : tactic => `(tactic| (
  try simp only [Union.union, HashSet.union, HashSet.Raw.union, HashMap.union, HashMap.Raw.union, DHashMap.union,
    drn_union, hmr_union]
  try simp only [HashSet.mem_iff_contains, HashMap.mem_iff_contains, DHashMap.mem_iff_contains, HashSet.Raw.mem_iff_contains,
    HashMap.Raw.mem_iff_contains, Std.DHashMap.Raw.mem_iff_contains, HashSet.contains, HashMap.contains, DHashMap.contains,
    HashSet.Raw.contains, HashMap.Raw.contains]
  try simp (disch := decide) only [dr_union_lit, hmr_empty, hsr_empty, dr_empty, dr_insert_lit]
  try simp (disch := decide) only [dr_union_lit]
  simp (config := {decide := true}) only [Raw₀.union, ite_false, ite_true]
  hm_expand))
namespace W2c0
-- CZ copies of W1c5.zh_hs / zh_wf: every CZ bucket array #[l, nil] is hash-self
theorem cz_hs {β : CZ → Type v} (l : AssocList CZ β) : IsHashSelf (#[l, .nil] : Array (AssocList CZ β)) := by
  refine ⟨fun i hi => ⟨fun h p hp => ?_⟩⟩
  rw [mkIdx_toNat' _ _ _ (by simp [Pow2])]
  have : (scrambleHash (hash p.1)).toNat % 2 = 0 := by
    show (scrambleHash 0).toNat % 2 = 0
    rw [scr_small _ (by decide)]; rfl
  rw [show (#[l, AssocList.nil] : Array (AssocList CZ β)).size = 2 from rfl, this]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => simp at hp
theorem cz_wf {β : CZ → Type v} (s : Nat) (l : AssocList CZ β) (hs : s = (toListModel #[l, .nil]).length)
    (hd : Std.Internal.List.DistinctKeys (toListModel #[l, .nil])) :
    (⟨s, #[l, .nil]⟩ : DHashMap.Raw CZ β).WF :=
  .wf (by simp) (fun {_ _} => ⟨cz_hs l, hs, hd⟩)
end W2c0
namespace W2c0
theorem contains_insert_of {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
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
variable {α : Type u} [BEq α] [Hashable α]
-- insertMany / insertManyIfNewUnit keep every found key, for arbitrary (also ill-formed) maps with buckets
theorem r0_mim {β : α → Type v} [EquivBEq α] [LawfulHashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)]
    (m : Raw₀ α β) (l : ρ) (k : α) (h : m.contains k = true) : (m.insertMany l).1.contains k = true :=
  (m.insertMany l).2 (fun m' => m'.contains k = true) (fun h' => contains_insert_of _ _ _ _ h') h
theorem r0c_mim {β : Type v} [EquivBEq α] [LawfulHashable α] {ρ : Type w} [ForIn Id ρ (α × β)]
    (m : Raw₀ α (fun _ => β)) (l : ρ) (k : α) (h : m.contains k = true) : (Raw₀.Const.insertMany m l).1.contains k = true :=
  (Raw₀.Const.insertMany m l).2 (fun m' => m'.contains k = true) (fun h' => contains_insert_of _ _ _ _ h') h
theorem r0u_mim [LawfulHashable α] {ρ : Type w} [ForIn Id ρ α]
    (m : Raw₀ α (fun _ => Unit)) (l : ρ) (k : α) (h : m.contains k = true) :
    (Raw₀.Const.insertManyIfNewUnit m l).1.contains k = true :=
  (Raw₀.Const.insertManyIfNewUnit m l).2 (fun m' => m'.contains k = true) (fun h' => W1c5.contains_insertIfNew_of _ _ _ _ h') h
theorem dr_mim {β : α → Type v} [EquivBEq α] [LawfulHashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)]
    (m : DHashMap.Raw α β) (l : ρ) (k : α) (h : k ∈ m) : k ∈ m.insertMany l := by
  rw [DHashMap.Raw.mem_iff_contains] at h ⊢
  unfold DHashMap.Raw.insertMany; split
  · rename_i hb
    unfold DHashMap.Raw.contains at h ⊢; rw [dif_pos hb] at h
    rw [dif_pos (Raw₀.insertMany ⟨m, hb⟩ l).1.2]; exact r0_mim ⟨m, hb⟩ l k h
  · exact h
theorem drc_mim {β : Type v} [EquivBEq α] [LawfulHashable α] {ρ : Type w} [ForIn Id ρ (α × β)]
    (m : DHashMap.Raw α (fun _ => β)) (l : ρ) (k : α) (h : k ∈ m) : k ∈ DHashMap.Raw.Const.insertMany m l := by
  rw [DHashMap.Raw.mem_iff_contains] at h ⊢
  unfold DHashMap.Raw.Const.insertMany; split
  · rename_i hb
    unfold DHashMap.Raw.contains at h ⊢; rw [dif_pos hb] at h
    rw [dif_pos (Raw₀.Const.insertMany ⟨m, hb⟩ l).1.2]; exact r0c_mim ⟨m, hb⟩ l k h
  · exact h
theorem dru_mim [LawfulHashable α] {ρ : Type w} [ForIn Id ρ α]
    (m : DHashMap.Raw α (fun _ => Unit)) (l : ρ) (k : α) (h : k ∈ m) : k ∈ DHashMap.Raw.Const.insertManyIfNewUnit m l := by
  rw [DHashMap.Raw.mem_iff_contains] at h ⊢
  unfold DHashMap.Raw.Const.insertManyIfNewUnit; split
  · rename_i hb
    unfold DHashMap.Raw.contains at h ⊢; rw [dif_pos hb] at h
    rw [dif_pos (Raw₀.Const.insertManyIfNewUnit ⟨m, hb⟩ l).1.2]; exact r0u_mim ⟨m, hb⟩ l k h
  · exact h
theorem hmr_mim {β : Type v} [EquivBEq α] [LawfulHashable α] {ρ : Type w} [ForIn Id ρ (α × β)]
    (m : HashMap.Raw α β) (l : ρ) (k : α) (h : k ∈ m) : k ∈ m.insertMany l := drc_mim m.inner l k h
theorem hsr_mim [LawfulHashable α] {ρ : Type w} [ForIn Id ρ α]
    (m : HashSet.Raw α) (l : ρ) (k : α) (h : k ∈ m) : k ∈ m.insertMany l := dru_mim m.inner.inner l k h
theorem hs_mim [LawfulHashable α] {ρ : Type w} [ForIn Id ρ α]
    (m : HashSet α) (l : ρ) (k : α) (h : k ∈ m) : k ∈ m.insertMany l :=
  r0u_mim ⟨m.inner.inner.1, m.inner.inner.2.size_buckets_pos⟩ l k h
end W2c0

/-! ## From `checks/W2c1Hand.lean` -/
/-! # W2c1 helpers -/
@[simp] theorem w2c1_hnh (n : Nat) : hash (Probe1.HN.mk n) = UInt64.ofNat n := rfl
-- helper: HN (halves, hash = number) is EquivBEq but not LawfulHashable
theorem w2c1HN : ∀ [EquivBEq Probe1.HN] [LawfulHashable Probe1.HN], False := fun {_ h} => Probe1.HN.notLH h
-- helper: a bucket that does not contain a returns the fallback (any BEq)
theorem w2c1_alD {α : Type u} {β : Type v} [BEq α] (l : AssocList α (fun _ => β)) (a : α) (fb : β)
    (h : l.contains a = false) : l.getD a fb = fb := by
  induction l with
  | nil => rfl
  | cons k v es ih => simp_all [AssocList.contains, AssocList.getD]
theorem w2c1_alCD {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] (l : AssocList α β) (a : α) (fb : β a)
    (h : l.contains a = false) : l.getCastD a fb = fb := by
  induction l with
  | nil => rfl
  | cons k v es ih => simp_all [AssocList.contains, AssocList.getCastD]
theorem w2c1_alKD {α : Type u} {β : α → Type v} [BEq α] (l : AssocList α β) (a fb : α)
    (h : l.contains a = false) : l.getKeyD a fb = fb := by
  induction l with
  | nil => rfl
  | cons k v es ih => simp_all [AssocList.contains, AssocList.getKeyD]
theorem w2c1_r0cD {α : Type u} {β : Type v} [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (fb : β)
    (h : m.contains a = false) : Raw₀.Const.getD m a fb = fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m; exact w2c1_alD _ _ _ h
theorem w2c1_r0D {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (fb : β a)
    (h : m.contains a = false) : Raw₀.getD m a fb = fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m; exact w2c1_alCD _ _ _ h
theorem w2c1_r0KD {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m : Raw₀ α β) (a fb : α)
    (h : m.contains a = false) : Raw₀.getKeyD m a fb = fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m; exact w2c1_alKD _ _ _ h
theorem w2c1_rcD {α : Type u} {β : Type v} [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => β)) (a : α) (fb : β)
    (h : m.contains a = false) : DHashMap.Raw.Const.getD m a fb = fb := by
  unfold DHashMap.Raw.Const.getD; unfold DHashMap.Raw.contains at h
  split
  · rename_i hb; rw [dite_eq_left hb] at h; exact w2c1_r0cD _ _ _ h
  · rfl
theorem w2c1_rD {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] [Hashable α] (m : DHashMap.Raw α β) (a : α) (fb : β a)
    (h : m.contains a = false) : DHashMap.Raw.getD m a fb = fb := by
  unfold DHashMap.Raw.getD; unfold DHashMap.Raw.contains at h
  split
  · rename_i hb; rw [dite_eq_left hb] at h; exact w2c1_r0D _ _ _ h
  · rfl
theorem w2c1_rKD {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m : DHashMap.Raw α β) (a fb : α)
    (h : m.contains a = false) : DHashMap.Raw.getKeyD m a fb = fb := by
  unfold DHashMap.Raw.getKeyD; unfold DHashMap.Raw.contains at h
  split
  · rename_i hb; rw [dite_eq_left hb] at h; exact w2c1_r0KD _ _ _ h
  · rfl
-- helper: WF closer for raw maps built from ∅ by insert / insertIfNew
macro "w2c1wf" : tactic => `(tactic| repeat (first | exact HashMap.Raw.WF.empty | exact DHashMap.Raw.WF.empty | exact HashSet.Raw.WF.empty | apply HashMap.Raw.WF.insert | apply HashMap.Raw.WF.insertIfNew | apply DHashMap.Raw.WF.insert | apply DHashMap.Raw.WF.insertIfNew | apply HashSet.Raw.WF.insert | apply DHashMap.Raw.WF.Const.insertMany | apply DHashMap.Raw.WF.insertMany | apply HashMap.Raw.WF.insertMany | apply HashMap.Raw.WF.insertManyIfNewUnit | apply DHashMap.Raw.WF.Const.insertManyIfNewUnit))
@[simp] theorem w2c1_zhh (a : W1c5.ZH) : hash a = 0 := rfl
-- helper: m₁ \ m₃ ~ m₂ \ m₃ needs WF only for m₁, m₂: m₃ enters through a fixed contains test or a fixed erase list
theorem w2c1_diffL {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ m₃ : Raw₀ α β) (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (e : m₁.1.Equiv m₂.1) :
    (m₁.diff m₃).1.Equiv (m₂.diff m₃).1 := by
  have w₁ := Raw.WF.out h₁; have w₂ := Raw.WF.out h₂
  have hs : m₁.1.size = m₂.1.size := by rw [w₁.size_eq, w₂.size_eq]; exact e.1.length_eq
  constructor
  rw [Raw₀.diff_eq_diffₘ, Raw₀.diff_eq_diffₘ]; simp only [Raw₀.diffₘ, hs]
  split
  · refine (Raw₀.toListModel_filterₘ).trans ?_
    refine List.Perm.trans ?_ (Raw₀.toListModel_filterₘ (m := m₂) (f := fun k _ => !m₃.containsₘ k)).symm
    exact e.1.filter _
  · rw [Raw₀.eraseManyEntries_eq_eraseListₘ, Raw₀.eraseManyEntries_eq_eraseListₘ]
    exact (Raw₀.toListModel_eraseListₘ w₁).trans ((Std.Internal.List.eraseList_perm_of_perm_first e.1 w₁.distinct).trans
      (Raw₀.toListModel_eraseListₘ w₂).symm)
-- helper: the same for raw maps (a bucketless m₃ leaves m₁ unchanged)
theorem w2c1_rdiffL {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ m₃ : DHashMap.Raw α β) (h₁ : m₁.WF) (h₂ : m₂.WF) (e : m₁.Equiv m₂) : (m₁ \ m₃).Equiv (m₂ \ m₃) := by
  simp only [SDiff.sdiff, DHashMap.Raw.diff, dif_pos h₁.size_buckets_pos, dif_pos h₂.size_buckets_pos]
  split
  · exact w2c1_diffL ⟨m₁, _⟩ ⟨m₂, _⟩ ⟨m₃, _⟩ h₁ h₂ e
  · exact e

/-! ## From `checks/W2c2Hand.lean` -/
/-! # W2c2 helpers -/
-- monad recording bind nesting (pure counts 0, each bind doubles the left count): not lawful
def w2c2AM (α : Type) : Type := Nat × α
instance : Monad w2c2AM where
  pure a := (0, a)
  bind x f := (2 * x.1 + (f x.2).1 + 1, (f x.2).2)
namespace W2c2R
variable {α : Type u} {β : α → Type v}
-- insert under any Ord only adds the new entry
theorem ins_sub [Ord α] (k : α) (v : β k) (t : Impl α β) (h : t.Balanced) :
    ∀ x ∈ (t.insert k v h).impl.toListModel, x = ⟨k, v⟩ ∨ x ∈ t.toListModel := by
  induction t with
  | leaf => intro x hx; simp [Impl.insert, Impl.toListModel] at hx; exact Or.inl hx
  | inner sz k' v' l r ihl ihr =>
    intro x hx
    simp only [Impl.insert] at hx
    split at hx
    · simp only [Impl.toListModel_balanceL, List.mem_append, List.mem_cons] at hx
      rcases hx with hx | hx | hx
      · rcases ihl _ x hx with e | e
        · exact Or.inl e
        · exact Or.inr (by simp [Impl.toListModel, e])
      · exact Or.inr (by simp [Impl.toListModel, hx])
      · exact Or.inr (by simp [Impl.toListModel, hx])
    · simp only [Impl.toListModel_balanceR, List.mem_append, List.mem_cons] at hx
      rcases hx with hx | hx | hx
      · exact Or.inr (by simp [Impl.toListModel, hx])
      · exact Or.inr (by simp [Impl.toListModel, hx])
      · rcases ihr _ x hx with e | e
        · exact Or.inl e
        · exact Or.inr (by simp [Impl.toListModel, e])
    · simp only [Impl.toListModel, List.mem_append, List.mem_cons] at hx
      rcases hx with hx | hx | hx
      · exact Or.inr (by simp [Impl.toListModel, hx])
      · exact Or.inl hx
      · exact Or.inr (by simp [Impl.toListModel, hx])
theorem fold_sub [Ord α] (l0 : List ((k : α) × β k)) : ∀ (l : List ((k : α) × β k)) (t : Impl α β),
    t.Balanced → (∀ x ∈ t.toListModel, x ∈ l0) → (∀ x ∈ l, x ∈ l0) →
    ∀ x ∈ (l.foldl (init := t) fun acc ⟨k, v⟩ => acc.insert! k v).toListModel, x ∈ l0
  | [], t, _, ht, _ => ht
  | ⟨a, b⟩ :: l, t, hb, ht, hl => by
    simp only [List.foldl_cons]
    rw [← Impl.insert_eq_insert! (h := hb)]
    refine fold_sub l0 l _ (Impl.insert a b t hb).balanced_impl ?_ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    intro x hx
    rcases ins_sub a b t hb x hx with e | e
    · exact e ▸ hl _ (List.mem_cons_self ..)
    · exact ht x e
theorem ofList_sub [Ord α] (l : List ((k : α) × β k)) : ∀ x ∈ (Impl.ofList l).toListModel, x ∈ l := by
  simp only [Impl.ofList]
  rw [Impl.insertMany_eq_foldl]
  exact fold_sub l l _ Impl.balanced_empty (by simp [Impl.empty]) (fun _ h => h)
theorem pw_eq {cmp : α → α → Ordering} [Std.ReflCmp cmp] : ∀ {l : List ((a : α) × β a)},
    l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq) → ∀ {x y}, x ∈ l → y ∈ l → x.1 = y.1 → x = y
  | [], _, _, _, hx, _, _ => nomatch hx
  | a :: l, hp, x, y, hx, hy, e => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · exact absurd (by rw [e]; exact Std.ReflCmp.compare_self) (hp.1 y hy')
    · exact absurd (by rw [← e]; exact Std.ReflCmp.compare_self) (hp.1 x hx')
    · exact pw_eq hp.2 hx' hy' e
theorem get_mem [Ord α] [LawfulEqOrd α] (t : Impl α β) (k : α) (h : k ∈ t) :
    ⟨k, t.get k h⟩ ∈ t.toListModel := by
  induction t with
  | leaf => exact absurd h (by simp [Impl.mem_iff_contains, Impl.contains])
  | inner sz k' v' l r ihl ihr =>
    unfold Impl.get
    split
    · simp only [Impl.toListModel, List.mem_append]; exact Or.inl (ihl _)
    · simp only [Impl.toListModel, List.mem_append, List.mem_cons]; exact Or.inr (Or.inr (ihr _))
    · rename_i hc
      have e := LawfulEqOrd.eq_of_compare hc
      subst e
      simp [Impl.toListModel]
end W2c2R

/-! ## From `checks/W2c3Hand.lean` -/
universe w2u w2v
def w2c3_bB {α : Type w2u} {β : α → Type w2v} : Impl α β → Bool
  | .leaf => true
  | .inner sz _ _ l r => w2c3_bB l && w2c3_bB r &&
      (decide (l.size + r.size ≤ 1) || (decide (l.size ≤ delta * r.size) && decide (r.size ≤ delta * l.size))) &&
      sz == l.size + 1 + r.size
theorem w2c3_bB_iff {α : Type w2u} {β : α → Type w2v} (t : Impl α β) : t.Balanced ↔ w2c3_bB t = true := by
  induction t with
  | leaf => simp [w2c3_bB, Impl.Balanced.leaf]
  | inner sz k v l r ihl ihr =>
    rw [Impl.balanced_inner_iff, ihl, ihr]
    simp [w2c3_bB, Impl.BalancedAtRoot, Bool.and_eq_true, and_assoc]
instance w2c3_decBal {α : Type w2u} {β : α → Type w2v} : DecidablePred (@Impl.Balanced α β) :=
  fun t => decidable_of_iff _ (w2c3_bB_iff t).symm
instance w2c3_decBAR (a b : Nat) : Decidable (Impl.BalancedAtRoot a b) := by
  unfold Impl.BalancedAtRoot; infer_instance
def w2c3_ser : Impl Nat (fun _ => Nat) → List Nat
  | .leaf => [0]
  | .inner sz k v l r => [1, sz, k, v] ++ w2c3_ser l ++ w2c3_ser r
theorem w2c3_sb {α : Type w2u} {β : α → Type w2v} {k : α} {v : β k} {l r : Impl α β} (hl : l.Balanced) (hr : r.Balanced) :
    (Impl.balance! k v l r).size = l.size + 1 + r.size := by
  fun_cases Impl.balance! k v l r
  all_goals simp only [Impl.size_inner, Impl.size_leaf, Impl.balanced_inner_iff, Impl.Balanced.leaf, true_and, Impl.BalancedAtRoot, delta] at *
  all_goals omega
theorem w2c3_sbL {α : Type w2u} {β : α → Type w2v} {k : α} {v : β k} {l r : Impl α β} (hl : l.Balanced) (hr : r.Balanced) :
    (Impl.balanceL! k v l r).size = l.size + 1 + r.size := by
  fun_cases Impl.balanceL! k v l r
  all_goals simp only [Impl.size_inner, Impl.size_leaf, Impl.balanced_inner_iff, Impl.Balanced.leaf, true_and, Impl.BalancedAtRoot, delta] at *
  all_goals omega
theorem w2c3_sbR {α : Type w2u} {β : α → Type w2v} {k : α} {v : β k} {l r : Impl α β} (hl : l.Balanced) (hr : r.Balanced) :
    (Impl.balanceR! k v l r).size = l.size + 1 + r.size := by
  fun_cases Impl.balanceR! k v l r
  all_goals simp only [Impl.size_inner, Impl.size_leaf, Impl.balanced_inner_iff, Impl.Balanced.leaf, true_and, Impl.BalancedAtRoot, delta] at *
  all_goals omega
theorem w2c3_isz {α : Type w2u} {β : α → Type w2v} [Ord α] (k : α) (v : β k) :
    ∀ t : Impl α β, t.Balanced → (t.insert! k v).size = if t.contains k then t.size else t.size + 1
  | .leaf, _ => by simp [Impl.insert!, Impl.contains, Impl.size_leaf, Impl.size_inner]
  | .inner sz ky y l r, hb => by
    have hl := hb.left; have hr := hb.right; have he := hb.eq
    have il := w2c3_isz k v l hl; have ir := w2c3_isz k v r hr
    have bl : (l.insert! k v).Balanced := Impl.insert_eq_insert! (h := hl) ▸ (l.insert k v hl).balanced_impl
    have br : (r.insert! k v).Balanced := Impl.insert_eq_insert! (h := hr) ▸ (r.insert k v hr).balanced_impl
    simp only [Impl.insert!, Impl.contains]
    split
    · next h => rw [w2c3_sbL bl hr, il]; simp only [h, Impl.size_inner]; split <;> omega
    · next h => rw [w2c3_sbR hl br, ir]; simp only [h, Impl.size_inner]; split <;> omega
    · next h => simp [h, Impl.size_inner]
theorem w2c3_cti {α : Type w2u} {β : α → Type w2v} [Ord α] {t : Impl α β} (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert! k v).1 = t.contains k := by
  have := w2c3_isz k v t h.balanced
  have hs : Impl.containsThenInsert!.size t = t.size := by cases t <;> rfl
  simp only [Impl.containsThenInsert!, hs, this]
  by_cases hc : t.contains k <;> simp [hc]
theorem w2c3_dl {α : Type w2u} {β : α → Type w2v} [Ord α] [TransOrd α] {m₁ m₂ : Impl α β} (h₁ : m₁.WF) {k : α}
    (h : m₁.contains k = false) : (m₁.diff m₂ h₁.balanced).contains k = false := by
  letI : BEq α := beqOfOrd
  have hw : (m₁.diff m₂ h₁.balanced).WF := Impl.WF.diff (h₁ := h₁)
  rw [Impl.contains_eq_containsKey hw.ordered]
  rw [Impl.contains_eq_containsKey h₁.ordered] at h
  rw [Std.Internal.List.containsKey_eq_false_iff] at h ⊢
  intro b hb
  apply h
  have sub : ∀ g : (a : α) × β a → Bool, b ∈ m₁.toListModel.filter g → b ∈ m₁.toListModel :=
    fun g hg => (List.mem_filter.1 hg).1
  revert hb
  unfold Impl.diff
  split
  · rw [Impl.toListModel_filter]; exact sub _
  · intro hb; exact sub _ ((Impl.toListModel_eraseManyEntries_impl h₁).mem_iff.1 hb)
theorem w2c3_ccong {α : Type w2u} {β : α → Type w2v} [Ord α] [TransOrd α] {k k' : α} (hk : compare k k' = .eq) :
    ∀ t : Impl α β, t.contains k = t.contains k'
  | .leaf => rfl
  | .inner _ ky _ l r => by
    have e : compare k ky = compare k' ky := Std.TransCmp.congr_left hk
    simp only [Impl.contains, e, w2c3_ccong hk l, w2c3_ccong hk r]
theorem w2c3_cmem {α : Type w2u} {β : α → Type w2v} [Ord α] {k : α} :
    ∀ t : Impl α β, t.contains k = true → ∃ x ∈ t.toListModel, compare k x.1 = .eq
  | .leaf, h => by simp [Impl.contains] at h
  | .inner _ ky y l r, h => by
    simp only [Impl.contains] at h
    split at h
    · obtain ⟨x, hx, e⟩ := w2c3_cmem l h; exact ⟨x, by simp [Impl.toListModel_inner, hx], e⟩
    · obtain ⟨x, hx, e⟩ := w2c3_cmem r h; exact ⟨x, by simp [Impl.toListModel_inner, hx], e⟩
    · exact ⟨⟨ky, y⟩, by simp [Impl.toListModel_inner], by assumption⟩
theorem w2c3_dr {α : Type w2u} {β : α → Type w2v} [Ord α] [TransOrd α] {m₁ m₂ : Impl α β} (h₁ : m₁.WF) {k : α}
    (h : m₂.contains k) : (m₁.diff m₂ h₁.balanced).contains k = false := by
  letI : BEq α := beqOfOrd
  have hw : (m₁.diff m₂ h₁.balanced).WF := Impl.WF.diff (h₁ := h₁)
  rw [Impl.contains_eq_containsKey hw.ordered]
  rw [Std.Internal.List.containsKey_eq_false_iff]
  intro b hb
  cases hkb : (k == b.1)
  · rfl
  have ekb : compare k b.1 = .eq := Std.LawfulBEqCmp.compare_eq_iff_beq.mpr hkb
  exfalso
  revert hb
  unfold Impl.diff
  split
  · rw [Impl.toListModel_filter]
    intro hb
    have := (List.mem_filter.1 hb).2
    rw [← w2c3_ccong ekb m₂, h] at this
    simp at this
  · intro hb
    have := (List.mem_filter.1 ((Impl.toListModel_eraseManyEntries_impl h₁).mem_iff.1 hb)).2
    obtain ⟨x, hx, e⟩ := w2c3_cmem m₂ h
    have ebx : compare b.1 x.1 = .eq := Std.TransCmp.eq_trans (Std.OrientedCmp.eq_symm ekb) e
    have : (List.map Sigma.fst m₂.toListModel).contains b.1 = true := by
      rw [List.contains_iff_exists_mem_beq]
      exact ⟨x.1, List.mem_map_of_mem hx, Std.LawfulBEqCmp.compare_eq_iff_beq.mp ebx⟩
    simp_all

/-! ## From `checks/W2c4Hand.lean` -/
namespace W2c4
open Std.PRange
-- Rxc finiteness from Rxi finiteness (RangeDepBHand).
theorem rxc_of_rxi {α : Type u} [UpwardEnumerable α] [LE α] [Rxi.IsAlwaysFinite α] :
    Rxc.IsAlwaysFinite α where
  finite init hi := by
    obtain ⟨n, hn⟩ := Rxi.IsAlwaysFinite.finite init; exact ⟨n, by simp [hn]⟩
theorem rxo_of_rxi {α : Type u} [UpwardEnumerable α] [LT α] [Rxi.IsAlwaysFinite α] :
    Rxo.IsAlwaysFinite α where
  finite init hi := by
    obtain ⟨n, hn⟩ := Rxi.IsAlwaysFinite.finite init; exact ⟨n, by simp [hn]⟩
-- Rxi finiteness from a lawful size function (RangeDepBHand).
theorem rxi_of_hasSize {α : Type u} [UpwardEnumerable α] [Rxi.HasSize α]
    [LawfulUpwardEnumerable α] [Rxi.LawfulHasSize α] : Rxi.IsAlwaysFinite α where
  finite init := by
    induction h : Rxi.HasSize.size init generalizing init with
    | zero => have := Rxi.size_pos (lo := init); omega
    | succ k ih =>
      cases hs : succ? init with
      | none => exact ⟨1, by rw [UpwardEnumerable.succMany?_one, hs]⟩
      | some x =>
        have := Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some init x hs
        obtain ⟨n, hn⟩ := ih x (by omega)
        exact ⟨n + 1, by
          rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs]; simpa using hn⟩
-- Rxc finiteness from LawfulUpwardEnumerable + LawfulUpwardEnumerableLE: the successor of hi
-- cannot be ≤ hi (no cycles), so the chain from init leaves the range one step after hi.
theorem rxc_of_lle {α : Type u} [UpwardEnumerable α] [LE α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] : Rxc.IsAlwaysFinite α where
  finite init hi := by
    by_cases h0 : init ≤ hi
    · obtain ⟨k, hk⟩ := (LawfulUpwardEnumerableLE.le_iff init hi).1 h0
      refine ⟨k + 1, ?_⟩
      rw [LawfulUpwardEnumerable.succMany?_add_one, hk]
      show (succ? hi).elim True (fun x => ¬ x ≤ hi)
      cases hs : succ? hi with
      | none => trivial
      | some x =>
        intro hx
        obtain ⟨j, hj⟩ := (LawfulUpwardEnumerableLE.le_iff x hi).1 hx
        apply LawfulUpwardEnumerable.ne_of_lt hi hi _ rfl
        refine ⟨j, ?_⟩
        rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs]; exact hj
    · exact ⟨0, by rw [LawfulUpwardEnumerable.succMany?_zero]; exact h0⟩
theorem rxo_of_llt {α : Type u} [UpwardEnumerable α] [LT α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] : Rxo.IsAlwaysFinite α where
  finite init hi := by
    by_cases h0 : init < hi
    · obtain ⟨k, hk⟩ := (LawfulUpwardEnumerableLT.lt_iff init hi).1 h0
      refine ⟨k + 1, ?_⟩
      rw [hk]
      show ¬ hi < hi
      intro hx
      exact LawfulUpwardEnumerable.ne_of_lt hi hi ((LawfulUpwardEnumerableLT.lt_iff hi hi).1 hx) rfl
    · exact ⟨0, by rw [LawfulUpwardEnumerable.succMany?_zero]; exact h0⟩
theorem nat_not_rxi : ¬ Rxi.IsAlwaysFinite Nat := fun h => by
  obtain ⟨n, hn⟩ := h.finite 0; cases hn
/-! UBad (RangeDepBHand): one point, succ? = none but succMany? 1 = some; ≤ and < always true.
Every class except LawfulUpwardEnumerable holds, incl. the Rxc/Rxo/Rxi sizes (size 1). -/
structure UBad where
deriving DecidableEq
instance : UpwardEnumerable UBad where
  succ? _ := none
  succMany? n _ := if n ≤ 1 then some ⟨⟩ else none
theorem UBad.not_lue : ¬ LawfulUpwardEnumerable UBad := fun h => by
  have := h.succMany?_add_one 0 ⟨⟩; cases this
instance : Rxi.IsAlwaysFinite UBad := ⟨fun _ => ⟨2, rfl⟩⟩
instance : LE UBad := ⟨fun _ _ => True⟩
instance : LT UBad := ⟨fun _ _ => True⟩
instance : DecidableLE UBad := fun _ _ => instDecidableTrue
instance : DecidableLT UBad := fun _ _ => instDecidableTrue
instance : Least? UBad := ⟨some ⟨⟩⟩
instance : LawfulUpwardEnumerableLE UBad := ⟨fun _ _ => ⟨fun _ => ⟨0, rfl⟩, fun _ => trivial⟩⟩
instance : LawfulUpwardEnumerableLT UBad := ⟨fun _ _ => ⟨fun _ => ⟨0, rfl⟩, fun _ => trivial⟩⟩
instance : Rxi.HasSize UBad := ⟨fun _ => 1⟩
instance : Rxi.LawfulHasSize UBad where
  size_eq_one_of_succ?_eq_none _ _ := rfl
  size_eq_succ_of_succ?_eq_some _ _ h := by cases h
instance : Rxc.HasSize UBad := ⟨fun _ _ => 1⟩
instance : Rxc.LawfulHasSize UBad where
  size_eq_zero_of_not_le _ _ h := (h trivial).elim
  size_eq_one_of_succ?_eq_none _ _ _ _ := rfl
  size_eq_succ_of_succ?_eq_some _ _ _ _ h := by cases h
instance : Rxo.HasSize UBad := ⟨fun _ _ => 1⟩
instance : Rxo.LawfulHasSize UBad where
  size_eq_zero_of_not_le _ _ h := (h trivial).elim
  size_eq_one_of_succ?_eq_none _ _ _ _ := rfl
  size_eq_succ_of_succ?_eq_some _ _ _ _ h := by cases h
instance : Rxc.IsAlwaysFinite UBad := rxc_of_rxi
instance : Rxo.IsAlwaysFinite UBad := rxo_of_rxi
/-! UF: one point, succ? = none (lawful), ≤ and < always false. LawfulUpwardEnumerableLE fails
(pt reaches itself in 0 steps); everything else holds, sizes 0. -/
structure UF where
instance : UpwardEnumerable UF where
  succ? _ := none
  succMany? n _ := if n = 0 then some ⟨⟩ else none
instance : LawfulUpwardEnumerable UF where
  ne_of_lt _ _ h := by obtain ⟨n, hn⟩ := h; cases hn
  succMany?_zero _ := rfl
  succMany?_add_one n _ := by
    show (if n + 1 = 0 then _ else _) = Option.bind (if n = 0 then _ else _) _
    by_cases h : n = 0 <;> simp [h] <;> rfl
theorem UF.not_lle [LE UF] (hle : ∀ a b : UF, ¬ a ≤ b) : ¬ LawfulUpwardEnumerableLE UF := fun h =>
  hle ⟨⟩ ⟨⟩ ((h.le_iff ⟨⟩ ⟨⟩).2 ⟨0, rfl⟩)
instance : LE UF := ⟨fun _ _ => False⟩
instance : LT UF := ⟨fun _ _ => False⟩
instance : DecidableLE UF := fun _ _ => instDecidableFalse
instance : DecidableLT UF := fun _ _ => instDecidableFalse
instance : Least? UF := ⟨some ⟨⟩⟩
instance : LawfulUpwardEnumerableLT UF := ⟨fun _ _ => ⟨False.elim, fun ⟨_, h⟩ => by cases h⟩⟩
instance : Rxc.IsAlwaysFinite UF := ⟨fun _ _ => ⟨0, id⟩⟩
instance : Rxo.IsAlwaysFinite UF := ⟨fun _ _ => ⟨0, id⟩⟩
instance : Rxc.HasSize UF := ⟨fun _ _ => 0⟩
instance : Rxc.LawfulHasSize UF where
  size_eq_zero_of_not_le _ _ _ := rfl
  size_eq_one_of_succ?_eq_none _ _ h _ := h.elim
  size_eq_succ_of_succ?_eq_some _ _ _ h _ := h.elim
theorem UF.not_lle' : ¬ LawfulUpwardEnumerableLE UF := UF.not_lle (fun _ _ h => h)
/-! UT: like UF but < always true: LawfulUpwardEnumerableLT fails; Rxo size 1. -/
structure UT where
instance : UpwardEnumerable UT where
  succ? _ := none
  succMany? n _ := if n = 0 then some ⟨⟩ else none
instance : LawfulUpwardEnumerable UT where
  ne_of_lt _ _ h := by obtain ⟨n, hn⟩ := h; cases hn
  succMany?_zero _ := rfl
  succMany?_add_one n _ := by
    show (if n + 1 = 0 then _ else _) = Option.bind (if n = 0 then _ else _) _
    by_cases h : n = 0 <;> simp [h] <;> rfl
instance : LT UT := ⟨fun _ _ => True⟩
instance : DecidableLT UT := fun _ _ => instDecidableTrue
instance : Least? UT := ⟨some ⟨⟩⟩
theorem UT.not_llt : ¬ LawfulUpwardEnumerableLT UT := fun h => by
  obtain ⟨n, hn⟩ := (h.lt_iff ⟨⟩ ⟨⟩).1 trivial; cases hn
instance : Rxo.IsAlwaysFinite UT := ⟨fun _ _ => ⟨1, trivial⟩⟩
instance : Rxo.HasSize UT := ⟨fun _ _ => 1⟩
instance : Rxo.LawfulHasSize UT where
  size_eq_zero_of_not_le _ _ h := (h trivial).elim
  size_eq_one_of_succ?_eq_none _ _ _ _ := rfl
  size_eq_succ_of_succ?_eq_some _ _ _ _ h := by cases h
/-! Two-size trick for the LawfulHasSize rows: NZ7/NZ8 (Nat copies) and T2a/T2b (two-point copies)
differ only in their constant size functions (7 vs 8), so the iterator lengths agree by rfl. -/
def NZ7 := Nat
def NZ8 := Nat
instance : LE NZ7 := inferInstanceAs (LE Nat)
instance : LT NZ7 := inferInstanceAs (LT Nat)
instance : DecidableLE NZ7 := inferInstanceAs (DecidableLE Nat)
instance : DecidableLT NZ7 := inferInstanceAs (DecidableLT Nat)
instance : UpwardEnumerable NZ7 := inferInstanceAs (UpwardEnumerable Nat)
instance : Least? NZ7 := inferInstanceAs (Least? Nat)
instance : LawfulUpwardEnumerable NZ7 := inferInstanceAs (LawfulUpwardEnumerable Nat)
instance : LawfulUpwardEnumerableLE NZ7 := inferInstanceAs (LawfulUpwardEnumerableLE Nat)
instance : LawfulUpwardEnumerableLT NZ7 := inferInstanceAs (LawfulUpwardEnumerableLT Nat)
instance : Rxc.IsAlwaysFinite NZ7 := inferInstanceAs (Rxc.IsAlwaysFinite Nat)
instance : Rxo.IsAlwaysFinite NZ7 := inferInstanceAs (Rxo.IsAlwaysFinite Nat)
instance : Rxc.HasSize NZ7 := ⟨fun _ _ => 7⟩
instance : Rxo.HasSize NZ7 := ⟨fun _ _ => 7⟩
instance : LE NZ8 := inferInstanceAs (LE Nat)
instance : LT NZ8 := inferInstanceAs (LT Nat)
instance : DecidableLE NZ8 := inferInstanceAs (DecidableLE Nat)
instance : DecidableLT NZ8 := inferInstanceAs (DecidableLT Nat)
instance : UpwardEnumerable NZ8 := inferInstanceAs (UpwardEnumerable Nat)
instance : Least? NZ8 := inferInstanceAs (Least? Nat)
instance : LawfulUpwardEnumerable NZ8 := inferInstanceAs (LawfulUpwardEnumerable Nat)
instance : LawfulUpwardEnumerableLE NZ8 := inferInstanceAs (LawfulUpwardEnumerableLE Nat)
instance : LawfulUpwardEnumerableLT NZ8 := inferInstanceAs (LawfulUpwardEnumerableLT Nat)
instance : Rxc.IsAlwaysFinite NZ8 := inferInstanceAs (Rxc.IsAlwaysFinite Nat)
instance : Rxo.IsAlwaysFinite NZ8 := inferInstanceAs (Rxo.IsAlwaysFinite Nat)
instance : Rxc.HasSize NZ8 := ⟨fun _ _ => 8⟩
instance : Rxo.HasSize NZ8 := ⟨fun _ _ => 8⟩
-- T2 (RangeDepBHand): two points false → true, lawful and Rxi-finite.
structure T2 where
  b : Bool
instance : UpwardEnumerable T2 where
  succ? a := if a.b then none else some ⟨true⟩
theorem T2.succMany?_add_two (n : Nat) (a : T2) : succMany? (n + 2) a = none := by
  induction n with
  | zero => obtain ⟨_ | _⟩ := a <;> rfl
  | succ n ih => show (succMany? (n + 2) a).bind succ? = none; rw [ih]; rfl
theorem T2.ueLT_iff' {a b : T2} : UpwardEnumerable.LT a b ↔ succ? a = some b := by
  constructor
  · rintro ⟨_ | n, h⟩
    · exact h
    · rw [T2.succMany?_add_two] at h; cases h
  · intro h; exact ⟨0, h⟩
instance : LawfulUpwardEnumerable T2 where
  ne_of_lt a b h := by
    rw [T2.ueLT_iff'] at h; intro e; subst e
    obtain ⟨_ | _⟩ := a <;> cases h
  succMany?_zero _ := rfl
  succMany?_add_one _ _ := rfl
instance : Rxi.IsAlwaysFinite T2 := ⟨fun a => ⟨2, T2.succMany?_add_two 0 a⟩⟩
def T2a := T2
def T2b := T2
instance : UpwardEnumerable T2a := inferInstanceAs (UpwardEnumerable T2)
instance : LawfulUpwardEnumerable T2a := inferInstanceAs (LawfulUpwardEnumerable T2)
instance : Rxi.IsAlwaysFinite T2a := inferInstanceAs (Rxi.IsAlwaysFinite T2)
instance : Least? T2a := ⟨some (⟨false⟩ : T2)⟩
instance : Rxi.HasSize T2a := ⟨fun _ => 7⟩
instance : UpwardEnumerable T2b := inferInstanceAs (UpwardEnumerable T2)
instance : LawfulUpwardEnumerable T2b := inferInstanceAs (LawfulUpwardEnumerable T2)
instance : Rxi.IsAlwaysFinite T2b := inferInstanceAs (Rxi.IsAlwaysFinite T2)
instance : Least? T2b := ⟨some (⟨false⟩ : T2)⟩
instance : Rxi.HasSize T2b := ⟨fun _ => 8⟩
/-! Iterator monads: P3.CM (bind-counting, not lawful) lifts lawfully to Id by forgetting the count. -/
theorem cm_not_lawful : ¬ LawfulMonad P3.CM := fun h => by
  have := h.pure_bind (0 : Nat) (fun _ => (pure 0 : P3.CM Nat))
  exact absurd (congrArg Prod.fst this) (by decide)
structure CW (α : Type) where
  v : α
instance : Monad CW where
  pure a := ⟨a⟩
  bind x f := f x.v
instance cwLawful : LawfulMonad CW := LawfulMonad.mk'
  (id_map := fun _ => rfl) (pure_bind := fun _ _ => rfl) (bind_assoc := fun _ _ _ => rfl)
instance : MonadLift P3.CM CW := ⟨fun x => ⟨x.2⟩⟩
instance : LawfulMonadLiftT P3.CM CW where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
/-! List models. PB: lawful Nat compare, BEq = same parity (TransOrd holds, LawfulBEqOrd fails).
KC: compare eq iff same half; two evens compare as Nat; otherwise lt (not oriented); BEq from compare. -/
structure PB where n : Nat deriving DecidableEq, Inhabited
instance : Ord PB := ⟨fun a b => compare a.n b.n⟩
instance : BEq PB := ⟨fun a b => a.n % 2 == b.n % 2⟩
instance : Std.TransOrd PB where
  eq_swap {a b} := Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering)) (a := a.n) (b := b.n)
  isLE_trans {a b c} h1 h2 := Std.TransCmp.isLE_trans (cmp := (compare : Nat → Nat → Ordering)) (a := a.n) (b := b.n) (c := c.n) h1 h2
theorem PB.notLBO : ¬ Std.LawfulBEqOrd PB := fun h => by
  have := h.compare_eq_iff_beq (a := ⟨0⟩) (b := ⟨2⟩)
  exact absurd this (by decide)
def kcmp (a b : Nat) : Ordering :=
  if a / 2 = b / 2 then .eq else if a % 2 = 0 ∧ b % 2 = 0 then compare a b else .lt
structure KC where n : Nat deriving DecidableEq, Inhabited
instance : Ord KC := ⟨fun a b => kcmp a.n b.n⟩
instance : BEq KC := ⟨fun a b => kcmp a.n b.n == .eq⟩
instance : Std.LawfulBEqOrd KC := ⟨fun {_ _} => by simp [compare, BEq.beq]⟩
theorem KC.notTrans : ¬ Std.TransOrd KC := fun h => by
  have := h.eq_swap (a := ⟨1⟩) (b := ⟨2⟩)
  exact absurd this (by decide)
/-! minKey?/maxKey? depend only on the key sequence; non-Const modifyKey keeps it (LawfulBEq). -/
theorem fold_fst {α : Type u} {β : α → Type v} (g : ((a : α) × β a) → ((a : α) × β a) → ((a : α) × β a))
    (hg : ∀ a b a' b', a.1 = a'.1 → b.1 = b'.1 → (g a b).1 = (g a' b').1) :
    ∀ (as bs : List ((a : α) × β a)) (a b : (a : α) × β a), a.1 = b.1 →
      as.map Sigma.fst = bs.map Sigma.fst → (as.foldl g a).1 = (bs.foldl g b).1
  | [], [], _, _, h, _ => h
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | x :: as, y :: bs, a, b, h, h' => by
    have h' := List.cons.inj h'
    exact fold_fst g hg as bs _ _ (hg _ _ _ _ h h'.1) h'.2
theorem mk_congr {α : Type u} {β : α → Type v} {o : Ord α} (l l' : List ((a : α) × β a))
    (h : l.map Sigma.fst = l'.map Sigma.fst) : Std.Internal.List.minKey? l = Std.Internal.List.minKey? l' := by
  unfold Std.Internal.List.minKey? Std.Internal.List.minEntry?
  match l, l', h with
  | [], [], _ => rfl
  | [], _ :: _, h => simp at h
  | _ :: _, [], h => simp at h
  | a :: as, b :: bs, h =>
    have h := List.cons.inj h
    show Option.map _ (some _) = Option.map _ (some _)
    simp only [Option.map_some, Option.some.injEq]
    refine fold_fst _ ?_ as bs a b h.1 h.2
    intro a b a' b' h1 h2
    show (if (compare a.1 b.1).isLE then a else b).1 = (if (compare a'.1 b'.1).isLE then a' else b').1
    rw [h1, h2]; split <;> assumption
theorem keys_rep {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] (k : α) (v : β k) :
    ∀ l : List ((a : α) × β a), (Std.Internal.List.replaceEntry k v l).map Sigma.fst = l.map Sigma.fst
  | [] => rfl
  | ⟨k', v'⟩ :: l => by
    rw [Std.Internal.List.replaceEntry_cons]
    split
    · rename_i hb; simp [eq_of_beq hb]
    · simp [keys_rep k v l]
theorem keys_mod {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] (k : α) (f : β k → β k)
    (l : List ((a : α) × β a)) : (Std.Internal.List.modifyKey k f l).map Sigma.fst = l.map Sigma.fst := by
  unfold Std.Internal.List.modifyKey
  split
  · rfl
  · exact keys_rep _ _ _
/-- A loop implementation that ignores the iterator and returns the initial value (not lawful). -/
def bogusLoop {α β : Type} {m : Type → Type} [Iterator α m β] {n : Type → Type} [Monad n] :
    IteratorLoop α m n := ⟨fun _ _ _ _ init _ => pure init⟩
open Std.Iterators.Types in
theorem fold1 : Std.Iter.fold (fun a b => a + b) 0 [1].iter = 1 := by rw [← Std.Iter.foldl_toList]; simp
theorem foldM1 : Std.Iter.foldM (fun a b => (pure (a + b) : Id Nat)) 0 [1].iter = pure 1 := by
  rw [← Std.Iter.foldlM_toList]; simp
theorem forIn1 : forIn [1].iter 0 (fun b a => (pure (.yield (a + b)) : Id (ForInStep Nat))) = pure 1 := by
  rw [← Std.Iter.forIn_toList]; simp
theorem fold1M : Std.IterM.fold (fun a b => a + b) 0 ([1].iterM Id) = pure 1 := by
  rw [← Std.IterM.foldl_toList]; simp
theorem foldM1M : Std.IterM.foldM (fun a b => (pure (a + b) : Id Nat)) 0 ([1].iterM Id) = pure 1 := by
  rw [← Std.IterM.foldlM_toList]; simp
theorem forIn1M : forIn ([1].iterM Id) 0 (fun b a => (pure (.yield (a + b)) : Id (ForInStep Nat))) = pure 1 := by
  rw [← Std.IterM.forIn_toList]; simp
/-- Unlawful loop in StateM Nat: sets the state to 5. -/
def bogusS : Std.IteratorLoop (Std.Iterators.Types.ListIterator Nat) (StateM Nat) (StateM Nat) := ⟨fun _ _ _ _ init _ => do set 5; pure init⟩
theorem dr1 : (([1].iterM (StateM Nat)).drain.run 0) = ((), 0) := by
  rw [Std.IterM.drain_eq_map_toList]; simp; rfl
end W2c4
open W2c4 Std.Iterators.Types
set_option maxHeartbeats 400000

/-! ## From `checks/W2c5Hand.lean` -/
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

/-! ## From `checks/W3c0Hand.lean` -/
/-! # W3c0 helpers -/
-- helper: 16 buckets with the given bucket at index 1 (W3c0 copy of the W1c2 helper)
abbrev w3c0g16 {α : Type u} {β : α → Type v} (b : AssocList α β) : Array (AssocList α β) :=
  #[.nil, b, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil]
-- helper: dependent alter on a literal raw map (copy of calter_eval for Raw₀.alter)
theorem w3c0_alter_eval {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulBEq α] {s : Nat}
    {bs : Array (AssocList α β)} {h : 0 < bs.size} (a : α) (f : Option (β a) → Option (β a)) (hsz : Pow2 bs.size) :
    Raw₀.alter (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a f =
      if (bs[ix bs a]'(Nat.mod_lt _ h)).contains a then
        ⟨⟨if (AssocList.alter a f (bs[ix bs a]'(Nat.mod_lt _ h))).contains a then s else s - 1,
          bs.set (ix bs a) (AssocList.alter a f (bs[ix bs a]'(Nat.mod_lt _ h))) (Nat.mod_lt _ h)⟩,
          by simpa using h⟩
      else match f none with
        | none => ⟨⟨s, bs⟩, h⟩
        | some b => Raw₀.expandIfNecessary ⟨⟨s + 1, bs.set (ix bs a)
            (AssocList.cons a b (bs[ix bs a]'(Nat.mod_lt _ h))) (Nat.mod_lt _ h)⟩, by simpa using h⟩ := by
  unfold Raw₀.alter; dsimp only; rw [mkIdx_eq _ _ _ hsz]
  simp only [Array.ugetElem_eq_getElem, Array.uset_eq_set, idx_lt h _ hsz, Array.set_set]
  rfl
namespace W3c0
export W2c0 (cz_hs)
export W2c0 (cz_wf)
end W3c0
namespace W3c0
-- alter with a `some` result keeps a found key in its bucket (needs only reflexivity)
theorem al_cont {α : Type u} {β : Type v} [BEq α] [ReflBEq α] (a : α) (f : Option β → Option β) :
    ∀ (l : AssocList α (fun _ => β)), l.contains a = true → (f (l.get? a)).isSome = true →
      (AssocList.Const.alter a f l).contains a = true
  | .nil, h, _ => by simp [AssocList.contains] at h
  | .cons k v l, h, h' => by
    unfold AssocList.Const.alter
    by_cases hk : (k == a) = true
    · simp only [hk, ite_true]
      simp only [AssocList.get?, hk, Bool.cond_true] at h'
      revert h'; cases f (some v) <;> simp [AssocList.contains]
    · simp only [hk, Bool.false_eq_true, ite_false, AssocList.contains, Bool.false_or]
      simp only [AssocList.contains, hk, Bool.false_or] at h
      simp only [AssocList.get?, hk, Bool.cond_false] at h'
      exact al_cont a f l h h'
theorem r0c_sa {α : Type u} {β : Type v} [BEq α] [Hashable α] [ReflBEq α] (m : Raw₀ α (fun _ => β)) (k : α)
    (f : Option β → Option β) (h₁ : m.contains k = true) (h₂ : (f (Raw₀.Const.get? m k)).isSome = true) :
    (Raw₀.Const.alter m k f).1.size = m.1.size := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.Const.alter
  unfold Raw₀.contains at h₁; unfold Raw₀.Const.get? at h₂
  dsimp only at h₁ h₂ ⊢
  rw [if_pos h₁]
  dsimp only
  rw [if_pos (al_cont _ _ _ h₁ h₂)]
-- dependent version of al_cont
theorem al_contd {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] (a : α) (f : Option (β a) → Option (β a)) :
    ∀ (l : AssocList α β), l.contains a = true → (f (l.getCast? a)).isSome = true →
      (AssocList.alter a f l).contains a = true
  | .nil, h, _ => by simp [AssocList.contains] at h
  | .cons k v l, h, h' => by
    unfold AssocList.alter
    by_cases hk : (k == a) = true
    · simp only [hk, dite_true]
      simp only [AssocList.getCast?, hk, dite_true] at h'
      revert h'; cases f _ <;> simp [AssocList.contains]
    · simp only [hk, Bool.false_eq_true, dite_false, AssocList.contains, Bool.false_or]
      simp only [AssocList.contains, hk, Bool.false_or] at h
      simp only [AssocList.getCast?, hk, Bool.false_eq_true, dite_false] at h'
      exact al_contd a f l h h'
theorem r0_sa {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k : α)
    (f : Option (β k) → Option (β k)) (h₁ : m.contains k = true) (h₂ : (f (m.get? k)).isSome = true) :
    (m.alter k f).1.size = m.1.size := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.alter
  unfold Raw₀.contains at h₁; unfold Raw₀.get? at h₂
  dsimp only at h₁ h₂ ⊢
  rw [if_pos h₁]
  dsimp only
  rw [if_pos (al_contd _ _ _ h₁ h₂)]
theorem drc_sa {α : Type u} {β : Type v} [BEq α] [Hashable α] [EquivBEq α] (m : DHashMap.Raw α (fun _ => β)) (k : α)
    (f : Option β → Option β) (h : m.contains k = true) (h' : (f (DHashMap.Raw.Const.get? m k)).isSome = true) :
    (DHashMap.Raw.Const.alter m k f).size = m.size := by
  simp only [DHashMap.Raw.contains] at h
  by_cases hb : 0 < m.buckets.size
  · simp only [hb, dite_true] at h
    simp only [DHashMap.Raw.Const.get?, hb, dite_true] at h'
    simp only [DHashMap.Raw.Const.alter, hb, dite_true, DHashMap.Raw.size]
    exact r0c_sa ⟨m, hb⟩ k f h h'
  · simp [hb] at h
theorem dr_sa {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k : α)
    (f : Option (β k) → Option (β k)) (h : k ∈ m) (h' : (f (m.get? k)).isSome = true) :
    (m.alter k f).size = m.size := by
  simp only [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains] at h
  by_cases hb : 0 < m.buckets.size
  · simp only [hb, dite_true] at h
    simp only [DHashMap.Raw.get?, hb, dite_true] at h'
    simp only [DHashMap.Raw.alter, hb, dite_true]
    exact r0_sa ⟨m, hb⟩ k f h h'
  · simp [hb] at h
end W3c0
namespace W3c0
section
variable {α : Type u} {γ : Type v}
-- getD-style lookups fall back when the bucket does not contain the key (no laws)
theorem a_cgetD (l : AssocList α (fun _ => γ)) [BEq α] (k : α) (fb : γ) (h : l.contains k = false) :
    l.getD k fb = fb := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.getD, h.1, cond_false]; exact ih h.2
theorem a_getKeyD {β : α → Type v} [BEq α] (l : AssocList α β) (k fb : α) (h : l.contains k = false) :
    l.getKeyD k fb = fb := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.getKeyD, h.1]; exact ih h.2
theorem a_getCastD {β : α → Type v} [BEq α] [LawfulBEq α] (l : AssocList α β) (k : α) (fb : β k)
    (h : l.contains k = false) : l.getCastD k fb = fb := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.getCastD, h.1]; exact ih h.2
theorem r0_cgetD [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (k : α) (fb : γ) (h : m.contains k = false) :
    Raw₀.Const.getD m k fb = fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.Const.getD; simp only [Array.ugetElem_eq_getElem]; exact a_cgetD _ _ _ h
theorem r0_getKeyD {β : α → Type v} [BEq α] [Hashable α] (m : Raw₀ α β) (k fb : α) (h : m.contains k = false) :
    m.getKeyD k fb = fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.getKeyD; simp only [Array.ugetElem_eq_getElem]; exact a_getKeyD _ _ _ h
theorem r0_getD {β : α → Type v} [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k : α) (fb : β k)
    (h : m.contains k = false) : m.getD k fb = fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.getD; simp only [Array.ugetElem_eq_getElem]; exact a_getCastD _ _ _ h
theorem dhc_gd [BEq α] [Hashable α] (m₁ m₂ : DHashMap α (fun _ => γ)) (k : α) (fb : γ) (h : ¬ k ∈ m₁) :
    DHashMap.Const.getD (m₁ \ m₂) k fb = fb :=
  r0_cgetD _ _ _ (raw0_diff_nc _ _ _ (Bool.eq_false_iff.mpr h))
theorem hs_gd [BEq α] [Hashable α] (m₁ m₂ : HashSet α) (k fb : α) (h : ¬ k ∈ m₁) :
    (m₁ \ m₂).getD k fb = fb :=
  r0_getKeyD _ _ _ (raw0_diff_nc _ _ _ (Bool.eq_false_iff.mpr h))
theorem drc_gd [BEq α] [Hashable α] (m₁ m₂ : DHashMap.Raw α (fun _ => γ)) (h₁ : m₁.WF) (k : α) (fb : γ)
    (h : ¬ k ∈ m₁) : DHashMap.Raw.Const.getD (m₁ \ m₂) k fb = fb := by
  obtain ⟨h', hc⟩ := dr_diff_nc m₁ m₂ k h₁.size_buckets_pos h
  unfold DHashMap.Raw.Const.getD; rw [dif_pos h']; exact r0_cgetD _ _ _ hc
theorem hsr_gd [BEq α] [Hashable α] (m₁ m₂ : HashSet.Raw α) (h₁ : m₁.WF) (k fb : α)
    (h : ¬ k ∈ m₁) : (m₁ \ m₂).getD k fb = fb := by
  obtain ⟨h', hc⟩ := dr_diff_nc m₁.inner.inner m₂.inner.inner k h₁.out.out.size_buckets_pos h
  show DHashMap.Raw.getKeyD (m₁.inner.inner \ m₂.inner.inner) k fb = fb
  unfold DHashMap.Raw.getKeyD; rw [dif_pos h']; exact r0_getKeyD _ _ _ hc
theorem hmr_gd [BEq α] [Hashable α] (m₁ m₂ : HashMap.Raw α γ) (h₁ : m₁.WF) (k : α) (fb : γ)
    (h : ¬ k ∈ m₁) : (m₁ \ m₂).getD k fb = fb := drc_gd m₁.inner m₂.inner h₁.out k fb h
end
theorem dr_gd {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulBEq α] (m₁ m₂ : DHashMap.Raw α β)
    (h₁ : m₁.WF) (k : α) (fb : β k) (h : ¬ k ∈ m₁) : (m₁ \ m₂).getD k fb = fb := by
  obtain ⟨h', hc⟩ := dr_diff_nc m₁ m₂ k h₁.size_buckets_pos h
  unfold DHashMap.Raw.getD; rw [dif_pos h']; exact r0_getD _ _ _ hc
end W3c0
namespace W3c0
-- inter_left without m₃.WF: both branches of Raw₀.inter only query m₁/m₂ (filter, or getEntry? while folding over m₃)
theorem r0_il {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ m₃ : Raw₀ α β) (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (e : m₁.1.Equiv m₂.1) :
    (m₁.inter m₃).1.Equiv (m₂.inter m₃).1 := by
  have w₁ := Raw.WF.out h₁
  have w₂ := Raw.WF.out h₂
  have hs : m₁.1.size = m₂.1.size := by rw [w₁.size_eq, w₂.size_eq]; exact e.1.length_eq
  unfold Raw₀.inter; rw [hs]; split
  · exact ⟨Raw₀.toListModel_filter.trans ((e.1.filter _).trans (Raw₀.toListModel_filter (m := m₂) (f := fun k _ => m₃.contains k)).symm)⟩
  · rw [Raw₀.interSmaller_eq_interSmallerₘ, Raw₀.interSmaller_eq_interSmallerₘ]
    refine ⟨(Raw₀.toListModel_interSmallerₘ _ _ w₁).trans (List.Perm.trans ?_ (Raw₀.toListModel_interSmallerₘ _ _ w₂).symm)⟩
    have : ∀ sofar k, Std.Internal.List.interSmallerFn (toListModel m₁.1.buckets) sofar k =
        Std.Internal.List.interSmallerFn (toListModel m₂.1.buckets) sofar k := by
      intro sofar k; simp only [Std.Internal.List.interSmallerFn, Std.Internal.List.getEntry?_of_perm w₁.distinct e.1]
    simp only [Std.Internal.List.interSmaller, this]; exact List.Perm.refl _
theorem dr_il {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ m₃ : DHashMap.Raw α β) (h₁ : m₁.WF) (h₂ : m₂.WF) (e : m₁.Equiv m₂) : (m₁.inter m₃).Equiv (m₂.inter m₃) := by
  by_cases h₃ : 0 < m₃.buckets.size
  · simp only [DHashMap.Raw.inter, h₁.size_buckets_pos, h₂.size_buckets_pos, h₃, dite_true]
    exact r0_il ⟨m₁, _⟩ ⟨m₂, _⟩ ⟨m₃, _⟩ h₁ h₂ e
  · simp only [DHashMap.Raw.inter, h₁.size_buckets_pos, h₂.size_buckets_pos, h₃, dite_true, dite_false]; exact e
end W3c0
open S1

/-! ## From `checks/W3c1Hand.lean` -/
set_option linter.unusedSimpArgs false
namespace W3c1
universe u4 v4
open Std Std.DHashMap.Internal HashInstHand
variable {α : Type u4} {β : Type v4} [BEq α] [Hashable α]
-- rfl unfoldings of the set-operation notations
theorem hs_un (m₁ m₂ : HashSet α) : m₁ ∪ m₂ = HashSet.union m₁ m₂ := rfl
theorem hs_in (m₁ m₂ : HashSet α) : m₁ ∩ m₂ = HashSet.inter m₁ m₂ := rfl
theorem hs_di (m₁ m₂ : HashSet α) : m₁ \ m₂ = HashSet.diff m₁ m₂ := rfl
theorem hsr_un (m₁ m₂ : HashSet.Raw α) : m₁ ∪ m₂ = HashSet.Raw.union m₁ m₂ := rfl
theorem hsr_in (m₁ m₂ : HashSet.Raw α) : m₁ ∩ m₂ = HashSet.Raw.inter m₁ m₂ := rfl
theorem hsr_di (m₁ m₂ : HashSet.Raw α) : m₁ \ m₂ = HashSet.Raw.diff m₁ m₂ := rfl
theorem hm_un (m₁ m₂ : HashMap α β) : m₁ ∪ m₂ = HashMap.union m₁ m₂ := rfl
theorem hm_in (m₁ m₂ : HashMap α β) : m₁ ∩ m₂ = HashMap.inter m₁ m₂ := rfl
theorem hm_di (m₁ m₂ : HashMap α β) : m₁ \ m₂ = HashMap.diff m₁ m₂ := rfl
theorem hmr_un (m₁ m₂ : HashMap.Raw α β) : m₁ ∪ m₂ = HashMap.Raw.union m₁ m₂ := rfl
theorem hmr_in (m₁ m₂ : HashMap.Raw α β) : m₁ ∩ m₂ = HashMap.Raw.inter m₁ m₂ := rfl
theorem hmr_di (m₁ m₂ : HashMap.Raw α β) : m₁ \ m₂ = HashMap.Raw.diff m₁ m₂ := rfl
theorem dm_un {γ : α → Type v4} (m₁ m₂ : DHashMap α γ) : m₁ ∪ m₂ = DHashMap.union m₁ m₂ := rfl
theorem dm_in {γ : α → Type v4} (m₁ m₂ : DHashMap α γ) : m₁ ∩ m₂ = DHashMap.inter m₁ m₂ := rfl
theorem dm_di {γ : α → Type v4} (m₁ m₂ : DHashMap α γ) : m₁ \ m₂ = DHashMap.diff m₁ m₂ := rfl
theorem dr_diff_nil {γ : α → Type v4} (s : Nat) (m : DHashMap.Raw α γ) :
    DHashMap.Raw.diff ⟨s, #[]⟩ m = m := by simp [DHashMap.Raw.diff]
theorem dr_inter_nil {γ : α → Type v4} (s : Nat) (m : DHashMap.Raw α γ) :
    DHashMap.Raw.inter ⟨s, #[]⟩ m = m := by simp [DHashMap.Raw.inter]
theorem dr_union_nil {γ : α → Type v4} (s : Nat) (m : DHashMap.Raw α γ) :
    DHashMap.Raw.union ⟨s, #[]⟩ m = m := by simp [DHashMap.Raw.union]
theorem dr_union_nil2 {γ : α → Type v4} (s : Nat) (m : DHashMap.Raw α γ) (h : 0 < m.buckets.size) :
    DHashMap.Raw.union m ⟨s, #[]⟩ = m := by simp [DHashMap.Raw.union, h]
theorem dgetD_eval {γ : α → Type v4} [LawfulBEq α] {s : Nat}
    {bs : Array (AssocList α γ)} {h : 0 < bs.size} (a : α) (fb : γ a) (hsz : Pow2 bs.size) :
    Raw₀.getD (⟨⟨s, bs⟩, h⟩ : Raw₀ α γ) a fb = (bs[ix bs a]'(Nat.mod_lt _ h)).getCastD a fb := by
  simp only [Raw₀.getD, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]
-- a raw ZH literal with a key in bucket 1 never finds anything
theorem zr_contains {γ : W1c5.ZH → Type v4} (s : Nat) (l : AssocList W1c5.ZH γ) (a : W1c5.ZH) :
    (⟨s, #[.nil, l]⟩ : DHashMap.Raw W1c5.ZH γ).contains a = false := by
  rw [HashInstHand.dr_contains_lit _ _ (by simp)]; exact W1c5.zh_contains _ _ _
theorem assoc_cget?_none {β : Type v4} (l : AssocList α (fun _ => β)) (k : α) (h : l.contains k = false) :
    l.get? k = none := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.get?, h.1, cond_false]; exact ih h.2
-- alter on an absent key with f none = none returns the map itself (no laws needed)
theorem r0_alter_same [LawfulBEq α] {γ : α → Type v4} (m : Raw₀ α γ) (k : α) (f : Option (γ k) → Option (γ k))
    (hc : m.contains k = false) (hs : (f (m.get? k)).isNone = true) : (m.alter k f).1.size = m.1.size := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  rw [contains_gen] at hc
  have hg : Raw₀.get? (⟨⟨s, bs⟩, h⟩ : Raw₀ α γ) k = none := by
    unfold Raw₀.get?; simp only [Array.ugetElem_eq_getElem]; exact assoc_getCast?_none _ _ hc
  rw [hg] at hs
  unfold Raw₀.alter; simp only [Array.ugetElem_eq_getElem, hc, Bool.false_eq_true, ite_false]
  split
  · rfl
  · rename_i e; rw [e] at hs; simp at hs
theorem r0c_alter_same (m : Raw₀ α (fun _ => β)) (k : α) (f : Option β → Option β)
    (hc : m.contains k = false) (hs : (f (Raw₀.Const.get? m k)).isNone = true) :
    (Raw₀.Const.alter m k f).1.size = m.1.size := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  rw [contains_gen] at hc
  have hg : Raw₀.Const.get? (⟨⟨s, bs⟩, h⟩ : Raw₀ α (fun _ => β)) k = none := by
    unfold Raw₀.Const.get?; simp only [Array.ugetElem_eq_getElem]; exact assoc_cget?_none _ _ hc
  rw [hg] at hs
  unfold Raw₀.Const.alter; simp only [Array.ugetElem_eq_getElem, hc, Bool.false_eq_true, ite_false]
  split
  · rfl
  · rename_i e; rw [e] at hs; simp at hs
theorem dhc_alter_same (m : DHashMap α (fun _ => β)) (k : α) (f : Option β → Option β) (h : ¬ k ∈ m)
    (h' : (f (DHashMap.Const.get? m k)).isNone = true) : (DHashMap.Const.alter m k f).size = m.size :=
  r0c_alter_same ⟨m.1, m.2.size_buckets_pos⟩ k f (by simpa [DHashMap.mem_iff_contains, DHashMap.contains] using h) h'
theorem hm_alter_same (m : HashMap α β) (k : α) (f : Option β → Option β) (h : ¬ k ∈ m)
    (h' : (f m[k]?).isNone = true) : (m.alter k f).size = m.size :=
  dhc_alter_same m.inner k f h h'
theorem r0g_wf : (⟨1, f16 (.cons (0 : Nat) (0 : Nat) .nil)⟩ : DHashMap.Raw Nat (fun _ => Nat)).WF :=
  dr_ins0 ▸ DHashMap.Raw.WF.insert .empty
theorem r0e_wf : (⟨0, nil16⟩ : DHashMap.Raw Nat (fun _ => Nat)).WF := by
  rw [← dr_empty (α := Nat)]; exact .empty
end W3c1
namespace W3c1
open Std Std.DHashMap.Internal HashInstHand
universe u2 v2
-- inter keeps every entry of a WF m₁ whose keys m₂ contains; m₂ needs no WF (port of the Probe2 HashSet.Raw proof)
theorem r0_inter_size {α : Type u2} {γ : α → Type v2} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : Raw₀ α γ) (h₁ : m₁.1.WF)
    (h : ∀ a, m₁.contains a = true → m₂.contains a = true) : (m₁.inter m₂).1.size = m₁.1.size := by
  obtain ⟨m₁, hb₁⟩ := m₁; obtain ⟨m₂, hb₂⟩ := m₂
  have w₁ : Raw.WFImp m₁ := Std.DHashMap.Internal.Raw.WF.out h₁
  have key' : ∀ p ∈ toListModel m₁.buckets, Raw₀.contains ⟨m₂, hb₂⟩ p.1 = true := by
    intro p hp
    apply h
    rw [Raw₀.contains_eq_containsKey w₁]
    exact Std.Internal.List.containsKey_of_mem hp
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) w₁
  rw [wr.size_eq, w₁.size_eq]
  unfold Raw₀.inter
  split
  · rw [(Raw₀.toListModel_filter).length_eq, List.filter_eq_self.mpr (fun p hp => key' p hp)]
  · rw [Raw₀.interSmaller_eq_interSmallerₘ, ((Raw₀.toListModel_interSmallerₘ ⟨_, hb₁⟩ m₂ w₁).trans
        (Std.Internal.List.interSmaller_perm_filter _ _ w₁.distinct)).length_eq,
        List.filter_eq_self.mpr (fun p hp => Probe2.raw0_contains_tlm ⟨_, hb₂⟩ _ (key' p hp))]
theorem dr_inter_size {α : Type u2} {γ : α → Type v2} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) (h : ∀ a, a ∈ m₁ → a ∈ m₂) : (m₁ ∩ m₂).size = m₁.size := by
  have hb₁ := h₁.size_buckets_pos
  show (DHashMap.Raw.inter m₁ m₂).size = m₁.size
  unfold DHashMap.Raw.inter; rw [dif_pos hb₁]; split
  · rename_i hb₂
    exact r0_inter_size ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ (fun a ha => by
      have := h a (by rw [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, dif_pos hb₁]; exact ha)
      rwa [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, dif_pos hb₂] at this)
  · rfl
theorem hmr_inter_size {α : Type u2} {β : Type v2} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : HashMap.Raw α β) (h₁ : m₁.WF) (h : ∀ a, a ∈ m₁ → a ∈ m₂) : (m₁ ∩ m₂).size = m₁.size :=
  dr_inter_size m₁.inner m₂.inner h₁.out h
end W3c1
namespace W3c1
open Std Std.DHashMap.Internal HashInstHand Std.Internal.List
universe u3 v3
section
variable {α : Type u3} {γ : α → Type v3} [BEq α] [Hashable α]
theorem r0_contains_congr [EquivBEq α] [LawfulHashable α] (m : Raw₀ α γ) {a b : α} (hab : (a == b) = true) :
    m.contains a = m.contains b := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have hh : hash a = hash b := hash_eq hab
  unfold Raw₀.contains; dsimp only
  simp only [hh, AssocList.contains_eq]
  exact containsKey_congr hab
theorem ck_filter [EquivBEq α] (l : List ((a : α) × γ a)) (P : (a : α) × γ a → Bool) (k : α)
    (hP : ∀ p ∈ l, (p.1 == k) = true → P p = false) : containsKey k (l.filter P) = false := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    have ih' := ih (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    rw [List.filter_cons]
    split
    · rename_i hp
      have : (p.1 == k) = false := by
        cases h : (p.1 == k)
        · rfl
        · rw [hP p List.mem_cons_self h] at hp; exact absurd hp (by simp)
      rw [containsKey_cons, this, ih']; rfl
    · exact ih'
theorem ck_eraseList_of_not [EquivBEq α] (l : List ((a : α) × γ a)) (ks : List α) (k : α)
    (hl : DistinctKeys l) (h : containsKey k l = false) : containsKey k (eraseList l ks) = false := by
  induction ks generalizing l with
  | nil => exact h
  | cons c ks ih =>
    exact ih (eraseKey c l) hl.eraseKey (by rw [containsKey_eraseKey hl, h]; simp)
theorem ck_eraseList_of_mem [EquivBEq α] (l : List ((a : α) × γ a)) (ks : List α) (k c : α)
    (hl : DistinctKeys l) (hc : c ∈ ks) (hck : (c == k) = true) : containsKey k (eraseList l ks) = false := by
  induction ks generalizing l with
  | nil => simp at hc
  | cons c' ks ih =>
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ck_eraseList_of_not _ ks k hl.eraseKey (containsKey_eraseKey_of_beq hl (BEq.symm hck))
    · exact ih (eraseKey c' l) hl.eraseKey hc'
-- diff with a WF m₁ drops every key that m₂ finds; m₂ needs no WF
theorem r0_diff_nc [EquivBEq α] [LawfulHashable α] (m₁ m₂ : Raw₀ α γ) (h₁ : m₁.1.WF) (k : α)
    (hk : m₂.contains k = true) : (m₁.diff m₂).contains k = false := by
  obtain ⟨m₁, hb₁⟩ := m₁; obtain ⟨m₂, hb₂⟩ := m₂
  have w₁ : Raw.WFImp m₁ := Std.DHashMap.Internal.Raw.WF.out h₁
  rw [Raw₀.contains_eq_containsKey (Std.DHashMap.Internal.Raw.WF.out (Raw₀.wf_diff₀ h₁)), Raw₀.diff_eq_diffₘ]
  unfold Raw₀.diffₘ
  split
  · rw [containsKey_of_perm Raw₀.toListModel_filterₘ]
    apply ck_filter
    intro p _ hp
    simp only [Bool.not_eq_false']
    rw [← Raw₀.contains_eq_containsₘ, r0_contains_congr _ hp]; exact hk
  · rw [Raw₀.eraseManyEntries_eq_eraseListₘ, containsKey_of_perm (Raw₀.toListModel_eraseListₘ w₁)]
    obtain ⟨p, hp, hpk⟩ := containsKey_eq_true_iff_exists_mem.mp (Probe2.raw0_contains_tlm ⟨m₂, hb₂⟩ k hk)
    exact ck_eraseList_of_mem _ _ k p.1 w₁.distinct (List.mem_map_of_mem hp) hpk
theorem dr_diff_nm [EquivBEq α] [LawfulHashable α] (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) (k : α)
    (hk : k ∈ m₂) : (m₁ \ m₂).WF ∧ ¬ k ∈ (m₁ \ m₂) := by
  have hb₁ := h₁.size_buckets_pos
  rw [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains] at hk
  split at hk
  · rename_i hb₂
    show (DHashMap.Raw.diff m₁ m₂).WF ∧ ¬ k ∈ DHashMap.Raw.diff m₁ m₂
    unfold DHashMap.Raw.diff; rw [dif_pos hb₁, dif_pos hb₂]
    refine ⟨Raw₀.wf_diff₀ h₁, ?_⟩
    rw [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, dif_pos (Raw₀.wf_diff₀ h₁).size_buckets_pos]
    simp only [Bool.not_eq_true]
    exact r0_diff_nc ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
  · exact absurd hk (by simp)
end
end W3c1
namespace W3c1
open Std Std.DHashMap.Internal HashInstHand Std.Internal.List
universe u5 v5
theorem gv_filter {α : Type u5} {β : Type v5} [BEq α] (l : List ((_ : α) × β)) (P : (_ : α) × β → Bool) (a : α)
    (hP : ∀ p ∈ l, (p.1 == a) = true → P p = true) : getValue? a (l.filter P) = getValue? a l := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    have ih' := ih (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    have hp := hP p List.mem_cons_self
    obtain ⟨k', v⟩ := p
    rw [List.filter_cons]
    by_cases hpa : (k' == a) = true
    · rw [if_pos (hp hpa)]; simp [getValue?, hpa]
    · have hpa' : (k' == a) = false := by simpa using hpa
      split <;> simp [getValue?, hpa', ih']
-- inter with a WF m₁ is a filter of m₁ that keeps every entry whose key is == a key found in m₂ (m₂ needs no WF)
theorem r0_inter_perm {α : Type u5} {γ : α → Type v5} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : Raw₀ α γ) (h₁ : m₁.1.WF) (k : α) (hk : m₂.contains k = true) :
    ∃ P : (a : α) × γ a → Bool, (toListModel (m₁.inter m₂).1.buckets).Perm ((toListModel m₁.1.buckets).filter P) ∧
      ∀ p : (a : α) × γ a, (p.1 == k) = true → P p = true := by
  obtain ⟨m₁, hb₁⟩ := m₁; obtain ⟨m₂, hb₂⟩ := m₂
  have w₁ : Raw.WFImp m₁ := Std.DHashMap.Internal.Raw.WF.out h₁
  unfold Raw₀.inter
  split
  · exact ⟨fun p => Raw₀.contains ⟨m₂, hb₂⟩ p.1, Raw₀.toListModel_filter, fun p hp => by
    show Raw₀.contains ⟨m₂, hb₂⟩ p.1 = true
    rw [r0_contains_congr _ hp]; exact hk⟩
  · refine ⟨fun p => containsKey p.1 (toListModel m₂.buckets), ?_, fun p hp => by
      show containsKey p.1 _ = true
      rw [containsKey_congr hp]; exact Probe2.raw0_contains_tlm ⟨m₂, hb₂⟩ k hk⟩
    rw [Raw₀.interSmaller_eq_interSmallerₘ]
    exact (Raw₀.toListModel_interSmallerₘ ⟨_, hb₁⟩ m₂ w₁).trans (interSmaller_perm_filter _ _ w₁.distinct)
theorem drc_inter_getD {α : Type u5} {β : Type v5} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : DHashMap.Raw α (fun _ => β)) (h₁ : m₁.WF) (k : α) (fb : β) (hk : k ∈ m₂) :
    DHashMap.Raw.Const.getD (m₁ ∩ m₂) k fb = DHashMap.Raw.Const.getD m₁ k fb := by
  have hb₁ := h₁.size_buckets_pos
  rw [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains] at hk
  split at hk
  · rename_i hb₂
    have e : m₁ ∩ m₂ = (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).1 := by
      show DHashMap.Raw.inter m₁ m₂ = _
      unfold DHashMap.Raw.inter; rw [dif_pos hb₁, dif_pos hb₂]
    have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
    obtain ⟨P, hperm, hP⟩ := r0_inter_perm ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
    rw [e]
    simp only [DHashMap.Raw.Const.getD, dif_pos (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).2, dif_pos hb₁]
    rw [Raw₀.Const.getD_eq_getValueD wr, Raw₀.Const.getD_eq_getValueD (Std.DHashMap.Internal.Raw.WF.out h₁),
      getValueD_of_perm wr.distinct hperm, getValueD_eq_getValue?, getValueD_eq_getValue?,
      gv_filter _ _ _ (fun p _ hp => hP p hp)]
  · exact absurd hk (by simp)
theorem gvc_filter {α : Type u5} {γ : α → Type v5} [BEq α] [LawfulBEq α] (l : List ((a : α) × γ a))
    (P : (a : α) × γ a → Bool) (a : α)
    (hP : ∀ p ∈ l, (p.1 == a) = true → P p = true) : getValueCast? a (l.filter P) = getValueCast? a l := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    have ih' := ih (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    have hp := hP p List.mem_cons_self
    obtain ⟨k', v⟩ := p
    rw [List.filter_cons]
    by_cases hpa : (k' == a) = true
    · rw [if_pos (hp hpa)]; simp [getValueCast?, hpa]
    · have hpa' : (k' == a) = false := by simpa using hpa
      split <;> simp [getValueCast?, hpa', ih']
theorem gk_filter {α : Type u5} {γ : α → Type v5} [BEq α] (l : List ((a : α) × γ a))
    (P : (a : α) × γ a → Bool) (a : α)
    (hP : ∀ p ∈ l, (p.1 == a) = true → P p = true) : getKey? a (l.filter P) = getKey? a l := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    have ih' := ih (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    have hp := hP p List.mem_cons_self
    obtain ⟨k', v⟩ := p
    rw [List.filter_cons]
    by_cases hpa : (k' == a) = true
    · rw [if_pos (hp hpa)]; simp [getKey?, hpa]
    · have hpa' : (k' == a) = false := by simpa using hpa
      split <;> simp [getKey?, hpa', ih']
theorem dr_inter_getD {α : Type u5} {γ : α → Type v5} [BEq α] [Hashable α] [LawfulBEq α]
    (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) (k : α) (fb : γ k) (hk : k ∈ m₂) :
    (m₁ ∩ m₂).getD k fb = m₁.getD k fb := by
  have hb₁ := h₁.size_buckets_pos
  rw [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains] at hk
  split at hk
  · rename_i hb₂
    have e : m₁ ∩ m₂ = (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).1 := by
      show DHashMap.Raw.inter m₁ m₂ = _
      unfold DHashMap.Raw.inter; rw [dif_pos hb₁, dif_pos hb₂]
    have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
    obtain ⟨P, hperm, hP⟩ := r0_inter_perm ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
    rw [e]
    simp only [DHashMap.Raw.getD, dif_pos (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).2, dif_pos hb₁]
    rw [Raw₀.getD_eq_getValueCastD wr, Raw₀.getD_eq_getValueCastD (Std.DHashMap.Internal.Raw.WF.out h₁),
      getValueCastD_of_perm wr.distinct hperm, getValueCastD_eq_getValueCast?, getValueCastD_eq_getValueCast?,
      gvc_filter _ _ _ (fun p _ hp => hP p hp)]
  · exact absurd hk (by simp)
theorem drk_inter_getKeyD {α : Type u5} {γ : α → Type v5} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) (k fb : α) (hk : k ∈ m₂) :
    (m₁ ∩ m₂).getKeyD k fb = m₁.getKeyD k fb := by
  have hb₁ := h₁.size_buckets_pos
  rw [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains] at hk
  split at hk
  · rename_i hb₂
    have e : m₁ ∩ m₂ = (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).1 := by
      show DHashMap.Raw.inter m₁ m₂ = _
      unfold DHashMap.Raw.inter; rw [dif_pos hb₁, dif_pos hb₂]
    have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
    obtain ⟨P, hperm, hP⟩ := r0_inter_perm ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
    rw [e]
    simp only [DHashMap.Raw.getKeyD, dif_pos (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).2, dif_pos hb₁]
    rw [Raw₀.getKeyD_eq_getKeyD wr, Raw₀.getKeyD_eq_getKeyD (Std.DHashMap.Internal.Raw.WF.out h₁),
      getKeyD_of_perm wr.distinct hperm, getKeyD_eq_getKey?, getKeyD_eq_getKey?,
      gk_filter _ _ _ (fun p _ hp => hP p hp)]
  · exact absurd hk (by simp)
end W3c1

/-! ## From `checks/W3c2Hand.lean` -/
set_option Elab.async false
theorem w3c2_tlmD {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (P : ((a : α) × β a) → Prop) (l : List ((a : α) × β a)) :
    ∀ (m : Raw₀ α β), (∀ p ∈ toListModel m.1.buckets, P p) → (∀ a ∈ l, P a) →
      ∀ p ∈ toListModel (Raw₀.insertListₘ m l).1.buckets, P p := by
  induction l with
  | nil => intro m hm _; exact hm
  | cons hd tl ih =>
    intro m hm hl
    refine ih (m.insert hd.1 hd.2) (fun p hp => ?_) (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    rcases mem_tlm_insert m hd.1 hd.2 p hp with h | h
    · exact h ▸ hl hd List.mem_cons_self
    · exact hm p h
theorem w3c2_dr_entries {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (l : List ((a : α) × β a)) :
    ∀ p ∈ toListModel (DHashMap.Raw.ofList l).buckets, p ∈ l := by
  show ∀ p ∈ toListModel (DHashMap.Raw.insertMany ∅ l).buckets, p ∈ l
  unfold DHashMap.Raw.insertMany
  rw [dif_pos (show 0 < (∅ : DHashMap.Raw α β).buckets.size from (Raw₀.emptyWithCapacity 8).2)]
  rw [Raw₀.insertMany_eq_insertListₘ]
  exact w3c2_tlmD (· ∈ l) l _ (fun p hp => by simp [dr_empty, nil16, toListModel] at hp) (fun a ha => ha)
theorem w3c2_dm_entries {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (l : List ((a : α) × β a)) :
    ∀ p ∈ toListModel (DHashMap.ofList l).1.buckets, p ∈ l := by
  show ∀ p ∈ toListModel (Raw₀.insertMany Raw₀.emptyWithCapacity l).1.1.buckets, p ∈ l
  rw [Raw₀.insertMany_eq_insertListₘ]
  exact w3c2_tlmD (· ∈ l) l _ (by simp) (fun a ha => ha)
theorem w3c2_gkD {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [EquivBEq α] (l : List ((a : α) × β a)) (k k' : α)
    (hkk : (k == k') = true) (hl : l.Pairwise (fun a b => (a.1 == b.1) = false)) (hk : k ∈ l.map Sigma.fst)
    (m : Raw₀ α β) (hm : ∀ p ∈ toListModel m.1.buckets, p ∈ l) (hc : m.contains k' = true) :
    m.getKey k' hc = k := by
  obtain ⟨p, hp, h1, h2⟩ := raw0_getKey_mem m k' hc
  rw [← h1]
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hk
  exact congrArg Sigma.fst (pw_unique Sigma.fst l hl p w (hm p hp) hw (BEq.trans h2 (BEq.symm hkk)))
theorem w3c2_gk {α : Type u} {β : Type v} [BEq α] [Hashable α] [EquivBEq α] (l : List (α × β)) (k k' : α)
    (hkk : (k == k') = true) (hl : l.Pairwise (fun a b => (a.1 == b.1) = false)) (hk : k ∈ l.map Prod.fst)
    (m : Raw₀ α (fun _ => β)) (hm : ∀ p ∈ toListModel m.1.buckets, (p.1, p.2) ∈ l) (hc : m.contains k' = true) :
    m.getKey k' hc = k := by
  obtain ⟨p, hp, h1, h2⟩ := raw0_getKey_mem m k' hc
  rw [← h1]
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hk
  exact congrArg Prod.fst (pw_unique Prod.fst l hl (p.1, p.2) w (hm p hp) hw (BEq.trans h2 (BEq.symm hkk)))
macro "w3c2_fin" : tactic => `(tactic| first | done | decide | (simp; done) | (simp (config := {decide := true}); done))
theorem w3c2_get!_eval {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] [Hashable α] {s : Nat}
    {bs : Array (AssocList α β)} {h : 0 < bs.size} (a : α) [Inhabited (β a)] (hsz : Pow2 bs.size) :
    Raw₀.get! (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a = (bs[ix bs a]'(Nat.mod_lt _ h)).getCast! a := by
  simp only [Raw₀.get!, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]
theorem w3c2_getD_eval {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] [Hashable α] {s : Nat}
    {bs : Array (AssocList α β)} {h : 0 < bs.size} (a : α) (fb : β a) (hsz : Pow2 bs.size) :
    Raw₀.getD (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a fb = (bs[ix bs a]'(Nat.mod_lt _ h)).getCastD a fb := by
  simp only [Raw₀.getD, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]
open S1

/-! ## From `checks/W3c3Hand.lean` -/
/-! # W3c3 helpers -/
/-- Evaluates a hash-map union/inter/diff of literals, allowing one resize (copy of W2c0's union macro). -/
macro "w3c3_ev" : tactic => `(tactic| (
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
namespace W3c3
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
end W3c3
namespace W3c3
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
end W3c3
namespace W3c3
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
end W3c3
namespace W3c3
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
end W3c3
namespace W3c3
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
end W3c3
namespace W3c3
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
end W3c3

/-! ## From `checks/W3c4Hand.lean` -/
namespace W3c4
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
end W3c4
namespace W3c4
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
end W3c4

/-! ## From `checks/W3c5Hand.lean` -/
namespace W3c5
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
-- size-field bounds for insert / insertIfNew (no laws, no WF)
theorem ins_ge (m : Raw₀ α β) (a : α) (b : β a) : m.1.size ≤ (m.insert a b).1.size := by
  obtain ⟨⟨s, bs⟩, h⟩ := m; unfold Raw₀.insert; dsimp only; split
  · exact Nat.le_refl _
  · rw [expand_size]; exact Nat.le_succ _
theorem ins_le (m : Raw₀ α β) (a : α) (b : β a) : (m.insert a b).1.size ≤ m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m; unfold Raw₀.insert; dsimp only; split
  · exact Nat.le_succ _
  · rw [expand_size]; exact Nat.le_refl _
theorem insn_le (m : Raw₀ α β) (a : α) (b : β a) : (m.insertIfNew a b).1.size ≤ m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m; unfold Raw₀.insertIfNew; dsimp only; split
  · exact Nat.le_succ _
  · rw [expand_size]; exact Nat.le_refl _
theorem ilm_le (m : Raw₀ α β) (l : List ((a : α) × β a)) :
    (Raw₀.insertListₘ m l).1.size ≤ m.1.size + l.length := by
  induction l generalizing m with
  | nil => simp [Raw₀.insertListₘ]
  | cons hd tl ih =>
    simp only [Raw₀.insertListₘ, List.length_cons]
    have := ih (m.insert hd.1 hd.2); have := ins_le m hd.1 hd.2; omega
theorem r0_sl (m : Raw₀ α β) (l : List ((a : α) × β a)) : (m.insertMany l).1.1.size ≤ m.1.size + l.length := by
  rw [Raw₀.insertMany_eq_insertListₘ]; exact ilm_le m l
theorem r0_sg {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (m : Raw₀ α β) (l : ρ) :
    m.1.size ≤ (m.insertMany l).1.1.size :=
  (m.insertMany l).2 (fun m' => m.1.size ≤ m'.1.size) (fun h => Nat.le_trans h (ins_ge _ _ _)) (Nat.le_refl _)
theorem dh_sl (m : DHashMap α β) (l : List ((a : α) × β a)) : (m.insertMany l).size ≤ m.size + l.length :=
  r0_sl ⟨m.1, m.2.size_buckets_pos⟩ l
theorem dh_sg {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (m : DHashMap α β) (l : ρ) : m.size ≤ (m.insertMany l).size :=
  r0_sg ⟨m.1, m.2.size_buckets_pos⟩ l
theorem dr_sl (m : DHashMap.Raw α β) (l : List ((a : α) × β a)) : (m.insertMany l).size ≤ m.size + l.length := by
  unfold DHashMap.Raw.insertMany; split
  · exact r0_sl ⟨m, _⟩ l
  · exact Nat.le_add_right _ _
theorem dr_sg {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (m : DHashMap.Raw α β) (l : ρ) : m.size ≤ (m.insertMany l).size := by
  unfold DHashMap.Raw.insertMany; split
  · exact r0_sg ⟨m, _⟩ l
  · exact Nat.le_refl _
end
section
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
theorem cilm_le (m : Raw₀ α (fun _ => β)) (l : List (α × β)) :
    (Raw₀.Const.insertListₘ m l).1.size ≤ m.1.size + l.length := by
  induction l generalizing m with
  | nil => simp [Raw₀.Const.insertListₘ]
  | cons hd tl ih =>
    simp only [Raw₀.Const.insertListₘ, List.length_cons]
    have := ih (m.insert hd.1 hd.2); have := ins_le m hd.1 hd.2; omega
theorem uilm_le (m : Raw₀ α (fun _ => Unit)) (l : List α) :
    (Raw₀.Const.insertListIfNewUnitₘ m l).1.size ≤ m.1.size + l.length := by
  induction l generalizing m with
  | nil => simp [Raw₀.Const.insertListIfNewUnitₘ]
  | cons hd tl ih =>
    simp only [Raw₀.Const.insertListIfNewUnitₘ, List.length_cons]
    have := ih (m.insertIfNew hd ()); have := insn_le m hd (); omega
theorem r0c_sl (m : Raw₀ α (fun _ => β)) (l : List (α × β)) :
    (Raw₀.Const.insertMany m l).1.1.size ≤ m.1.size + l.length := by
  rw [Raw₀.Const.insertMany_eq_insertListₘ]; exact cilm_le m l
theorem r0u_sl (m : Raw₀ α (fun _ => Unit)) (l : List α) :
    (Raw₀.Const.insertManyIfNewUnit m l).1.1.size ≤ m.1.size + l.length := by
  rw [Raw₀.Const.insertManyIfNewUnit_eq_insertListIfNewUnitₘ]; exact uilm_le m l
theorem r0c_sg {ρ : Type w} [ForIn Id ρ (α × β)] (m : Raw₀ α (fun _ => β)) (l : ρ) :
    m.1.size ≤ (Raw₀.Const.insertMany m l).1.1.size :=
  (Raw₀.Const.insertMany m l).2 (fun m' => m.1.size ≤ m'.1.size) (fun h => Nat.le_trans h (ins_ge _ _ _)) (Nat.le_refl _)
theorem r0u_sg {ρ : Type w} [ForIn Id ρ α] (m : Raw₀ α (fun _ => Unit)) (l : ρ) :
    m.1.size ≤ (Raw₀.Const.insertManyIfNewUnit m l).1.1.size :=
  (Raw₀.Const.insertManyIfNewUnit m l).2 (fun m' => m.1.size ≤ m'.1.size)
    (fun h => Nat.le_trans h (insertIfNew_size_ge _ _ _)) (Nat.le_refl _)
theorem dhc_sl (m : DHashMap α (fun _ => β)) (l : List (α × β)) :
    (DHashMap.Const.insertMany m l).size ≤ m.size + l.length := r0c_sl ⟨m.1, m.2.size_buckets_pos⟩ l
theorem dhc_sg {ρ : Type w} [ForIn Id ρ (α × β)] (m : DHashMap α (fun _ => β)) (l : ρ) :
    m.size ≤ (DHashMap.Const.insertMany m l).size := r0c_sg ⟨m.1, m.2.size_buckets_pos⟩ l
theorem dhu_sl (m : DHashMap α (fun _ => Unit)) (l : List α) :
    (DHashMap.Const.insertManyIfNewUnit m l).size ≤ m.size + l.length := r0u_sl ⟨m.1, m.2.size_buckets_pos⟩ l
theorem dhu_sg {ρ : Type w} [ForIn Id ρ α] (m : DHashMap α (fun _ => Unit)) (l : ρ) :
    m.size ≤ (DHashMap.Const.insertManyIfNewUnit m l).size := r0u_sg ⟨m.1, m.2.size_buckets_pos⟩ l
theorem drc_sl (m : DHashMap.Raw α (fun _ => β)) (l : List (α × β)) :
    (DHashMap.Raw.Const.insertMany m l).size ≤ m.size + l.length := by
  unfold DHashMap.Raw.Const.insertMany; split
  · exact r0c_sl ⟨m, _⟩ l
  · exact Nat.le_add_right _ _
theorem drc_sg {ρ : Type w} [ForIn Id ρ (α × β)] (m : DHashMap.Raw α (fun _ => β)) (l : ρ) :
    m.size ≤ (DHashMap.Raw.Const.insertMany m l).size := by
  unfold DHashMap.Raw.Const.insertMany; split
  · exact r0c_sg ⟨m, _⟩ l
  · exact Nat.le_refl _
theorem dru_sl (m : DHashMap.Raw α (fun _ => Unit)) (l : List α) :
    (DHashMap.Raw.Const.insertManyIfNewUnit m l).size ≤ m.size + l.length := by
  unfold DHashMap.Raw.Const.insertManyIfNewUnit; split
  · exact r0u_sl ⟨m, _⟩ l
  · exact Nat.le_add_right _ _
theorem dru_sg {ρ : Type w} [ForIn Id ρ α] (m : DHashMap.Raw α (fun _ => Unit)) (l : ρ) :
    m.size ≤ (DHashMap.Raw.Const.insertManyIfNewUnit m l).size := by
  unfold DHashMap.Raw.Const.insertManyIfNewUnit; split
  · exact r0u_sg ⟨m, _⟩ l
  · exact Nat.le_refl _
theorem hm_sl (m : HashMap α β) (l : List (α × β)) : (m.insertMany l).size ≤ m.size + l.length := dhc_sl m.inner l
theorem hm_sg {ρ : Type w} [ForIn Id ρ (α × β)] (m : HashMap α β) (l : ρ) : m.size ≤ (m.insertMany l).size := dhc_sg m.inner l
theorem hmr_sl (m : HashMap.Raw α β) (l : List (α × β)) : (m.insertMany l).size ≤ m.size + l.length := drc_sl m.inner l
theorem hmr_sg {ρ : Type w} [ForIn Id ρ (α × β)] (m : HashMap.Raw α β) (l : ρ) : m.size ≤ (m.insertMany l).size := drc_sg m.inner l
theorem hs_sl (m : HashSet α) (l : List α) : (m.insertMany l).size ≤ m.size + l.length := dhu_sl m.inner.inner l
theorem hs_sg {ρ : Type w} [ForIn Id ρ α] (m : HashSet α) (l : ρ) : m.size ≤ (m.insertMany l).size := dhu_sg m.inner.inner l
theorem hsr_sl (m : HashSet.Raw α) (l : List α) : (m.insertMany l).size ≤ m.size + l.length := dru_sl m.inner.inner l
theorem hsr_sg {ρ : Type w} [ForIn Id ρ α] (m : HashSet.Raw α) (l : ρ) : m.size ≤ (m.insertMany l).size := dru_sg m.inner.inner l
end
end W3c5
namespace W3c5
theorem dru_ins0 : (∅ : DHashMap.Raw Nat (fun _ => Unit)).insert 0 () = ⟨1, f16 (.cons 0 () .nil)⟩ := by
  simp only [dr_empty]; hm_eval_raw
end W3c5
namespace W3c5
section
variable {α : Type u} [BEq α]
-- get? and get! read the same bucket with the same test, so they agree on any found key (no laws, no WF)
theorem al_cget {β : Type v} [Inhabited β] (a : α) (l : AssocList α (fun _ => β)) (h : l.contains a = true) :
    l.get? a = some (l.get! a) := by
  induction l with
  | nil => simp [AssocList.contains] at h
  | cons k v t ih =>
    simp only [AssocList.get?, AssocList.get!]
    cases hk : (k == a)
    · simp only [cond_false]; apply ih; simpa [AssocList.contains, hk] using h
    · rfl
theorem al_kget {β : α → Type v} [Inhabited α] (a : α) (l : AssocList α β) (h : l.contains a = true) :
    l.getKey? a = some (l.getKey! a) := by
  induction l with
  | nil => simp [AssocList.contains] at h
  | cons k v t ih =>
    simp only [AssocList.getKey?, AssocList.getKey!]
    cases hk : (k == a)
    · simp only [Bool.false_eq_true, ite_false]; apply ih; simpa [AssocList.contains, hk] using h
    · simp
theorem al_dget [LawfulBEq α] {β : α → Type v} (a : α) [Inhabited (β a)] (l : AssocList α β) (h : l.contains a = true) :
    l.getCast? a = some (l.getCast! a) := by
  induction l with
  | nil => simp [AssocList.contains] at h
  | cons k v t ih =>
    simp only [AssocList.getCast?, AssocList.getCast!]
    by_cases hk : (k == a) = true
    · simp only [hk, dite_true]
    · simp only [hk, dite_false]; apply ih; simpa [AssocList.contains, hk] using h
variable [Hashable α]
theorem r0c_gsg {β : Type v} [Inhabited β] (m : Raw₀ α (fun _ => β)) (a : α) (h : m.contains a = true) :
    Raw₀.Const.get? m a = some (Raw₀.Const.get! m a) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; rw [cget?_gen, cget!_gen]; exact al_cget a _ h
theorem r0k_gsg {β : α → Type v} [Inhabited α] (m : Raw₀ α β) (a : α) (h : m.contains a = true) :
    m.getKey? a = some (m.getKey! a) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; exact al_kget a _ h
theorem r0_gsg [LawfulBEq α] {β : α → Type v} (m : Raw₀ α β) (a : α) [Inhabited (β a)] (h : m.contains a = true) :
    m.get? a = some (m.get! a) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; exact al_dget a _ h
theorem dhc_gsg {β : Type v} [Inhabited β] (m : DHashMap α (fun _ => β)) (a : α) (h : a ∈ m) :
    DHashMap.Const.get? m a = some (DHashMap.Const.get! m a) :=
  r0c_gsg ⟨m.1, m.2.size_buckets_pos⟩ a (DHashMap.mem_iff_contains.1 h)
theorem drc_gsg {β : Type v} [Inhabited β] (m : DHashMap.Raw α (fun _ => β)) (a : α) (h : a ∈ m) :
    DHashMap.Raw.Const.get? m a = some (DHashMap.Raw.Const.get! m a) := by
  rw [DHashMap.Raw.mem_iff_contains] at h
  unfold DHashMap.Raw.contains at h; unfold DHashMap.Raw.Const.get? DHashMap.Raw.Const.get!
  split
  · rename_i hb; rw [dif_pos hb] at h; exact r0c_gsg ⟨m, hb⟩ a h
  · rename_i hb; rw [dif_neg hb] at h; exact absurd h (by simp)
theorem dr_gsg [LawfulBEq α] {β : α → Type v} (m : DHashMap.Raw α β) (a : α) [Inhabited (β a)] (h : a ∈ m) :
    m.get? a = some (m.get! a) := by
  rw [DHashMap.Raw.mem_iff_contains] at h
  unfold DHashMap.Raw.contains at h; unfold DHashMap.Raw.get? DHashMap.Raw.get!
  split
  · rename_i hb; rw [dif_pos hb] at h; exact r0_gsg ⟨m, hb⟩ a h
  · rename_i hb; rw [dif_neg hb] at h; exact absurd h (by simp)
theorem hs_gsg [Inhabited α] (m : HashSet α) (a : α) (h : a ∈ m) : m.get? a = some (m.get! a) :=
  r0k_gsg ⟨m.1.1.1, m.1.1.2.size_buckets_pos⟩ a (HashSet.mem_iff_contains.1 h)
theorem hsr_gsg [Inhabited α] (m : HashSet.Raw α) (a : α) (h : a ∈ m) : m.get? a = some (m.get! a) := by
  rw [HashSet.Raw.mem_iff_contains] at h
  simp only [HashSet.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains] at h
  simp only [HashSet.Raw.get?, HashSet.Raw.get!, HashMap.Raw.getKey?, HashMap.Raw.getKey!, DHashMap.Raw.getKey?, DHashMap.Raw.getKey!]
  split
  · rename_i hb; rw [dif_pos hb] at h; exact r0k_gsg ⟨_, hb⟩ a h
  · rename_i hb; rw [dif_neg hb] at h; exact absurd h (by simp)
end
end W3c5
namespace W3c5
export W2c0 (cz_hs)
export W2c0 (cz_wf)
end W3c5
namespace W3c5
-- under HZ, key 2 stored in bucket 1 of 2 is found by no key (only 5 looks in bucket 1, and 5/2 ≠ 2/2)
theorem hz_unreach {β : Type v} (s : Nat) (v : β) (h : 0 < (#[.nil, b1 (HZ.mk 2) v] : Array (AssocList HZ (fun _ => β))).size)
    (a : HZ) : Raw₀.contains (⟨⟨s, #[.nil, b1 (HZ.mk 2) v]⟩, h⟩ : Raw₀ HZ (fun _ => β)) a = false := by
  rw [contains_eval _ (by simp [Pow2])]; obtain ⟨n⟩ := a
  by_cases hn : n = 5
  · subst hn
    have : ix (#[.nil, b1 (HZ.mk 2) v] : Array (AssocList HZ (fun _ => β))) (HZ.mk 5) = 1 := by
      show (scrambleHash 1).toNat % 2 = 1
      rw [scr_small _ (by decide)]; rfl
    simp only [this]; rfl
  · have : ix (#[.nil, b1 (HZ.mk 2) v] : Array (AssocList HZ (fun _ => β))) (HZ.mk n) = 0 := by
      show (scrambleHash (if n = 5 then 1 else 0)).toNat % 2 = 0
      rw [if_neg hn, scr_small _ (by decide)]; rfl
    simp only [this]; rfl
end W3c5
namespace W3c5
theorem dr_inter_gen {α : Type u} {γ : α → Type v} [BEq α] [Hashable α] (m₁ m₂ : DHashMap.Raw α γ)
    (h₁ : 0 < m₁.buckets.size) (h₂ : 0 < m₂.buckets.size) : DHashMap.Raw.inter m₁ m₂ = (Raw₀.inter ⟨m₁, h₁⟩ ⟨m₂, h₂⟩).1 := by
  simp [DHashMap.Raw.inter, h₁, h₂]
end W3c5

/-! ## From `checks/W4c0Hand.lean` -/
/-! # W4c0 helpers -/
theorem w4c0HN : ∀ [EquivBEq Probe1.HN] [LawfulHashable Probe1.HN], False := fun {_ h} => Probe1.HN.notLH h
macro "w4e" : tactic => `(tactic| first
  | (hm_eval3; done)
  | (simp only [SDiff.sdiff, Union.union, Inter.inter, HashSet.diff, HashSet.Raw.diff, HashMap.diff, HashMap.Raw.diff, DHashMap.diff, DHashMap.Raw.diff, HashSet.union, HashSet.Raw.union, HashMap.union, HashMap.Raw.union, DHashMap.union, DHashMap.Raw.union, HashSet.inter, HashSet.Raw.inter, HashMap.inter, HashMap.Raw.inter, DHashMap.inter, DHashMap.Raw.inter]; hm_eval3; done)
  | (simp only [SDiff.sdiff, Union.union, Inter.inter, HashSet.diff, HashSet.Raw.diff, HashMap.diff, HashMap.Raw.diff, DHashMap.diff, DHashMap.Raw.diff, HashSet.union, HashSet.Raw.union, HashMap.union, HashMap.Raw.union, DHashMap.union, DHashMap.Raw.union, HashSet.inter, HashSet.Raw.inter, HashMap.inter, HashMap.Raw.inter, DHashMap.inter, DHashMap.Raw.inter]; hm_eval3 <;> (try simp (disch := first | decide | simp) [Probe1.get?_eval, ix]) <;> decide)
  | (hm_eval3 <;> (try simp (disch := first | decide | simp) [Probe1.get?_eval, ix]) <;> decide))
theorem w4c0_dre [BEq α] [Hashable α] {β : α → Type v} (m : DHashMap.Raw α β) (k a : α)
    (h : (m.erase k).contains a = true) : m.contains a = true := by
  by_cases hb : 0 < m.buckets.size
  · simp only [DHashMap.Raw.erase, DHashMap.Raw.contains, hb, dite_true] at h ⊢
    rw [dif_pos (Raw₀.erase ⟨m, hb⟩ k).2] at h
    exact raw0_contains_of_contains_erase _ _ _ h
  · simp only [DHashMap.Raw.erase, hb, dite_false] at h; exact h
theorem w4c0_dre_mem [BEq α] [Hashable α] {β : α → Type v} {m : DHashMap.Raw α β} {k a : α}
    (h : a ∈ m.erase k) : a ∈ m := w4c0_dre m k a h
theorem w4c0_dme_mem [BEq α] [Hashable α] {β : α → Type v} {m : DHashMap α β} {k a : α}
    (h : a ∈ m.erase k) : a ∈ m := raw0_contains_of_contains_erase _ k a h
theorem w4c0_hmre_mem [BEq α] [Hashable α] {β : Type v} {m : HashMap.Raw α β} {k a : α}
    (h : a ∈ m.erase k) : a ∈ m := w4c0_dre m.inner k a h
theorem w4c0_hme_mem [BEq α] [Hashable α] {β : Type v} {m : HashMap α β} {k a : α}
    (h : a ∈ m.erase k) : a ∈ m := raw0_contains_of_contains_erase _ k a h
theorem w4c0_hsre_mem [BEq α] [Hashable α] {m : HashSet.Raw α} {k a : α}
    (h : a ∈ m.erase k) : a ∈ m := w4c0_dre m.inner.inner k a h
theorem w4c0_hse_mem [BEq α] [Hashable α] {m : HashSet α} {k a : α}
    (h : a ∈ m.erase k) : a ∈ m := raw0_contains_of_contains_erase _ k a h
theorem w4c0_agd [BEq α] [EquivBEq α] {β : Type v} (l : AssocList α (fun _ => β)) (a b : α) (fb : β)
    (hab : (a == b) = true) : l.getD a fb = l.getD b fb := by
  induction l with
  | nil => rfl
  | cons k v t ih => simp only [AssocList.getD, BEq.congr_right hab, ih]
theorem w4c0_agkd [BEq α] [EquivBEq α] {β : α → Type v} (l : AssocList α β) (a b fb : α)
    (hab : (a == b) = true) : l.getKeyD a fb = l.getKeyD b fb := by
  induction l with
  | nil => rfl
  | cons k v t ih => simp only [AssocList.getKeyD, BEq.congr_right hab, ih]
theorem w4c0_r0gd [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {β : Type v}
    (m : Raw₀ α (fun _ => β)) (a b : α) (fb : β) (hab : (a == b) = true) :
    Raw₀.Const.getD m a fb = Raw₀.Const.getD m b fb := by
  obtain ⟨⟨s, bs⟩, hm⟩ := m
  simp only [Raw₀.Const.getD, hash_eq hab]
  exact w4c0_agd _ _ _ _ hab
theorem w4c0_r0gkd [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {β : α → Type v}
    (m : Raw₀ α β) (a b fb : α) (hab : (a == b) = true) :
    Raw₀.getKeyD m a fb = Raw₀.getKeyD m b fb := by
  obtain ⟨⟨s, bs⟩, hm⟩ := m
  simp only [Raw₀.getKeyD, hash_eq hab]
  exact w4c0_agkd _ _ _ _ hab
theorem w4c0_drgd [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {β : Type v}
    {m : DHashMap.Raw α (fun _ => β)} {a b : α} {fb : β} (hab : (a == b) = true) :
    DHashMap.Raw.Const.getD m a fb = DHashMap.Raw.Const.getD m b fb := by
  simp only [DHashMap.Raw.Const.getD]; split
  · exact w4c0_r0gd _ _ _ _ hab
  · rfl
theorem w4c0_drgkd [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {β : α → Type v}
    {m : DHashMap.Raw α β} {a b fb : α} (hab : (a == b) = true) :
    m.getKeyD a fb = m.getKeyD b fb := by
  simp only [DHashMap.Raw.getKeyD]; split
  · exact w4c0_r0gkd _ _ _ _ hab
  · rfl
theorem w4c0_get!_eval {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] [Hashable α] {s : Nat}
    {bs : Array (AssocList α β)} {h : 0 < bs.size} (a : α) [Inhabited (β a)] (hsz : Pow2 bs.size) :
    Raw₀.get! (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a = (bs[ix bs a]'(Nat.mod_lt _ h)).getCast! a := by
  unfold Raw₀.get!; dsimp only; simp only [mkIdx_eq _ _ _ hsz]
  simp only [Array.ugetElem_eq_getElem, idx_lt h _ hsz]
macro "w4d" : tactic => `(tactic| first
  | w4e
  | decide +kernel
  | (simp only [Union.union, drn_union]; decide +kernel)
  | (hm_eval3 <;> decide +kernel)
  | (simp only [Union.union]; hm_eval3 <;> simp only [DHashMap.Raw.get!] <;> simp (disch := first | decide | simp) [w4c0_get!_eval, ix, scr_small, AssocList.getCast!] <;> (try simp [Std.Internal.List.getValueCast!, Std.Internal.List.getValueCast?]) <;> decide))

/-! ## From `checks/W4c1Hand.lean` -/
set_option Elab.async false
set_option linter.unusedSimpArgs false
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
export W3c3 (al_getD)
export W3c3 (al_getKeyD)
export W3c3 (al_getCastD)
export W3c3 (r0c_getD)
export W3c3 (r0_getKeyD)
export W3c3 (r0_getD)
export W3c3 (drc_getD)
export W3c3 (dr_getKeyD)
export W3c3 (dr_getD)
end W4c1B
namespace W4c1B
variable {α : Type u} [BEq α] [Hashable α]
export W3c3 (ck_any)
export W3c3 (al_filter)
export W3c3 (mkIdx_map_toNat)
export W3c3 (al_erase)
export W3c3 (r0_filter_nc)
export W3c3 (r0_erase_nc)
export W3c3 (r0_diff_nc)
export W3c3 (dr_nmd)
export W3c3 (hmr_nmd)
export W3c3 (hsr_nmd)
export W3c3 (dh_nmd)
export W3c3 (hm_nmd)
export W3c3 (hs_nmd)
end W4c1B
namespace W4c1B
variable {α : Type u} [BEq α] [Hashable α]
export W3c3 (r0_ied)
export W3c3 (r0_iil)
export W3c3 (dr_ied)
export W3c3 (dr_iil)
export W3c3 (hmr_ied)
export W3c3 (hmr_iil)
export W3c3 (hsr_ied)
export W3c3 (hsr_iil)
end W4c1B
namespace W4c1B
variable {α : Type u} [BEq α] [Hashable α]
export W3c3 (r0_iir)
export W3c3 (dr_iir)
export W3c3 (hmr_iir)
export W3c3 (hsr_iir)
end W4c1B
namespace W4c1B
variable {α : Type u} [BEq α] [Hashable α]
export W3c3 (contains_insert_of)
export W3c3 (ins_self)
export W3c3 (insIfNew_self)
export W3c3 (r0_cc)
export W3c3 (mem_tlm)
export W3c3 (ilin_keep)
export W3c3 (ilm_keep)
export W3c3 (ilin_mem)
export W3c3 (ilm_mem)
export W3c3 (r0_mul)
export W3c3 (r0_mur)
export W3c3 (dr_mul)
export W3c3 (dr_mur)
export W3c3 (hmr_mul)
export W3c3 (hmr_mur)
export W3c3 (hsr_mul)
export W3c3 (hsr_mur)
end W4c1B
namespace W4c1B
variable {α : Type u} [BEq α] [Hashable α]
export W3c3 (al_filter_ex)
export W3c3 (al_getEntry)
export W3c3 (r0_getEntry)
export W3c3 (r0_nmi)
export W3c3 (dr_nmi)
export W3c3 (hmr_nmi)
export W3c3 (hsr_nmi)
end W4c1B
namespace W4c1A
open Std Std.DHashMap.Internal Probe2
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
export W3c4 (ins_ge)
export W3c4 (im_ge)
export W3c4 (cim_ge)
export W3c4 (cimu_ge)
export W3c4 (a_getKey?_none)
export W3c4 (a_cget?_some)
export W3c4 (a_getKey?_some)
export W3c4 (a_getCast?_some)
end
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
export W3c4 (cce_dr)
export W3c4 (im_dr)
export W3c4 (im_drc)
export W3c4 (im_dru)
export W3c4 (r0c_get?_nc)
export W3c4 (r0_getKey?_nc)
export W3c4 (r0_get?_nc)
export W3c4 (r0c_get?_c)
export W3c4 (r0_getKey?_c)
export W3c4 (r0_get?_c)
export W3c4 (drc_get?_nc)
export W3c4 (drc_get!_nc)
export W3c4 (dr_getKey?_nc)
export W3c4 (dr_getKey!_nc)
export W3c4 (dr_get?_nc)
export W3c4 (dr_get!_nc)
export W3c4 (drc_get?_c)
export W3c4 (dr_getKey?_c)
export W3c4 (dr_get?_c)
end
section
variable {α : Type u} {β : α → Type v}
export W3c4 (u_dm_union)
export W3c4 (u_dm_inter)
export W3c4 (u_dm_diff)
export W3c4 (u_hm_union)
export W3c4 (u_hs_union)
export W3c4 (u_hs_inter)
export W3c4 (u_hs_diff)
export W3c4 (u_hsr_union)
end
section
variable {α : Type u} {β : α → Type v}
export W3c4 (dgetD_eval)
end
section
variable {α : Type u} {β : α → Type v}
export W3c4 (tlm_iin)
export W3c4 (keys_iin)
end
end W4c1A
namespace W4c1A
open Std Std.DHashMap.Internal Probe2
section
variable {α : Type u} {β : α → Type v}
export W3c4 (a_getEntry_mem)
export W3c4 (a_contains_of_mem)
export W3c4 (D)
export W3c4 (D_of_getEntry)
export W3c4 (contains_of_D)
export W3c4 (fold_D)
export W3c4 (ni_r0)
export W3c4 (ni_dr)
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
end W4c1

/-! ## From `checks/W4c2Hand.lean` -/
set_option Elab.async false
-- helper: 16 buckets with the given bucket at index 1 (a key 0 there is misplaced)
abbrev w4c2g16 {α : Type u} {β : α → Type v} (b : AssocList α β) : Array (AssocList α β) :=
  #[.nil, b, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil]
-- helper: the empty raw literal is well-formed
theorem w4c2eWF {β : Nat → Type v} : (⟨0, nil16⟩ : DHashMap.Raw Nat β).WF := (dr_empty (α := Nat) (β := β)) ▸ .empty
-- helper: ∅.insert 1 5 as a literal (key 1 sits in bucket 1)
theorem w4c2_dr1 : (∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 1 5 =
    ⟨1, #[.nil, .cons 1 5 .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil]⟩ := by
  simp only [dr_empty]; hm_eval_raw
theorem w4c2_hmr1 : (∅ : HashMap.Raw Nat Nat).insert 1 5 =
    hmr 1 #[.nil, .cons 1 5 .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil] := by
  show HashMap.Raw.mk _ = _; rw [show ((∅ : HashMap.Raw Nat Nat).inner : DHashMap.Raw Nat (fun _ => Nat)) = ∅ from rfl]
  simp only [dr_empty]; hm_eval_raw
theorem w4c2_hsr1 : (∅ : HashSet.Raw Nat).insert 1 =
    hsr 1 #[.nil, .cons 1 () .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil] := by
  show HashSet.Raw.mk (HashMap.Raw.mk _) = _
  rw [show ((∅ : HashSet.Raw Nat).inner.inner : DHashMap.Raw Nat (fun _ => Unit)) = ∅ from rfl]
  simp only [dr_empty]; hm_eval_raw
namespace W4c2
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
-- insert never lowers the size field (no laws, no WF; copy of the W2c0 lemma)
theorem isg (m : Raw₀ α β) (a : α) (b : β a) : m.1.size ≤ (m.insert a b).1.size := by
  obtain ⟨⟨s, bs⟩, h⟩ := m; unfold Raw₀.insert; dsimp only; split
  · exact Nat.le_refl _
  · rw [expand_size]; exact Nat.le_succ _
-- the union is at least as large as its right argument (no laws, no WF)
theorem r0_un (m₁ m₂ : Raw₀ α β) : m₂.1.size ≤ (m₁.union m₂).1.size := by
  unfold Raw₀.union; split
  · exact (m₂.insertManyIfNew m₁.1).2 (fun m' => m₂.1.size ≤ m'.1.size)
      (fun h => Nat.le_trans h (insertIfNew_size_ge _ _ _)) (Nat.le_refl _)
  · have := (m₁.insertMany m₂.1).2 (fun m' => m₁.1.size ≤ m'.1.size)
      (fun h => Nat.le_trans h (isg _ _ _)) (Nat.le_refl _)
    omega
theorem dr_un (m₁ m₂ : DHashMap.Raw α β) (h₂ : 0 < m₂.buckets.size) : m₂.size ≤ (m₁ ∪ m₂).size := by
  show _ ≤ (DHashMap.Raw.union m₁ m₂).size
  unfold DHashMap.Raw.union
  by_cases h₁ : 0 < m₁.buckets.size
  · rw [dif_pos h₁, dif_pos h₂]; exact r0_un _ ⟨m₂, h₂⟩
  · rw [dif_neg h₁]; exact Nat.le_refl _
theorem dh_un (m₁ m₂ : DHashMap α β) : m₂.size ≤ (m₁ ∪ m₂).size :=
  r0_un ⟨m₁.1, m₁.2.size_buckets_pos⟩ ⟨m₂.1, m₂.2.size_buckets_pos⟩
end W4c2
namespace W4c2
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
theorem hmr_un (m₁ m₂ : HashMap.Raw α β) (h₂ : m₂.WF) : m₂.size ≤ (m₁ ∪ m₂).size :=
  dr_un m₁.inner m₂.inner (DHashMap.Raw.WF.size_buckets_pos _ h₂.out)
theorem hm_un (m₁ m₂ : HashMap α β) : m₂.size ≤ (m₁ ∪ m₂).size := dh_un m₁.inner m₂.inner
theorem hsr_un (m₁ m₂ : HashSet.Raw α) (h₂ : m₂.WF) : m₂.size ≤ (m₁ ∪ m₂).size :=
  dr_un m₁.inner.inner m₂.inner.inner (DHashMap.Raw.WF.size_buckets_pos _ h₂.out.out)
theorem hs_un (m₁ m₂ : HashSet α) : m₂.size ≤ (m₁ ∪ m₂).size := dh_un m₁.inner.inner m₂.inner.inner
end W4c2
namespace W4c2W
open Std Std.DHashMap.Internal HashInstHand Std.Internal.List
universe w4u3 w4v3
section
variable {α : Type w4u3} {γ : α → Type w4v3} [BEq α] [Hashable α]
export W3c1 (r0_contains_congr)
export W3c1 (ck_filter)
export W3c1 (ck_eraseList_of_not)
export W3c1 (ck_eraseList_of_mem)
export W3c1 (r0_diff_nc)
export W3c1 (dr_diff_nm)
end
end W4c2W
namespace W4c2W
open Std Std.DHashMap.Internal HashInstHand Std.Internal.List
universe w4u5 w4v5
theorem gv_filter {α : Type w4u5} {β : Type w4v5} [BEq α] (l : List ((_ : α) × β)) (P : (_ : α) × β → Bool) (a : α)
    (hP : ∀ p ∈ l, (p.1 == a) = true → P p = true) : getValue? a (l.filter P) = getValue? a l := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    have ih' := ih (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    have hp := hP p List.mem_cons_self
    obtain ⟨k', v⟩ := p
    rw [List.filter_cons]
    by_cases hpa : (k' == a) = true
    · rw [if_pos (hp hpa)]; simp [getValue?, hpa]
    · have hpa' : (k' == a) = false := by simpa using hpa
      split <;> simp [getValue?, hpa', ih']
-- inter with a WF m₁ is a filter of m₁ that keeps every entry whose key is == a key found in m₂ (m₂ needs no WF)
theorem r0_inter_perm {α : Type w4u5} {γ : α → Type w4v5} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : Raw₀ α γ) (h₁ : m₁.1.WF) (k : α) (hk : m₂.contains k = true) :
    ∃ P : (a : α) × γ a → Bool, (toListModel (m₁.inter m₂).1.buckets).Perm ((toListModel m₁.1.buckets).filter P) ∧
      ∀ p : (a : α) × γ a, (p.1 == k) = true → P p = true := by
  obtain ⟨m₁, hb₁⟩ := m₁; obtain ⟨m₂, hb₂⟩ := m₂
  have w₁ : Raw.WFImp m₁ := Std.DHashMap.Internal.Raw.WF.out h₁
  unfold Raw₀.inter
  split
  · exact ⟨fun p => Raw₀.contains ⟨m₂, hb₂⟩ p.1, Raw₀.toListModel_filter, fun p hp => by
    show Raw₀.contains ⟨m₂, hb₂⟩ p.1 = true
    rw [r0_contains_congr _ hp]; exact hk⟩
  · refine ⟨fun p => containsKey p.1 (toListModel m₂.buckets), ?_, fun p hp => by
      show containsKey p.1 _ = true
      rw [containsKey_congr hp]; exact Probe2.raw0_contains_tlm ⟨m₂, hb₂⟩ k hk⟩
    rw [Raw₀.interSmaller_eq_interSmallerₘ]
    exact (Raw₀.toListModel_interSmallerₘ ⟨_, hb₁⟩ m₂ w₁).trans (interSmaller_perm_filter _ _ w₁.distinct)
theorem drc_inter_getD {α : Type w4u5} {β : Type w4v5} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : DHashMap.Raw α (fun _ => β)) (h₁ : m₁.WF) (k : α) (fb : β) (hk : k ∈ m₂) :
    DHashMap.Raw.Const.getD (m₁ ∩ m₂) k fb = DHashMap.Raw.Const.getD m₁ k fb := by
  have hb₁ := h₁.size_buckets_pos
  rw [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains] at hk
  split at hk
  · rename_i hb₂
    have e : m₁ ∩ m₂ = (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).1 := by
      show DHashMap.Raw.inter m₁ m₂ = _
      unfold DHashMap.Raw.inter; rw [dif_pos hb₁, dif_pos hb₂]
    have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
    obtain ⟨P, hperm, hP⟩ := r0_inter_perm ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
    rw [e]
    simp only [DHashMap.Raw.Const.getD, dif_pos (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).2, dif_pos hb₁]
    rw [Raw₀.Const.getD_eq_getValueD wr, Raw₀.Const.getD_eq_getValueD (Std.DHashMap.Internal.Raw.WF.out h₁),
      getValueD_of_perm wr.distinct hperm, getValueD_eq_getValue?, getValueD_eq_getValue?,
      gv_filter _ _ _ (fun p _ hp => hP p hp)]
  · exact absurd hk (by simp)
theorem gvc_filter {α : Type w4u5} {γ : α → Type w4v5} [BEq α] [LawfulBEq α] (l : List ((a : α) × γ a))
    (P : (a : α) × γ a → Bool) (a : α)
    (hP : ∀ p ∈ l, (p.1 == a) = true → P p = true) : getValueCast? a (l.filter P) = getValueCast? a l := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    have ih' := ih (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    have hp := hP p List.mem_cons_self
    obtain ⟨k', v⟩ := p
    rw [List.filter_cons]
    by_cases hpa : (k' == a) = true
    · rw [if_pos (hp hpa)]; simp [getValueCast?, hpa]
    · have hpa' : (k' == a) = false := by simpa using hpa
      split <;> simp [getValueCast?, hpa', ih']
theorem gk_filter {α : Type w4u5} {γ : α → Type w4v5} [BEq α] (l : List ((a : α) × γ a))
    (P : (a : α) × γ a → Bool) (a : α)
    (hP : ∀ p ∈ l, (p.1 == a) = true → P p = true) : getKey? a (l.filter P) = getKey? a l := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    have ih' := ih (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    have hp := hP p List.mem_cons_self
    obtain ⟨k', v⟩ := p
    rw [List.filter_cons]
    by_cases hpa : (k' == a) = true
    · rw [if_pos (hp hpa)]; simp [getKey?, hpa]
    · have hpa' : (k' == a) = false := by simpa using hpa
      split <;> simp [getKey?, hpa', ih']
theorem dr_inter_getD {α : Type w4u5} {γ : α → Type w4v5} [BEq α] [Hashable α] [LawfulBEq α]
    (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) (k : α) (fb : γ k) (hk : k ∈ m₂) :
    (m₁ ∩ m₂).getD k fb = m₁.getD k fb := by
  have hb₁ := h₁.size_buckets_pos
  rw [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains] at hk
  split at hk
  · rename_i hb₂
    have e : m₁ ∩ m₂ = (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).1 := by
      show DHashMap.Raw.inter m₁ m₂ = _
      unfold DHashMap.Raw.inter; rw [dif_pos hb₁, dif_pos hb₂]
    have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
    obtain ⟨P, hperm, hP⟩ := r0_inter_perm ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
    rw [e]
    simp only [DHashMap.Raw.getD, dif_pos (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).2, dif_pos hb₁]
    rw [Raw₀.getD_eq_getValueCastD wr, Raw₀.getD_eq_getValueCastD (Std.DHashMap.Internal.Raw.WF.out h₁),
      getValueCastD_of_perm wr.distinct hperm, getValueCastD_eq_getValueCast?, getValueCastD_eq_getValueCast?,
      gvc_filter _ _ _ (fun p _ hp => hP p hp)]
  · exact absurd hk (by simp)
theorem drk_inter_getKeyD {α : Type w4u5} {γ : α → Type w4v5} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) (k fb : α) (hk : k ∈ m₂) :
    (m₁ ∩ m₂).getKeyD k fb = m₁.getKeyD k fb := by
  have hb₁ := h₁.size_buckets_pos
  rw [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains] at hk
  split at hk
  · rename_i hb₂
    have e : m₁ ∩ m₂ = (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).1 := by
      show DHashMap.Raw.inter m₁ m₂ = _
      unfold DHashMap.Raw.inter; rw [dif_pos hb₁, dif_pos hb₂]
    have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
    obtain ⟨P, hperm, hP⟩ := r0_inter_perm ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
    rw [e]
    simp only [DHashMap.Raw.getKeyD, dif_pos (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).2, dif_pos hb₁]
    rw [Raw₀.getKeyD_eq_getKeyD wr, Raw₀.getKeyD_eq_getKeyD (Std.DHashMap.Internal.Raw.WF.out h₁),
      getKeyD_of_perm wr.distinct hperm, getKeyD_eq_getKey?, getKeyD_eq_getKey?,
      gk_filter _ _ _ (fun p _ hp => hP p hp)]
  · exact absurd hk (by simp)
end W4c2W
namespace W4c2W
open Std Std.DHashMap.Internal HashInstHand Std.Internal.List
universe w4u6 w4v6
-- inter with m₂ not WF, as in W3c1: the lookups of k in m₁ ∩ m₂ and m₁ agree (get?/get!/getKey?/getKey!)
theorem r0_inter_setup {α : Type w4u6} {γ : α → Type w4v6} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) (k : α) (hk : k ∈ m₂) :
    ∃ hb₁ : 0 < m₁.buckets.size, ∃ hb₂ : 0 < m₂.buckets.size, m₁ ∩ m₂ = (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).1 ∧
      Raw₀.contains ⟨m₂, hb₂⟩ k = true := by
  have hb₁ := h₁.size_buckets_pos
  rw [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains] at hk
  split at hk
  · rename_i hb₂
    refine ⟨hb₁, hb₂, ?_, hk⟩
    show DHashMap.Raw.inter m₁ m₂ = _
    unfold DHashMap.Raw.inter; rw [dif_pos hb₁, dif_pos hb₂]
  · exact absurd hk (by simp)
theorem drc_inter_get? {α : Type w4u6} {β : Type w4v6} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : DHashMap.Raw α (fun _ => β)) (h₁ : m₁.WF) (k : α) (hk : k ∈ m₂) :
    DHashMap.Raw.Const.get? (m₁ ∩ m₂) k = DHashMap.Raw.Const.get? m₁ k := by
  obtain ⟨hb₁, hb₂, e, hk⟩ := r0_inter_setup m₁ m₂ h₁ k hk
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
  obtain ⟨P, hperm, hP⟩ := r0_inter_perm ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
  rw [e]
  simp only [DHashMap.Raw.Const.get?, dif_pos (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).2, dif_pos hb₁]
  rw [Raw₀.Const.get?_eq_getValue? wr, Raw₀.Const.get?_eq_getValue? (Std.DHashMap.Internal.Raw.WF.out h₁),
    getValue?_of_perm wr.distinct hperm, gv_filter _ _ _ (fun p _ hp => hP p hp)]
theorem drc_inter_get! {α : Type w4u6} {β : Type w4v6} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [Inhabited β]
    (m₁ m₂ : DHashMap.Raw α (fun _ => β)) (h₁ : m₁.WF) (k : α) (hk : k ∈ m₂) :
    DHashMap.Raw.Const.get! (m₁ ∩ m₂) k = DHashMap.Raw.Const.get! m₁ k := by
  obtain ⟨hb₁, hb₂, e, hk⟩ := r0_inter_setup m₁ m₂ h₁ k hk
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
  obtain ⟨P, hperm, hP⟩ := r0_inter_perm ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
  rw [e]
  simp only [DHashMap.Raw.Const.get!, dif_pos (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).2, dif_pos hb₁]
  rw [Raw₀.Const.get!_eq_getValue! wr, Raw₀.Const.get!_eq_getValue! (Std.DHashMap.Internal.Raw.WF.out h₁),
    getValue!_of_perm wr.distinct hperm, getValue!_eq_getValue?, getValue!_eq_getValue?,
    gv_filter _ _ _ (fun p _ hp => hP p hp)]
theorem dr_inter_get? {α : Type w4u6} {γ : α → Type w4v6} [BEq α] [Hashable α] [LawfulBEq α]
    (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) (k : α) (hk : k ∈ m₂) :
    (m₁ ∩ m₂).get? k = m₁.get? k := by
  obtain ⟨hb₁, hb₂, e, hk⟩ := r0_inter_setup m₁ m₂ h₁ k hk
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
  obtain ⟨P, hperm, hP⟩ := r0_inter_perm ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
  rw [e]
  simp only [DHashMap.Raw.get?, dif_pos (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).2, dif_pos hb₁]
  rw [Raw₀.get?_eq_getValueCast? wr, Raw₀.get?_eq_getValueCast? (Std.DHashMap.Internal.Raw.WF.out h₁),
    getValueCast?_of_perm wr.distinct hperm, gvc_filter _ _ _ (fun p _ hp => hP p hp)]
theorem dr_inter_get! {α : Type w4u6} {γ : α → Type w4v6} [BEq α] [Hashable α] [LawfulBEq α]
    (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) (k : α) [Inhabited (γ k)] (hk : k ∈ m₂) :
    (m₁ ∩ m₂).get! k = m₁.get! k := by
  obtain ⟨hb₁, hb₂, e, hk⟩ := r0_inter_setup m₁ m₂ h₁ k hk
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
  obtain ⟨P, hperm, hP⟩ := r0_inter_perm ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
  rw [e]
  simp only [DHashMap.Raw.get!, dif_pos (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).2, dif_pos hb₁]
  rw [Raw₀.get!_eq_getValueCast! wr, Raw₀.get!_eq_getValueCast! (Std.DHashMap.Internal.Raw.WF.out h₁),
    getValueCast!_of_perm wr.distinct hperm, getValueCast!_eq_getValueCast?, getValueCast!_eq_getValueCast?,
    gvc_filter _ _ _ (fun p _ hp => hP p hp)]
theorem dr_inter_getKey? {α : Type w4u6} {γ : α → Type w4v6} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) (k : α) (hk : k ∈ m₂) :
    (m₁ ∩ m₂).getKey? k = m₁.getKey? k := by
  obtain ⟨hb₁, hb₂, e, hk⟩ := r0_inter_setup m₁ m₂ h₁ k hk
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
  obtain ⟨P, hperm, hP⟩ := r0_inter_perm ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
  rw [e]
  simp only [DHashMap.Raw.getKey?, dif_pos (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).2, dif_pos hb₁]
  rw [Raw₀.getKey?_eq_getKey? wr, Raw₀.getKey?_eq_getKey? (Std.DHashMap.Internal.Raw.WF.out h₁),
    getKey?_of_perm wr.distinct hperm, gk_filter _ _ _ (fun p _ hp => hP p hp)]
theorem dr_inter_getKey! {α : Type w4u6} {γ : α → Type w4v6} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) (k : α) (hk : k ∈ m₂) :
    (m₁ ∩ m₂).getKey! k = m₁.getKey! k := by
  obtain ⟨hb₁, hb₂, e, hk⟩ := r0_inter_setup m₁ m₂ h₁ k hk
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
  obtain ⟨P, hperm, hP⟩ := r0_inter_perm ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩ h₁ k hk
  rw [e]
  simp only [DHashMap.Raw.getKey!, dif_pos (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).2, dif_pos hb₁]
  rw [Raw₀.getKey!_eq_getKey! wr, Raw₀.getKey!_eq_getKey! (Std.DHashMap.Internal.Raw.WF.out h₁),
    getKey!_of_perm wr.distinct hperm, getKey!_eq_getKey?, getKey!_eq_getKey?,
    gk_filter _ _ _ (fun p _ hp => hP p hp)]
end W4c2W
namespace W4c2
open Std Std.DHashMap.Internal
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
-- the union is at least as large as its left argument (no laws, no WF)
theorem r0_unl (m₁ m₂ : Raw₀ α β) : m₁.1.size ≤ (m₁.union m₂).1.size := by
  unfold Raw₀.union; split
  · have := (m₂.insertManyIfNew m₁.1).2 (fun m' => m₂.1.size ≤ m'.1.size)
      (fun h => Nat.le_trans h (insertIfNew_size_ge _ _ _)) (Nat.le_refl _)
    omega
  · exact (m₁.insertMany m₂.1).2 (fun m' => m₁.1.size ≤ m'.1.size)
      (fun h => Nat.le_trans h (isg _ _ _)) (Nat.le_refl _)
-- isEmpty of a union needs WF only on the left: a WF m₁ of size 0 has no entries, so the union is m₂
theorem r0_iu [EquivBEq α] [LawfulHashable α] (m₁ m₂ : Raw₀ α β) (h₁ : m₁.1.WF) :
    (m₁.union m₂).1.isEmpty = (m₁.1.isEmpty && m₂.1.isEmpty) := by
  have w₁ : Raw.WFImp m₁.1 := Std.DHashMap.Internal.Raw.WF.out h₁
  by_cases h0 : m₁.1.size = 0
  · have hl : toListModel m₁.1.buckets = [] :=
      List.eq_nil_of_length_eq_zero (by rw [← Raw.size_eq_length w₁]; exact h0)
    rw [Raw₀.union_eq_unionₘ]; unfold Raw₀.unionₘ; rw [ite_cond_eq_true _ _ (eq_true (by omega)), hl]
    simp [DHashMap.Raw.isEmpty, h0, Raw₀.insertListIfNewₘ]
  · have := r0_unl m₁ m₂
    have a : ((m₁.union m₂).1.size == 0) = false := by simp; omega
    have b : (m₁.1.size == 0) = false := by simp; omega
    simp only [DHashMap.Raw.isEmpty, a, b, Bool.false_and]
end W4c2

/-! ## From `checks/W4c3Hand.lean` -/
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace W4c3
universe u4 v4
open Std Std.DHashMap.Internal HashInstHand
variable {α : Type u4} {β : Type v4} [BEq α] [Hashable α]
export W3c1 (hs_un)
export W3c1 (hs_in)
export W3c1 (hs_di)
export W3c1 (hsr_un)
export W3c1 (hsr_in)
export W3c1 (hsr_di)
export W3c1 (hm_un)
export W3c1 (hm_in)
export W3c1 (hm_di)
export W3c1 (hmr_un)
export W3c1 (hmr_in)
export W3c1 (hmr_di)
export W3c1 (dm_un)
export W3c1 (dm_in)
export W3c1 (dm_di)
export W3c1 (dr_diff_nil)
export W3c1 (dr_inter_nil)
export W3c1 (dr_union_nil)
export W3c1 (dr_union_nil2)
export W3c1 (dgetD_eval)
export W3c1 (zr_contains)
export W3c1 (assoc_cget?_none)
export W3c1 (r0_alter_same)
export W3c1 (r0c_alter_same)
export W3c1 (dhc_alter_same)
export W3c1 (hm_alter_same)
export W3c1 (r0g_wf)
export W3c1 (r0e_wf)
end W4c3
namespace W4c3
open Std Std.DHashMap.Internal HashInstHand
theorem zh_hash (a : W1c5.ZH) : hash a = 0 := rfl
theorem zh_contains0 {β : W1c5.ZH → Type v} (s : Nat) (l : AssocList W1c5.ZH β) (a : W1c5.ZH) :
    Raw₀.contains (⟨⟨s, #[l, .nil]⟩, by simp⟩ : Raw₀ W1c5.ZH β) a = l.contains a := by
  rw [contains_eval _ (by simp [Pow2])]
  have : ix #[l, .nil] a = 0 := by
    show (scrambleHash 0).toNat % 2 = 0
    rw [scr_small _ (by decide)]; rfl
  simp only [this]; rfl
end W4c3
namespace W4c3
open Std Std.DHashMap.Internal HashInstHand
section
universe u6 v6
variable {α : Type u6} {γ : α → Type v6} [BEq α] [Hashable α]
theorem ins_size_ge (m : Raw₀ α γ) (a : α) (b : γ a) : m.1.size ≤ (m.insert a b).1.size := by
  obtain ⟨⟨s, bs⟩, h⟩ := m; unfold Raw₀.insert; dsimp only; split
  · exact Nat.le_refl _
  · rw [S1.expand_size]; exact Nat.le_succ _
-- the union never has a smaller size field than its first argument (no laws, no WF)
theorem r0_union_ge (m₁ m₂ : Raw₀ α γ) : m₁.1.size ≤ (m₁.union m₂).1.size := by
  unfold Raw₀.union; split
  · rename_i hs
    exact (m₂.insertManyIfNew m₁.1).2 (fun m => m₁.1.size ≤ m.1.size)
      (fun h => Nat.le_trans h (S1.insertIfNew_size_ge _ _ _)) hs
  · exact (m₁.insertMany m₂.1).2 (fun m => m₁.1.size ≤ m.1.size) (fun h => Nat.le_trans h (ins_size_ge _ _ _)) (Nat.le_refl _)
theorem dr_union_ge (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) : m₁.size ≤ (m₁ ∪ m₂).size := by
  show m₁.size ≤ (DHashMap.Raw.union m₁ m₂).size
  unfold DHashMap.Raw.union; rw [dif_pos h₁.size_buckets_pos]; split
  · exact r0_union_ge ⟨m₁, _⟩ ⟨m₂, _⟩
  · exact Nat.le_refl _
theorem dm_union_ge (m₁ m₂ : DHashMap α γ) : m₁.size ≤ (m₁ ∪ m₂).size :=
  r0_union_ge ⟨m₁.1, _⟩ ⟨m₂.1, _⟩
theorem hm_union_ge {β : Type v6} (m₁ m₂ : HashMap α β) : m₁.size ≤ (m₁ ∪ m₂).size := dm_union_ge m₁.inner m₂.inner
theorem hs_union_ge (m₁ m₂ : HashSet α) : m₁.size ≤ (m₁ ∪ m₂).size := hm_union_ge m₁.inner m₂.inner
theorem hmr_union_ge {β : Type v6} (m₁ m₂ : HashMap.Raw α β) (h₁ : m₁.WF) : m₁.size ≤ (m₁ ∪ m₂).size :=
  dr_union_ge m₁.inner m₂.inner h₁.out
theorem hsr_union_ge (m₁ m₂ : HashSet.Raw α) (h₁ : m₁.WF) : m₁.size ≤ (m₁ ∪ m₂).size :=
  hmr_union_ge m₁.inner m₂.inner h₁.out
-- diff only filters or erases, so its size stays below the size of a WF m₁ (m₂ arbitrary)
theorem r0_diff_le [EquivBEq α] [LawfulHashable α] (m₁ m₂ : Raw₀ α γ) (h₁ : m₁.1.WF) :
    (m₁.diff m₂).1.size ≤ m₁.1.size := by
  unfold Raw₀.diff; split
  · exact Raw₀.size_filter_le_size (m := m₁) h₁
  · exact ((Raw₀.eraseManyEntries m₁ m₂.1).2 (fun m => m.1.WF ∧ m.1.size ≤ m₁.1.size)
      (fun ⟨hw, hs⟩ => ⟨DHashMap.Raw.WF.erase₀ hw, Nat.le_trans (Raw₀.size_erase_le (m := _) hw) hs⟩) ⟨h₁, Nat.le_refl _⟩).2
theorem dr_diff_le [EquivBEq α] [LawfulHashable α] (m₁ m₂ : DHashMap.Raw α γ) (h₁ : m₁.WF) :
    (m₁ \ m₂).size ≤ m₁.size := by
  show (DHashMap.Raw.diff m₁ m₂).size ≤ m₁.size
  unfold DHashMap.Raw.diff; rw [dif_pos h₁.size_buckets_pos]; split
  · exact r0_diff_le ⟨m₁, _⟩ ⟨m₂, _⟩ h₁
  · exact Nat.le_refl _
theorem hmr_diff_le [EquivBEq α] [LawfulHashable α] {β : Type v6} (m₁ m₂ : HashMap.Raw α β) (h₁ : m₁.WF) :
    (m₁ \ m₂).size ≤ m₁.size := dr_diff_le m₁.inner m₂.inner h₁.out
theorem hsr_diff_le [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashSet.Raw α) (h₁ : m₁.WF) :
    (m₁ \ m₂).size ≤ m₁.size := hmr_diff_le m₁.inner m₂.inner h₁.out
-- contains respects == on any raw map (bucket-level, no WF)
theorem r0_cc [EquivBEq α] [LawfulHashable α] (m : Raw₀ α γ) {a b : α} (hab : (a == b) = true) :
    m.contains a = m.contains b := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have hh : hash a = hash b := hash_eq hab
  unfold Raw₀.contains; dsimp only
  simp only [hh, AssocList.contains_eq]
  exact Std.Internal.List.containsKey_congr hab
theorem dr_cc [EquivBEq α] [LawfulHashable α] (m : DHashMap.Raw α γ) {a b : α} (hab : (a == b) = true) :
    m.contains a = m.contains b := by
  unfold DHashMap.Raw.contains; split
  · exact r0_cc _ hab
  · rfl
theorem hmr_cc [EquivBEq α] [LawfulHashable α] {β : Type v6} (m : HashMap.Raw α β) {a b : α} (hab : (a == b) = true) :
    m.contains a = m.contains b := dr_cc m.inner hab
theorem hsr_cc [EquivBEq α] [LawfulHashable α] (m : HashSet.Raw α) {a b : α} (hab : (a == b) = true) :
    m.contains a = m.contains b := hmr_cc m.inner hab
end
end W4c3
namespace W4c3
open Std Std.DHashMap.Internal
-- dependent getD with a constant value type is Const.getD (bucket level, no WF)
theorem r0_getD_const {α : Type} {β : Type} [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (fb : β) :
    m.getD a fb = Raw₀.Const.getD m a fb := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  simp only [Raw₀.getD, Raw₀.Const.getD, AssocList.getCastD_eq, AssocList.getD_eq]
  exact (Std.Internal.List.getValueD_eq_getValueCastD).symm
theorem dr_getD_const {α : Type} {β : Type} [BEq α] [LawfulBEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => β)) (a : α) (fb : β) :
    m.getD a fb = DHashMap.Raw.Const.getD m a fb := by
  simp only [DHashMap.Raw.getD, DHashMap.Raw.Const.getD]; split
  · exact r0_getD_const _ _ _
  · rfl
end W4c3
theorem w4c3_tlmD {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (P : ((a : α) × β a) → Prop) (l : List ((a : α) × β a)) :
    ∀ (m : Raw₀ α β), (∀ p ∈ toListModel m.1.buckets, P p) → (∀ a ∈ l, P a) →
      ∀ p ∈ toListModel (Raw₀.insertListₘ m l).1.buckets, P p := by
  induction l with
  | nil => intro m hm _; exact hm
  | cons hd tl ih =>
    intro m hm hl
    refine ih (m.insert hd.1 hd.2) (fun p hp => ?_) (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    rcases mem_tlm_insert m hd.1 hd.2 p hp with h | h
    · exact h ▸ hl hd List.mem_cons_self
    · exact hm p h
theorem w4c3_dr_entries {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (l : List ((a : α) × β a)) :
    ∀ p ∈ toListModel (DHashMap.Raw.ofList l).buckets, p ∈ l := by
  show ∀ p ∈ toListModel (DHashMap.Raw.insertMany ∅ l).buckets, p ∈ l
  unfold DHashMap.Raw.insertMany
  rw [dif_pos (show 0 < (∅ : DHashMap.Raw α β).buckets.size from (Raw₀.emptyWithCapacity 8).2)]
  rw [Raw₀.insertMany_eq_insertListₘ]
  exact w4c3_tlmD (· ∈ l) l _ (fun p hp => by simp [dr_empty, nil16, toListModel] at hp) (fun a ha => ha)
theorem w4c3_dm_entries {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (l : List ((a : α) × β a)) :
    ∀ p ∈ toListModel (DHashMap.ofList l).1.buckets, p ∈ l := by
  show ∀ p ∈ toListModel (Raw₀.insertMany Raw₀.emptyWithCapacity l).1.1.buckets, p ∈ l
  rw [Raw₀.insertMany_eq_insertListₘ]
  exact w4c3_tlmD (· ∈ l) l _ (by simp) (fun a ha => ha)
theorem w4c3_gkD {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [EquivBEq α] (l : List ((a : α) × β a)) (k k' : α)
    (hkk : (k == k') = true) (hl : l.Pairwise (fun a b => (a.1 == b.1) = false)) (hk : k ∈ l.map Sigma.fst)
    (m : Raw₀ α β) (hm : ∀ p ∈ toListModel m.1.buckets, p ∈ l) (hc : m.contains k' = true) :
    m.getKey k' hc = k := by
  obtain ⟨p, hp, h1, h2⟩ := raw0_getKey_mem m k' hc
  rw [← h1]
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hk
  exact congrArg Sigma.fst (pw_unique Sigma.fst l hl p w (hm p hp) hw (BEq.trans h2 (BEq.symm hkk)))
theorem w4c3_gk {α : Type u} {β : Type v} [BEq α] [Hashable α] [EquivBEq α] (l : List (α × β)) (k k' : α)
    (hkk : (k == k') = true) (hl : l.Pairwise (fun a b => (a.1 == b.1) = false)) (hk : k ∈ l.map Prod.fst)
    (m : Raw₀ α (fun _ => β)) (hm : ∀ p ∈ toListModel m.1.buckets, (p.1, p.2) ∈ l) (hc : m.contains k' = true) :
    m.getKey k' hc = k := by
  obtain ⟨p, hp, h1, h2⟩ := raw0_getKey_mem m k' hc
  rw [← h1]
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hk
  exact congrArg Prod.fst (pw_unique Prod.fst l hl (p.1, p.2) w (hm p hp) hw (BEq.trans h2 (BEq.symm hkk)))
macro "w4c3_fin" : tactic => `(tactic| first | done | decide | (simp; done) | (simp (config := {decide := true}); done))
theorem w4c3_get!_eval {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] [Hashable α] {s : Nat}
    {bs : Array (AssocList α β)} {h : 0 < bs.size} (a : α) [Inhabited (β a)] (hsz : Pow2 bs.size) :
    Raw₀.get! (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a = (bs[ix bs a]'(Nat.mod_lt _ h)).getCast! a := by
  simp only [Raw₀.get!, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]
theorem w4c3_getD_eval {α : Type u} {β : α → Type v} [BEq α] [LawfulBEq α] [Hashable α] {s : Nat}
    {bs : Array (AssocList α β)} {h : 0 < bs.size} (a : α) (fb : β a) (hsz : Pow2 bs.size) :
    Raw₀.getD (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a fb = (bs[ix bs a]'(Nat.mod_lt _ h)).getCastD a fb := by
  simp only [Raw₀.getD, mkIdx_eq _ _ _ hsz, Array.ugetElem_eq_getElem, idx_lt h _ hsz]
namespace W4c3
open Std Std.DHashMap.Internal HashInstHand
section
universe u7
variable {α : Type u7} [BEq α] [Hashable α]
-- keys stored by unitOfList come from l (no laws)
theorem uol_entries (l : List α) :
    ∀ p ∈ toListModel (DHashMap.Const.unitOfList l : DHashMap α (fun _ => Unit)).1.buckets, p.1 ∈ l := by
  have e : (DHashMap.Const.unitOfList l : DHashMap α (fun _ => Unit)).1 =
      (Raw₀.Const.insertListIfNewUnitₘ (Raw₀.emptyWithCapacity 8) l).1 := hs_ofList_raw l
  rw [e]
  exact tlm_insertListIfNewUnit (fun p => p.1 ∈ l) l _ (by simp) (fun a ha => ha)
theorem uolr_entries (l : List α) :
    ∀ p ∈ toListModel (DHashMap.Raw.Const.unitOfList l : DHashMap.Raw α (fun _ => Unit)).buckets, p.1 ∈ l := by
  have e : (DHashMap.Raw.Const.unitOfList l : DHashMap.Raw α (fun _ => Unit)) =
      (Raw₀.Const.insertListIfNewUnitₘ (Raw₀.emptyWithCapacity 8) l).1 := hsr_ofList_raw l
  rw [e]
  exact tlm_insertListIfNewUnit (fun p => p.1 ∈ l) l _ (by simp) (fun a ha => ha)
-- with EquivBEq, the stored key found for k' is the unique ==-match k of the distinct list
theorem gk_unit [EquivBEq α] (l : List α) (k k' : α) (hkk : (k == k') = true)
    (hl : l.Pairwise (fun a b => (a == b) = false)) (hk : k ∈ l)
    (m : Raw₀ α (fun _ => Unit)) (hm : ∀ p ∈ toListModel m.1.buckets, p.1 ∈ l) (hc : m.contains k' = true) :
    m.getKey k' hc = k := by
  obtain ⟨p, hp, h1, h2⟩ := raw0_getKey_mem m k' hc
  rw [← h1]
  exact pw_unique id l hl p.1 k (hm p hp) hk (BEq.trans h2 (BEq.symm hkk))
theorem gk_unit_raw [EquivBEq α] (l : List α) (k k' : α) (hkk : (k == k') = true)
    (hl : l.Pairwise (fun a b => (a == b) = false)) (hk : k ∈ l) (h : k' ∈ DHashMap.Raw.Const.unitOfList l) :
    (DHashMap.Raw.Const.unitOfList l).getKey k' h = k := by
  obtain ⟨hb, hc, e⟩ := dr_getKey_eq _ _ h
  rw [e]; exact gk_unit l k k' hkk hl hk _ (uolr_entries l) hc
end
end W4c3

/-! ## From `checks/W4c4Hand.lean` -/
set_option Elab.async false
namespace W4c4
@[simp] theorem zh_hash (a : W1c5.ZH) : hash a = 0 := rfl
section
variable {α : Type u} [BEq α] [Hashable α]
export W2c0 (r0u_mim)
export W2c0 (dru_mim)
end
section
variable {α : Type u} {β : α → Type v} {γ : α → Type w} [BEq α] [Hashable α]
-- filterMap / map / filter on literals and bundled maps, as Raw₀ literals
theorem dr_fm_lit (f : (a : α) → β a → Option (γ a)) (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) :
    DHashMap.Raw.filterMap f ⟨s, bs⟩ = (Raw₀.filterMap f ⟨⟨s, bs⟩, h⟩).1 := by simp [DHashMap.Raw.filterMap, h]
theorem dr_map_lit (f : (a : α) → β a → γ a) (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) :
    DHashMap.Raw.map f ⟨s, bs⟩ = (Raw₀.map f ⟨⟨s, bs⟩, h⟩).1 := by simp [DHashMap.Raw.map, h]
theorem dr_flt_lit (f : (a : α) → β a → Bool) (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) :
    DHashMap.Raw.filter f ⟨s, bs⟩ = (Raw₀.filter f ⟨⟨s, bs⟩, h⟩).1 := by simp [DHashMap.Raw.filter, h]
theorem dm_fm (f : (a : α) → β a → Option (γ a)) (m : DHashMap α β) (h) :
    (⟨(DHashMap.filterMap f m).1, h⟩ : Raw₀ α γ) = Raw₀.filterMap f ⟨m.1, m.2.size_buckets_pos⟩ := rfl
theorem dm_map (f : (a : α) → β a → γ a) (m : DHashMap α β) (h) :
    (⟨(DHashMap.map f m).1, h⟩ : Raw₀ α γ) = Raw₀.map f ⟨m.1, m.2.size_buckets_pos⟩ := rfl
theorem dm_flt (f : (a : α) → β a → Bool) (m : DHashMap α β) (h) :
    (⟨(DHashMap.filter f m).1, h⟩ : Raw₀ α β) = Raw₀.filter f ⟨m.1, m.2.size_buckets_pos⟩ := rfl
theorem r0_fm (f : (a : α) → β a → Option (γ a)) (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) :
    Raw₀.filterMap f ⟨⟨s, bs⟩, h⟩ = ⟨⟨computeSize (bs.map (AssocList.filterMap f)), bs.map (AssocList.filterMap f)⟩, by simpa using h⟩ := rfl
theorem r0_map (f : (a : α) → β a → γ a) (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) :
    Raw₀.map f ⟨⟨s, bs⟩, h⟩ = ⟨⟨s, bs.map (AssocList.map f)⟩, by simpa using h⟩ := rfl
theorem r0_flt (f : (a : α) → β a → Bool) (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) :
    Raw₀.filter f ⟨⟨s, bs⟩, h⟩ = ⟨⟨computeSize (bs.map (AssocList.filter f)), bs.map (AssocList.filter f)⟩, by simpa using h⟩ := rfl
end
end W4c4
namespace W4c4
/-- `HZ0`: `a == b ↔ a/2 = b/2`, hash 0: `EquivBEq` and `LawfulHashable` hold, `LawfulBEq` fails. -/
structure HZ0 where n : Nat deriving DecidableEq, Inhabited
instance : BEq HZ0 := ⟨fun a b => a.n / 2 == b.n / 2⟩
instance : Hashable HZ0 := ⟨fun _ => 0⟩
instance : EquivBEq HZ0 where
  symm h := by simp_all [BEq.beq]
  trans h₁ h₂ := by simp_all [BEq.beq]
  rfl := by simp [BEq.beq]
instance : LawfulHashable HZ0 := ⟨fun _ _ _ => rfl⟩
end W4c4
namespace W4c4
theorem dm_empty0 {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (h) :
    (⟨(∅ : DHashMap α β).inner, h⟩ : Raw₀ α β) = ⟨⟨0, nil16⟩, by simp [nil16]⟩ := Subtype.ext dm_empty
end W4c4
namespace W4c4
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
-- the intersection holds at most m₁'s entries; only m₁ needs to be well-formed (after Probe2's p24)
theorem sil [EquivBEq α] [LawfulHashable α] (m₁ m₂ : DHashMap.Raw α β) (hb₁ : 0 < m₁.buckets.size)
    (hb₂ : 0 < m₂.buckets.size) (w₁ : Raw.WFImp m₁) : (Raw₀.inter ⟨m₁, hb₁⟩ ⟨m₂, hb₂⟩).1.size ≤ m₁.size := by
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) w₁
  rw [wr.size_eq, w₁.size_eq]
  unfold Raw₀.inter
  split
  · exact (Raw₀.toListModel_filter).length_eq ▸ List.length_filter_le _ _
  · rw [Raw₀.interSmaller_eq_interSmallerₘ]
    exact ((Raw₀.toListModel_interSmallerₘ ⟨m₁, hb₁⟩ m₂ w₁).trans
      (Std.Internal.List.interSmaller_perm_filter _ _ w₁.distinct)).length_eq ▸ List.length_filter_le _ _
theorem dr_sil [EquivBEq α] [LawfulHashable α] (m₁ m₂ : DHashMap.Raw α β) (h₁ : m₁.WF) :
    (m₁ ∩ m₂).size ≤ m₁.size := by
  show (DHashMap.Raw.inter m₁ m₂).size ≤ m₁.size
  unfold DHashMap.Raw.inter; rw [dif_pos h₁.size_buckets_pos]; split
  · exact sil m₁ m₂ _ _ (Std.DHashMap.Internal.Raw.WF.out h₁)
  · exact Nat.le_refl _
end
end W4c4

/-! ## From `checks/W4c5Hand.lean` -/
namespace W4c5
open Std Std.DHashMap.Internal Probe2
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
-- bucket lookups when contains finds the key (no laws); copies of W3c4's a_*_some plus get! versions
theorem a_cget?_d [BEq α] (l : AssocList α (fun _ => γ)) (k : α) (fb : γ) (h : l.contains k = true) :
    l.get? k = some (l.getD k fb) := by
  induction l with
  | nil => cases h
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_true] at h
    cases hk : (k' == k) <;> simp_all [AssocList.get?, AssocList.getD]
theorem a_cget?_b [BEq α] [Inhabited γ] (l : AssocList α (fun _ => γ)) (k : α) (h : l.contains k = true) :
    l.get? k = some (l.get! k) := by
  induction l with
  | nil => cases h
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_true] at h
    cases hk : (k' == k) <;> simp_all [AssocList.get?, AssocList.get!]
theorem a_getKey?_d [BEq α] (l : AssocList α β) (k : α) (fb : α) (h : l.contains k = true) :
    l.getKey? k = some (l.getKeyD k fb) := by
  induction l with
  | nil => cases h
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_true] at h
    cases hk : (k' == k) <;> simp_all [AssocList.getKey?, AssocList.getKeyD]
theorem a_getKey?_b [BEq α] [Inhabited α] (l : AssocList α β) (k : α) (h : l.contains k = true) :
    l.getKey? k = some (l.getKey! k) := by
  induction l with
  | nil => cases h
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_true] at h
    cases hk : (k' == k) <;> simp_all [AssocList.getKey?, AssocList.getKey!]
theorem a_getCast?_d [BEq α] [LawfulBEq α] (l : AssocList α β) (k : α) (fb : β k) (h : l.contains k = true) :
    l.getCast? k = some (l.getCastD k fb) := by
  induction l with
  | nil => cases h
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_true] at h
    cases hk : (k' == k) <;> simp_all [AssocList.getCast?, AssocList.getCastD]
theorem a_getCast?_b [BEq α] [LawfulBEq α] (l : AssocList α β) (k : α) [Inhabited (β k)] (h : l.contains k = true) :
    l.getCast? k = some (l.getCast! k) := by
  induction l with
  | nil => cases h
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_true] at h
    cases hk : (k' == k) <;> simp_all [AssocList.getCast?, AssocList.getCast!]
theorem a_getKeyD_nc [BEq α] (l : AssocList α β) (a fb : α) (h : l.contains a = false) : l.getKeyD a fb = fb := by
  induction l with
  | nil => rfl
  | cons k' v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.getKeyD, h.1]; exact ih h.2
-- Raw₀ level
theorem r0c_gd [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (k : α) (fb : γ) (h : m.contains k = true) :
    Raw₀.Const.get? m k = some (Raw₀.Const.getD m k fb) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.Const.get? Raw₀.Const.getD; simp only [Array.ugetElem_eq_getElem]
  exact a_cget?_d _ _ _ h
theorem r0c_gb [BEq α] [Hashable α] [Inhabited γ] (m : Raw₀ α (fun _ => γ)) (k : α) (h : m.contains k = true) :
    Raw₀.Const.get? m k = some (Raw₀.Const.get! m k) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.Const.get? Raw₀.Const.get!; simp only [Array.ugetElem_eq_getElem]
  exact a_cget?_b _ _ h
theorem r0_kd [BEq α] [Hashable α] (m : Raw₀ α β) (k : α) (fb : α) (h : m.contains k = true) :
    m.getKey? k = some (m.getKeyD k fb) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.getKey? Raw₀.getKeyD; simp only [Array.ugetElem_eq_getElem]
  exact a_getKey?_d _ _ _ h
theorem r0_kb [BEq α] [Hashable α] [Inhabited α] (m : Raw₀ α β) (k : α) (h : m.contains k = true) :
    m.getKey? k = some (m.getKey! k) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.getKey? Raw₀.getKey!; simp only [Array.ugetElem_eq_getElem]
  exact a_getKey?_b _ _ h
theorem r0_gd [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k : α) (fb : β k) (h : m.contains k = true) :
    m.get? k = some (m.getD k fb) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.get? Raw₀.getD; simp only [Array.ugetElem_eq_getElem]
  exact a_getCast?_d _ _ _ h
theorem r0_gb [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k : α) [Inhabited (β k)] (h : m.contains k = true) :
    m.get? k = some (m.get! k) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.get? Raw₀.get!; simp only [Array.ugetElem_eq_getElem]
  exact a_getCast?_b _ _ h
theorem r0_kD [BEq α] [Hashable α] (m : Raw₀ α β) (a fb : α) (h : m.contains a = false) :
    m.getKeyD a fb = fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.getKeyD; simp only [Array.ugetElem_eq_getElem]
  exact a_getKeyD_nc _ _ _ h
-- DHashMap.Raw level (no buckets: contains is false)
theorem dr_pos [BEq α] [Hashable α] {m : DHashMap.Raw α β} {k : α} (h : m.contains k = true) :
    ∃ hb : 0 < m.buckets.size, Raw₀.contains ⟨m, hb⟩ k = true := by
  unfold DHashMap.Raw.contains at h; split at h
  · exact ⟨_, h⟩
  · cases h
theorem dr_neg [BEq α] [Hashable α] {m : DHashMap.Raw α β} {k : α} (h : m.contains k = false)
    (hb : 0 < m.buckets.size) : Raw₀.contains ⟨m, hb⟩ k = false := by
  unfold DHashMap.Raw.contains at h; rw [dite_eq_left hb] at h; exact h
theorem drc_gd [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => γ)) (k : α) (fb : γ) (h : m.contains k = true) :
    DHashMap.Raw.Const.get? m k = some (DHashMap.Raw.Const.getD m k fb) := by
  obtain ⟨hb, h⟩ := dr_pos h
  unfold DHashMap.Raw.Const.get? DHashMap.Raw.Const.getD; rw [dite_eq_left hb, dite_eq_left hb]; exact r0c_gd _ _ _ h
theorem drc_gb [BEq α] [Hashable α] [Inhabited γ] (m : DHashMap.Raw α (fun _ => γ)) (k : α) (h : m.contains k = true) :
    DHashMap.Raw.Const.get? m k = some (DHashMap.Raw.Const.get! m k) := by
  obtain ⟨hb, h⟩ := dr_pos h
  unfold DHashMap.Raw.Const.get? DHashMap.Raw.Const.get!; rw [dite_eq_left hb, dite_eq_left hb]; exact r0c_gb _ _ h
theorem dr_kd [BEq α] [Hashable α] (m : DHashMap.Raw α β) (k : α) (fb : α) (h : m.contains k = true) :
    m.getKey? k = some (m.getKeyD k fb) := by
  obtain ⟨hb, h⟩ := dr_pos h
  unfold DHashMap.Raw.getKey? DHashMap.Raw.getKeyD; rw [dite_eq_left hb, dite_eq_left hb]; exact r0_kd _ _ _ h
theorem dr_kb [BEq α] [Hashable α] [Inhabited α] (m : DHashMap.Raw α β) (k : α) (h : m.contains k = true) :
    m.getKey? k = some (m.getKey! k) := by
  obtain ⟨hb, h⟩ := dr_pos h
  unfold DHashMap.Raw.getKey? DHashMap.Raw.getKey!; rw [dite_eq_left hb, dite_eq_left hb]; exact r0_kb _ _ h
theorem dr_gd [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k : α) (fb : β k) (h : m.contains k = true) :
    m.get? k = some (m.getD k fb) := by
  obtain ⟨hb, h⟩ := dr_pos h
  unfold DHashMap.Raw.get? DHashMap.Raw.getD; rw [dite_eq_left hb, dite_eq_left hb]; exact r0_gd _ _ _ h
theorem dr_gb [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k : α) [Inhabited (β k)] (h : m.contains k = true) :
    m.get? k = some (m.get! k) := by
  obtain ⟨hb, h⟩ := dr_pos h
  unfold DHashMap.Raw.get? DHashMap.Raw.get!; rw [dite_eq_left hb, dite_eq_left hb]; exact r0_gb _ _ h
theorem dr_kD [BEq α] [Hashable α] (m : DHashMap.Raw α β) (a fb : α) (h : m.contains a = false) :
    m.getKeyD a fb = fb := by
  unfold DHashMap.Raw.getKeyD; split
  · exact r0_kD _ _ _ (dr_neg h ‹_›)
  · rfl
theorem dr_kB [BEq α] [Hashable α] [Inhabited α] (m : DHashMap.Raw α β) (a : α) (h : m.contains a = false) :
    m.getKey! a = default := by
  unfold DHashMap.Raw.getKey!; split
  · exact raw0_getKey!_nc _ _ (dr_neg h ‹_›)
  · rfl
theorem drc_gB [BEq α] [Hashable α] [Inhabited γ] (m : DHashMap.Raw α (fun _ => γ)) (a : α) (h : m.contains a = false) :
    DHashMap.Raw.Const.get! m a = default := by
  unfold DHashMap.Raw.Const.get!; split
  · exact raw0_cget!_nc _ _ (dr_neg h ‹_›)
  · rfl
theorem dr_gB [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (a : α) [Inhabited (β a)] (h : m.contains a = false) :
    m.get! a = default := by
  unfold DHashMap.Raw.get!; split
  · exact raw0_get!_nc _ _ (dr_neg h ‹_›)
  · rfl
theorem dr_filter_c [BEq α] [Hashable α] (f : (a : α) → β a → Bool) (m : DHashMap.Raw α β) (k : α)
    (h : (m.filter f).contains k = true) : m.contains k = true := by
  unfold DHashMap.Raw.filter at h; split at h
  · rename_i hb
    obtain ⟨hb', h⟩ := dr_pos h
    have := raw0_filter_contains f ⟨m, hb⟩ k h
    unfold DHashMap.Raw.contains; rw [dite_eq_left hb]; exact this
  · simp [DHashMap.Raw.contains_empty] at h
theorem dr_map_c [BEq α] [Hashable α] {δ : α → Type w} (f : (a : α) → β a → δ a) (m : DHashMap.Raw α β) (k : α)
    (h : (m.map f).contains k = true) : m.contains k = true := by
  rw [dr_map_contains] at h; exact h
end
end W4c5
namespace W4c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v}
theorem al_gk [BEq α] (a k0 : α) (v0 : β k0) (es : AssocList α β) (hk : (k0 == a) = true) (P : α → Prop) (hP : P k0) :
    ∀ (L : AssocList α β) (_ : L = .cons k0 v0 es) (hc : L.contains a = true), P (L.getKey a hc) := by
  intro L hL hc; subst hL; simp [AssocList.getKey, hk, hP]
theorem arr2 (c : AssocList α β) : ∀ (i : Nat) (hi : i < (#[c, c] : Array (AssocList α β)).size), (#[c, c] : Array _)[i] = c := by
  intro i hi; simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
-- two equal buckets: every successful key lookup returns the first key of the bucket
theorem gk2 [BEq α] [Hashable α] (s : Nat) (k0 : α) (v0 : β k0) (es : AssocList α β) (a : α)
    (hk : (k0 == a) = true) (h) (hc) (P : α → Prop) (hP : P k0) :
    P (Raw₀.getKey ⟨⟨s, #[.cons k0 v0 es, .cons k0 v0 es]⟩, h⟩ a hc) := by
  unfold Raw₀.getKey
  exact al_gk a k0 v0 es hk P hP _ (arr2 _ _ _) _
end
end W4c5
open W4c5
set_option Elab.async false

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

/-! Elaborate synchronously: about 40% lower peak memory for large cluster files (W3c2). -/
set_option Elab.async false

/-! Canonical opens: after `import Tk` in a scratch file, repeat this line. -/
open Std Std.DHashMap.Internal Std.DTreeMap.Internal HashInstHand Probe2 P3 S1

/-! # W7c3 helpers -/
/-! W7c3: Raw toList/fold/forIn/insertMany stems need no WF: the Raw₀ lemmas need only buckets, and a bucketless raw map makes both sides trivial -/
namespace W7c3
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem bk {P : DHashMap.Raw α β → Prop} (m : DHashMap.Raw α β) (h0 : ∀ s, P ⟨s, #[]⟩)
    (h1 : ∀ hb : 0 < m.buckets.size, P m) : P m := by
  by_cases hb : 0 < m.buckets.size
  · exact h1 hb
  · obtain ⟨s, bs⟩ := m
    obtain rfl : bs = #[] := Array.eq_empty_of_size_eq_zero (Nat.eq_zero_of_not_pos hb)
    exact h0 s
theorem dr_all {m : DHashMap.Raw α β} {p : (a : α) → β a → Bool} :
    m.toList.all (fun x => p x.1 x.2) = m.all p :=
  bk (P := fun m => m.toList.all (fun x => p x.1 x.2) = m.all p) m (fun _ => rfl) (fun hb => Raw₀.all_toList ⟨m, hb⟩)
theorem dr_any {m : DHashMap.Raw α β} {p : (a : α) → β a → Bool} :
    m.toList.any (fun x => p x.1 x.2) = m.any p :=
  bk (P := fun m => m.toList.any (fun x => p x.1 x.2) = m.any p) m (fun _ => rfl) (fun hb => Raw₀.any_toList ⟨m, hb⟩)
theorem drc_all {γ : Type v} {m : DHashMap.Raw α (fun _ => γ)} {p : α → γ → Bool} :
    (DHashMap.Raw.Const.toList m).all (fun x => p x.1 x.2) = m.all p :=
  bk (P := fun m => (DHashMap.Raw.Const.toList m).all (fun x => p x.1 x.2) = m.all p) m (fun _ => rfl) (fun hb => Raw₀.Const.all_toList ⟨m, hb⟩)
theorem drc_any {γ : Type v} {m : DHashMap.Raw α (fun _ => γ)} {p : α → γ → Bool} :
    (DHashMap.Raw.Const.toList m).any (fun x => p x.1 x.2) = m.any p :=
  bk (P := fun m => (DHashMap.Raw.Const.toList m).any (fun x => p x.1 x.2) = m.any p) m (fun _ => rfl) (fun hb => Raw₀.Const.any_toList ⟨m, hb⟩)
theorem dr_tat {m : DHashMap.Raw α β} : m.toList.toArray = m.toArray :=
  bk (P := fun m => m.toList.toArray = m.toArray) m (fun _ => rfl) (fun hb => Raw₀.toArray_toList_eq_toArray ⟨m, hb⟩)
theorem dr_tta {m : DHashMap.Raw α β} : m.toArray.toList = m.toList :=
  bk (P := fun m => m.toArray.toList = m.toList) m (fun _ => rfl) (fun hb => Raw₀.toList_toArray_eq_toList ⟨m, hb⟩)
theorem drc_tat {γ : Type v} {m : DHashMap.Raw α (fun _ => γ)} : (DHashMap.Raw.Const.toList m).toArray = DHashMap.Raw.Const.toArray m :=
  bk (P := fun m => (DHashMap.Raw.Const.toList m).toArray = DHashMap.Raw.Const.toArray m) m (fun _ => rfl) (fun hb => Raw₀.Const.toArray_toList_eq_toArray ⟨m, hb⟩)
theorem drc_tta {γ : Type v} {m : DHashMap.Raw α (fun _ => γ)} : (DHashMap.Raw.Const.toArray m).toList = DHashMap.Raw.Const.toList m :=
  bk (P := fun m => (DHashMap.Raw.Const.toArray m).toList = DHashMap.Raw.Const.toList m) m (fun _ => rfl) (fun hb => Raw₀.Const.toList_toArray_eq_toList ⟨m, hb⟩)
theorem dr_ftl {δ : Type w} {m : DHashMap.Raw α β} {f : δ → (a : α) → β a → δ} {init : δ} :
    m.fold f init = m.toList.foldl (fun a b => f a b.1 b.2) init :=
  bk (P := fun m => m.fold f init = m.toList.foldl (fun a b => f a b.1 b.2) init) m (fun _ => rfl) (fun hb => Raw₀.fold_eq_foldl_toList ⟨m, hb⟩)
theorem drc_ftl {γ : Type v} {δ : Type w} {m : DHashMap.Raw α (fun _ => γ)} {f : δ → α → γ → δ} {init : δ} :
    m.fold f init = (DHashMap.Raw.Const.toList m).foldl (fun a b => f a b.1 b.2) init :=
  bk (P := fun m => m.fold f init = (DHashMap.Raw.Const.toList m).foldl (fun a b => f a b.1 b.2) init) m (fun _ => rfl) (fun hb => Raw₀.Const.fold_eq_foldl_toList ⟨m, hb⟩)
theorem dr_fta {δ : Type w} {m : DHashMap.Raw α β} {f : δ → (a : α) → β a → δ} {init : δ} :
    m.fold f init = m.toArray.foldl (fun a b => f a b.1 b.2) init :=
  bk (P := fun m => m.fold f init = m.toArray.foldl (fun a b => f a b.1 b.2) init) m (fun _ => rfl) (fun hb => Raw₀.fold_eq_foldl_toArray ⟨m, hb⟩)
theorem drc_fta {γ : Type v} {δ : Type w} {m : DHashMap.Raw α (fun _ => γ)} {f : δ → α → γ → δ} {init : δ} :
    m.fold f init = (DHashMap.Raw.Const.toArray m).foldl (fun a b => f a b.1 b.2) init :=
  bk (P := fun m => m.fold f init = (DHashMap.Raw.Const.toArray m).foldl (fun a b => f a b.1 b.2) init) m (fun _ => rfl) (fun hb => Raw₀.Const.fold_eq_foldl_toArray ⟨m, hb⟩)
theorem dk_fta {δ : Type w} {m : DHashMap.Raw α β} {f : δ → α → δ} {init : δ} :
    m.fold (fun d a _ => f d a) init = m.keysArray.foldl f init :=
  bk (P := fun m => m.fold (fun d a _ => f d a) init = m.keysArray.foldl f init) m (fun _ => rfl) (fun hb => Raw₀.fold_eq_foldl_keysArray ⟨m, hb⟩)
theorem dk_ftl {δ : Type w} {m : DHashMap.Raw α β} {f : δ → α → δ} {init : δ} :
    m.fold (fun d a _ => f d a) init = m.keys.foldl f init :=
  bk (P := fun m => m.fold (fun d a _ => f d a) init = m.keys.foldl f init) m (fun _ => rfl) (fun hb => Raw₀.fold_eq_foldl_keys ⟨m, hb⟩)
theorem dr_fmka {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {m : DHashMap.Raw α β} {f : δ → α → m' δ} {init : δ} :
    m.foldM (fun d a _ => f d a) init = m.keysArray.foldlM f init :=
  bk (P := fun m => m.foldM (fun d a _ => f d a) init = m.keysArray.foldlM f init) m (fun _ => rfl) (fun hb => Raw₀.foldM_eq_foldlM_keysArray ⟨m, hb⟩)
theorem dr_fmk {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {m : DHashMap.Raw α β} {f : α → m' PUnit} :
    m.forM (fun a _ => f a) = m.keysArray.forM f :=
  bk (P := fun m => m.forM (fun a _ => f a) = m.keysArray.forM f) m (fun _ => rfl) (fun hb => Raw₀.forM_eq_forM_keysArray ⟨m, hb⟩)
theorem dr_fika {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {m : DHashMap.Raw α β} {f : α → δ → m' (ForInStep δ)} {init : δ} :
    m.forIn (fun a _ d => f a d) init = ForIn.forIn m.keysArray init f :=
  bk (P := fun m => m.forIn (fun a _ d => f a d) init = ForIn.forIn m.keysArray init f) m (fun _ => rfl) (fun hb => Raw₀.forIn_eq_forIn_keysArray ⟨m, hb⟩)
theorem dr_fik {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {m : DHashMap.Raw α β} {f : α → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init (fun a d => f a.1 d) = ForIn.forIn m.keys init f :=
  bk (P := fun m => ForIn.forIn m init (fun a d => f a.1 d) = ForIn.forIn m.keys init f) m (fun _ => rfl) (fun hb => Raw₀.forIn_eq_forIn_keys ⟨m, hb⟩)
end W7c3
/-! W7c3: Raw insertMany over a list is the foldl of Raw inserts on any raw map (bucketless: both stay put) -/
namespace W7c3
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem r0_fv (m : Raw₀ α β) (l : List ((a : α) × β a)) :
    (l.foldl (fun a b => a.insert b.1 b.2) m).1 = l.foldl (fun acc p => acc.insert p.1 p.2) m.1 := by
  induction l generalizing m with
  | nil => rfl
  | cons p t ih => simp only [List.foldl_cons]; rw [ih]; congr 1; simp [DHashMap.Raw.insert, m.2]
theorem e_fv (s : Nat) (l : List ((a : α) × β a)) :
    l.foldl (fun acc p => acc.insert p.1 p.2) (⟨s, #[]⟩ : DHashMap.Raw α β) = ⟨s, #[]⟩ := by
  induction l with
  | nil => rfl
  | cons p t ih => simp only [List.foldl_cons]; rw [show (⟨s, #[]⟩ : DHashMap.Raw α β).insert p.1 p.2 = ⟨s, #[]⟩ by simp [DHashMap.Raw.insert]]; exact ih
theorem dr_imf (m : DHashMap.Raw α β) (l : List ((a : α) × β a)) :
    m.insertMany l = l.foldl (fun acc p => acc.insert p.1 p.2) m :=
  bk (P := fun m => m.insertMany l = l.foldl (fun acc p => acc.insert p.1 p.2) m) m
    (fun s => by rw [e_fv]; simp [DHashMap.Raw.insertMany])
    (fun hb => by rw [DHashMap.Raw.insertMany, dif_pos hb, Raw₀.insertMany_list_eq_foldl, r0_fv])
end W7c3
namespace W7c3
variable {α : Type u} [BEq α] [Hashable α]
theorem r0c_fv {γ : Type v} (m : Raw₀ α (fun _ => γ)) (l : List (α × γ)) :
    (l.foldl (fun a b => a.insert b.1 b.2) m).1 = l.foldl (fun acc p => acc.insert p.1 p.2) m.1 := by
  induction l generalizing m with
  | nil => rfl
  | cons p t ih => simp only [List.foldl_cons]; rw [ih]; congr 1; simp [DHashMap.Raw.insert, m.2]
theorem ec_fv {γ : Type v} (s : Nat) (l : List (α × γ)) :
    l.foldl (fun acc p => acc.insert p.1 p.2) (⟨s, #[]⟩ : DHashMap.Raw α (fun _ => γ)) = ⟨s, #[]⟩ := by
  induction l with
  | nil => rfl
  | cons p t ih => simp only [List.foldl_cons]; rw [show (⟨s, #[]⟩ : DHashMap.Raw α (fun _ => γ)).insert p.1 p.2 = ⟨s, #[]⟩ by simp [DHashMap.Raw.insert]]; exact ih
theorem drc_imf {γ : Type v} (m : DHashMap.Raw α (fun _ => γ)) (l : List (α × γ)) :
    DHashMap.Raw.Const.insertMany m l = l.foldl (fun acc p => acc.insert p.1 p.2) m :=
  bk (P := fun m => DHashMap.Raw.Const.insertMany m l = l.foldl (fun acc p => acc.insert p.1 p.2) m) m
    (fun s => by rw [ec_fv]; simp [DHashMap.Raw.Const.insertMany])
    (fun hb => by rw [DHashMap.Raw.Const.insertMany, dif_pos hb, Raw₀.Const.insertMany_list_eq_foldl, r0c_fv])
theorem r0u_fv (m : Raw₀ α (fun _ => Unit)) (l : List α) :
    (l.foldl (fun a b => a.insertIfNew b ()) m).1 = l.foldl (fun acc p => acc.insertIfNew p ()) m.1 := by
  induction l generalizing m with
  | nil => rfl
  | cons p t ih => simp only [List.foldl_cons]; rw [ih]; congr 1; simp [DHashMap.Raw.insertIfNew, m.2]
theorem eu_fv (s : Nat) (l : List α) :
    l.foldl (fun acc p => acc.insertIfNew p ()) (⟨s, #[]⟩ : DHashMap.Raw α (fun _ => Unit)) = ⟨s, #[]⟩ := by
  induction l with
  | nil => rfl
  | cons p t ih => simp only [List.foldl_cons]; rw [show (⟨s, #[]⟩ : DHashMap.Raw α (fun _ => Unit)).insertIfNew p () = ⟨s, #[]⟩ by simp [DHashMap.Raw.insertIfNew]]; exact ih
theorem dru_imf (m : DHashMap.Raw α (fun _ => Unit)) (l : List α) :
    DHashMap.Raw.Const.insertManyIfNewUnit m l = l.foldl (fun acc p => acc.insertIfNew p ()) m :=
  bk (P := fun m => DHashMap.Raw.Const.insertManyIfNewUnit m l = l.foldl (fun acc p => acc.insertIfNew p ()) m) m
    (fun s => by rw [eu_fv]; simp [DHashMap.Raw.Const.insertManyIfNewUnit])
    (fun hb => by rw [DHashMap.Raw.Const.insertManyIfNewUnit, dif_pos hb, Raw₀.Const.insertManyIfNewUnit_list_eq_foldl, r0u_fv])
theorem hmr_imf {γ : Type v} (m : HashMap.Raw α γ) (l : List (α × γ)) :
    m.insertMany l = l.foldl (fun acc p => acc.insert p.1 p.2) m := by
  obtain ⟨m⟩ := m
  simp only [HashMap.Raw.insertMany, drc_imf]
  induction l generalizing m with
  | nil => rfl
  | cons p t ih => simp only [List.foldl_cons]; exact ih _
theorem hsr_imf (m : HashSet.Raw α) (l : List α) :
    m.insertMany l = l.foldl (fun acc p => acc.insert p) m := by
  obtain ⟨⟨m⟩⟩ := m
  simp only [HashSet.Raw.insertMany, HashMap.Raw.insertManyIfNewUnit, dru_imf]
  induction l generalizing m with
  | nil => rfl
  | cons p t ih => simp only [List.foldl_cons]; exact ih _
end W7c3
namespace W7c3
variable {α : Type u} [BEq α] [Hashable α]
theorem dk_tat {β : α → Type v} {m : DHashMap.Raw α β} : m.keys.toArray = m.keysArray :=
  bk (P := fun m => m.keys.toArray = m.keysArray) m (fun _ => rfl) (fun hb => Raw₀.toArray_keys_eq_keysArray ⟨m, hb⟩)
theorem dk_tta {β : α → Type v} {m : DHashMap.Raw α β} : m.keysArray.toList = m.keys :=
  bk (P := fun m => m.keysArray.toList = m.keys) m (fun _ => rfl) (fun hb => Raw₀.toList_keysArray_eq_keys ⟨m, hb⟩)
theorem dk_any {γ : Type v} [LawfulHashable α] [EquivBEq α] {m : DHashMap.Raw α (fun _ => γ)} {p : α → Bool} :
    m.keys.any p = m.any (fun a _ => p a) :=
  bk (P := fun m => m.keys.any p = m.any (fun a _ => p a)) m (fun _ => rfl) (fun hb => Raw₀.Const.any_keys ⟨m, hb⟩)
theorem dk_all {γ : Type v} [LawfulHashable α] [EquivBEq α] {m : DHashMap.Raw α (fun _ => γ)} {p : α → Bool} :
    m.keys.all p = m.all (fun a _ => p a) :=
  bk (P := fun m => m.keys.all p = m.all (fun a _ => p a)) m (fun _ => rfl) (fun hb => Raw₀.Const.all_keys ⟨m, hb⟩)
end W7c3

/-! W7c3: dependent ofList / insertListₘ never empty (any instances) -/
namespace W7c3
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem tlm_il_ne_nil (tl : List ((a : α) × β a)) :
    ∀ (m : Raw₀ α β) (hd : (a : α) × β a), toListModel (Raw₀.insertListₘ m (hd :: tl)).1.buckets ≠ [] := by
  induction tl with
  | nil => intro m hd; exact tlm_insert_ne_nil m hd.1 hd.2
  | cons hd' tl ih => intro m hd; exact ih (m.insert hd.1 hd.2) hd'
theorem dm_ofList_raw (l : List ((a : α) × β a)) :
    (DHashMap.ofList l).1 = (Raw₀.insertListₘ (Raw₀.emptyWithCapacity 8) l).1 := by
  show (Raw₀.insertMany _ l).1.1 = _
  rw [Raw₀.insertMany_eq_insertListₘ]; rfl
end W7c3

/-! W7c3: under LawfulBEq a stored key found by getKey!/getKeyD is the query itself; no WF needed (the lookup scans the query's bucket) -/
namespace W7c3
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem al_k! [LawfulBEq α] [Inhabited α] (l : AssocList α β) (a : α) (h : l.contains a = true) : l.getKey! a = a := by
  rw [AssocList.contains_eq] at h
  rw [AssocList.getKey!_eq, Std.Internal.List.getKey!_eq_getKey?, Std.Internal.List.getKey?_eq_some_getKey h]
  exact eq_of_beq (Std.Internal.List.getKey_beq h)
theorem al_kD [LawfulBEq α] (l : AssocList α β) (a fb : α) (h : l.contains a = true) : l.getKeyD a fb = a := by
  rw [AssocList.contains_eq] at h
  rw [AssocList.getKeyD_eq, Std.Internal.List.getKeyD_eq_getKey?, Std.Internal.List.getKey?_eq_some_getKey h]
  exact eq_of_beq (Std.Internal.List.getKey_beq h)
theorem dr_k! [LawfulBEq α] [Inhabited α] (m : DHashMap.Raw α β) (a : α) (h : m.contains a = true) : m.getKey! a = a := by
  obtain ⟨hb, h⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.getKey!; rw [dif_pos hb]
  obtain ⟨s, bs⟩ := m
  rw [contains_gen] at h
  unfold Raw₀.getKey!; simp only [Array.ugetElem_eq_getElem]; exact al_k! _ _ h
theorem dr_kD' [LawfulBEq α] (m : DHashMap.Raw α β) (a fb : α) (h : m.contains a = true) : m.getKeyD a fb = a := by
  obtain ⟨hb, h⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.getKeyD; rw [dif_pos hb]
  obtain ⟨s, bs⟩ := m
  rw [contains_gen] at h
  unfold Raw₀.getKeyD; simp only [Array.ugetElem_eq_getElem]; exact al_kD _ _ _ h
theorem hsr_g! [LawfulBEq α] [Inhabited α] (m : HashSet.Raw α) (k : α) (h : k ∈ m) : m.get! k = k :=
  dr_k! m.inner.inner k h
theorem hsr_gD [LawfulBEq α] (m : HashSet.Raw α) (k fb : α) (h : k ∈ m) : m.getD k fb = k :=
  dr_kD' m.inner.inner k fb h
end W7c3
macro "w7ne " t:term : tactic => `(tactic| first
  | exact absurd (List.Perm.length_eq ($t).1) (by simp [toListModel])
  | exact absurd (List.Perm.length_eq ($t).1.1) (by simp [toListModel])
  | exact absurd (List.Perm.length_eq ($t).1.1.1) (by simp [toListModel])
  | exact absurd (List.Perm.length_eq ($t).1) (by decide +kernel)
  | exact absurd (List.Perm.length_eq ($t).1.1) (by decide +kernel)
  | exact absurd (List.Perm.length_eq ($t).1.1.1) (by decide +kernel))

/-! W7c3: sizes of insertMany from an empty map (copied from W5c2, W6c2, W6c7 and adapted to insert) -/
namespace W7c3
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem e_ins (c : Nat) (a : α) (b : β a) : ((Raw₀.emptyWithCapacity c : Raw₀ α β).insert a b).1.size = 1 := by
  have h0 : (Raw₀.emptyWithCapacity c : Raw₀ α β).contains a = false := Raw₀.contains_emptyWithCapacity
  revert h0
  unfold Raw₀.insert Raw₀.contains; dsimp only
  split
  · intro h; simp_all
  · intro _; rw [expand_size]; simp [Raw₀.emptyWithCapacity]
theorem il_ge (l : List ((a : α) × β a)) : ∀ m : Raw₀ α β, m.1.size ≤ (Raw₀.insertListₘ m l).1.size := by
  induction l with
  | nil => intro m; exact Nat.le_refl _
  | cons hd tl ih => intro m; exact Nat.le_trans (W2c0.ins_size_ge m hd.1 hd.2) (ih _)
theorem r0_ofl (c : Nat) (l : List ((a : α) × β a)) :
    (Raw₀.insertMany (Raw₀.emptyWithCapacity c : Raw₀ α β) l).1.1.isEmpty = l.isEmpty := by
  rw [Raw₀.insertMany_eq_insertListₘ]
  cases l with
  | nil => simp [Raw₀.insertListₘ, DHashMap.Raw.isEmpty, Raw₀.emptyWithCapacity]
  | cons hd tl =>
    have := il_ge tl ((Raw₀.emptyWithCapacity c : Raw₀ α β).insert hd.1 hd.2)
    rw [e_ins] at this
    simp only [Raw₀.insertListₘ, DHashMap.Raw.isEmpty, List.isEmpty_cons, beq_eq_false_iff_ne]; omega
theorem size_insertListD_le (l : List ((a : α) × β a)) :
    ∀ (m : Raw₀ α β), (Raw₀.insertListₘ m l).1.size ≤ m.1.size + l.length := by
  induction l with
  | nil => intro m; exact Nat.le_refl _
  | cons hd tl ih =>
    intro m
    have := ih (m.insert hd.1 hd.2)
    have := (raw0_size_insert m hd.1 hd.2).2
    show (Raw₀.insertListₘ (m.insert hd.1 hd.2) tl).1.size ≤ _
    simp only [List.length_cons]; omega
theorem r0_si (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insert a b).1.size = if m.contains a then m.1.size else m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.insert Raw₀.contains; dsimp only
  split <;> simp [Raw₀.size_expandIfNecessary]
theorem il_size (l : List ((a : α) × β a)) : ∀ (m : Raw₀ α β),
    (∀ p ∈ toListModel m.1.buckets, ∀ b ∈ l, (p.1 == b.1) = false) →
    l.Pairwise (fun a b => (a.1 == b.1) = false) →
    (Raw₀.insertListₘ m l).1.size = m.1.size + l.length := by
  induction l with
  | nil => intro m _ _; simp [Raw₀.insertListₘ]
  | cons hd tl ih =>
    intro m hm hl
    have hc : m.contains hd.1 = false := by
      cases h : m.contains hd.1
      · rfl
      · obtain ⟨p, hp, hpa⟩ := Std.Internal.List.containsKey_eq_true_iff_exists_mem.mp (raw0_contains_tlm m hd.1 h)
        have := hm p hp hd List.mem_cons_self
        rw [this] at hpa; exact absurd hpa (by simp)
    rw [List.pairwise_cons] at hl
    simp only [Raw₀.insertListₘ]
    rw [ih (m.insert hd.1 hd.2) ?_ hl.2, r0_si, hc]
    · simp; omega
    · intro p hp b hb
      rcases mem_tlm_insert m hd.1 hd.2 p hp with h | h
      · subst h; exact hl.1 b hb
      · exact hm p h b (List.mem_cons_of_mem _ hb)
end
section
variable {α : Type u} {γ : Type v} [BEq α] [Hashable α]
theorem ilc_ge (l : List (α × γ)) : ∀ m : Raw₀ α (fun _ => γ), m.1.size ≤ (Raw₀.Const.insertListₘ m l).1.size := by
  induction l with
  | nil => intro m; exact Nat.le_refl _
  | cons hd tl ih => intro m; exact Nat.le_trans (W2c0.ins_size_ge m hd.1 hd.2) (ih _)
theorem r0c_ofl (c : Nat) (l : List (α × γ)) :
    (Raw₀.Const.insertMany (Raw₀.emptyWithCapacity c : Raw₀ α (fun _ => γ)) l).1.1.isEmpty = l.isEmpty := by
  rw [Raw₀.Const.insertMany_eq_insertListₘ]
  cases l with
  | nil => simp [Raw₀.Const.insertListₘ, DHashMap.Raw.isEmpty, Raw₀.emptyWithCapacity]
  | cons hd tl =>
    have := ilc_ge tl ((Raw₀.emptyWithCapacity c : Raw₀ α (fun _ => γ)).insert hd.1 hd.2)
    rw [e_ins] at this
    simp only [Raw₀.Const.insertListₘ, DHashMap.Raw.isEmpty, List.isEmpty_cons, beq_eq_false_iff_ne]; omega
theorem ilc_size (l : List (α × γ)) : ∀ (m : Raw₀ α (fun _ => γ)),
    (∀ p ∈ toListModel m.1.buckets, ∀ b ∈ l, (p.1 == b.1) = false) →
    l.Pairwise (fun a b => (a.1 == b.1) = false) →
    (Raw₀.Const.insertListₘ m l).1.size = m.1.size + l.length := by
  induction l with
  | nil => intro m _ _; simp [Raw₀.Const.insertListₘ]
  | cons hd tl ih =>
    intro m hm hl
    have hc : m.contains hd.1 = false := by
      cases h : m.contains hd.1
      · rfl
      · obtain ⟨p, hp, hpa⟩ := Std.Internal.List.containsKey_eq_true_iff_exists_mem.mp (raw0_contains_tlm m hd.1 h)
        have := hm p hp hd List.mem_cons_self
        rw [this] at hpa; exact absurd hpa (by simp)
    rw [List.pairwise_cons] at hl
    simp only [Raw₀.Const.insertListₘ]
    rw [ih (m.insert hd.1 hd.2) ?_ hl.2, r0_si, hc]
    · simp; omega
    · intro p hp b hb
      rcases mem_tlm_insert m hd.1 hd.2 p hp with h | h
      · subst h; exact hl.1 b hb
      · exact hm p h b (List.mem_cons_of_mem _ hb)
end
end W7c3

/-! W7c3: WFImp of two-bucket literals #[l, nil] under any hash-0 model (generalizes W1c5.zh_hs) -/
namespace W7c3
theorem h0_hs {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (h0 : ∀ a : α, hash a = 0) (l : AssocList α β) :
    IsHashSelf (#[l, .nil] : Array (AssocList α β)) := by
  refine ⟨fun i hi => ⟨fun h p hp => ?_⟩⟩
  rw [mkIdx_toNat' _ _ _ (by simp [Pow2])]
  have : (scrambleHash (hash p.1)).toNat % 2 = 0 := by
    rw [h0]; rw [scr_small _ (by decide)]; rfl
  rw [show (#[l, AssocList.nil] : Array (AssocList α β)).size = 2 from rfl, this]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => simp at hp
theorem h0_wfi {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (h0 : ∀ a : α, hash a = 0) (s : Nat) (l : AssocList α β)
    (hs : s = (toListModel #[l, .nil]).length) (hd : Std.Internal.List.DistinctKeys (toListModel #[l, .nil])) :
    Raw.WFImp (⟨s, #[l, .nil]⟩ : DHashMap.Raw α β) := ⟨h0_hs h0 l, hs, hd⟩
end W7c3
namespace W7c3
abbrev nsl (s : Nat) (l : AssocList NS (fun _ => Unit)) : Raw₀ NS (fun _ => Unit) := ⟨⟨s, #[l, .nil]⟩, by simp⟩
abbrev zl (s : Nat) (l : AssocList W1c5.ZH (fun _ => Unit)) : Raw₀ W1c5.ZH (fun _ => Unit) := ⟨⟨s, #[l, .nil]⟩, by simp⟩
abbrev zl1 (s : Nat) (l : AssocList W1c5.ZH (fun _ => Unit)) : Raw₀ W1c5.ZH (fun _ => Unit) := ⟨⟨s, #[.nil, l]⟩, by simp⟩
end W7c3
namespace W7c3
theorem h0_wf {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (h0 : ∀ a : α, hash a = 0) (s : Nat) (l : AssocList α β)
    (hs : s = (toListModel #[l, .nil]).length) (hd : Std.Internal.List.DistinctKeys (toListModel #[l, .nil])) :
    (⟨s, #[l, .nil]⟩ : DHashMap.Raw α β).WF :=
  .wf (by simp) (fun {_ _} => ⟨h0_hs h0 l, hs, hd⟩)
end W7c3

/-! W7c3: HashMap.Raw ofList lookups of a key outside the list need no LawfulHashable (from HashInstHand's bundled proof) -/
namespace W7c3
variable {α : Type u} {γ : Type v} [BEq α] [Hashable α]
theorem hmr_ofl_none [EquivBEq α] (l : List (α × γ)) (k : α) (hc : (l.map Prod.fst).contains k = false) :
    (HashMap.Raw.ofList l)[k]? = none := by
  have e : (HashMap.Raw.ofList l).inner = (HashMap.ofList l).inner.1 := by rw [hmr_ofList_raw, hm_ofList_raw]
  show DHashMap.Raw.Const.get? (HashMap.Raw.ofList l).inner k = none
  rw [e]; unfold DHashMap.Raw.Const.get?; rw [dif_pos (HashMap.ofList l).inner.2.size_buckets_pos]
  exact hm_cget?_ofList_none l k hc
theorem hmr_ofl_d [EquivBEq α] [Inhabited γ] (l : List (α × γ)) (k : α) (hc : (l.map Prod.fst).contains k = false) :
    (HashMap.Raw.ofList l)[k]! = default := by
  have e : (HashMap.Raw.ofList l).inner = (HashMap.ofList l).inner.1 := by rw [hmr_ofList_raw, hm_ofList_raw]
  show DHashMap.Raw.Const.get! (HashMap.Raw.ofList l).inner k = default
  rw [e]; unfold DHashMap.Raw.Const.get!; rw [dif_pos (HashMap.ofList l).inner.2.size_buckets_pos]
  rw [Raw₀.Const.get!_eq_get!ₘ]; unfold Raw₀.Const.get!ₘ
  rw [← Raw₀.Const.get?_eq_get?ₘ, hm_cget?_ofList_none l k hc]; rfl
end W7c3

/-! W7c3: Const.modify k then get? k needs no LawfulHashable/WF (copied from W6c4) -/
namespace W7c3
theorem mk_eq {a b : Nat} (e : a = b) (ha : 0 < a) (hb : 0 < b) (x : UInt64) :
    (mkIdx a ha x).val = (mkIdx b hb x).val := by subst e; rfl
theorem al_gm {α : Type u} {γ : Type v} [BEq α] [EquivBEq α] (l : AssocList α (fun _ => γ)) (k : α)
    (f : γ → γ) : (AssocList.Const.modify k f l).get? k = (l.get? k).map f := by
  induction l with
  | nil => rfl
  | cons a v l ih =>
    simp only [AssocList.Const.modify]
    split <;> simp_all [AssocList.get?]
theorem al_g! {α : Type u} {γ : Type v} [BEq α] [Inhabited γ] (l : AssocList α (fun _ => γ)) (k : α) :
    l.get! k = (l.get? k).get! := by
  induction l with
  | nil => rfl
  | cons a v l ih => simp only [AssocList.get!, AssocList.get?]; cases a == k <;> simp_all
theorem al_gnc {α : Type u} {γ : Type v} [BEq α] (l : AssocList α (fun _ => γ)) (k : α)
    (h : l.contains k = false) : l.get? k = none := by
  induction l with
  | nil => rfl
  | cons a v l ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.get?, h.1, cond_false]; exact ih h.2
theorem r0_gm {α : Type u} {γ : Type v} [BEq α] [Hashable α] [EquivBEq α] (m : Raw₀ α (fun _ => γ)) (k : α)
    (f : γ → γ) : Raw₀.Const.get? (Raw₀.Const.modify m k f) k = (Raw₀.Const.get? m k).map f := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  rw [cmodify_gen]
  split
  · rw [cget?_gen, cget?_gen, Array.getElem_set, if_pos (congrArg USize.toNat (mk_eq (by simp) _ _ _))]
    exact al_gm _ _ _
  · rename_i hc; rw [cget?_gen, al_gnc _ _ (Bool.eq_false_iff.mpr hc)]; rfl
theorem r0_g!m {α : Type u} {γ : Type v} [BEq α] [Hashable α] [EquivBEq α] [Inhabited γ] (m : Raw₀ α (fun _ => γ))
    (k : α) (f : γ → γ) :
    Raw₀.Const.get! (Raw₀.Const.modify m k f) k = ((Raw₀.Const.get? m k).map f).get! := by
  rw [← r0_gm]; obtain ⟨⟨s, bs⟩, h⟩ := Raw₀.Const.modify m k f; rw [cget!_gen, cget?_gen, al_g!]
theorem dr_gm {α : Type u} {γ : Type v} [BEq α] [Hashable α] [EquivBEq α] (m : DHashMap.Raw α (fun _ => γ)) (k : α)
    (f : γ → γ) : DHashMap.Raw.Const.get? (DHashMap.Raw.Const.modify m k f) k = (DHashMap.Raw.Const.get? m k).map f := by
  unfold DHashMap.Raw.Const.modify; split
  · rename_i h; unfold DHashMap.Raw.Const.get?; rw [dif_pos (Raw₀.Const.modify ⟨m, h⟩ k f).2, dif_pos h]; exact r0_gm (m := ⟨m, h⟩) k f
  · rename_i h; show DHashMap.Raw.Const.get? ∅ k = _
    simp only [DHashMap.Raw.Const.get?_empty]; unfold DHashMap.Raw.Const.get?; rw [dif_neg h]; rfl
end W7c3

/-! W7c3: Raw₀ get? of an intersection at a key of m₂ needs only m₁.WF (W4c2W's inter-as-filter argument at the Raw₀ level) -/
namespace W7c3
open Std.Internal.List W4c2W in
theorem r0c_inter_get? {α : Type u} {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : Raw₀ α (fun _ => β)) (h₁ : m₁.1.WF) (k : α) (hk : m₂.contains k = true) :
    Raw₀.Const.get? (m₁.inter m₂) k = Raw₀.Const.get? m₁ k := by
  obtain ⟨P, hperm, hP⟩ := r0_inter_perm m₁ m₂ h₁ k hk
  obtain ⟨m₁, hb₁⟩ := m₁; obtain ⟨m₂, hb₂⟩ := m₂
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
  rw [Raw₀.Const.get?_eq_getValue? wr, Raw₀.Const.get?_eq_getValue? (Std.DHashMap.Internal.Raw.WF.out h₁),
    getValue?_of_perm wr.distinct hperm, gv_filter _ _ _ (fun p _ hp => hP p hp)]
open Std.Internal.List W4c2W in
theorem r0_inter_get? {α : Type u} {γ : α → Type v} [BEq α] [Hashable α] [LawfulBEq α]
    (m₁ m₂ : Raw₀ α γ) (h₁ : m₁.1.WF) (k : α) (hk : m₂.contains k = true) :
    (m₁.inter m₂).get? k = m₁.get? k := by
  obtain ⟨P, hperm, hP⟩ := r0_inter_perm m₁ m₂ h₁ k hk
  obtain ⟨m₁, hb₁⟩ := m₁; obtain ⟨m₂, hb₂⟩ := m₂
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
  rw [Raw₀.get?_eq_getValueCast? wr, Raw₀.get?_eq_getValueCast? (Std.DHashMap.Internal.Raw.WF.out h₁),
    getValueCast?_of_perm wr.distinct hperm, gvc_filter _ _ _ (fun p _ hp => hP p hp)]
end W7c3

/-! W7c3: IsHashSelf / WFImp of literal bucket arrays from a decidable index check (avoids mkIdx's USize arithmetic) -/
namespace W7c3
theorem hs_of {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (bs : Array (AssocList α β)) (hp2 : Pow2 bs.size)
    (h : ∀ i (hi : i < bs.size), ∀ p ∈ (bs[i]'hi).toList, (scrambleHash (hash p.1)).toNat % bs.size = i) : IsHashSelf bs := by
  refine ⟨fun i hi => ⟨fun hpos p hp => ?_⟩⟩
  rw [mkIdx_toNat' _ _ _ hp2]; exact h i hi p hp
abbrev hz8 (s : Nat) (b0 b1 : AssocList HZ (fun _ => Nat)) : Raw₀ HZ (fun _ => Nat) :=
  ⟨⟨s, #[b0, b1, .nil, .nil, .nil, .nil, .nil, .nil]⟩, by simp⟩
end W7c3
namespace W7c3
theorem hz_w5 : Raw.WFImp (hz8 1 .nil (b1 (HZ.mk 5) 0)).1 :=
  ⟨hs_of _ (by simp [Pow2]) (by decide +kernel), rfl, ⟨by decide +kernel⟩⟩
theorem hz_w4 : Raw.WFImp (hz8 1 (b1 (HZ.mk 4) 0) .nil).1 :=
  ⟨hs_of _ (by simp [Pow2]) (by decide +kernel), rfl, ⟨by decide +kernel⟩⟩
end W7c3




/-! # W7c3 verdicts -/

-- `Std.DHashMap.Raw.Const.all_toList` (binder 6): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_0 : drop% Std.DHashMap.Raw.Const.all_toList 6 :=
  by intros; exact W7c3.drc_all

-- `Std.DHashMap.Raw.all_toList` (binder 6): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_1 : drop% Std.DHashMap.Raw.all_toList 6 :=
  by intros; exact W7c3.dr_all

-- `Std.HashMap.Raw.all_toList` (binder 6): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_2 : drop% Std.HashMap.Raw.all_toList 6 :=
  by intros; exact W7c3.drc_all

-- `Std.HashSet.Raw.all_toList` (binder 7): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_3 : drop% Std.HashSet.Raw.all_toList 7 :=
  by intros; exact W7c3.dk_all

-- `Std.DHashMap.Raw.Const.any_toList` (binder 6): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_4 : drop% Std.DHashMap.Raw.Const.any_toList 6 :=
  by intros; exact W7c3.drc_any

-- `Std.DHashMap.Raw.any_toList` (binder 6): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_5 : drop% Std.DHashMap.Raw.any_toList 6 :=
  by intros; exact W7c3.dr_any

-- `Std.HashMap.Raw.any_toList` (binder 6): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_6 : drop% Std.HashMap.Raw.any_toList 6 :=
  by intros; exact W7c3.drc_any

-- `Std.HashSet.Raw.any_toList` (binder 7): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_7 : drop% Std.HashSet.Raw.any_toList 7 :=
  by intros; exact W7c3.dk_any

-- `Std.DHashMap.Internal.apply_bucket` (binder 12): f constantly 0, g constantly 1 (g satisfies the other two premises), m = empty: the conclusion reads 0 = 1
theorem w7c3_8 : ¬ drop0% Std.DHashMap.Internal.apply_bucket 12 :=
  fun h => absurd (h (α := Nat) (β := fun _ => Nat) (γ := Nat) (m := Raw₀.emptyWithCapacity 8) Raw₀.wfImp_emptyWithCapacity (a := 0) (f := fun _ => 0) (g := fun _ => 1) (fun _ _ => rfl) (fun _ => rfl)) (by decide)

-- `Std.DHashMap.Internal.apply_bucket` (binder 13): HB, m = {0 (bucket 0), 2 (bucket 1)} of 8, a = 2, g = index of the first a-key (suffix-invariant, not perm-invariant): 0 in the bucket of 2, 1 in the model
theorem w7c3_9 : ¬ drop0% Std.DHashMap.Internal.apply_bucket 13 :=
  fun h => by
  have := h (α := HB) (β := fun _ => Nat) (γ := Option Nat)
    (m := (⟨⟨2, #[b1 (HB.mk 0) (0 : Nat), b1 (HB.mk 2) (0 : Nat), .nil, .nil, .nil, .nil, .nil, .nil]⟩, by simp⟩ : Raw₀ HB (fun _ => Nat)))
    ⟨W7c3.hs_of _ (by simp [Pow2]) (by decide +kernel), rfl, ⟨by decide +kernel⟩⟩ (a := ⟨2⟩)
    (f := fun l => l.toList.findIdx? (fun p => p.1 == ⟨2⟩)) (g := fun l => l.findIdx? (fun p => p.1 == ⟨2⟩)) rfl
    (fun {l l'} hc => by
      have : l'.findIdx? (fun p => p.1 == (⟨2⟩ : HB)) = none := by
        rw [List.findIdx?_eq_none_iff]; intro x hx
        cases e : (x.1 == (⟨2⟩ : HB))
        · rfl
        · exact absurd (Std.Internal.List.containsKey_eq_true_iff_exists_mem.mpr ⟨x, hx, e⟩) (by simp [hc])
      simp [List.findIdx?_append, this])
  have e : ∀ (bs : Array (AssocList HB (fun _ => Nat))) (hb : 0 < bs.size), Pow2 bs.size → (hi : 1 < bs.size) →
      bucket bs hb (⟨2⟩ : HB) = bs[1] := by
    intro bs hb hp hi
    unfold bucket
    have hx : (mkIdx bs.size hb (hash (⟨2⟩ : HB))).1.toNat = 1 := by
      rw [mkIdx_toNat' _ _ _ hp]
      show (scrambleHash 1).toNat % bs.size = 1
      rw [scr_small _ (by decide)]; show 1 % bs.size = 1; exact Nat.mod_eq_of_lt hi
    simp only [Array.ugetElem_eq_getElem, hx]
  rw [e _ _ (by simp [Pow2]) (by decide)] at this
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Internal.apply_bucket` (binder 14): HB (a/2 == b/2, hash a/2: PartialEquivBEq and LawfulHashable), m = {0 (bucket 0), 2 (bucket 1)} of 8, a = 0, f/g = length (perm invariant): the bucket of 0 has 1 entry, the model 2
theorem w7c3_10 : ¬ drop0% Std.DHashMap.Internal.apply_bucket 14 :=
  fun h => by
  have := h (α := HB) (β := fun _ => Nat) (γ := Nat)
    (m := (⟨⟨2, #[b1 (HB.mk 0) (0 : Nat), b1 (HB.mk 2) (0 : Nat), .nil, .nil, .nil, .nil, .nil, .nil]⟩, by simp⟩ : Raw₀ HB (fun _ => Nat)))
    ⟨W7c3.hs_of _ (by simp [Pow2]) (by decide +kernel), rfl, ⟨by decide +kernel⟩⟩ (a := ⟨0⟩)
    (f := fun l => l.toList.length) (g := fun l => l.length) rfl (fun _ hp => hp.length_eq)
  exact absurd this (by decide +kernel)

-- `Std.HashSet.contains_of_mem_toArray` (binder 4): NB, the key 0 is never found
theorem w7c3_11 : ¬ drop0% Std.HashSet.contains_of_mem_toArray 4 :=
  fun h => absurd (h (m := hs NB.broken 1 #[b1 (NB.mk 0) ()] (by decide)) (k := ⟨0⟩) (h' := by hm_eval)) (by hm_eval)

-- `Std.HashSet.contains_of_mem_toArray` (binder 7): m = ∅, k = 0
theorem w7c3_12 : ¬ drop0% Std.HashSet.contains_of_mem_toArray 7 :=
  fun h => absurd (h (m := (∅ : HashSet Nat)) (k := 0)) (by simp)

-- `Std.HashSet.contains_of_mem_toArray` (binder 5): AB, the key 0 sits in bucket 1 of 2
theorem w7c3_13 : ¬ drop0% Std.HashSet.contains_of_mem_toArray 5 :=
  fun h => absurd (h (m := hs AB.broken 1 #[.nil, b1 (AB.mk 0) ()] (by decide)) (k := ⟨0⟩) (h' := by hm_eval)) (by hm_eval)

-- `Std.HashSet.Raw.contains_of_mem_toArray` (binder 6): lawful ZH (hash 0), key 0 misplaced in bucket 1 of 2: listed by toArray, never found by contains
theorem w7c3_14 : ¬ drop0% Std.HashSet.Raw.contains_of_mem_toArray 6 :=
  fun h => absurd (h (m := hsr 1 #[.nil, b1 (W1c5.ZH.mk 0) ()]) (k := ⟨0⟩) (h' := by decide +kernel)) (by decide +kernel)

-- `Std.ExtDHashMap.emptyWithCapacity_eq` (binder 4): both maps have no entries, so they are equivalent for any instances
theorem w7c3_15 : drop% Std.ExtDHashMap.emptyWithCapacity_eq 4 :=
  by
  intro α _ _ β _ c
  show ExtDHashMap.mk (DHashMap.emptyWithCapacity c) =
    ExtDHashMap.mk (DHashMap.emptyWithCapacity 8)
  exact congrArg ExtDHashMap.mk' (Quotient.sound ⟨⟨by
    show List.Perm (toListModel (Raw₀.emptyWithCapacity c : Raw₀ α _).1.buckets)
      (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets)
    simp⟩⟩)

-- `Std.ExtHashMap.emptyWithCapacity_eq` (binder 4): both maps have no entries, so they are equivalent for any instances
theorem w7c3_16 : drop% Std.ExtHashMap.emptyWithCapacity_eq 4 :=
  by
  intro α β _ _ _ c
  show ExtHashMap.mk (ExtDHashMap.mk (DHashMap.emptyWithCapacity c)) =
    ExtHashMap.mk (ExtDHashMap.mk (DHashMap.emptyWithCapacity 8))
  exact congrArg _ (congrArg ExtDHashMap.mk' (Quotient.sound ⟨⟨by
    show List.Perm (toListModel (Raw₀.emptyWithCapacity c : Raw₀ α _).1.buckets)
      (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets)
    simp⟩⟩))

-- `Std.ExtDHashMap.emptyWithCapacity_eq` (binder 5): both maps have no entries, so they are equivalent for any instances
theorem w7c3_17 : drop% Std.ExtDHashMap.emptyWithCapacity_eq 5 :=
  by
  intro α _ _ β _ c
  show ExtDHashMap.mk (DHashMap.emptyWithCapacity c) =
    ExtDHashMap.mk (DHashMap.emptyWithCapacity 8)
  exact congrArg ExtDHashMap.mk' (Quotient.sound ⟨⟨by
    show List.Perm (toListModel (Raw₀.emptyWithCapacity c : Raw₀ α _).1.buckets)
      (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets)
    simp⟩⟩)

-- `Std.ExtHashMap.emptyWithCapacity_eq` (binder 5): both maps have no entries, so they are equivalent for any instances
theorem w7c3_18 : drop% Std.ExtHashMap.emptyWithCapacity_eq 5 :=
  by
  intro α β _ _ _ c
  show ExtHashMap.mk (ExtDHashMap.mk (DHashMap.emptyWithCapacity c)) =
    ExtHashMap.mk (ExtDHashMap.mk (DHashMap.emptyWithCapacity 8))
  exact congrArg _ (congrArg ExtDHashMap.mk' (Quotient.sound ⟨⟨by
    show List.Perm (toListModel (Raw₀.emptyWithCapacity c : Raw₀ α _).1.buckets)
      (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets)
    simp⟩⟩))

-- `Std.DHashMap.foldM_eq_foldlM_keysArray` (binder 8): P3.CM (bind-counting monad, not lawful), m = ∅ with 2 buckets (lawful ZH): the bucket traversal binds once per bucket, the fold over the empty key list binds never
theorem w7c3_19 : ¬ drop0% Std.DHashMap.foldM_eq_foldlM_keysArray 8 :=
  fun h => by
  have := congrArg (fun x : Nat × Nat => x.1) (h (m := (⟨⟨0, #[.nil, .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩ : DHashMap W1c5.ZH (fun _ => Nat))) (m' := P3.CM)  (δ := Nat) (f := (fun a _ => pure a)) (init := 0))
  exact absurd this (by decide +kernel)

-- `Std.HashMap.foldM_eq_foldlM_keysArray` (binder 8): P3.CM (bind-counting monad, not lawful), m = ∅ with 2 buckets (lawful ZH): the bucket traversal binds once per bucket, the fold over the empty key list binds never
theorem w7c3_20 : ¬ drop0% Std.HashMap.foldM_eq_foldlM_keysArray 8 :=
  fun h => by
  have := congrArg (fun x : Nat × Nat => x.1) (h (m := (⟨⟨⟨0, #[.nil, .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩ : HashMap W1c5.ZH Nat)) (m' := P3.CM)  (δ := Nat) (f := (fun a _ => pure a)) (init := 0))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.foldM_eq_foldlM_keysArray` (binder 11): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_21 : drop% Std.DHashMap.Raw.foldM_eq_foldlM_keysArray 11 :=
  by intros; exact W7c3.dr_fmka

-- `Std.HashMap.Raw.foldM_eq_foldlM_keysArray` (binder 11): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_22 : drop% Std.HashMap.Raw.foldM_eq_foldlM_keysArray 11 :=
  by intros; exact W7c3.dr_fmka

-- `Std.DHashMap.Raw.Const.fold_eq_foldl_toArray` (binder 8): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_23 : drop% Std.DHashMap.Raw.Const.fold_eq_foldl_toArray 8 :=
  by intros; exact W7c3.drc_fta

-- `Std.DHashMap.Raw.fold_eq_foldl_toArray` (binder 8): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_24 : drop% Std.DHashMap.Raw.fold_eq_foldl_toArray 8 :=
  by intros; exact W7c3.dr_fta

-- `Std.HashMap.Raw.fold_eq_foldl_toArray` (binder 8): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_25 : drop% Std.HashMap.Raw.fold_eq_foldl_toArray 8 :=
  by intros; exact W7c3.drc_fta

-- `Std.HashSet.Raw.fold_eq_foldl_toArray` (binder 7): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_26 : drop% Std.HashSet.Raw.fold_eq_foldl_toArray 7 :=
  by intros; exact W7c3.dk_fta

-- `Std.DHashMap.Raw.Const.fold_eq_foldl_toList` (binder 6): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_27 : drop% Std.DHashMap.Raw.Const.fold_eq_foldl_toList 6 :=
  by intros; exact W7c3.drc_ftl

-- `Std.DHashMap.Raw.fold_eq_foldl_toList` (binder 6): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_28 : drop% Std.DHashMap.Raw.fold_eq_foldl_toList 6 :=
  by intros; exact W7c3.dr_ftl

-- `Std.HashMap.Raw.fold_eq_foldl_toList` (binder 6): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_29 : drop% Std.HashMap.Raw.fold_eq_foldl_toList 6 :=
  by intros; exact W7c3.drc_ftl

-- `Std.HashSet.Raw.fold_eq_foldl_toList` (binder 5): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_30 : drop% Std.HashSet.Raw.fold_eq_foldl_toList 5 :=
  by intros; exact W7c3.dk_ftl

-- `Std.DHashMap.Raw.forIn_eq_forIn_keys` (binder 8): P3.CM (bind-counting monad, not lawful), m = ∅ with 2 buckets (lawful ZH): the bucket traversal binds once per bucket, the fold over the empty key list binds never
theorem w7c3_31 : ¬ drop0% Std.DHashMap.Raw.forIn_eq_forIn_keys 8 :=
  fun h => by
  have := congrArg (fun x : Nat × Nat => x.1) (h (m := (⟨0, #[.nil, .nil]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (m' := P3.CM) (h := (W1c5.zh_wf _ _ rfl (by simp [toListModel]))) (δ := Nat) (f := (fun _ d => pure (ForInStep.yield d))) (init := 0))
  exact absurd this (by decide +kernel)

-- `Std.HashMap.Raw.forIn_eq_forIn_keys` (binder 8): P3.CM (bind-counting monad, not lawful), m = ∅ with 2 buckets (lawful ZH): the bucket traversal binds once per bucket, the fold over the empty key list binds never
theorem w7c3_32 : ¬ drop0% Std.HashMap.Raw.forIn_eq_forIn_keys 8 :=
  fun h => by
  have := congrArg (fun x : Nat × Nat => x.1) (h (m := (hmr 0 #[.nil, .nil] : HashMap.Raw W1c5.ZH Nat)) (m' := P3.CM) (h := ⟨(W1c5.zh_wf _ _ rfl (by simp [toListModel]))⟩) (δ := Nat) (f := (fun _ d => pure (ForInStep.yield d))) (init := 0))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.forIn_eq_forIn_keys` (binder 9): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_33 : drop% Std.DHashMap.Raw.forIn_eq_forIn_keys 9 :=
  by intros; exact W7c3.dr_fik

-- `Std.HashMap.Raw.forIn_eq_forIn_keys` (binder 9): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_34 : drop% Std.HashMap.Raw.forIn_eq_forIn_keys 9 :=
  by intros; exact W7c3.dr_fik

-- `Std.DHashMap.forIn_eq_forIn_keysArray` (binder 8): P3.CM (bind-counting monad, not lawful), m = ∅ with 2 buckets (lawful ZH): the bucket traversal binds once per bucket, the fold over the empty key list binds never
theorem w7c3_35 : ¬ drop0% Std.DHashMap.forIn_eq_forIn_keysArray 8 :=
  fun h => by
  have := congrArg (fun x : Nat × Nat => x.1) (h (m := (⟨⟨0, #[.nil, .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩ : DHashMap W1c5.ZH (fun _ => Nat))) (m' := P3.CM)  (δ := Nat) (f := (fun _ d => pure (ForInStep.yield d))) (init := 0))
  exact absurd this (by decide +kernel)

-- `Std.HashMap.forIn_eq_forIn_keysArray` (binder 8): P3.CM (bind-counting monad, not lawful), m = ∅ with 2 buckets (lawful ZH): the bucket traversal binds once per bucket, the fold over the empty key list binds never
theorem w7c3_36 : ¬ drop0% Std.HashMap.forIn_eq_forIn_keysArray 8 :=
  fun h => by
  have := congrArg (fun x : Nat × Nat => x.1) (h (m := (⟨⟨⟨0, #[.nil, .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩ : HashMap W1c5.ZH Nat)) (m' := P3.CM)  (δ := Nat) (f := (fun _ d => pure (ForInStep.yield d))) (init := 0))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.forIn_eq_forIn_keysArray` (binder 11): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_37 : drop% Std.DHashMap.Raw.forIn_eq_forIn_keysArray 11 :=
  by intros; exact W7c3.dr_fika

-- `Std.HashMap.Raw.forIn_eq_forIn_keysArray` (binder 11): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_38 : drop% Std.HashMap.Raw.forIn_eq_forIn_keysArray 11 :=
  by intros; exact W7c3.dr_fika

-- `Std.DHashMap.forM_eq_forM_keysArray` (binder 7): P3.CM (bind-counting monad, not lawful), m = ∅ with 2 buckets (lawful ZH): the bucket traversal binds once per bucket, the fold over the empty key list binds never
theorem w7c3_39 : ¬ drop0% Std.DHashMap.forM_eq_forM_keysArray 7 :=
  fun h => by
  have := congrArg (fun x : Nat × PUnit => x.1) (h (m := (⟨⟨0, #[.nil, .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩ : DHashMap W1c5.ZH (fun _ => Nat))) (m' := P3.CM)  (f := (fun _ => pure PUnit.unit)))
  exact absurd this (by decide +kernel)

-- `Std.HashMap.forM_eq_forM_keysArray` (binder 7): P3.CM (bind-counting monad, not lawful), m = ∅ with 2 buckets (lawful ZH): the bucket traversal binds once per bucket, the fold over the empty key list binds never
theorem w7c3_40 : ¬ drop0% Std.HashMap.forM_eq_forM_keysArray 7 :=
  fun h => by
  have := congrArg (fun x : Nat × PUnit => x.1) (h (m := (⟨⟨⟨0, #[.nil, .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩ : HashMap W1c5.ZH Nat)) (m' := P3.CM)  (f := (fun _ => pure PUnit.unit)))
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.forM_eq_forM_keysArray` (binder 9): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_41 : drop% Std.DHashMap.Raw.forM_eq_forM_keysArray 9 :=
  by intros; exact W7c3.dr_fmk

-- `Std.HashMap.Raw.forM_eq_forM_keysArray` (binder 9): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_42 : drop% Std.HashMap.Raw.forM_eq_forM_keysArray 9 :=
  by intros; exact W7c3.dr_fmk

-- `Std.ExtHashSet.get!_eq_of_mem` (binder 7): m = ∅, k = 1: the lookup returns the fallback/default 0
theorem w7c3_43 : ¬ drop0% Std.ExtHashSet.get!_eq_of_mem 7 :=
  fun h => absurd (h (m := (∅ : ExtHashSet Nat)) (k := 1)) (by simp)

-- `Std.HashSet.Raw.get!_eq_of_mem` (binder 8): m = ∅, k = 1: the lookup returns the fallback/default 0
theorem w7c3_44 : ¬ drop0% Std.HashSet.Raw.get!_eq_of_mem 8 :=
  fun h => absurd (h (m := (∅ : HashSet.Raw Nat)) (h := HashSet.Raw.WF.empty) (k := 1)) (by simp)

-- `Std.HashSet.Raw.get!_eq_of_mem` (binder 4): HB (a/2 == b/2, lawful except LawfulBEq): m = {0}, k = 1: the lookup returns the stored key 0
theorem w7c3_45 : ¬ drop0% Std.HashSet.Raw.get!_eq_of_mem 4 :=
  fun h => absurd (h (m := ((∅ : HashSet.Raw HB).insert ⟨0⟩)) (h := HashSet.Raw.WF.insert HashSet.Raw.WF.empty) (k := ⟨1⟩) (h' := by first | decide +kernel | (simp only [HashSet.Raw.mem_iff_contains]; decide +kernel))) (by decide +kernel)

-- `Std.HashSet.Raw.get!_eq_of_mem` (binder 6): under LawfulBEq the key found in the query bucket is the query itself; k ∈ m already makes the bucket scan succeed, so WF is not needed
theorem w7c3_46 : drop% Std.HashSet.Raw.get!_eq_of_mem 6 :=
  by intros; exact W7c3.hsr_g! _ _ ‹_›

-- `Std.DHashMap.Internal.Raw₀.Const.get?_inter_of_contains_right` (binder 8): m₁ holds key 0 twice (values 5, 6; size field 0, lawful ZH), m₂ = {0}: the intersection filters m₁, and the filter reverses the bucket, so it returns 6 while m₁.get? 0 = 5
theorem w7c3_47 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.get?_inter_of_contains_right 8 :=
  fun h => by
  have := h (m₁ := (⟨⟨0, #[(.cons (W1c5.ZH.mk 0) (5 : Nat) (.cons (W1c5.ZH.mk 0) (6 : Nat) .nil)), .nil]⟩, by simp⟩ : Raw₀ W1c5.ZH (fun _ => Nat))) (m₂ := (⟨⟨1, #[(.cons (W1c5.ZH.mk 0) (5 : Nat) .nil), .nil]⟩, by simp⟩ : Raw₀ W1c5.ZH (fun _ => Nat))) (W1c5.zh_wf _ _ rfl (by simp [toListModel])) (k := ⟨0⟩) (by decide +kernel)
  revert this; first | decide +kernel | hm_eval3 | (simp only [Raw₀.inter]; decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.Const.get?_inter_of_contains_right` (binder 9): the intersection holds a filter of m₁ that keeps every entry whose key is == k (r0_inter_perm), so only m₁.WF is needed
theorem w7c3_48 : drop% Std.DHashMap.Internal.Raw₀.Const.get?_inter_of_contains_right 9 :=
  by intro α _ _ β m₁ m₂ _ _ h₁ k hk; exact W7c3.r0c_inter_get? m₁ m₂ h₁ k hk

-- `Std.DHashMap.Internal.Raw₀.get?_inter_of_contains_right` (binder 7): m₁ holds key 0 twice (values 5, 6; size field 0, lawful ZH), m₂ = {0}: the intersection filters m₁, and the filter reverses the bucket, so it returns 6 while m₁.get? 0 = 5
theorem w7c3_49 : ¬ drop0% Std.DHashMap.Internal.Raw₀.get?_inter_of_contains_right 7 :=
  fun h => by
  have := h (m₁ := (⟨⟨0, #[(.cons (W1c5.ZH.mk 0) (5 : Nat) (.cons (W1c5.ZH.mk 0) (6 : Nat) .nil)), .nil]⟩, by simp⟩ : Raw₀ W1c5.ZH (fun _ => Nat))) (m₂ := (⟨⟨1, #[(.cons (W1c5.ZH.mk 0) (5 : Nat) .nil), .nil]⟩, by simp⟩ : Raw₀ W1c5.ZH (fun _ => Nat))) (W1c5.zh_wf _ _ rfl (by simp [toListModel])) (k := ⟨0⟩) (by decide +kernel)
  revert this; first | decide +kernel | hm_eval3 | (simp only [Raw₀.inter]; decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.get?_inter_of_contains_right` (binder 8): the intersection holds a filter of m₁ that keeps every entry whose key is == k (r0_inter_perm), so only m₁.WF is needed
theorem w7c3_50 : drop% Std.DHashMap.Internal.Raw₀.get?_inter_of_contains_right 8 :=
  by intro α β _ _ m₁ m₂ _ h₁ k hk; exact W7c3.r0_inter_get? m₁ m₂ h₁ k hk

-- `Std.ExtHashSet.getD_eq_of_mem` (binder 7): m = ∅, k = 1: the lookup returns the fallback/default 0
theorem w7c3_51 : ¬ drop0% Std.ExtHashSet.getD_eq_of_mem 7 :=
  fun h => absurd (h (m := (∅ : ExtHashSet Nat)) (k := 1) (fallback := 0)) (by simp)

-- `Std.HashSet.Raw.getD_eq_of_mem` (binder 8): m = ∅, k = 1: the lookup returns the fallback/default 0
theorem w7c3_52 : ¬ drop0% Std.HashSet.Raw.getD_eq_of_mem 8 :=
  fun h => absurd (h (m := (∅ : HashSet.Raw Nat)) (h := HashSet.Raw.WF.empty) (k := 1) (fallback := 0)) (by simp)

-- `Std.HashSet.Raw.getD_eq_of_mem` (binder 4): HB (a/2 == b/2, lawful except LawfulBEq): m = {0}, k = 1: the lookup returns the stored key 0
theorem w7c3_53 : ¬ drop0% Std.HashSet.Raw.getD_eq_of_mem 4 :=
  fun h => absurd (h (m := ((∅ : HashSet.Raw HB).insert ⟨0⟩)) (h := HashSet.Raw.WF.insert HashSet.Raw.WF.empty) (k := ⟨1⟩) (fallback := 0) (h' := by first | decide +kernel | (simp only [HashSet.Raw.mem_iff_contains]; decide +kernel))) (by decide +kernel)

-- `Std.HashSet.Raw.getD_eq_of_mem` (binder 5): under LawfulBEq the key found in the query bucket is the query itself; k ∈ m already makes the bucket scan succeed, so WF is not needed
theorem w7c3_54 : drop% Std.HashSet.Raw.getD_eq_of_mem 5 :=
  by intros; exact W7c3.hsr_gD _ _ _ ‹_›

-- `Std.HashMap.getElem!_alter` (binder 5): NS (a ≤ b, hash 0): m = {0 ↦ 5}, k = 1, k' = 0: the update finds the stored 0 by 0 ≤ 1, while the k == k' test (1 ≤ 0) is false
theorem w7c3_55 : ¬ drop0% Std.HashMap.getElem!_alter 5 :=
  fun h => absurd (h (m := (hm NS.broken 1 #[(.cons (NS.mk 0) (5 : Nat) .nil)] (by decide) : HashMap NS Nat)) (k := ⟨1⟩) (k' := ⟨0⟩) (f := fun o => o.map (· + 1))) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.Raw.getElem!_alter` (binder 6): AB: m = {0 ↦ 5 (bucket 0), 1 ↦ 7 (bucket 1)}, k = 0, k' = 1: 0 == 1, so the right side uses the updated value of 0, but the update leaves bucket 1 alone
theorem w7c3_56 : ¬ drop0% Std.HashMap.Raw.getElem!_alter 6 :=
  fun h => absurd (h (m := (hmr 2 #[(.cons (AB.mk 0) (5 : Nat) .nil), (.cons (AB.mk 1) (7 : Nat) .nil)] : HashMap.Raw AB Nat)) (h := (hmr_wf AB.broken _ _ (by decide))) (k := ⟨0⟩) (k' := ⟨1⟩) (f := fun o => o.map (· + 1))) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.getElem!_alter` (binder 6): AB: m = {0 ↦ 5 (bucket 0), 1 ↦ 7 (bucket 1)}, k = 0, k' = 1: 0 == 1, so the right side uses the updated value of 0, but the update leaves bucket 1 alone
theorem w7c3_57 : ¬ drop0% Std.HashMap.getElem!_alter 6 :=
  fun h => absurd (h (m := (hm AB.broken 2 #[(.cons (AB.mk 0) (5 : Nat) .nil), (.cons (AB.mk 1) (7 : Nat) .nil)] (by decide) : HashMap AB Nat)) (k := ⟨0⟩) (k' := ⟨1⟩) (f := fun o => o.map (· + 1))) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.Raw.getElem!_alter` (binder 11): bucketless raw map (size 0, no buckets): alter leaves it unchanged, so k is still absent although f sets some 1
theorem w7c3_58 : ¬ drop0% Std.HashMap.Raw.getElem!_alter 11 :=
  fun h => absurd (h (m := (⟨⟨0, #[]⟩⟩ : HashMap.Raw Nat Nat)) (k := 0) (k' := 0) (f := fun _ => some 1)) (by rw [show ((⟨⟨0, #[]⟩⟩ : HashMap.Raw Nat Nat).alter 0 (fun _ => some 1)) = ∅ from rfl]; simp)

-- `Std.HashMap.getElem!_modify` (binder 5): NS (a ≤ b, hash 0): m = {0 ↦ 5}, k = 1, k' = 0: the update finds the stored 0 by 0 ≤ 1, while the k == k' test (1 ≤ 0) is false
theorem w7c3_59 : ¬ drop0% Std.HashMap.getElem!_modify 5 :=
  fun h => absurd (h (m := (hm NS.broken 1 #[(.cons (NS.mk 0) (5 : Nat) .nil)] (by decide) : HashMap NS Nat)) (k := ⟨1⟩) (k' := ⟨0⟩) (f := fun x => x + 1)) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.Raw.getElem!_modify` (binder 6): AB: m = {0 ↦ 5 (bucket 0), 1 ↦ 7 (bucket 1)}, k = 0, k' = 1: 0 == 1, so the right side uses the updated value of 0, but the update leaves bucket 1 alone
theorem w7c3_60 : ¬ drop0% Std.HashMap.Raw.getElem!_modify 6 :=
  fun h => absurd (h (m := (hmr 2 #[(.cons (AB.mk 0) (5 : Nat) .nil), (.cons (AB.mk 1) (7 : Nat) .nil)] : HashMap.Raw AB Nat)) (h := (hmr_wf AB.broken _ _ (by decide))) (k := ⟨0⟩) (k' := ⟨1⟩) (f := fun x => x + 1)) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.getElem!_modify` (binder 6): AB: m = {0 ↦ 5 (bucket 0), 1 ↦ 7 (bucket 1)}, k = 0, k' = 1: 0 == 1, so the right side uses the updated value of 0, but the update leaves bucket 1 alone
theorem w7c3_61 : ¬ drop0% Std.HashMap.getElem!_modify 6 :=
  fun h => absurd (h (m := (hm AB.broken 2 #[(.cons (AB.mk 0) (5 : Nat) .nil), (.cons (AB.mk 1) (7 : Nat) .nil)] (by decide) : HashMap AB Nat)) (k := ⟨0⟩) (k' := ⟨1⟩) (f := fun x => x + 1)) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.Raw.getElem!_ofList_of_contains_eq_false` (binder 9): l = [(0, 5)], k = 0 (lawful ZH): the lookup finds 5
theorem w7c3_62 : ¬ drop0% Std.HashMap.Raw.getElem!_ofList_of_contains_eq_false 9 :=
  fun h => absurd (h (α := W1c5.ZH) (β := Nat) (l := [(⟨0⟩, 5)]) (k := ⟨0⟩)) (by first | decide +kernel | simp | (simp [HashMap.Raw.ofList]; decide +kernel))

-- `Std.HashMap.getElem!_ofList_of_contains_eq_false` (binder 9): l = [(0, 5)], k = 0 (lawful ZH): the lookup finds 5
theorem w7c3_63 : ¬ drop0% Std.HashMap.getElem!_ofList_of_contains_eq_false 9 :=
  fun h => absurd (h (α := W1c5.ZH) (β := Nat) (l := [(⟨0⟩, 5)]) (k := ⟨0⟩)) (by first | decide +kernel | simp | (simp [HashMap.ofList]; decide +kernel))

-- `Std.HashMap.Raw.getElem!_ofList_of_contains_eq_false` (binder 4): NS (a ≤ b, hash 0), l = [(2, 7)], k = 3: not 3 == 2, but the stored 2 == 3
theorem w7c3_64 : ¬ drop0% Std.HashMap.Raw.getElem!_ofList_of_contains_eq_false 4 :=
  fun h => absurd ((@h NS Nat inferInstance inferInstance) (l := [(NS.mk 2, (7 : Nat))]) (k := ⟨3⟩) (by decide)) (by first | decide +kernel | hm_eval | hm_eval_raw | (simp only [HashMap.Raw.ofList, DHashMap.Raw.Const.ofList]; w1c0_raw))

-- `Std.HashMap.Raw.getElem!_ofList_of_contains_eq_false` (binder 5): with EquivBEq an entry found for k has a key x in l with x == k, so the key list contains k; bucket placement does not matter
theorem w7c3_65 : drop% Std.HashMap.Raw.getElem!_ofList_of_contains_eq_false 5 :=
  by intros; rename_i l k _ hc; exact W7c3.hmr_ofl_d l k hc

-- `Std.HashMap.getElem?_alter` (binder 5): NS (a ≤ b, hash 0): m = {0 ↦ 5}, k = 1, k' = 0: the update finds the stored 0 by 0 ≤ 1, while the k == k' test (1 ≤ 0) is false
theorem w7c3_66 : ¬ drop0% Std.HashMap.getElem?_alter 5 :=
  fun h => absurd (h (m := (hm NS.broken 1 #[(.cons (NS.mk 0) (5 : Nat) .nil)] (by decide) : HashMap NS Nat)) (k := ⟨1⟩) (k' := ⟨0⟩) (f := fun o => o.map (· + 1))) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.Raw.getElem?_alter` (binder 6): AB: m = {0 ↦ 5 (bucket 0), 1 ↦ 7 (bucket 1)}, k = 0, k' = 1: 0 == 1, so the right side uses the updated value of 0, but the update leaves bucket 1 alone
theorem w7c3_67 : ¬ drop0% Std.HashMap.Raw.getElem?_alter 6 :=
  fun h => absurd (h (m := (hmr 2 #[(.cons (AB.mk 0) (5 : Nat) .nil), (.cons (AB.mk 1) (7 : Nat) .nil)] : HashMap.Raw AB Nat)) (h := (hmr_wf AB.broken _ _ (by decide))) (k := ⟨0⟩) (k' := ⟨1⟩) (f := fun o => o.map (· + 1))) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.getElem?_alter` (binder 6): AB: m = {0 ↦ 5 (bucket 0), 1 ↦ 7 (bucket 1)}, k = 0, k' = 1: 0 == 1, so the right side uses the updated value of 0, but the update leaves bucket 1 alone
theorem w7c3_68 : ¬ drop0% Std.HashMap.getElem?_alter 6 :=
  fun h => absurd (h (m := (hm AB.broken 2 #[(.cons (AB.mk 0) (5 : Nat) .nil), (.cons (AB.mk 1) (7 : Nat) .nil)] (by decide) : HashMap AB Nat)) (k := ⟨0⟩) (k' := ⟨1⟩) (f := fun o => o.map (· + 1))) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.Raw.getElem?_alter` (binder 10): bucketless raw map (size 0, no buckets): alter leaves it unchanged, so k is still absent although f sets some 1
theorem w7c3_69 : ¬ drop0% Std.HashMap.Raw.getElem?_alter 10 :=
  fun h => absurd (h (m := (⟨⟨0, #[]⟩⟩ : HashMap.Raw Nat Nat)) (k := 0) (k' := 0) (f := fun _ => some 1)) (by rw [show ((⟨⟨0, #[]⟩⟩ : HashMap.Raw Nat Nat).alter 0 (fun _ => some 1)) = ∅ from rfl]; simp)

-- `Std.HashMap.getElem?_modify` (binder 5): NS (a ≤ b, hash 0): m = {0 ↦ 5}, k = 1, k' = 0: the update finds the stored 0 by 0 ≤ 1, while the k == k' test (1 ≤ 0) is false
theorem w7c3_70 : ¬ drop0% Std.HashMap.getElem?_modify 5 :=
  fun h => absurd (h (m := (hm NS.broken 1 #[(.cons (NS.mk 0) (5 : Nat) .nil)] (by decide) : HashMap NS Nat)) (k := ⟨1⟩) (k' := ⟨0⟩) (f := fun x => x + 1)) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.Raw.getElem?_modify` (binder 6): AB: m = {0 ↦ 5 (bucket 0), 1 ↦ 7 (bucket 1)}, k = 0, k' = 1: 0 == 1, so the right side uses the updated value of 0, but the update leaves bucket 1 alone
theorem w7c3_71 : ¬ drop0% Std.HashMap.Raw.getElem?_modify 6 :=
  fun h => absurd (h (m := (hmr 2 #[(.cons (AB.mk 0) (5 : Nat) .nil), (.cons (AB.mk 1) (7 : Nat) .nil)] : HashMap.Raw AB Nat)) (h := (hmr_wf AB.broken _ _ (by decide))) (k := ⟨0⟩) (k' := ⟨1⟩) (f := fun x => x + 1)) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.getElem?_modify` (binder 6): AB: m = {0 ↦ 5 (bucket 0), 1 ↦ 7 (bucket 1)}, k = 0, k' = 1: 0 == 1, so the right side uses the updated value of 0, but the update leaves bucket 1 alone
theorem w7c3_72 : ¬ drop0% Std.HashMap.getElem?_modify 6 :=
  fun h => absurd (h (m := (hm AB.broken 2 #[(.cons (AB.mk 0) (5 : Nat) .nil), (.cons (AB.mk 1) (7 : Nat) .nil)] (by decide) : HashMap AB Nat)) (k := ⟨0⟩) (k' := ⟨1⟩) (f := fun x => x + 1)) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.getElem?_modify_self` (binder 5): S1.NE (a == b iff a ≠ b, hash 0): m = {0 ↦ 5}, k = 1: 0 == 1, so modify rewrites the entry to key 1 ↦ 6, but 1 == 1 is false and the lookup of 1 misses it
theorem w7c3_73 : ¬ drop0% Std.HashMap.getElem?_modify_self 5 :=
  fun h => absurd (h (m := (hm S1.NE.broken 1 #[(.cons (S1.NE.mk 0) (5 : Nat) .nil)] (by decide) : HashMap S1.NE Nat)) (k := ⟨1⟩) (f := fun x => x + 1)) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.Raw.getElem?_modify_self` (binder 6): Const.modify k and the lookup of k use the same bucket and the same first-match scan, and modify writes key k, found again by k == k (EquivBEq reflexivity only; no LawfulHashable, no WF)
theorem w7c3_74 : drop% Std.HashMap.Raw.getElem?_modify_self 6 :=
  by intros; exact W7c3.dr_gm _ _ _

-- `Std.HashMap.getElem?_modify_self` (binder 6): Const.modify k and the lookup of k use the same bucket and the same first-match scan, and modify writes key k, found again by k == k (EquivBEq reflexivity only; no LawfulHashable, no WF)
theorem w7c3_75 : drop% Std.HashMap.getElem?_modify_self 6 :=
  by intro α β _ _ m _ k f; exact W7c3.r0_gm ⟨m.inner.1, m.inner.2.size_buckets_pos⟩ k f

-- `Std.HashMap.Raw.getElem?_modify_self` (binder 9): Const.modify k and the lookup of k use the same bucket and the same first-match scan, and modify writes key k, found again by k == k (EquivBEq reflexivity only; no LawfulHashable, no WF)
theorem w7c3_76 : drop% Std.HashMap.Raw.getElem?_modify_self 9 :=
  by intros; exact W7c3.dr_gm _ _ _

-- `Std.HashMap.Raw.getElem?_ofList_of_contains_eq_false` (binder 8): l = [(0, 5)], k = 0 (lawful ZH): the lookup finds 5
theorem w7c3_77 : ¬ drop0% Std.HashMap.Raw.getElem?_ofList_of_contains_eq_false 8 :=
  fun h => absurd (h (α := W1c5.ZH) (β := Nat) (l := [(⟨0⟩, 5)]) (k := ⟨0⟩)) (by first | decide +kernel | simp | (simp [HashMap.Raw.ofList]; decide +kernel))

-- `Std.HashMap.getElem?_ofList_of_contains_eq_false` (binder 8): l = [(0, 5)], k = 0 (lawful ZH): the lookup finds 5
theorem w7c3_78 : ¬ drop0% Std.HashMap.getElem?_ofList_of_contains_eq_false 8 :=
  fun h => absurd (h (α := W1c5.ZH) (β := Nat) (l := [(⟨0⟩, 5)]) (k := ⟨0⟩)) (by first | decide +kernel | simp | (simp [HashMap.ofList]; decide +kernel))

-- `Std.HashMap.Raw.getElem?_ofList_of_contains_eq_false` (binder 4): NS (a ≤ b, hash 0), l = [(2, 7)], k = 3: not 3 == 2, but the stored 2 == 3
theorem w7c3_79 : ¬ drop0% Std.HashMap.Raw.getElem?_ofList_of_contains_eq_false 4 :=
  fun h => absurd ((@h NS Nat inferInstance inferInstance) (l := [(NS.mk 2, (7 : Nat))]) (k := ⟨3⟩) (by decide)) (by first | decide +kernel | hm_eval | hm_eval_raw | (simp only [HashMap.Raw.ofList, DHashMap.Raw.Const.ofList]; w1c0_raw))

-- `Std.HashMap.Raw.getElem?_ofList_of_contains_eq_false` (binder 5): with EquivBEq an entry found for k has a key x in l with x == k, so the key list contains k; bucket placement does not matter
theorem w7c3_80 : drop% Std.HashMap.Raw.getElem?_ofList_of_contains_eq_false 5 :=
  by intros; rename_i l k hc; exact W7c3.hmr_ofl_none l k hc

-- `Std.DHashMap.Raw.getKey!_diff_of_not_mem_right` (binder 9): m₁ holds keys 0 and 1 in one bucket with 0 == 1 (HZ0: a/2 equality, hash 0; size field 0), m₂ = {4}: the diff filters m₁ and the filter reverses the bucket, so getKey! 0 returns 1 instead of 0
theorem w7c3_81 : ¬ drop0% Std.DHashMap.Raw.getKey!_diff_of_not_mem_right 9 :=
  fun h => by
  have := h (m₁ := (⟨0, #[(.cons (W4c4.HZ0.mk 0) (5 : Nat) (.cons (W4c4.HZ0.mk 1) (6 : Nat) .nil)), .nil]⟩ : DHashMap.Raw W4c4.HZ0 (fun _ => Nat))) (m₂ := ⟨1, #[b1 (W4c4.HZ0.mk 4) (0 : Nat), .nil]⟩) (h₂ := W7c3.h0_wf (fun _ => rfl) _ _ rfl ⟨by decide⟩) (k := ⟨0⟩) (not_mem := by decide +kernel)
  revert this; first | decide +kernel | hm_eval3

-- `Std.DHashMap.Raw.getKey!_diff_of_not_mem_right` (binder 10): m₁ = {7}, m₂ with size field 0 holds 7 misplaced in bucket 1 (lawful ZH): 7 ∉ m₂, but the diff erases m₂ keys from m₁, so getKey! 7 drops to default 0
theorem w7c3_82 : ¬ drop0% Std.DHashMap.Raw.getKey!_diff_of_not_mem_right 10 :=
  fun h => by
  have := h (m₁ := (⟨1, #[b1 (W1c5.ZH.mk 7) (0 : Nat), .nil]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (m₂ := ⟨0, #[.nil, b1 (W1c5.ZH.mk 7) (0 : Nat)]⟩) (h₁ := W1c5.zh_wf _ _ rfl (by simp [toListModel])) (k := ⟨7⟩) (not_mem := by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.HashMap.Raw.getKey!_diff_of_not_mem_right` (binder 9): m₁ holds keys 0 and 1 in one bucket with 0 == 1 (HZ0: a/2 equality, hash 0; size field 0), m₂ = {4}: the diff filters m₁ and the filter reverses the bucket, so getKey! 0 returns 1 instead of 0
theorem w7c3_83 : ¬ drop0% Std.HashMap.Raw.getKey!_diff_of_not_mem_right 9 :=
  fun h => by
  have := h (m₁ := (⟨⟨0, #[(.cons (W4c4.HZ0.mk 0) (5 : Nat) (.cons (W4c4.HZ0.mk 1) (6 : Nat) .nil)), .nil]⟩⟩ : HashMap.Raw W4c4.HZ0 Nat)) (m₂ := ⟨⟨1, #[b1 (W4c4.HZ0.mk 4) (0 : Nat), .nil]⟩⟩) (h₂ := ⟨W7c3.h0_wf (fun _ => rfl) _ _ rfl ⟨by decide⟩⟩) (k := ⟨0⟩) (not_mem := by decide +kernel)
  revert this; first | decide +kernel | hm_eval3

-- `Std.HashMap.Raw.getKey!_diff_of_not_mem_right` (binder 10): m₁ = {7}, m₂ with size field 0 holds 7 misplaced in bucket 1 (lawful ZH): 7 ∉ m₂, but the diff erases m₂ keys from m₁, so getKey! 7 drops to default 0
theorem w7c3_84 : ¬ drop0% Std.HashMap.Raw.getKey!_diff_of_not_mem_right 10 :=
  fun h => by
  have := h (m₁ := (⟨⟨1, #[b1 (W1c5.ZH.mk 7) (0 : Nat), .nil]⟩⟩ : HashMap.Raw W1c5.ZH Nat)) (m₂ := ⟨⟨0, #[.nil, b1 (W1c5.ZH.mk 7) (0 : Nat)]⟩⟩) (h₁ := ⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩) (k := ⟨7⟩) (not_mem := by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.getKey?_inter_of_contains_eq_false_left` (binder 6): a key contained in the intersection is contained in m₁ (W3c4.ni_r0, LawfulHashable only), so m₁.contains k = false gives none (no EquivBEq, no WF)
theorem w7c3_85 : drop% Std.DHashMap.Internal.Raw₀.getKey?_inter_of_contains_eq_false_left 6 :=
  by intros; rename_i k hk; exact W3c4.r0_getKey?_nc _ k (Bool.eq_false_iff.mpr (fun h => absurd (W3c4.ni_r0 _ _ k h) (by simp [hk])))

-- `Std.DHashMap.Internal.Raw₀.getKey?_inter_of_contains_eq_false_left` (binder 8): a key contained in the intersection is contained in m₁ (W3c4.ni_r0, LawfulHashable only), so m₁.contains k = false gives none (no EquivBEq, no WF)
theorem w7c3_86 : drop% Std.DHashMap.Internal.Raw₀.getKey?_inter_of_contains_eq_false_left 8 :=
  by intros; rename_i k hk; exact W3c4.r0_getKey?_nc _ k (Bool.eq_false_iff.mpr (fun h => absurd (W3c4.ni_r0 _ _ k h) (by simp [hk])))

-- `Std.DHashMap.Internal.Raw₀.getKey?_inter_of_contains_eq_false_left` (binder 9): a key contained in the intersection is contained in m₁ (W3c4.ni_r0, LawfulHashable only), so m₁.contains k = false gives none (no EquivBEq, no WF)
theorem w7c3_87 : drop% Std.DHashMap.Internal.Raw₀.getKey?_inter_of_contains_eq_false_left 9 :=
  by intros; rename_i k hk; exact W3c4.r0_getKey?_nc _ k (Bool.eq_false_iff.mpr (fun h => absurd (W3c4.ni_r0 _ _ k h) (by simp [hk])))

-- `Std.DHashMap.Internal.Raw₀.getKey?_inter_of_contains_eq_false_left` (binder 11): m₁ = m₂ = {0} (lawful ZH), k = 0: the intersection contains 0
theorem w7c3_88 : ¬ drop0% Std.DHashMap.Internal.Raw₀.getKey?_inter_of_contains_eq_false_left 11 :=
  fun h => by
  have := h (m₁ := (⟨⟨1, #[b1 (W1c5.ZH.mk 0) (0 : Nat), .nil]⟩, by simp⟩ : Raw₀ W1c5.ZH (fun _ => Nat))) (m₂ := (⟨⟨1, #[b1 (W1c5.ZH.mk 0) (0 : Nat), .nil]⟩, by simp⟩ : Raw₀ W1c5.ZH (fun _ => Nat))) (W1c5.zh_wf _ _ rfl (by simp [toListModel])) (W1c5.zh_wf _ _ rfl (by simp [toListModel])) (k := ⟨0⟩)
  revert this; first | decide +kernel | hm_eval3

-- `Std.DHashMap.Raw.getKey?_inter_of_mem_right` (binder 8): bucketless m₁ (Raw.inter then returns m₂), m₂ = {0} (lawful ZH), k = 0: the left side is some 0, m₁.getKey? 0 = none
theorem w7c3_89 : ¬ drop0% Std.DHashMap.Raw.getKey?_inter_of_mem_right 8 :=
  fun h => by
  have := h (m₁ := (⟨0, #[]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (m₂ := ⟨1, #[b1 (W1c5.ZH.mk 0) (0 : Nat), .nil]⟩) (h₂ := W1c5.zh_wf _ _ rfl (by simp [toListModel])) (k := ⟨0⟩) (mem := by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.getKey?_inter_of_mem_right` (binder 9): the intersection holds a filter of m₁ that keeps every entry whose key is == k (r0_inter_perm), so only m₁.WF is needed
theorem w7c3_90 : drop% Std.DHashMap.Raw.getKey?_inter_of_mem_right 9 :=
  by intro α β _ _ m₁ m₂ _ _ h₁ k mem; exact W4c2W.dr_inter_getKey? m₁ m₂ h₁ k mem

-- `Std.HashMap.Raw.getKey?_inter_of_mem_right` (binder 8): bucketless m₁ (Raw.inter then returns m₂), m₂ = {0} (lawful ZH), k = 0: the left side is some 0, m₁.getKey? 0 = none
theorem w7c3_91 : ¬ drop0% Std.HashMap.Raw.getKey?_inter_of_mem_right 8 :=
  fun h => by
  have := h (m₁ := (⟨⟨0, #[]⟩⟩ : HashMap.Raw W1c5.ZH Nat)) (m₂ := ⟨⟨1, #[b1 (W1c5.ZH.mk 0) (0 : Nat), .nil]⟩⟩) (h₂ := ⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩) (k := ⟨0⟩) (mem := by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.HashMap.Raw.getKey?_inter_of_mem_right` (binder 9): the intersection holds a filter of m₁ that keeps every entry whose key is == k (r0_inter_perm), so only m₁.WF is needed
theorem w7c3_92 : drop% Std.HashMap.Raw.getKey?_inter_of_mem_right 9 :=
  by intro α _ _ β m₁ m₂ _ _ h₁ k mem; exact W4c2W.dr_inter_getKey? m₁.inner m₂.inner h₁.out k mem

-- `Std.DHashMap.Raw.getKey?_inter_of_not_mem_right` (binder 8): k ∉ m₂ with m₂ WF already gives k ∉ m₁ ∩ m₂ for any m₁ (W3c3.dr_nmi), and a non-member has no getKey? (no WF)
theorem w7c3_93 : drop% Std.DHashMap.Raw.getKey?_inter_of_not_mem_right 8 :=
  by intro α β _ _ m₁ m₂ _ _ h₂ k not_mem; exact W3c4.dr_getKey?_nc _ k (W3c3.dr_nmi m₁ m₂ h₂ k not_mem)

-- `Std.DHashMap.Raw.getKey?_inter_of_not_mem_right` (binder 9): m₁ = {0} (lawful ZH), m₂ with size field 0 holds 0 misplaced in bucket 1: 0 ∉ m₂ by contains, but the intersection folds over m₂ and keeps 0
theorem w7c3_94 : ¬ drop0% Std.DHashMap.Raw.getKey?_inter_of_not_mem_right 9 :=
  fun h => by
  have := h (m₁ := (⟨1, #[b1 (W1c5.ZH.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (m₂ := ⟨0, #[.nil, b1 (W1c5.ZH.mk 0) (0 : Nat)]⟩) (h₁ := W1c5.zh_wf _ _ rfl (by simp [toListModel])) (k := ⟨0⟩) (not_mem := by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.HashMap.Raw.getKey?_inter_of_not_mem_right` (binder 8): k ∉ m₂ with m₂ WF already gives k ∉ m₁ ∩ m₂ for any m₁ (W3c3.dr_nmi), and a non-member has no getKey? (no WF)
theorem w7c3_95 : drop% Std.HashMap.Raw.getKey?_inter_of_not_mem_right 8 :=
  by intro α _ _ β m₁ m₂ _ _ h₂ k not_mem; exact W3c4.dr_getKey?_nc _ k (W3c3.dr_nmi m₁.inner m₂.inner h₂.out k not_mem)

-- `Std.HashMap.Raw.getKey?_inter_of_not_mem_right` (binder 9): m₁ = {0} (lawful ZH), m₂ with size field 0 holds 0 misplaced in bucket 1: 0 ∉ m₂ by contains, but the intersection folds over m₂ and keeps 0
theorem w7c3_96 : ¬ drop0% Std.HashMap.Raw.getKey?_inter_of_not_mem_right 9 :=
  fun h => by
  have := h (m₁ := (⟨⟨1, #[b1 (W1c5.ZH.mk 0) (0 : Nat), .nil]⟩⟩ : HashMap.Raw W1c5.ZH Nat)) (m₂ := ⟨⟨0, #[.nil, b1 (W1c5.ZH.mk 0) (0 : Nat)]⟩⟩) (h₁ := ⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩) (k := ⟨0⟩) (not_mem := by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.getKeyD_union_of_not_mem_left` (binder 8): m₁ with size field 0 holds 0 misplaced in bucket 1 (lawful ZH), m₂ = ∅: 0 ∉ m₁, the union reinserts 0 into m₂ properly, so getKeyD 0 7 is 0, not 7
theorem w7c3_97 : ¬ drop0% Std.DHashMap.Raw.getKeyD_union_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := (⟨0, #[.nil, b1 (W1c5.ZH.mk 0) (0 : Nat)]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (m₂ := ⟨0, #[.nil, .nil]⟩) (h₂ := W1c5.zh_wf _ _ rfl (by simp [toListModel])) (k := ⟨0⟩) (fallback := ⟨7⟩) (mem := by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.getKeyD_union_of_not_mem_left` (binder 9): m₁ = {1}, m₂ with size field 0 holds 0 misplaced in bucket 1 (lawful ZH): the union inserts 0 into m₁ properly, so getKeyD 0 7 is 0 while m₂.getKeyD 0 7 = 7
theorem w7c3_98 : ¬ drop0% Std.DHashMap.Raw.getKeyD_union_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := (⟨1, #[b1 (W1c5.ZH.mk 1) (0 : Nat), .nil]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (m₂ := ⟨0, #[.nil, b1 (W1c5.ZH.mk 0) (0 : Nat)]⟩) (h₁ := W1c5.zh_wf _ _ rfl (by simp [toListModel])) (k := ⟨0⟩) (fallback := ⟨7⟩) (mem := by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.HashMap.Raw.getKeyD_union_of_not_mem_left` (binder 8): m₁ with size field 0 holds 0 misplaced in bucket 1 (lawful ZH), m₂ = ∅: 0 ∉ m₁, the union reinserts 0 into m₂ properly, so getKeyD 0 7 is 0, not 7
theorem w7c3_99 : ¬ drop0% Std.HashMap.Raw.getKeyD_union_of_not_mem_left 8 :=
  fun h => by
  have := h (m₁ := (⟨⟨0, #[.nil, b1 (W1c5.ZH.mk 0) (0 : Nat)]⟩⟩ : HashMap.Raw W1c5.ZH Nat)) (m₂ := ⟨⟨0, #[.nil, .nil]⟩⟩) (h₂ := ⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩) (k := ⟨0⟩) (fallback := ⟨7⟩) (not_mem := by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.HashMap.Raw.getKeyD_union_of_not_mem_left` (binder 9): m₁ = {1}, m₂ with size field 0 holds 0 misplaced in bucket 1 (lawful ZH): the union inserts 0 into m₁ properly, so getKeyD 0 7 is 0 while m₂.getKeyD 0 7 = 7
theorem w7c3_100 : ¬ drop0% Std.HashMap.Raw.getKeyD_union_of_not_mem_left 9 :=
  fun h => by
  have := h (m₁ := (⟨⟨1, #[b1 (W1c5.ZH.mk 1) (0 : Nat), .nil]⟩⟩ : HashMap.Raw W1c5.ZH Nat)) (m₂ := ⟨⟨0, #[.nil, b1 (W1c5.ZH.mk 0) (0 : Nat)]⟩⟩) (h₁ := ⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩) (k := ⟨0⟩) (fallback := ⟨7⟩) (not_mem := by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DHashMap.Raw.WF.Const.insertMany` (binder 8): bucketless raw map (size field 0, no buckets): insertMany leaves it unchanged, and it is not WF (WF needs a bucket)
theorem w7c3_101 : ¬ drop0% Std.DHashMap.Raw.WF.Const.insertMany 8 :=
  fun h => by
  have := h (m := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (l := ([] : List (Nat × Nat)))
  exact absurd this.size_buckets_pos (by decide)

-- `Std.DHashMap.Raw.WF.insertMany` (binder 8): bucketless raw map (size field 0, no buckets): insertMany leaves it unchanged, and it is not WF (WF needs a bucket)
theorem w7c3_102 : ¬ drop0% Std.DHashMap.Raw.WF.insertMany 8 :=
  fun h => by
  have := h (m := (⟨0, #[]⟩ : DHashMap.Raw Nat (fun _ => Nat))) (l := ([] : List ((_ : Nat) × Nat)))
  exact absurd this.size_buckets_pos (by decide)

-- `Std.HashMap.Raw.WF.insertMany` (binder 8): bucketless raw map (size field 0, no buckets): insertMany leaves it unchanged, and it is not WF (WF needs a bucket)
theorem w7c3_103 : ¬ drop0% Std.HashMap.Raw.WF.insertMany 8 :=
  fun h => by
  have := h (m := (⟨⟨0, #[]⟩⟩ : HashMap.Raw Nat Nat)) (l := ([] : List (Nat × Nat)))
  exact absurd this.out.size_buckets_pos (by decide)

-- `Std.HashSet.Raw.WF.insertMany` (binder 7): bucketless raw map (size field 0, no buckets): insertMany leaves it unchanged, and it is not WF (WF needs a bucket)
theorem w7c3_104 : ¬ drop0% Std.HashSet.Raw.WF.insertMany 7 :=
  fun h => by
  have := h (m := (⟨⟨⟨0, #[]⟩⟩⟩ : HashSet.Raw Nat)) (l := ([] : List Nat))
  exact absurd this.out.out.size_buckets_pos (by decide)

-- `Std.HashMap.Equiv.insertManyIfNewUnit_list` (binder 8): m₁ = ∅, m₂ = {0} (lawful ZH), l = []: not equivalent
theorem w7c3_105 : ¬ drop0% Std.HashMap.Equiv.insertManyIfNewUnit_list 8 :=
  fun h => by
  have := h (m₁ := (⟨⟨⟨0, #[.nil, .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩ : HashMap W1c5.ZH Unit)) (m₂ := (⟨⟨⟨1, #[b1 (W1c5.ZH.mk 0) (), .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩ : HashMap W1c5.ZH Unit)) []
  w7ne this

-- `Std.HashMap.Raw.Equiv.insertManyIfNewUnit_list` (binder 10): m₁ = ∅, m₂ = {0} (lawful ZH), l = []: not equivalent
theorem w7c3_106 : ¬ drop0% Std.HashMap.Raw.Equiv.insertManyIfNewUnit_list 10 :=
  fun h => by
  have := h (m₁ := (⟨⟨0, #[.nil, .nil]⟩⟩ : HashMap.Raw W1c5.ZH Unit)) (m₂ := (⟨⟨1, #[b1 (W1c5.ZH.mk 0) (), .nil]⟩⟩ : HashMap.Raw W1c5.ZH Unit)) (h₁ := ⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩) (h₂ := ⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩) []
  simp only [HashMap.Raw.insertManyIfNewUnit, W7c3.dru_imf, List.foldl_cons, List.foldl_nil] at this
  w7ne this

-- `Std.HashMap.Raw.Equiv.insertManyIfNewUnit_list` (binder 7): m₁ holds 0 misplaced in bucket 1, m₂ = {0} (lawful ZH; same entries, so Equiv), l = [0]: m₁ gains a second 0, m₂ does not
theorem w7c3_107 : ¬ drop0% Std.HashMap.Raw.Equiv.insertManyIfNewUnit_list 7 :=
  fun h => by
  have := h (m₁ := (⟨⟨1, #[.nil, b1 (W1c5.ZH.mk 0) ()]⟩⟩ : HashMap.Raw W1c5.ZH Unit)) (m₂ := (⟨⟨1, #[b1 (W1c5.ZH.mk 0) (), .nil]⟩⟩ : HashMap.Raw W1c5.ZH Unit)) (h₂ := ⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩) [⟨0⟩] ⟨⟨by simp [toListModel]⟩⟩
  simp only [HashMap.Raw.insertManyIfNewUnit, W7c3.dru_imf, List.foldl_cons, List.foldl_nil] at this
  exact absurd (List.Perm.length_eq this.1.1) (by decide +kernel)

-- `Std.HashMap.Raw.Equiv.insertManyIfNewUnit_list` (binder 8): m₂ holds 0 misplaced in bucket 1, m₁ = {0} (lawful ZH; same entries, so Equiv), l = [0]: m₂ gains a second 0, m₁ does not
theorem w7c3_108 : ¬ drop0% Std.HashMap.Raw.Equiv.insertManyIfNewUnit_list 8 :=
  fun h => by
  have := h (m₂ := (⟨⟨1, #[.nil, b1 (W1c5.ZH.mk 0) ()]⟩⟩ : HashMap.Raw W1c5.ZH Unit)) (m₁ := (⟨⟨1, #[b1 (W1c5.ZH.mk 0) (), .nil]⟩⟩ : HashMap.Raw W1c5.ZH Unit)) (h₁ := ⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩) [⟨0⟩] ⟨⟨by simp [toListModel]⟩⟩
  simp only [HashMap.Raw.insertManyIfNewUnit, W7c3.dru_imf, List.foldl_cons, List.foldl_nil] at this
  exact absurd (List.Perm.length_eq this.1.1) (by decide +kernel)

-- `Std.DHashMap.Raw.Const.insertMany_append` (binder 5): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_109 : drop% Std.DHashMap.Raw.Const.insertMany_append 5 :=
  by intros; simp only [W7c3.drc_imf, List.foldl_append]

-- `Std.DHashMap.Raw.insertMany_append` (binder 7): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_110 : drop% Std.DHashMap.Raw.insertMany_append 7 :=
  by intros; simp only [W7c3.dr_imf, List.foldl_append]

-- `Std.HashMap.Raw.insertMany_append` (binder 5): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_111 : drop% Std.HashMap.Raw.insertMany_append 5 :=
  by intros; simp only [W7c3.hmr_imf, List.foldl_append]

-- `Std.HashSet.Raw.insertMany_append` (binder 4): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_112 : drop% Std.HashSet.Raw.insertMany_append 4 :=
  by intros; simp only [W7c3.hsr_imf, List.foldl_append]

-- `Std.DHashMap.Raw.Const.insertMany_list_equiv_foldl` (binder 6): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_113 : drop% Std.DHashMap.Raw.Const.insertMany_list_equiv_foldl 6 :=
  by intros; first | (rw [W7c3.drc_imf]; done) | (rw [W7c3.drc_imf]; exact DHashMap.Raw.Equiv.refl _)

-- `Std.DHashMap.Raw.insertMany_list_equiv_foldl` (binder 6): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_114 : drop% Std.DHashMap.Raw.insertMany_list_equiv_foldl 6 :=
  by intros; first | (rw [W7c3.dr_imf]; done) | (rw [W7c3.dr_imf]; exact DHashMap.Raw.Equiv.refl _)

-- `Std.HashMap.Raw.insertMany_list_equiv_foldl` (binder 6): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_115 : drop% Std.HashMap.Raw.insertMany_list_equiv_foldl 6 :=
  by intros; first | (rw [W7c3.hmr_imf]; done) | (rw [W7c3.hmr_imf]; exact HashMap.Raw.Equiv.refl _)

-- `Std.HashSet.Raw.insertMany_list_equiv_foldl` (binder 5): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_116 : drop% Std.HashSet.Raw.insertMany_list_equiv_foldl 5 :=
  by intros; first | (rw [W7c3.hsr_imf]; done) | (rw [W7c3.hsr_imf]; exact HashSet.Raw.Equiv.refl _)

-- `Std.DHashMap.Raw.Const.insertMany_list_singleton` (binder 5): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_117 : drop% Std.DHashMap.Raw.Const.insertMany_list_singleton 5 :=
  by intros; first | (rw [W7c3.drc_imf]; done) | (rw [W7c3.drc_imf]; rfl)

-- `Std.DHashMap.Raw.insertMany_list_singleton` (binder 9): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_118 : drop% Std.DHashMap.Raw.insertMany_list_singleton 9 :=
  by intros; first | (rw [W7c3.dr_imf]; done) | (rw [W7c3.dr_imf]; rfl)

-- `Std.HashMap.Raw.insertMany_list_singleton` (binder 5): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_119 : drop% Std.HashMap.Raw.insertMany_list_singleton 5 :=
  by intros; first | (rw [W7c3.hmr_imf]; done) | (rw [W7c3.hmr_imf]; rfl)

-- `Std.HashSet.Raw.insertMany_list_singleton` (binder 4): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_120 : drop% Std.HashSet.Raw.insertMany_list_singleton 4 :=
  by intros; first | (rw [W7c3.hsr_imf]; done) | (rw [W7c3.hsr_imf]; rfl)

-- `Std.DHashMap.Raw.Const.insertMany_nil` (binder 5): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_121 : drop% Std.DHashMap.Raw.Const.insertMany_nil 5 :=
  by intros; first | (rw [W7c3.drc_imf]; done) | (rw [W7c3.drc_imf]; rfl)

-- `Std.DHashMap.Raw.insertMany_nil` (binder 7): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_122 : drop% Std.DHashMap.Raw.insertMany_nil 7 :=
  by intros; first | (rw [W7c3.dr_imf]; done) | (rw [W7c3.dr_imf]; rfl)

-- `Std.HashMap.Raw.insertMany_nil` (binder 5): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_123 : drop% Std.HashMap.Raw.insertMany_nil 5 :=
  by intros; first | (rw [W7c3.hmr_imf]; done) | (rw [W7c3.hmr_imf]; rfl)

-- `Std.HashSet.Raw.insertMany_nil` (binder 4): Raw insertMany over a list equals the foldl of Raw inserts on any raw map (bucketless maps stay unchanged), so no WF is needed
theorem w7c3_124 : drop% Std.HashSet.Raw.insertMany_nil 4 :=
  by intros; first | (rw [W7c3.hsr_imf]; done) | (rw [W7c3.hsr_imf]; rfl)

-- `Std.DHashMap.Internal.Raw₀.Const.isEmpty_insertMany_emptyWithCapacity_list` (binder 4): inserting into an empty map sets size field 1 and later inserts never lower it (any instances)
theorem w7c3_125 : drop% Std.DHashMap.Internal.Raw₀.Const.isEmpty_insertMany_emptyWithCapacity_list 4 :=
  by intros; exact W7c3.r0c_ofl _ _

-- `Std.DHashMap.Internal.Raw₀.isEmpty_insertMany_emptyWithCapacity_list` (binder 4): inserting into an empty map sets size field 1 and later inserts never lower it (any instances)
theorem w7c3_126 : drop% Std.DHashMap.Internal.Raw₀.isEmpty_insertMany_emptyWithCapacity_list 4 :=
  by intros; exact W7c3.r0_ofl _ _

-- `Std.DHashMap.Internal.Raw₀.Const.isEmpty_insertMany_emptyWithCapacity_list` (binder 5): inserting into an empty map sets size field 1 and later inserts never lower it (any instances)
theorem w7c3_127 : drop% Std.DHashMap.Internal.Raw₀.Const.isEmpty_insertMany_emptyWithCapacity_list 5 :=
  by intros; exact W7c3.r0c_ofl _ _

-- `Std.DHashMap.Internal.Raw₀.isEmpty_insertMany_emptyWithCapacity_list` (binder 5): inserting into an empty map sets size field 1 and later inserts never lower it (any instances)
theorem w7c3_128 : drop% Std.DHashMap.Internal.Raw₀.isEmpty_insertMany_emptyWithCapacity_list 5 :=
  by intros; exact W7c3.r0_ofl _ _

-- `Std.DHashMap.Equiv.keys_perm` (binder 6): m₁ = ∅, m₂ = {0} (lawful ZH, hash 0): the key lists have lengths 0 and 1
theorem w7c3_129 : ¬ drop0% Std.DHashMap.Equiv.keys_perm 6 :=
  fun h => absurd (h (m₁ := (⟨⟨0, #[.nil, .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩ : DHashMap W1c5.ZH (fun _ => Nat))) (m₂ := (⟨⟨1, #[b1 (W1c5.ZH.mk 0) (0 : Nat), .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩ : DHashMap W1c5.ZH (fun _ => Nat)))).length_eq (by decide +kernel)

-- `Std.DHashMap.Raw.Equiv.keys_perm` (binder 4): m₁ = ∅, m₂ = {0} (lawful ZH, hash 0): the key lists have lengths 0 and 1
theorem w7c3_130 : ¬ drop0% Std.DHashMap.Raw.Equiv.keys_perm 4 :=
  fun h => absurd (h (m₁ := (⟨0, #[.nil, .nil]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (m₂ := (⟨1, #[b1 (W1c5.ZH.mk 0) (0 : Nat), .nil]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat)))).length_eq (by decide +kernel)

-- `Std.HashMap.Equiv.keys_perm` (binder 6): m₁ = ∅, m₂ = {0} (lawful ZH, hash 0): the key lists have lengths 0 and 1
theorem w7c3_131 : ¬ drop0% Std.HashMap.Equiv.keys_perm 6 :=
  fun h => absurd (h (m₁ := (⟨⟨⟨0, #[.nil, .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩ : HashMap W1c5.ZH Nat)) (m₂ := (⟨⟨⟨1, #[b1 (W1c5.ZH.mk 0) (0 : Nat), .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩ : HashMap W1c5.ZH Nat))).length_eq (by decide +kernel)

-- `Std.HashMap.Raw.Equiv.keys_perm` (binder 4): m₁ = ∅, m₂ = {0} (lawful ZH, hash 0): the key lists have lengths 0 and 1
theorem w7c3_132 : ¬ drop0% Std.HashMap.Raw.Equiv.keys_perm 4 :=
  fun h => absurd (h (m₁ := (⟨⟨0, #[.nil, .nil]⟩⟩ : HashMap.Raw W1c5.ZH Nat)) (m₂ := (⟨⟨1, #[b1 (W1c5.ZH.mk 0) (0 : Nat), .nil]⟩⟩ : HashMap.Raw W1c5.ZH Nat))).length_eq (by decide +kernel)

-- `Std.HashMap.mem_alter` (binder 5): NS (a ≤ b, hash 0): m = {0 ↦ 5}, k = 1, k' = 0: the update finds the stored 0 by 0 ≤ 1, while the k == k' test (1 ≤ 0) is false
theorem w7c3_133 : ¬ drop0% Std.HashMap.mem_alter 5 :=
  fun h => absurd (h (m := (hm NS.broken 1 #[(.cons (NS.mk 0) (5 : Nat) .nil)] (by decide) : HashMap NS Nat)) (k := ⟨1⟩) (k' := ⟨0⟩) (f := fun _ => none)) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.Raw.mem_alter` (binder 6): AB: m = {0 ↦ 5 (bucket 0), 1 ↦ 7 (bucket 1)}, k = 0, k' = 1: 0 == 1, so the right side uses the updated value of 0, but the update leaves bucket 1 alone
theorem w7c3_134 : ¬ drop0% Std.HashMap.Raw.mem_alter 6 :=
  fun h => absurd (h (m := (hmr 2 #[(.cons (AB.mk 0) (5 : Nat) .nil), (.cons (AB.mk 1) (7 : Nat) .nil)] : HashMap.Raw AB Nat)) (h := (hmr_wf AB.broken _ _ (by decide))) (k := ⟨0⟩) (k' := ⟨1⟩) (f := fun _ => none)) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.mem_alter` (binder 6): AB: m = {0 ↦ 5 (bucket 0), 1 ↦ 7 (bucket 1)}, k = 0, k' = 1: 0 == 1, so the right side uses the updated value of 0, but the update leaves bucket 1 alone
theorem w7c3_135 : ¬ drop0% Std.HashMap.mem_alter 6 :=
  fun h => absurd (h (m := (hm AB.broken 2 #[(.cons (AB.mk 0) (5 : Nat) .nil), (.cons (AB.mk 1) (7 : Nat) .nil)] (by decide) : HashMap AB Nat)) (k := ⟨0⟩) (k' := ⟨1⟩) (f := fun _ => none)) (by (first | (decide +kernel) | (hm_eval; done) | hm_expand | (simp only [DHashMap.Const.insertIfNew, DHashMap.Const.get!, DHashMap.Const.modify, DHashMap.Const.get?]; hm_eval; done) | (simp only [DHashMap.Raw.Const.insertIfNew, DHashMap.Raw.Const.get!, DHashMap.Raw.insertIfNew, DHashMap.Raw.get!, DHashMap.Raw.Const.modify, DHashMap.Raw.Const.get?]; hm_eval_raw; done) | (simp only [HashMap.modify, HashMap.alter, HashMap.Raw.modify, HashMap.Raw.alter, hm_getElem?, hmr_getElem?, hm_getElem!, hmr_getElem!, HashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashMap.contains, HashMap.Raw.contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))))

-- `Std.HashMap.Raw.mem_alter` (binder 10): bucketless raw map (size 0, no buckets): alter leaves it unchanged, so k is still absent although f sets some 1
theorem w7c3_136 : ¬ drop0% Std.HashMap.Raw.mem_alter 10 :=
  fun h => absurd (h (m := (⟨⟨0, #[]⟩⟩ : HashMap.Raw Nat Nat)) (k := 0) (k' := 0) (f := fun _ => some 1)) (by rw [show ((⟨⟨0, #[]⟩⟩ : HashMap.Raw Nat Nat).alter 0 (fun _ => some 1)) = ∅ from rfl]; simp)

-- `Std.DHashMap.Const.mem_toList_iff_get?_eq_some` (binder 5): HB (a/2 == b/2, lawful except LawfulBEq): m = {0 ↦ 5}, k = 1: get? 1 = some 5 but (1, 5) is not listed
theorem w7c3_137 : ¬ drop0% Std.DHashMap.Const.mem_toList_iff_get?_eq_some 5 :=
  fun h => by
  have := (h (m := ((∅ : DHashMap HB (fun _ => Nat)).insert ⟨0⟩ 5)) (k := ⟨1⟩) (v := 5)).mpr (by decide +kernel)
  have e : DHashMap.Const.toList ((∅ : DHashMap HB (fun _ => Nat)).insert ⟨0⟩ 5) = [(⟨0⟩, 5)] := by decide +kernel
  rw [e] at this; simp at this

-- `Std.DHashMap.Internal.Raw₀.Const.mem_toList_iff_get?_eq_some` (binder 6): lawful ZH (hash 0), entry 0 ↦ 5 misplaced in bucket 1 of 2: listed by toList, but get? 0 scans bucket 0 and returns none
theorem w7c3_138 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.mem_toList_iff_get?_eq_some 6 :=
  fun h => absurd ((h (m := (⟨⟨1, #[.nil, b1 (W1c5.ZH.mk 0) (5 : Nat)]⟩, by decide⟩ : Raw₀ W1c5.ZH (fun _ => Nat))) (k := ⟨0⟩) (v := 5) ).mp (by decide +kernel)) (by decide +kernel)

-- `Std.DHashMap.Raw.Const.mem_toList_iff_get?_eq_some` (binder 6): lawful ZH (hash 0), entry 0 ↦ 5 misplaced in bucket 1 of 2: listed by toList, but get? 0 scans bucket 0 and returns none
theorem w7c3_139 : ¬ drop0% Std.DHashMap.Raw.Const.mem_toList_iff_get?_eq_some 6 :=
  fun h => absurd ((h (m := (⟨1, #[.nil, b1 (W1c5.ZH.mk 0) (5 : Nat)]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (k := ⟨0⟩) (v := 5) ).mp (by decide +kernel)) (by decide +kernel)

-- `Std.DHashMap.Raw.mem_toList_iff_get?_eq_some` (binder 6): lawful ZH (hash 0), entry 0 ↦ 5 misplaced in bucket 1 of 2: listed by toList, but get? 0 scans bucket 0 and returns none
theorem w7c3_140 : ¬ drop0% Std.DHashMap.Raw.mem_toList_iff_get?_eq_some 6 :=
  fun h => absurd ((h (m := (⟨1, #[.nil, b1 (W1c5.ZH.mk 0) (5 : Nat)]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (k := ⟨0⟩) (v := 5) ).mp (by decide +kernel)) (by decide +kernel)

-- `Std.ExtDHashMap.Const.ofList_eq_empty_iff` (binder 4): ofList [] is ∅ by definition, and inserting into any map leaves an entry, so ofList (hd :: tl) is not equivalent to ∅ (any instances)
theorem w7c3_141 : drop% Std.ExtDHashMap.Const.ofList_eq_empty_iff 4 :=
  by
  intro α; intros; rename_i l
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases l with
  | nil => rfl
  | cons hd tl =>
    exfalso
    have h' := Quotient.exact (congrArg ExtDHashMap.inner h)
    have p := h'.inner.impl
    have hr : (DHashMap.Const.ofList (hd :: tl)).inner = (Raw₀.Const.insertListₘ (Raw₀.emptyWithCapacity 8) (hd :: tl)).1 := hm_ofList_raw (hd :: tl)
    rw [hr] at p
    exact tlm_insertList_ne_nil tl _ hd (List.Perm.eq_nil (p.trans (by
      show List.Perm (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets) []
      simp)))

-- `Std.ExtDHashMap.ofList_eq_empty_iff` (binder 4): ofList [] is ∅ by definition, and inserting into any map leaves an entry, so ofList (hd :: tl) is not equivalent to ∅ (any instances)
theorem w7c3_142 : drop% Std.ExtDHashMap.ofList_eq_empty_iff 4 :=
  by
  intro α; intros; rename_i l
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases l with
  | nil => rfl
  | cons hd tl =>
    exfalso
    have h' := Quotient.exact (congrArg ExtDHashMap.inner h)
    have p := h'.inner.impl
    have hr : (DHashMap.ofList (hd :: tl)).1 = (Raw₀.insertListₘ (Raw₀.emptyWithCapacity 8) (hd :: tl)).1 := W7c3.dm_ofList_raw (hd :: tl)
    rw [hr] at p
    exact W7c3.tlm_il_ne_nil tl _ hd (List.Perm.eq_nil (p.trans (by
      show List.Perm (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets) []
      simp)))

-- `Std.ExtDHashMap.Const.ofList_eq_empty_iff` (binder 5): ofList [] is ∅ by definition, and inserting into any map leaves an entry, so ofList (hd :: tl) is not equivalent to ∅ (any instances)
theorem w7c3_143 : drop% Std.ExtDHashMap.Const.ofList_eq_empty_iff 5 :=
  by
  intro α; intros; rename_i l
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases l with
  | nil => rfl
  | cons hd tl =>
    exfalso
    have h' := Quotient.exact (congrArg ExtDHashMap.inner h)
    have p := h'.inner.impl
    have hr : (DHashMap.Const.ofList (hd :: tl)).inner = (Raw₀.Const.insertListₘ (Raw₀.emptyWithCapacity 8) (hd :: tl)).1 := hm_ofList_raw (hd :: tl)
    rw [hr] at p
    exact tlm_insertList_ne_nil tl _ hd (List.Perm.eq_nil (p.trans (by
      show List.Perm (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets) []
      simp)))

-- `Std.ExtDHashMap.ofList_eq_empty_iff` (binder 5): ofList [] is ∅ by definition, and inserting into any map leaves an entry, so ofList (hd :: tl) is not equivalent to ∅ (any instances)
theorem w7c3_144 : drop% Std.ExtDHashMap.ofList_eq_empty_iff 5 :=
  by
  intro α; intros; rename_i l
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases l with
  | nil => rfl
  | cons hd tl =>
    exfalso
    have h' := Quotient.exact (congrArg ExtDHashMap.inner h)
    have p := h'.inner.impl
    have hr : (DHashMap.ofList (hd :: tl)).1 = (Raw₀.insertListₘ (Raw₀.emptyWithCapacity 8) (hd :: tl)).1 := W7c3.dm_ofList_raw (hd :: tl)
    rw [hr] at p
    exact W7c3.tlm_il_ne_nil tl _ hd (List.Perm.eq_nil (p.trans (by
      show List.Perm (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets) []
      simp)))

-- `Std.HashSet.Raw.Equiv.of_forall_contains_eq` (binder 5): HZ0 (a/2 == b/2, hash 0): m₁ = {0}, m₂ = {1} have the same contains but different stored keys
theorem w7c3_145 : ¬ drop0% Std.HashSet.Raw.Equiv.of_forall_contains_eq 5 :=
  fun h => by
  have := h (m₁ := ((∅ : HashSet.Raw W4c4.HZ0).insert ⟨0⟩)) (m₂ := ((∅ : HashSet.Raw W4c4.HZ0).insert ⟨1⟩)) (h₁ := HashSet.Raw.WF.insert HashSet.Raw.WF.empty) (h₂ := HashSet.Raw.WF.insert HashSet.Raw.WF.empty) (h := fun k => by
    obtain ⟨n⟩ := k
    simp only [HashSet.Raw.contains_insert HashSet.Raw.WF.empty, HashSet.Raw.contains_empty]
    simp [BEq.beq])
  exact absurd (List.Perm.mem_iff (a := (⟨⟨0⟩, ()⟩ : (_ : W4c4.HZ0) × Unit)) this.1.1.1) (by decide +kernel)

-- `Std.HashSet.Raw.Equiv.of_forall_contains_eq` (binder 6): m₁ holds key 0 misplaced in bucket 1 of 2 (lawful ZH, hash 0): contains is false everywhere, as for m₂ = ∅, but m₁ has one entry
theorem w7c3_146 : ¬ drop0% Std.HashSet.Raw.Equiv.of_forall_contains_eq 6 :=
  fun h => by
  have := h (m₁ := (⟨⟨⟨1, #[.nil, b1 (W1c5.ZH.mk 0) ()]⟩⟩⟩ : HashSet.Raw W1c5.ZH)) (m₂ := (⟨⟨⟨0, #[.nil, .nil]⟩⟩⟩ : HashSet.Raw W1c5.ZH)) (h₂ := ⟨⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩) (h := fun k => by
    simp only [HashSet.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains]
    rw [dite_eq_left_of_eq_true (by decide), dite_eq_left_of_eq_true (by decide), W1c5.zh_contains, W1c5.zh_contains])
  w7ne this

-- `Std.HashSet.Raw.Equiv.of_forall_contains_eq` (binder 7): m₂ holds key 0 misplaced in bucket 1 of 2 (lawful ZH, hash 0): contains is false everywhere, as for m₁ = ∅, but m₂ has one entry
theorem w7c3_147 : ¬ drop0% Std.HashSet.Raw.Equiv.of_forall_contains_eq 7 :=
  fun h => by
  have := h (m₂ := (⟨⟨⟨1, #[.nil, b1 (W1c5.ZH.mk 0) ()]⟩⟩⟩ : HashSet.Raw W1c5.ZH)) (m₁ := (⟨⟨⟨0, #[.nil, .nil]⟩⟩⟩ : HashSet.Raw W1c5.ZH)) (h₁ := ⟨⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩) (h := fun k => by
    simp only [HashSet.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains]
    rw [dite_eq_left_of_eq_true (by decide), dite_eq_left_of_eq_true (by decide), W1c5.zh_contains, W1c5.zh_contains])
  w7ne this

-- `Std.HashSet.Raw.Equiv.of_forall_contains_eq` (binder 8): m₁ = ∅, m₂ = {0} (lawful ZH)
theorem w7c3_148 : ¬ drop0% Std.HashSet.Raw.Equiv.of_forall_contains_eq 8 :=
  fun h => by
  have := h (m₁ := (⟨⟨⟨0, #[.nil, .nil]⟩⟩⟩ : HashSet.Raw W1c5.ZH)) (m₂ := (⟨⟨⟨1, #[b1 (W1c5.ZH.mk 0) (), .nil]⟩⟩⟩ : HashSet.Raw W1c5.ZH)) (h₁ := ⟨⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩) (h₂ := ⟨⟨W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩)
  w7ne this

-- `Std.DHashMap.Equiv.of_keys_unit_perm` (binder 5): m₁ = ∅, m₂ = {0} (lawful ZH, hash 0): not equivalent (0 vs 1 entries)
theorem w7c3_149 : ¬ drop0% Std.DHashMap.Equiv.of_keys_unit_perm 5 :=
  fun h => by
  have := h (m₁ := (⟨⟨0, #[.nil, .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩ : DHashMap W1c5.ZH (fun _ => Unit))) (m₂ := (⟨⟨1, #[b1 (W1c5.ZH.mk 0) (), .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩ : DHashMap W1c5.ZH (fun _ => Unit)))
  w7ne this

-- `Std.DHashMap.Raw.Equiv.of_keys_unit_perm` (binder 3): m₁ = ∅, m₂ = {0} (lawful ZH, hash 0): not equivalent (0 vs 1 entries)
theorem w7c3_150 : ¬ drop0% Std.DHashMap.Raw.Equiv.of_keys_unit_perm 3 :=
  fun h => by
  have := h (m₁ := (⟨0, #[.nil, .nil]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Unit))) (m₂ := (⟨1, #[b1 (W1c5.ZH.mk 0) (), .nil]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Unit)))
  w7ne this

-- `Std.HashMap.Equiv.of_keys_unit_perm` (binder 5): m₁ = ∅, m₂ = {0} (lawful ZH, hash 0): not equivalent (0 vs 1 entries)
theorem w7c3_151 : ¬ drop0% Std.HashMap.Equiv.of_keys_unit_perm 5 :=
  fun h => by
  have := h (m₁ := (⟨⟨⟨0, #[.nil, .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩ : HashMap W1c5.ZH Unit)) (m₂ := (⟨⟨⟨1, #[b1 (W1c5.ZH.mk 0) (), .nil]⟩, W1c5.zh_wf _ _ rfl (by simp [toListModel])⟩⟩ : HashMap W1c5.ZH Unit))
  w7ne this

-- `Std.HashMap.Raw.Equiv.of_keys_unit_perm` (binder 3): m₁ = ∅, m₂ = {0} (lawful ZH, hash 0): not equivalent (0 vs 1 entries)
theorem w7c3_152 : ¬ drop0% Std.HashMap.Raw.Equiv.of_keys_unit_perm 3 :=
  fun h => by
  have := h (m₁ := (⟨⟨0, #[.nil, .nil]⟩⟩ : HashMap.Raw W1c5.ZH Unit)) (m₂ := (⟨⟨1, #[b1 (W1c5.ZH.mk 0) (), .nil]⟩⟩ : HashMap.Raw W1c5.ZH Unit))
  w7ne this

-- `Std.DHashMap.Internal.Raw₀.Const.size_insertMany_emptyWithCapacity_list` (binder 4): stored keys come from the list; the distinctness premise makes every contains check fail (stored == query is false), so each insert adds one entry (no EquivBEq/LawfulHashable)
theorem w7c3_153 : drop% Std.DHashMap.Internal.Raw₀.Const.size_insertMany_emptyWithCapacity_list 4 :=
  by
  intros; rename_i l hl
  rw [Raw₀.Const.insertMany_eq_insertListₘ, W7c3.ilc_size l _ (by simp) hl]; simp [Raw₀.emptyWithCapacity]

-- `Std.DHashMap.Internal.Raw₀.size_insertMany_emptyWithCapacity_list` (binder 4): stored keys come from the list; the distinctness premise makes every contains check fail (stored == query is false), so each insert adds one entry (no EquivBEq/LawfulHashable)
theorem w7c3_154 : drop% Std.DHashMap.Internal.Raw₀.size_insertMany_emptyWithCapacity_list 4 :=
  by
  intros; rename_i l hl
  rw [Raw₀.insertMany_eq_insertListₘ, W7c3.il_size l _ (by simp) hl]; simp [Raw₀.emptyWithCapacity]

-- `Std.DHashMap.Internal.Raw₀.Const.size_insertMany_emptyWithCapacity_list` (binder 5): stored keys come from the list; the distinctness premise makes every contains check fail (stored == query is false), so each insert adds one entry (no EquivBEq/LawfulHashable)
theorem w7c3_155 : drop% Std.DHashMap.Internal.Raw₀.Const.size_insertMany_emptyWithCapacity_list 5 :=
  by
  intros; rename_i l hl
  rw [Raw₀.Const.insertMany_eq_insertListₘ, W7c3.ilc_size l _ (by simp) hl]; simp [Raw₀.emptyWithCapacity]

-- `Std.DHashMap.Internal.Raw₀.size_insertMany_emptyWithCapacity_list` (binder 5): stored keys come from the list; the distinctness premise makes every contains check fail (stored == query is false), so each insert adds one entry (no EquivBEq/LawfulHashable)
theorem w7c3_156 : drop% Std.DHashMap.Internal.Raw₀.size_insertMany_emptyWithCapacity_list 5 :=
  by
  intros; rename_i l hl
  rw [Raw₀.insertMany_eq_insertListₘ, W7c3.il_size l _ (by simp) hl]; simp [Raw₀.emptyWithCapacity]

-- `Std.DHashMap.Internal.Raw₀.Const.size_insertMany_emptyWithCapacity_list_le` (binder 4): each insert adds at most one to the size field (any instances)
theorem w7c3_157 : drop% Std.DHashMap.Internal.Raw₀.Const.size_insertMany_emptyWithCapacity_list_le 4 :=
  by
  intros; rename_i l
  rw [Raw₀.Const.insertMany_eq_insertListₘ]; exact Nat.le_trans (size_insertList_le l _) (Nat.le_of_eq (by simp [Raw₀.emptyWithCapacity]))

-- `Std.DHashMap.Internal.Raw₀.size_insertMany_emptyWithCapacity_list_le` (binder 4): each insert adds at most one to the size field (any instances)
theorem w7c3_158 : drop% Std.DHashMap.Internal.Raw₀.size_insertMany_emptyWithCapacity_list_le 4 :=
  by
  intros; rename_i l
  rw [Raw₀.insertMany_eq_insertListₘ]; exact Nat.le_trans (W7c3.size_insertListD_le l _) (Nat.le_of_eq (by simp [Raw₀.emptyWithCapacity]))

-- `Std.DHashMap.Internal.Raw₀.Const.size_insertMany_emptyWithCapacity_list_le` (binder 5): each insert adds at most one to the size field (any instances)
theorem w7c3_159 : drop% Std.DHashMap.Internal.Raw₀.Const.size_insertMany_emptyWithCapacity_list_le 5 :=
  by
  intros; rename_i l
  rw [Raw₀.Const.insertMany_eq_insertListₘ]; exact Nat.le_trans (size_insertList_le l _) (Nat.le_of_eq (by simp [Raw₀.emptyWithCapacity]))

-- `Std.DHashMap.Internal.Raw₀.size_insertMany_emptyWithCapacity_list_le` (binder 5): each insert adds at most one to the size field (any instances)
theorem w7c3_160 : drop% Std.DHashMap.Internal.Raw₀.size_insertMany_emptyWithCapacity_list_le 5 :=
  by
  intros; rename_i l
  rw [Raw₀.insertMany_eq_insertListₘ]; exact Nat.le_trans (W7c3.size_insertListD_le l _) (Nat.le_of_eq (by simp [Raw₀.emptyWithCapacity]))

-- `Std.DHashMap.Raw.Const.toArray_toList` (binder 5): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_161 : drop% Std.DHashMap.Raw.Const.toArray_toList 5 :=
  by intros; exact W7c3.drc_tat

-- `Std.DHashMap.Raw.toArray_toList` (binder 5): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_162 : drop% Std.DHashMap.Raw.toArray_toList 5 :=
  by intros; exact W7c3.dr_tat

-- `Std.HashMap.Raw.toArray_toList` (binder 5): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_163 : drop% Std.HashMap.Raw.toArray_toList 5 :=
  by intros; exact W7c3.drc_tat

-- `Std.HashSet.Raw.toArray_toList` (binder 4): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_164 : drop% Std.HashSet.Raw.toArray_toList 4 :=
  by intros; exact W7c3.dk_tat

-- `Std.DHashMap.Internal.Raw₀.toListModel_inter` (binder 3): NS (a ≤ b, hash 0), m₁ = {1, 0}, m₂ = {0} or {1}: the lookup-based intersection and the containsKey filter of the model compare in opposite directions (different lengths)
theorem w7c3_165 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_inter 3 :=
  fun h => by
  first
  | (have := h (W7c3.nsl 2 (.cons (NS.mk 1) () (b1 (NS.mk 0) ()))) (W7c3.nsl 1 (b1 (NS.mk 0) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
     exact absurd this.length_eq (by decide +kernel))
  | (have := h (W7c3.nsl 2 (.cons (NS.mk 1) () (b1 (NS.mk 0) ()))) (W7c3.nsl 1 (b1 (NS.mk 1) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
     exact absurd this.length_eq (by decide +kernel))

-- `Std.DHashMap.Internal.Raw₀.toListModel_inter` (binder 5): HZ (hash 1 for 5, else 0), m₁ = {2 (bucket 0), 5 (bucket 1)} of 8, m₂ = {4}: m₁ is larger, so the intersection looks up 4 in m₁ (bucket 0, misses 5), while the model keeps 5 since 4 == 5
theorem w7c3_166 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_inter 5 :=
  fun h => by
  have := h (W7c3.hz8 2 (b1 (HZ.mk 2) 0) (b1 (HZ.mk 5) 0)) (W7c3.hz8 1 (b1 (HZ.mk 4) 0) .nil) ⟨W7c3.hs_of _ (by simp [Pow2]) (by decide +kernel), rfl, ⟨by decide +kernel⟩⟩ W7c3.hz_w4
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.toListModel_inter` (binder 8): m₁ (size field 5) holds key 0 misplaced in bucket 1 (lawful ZH), m₂ = {0}: the intersection looks up 0 in m₁ and misses it, the model filter keeps it
theorem w7c3_167 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_inter 8 :=
  fun h => by
  have := h (W7c3.zl1 5 (b1 (W1c5.ZH.mk 0) ())) (W7c3.zl 1 (b1 (W1c5.ZH.mk 0) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.toListModel_inter` (binder 9): m₁ = {0}, m₂ (size field 5) holds key 0 misplaced in bucket 1 (lawful ZH): the intersection filters m₁ by m₂.contains, which misses 0; the model keeps it
theorem w7c3_168 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_inter 9 :=
  fun h => by
  have := h (W7c3.zl 1 (b1 (W1c5.ZH.mk 0) ())) (W7c3.zl1 5 (b1 (W1c5.ZH.mk 0) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.toListModel_perm_eraseKey_of_containsₘ_eq_false` (binder 5): HZ (hash 1 for 5, else 0), m = {5} in bucket 1 of 8, a = 4: containsₘ 4 scans bucket 0 and is false, but eraseKey 4 removes 5 (5 == 4) from the model
theorem w7c3_169 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_perm_eraseKey_of_containsₘ_eq_false 5 :=
  fun h => by
  have := h (W7c3.hz8 1 .nil (b1 (HZ.mk 5) 0)) ⟨4⟩ W7c3.hz_w5 (by decide +kernel)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.toListModel_perm_eraseKey_of_containsₘ_eq_false` (binder 9): lawful ZH, m = {0}, a = 0: containsₘ is true, eraseKey removes the entry, so the lengths differ
theorem w7c3_170 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_perm_eraseKey_of_containsₘ_eq_false 9 :=
  fun h => by
  have := h (W7c3.zl 1 (b1 (W1c5.ZH.mk 0) ())) ⟨0⟩ (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.toListModel_perm_eraseKey_of_containsₘ_eq_false` (binder 8): m holds key 0 misplaced in bucket 1 of 2 (lawful ZH): containsₘ 0 is false, but the model holds 0 and eraseKey removes it
theorem w7c3_171 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_perm_eraseKey_of_containsₘ_eq_false 8 :=
  fun h => by
  have := h (W7c3.zl1 1 (b1 (W1c5.ZH.mk 0) ())) ⟨0⟩ (by decide +kernel)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.toListModel_union` (binder 4): NS (a ≤ b, hash 0), one-key maps {1} and {0}: the union finds the other key by the asymmetric ==, the model does not (different lengths)
theorem w7c3_172 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_union 4 :=
  fun h => by
  first
  | (have := h (m₁ := W7c3.nsl 1 (b1 (NS.mk 1) ())) (m₂ := W7c3.nsl 1 (b1 (NS.mk 0) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
     exact absurd this.length_eq (by decide +kernel))
  | (have := h (m₁ := W7c3.nsl 1 (b1 (NS.mk 0) ())) (m₂ := W7c3.nsl 1 (b1 (NS.mk 1) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
     exact absurd this.length_eq (by decide +kernel))

-- `Std.DHashMap.Internal.Raw₀.toListModel_union` (binder 5): HZ (hash 1 for 5, else 0), m₁ = {4} in bucket 0, m₂ = {5} in bucket 1 of 8: the union inserts 4 into bucket 0 (2 entries), the model replaces 5 by 4 (1 entry)
theorem w7c3_173 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_union 5 :=
  fun h => by
  have := h (m₁ := W7c3.hz8 1 (b1 (HZ.mk 4) 0) .nil) (m₂ := W7c3.hz8 1 .nil (b1 (HZ.mk 5) 0)) W7c3.hz_w4 W7c3.hz_w5
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.toListModel_union` (binder 8): m₁ (size field 5) holds key 0 misplaced in bucket 1 of 2 (lawful ZH), m₂ = {0}: inserting 0 into m₁ misses it, giving two entries, the model one
theorem w7c3_174 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_union 8 :=
  fun h => by
  have := h (m₁ := W7c3.zl1 5 (b1 (W1c5.ZH.mk 0) ())) (m₂ := W7c3.zl 1 (b1 (W1c5.ZH.mk 0) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.toListModel_union` (binder 9): m₁ = {0}, m₂ (size field 5) holds key 0 misplaced in bucket 1 (lawful ZH): insertIfNew 0 into m₂ misses it, giving two entries, the model one
theorem w7c3_175 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_union 9 :=
  fun h => by
  have := h (m₁ := W7c3.zl 1 (b1 (W1c5.ZH.mk 0) ())) (m₂ := W7c3.zl1 5 (b1 (W1c5.ZH.mk 0) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.toListModel_unionₘ` (binder 4): NS (a ≤ b, hash 0), one-key maps {1} and {0}: the union finds the other key by the asymmetric ==, the model does not (different lengths)
theorem w7c3_176 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_unionₘ 4 :=
  fun h => by
  first
  | (have := h (m₁ := W7c3.nsl 1 (b1 (NS.mk 1) ())) (m₂ := W7c3.nsl 1 (b1 (NS.mk 0) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
     exact absurd this.length_eq (by decide +kernel))
  | (have := h (m₁ := W7c3.nsl 1 (b1 (NS.mk 0) ())) (m₂ := W7c3.nsl 1 (b1 (NS.mk 1) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
     exact absurd this.length_eq (by decide +kernel))

-- `Std.DHashMap.Internal.Raw₀.toListModel_unionₘ` (binder 5): HZ (hash 1 for 5, else 0), m₁ = {4} in bucket 0, m₂ = {5} in bucket 1 of 8: the union inserts 4 into bucket 0 (2 entries), the model replaces 5 by 4 (1 entry)
theorem w7c3_177 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_unionₘ 5 :=
  fun h => by
  have := h (m₁ := W7c3.hz8 1 (b1 (HZ.mk 4) 0) .nil) (m₂ := W7c3.hz8 1 .nil (b1 (HZ.mk 5) 0)) W7c3.hz_w4 W7c3.hz_w5
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.toListModel_unionₘ` (binder 8): m₁ (size field 5) holds key 0 misplaced in bucket 1 of 2 (lawful ZH), m₂ = {0}: inserting 0 into m₁ misses it, giving two entries, the model one
theorem w7c3_178 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_unionₘ 8 :=
  fun h => by
  have := h (m₁ := W7c3.zl1 5 (b1 (W1c5.ZH.mk 0) ())) (m₂ := W7c3.zl 1 (b1 (W1c5.ZH.mk 0) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.toListModel_unionₘ` (binder 9): m₁ = {0}, m₂ (size field 5) holds key 0 misplaced in bucket 1 (lawful ZH): insertIfNew 0 into m₂ misses it, giving two entries, the model one
theorem w7c3_179 : ¬ drop0% Std.DHashMap.Internal.Raw₀.toListModel_unionₘ 9 :=
  fun h => by
  have := h (m₁ := W7c3.zl 1 (b1 (W1c5.ZH.mk 0) ())) (m₂ := W7c3.zl1 5 (b1 (W1c5.ZH.mk 0) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
  exact absurd this.length_eq (by decide +kernel)

-- `Std.DHashMap.Raw.Const.toList_toArray` (binder 5): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_180 : drop% Std.DHashMap.Raw.Const.toList_toArray 5 :=
  by intros; exact W7c3.drc_tta

-- `Std.DHashMap.Raw.toList_toArray` (binder 5): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_181 : drop% Std.DHashMap.Raw.toList_toArray 5 :=
  by intros; exact W7c3.dr_tta

-- `Std.HashMap.Raw.toList_toArray` (binder 5): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_182 : drop% Std.HashMap.Raw.toList_toArray 5 :=
  by intros; exact W7c3.drc_tta

-- `Std.HashSet.Raw.toList_toArray` (binder 4): the Raw₀ lemma needs only buckets, not WF; a bucketless raw map makes both sides trivial (by_cases on the bucket count)
theorem w7c3_183 : drop% Std.HashSet.Raw.toList_toArray 4 :=
  by intros; exact W7c3.dk_tta

-- `Std.ExtDHashMap.union_insert_right_eq_insert_union` (binder 6): NB (== always false, hash 0) is LawfulHashable but not EquivBEq
theorem w7c3_184 : ¬ indep0% Std.ExtDHashMap.union_insert_right_eq_insert_union 6 :=
  fun h => @NB.broken (h (α := NB) (β := fun _ => Nat) (m₁ := ∅) (m₂ := ∅) (p := ⟨NB.mk 0, (0 : Nat)⟩)) inferInstance

-- `Std.ExtHashMap.union_insert_right_eq_insert_union` (binder 6): NB (== always false, hash 0) is LawfulHashable but not EquivBEq
theorem w7c3_185 : ¬ indep0% Std.ExtHashMap.union_insert_right_eq_insert_union 6 :=
  fun h => @NB.broken (h (α := NB) (β := Nat) (m₁ := ∅) (m₂ := ∅) (p := ⟨NB.mk 0, (0 : Nat)⟩)) inferInstance

-- `Std.ExtDHashMap.union_insert_right_eq_insert_union` (binder 7): AB (== always true, hash n) is EquivBEq but not LawfulHashable
theorem w7c3_186 : ¬ indep0% Std.ExtDHashMap.union_insert_right_eq_insert_union 7 :=
  fun h => @AB.broken inferInstance (h (α := AB) (β := fun _ => Nat) (m₁ := ∅) (m₂ := ∅) (p := ⟨AB.mk 0, (0 : Nat)⟩))

-- `Std.ExtHashMap.union_insert_right_eq_insert_union` (binder 7): AB (== always true, hash n) is EquivBEq but not LawfulHashable
theorem w7c3_187 : ¬ indep0% Std.ExtHashMap.union_insert_right_eq_insert_union 7 :=
  fun h => @AB.broken inferInstance (h (α := AB) (β := Nat) (m₁ := ∅) (m₂ := ∅) (p := ⟨AB.mk 0, (0 : Nat)⟩))

-- `Std.ExtDHashMap.Const.unitOfList_eq_empty_iff` (binder 3): ofList [] is ∅ by definition, and inserting into any map leaves an entry, so ofList (hd :: tl) is not equivalent to ∅ (any instances)
theorem w7c3_188 : drop% Std.ExtDHashMap.Const.unitOfList_eq_empty_iff 3 :=
  by
  intro α; intros; rename_i l
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases l with
  | nil => rfl
  | cons hd tl =>
    exfalso
    have h' := Quotient.exact (congrArg ExtDHashMap.inner h)
    have p := h'.inner.impl
    have hr : (DHashMap.Const.unitOfList (hd :: tl)).inner = (Raw₀.Const.insertListIfNewUnitₘ (Raw₀.emptyWithCapacity 8) (hd :: tl)).1 := hs_ofList_raw (hd :: tl)
    rw [hr] at p
    exact tlm_insertListIfNewUnit_ne_nil tl _ hd (List.Perm.eq_nil (p.trans (by
      show List.Perm (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets) []
      simp)))

-- `Std.ExtHashMap.unitOfList_eq_empty_iff` (binder 3): ofList [] is ∅ by definition, and inserting into any map leaves an entry, so ofList (hd :: tl) is not equivalent to ∅ (any instances)
theorem w7c3_189 : drop% Std.ExtHashMap.unitOfList_eq_empty_iff 3 :=
  by
  intro α; intros; rename_i l
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases l with
  | nil => rfl
  | cons hd tl =>
    exfalso
    have h' := Quotient.exact (congrArg (fun s : ExtHashMap α Unit => s.inner.inner) h)
    have p := h'.inner.impl
    have hr : (DHashMap.Const.unitOfList (hd :: tl)).inner = (Raw₀.Const.insertListIfNewUnitₘ (Raw₀.emptyWithCapacity 8) (hd :: tl)).1 := hs_ofList_raw (hd :: tl)
    rw [hr] at p
    exact tlm_insertListIfNewUnit_ne_nil tl _ hd (List.Perm.eq_nil (p.trans (by
      show List.Perm (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets) []
      simp)))

-- `Std.ExtDHashMap.Const.unitOfList_eq_empty_iff` (binder 4): ofList [] is ∅ by definition, and inserting into any map leaves an entry, so ofList (hd :: tl) is not equivalent to ∅ (any instances)
theorem w7c3_190 : drop% Std.ExtDHashMap.Const.unitOfList_eq_empty_iff 4 :=
  by
  intro α; intros; rename_i l
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases l with
  | nil => rfl
  | cons hd tl =>
    exfalso
    have h' := Quotient.exact (congrArg ExtDHashMap.inner h)
    have p := h'.inner.impl
    have hr : (DHashMap.Const.unitOfList (hd :: tl)).inner = (Raw₀.Const.insertListIfNewUnitₘ (Raw₀.emptyWithCapacity 8) (hd :: tl)).1 := hs_ofList_raw (hd :: tl)
    rw [hr] at p
    exact tlm_insertListIfNewUnit_ne_nil tl _ hd (List.Perm.eq_nil (p.trans (by
      show List.Perm (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets) []
      simp)))

-- `Std.ExtHashMap.unitOfList_eq_empty_iff` (binder 4): ofList [] is ∅ by definition, and inserting into any map leaves an entry, so ofList (hd :: tl) is not equivalent to ∅ (any instances)
theorem w7c3_191 : drop% Std.ExtHashMap.unitOfList_eq_empty_iff 4 :=
  by
  intro α; intros; rename_i l
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases l with
  | nil => rfl
  | cons hd tl =>
    exfalso
    have h' := Quotient.exact (congrArg (fun s : ExtHashMap α Unit => s.inner.inner) h)
    have p := h'.inner.impl
    have hr : (DHashMap.Const.unitOfList (hd :: tl)).inner = (Raw₀.Const.insertListIfNewUnitₘ (Raw₀.emptyWithCapacity 8) (hd :: tl)).1 := hs_ofList_raw (hd :: tl)
    rw [hr] at p
    exact tlm_insertListIfNewUnit_ne_nil tl _ hd (List.Perm.eq_nil (p.trans (by
      show List.Perm (toListModel (Raw₀.emptyWithCapacity 8 : Raw₀ α _).1.buckets) []
      simp)))

-- `Std.DHashMap.Internal.Raw₀.wfImp_consₘ` (binder 4): NS (a ≤ b, hash 0): m = {1}, a = 0: the bucket scan misses 0 (1 ≤ 0 is false), but after consₘ the keys 0, 1 are not ==-distinct (0 ≤ 1)
theorem w7c3_192 : ¬ drop0% Std.DHashMap.Internal.Raw₀.wfImp_consₘ 4 :=
  fun h => by
  first
  | (have := h (W7c3.nsl 1 (b1 (NS.mk 1) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩) ⟨0⟩ () (by decide +kernel)
     exact absurd this.distinct.1 (by decide +kernel))
  | (have := h (W7c3.nsl 1 (b1 (NS.mk 0) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩) ⟨1⟩ () (by decide +kernel)
     exact absurd this.distinct.1 (by decide +kernel))

-- `Std.DHashMap.Internal.Raw₀.wfImp_consₘ` (binder 5): HZ (a/2 == b/2; hash 1 for 5, else 0: EquivBEq, not LawfulHashable), m = {5} in bucket 1 of 8, a = 4: bucket 0 has no 4, but after consₘ the keys 4 and 5 are == in different buckets (not distinct)
theorem w7c3_193 : ¬ drop0% Std.DHashMap.Internal.Raw₀.wfImp_consₘ 5 :=
  fun h => by
  have := h (W7c3.hz8 1 .nil (b1 (HZ.mk 5) 0)) W7c3.hz_w5 ⟨4⟩ 0 (by decide +kernel)
  exact absurd this.distinct.1 (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.wfImp_consₘ` (binder 10): lawful ZH (hash 0), m = {0}, a = 0: consₘ adds a second key 0 to the bucket, so the keys are not distinct
theorem w7c3_194 : ¬ drop0% Std.DHashMap.Internal.Raw₀.wfImp_consₘ 10 :=
  fun h => by
  have := h (W7c3.zl 1 (b1 (W1c5.ZH.mk 0) ())) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩) ⟨0⟩ ()
  exact absurd this.distinct.1 (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.wfImp_consₘ` (binder 7): m with size field 5 and no entries (ZH): consₘ gives size field 6 with one entry
theorem w7c3_195 : ¬ drop0% Std.DHashMap.Internal.Raw₀.wfImp_consₘ 7 :=
  fun h => by
  have := h (W7c3.zl 5 .nil) ⟨0⟩ () (by decide +kernel)
  exact absurd this.size_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.wfImp_eraseₘaux` (binder 9): lawful ZH, m = {1}, a = 0 (not contained): eraseₘaux still lowers the size field to 0 while one entry remains
theorem w7c3_196 : ¬ drop0% Std.DHashMap.Internal.Raw₀.wfImp_eraseₘaux 9 :=
  fun h => by
  have := h (W7c3.zl 1 (b1 (W1c5.ZH.mk 1) ())) ⟨0⟩ (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
  exact absurd this.size_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.wfImp_eraseₘaux` (binder 8): m = {0} with size field 5 (ZH): eraseₘaux 0 gives size field 4 and no entries
theorem w7c3_197 : ¬ drop0% Std.DHashMap.Internal.Raw₀.wfImp_eraseₘaux 8 :=
  fun h => by
  have := h (W7c3.zl 5 (b1 (W1c5.ZH.mk 0) ())) ⟨0⟩ (by decide +kernel)
  exact absurd this.size_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.Const.wfImp_getThenInsertIfNew?` (binder 4): NS (a ≤ b, hash 0), m = {1}, a = 0: the lookup misses 0, the inserted 0 and the stored 1 are not ==-distinct
theorem w7c3_198 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.wfImp_getThenInsertIfNew? 4 :=
  fun h => by
  first
  | (have := h (m := (⟨⟨1, #[b1 (NS.mk 1) (0 : Nat), .nil]⟩, by simp⟩ : Raw₀ NS (fun _ => Nat))) (a := ⟨0⟩) (b := 0) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
     exact absurd this.distinct.1 (by decide +kernel))
  | (have := h (m := (⟨⟨1, #[b1 (NS.mk 0) (0 : Nat), .nil]⟩, by simp⟩ : Raw₀ NS (fun _ => Nat))) (a := ⟨1⟩) (b := 0) (W7c3.h0_wfi (fun _ => rfl) _ _ (by decide) ⟨by decide⟩)
     exact absurd this.distinct.1 (by decide +kernel))

-- `Std.DHashMap.Internal.Raw₀.wfImp_getThenInsertIfNew?` (binder 4): HB (a/2 == b/2) is not LawfulBEq; the WFImp premise holds for the empty map
theorem w7c3_199 : ¬ indep0% Std.DHashMap.Internal.Raw₀.wfImp_getThenInsertIfNew? 4 :=
  fun h => by
  have := h (α := HB) (β := fun _ => Nat) (m := Raw₀.emptyWithCapacity 8) (a := ⟨0⟩) (b := 0) Raw₀.wfImp_emptyWithCapacity
  exact absurd (@eq_of_beq HB _ this ⟨0⟩ ⟨1⟩ rfl) (by decide)

-- `Std.DHashMap.Internal.Raw₀.Const.wfImp_getThenInsertIfNew?` (binder 5): HZ (hash 1 for 5, else 0), m = {5} in bucket 1 of 8, a = 4: the lookup in bucket 0 misses, the inserted 4 is == to the stored 5 (not distinct)
theorem w7c3_200 : ¬ drop0% Std.DHashMap.Internal.Raw₀.Const.wfImp_getThenInsertIfNew? 5 :=
  fun h => by
  have := h (m := W7c3.hz8 1 .nil (b1 (HZ.mk 5) 0)) (a := ⟨4⟩) (b := 0) W7c3.hz_w5
  exact absurd this.distinct.1 (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.wfImp_getThenInsertIfNew?` (binder 8): empty m with size field 5 (ZH): inserting 0 gives size field 6 with one entry
theorem w7c3_201 : ¬ drop0% Std.DHashMap.Internal.Raw₀.wfImp_getThenInsertIfNew? 8 :=
  fun h => by
  have := h (m := (⟨⟨5, #[.nil, .nil]⟩, by decide⟩ : Raw₀ W1c5.ZH (fun _ => Nat))) (a := ⟨0⟩) (b := 0)
  exact absurd this.size_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.wf_union₀` (binder 8): the m₁.WF premise already gives 0 < m₁.buckets.size
theorem w7c3_202 : indep% Std.DHashMap.Internal.Raw₀.wf_union₀ 8 :=
  by
  intros; rename_i h₁ _; exact h₁.size_buckets_pos

-- `Std.DHashMap.Internal.Raw₀.wf_union₀` (binder 9): the m₂.WF premise already gives 0 < m₂.buckets.size
theorem w7c3_203 : indep% Std.DHashMap.Internal.Raw₀.wf_union₀ 9 :=
  by
  intros; rename_i h₂; exact h₂.size_buckets_pos

-- `Std.DHashMap.Internal.Raw₀.wf_union₀` (binder 10): m₁ with size field 5 and no entries (ZH), m₂ = ∅: the union keeps m₁ as the base and stays non-WF
theorem w7c3_204 : ¬ drop0% Std.DHashMap.Internal.Raw₀.wf_union₀ 10 :=
  fun h => by
  have := h (m₁ := (⟨5, #[.nil, .nil]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (m₂ := (⟨0, #[.nil, .nil]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (h₁ := by decide) (h₂ := by decide) (W1c5.zh_wf _ _ rfl (by simp [toListModel]))
  exact absurd (Std.DHashMap.Internal.Raw.WF.out this).size_eq (by decide +kernel)

-- `Std.DHashMap.Internal.Raw₀.wf_union₀` (binder 11): m₁ = ∅, m₂ with size field 5 and no entries (ZH): the union keeps m₂ as the base and stays non-WF
theorem w7c3_205 : ¬ drop0% Std.DHashMap.Internal.Raw₀.wf_union₀ 11 :=
  fun h => by
  have := h (m₁ := (⟨0, #[.nil, .nil]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (m₂ := (⟨5, #[.nil, .nil]⟩ : DHashMap.Raw W1c5.ZH (fun _ => Nat))) (h₁ := by decide) (h₂ := by decide) (W1c5.zh_wf _ _ rfl (by simp [toListModel]))
  exact absurd (Std.DHashMap.Internal.Raw.WF.out this).size_eq (by decide +kernel)
