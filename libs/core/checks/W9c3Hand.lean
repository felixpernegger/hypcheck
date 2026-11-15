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

/-! # Toolkit helpers collected from the merged probe and wave files (A0, the A1 fold-in, the W2-W4 fold-in (2026-11-09) and the W4c6-W7 fold-in (2026-11-10)).
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
open Std.Iterators.Types in
/-- Unlawful loop in StateM Nat: sets the state to 5. -/
def bogusS : Std.IteratorLoop (Std.Iterators.Types.ListIterator Nat) (StateM Nat) (StateM Nat) := ⟨fun _ _ _ _ init _ => do set 5; pure init⟩
open Std.Iterators.Types in
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

/-! ## From `checks/W4c6Hand.lean` -/
namespace W4c6
theorem hz_hs {β : W4c4.HZ0 → Type v} (l : AssocList W4c4.HZ0 β) : IsHashSelf (#[l, .nil] : Array (AssocList W4c4.HZ0 β)) := by
  refine ⟨fun i hi => ⟨fun h p hp => ?_⟩⟩
  rw [mkIdx_toNat' _ _ _ (by simp [Pow2])]
  have : (scrambleHash (hash p.1)).toNat % 2 = 0 := by
    show (scrambleHash 0).toNat % 2 = 0
    rw [scr_small _ (by decide)]; rfl
  rw [show (#[l, AssocList.nil] : Array (AssocList W4c4.HZ0 β)).size = 2 from rfl, this]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => simp at hp
theorem hz_wf {β : W4c4.HZ0 → Type v} (s : Nat) (l : AssocList W4c4.HZ0 β) (hs : s = (toListModel #[l, .nil]).length)
    (hd : Std.Internal.List.DistinctKeys (toListModel #[l, .nil])) :
    (⟨s, #[l, .nil]⟩ : DHashMap.Raw W4c4.HZ0 β).WF :=
  .wf (by simp) (fun {_ _} => ⟨hz_hs l, hs, hd⟩)
end W4c6
namespace W4c6
section
variable {α : Type u} {β : α → Type v} [BEq α]
theorem al_erase_nc (l : AssocList α β) (a : α) (h : l.contains a = false) : l.erase a = l := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.erase, h.1, Bool.cond_false, ih h.2]
theorem al_contains_erase [EquivBEq α] (l : AssocList α β) (a b : α) (hab : (a == b) = false) :
    (l.erase a).contains b = l.contains b := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    cases hka : k == a
    · simp only [AssocList.erase, hka, Bool.cond_false, AssocList.contains, ih]
    · have hkb : (k == b) = false := by
        cases hkb : k == b
        · rfl
        · exact absurd (BEq.trans (BEq.symm hka) hkb) (by simp [hab])
      simp only [AssocList.erase, hka, Bool.cond_true, AssocList.contains, hkb, Bool.false_or]
theorem al_erase_comm [EquivBEq α] (l : AssocList α β) (a b : α) (hab : (a == b) = false) :
    (l.erase a).erase b = (l.erase b).erase a := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    cases hka : k == a <;> cases hkb : k == b
    · simp only [AssocList.erase, hka, hkb, Bool.cond_false, ih]
    · simp only [AssocList.erase, hka, hkb, Bool.cond_false, Bool.cond_true]
    · simp only [AssocList.erase, hka, hkb, Bool.cond_false, Bool.cond_true]
    · exact absurd (BEq.trans (BEq.symm hka) hkb) (by simp [hab])
end
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem mk_congr {n m : Nat} (e : n = m) (h : 0 < n) (h' : 0 < m) (x : UInt64) :
    (mkIdx n h x).1.toNat = (mkIdx m h' x).1.toNat := by subst e; rfl
-- erase as an unconditional bucket update (erasing a missing key leaves the bucket unchanged)
theorem r0_erase_eq (s : Nat) (bs : Array (AssocList α β)) (h : 0 < bs.size) (a : α) :
    Raw₀.erase (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a =
      ⟨⟨if (bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).contains a then s - 1 else s,
        bs.set (mkIdx bs.size h (hash a)).1.toNat
          ((bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).erase a)
          (mkIdx bs.size h (hash a)).2⟩, by simpa using h⟩ := by
  rw [erase_gen]; split
  · rfl
  · rename_i hc
    apply Subtype.ext; simp only [hc, if_false, Bool.false_eq_true]
    rw [al_erase_nc _ _ (by simpa using hc)]; simp
theorem r0_erase_comm [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) (a b : α) (hab : (a == b) = false) :
    (m.erase a).erase b = (m.erase b).erase a := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  rw [r0_erase_eq, r0_erase_eq, r0_erase_eq, r0_erase_eq]
  apply Subtype.ext
  have hba : (b == a) = false := by cases hh : b == a; rfl; exact absurd (BEq.symm hh) (by simp [hab])
  have ea := mk_congr (Array.size_set (xs := bs) (i := (mkIdx bs.size h (hash b)).1.toNat) (v := (bs[(mkIdx bs.size h (hash b)).1.toNat]'(mkIdx bs.size h (hash b)).2).erase b) (mkIdx bs.size h (hash b)).2) (by simpa using h) h (hash a)
  have eb := mk_congr (Array.size_set (xs := bs) (i := (mkIdx bs.size h (hash a)).1.toNat) (v := (bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).erase a) (mkIdx bs.size h (hash a)).2) (by simpa using h) h (hash b)
  simp only [ea, eb, Array.getElem_set]
  by_cases hij : (mkIdx bs.size h (hash a)).val.toNat = (mkIdx bs.size h (hash b)).val.toNat
  · have hji := hij.symm
    simp only [hij, ite_true, al_contains_erase _ _ _ hab, al_contains_erase _ _ _ hba, al_erase_comm _ _ _ hab, Array.set_set]
    congr 1
    split <;> split <;> omega
  · have hji : ¬ (mkIdx bs.size h (hash b)).val.toNat = (mkIdx bs.size h (hash a)).val.toNat := fun e => hij e.symm
    simp only [hij, hji, ite_false]
    congr 1
    · split <;> split <;> omega
    · exact Array.set_comm _ _ hij
theorem eraseList_foldl (m : Raw₀ α β) (l : List α) : Raw₀.eraseListₘ m l = l.foldl Raw₀.erase m := by
  induction l generalizing m with
  | nil => rfl
  | cons hd tl ih => exact ih _
-- erasing a list of pairwise unequal keys from any (not necessarily WF) map does not depend on the order
theorem r0_eraseList_perm [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) {l₁ l₂ : List α} (p : l₁.Perm l₂)
    (hd : l₁.Pairwise (fun a b => (a == b) = false)) : Raw₀.eraseListₘ m l₁ = Raw₀.eraseListₘ m l₂ := by
  rw [eraseList_foldl, eraseList_foldl]
  apply p.foldl_eq'
  apply List.Pairwise.forall_of_forall_of_flip (R := fun x y => ∀ z : Raw₀ α β, (z.erase x).erase y = (z.erase y).erase x)
  · intro x _ z; rfl
  · exact hd.imp (fun h z => r0_erase_comm z _ _ h)
  · exact hd.imp (fun h z => (r0_erase_comm z _ _ h).symm)
-- m₁ \ m₂ only depends on m₂ up to Equiv when m₂, m₃ are WF; m₁ may be any map
theorem r0_diff_right [EquivBEq α] [LawfulHashable α] (m₁ m₂ m₃ : Raw₀ α β) (h₂ : Raw.WFImp m₂.1) (h₃ : Raw.WFImp m₃.1)
    (e : (toListModel m₂.1.buckets).Perm (toListModel m₃.1.buckets)) : m₁.diff m₂ = m₁.diff m₃ := by
  have hs : m₂.1.size = m₃.1.size := by rw [h₂.size_eq, h₃.size_eq]; exact e.length_eq
  have hc : ∀ k, m₂.contains k = m₃.contains k := fun k => by
    rw [Raw₀.contains_eq_containsKey h₂, Raw₀.contains_eq_containsKey h₃]; exact Std.Internal.List.containsKey_of_perm e
  unfold Raw₀.diff
  rw [hs]
  split
  · simp only [hc]
  · rw [Raw₀.eraseMany_eq_eraseListₘ_toListModel, Raw₀.eraseMany_eq_eraseListₘ_toListModel]
    have hd := h₂.distinct.distinct
    simp only [Std.Internal.List.keys_eq_map] at hd
    exact r0_eraseList_perm _ (e.map _) hd
theorem dr_diff_right [EquivBEq α] [LawfulHashable α] (m₁ m₂ m₃ : DHashMap.Raw α β) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (e : m₂.Equiv m₃) : (m₁ \ m₂).Equiv (m₁ \ m₃) := by
  simp only [SDiff.sdiff, DHashMap.Raw.diff, h₂.size_buckets_pos, h₃.size_buckets_pos, dite_true]
  split
  · rw [r0_diff_right _ ⟨m₂, h₂.size_buckets_pos⟩ ⟨m₃, h₃.size_buckets_pos⟩ (Std.DHashMap.Internal.Raw.WF.out h₂) (Std.DHashMap.Internal.Raw.WF.out h₃) e.1]
    try exact ⟨List.Perm.refl _⟩
  · exact e
end
end W4c6
namespace W4c6
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
open Std.Internal.List in
theorem al_getEntry?_beq (l : AssocList α β) (a : α) (s : (a : α) × β a) (h : l.getEntry? a = some s) : (s.1 == a) = true := by
  induction l with
  | nil => simp [AssocList.getEntry?] at h
  | cons k v t ih =>
    simp only [AssocList.getEntry?] at h
    split at h
    · cases h; assumption
    · exact ih h
theorem al_getEntry?_congr [EquivBEq α] (l : AssocList α β) {a b : α} (hab : (a == b) = true) : l.getEntry? a = l.getEntry? b := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    simp only [AssocList.getEntry?]
    have : (k == a) = (k == b) := by
      cases h1 : k == a <;> cases h2 : k == b
      · rfl
      · exact absurd (BEq.trans h2 (BEq.symm hab)) (by simp [h1])
      · exact absurd (BEq.trans h1 hab) (by simp [h2])
      · rfl
    rw [this, ih]
-- a key found in any (not necessarily WF) map is == the query
theorem r0_getEntry?_beq (m : Raw₀ α β) (a : α) (s : (a : α) × β a) (h : m.getEntry? a = some s) : (s.1 == a) = true := by
  obtain ⟨⟨_, bs⟩, hb⟩ := m
  exact al_getEntry?_beq _ _ _ h
-- lookups in any map respect == (same bucket by LawfulHashable, same scan by EquivBEq)
theorem r0_getEntry?_congr [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) {a b : α} (hab : (a == b) = true) :
    m.getEntry? a = m.getEntry? b := by
  obtain ⟨⟨_, bs⟩, hb⟩ := m
  unfold Raw₀.getEntry?; dsimp only
  simp only [hash_eq hab, al_getEntry?_congr _ hab]
-- interSmaller's fold over a list of distinct-key entries, with any (not necessarily WF) searched map m₁
open Std.Internal.List in
theorem is_fold [EquivBEq α] [LawfulHashable α] (m₁ : Raw₀ α β) (L : List ((a : α) × β a)) (hL : DistinctKeys L)
    (sofar : Raw₀ α β) (hs : Raw.WFImp sofar.1) :
    Raw.WFImp (L.foldl (fun a b => Raw₀.interSmallerFn m₁ a b.1) sofar).1 ∧
    ∀ k, getEntry? k (toListModel (L.foldl (fun a b => Raw₀.interSmallerFn m₁ a b.1) sofar).1.buckets) =
      (if containsKey k L then m₁.getEntry? k else none).or (getEntry? k (toListModel sofar.1.buckets)) := by
  induction L generalizing sofar with
  | nil => exact ⟨hs, fun k => by simp⟩
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    rw [distinctKeys_cons_iff] at hL
    have step : Raw.WFImp (Raw₀.interSmallerFn m₁ sofar a).1 ∧ ∀ k, getEntry? k (toListModel (Raw₀.interSmallerFn m₁ sofar a).1.buckets) =
        (if (a == k) = true then m₁.getEntry? k else none).or (getEntry? k (toListModel sofar.1.buckets)) := by
      unfold Raw₀.interSmallerFn
      cases hg : m₁.getEntry? a with
      | none =>
        simp only [hg]
        refine ⟨hs, fun k => ?_⟩
        by_cases hak : (a == k) = true
        · rw [if_pos hak, ← r0_getEntry?_congr m₁ hak, hg]; rfl
        · rw [if_neg hak]; rfl
      | some s =>
        have hsa := r0_getEntry?_beq m₁ a s hg
        simp only [hg]
        refine ⟨Raw₀.wfImp_insert hs, fun k => ?_⟩
        rw [getEntry?_of_perm (Raw₀.wfImp_insert hs).distinct (Raw₀.toListModel_insert hs), getEntry?_insertEntry]
        by_cases hak : (a == k) = true
        · have : (s.fst == k) = true := BEq.trans hsa hak
          rw [if_pos this, if_pos hak, ← r0_getEntry?_congr m₁ hak, hg]; rfl
        · have : (s.fst == k) = false := by
            cases h' : s.fst == k
            · rfl
            · exact absurd (BEq.trans (BEq.symm hsa) h') hak
          rw [if_neg (by simp [this]), if_neg hak]; rfl
    obtain ⟨w, f⟩ := ih hL.1 _ step.1
    refine ⟨w, fun k => ?_⟩
    simp only [List.foldl_cons]
    rw [f, step.2, containsKey_cons]
    by_cases hak : (a == k) = true
    · have : containsKey k L = false := by rw [← containsKey_congr hak]; exact hL.2
      simp [hak, this]
    · simp only [Bool.not_eq_true] at hak
      simp [hak]
-- m₁ ∩ m₂ only depends on m₂ up to Equiv when m₂, m₃ are WF; m₁ may be any map
theorem r0_inter_right [EquivBEq α] [LawfulHashable α] (m₁ m₂ m₃ : Raw₀ α β) (h₂ : Raw.WFImp m₂.1) (h₃ : Raw.WFImp m₃.1)
    (e : (toListModel m₂.1.buckets).Perm (toListModel m₃.1.buckets)) :
    (toListModel (m₁.inter m₂).1.buckets).Perm (toListModel (m₁.inter m₃).1.buckets) := by
  have hs : m₂.1.size = m₃.1.size := by rw [h₂.size_eq, h₃.size_eq]; exact e.length_eq
  have hc : ∀ k, m₂.contains k = m₃.contains k := fun k => by
    rw [Raw₀.contains_eq_containsKey h₂, Raw₀.contains_eq_containsKey h₃]; exact Std.Internal.List.containsKey_of_perm e
  unfold Raw₀.inter
  rw [hs]
  split
  · simp only [hc]; exact List.Perm.refl _
  · simp only [Raw₀.interSmaller, Raw.fold_eq_foldl_toListModel]
    obtain ⟨w2, f2⟩ := is_fold m₁ _ h₂.distinct _ (Raw₀.wfImp_emptyWithCapacity (c := 8))
    obtain ⟨w3, f3⟩ := is_fold m₁ _ h₃.distinct _ (Raw₀.wfImp_emptyWithCapacity (c := 8))
    apply Std.Internal.List.getEntry?_ext w2.distinct w3.distinct
    intro k; rw [f2, f3, Std.Internal.List.containsKey_of_perm e]
theorem dr_inter_right [EquivBEq α] [LawfulHashable α] (m₁ m₂ m₃ : DHashMap.Raw α β) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (e : m₂.Equiv m₃) : (m₁ ∩ m₂).Equiv (m₁ ∩ m₃) := by
  simp only [Inter.inter, DHashMap.Raw.inter, h₂.size_buckets_pos, h₃.size_buckets_pos, dite_true]
  split
  · exact ⟨r0_inter_right _ ⟨m₂, h₂.size_buckets_pos⟩ ⟨m₃, h₃.size_buckets_pos⟩ (Std.DHashMap.Internal.Raw.WF.out h₂) (Std.DHashMap.Internal.Raw.WF.out h₃) e.1⟩
  · exact e
end
end W4c6

/-! ## From `checks/W5c0Hand.lean` -/
namespace W5c0
end W5c0
/-- Evaluator for literal hash maps under set operations (unfolds the ∪/∩/\\ notation first). -/
macro "w5e" : tactic => `(tactic| first
  | (decide +kernel; done)
  | (hm_eval; done) | (hm_eval2; done)
  | (simp only [Union.union, Inter.inter, SDiff.sdiff, HashSet.union, HashSet.inter, HashMap.union, HashMap.inter,
      HashSet.Raw.union, HashSet.Raw.inter, HashMap.Raw.union, HashMap.Raw.inter, DHashMap.union, DHashMap.inter, Raw₀.union]; hm_eval2; done)
  | (simp only [Union.union, Inter.inter, SDiff.sdiff, HashSet.union, HashSet.inter, HashMap.union, HashMap.inter,
      HashSet.Raw.union, HashSet.Raw.inter, HashMap.Raw.union, HashMap.Raw.inter, DHashMap.union, DHashMap.inter, Raw₀.union]; hm_eval; done)
  | (simp only [W3c1.hsr_un, W3c1.hsr_in, W3c1.hmr_un, W3c1.hmr_in, HashSet.Raw.union, HashSet.Raw.inter, HashMap.Raw.union, HashMap.Raw.inter]; hm_eval2; done)
  | (simp only [W3c1.hsr_un, W3c1.hsr_in, W3c1.hmr_un, W3c1.hmr_in, HashSet.Raw.union, HashSet.Raw.inter, HashMap.Raw.union, HashMap.Raw.inter]; hm_eval; done)
  | (simp only [W3c1.hsr_un, W3c1.hsr_in, HashSet.Raw.union, HashSet.Raw.inter, HashMap.Raw.union, HashMap.Raw.inter,
      DHashMap.Raw.union, DHashMap.Raw.inter, hsr_empty]; hm_eval; done)
  | (hm_eval3; done))

/-! ## From `checks/W5c1Hand.lean` -/
set_option linter.unusedSimpArgs false
namespace W5c1
variable {α : Type u} {β : α → Type v}
-- Raw₀ insert/insertIfNew/erase change the size field exactly as contains predicts (no laws needed)
theorem r0_si [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insert a b).1.size = if m.contains a then m.1.size else m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.insert Raw₀.contains; dsimp only
  split <;> simp [Raw₀.size_expandIfNecessary]
theorem r0_sin [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insertIfNew a b).1.size = if m.contains a then m.1.size else m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.insertIfNew Raw₀.contains; dsimp only
  split <;> simp [Raw₀.size_expandIfNecessary]
theorem r0_se [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    (m.erase a).1.size = if m.contains a then m.1.size - 1 else m.1.size := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  rw [erase_gen, contains_gen]
  split <;> simp_all
theorem r0_sle [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : (m.erase a).1.size ≤ m.1.size := by
  rw [r0_se]; split <;> omega
theorem r0_lse [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : m.1.size ≤ (m.erase a).1.size + 1 := by
  rw [r0_se]; split <;> omega
theorem r0_sil [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : (m.insert a b).1.size ≤ m.1.size + 1 := by
  rw [r0_si]; split <;> omega
theorem r0_sinl [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insertIfNew a b).1.size ≤ m.1.size + 1 := by
  rw [r0_sin]; split <;> omega
theorem r0_lsi [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : m.1.size ≤ (m.insert a b).1.size := by
  rw [r0_si]; split <;> omega
theorem r0_lsin [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    m.1.size ≤ (m.insertIfNew a b).1.size := by
  rw [r0_sin]; split <;> omega
theorem r0_ie [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    (m.erase a).1.isEmpty = (m.1.isEmpty || (m.1.size == 1 && m.contains a)) := by
  simp only [DHashMap.Raw.isEmpty, r0_se]
  generalize m.contains a = c; generalize m.1.size = s
  cases c <;> rcases s with _ | _ | s <;> simp
end W5c1
namespace W5c1
variable {α : Type u} {β : α → Type v}
-- dependent analogue of size_insertList_eq: no key of l finds an earlier one, so each insert adds one
theorem r0_sild [BEq α] [Hashable α] (l : List ((a : α) × β a))
    (hl : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    ∀ (m : Raw₀ α β), (∀ p ∈ toListModel m.1.buckets, ∀ y ∈ l, (p.1 == y.1) = false) →
      (Raw₀.insertListₘ m l).1.size = m.1.size + l.length := by
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
    show (Raw₀.insertListₘ (m.insert hd.1 hd.2) tl).1.size = _
    simp only [List.length_cons]; omega
theorem dr_ofList_raw [BEq α] [Hashable α] (l : List ((a : α) × β a)) :
    (DHashMap.Raw.ofList l) = (Raw₀.insertListₘ (Raw₀.emptyWithCapacity 8) l).1 := by
  show DHashMap.Raw.insertMany ∅ l = _
  unfold DHashMap.Raw.insertMany
  rw [dif_pos (show 0 < (∅ : DHashMap.Raw α β).buckets.size from (Raw₀.emptyWithCapacity 8).2)]
  rw [Raw₀.insertMany_eq_insertListₘ]; rfl
theorem dm_ofList_raw [BEq α] [Hashable α] (l : List ((a : α) × β a)) :
    (DHashMap.ofList l).1 = (Raw₀.insertListₘ (Raw₀.emptyWithCapacity 8) l).1 := by
  show (Raw₀.insertMany _ l).1.1 = _
  rw [Raw₀.insertMany_eq_insertListₘ]; rfl
end W5c1
namespace W5c1
variable {α : Type u} {β : α → Type v}
-- Equiv with ∅ means an empty toListModel (no laws needed)
theorem ee_dr [BEq α] [Hashable α] (m : DHashMap.Raw α β) :
    m.Equiv ∅ ↔ (toListModel m.buckets).length = 0 := by
  have e : toListModel (∅ : DHashMap.Raw α β).buckets = [] := Raw₀.toListModel_buckets_emptyWithCapacity
  rw [List.length_eq_zero_iff]
  constructor
  · intro h; exact List.perm_nil.mp (e ▸ h.1)
  · intro h; exact ⟨by rw [h, e]⟩
theorem ee_dh [BEq α] [Hashable α] (m : DHashMap α β) : m.Equiv ∅ ↔ (toListModel m.1.buckets).length = 0 :=
  ⟨fun h => (ee_dr _).1 h.1, fun h => ⟨(ee_dr _).2 h⟩⟩
theorem ee_hmr {γ : Type v} [BEq α] [Hashable α] (m : HashMap.Raw α γ) : m.Equiv ∅ ↔ (toListModel m.inner.buckets).length = 0 :=
  ⟨fun h => (ee_dr _).1 h.1, fun h => ⟨(ee_dr _).2 h⟩⟩
theorem ee_hm {γ : Type v} [BEq α] [Hashable α] (m : HashMap α γ) : m.Equiv ∅ ↔ (toListModel m.inner.1.buckets).length = 0 :=
  ⟨fun h => (ee_dh _).1 h.1, fun h => ⟨(ee_dh _).2 h⟩⟩
theorem ee_hsr [BEq α] [Hashable α] (m : HashSet.Raw α) : m.Equiv ∅ ↔ (toListModel m.inner.inner.buckets).length = 0 :=
  ⟨fun h => (ee_hmr _).1 h.1, fun h => ⟨(ee_hmr _).2 h⟩⟩
theorem ee_hs [BEq α] [Hashable α] (m : HashSet α) : m.Equiv ∅ ↔ (toListModel m.inner.inner.1.buckets).length = 0 :=
  ⟨fun h => (ee_hm _).1 h.1, fun h => ⟨(ee_hm _).2 h⟩⟩
end W5c1

/-! ## From `checks/W5c2Hand.lean` -/
namespace W5c2
open Std Std.DHashMap.Internal Probe2
section
variable {α : Type u} {β : α → Type v}
-- filterMap keeps a subset of each bucket (no laws, no WF)
theorem al_fm_c [BEq α] {γ : α → Type w} (f : (a : α) → β a → Option (γ a)) (a : α) (l : AssocList α β)
    (h : (l.filterMap f).contains a = true) : l.contains a = true := by
  simp only [AssocList.contains_eq, ck_any, (AssocList.toList_filterMap (f := f) (l := l)).any_eq] at h ⊢
  simp only [List.any_eq_true, List.mem_filterMap] at h ⊢
  obtain ⟨x, ⟨y, hy, hxy⟩, hx⟩ := h
  cases hf : f y.1 y.2 <;> simp only [hf, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hxy
  subst hxy; exact ⟨y, hy, hx⟩
theorem r0_fm_c [BEq α] [Hashable α] {γ : α → Type w} (f : (a : α) → β a → Option (γ a)) (m : Raw₀ α β) (k : α)
    (h : (Raw₀.filterMap f m).contains k = true) : m.contains k = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have e : Raw₀.filterMap f ⟨⟨s, bs⟩, hb⟩ =
      ⟨⟨computeSize (bs.map (AssocList.filterMap f)), bs.map (AssocList.filterMap f)⟩, by simpa using hb⟩ := rfl
  rw [e, contains_gen, map_idx _ _ _ hb] at h
  rw [contains_gen]; exact al_fm_c _ _ _ h
theorem dr_fm_c [BEq α] [Hashable α] {γ : α → Type w} (f : (a : α) → β a → Option (γ a)) (m : DHashMap.Raw α β) (k : α)
    (h : (m.filterMap f).contains k = true) : m.contains k = true := by
  unfold DHashMap.Raw.filterMap at h; split at h
  · rename_i hb
    obtain ⟨hb', h⟩ := W4c5.dr_pos h
    have := r0_fm_c f ⟨m, hb⟩ k h
    unfold DHashMap.Raw.contains; rw [dite_eq_left hb]; exact this
  · simp at h
-- getKey? congruence scans one bucket with an EquivBEq ==, so no WF is needed
theorem al_gk_congr [BEq α] [EquivBEq α] (l : AssocList α β) {a b : α} (hab : (a == b) = true) :
    l.getKey? a = l.getKey? b := by
  induction l with
  | nil => rfl
  | cons k v t ih => simp only [AssocList.getKey?, BEq.congr_right hab, ih]
theorem r0_gk_congr [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) {a b : α}
    (hab : (a == b) = true) : m.getKey? a = m.getKey? b := by
  obtain ⟨⟨s, bs⟩, hm⟩ := m
  simp only [Raw₀.getKey?, hash_eq hab]
  exact al_gk_congr _ hab
theorem dr_gk_congr [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : DHashMap.Raw α β} {a b : α}
    (hab : (a == b) = true) : m.getKey? a = m.getKey? b := by
  simp only [DHashMap.Raw.getKey?]; split
  · exact r0_gk_congr _ hab
  · rfl
end
section
variable {α : Type u} {γ : Type v}
theorem al_cg_congr [BEq α] [EquivBEq α] (l : AssocList α (fun _ => γ)) {a b : α} (hab : (a == b) = true) :
    l.get? a = l.get? b := by
  induction l with
  | nil => rfl
  | cons k v t ih => simp only [AssocList.get?, BEq.congr_right hab, ih]
theorem r0c_g_congr [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => γ)) {a b : α}
    (hab : (a == b) = true) : Raw₀.Const.get? m a = Raw₀.Const.get? m b := by
  obtain ⟨⟨s, bs⟩, hm⟩ := m
  simp only [Raw₀.Const.get?, hash_eq hab]
  exact al_cg_congr _ hab
theorem drc_g_congr [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : DHashMap.Raw α (fun _ => γ)} {a b : α}
    (hab : (a == b) = true) : DHashMap.Raw.Const.get? m a = DHashMap.Raw.Const.get? m b := by
  simp only [DHashMap.Raw.Const.get?]; split
  · exact r0c_g_congr _ hab
  · rfl
end
end W5c2
namespace W5c2
open Std Std.DHashMap.Internal Probe2
variable {α : Type u} {β : α → Type v}
theorem dr_gk_nc [BEq α] [Hashable α] (m : DHashMap.Raw α β) (a : α) (h : m.contains a = false) :
    m.getKey? a = none := by
  unfold DHashMap.Raw.getKey?; split
  · exact W3c4.r0_getKey?_nc _ _ (W4c5.dr_neg h ‹_›)
  · rfl
end W5c2
namespace W5c2
open Std Std.DHashMap.Internal Probe2
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
-- inserting into an empty map gives size field 1 (no laws)
theorem e_ins (c : Nat) (a : α) (b : β a) : ((Raw₀.emptyWithCapacity c : Raw₀ α β).insert a b).1.size = 1 := by
  have h0 : (Raw₀.emptyWithCapacity c : Raw₀ α β).contains a = false := Raw₀.contains_emptyWithCapacity
  revert h0
  unfold Raw₀.insert Raw₀.contains; dsimp only
  split
  · intro h; simp_all
  · intro _; rw [expand_size]; simp [Raw₀.emptyWithCapacity]
theorem e_insIfNew (c : Nat) (a : α) (b : β a) : ((Raw₀.emptyWithCapacity c : Raw₀ α β).insertIfNew a b).1.size = 1 := by
  have h0 : (Raw₀.emptyWithCapacity c : Raw₀ α β).contains a = false := Raw₀.contains_emptyWithCapacity
  revert h0
  unfold Raw₀.insertIfNew Raw₀.contains; dsimp only
  split
  · intro h; simp_all
  · intro _; simp [Raw₀.size_expandIfNecessary, Raw₀.emptyWithCapacity]
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
end
section
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
theorem ilc_ge (l : List (α × β)) : ∀ m : Raw₀ α (fun _ => β), m.1.size ≤ (Raw₀.Const.insertListₘ m l).1.size := by
  induction l with
  | nil => intro m; exact Nat.le_refl _
  | cons hd tl ih => intro m; exact Nat.le_trans (W2c0.ins_size_ge m hd.1 hd.2) (ih _)
theorem r0c_ofl (c : Nat) (l : List (α × β)) :
    (Raw₀.Const.insertMany (Raw₀.emptyWithCapacity c : Raw₀ α (fun _ => β)) l).1.1.isEmpty = l.isEmpty := by
  rw [Raw₀.Const.insertMany_eq_insertListₘ]
  cases l with
  | nil => simp [Raw₀.Const.insertListₘ, DHashMap.Raw.isEmpty, Raw₀.emptyWithCapacity]
  | cons hd tl =>
    have := ilc_ge tl ((Raw₀.emptyWithCapacity c : Raw₀ α (fun _ => β)).insert hd.1 hd.2)
    rw [e_ins] at this
    simp only [Raw₀.Const.insertListₘ, DHashMap.Raw.isEmpty, List.isEmpty_cons, beq_eq_false_iff_ne]; omega
theorem r0u_ofl (c : Nat) (l : List α) :
    (Raw₀.Const.insertManyIfNewUnit (Raw₀.emptyWithCapacity c : Raw₀ α (fun _ => Unit)) l).1.1.isEmpty = l.isEmpty := by
  rw [Raw₀.Const.insertManyIfNewUnit_eq_insertListIfNewUnitₘ]
  cases l with
  | nil => simp [Raw₀.Const.insertListIfNewUnitₘ, DHashMap.Raw.isEmpty, Raw₀.emptyWithCapacity]
  | cons hd tl =>
    have := Probe1.size_insertListIfNewUnit_ge tl ((Raw₀.emptyWithCapacity c : Raw₀ α (fun _ => Unit)).insertIfNew hd ())
    rw [e_insIfNew] at this
    simp only [Raw₀.Const.insertListIfNewUnitₘ, DHashMap.Raw.isEmpty, List.isEmpty_cons, beq_eq_false_iff_ne]; omega
end
section
variable {α : Type u} [BEq α] [Hashable α]
theorem dh_ofl {β : α → Type v} (l : List ((a : α) × β a)) : (DHashMap.ofList l).isEmpty = l.isEmpty := r0_ofl _ l
theorem dhc_ofl {β : Type v} (l : List (α × β)) : (DHashMap.Const.ofList l).isEmpty = l.isEmpty := r0c_ofl _ l
theorem dhu_ofl (l : List α) : (DHashMap.Const.unitOfList l).isEmpty = l.isEmpty := r0u_ofl _ l
theorem dr_ofl {β : α → Type v} (l : List ((a : α) × β a)) : (DHashMap.Raw.ofList l).isEmpty = l.isEmpty := by
  simp only [DHashMap.Raw.ofList, DHashMap.Raw.insertMany]
  split
  · exact r0_ofl 8 l
  · rename_i h; exact (h (Raw₀.emptyWithCapacity 8).2).elim
theorem drc_ofl {β : Type v} (l : List (α × β)) : (DHashMap.Raw.Const.ofList l).isEmpty = l.isEmpty := by
  simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.Const.insertMany]
  split
  · exact r0c_ofl 8 l
  · rename_i h; exact (h (Raw₀.emptyWithCapacity 8).2).elim
theorem dru_ofl (l : List α) : (DHashMap.Raw.Const.unitOfList l).isEmpty = l.isEmpty := by
  simp only [DHashMap.Raw.Const.unitOfList, DHashMap.Raw.Const.insertManyIfNewUnit]
  split
  · exact r0u_ofl 8 l
  · rename_i h; exact (h (Raw₀.emptyWithCapacity 8).2).elim
end
end W5c2
open W5c2

/-! ## From `checks/W5c3Hand.lean` -/
namespace W5c3
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
-- bucket level: every lookup variant agrees with get? on the same bucket (no laws)
theorem a_cbq [BEq α] [Inhabited γ] (l : AssocList α (fun _ => γ)) (a : α) : l.get! a = (l.get? a).get! := by
  induction l with
  | nil => rfl
  | cons k v t ih => cases hk : (k == a) <;> simp_all [AssocList.get!, AssocList.get?]
theorem a_cdq [BEq α] (l : AssocList α (fun _ => γ)) (a : α) (fb : γ) : l.getD a fb = (l.get? a).getD fb := by
  induction l with
  | nil => rfl
  | cons k v t ih => cases hk : (k == a) <;> simp_all [AssocList.getD, AssocList.get?]
theorem a_cqg [BEq α] (l : AssocList α (fun _ => γ)) (a : α) (h) : l.get? a = some (l.get a h) := by
  induction l with
  | nil => cases h
  | cons k v t ih =>
    cases hk : (k == a)
    · have h' : t.contains a = true := by simpa only [AssocList.contains, hk, Bool.false_or] using h
      simp only [AssocList.get, AssocList.get?, hk, Bool.cond_false, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]; exact ih h'
    · simp [AssocList.get, AssocList.get?, hk]
theorem a_kbq [BEq α] [Inhabited α] (l : AssocList α β) (a : α) : l.getKey! a = (l.getKey? a).get! := by
  induction l with
  | nil => rfl
  | cons k v t ih => cases hk : (k == a) <;> simp_all [AssocList.getKey!, AssocList.getKey?]
theorem a_kdq [BEq α] (l : AssocList α β) (a : α) (fb : α) : l.getKeyD a fb = (l.getKey? a).getD fb := by
  induction l with
  | nil => rfl
  | cons k v t ih => cases hk : (k == a) <;> simp_all [AssocList.getKeyD, AssocList.getKey?]
theorem a_kqg [BEq α] (l : AssocList α β) (a : α) (h) : l.getKey? a = some (l.getKey a h) := by
  induction l with
  | nil => cases h
  | cons k v t ih =>
    cases hk : (k == a)
    · have h' : t.contains a = true := by simpa only [AssocList.contains, hk, Bool.false_or] using h
      simp only [AssocList.getKey, AssocList.getKey?, hk, Bool.cond_false, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]; exact ih h'
    · simp [AssocList.getKey, AssocList.getKey?, hk]
theorem a_gbq [BEq α] [LawfulBEq α] (l : AssocList α β) (a : α) [Inhabited (β a)] : l.getCast! a = (l.getCast? a).get! := by
  induction l with
  | nil => rfl
  | cons k v t ih => cases hk : (k == a) <;> simp_all [AssocList.getCast!, AssocList.getCast?]
theorem a_gdq [BEq α] [LawfulBEq α] (l : AssocList α β) (a : α) (fb : β a) : l.getCastD a fb = (l.getCast? a).getD fb := by
  induction l with
  | nil => rfl
  | cons k v t ih => cases hk : (k == a) <;> simp_all [AssocList.getCastD, AssocList.getCast?]
theorem a_gqg [BEq α] [LawfulBEq α] (l : AssocList α β) (a : α) (h) : l.getCast? a = some (l.getCast a h) := by
  induction l with
  | nil => cases h
  | cons k v t ih =>
    cases hk : (k == a)
    · have h' : t.contains a = true := by simpa only [AssocList.contains, hk, Bool.false_or] using h
      simp only [AssocList.getCast, AssocList.getCast?, hk, Bool.cond_false, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]; exact ih h'
    · simp [AssocList.getCast, AssocList.getCast?, hk]
theorem a_cgb [BEq α] [Inhabited γ] (l : AssocList α (fun _ => γ)) (a : α) (h) : l.get a h = l.get! a := by
  rw [a_cbq, a_cqg _ _ h]; rfl
theorem a_cgd [BEq α] (l : AssocList α (fun _ => γ)) (a : α) (fb : γ) (h) : l.get a h = l.getD a fb := by
  rw [a_cdq _ _ fb, a_cqg _ _ h]; rfl
theorem a_kgb [BEq α] [Inhabited α] (l : AssocList α β) (a : α) (h) : l.getKey a h = l.getKey! a := by
  rw [a_kbq, a_kqg _ _ h]; rfl
theorem a_kgd [BEq α] (l : AssocList α β) (a : α) (fb : α) (h) : l.getKey a h = l.getKeyD a fb := by
  rw [a_kdq _ _ fb, a_kqg _ _ h]; rfl
theorem a_ggb [BEq α] [LawfulBEq α] (l : AssocList α β) (a : α) [Inhabited (β a)] (h) : l.getCast a h = l.getCast! a := by
  rw [a_gbq, a_gqg _ _ h]; rfl
theorem a_ggd [BEq α] [LawfulBEq α] (l : AssocList α β) (a : α) (fb : β a) (h) : l.getCast a h = l.getCastD a fb := by
  rw [a_gdq _ _ fb, a_gqg _ _ h]; rfl
theorem zr0c_bq [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (a : α) [Inhabited γ] :
    Raw₀.Const.get! m a = (Raw₀.Const.get? m a).get! := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.Const.get? Raw₀.Const.get!; simp only [Array.ugetElem_eq_getElem]; exact a_cbq _ _
theorem zdrc_bq [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => γ)) (a : α) [Inhabited γ] :
    DHashMap.Raw.Const.get! m a = (DHashMap.Raw.Const.get? m a).get! := by
  unfold DHashMap.Raw.Const.get! DHashMap.Raw.Const.get?; split
  · exact zr0c_bq _ _
  · rfl
theorem zr0c_dq [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (a : α)  (fb : γ) :
    Raw₀.Const.getD m a fb = (Raw₀.Const.get? m a).getD fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.Const.get? Raw₀.Const.getD; simp only [Array.ugetElem_eq_getElem]; exact a_cdq _ _ _
theorem zdrc_dq [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => γ)) (a : α)  (fb : γ) :
    DHashMap.Raw.Const.getD m a fb = (DHashMap.Raw.Const.get? m a).getD fb := by
  unfold DHashMap.Raw.Const.getD DHashMap.Raw.Const.get?; split
  · exact zr0c_dq _ _ _
  · rfl
theorem zr0c_gb [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (a : α) [Inhabited γ] (h) :
    Raw₀.Const.get m a h = Raw₀.Const.get! m a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.Const.get Raw₀.Const.get!; simp only [Array.ugetElem_eq_getElem]; exact a_cgb _ _ _
theorem zdrc_gb [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => γ)) (a : α) [Inhabited γ] (h : a ∈ m) :
    DHashMap.Raw.Const.get m a h = DHashMap.Raw.Const.get! m a := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.Const.get DHashMap.Raw.Const.get!; rw [dite_eq_left hb]; exact zr0c_gb _ _ _
theorem zr0c_gd [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (a : α)  (fb : γ) (h) :
    Raw₀.Const.get m a h = Raw₀.Const.getD m a fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.Const.get Raw₀.Const.getD; simp only [Array.ugetElem_eq_getElem]; exact a_cgd _ _ _ _
theorem zdrc_gd [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => γ)) (a : α)  (fb : γ) (h : a ∈ m) :
    DHashMap.Raw.Const.get m a h = DHashMap.Raw.Const.getD m a fb := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.Const.get DHashMap.Raw.Const.getD; rw [dite_eq_left hb]; exact zr0c_gd _ _ _ _
theorem zr0c_qg [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (a : α)  (h) :
    Raw₀.Const.get? m a = some (Raw₀.Const.get m a h) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.Const.get Raw₀.Const.get?; simp only [Array.ugetElem_eq_getElem]; exact a_cqg _ _ _
theorem zdrc_qg [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => γ)) (a : α)  (h : a ∈ m) :
    DHashMap.Raw.Const.get? m a = some (DHashMap.Raw.Const.get m a h) := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.Const.get DHashMap.Raw.Const.get?; rw [dite_eq_left hb]; exact zr0c_qg _ _ _
theorem zr0g_bq [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α) [Inhabited (β a)] :
    Raw₀.get! m a = (Raw₀.get? m a).get! := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.get? Raw₀.get!; simp only [Array.ugetElem_eq_getElem]; exact a_gbq _ _
theorem zdrg_bq [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (a : α) [Inhabited (β a)] :
    DHashMap.Raw.get! m a = (DHashMap.Raw.get? m a).get! := by
  unfold DHashMap.Raw.get! DHashMap.Raw.get?; split
  · exact zr0g_bq _ _
  · rfl
theorem zr0g_dq [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)  (fb : β a) :
    Raw₀.getD m a fb = (Raw₀.get? m a).getD fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.get? Raw₀.getD; simp only [Array.ugetElem_eq_getElem]; exact a_gdq _ _ _
theorem zdrg_dq [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (a : α)  (fb : β a) :
    DHashMap.Raw.getD m a fb = (DHashMap.Raw.get? m a).getD fb := by
  unfold DHashMap.Raw.getD DHashMap.Raw.get?; split
  · exact zr0g_dq _ _ _
  · rfl
theorem zr0g_gb [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α) [Inhabited (β a)] (h) :
    Raw₀.get m a h = Raw₀.get! m a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.get Raw₀.get!; simp only [Array.ugetElem_eq_getElem]; exact a_ggb _ _ _
theorem zdrg_gb [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (a : α) [Inhabited (β a)] (h : a ∈ m) :
    DHashMap.Raw.get m a h = DHashMap.Raw.get! m a := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.get DHashMap.Raw.get!; rw [dite_eq_left hb]; exact zr0g_gb _ _ _
theorem zr0g_gd [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)  (fb : β a) (h) :
    Raw₀.get m a h = Raw₀.getD m a fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.get Raw₀.getD; simp only [Array.ugetElem_eq_getElem]; exact a_ggd _ _ _ _
theorem zdrg_gd [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (a : α)  (fb : β a) (h : a ∈ m) :
    DHashMap.Raw.get m a h = DHashMap.Raw.getD m a fb := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.get DHashMap.Raw.getD; rw [dite_eq_left hb]; exact zr0g_gd _ _ _ _
theorem zr0g_qg [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)  (h) :
    Raw₀.get? m a = some (Raw₀.get m a h) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.get Raw₀.get?; simp only [Array.ugetElem_eq_getElem]; exact a_gqg _ _ _
theorem zdrg_qg [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (a : α)  (h : a ∈ m) :
    DHashMap.Raw.get? m a = some (DHashMap.Raw.get m a h) := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.get DHashMap.Raw.get?; rw [dite_eq_left hb]; exact zr0g_qg _ _ _
theorem zr0k_bq [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) [Inhabited α] :
    Raw₀.getKey! m a = (Raw₀.getKey? m a).get! := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey? Raw₀.getKey!; simp only [Array.ugetElem_eq_getElem]; exact a_kbq _ _
theorem zdrk_bq [BEq α] [Hashable α] (m : DHashMap.Raw α β) (a : α) [Inhabited α] :
    DHashMap.Raw.getKey! m a = (DHashMap.Raw.getKey? m a).get! := by
  unfold DHashMap.Raw.getKey! DHashMap.Raw.getKey?; split
  · exact zr0k_bq _ _
  · rfl
theorem zr0k_dq [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)  (fb : α) :
    Raw₀.getKeyD m a fb = (Raw₀.getKey? m a).getD fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey? Raw₀.getKeyD; simp only [Array.ugetElem_eq_getElem]; exact a_kdq _ _ _
theorem zdrk_dq [BEq α] [Hashable α] (m : DHashMap.Raw α β) (a : α)  (fb : α) :
    DHashMap.Raw.getKeyD m a fb = (DHashMap.Raw.getKey? m a).getD fb := by
  unfold DHashMap.Raw.getKeyD DHashMap.Raw.getKey?; split
  · exact zr0k_dq _ _ _
  · rfl
theorem zr0k_gb [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) [Inhabited α] (h) :
    Raw₀.getKey m a h = Raw₀.getKey! m a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey Raw₀.getKey!; simp only [Array.ugetElem_eq_getElem]; exact a_kgb _ _ _
theorem zdrk_gb [BEq α] [Hashable α] (m : DHashMap.Raw α β) (a : α) [Inhabited α] (h : a ∈ m) :
    DHashMap.Raw.getKey m a h = DHashMap.Raw.getKey! m a := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.getKey DHashMap.Raw.getKey!; rw [dite_eq_left hb]; exact zr0k_gb _ _ _
theorem zr0k_gd [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)  (fb : α) (h) :
    Raw₀.getKey m a h = Raw₀.getKeyD m a fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey Raw₀.getKeyD; simp only [Array.ugetElem_eq_getElem]; exact a_kgd _ _ _ _
theorem zdrk_gd [BEq α] [Hashable α] (m : DHashMap.Raw α β) (a : α)  (fb : α) (h : a ∈ m) :
    DHashMap.Raw.getKey m a h = DHashMap.Raw.getKeyD m a fb := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.getKey DHashMap.Raw.getKeyD; rw [dite_eq_left hb]; exact zr0k_gd _ _ _ _
theorem zr0k_qg [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)  (h) :
    Raw₀.getKey? m a = some (Raw₀.getKey m a h) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey Raw₀.getKey?; simp only [Array.ugetElem_eq_getElem]; exact a_kqg _ _ _
theorem zdrk_qg [BEq α] [Hashable α] (m : DHashMap.Raw α β) (a : α)  (h : a ∈ m) :
    DHashMap.Raw.getKey? m a = some (DHashMap.Raw.getKey m a h) := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.getKey DHashMap.Raw.getKey?; rw [dite_eq_left hb]; exact zr0k_qg _ _ _
end
end W5c3
namespace W5c3
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
-- get! congruence needs EquivBEq and LawfulHashable only (same bucket, same first match)
theorem a_cgc [BEq α] [EquivBEq α] [Inhabited γ] (l : AssocList α (fun _ => γ)) (a b : α) (hab : (a == b) = true) :
    l.get! a = l.get! b := by
  induction l with
  | nil => rfl
  | cons k v t ih => simp only [AssocList.get!, BEq.congr_right hab, ih]
theorem a_kgc [BEq α] [EquivBEq α] [Inhabited α] (l : AssocList α β) (a b : α) (hab : (a == b) = true) :
    l.getKey! a = l.getKey! b := by
  induction l with
  | nil => rfl
  | cons k v t ih => simp only [AssocList.getKey!, BEq.congr_right hab, ih]
theorem zr0c_gc [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [Inhabited γ] (m : Raw₀ α (fun _ => γ)) (a b : α)
    (hab : (a == b) = true) : Raw₀.Const.get! m a = Raw₀.Const.get! m b := by
  obtain ⟨⟨s, bs⟩, hm⟩ := m
  simp only [Raw₀.Const.get!, hash_eq hab]
  exact a_cgc _ _ _ hab
theorem zr0k_gc [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [Inhabited α] (m : Raw₀ α β) (a b : α)
    (hab : (a == b) = true) : Raw₀.getKey! m a = Raw₀.getKey! m b := by
  obtain ⟨⟨s, bs⟩, hm⟩ := m
  simp only [Raw₀.getKey!, hash_eq hab]
  exact a_kgc _ _ _ hab
theorem zdrc_gc [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [Inhabited γ] (m : DHashMap.Raw α (fun _ => γ)) (a b : α)
    (hab : (a == b) = true) : DHashMap.Raw.Const.get! m a = DHashMap.Raw.Const.get! m b := by
  simp only [DHashMap.Raw.Const.get!]; split
  · exact zr0c_gc _ _ _ hab
  · rfl
theorem zdrk_gc [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [Inhabited α] (m : DHashMap.Raw α β) (a b : α)
    (hab : (a == b) = true) : DHashMap.Raw.getKey! m a = DHashMap.Raw.getKey! m b := by
  simp only [DHashMap.Raw.getKey!]; split
  · exact zr0k_gc _ _ _ hab
  · rfl
-- filterMap keeps the bucket array and filters each bucket (no laws, no WF)
theorem al_fm_c [BEq α] {δ : α → Type w} (f : (a : α) → β a → Option (δ a)) (a : α) (l : AssocList α β)
    (h : (l.filterMap f).contains a = true) : l.contains a = true := by
  simp only [AssocList.contains_eq, ck_any, (AssocList.toList_filterMap (f := f) (l := l)).any_eq] at h ⊢
  simp only [List.any_eq_true] at h ⊢
  obtain ⟨x, hx, hx2⟩ := h
  simp only [List.mem_filterMap, Option.map_eq_some_iff] at hx
  obtain ⟨y, hy, c, -, rfl⟩ := hx
  exact ⟨y, hy, hx2⟩
theorem r0_fm_c [BEq α] [Hashable α] {δ : α → Type w} (f : (a : α) → β a → Option (δ a)) (m : Raw₀ α β) (k : α)
    (h : (Raw₀.filterMap f m).contains k = true) : m.contains k = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have e : Raw₀.filterMap f ⟨⟨s, bs⟩, hb⟩ =
      ⟨⟨computeSize (bs.map (AssocList.filterMap f)), bs.map (AssocList.filterMap f)⟩, by simpa using hb⟩ := rfl
  rw [e, contains_gen, map_idx _ _ _ hb] at h
  rw [contains_gen]; exact al_fm_c _ _ _ h
theorem dr_fm_c [BEq α] [Hashable α] {δ : α → Type w} (f : (a : α) → β a → Option (δ a)) (m : DHashMap.Raw α β) (k : α)
    (h : (m.filterMap f).contains k = true) : m.contains k = true := by
  unfold DHashMap.Raw.filterMap at h; split at h
  · rename_i hb
    obtain ⟨hb', h⟩ := W4c5.dr_pos h
    have := r0_fm_c f ⟨m, hb⟩ k h
    unfold DHashMap.Raw.contains; rw [dite_eq_left hb]; exact this
  · simp [DHashMap.Raw.contains_empty] at h
-- insertManyIfNewUnit only inserts (no laws, no WF)
theorem r0u_sz {ρ : Type w} [ForIn Id ρ α] [BEq α] [Hashable α] (m : Raw₀ α (fun _ => Unit)) (l : ρ) :
    m.1.size ≤ (Raw₀.Const.insertManyIfNewUnit m l).1.1.size :=
  (Raw₀.Const.insertManyIfNewUnit m l).2 (fun m' => m.1.size ≤ m'.1.size)
    (fun h => Nat.le_trans h (raw0_size_insertIfNew _ _ _).1) (Nat.le_refl _)
theorem dru_sz {ρ : Type w} [ForIn Id ρ α] [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => Unit)) (l : ρ) :
    m.size ≤ (DHashMap.Raw.Const.insertManyIfNewUnit m l).size := by
  unfold DHashMap.Raw.Const.insertManyIfNewUnit; split
  · exact r0u_sz ⟨m, _⟩ l
  · exact Nat.le_refl _
end
end W5c3
namespace W5c3
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v}
-- Raw.filter permutes to the filtered model list without WF (a bucketless map gives ∅)
theorem dr_tlm_filter [BEq α] [Hashable α] (f : (a : α) → β a → Bool) (m : DHashMap.Raw α β) :
    (toListModel (m.filter f).buckets).Perm ((toListModel m.buckets).filter fun p => f p.1 p.2) := by
  unfold DHashMap.Raw.filter; split
  · exact Raw₀.toListModel_filter
  · rename_i hb
    have e : m.buckets = #[] := Array.eq_empty_of_size_eq_zero (by omega)
    rw [e, dr_empty]; simp [toListModel, nil16]
theorem dr_eqv_filter [BEq α] [Hashable α] (f : (a : α) → β a → Bool) {m₁ m₂ : DHashMap.Raw α β}
    (h : m₁.Equiv m₂) : (m₁.filter f).Equiv (m₂.filter f) :=
  ⟨(dr_tlm_filter f m₁).trans ((h.1.filter _).trans (dr_tlm_filter f m₂).symm)⟩
end
end W5c3
namespace W5c3
open Std Std.DHashMap.Internal
section
variable {α : Type u}
-- unreachable buckets: with hash 0 (or 0/1) no key ever looks into bucket 1 of 2 (or bucket 2 of 4)
theorem z2_c [BEq α] [Hashable α] {β : α → Type v} (s : Nat) (l : AssocList α β) (a : α) (hh : hash a = 0) :
    Raw₀.contains (⟨⟨s, #[.nil, l]⟩, by simp⟩ : Raw₀ α β) a = false := by
  rw [contains_eval _ (by simp [Pow2])]
  have : ix #[.nil, l] a = 0 := by
    show (scrambleHash (hash a)).toNat % 2 = 0
    rw [hh, scr_small _ (by decide)]; rfl
  simp only [this]; rfl
theorem z4_c [BEq α] [Hashable α] {β : α → Type v} (s : Nat) (l : AssocList α β) (a : α) (hh : hash a = 0 ∨ hash a = 1) :
    Raw₀.contains (⟨⟨s, #[.nil, .nil, l, .nil]⟩, by simp⟩ : Raw₀ α β) a = false := by
  rw [contains_eval _ (by simp [Pow2])]
  rcases hh with hh | hh
  · have : ix #[.nil, .nil, l, .nil] a = 0 := by
      show (scrambleHash (hash a)).toNat % 4 = 0
      rw [hh, scr_small _ (by decide)]; rfl
    simp only [this]; rfl
  · have : ix #[.nil, .nil, l, .nil] a = 1 := by
      show (scrambleHash (hash a)).toNat % 4 = 1
      rw [hh, scr_small _ (by decide)]; rfl
    simp only [this]; rfl
theorem hz_h (k : HZ) : hash k = 0 ∨ hash k = 1 := by
  rcases k with ⟨n⟩; simp only [HZ.hash_def]; split <;> simp
end
end W5c3
open W5c3
set_option Elab.async false
set_option maxHeartbeats 400000

/-! ## From `checks/W5c4Hand.lean` -/
namespace W5c4
variable {α : Type u} [BEq α] [Hashable α]
-- bucket-level facts that need no BEq/Hashable laws and no WF
open Std.Internal.List in
theorem al_gs {γ : Type v} (l : AssocList α (fun _ => γ)) (k : α) (v : γ) :
    l.get? k = some v ↔ ∃ h : l.contains k, l.get k h = v := by
  simp only [AssocList.get?_eq, AssocList.get_eq, AssocList.contains_eq]; exact getValue?_eq_some_iff
open Std.Internal.List in
theorem al_ks {β : α → Type v} (l : AssocList α β) (k k' : α) :
    l.getKey? k = some k' ↔ ∃ h : l.contains k, l.getKey k h = k' := by
  simp only [AssocList.getKey?_eq, AssocList.getKey_eq, AssocList.contains_eq]
  by_cases h : containsKey k l.toList
  · simp [h, getKey?_eq_some_getKey]
  · simp only [h]
    simp only [containsKey_eq_isSome_getKey?, Bool.not_eq_true, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at h
    simp [h]
theorem r0c_g!D {γ : Type v} [Inhabited γ] (m : Raw₀ α (fun _ => γ)) (a : α) :
    Raw₀.Const.get! m a = Raw₀.Const.getD m a default := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.Const.get! Raw₀.Const.getD; simp only [AssocList.get!_eq, AssocList.getD_eq]; rfl
theorem r0_k!D {β : α → Type v} [Inhabited α] (m : Raw₀ α β) (a : α) :
    Raw₀.getKey! m a = Raw₀.getKeyD m a default := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey! Raw₀.getKeyD; simp only [AssocList.getKey!_eq, AssocList.getKeyD_eq]; rfl
theorem r0c_cs {γ : Type v} (m : Raw₀ α (fun _ => γ)) (a : α) :
    m.contains a = (Raw₀.Const.get? m a).isSome := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.Const.get? Raw₀.contains
  simp only [AssocList.get?_eq, AssocList.contains_eq]; exact Std.Internal.List.containsKey_eq_isSome_getValue?
theorem r0_csc [LawfulBEq α] {β : α → Type v} (m : Raw₀ α β) (a : α) :
    m.contains a = (m.get? a).isSome := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.get? Raw₀.contains
  simp only [AssocList.getCast?_eq, AssocList.contains_eq]; exact Std.Internal.List.containsKey_eq_isSome_getValueCast?
theorem r0_ck {β : α → Type v} (m : Raw₀ α β) (a : α) :
    m.contains a = (m.getKey? a).isSome := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey? Raw₀.contains
  simp only [AssocList.getKey?_eq, AssocList.contains_eq]; exact Std.Internal.List.containsKey_eq_isSome_getKey?
theorem r0c_gs {γ : Type v} (m : Raw₀ α (fun _ => γ)) (k : α) (v : γ) :
    Raw₀.Const.get? m k = some v ↔ ∃ h : m.contains k, Raw₀.Const.get m k h = v := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  exact al_gs _ _ _
theorem r0_ks {β : α → Type v} (m : Raw₀ α β) (k k' : α) :
    m.getKey? k = some k' ↔ ∃ h : m.contains k, m.getKey k h = k' := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  exact al_ks _ _ _
theorem al_gcs [LawfulBEq α] {β : α → Type v} (l : AssocList α β) (k : α) (v : β k) :
    l.getCast? k = some v ↔ ∃ h : l.contains k, l.getCast k h = v := by
  simp only [AssocList.getCast?_eq, AssocList.getCast_eq, AssocList.contains_eq]
  exact Std.Internal.List.getValueCast?_eq_some_iff
theorem r0_gs [LawfulBEq α] {β : α → Type v} (m : Raw₀ α β) (k : α) (v : β k) :
    m.get? k = some v ↔ ∃ h : m.contains k, m.get k h = v := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  exact al_gcs _ _ _
theorem r0_g!D [LawfulBEq α] {β : α → Type v} (m : Raw₀ α β) (a : α) [Inhabited (β a)] :
    m.get! a = m.getD a default := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.get! Raw₀.getD; simp only [AssocList.getCast!_eq, AssocList.getCastD_eq]; rfl
-- Raw wrappers
theorem drc_g!D {γ : Type v} [Inhabited γ] (m : DHashMap.Raw α (fun _ => γ)) (a : α) :
    DHashMap.Raw.Const.get! m a = DHashMap.Raw.Const.getD m a default := by
  unfold DHashMap.Raw.Const.get! DHashMap.Raw.Const.getD; split
  · exact r0c_g!D _ _
  · rfl
theorem dr_g!D [LawfulBEq α] {β : α → Type v} (m : DHashMap.Raw α β) (a : α) [Inhabited (β a)] :
    m.get! a = m.getD a default := by
  unfold DHashMap.Raw.get! DHashMap.Raw.getD; split
  · exact r0_g!D _ _
  · rfl
theorem dr_k!D {β : α → Type v} [Inhabited α] (m : DHashMap.Raw α β) (a : α) :
    m.getKey! a = m.getKeyD a default := by
  unfold DHashMap.Raw.getKey! DHashMap.Raw.getKeyD; split
  · exact r0_k!D _ _
  · rfl
theorem drc_cs {γ : Type v} (m : DHashMap.Raw α (fun _ => γ)) (a : α) :
    m.contains a = (DHashMap.Raw.Const.get? m a).isSome := by
  unfold DHashMap.Raw.contains DHashMap.Raw.Const.get?; split
  · exact r0c_cs _ _
  · rfl
theorem dr_csc [LawfulBEq α] {β : α → Type v} (m : DHashMap.Raw α β) (a : α) :
    m.contains a = (m.get? a).isSome := by
  unfold DHashMap.Raw.contains DHashMap.Raw.get?; split
  · exact r0_csc _ _
  · rfl
theorem dr_ck {β : α → Type v} (m : DHashMap.Raw α β) (a : α) :
    m.contains a = (m.getKey? a).isSome := by
  unfold DHashMap.Raw.contains DHashMap.Raw.getKey?; split
  · exact r0_ck _ _
  · rfl
theorem drc_gs {γ : Type v} (m : DHashMap.Raw α (fun _ => γ)) (k : α) (v : γ) :
    DHashMap.Raw.Const.get? m k = some v ↔ ∃ h : k ∈ m, DHashMap.Raw.Const.get m k h = v := by
  simp only [DHashMap.Raw.mem_iff_contains]
  unfold DHashMap.Raw.Const.get? DHashMap.Raw.Const.get DHashMap.Raw.contains; split
  · exact r0c_gs _ _ _
  · simp
theorem dr_gs [LawfulBEq α] {β : α → Type v} (m : DHashMap.Raw α β) (k : α) (v : β k) :
    m.get? k = some v ↔ ∃ h : k ∈ m, m.get k h = v := by
  simp only [DHashMap.Raw.mem_iff_contains]
  unfold DHashMap.Raw.get? DHashMap.Raw.get DHashMap.Raw.contains; split
  · exact r0_gs _ _ _
  · simp
theorem dr_ks {β : α → Type v} (m : DHashMap.Raw α β) (k k' : α) :
    m.getKey? k = some k' ↔ ∃ h : k ∈ m, m.getKey k h = k' := by
  simp only [DHashMap.Raw.mem_iff_contains]
  unfold DHashMap.Raw.getKey? DHashMap.Raw.getKey DHashMap.Raw.contains; split
  · exact r0_ks _ _ _
  · simp
end W5c4
open W5c4
macro "w5ev" : tactic => `(tactic| first
  | decide +kernel
  | (hm_eval; done)
  | (simp [DHashMap.Raw.toList, DHashMap.Raw.Const.toList, DHashMap.Raw.toArray, DHashMap.Raw.Const.toArray]; hm_eval; done)
  | (simp [DHashMap.toList, DHashMap.Const.toList, HashMap.toList, HashMap.Raw.toList, DHashMap.toArray, DHashMap.Const.toArray, HashMap.toArray, HashMap.Raw.toArray, HashSet.toArray, HashSet.Raw.toArray, DHashMap.Raw.toList, DHashMap.Raw.Const.toList, DHashMap.Raw.toArray, DHashMap.Raw.Const.toArray, DHashMap.size, HashMap.size, HashSet.size]; hm_eval; done)
  | (hm_eval_raw; done)
  | (w1c0_raw; done)
  | (simp [ExtHashMap.mem_alter]; done)
  | (simp [ExtDHashMap.mem_alter]; done)
  | (simp [ExtDHashMap.Const.mem_alter]; done)
  | (simp [ExtHashMap.contains_alter]; done)
  | (simp [ExtDHashMap.contains_alter]; done)
  | (simp [ExtDHashMap.Const.contains_alter]; done)
  | (simp [ExtHashMap.getKey!_insert]; done)
  | (simp [ExtDHashMap.getKey!_insert]; done)
  | (simp [DHashMap.mem_alter]; done)
  | (simp [DHashMap.Raw.mem_alter, DHashMap.Raw.WF.empty]; done)
  | (simp; done))
macro "w5evt" : tactic => `(tactic| first
  | rfl
  | decide +kernel
  | (simp only [HashMap.mem_iff_contains, HashSet.mem_iff_contains, DHashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashSet.Raw.mem_iff_contains, DHashMap.Raw.mem_iff_contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))
  | (hm_eval; done)
  | (hm_eval_raw; done))
namespace W5c4
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
-- getKey returns a stored key that is == the query (no WF)
theorem r0_gk [LawfulBEq α] (m : Raw₀ α β) (a : α) (h' : m.contains a) : m.getKey a h' = a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey; simp only [AssocList.getKey_eq]; exact eq_of_beq (getKey_beq _)
theorem dr_gk [LawfulBEq α] (m : DHashMap.Raw α β) (a : α) (h' : a ∈ m) : m.getKey a h' = a := by
  unfold DHashMap.Raw.getKey; exact r0_gk _ _ _
-- == keys share a bucket (LawfulHashable) and the bucket lookup respects == (EquivBEq); no WF
theorem r0_gkc [EquivBEq α] [LawfulHashable α] [Inhabited α] (m : Raw₀ α β) (k k' : α) (h : k == k') :
    m.getKey! k = m.getKey! k' := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey!; simp only [hash_eq h, AssocList.getKey!_eq]; exact getKey!_congr h
theorem dr_gkc [EquivBEq α] [LawfulHashable α] [Inhabited α] (m : DHashMap.Raw α β) (k k' : α) (h : k == k') :
    m.getKey! k = m.getKey! k' := by
  unfold DHashMap.Raw.getKey!; split
  · exact r0_gkc _ _ _ h
  · rfl
-- a key returned by getKey? lies in the query's bucket and is == to itself; no WF
theorem r0_mgk [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) (a a' : α) (h : m.getKey? a = some a') :
    m.contains a' = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey? at h; simp only [AssocList.getKey?_eq] at h
  have hab : (a' == a) = true := by
    have := getKey?_beq (a := a) (l := (bs[(mkIdx bs.size hb (hash a)).1.toNat]'(mkIdx bs.size hb (hash a)).2).toList)
    simp only [Array.ugetElem_eq_getElem] at h
    rw [h] at this; simpa using this
  have hc : containsKey a (bs[(mkIdx bs.size hb (hash a)).1.toNat]'(mkIdx bs.size hb (hash a)).2).toList = true := by
    rw [containsKey_eq_isSome_getKey?]; simp only [Array.ugetElem_eq_getElem] at h; rw [h]; rfl
  rw [contains_gen, AssocList.contains_eq]; simp only [hash_eq hab]
  exact containsKey_of_beq hc (BEq.symm hab)
theorem dr_mgk [EquivBEq α] [LawfulHashable α] (m : DHashMap.Raw α β) (a a' : α) (h : m.getKey? a = some a') :
    a' ∈ m := by
  rw [DHashMap.Raw.mem_iff_contains]
  unfold DHashMap.Raw.getKey? at h; unfold DHashMap.Raw.contains; split
  · rename_i hb; rw [dif_pos hb] at h; exact r0_mgk _ _ _ h
  · rename_i hb; rw [dif_neg hb] at h; cases h
end
end W5c4
open W5c4
namespace W5c4
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
-- a stored key is found in a hash-self array by itself (== reflexive; LawfulHashable not needed)
theorem com_self [EquivBEq α] (s : Nat) (bs : Array (AssocList α β)) (hb : 0 < bs.size) (hs : IsHashSelf bs)
    (p : (a : α) × β a) (hp : p ∈ toListModel bs) : Raw₀.contains (⟨⟨s, bs⟩, hb⟩ : Raw₀ α β) p.1 = true := by
  rw [contains_gen, AssocList.contains_eq]
  have hp' : p ∈ bs.toList.flatMap AssocList.toList := hp
  obtain ⟨l, hl, hpl⟩ := List.mem_flatMap.mp hp'
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hl)
  have hidx := (hs.hashes_to j hj).hash_self hb p hpl
  apply containsKey_eq_true_iff_exists_mem.mpr
  refine ⟨p, ?_, BEq.rfl⟩
  simp only [hidx]; exact hpl
theorem cex_self [EquivBEq α] (m : Raw₀ α β) (p : (a : α) × β a) (hp : p ∈ toListModel m.1.buckets)
    (h : m.contains p.1 = true) : m.expandIfNecessary.contains p.1 = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have hperm := tlm_expandIfNecessary (⟨⟨s, bs⟩, hb⟩ : Raw₀ α β)
  unfold Raw₀.expandIfNecessary at hperm ⊢
  dsimp only at hperm ⊢
  split
  · exact h
  · rename_i hn
    simp only [hn] at hperm
    exact com_self _ _ _ (W1c5.isHashSelf_expand' _) p (hperm.mem_iff.mpr hp)
theorem mem_uset_self (bs : Array (AssocList α β)) (i : USize) (hi : i.toNat < bs.size) (d : AssocList α β)
    (p : (a : α) × β a) (hp : p ∈ d.toList) : p ∈ toListModel (bs.uset i d hi) := by
  obtain ⟨l, h₁, h₂, -⟩ := exists_bucket_of_uset bs i hi d
  exact h₂.mem_iff.mpr (List.mem_append_left _ hp)
-- insert/insertIfNew make the key findable for any EquivBEq, without LawfulHashable or WF
theorem r0_cis [EquivBEq α] (m : Raw₀ α β) (k : α) (v : β k) : (m.insert k v).contains k = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.insert
  dsimp only
  split
  · rename_i hc
    rw [contains_gen]
    simp only [Array.uset, mkIdx_set_toNat, Array.getElem_set, ite_true]
    simp only [Array.ugetElem_eq_getElem] at hc
    rw [AssocList.contains_eq, AssocList.toList_replace, containsKey_replaceEntry, ← AssocList.contains_eq]
    exact hc
  · exact cex_self (β := β) _ ⟨k, v⟩ (mem_uset_self _ _ (mkIdx bs.size hb (hash k)).2 _ _ (by simp))
      (by rw [contains_gen]; simp only [Array.uset, mkIdx_set_toNat, Array.getElem_set, ite_true]
          simp [AssocList.contains])
theorem r0_ciis [EquivBEq α] (m : Raw₀ α β) (k : α) (v : β k) : (m.insertIfNew k v).contains k = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.insertIfNew
  dsimp only
  split
  · rename_i hc
    rw [contains_gen]; simpa only [Array.ugetElem_eq_getElem] using hc
  · exact cex_self (β := β) _ ⟨k, v⟩ (mem_uset_self _ _ (mkIdx bs.size hb (hash k)).2 _ _ (by simp))
      (by rw [contains_gen]; simp only [Array.uset, mkIdx_set_toNat, Array.getElem_set, ite_true]
          simp [AssocList.contains])
theorem dr_cis [EquivBEq α] (m : DHashMap.Raw α β) (h : 0 < m.buckets.size) (k : α) (v : β k) :
    (m.insert k v).contains k = true := by
  unfold DHashMap.Raw.insert; rw [dif_pos h]; unfold DHashMap.Raw.contains
  rw [dif_pos (Raw₀.insert ⟨m, h⟩ k v).2]; exact r0_cis (⟨m, h⟩ : Raw₀ α β) k v
theorem dr_ciis [EquivBEq α] (m : DHashMap.Raw α β) (h : 0 < m.buckets.size) (k : α) (v : β k) :
    (m.insertIfNew k v).contains k = true := by
  unfold DHashMap.Raw.insertIfNew; rw [dif_pos h]; unfold DHashMap.Raw.contains
  rw [dif_pos (Raw₀.insertIfNew ⟨m, h⟩ k v).2]; exact r0_ciis (⟨m, h⟩ : Raw₀ α β) k v
end
end W5c4
open W5c4
namespace W5c4
-- under NB (== always false) no key is ever found
theorem nb_al {β : NB → Type v} (l : AssocList NB β) (k : NB) : l.contains k = false := by
  induction l with
  | nil => rfl
  | cons a b t ih => simp only [AssocList.contains, ih]; rfl
theorem nb_nc {β : NB → Type v} (s : Nat) (bs : Array (AssocList NB β)) (h : 0 < bs.size) (k : NB) :
    Raw₀.contains (⟨⟨s, bs⟩, h⟩ : Raw₀ NB β) k = false := by
  rw [contains_gen]; exact nb_al _ _
end W5c4
macro "w5nf" : tactic => `(tactic| (
  simp only [HashMap.mem_iff_contains, DHashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains,
    DHashMap.Raw.mem_iff_contains, Bool.not_eq_true]
  try simp only [HashMap.contains, HashMap.Raw.contains, DHashMap.contains]
  try unfold DHashMap.Raw.contains
  try rw [dif_pos (by decide)]
  first
  | exact W5c4.nb_nc _ _ _ _
  | exact W3c5.hz_unreach _ _ _ _
  | exact W1c5.zh_contains _ _ _))
namespace W5c4
variable {α : Type u} [BEq α] [Hashable α]
theorem nil2_nc {β : α → Type v} (s : Nat) (h : 0 < (#[.nil, .nil] : Array (AssocList α β)).size) (k : α) :
    Raw₀.contains (⟨⟨s, #[.nil, .nil]⟩, h⟩ : Raw₀ α β) k = false := by
  rw [contains_gen]
  have : ∀ (j : Nat) (hj : j < 2), ((#[.nil, .nil] : Array (AssocList α β))[j]'hj).contains k = false := by
    intro j hj; match j, hj with | 0, _ => rfl | 1, _ => rfl
  exact this _ _
theorem r0_gkn {β : α → Type v} (m : Raw₀ α β) (k : α) (h : m.contains k = false) : m.getKey? k = none := by
  rw [r0_ck] at h; simpa using h
end W5c4
macro "w5c" : tactic => `(tactic| first
  | exact W5c4.nb_nc _ _ _ _
  | exact W3c5.hz_unreach _ _ _ _
  | exact W1c5.zh_contains _ _ _
  | exact W5c4.nil2_nc _ _ _)
macro "w5gk" : tactic => `(tactic| (
  try simp only [HashMap.getKey?, HashMap.Raw.getKey?, DHashMap.getKey?]
  try unfold DHashMap.Raw.getKey?
  try rw [dif_pos (by decide), dif_pos (by decide)]
  rw [W5c4.r0_gkn _ _ (by w5c), W5c4.r0_gkn _ _ (by w5c)]))
macro "w5neq" : tactic => `(tactic| first
  | exact absurd (List.Perm.length_eq this.1) (by decide)
  | exact absurd (List.Perm.length_eq this.1.1) (by decide)
  | exact absurd (List.Perm.length_eq this.1.1.1) (by decide)
  | exact absurd (List.Perm.length_eq this.1) (by simp [toListModel])
  | exact absurd (List.Perm.length_eq this.1.1) (by simp [toListModel])
  | exact absurd (List.Perm.length_eq this.1.1.1) (by simp [toListModel]))
namespace W5c4
abbrev cg : DHashMap.Raw CZ (fun _ => Nat) := ⟨1, #[b1 (CZ.mk 0) 0, .nil]⟩
abbrev cb : DHashMap.Raw CZ (fun _ => Nat) := ⟨5, #[b1 (CZ.mk 0) 0, .nil]⟩
abbrev ce : DHashMap.Raw CZ (fun _ => Nat) := ⟨0, #[.nil, .nil]⟩
theorem cg_wf : cg.WF := W2c0.cz_wf _ _ rfl (by simp [toListModel])
theorem ce_wf : ce.WF := W2c0.cz_wf _ _ rfl (by simp [toListModel])
-- the size field 5 differs from the single entry
theorem cb_nwf : ¬ cb.WF := fun hw => absurd (Std.DHashMap.Internal.Raw.WF.out hw).size_eq (by simp [toListModel])
theorem cb_eq : cb.Equiv cg := ⟨List.Perm.refl _⟩
theorem cg_eq : cg.Equiv cb := ⟨List.Perm.refl _⟩
theorem cg_mem : CZ.mk 0 ∈ cg := by simp only [DHashMap.Raw.mem_iff_contains]; decide +kernel
theorem cb_mem : CZ.mk 0 ∈ cb := by simp only [DHashMap.Raw.mem_iff_contains]; decide +kernel
theorem cg_ne : ¬ cg.Equiv ce := fun h => absurd (List.Perm.length_eq h.1) (by simp [toListModel])
end W5c4

/-! ## From `checks/W5c5Hand.lean` -/
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
export W5c3 (a_cbq)
export W5c3 (a_cdq)
export W5c3 (a_cqg)
export W5c3 (a_kbq)
export W5c3 (a_kdq)
export W5c3 (a_kqg)
export W5c3 (a_gbq)
export W5c3 (a_gdq)
export W5c3 (a_gqg)
export W5c3 (a_cgb)
export W5c3 (a_cgd)
export W5c3 (a_kgb)
export W5c3 (a_kgd)
export W5c3 (a_ggb)
export W5c3 (a_ggd)
export W5c3 (zr0c_bq)
export W5c3 (zdrc_bq)
export W5c3 (zr0c_dq)
export W5c3 (zdrc_dq)
export W5c3 (zr0c_gb)
export W5c3 (zdrc_gb)
export W5c3 (zr0c_gd)
export W5c3 (zdrc_gd)
export W5c3 (zr0c_qg)
export W5c3 (zdrc_qg)
export W5c3 (zr0g_bq)
export W5c3 (zdrg_bq)
export W5c3 (zr0g_dq)
export W5c3 (zdrg_dq)
export W5c3 (zr0g_gb)
export W5c3 (zdrg_gb)
export W5c3 (zr0g_gd)
export W5c3 (zdrg_gd)
export W5c3 (zr0g_qg)
export W5c3 (zdrg_qg)
export W5c3 (zr0k_bq)
export W5c3 (zdrk_bq)
export W5c3 (zr0k_dq)
export W5c3 (zdrk_dq)
export W5c3 (zr0k_gb)
export W5c3 (zdrk_gb)
export W5c3 (zr0k_gd)
export W5c3 (zdrk_gd)
export W5c3 (zr0k_qg)
export W5c3 (zdrk_qg)
end
end W5c5
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
-- getKey returns a stored key x found by x == a (no laws)
theorem a_gkb [BEq α] (l : AssocList α β) (a : α) (h) : (l.getKey a h == a) = true := by
  induction l with
  | nil => cases h
  | cons k v t ih =>
    cases hk : (k == a)
    · have h' : t.contains a = true := by simpa only [AssocList.contains, hk, Bool.false_or] using h
      simp only [AssocList.getKey, hk, Bool.false_eq_true, ↓reduceDIte]; exact ih h'
    · simp [AssocList.getKey, hk]
theorem r0_gkb [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (h) : (Raw₀.getKey m a h == a) = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey; exact a_gkb _ _ _
theorem dr_gkb [BEq α] [Hashable α] (m : DHashMap.Raw α β) (a : α) (h : a ∈ m) : (DHashMap.Raw.getKey m a h == a) = true := by
  unfold DHashMap.Raw.getKey; exact r0_gkb _ _ _
-- Const.modify on a bucket: only EquivBEq, no distinct keys
theorem a_mk [BEq α] [EquivBEq α] (l : AssocList α (fun _ => γ)) (k k' : α) (f : γ → γ) :
    (AssocList.Const.modify k f l).getKey? k' = if k == k' then (if l.contains k then some k else none) else l.getKey? k' := by
  induction l with
  | nil => simp [AssocList.Const.modify, AssocList.getKey?, AssocList.contains]
  | cons e v t ih =>
    by_cases he : (e == k) = true
    · simp only [AssocList.Const.modify, he, ↓reduceIte, AssocList.getKey?, AssocList.contains, Bool.true_or]
      by_cases hk : (k == k') = true
      · simp [hk]
      · have : (e == k') = false := by
          cases h2 : (e == k')
          · rfl
          · exact absurd (BEq.trans (BEq.symm he) h2) hk
        simp [hk, this]
    · have he' : (e == k) = false := by simpa using he
      simp only [AssocList.Const.modify, he', Bool.false_eq_true, ↓reduceIte, AssocList.getKey?, AssocList.contains, Bool.false_or, ih]
      by_cases hk : (k == k') = true
      · have : (e == k') = false := by
          cases h2 : (e == k')
          · rfl
          · exact absurd (BEq.trans h2 (BEq.symm hk)) he
        simp [hk, this]
      · simp [hk]
theorem a_mg [BEq α] [EquivBEq α] (l : AssocList α (fun _ => γ)) (k k' : α) (f : γ → γ) :
    (AssocList.Const.modify k f l).get? k' = if k == k' then (l.get? k).map f else l.get? k' := by
  induction l with
  | nil => simp [AssocList.Const.modify, AssocList.get?]
  | cons e v t ih =>
    by_cases he : (e == k) = true
    · simp only [AssocList.Const.modify, he, ↓reduceIte, AssocList.get?]
      by_cases hk : (k == k') = true
      · simp [hk]
      · have : (e == k') = false := by
          cases h2 : (e == k')
          · rfl
          · exact absurd (BEq.trans (BEq.symm he) h2) hk
        simp [hk, this]
    · have he' : (e == k) = false := by simpa using he
      simp only [AssocList.Const.modify, he', Bool.false_eq_true, ↓reduceIte, AssocList.get?, ih]
      by_cases hk : (k == k') = true
      · have : (e == k') = false := by
          cases h2 : (e == k')
          · rfl
          · exact absurd (BEq.trans h2 (BEq.symm hk)) he
        simp [hk, this]
      · simp [hk]
end
end W5c5
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
theorem a_gkn [BEq α] [EquivBEq α] (l : AssocList α β) (k k' : α) (hk : (k == k') = true) (hc : ¬ l.contains k = true) :
    l.getKey? k' = none := by
  induction l with
  | nil => rfl
  | cons e v t ih =>
    simp only [AssocList.contains, Bool.or_eq_true, not_or] at hc
    have : (e == k') = false := by
      cases h2 : (e == k')
      · rfl
      · exact absurd (BEq.trans h2 (BEq.symm hk)) hc.1
    simp only [AssocList.getKey?, this, Bool.false_eq_true, ↓reduceIte]; exact ih hc.2
theorem a_ggn [BEq α] [EquivBEq α] (l : AssocList α (fun _ => γ)) (k k' : α) (hk : (k == k') = true) (hc : ¬ l.contains k = true) :
    l.get? k' = none := by
  induction l with
  | nil => rfl
  | cons e v t ih =>
    simp only [AssocList.contains, Bool.or_eq_true, not_or] at hc
    have : (e == k') = false := by
      cases h2 : (e == k')
      · rfl
      · exact absurd (BEq.trans h2 (BEq.symm hk)) hc.1
    simp only [AssocList.get?, this, cond_false]; exact ih hc.2
theorem r0_mk [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => γ)) (k k' : α) (f : γ → γ) :
    (Raw₀.Const.modify m k f).getKey? k' = if k == k' then (if m.contains k then some k else none) else m.getKey? k' := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  by_cases hc : (bs[(mkIdx bs.size hb (hash k)).1.toNat]'(mkIdx bs.size hb (hash k)).2).contains k = true
  · rw [cmodify_gen, if_pos hc]
    unfold Raw₀.getKey? Raw₀.contains
    simp only [Array.ugetElem_eq_getElem, Array.getElem_set, mkIdx_set_toNat]
    by_cases hk : (k == k') = true
    · have hh : hash k = hash k' := hash_eq hk
      simp only [← hh, ↓reduceIte, a_mk, hk, hc]
    · split
      · rw [a_mk]; simp only [hk]; simp_all
      · simp [hk]
  · rw [cmodify_gen, if_neg hc]
    unfold Raw₀.getKey? Raw₀.contains
    simp only [Array.ugetElem_eq_getElem, hc]
    by_cases hk : (k == k') = true
    · have hh : hash k = hash k' := hash_eq hk
      simp only [hk, ↓reduceIte, Bool.false_eq_true]
      simp only [← hh]; exact a_gkn _ _ _ hk hc
    · simp [hk]
theorem r0_mg [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => γ)) (k k' : α) (f : γ → γ) :
    Raw₀.Const.get? (Raw₀.Const.modify m k f) k' = if k == k' then (Raw₀.Const.get? m k).map f else Raw₀.Const.get? m k' := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  by_cases hc : (bs[(mkIdx bs.size hb (hash k)).1.toNat]'(mkIdx bs.size hb (hash k)).2).contains k = true
  · rw [cmodify_gen, if_pos hc]
    unfold Raw₀.Const.get?
    simp only [Array.ugetElem_eq_getElem, Array.getElem_set, mkIdx_set_toNat]
    by_cases hk : (k == k') = true
    · have hh : hash k = hash k' := hash_eq hk
      simp only [← hh, ↓reduceIte, a_mg, hk]
    · split
      · rw [a_mg]; simp only [hk]; simp_all
      · simp [hk]
  · rw [cmodify_gen, if_neg hc]
    unfold Raw₀.Const.get?
    simp only [Array.ugetElem_eq_getElem]
    by_cases hk : (k == k') = true
    · have hh : hash k = hash k' := hash_eq hk
      simp only [hk, ↓reduceIte]
      simp only [← hh, a_ggn _ _ _ hk hc, a_ggn _ _ _ (BEq.refl k) hc, Option.map_none]
    · simp [hk]
-- self versions: only EquivBEq (both sides read bucket idx(hash k))
theorem r0_mks [BEq α] [Hashable α] [EquivBEq α] (m : Raw₀ α (fun _ => γ)) (k : α) (f : γ → γ) :
    (Raw₀.Const.modify m k f).getKey? k = if m.contains k then some k else none := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  by_cases hc : (bs[(mkIdx bs.size hb (hash k)).1.toNat]'(mkIdx bs.size hb (hash k)).2).contains k = true
  · rw [cmodify_gen, if_pos hc]
    unfold Raw₀.getKey? Raw₀.contains
    simp only [Array.ugetElem_eq_getElem, Array.getElem_set, mkIdx_set_toNat, if_true]
    rw [a_mk]; simp only [BEq.refl, if_true, hc]
  · rw [cmodify_gen, if_neg hc]
    unfold Raw₀.getKey? Raw₀.contains
    simp only [Array.ugetElem_eq_getElem, hc]
    exact a_gkn _ _ _ (BEq.refl k) hc
theorem r0_mgs [BEq α] [Hashable α] [EquivBEq α] (m : Raw₀ α (fun _ => γ)) (k : α) (f : γ → γ) :
    Raw₀.Const.get? (Raw₀.Const.modify m k f) k = (Raw₀.Const.get? m k).map f := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  by_cases hc : (bs[(mkIdx bs.size hb (hash k)).1.toNat]'(mkIdx bs.size hb (hash k)).2).contains k = true
  · rw [cmodify_gen, if_pos hc]
    unfold Raw₀.Const.get?
    simp only [Array.ugetElem_eq_getElem, Array.getElem_set, mkIdx_set_toNat, if_true]
    rw [a_mg]; simp only [BEq.refl, if_true]
  · rw [cmodify_gen, if_neg hc]
    unfold Raw₀.Const.get?
    simp only [Array.ugetElem_eq_getElem]
    rw [a_ggn _ _ _ (BEq.refl k) hc]; rfl
end
end W5c5
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
-- Raw₀.Const statements of the modify lemmas without WF
theorem r0c_gkm [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => γ)) (k k' : α) (f : γ → γ) :
    (Raw₀.Const.modify m k f).getKey? k' = if k == k' then (if m.contains k then some k else none) else m.getKey? k' :=
  r0_mk m k k' f
theorem r0c_gkdm [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => γ)) (k k' fb : α) (f : γ → γ) :
    (Raw₀.Const.modify m k f).getKeyD k' fb = if k == k' then (if m.contains k then k else fb) else m.getKeyD k' fb := by
  rw [zr0k_dq, r0_mk, zr0k_dq]; split <;> (try split) <;> rfl
theorem r0c_gdm [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => γ)) (k k' : α) (fb : γ) (f : γ → γ) :
    Raw₀.Const.getD (Raw₀.Const.modify m k f) k' fb = if k == k' then ((Raw₀.Const.get? m k).map f).getD fb else Raw₀.Const.getD m k' fb := by
  rw [zr0c_dq, r0_mg, zr0c_dq]; split <;> rfl
theorem r0c_gkms [BEq α] [Hashable α] [EquivBEq α] (m : Raw₀ α (fun _ => γ)) (k : α) (f : γ → γ) :
    (Raw₀.Const.modify m k f).getKey? k = if m.contains k then some k else none :=
  r0_mks m k f
theorem r0c_gkdms [BEq α] [Hashable α] [EquivBEq α] (m : Raw₀ α (fun _ => γ)) (k fb : α) (f : γ → γ) :
    (Raw₀.Const.modify m k f).getKeyD k fb = if m.contains k then k else fb := by
  rw [zr0k_dq, r0_mks]; split <;> rfl
theorem r0c_gdms [BEq α] [Hashable α] [EquivBEq α] (m : Raw₀ α (fun _ => γ)) (k : α) (fb : γ) (f : γ → γ) :
    Raw₀.Const.getD (Raw₀.Const.modify m k f) k fb = ((Raw₀.Const.get? m k).map f).getD fb := by
  rw [zr0c_dq, r0_mgs]
theorem r0c_gks [BEq α] [Hashable α] [EquivBEq α] (m : Raw₀ α (fun _ => γ)) (k : α) (f : γ → γ) (hc) :
    (Raw₀.Const.modify m k f).getKey k hc = k := by
  have := zr0k_qg (Raw₀.Const.modify m k f) k hc
  rw [r0_mks] at this; split at this
  · exact (Option.some.inj this).symm
  · cases this
-- DHashMap.Raw.Const versions (a bucketless map is modified into ∅)
theorem e_gk [BEq α] [Hashable α] (a : α) : DHashMap.Raw.getKey? (∅ : DHashMap.Raw α β) a = none := by
  simp only [DHashMap.Raw.getKey?]; split
  · rename_i h; unfold Raw₀.getKey?; simp only [Array.ugetElem_eq_getElem]
    simp [EmptyCollection.emptyCollection, DHashMap.Raw.emptyWithCapacity, AssocList.getKey?]
  · rfl
theorem e_g [BEq α] [Hashable α] (a : α) : DHashMap.Raw.Const.get? (∅ : DHashMap.Raw α (fun _ => γ)) a = none := by
  simp only [DHashMap.Raw.Const.get?]; split
  · rename_i h; unfold Raw₀.Const.get?; simp only [Array.ugetElem_eq_getElem]
    simp [EmptyCollection.emptyCollection, DHashMap.Raw.emptyWithCapacity, AssocList.get?]
  · rfl
theorem drc_e1 [BEq α] [Hashable α] [EquivBEq α] (m : DHashMap.Raw α (fun _ => γ)) (k : α) (f : γ → γ) (hb : 0 < m.buckets.size) :
    DHashMap.Raw.Const.modify m k f = (Raw₀.Const.modify ⟨m, hb⟩ k f).1 := by
  simp [DHashMap.Raw.Const.modify, hb]
theorem drc_e0 [BEq α] [Hashable α] [EquivBEq α] (m : DHashMap.Raw α (fun _ => γ)) (k : α) (f : γ → γ) (hb : ¬ 0 < m.buckets.size) :
    DHashMap.Raw.Const.modify m k f = ∅ := by
  simp [DHashMap.Raw.Const.modify, hb]
theorem dr_gk_l [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : DHashMap.Raw.getKey? m.1 a = m.getKey? a := by
  simp [DHashMap.Raw.getKey?, m.2]
theorem dr_gk_l' [BEq α] [Hashable α] (m : DHashMap.Raw α β) (hb : 0 < m.buckets.size) (a : α) :
    DHashMap.Raw.getKey? m a = Raw₀.getKey? ⟨m, hb⟩ a := by
  simp [DHashMap.Raw.getKey?, hb]
theorem drc_g_l [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (a : α) : DHashMap.Raw.Const.get? m.1 a = Raw₀.Const.get? m a := by
  simp [DHashMap.Raw.Const.get?, m.2]
theorem drc_g_l' [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => γ)) (hb : 0 < m.buckets.size) (a : α) :
    DHashMap.Raw.Const.get? m a = Raw₀.Const.get? ⟨m, hb⟩ a := by
  simp [DHashMap.Raw.Const.get?, hb]
theorem dr_c_l' [BEq α] [Hashable α] (m : DHashMap.Raw α β) (hb : 0 < m.buckets.size) (a : α) :
    m.contains a = Raw₀.contains ⟨m, hb⟩ a := by
  simp [DHashMap.Raw.contains, hb]
theorem drc_gkm [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : DHashMap.Raw α (fun _ => γ)) (k k' : α) (f : γ → γ) :
    (DHashMap.Raw.Const.modify m k f).getKey? k' = if k == k' then (if k ∈ m then some k else none) else m.getKey? k' := by
  simp only [DHashMap.Raw.mem_iff_contains]
  by_cases hb : 0 < m.buckets.size
  · rw [drc_e1 _ _ _ hb, dr_gk_l, r0_mk, dr_c_l' _ hb, dr_gk_l' _ hb]
  · rw [drc_e0 _ _ _ hb, e_gk]; simp [DHashMap.Raw.getKey?, DHashMap.Raw.contains, hb]
theorem drc_gkms [BEq α] [Hashable α] [EquivBEq α] (m : DHashMap.Raw α (fun _ => γ)) (k : α) (f : γ → γ) :
    (DHashMap.Raw.Const.modify m k f).getKey? k = if k ∈ m then some k else none := by
  simp only [DHashMap.Raw.mem_iff_contains]
  by_cases hb : 0 < m.buckets.size
  · rw [drc_e1 _ _ _ hb, dr_gk_l, r0_mks, dr_c_l' _ hb]
  · rw [drc_e0 _ _ _ hb, e_gk]; simp [DHashMap.Raw.getKey?, DHashMap.Raw.contains, hb]
theorem drc_gm [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : DHashMap.Raw α (fun _ => γ)) (k k' : α) (f : γ → γ) :
    DHashMap.Raw.Const.get? (DHashMap.Raw.Const.modify m k f) k' = if k == k' then (DHashMap.Raw.Const.get? m k).map f else DHashMap.Raw.Const.get? m k' := by
  by_cases hb : 0 < m.buckets.size
  · rw [drc_e1 _ _ _ hb, drc_g_l, r0_mg, drc_g_l' _ hb, drc_g_l' _ hb]
  · rw [drc_e0 _ _ _ hb, e_g]; simp [DHashMap.Raw.Const.get?, hb]
theorem drc_gms [BEq α] [Hashable α] [EquivBEq α] (m : DHashMap.Raw α (fun _ => γ)) (k : α) (f : γ → γ) :
    DHashMap.Raw.Const.get? (DHashMap.Raw.Const.modify m k f) k = (DHashMap.Raw.Const.get? m k).map f := by
  by_cases hb : 0 < m.buckets.size
  · rw [drc_e1 _ _ _ hb, drc_g_l, r0_mgs, drc_g_l' _ hb]
  · rw [drc_e0 _ _ _ hb, e_g]; simp [DHashMap.Raw.Const.get?, hb]
theorem drc_gkdm [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : DHashMap.Raw α (fun _ => γ)) (k k' fb : α) (f : γ → γ) :
    (DHashMap.Raw.Const.modify m k f).getKeyD k' fb = if k == k' then (if k ∈ m then k else fb) else m.getKeyD k' fb := by
  rw [zdrk_dq, drc_gkm, zdrk_dq]; split <;> (try split) <;> rfl
theorem drc_gdm [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : DHashMap.Raw α (fun _ => γ)) (k k' : α) (fb : γ) (f : γ → γ) :
    DHashMap.Raw.Const.getD (DHashMap.Raw.Const.modify m k f) k' fb = if k == k' then ((DHashMap.Raw.Const.get? m k).map f).getD fb else DHashMap.Raw.Const.getD m k' fb := by
  rw [zdrc_dq, drc_gm, zdrc_dq]; split <;> rfl
theorem drc_gkdms [BEq α] [Hashable α] [EquivBEq α] (m : DHashMap.Raw α (fun _ => γ)) (k fb : α) (f : γ → γ) :
    (DHashMap.Raw.Const.modify m k f).getKeyD k fb = if k ∈ m then k else fb := by
  rw [zdrk_dq, drc_gkms]; split <;> rfl
theorem drc_gdms [BEq α] [Hashable α] [EquivBEq α] (m : DHashMap.Raw α (fun _ => γ)) (k : α) (fb : γ) (f : γ → γ) :
    DHashMap.Raw.Const.getD (DHashMap.Raw.Const.modify m k f) k fb = ((DHashMap.Raw.Const.get? m k).map f).getD fb := by
  rw [zdrc_dq, drc_gms]
theorem drc_gks [BEq α] [Hashable α] [EquivBEq α] (m : DHashMap.Raw α (fun _ => γ)) (k : α) (f : γ → γ) (hc : k ∈ DHashMap.Raw.Const.modify m k f) :
    (DHashMap.Raw.Const.modify m k f).getKey k hc = k := by
  have := zdrk_qg (DHashMap.Raw.Const.modify m k f) k hc
  rw [drc_gkms] at this; split at this
  · exact (Option.some.inj this).symm
  · cases this
end
end W5c5
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v}
-- dependent modify (LawfulBEq): bucket level, no WF
theorem dmodify_gen [BEq α] [Hashable α] [LawfulBEq α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size}
    (a : α) (f : β a → β a) :
    Raw₀.modify (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a f =
      if (bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).contains a then
        ⟨⟨s, bs.set (mkIdx bs.size h (hash a)).1.toNat
          (AssocList.modify a f (bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2))
          (mkIdx bs.size h (hash a)).2⟩, by simpa using h⟩
      else ⟨⟨s, bs⟩, h⟩ := by
  unfold Raw₀.modify; simp only [Array.ugetElem_eq_getElem, Array.uset_eq_set, Array.set_set]
theorem a_dmk [BEq α] [LawfulBEq α] (l : AssocList α β) (k k' : α) (f : β k → β k) :
    (AssocList.modify k f l).getKey? k' = if k == k' then (if l.contains k then some k else none) else l.getKey? k' := by
  induction l with
  | nil => simp [AssocList.modify, AssocList.getKey?, AssocList.contains]
  | cons e v t ih =>
    by_cases he : e = k
    · subst he
      simp only [AssocList.modify, BEq.refl, ↓reduceDIte, AssocList.getKey?, AssocList.contains, Bool.true_or, ↓reduceIte]
      by_cases h2 : (e == k') = true <;> simp [h2]
    · have he' : (e == k) = false := by simpa using he
      simp only [AssocList.modify, he', Bool.false_eq_true, ↓reduceDIte, AssocList.getKey?, AssocList.contains, Bool.false_or, ih]
      by_cases hk : k = k'
      · subst hk; simp [he']
      · simp [hk]
theorem a_dgs [BEq α] [LawfulBEq α] (l : AssocList α β) (k : α) (f : β k → β k) :
    (AssocList.modify k f l).getCast? k = (l.getCast? k).map f := by
  induction l with
  | nil => simp [AssocList.modify, AssocList.getCast?]
  | cons e v t ih =>
    by_cases he : e = k
    · subst he
      simp [AssocList.modify, AssocList.getCast?]
    · have he' : (e == k) = false := by simpa using he
      simp only [AssocList.modify, he', Bool.false_eq_true, ↓reduceDIte, AssocList.getCast?, ih]
theorem a_dgo [BEq α] [LawfulBEq α] (l : AssocList α β) (k k' : α) (f : β k → β k) (hk : (k == k') = false) :
    (AssocList.modify k f l).getCast? k' = l.getCast? k' := by
  induction l with
  | nil => simp [AssocList.modify, AssocList.getCast?]
  | cons e v t ih =>
    by_cases he : e = k
    · subst he
      simp only [AssocList.modify, BEq.refl, ↓reduceDIte, AssocList.getCast?, hk, Bool.false_eq_true]
    · have he' : (e == k) = false := by simpa using he
      simp only [AssocList.modify, he', Bool.false_eq_true, ↓reduceDIte, AssocList.getCast?, ih]
theorem a_dgn [BEq α] [LawfulBEq α] (l : AssocList α β) (k : α) (hc : ¬ l.contains k = true) :
    l.getCast? k = none := by
  induction l with
  | nil => rfl
  | cons e v t ih =>
    simp only [AssocList.contains, Bool.or_eq_true, not_or] at hc
    simp only [AssocList.getCast?, hc.1, Bool.false_eq_true, ↓reduceDIte]; exact ih hc.2
theorem r0_dmk [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k k' : α) (f : β k → β k) :
    (m.modify k f).getKey? k' = if k == k' then (if m.contains k then some k else none) else m.getKey? k' := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  by_cases hc : (bs[(mkIdx bs.size hb (hash k)).1.toNat]'(mkIdx bs.size hb (hash k)).2).contains k = true
  · rw [dmodify_gen, if_pos hc]
    unfold Raw₀.getKey? Raw₀.contains
    simp only [Array.ugetElem_eq_getElem, Array.getElem_set, mkIdx_set_toNat]
    by_cases hk : k = k'
    · subst hk
      simp only [↓reduceIte]; rw [a_dmk]; (try simp [hc])
    · have hk' : (k == k') = false := by simpa using hk
      split
      · rw [a_dmk]; simp only [hk']; simp_all
      · simp [hk']
  · rw [dmodify_gen, if_neg hc]
    unfold Raw₀.getKey? Raw₀.contains
    simp only [Array.ugetElem_eq_getElem, hc]
    by_cases hk : k = k'
    · subst hk; simp only [BEq.refl, ↓reduceIte, Bool.false_eq_true]; exact a_gkn _ _ _ (BEq.refl k) hc
    · have hk' : (k == k') = false := by simpa using hk
      simp [hk']
theorem r0_dgs [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k : α) (f : β k → β k) :
    (m.modify k f).get? k = (m.get? k).map f := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  by_cases hc : (bs[(mkIdx bs.size hb (hash k)).1.toNat]'(mkIdx bs.size hb (hash k)).2).contains k = true
  · rw [dmodify_gen, if_pos hc]
    unfold Raw₀.get?
    simp only [Array.ugetElem_eq_getElem, Array.getElem_set, mkIdx_set_toNat, if_true]
    rw [a_dgs]
  · rw [dmodify_gen, if_neg hc]
    unfold Raw₀.get?
    simp only [Array.ugetElem_eq_getElem]
    rw [a_dgn _ _ hc]; rfl
theorem r0_dgo [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k k' : α) (f : β k → β k) (hk : (k == k') = false) :
    (m.modify k f).get? k' = m.get? k' := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  by_cases hc : (bs[(mkIdx bs.size hb (hash k)).1.toNat]'(mkIdx bs.size hb (hash k)).2).contains k = true
  · rw [dmodify_gen, if_pos hc]
    unfold Raw₀.get?
    simp only [Array.ugetElem_eq_getElem, Array.getElem_set, mkIdx_set_toNat]
    split
    · rw [a_dgo _ _ _ _ hk]; simp_all
    · rfl
  · rw [dmodify_gen, if_neg hc]
-- statement forms
theorem r0_dgkdm [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k k' fb : α) (f : β k → β k) :
    (m.modify k f).getKeyD k' fb = if k == k' then (if m.contains k then k else fb) else m.getKeyD k' fb := by
  rw [zr0k_dq, r0_dmk, zr0k_dq]; split <;> (try split) <;> rfl
theorem r0_dgkdms [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k fb : α) (f : β k → β k) :
    (m.modify k f).getKeyD k fb = if m.contains k then k else fb := by
  rw [r0_dgkdm]; simp
theorem r0_dgks [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k : α) (f : β k → β k) (hc) :
    (m.modify k f).getKey k hc = k := by
  have := zr0k_qg (m.modify k f) k hc
  rw [r0_dmk] at this; simp only [BEq.refl, ↓reduceIte] at this; split at this
  · exact (Option.some.inj this).symm
  · cases this
theorem r0_dgdms [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k : α) (fb : β k) (f : β k → β k) :
    (m.modify k f).getD k fb = ((m.get? k).map f).getD fb := by
  rw [zr0g_dq, r0_dgs]
theorem r0_dgdm [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (k k' : α) (fb : β k') (f : β k → β k) :
    (m.modify k f).getD k' fb = if heq : k == k' then
        m.get? k |>.map f |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fb else m.getD k' fb := by
  by_cases hk : k = k'
  · subst hk; simp only [BEq.refl, ↓reduceDIte]; rw [r0_dgdms]; cases m.get? k <;> simp
  · have hk' : (k == k') = false := by simpa using hk
    rw [zr0g_dq, r0_dgo _ _ _ _ hk', zr0g_dq]; simp [hk']
end
end W5c5
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v}
theorem dr_e1 [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k : α) (f : β k → β k) (hb : 0 < m.buckets.size) :
    m.modify k f = (Raw₀.modify ⟨m, hb⟩ k f).1 := by
  simp [DHashMap.Raw.modify, hb]
theorem dr_e0 [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k : α) (f : β k → β k) (hb : ¬ 0 < m.buckets.size) :
    m.modify k f = ∅ := by
  simp [DHashMap.Raw.modify, hb]
theorem e_dg [BEq α] [Hashable α] [LawfulBEq α] (a : α) : DHashMap.Raw.get? (∅ : DHashMap.Raw α β) a = none := by
  simp only [DHashMap.Raw.get?]; split
  · rename_i h; unfold Raw₀.get?; simp only [Array.ugetElem_eq_getElem]
    simp [EmptyCollection.emptyCollection, DHashMap.Raw.emptyWithCapacity, AssocList.getCast?]
  · rfl
theorem dr_g_l [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α) : DHashMap.Raw.get? m.1 a = m.get? a := by
  simp [DHashMap.Raw.get?, m.2]
theorem dr_g_l' [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (hb : 0 < m.buckets.size) (a : α) :
    DHashMap.Raw.get? m a = Raw₀.get? ⟨m, hb⟩ a := by
  simp [DHashMap.Raw.get?, hb]
theorem dr_dmk [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k k' : α) (f : β k → β k) :
    (m.modify k f).getKey? k' = if k == k' then (if k ∈ m then some k else none) else m.getKey? k' := by
  simp only [DHashMap.Raw.mem_iff_contains]
  by_cases hb : 0 < m.buckets.size
  · rw [dr_e1 _ _ _ hb, dr_gk_l, r0_dmk, dr_c_l' _ hb, dr_gk_l' _ hb]
  · rw [dr_e0 _ _ _ hb, e_gk]; simp [DHashMap.Raw.getKey?, DHashMap.Raw.contains, hb]
theorem dr_dgs [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k : α) (f : β k → β k) :
    (m.modify k f).get? k = (m.get? k).map f := by
  by_cases hb : 0 < m.buckets.size
  · rw [dr_e1 _ _ _ hb, dr_g_l, r0_dgs, dr_g_l' _ hb]
  · rw [dr_e0 _ _ _ hb, e_dg]; simp [DHashMap.Raw.get?, hb]
theorem dr_dgo [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k k' : α) (f : β k → β k) (hk : (k == k') = false) :
    (m.modify k f).get? k' = m.get? k' := by
  by_cases hb : 0 < m.buckets.size
  · rw [dr_e1 _ _ _ hb, dr_g_l, r0_dgo _ _ _ _ hk, dr_g_l' _ hb]
  · rw [dr_e0 _ _ _ hb, e_dg]; simp [DHashMap.Raw.get?, hb]
theorem dr_dgkdm [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k k' fb : α) (f : β k → β k) :
    (m.modify k f).getKeyD k' fb = if k == k' then (if k ∈ m then k else fb) else m.getKeyD k' fb := by
  rw [zdrk_dq, dr_dmk, zdrk_dq]; split <;> (try split) <;> rfl
theorem dr_dgkdms [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k fb : α) (f : β k → β k) :
    (m.modify k f).getKeyD k fb = if k ∈ m then k else fb := by
  rw [dr_dgkdm]; simp
theorem dr_dgks [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k : α) (f : β k → β k) (hc : k ∈ m.modify k f) :
    (m.modify k f).getKey k hc = k := by
  have := zdrk_qg (m.modify k f) k hc
  rw [dr_dmk] at this; simp only [BEq.refl, ↓reduceIte] at this; split at this
  · exact (Option.some.inj this).symm
  · cases this
theorem dr_dgdms [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k : α) (fb : β k) (f : β k → β k) :
    (m.modify k f).getD k fb = ((m.get? k).map f).getD fb := by
  rw [zdrg_dq, dr_dgs]
theorem dr_dgdm [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (k k' : α) (fb : β k') (f : β k → β k) :
    (m.modify k f).getD k' fb = if heq : k == k' then
        m.get? k |>.map f |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fb else m.getD k' fb := by
  by_cases hk : k = k'
  · subst hk; simp only [BEq.refl, ↓reduceDIte]; rw [dr_dgdms]; cases m.get? k <;> simp
  · have hk' : (k == k') = false := by simpa using hk
    rw [zdrg_dq, dr_dgo _ _ _ _ hk', zdrg_dq]; simp [hk']
end
end W5c5
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
-- ofList without LawfulHashable: a key found for k is a key of l that is == k
theorem hm_ofl_kd [BEq α] [Hashable α] [EquivBEq α] (l : List (α × γ)) (k fb : α)
    (hc : (l.map Prod.fst).contains k = false) :
    Raw₀.getKeyD ⟨(HashMap.ofList l).inner.1, (HashMap.ofList l).inner.2.size_buckets_pos⟩ k fb = fb := by
  rw [zr0k_dq, hm_getKey?_ofList_none l k hc]; rfl
theorem tlm_insertListD [BEq α] [Hashable α] (P : ((a : α) × β a) → Prop) (l : List ((a : α) × β a)) :
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
theorem dh_ofList_raw [BEq α] [Hashable α] (l : List ((a : α) × β a)) :
    (DHashMap.ofList l).1 = (Raw₀.insertListₘ (Raw₀.emptyWithCapacity 8) l).1 := by
  show (Raw₀.insertMany _ l).1.1 = _
  rw [Raw₀.insertMany_eq_insertListₘ]; rfl
theorem dh_ofl_none [BEq α] [Hashable α] [EquivBEq α] (l : List ((a : α) × β a)) (k : α)
    (hc : (l.map Sigma.fst).contains k = false) :
    Raw₀.getKey? ⟨(DHashMap.ofList l).1, (DHashMap.ofList l).2.size_buckets_pos⟩ k = none := by
  cases hg : Raw₀.getKey? _ k with
  | none => rfl
  | some x =>
    obtain ⟨p, hp, h1, h2⟩ := raw0_getKey?_some _ k x hg
    have hx : p ∈ l := by
      have := tlm_insertListD (fun p => p ∈ l) l (Raw₀.emptyWithCapacity 8) (by simp) (fun a ha => ha)
      exact this p (by rw [← dh_ofList_raw]; exact hp)
    have : (l.map Sigma.fst).contains k = true :=
      List.contains_iff_exists_mem_beq.mpr ⟨x, List.mem_map.mpr ⟨_, hx, h1⟩, BEq.symm h2⟩
    simp_all
theorem dh_ofl_kd [BEq α] [Hashable α] [EquivBEq α] (l : List ((a : α) × β a)) (k fb : α)
    (hc : (l.map Sigma.fst).contains k = false) :
    Raw₀.getKeyD ⟨(DHashMap.ofList l).1, (DHashMap.ofList l).2.size_buckets_pos⟩ k fb = fb := by
  rw [zr0k_dq, dh_ofl_none l k hc]; rfl
-- wrappers
theorem dhc_ofl [BEq α] [Hashable α] [EquivBEq α] (l : List (α × γ)) (k fb : α)
    (hc : (l.map Prod.fst).contains k = false) : (DHashMap.Const.ofList l).getKeyD k fb = fb :=
  hm_ofl_kd l k fb hc
theorem drc_ofl_eq [BEq α] [Hashable α] (l : List (α × γ)) : DHashMap.Raw.Const.ofList l = (HashMap.ofList l).inner.1 := by
  simp only [DHashMap.Raw.Const.ofList, DHashMap.Raw.Const.insertMany]; split
  · rfl
  · rename_i h; exact absurd (Raw₀.emptyWithCapacity 8).2 h
theorem dr_ofl_eq [BEq α] [Hashable α] (l : List ((a : α) × β a)) : DHashMap.Raw.ofList l = (DHashMap.ofList l).1 := by
  simp only [DHashMap.Raw.ofList, DHashMap.Raw.insertMany]; split
  · rfl
  · rename_i h; exact absurd (Raw₀.emptyWithCapacity 8).2 h
theorem drc_ofl [BEq α] [Hashable α] [EquivBEq α] (l : List (α × γ)) (k fb : α)
    (hc : (l.map Prod.fst).contains k = false) : (DHashMap.Raw.Const.ofList l).getKeyD k fb = fb := by
  rw [drc_ofl_eq]; unfold DHashMap.Raw.getKeyD; rw [dif_pos (HashMap.ofList l).inner.2.size_buckets_pos]
  exact hm_ofl_kd l k fb hc
theorem dh_ofl [BEq α] [Hashable α] [EquivBEq α] (l : List ((a : α) × β a)) (k fb : α)
    (hc : (l.map Sigma.fst).contains k = false) : (DHashMap.ofList l).getKeyD k fb = fb :=
  dh_ofl_kd l k fb hc
theorem dr_ofl [BEq α] [Hashable α] [EquivBEq α] (l : List ((a : α) × β a)) (k fb : α)
    (hc : (l.map Sigma.fst).contains k = false) : (DHashMap.Raw.ofList l).getKeyD k fb = fb := by
  rw [dr_ofl_eq]; unfold DHashMap.Raw.getKeyD; rw [dif_pos (DHashMap.ofList l).2.size_buckets_pos]
  exact dh_ofl_kd l k fb hc
theorem hmr_ofl [BEq α] [Hashable α] [EquivBEq α] (l : List (α × γ)) (k fb : α)
    (hc : (l.map Prod.fst).contains k = false) : (HashMap.Raw.ofList l).getKeyD k fb = fb :=
  drc_ofl l k fb hc
end
end W5c5
open W5c5

/-! ## From `checks/W6c0Hand.lean` -/
namespace W6c0
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
-- size field: modify never changes it (no laws, no WF)
theorem r0c_ms {γ : Type v} (m : Raw₀ α (fun _ => γ)) (k : α) (f : γ → γ) :
    (Raw₀.Const.modify m k f).1.size = m.1.size := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m; unfold Raw₀.Const.modify; dsimp only; split <;> rfl
theorem r0_ms [LawfulBEq α] (m : Raw₀ α β) (k : α) (f : β k → β k) :
    (m.modify k f).1.size = m.1.size := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m; unfold Raw₀.modify; dsimp only; split <;> rfl
theorem drc_ms [EquivBEq α] {γ : Type v} (m : DHashMap.Raw α (fun _ => γ)) (hb : 0 < m.buckets.size) (k : α) (f : γ → γ) :
    (DHashMap.Raw.Const.modify m k f).size = m.size := by
  unfold DHashMap.Raw.Const.modify; rw [dite_eq_left hb]; exact r0c_ms _ _ _
theorem dr_ms [LawfulBEq α] (m : DHashMap.Raw α β) (hb : 0 < m.buckets.size) (k : α) (f : β k → β k) :
    (m.modify k f).size = m.size := by
  unfold DHashMap.Raw.modify; rw [dite_eq_left hb]; exact r0_ms _ _ _
-- getKey? returns a stored key x with x == a (no laws)
theorem al_kb (l : AssocList α β) (a : α) : (l.getKey? a).all (· == a) := by
  induction l with
  | nil => rfl
  | cons k v l ih => unfold AssocList.getKey?; split <;> simp_all
theorem r0_kb (m : Raw₀ α β) (a : α) : (m.getKey? a).all (· == a) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m; exact al_kb _ _
theorem dr_kb (m : DHashMap.Raw α β) (a : α) : (m.getKey? a).all (· == a) := by
  unfold DHashMap.Raw.getKey?; split
  · exact r0_kb _ _
  · rfl
-- insertIfNew changes the size field exactly as contains predicts (copy of W5c1.r0_sin)
theorem r0_sin (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insertIfNew a b).1.size = if m.contains a then m.1.size else m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.insertIfNew Raw₀.contains; dsimp only
  split <;> simp [Raw₀.size_expandIfNecessary]
theorem r0u_le (m : Raw₀ α (fun _ => Unit)) (l : List α) :
    (Raw₀.Const.insertManyIfNewUnit m l).1.1.size ≤ m.1.size + l.length := by
  rw [Raw₀.Const.insertManyIfNewUnit_eq_insertListIfNewUnitₘ]
  induction l generalizing m with
  | nil => simp [Raw₀.Const.insertListIfNewUnitₘ]
  | cons hd tl ih =>
    simp only [Raw₀.Const.insertListIfNewUnitₘ, List.length_cons]
    have h1 := ih (m.insertIfNew hd ())
    have h2 := r0_sin m hd ()
    split at h2 <;> omega
theorem dru_le (m : DHashMap.Raw α (fun _ => Unit)) (l : List α) :
    (DHashMap.Raw.Const.insertManyIfNewUnit m l).size ≤ m.size + l.length := by
  unfold DHashMap.Raw.Const.insertManyIfNewUnit; split
  · exact r0u_le ⟨m, _⟩ l
  · omega
theorem a_kbq [Inhabited α] (l : AssocList α β) (a : α) : l.getKey! a = (l.getKey? a).get! := by
  induction l with
  | nil => rfl
  | cons k v t ih => cases hk : (k == a) <;> simp_all [AssocList.getKey!, AssocList.getKey?]
theorem r0_kbq (m : Raw₀ α β) (a : α) [Inhabited α] :
    Raw₀.getKey! m a = (Raw₀.getKey? m a).get! := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey? Raw₀.getKey!; simp only [Array.ugetElem_eq_getElem]; exact a_kbq _ _
theorem dr_kbq (m : DHashMap.Raw α β) (a : α) [Inhabited α] :
    DHashMap.Raw.getKey! m a = (DHashMap.Raw.getKey? m a).get! := by
  unfold DHashMap.Raw.getKey! DHashMap.Raw.getKey?; split
  · exact r0_kbq _ _
  · rfl
theorem r0_ck (m : Raw₀ α β) (a : α) :
    m.contains a = (m.getKey? a).isSome := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey? Raw₀.contains
  simp only [AssocList.getKey?_eq, AssocList.contains_eq]; exact Std.Internal.List.containsKey_eq_isSome_getKey?
theorem dr_ck (m : DHashMap.Raw α β) (a : α) :
    m.contains a = (m.getKey? a).isSome := by
  unfold DHashMap.Raw.contains DHashMap.Raw.getKey?; split
  · exact r0_ck _ _
  · rfl
theorem dr_sin (m : DHashMap.Raw α β) (hb : 0 < m.buckets.size) (a : α) (b : β a) :
    (m.insertIfNew a b).size = if a ∈ m then m.size else m.size + 1 := by
  have := r0_sin ⟨m, hb⟩ a b
  simp only [DHashMap.Raw.mem_iff_contains]
  unfold DHashMap.Raw.insertIfNew DHashMap.Raw.contains; simp only [hb, ↓reduceDIte]; exact this
end
end W6c0
macro "w6bp" : tactic => `(tactic| first
  | (apply DHashMap.Raw.WF.size_buckets_pos; assumption)
  | (apply DHashMap.Raw.WF.size_buckets_pos; apply HashMap.Raw.WF.out; assumption))
macro "w6ev" : tactic => `(tactic| first
  | decide +kernel
  | (hm_eval; done)
  | (hm_eval; decide +kernel)
  | (hm_eval_raw; done)
  | (w1c0_raw; done)
  | (simp; done))
open W6c0
namespace W6c0
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
-- Const.modify renames the first matching key to a; under EquivBEq lookups see the same keys
theorem al_cm [EquivBEq α] (l : AssocList α (fun _ => γ)) (a k' : α) (f : γ → γ) :
    (AssocList.Const.modify a f l).contains k' = l.contains k' := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    unfold AssocList.Const.modify; split
    · rename_i hk; simp only [AssocList.contains]; rw [BEq.congr_left hk]
    · simp only [AssocList.contains, ih]
theorem al_km [EquivBEq α] (l : AssocList α (fun _ => γ)) (a : α) (f : γ → γ) :
    (AssocList.Const.modify a f l).getKey? a = if l.contains a then some a else none := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    unfold AssocList.Const.modify; split
    · rename_i hk; simp [AssocList.getKey?, AssocList.contains, hk]
    · rename_i hk; simp only [AssocList.getKey?, AssocList.contains, hk, ih, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
theorem ald_cm [LawfulBEq α] (l : AssocList α β) (a k' : α) (f : β a → β a) :
    (l.modify a f).contains k' = l.contains k' := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    unfold AssocList.modify; split
    · rename_i hk; simp only [AssocList.contains]; rw [BEq.congr_left hk]
    · simp only [AssocList.contains, ih]
theorem ald_km [LawfulBEq α] (l : AssocList α β) (a : α) (f : β a → β a) :
    (l.modify a f).getKey? a = if l.contains a then some a else none := by
  induction l with
  | nil => rfl
  | cons k v t ih =>
    unfold AssocList.modify; split
    · rename_i hk; simp [AssocList.getKey?, AssocList.contains, hk]
    · rename_i hk; simp only [AssocList.getKey?, AssocList.contains, hk, ih, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
theorem set_ix {X : Type w} (bs : Array X) (i : Nat) (hi : i < bs.size) (x : X) (hb' : 0 < (bs.set i x hi).size)
    (hb : 0 < bs.size) (h : UInt64) :
    (bs.set i x hi)[(mkIdx (bs.set i x hi).size hb' h).1.toNat]'((mkIdx _ hb' h).2) =
      if i = (mkIdx bs.size hb h).1.toNat then x else bs[(mkIdx bs.size hb h).1.toNat]'(mkIdx bs.size hb h).2 := by
  have e : ∀ n n' (_ : n = n') (h1 : 0 < n) (h2 : 0 < n'), (mkIdx n h1 h).1 = (mkIdx n' h2 h).1 := by
    intros; subst_vars; rfl
  have := e _ _ (Array.size_set ..) hb' hb
  simp only [this]
  rw [Array.getElem_set]
theorem al_kn (l : AssocList α β) (a : α) (h : l.contains a = false) : l.getKey? a = none := by
  have : l.contains a = (l.getKey? a).isSome := by
    simp only [AssocList.getKey?_eq, AssocList.contains_eq]; exact Std.Internal.List.containsKey_eq_isSome_getKey?
  cases e : l.getKey? a <;> simp_all
theorem r0c_cm [EquivBEq α] (m : Raw₀ α (fun _ => γ)) (a k' : α) (f : γ → γ) :
    (Raw₀.Const.modify m a f).contains k' = m.contains k' := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [cmodify_gen]; split
  · simp only [contains_gen]; rw [set_ix _ _ _ _ _ hb]
    split
    · rename_i he
      have he' : (mkIdx bs.size hb (hash a)).1.toNat = (mkIdx bs.size hb (hash k')).1.toNat := he
      simp only [← he']; exact al_cm _ _ _ _
    · rfl
  · rfl
theorem r0c_km [EquivBEq α] (m : Raw₀ α (fun _ => γ)) (a : α) (f : γ → γ) :
    (Raw₀.Const.modify m a f).getKey? a = if m.contains a then some a else none := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [cmodify_gen, contains_gen]; split
  · rename_i hc; simp only [Raw₀.getKey?, Array.ugetElem_eq_getElem]; rw [set_ix _ _ _ _ _ hb, ite_cond_eq_true _ _ (eq_true rfl)]
    rw [al_km, ite_cond_eq_true _ _ (eq_true hc)]
  · rename_i hc; simp only [Raw₀.getKey?, Array.ugetElem_eq_getElem]
    exact al_kn _ _ (by simpa using hc)
end
end W6c0
namespace W6c0
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
theorem modify_gen [LawfulBEq α] {s : Nat} {bs : Array (AssocList α β)} {h : 0 < bs.size}
    (a : α) (f : β a → β a) :
    Raw₀.modify (⟨⟨s, bs⟩, h⟩ : Raw₀ α β) a f =
      if (bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).contains a then
        ⟨⟨s, bs.set (mkIdx bs.size h (hash a)).1.toNat
          ((bs[(mkIdx bs.size h (hash a)).1.toNat]'(mkIdx bs.size h (hash a)).2).modify a f)
          (mkIdx bs.size h (hash a)).2⟩, by simpa using h⟩
      else ⟨⟨s, bs⟩, h⟩ := by
  unfold Raw₀.modify; simp only [Array.ugetElem_eq_getElem, Array.uset_eq_set, Array.set_set]
theorem r0_cm [LawfulBEq α] (m : Raw₀ α β) (a k' : α) (f : β a → β a) :
    (m.modify a f).contains k' = m.contains k' := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [modify_gen]; split
  · simp only [contains_gen]; rw [set_ix _ _ _ _ _ hb]
    split
    · rename_i he
      have he' : (mkIdx bs.size hb (hash a)).1.toNat = (mkIdx bs.size hb (hash k')).1.toNat := he
      simp only [← he']; exact ald_cm _ _ _ _
    · rfl
  · rfl
theorem r0_km [LawfulBEq α] (m : Raw₀ α β) (a : α) (f : β a → β a) :
    (m.modify a f).getKey? a = if m.contains a then some a else none := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [modify_gen, contains_gen]; split
  · rename_i hc; simp only [Raw₀.getKey?, Array.ugetElem_eq_getElem]; rw [set_ix _ _ _ _ _ hb, ite_cond_eq_true _ _ (eq_true rfl)]
    rw [ald_km, ite_cond_eq_true _ _ (eq_true hc)]
  · rename_i hc; simp only [Raw₀.getKey?, Array.ugetElem_eq_getElem]
    exact al_kn _ _ (by simpa using hc)
-- getKey! versions
theorem r0c_k!m [EquivBEq α] [Inhabited α] (m : Raw₀ α (fun _ => γ)) (a : α) (f : γ → γ) :
    (Raw₀.Const.modify m a f).getKey! a = if m.contains a then a else default := by
  rw [r0_kbq, r0c_km]; split <;> rfl
theorem r0_k!m [LawfulBEq α] [Inhabited α] (m : Raw₀ α β) (a : α) (f : β a → β a) :
    (m.modify a f).getKey! a = if m.contains a then a else default := by
  rw [r0_kbq, r0_km]; split <;> rfl
-- raw wrappers (a bucketless map is sent to ∅, where every lookup fails)
theorem dr_c0 (m : Raw₀ α β) (a : α) : m.1.contains a = m.contains a := by
  unfold DHashMap.Raw.contains; rw [dite_eq_left m.2]
theorem dr_k0 (m : Raw₀ α β) (a : α) : m.1.getKey? a = m.getKey? a := by
  unfold DHashMap.Raw.getKey?; rw [dite_eq_left m.2]
theorem dr_k!0 [Inhabited α] (m : Raw₀ α β) (a : α) : m.1.getKey! a = m.getKey! a := by
  unfold DHashMap.Raw.getKey!; rw [dite_eq_left m.2]
theorem dr_cnb (m : DHashMap.Raw α β) (hb : ¬ 0 < m.buckets.size) (a : α) : m.contains a = false := by
  unfold DHashMap.Raw.contains; rw [dite_eq_right hb]
theorem drc_cm [EquivBEq α] (m : DHashMap.Raw α (fun _ => γ)) (a k' : α) (f : γ → γ) :
    (DHashMap.Raw.Const.modify m a f).contains k' = m.contains k' := by
  unfold DHashMap.Raw.Const.modify; split
  · rename_i hb; rw [dr_c0, r0c_cm]; unfold DHashMap.Raw.contains; rw [dite_eq_left hb]
  · rename_i hb; rw [dr_cnb _ hb]; exact DHashMap.Raw.contains_emptyWithCapacity
theorem dr_knb (m : DHashMap.Raw α β) (hb : ¬ 0 < m.buckets.size) (a : α) : m.getKey? a = none := by
  unfold DHashMap.Raw.getKey?; rw [dite_eq_right hb]
theorem dr_cm [LawfulBEq α] (m : DHashMap.Raw α β) (a k' : α) (f : β a → β a) :
    (m.modify a f).contains k' = m.contains k' := by
  unfold DHashMap.Raw.modify; split
  · rename_i hb; rw [dr_c0, r0_cm]; unfold DHashMap.Raw.contains; rw [dite_eq_left hb]
  · rename_i hb; rw [dr_cnb _ hb]; exact DHashMap.Raw.contains_emptyWithCapacity
theorem drc_km [EquivBEq α] (m : DHashMap.Raw α (fun _ => γ)) (a : α) (f : γ → γ) :
    (DHashMap.Raw.Const.modify m a f).getKey? a = if a ∈ m then some a else none := by
  simp only [DHashMap.Raw.mem_iff_contains]
  unfold DHashMap.Raw.Const.modify; split
  · rename_i hb; rw [dr_k0, r0c_km]; unfold DHashMap.Raw.contains; rw [dite_eq_left hb]
  · rename_i hb; simp only [dr_cnb _ hb, Bool.false_eq_true, ↓reduceIte]; exact DHashMap.Raw.getKey?_emptyWithCapacity
theorem dr_km [LawfulBEq α] (m : DHashMap.Raw α β) (a : α) (f : β a → β a) :
    (m.modify a f).getKey? a = if a ∈ m then some a else none := by
  simp only [DHashMap.Raw.mem_iff_contains]
  unfold DHashMap.Raw.modify; split
  · rename_i hb; rw [dr_k0, r0_km]; unfold DHashMap.Raw.contains; rw [dite_eq_left hb]
  · rename_i hb; simp only [dr_cnb _ hb, Bool.false_eq_true, ↓reduceIte]; exact DHashMap.Raw.getKey?_emptyWithCapacity
theorem drc_k!m [EquivBEq α] [Inhabited α] (m : DHashMap.Raw α (fun _ => γ)) (a : α) (f : γ → γ) :
    (DHashMap.Raw.Const.modify m a f).getKey! a = if a ∈ m then a else default := by
  rw [dr_kbq, drc_km]; split <;> rfl
theorem dr_k!m [LawfulBEq α] [Inhabited α] (m : DHashMap.Raw α β) (a : α) (f : β a → β a) :
    (m.modify a f).getKey! a = if a ∈ m then a else default := by
  rw [dr_kbq, dr_km]; split <;> rfl
end
end W6c0
namespace W6c0
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
theorem al_kmg [EquivBEq α] (l : AssocList α (fun _ => γ)) (a k' : α) (f : γ → γ) :
    (AssocList.Const.modify a f l).getKey? k' =
      if a == k' then (if l.contains a then some a else none) else l.getKey? k' := by
  induction l with
  | nil => simp [AssocList.Const.modify, AssocList.getKey?]
  | cons s v t ih =>
    unfold AssocList.Const.modify; split
    · rename_i hs
      have e : (s == k') = (a == k') := by
        apply Bool.eq_iff_iff.2; constructor
        · intro h1; exact BEq.trans (BEq.symm hs) h1
        · intro h2; exact BEq.trans hs h2
      cases ha : (a == k') <;> simp_all [AssocList.getKey?, AssocList.contains]
    · rename_i hs
      have tr : (s == k') = true → (a == k') = true → (s == a) = true := fun h1 h2 => BEq.trans h1 (BEq.symm h2)
      cases ha : (a == k') <;> cases hsk : (s == k') <;> simp_all [AssocList.getKey?, AssocList.contains]
theorem ald_kmg [LawfulBEq α] (l : AssocList α β) (a k' : α) (f : β a → β a) (hne : (a == k') = false) :
    (l.modify a f).getKey? k' = l.getKey? k' := by
  induction l with
  | nil => rfl
  | cons s v t ih =>
    unfold AssocList.modify; split
    · rename_i hs
      have e : (s == k') = (a == k') := by
        apply Bool.eq_iff_iff.2; constructor
        · intro h1; exact BEq.trans (BEq.symm hs) h1
        · intro h2; exact BEq.trans hs h2
      simp_all [AssocList.getKey?]
    · simp_all [AssocList.getKey?]
theorem r0c_kmg [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => γ)) (a k' : α) (f : γ → γ) :
    (Raw₀.Const.modify m a f).getKey? k' =
      if a == k' then (if m.contains a then some a else none) else m.getKey? k' := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have hidx : (a == k') = true → (mkIdx bs.size hb (hash a)).1.toNat = (mkIdx bs.size hb (hash k')).1.toNat := by
    intro h; rw [hash_eq h]
  rw [cmodify_gen, contains_gen]; split
  · rename_i hc; simp only [Raw₀.getKey?, Array.ugetElem_eq_getElem]; rw [set_ix _ _ _ _ _ hb]
    split
    · rename_i he
      have he' : (mkIdx bs.size hb (hash a)).1.toNat = (mkIdx bs.size hb (hash k')).1.toNat := he
      simp only [← he']; rw [al_kmg]; simp only [hc, ite_true]
    · rename_i he
      cases ha : (a == k')
      · rfl
      · exact absurd (hidx ha) he
  · rename_i hc; simp only [Raw₀.getKey?, Array.ugetElem_eq_getElem]
    cases ha : (a == k')
    · rfl
    · simp only [Bool.not_eq_true] at hc
      simp only [ite_true]
      have he := hidx ha
      simp only [← he]
      rw [AssocList.getKey?_eq, ← Std.Internal.List.getKey?_congr ha, ← AssocList.getKey?_eq]
      exact al_kn _ _ hc
theorem r0c_k!mg [EquivBEq α] [LawfulHashable α] [Inhabited α] (m : Raw₀ α (fun _ => γ)) (a k' : α) (f : γ → γ) :
    (Raw₀.Const.modify m a f).getKey! k' =
      if a == k' then (if m.contains a then a else default) else m.getKey! k' := by
  rw [r0_kbq, r0c_kmg, r0_kbq]; split <;> (try split) <;> rfl
end
end W6c0
namespace W6c0
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
theorem r0_kmg [LawfulBEq α] (m : Raw₀ α β) (a k' : α) (f : β a → β a) (hne : (a == k') = false) :
    (m.modify a f).getKey? k' = m.getKey? k' := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [modify_gen]; split
  · simp only [Raw₀.getKey?, Array.ugetElem_eq_getElem]; rw [set_ix _ _ _ _ _ hb]
    split
    · rename_i he
      have he' : (mkIdx bs.size hb (hash a)).1.toNat = (mkIdx bs.size hb (hash k')).1.toNat := he
      simp only [← he']; exact ald_kmg _ _ _ _ hne
    · rfl
  · rfl
theorem r0_k!mg [LawfulBEq α] [Inhabited α] (m : Raw₀ α β) (a k' : α) (f : β a → β a) :
    (m.modify a f).getKey! k' =
      if a == k' then (if m.contains a then a else default) else m.getKey! k' := by
  cases ha : (a == k')
  · rw [r0_kbq, r0_kmg _ _ _ _ ha, ← r0_kbq]; rfl
  · have := eq_of_beq ha; subst this; rw [r0_k!m]; rfl
theorem drc_k!mg [EquivBEq α] [LawfulHashable α] [Inhabited α] (m : DHashMap.Raw α (fun _ => γ)) (a k' : α) (f : γ → γ) :
    (DHashMap.Raw.Const.modify m a f).getKey! k' =
      if a == k' then (if a ∈ m then a else default) else m.getKey! k' := by
  simp only [DHashMap.Raw.mem_iff_contains]
  unfold DHashMap.Raw.Const.modify; split
  · rename_i hb; rw [dr_k!0, r0c_k!mg]; unfold DHashMap.Raw.contains DHashMap.Raw.getKey!; rw [dite_eq_left hb, dite_eq_left hb]
  · rename_i hb; rw [dr_cnb _ hb, dr_kbq, DHashMap.Raw.getKey?_empty, dr_kbq, dr_knb _ hb]
    simp only [Bool.false_eq_true, ↓reduceIte, Option.get!_none, ite_self]
theorem dr_k!mg [LawfulBEq α] [Inhabited α] (m : DHashMap.Raw α β) (a k' : α) (f : β a → β a) :
    (m.modify a f).getKey! k' =
      if a == k' then (if a ∈ m then a else default) else m.getKey! k' := by
  simp only [DHashMap.Raw.mem_iff_contains]
  unfold DHashMap.Raw.modify; split
  · rename_i hb; rw [dr_k!0, r0_k!mg]; unfold DHashMap.Raw.contains DHashMap.Raw.getKey!; rw [dite_eq_left hb, dite_eq_left hb]
  · rename_i hb; rw [dr_cnb _ hb, dr_kbq, DHashMap.Raw.getKey?_empty, dr_kbq, dr_knb _ hb]
    simp only [Bool.false_eq_true, ↓reduceIte, Option.get!_none, ite_self]
end
end W6c0
namespace W6c0
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
-- a key k that no stored key matches is not found (any hash function); ofList only stores keys of l
theorem r0_nc [EquivBEq α] (m : Raw₀ α β) (k : α) (hk : ∀ p ∈ toListModel m.1.buckets, (k == p.1) = false) :
    m.contains k = false := by
  cases hc : m.contains k
  · rfl
  · obtain ⟨p, hp, -, h2⟩ := raw0_getKey_mem m k hc
    have := hk p hp; rw [BEq.symm h2] at this; exact absurd this (by simp)
theorem r0_nk [EquivBEq α] (m : Raw₀ α β) (k : α) (hk : ∀ p ∈ toListModel m.1.buckets, (k == p.1) = false) :
    m.getKey? k = none := by
  have h1 := r0_ck m k; rw [r0_nc m k hk] at h1
  cases e : m.getKey? k with
  | none => rfl
  | some x => rw [e] at h1; exact absurd h1 (by simp)
theorem r0_nk! [EquivBEq α] [Inhabited α] (m : Raw₀ α β) (k : α) (hk : ∀ p ∈ toListModel m.1.buckets, (k == p.1) = false) :
    m.getKey! k = default := by
  rw [r0_kbq, r0_nk m k hk]; rfl
theorem r0c_ngD [EquivBEq α] (m : Raw₀ α (fun _ => γ)) (k : α) (fb : γ)
    (hk : ∀ p ∈ toListModel m.1.buckets, (k == p.1) = false) : Raw₀.Const.getD m k fb = fb := by
  have hc := r0_nc m k hk
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.Const.getD; unfold Raw₀.contains at hc
  simp only [Array.ugetElem_eq_getElem] at hc ⊢
  rw [AssocList.getD_eq]; rw [AssocList.contains_eq] at hc
  exact Std.Internal.List.getValueD_eq_fallback hc
theorem r0_nkD [EquivBEq α] (m : Raw₀ α β) (k : α) (fb : α)
    (hk : ∀ p ∈ toListModel m.1.buckets, (k == p.1) = false) : m.getKeyD k fb = fb := by
  have hc := r0_nc m k hk
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKeyD; unfold Raw₀.contains at hc
  simp only [Array.ugetElem_eq_getElem] at hc ⊢
  rw [AssocList.getKeyD_eq]; rw [AssocList.contains_eq] at hc
  exact Std.Internal.List.getKeyD_eq_fallback hc
theorem dr_nk [EquivBEq α] (m : DHashMap.Raw α β) (k : α) (hk : ∀ p ∈ toListModel m.buckets, (k == p.1) = false) :
    m.getKey? k = none := by
  unfold DHashMap.Raw.getKey?; split
  · exact r0_nk ⟨m, _⟩ k hk
  · rfl
theorem dr_nk! [EquivBEq α] [Inhabited α] (m : DHashMap.Raw α β) (k : α)
    (hk : ∀ p ∈ toListModel m.buckets, (k == p.1) = false) : m.getKey! k = default := by
  rw [dr_kbq, dr_nk m k hk]; rfl
theorem drc_ngD [EquivBEq α] (m : DHashMap.Raw α (fun _ => γ)) (k : α) (fb : γ)
    (hk : ∀ p ∈ toListModel m.buckets, (k == p.1) = false) : DHashMap.Raw.Const.getD m k fb = fb := by
  unfold DHashMap.Raw.Const.getD; split
  · exact r0c_ngD ⟨m, _⟩ k fb hk
  · rfl
theorem dr_nkD [EquivBEq α] (m : DHashMap.Raw α β) (k : α) (fb : α)
    (hk : ∀ p ∈ toListModel m.buckets, (k == p.1) = false) : m.getKeyD k fb = fb := by
  unfold DHashMap.Raw.getKeyD; split
  · exact r0_nkD ⟨m, _⟩ k fb hk
  · rfl
theorem lst {δ : Type w} (f : δ → α) (l : List δ) (k : α) (h : (l.map f).contains k = false) :
    ∀ x ∈ l, (k == f x) = false := by
  intro x hx
  cases h' : (k == f x)
  · rfl
  · have : (l.map f).contains k = true := List.contains_iff_exists_mem_beq.2 ⟨f x, List.mem_map_of_mem hx, h'⟩
    simp_all
theorem drc_ofl_keys (l : List (α × γ)) (k : α) (h : (l.map Prod.fst).contains k = false) :
    ∀ p ∈ toListModel (DHashMap.Raw.Const.ofList l).buckets, (k == p.1) = false := by
  have e : DHashMap.Raw.Const.ofList l = (Raw₀.Const.insertListₘ (Raw₀.emptyWithCapacity 8) l).1 := hmr_ofList_raw l
  rw [e]; exact tlm_insertList (fun p => (k == p.1) = false) l _ (by simp) (fun a ha => lst Prod.fst l k h a ha)
theorem dc_ofl_keys (l : List (α × γ)) (k : α) (h : (l.map Prod.fst).contains k = false) :
    ∀ p ∈ toListModel (DHashMap.Const.ofList l).1.buckets, (k == p.1) = false := by
  have e : (DHashMap.Const.ofList l).1 = (Raw₀.Const.insertListₘ (Raw₀.emptyWithCapacity 8) l).1 := hm_ofList_raw l
  rw [e]; exact tlm_insertList (fun p => (k == p.1) = false) l _ (by simp) (fun a ha => lst Prod.fst l k h a ha)
theorem dr_ofl_keys (l : List ((a : α) × β a)) (k : α) (h : (l.map Sigma.fst).contains k = false) :
    ∀ p ∈ toListModel (DHashMap.Raw.ofList l).buckets, (k == p.1) = false :=
  fun p hp => lst Sigma.fst l k h p (w4c3_dr_entries l p hp)
theorem dm_ofl_keys (l : List ((a : α) × β a)) (k : α) (h : (l.map Sigma.fst).contains k = false) :
    ∀ p ∈ toListModel (DHashMap.ofList l).1.buckets, (k == p.1) = false :=
  fun p hp => lst Sigma.fst l k h p (w4c3_dm_entries l p hp)
theorem hsr_ofl_keys (l : List α) (k : α) (h : l.contains k = false) :
    ∀ p ∈ toListModel (HashSet.Raw.ofList l).inner.inner.buckets, (k == p.1) = false := by
  rw [hsr_ofList_raw]
  exact tlm_insertListIfNewUnit (fun p => (k == p.1) = false) l _ (by simp)
    (fun a ha => lst id l k (by simpa using h) a ha)
end
end W6c0

/-! ## From `checks/W6c1Hand.lean` -/
namespace W6c1A
variable {α : Type u} [BEq α] [Hashable α]
export W5c4 (al_gs)
export W5c4 (al_ks)
export W5c4 (r0c_g!D)
export W5c4 (r0_k!D)
export W5c4 (r0c_cs)
export W5c4 (r0_csc)
export W5c4 (r0_ck)
export W5c4 (r0c_gs)
export W5c4 (r0_ks)
export W5c4 (al_gcs)
export W5c4 (r0_gs)
export W5c4 (r0_g!D)
export W5c4 (drc_g!D)
export W5c4 (dr_g!D)
export W5c4 (dr_k!D)
export W5c4 (drc_cs)
export W5c4 (dr_csc)
export W5c4 (dr_ck)
export W5c4 (drc_gs)
export W5c4 (dr_gs)
export W5c4 (dr_ks)
end W6c1A
namespace W6c1B
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
export W5c3 (a_cbq)
export W5c3 (a_cdq)
export W5c3 (a_cqg)
export W5c3 (a_kbq)
export W5c3 (a_kdq)
export W5c3 (a_kqg)
export W5c3 (a_gbq)
export W5c3 (a_gdq)
export W5c3 (a_gqg)
export W5c3 (a_cgb)
export W5c3 (a_cgd)
export W5c3 (a_kgb)
export W5c3 (a_kgd)
export W5c3 (a_ggb)
export W5c3 (a_ggd)
export W5c3 (zr0c_bq)
export W5c3 (zdrc_bq)
export W5c3 (zr0c_dq)
export W5c3 (zdrc_dq)
export W5c3 (zr0c_gb)
export W5c3 (zdrc_gb)
export W5c3 (zr0c_gd)
export W5c3 (zdrc_gd)
export W5c3 (zr0c_qg)
export W5c3 (zdrc_qg)
export W5c3 (zr0g_bq)
export W5c3 (zdrg_bq)
export W5c3 (zr0g_dq)
export W5c3 (zdrg_dq)
export W5c3 (zr0g_gb)
export W5c3 (zdrg_gb)
export W5c3 (zr0g_gd)
export W5c3 (zdrg_gd)
export W5c3 (zr0g_qg)
export W5c3 (zdrg_qg)
export W5c3 (zr0k_bq)
export W5c3 (zdrk_bq)
export W5c3 (zr0k_dq)
export W5c3 (zdrk_dq)
export W5c3 (zr0k_gb)
export W5c3 (zdrk_gb)
export W5c3 (zr0k_gd)
export W5c3 (zdrk_gd)
export W5c3 (zr0k_qg)
export W5c3 (zdrk_qg)
end
end W6c1B
set_option linter.unusedSimpArgs false
namespace W6c1C
variable {α : Type u} {β : α → Type v}
export W5c1 (r0_si)
export W5c1 (r0_sin)
export W5c1 (r0_se)
export W5c1 (r0_sle)
export W5c1 (r0_lse)
export W5c1 (r0_sil)
export W5c1 (r0_sinl)
export W5c1 (r0_lsi)
export W5c1 (r0_lsin)
export W5c1 (r0_ie)
end W6c1C
namespace W6c1
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem dr_sinl (m : DHashMap.Raw α β) (a : α) (b : β a) : (m.insertIfNew a b).size ≤ m.size + 1 := by
  unfold DHashMap.Raw.insertIfNew; split
  · exact W6c1C.r0_sinl ⟨m, _⟩ a b
  · omega
theorem dr_lsin (m : DHashMap.Raw α β) (a : α) (b : β a) : m.size ≤ (m.insertIfNew a b).size := by
  unfold DHashMap.Raw.insertIfNew; split
  · exact W6c1C.r0_lsin ⟨m, _⟩ a b
  · omega
theorem r0_szmap {γ : α → Type w} (f : (a : α) → β a → γ a) (m : Raw₀ α β) : (m.map f).1.size = m.1.size := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m; rfl
theorem r0_iemap {γ : α → Type w} (f : (a : α) → β a → γ a) (m : Raw₀ α β) : (m.map f).1.isEmpty = m.1.isEmpty := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m; rfl
theorem dr_szmap {γ : α → Type w} (f : (a : α) → β a → γ a) (m : DHashMap.Raw α β) (h : 0 < m.buckets.size) :
    (m.map f).size = m.size := by
  unfold DHashMap.Raw.map; rw [dif_pos h]; exact r0_szmap f ⟨m, h⟩
theorem dr_iemap {γ : α → Type w} (f : (a : α) → β a → γ a) (m : DHashMap.Raw α β) (h : 0 < m.buckets.size) :
    (m.map f).isEmpty = m.isEmpty := by
  unfold DHashMap.Raw.map; rw [dif_pos h]; exact r0_iemap f ⟨m, h⟩
end W6c1
namespace W6c1
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem dr_szw {γ : α → Type w} (f : (a : α) → β a → γ a) (m : DHashMap.Raw α β) (h : m.WF) :
    (m.map f).size = m.size := dr_szmap f m h.size_buckets_pos
theorem dr_iew {γ : α → Type w} (f : (a : α) → β a → γ a) (m : DHashMap.Raw α β) (h : m.WF) :
    (m.map f).isEmpty = m.isEmpty := dr_iemap f m h.size_buckets_pos
theorem hmr_szw {γ : Type v} {δ : Type w} (f : α → γ → δ) (m : HashMap.Raw α γ) (h : m.WF) :
    (m.map f).size = m.size := dr_szmap _ m.inner h.out.size_buckets_pos
theorem hmr_iew {γ : Type v} {δ : Type w} (f : α → γ → δ) (m : HashMap.Raw α γ) (h : m.WF) :
    (m.map f).isEmpty = m.isEmpty := dr_iemap _ m.inner h.out.size_buckets_pos
theorem dh_szw {γ : α → Type w} (f : (a : α) → β a → γ a) (m : DHashMap α β) : (m.map f).size = m.size :=
  r0_szmap f ⟨m.1, m.2.size_buckets_pos⟩
theorem dh_iew {γ : α → Type w} (f : (a : α) → β a → γ a) (m : DHashMap α β) : (m.map f).isEmpty = m.isEmpty :=
  r0_iemap f ⟨m.1, m.2.size_buckets_pos⟩
theorem hm_szw {γ : Type v} {δ : Type w} (f : α → γ → δ) (m : HashMap α γ) : (m.map f).size = m.size :=
  dh_szw _ m.inner
theorem hm_iew {γ : Type v} {δ : Type w} (f : α → γ → δ) (m : HashMap α γ) : (m.map f).isEmpty = m.isEmpty :=
  dh_iew _ m.inner
end W6c1
macro "w6ev1" : tactic => `(tactic| first
  | decide +kernel
  | (hm_eval; done)
  | (simp [DHashMap.Raw.toList, DHashMap.Raw.Const.toList, DHashMap.Raw.toArray, DHashMap.Raw.Const.toArray]; hm_eval; done)
  | (simp [DHashMap.toList, DHashMap.Const.toList, HashMap.toList, HashMap.Raw.toList, DHashMap.toArray, DHashMap.Const.toArray, HashMap.toArray, HashMap.Raw.toArray, HashSet.toArray, HashSet.Raw.toArray, DHashMap.Raw.toList, DHashMap.Raw.Const.toList, DHashMap.Raw.toArray, DHashMap.Raw.Const.toArray, DHashMap.size, HashMap.size, HashSet.size]; hm_eval; done)
  | (hm_eval_raw; done)
  | (w1c0_raw; done)
  | (simp [ExtHashMap.mem_alter]; done)
  | (simp [ExtDHashMap.mem_alter]; done)
  | (simp [ExtDHashMap.Const.mem_alter]; done)
  | (simp [ExtHashMap.contains_alter]; done)
  | (simp [ExtDHashMap.contains_alter]; done)
  | (simp [ExtDHashMap.Const.contains_alter]; done)
  | (simp [ExtHashMap.getKey!_insert]; done)
  | (simp [ExtDHashMap.getKey!_insert]; done)
  | (simp [DHashMap.mem_alter]; done)
  | (simp [DHashMap.Raw.mem_alter, DHashMap.Raw.WF.empty]; done)
  | (simp; done))
macro "w6evt" : tactic => `(tactic| first
  | rfl
  | decide +kernel
  | (simp only [HashMap.mem_iff_contains, HashSet.mem_iff_contains, DHashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashSet.Raw.mem_iff_contains, DHashMap.Raw.mem_iff_contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))
  | (hm_eval; done)
  | (hm_eval_raw; done))
namespace W6c1
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem dh_dkb [Inhabited α] (m₁ m₂ : DHashMap α β) (k : α) (h : ¬ k ∈ m₁) : (m₁ \ m₂).getKey! k = default :=
  raw0_getKey!_nc _ _ (W3c3.r0_diff_nc _ _ _ (Bool.eq_false_iff.2 (fun hc => h (DHashMap.mem_iff_contains.2 hc))))
theorem dh_dkd (m₁ m₂ : DHashMap α β) (k fb : α) (h : ¬ k ∈ m₁) : (m₁ \ m₂).getKeyD k fb = fb :=
  W4c5.r0_kD _ _ _ (W3c3.r0_diff_nc _ _ _ (Bool.eq_false_iff.2 (fun hc => h (DHashMap.mem_iff_contains.2 hc))))
theorem dr_dkb [Inhabited α] (m₁ m₂ : DHashMap.Raw α β) (hw : m₁.WF) (k : α) (h : ¬ k ∈ m₁) :
    (m₁ \ m₂).getKey! k = default :=
  W4c5.dr_kB _ _ (Bool.eq_false_iff.2 (fun hc => W3c3.dr_nmd m₁ m₂ hw k h (DHashMap.Raw.mem_iff_contains.2 hc)))
theorem dr_dkd (m₁ m₂ : DHashMap.Raw α β) (hw : m₁.WF) (k fb : α) (h : ¬ k ∈ m₁) :
    (m₁ \ m₂).getKeyD k fb = fb :=
  W4c5.dr_kD _ _ _ (Bool.eq_false_iff.2 (fun hc => W3c3.dr_nmd m₁ m₂ hw k h (DHashMap.Raw.mem_iff_contains.2 hc)))
theorem hm_dkb {γ : Type v} [Inhabited α] (m₁ m₂ : HashMap α γ) (k : α) (h : ¬ k ∈ m₁) : (m₁ \ m₂).getKey! k = default :=
  dh_dkb m₁.inner m₂.inner k h
theorem hm_dkd {γ : Type v} (m₁ m₂ : HashMap α γ) (k fb : α) (h : ¬ k ∈ m₁) : (m₁ \ m₂).getKeyD k fb = fb :=
  dh_dkd m₁.inner m₂.inner k fb h
theorem hmr_dkb {γ : Type v} [Inhabited α] (m₁ m₂ : HashMap.Raw α γ) (hw : m₁.WF) (k : α) (h : ¬ k ∈ m₁) :
    (m₁ \ m₂).getKey! k = default :=
  dr_dkb m₁.inner m₂.inner hw.out k h
theorem hmr_dkd {γ : Type v} (m₁ m₂ : HashMap.Raw α γ) (hw : m₁.WF) (k fb : α) (h : ¬ k ∈ m₁) :
    (m₁ \ m₂).getKeyD k fb = fb :=
  dr_dkd m₁.inner m₂.inner hw.out k fb h
end W6c1
namespace W6c1A
export W5c4 (nb_al)
export W5c4 (nb_nc)
end W6c1A
macro "w6nf" : tactic => `(tactic| (
  simp only [HashMap.mem_iff_contains, DHashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains,
    DHashMap.Raw.mem_iff_contains, Bool.not_eq_true]
  try simp only [HashMap.contains, HashMap.Raw.contains, DHashMap.contains]
  try unfold DHashMap.Raw.contains
  try rw [dif_pos (by decide)]
  first
  | exact W6c1A.nb_nc _ _ _ _
  | exact W3c5.hz_unreach _ _ _ _
  | exact W1c5.zh_contains _ _ _
  | exact W6c1A.nil2_nc _ _ _))
namespace W6c1A
variable {α : Type u} [BEq α] [Hashable α]
export W5c4 (nil2_nc)
export W5c4 (r0_gkn)
end W6c1A
macro "w6ne " t:term : tactic => `(tactic| first
  | exact absurd (List.Perm.length_eq ($t).1) (by simp [toListModel])
  | exact absurd (List.Perm.length_eq ($t).1.1) (by simp [toListModel])
  | exact absurd (List.Perm.length_eq ($t).1.1.1) (by simp [toListModel]))
theorem W6c1.mem_of_eq {α : Type u} {l : List α} {a : α} (h : l = [a]) : a ∈ l := h ▸ List.mem_singleton_self a
universe w'
namespace W6c1
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem dr_fm {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    (f : δ → (a : α) → β a → m' δ) (init : δ) :
    m.foldM f init = m.toList.foldlM (fun a b => f a b.1 b.2) init := by
  by_cases hb : 0 < m.buckets.size
  · exact Raw₀.foldM_eq_foldlM_toList ⟨m, hb⟩
  · obtain ⟨s, bs⟩ := m
    have : bs = #[] := Array.eq_empty_of_size_eq_zero (Nat.eq_zero_of_not_pos hb)
    subst this; rfl
theorem drc_fm {γ : Type v} {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α (fun _ => γ))
    (f : δ → α → γ → m' δ) (init : δ) :
    m.foldM f init = (DHashMap.Raw.Const.toList m).foldlM (fun a b => f a b.1 b.2) init := by
  by_cases hb : 0 < m.buckets.size
  · exact Raw₀.Const.foldM_eq_foldlM_toList ⟨m, hb⟩
  · obtain ⟨s, bs⟩ := m
    have : bs = #[] := Array.eq_empty_of_size_eq_zero (Nat.eq_zero_of_not_pos hb)
    subst this; rfl
theorem dk_fm {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    (f : δ → α → m' δ) (init : δ) :
    m.foldM (fun d a _ => f d a) init = m.keys.foldlM f init := by
  by_cases hb : 0 < m.buckets.size
  · exact Raw₀.foldM_eq_foldlM_keys ⟨m, hb⟩
  · obtain ⟨s, bs⟩ := m
    have : bs = #[] := Array.eq_empty_of_size_eq_zero (Nat.eq_zero_of_not_pos hb)
    subst this; rfl
theorem hmr_fm {γ : Type v} {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] (m : HashMap.Raw α γ)
    (f : δ → α → γ → m' δ) (init : δ) :
    m.foldM f init = m.toList.foldlM (fun a b => f a b.1 b.2) init := drc_fm m.inner f init
theorem hsr_fm {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] (m : HashSet.Raw α)
    (f : δ → α → m' δ) (init : δ) :
    m.foldM f init = m.toList.foldlM f init := dk_fm m.inner.inner f init
end W6c1
namespace W6c1
theorem fm_set {γ : Type u} {δ : Type v} (g : γ → List δ) (y : δ) (x : γ) :
    ∀ (l : List γ) (i : Nat) (hi : i < l.length), g x = y :: g (l[i]'hi) →
      ((l.set i x).flatMap g).Perm (y :: l.flatMap g)
  | [], _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | c :: t, 0, _, hx => by simp [hx]
  | c :: t, i + 1, hi, hx => by
    have ih := fm_set g y x t i (by simpa using hi) (by simpa using hx)
    simp only [List.set_cons_succ, List.flatMap_cons]
    exact (List.Perm.append_left _ ih).trans List.perm_middle
theorem r0_kin {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insertIfNew a b).1.keys.Perm (if m.contains a then m.1.keys else a :: m.1.keys) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen]
  unfold Raw₀.insertIfNew
  dsimp only
  simp only [Array.ugetElem_eq_getElem]
  split
  · exact List.Perm.refl _
  · simp only [Raw.keys_eq_keys_toListModel, Std.Internal.List.keys_eq_map]
    rw [show a :: List.map (fun x => x.fst) (toListModel bs) = List.map (fun x => x.fst) (⟨a, b⟩ :: toListModel bs) from rfl]
    refine List.Perm.map _ ((tlm_expandIfNecessary (α := α) (β := β) _).trans ?_)
    simp only [toListModel, Array.uset, Array.toList_set]
    exact fm_set AssocList.toList (⟨a, b⟩ : (a : α) × β a) (AssocList.cons a b (bs[(mkIdx bs.size hb (hash a)).val.toNat]'(mkIdx bs.size hb (hash a)).2)) bs.toList _
      (by rw [Array.length_toList]; exact (mkIdx bs.size hb (hash a)).2) (by simp [AssocList.toList])
end W6c1
namespace W6c1
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem dr_kin (m : DHashMap.Raw α β) (hb : 0 < m.buckets.size) (k : α) (v : β k) :
    (m.insertIfNew k v).keys.Perm (if k ∈ m then m.keys else k :: m.keys) := by
  have := r0_kin ⟨m, hb⟩ k v
  have hc : (k ∈ m) ↔ Raw₀.contains ⟨m, hb⟩ k = true := by
    rw [DHashMap.Raw.mem_iff_contains]; unfold DHashMap.Raw.contains; rw [dif_pos hb]
  unfold DHashMap.Raw.insertIfNew; rw [dif_pos hb]
  by_cases h : k ∈ m
  · rw [if_pos h]; rw [if_pos (hc.1 h)] at this; exact this
  · rw [if_neg h]; rw [if_neg (fun e => h (hc.2 e))] at this; exact this
theorem dh_kin (m : DHashMap α β) (k : α) (v : β k) :
    (m.insertIfNew k v).keys.Perm (if k ∈ m then m.keys else k :: m.keys) := by
  have := r0_kin ⟨m.1, m.2.size_buckets_pos⟩ k v
  have hc : (k ∈ m) ↔ Raw₀.contains ⟨m.1, m.2.size_buckets_pos⟩ k = true := DHashMap.mem_iff_contains
  by_cases h : k ∈ m
  · rw [if_pos h]; rw [if_pos (hc.1 h)] at this; exact this
  · rw [if_neg h]; rw [if_neg (fun e => h (hc.2 e))] at this; exact this
theorem hmr_kin {γ : Type v} (m : HashMap.Raw α γ) (hw : m.WF) (k : α) (v : γ) :
    (m.insertIfNew k v).keys.Perm (if k ∈ m then m.keys else k :: m.keys) :=
  dr_kin m.inner hw.out.size_buckets_pos k v
theorem hm_kin {γ : Type v} (m : HashMap α γ) (k : α) (v : γ) :
    (m.insertIfNew k v).keys.Perm (if k ∈ m then m.keys else k :: m.keys) :=
  dh_kin m.inner k v
end W6c1

/-! ## From `checks/W6c2Hand.lean` -/
namespace W5c4
variable {α : Type u} [BEq α] [Hashable α]
end W5c4
open W5c4
namespace W5c4
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
end
end W5c4
open W5c4
namespace W5c4
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
end
end W5c4
open W5c4
namespace W5c4
end W5c4
namespace W5c4
variable {α : Type u} [BEq α] [Hashable α]
end W5c4
namespace W5c4
end W5c4
set_option linter.unusedSimpArgs false
namespace W5c1
variable {α : Type u} {β : α → Type v}
end W5c1
namespace W5c1
variable {α : Type u} {β : α → Type v}
end W5c1
namespace W5c1
variable {α : Type u} {β : α → Type v}
end W5c1
namespace W6c2
variable {α : Type u}
-- size of the dependent insertListₘ grows by at most the list length (any instances)
theorem size_insertListD_le {β : α → Type v} [BEq α] [Hashable α] (l : List ((a : α) × β a)) :
    ∀ (m : Raw₀ α β), (Raw₀.insertListₘ m l).1.size ≤ m.1.size + l.length := by
  induction l with
  | nil => intro m; exact Nat.le_refl _
  | cons hd tl ih =>
    intro m
    have := ih (m.insert hd.1 hd.2)
    have := (raw0_size_insert m hd.1 hd.2).2
    show (Raw₀.insertListₘ (m.insert hd.1 hd.2) tl).1.size ≤ _
    simp only [List.length_cons]; omega
-- a key that is not a member has no getKey? (no laws, no WF)
theorem dr_gkn {β : α → Type v} [BEq α] [Hashable α] (m : DHashMap.Raw α β) (k : α) (h : ¬ k ∈ m) :
    m.getKey? k = none := by
  unfold DHashMap.Raw.getKey?; split
  · rename_i hb; apply W5c4.r0_gkn
    rw [DHashMap.Raw.mem_iff_contains] at h; unfold DHashMap.Raw.contains at h; rw [dif_pos hb] at h
    simpa using h
  · rfl
end W6c2

/-! ## From `checks/W6c3Hand.lean` -/
namespace W5c4
variable {α : Type u} [BEq α] [Hashable α]
end W5c4
open W5c4
namespace W5c4
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
end
end W5c4
open W5c4
namespace W5c4
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
end
end W5c4
open W5c4
namespace W5c4
end W5c4
namespace W5c4
variable {α : Type u} [BEq α] [Hashable α]
end W5c4
namespace W5c4
end W5c4
macro "w6ck" : tactic => `(tactic| first
  | exact (W5c4.r0c_cs ⟨_, _⟩ _)
  | exact ((W5c4.r0c_cs ⟨_, _⟩ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W5c4.r0c_cs ⟨_, _⟩ _))
  | exact Iff.of_eq (congrArg (· = true) ((W5c4.r0c_cs ⟨_, _⟩ _)).symm)
  | exact (W5c4.r0c_cs _ _)
  | exact ((W5c4.r0c_cs _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W5c4.r0c_cs _ _))
  | exact Iff.of_eq (congrArg (· = true) ((W5c4.r0c_cs _ _)).symm)
  | exact (W5c4.r0_ck ⟨_, _⟩ _)
  | exact ((W5c4.r0_ck ⟨_, _⟩ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W5c4.r0_ck ⟨_, _⟩ _))
  | exact Iff.of_eq (congrArg (· = true) ((W5c4.r0_ck ⟨_, _⟩ _)).symm)
  | exact (W5c4.r0_ck _ _)
  | exact ((W5c4.r0_ck _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W5c4.r0_ck _ _))
  | exact Iff.of_eq (congrArg (· = true) ((W5c4.r0_ck _ _)).symm)
  | exact (W5c4.r0_csc ⟨_, _⟩ _)
  | exact ((W5c4.r0_csc ⟨_, _⟩ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W5c4.r0_csc ⟨_, _⟩ _))
  | exact Iff.of_eq (congrArg (· = true) ((W5c4.r0_csc ⟨_, _⟩ _)).symm)
  | exact (W5c4.r0_csc _ _)
  | exact ((W5c4.r0_csc _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W5c4.r0_csc _ _))
  | exact Iff.of_eq (congrArg (· = true) ((W5c4.r0_csc _ _)).symm)
  | exact (W5c4.drc_cs _ _)
  | exact ((W5c4.drc_cs _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W5c4.drc_cs _ _))
  | exact Iff.of_eq (congrArg (· = true) ((W5c4.drc_cs _ _)).symm)
  | exact (W5c4.dr_ck _ _)
  | exact ((W5c4.dr_ck _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W5c4.dr_ck _ _))
  | exact Iff.of_eq (congrArg (· = true) ((W5c4.dr_ck _ _)).symm)
  | exact (W5c4.dr_csc _ _)
  | exact ((W5c4.dr_csc _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W5c4.dr_csc _ _))
  | exact Iff.of_eq (congrArg (· = true) ((W5c4.dr_csc _ _)).symm)
  | exact (raw0_map_contains _ _ _)
  | exact ((raw0_map_contains _ _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (raw0_map_contains _ _ _))
  | exact Iff.of_eq (congrArg (· = true) ((raw0_map_contains _ _ _)).symm)
  | exact (dr_map_contains _ _ _)
  | exact ((dr_map_contains _ _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (dr_map_contains _ _ _))
  | exact Iff.of_eq (congrArg (· = true) ((dr_map_contains _ _ _)).symm)
  | exact (dm_map_contains _ _ _)
  | exact ((dm_map_contains _ _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (dm_map_contains _ _ _))
  | exact Iff.of_eq (congrArg (· = true) ((dm_map_contains _ _ _)).symm))
namespace W6c3
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
open Std.Internal.List
theorem bk_nil (m : DHashMap.Raw α β) (h : ¬ 0 < m.buckets.size) : toListModel m.buckets = [] := by
  have : m.buckets = #[] := Array.eq_empty_of_size_eq_zero (by omega)
  simp [this, toListModel]
theorem empty_tlm {γ : α → Type w} : toListModel (∅ : DHashMap.Raw α γ).buckets = [] :=
  Raw₀.toListModel_buckets_emptyWithCapacity
-- map / filterMap act bucket-wise, so their model is a permutation of the mapped model (no WF)
theorem dr_map_perm {γ : α → Type w} (m : DHashMap.Raw α β) (f : (a : α) → β a → γ a) :
    (toListModel (m.map f).buckets).Perm ((toListModel m.buckets).map fun p => ⟨p.1, f p.1 p.2⟩) := by
  unfold DHashMap.Raw.map; split
  · exact Raw₀.toListModel_map
  · rename_i h; rw [bk_nil m h, empty_tlm]; simp
theorem dr_filterMap_perm {γ : α → Type w} (m : DHashMap.Raw α β) (f : (a : α) → β a → Option (γ a)) :
    (toListModel (m.filterMap f).buckets).Perm
      ((toListModel m.buckets).filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := by
  unfold DHashMap.Raw.filterMap; split
  · exact Raw₀.toListModel_filterMap
  · rename_i h; rw [bk_nil m h, empty_tlm]; simp
theorem dr_map_eqv {γ : α → Type w} (m₁ m₂ : DHashMap.Raw α β) (f : (a : α) → β a → γ a) (h : m₁.Equiv m₂) :
    (m₁.map f).Equiv (m₂.map f) :=
  ⟨(dr_map_perm m₁ f).trans ((h.1.map _).trans (dr_map_perm m₂ f).symm)⟩
theorem dr_filterMap_eqv {γ : α → Type w} (m₁ m₂ : DHashMap.Raw α β) (f : (a : α) → β a → Option (γ a))
    (h : m₁.Equiv m₂) : (m₁.filterMap f).Equiv (m₂.filterMap f) :=
  ⟨(dr_filterMap_perm m₁ f).trans ((h.1.filterMap _).trans (dr_filterMap_perm m₂ f).symm)⟩
end
end W6c3
namespace W6c3
section
variable {α : Type u} [BEq α] [Hashable α]
theorem r0c_gn2 {γ : Type v} (m₁ m₂ : Raw₀ α (fun _ => γ)) (h₁ : ∀ k, m₁.contains k = false)
    (h₂ : ∀ k, m₂.contains k = false) (k : α) : Raw₀.Const.get? m₁ k = Raw₀.Const.get? m₂ k := by
  have a := h₁ k; have b := h₂ k
  rw [W5c4.r0c_cs] at a b; simp only [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at a b
  rw [a, b]
theorem drc_gn2 {γ : Type v} (m₁ m₂ : DHashMap.Raw α (fun _ => γ)) (h₁ : ∀ k, m₁.contains k = false)
    (h₂ : ∀ k, m₂.contains k = false) (k : α) : DHashMap.Raw.Const.get? m₁ k = DHashMap.Raw.Const.get? m₂ k := by
  have a := h₁ k; have b := h₂ k
  rw [W5c4.drc_cs] at a b; simp only [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at a b
  rw [a, b]
end
end W6c3
macro "w6nc" : tactic => `(tactic| (
  try simp only [HashMap.contains, HashMap.Raw.contains, DHashMap.contains]
  try unfold DHashMap.Raw.contains
  try rw [dif_pos (by decide)]
  first
  | exact W5c4.nb_nc _ _ _ _
  | exact W3c5.hz_unreach _ _ _ _
  | exact W1c5.zh_contains _ _ _
  | exact W5c4.nil2_nc _ _ _))

/-! ## From `checks/W6c4Hand.lean` -/
namespace W5c4
variable {α : Type u} [BEq α] [Hashable α]
end W5c4
open W5c4
namespace W5c4
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
end
end W5c4
open W5c4
namespace W5c4
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
end
end W5c4
open W5c4
namespace W5c4
end W5c4
namespace W5c4
variable {α : Type u} [BEq α] [Hashable α]
end W5c4
namespace W5c4
end W5c4
namespace W6c4
theorem sa {α : Type u} [BEq α] [Hashable α] {β : Type v} (m : Raw₀ α (fun _ => β)) (k : α)
    (f : Option β → Option β) : (Raw₀.Const.alter m k f).1.size ≤ m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.Const.alter; dsimp only
  generalize mkIdx bs.size h (hash k) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  split
  · split <;> simp <;> omega
  · split <;> simp [Raw₀.size_expandIfNecessary]
theorem sad {α : Type u} [BEq α] [Hashable α] [LawfulBEq α] {β : α → Type v} (m : Raw₀ α β) (k : α)
    (f : Option (β k) → Option (β k)) : (Raw₀.alter m k f).1.size ≤ m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.alter; dsimp only
  generalize mkIdx bs.size h (hash k) = i
  obtain ⟨i, hi⟩ := i
  dsimp only
  split
  · split <;> simp <;> omega
  · split <;> simp [Raw₀.size_expandIfNecessary]
end W6c4
namespace W6c4
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
theorem dr_g!m {α : Type u} {γ : Type v} [BEq α] [Hashable α] [EquivBEq α] [Inhabited γ] (m : DHashMap.Raw α (fun _ => γ)) (k : α)
    (f : γ → γ) : DHashMap.Raw.Const.get! (DHashMap.Raw.Const.modify m k f) k = ((DHashMap.Raw.Const.get? m k).map f).get! := by
  unfold DHashMap.Raw.Const.modify; split
  · rename_i h; unfold DHashMap.Raw.Const.get? DHashMap.Raw.Const.get!; rw [dif_pos (Raw₀.Const.modify ⟨m, h⟩ k f).2, dif_pos h]; exact r0_g!m (m := ⟨m, h⟩) k f
  · rename_i h; show DHashMap.Raw.Const.get! ∅ k = _
    simp only [DHashMap.Raw.Const.get!_empty]; unfold DHashMap.Raw.Const.get?; rw [dif_neg h]; rfl
end W6c4

/-! ## From `checks/W6c5Hand.lean` -/
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
export W5c3 (a_cbq)
export W5c3 (a_cdq)
export W5c3 (a_cqg)
export W5c3 (a_kbq)
export W5c3 (a_kdq)
export W5c3 (a_kqg)
export W5c3 (a_gbq)
export W5c3 (a_gdq)
export W5c3 (a_gqg)
export W5c3 (a_cgb)
export W5c3 (a_cgd)
export W5c3 (a_kgb)
export W5c3 (a_kgd)
export W5c3 (a_ggb)
export W5c3 (a_ggd)
export W5c3 (zr0c_bq)
export W5c3 (zdrc_bq)
export W5c3 (zr0c_dq)
export W5c3 (zdrc_dq)
export W5c3 (zr0c_gb)
export W5c3 (zdrc_gb)
export W5c3 (zr0c_gd)
export W5c3 (zdrc_gd)
export W5c3 (zr0c_qg)
export W5c3 (zdrc_qg)
export W5c3 (zr0g_bq)
export W5c3 (zdrg_bq)
export W5c3 (zr0g_dq)
export W5c3 (zdrg_dq)
export W5c3 (zr0g_gb)
export W5c3 (zdrg_gb)
export W5c3 (zr0g_gd)
export W5c3 (zdrg_gd)
export W5c3 (zr0g_qg)
export W5c3 (zdrg_qg)
export W5c3 (zr0k_bq)
export W5c3 (zdrk_bq)
export W5c3 (zr0k_dq)
export W5c3 (zdrk_dq)
export W5c3 (zr0k_gb)
export W5c3 (zdrk_gb)
export W5c3 (zr0k_gd)
export W5c3 (zdrk_gd)
export W5c3 (zr0k_qg)
export W5c3 (zdrk_qg)
end
end W5c5
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
end
end W5c5
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
end
end W5c5
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
end
end W5c5
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v}
end
end W5c5
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v}
end
end W5c5
namespace W5c5
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
end
end W5c5
namespace W6c0
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
end
end W6c0
open W6c0
namespace W6c0
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
end
end W6c0
namespace W6c0
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
end
end W6c0
namespace W6c0
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
end
end W6c0
namespace W6c0
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
end
end W6c0
namespace W6c0
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
end
end W6c0
namespace W5c4
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
end
end W5c4
macro "w65ev" : tactic => `(tactic| first
  | (decide +kernel; done)
  | (hm_eval; done)
  | (hm_eval; decide +kernel)
  | (hm_eval_raw; done)
  | (hm_eval_raw; decide +kernel)
  | (hm_eval3; done)
  | (w1c0_raw; done)
  | (simp; done))
namespace W6c5
section
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
-- a key not contained in m₁ is not contained in an intersection (only LawfulHashable)
theorem r0_nci [LawfulHashable α] (m₁ m₂ : Raw₀ α β) (k : α) (hn : m₁.contains k = false) :
    (Raw₀.inter m₁ m₂).contains k = false := by
  cases h : (Raw₀.inter m₁ m₂).contains k
  · rfl
  · rw [W3c4.ni_r0 _ _ _ h] at hn; cases hn
theorem dr_gki [LawfulHashable α] (m₁ m₂ : DHashMap.Raw α β) (h₁ : 0 < m₁.buckets.size) {k : α} (hn : ¬ k ∈ m₁) :
    (m₁ ∩ m₂).getKey? k = none := W3c4.dr_getKey?_nc _ _ (W3c4.ni_dr _ _ h₁ k hn)
theorem dr_gki! [LawfulHashable α] [Inhabited α] (m₁ m₂ : DHashMap.Raw α β) (h₁ : 0 < m₁.buckets.size) {k : α}
    (hn : ¬ k ∈ m₁) : (m₁ ∩ m₂).getKey! k = default := W3c4.dr_getKey!_nc _ _ (W3c4.ni_dr _ _ h₁ k hn)
theorem dr_gkiD [LawfulHashable α] (m₁ m₂ : DHashMap.Raw α β) (h₁ : 0 < m₁.buckets.size) {k fb : α}
    (hn : ¬ k ∈ m₁) : (m₁ ∩ m₂).getKeyD k fb = fb :=
  W3c3.dr_getKeyD _ _ _ (Bool.eq_false_iff.mpr (W3c4.ni_dr _ _ h₁ k hn))
theorem hmr_gki [LawfulHashable α] (m₁ m₂ : HashMap.Raw α γ) (h₁ : m₁.WF) {k : α} (hn : ¬ k ∈ m₁) :
    (m₁ ∩ m₂).getKey? k = none := dr_gki m₁.inner m₂.inner (DHashMap.Raw.WF.size_buckets_pos _ h₁.out) hn
theorem hmr_gki! [LawfulHashable α] [Inhabited α] (m₁ m₂ : HashMap.Raw α γ) (h₁ : m₁.WF) {k : α}
    (hn : ¬ k ∈ m₁) : (m₁ ∩ m₂).getKey! k = default := dr_gki! m₁.inner m₂.inner (DHashMap.Raw.WF.size_buckets_pos _ h₁.out) hn
theorem hmr_gkiD [LawfulHashable α] (m₁ m₂ : HashMap.Raw α γ) (h₁ : m₁.WF) {k fb : α}
    (hn : ¬ k ∈ m₁) : (m₁ ∩ m₂).getKeyD k fb = fb := dr_gkiD m₁.inner m₂.inner (DHashMap.Raw.WF.size_buckets_pos _ h₁.out) hn
theorem dh_gki [LawfulHashable α] (m₁ m₂ : DHashMap α β) {k : α} (hn : ¬ k ∈ m₁) :
    (m₁ ∩ m₂).getKey? k = none :=
  W3c4.r0_getKey?_nc _ _ (r0_nci ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ k (Bool.eq_false_iff.mpr hn))
theorem dh_gki! [LawfulHashable α] [Inhabited α] (m₁ m₂ : DHashMap α β) {k : α} (hn : ¬ k ∈ m₁) :
    (m₁ ∩ m₂).getKey! k = default :=
  raw0_getKey!_nc _ _ (r0_nci ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ k (Bool.eq_false_iff.mpr hn))
theorem dh_gkiD [LawfulHashable α] (m₁ m₂ : DHashMap α β) {k fb : α} (hn : ¬ k ∈ m₁) :
    (m₁ ∩ m₂).getKeyD k fb = fb :=
  W3c3.r0_getKeyD _ _ _ (r0_nci ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ k (Bool.eq_false_iff.mpr hn))
theorem hm_gki [LawfulHashable α] (m₁ m₂ : HashMap α γ) {k : α} (hn : ¬ k ∈ m₁) :
    (m₁ ∩ m₂).getKey? k = none := dh_gki m₁.inner m₂.inner hn
theorem hm_gki! [LawfulHashable α] [Inhabited α] (m₁ m₂ : HashMap α γ) {k : α} (hn : ¬ k ∈ m₁) :
    (m₁ ∩ m₂).getKey! k = default := dh_gki! m₁.inner m₂.inner hn
theorem hm_gkiD [LawfulHashable α] (m₁ m₂ : HashMap α γ) {k fb : α} (hn : ¬ k ∈ m₁) :
    (m₁ ∩ m₂).getKeyD k fb = fb := dh_gkiD m₁.inner m₂.inner hn
-- insert makes the key findable without LawfulHashable (W5c4.r0_cis / r0_ciis)
theorem dh_mis [EquivBEq α] (m : DHashMap α β) (k : α) (v : β k) : k ∈ m.insert k v := by
  rw [DHashMap.mem_iff_contains]; exact W5c4.r0_cis ⟨m.1, _⟩ k v
theorem hm_mis [EquivBEq α] (m : HashMap α γ) {k : α} {v : γ} : k ∈ m.insert k v := dh_mis m.inner k v
theorem hs_mis [EquivBEq α] (m : HashSet α) {k : α} : k ∈ m.insert k := by
  show (m.inner.inner.insertIfNew k ()).contains k = true
  exact W5c4.r0_ciis ⟨m.inner.inner.1, _⟩ k ()
end
end W6c5
namespace W6c5
section
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
-- diff keeps contains k false when m₁ does not contain k (no laws; raw: m₁ needs buckets)
theorem dr_ndl (m₁ m₂ : DHashMap.Raw α β) (h₁ : 0 < m₁.buckets.size) (k : α) (hn : ¬ k ∈ m₁) : ¬ k ∈ m₁ \ m₂ := by
  obtain ⟨h', hc⟩ := dr_diff_nc m₁ m₂ k h₁ hn
  rw [DHashMap.Raw.mem_iff_contains]; unfold DHashMap.Raw.contains; rw [dif_pos h', hc]; simp
theorem hmr_dnl (m₁ m₂ : HashMap.Raw α γ) (h₁ : m₁.WF) {k : α} (hn : ¬ k ∈ m₁) : (m₁ \ m₂)[k]? = none :=
  W3c4.drc_get?_nc _ _ (dr_ndl m₁.inner m₂.inner (DHashMap.Raw.WF.size_buckets_pos _ h₁.out) k hn)
theorem hmr_dnl! [Inhabited γ] (m₁ m₂ : HashMap.Raw α γ) (h₁ : m₁.WF) {k : α} (hn : ¬ k ∈ m₁) : (m₁ \ m₂)[k]! = default :=
  W3c4.drc_get!_nc _ _ (dr_ndl m₁.inner m₂.inner (DHashMap.Raw.WF.size_buckets_pos _ h₁.out) k hn)
theorem hm_dnl (m₁ m₂ : HashMap α γ) {k : α} (hn : ¬ k ∈ m₁) : (m₁ \ m₂)[k]? = none :=
  W3c4.r0c_get?_nc _ _ (raw0_diff_nc ⟨m₁.inner.1, _⟩ ⟨m₂.inner.1, _⟩ _ (Bool.eq_false_iff.mpr hn))
theorem hm_dnl! [Inhabited γ] (m₁ m₂ : HashMap α γ) {k : α} (hn : ¬ k ∈ m₁) : (m₁ \ m₂)[k]! = default :=
  raw0_cget!_nc _ _ (raw0_diff_nc ⟨m₁.inner.1, _⟩ ⟨m₂.inner.1, _⟩ _ (Bool.eq_false_iff.mpr hn))
-- ofList / unitOfList lookups of a key outside the list (EquivBEq, no LawfulHashable)
theorem dhc_ng? [EquivBEq α] (l : List (α × γ)) (k : α) (h : (l.map Prod.fst).contains k = false) :
    DHashMap.Const.get? (DHashMap.Const.ofList l) k = none :=
  W3c4.r0c_get?_nc ⟨_, _⟩ _ (W6c0.r0_nc ⟨_, _⟩ _ (W6c0.dc_ofl_keys _ _ h))
theorem dhc_ng! [EquivBEq α] [Inhabited γ] (l : List (α × γ)) (k : α) (h : (l.map Prod.fst).contains k = false) :
    DHashMap.Const.get! (DHashMap.Const.ofList l) k = default :=
  raw0_cget!_nc ⟨_, _⟩ _ (W6c0.r0_nc ⟨_, _⟩ _ (W6c0.dc_ofl_keys _ _ h))
theorem drc_ng? [EquivBEq α] (m : DHashMap.Raw α (fun _ => γ)) (k : α)
    (hk : ∀ p ∈ toListModel m.buckets, (k == p.1) = false) : DHashMap.Raw.Const.get? m k = none := by
  unfold DHashMap.Raw.Const.get?; split
  · exact W3c4.r0c_get?_nc ⟨m, _⟩ k (W6c0.r0_nc ⟨m, _⟩ k hk)
  · rfl
theorem drc_ng! [EquivBEq α] [Inhabited γ] (m : DHashMap.Raw α (fun _ => γ)) (k : α)
    (hk : ∀ p ∈ toListModel m.buckets, (k == p.1) = false) : DHashMap.Raw.Const.get! m k = default := by
  unfold DHashMap.Raw.Const.get!; split
  · exact raw0_cget!_nc ⟨m, _⟩ k (W6c0.r0_nc ⟨m, _⟩ k hk)
  · rfl
theorem uol_k (l : List α) (k : α) (h : l.contains k = false) (m : List ((_ : α) × Unit))
    (hm : ∀ p ∈ m, p.1 ∈ l) : ∀ p ∈ m, (k == p.1) = false :=
  fun p hp => W6c0.lst id l k (by simpa using h) p.1 (hm p hp)
theorem dc_uol [EquivBEq α] (l : List α) (k : α) (h : l.contains k = false) :
    (DHashMap.Const.unitOfList l).getKey? k = none :=
  W6c0.r0_nk ⟨_, _⟩ _ (uol_k l k h _ (W4c3.uol_entries l))
theorem drc_uol [EquivBEq α] (l : List α) (k : α) (h : l.contains k = false) :
    (DHashMap.Raw.Const.unitOfList l).getKey? k = none :=
  W6c0.dr_nk _ _ (uol_k l k h _ (W4c3.uolr_entries l))
end
end W6c5
namespace W6c5
section
variable {α : Type u} {γ : Type v} [BEq α] [Hashable α]
theorem a_mg [EquivBEq α] (l : AssocList α (fun _ => γ)) (k k' : α) (f : γ → γ) :
    (AssocList.Const.modify k f l).get? k' = if k == k' then (l.get? k).map f else l.get? k' := by
  induction l with
  | nil => simp [AssocList.Const.modify, AssocList.get?]
  | cons e v t ih =>
    by_cases he : (e == k) = true
    · simp only [AssocList.Const.modify, he, ↓reduceIte, AssocList.get?]
      by_cases hk : (k == k') = true
      · simp [hk]
      · have : (e == k') = false := by
          cases h2 : (e == k')
          · rfl
          · exact absurd (BEq.trans (BEq.symm he) h2) hk
        simp [hk, this]
    · have he' : (e == k) = false := by simpa using he
      simp only [AssocList.Const.modify, he', Bool.false_eq_true, ↓reduceIte, AssocList.get?, ih]
      by_cases hk : (k == k') = true
      · have : (e == k') = false := by
          cases h2 : (e == k')
          · rfl
          · exact absurd (BEq.trans h2 (BEq.symm hk)) he
        simp [hk, this]
      · simp [hk]
theorem al_cmod_nc (l : AssocList α (fun _ => γ)) (a : α) (f : γ → γ) (h : l.contains a = false) :
    AssocList.Const.modify a f l = l := by
  induction l with
  | nil => rfl
  | cons s v t ih =>
    simp only [AssocList.contains, Bool.or_eq_false_iff] at h
    simp only [AssocList.Const.modify, h.1, Bool.false_eq_true, ↓reduceIte, ih h.2]
-- get? after Const.modify: only EquivBEq and LawfulHashable, no WF
theorem r0c_gmg [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => γ)) (a k' : α) (f : γ → γ) :
    Raw₀.Const.get? (Raw₀.Const.modify m a f) k' =
      if a == k' then (Raw₀.Const.get? m a).map f else Raw₀.Const.get? m k' := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have hidx : (a == k') = true → (mkIdx bs.size hb (hash a)).1.toNat = (mkIdx bs.size hb (hash k')).1.toNat := by
    intro h; rw [hash_eq h]
  rw [cmodify_gen]; split
  · rename_i hc; simp only [cget?_gen]; rw [set_ix _ _ _ _ _ hb]
    split
    · rename_i he
      have he' : (mkIdx bs.size hb (hash a)).1.toNat = (mkIdx bs.size hb (hash k')).1.toNat := he
      simp only [← he']; rw [a_mg]
    · rename_i he
      cases ha : (a == k')
      · simp
      · exact absurd (hidx ha) he
  · rename_i hc; simp only [cget?_gen]
    cases ha : (a == k')
    · simp
    · simp only [ite_true]
      have he := hidx ha
      simp only [← he]
      have := a_mg (bs[(mkIdx bs.size hb (hash a)).1.toNat]'(mkIdx bs.size hb (hash a)).2) a k' f
      rw [al_cmod_nc _ _ _ (by simpa using hc), ha] at this
      simpa using this
theorem drc_gmg [EquivBEq α] [LawfulHashable α] (m : DHashMap.Raw α (fun _ => γ)) (a k' : α) (f : γ → γ) :
    DHashMap.Raw.Const.get? (DHashMap.Raw.Const.modify m a f) k' =
      if a == k' then (DHashMap.Raw.Const.get? m a).map f else DHashMap.Raw.Const.get? m k' := by
  have e1 : ∀ (r : Raw₀ α (fun _ => γ)) k, DHashMap.Raw.Const.get? r.1 k = Raw₀.Const.get? r k := by
    intro r k; unfold DHashMap.Raw.Const.get?; rw [dif_pos r.2]
  unfold DHashMap.Raw.Const.modify; split
  · rename_i hb
    rw [e1, r0c_gmg]; unfold DHashMap.Raw.Const.get?; rw [dif_pos hb, dif_pos hb]
  · rename_i hb
    have h0 : DHashMap.Raw.Const.get? (∅ : DHashMap.Raw α (fun _ => γ)) k' = none := DHashMap.Raw.Const.get?_empty
    unfold DHashMap.Raw.Const.get? at h0 ⊢; simp only [hb, dite_false]; rw [h0]; split <;> rfl
end
end W6c5
namespace W6c5
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
-- dependent get? after modify, without WF or LawfulHashable (W5c5.r0_dgs/r0_dgo)
theorem r0_gmd [LawfulBEq α] (m : Raw₀ α β) (k k' : α) (f : β k → β k) :
    (m.modify k f).get? k' = if h : k == k' then cast (congrArg (Option ∘ β) (eq_of_beq h)) ((m.get? k).map f)
      else m.get? k' := by
  split
  · rename_i h; have e := eq_of_beq h; subst e; rw [W5c5.r0_dgs]; rfl
  · rename_i h; exact W5c5.r0_dgo _ _ _ _ (Bool.eq_false_iff.mpr h)
theorem dr_gmd [LawfulBEq α] (m : DHashMap.Raw α β) (k k' : α) (f : β k → β k) :
    (m.modify k f).get? k' = if h : k == k' then cast (congrArg (Option ∘ β) (eq_of_beq h)) ((m.get? k).map f)
      else m.get? k' := by
  split
  · rename_i h; have e := eq_of_beq h; subst e; rw [W5c5.dr_dgs]; rfl
  · rename_i h; exact W5c5.dr_dgo _ _ _ _ (Bool.eq_false_iff.mpr h)
end
end W6c5
namespace W6c5
-- number of entries with key == a; unaffected by appending a list without a
theorem cnt0 (l' : List ((_ : CZ) × Nat)) (a : CZ) (h : Std.Internal.List.containsKey a l' = false) :
    (l'.filter (fun p => p.1 == a)).length = 0 := by
  induction l' with
  | nil => rfl
  | cons p t ih =>
    simp only [Std.Internal.List.containsKey, Bool.or_eq_false_iff] at h
    simp only [List.filter_cons, h.1, Bool.false_eq_true, ↓reduceIte]; exact ih h.2
end W6c5
namespace W6c5
-- NS copy of W2c0.cz_hs: every NS bucket array #[l, nil] is hash-self (hash 0)
theorem ns_hs {β : NS → Type v} (l : AssocList NS β) : IsHashSelf (#[l, .nil] : Array (AssocList NS β)) := by
  refine ⟨fun i hi => ⟨fun h p hp => ?_⟩⟩
  rw [mkIdx_toNat' _ _ _ (by simp [Pow2])]
  have : (scrambleHash (hash p.1)).toNat % 2 = 0 := by
    show (scrambleHash 0).toNat % 2 = 0
    rw [scr_small _ (by decide)]; rfl
  rw [show (#[l, AssocList.nil] : Array (AssocList NS β)).size = 2 from rfl, this]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => simp at hp
end W6c5
namespace W6c5
-- lawful Nat literal with keys 0 and 1 in buckets 0 and 1 (key n lands in bucket n mod 2)
def B01 : Array (AssocList Nat (fun _ => Nat)) := #[.cons 0 0 .nil, .cons 1 0 .nil]
theorem ix2 (n : Nat) (hn : n < 2) (h : 0 < 2) : (mkIdx 2 h (hash n)).1.toNat = n := by
  rw [mkIdx_toNat' _ _ _ (by simp [Pow2])]
  show (scrambleHash (UInt64.ofNat n)).toNat % 2 = n
  rw [scr_small _ (by simp; omega)]; simp; omega
theorem b01_wf : Raw.WFImp (⟨2, B01⟩ : DHashMap.Raw Nat (fun _ => Nat)) := by
  refine ⟨⟨fun i hi => ⟨fun h p hp => ?_⟩⟩, rfl, ⟨by decide⟩⟩
  match i, hi with
  | 0, _ => simp [B01] at hp; subst hp; exact ix2 0 (by decide) h
  | 1, _ => simp [B01] at hp; subst hp; exact ix2 1 (by decide) h
theorem b01_b1 (h : 0 < B01.size) : bucket B01 h (1 : Nat) = .cons 1 0 .nil := by
  unfold bucket
  have hx : (mkIdx B01.size h (hash (1 : Nat))).1.toNat = 1 := ix2 1 (by decide) h
  generalize mkIdx B01.size h (hash (1 : Nat)) = x at hx ⊢
  obtain ⟨i, hi⟩ := x
  have : i = 1 := USize.toNat_inj.mp (by simpa using hx)
  subst this; simp [B01]
end W6c5

/-! ## From `checks/W6c6Hand.lean` -/
namespace W6c6
open Std Std.DHashMap.Internal
section
variable {α : Type u} {γ : Type v}
-- HashMap / HashMap.Raw lookups as Raw₀ / DHashMap.Raw lookups (definitional)
theorem hm_g? [BEq α] [Hashable α] (m : HashMap α γ) (a : α) :
    m[a]? = Raw₀.Const.get? ⟨m.inner.1, m.inner.2.size_buckets_pos⟩ a := rfl
theorem hm_g! [BEq α] [Hashable α] [Inhabited γ] (m : HashMap α γ) (a : α) :
    m[a]! = Raw₀.Const.get! ⟨m.inner.1, m.inner.2.size_buckets_pos⟩ a := rfl
theorem hm_gD [BEq α] [Hashable α] (m : HashMap α γ) (a : α) (f : γ) :
    m.getD a f = Raw₀.Const.getD ⟨m.inner.1, m.inner.2.size_buckets_pos⟩ a f := rfl
theorem hmr_g? [BEq α] [Hashable α] (m : HashMap.Raw α γ) (a : α) :
    m[a]? = DHashMap.Raw.Const.get? m.inner a := rfl
theorem hmr_g! [BEq α] [Hashable α] [Inhabited γ] (m : HashMap.Raw α γ) (a : α) :
    m[a]! = DHashMap.Raw.Const.get! m.inner a := rfl
theorem hmr_gD [BEq α] [Hashable α] (m : HashMap.Raw α γ) (a : α) (f : γ) :
    m.getD a f = DHashMap.Raw.Const.getD m.inner a f := rfl
theorem r0c_g!n [BEq α] [Hashable α] [Inhabited γ] (m : Raw₀ α (fun _ => γ)) (a : α) (h : m.contains a = false) :
    Raw₀.Const.get! m a = default := by
  have := W3c4.drc_get!_nc m.1 a (by
    show ¬ (m.1.contains a = true)
    simp only [DHashMap.Raw.contains, dite_eq_left m.2]; simp [h])
  simpa [DHashMap.Raw.Const.get!, dite_eq_left m.2] using this
theorem hmr_g?n [BEq α] [Hashable α] (m : HashMap.Raw α γ) (a : α) (h : ¬ a ∈ m) : m[a]? = none :=
  W3c4.drc_get?_nc m.inner a h
theorem hmr_g?n' [BEq α] [Hashable α] (m : HashMap.Raw α γ) (a : α) (h : m.contains a = false) : m[a]? = none :=
  W3c4.drc_get?_nc m.inner a (Bool.eq_false_iff.1 h)
theorem hmr_g!n [BEq α] [Hashable α] [Inhabited γ] (m : HashMap.Raw α γ) (a : α) (h : ¬ a ∈ m) : m[a]! = default :=
  W3c4.drc_get!_nc m.inner a h
theorem hmr_g!n' [BEq α] [Hashable α] [Inhabited γ] (m : HashMap.Raw α γ) (a : α) (h : m.contains a = false) : m[a]! = default :=
  W3c4.drc_get!_nc m.inner a (Bool.eq_false_iff.1 h)
export W5c3 (a_cgc)
export W5c2 (al_cg_congr)
theorem r0c_g!c [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [Inhabited γ] (m : Raw₀ α (fun _ => γ)) (a b : α)
    (hab : (a == b) = true) : Raw₀.Const.get! m a = Raw₀.Const.get! m b := by
  obtain ⟨⟨s, bs⟩, hm⟩ := m
  simp only [Raw₀.Const.get!, hash_eq hab]
  exact a_cgc _ _ _ hab
theorem drc_g!c [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [Inhabited γ] (m : DHashMap.Raw α (fun _ => γ)) (a b : α)
    (hab : (a == b) = true) : DHashMap.Raw.Const.get! m a = DHashMap.Raw.Const.get! m b := by
  simp only [DHashMap.Raw.Const.get!]; split
  · exact r0c_g!c _ _ _ hab
  · rfl
theorem r0c_g?c [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => γ)) (a b : α)
    (hab : (a == b) = true) : Raw₀.Const.get? m a = Raw₀.Const.get? m b := by
  obtain ⟨⟨s, bs⟩, hm⟩ := m
  simp only [Raw₀.Const.get?, hash_eq hab]
  exact al_cg_congr _ hab
theorem drc_g?c [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : DHashMap.Raw α (fun _ => γ)) (a b : α)
    (hab : (a == b) = true) : DHashMap.Raw.Const.get? m a = DHashMap.Raw.Const.get? m b := by
  simp only [DHashMap.Raw.Const.get?]; split
  · exact r0c_g?c _ _ _ hab
  · rfl
theorem mem_of_eq {l : List α} {a : α} (h : l = [a]) : a ∈ l := h ▸ List.mem_singleton_self a
theorem amem_of_eq {arr : Array α} {a : α} (h : arr.toList = [a]) : a ∈ arr := Array.mem_def.2 (h ▸ List.mem_singleton_self a)
end
end W6c6
namespace W6c6
variable {α : Type u} {β : α → Type v}
theorem r0_k!m [BEq α] [Hashable α] [LawfulBEq α] [Inhabited α] (m : Raw₀ α β) (a : α) (h : m.contains a = true) :
    m.getKey! a = a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  simp only [Raw₀.getKey!, Raw₀.contains] at h ⊢
  rw [AssocList.contains_eq] at h
  rw [AssocList.getKey!_eq, Std.Internal.List.getKey!_eq_getKey?, Std.Internal.List.getKey?_eq_some h]; rfl
theorem r0_kDm [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a fb : α) (h : m.contains a = true) :
    m.getKeyD a fb = a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  simp only [Raw₀.getKeyD, Raw₀.contains] at h ⊢
  rw [AssocList.contains_eq] at h
  rw [AssocList.getKeyD_eq, Std.Internal.List.getKeyD_eq_getKey?, Std.Internal.List.getKey?_eq_some h]; rfl
theorem dr_k!m [BEq α] [Hashable α] [LawfulBEq α] [Inhabited α] (m : DHashMap.Raw α β) (a : α) (h : a ∈ m) :
    m.getKey! a = a := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.getKey!; rw [dite_eq_left hb]; exact r0_k!m _ _ h'
theorem dr_kDm [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (a fb : α) (h : a ∈ m) :
    m.getKeyD a fb = a := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.getKeyD; rw [dite_eq_left hb]; exact r0_kDm _ _ _ h'
end W6c6
macro "w6r" : tactic => `(tactic| (intros; first
  | exact (W6c6.hm_g? _ _).trans (W3c4.r0c_get?_nc _ _ ‹_›)
  | exact (W6c6.hm_g? _ _).trans (W3c4.r0c_get?_nc _ _ (Bool.eq_false_iff.2 ‹_›))
  | exact (W6c6.hm_g! _ _).trans (W6c6.r0c_g!n _ _ ‹_›)
  | exact (W6c6.hm_g! _ _).trans (W6c6.r0c_g!n _ _ (Bool.eq_false_iff.2 ‹_›))
  | exact (W6c6.hm_g? _ _).trans (W4c5.r0c_gd _ _ _ ‹_›)
  | exact (W6c6.hm_g? _ _).trans (W4c5.r0c_gb _ _ ‹_›)
  | exact (W6c6.hm_g? _ _).trans (W6c6.r0c_g?c _ _ _ ‹_›)
  | exact (W6c6.hm_g! _ _).trans (W6c6.r0c_g!c _ _ _ ‹_›)
  | exact W6c6.hmr_g?n _ _ ‹_›
  | exact W6c6.hmr_g?n' _ _ ‹_›
  | exact W6c6.hmr_g!n _ _ ‹_›
  | exact W6c6.hmr_g!n' _ _ ‹_›
  | exact (W6c6.hmr_g? _ _).trans (W4c5.drc_gd _ _ _ ‹_›)
  | exact (W6c6.hmr_g? _ _).trans (W4c5.drc_gb _ _ ‹_›)
  | exact (W6c6.hmr_g? _ _).trans (W6c6.drc_g?c _ _ _ ‹_›)
  | exact (W6c6.hmr_g! _ _).trans (W6c6.drc_g!c _ _ _ ‹_›)))
namespace W6c6
open Std Std.DHashMap.Internal
section
variable {α : Type u}
export W5c3 (z2_c)
export W5c3 (z4_c)
export W5c3 (hz_h)
theorem z2_r0 [BEq α] [Hashable α] {β : α → Type v} (s : Nat) (l : AssocList α β) (a : α) (hh : hash a = 0) (hb)
    (h : Raw₀.contains (⟨⟨s, #[.nil, l]⟩, hb⟩ : Raw₀ α β) a = true) : False :=
  Bool.noConfusion (h.symm.trans (z2_c s l a hh))
theorem z4_r0 [BEq α] [Hashable α] {β : α → Type v} (s : Nat) (l : AssocList α β) (a : α) (hh : hash a = 0 ∨ hash a = 1) (hb)
    (h : Raw₀.contains (⟨⟨s, #[.nil, .nil, l, .nil]⟩, hb⟩ : Raw₀ α β) a = true) : False :=
  Bool.noConfusion (h.symm.trans (z4_c s l a hh))
theorem z2_dr [BEq α] [Hashable α] {β : α → Type v} (s : Nat) (l : AssocList α β) (a : α) (hh : hash a = 0)
    (h : a ∈ (⟨s, #[.nil, l]⟩ : DHashMap.Raw α β)) : False := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h; exact z2_r0 s l a hh hb h'
theorem z4_dr [BEq α] [Hashable α] {β : α → Type v} (s : Nat) (l : AssocList α β) (a : α) (hh : hash a = 0 ∨ hash a = 1)
    (h : a ∈ (⟨s, #[.nil, .nil, l, .nil]⟩ : DHashMap.Raw α β)) : False := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h; exact z4_r0 s l a hh hb h'
end
end W6c6
macro "w6nm" : tactic => `(tactic| first
  | exact W6c6.z2_r0 _ _ _ rfl _ ‹_›
  | exact W6c6.z4_r0 _ _ _ (W6c6.hz_h _) _ ‹_›
  | exact W6c6.z2_dr _ _ _ rfl ‹_›
  | exact W6c6.z4_dr _ _ _ (W6c6.hz_h _) ‹_›)
universe w6u
namespace W6c6
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v} {δ : Type w} {m' : Type w → Type w6u}
-- monadic folds/loops of a raw map without WF: buckets nonempty → the Raw₀ lemma; no buckets → both sides are pure
macro "w6b " m:ident t:term : tactic => `(tactic| (
  by_cases hb : 0 < ($m).buckets.size
  · exact $t ⟨$m, hb⟩
  · obtain ⟨s, bs⟩ := $m
    have e : bs = #[] := Array.eq_empty_of_size_eq_zero (by simp_all)
    subst e
    first | rfl | simp [DHashMap.Raw.foldM, DHashMap.Raw.forIn, DHashMap.Raw.forM, DHashMap.Raw.toList, DHashMap.Raw.toArray, DHashMap.Raw.keys, DHashMap.Raw.keysArray, DHashMap.Raw.Const.toList, DHashMap.Raw.Const.toArray, DHashMap.Raw.fold, ForIn.forIn, ForM.forM, DHashMap.Raw.Const.forMUncurried, DHashMap.Raw.Const.forInUncurried]))
theorem m_fa [BEq α] [Hashable α] [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    {f : δ → (a : α) → β a → m' δ} {init : δ} :
    m.foldM f init = m.toArray.foldlM (fun a b => f a b.1 b.2) init := by w6b m Raw₀.foldM_eq_foldlM_toArray
theorem m_cfa [BEq α] [Hashable α] [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α (fun _ => γ))
    {f : δ → α → γ → m' δ} {init : δ} :
    m.foldM f init = (DHashMap.Raw.Const.toArray m).foldlM (fun a b => f a b.1 b.2) init := by w6b m Raw₀.Const.foldM_eq_foldlM_toArray
theorem m_ka [BEq α] [Hashable α] [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    {f : δ → α → m' δ} {init : δ} :
    m.foldM (fun d a _ => f d a) init = m.keysArray.foldlM f init := by w6b m Raw₀.foldM_eq_foldlM_keysArray
theorem m_ia [BEq α] [Hashable α] [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    {f : (a : α) → β a → δ → m' (ForInStep δ)} {init : δ} :
    m.forIn f init = ForIn.forIn m.toArray init (fun a b => f a.1 a.2 b) := by w6b m Raw₀.forIn_eq_forIn_toArray
theorem m_cia [BEq α] [Hashable α] [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α (fun _ => γ))
    {f : α → γ → δ → m' (ForInStep δ)} {init : δ} :
    m.forIn f init = ForIn.forIn (DHashMap.Raw.Const.toArray m) init (fun a b => f a.1 a.2 b) := by w6b m Raw₀.Const.forIn_eq_forIn_toArray
theorem m_kia [BEq α] [Hashable α] [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    m.forIn (fun a _ d => f a d) init = ForIn.forIn m.keysArray init f := by w6b m Raw₀.forIn_eq_forIn_keysArray
theorem m_il [BEq α] [Hashable α] [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    {f : (a : α) × β a → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init f = ForIn.forIn m.toList init f := by w6b m Raw₀.forIn_eq_forIn_toList
theorem m_cil [BEq α] [Hashable α] [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α (fun _ => γ))
    {f : α × γ → δ → m' (ForInStep δ)} {init : δ} :
    DHashMap.Raw.Const.forInUncurried f init m = ForIn.forIn (DHashMap.Raw.Const.toList m) init f := by w6b m Raw₀.Const.forIn_eq_forIn_toList
theorem m_kil [BEq α] [Hashable α] [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init (fun a d => f a.1 d) = ForIn.forIn m.keys init f := by w6b m Raw₀.forIn_eq_forIn_keys
theorem m_ml [BEq α] [Hashable α] [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    {f : (a : α) × β a → m' PUnit} :
    ForM.forM m f = m.toList.forM f := by w6b m Raw₀.forM_eq_forM_toList
theorem m_cml [BEq α] [Hashable α] [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α (fun _ => γ))
    {f : α × γ → m' PUnit} :
    DHashMap.Raw.Const.forMUncurried f m = (DHashMap.Raw.Const.toList m).forM f := by w6b m Raw₀.Const.forM_eq_forM_toList
theorem m_kml [BEq α] [Hashable α] [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    {f : α → m' PUnit} :
    ForM.forM m (fun a => f a.1) = m.keys.forM f := by w6b m Raw₀.forM_eq_forM_keys
end
end W6c6
macro "w6mon" : tactic => `(tactic| (intros; first
  | exact W6c6.m_fa _ | exact W6c6.m_cfa _ | exact W6c6.m_ka _ | exact W6c6.m_ia _ | exact W6c6.m_cia _ | exact W6c6.m_kia _
  | exact W6c6.m_il _ | exact W6c6.m_cil _ | exact W6c6.m_kil _ | exact W6c6.m_ml _ | exact W6c6.m_cml _ | exact W6c6.m_kml _))
namespace W6c6
open Std Std.DHashMap.Internal
section
variable {α : Type u} [BEq α] [Hashable α]
-- unitOfList without laws: the first insert into ∅ sets size 1, later inserts never lower it and add at most 1
theorem e_insIfNew {β : α → Type v} (c : Nat) (a : α) (b : β a) : ((Raw₀.emptyWithCapacity c : Raw₀ α β).insertIfNew a b).1.size = 1 := by
  have h0 : (Raw₀.emptyWithCapacity c : Raw₀ α β).contains a = false := Raw₀.contains_emptyWithCapacity
  revert h0
  unfold Raw₀.insertIfNew Raw₀.contains; dsimp only
  split
  · intro h; simp_all
  · intro _; simp [Raw₀.size_expandIfNecessary, Raw₀.emptyWithCapacity]
export W5c2 (r0u_ofl)
theorem siu_le (l : List α) :
    ∀ (m : Raw₀ α (fun _ => Unit)), (Raw₀.Const.insertListIfNewUnitₘ m l).1.size ≤ m.1.size + l.length := by
  induction l with
  | nil => intro m; exact Nat.le_refl _
  | cons hd tl ih =>
    intro m
    have := ih (m.insertIfNew hd ())
    have := (raw0_size_insertIfNew m hd ()).2
    show (Raw₀.Const.insertListIfNewUnitₘ (m.insertIfNew hd ()) tl).1.size ≤ _
    simp only [List.length_cons]; omega
theorem r0u_sle (c : Nat) (l : List α) :
    (Raw₀.Const.insertManyIfNewUnit (Raw₀.emptyWithCapacity c : Raw₀ α (fun _ => Unit)) l).1.1.size ≤ l.length := by
  rw [Raw₀.Const.insertManyIfNewUnit_eq_insertListIfNewUnitₘ]
  have := siu_le l (Raw₀.emptyWithCapacity c)
  simpa [Raw₀.emptyWithCapacity] using this
export W5c2 (dhu_ofl)
theorem dhu_sle (l : List α) : (DHashMap.Const.unitOfList l).size ≤ l.length := r0u_sle _ l
export W5c2 (dru_ofl)
theorem dru_sle (l : List α) : (DHashMap.Raw.Const.unitOfList l).size ≤ l.length := by
  simp only [DHashMap.Raw.Const.unitOfList, DHashMap.Raw.Const.insertManyIfNewUnit]
  split
  · exact r0u_sle 8 l
  · rename_i h; exact (h (Raw₀.emptyWithCapacity 8).2).elim
end
end W6c6
macro "w6u" : tactic => `(tactic| (intros; first
  | exact W6c6.dhu_ofl _ | exact W6c6.dhu_sle _ | exact W6c6.dru_ofl _ | exact W6c6.dru_sle _))
namespace W6c6z
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
export W6c0 (r0c_ms)
export W6c0 (r0_ms)
export W6c0 (drc_ms)
export W6c0 (dr_ms)
export W6c0 (al_kb)
export W6c0 (r0_kb)
export W6c0 (dr_kb)
export W6c0 (r0_sin)
export W6c0 (r0u_le)
export W6c0 (dru_le)
export W6c0 (a_kbq)
export W6c0 (r0_kbq)
export W6c0 (dr_kbq)
export W6c0 (r0_ck)
export W6c0 (dr_ck)
export W6c0 (dr_sin)
end
end W6c6z
macro "w6zbp" : tactic => `(tactic| first
  | (apply DHashMap.Raw.WF.size_buckets_pos; assumption)
  | (apply DHashMap.Raw.WF.size_buckets_pos; apply HashMap.Raw.WF.out; assumption))
macro "w6zev" : tactic => `(tactic| first
  | decide +kernel
  | (hm_eval; done)
  | (hm_eval; decide +kernel)
  | (hm_eval_raw; done)
  | (w1c0_raw; done)
  | (simp; done))
open W6c6z
namespace W6c6z
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
export W6c0 (al_cm)
export W6c0 (al_km)
export W6c0 (ald_cm)
export W6c0 (ald_km)
export W6c0 (set_ix)
export W6c0 (al_kn)
export W6c0 (r0c_cm)
export W6c0 (r0c_km)
end
end W6c6z
namespace W6c6z
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
export W6c0 (modify_gen)
export W6c0 (r0_cm)
export W6c0 (r0_km)
export W6c0 (r0c_k!m)
export W6c0 (r0_k!m)
export W6c0 (dr_c0)
export W6c0 (dr_k0)
export W6c0 (dr_k!0)
export W6c0 (dr_cnb)
export W6c0 (drc_cm)
export W6c0 (dr_knb)
export W6c0 (dr_cm)
export W6c0 (drc_km)
export W6c0 (dr_km)
export W6c0 (drc_k!m)
export W6c0 (dr_k!m)
end
end W6c6z
namespace W6c6z
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
export W6c0 (al_kmg)
export W6c0 (ald_kmg)
export W6c0 (r0c_kmg)
export W6c0 (r0c_k!mg)
end
end W6c6z
namespace W6c6z
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
export W6c0 (r0_kmg)
export W6c0 (r0_k!mg)
export W6c0 (drc_k!mg)
export W6c0 (dr_k!mg)
end
end W6c6z
namespace W6c6z
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
export W6c0 (r0_nc)
export W6c0 (r0_nk)
export W6c0 (r0_nk!)
export W6c0 (r0c_ngD)
export W6c0 (r0_nkD)
export W6c0 (dr_nk)
export W6c0 (dr_nk!)
export W6c0 (drc_ngD)
export W6c0 (dr_nkD)
export W6c0 (lst)
export W6c0 (drc_ofl_keys)
export W6c0 (dc_ofl_keys)
export W6c0 (dr_ofl_keys)
export W6c0 (dm_ofl_keys)
export W6c0 (hsr_ofl_keys)
end
end W6c6z
namespace W6c6y
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
export W5c4 (com_self)
export W5c4 (cex_self)
export W5c4 (mem_uset_self)
export W5c4 (r0_cis)
export W5c4 (r0_ciis)
export W5c4 (dr_cis)
export W5c4 (dr_ciis)
end
end W6c6y
namespace W6c6y
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
-- bundled wrappers of r0_ciis and W6c0's r0c_cm
theorem dh_iis [EquivBEq α] (m : DHashMap α β) (k : α) (v : β k) : k ∈ m.insertIfNew k v :=
  r0_ciis ⟨m.1, m.2.size_buckets_pos⟩ k v
theorem hm_iis [EquivBEq α] (m : HashMap α γ) (k : α) (v : γ) : k ∈ m.insertIfNew k v := dh_iis m.inner k v
theorem dhc_mm [EquivBEq α] (m : DHashMap α (fun _ => γ)) (k k' : α) (f : γ → γ) :
    k' ∈ DHashMap.Const.modify m k f ↔ k' ∈ m :=
  Iff.of_eq (congrArg (· = true) (W6c6z.r0c_cm ⟨m.1, m.2.size_buckets_pos⟩ k k' f))
theorem hm_mm [EquivBEq α] (m : HashMap α γ) (k k' : α) (f : γ → γ) : k' ∈ m.modify k f ↔ k' ∈ m := dhc_mm m.inner k k' f
end
end W6c6y
macro "w6iis" : tactic => `(tactic| (intros; first
  | exact W6c6y.r0_ciis _ _ _
  | exact W6c6y.dh_iis _ _ _
  | exact W6c6y.hm_iis _ _ _
  | exact W6c6y.dr_ciis _ (DHashMap.Raw.WF.size_buckets_pos _ ‹_›) _ _
  | exact W6c6y.dr_ciis _ (DHashMap.Raw.WF.size_buckets_pos _ (HashMap.Raw.WF.out ‹_›)) _ _))
macro "w6mm" : tactic => `(tactic| (intros; first
  | exact Iff.of_eq (congrArg (· = true) (W6c6z.r0c_cm _ _ _ _))
  | exact W6c6y.dhc_mm _ _ _ _
  | exact W6c6y.hm_mm _ _ _ _
  | exact Iff.of_eq (congrArg (· = true) (W6c6z.drc_cm _ _ _ _))
  | exact Iff.of_eq (congrArg (· = true) (W6c6z.dr_cm _ _ _ _))))
namespace W6c6
open Std Std.DHashMap.Internal
-- inter only keeps keys found in m₁ (filter of m₁'s buckets, or fold over m₂ looking up m₁): LawfulHashable only, no WF
theorem inter_nc {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulHashable α] (m₁ m₂ : Raw₀ α β) (k : α)
    (h : m₁.contains k = false) : (m₁.inter m₂).contains k = false := by
  cases hc : (m₁.inter m₂).contains k
  · rfl
  · have := W3c4.ni_r0 m₁ m₂ k hc; rw [h] at this; cases this
end W6c6
macro "w6in" : tactic => `(tactic| (intros; first
  | exact W3c4.r0c_get?_nc _ _ (W6c6.inter_nc _ _ _ ‹_›)
  | exact raw0_cget!_nc _ _ (W6c6.inter_nc _ _ _ ‹_›)
  | exact W3c3.r0c_getD _ _ _ (W6c6.inter_nc _ _ _ ‹_›)
  | exact W3c4.r0_get?_nc _ _ (W6c6.inter_nc _ _ _ ‹_›)
  | exact S1.raw0_get!_nc _ _ (W6c6.inter_nc _ _ _ ‹_›)
  | exact W3c3.r0_getD _ _ _ (W6c6.inter_nc _ _ _ ‹_›)))
namespace W6c6
open Std Std.DHashMap.Internal
-- cheap WF of HZ0 literals #[l, nil] (copy of W1c5.zh_hs / zh_wf)
theorem hz0_hs {β : W4c4.HZ0 → Type v} (l : AssocList W4c4.HZ0 β) : IsHashSelf (#[l, .nil] : Array (AssocList W4c4.HZ0 β)) := by
  refine ⟨fun i hi => ⟨fun h p hp => ?_⟩⟩
  rw [mkIdx_toNat' _ _ _ (by simp [Pow2])]
  have : (scrambleHash (hash p.1)).toNat % 2 = 0 := by
    show (scrambleHash 0).toNat % 2 = 0
    rw [scr_small _ (by decide)]; rfl
  rw [show (#[l, AssocList.nil] : Array (AssocList W4c4.HZ0 β)).size = 2 from rfl, this]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => simp at hp
theorem hz0_wf {β : W4c4.HZ0 → Type v} (s : Nat) (l : AssocList W4c4.HZ0 β) (hs : s = (toListModel #[l, .nil]).length)
    (hd : Std.Internal.List.DistinctKeys (toListModel #[l, .nil])) :
    (⟨s, #[l, .nil]⟩ : DHashMap.Raw W4c4.HZ0 β).WF :=
  .wf (by simp) (fun {_ _} => ⟨hz0_hs l, hs, hd⟩)
end W6c6
namespace W6c6
open Std Std.DHashMap.Internal
-- under HZ0 (hash 0) both literals are looked up in bucket 0, and 0 == k iff 1 == k
theorem hz0_g (k : W4c4.HZ0) :
    Raw₀.Const.get? (⟨⟨1, #[.cons ⟨0⟩ (5 : Nat) .nil, .nil]⟩, by decide⟩ : Raw₀ W4c4.HZ0 (fun _ => Nat)) k =
    Raw₀.Const.get? (⟨⟨1, #[.cons ⟨1⟩ (5 : Nat) .nil, .nil]⟩, by decide⟩ : Raw₀ W4c4.HZ0 (fun _ => Nat)) k := by
  rw [cget?_eval _ (by simp [Pow2]), cget?_eval _ (by simp [Pow2])]
  have e : (scrambleHash (hash k)).toNat % 2 = 0 := by
    show (scrambleHash 0).toNat % 2 = 0
    rw [scr_small _ (by decide)]; rfl
  simp only [ix, List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd, e]
  rfl
end W6c6

/-! ## From `checks/W6c7Hand.lean` -/
namespace W5c4
variable {α : Type u} [BEq α] [Hashable α]
end W5c4
open W5c4
namespace W5c4
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
end
end W5c4
open W5c4
namespace W5c4
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
end
end W5c4
open W5c4
namespace W5c4
end W5c4
namespace W5c4
variable {α : Type u} [BEq α] [Hashable α]
end W5c4
namespace W5c4
end W5c4
namespace W6c3
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
open Std.Internal.List
end
end W6c3
namespace W6c3
section
variable {α : Type u} [BEq α] [Hashable α]
end
end W6c3
namespace W6c7
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
open Std.Internal.List
-- alter changes the size field by at most -1 (no EquivBEq/LawfulHashable/WF)
theorem r0_alter_ge [LawfulBEq α] (m : Raw₀ α β) (a : α) (f : Option (β a) → Option (β a)) :
    m.1.size - 1 ≤ (m.alter a f).1.size := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.alter; dsimp only
  split
  · split <;> simp <;> omega
  · split
    · simp
    · simp [Raw₀.size_expandIfNecessary]; omega
theorem r0c_alter_ge {γ : Type v} (m : Raw₀ α (fun _ => γ)) (a : α) (f : Option γ → Option γ) :
    m.1.size - 1 ≤ (Raw₀.Const.alter m a f).1.size := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.Const.alter; dsimp only
  split
  · split <;> simp <;> omega
  · split
    · simp
    · simp [Raw₀.size_expandIfNecessary]; omega
-- under LawfulBEq a found key is the query itself (no WF)
theorem r0_gkD [LawfulBEq α] (m : Raw₀ α β) (k fb : α) (h : m.contains k) : m.getKeyD k fb = k := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKeyD; unfold Raw₀.contains at h
  simp only [AssocList.getKeyD_eq, getKeyD_eq_getKey?]; simp only [AssocList.contains_eq] at h
  rw [getKey?_eq_some_getKey h]; exact eq_of_beq (getKey_beq h)
theorem r0_gk! [LawfulBEq α] [Inhabited α] (m : Raw₀ α β) (k : α) (h : m.contains k) : m.getKey! k = k := by
  rw [W5c4.r0_k!D]; exact r0_gkD _ _ _ h
theorem dr_gkD [LawfulBEq α] (m : DHashMap.Raw α β) (k fb : α) (h : m.contains k) : m.getKeyD k fb = k := by
  unfold DHashMap.Raw.getKeyD; unfold DHashMap.Raw.contains at h; split
  · exact r0_gkD _ _ _ (by simpa [*] using h)
  · simp_all
theorem dr_gk! [LawfulBEq α] [Inhabited α] (m : DHashMap.Raw α β) (k : α) (h : m.contains k) : m.getKey! k = k := by
  rw [W5c4.dr_k!D]; exact dr_gkD _ _ _ h
end
end W6c7
macro "w7alt" : tactic => `(tactic| first
  | exact W6c7.r0_alter_ge _ _ _ | exact W6c7.r0c_alter_ge _ _ _
  | exact W6c7.r0_alter_ge ⟨_, _⟩ _ _ | exact W6c7.r0c_alter_ge ⟨_, _⟩ _ _
  | (simp only [DHashMap.Const.alter, DHashMap.Const.size, DHashMap.size, DHashMap.alter, HashMap.alter, HashMap.size]; first | exact W6c7.r0c_alter_ge ⟨_, _⟩ _ _ | exact W6c7.r0_alter_ge ⟨_, _⟩ _ _))
macro "w7gk" : tactic => `(tactic| first
  | exact W6c7.r0_gkD _ _ _ ‹_› | exact W6c7.r0_gk! _ _ ‹_›
  | exact W6c7.dr_gkD _ _ _ ‹_› | exact W6c7.dr_gk! _ _ ‹_›
  | exact W6c7.dr_gkD _ _ _ (by assumption) | exact W6c7.dr_gk! _ _ (by assumption))
namespace W6c7
section
variable {α : Type u} [BEq α] [Hashable α]
theorem r0_sin {β : α → Type v} (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insertIfNew a b).1.size = if m.contains a then m.1.size else m.1.size + 1 := by
  obtain ⟨⟨s, bs⟩, h⟩ := m
  unfold Raw₀.insertIfNew Raw₀.contains; dsimp only
  split <;> simp [Raw₀.size_expandIfNecessary]
-- unitOfList of a ==-distinct list adds one entry per key (no EquivBEq/LawfulHashable)
theorem uol_size (l : List α) : ∀ (m : Raw₀ α (fun _ => Unit)),
    (∀ p ∈ toListModel m.1.buckets, ∀ b ∈ l, (p.1 == b) = false) →
    l.Pairwise (fun a b => (a == b) = false) →
    (Raw₀.Const.insertListIfNewUnitₘ m l).1.size = m.1.size + l.length := by
  induction l with
  | nil => intro m _ _; simp [Raw₀.Const.insertListIfNewUnitₘ]
  | cons hd tl ih =>
    intro m hm hl
    have hc : m.contains hd = false := by
      cases h : m.contains hd
      · rfl
      · obtain ⟨p, hp, hpa⟩ := Std.Internal.List.containsKey_eq_true_iff_exists_mem.mp (raw0_contains_tlm m hd h)
        have := hm p hp hd List.mem_cons_self
        rw [this] at hpa; exact absurd hpa (by simp)
    rw [List.pairwise_cons] at hl
    simp only [Raw₀.Const.insertListIfNewUnitₘ]
    rw [ih (m.insertIfNew hd ()) ?_ hl.2, r0_sin, hc]
    · simp; omega
    · intro p hp b hb
      rcases mem_tlm_insertIfNew m hd () p hp with h | h
      · subst h; exact hl.1 b hb
      · exact hm p h b (List.mem_cons_of_mem _ hb)
theorem dhc_uol_size (l : List α) (hl : l.Pairwise (fun a b => (a == b) = false)) :
    (DHashMap.Const.unitOfList l : DHashMap α (fun _ => Unit)).1.size = l.length := by
  have e : (DHashMap.Const.unitOfList l : DHashMap α (fun _ => Unit)).1 =
      (Raw₀.Const.insertListIfNewUnitₘ (Raw₀.emptyWithCapacity 8) l).1 := hs_ofList_raw l
  rw [e, uol_size l _ (by simp) hl]; simp
theorem drc_uol_size (l : List α) (hl : l.Pairwise (fun a b => (a == b) = false)) :
    (DHashMap.Raw.Const.unitOfList l : DHashMap.Raw α (fun _ => Unit)).size = l.length := by
  have e : (DHashMap.Raw.Const.unitOfList l : DHashMap.Raw α (fun _ => Unit)) =
      (Raw₀.Const.insertListIfNewUnitₘ (Raw₀.emptyWithCapacity 8) l).1 := hsr_ofList_raw l
  rw [e, uol_size l _ (by simp) hl]; simp
end
end W6c7
macro "w7uol" : tactic => `(tactic| first
  | exact W6c7.dhc_uol_size _ ‹_› | exact W6c7.drc_uol_size _ ‹_›
  | exact W6c7.dhc_uol_size _ (by assumption) | exact W6c7.drc_uol_size _ (by assumption))

/-! ## From `checks/W7c0Hand.lean` -/
namespace W7c0
export W4c6 (hz_hs)
export W4c6 (hz_wf)
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
-- under LawfulBEq a found key is the query itself (no WF)
theorem r0_gks [LawfulBEq α] (m : Raw₀ α β) (a : α) (h : m.contains a = true) : m.getKey? a = some a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen, AssocList.contains_eq] at h
  unfold Raw₀.getKey?; simp only [Array.ugetElem_eq_getElem, AssocList.getKey?_eq]
  exact Std.Internal.List.getKey?_eq_some h
theorem dr_gks [LawfulBEq α] (m : DHashMap.Raw α β) (a : α) (h : m.contains a = true) : m.getKey? a = some a := by
  unfold DHashMap.Raw.getKey?; unfold DHashMap.Raw.contains at h; split at h
  · rename_i hb; rw [dif_pos hb]; exact r0_gks _ _ h
  · cases h
export W5c4 (r0_mgk)
export W5c4 (dr_mgk)
end
export W5c4 (nb_al)
export W5c4 (nb_nc)
-- in a one-bucket map under AB (== always true) getKey returns the first stored key
theorem ab_gk1 (s : Nat) (k : AB) (t : AssocList AB (fun _ => Unit)) (h) (a : AB) (ha) :
    Raw₀.getKey (⟨⟨s, #[.cons k () t]⟩, h⟩ : Raw₀ AB (fun _ => Unit)) a ha = k := by
  unfold Raw₀.getKey
  simp only [Array.ugetElem_eq_getElem, Array.getElem_singleton]
  rfl
-- under a constant-0 hash every key is looked up in bucket 0 of a 2-bucket map
theorem zh_c0 {β : W1c5.ZH → Type v} (s : Nat) (l : AssocList W1c5.ZH β) (h) (a : W1c5.ZH) :
    Raw₀.contains (⟨⟨s, #[l, .nil]⟩, h⟩ : Raw₀ W1c5.ZH β) a = l.contains a := by
  rw [contains_eval _ (by simp [Pow2])]
  have : ix #[l, .nil] a = 0 := by
    show (scrambleHash 0).toNat % 2 = 0
    rw [scr_small _ (by decide)]; rfl
  simp only [this]; rfl
theorem hz_c0 {β : W4c4.HZ0 → Type v} (s : Nat) (l : AssocList W4c4.HZ0 β) (h) (a : W4c4.HZ0) :
    Raw₀.contains (⟨⟨s, #[l, .nil]⟩, h⟩ : Raw₀ W4c4.HZ0 β) a = l.contains a := by
  rw [contains_eval _ (by simp [Pow2])]
  have : ix #[l, .nil] a = 0 := by
    show (scrambleHash 0).toNat % 2 = 0
    rw [scr_small _ (by decide)]; rfl
  simp only [this]; rfl
section
variable {α : Type u} [BEq α] [Hashable α]
-- insertMany of a cons is insert then insertMany, for any raw map (bucketless: both sides are m)
theorem dr_imc {β : α → Type v} (m : DHashMap.Raw α β) (l : List ((a : α) × β a)) (k : α) (v : β k) :
    m.insertMany (⟨k, v⟩ :: l) = (m.insert k v).insertMany l := by
  unfold DHashMap.Raw.insertMany DHashMap.Raw.insert
  by_cases h : 0 < m.buckets.size
  · rw [dif_pos h, dif_pos h, dif_pos (Raw₀.insert ⟨m, h⟩ k v).2]
    exact congrArg Subtype.val (Raw₀.insertMany_cons (m := ⟨m, h⟩))
  · rw [dif_neg h, dif_neg h, dif_neg h]
theorem drc_imc {β : Type v} (m : DHashMap.Raw α (fun _ => β)) (l : List (α × β)) (k : α) (v : β) :
    DHashMap.Raw.Const.insertMany m ((k, v) :: l) = DHashMap.Raw.Const.insertMany (m.insert k v) l := by
  unfold DHashMap.Raw.Const.insertMany DHashMap.Raw.insert
  by_cases h : 0 < m.buckets.size
  · rw [dif_pos h, dif_pos h, dif_pos (Raw₀.insert ⟨m, h⟩ k v).2]
    exact congrArg Subtype.val (Raw₀.Const.insertMany_cons (m := ⟨m, h⟩))
  · rw [dif_neg h, dif_neg h, dif_neg h]
theorem dru_imc (m : DHashMap.Raw α (fun _ => Unit)) (l : List α) (k : α) :
    DHashMap.Raw.Const.insertManyIfNewUnit m (k :: l) = DHashMap.Raw.Const.insertManyIfNewUnit (m.insertIfNew k ()) l := by
  unfold DHashMap.Raw.Const.insertManyIfNewUnit DHashMap.Raw.insertIfNew
  by_cases h : 0 < m.buckets.size
  · rw [dif_pos h, dif_pos h, dif_pos (Raw₀.insertIfNew ⟨m, h⟩ k ()).2]
    exact congrArg Subtype.val (Raw₀.Const.insertManyIfNewUnit_cons (m := ⟨m, h⟩))
  · rw [dif_neg h, dif_neg h, dif_neg h]
end
end W7c0
namespace W7c0
section
variable {α : Type u} [BEq α] [Hashable α]
-- one-bucket maps: every key is looked up in bucket 0
theorem sb_hs {β : α → Type v} (l : AssocList α β) : IsHashSelf (#[l] : Array (AssocList α β)) := by
  refine ⟨fun i hi => ⟨fun h p hp => ?_⟩⟩
  have h1 := (mkIdx (#[l] : Array (AssocList α β)).size h (hash p.1)).2
  have : (#[l] : Array (AssocList α β)).size = 1 := rfl
  omega
theorem sb_wf {β : α → Type v} (s : Nat) (l : AssocList α β) (hs : s = (toListModel #[l]).length)
    (hd : Std.Internal.List.DistinctKeys (toListModel #[l])) : (⟨s, #[l]⟩ : DHashMap.Raw α β).WF :=
  .wf (by simp) (fun {_ _} => ⟨sb_hs l, hs, hd⟩)
theorem sb_cget? {β : Type v} (s : Nat) (k0 : α) (v : β) (t : AssocList α (fun _ => β)) (h) (a : α)
    (hb : (k0 == a) = true) : Raw₀.Const.get? (⟨⟨s, #[.cons k0 v t]⟩, h⟩ : Raw₀ α (fun _ => β)) a = some v := by
  unfold Raw₀.Const.get?; simp only [Array.ugetElem_eq_getElem, Array.getElem_singleton]
  simp [AssocList.get?, hb]
theorem sb_gk {β : α → Type v} (s : Nat) (k0 : α) (v : β k0) (t : AssocList α β) (h) (a : α) (ha)
    (hb : (k0 == a) = true) : Raw₀.getKey (⟨⟨s, #[.cons k0 v t]⟩, h⟩ : Raw₀ α β) a ha = k0 := by
  unfold Raw₀.getKey; simp only [Array.ugetElem_eq_getElem, Array.getElem_singleton]
  simp [AssocList.getKey, hb]
theorem sb_cget?' {β : Type v} (s : Nat) (l : AssocList α (fun _ => β)) (h) (a : α) :
    Raw₀.Const.get? (⟨⟨s, #[l]⟩, h⟩ : Raw₀ α (fun _ => β)) a = l.get? a := by
  unfold Raw₀.Const.get?; simp only [Array.ugetElem_eq_getElem, Array.getElem_singleton]
-- under LawfulBEq getKey returns the query (copy of W5c4.r0_gk)
open Std.Internal.List in
theorem r0_gk [LawfulBEq α] {β : α → Type v} (m : Raw₀ α β) (a : α) (h' : m.contains a) : m.getKey a h' = a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey; simp only [AssocList.getKey_eq]; exact eq_of_beq (getKey_beq _)
end
end W7c0
namespace W7c0
section
variable {α : Type u} [BEq α] [Hashable α]
-- a key absent from l is absent from any map whose entries all come from l (EquivBEq only)
theorem r0_nc_of [EquivBEq α] (l : List α) (k : α) (m : Raw₀ α (fun _ => Unit))
    (hm : ∀ p ∈ toListModel m.1.buckets, p.1 ∈ l) (hl : l.contains k = false) : m.contains k = false := by
  apply Bool.eq_false_iff.2; intro hc
  obtain ⟨p, hp, -, h2⟩ := raw0_getKey_mem m k hc
  have : l.contains k = true := List.contains_iff_exists_mem_beq.2 ⟨p.1, hm p hp, BEq.symm h2⟩
  rw [hl] at this; cases this
theorem uolr_gkD [EquivBEq α] (l : List α) (k fb : α) (hl : l.contains k = false) :
    DHashMap.Raw.getKeyD (DHashMap.Raw.Const.unitOfList l) k fb = fb := by
  apply W3c3.dr_getKeyD
  unfold DHashMap.Raw.contains; split
  · rename_i hb; exact r0_nc_of l k ⟨_, hb⟩ (W4c3.uolr_entries l) hl
  · rfl
theorem uol_gkD [EquivBEq α] (l : List α) (k fb : α) (hl : l.contains k = false) :
    DHashMap.getKeyD (DHashMap.Const.unitOfList l : DHashMap α (fun _ => Unit)) k fb = fb :=
  W3c3.r0_getKeyD _ _ _ (r0_nc_of l k _ (W4c3.uol_entries l) hl)
end
end W7c0
namespace W7c0
export W6c5 (ns_hs)
end W7c0
-- no key reaches an entry stored in bucket 1 of 2 under ZH (after W5c4's w5nf)
macro "w7nf" : tactic => `(tactic| (
  simp only [HashMap.mem_iff_contains, DHashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains,
    DHashMap.Raw.mem_iff_contains, HashSet.mem_iff_contains, HashSet.Raw.mem_iff_contains, Bool.not_eq_true]
  try simp only [HashSet.contains, HashSet.Raw.contains, HashMap.contains, HashMap.Raw.contains, DHashMap.contains]
  try unfold DHashMap.Raw.contains
  try rw [dif_pos (by decide)]
  first
  | exact W7c0.nb_nc _ _ _ _
  | exact W3c5.hz_unreach _ _ _ _
  | exact W1c5.zh_contains _ _ _))

/-! ## From `checks/W7c1Hand.lean` -/
set_option linter.unusedSimpArgs false
theorem w7_dh : ¬ DHashMap.Equiv ((∅ : DHashMap Nat (fun _ => Nat)).insert 0 0) ∅ := fun h => by
  have := h.size_eq; simp [DHashMap.size_insert] at this
theorem w7_hm : ¬ HashMap.Equiv ((∅ : HashMap Nat Nat).insert 0 0) ∅ := fun h => by
  have := h.size_eq; simp [HashMap.size_insert] at this
theorem w7_hs : ¬ HashSet.Equiv ((∅ : HashSet Nat).insert 0) ∅ := fun h => by
  have := h.size_eq; simp [HashSet.size_insert] at this
theorem w7_dhr : ¬ DHashMap.Raw.Equiv ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0) ∅ := fun h => by
  have := h.size_eq (DHashMap.Raw.WF.empty.insert) DHashMap.Raw.WF.empty; simp [DHashMap.Raw.size_insert, DHashMap.Raw.WF.empty] at this
theorem w7_hmr : ¬ HashMap.Raw.Equiv ((∅ : HashMap.Raw Nat Nat).insert 0 0) ∅ := fun h => by
  have := h.size_eq (HashMap.Raw.WF.empty.insert) HashMap.Raw.WF.empty; simp [HashMap.Raw.size_insert, HashMap.Raw.WF.empty] at this
theorem w7_hsr : ¬ HashSet.Raw.Equiv ((∅ : HashSet.Raw Nat).insert 0) ∅ := fun h => by
  have := h.size_eq (HashSet.Raw.WF.empty.insert) HashSet.Raw.WF.empty; simp [HashSet.Raw.size_insert, HashSet.Raw.WF.empty] at this
theorem w7_diffR [BEq α] [Hashable α] {m₁ m₂ : DHashMap.Raw α β} (h₁ : m₁.WF) : (m₁ \ m₂).WF := by
  simp only [SDiff.sdiff, DHashMap.Raw.diff, h₁.size_buckets_pos, dite_true]
  split
  · simp only [Raw₀.diff]; split
    · exact @DHashMap.Raw.WF.filter₀ α β _ _ m₁ h₁.size_buckets_pos _ h₁
    · exact (Raw₀.eraseManyEntries ⟨m₁, _⟩ m₂).2 _ DHashMap.Raw.WF.erase₀ h₁
  · exact h₁
theorem w7_interR [BEq α] [Hashable α] {m₁ m₂ : DHashMap.Raw α β} (h₁ : m₁.WF) : (m₁ ∩ m₂).WF := by
  simp only [Inter.inter, DHashMap.Raw.inter, h₁.size_buckets_pos, dite_true]
  split
  · exact .wf (Raw₀.inter _ _).2 (by intro _ _; exact Raw₀.wfImp_inter (Std.DHashMap.Internal.Raw.WF.out h₁))
  · exact h₁
theorem w7_diffHMR {β : Type v} [BEq α] [Hashable α] {m₁ m₂ : HashMap.Raw α β} (h₁ : m₁.WF) : (m₁ \ m₂).WF :=
  ⟨w7_diffR (m₂ := m₂.inner) h₁.out⟩
theorem w7_interHMR {β : Type v} [BEq α] [Hashable α] {m₁ m₂ : HashMap.Raw α β} (h₁ : m₁.WF) : (m₁ ∩ m₂).WF :=
  ⟨w7_interR (m₂ := m₂.inner) h₁.out⟩
theorem w7_diffHSR [BEq α] [Hashable α] {m₁ m₂ : HashSet.Raw α} (h₁ : m₁.WF) : (m₁ \ m₂).WF :=
  ⟨w7_diffHMR (m₂ := m₂.inner) h₁.out⟩
theorem w7_interHSR [BEq α] [Hashable α] {m₁ m₂ : HashSet.Raw α} (h₁ : m₁.WF) : (m₁ ∩ m₂).WF :=
  ⟨w7_interHMR (m₂ := m₂.inner) h₁.out⟩
theorem w7_dhr_d : ¬ ((⟨1, nil16⟩ : DHashMap.Raw Nat (fun _ => Nat)) \ (∅ : DHashMap.Raw Nat (fun _ => Nat))).WF := by
  intro h; have := (Std.DHashMap.Internal.Raw.WF.out h).size_eq; revert this; decide +kernel
theorem w7_dhr_u1 : ¬ ((⟨1, nil16⟩ : DHashMap.Raw Nat (fun _ => Nat)) ∪ (∅ : DHashMap.Raw Nat (fun _ => Nat))).WF := by
  intro h; have := (Std.DHashMap.Internal.Raw.WF.out h).size_eq; revert this; decide +kernel
theorem w7_dhr_u2 : ¬ ((∅ : DHashMap.Raw Nat (fun _ => Nat)) ∪ (⟨1, nil16⟩ : DHashMap.Raw Nat (fun _ => Nat))).WF := by
  intro h; have := (Std.DHashMap.Internal.Raw.WF.out h).size_eq; revert this; decide +kernel
theorem w7_dhr_i : ¬ ((⟨0, #[.cons 0 0 (.cons 0 0 .nil), .nil]⟩ : DHashMap.Raw Nat (fun _ => Nat)) ∩ ((∅ : DHashMap.Raw Nat (fun _ => Nat)).insert 0 0)).WF := by
  intro h; have := (Std.DHashMap.Internal.Raw.WF.out h).distinct.distinct; revert this; decide +kernel
theorem w7_hmr_d : ¬ ((⟨⟨1, nil16⟩⟩ : HashMap.Raw Nat Nat) \ (∅ : HashMap.Raw Nat Nat)).WF := by
  intro h; have := (Std.DHashMap.Internal.Raw.WF.out h.out).size_eq; revert this; decide +kernel
theorem w7_hmr_u1 : ¬ ((⟨⟨1, nil16⟩⟩ : HashMap.Raw Nat Nat) ∪ (∅ : HashMap.Raw Nat Nat)).WF := by
  intro h; have := (Std.DHashMap.Internal.Raw.WF.out h.out).size_eq; revert this; decide +kernel
theorem w7_hmr_u2 : ¬ ((∅ : HashMap.Raw Nat Nat) ∪ (⟨⟨1, nil16⟩⟩ : HashMap.Raw Nat Nat)).WF := by
  intro h; have := (Std.DHashMap.Internal.Raw.WF.out h.out).size_eq; revert this; decide +kernel
theorem w7_hmr_i : ¬ ((⟨⟨0, #[.cons 0 0 (.cons 0 0 .nil), .nil]⟩⟩ : HashMap.Raw Nat Nat) ∩ ((∅ : HashMap.Raw Nat Nat).insert 0 0)).WF := by
  intro h; have := (Std.DHashMap.Internal.Raw.WF.out h.out).distinct.distinct; revert this; decide +kernel
theorem w7_hsr_d : ¬ ((⟨⟨⟨1, nil16⟩⟩⟩ : HashSet.Raw Nat) \ (∅ : HashSet.Raw Nat)).WF := by
  intro h; have := (Std.DHashMap.Internal.Raw.WF.out h.out.out).size_eq; revert this; decide +kernel
theorem w7_hsr_u1 : ¬ ((⟨⟨⟨1, nil16⟩⟩⟩ : HashSet.Raw Nat) ∪ (∅ : HashSet.Raw Nat)).WF := by
  intro h; have := (Std.DHashMap.Internal.Raw.WF.out h.out.out).size_eq; revert this; decide +kernel
theorem w7_hsr_u2 : ¬ ((∅ : HashSet.Raw Nat) ∪ (⟨⟨⟨1, nil16⟩⟩⟩ : HashSet.Raw Nat)).WF := by
  intro h; have := (Std.DHashMap.Internal.Raw.WF.out h.out.out).size_eq; revert this; decide +kernel
theorem w7_hsr_i : ¬ ((⟨⟨⟨0, #[.cons 0 () (.cons 0 () .nil), .nil]⟩⟩⟩ : HashSet.Raw Nat) ∩ ((∅ : HashSet.Raw Nat).insert 0)).WF := by
  intro h; have := (Std.DHashMap.Internal.Raw.WF.out h.out.out).distinct.distinct; revert this; decide +kernel
namespace W7c1
section
variable {α : Type u} {β : α → Type v}
export W5c5 (a_gkb)
export W5c5 (r0_gkb)
export W5c5 (dr_gkb)
-- under LawfulBEq a found key is the query itself (no WF)
theorem a_gkq [BEq α] [LawfulBEq α] (l : AssocList α β) (a : α) (h : l.contains a = true) : l.getKey? a = some a := by
  induction l with
  | nil => simp [AssocList.contains] at h
  | cons k v t ih =>
    by_cases hk : k = a
    · subst hk; simp only [AssocList.getKey?, beq_self_eq_true, ite_true]
    · have hb : (k == a) = false := by simpa using hk
      simp only [AssocList.contains, hb, Bool.false_or] at h
      simp only [AssocList.getKey?, hb, Bool.false_eq_true, ite_false]; exact ih h
theorem a_gkx [BEq α] [LawfulBEq α] [Inhabited α] (l : AssocList α β) (a : α) (h : l.contains a = true) : l.getKey! a = a := by
  induction l with
  | nil => simp [AssocList.contains] at h
  | cons k v t ih =>
    by_cases hk : k = a
    · subst hk; simp only [AssocList.getKey!, beq_self_eq_true, ite_true]
    · have hb : (k == a) = false := by simpa using hk
      simp only [AssocList.contains, hb, Bool.false_or] at h
      simp only [AssocList.getKey!, hb, Bool.false_eq_true, ite_false]; exact ih h
theorem a_gkd [BEq α] [LawfulBEq α] (l : AssocList α β) (a fb : α) (h : l.contains a = true) : l.getKeyD a fb = a := by
  induction l with
  | nil => simp [AssocList.contains] at h
  | cons k v t ih =>
    by_cases hk : k = a
    · subst hk; simp only [AssocList.getKeyD, beq_self_eq_true, ite_true]
    · have hb : (k == a) = false := by simpa using hk
      simp only [AssocList.contains, hb, Bool.false_or] at h
      simp only [AssocList.getKeyD, hb, Bool.false_eq_true, ite_false]; exact ih h
theorem r0_gkq [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α) (h : m.contains a = true) : m.getKey? a = some a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.getKey?; simp only [Array.ugetElem_eq_getElem]; exact a_gkq _ _ h
theorem r0_gkx [BEq α] [Hashable α] [LawfulBEq α] [Inhabited α] (m : Raw₀ α β) (a : α) (h : m.contains a = true) : m.getKey! a = a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.getKey!; simp only [Array.ugetElem_eq_getElem]; exact a_gkx _ _ h
theorem r0_gkd [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a fb : α) (h : m.contains a = true) : m.getKeyD a fb = a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  rw [contains_gen] at h; unfold Raw₀.getKeyD; simp only [Array.ugetElem_eq_getElem]; exact a_gkd _ _ _ h
theorem dr_gkq [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (a : α) (h : m.contains a = true) : m.getKey? a = some a := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.getKey?; rw [dite_eq_left hb]; exact r0_gkq _ _ h'
theorem dr_gkx [BEq α] [Hashable α] [LawfulBEq α] [Inhabited α] (m : DHashMap.Raw α β) (a : α) (h : m.contains a = true) : m.getKey! a = a := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.getKey!; rw [dite_eq_left hb]; exact r0_gkx _ _ h'
theorem dr_gkd [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap.Raw α β) (a fb : α) (h : m.contains a = true) : m.getKeyD a fb = a := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.getKeyD; rw [dite_eq_left hb]; exact r0_gkd _ _ _ h'
end
end W7c1
namespace W7c1
open W4c4 in
theorem hz0_e (k : HZ0) : ((⟨0⟩ : HZ0) == k) = ((⟨1⟩ : HZ0) == k) := rfl
-- HZ0 maps {0 ↦ 0} and {1 ↦ 0}: same lookups, different stored keys
theorem hz0_hm : ¬ HashMap.Equiv ((∅ : HashMap W4c4.HZ0 Nat).insert ⟨0⟩ 0) ((∅ : HashMap W4c4.HZ0 Nat).insert ⟨1⟩ 0) := fun h => by
  have := h.getKey?_eq (k := ⟨0⟩); simp [HashMap.getKey?_insert] at this
theorem hz0_hmr : ¬ HashMap.Raw.Equiv ((∅ : HashMap.Raw W4c4.HZ0 Nat).insert ⟨0⟩ 0) ((∅ : HashMap.Raw W4c4.HZ0 Nat).insert ⟨1⟩ 0) := fun h => by
  have := h.getKey?_eq (k := ⟨0⟩) HashMap.Raw.WF.empty.insert HashMap.Raw.WF.empty.insert
  simp [HashMap.Raw.getKey?_insert, HashMap.Raw.WF.empty] at this
theorem hz0_dh : ¬ DHashMap.Equiv ((∅ : DHashMap W4c4.HZ0 (fun _ => Nat)).insert ⟨0⟩ 0) ((∅ : DHashMap W4c4.HZ0 (fun _ => Nat)).insert ⟨1⟩ 0) := fun h => by
  have := h.getKey?_eq (k := ⟨0⟩); simp [DHashMap.getKey?_insert] at this
theorem hz0_dhr : ¬ DHashMap.Raw.Equiv ((∅ : DHashMap.Raw W4c4.HZ0 (fun _ => Nat)).insert ⟨0⟩ 0) ((∅ : DHashMap.Raw W4c4.HZ0 (fun _ => Nat)).insert ⟨1⟩ 0) := fun h => by
  have := h.getKey?_eq (k := ⟨0⟩) DHashMap.Raw.WF.empty.insert DHashMap.Raw.WF.empty.insert
  simp [DHashMap.Raw.getKey?_insert, DHashMap.Raw.WF.empty] at this
theorem hz0_hs : ¬ HashSet.Equiv ((∅ : HashSet W4c4.HZ0).insert ⟨0⟩) ((∅ : HashSet W4c4.HZ0).insert ⟨1⟩) := fun h => by
  have := h.get?_eq (k := ⟨0⟩); simp [HashSet.get?_insert] at this
theorem hz0_hsr : ¬ HashSet.Raw.Equiv ((∅ : HashSet.Raw W4c4.HZ0).insert ⟨0⟩) ((∅ : HashSet.Raw W4c4.HZ0).insert ⟨1⟩) := fun h => by
  have := h.get?_eq (k := ⟨0⟩) HashSet.Raw.WF.empty.insert HashSet.Raw.WF.empty.insert
  simp [HashSet.Raw.get?_insert, HashSet.Raw.WF.empty] at this
-- ZH key in bucket 1 of 2 is never found
theorem zh_cg {γ : Type v} (s : Nat) (l : AssocList W1c5.ZH (fun _ => γ)) (k : W1c5.ZH) :
    DHashMap.Raw.Const.get? (⟨s, #[.nil, l]⟩ : DHashMap.Raw W1c5.ZH (fun _ => γ)) k = none :=
  W3c4.drc_get?_nc _ k (by simp [DHashMap.Raw.mem_iff_contains, DHashMap.Raw.contains, W1c5.zh_contains])
theorem zh_mem (s : Nat) (l : AssocList W1c5.ZH (fun _ => Unit)) (k : W1c5.ZH) :
    ¬ k ∈ (⟨⟨⟨s, #[.nil, l]⟩⟩⟩ : HashSet.Raw W1c5.ZH) := by
  simp [HashSet.Raw.mem_iff_contains, HashSet.Raw.contains, HashMap.Raw.contains, DHashMap.Raw.contains, W1c5.zh_contains]
end W7c1
namespace W7c1
section
variable {α : Type u} {γ : Type v}
export W5c3 (a_cbq)
export W5c3 (a_cqg)
export W5c3 (a_cgb)
theorem r0c_gb [BEq α] [Hashable α] (m : Raw₀ α (fun _ => γ)) (a : α) [Inhabited γ] (h) :
    Raw₀.Const.get m a h = Raw₀.Const.get! m a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.Const.get Raw₀.Const.get!; simp only [Array.ugetElem_eq_getElem]; exact a_cgb _ _ _
theorem drc_gb [BEq α] [Hashable α] (m : DHashMap.Raw α (fun _ => γ)) (a : α) [Inhabited γ] (h : a ∈ m) :
    DHashMap.Raw.Const.get m a h = DHashMap.Raw.Const.get! m a := by
  obtain ⟨hb, h'⟩ := W4c5.dr_pos h
  unfold DHashMap.Raw.Const.get DHashMap.Raw.Const.get!; rw [dite_eq_left hb]; exact r0c_gb _ _ _
end
end W7c1
namespace W7c1
section
variable {α : Type u} {β : α → Type v}
-- the Raw₀ fold/forM lemmas need only buckets; a bucketless raw map gives `pure` on both sides
theorem dr_fk [BEq α] [Hashable α] {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    (f : δ → α → m' δ) (init : δ) :
    m.foldM (fun d a _ => f d a) init = m.keys.foldlM f init := by
  by_cases hb : 0 < m.buckets.size
  · exact Raw₀.foldM_eq_foldlM_keys ⟨m, hb⟩
  · obtain ⟨s, bs⟩ := m
    have : bs = #[] := Array.eq_empty_of_size_eq_zero (Nat.eq_zero_of_not_pos hb)
    subst this; rfl
theorem dr_mk [BEq α] [Hashable α] {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    (f : α → m' PUnit) : ForM.forM m (fun a => f a.1) = m.keys.forM f := by
  by_cases hb : 0 < m.buckets.size
  · exact Raw₀.forM_eq_forM_keys ⟨m, hb⟩
  · obtain ⟨s, bs⟩ := m
    have : bs = #[] := Array.eq_empty_of_size_eq_zero (Nat.eq_zero_of_not_pos hb)
    subst this; rfl
theorem dr_ma [BEq α] [Hashable α] {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    (f : (a : α) → β a → m' PUnit) : m.forM f = m.toArray.forM (fun a => f a.1 a.2) := by
  by_cases hb : 0 < m.buckets.size
  · exact Raw₀.forM_eq_forM_toArray ⟨m, hb⟩
  · obtain ⟨s, bs⟩ := m
    have : bs = #[] := Array.eq_empty_of_size_eq_zero (Nat.eq_zero_of_not_pos hb)
    subst this; rfl
theorem drc_ma {γ : Type v} [BEq α] [Hashable α] {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α (fun _ => γ))
    (f : α → γ → m' PUnit) : m.forM f = (DHashMap.Raw.Const.toArray m).forM (fun a => f a.1 a.2) := by
  by_cases hb : 0 < m.buckets.size
  · exact Raw₀.Const.forM_eq_forM_toArray ⟨m, hb⟩
  · obtain ⟨s, bs⟩ := m
    have : bs = #[] := Array.eq_empty_of_size_eq_zero (Nat.eq_zero_of_not_pos hb)
    subst this; rfl
theorem dr_mka [BEq α] [Hashable α] {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] (m : DHashMap.Raw α β)
    (f : α → m' PUnit) : m.forM (fun a _ => f a) = m.keysArray.forM f := by
  by_cases hb : 0 < m.buckets.size
  · exact Raw₀.forM_eq_forM_keysArray ⟨m, hb⟩
  · obtain ⟨s, bs⟩ := m
    have : bs = #[] := Array.eq_empty_of_size_eq_zero (Nat.eq_zero_of_not_pos hb)
    subst this; rfl
end
end W7c1
namespace W7c1
theorem nb_al {β : NB → Type v} (l : AssocList NB β) (k : NB) : l.contains k = false := by
  induction l with
  | nil => rfl
  | cons a b t ih => simp only [AssocList.contains, NB.beq_def, Bool.false_or, ih]
export W5c4 (nb_nc)
end W7c1

/-! ## From `checks/W7c2Hand.lean` -/
namespace W7c2a
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
export W5c3 (a_cbq)
export W5c3 (a_cdq)
export W5c3 (a_cqg)
export W5c3 (a_kbq)
export W5c3 (a_kdq)
export W5c3 (a_kqg)
export W5c3 (a_gbq)
export W5c3 (a_gdq)
export W5c3 (a_gqg)
export W5c3 (a_cgb)
export W5c3 (a_cgd)
export W5c3 (a_kgb)
export W5c3 (a_kgd)
export W5c3 (a_ggb)
export W5c3 (a_ggd)
export W5c3 (zr0c_bq)
export W5c3 (zdrc_bq)
export W5c3 (zr0c_dq)
export W5c3 (zdrc_dq)
export W5c3 (zr0c_gb)
export W5c3 (zdrc_gb)
export W5c3 (zr0c_gd)
export W5c3 (zdrc_gd)
export W5c3 (zr0c_qg)
export W5c3 (zdrc_qg)
export W5c3 (zr0g_bq)
export W5c3 (zdrg_bq)
export W5c3 (zr0g_dq)
export W5c3 (zdrg_dq)
export W5c3 (zr0g_gb)
export W5c3 (zdrg_gb)
export W5c3 (zr0g_gd)
export W5c3 (zdrg_gd)
export W5c3 (zr0g_qg)
export W5c3 (zdrg_qg)
export W5c3 (zr0k_bq)
export W5c3 (zdrk_bq)
export W5c3 (zr0k_dq)
export W5c3 (zdrk_dq)
export W5c3 (zr0k_gb)
export W5c3 (zdrk_gb)
export W5c3 (zr0k_gd)
export W5c3 (zdrk_gd)
export W5c3 (zr0k_qg)
export W5c3 (zdrk_qg)
end
end W7c2a
namespace W7c2a
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v} {γ : Type v}
export W5c3 (a_cgc)
export W5c3 (a_kgc)
export W5c3 (zr0c_gc)
export W5c3 (zr0k_gc)
export W5c3 (zdrc_gc)
export W5c3 (zdrk_gc)
export W5c3 (al_fm_c)
export W5c3 (r0_fm_c)
export W5c3 (dr_fm_c)
export W5c3 (r0u_sz)
export W5c3 (dru_sz)
end
end W7c2a
namespace W7c2a
open Std Std.DHashMap.Internal
section
variable {α : Type u} {β : α → Type v}
export W5c3 (dr_tlm_filter)
export W5c3 (dr_eqv_filter)
end
end W7c2a
namespace W7c2a
open Std Std.DHashMap.Internal
section
variable {α : Type u}
export W5c3 (z2_c)
export W5c3 (z4_c)
export W5c3 (hz_h)
end
end W7c2a
open W7c2a
set_option Elab.async false
set_option maxHeartbeats 400000
namespace W7c2b
variable {α : Type u} [BEq α] [Hashable α]
export W5c4 (al_gs)
export W5c4 (al_ks)
export W5c4 (r0c_g!D)
export W5c4 (r0_k!D)
export W5c4 (r0c_cs)
export W5c4 (r0_csc)
export W5c4 (r0_ck)
export W5c4 (r0c_gs)
export W5c4 (r0_ks)
export W5c4 (al_gcs)
export W5c4 (r0_gs)
export W5c4 (r0_g!D)
export W5c4 (drc_g!D)
export W5c4 (dr_g!D)
export W5c4 (dr_k!D)
export W5c4 (drc_cs)
export W5c4 (dr_csc)
export W5c4 (dr_ck)
export W5c4 (drc_gs)
export W5c4 (dr_gs)
export W5c4 (dr_ks)
end W7c2b
open W7c2b
macro "w72ev" : tactic => `(tactic| first
  | decide +kernel
  | (hm_eval; done)
  | (simp [DHashMap.Raw.toList, DHashMap.Raw.Const.toList, DHashMap.Raw.toArray, DHashMap.Raw.Const.toArray]; hm_eval; done)
  | (simp [DHashMap.toList, DHashMap.Const.toList, HashMap.toList, HashMap.Raw.toList, DHashMap.toArray, DHashMap.Const.toArray, HashMap.toArray, HashMap.Raw.toArray, HashSet.toArray, HashSet.Raw.toArray, DHashMap.Raw.toList, DHashMap.Raw.Const.toList, DHashMap.Raw.toArray, DHashMap.Raw.Const.toArray, DHashMap.size, HashMap.size, HashSet.size]; hm_eval; done)
  | (hm_eval_raw; done)
  | (w1c0_raw; done)
  | (simp [ExtHashMap.mem_alter]; done)
  | (simp [ExtDHashMap.mem_alter]; done)
  | (simp [ExtDHashMap.Const.mem_alter]; done)
  | (simp [ExtHashMap.contains_alter]; done)
  | (simp [ExtDHashMap.contains_alter]; done)
  | (simp [ExtDHashMap.Const.contains_alter]; done)
  | (simp [ExtHashMap.getKey!_insert]; done)
  | (simp [ExtDHashMap.getKey!_insert]; done)
  | (simp [DHashMap.mem_alter]; done)
  | (simp [DHashMap.Raw.mem_alter, DHashMap.Raw.WF.empty]; done)
  | (simp; done))
macro "w72evt" : tactic => `(tactic| first
  | rfl
  | decide +kernel
  | (simp only [HashMap.mem_iff_contains, HashSet.mem_iff_contains, DHashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains, HashSet.Raw.mem_iff_contains, DHashMap.Raw.mem_iff_contains]; first | decide +kernel | (hm_eval; done) | (hm_eval_raw; done))
  | (hm_eval; done)
  | (hm_eval_raw; done))
namespace W7c2b
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
export W5c4 (r0_gk)
export W5c4 (dr_gk)
export W5c4 (r0_gkc)
export W5c4 (dr_gkc)
export W5c4 (r0_mgk)
export W5c4 (dr_mgk)
end
end W7c2b
open W7c2b
namespace W7c2b
section
variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v}
open Std.Internal.List
export W5c4 (com_self)
export W5c4 (cex_self)
export W5c4 (mem_uset_self)
export W5c4 (r0_cis)
export W5c4 (r0_ciis)
export W5c4 (dr_cis)
export W5c4 (dr_ciis)
end
end W7c2b
open W7c2b
namespace W7c2b
export W5c4 (nb_al)
export W5c4 (nb_nc)
end W7c2b
macro "w72nf" : tactic => `(tactic| (
  simp only [HashMap.mem_iff_contains, DHashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains,
    DHashMap.Raw.mem_iff_contains, Bool.not_eq_true]
  try simp only [HashMap.contains, HashMap.Raw.contains, DHashMap.contains]
  try unfold DHashMap.Raw.contains
  try rw [dif_pos (by decide)]
  first
  | exact W7c2b.nb_nc _ _ _ _
  | exact W3c5.hz_unreach _ _ _ _
  | exact W1c5.zh_contains _ _ _))
namespace W7c2b
variable {α : Type u} [BEq α] [Hashable α]
export W5c4 (nil2_nc)
export W5c4 (r0_gkn)
end W7c2b
macro "w72c" : tactic => `(tactic| first
  | exact W7c2b.nb_nc _ _ _ _
  | exact W3c5.hz_unreach _ _ _ _
  | exact W1c5.zh_contains _ _ _
  | exact W7c2b.nil2_nc _ _ _)
macro "w72gk" : tactic => `(tactic| (
  try simp only [HashMap.getKey?, HashMap.Raw.getKey?, DHashMap.getKey?]
  try unfold DHashMap.Raw.getKey?
  try rw [dif_pos (by decide), dif_pos (by decide)]
  rw [W7c2b.r0_gkn _ _ (by w72c), W7c2b.r0_gkn _ _ (by w72c)]))
macro "w72neq" : tactic => `(tactic| first
  | exact absurd (List.Perm.length_eq this.1) (by decide)
  | exact absurd (List.Perm.length_eq this.1.1) (by decide)
  | exact absurd (List.Perm.length_eq this.1.1.1) (by decide)
  | exact absurd (List.Perm.length_eq this.1) (by simp [toListModel])
  | exact absurd (List.Perm.length_eq this.1.1) (by simp [toListModel])
  | exact absurd (List.Perm.length_eq this.1.1.1) (by simp [toListModel]))
namespace W7c2b
export W5c4 (cg)
export W5c4 (cb)
export W5c4 (ce)
export W5c4 (cg_wf)
export W5c4 (ce_wf)
export W5c4 (cb_nwf)
export W5c4 (cb_eq)
export W5c4 (cg_eq)
export W5c4 (cg_mem)
export W5c4 (cb_mem)
export W5c4 (cg_ne)
end W7c2b
macro "w72ckx" : tactic => `(tactic| first
  | exact (W7c2b.r0c_cs ⟨_, _⟩ _)
  | exact ((W7c2b.r0c_cs ⟨_, _⟩ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W7c2b.r0c_cs ⟨_, _⟩ _))
  | exact Iff.of_eq (congrArg (· = true) ((W7c2b.r0c_cs ⟨_, _⟩ _)).symm)
  | exact (W7c2b.r0c_cs _ _)
  | exact ((W7c2b.r0c_cs _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W7c2b.r0c_cs _ _))
  | exact Iff.of_eq (congrArg (· = true) ((W7c2b.r0c_cs _ _)).symm)
  | exact (W7c2b.r0_ck ⟨_, _⟩ _)
  | exact ((W7c2b.r0_ck ⟨_, _⟩ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W7c2b.r0_ck ⟨_, _⟩ _))
  | exact Iff.of_eq (congrArg (· = true) ((W7c2b.r0_ck ⟨_, _⟩ _)).symm)
  | exact (W7c2b.r0_ck _ _)
  | exact ((W7c2b.r0_ck _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W7c2b.r0_ck _ _))
  | exact Iff.of_eq (congrArg (· = true) ((W7c2b.r0_ck _ _)).symm)
  | exact (W7c2b.r0_csc ⟨_, _⟩ _)
  | exact ((W7c2b.r0_csc ⟨_, _⟩ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W7c2b.r0_csc ⟨_, _⟩ _))
  | exact Iff.of_eq (congrArg (· = true) ((W7c2b.r0_csc ⟨_, _⟩ _)).symm)
  | exact (W7c2b.r0_csc _ _)
  | exact ((W7c2b.r0_csc _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W7c2b.r0_csc _ _))
  | exact Iff.of_eq (congrArg (· = true) ((W7c2b.r0_csc _ _)).symm)
  | exact (W7c2b.drc_cs _ _)
  | exact ((W7c2b.drc_cs _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W7c2b.drc_cs _ _))
  | exact Iff.of_eq (congrArg (· = true) ((W7c2b.drc_cs _ _)).symm)
  | exact (W7c2b.dr_ck _ _)
  | exact ((W7c2b.dr_ck _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W7c2b.dr_ck _ _))
  | exact Iff.of_eq (congrArg (· = true) ((W7c2b.dr_ck _ _)).symm)
  | exact (W7c2b.dr_csc _ _)
  | exact ((W7c2b.dr_csc _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (W7c2b.dr_csc _ _))
  | exact Iff.of_eq (congrArg (· = true) ((W7c2b.dr_csc _ _)).symm)
  | exact (raw0_map_contains _ _ _)
  | exact ((raw0_map_contains _ _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (raw0_map_contains _ _ _))
  | exact Iff.of_eq (congrArg (· = true) ((raw0_map_contains _ _ _)).symm)
  | exact (dr_map_contains _ _ _)
  | exact ((dr_map_contains _ _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (dr_map_contains _ _ _))
  | exact Iff.of_eq (congrArg (· = true) ((dr_map_contains _ _ _)).symm)
  | exact (dm_map_contains _ _ _)
  | exact ((dm_map_contains _ _ _)).symm
  | exact Iff.of_eq (congrArg (· = true) (dm_map_contains _ _ _))
  | exact Iff.of_eq (congrArg (· = true) ((dm_map_contains _ _ _)).symm))
namespace W7c2c
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
open Std.Internal.List
export W6c3 (bk_nil)
export W6c3 (empty_tlm)
export W6c3 (dr_map_perm)
export W6c3 (dr_filterMap_perm)
export W6c3 (dr_map_eqv)
export W6c3 (dr_filterMap_eqv)
end
end W7c2c
namespace W7c2c
section
variable {α : Type u} [BEq α] [Hashable α]
theorem r0c_gn2 {γ : Type v} (m₁ m₂ : Raw₀ α (fun _ => γ)) (h₁ : ∀ k, m₁.contains k = false)
    (h₂ : ∀ k, m₂.contains k = false) (k : α) : Raw₀.Const.get? m₁ k = Raw₀.Const.get? m₂ k := by
  have a := h₁ k; have b := h₂ k
  rw [W7c2b.r0c_cs] at a b; simp only [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at a b
  rw [a, b]
theorem drc_gn2 {γ : Type v} (m₁ m₂ : DHashMap.Raw α (fun _ => γ)) (h₁ : ∀ k, m₁.contains k = false)
    (h₂ : ∀ k, m₂.contains k = false) (k : α) : DHashMap.Raw.Const.get? m₁ k = DHashMap.Raw.Const.get? m₂ k := by
  have a := h₁ k; have b := h₂ k
  rw [W7c2b.drc_cs] at a b; simp only [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at a b
  rw [a, b]
end
end W7c2c
macro "w72ncx" : tactic => `(tactic| (
  try simp only [HashMap.contains, HashMap.Raw.contains, DHashMap.contains]
  try unfold DHashMap.Raw.contains
  try rw [dif_pos (by decide)]
  first
  | exact W7c2b.nb_nc _ _ _ _
  | exact W3c5.hz_unreach _ _ _ _
  | exact W1c5.zh_contains _ _ _
  | exact W7c2b.nil2_nc _ _ _))
namespace W7c2e
export W4c6 (hz_hs)
export W4c6 (hz_wf)
end W7c2e
namespace W7c2e
section
variable {α : Type u} {β : α → Type v} [BEq α]
export W4c6 (al_erase_nc)
export W4c6 (al_contains_erase)
export W4c6 (al_erase_comm)
end
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
export W4c6 (mk_congr)
export W4c6 (r0_erase_eq)
export W4c6 (r0_erase_comm)
export W4c6 (eraseList_foldl)
export W4c6 (r0_eraseList_perm)
export W4c6 (r0_diff_right)
export W4c6 (dr_diff_right)
end
end W7c2e
namespace W7c2e
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
export W4c6 (al_getEntry?_beq)
export W4c6 (al_getEntry?_congr)
export W4c6 (r0_getEntry?_beq)
export W4c6 (r0_getEntry?_congr)
export W4c6 (is_fold)
export W4c6 (r0_inter_right)
export W4c6 (dr_inter_right)
end
end W7c2e
namespace W7c2f
-- getKey? returns a stored key x with x == a (no laws; copy of the W6c0 helpers)
theorem al_kb {α : Type u} {β : α → Type v} [BEq α] (l : AssocList α β) (a : α) : (l.getKey? a).all (· == a) := by
  induction l with
  | nil => rfl
  | cons k v l ih => unfold AssocList.getKey?; split <;> simp_all
theorem r0_kb {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : (m.getKey? a).all (· == a) := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m; exact al_kb _ _
theorem dr_kb {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m : DHashMap.Raw α β) (a : α) : (m.getKey? a).all (· == a) := by
  unfold DHashMap.Raw.getKey?; split
  · exact r0_kb _ _
  · rfl
end W7c2f
macro "w72nfs" : tactic => `(tactic| (
  simp only [HashSet.mem_iff_contains, HashSet.Raw.mem_iff_contains, HashMap.mem_iff_contains, DHashMap.mem_iff_contains, HashMap.Raw.mem_iff_contains,
    DHashMap.Raw.mem_iff_contains, Bool.not_eq_true]
  try simp only [HashSet.contains, HashSet.Raw.contains, HashMap.contains, HashMap.Raw.contains, DHashMap.contains]
  try unfold DHashMap.Raw.contains
  try rw [dif_pos (by decide)]
  first
  | exact W7c2b.nb_nc _ _ _ _
  | exact W3c5.hz_unreach _ _ _ _
  | exact W1c5.zh_contains _ _ _))
macro "w72ee" : tactic => `(tactic| (
  (try simp only [HashSet.Raw.emptyWithCapacity, HashMap.Raw.emptyWithCapacity, DHashMap.Raw.emptyWithCapacity])
  rw [Raw₀.toListModel_buckets_emptyWithCapacity]; simp [toListModel]))
namespace W7c2g
open Std.Internal.List
-- lookups in Raw₀.inter m₁ m₂ at a key that m₂ contains agree with m₁ (only m₁ WF; r0_inter_perm)
theorem r0c_ig! {α : Type u} {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [Inhabited β]
    (m₁ m₂ : Raw₀ α (fun _ => β)) (h₁ : m₁.1.WF) (k : α) (hk : m₂.contains k = true) :
    Raw₀.Const.get! (m₁.inter m₂) k = Raw₀.Const.get! m₁ k := by
  obtain ⟨P, hperm, hP⟩ := W3c1.r0_inter_perm m₁ m₂ h₁ k hk
  obtain ⟨m₁, hb₁⟩ := m₁; obtain ⟨m₂, hb₂⟩ := m₂
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
  rw [Raw₀.Const.get!_eq_getValue! wr, Raw₀.Const.get!_eq_getValue! (Std.DHashMap.Internal.Raw.WF.out h₁),
    getValue!_of_perm wr.distinct hperm, getValue!_eq_getValue?, getValue!_eq_getValue?,
    W3c1.gv_filter _ _ _ (fun p _ hp => hP p hp)]
theorem r0c_igD {α : Type u} {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : Raw₀ α (fun _ => β)) (h₁ : m₁.1.WF) (k : α) (fb : β) (hk : m₂.contains k = true) :
    Raw₀.Const.getD (m₁.inter m₂) k fb = Raw₀.Const.getD m₁ k fb := by
  obtain ⟨P, hperm, hP⟩ := W3c1.r0_inter_perm m₁ m₂ h₁ k hk
  obtain ⟨m₁, hb₁⟩ := m₁; obtain ⟨m₂, hb₂⟩ := m₂
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
  rw [Raw₀.Const.getD_eq_getValueD wr, Raw₀.Const.getD_eq_getValueD (Std.DHashMap.Internal.Raw.WF.out h₁),
    getValueD_of_perm wr.distinct hperm, getValueD_eq_getValue?, getValueD_eq_getValue?,
    W3c1.gv_filter _ _ _ (fun p _ hp => hP p hp)]
theorem r0_ig! {α : Type u} {γ : α → Type v} [BEq α] [Hashable α] [LawfulBEq α]
    (m₁ m₂ : Raw₀ α γ) (h₁ : m₁.1.WF) (k : α) [Inhabited (γ k)] (hk : m₂.contains k = true) :
    (m₁.inter m₂).get! k = m₁.get! k := by
  obtain ⟨P, hperm, hP⟩ := W3c1.r0_inter_perm m₁ m₂ h₁ k hk
  obtain ⟨m₁, hb₁⟩ := m₁; obtain ⟨m₂, hb₂⟩ := m₂
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
  rw [Raw₀.get!_eq_getValueCast! wr, Raw₀.get!_eq_getValueCast! (Std.DHashMap.Internal.Raw.WF.out h₁),
    getValueCast!_of_perm wr.distinct hperm, getValueCast!_eq_getValueCast?, getValueCast!_eq_getValueCast?,
    W3c1.gvc_filter _ _ _ (fun p _ hp => hP p hp)]
theorem r0_igD {α : Type u} {γ : α → Type v} [BEq α] [Hashable α] [LawfulBEq α]
    (m₁ m₂ : Raw₀ α γ) (h₁ : m₁.1.WF) (k : α) (fb : γ k) (hk : m₂.contains k = true) :
    (m₁.inter m₂).getD k fb = m₁.getD k fb := by
  obtain ⟨P, hperm, hP⟩ := W3c1.r0_inter_perm m₁ m₂ h₁ k hk
  obtain ⟨m₁, hb₁⟩ := m₁; obtain ⟨m₂, hb₂⟩ := m₂
  have wr := Raw₀.wfImp_inter (h₁ := hb₁) (h₂ := hb₂) (Std.DHashMap.Internal.Raw.WF.out h₁)
  rw [Raw₀.getD_eq_getValueCastD wr, Raw₀.getD_eq_getValueCastD (Std.DHashMap.Internal.Raw.WF.out h₁),
    getValueCastD_of_perm wr.distinct hperm, getValueCastD_eq_getValueCast?, getValueCastD_eq_getValueCast?,
    W3c1.gvc_filter _ _ _ (fun p _ hp => hP p hp)]
end W7c2g
namespace W7c2h
-- every NT literal #[l, .nil] is IsHashSelf (hash 0; copy of W2c0.cz_hs)
theorem nt_hs {β : NT → Type v} (l : AssocList NT β) : IsHashSelf (#[l, .nil] : Array (AssocList NT β)) := by
  refine ⟨fun i hi => ⟨fun h p hp => ?_⟩⟩
  rw [mkIdx_toNat' _ _ _ (by simp [Pow2])]
  have : (scrambleHash (hash p.1)).toNat % 2 = 0 := by
    show (scrambleHash 0).toNat % 2 = 0
    rw [scr_small _ (by decide)]; rfl
  rw [show (#[l, AssocList.nil] : Array (AssocList NT β)).size = 2 from rfl, this]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => simp at hp
-- a CZ map whose size field 5 differs from its one entry is not WF
theorem cb_nwf : ¬ (⟨5, #[(.cons (CZ.mk 0) (0 : Nat) .nil), .nil]⟩ : DHashMap.Raw CZ (fun _ => Nat)).WF :=
  fun hw => absurd (Std.DHashMap.Internal.Raw.WF.out hw).size_eq (by simp [toListModel])
end W7c2h
namespace W7c2h
-- a one-bucket array is always IsHashSelf (every key lands in bucket 0)
theorem hs1 {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (l : AssocList α β) :
    IsHashSelf (#[l] : Array (AssocList α β)) := by
  refine ⟨fun i hi => ⟨fun h p hp => ?_⟩⟩
  rw [mkIdx_toNat' _ _ _ (by simp [Pow2])]
  match i, hi with
  | 0, _ => simp; exact Nat.mod_one _
theorem hs0 {α : Type u} {β : α → Type v} [BEq α] [Hashable α] : IsHashSelf (#[] : Array (AssocList α β)) :=
  ⟨fun i hi => absurd hi (by simp)⟩
theorem ns_nl : ¬ LawfulBEq NS := fun h => absurd (@LawfulBEq.eq_of_beq NS _ h ⟨1⟩ ⟨2⟩ (by decide)) (by decide)
theorem nt_npe : ¬ PartialEquivBEq NT :=
  fun h => absurd (@PartialEquivBEq.trans NT _ h ⟨0⟩ ⟨1⟩ ⟨2⟩ (by decide) (by decide)) (by decide)
theorem hz_nlh : ¬ LawfulHashable HZ := fun h => @HZ.broken _ h
end W7c2h
namespace W7c2i
open Std.Internal.List
-- every entry of AssocList.Const.alter a f l is an entry of l or has key a (no laws)
theorem calt_mem {α : Type u} [BEq α] {β : Type v} (a : α) (f : Option β → Option β) :
    ∀ (l : AssocList α (fun _ => β)) (p : (_ : α) × β), p ∈ (AssocList.Const.alter a f l).toList → p ∈ l.toList ∨ p.1 = a
  | .nil, p, hp => by
    simp only [AssocList.Const.alter] at hp; split at hp <;> simp_all
  | .cons k v l, p, hp => by
    simp only [AssocList.Const.alter] at hp
    split at hp
    · split at hp
      · exact .inl (by simp [hp])
      · simp only [AssocList.toList_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact .inr rfl
        · exact .inl (by simp [hp])
    · simp only [AssocList.toList_cons, List.mem_cons] at hp
      rcases hp with hp | hp
      · simp_all
      · rcases calt_mem a f l p hp with h | h <;> simp_all
-- isHashSelf_updateBucket_alter (Const) without LawfulHashable: altered entries keep their bucket or get key a
theorem r0c_hsua {α : Type u} {β : Type v} [BEq α] [Hashable α] {m : Raw₀ α (fun _ => β)}
    (h : Raw.WFImp m.1) {a : α} {f : Option β → Option β} :
    IsHashSelf (updateBucket m.1.buckets m.2 a (AssocList.Const.alter a f)) := by
  rw [updateBucket]
  refine IsHashSelf.uset (fun h' => ⟨fun _ p hp => ?_⟩) h.buckets_hash_self
  rcases calt_mem a f _ p hp with hp | hp
  · exact h'.hash_self _ _ hp
  · rw [hp]
end W7c2i
namespace W7c2i
theorem r0c_hscons {α : Type u} {β : Type v} [BEq α] [Hashable α] {m : Raw₀ α (fun _ => β)}
    (h : IsHashSelf m.1.buckets) (a : α) (b : β) : IsHashSelf (m.consₘ a b).1.buckets := by
  show IsHashSelf (updateBucket m.1.buckets m.2 a (fun l => l.cons a b))
  rw [updateBucket]
  refine IsHashSelf.uset (fun h' => ⟨fun _ p hp => ?_⟩) h
  simp only [AssocList.toList_cons, List.mem_cons] at hp
  rcases hp with rfl | hp
  · rfl
  · exact h'.hash_self _ _ hp
theorem r0_hsexp {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m : Raw₀ α β) (h : IsHashSelf m.1.buckets) :
    IsHashSelf (Raw₀.expandIfNecessary m).1.buckets := by
  obtain ⟨⟨s, bs⟩, hm⟩ := m
  unfold Raw₀.expandIfNecessary; dsimp only
  split
  · exact h
  · exact W1c5.isHashSelf_expand' _
-- isHashSelf_alterₘ (Const) without EquivBEq/LawfulHashable (only IsHashSelf of m is used)
theorem r0c_hsalt {α : Type u} {β : Type v} [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β))
    (h : Raw.WFImp m.1) (a : α) (f : Option β → Option β) : IsHashSelf (Raw₀.Const.alterₘ m a f).1.buckets := by
  unfold Raw₀.Const.alterₘ
  split
  · exact r0c_hsua h
  · split
    · exact h.buckets_hash_self
    · exact r0_hsexp _ (r0c_hscons h.buckets_hash_self _ _)
end W7c2i

/-! ## From `checks/W7c3Hand.lean` -/
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
namespace W7c3
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
export W5c2 (e_ins)
export W5c2 (il_ge)
export W5c2 (r0_ofl)
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
namespace W7c3
export W6c4 (mk_eq)
export W6c4 (al_gm)
export W6c4 (al_g!)
export W6c4 (al_gnc)
export W6c4 (r0_gm)
export W6c4 (r0_g!m)
export W6c4 (dr_gm)
end W7c3
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

/-! ## From `checks/W7c4Hand.lean` -/
namespace W7c4
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
export W6c0 (a_kbq)
export W6c0 (r0_kbq)
export W6c0 (r0_ck)
export W6c0 (r0_nc)
theorem r0_nk [EquivBEq α] (m : Raw₀ α β) (k : α) (hk : ∀ p ∈ toListModel m.1.buckets, (k == p.1) = false) :
    m.getKey? k = none := W3c4.r0_getKey?_nc m k (r0_nc m k hk)
theorem r0_nk! [EquivBEq α] [Inhabited α] (m : Raw₀ α β) (k : α) (hk : ∀ p ∈ toListModel m.1.buckets, (k == p.1) = false) :
    m.getKey! k = default := raw0_getKey!_nc m k (r0_nc m k hk)
theorem r0_nkD [EquivBEq α] (m : Raw₀ α β) (k : α) (fb : α)
    (hk : ∀ p ∈ toListModel m.1.buckets, (k == p.1) = false) : m.getKeyD k fb = fb :=
  W4c5.r0_kD m k fb (r0_nc m k hk)
theorem r0c_ng [EquivBEq α] (m : Raw₀ α (fun _ => γ)) (k : α)
    (hk : ∀ p ∈ toListModel m.1.buckets, (k == p.1) = false) : Raw₀.Const.get? m k = none :=
  W3c4.r0c_get?_nc m k (r0_nc m k hk)
theorem r0c_ng! [EquivBEq α] [Inhabited γ] (m : Raw₀ α (fun _ => γ)) (k : α)
    (hk : ∀ p ∈ toListModel m.1.buckets, (k == p.1) = false) : Raw₀.Const.get! m k = default :=
  raw0_cget!_nc m k (r0_nc m k hk)
export W6c0 (r0c_ngD)
export W6c0 (lst)
-- entries of a map built by the dependent insertListₘ come from the start map or the list (no laws)
theorem tlm_insertListD (P : ((a : α) × β a) → Prop) (l : List ((a : α) × β a)) :
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
theorem e_nil (c : Nat) (P : ((a : α) × β a) → Prop) :
    ∀ p ∈ toListModel (Raw₀.emptyWithCapacity (α := α) (β := β) c).1.buckets, P p := by
  intro p hp; simp [Raw₀.emptyWithCapacity, toListModel] at hp
  obtain ⟨a, ⟨_, rfl⟩, h⟩ := hp; simp at h
-- keys of insertMany / insertManyIfNewUnit from an empty map: only keys of l
theorem im_keys (c : Nat) (l : List ((a : α) × β a)) (k : α) (h : (l.map Sigma.fst).contains k = false) :
    ∀ p ∈ toListModel (Raw₀.insertMany (Raw₀.emptyWithCapacity (α := α) (β := β) c) l).1.1.buckets, (k == p.1) = false := by
  rw [Raw₀.insertMany_eq_insertListₘ]
  exact tlm_insertListD (fun p => (k == p.1) = false) l _ (e_nil c _) (fun a ha => lst Sigma.fst l k h a ha)
theorem cim_keys (c : Nat) (l : List (α × γ)) (k : α) (h : (l.map Prod.fst).contains k = false) :
    ∀ p ∈ toListModel (Raw₀.Const.insertMany (Raw₀.emptyWithCapacity (α := α) (β := fun _ => γ) c) l).1.1.buckets, (k == p.1) = false := by
  rw [Raw₀.Const.insertMany_eq_insertListₘ]
  exact tlm_insertList (fun p => (k == p.1) = false) l _ (e_nil c _) (fun a ha => lst Prod.fst l k h a ha)
theorem uim_keys (c : Nat) (l : List α) (k : α) (h : l.contains k = false) :
    ∀ p ∈ toListModel (Raw₀.Const.insertManyIfNewUnit (Raw₀.emptyWithCapacity (α := α) (β := fun _ => Unit) c) l).1.1.buckets, (k == p.1) = false := by
  rw [Raw₀.Const.insertManyIfNewUnit_eq_insertListIfNewUnitₘ]
  exact tlm_insertListIfNewUnit (fun p => (k == p.1) = false) l _ (e_nil c _) (fun a ha => lst id l k (by simpa using h) a ha)
theorem r0_kB [Inhabited α] (m : Raw₀ α β) (k : α) (h : m.contains k = false) : m.getKey! k = default :=
  raw0_getKey!_nc m k h
end
end W7c4
namespace W7c4
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} {γ : Type v} [BEq α] [Hashable α]
-- getKeyD respects == on any map (same bucket by LawfulHashable, list lemma needs only EquivBEq)
theorem r0_gkdc [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) (k k' fb : α) (h : k == k') :
    m.getKeyD k fb = m.getKeyD k' fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKeyD; simp only [hash_eq h, AssocList.getKeyD_eq]; exact Std.Internal.List.getKeyD_congr h
theorem dr_gkdc [EquivBEq α] [LawfulHashable α] (m : DHashMap.Raw α β) (k k' fb : α) (h : k == k') :
    m.getKeyD k fb = m.getKeyD k' fb := by
  unfold DHashMap.Raw.getKeyD; split
  · exact r0_gkdc _ _ _ _ h
  · rfl
-- Const.get? / Const.getD and get? / getD scan the same bucket; no WF
theorem r0c_gg [LawfulBEq α] (m : Raw₀ α (fun _ => γ)) (a : α) : Raw₀.Const.get? m a = m.get? a := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.Const.get? Raw₀.get?; simp only [AssocList.get?_eq, AssocList.getCast?_eq]
  exact Std.Internal.List.getValue?_eq_getValueCast?
theorem r0c_gD [LawfulBEq α] (m : Raw₀ α (fun _ => γ)) (a : α) (fb : γ) : Raw₀.Const.getD m a fb = m.getD a fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.Const.getD Raw₀.getD; simp only [AssocList.getD_eq, AssocList.getCastD_eq]
  exact Std.Internal.List.getValueD_eq_getValueCastD
theorem drc_gg [LawfulBEq α] (m : DHashMap.Raw α (fun _ => γ)) (a : α) : DHashMap.Raw.Const.get? m a = m.get? a := by
  unfold DHashMap.Raw.Const.get? DHashMap.Raw.get?; split
  · exact r0c_gg _ _
  · rfl
theorem drc_gD [LawfulBEq α] (m : DHashMap.Raw α (fun _ => γ)) (a : α) (fb : γ) : DHashMap.Raw.Const.getD m a fb = m.getD a fb := by
  unfold DHashMap.Raw.Const.getD DHashMap.Raw.getD; split
  · exact r0c_gD _ _ _
  · rfl
end
-- closes `hyp → False` for literal maps: apply the hypothesis to up to three decidable premises
macro "w7c" : tactic => `(tactic| (intro hh; first
  | exact absurd hh (by decide +kernel)
  | exact absurd (hh (by decide +kernel)) (by decide +kernel)
  | exact absurd (hh (by decide +kernel) (by decide +kernel)) (by decide +kernel)
  | exact absurd (hh (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)
  | exact absurd (hh (by decide +kernel) (by decide +kernel) (by simp)) (by decide +kernel)
  | exact absurd (hh (by decide +kernel) (by simp)) (by decide +kernel)))
end W7c4
namespace W7c4
export W4c6 (hz_hs)
export W4c6 (hz_wf)
end W7c4
namespace W7c4
-- under a hash that is constantly 0, a two-bucket literal is searched in bucket 0 only
theorem c0_contains {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (hz : ∀ a : α, hash a = 0) (s : Nat)
    (l0 l1 : AssocList α β) (a : α) :
    Raw₀.contains (⟨⟨s, #[l0, l1]⟩, by simp⟩ : Raw₀ α β) a = l0.contains a := by
  rw [contains_eval _ (by simp [Pow2])]
  have : ix #[l0, l1] a = 0 := by
    show (scrambleHash (hash a)).toNat % 2 = 0
    rw [hz a, scr_small _ (by decide)]; rfl
  simp only [this]; rfl
end W7c4
namespace W7c4
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
-- filter keeps a key whose stored == entries all pass the predicate
theorem al_filter_keep (f : (a : α) → β a → Bool) (a : α) (l : AssocList α β)
    (hf : ∀ q ∈ l.toList, (q.1 == a) = true → f q.1 q.2 = true) (h : l.contains a = true) :
    (l.filter f).contains a = true := by
  simp only [AssocList.contains_eq, ck_any, (AssocList.toList_filter (f := f) (l := l)).any_eq, List.any_filter] at h ⊢
  simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨x, hx, hx2⟩ := h; exact ⟨x, hx, hf x hx hx2, hx2⟩
theorem r0_filter_keep (f : (a : α) → β a → Bool) (m : Raw₀ α β) (k : α)
    (hf : ∀ (x : α) (v : β x), (x == k) = true → f x v = true) (h : m.contains k = true) :
    (Raw₀.filter f m).contains k = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have e : Raw₀.filter f ⟨⟨s, bs⟩, hb⟩ =
      ⟨⟨computeSize (bs.map (AssocList.filter f)), bs.map (AssocList.filter f)⟩, by simpa using hb⟩ := rfl
  rw [e, contains_gen, map_idx _ _ _ hb]
  rw [contains_gen] at h; exact al_filter_keep _ _ _ (fun q _ hq => hf q.1 q.2 hq) h
theorem isf_keep [EquivBEq α] [LawfulHashable α] (m₁ acc : Raw₀ α β) (x k : α) (h : acc.contains k = true) :
    (Raw₀.interSmallerFn m₁ acc x).contains k = true := by
  unfold Raw₀.interSmallerFn; split
  · exact W2c0.contains_insert_of _ _ _ _ h
  · exact h
theorem isf_hit [EquivBEq α] [LawfulHashable α] (m₁ acc : Raw₀ α β) (x k : α) (hx : (x == k) = true)
    (hk : m₁.contains k = true) : (Raw₀.interSmallerFn m₁ acc x).contains k = true := by
  have hc : m₁.contains x = true := by rw [W3c1.r0_contains_congr _ hx]; exact hk
  unfold Raw₀.interSmallerFn; split
  · rename_i e he
    have h2 : (e.1 == x) = true := by
      obtain ⟨⟨s, bs⟩, hb⟩ := m₁
      have h' : (bs[(mkIdx bs.size hb (hash x)).1.toNat]'(mkIdx bs.size hb (hash x)).2).getEntry? x = some e := by
        unfold Raw₀.getEntry? at he; simpa only [Array.ugetElem_eq_getElem] using he
      exact (W3c4.a_getEntry_mem _ _ _ h').2
    rw [← W3c1.r0_contains_congr _ (BEq.trans h2 hx)]; exact raw0_contains_insert_self _ _ _
  · rename_i he
    exfalso
    obtain ⟨⟨s, bs⟩, hb⟩ := m₁
    unfold Raw₀.getEntry? at he; unfold Raw₀.contains at hc
    simp only [Array.ugetElem_eq_getElem, AssocList.getEntry?_eq, AssocList.contains_eq] at he hc
    rw [Std.Internal.List.containsKey_eq_isSome_getEntry?, he] at hc; simp at hc
theorem fold_keep [EquivBEq α] [LawfulHashable α] (m₁ : Raw₀ α β) (k : α) (hk : m₁.contains k = true) :
    ∀ (l : List ((a : α) × β a)) (acc : Raw₀ α β), (acc.contains k = true ∨ ∃ b ∈ l, (b.1 == k) = true) →
      (l.foldl (fun a b => Raw₀.interSmallerFn m₁ a b.1) acc).contains k = true
  | [], acc, h => by
    rcases h with h | ⟨b, hb, -⟩
    · exact h
    · cases hb
  | b :: l, acc, h => by
    simp only [List.foldl_cons]
    apply fold_keep m₁ k hk l
    by_cases hbk : (b.1 == k) = true
    · left; exact isf_hit _ _ _ _ hbk hk
    · rcases h with h | ⟨b', hb', hbk'⟩
      · left; exact isf_keep _ _ _ _ h
      · rcases List.mem_cons.1 hb' with rfl | hb'
        · exact absurd hbk' hbk
        · right; exact ⟨b', hb', hbk'⟩
-- contains_inter_iff without m₁.WF
theorem r0_inter_iff [EquivBEq α] [LawfulHashable α] (m₁ m₂ : Raw₀ α β) (h₂ : m₂.1.WF) (k : α) :
    (m₁.inter m₂).contains k = true ↔ m₁.contains k = true ∧ m₂.contains k = true := by
  constructor
  · intro h
    refine ⟨W3c4.ni_r0 _ _ _ h, ?_⟩
    cases hc : m₂.contains k
    · rw [W3c3.r0_nmi _ _ h₂ _ hc] at h; exact absurd h (by simp)
    · rfl
  · rintro ⟨h1, h2⟩
    unfold Raw₀.inter; split
    · exact r0_filter_keep _ _ _ (fun x _ hx => by rw [W3c1.r0_contains_congr _ hx]; exact h2) h1
    · unfold Raw₀.interSmaller
      rw [Raw.fold_eq_foldl_toListModel]
      apply fold_keep m₁ k h1
      right
      obtain ⟨p, hp, hpk⟩ := Std.Internal.List.containsKey_eq_true_iff_exists_mem.mp (raw0_contains_tlm _ k h2)
      exact ⟨p, hp, hpk⟩
end
end W7c4
namespace W7c4
section
set_option linter.unusedSectionVars false
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
theorem a_kDq (l : AssocList α β) (a fb : α) : l.getKeyD a fb = (l.getKey? a).getD fb := by
  induction l with
  | nil => rfl
  | cons k v t ih => cases hk : (k == a) <;> simp_all [AssocList.getKeyD, AssocList.getKey?]
theorem r0_kDq (m : Raw₀ α β) (a fb : α) : Raw₀.getKeyD m a fb = (Raw₀.getKey? m a).getD fb := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  unfold Raw₀.getKey? Raw₀.getKeyD; simp only [Array.ugetElem_eq_getElem]; exact a_kDq _ _ _
-- in a WF map, a getEntry? hit for x == k is what getKey? k returns
theorem ge_gk [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) (hm : m.1.WF) (x k : α) (e : (a : α) × β a)
    (he : m.getEntry? x = some e) (hx : (x == k) = true) : m.getKey? k = some e.1 := by
  have w := Std.DHashMap.Internal.Raw.WF.out hm
  rw [Raw₀.getKey?_eq_getKey? w, Std.Internal.List.getKey?_eq_getEntry?,
    ← Std.Internal.List.getEntry?_congr hx, ← Raw₀.getEntry?_eq_getEntry? w, he]; rfl
theorem ge_beq (m : Raw₀ α β) (x : α) (e : (a : α) × β a) (he : m.getEntry? x = some e) : (e.1 == x) = true := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  have h' : (bs[(mkIdx bs.size hb (hash x)).1.toNat]'(mkIdx bs.size hb (hash x)).2).getEntry? x = some e := by
    unfold Raw₀.getEntry? at he; simpa only [Array.ugetElem_eq_getElem] using he
  exact (W3c4.a_getEntry_mem _ _ _ h').2
-- one interSmaller step on a WF accumulator: stays WF, getKey? k is unchanged or becomes m₁.getKey? k
theorem isf_step [EquivBEq α] [LawfulHashable α] (m₁ : Raw₀ α β) (h₁ : m₁.1.WF) (k : α) (acc : Raw₀ α β) (x : α)
    (hw : acc.1.WF) : (Raw₀.interSmallerFn m₁ acc x).1.WF ∧
      ((Raw₀.interSmallerFn m₁ acc x).getKey? k = acc.getKey? k ∨
        (Raw₀.interSmallerFn m₁ acc x).getKey? k = m₁.getKey? k) := by
  unfold Raw₀.interSmallerFn; split
  · rename_i e he
    obtain ⟨acc, ha⟩ := acc
    refine ⟨Std.DHashMap.Raw.WF.insert₀ hw, ?_⟩
    rw [Raw₀.getKey?_insert (h := hw)]
    split
    · rename_i hek; right
      exact (ge_gk m₁ h₁ x k e he (BEq.trans (BEq.symm (ge_beq m₁ x e he)) hek)).symm
    · left; rfl
  · exact ⟨hw, Or.inl rfl⟩
theorem isf_hit2 [EquivBEq α] [LawfulHashable α] (m₁ : Raw₀ α β) (h₁ : m₁.1.WF) (k : α) (acc : Raw₀ α β) (x : α)
    (hw : acc.1.WF) (hx : (x == k) = true) (hk : m₁.contains k = true) :
    (Raw₀.interSmallerFn m₁ acc x).getKey? k = m₁.getKey? k := by
  have hc : m₁.contains x = true := by rw [W3c1.r0_contains_congr _ hx]; exact hk
  unfold Raw₀.interSmallerFn; split
  · rename_i e he
    obtain ⟨acc, ha⟩ := acc
    rw [Raw₀.getKey?_insert (h := hw), if_pos (BEq.trans (ge_beq m₁ x e he) hx)]
    exact (ge_gk m₁ h₁ x k e he hx).symm
  · rename_i he
    exfalso
    obtain ⟨⟨s, bs⟩, hb⟩ := m₁
    unfold Raw₀.getEntry? at he; unfold Raw₀.contains at hc
    simp only [Array.ugetElem_eq_getElem, AssocList.getEntry?_eq, AssocList.contains_eq] at he hc
    rw [Std.Internal.List.containsKey_eq_isSome_getEntry?, he] at hc; simp at hc
theorem fold_gk [EquivBEq α] [LawfulHashable α] (m₁ : Raw₀ α β) (h₁ : m₁.1.WF) (k : α) (hk : m₁.contains k = true) :
    ∀ (l : List ((a : α) × β a)) (acc : Raw₀ α β), acc.1.WF →
      (acc.getKey? k = m₁.getKey? k ∨ ∃ b ∈ l, (b.1 == k) = true) →
      (l.foldl (fun a b => Raw₀.interSmallerFn m₁ a b.1) acc).getKey? k = m₁.getKey? k
  | [], acc, _, h => by
    rcases h with h | ⟨b, hb, -⟩
    · exact h
    · cases hb
  | b :: l, acc, hw, h => by
    simp only [List.foldl_cons]
    obtain ⟨hw', hs⟩ := isf_step m₁ h₁ k acc b.1 hw
    apply fold_gk m₁ h₁ k hk l _ hw'
    by_cases hbk : (b.1 == k) = true
    · left; exact isf_hit2 m₁ h₁ k acc b.1 hw hbk hk
    · rcases h with h | ⟨b', hb', hbk'⟩
      · left; rcases hs with hs | hs
        · rw [hs, h]
        · exact hs
      · rcases List.mem_cons.1 hb' with rfl | hb'
        · exact absurd hbk' hbk
        · right; exact ⟨b', hb', hbk'⟩
-- getKey?_inter_of_contains_right without m₂.WF
theorem r0_inter_gk [EquivBEq α] [LawfulHashable α] (m₁ m₂ : Raw₀ α β) (h₁ : m₁.1.WF) (k : α)
    (h : m₂.contains k = true) : (m₁.inter m₂).getKey? k = m₁.getKey? k := by
  cases hc : m₁.contains k
  · have : (m₁.inter m₂).contains k = false := by
      cases h' : (m₁.inter m₂).contains k
      · rfl
      · rw [W3c4.ni_r0 _ _ _ h'] at hc; exact absurd hc (by simp)
    rw [W3c4.r0_getKey?_nc _ _ this, W3c4.r0_getKey?_nc _ _ hc]
  · unfold Raw₀.inter; split
    · rw [Raw₀.getKey?_filter_key (f := fun k => m₂.contains k) (h := h₁)]
      cases hg : m₁.getKey? k with
      | none => rfl
      | some s =>
        have hb := Raw₀.getKey?_beq (h := h₁) (a := k); rw [hg] at hb
        simp only [Option.all_some] at hb
        simp [Option.filter_some, W3c1.r0_contains_congr m₂ hb, h]
    · unfold Raw₀.interSmaller; rw [Raw.fold_eq_foldl_toListModel]
      apply fold_gk m₁ h₁ k hc _ _ Std.DHashMap.Raw.WF.emptyWithCapacity₀
      right
      obtain ⟨p, hp, hpk⟩ := Std.Internal.List.containsKey_eq_true_iff_exists_mem.mp (raw0_contains_tlm _ k h)
      exact ⟨p, hp, hpk⟩
theorem r0_inter_gk! [EquivBEq α] [LawfulHashable α] [Inhabited α] (m₁ m₂ : Raw₀ α β) (h₁ : m₁.1.WF) (k : α)
    (h : m₂.contains k = true) : (m₁.inter m₂).getKey! k = m₁.getKey! k := by
  rw [r0_kbq, r0_kbq, r0_inter_gk m₁ m₂ h₁ k h]
theorem r0_inter_gkD [EquivBEq α] [LawfulHashable α] (m₁ m₂ : Raw₀ α β) (h₁ : m₁.1.WF) (k fb : α)
    (h : m₂.contains k = true) : (m₁.inter m₂).getKeyD k fb = m₁.getKeyD k fb := by
  rw [r0_kDq, r0_kDq, r0_inter_gk m₁ m₂ h₁ k h]
end
end W7c4

/-! ## From `checks/W7c5Hand.lean` -/
namespace W7c5
open Std.Internal.List Std.DHashMap.Internal.List
theorem split {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulHashable α]
    (self : Array (AssocList α β)) (h₀ : 0 < self.size) (hs : IsHashSelf self) (a : α) :
    ∃ l₁ l₃, toListModel self = l₁ ++ (bucket self h₀ a).toList ++ l₃ ∧
      containsKey a l₁ = false ∧ containsKey a l₃ = false := by
  have hi := (mkIdx self.size h₀ (hash a)).2
  obtain ⟨l₁, l₂, h₁, h₂, -⟩ := Array.exists_of_uset (d := (AssocList.nil : AssocList α β)) hi
  refine ⟨l₁.flatMap AssocList.toList, l₂.flatMap AssocList.toList, ?_, ?_, ?_⟩
  · rw [toListModel, h₁, bucket_eq]; simp
  · apply Std.Internal.List.containsKey_flatMap_eq_false
    intro j hj
    rw [List.getElem_append_left' (l₂ := self[(mkIdx self.size h₀ (hash a)).1] :: l₂),
      getElem_congr_coll h₁.symm]
    apply (hs.hashes_to j _).containsKey_eq_false h₀ a
    omega
  · apply Std.Internal.List.containsKey_flatMap_eq_false
    intro j hj
    rw [← List.getElem_cons_succ self[(mkIdx self.size h₀ (hash a)).1] _ _
      (by simp only [List.length_cons]; omega)]
    rw [List.getElem_append_right' l₁, getElem_congr_coll h₁.symm]
    apply (hs.hashes_to (j + 1 + l₁.length) _).containsKey_eq_false h₀ a
    omega
theorem ab {α : Type u} {β : α → Type v} {γ : Type w} [BEq α] [Hashable α] [LawfulHashable α]
    {m : Raw₀ α β} (hs : IsHashSelf m.1.buckets) {a : α} {f : AssocList α β → γ}
    {g : List ((a : α) × β a) → γ} (hfg : ∀ {l}, f l = g l.toList)
    (hg : ∀ {l₁ l₂ l₃}, containsKey a l₁ = false → containsKey a l₃ = false → g (l₁ ++ l₂ ++ l₃) = g l₂) :
    f (bucket m.1.buckets m.2 a) = g (toListModel m.1.buckets) := by
  obtain ⟨l₁, l₃, e, h₁, h₃⟩ := split m.1.buckets m.2 hs a
  rw [e, hfg, hg h₁ h₃]
theorem ge {α : Type u} {β : α → Type v} [BEq α] {a : α} {l₁ l₂ l₃ : List ((a : α) × β a)}
    (h₁ : containsKey a l₁ = false) (h₃ : containsKey a l₃ = false) :
    getEntry? a (l₁ ++ l₂ ++ l₃) = getEntry? a l₂ := by
  rw [getEntry?_append, getEntry?_append, getEntry?_eq_none.2 h₁, getEntry?_eq_none.2 h₃]
  simp
section
variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulHashable α] {m : Raw₀ α β}
theorem b_c (hs : IsHashSelf m.1.buckets) {a : α} : m.containsₘ a = containsKey a (toListModel m.1.buckets) :=
  ab hs AssocList.contains_eq (fun h₁ h₃ => by
    rw [containsKey_eq_isSome_getEntry?, containsKey_eq_isSome_getEntry?, ge h₁ h₃])
theorem b_e (hs : IsHashSelf m.1.buckets) {a : α} : m.getEntry?ₘ a = getEntry? a (toListModel m.1.buckets) :=
  ab hs AssocList.getEntry?_eq (fun h₁ h₃ => ge h₁ h₃)
theorem b_eD (hs : IsHashSelf m.1.buckets) {a : α} {fallback} :
    m.getEntryDₘ a fallback = getEntryD a fallback (toListModel m.1.buckets) :=
  ab hs AssocList.getEntryD_eq (fun h₁ h₃ => by rw [getEntryD_eq_getEntry?, getEntryD_eq_getEntry?, ge h₁ h₃])
theorem b_e! (hs : IsHashSelf m.1.buckets) {a : α} [Inhabited ((a : α) × β a)] :
    m.getEntry!ₘ a = getEntry! a (toListModel m.1.buckets) :=
  ab hs AssocList.getEntry!_eq (fun h₁ h₃ => by rw [getEntry!_eq_getEntry?, getEntry!_eq_getEntry?, ge h₁ h₃])
theorem b_k (hs : IsHashSelf m.1.buckets) {a : α} : m.getKey?ₘ a = Std.Internal.List.getKey? a (toListModel m.1.buckets) :=
  ab hs AssocList.getKey?_eq (fun h₁ h₃ => by rw [getKey?_eq_getEntry?, getKey?_eq_getEntry?, ge h₁ h₃])
theorem b_g {β : Type v} {m : Raw₀ α (fun _ => β)} (hs : IsHashSelf m.1.buckets) {a : α} :
    Raw₀.Const.get?ₘ m a = getValue? a (toListModel m.1.buckets) :=
  ab hs AssocList.get?_eq (fun h₁ h₃ => by rw [getValue?_eq_getEntry?, getValue?_eq_getEntry?, ge h₁ h₃])
end
/-- Bucket lookups equal list lookups for any BEq once LawfulHashable and IsHashSelf hold. -/
macro "w75p" : tactic => `(tactic| (
  intros
  have hs := Raw.WFImp.buckets_hash_self (by assumption : Raw.WFImp _)
  (try simp only [Raw₀.contains_eq_containsₘ, Raw₀.getEntry?_eq_getEntry?ₘ, Raw₀.getEntryD_eq_getEntryDₘ,
    Raw₀.getEntry!_eq_getEntry!ₘ, Raw₀.getKey?_eq_getKey?ₘ, Raw₀.getKeyD_eq_getKeyDₘ, Raw₀.getKey!_eq_getKey!ₘ,
    Raw₀.Const.get?_eq_get?ₘ, Raw₀.Const.getD_eq_getDₘ, Raw₀.Const.get!_eq_get!ₘ, Raw₀.getKey!ₘ, Raw₀.getKeyDₘ,
    Raw₀.Const.get!ₘ, Raw₀.Const.getDₘ, Std.Internal.List.getKey!_eq_getKey?, Std.Internal.List.getKeyD_eq_getKey?,
    Std.Internal.List.getValue!_eq_getValue?, Std.Internal.List.getValueD_eq_getValue?])
  first | rw [b_c hs] | rw [b_e hs] | rw [b_eD hs] | rw [b_e! hs] | rw [b_k hs] | rw [b_g hs]))
theorem hs1 {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (l : AssocList α β) :
    IsHashSelf (#[l] : Array (AssocList α β)) :=
  ⟨fun i hi => ⟨fun h p _ => by
    have := (mkIdx _ h (hash p.1)).2
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hi this ⊢
    omega⟩⟩
theorem wi1 {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (k : α) (v : β k) :
    Std.DHashMap.Internal.Raw.WFImp (⟨1, #[AssocList.cons k v .nil]⟩ : DHashMap.Raw α β) :=
  ⟨hs1 _, by simp [toListModel], ⟨by simp [toListModel, keys]⟩⟩
theorem wi0 {α : Type u} {β : α → Type v} [BEq α] [Hashable α] :
    Std.DHashMap.Internal.Raw.WFImp (⟨0, #[.nil]⟩ : DHashMap.Raw α β) :=
  ⟨hs1 _, by simp [toListModel], ⟨by simp [toListModel, keys]⟩⟩
abbrev r1 {α : Type} [BEq α] [Hashable α] (k : α) : Raw₀ α (fun _ => Nat) := ⟨⟨1, #[AssocList.cons k 0 .nil]⟩, by simp⟩
abbrev r0 {α : Type} [BEq α] [Hashable α] : Raw₀ α (fun _ => Nat) := ⟨⟨0, #[.nil]⟩, by simp⟩
theorem NS.notPEq : ¬ PartialEquivBEq NS := fun h => NS.notEquiv (@EquivBEq.mk NS _ h inferInstance)
export W5c4 (cg)
export W5c4 (cb)
export W5c4 (ce)
export W5c4 (cg_wf)
export W5c4 (ce_wf)
export W5c4 (cb_nwf)
export W5c4 (cb_eq)
export W5c4 (cg_eq)
export W5c4 (cg_ne)
-- AB (EquivBEq, not LawfulHashable): key 1 sits in its own bucket 1 of 2, query 0 goes to bucket 0
theorem hsA : IsHashSelf (#[.nil, AssocList.cons (AB.mk 1) 7 .nil] : Array (AssocList AB (fun _ => Nat))) := by
  refine ⟨fun i hi => ⟨fun h p hp => ?_⟩⟩
  match i, hi with
  | 0, _ => simp at hp
  | 1, _ =>
    simp at hp; subst hp
    rw [mkIdx_toNat' _ _ _ (by simp [Pow2])]
    show (scrambleHash 1).toNat % 2 = 1
    rw [scr_small _ (by decide)]; rfl
abbrev mA : Raw₀ AB (fun _ => Nat) := ⟨⟨1, #[.nil, AssocList.cons (AB.mk 1) 7 .nil]⟩, by simp⟩
theorem wA : Std.DHashMap.Internal.Raw.WFImp mA.1 := ⟨hsA, by simp [toListModel], ⟨by simp [toListModel]⟩⟩
-- CZ (lawful, hash 0): key 0 misplaced in bucket 1 of 2
abbrev mZ : Raw₀ CZ (fun _ => Nat) := ⟨⟨1, #[.nil, AssocList.cons (CZ.mk 0) 7 .nil]⟩, by simp⟩
theorem cons_hs {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m : Raw₀ α β)
    (hs : IsHashSelf m.1.buckets) (a : α) (b : β a) : IsHashSelf (m.consₘ a b).1.buckets := by
  simp only [Raw₀.consₘ]; rw [updateBucket]
  exact IsHashSelf.uset (fun h' => hashesTo_cons (fun _ => rfl) h') hs
instance w75iA : Inhabited ((_ : AB) × Nat) := ⟨⟨⟨0⟩, 0⟩⟩
instance w75iZ : Inhabited ((_ : CZ) × Nat) := ⟨⟨⟨1⟩, 0⟩⟩
end W7c5
open W7c5
namespace W7c5
abbrev m5 {α : Type} [BEq α] [Hashable α] (k : α) : Raw₀ α (fun _ => Nat) := ⟨⟨5, #[AssocList.cons k 0 .nil, .nil]⟩, by simp⟩
end W7c5
namespace W7c5
abbrev g7 : Raw₀ CZ (fun _ => Nat) := ⟨⟨1, #[AssocList.cons ⟨0⟩ 7 .nil, .nil]⟩, by simp⟩
theorem g7_wf : g7.1.WF := W2c0.cz_wf _ _ rfl (by simp [toListModel])
abbrev g2 : Raw₀ CZ (fun _ => Nat) := ⟨⟨1, #[AssocList.cons ⟨2⟩ 7 .nil, .nil]⟩, by simp⟩
theorem g2_wf : g2.1.WF := W2c0.cz_wf _ _ rfl (by simp [toListModel])
abbrev e7 : Raw₀ CZ (fun _ => Nat) := ⟨⟨0, #[.nil, .nil]⟩, by simp⟩
theorem e7_wf : e7.1.WF := W2c0.cz_wf _ _ rfl (by simp [toListModel])
abbrev s0 : Raw₀ CZ (fun _ => Nat) := ⟨⟨0, #[AssocList.cons ⟨0⟩ 7 .nil, .nil]⟩, by simp⟩
abbrev z0 : Raw₀ CZ (fun _ => Nat) := ⟨⟨0, #[.nil, AssocList.cons ⟨0⟩ 7 .nil]⟩, by simp⟩
abbrev gu : Raw₀ CZ (fun _ => Unit) := ⟨⟨1, #[AssocList.cons ⟨0⟩ () .nil, .nil]⟩, by simp⟩
theorem gu_wf : gu.1.WF := W2c0.cz_wf _ _ rfl (by simp [toListModel])
abbrev eu : Raw₀ CZ (fun _ => Unit) := ⟨⟨0, #[.nil, .nil]⟩, by simp⟩
theorem eu_wf : eu.1.WF := W2c0.cz_wf _ _ rfl (by simp [toListModel])
abbrev zu : Raw₀ CZ (fun _ => Unit) := ⟨⟨1, #[.nil, AssocList.cons ⟨0⟩ () .nil]⟩, by simp⟩
abbrev h1 : Raw₀ W4c4.HZ0 (fun _ => Unit) := (Raw₀.emptyWithCapacity : Raw₀ W4c4.HZ0 (fun _ => Unit)).insert ⟨0⟩ ()
theorem h1_wf : h1.1.WF := Std.DHashMap.Raw.WF.insert₀ Std.DHashMap.Raw.WF.emptyWithCapacity₀
end W7c5
namespace W7c5
section
variable {α : Type u} [BEq α] [Hashable α]
export W6c6 (e_insIfNew)
export W5c2 (r0u_ofl)
export W6c7 (r0_sin)
export W6c7 (uol_size)
-- each insertIfNew raises the size field by at most one (no laws)
theorem uol_le (l : List α) : ∀ (m : Raw₀ α (fun _ => Unit)),
    (Raw₀.Const.insertListIfNewUnitₘ m l).1.size ≤ m.1.size + l.length := by
  induction l with
  | nil => intro m; simp [Raw₀.Const.insertListIfNewUnitₘ]
  | cons hd tl ih =>
    intro m
    simp only [Raw₀.Const.insertListIfNewUnitₘ]
    have := ih (m.insertIfNew hd ())
    rw [r0_sin] at this
    split at this <;> simp <;> omega
end
end W7c5
namespace W7c5
-- Const.get and getCast return the value of the same first match (LawfulBEq, no WF)
theorem al_gg {α : Type u} {β : Type v} [BEq α] [LawfulBEq α] (a : α) :
    ∀ (l : AssocList α (fun _ => β)) (h : l.contains a), l.get a h = l.getCast a h
  | .nil, h => by simp [AssocList.contains] at h
  | .cons k v es, h => by
    simp only [AssocList.get, AssocList.getCast]
    split
    · simp
    · exact al_gg a es _
theorem r0_gg {α : Type u} {β : Type v} [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α (fun _ => β)) (a : α)
    (h : m.contains a) : Raw₀.Const.get m a h = m.get a h := by
  obtain ⟨⟨s, bs⟩, hb⟩ := m
  exact al_gg a _ _
end W7c5

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

/-! # W9c3 helpers -/
namespace W9c3
theorem g?n {α : Type u} {β : α → Type v} {_ : Ord α} [LawfulEqOrd α] (t : Impl α β) (k : α)
    (h : Impl.contains k t = false) : t.get? k = none := by
  induction t with
  | leaf => rfl
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.get?]; split <;> simp_all
theorem cg?n {α : Type u} {β : Type v} {_ : Ord α} (t : Impl α (fun _ => β)) (k : α)
    (h : Impl.contains k t = false) : Impl.Const.get? t k = none := by
  induction t with
  | leaf => rfl
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.Const.get?]; split <;> simp_all
theorem kg?n {α : Type u} {β : α → Type v} {_ : Ord α} (t : Impl α β) (k : α)
    (h : Impl.contains k t = false) : t.getKey? k = none := by
  induction t with
  | leaf => rfl
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.getKey?]; split <;> simp_all
theorem g?s! {α : Type u} {β : α → Type v} {_ : Ord α} [LawfulEqOrd α] (t : Impl α β) (k : α) [Inhabited (β k)]
    (h : Impl.contains k t = true) : t.get? k = some (t.get! k) := by
  induction t with
  | leaf => cases h
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.get?, Impl.get!]; split <;> simp_all
theorem cg?s! {α : Type u} {β : Type v} {_ : Ord α} (t : Impl α (fun _ => β)) (k : α) [Inhabited β]
    (h : Impl.contains k t = true) : Impl.Const.get? t k = some (Impl.Const.get! t k) := by
  induction t with
  | leaf => cases h
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.Const.get?, Impl.Const.get!]; split <;> simp_all
theorem kg?s! {α : Type u} {β : α → Type v} {_ : Ord α} (t : Impl α β) (k : α) [Inhabited α]
    (h : Impl.contains k t = true) : t.getKey? k = some (t.getKey! k) := by
  induction t with
  | leaf => cases h
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.getKey?, Impl.getKey!]; split <;> simp_all
theorem g?sD {α : Type u} {β : α → Type v} {_ : Ord α} [LawfulEqOrd α] (t : Impl α β) (k : α) (fb : β k)
    (h : Impl.contains k t = true) : t.get? k = some (t.getD k fb) := by
  induction t with
  | leaf => cases h
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.get?, Impl.getD]; split <;> simp_all
theorem cg?sD {α : Type u} {β : Type v} {_ : Ord α} (t : Impl α (fun _ => β)) (k : α) (fb : β)
    (h : Impl.contains k t = true) : Impl.Const.get? t k = some (Impl.Const.getD t k fb) := by
  induction t with
  | leaf => cases h
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.Const.get?, Impl.Const.getD]; split <;> simp_all
theorem kg?sD {α : Type u} {β : α → Type v} {_ : Ord α} (t : Impl α β) (k : α) (fb : α)
    (h : Impl.contains k t = true) : t.getKey? k = some (t.getKeyD k fb) := by
  induction t with
  | leaf => cases h
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.getKey?, Impl.getKeyD]; split <;> simp_all
theorem eg? {α : Type u} {β : α → Type v} {_ : Ord α} [LawfulEqOrd α] (t : Impl α β) (k : α)
    (h : t.isEmpty = true) : t.get? k = none := by cases t with | leaf => rfl | inner => cases h
theorem ecg? {α : Type u} {β : Type v} {_ : Ord α} (t : Impl α (fun _ => β)) (k : α)
    (h : t.isEmpty = true) : Impl.Const.get? t k = none := by cases t with | leaf => rfl | inner => cases h
theorem ekg? {α : Type u} {β : α → Type v} {_ : Ord α} (t : Impl α β) (k : α)
    (h : t.isEmpty = true) : t.getKey? k = none := by cases t with | leaf => rfl | inner => cases h
theorem eg! {α : Type u} {β : α → Type v} {_ : Ord α} [LawfulEqOrd α] (t : Impl α β) (k : α) [Inhabited (β k)]
    (h : t.isEmpty = true) : t.get! k = default := by
  cases t with | leaf => simp [Impl.get!, panicWithPosWithDecl, panic, panicCore] | inner => cases h
theorem ecg! {α : Type u} {β : Type v} {_ : Ord α} (t : Impl α (fun _ => β)) (k : α) [Inhabited β]
    (h : t.isEmpty = true) : Impl.Const.get! t k = default := by
  cases t with | leaf => simp [Impl.Const.get!, panicWithPosWithDecl, panic, panicCore] | inner => cases h
theorem ekg! {α : Type u} {β : α → Type v} {_ : Ord α} (t : Impl α β) (k : α) [Inhabited α]
    (h : t.isEmpty = true) : t.getKey! k = default := by
  cases t with | leaf => simp [Impl.getKey!, panicWithPosWithDecl, panic, panicCore] | inner => cases h
macro "w93g" : tactic => `(tactic| (intros; first
  | (exact W9c3.g?n _ _ (by assumption); done) | (exact W9c3.cg?n _ _ (by assumption); done) | (exact W9c3.kg?n _ _ (by assumption); done)
  | (exact W9c3.g?n _ _ (Bool.eq_false_iff.2 (by assumption)); done) | (exact W9c3.cg?n _ _ (Bool.eq_false_iff.2 (by assumption)); done)
  | (exact W9c3.kg?n _ _ (Bool.eq_false_iff.2 (by assumption)); done)
  | (exact W9c3.g?s! _ _ (by assumption); done) | (exact W9c3.cg?s! _ _ (by assumption); done) | (exact W9c3.kg?s! _ _ (by assumption); done)
  | (exact W9c3.g?sD _ _ _ (by assumption); done) | (exact W9c3.cg?sD _ _ _ (by assumption); done) | (exact W9c3.kg?sD _ _ _ (by assumption); done)
  | (exact W9c3.eg? _ _ (by assumption); done) | (exact W9c3.ecg? _ _ (by assumption); done) | (exact W9c3.ekg? _ _ (by assumption); done)
  | (exact W9c3.eg! _ _ (by assumption); done) | (exact W9c3.ecg! _ _ (by assumption); done) | (exact W9c3.ekg! _ _ (by assumption); done)))
theorem alsz {α : Type u} {β : α → Type v} {_ : Ord α} [LawfulEqOrd α] (k : α) (f : Option (β k) → Option (β k))
    (t : Impl α β) (hb : t.Balanced) :
    (Impl.contains k t = false → (f (t.get? k)).isSome = true → (t.alter k f hb).impl.size = t.size + 1) ∧
    (Impl.contains k t = false → (f (t.get? k)).isNone = true → (t.alter k f hb).impl.size = t.size) ∧
    (Impl.contains k t = true → (f (t.get? k)).isSome = true → (t.alter k f hb).impl.size = t.size) := by
  induction t with
  | leaf =>
    simp only [Impl.alter, Impl.contains, Impl.get?]
    split <;> simp_all [Impl.size_leaf, Impl.size_inner]
  | inner sz k' v' l r ihl ihr =>
    have e := hb.eq
    have il := ihl hb.left; have ir := ihr hb.right
    simp only [Impl.alter, Impl.contains, Impl.get?]
    repeat' split
    all_goals (simp_all [Impl.size_balance, Impl.size_glue, Impl.size_inner]; try omega)
theorem calsz {α : Type u} {β : Type v} {_ : Ord α} (k : α) (f : Option β → Option β)
    (t : Impl α (fun _ => β)) (hb : t.Balanced) :
    (Impl.contains k t = false → (f (Impl.Const.get? t k)).isSome = true → (Impl.Const.alter k f t hb).impl.size = t.size + 1) ∧
    (Impl.contains k t = false → (f (Impl.Const.get? t k)).isNone = true → (Impl.Const.alter k f t hb).impl.size = t.size) ∧
    (Impl.contains k t = true → (f (Impl.Const.get? t k)).isSome = true → (Impl.Const.alter k f t hb).impl.size = t.size) := by
  induction t with
  | leaf =>
    simp only [Impl.Const.alter, Impl.contains, Impl.Const.get?]
    split <;> simp_all [Impl.size_leaf, Impl.size_inner]
  | inner sz k' v' l r ihl ihr =>
    have e := hb.eq
    have il := ihl hb.left; have ir := ihr hb.right
    simp only [Impl.Const.alter, Impl.contains, Impl.Const.get?]
    repeat' split
    all_goals (simp_all [Impl.size_balance, Impl.size_glue, Impl.size_inner]; try omega)
theorem alsz! {α : Type u} {β : α → Type v} {_ : Ord α} [LawfulEqOrd α] (k : α) (f : Option (β k) → Option (β k))
    (t : Impl α β) (hb : t.Balanced) :
    (Impl.contains k t = false → (f (t.get? k)).isSome = true → (t.alter! k f).size = t.size + 1) ∧
    (Impl.contains k t = false → (f (t.get? k)).isNone = true → (t.alter! k f).size = t.size) ∧
    (Impl.contains k t = true → (f (t.get? k)).isSome = true → (t.alter! k f).size = t.size) := by
  rw [← Impl.alter_eq_alter! hb]; exact alsz k f t hb
theorem calsz! {α : Type u} {β : Type v} {_ : Ord α} (k : α) (f : Option β → Option β)
    (t : Impl α (fun _ => β)) (hb : t.Balanced) :
    (Impl.contains k t = false → (f (Impl.Const.get? t k)).isSome = true → (Impl.Const.alter! k f t).size = t.size + 1) ∧
    (Impl.contains k t = false → (f (Impl.Const.get? t k)).isNone = true → (Impl.Const.alter! k f t).size = t.size) ∧
    (Impl.contains k t = true → (f (Impl.Const.get? t k)).isSome = true → (Impl.Const.alter! k f t).size = t.size) := by
  rw [← Impl.Const.alter_eq_alter! hb]; exact calsz k f t hb
theorem dr_bal {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : DTreeMap.Raw α β cmp} (h : t.WF) :
    t.inner.Balanced := @Impl.WF.balanced _ _ ⟨cmp⟩ _ h.out
theorem tmr_bal {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeMap.Raw α β cmp} (h : t.WF) :
    t.inner.inner.Balanced := @Impl.WF.balanced _ _ ⟨cmp⟩ _ h.out.out
macro "w93a" : tactic => `(tactic| (intros; first
  | (exact (W9c3.alsz _ _ _ _).1 (Bool.eq_false_iff.2 ‹_›) ‹_›; done) | (exact (W9c3.alsz _ _ _ _).2.1 (Bool.eq_false_iff.2 ‹_›) ‹_›; done)
  | (exact (W9c3.alsz _ _ _ _).2.2 ‹_› ‹_›; done)
  | (exact (W9c3.calsz _ _ _ _).1 (Bool.eq_false_iff.2 ‹_›) ‹_›; done) | (exact (W9c3.calsz _ _ _ _).2.1 (Bool.eq_false_iff.2 ‹_›) ‹_›; done)
  | (exact (W9c3.calsz _ _ _ _).2.2 ‹_› ‹_›; done)
  | (exact (W9c3.alsz! _ _ _ (W9c3.dr_bal ‹_›)).1 (Bool.eq_false_iff.2 ‹_›) ‹_›; done) | (exact (W9c3.alsz! _ _ _ (W9c3.dr_bal ‹_›)).2.1 (Bool.eq_false_iff.2 ‹_›) ‹_›; done)
  | (exact (W9c3.alsz! _ _ _ (W9c3.dr_bal ‹_›)).2.2 ‹_› ‹_›; done)
  | (exact (W9c3.calsz! _ _ _ (W9c3.dr_bal ‹_›)).1 (Bool.eq_false_iff.2 ‹_›) ‹_›; done) | (exact (W9c3.calsz! _ _ _ (W9c3.dr_bal ‹_›)).2.1 (Bool.eq_false_iff.2 ‹_›) ‹_›; done)
  | (exact (W9c3.calsz! _ _ _ (W9c3.dr_bal ‹_›)).2.2 ‹_› ‹_›; done)
  | (exact (W9c3.calsz! _ _ _ (W9c3.tmr_bal ‹_›)).1 (Bool.eq_false_iff.2 ‹_›) ‹_›; done) | (exact (W9c3.calsz! _ _ _ (W9c3.tmr_bal ‹_›)).2.1 (Bool.eq_false_iff.2 ‹_›) ‹_›; done)
  | (exact (W9c3.calsz! _ _ _ (W9c3.tmr_bal ‹_›)).2.2 ‹_› ‹_›; done)))
theorem gD {α : Type u} {β : α → Type v} {_ : Ord α} [LawfulEqOrd α] (t : Impl α β) (k : α) (fb : β k)
    (h : Impl.contains k t = false) : t.getD k fb = fb := by
  induction t with
  | leaf => rfl
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.getD]; split <;> simp_all
theorem cgD {α : Type u} {β : Type v} {_ : Ord α} (t : Impl α (fun _ => β)) (k : α) (fb : β)
    (h : Impl.contains k t = false) : Impl.Const.getD t k fb = fb := by
  induction t with
  | leaf => rfl
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.Const.getD]; split <;> simp_all
theorem nc {α : Type u} {β : α → Type v} {_ : Ord α} (k : α) (t : Impl α β)
    (h : ∀ x ∈ t.toListModel, compare k x.1 ≠ .eq) : Impl.contains k t = false := by
  induction t with
  | leaf => rfl
  | inner _ k' v' l r ihl ihr =>
    simp only [Impl.toListModel_inner, List.mem_append, List.mem_cons] at h
    have hl := ihl (fun x hx => h x (Or.inl hx))
    have hr := ihr (fun x hx => h x (Or.inr (Or.inr hx)))
    have hk := h ⟨k', v'⟩ (Or.inr (Or.inl rfl))
    simp only [Impl.contains]; split <;> simp_all
theorem fnc {α : Type u} {β : α → Type v} {_ : Ord α} (k : α) : ∀ (l : List ((k : α) × β k)) (t : Impl α β),
    t.Balanced → (∀ x ∈ t.toListModel, compare k x.1 ≠ .eq) → (∀ x ∈ l, compare k x.1 ≠ .eq) →
    ∀ x ∈ (l.foldl (init := t) fun acc ⟨k, v⟩ => acc.insert! k v).toListModel, compare k x.1 ≠ .eq
  | [], t, _, ht, _ => ht
  | ⟨a, b⟩ :: l, t, hb, ht, hl => by
    simp only [List.foldl_cons]
    rw [← Impl.insert_eq_insert! (h := hb)]
    refine fnc k l _ (Impl.insert a b t hb).balanced_impl ?_ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    intro x hx
    rcases W2c2R.ins_sub a b t hb x hx with e | e
    · exact e ▸ hl _ (List.mem_cons_self ..)
    · exact ht x e
theorem cfnc {α : Type u} {β : Type v} {_ : Ord α} (k : α) : ∀ (l : List (α × β)) (t : Impl α (fun _ => β)),
    t.Balanced → (∀ x ∈ t.toListModel, compare k x.1 ≠ .eq) → (∀ x ∈ l, compare k x.1 ≠ .eq) →
    ∀ x ∈ (l.foldl (init := t) fun acc ⟨k, v⟩ => acc.insert! k v).toListModel, compare k x.1 ≠ .eq
  | [], t, _, ht, _ => ht
  | ⟨a, b⟩ :: l, t, hb, ht, hl => by
    simp only [List.foldl_cons]
    rw [← Impl.insert_eq_insert! (h := hb)]
    refine cfnc k l _ (Impl.insert a b t hb).balanced_impl ?_ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    intro x hx
    rcases W2c2R.ins_sub a b t hb x hx with e | e
    · exact e ▸ hl _ (List.mem_cons_self ..)
    · exact ht x e
theorem bnc {α : Type u} {γ : Type v} [BEq α] {cmp : α → α → Ordering} [LawfulBEqCmp cmp] (k : α) (g : γ → α) (l : List γ)
    (h : (l.map g).contains k = false) : ∀ x ∈ l, cmp k (g x) ≠ .eq := by
  intro x hx e
  have : (l.map g).contains k = true :=
    List.contains_iff_exists_mem_beq.2 ⟨g x, List.mem_map_of_mem hx, LawfulBEqCmp.compare_eq_iff_beq.1 e⟩
  simp_all
theorem ofl {α : Type u} {β : α → Type v} {_ : Ord α} (k : α) (l : List ((k : α) × β k))
    (h : ∀ x ∈ l, compare k x.1 ≠ .eq) : Impl.contains k (Impl.ofList l) = false := by
  apply nc
  simp only [Impl.ofList]; rw [Impl.insertMany_eq_foldl]
  exact fnc k l _ Impl.balanced_empty (by simp [Impl.empty]) h
theorem cofl {α : Type u} {β : Type v} {_ : Ord α} (k : α) (l : List (α × β))
    (h : ∀ x ∈ l, compare k x.1 ≠ .eq) : Impl.contains k (Impl.Const.ofList l) = false := by
  apply nc
  simp only [Impl.Const.ofList]; rw [Impl.Const.insertMany_eq_foldl]
  exact cfnc k l _ Impl.balanced_empty (by simp [Impl.empty]) h
theorem bnc' {α : Type u} {γ : Type v} [BEq α] {_ : Ord α} [LawfulBEqCmp (compare : α → α → Ordering)] (k : α) (g : γ → α) (l : List γ)
    (h : (l.map g).contains k = false) : ∀ x ∈ l, compare k (g x) ≠ .eq := bnc k g l h
theorem kD {α : Type u} {β : α → Type v} {_ : Ord α} (t : Impl α β) (k : α) (fb : α)
    (h : Impl.contains k t = false) : t.getKeyD k fb = fb := by
  induction t with
  | leaf => rfl
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.getKeyD]; split <;> simp_all
theorem ufnc {α : Type u} {_ : Ord α} (k : α) : ∀ (l : List α) (t : Impl α (fun _ => Unit)),
    t.Balanced → (∀ x ∈ t.toListModel, compare k x.1 ≠ .eq) → (∀ x ∈ l, compare k x ≠ .eq) →
    ∀ x ∈ (l.foldl (init := t) fun acc k => acc.insertIfNew! k ()).toListModel, compare k x.1 ≠ .eq
  | [], t, _, ht, _ => ht
  | a :: l, t, hb, ht, hl => by
    simp only [List.foldl_cons, Impl.insertIfNew!]
    split
    · exact ufnc k l t hb ht (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    · rw [← Impl.insert_eq_insert! (h := hb)]
      refine ufnc k l _ (Impl.insert a () t hb).balanced_impl ?_ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      intro x hx
      rcases W2c2R.ins_sub a () t hb x hx with e | e
      · exact e ▸ hl _ (List.mem_cons_self ..)
      · exact ht x e
theorem uofl {α : Type u} {_ : Ord α} (k : α) (l : List α)
    (h : ∀ x ∈ l, compare k x ≠ .eq) : Impl.contains k (Impl.Const.unitOfList l) = false := by
  apply nc
  simp only [Impl.Const.unitOfList]; rw [Impl.Const.insertManyIfNewUnit_eq_foldl]
  exact ufnc k l _ Impl.balanced_empty (by simp [Impl.empty]) h
theorem lnc {α : Type u} [BEq α] {_ : Ord α} [LawfulBEqCmp (compare : α → α → Ordering)] (k : α) (l : List α)
    (h : l.contains k = false) : ∀ x ∈ l, compare k x ≠ .eq := by
  have := bnc' k id l (by simpa using h); simpa using this
macro "w93o" : tactic => `(tactic| (intros; first
  | (exact W9c3.gD _ _ _ (W9c3.ofl _ _ (W9c3.bnc' _ _ _ ‹_›)); done)
  | (exact W9c3.cgD _ _ _ (W9c3.cofl _ _ (W9c3.bnc' _ _ _ ‹_›)); done)
  | (exact W9c3.kD _ _ _ (W9c3.uofl _ _ (W9c3.lnc _ _ ‹_›)); done)))
theorem g!n {α : Type u} {β : α → Type v} {_ : Ord α} [LawfulEqOrd α] (t : Impl α β) (k : α) [Inhabited (β k)]
    (h : Impl.contains k t = false) : t.get! k = default := by
  induction t with
  | leaf => simp [Impl.get!, panicWithPosWithDecl, panic, panicCore]
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.get!]; split <;> simp_all
theorem cg!n {α : Type u} {β : Type v} {_ : Ord α} (t : Impl α (fun _ => β)) (k : α) [Inhabited β]
    (h : Impl.contains k t = false) : Impl.Const.get! t k = default := by
  induction t with
  | leaf => simp [Impl.Const.get!, panicWithPosWithDecl, panic, panicCore]
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.Const.get!]; split <;> simp_all
theorem kg!n {α : Type u} {β : α → Type v} {_ : Ord α} (t : Impl α β) (k : α) [Inhabited α]
    (h : Impl.contains k t = false) : t.getKey! k = default := by
  induction t with
  | leaf => simp [Impl.getKey!, panicWithPosWithDecl, panic, panicCore]
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains] at h; simp only [Impl.getKey!]; split <;> simp_all
theorem dnl {α : Type u} {β : α → Type v} {_ : Ord α} [TransOrd α] {t₁ : Impl α β} (h₁ : t₁.WF) (t₂ : Impl α β) (k : α)
    (h : Impl.contains k t₁ = false) : Impl.contains k (t₁.diff! t₂) = false := by
  letI : BEq α := beqOfOrd
  rw [← Impl.diff_eq_diff! h₁]
  apply nc
  have hc := (Impl.contains_eq_containsKey h₁.ordered).symm.trans h
  rw [Std.Internal.List.containsKey_eq_false_iff] at hc
  intro x hx e
  have hx1 : x ∈ t₁.toListModel := by
    simp only [Impl.diff] at hx; split at hx
    · rw [Impl.toListModel_filter] at hx; exact (List.mem_filter.1 hx).1
    · exact (List.mem_filter.1 ((Impl.toListModel_eraseManyEntries_impl h₁).mem_iff.1 hx)).1
  have h3 := hc x hx1
  have h2 : (k == x.fst) = true := by show (compare k x.1).isEq = true; rw [e]; rfl
  rw [h2] at h3; cases h3
theorem ccong {α : Type u} {β : α → Type v} {_ : Ord α} [TransOrd α] (t : Impl α β) (a b : α)
    (e : compare a b = .eq) : Impl.contains a t = Impl.contains b t := by
  induction t with
  | leaf => rfl
  | inner _ k' _ l r ihl ihr =>
    simp only [Impl.contains, TransCmp.congr_left (cmp := compare) (c := k') e, ihl, ihr]
theorem cex {α : Type u} {β : α → Type v} {_ : Ord α} (t : Impl α β) (k : α)
    (h : Impl.contains k t = true) : ∃ e ∈ t.toListModel, compare k e.1 = .eq := by
  induction t with
  | leaf => cases h
  | inner _ k' v' l r ihl ihr =>
    simp only [Impl.contains] at h
    split at h
    · obtain ⟨e, he, h2⟩ := ihl h; exact ⟨e, by simp [Impl.toListModel_inner, he], h2⟩
    · obtain ⟨e, he, h2⟩ := ihr h; exact ⟨e, by simp [Impl.toListModel_inner, he], h2⟩
    · exact ⟨⟨k', v'⟩, by simp [Impl.toListModel_inner], by assumption⟩
theorem dmr {α : Type u} {β : α → Type v} {_ : Ord α} [TransOrd α] {t₁ : Impl α β} (h₁ : t₁.WF) (t₂ : Impl α β) (k : α)
    (h : Impl.contains k t₂ = true) : Impl.contains k (t₁.diff! t₂) = false := by
  letI : BEq α := beqOfOrd
  rw [← Impl.diff_eq_diff! h₁]
  apply nc
  intro x hx e
  simp only [Impl.diff] at hx; split at hx
  · rw [Impl.toListModel_filter] at hx
    have h3 := (List.mem_filter.1 hx).2
    rw [← ccong t₂ k x.1 e, h] at h3; cases h3
  · have h3 := (List.mem_filter.1 ((Impl.toListModel_eraseManyEntries_impl h₁).mem_iff.1 hx)).2
    obtain ⟨y, hy, hky⟩ := cex t₂ k h
    have hxy : compare x.1 y.1 = .eq := TransCmp.eq_trans (OrientedCmp.eq_symm e) hky
    have h4 : (t₂.toListModel.map Sigma.fst).contains x.1 = true :=
      List.contains_iff_exists_mem_beq.2 ⟨y.1, List.mem_map_of_mem hy, by show (compare x.1 y.1).isEq = true; rw [hxy]; rfl⟩
    rw [h4] at h3; cases h3
theorem gem {α : Type u} {β : α → Type v} {_ : Ord α} (t : Impl α β) (k : α) (e : (a : α) × β a)
    (h : t.getEntry? k = some e) : e ∈ t.toListModel := by
  induction t with
  | leaf => cases h
  | inner _ k' v' l r ihl ihr =>
    simp only [Impl.getEntry?] at h
    split at h
    · simp [Impl.toListModel_inner, ihl h]
    · simp [Impl.toListModel_inner, ihr h]
    · cases h; simp [Impl.toListModel_inner]
theorem isub {α : Type u} {β : α → Type v} {_ : Ord α} (m₁ : Impl α β) : ∀ (L : List ((a : α) × β a))
    (s : { t : Impl α β // t.Balanced }), (∀ x ∈ s.1.toListModel, x ∈ m₁.toListModel) →
    ∀ x ∈ (L.foldl (fun acc p => Impl.interSmallerFn m₁ acc p.1) s).1.toListModel, x ∈ m₁.toListModel
  | [], s, hs => hs
  | p :: L, s, hs => by
    simp only [List.foldl_cons]
    apply isub m₁ L
    simp only [Impl.interSmallerFn]
    split
    · next kv h =>
      intro x hx
      rcases W2c2R.ins_sub kv.1 kv.2 s.1 s.2 x hx with e | e
      · exact e ▸ gem m₁ p.1 kv h
      · exact hs x e
    · exact hs
theorem inl {α : Type u} {β : α → Type v} {_ : Ord α} [TransOrd α] {t₁ : Impl α β} (h₁ : t₁.WF) (t₂ : Impl α β) (k : α)
    (h : Impl.contains k t₁ = false) : Impl.contains k (t₁.inter! t₂) = false := by
  letI : BEq α := beqOfOrd
  rw [← Impl.inter_eq_inter! (h := h₁.balanced)]
  apply nc
  have hc := (Impl.contains_eq_containsKey h₁.ordered).symm.trans h
  rw [Std.Internal.List.containsKey_eq_false_iff] at hc
  intro x hx e
  have hx1 : x ∈ t₁.toListModel := by
    simp only [Impl.inter] at hx; split at hx
    · rw [Impl.toListModel_filter] at hx; exact (List.mem_filter.1 hx).1
    · simp only [Impl.interSmaller, Impl.foldl_eq_foldl] at hx
      exact isub t₁ _ _ (by simp [Impl.empty]) x hx
  have h3 := hc x hx1
  have h2 : (k == x.fst) = true := by show (compare k x.1).isEq = true; rw [e]; rfl
  rw [h2] at h3; cases h3
end W9c3



/-! # W9c3 verdicts -/

-- `Std.DTreeMap.Raw.Const.get!_diff_of_mem_right` (binder 10): compare, t1 = {1 ↦ 11}, t2 = ∅, k = 1
theorem w9c3_0 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_diff_of_mem_right 10 :=
  fun h => by
  have := h (m₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (m₂ := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_diff_of_mem_right` (binder 11): compare, t1 = {1 ↦ 11}, t2 = ∅, k = 1
theorem w9c3_1 : ¬ drop0% Std.DTreeMap.Raw.get!_diff_of_mem_right 11 :=
  fun h => by
  have := h (t₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (t₂ := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.get!_diff_of_mem_right` (binder 9): compare, t1 = {1 ↦ 11}, t2 = ∅, k = 1
theorem w9c3_2 : ¬ drop0% Std.DTreeMap.get!_diff_of_mem_right 9 :=
  fun h => by
  have := h (t₁ := (DTreeMap.ofList [⟨1, 11⟩] compare : DTreeMap Nat (fun _ => Nat) compare)) (t₂ := (DTreeMap.ofList [] compare : DTreeMap Nat (fun _ => Nat) compare)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.ExtDTreeMap.get!_diff_of_mem_right` (binder 9): compare, t1 = {1 ↦ 11}, t2 = ∅, k = 1
theorem w9c3_3 : ¬ drop0% Std.ExtDTreeMap.get!_diff_of_mem_right 9 :=
  fun h => by
  have := h (t₁ := (⟨Quotient.mk _ (DTreeMap.ofList [⟨1, 11⟩] compare)⟩ : ExtDTreeMap Nat (fun _ => Nat) compare)) (t₂ := (⟨Quotient.mk _ (DTreeMap.ofList [] compare)⟩ : ExtDTreeMap Nat (fun _ => Nat) compare)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_diff_of_mem_right` (binder 9): compare, t1 = {1 ↦ 11}, t2 = ∅, k = 1
theorem w9c3_4 : ¬ drop0% Std.TreeSet.Raw.get!_diff_of_mem_right 9 :=
  fun h => by
  have := h (t₁ := (TreeSet.Raw.ofList [1] compare : TreeSet.Raw Nat compare)) (t₂ := (TreeSet.Raw.ofList [] compare : TreeSet.Raw Nat compare)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_diff_of_mem_right` (binder 7): compare, t1 holds key 1 twice (root and right child, size field 2), t2 = {1}: diff erases only the root copy, get! 1 finds the other
theorem w9c3_5 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_diff_of_mem_right 7 :=
  fun h => by
  have := h (m₁ := (⟨.inner 2 1 11 .leaf (.inner 1 1 12 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (m₂ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_diff_of_mem_right` (binder 8): diff of WF t1 only drops entries of t1: in the filter branch an entry equal to k is dropped because t2.contains respects compare-equality (same search path under TransCmp), in the erase branch because t2 has an entry equal to k; so k is absent from the result and get! is default, without t2.WF
theorem w9c3_6 : drop% Std.DTreeMap.Raw.Const.get!_diff_of_mem_right 8 :=
  by
  intro _ _ _ _ _ _ _ h₁ k h
  exact W9c3.cg!n _ _ (W9c3.dmr h₁.out _ _ h)

-- `Std.DTreeMap.Raw.get!_diff_of_mem_right` (binder 7): compare, t1 holds key 1 twice (root and right child, size field 2), t2 = {1}: diff erases only the root copy, get! 1 finds the other
theorem w9c3_7 : ¬ drop0% Std.DTreeMap.Raw.get!_diff_of_mem_right 7 :=
  fun h => by
  have := h (t₁ := (⟨.inner 2 1 11 .leaf (.inner 1 1 12 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (t₂ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_diff_of_mem_right` (binder 8): diff of WF t1 only drops entries of t1: in the filter branch an entry equal to k is dropped because t2.contains respects compare-equality (same search path under TransCmp), in the erase branch because t2 has an entry equal to k; so k is absent from the result and get! is default, without t2.WF
theorem w9c3_8 : drop% Std.DTreeMap.Raw.get!_diff_of_mem_right 8 :=
  by
  intro _ _ _ _ _ _ _ h₁ k _ h
  exact W9c3.g!n _ _ (W9c3.dmr h₁.out _ _ h)

-- `Std.TreeSet.Raw.get!_diff_of_mem_right` (binder 6): compare, t1 holds key 1 twice (root and right child, size field 2), t2 = {1}: diff erases only the root copy, get! 1 finds the other
theorem w9c3_9 : ¬ drop0% Std.TreeSet.Raw.get!_diff_of_mem_right 6 :=
  fun h => by
  have := h (t₁ := (⟨⟨⟨.inner 2 1 () .leaf (.inner 1 1 () .leaf .leaf)⟩⟩⟩ : TreeSet.Raw Nat compare)) (t₂ := (TreeSet.Raw.ofList [1] compare : TreeSet.Raw Nat compare)) (h₂ := (by wfx)) (k := 1) (mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_diff_of_mem_right` (binder 7): diff of WF t1 only drops entries of t1: in the filter branch an entry equal to k is dropped because t2.contains respects compare-equality (same search path under TransCmp), in the erase branch because t2 has an entry equal to k; so k is absent from the result and get! is default, without t2.WF
theorem w9c3_10 : drop% Std.TreeSet.Raw.get!_diff_of_mem_right 7 :=
  by
  intro _ _ _ _ _ _ h₁ k mem
  exact W9c3.kg!n _ _ (W9c3.dmr h₁.out.out.out _ _ mem)

-- `Std.DTreeMap.Const.get!_diff_of_mem_right` (binder 5): cmpT, t1 = ofList [2, 4, 3, 2], t2 = ofList [4, 3, 2] (values key+10), k = 2: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_11 : ¬ drop0% Std.DTreeMap.Const.get!_diff_of_mem_right 5 :=
  fun h => by
  have := h (t₁ := (DTreeMap.ofList [⟨2, 12⟩, ⟨4, 14⟩, ⟨3, 13⟩, ⟨2, 12⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (t₂ := (DTreeMap.ofList [⟨4, 14⟩, ⟨3, 13⟩, ⟨2, 12⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (k := 2) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_diff_of_mem_right` (binder 5): cmpT, t1 = ofList [2, 4, 3, 2], t2 = ofList [4, 3, 2] (values key+10), k = 2: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_12 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_diff_of_mem_right 5 :=
  fun h => by
  have := h (m₁ := (DTreeMap.Raw.ofList [⟨2, 12⟩, ⟨4, 14⟩, ⟨3, 13⟩, ⟨2, 12⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (m₂ := (DTreeMap.Raw.ofList [⟨4, 14⟩, ⟨3, 13⟩, ⟨2, 12⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 2) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_diff_of_mem_right` (binder 5): cmpT, t1 = ofList [2, 4, 3, 2], t2 = ofList [4, 3, 2] (values key+10), k = 2: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_13 : ¬ drop0% Std.DTreeMap.Raw.get!_diff_of_mem_right 5 :=
  fun h => by
  have := h (t₁ := (DTreeMap.Raw.ofList [⟨2, 12⟩, ⟨4, 14⟩, ⟨3, 13⟩, ⟨2, 12⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (t₂ := (DTreeMap.Raw.ofList [⟨4, 14⟩, ⟨3, 13⟩, ⟨2, 12⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 2) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.get!_diff_of_mem_right` (binder 5): cmpT, t1 = ofList [2, 4, 3, 2], t2 = ofList [4, 3, 2] (values key+10), k = 2: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_14 : ¬ drop0% Std.DTreeMap.get!_diff_of_mem_right 5 :=
  fun h => by
  have := h (t₁ := (DTreeMap.ofList [⟨2, 12⟩, ⟨4, 14⟩, ⟨3, 13⟩, ⟨2, 12⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (t₂ := (DTreeMap.ofList [⟨4, 14⟩, ⟨3, 13⟩, ⟨2, 12⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (k := 2) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_diff_of_mem_right` (binder 5): cmpT, t1 = ofList [2, 4, 3, 2], t2 = ofList [4, 3, 2] (values key+10), k = 2: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_15 : ¬ drop0% Std.TreeSet.Raw.get!_diff_of_mem_right 5 :=
  fun h => by
  have := h (t₁ := (TreeSet.Raw.ofList [2, 4, 3, 2] cmpT : TreeSet.Raw Nat cmpT)) (t₂ := (TreeSet.Raw.ofList [4, 3, 2] cmpT : TreeSet.Raw Nat cmpT)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 2) (mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.get!_diff_of_mem_right` (binder 4): cmpT, t1 = ofList [2, 4, 3, 2], t2 = ofList [4, 3, 2] (values key+10), k = 2: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_16 : ¬ drop0% Std.TreeSet.get!_diff_of_mem_right 4 :=
  fun h => by
  have := h (t₁ := (TreeSet.ofList [2, 4, 3, 2] cmpT : TreeSet Nat cmpT)) (t₂ := (TreeSet.ofList [4, 3, 2] cmpT : TreeSet Nat cmpT)) (k := 2) (mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_left` (binder 7): compare, t1 unordered (root 2, unreachable right child 1), t2 = {2}: erasing the root makes 1 reachable
theorem w9c3_17 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_left 7 :=
  fun h => by
  have := h (m₁ := (⟨.inner 2 2 12 .leaf (.inner 1 1 11 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (m₂ := (DTreeMap.Raw.ofList [⟨2, 12⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_left` (binder 8): diff of WF t1 (filter or eraseManyEntries) keeps only entries of t1, none equal to k, so contains k is false on the result and get! is default, without t2.WF
theorem w9c3_18 : drop% Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_left 8 :=
  by
  intro _ _ _ _ _ _ _ h₁ k h
  exact W9c3.cg!n _ _ (W9c3.dnl h₁.out _ _ (Bool.eq_false_iff.2 h))

-- `Std.DTreeMap.Raw.get!_diff_of_not_mem_left` (binder 7): compare, t1 unordered (root 2, unreachable right child 1), t2 = {2}: erasing the root makes 1 reachable
theorem w9c3_19 : ¬ drop0% Std.DTreeMap.Raw.get!_diff_of_not_mem_left 7 :=
  fun h => by
  have := h (t₁ := (⟨.inner 2 2 12 .leaf (.inner 1 1 11 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (t₂ := (DTreeMap.Raw.ofList [⟨2, 12⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_diff_of_not_mem_left` (binder 8): diff of WF t1 (filter or eraseManyEntries) keeps only entries of t1, none equal to k, so contains k is false on the result and get! is default, without t2.WF
theorem w9c3_20 : drop% Std.DTreeMap.Raw.get!_diff_of_not_mem_left 8 :=
  by
  intro _ _ _ _ _ _ _ h₁ k _ h
  exact W9c3.g!n _ _ (W9c3.dnl h₁.out _ _ (Bool.eq_false_iff.2 h))

-- `Std.TreeSet.Raw.get!_diff_of_not_mem_left` (binder 6): compare, t1 unordered (root 2, unreachable right child 1), t2 = {2}: erasing the root makes 1 reachable
theorem w9c3_21 : ¬ drop0% Std.TreeSet.Raw.get!_diff_of_not_mem_left 6 :=
  fun h => by
  have := h (t₁ := (⟨⟨⟨.inner 2 2 () .leaf (.inner 1 1 () .leaf .leaf)⟩⟩⟩ : TreeSet.Raw Nat compare)) (t₂ := (TreeSet.Raw.ofList [2] compare : TreeSet.Raw Nat compare)) (h₂ := (by wfx)) (k := 1) (not_mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_diff_of_not_mem_left` (binder 7): diff of WF t1 (filter or eraseManyEntries) keeps only entries of t1, none equal to k, so contains k is false on the result and get! is default, without t2.WF
theorem w9c3_22 : drop% Std.TreeSet.Raw.get!_diff_of_not_mem_left 7 :=
  by
  intro _ _ _ _ _ _ h₁ k not_mem
  exact W9c3.kg!n _ _ (W9c3.dnl h₁.out.out.out _ _ (Bool.eq_false_iff.2 not_mem))

-- `Std.DTreeMap.Const.get!_diff_of_not_mem_left` (binder 5): cmpT, t1 = ofList [1, 2, 3], t2 = ofList [2, 3] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_23 : ¬ drop0% Std.DTreeMap.Const.get!_diff_of_not_mem_left 5 :=
  fun h => by
  have := h (t₁ := (DTreeMap.ofList [⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (t₂ := (DTreeMap.ofList [⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_left` (binder 5): cmpT, t1 = ofList [1, 2, 3], t2 = ofList [2, 3] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_24 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_left 5 :=
  fun h => by
  have := h (m₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (m₂ := (DTreeMap.Raw.ofList [⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_diff_of_not_mem_left` (binder 5): cmpT, t1 = ofList [1, 2, 3], t2 = ofList [2, 3] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_25 : ¬ drop0% Std.DTreeMap.Raw.get!_diff_of_not_mem_left 5 :=
  fun h => by
  have := h (t₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (t₂ := (DTreeMap.Raw.ofList [⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.get!_diff_of_not_mem_left` (binder 5): cmpT, t1 = ofList [1, 2, 3], t2 = ofList [2, 3] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_26 : ¬ drop0% Std.DTreeMap.get!_diff_of_not_mem_left 5 :=
  fun h => by
  have := h (t₁ := (DTreeMap.ofList [⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (t₂ := (DTreeMap.ofList [⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_diff_of_not_mem_left` (binder 5): cmpT, t1 = ofList [1, 2, 3], t2 = ofList [2, 3] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_27 : ¬ drop0% Std.TreeSet.Raw.get!_diff_of_not_mem_left 5 :=
  fun h => by
  have := h (t₁ := (TreeSet.Raw.ofList [1, 2, 3] cmpT : TreeSet.Raw Nat cmpT)) (t₂ := (TreeSet.Raw.ofList [2, 3] cmpT : TreeSet.Raw Nat cmpT)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1) (not_mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.get!_diff_of_not_mem_left` (binder 4): cmpT, t1 = ofList [1, 2, 3], t2 = ofList [2, 3] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_28 : ¬ drop0% Std.TreeSet.get!_diff_of_not_mem_left 4 :=
  fun h => by
  have := h (t₁ := (TreeSet.ofList [1, 2, 3] cmpT : TreeSet Nat cmpT)) (t₂ := (TreeSet.ofList [2, 3] cmpT : TreeSet Nat cmpT)) (k := 1) (not_mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_left` (binder 10): compare, t1 = {1 ↦ 11}, t2 = ∅, k = 1
theorem w9c3_29 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_left 10 :=
  fun h => by
  have := h (m₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (m₂ := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_diff_of_not_mem_left` (binder 11): compare, t1 = {1 ↦ 11}, t2 = ∅, k = 1
theorem w9c3_30 : ¬ drop0% Std.DTreeMap.Raw.get!_diff_of_not_mem_left 11 :=
  fun h => by
  have := h (t₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (t₂ := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.get!_diff_of_not_mem_left` (binder 9): compare, t1 = {1 ↦ 11}, t2 = ∅, k = 1
theorem w9c3_31 : ¬ drop0% Std.DTreeMap.get!_diff_of_not_mem_left 9 :=
  fun h => by
  have := h (t₁ := (DTreeMap.ofList [⟨1, 11⟩] compare : DTreeMap Nat (fun _ => Nat) compare)) (t₂ := (DTreeMap.ofList [] compare : DTreeMap Nat (fun _ => Nat) compare)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.ExtDTreeMap.get!_diff_of_not_mem_left` (binder 9): compare, t1 = {1 ↦ 11}, t2 = ∅, k = 1
theorem w9c3_32 : ¬ drop0% Std.ExtDTreeMap.get!_diff_of_not_mem_left 9 :=
  fun h => by
  have := h (t₁ := (⟨Quotient.mk _ (DTreeMap.ofList [⟨1, 11⟩] compare)⟩ : ExtDTreeMap Nat (fun _ => Nat) compare)) (t₂ := (⟨Quotient.mk _ (DTreeMap.ofList [] compare)⟩ : ExtDTreeMap Nat (fun _ => Nat) compare)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_diff_of_not_mem_left` (binder 9): compare, t1 = {1 ↦ 11}, t2 = ∅, k = 1
theorem w9c3_33 : ¬ drop0% Std.TreeSet.Raw.get!_diff_of_not_mem_left 9 :=
  fun h => by
  have := h (t₁ := (TreeSet.Raw.ofList [1] compare : TreeSet.Raw Nat compare)) (t₂ := (TreeSet.Raw.ofList [] compare : TreeSet.Raw Nat compare)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_right` (binder 7): compare, t1 unordered (root 2, unreachable right child 1), t2 = {2}: t1.get! 1 is default, but erasing the root makes 1 reachable
theorem w9c3_34 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_right 7 :=
  fun h => by
  have := h (m₁ := (⟨.inner 2 2 12 .leaf (.inner 1 1 11 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (m₂ := (DTreeMap.Raw.ofList [⟨2, 12⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_right` (binder 8): compare, t2 unordered (root 2, unreachable right child 1, size field 0), t1 = {1}: diff erases every key of t2, so 1 goes although 1 is not in t2
theorem w9c3_35 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_right 8 :=
  fun h => by
  have := h (m₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (m₂ := (⟨.inner 0 2 12 .leaf (.inner 1 1 11 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₁ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_diff_of_not_mem_right` (binder 7): compare, t1 unordered (root 2, unreachable right child 1), t2 = {2}: t1.get! 1 is default, but erasing the root makes 1 reachable
theorem w9c3_36 : ¬ drop0% Std.DTreeMap.Raw.get!_diff_of_not_mem_right 7 :=
  fun h => by
  have := h (t₁ := (⟨.inner 2 2 12 .leaf (.inner 1 1 11 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (t₂ := (DTreeMap.Raw.ofList [⟨2, 12⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_diff_of_not_mem_right` (binder 8): compare, t2 unordered (root 2, unreachable right child 1, size field 0), t1 = {1}: diff erases every key of t2, so 1 goes although 1 is not in t2
theorem w9c3_37 : ¬ drop0% Std.DTreeMap.Raw.get!_diff_of_not_mem_right 8 :=
  fun h => by
  have := h (t₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (t₂ := (⟨.inner 0 2 12 .leaf (.inner 1 1 11 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₁ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_diff_of_not_mem_right` (binder 6): compare, t1 unordered (root 2, unreachable right child 1), t2 = {2}: t1.get! 1 is default, but erasing the root makes 1 reachable
theorem w9c3_38 : ¬ drop0% Std.TreeSet.Raw.get!_diff_of_not_mem_right 6 :=
  fun h => by
  have := h (t₁ := (⟨⟨⟨.inner 2 2 () .leaf (.inner 1 1 () .leaf .leaf)⟩⟩⟩ : TreeSet.Raw Nat compare)) (t₂ := (TreeSet.Raw.ofList [2] compare : TreeSet.Raw Nat compare)) (h₂ := (by wfx)) (k := 1) (not_mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_diff_of_not_mem_right` (binder 7): compare, t2 unordered (root 2, unreachable right child 1, size field 0), t1 = {1}: diff erases every key of t2, so 1 goes although 1 is not in t2
theorem w9c3_39 : ¬ drop0% Std.TreeSet.Raw.get!_diff_of_not_mem_right 7 :=
  fun h => by
  have := h (t₁ := (TreeSet.Raw.ofList [1] compare : TreeSet.Raw Nat compare)) (t₂ := (⟨⟨⟨.inner 0 2 () .leaf (.inner 1 1 () .leaf .leaf)⟩⟩⟩ : TreeSet.Raw Nat compare)) (h₁ := (by wfx)) (k := 1) (not_mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.get!_diff_of_not_mem_right` (binder 5): cmpT, t1 = ofList [1, 2], t2 = ofList [3, 4] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_40 : ¬ drop0% Std.DTreeMap.Const.get!_diff_of_not_mem_right 5 :=
  fun h => by
  have := h (t₁ := (DTreeMap.ofList [⟨1, 11⟩, ⟨2, 12⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (t₂ := (DTreeMap.ofList [⟨3, 13⟩, ⟨4, 14⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_right` (binder 5): cmpT, t1 = ofList [1, 2], t2 = ofList [3, 4] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_41 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_right 5 :=
  fun h => by
  have := h (m₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩, ⟨2, 12⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (m₂ := (DTreeMap.Raw.ofList [⟨3, 13⟩, ⟨4, 14⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_diff_of_not_mem_right` (binder 5): cmpT, t1 = ofList [1, 2], t2 = ofList [3, 4] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_42 : ¬ drop0% Std.DTreeMap.Raw.get!_diff_of_not_mem_right 5 :=
  fun h => by
  have := h (t₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩, ⟨2, 12⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (t₂ := (DTreeMap.Raw.ofList [⟨3, 13⟩, ⟨4, 14⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.get!_diff_of_not_mem_right` (binder 5): cmpT, t1 = ofList [1, 2], t2 = ofList [3, 4] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_43 : ¬ drop0% Std.DTreeMap.get!_diff_of_not_mem_right 5 :=
  fun h => by
  have := h (t₁ := (DTreeMap.ofList [⟨1, 11⟩, ⟨2, 12⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (t₂ := (DTreeMap.ofList [⟨3, 13⟩, ⟨4, 14⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_diff_of_not_mem_right` (binder 5): cmpT, t1 = ofList [1, 2], t2 = ofList [3, 4] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_44 : ¬ drop0% Std.TreeSet.Raw.get!_diff_of_not_mem_right 5 :=
  fun h => by
  have := h (t₁ := (TreeSet.Raw.ofList [1, 2] cmpT : TreeSet.Raw Nat cmpT)) (t₂ := (TreeSet.Raw.ofList [3, 4] cmpT : TreeSet.Raw Nat cmpT)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1) (not_mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.get!_diff_of_not_mem_right` (binder 4): cmpT, t1 = ofList [1, 2], t2 = ofList [3, 4] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the diff lookup differs
theorem w9c3_45 : ¬ drop0% Std.TreeSet.get!_diff_of_not_mem_right 4 :=
  fun h => by
  have := h (t₁ := (TreeSet.ofList [1, 2] cmpT : TreeSet Nat cmpT)) (t₂ := (TreeSet.ofList [3, 4] cmpT : TreeSet Nat cmpT)) (k := 1) (not_mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_right` (binder 10): compare, t1 = {1 ↦ 11}, t2 = {1 ↦ 11}, k = 1
theorem w9c3_46 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_diff_of_not_mem_right 10 :=
  fun h => by
  have := h (m₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (m₂ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_diff_of_not_mem_right` (binder 11): compare, t1 = {1 ↦ 11}, t2 = {1 ↦ 11}, k = 1
theorem w9c3_47 : ¬ drop0% Std.DTreeMap.Raw.get!_diff_of_not_mem_right 11 :=
  fun h => by
  have := h (t₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (t₂ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.get!_diff_of_not_mem_right` (binder 9): compare, t1 = {1 ↦ 11}, t2 = {1 ↦ 11}, k = 1
theorem w9c3_48 : ¬ drop0% Std.DTreeMap.get!_diff_of_not_mem_right 9 :=
  fun h => by
  have := h (t₁ := (DTreeMap.ofList [⟨1, 11⟩] compare : DTreeMap Nat (fun _ => Nat) compare)) (t₂ := (DTreeMap.ofList [⟨1, 11⟩] compare : DTreeMap Nat (fun _ => Nat) compare)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.ExtDTreeMap.get!_diff_of_not_mem_right` (binder 9): compare, t1 = {1 ↦ 11}, t2 = {1 ↦ 11}, k = 1
theorem w9c3_49 : ¬ drop0% Std.ExtDTreeMap.get!_diff_of_not_mem_right 9 :=
  fun h => by
  have := h (t₁ := (⟨Quotient.mk _ (DTreeMap.ofList [⟨1, 11⟩] compare)⟩ : ExtDTreeMap Nat (fun _ => Nat) compare)) (t₂ := (⟨Quotient.mk _ (DTreeMap.ofList [⟨1, 11⟩] compare)⟩ : ExtDTreeMap Nat (fun _ => Nat) compare)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_diff_of_not_mem_right` (binder 9): compare, t1 = {1 ↦ 11}, t2 = {1 ↦ 11}, k = 1
theorem w9c3_50 : ¬ drop0% Std.TreeSet.Raw.get!_diff_of_not_mem_right 9 :=
  fun h => by
  have := h (t₁ := (TreeSet.Raw.ofList [1] compare : TreeSet.Raw Nat compare)) (t₂ := (TreeSet.Raw.ofList [1] compare : TreeSet.Raw Nat compare)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_inter_of_not_mem_left` (binder 7): compare, t1 unordered (root 2, unreachable right child 1), t2 = {1,5,6}: filter drops the root and 1 becomes reachable
theorem w9c3_51 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_inter_of_not_mem_left 7 :=
  fun h => by
  have := h (m₁ := (⟨.inner 2 2 12 .leaf (.inner 1 1 11 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (m₂ := (DTreeMap.Raw.ofList [⟨1, 11⟩, ⟨5, 15⟩, ⟨6, 16⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_inter_of_not_mem_left` (binder 8): inter of WF t1 keeps only entries of t1 (filter branch, or interSmaller which inserts t1.getEntry? results), none equal to k, so get! is default, without t2.WF
theorem w9c3_52 : drop% Std.DTreeMap.Raw.Const.get!_inter_of_not_mem_left 8 :=
  by
  intro _ _ _ _ _ _ _ h₁ k h
  exact W9c3.cg!n _ _ (W9c3.inl h₁.out _ _ (Bool.eq_false_iff.2 h))

-- `Std.DTreeMap.Raw.get!_inter_of_not_mem_left` (binder 7): compare, t1 unordered (root 2, unreachable right child 1), t2 = {1,5,6}: filter drops the root and 1 becomes reachable
theorem w9c3_53 : ¬ drop0% Std.DTreeMap.Raw.get!_inter_of_not_mem_left 7 :=
  fun h => by
  have := h (t₁ := (⟨.inner 2 2 12 .leaf (.inner 1 1 11 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (t₂ := (DTreeMap.Raw.ofList [⟨1, 11⟩, ⟨5, 15⟩, ⟨6, 16⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_inter_of_not_mem_left` (binder 8): inter of WF t1 keeps only entries of t1 (filter branch, or interSmaller which inserts t1.getEntry? results), none equal to k, so get! is default, without t2.WF
theorem w9c3_54 : drop% Std.DTreeMap.Raw.get!_inter_of_not_mem_left 8 :=
  by
  intro _ _ _ _ _ _ _ h₁ k _ h
  exact W9c3.g!n _ _ (W9c3.inl h₁.out _ _ (Bool.eq_false_iff.2 h))

-- `Std.TreeSet.Raw.get!_inter_of_not_mem_left` (binder 6): compare, t1 unordered (root 2, unreachable right child 1), t2 = {1,5,6}: filter drops the root and 1 becomes reachable
theorem w9c3_55 : ¬ drop0% Std.TreeSet.Raw.get!_inter_of_not_mem_left 6 :=
  fun h => by
  have := h (t₁ := (⟨⟨⟨.inner 2 2 () .leaf (.inner 1 1 () .leaf .leaf)⟩⟩⟩ : TreeSet.Raw Nat compare)) (t₂ := (TreeSet.Raw.ofList [1, 5, 6] compare : TreeSet.Raw Nat compare)) (h₂ := (by wfx)) (k := 1) (not_mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_inter_of_not_mem_left` (binder 7): inter of WF t1 keeps only entries of t1 (filter branch, or interSmaller which inserts t1.getEntry? results), none equal to k, so get! is default, without t2.WF
theorem w9c3_56 : drop% Std.TreeSet.Raw.get!_inter_of_not_mem_left 7 :=
  by
  intro _ _ _ _ _ _ h₁ k not_mem
  exact W9c3.kg!n _ _ (W9c3.inl h₁.out.out.out _ _ (Bool.eq_false_iff.2 not_mem))

-- `Std.DTreeMap.Const.get!_inter_of_not_mem_left` (binder 5): cmpT, t1 = ofList [1, 2, 3], t2 = ofList [2, 1, 4] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the inter lookup differs
theorem w9c3_57 : ¬ drop0% Std.DTreeMap.Const.get!_inter_of_not_mem_left 5 :=
  fun h => by
  have := h (t₁ := (DTreeMap.ofList [⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (t₂ := (DTreeMap.ofList [⟨2, 12⟩, ⟨1, 11⟩, ⟨4, 14⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_inter_of_not_mem_left` (binder 5): cmpT, t1 = ofList [1, 2, 3], t2 = ofList [2, 1, 4] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the inter lookup differs
theorem w9c3_58 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_inter_of_not_mem_left 5 :=
  fun h => by
  have := h (m₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (m₂ := (DTreeMap.Raw.ofList [⟨2, 12⟩, ⟨1, 11⟩, ⟨4, 14⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_inter_of_not_mem_left` (binder 5): cmpT, t1 = ofList [1, 2, 3], t2 = ofList [2, 1, 4] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the inter lookup differs
theorem w9c3_59 : ¬ drop0% Std.DTreeMap.Raw.get!_inter_of_not_mem_left 5 :=
  fun h => by
  have := h (t₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (t₂ := (DTreeMap.Raw.ofList [⟨2, 12⟩, ⟨1, 11⟩, ⟨4, 14⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.get!_inter_of_not_mem_left` (binder 5): cmpT, t1 = ofList [1, 2, 3], t2 = ofList [2, 1, 4] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the inter lookup differs
theorem w9c3_60 : ¬ drop0% Std.DTreeMap.get!_inter_of_not_mem_left 5 :=
  fun h => by
  have := h (t₁ := (DTreeMap.ofList [⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (t₂ := (DTreeMap.ofList [⟨2, 12⟩, ⟨1, 11⟩, ⟨4, 14⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (k := 1) (h := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_inter_of_not_mem_left` (binder 5): cmpT, t1 = ofList [1, 2, 3], t2 = ofList [2, 1, 4] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the inter lookup differs
theorem w9c3_61 : ¬ drop0% Std.TreeSet.Raw.get!_inter_of_not_mem_left 5 :=
  fun h => by
  have := h (t₁ := (TreeSet.Raw.ofList [1, 2, 3] cmpT : TreeSet.Raw Nat cmpT)) (t₂ := (TreeSet.Raw.ofList [2, 1, 4] cmpT : TreeSet.Raw Nat cmpT)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1) (not_mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.get!_inter_of_not_mem_left` (binder 4): cmpT, t1 = ofList [1, 2, 3], t2 = ofList [2, 1, 4] (values key+10), k = 1: non-transitive compare leaves keys off the search path, the inter lookup differs
theorem w9c3_62 : ¬ drop0% Std.TreeSet.get!_inter_of_not_mem_left 4 :=
  fun h => by
  have := h (t₁ := (TreeSet.ofList [1, 2, 3] cmpT : TreeSet Nat cmpT)) (t₂ := (TreeSet.ofList [2, 1, 4] cmpT : TreeSet Nat cmpT)) (k := 1) (not_mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_inter_of_not_mem_left` (binder 10): compare, t1 = {1 ↦ 11}, t2 = {1 ↦ 11}, k = 1
theorem w9c3_63 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_inter_of_not_mem_left 10 :=
  fun h => by
  have := h (m₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (m₂ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get!_inter_of_not_mem_left` (binder 11): compare, t1 = {1 ↦ 11}, t2 = {1 ↦ 11}, k = 1
theorem w9c3_64 : ¬ drop0% Std.DTreeMap.Raw.get!_inter_of_not_mem_left 11 :=
  fun h => by
  have := h (t₁ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (t₂ := (DTreeMap.Raw.ofList [⟨1, 11⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.get!_inter_of_not_mem_left` (binder 9): compare, t1 = {1 ↦ 11}, t2 = {1 ↦ 11}, k = 1
theorem w9c3_65 : ¬ drop0% Std.DTreeMap.get!_inter_of_not_mem_left 9 :=
  fun h => by
  have := h (t₁ := (DTreeMap.ofList [⟨1, 11⟩] compare : DTreeMap Nat (fun _ => Nat) compare)) (t₂ := (DTreeMap.ofList [⟨1, 11⟩] compare : DTreeMap Nat (fun _ => Nat) compare)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.ExtDTreeMap.get!_inter_of_not_mem_left` (binder 9): compare, t1 = {1 ↦ 11}, t2 = {1 ↦ 11}, k = 1
theorem w9c3_66 : ¬ drop0% Std.ExtDTreeMap.get!_inter_of_not_mem_left 9 :=
  fun h => by
  have := h (t₁ := (⟨Quotient.mk _ (DTreeMap.ofList [⟨1, 11⟩] compare)⟩ : ExtDTreeMap Nat (fun _ => Nat) compare)) (t₂ := (⟨Quotient.mk _ (DTreeMap.ofList [⟨1, 11⟩] compare)⟩ : ExtDTreeMap Nat (fun _ => Nat) compare)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_inter_of_not_mem_left` (binder 9): compare, t1 = {1 ↦ 11}, t2 = {1 ↦ 11}, k = 1
theorem w9c3_67 : ¬ drop0% Std.TreeSet.Raw.get!_inter_of_not_mem_left 9 :=
  fun h => by
  have := h (t₁ := (TreeSet.Raw.ofList [1] compare : TreeSet.Raw Nat compare)) (t₂ := (TreeSet.Raw.ofList [1] compare : TreeSet.Raw Nat compare)) (h₁ := (by wfx)) (h₂ := (by wfx)) (k := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.get!_of_isEmpty` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_68 : drop% Std.DTreeMap.Internal.Impl.Const.get!_of_isEmpty 6 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.get!_of_isEmpty` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_69 : drop% Std.DTreeMap.Internal.Impl.get!_of_isEmpty 6 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.get!_of_isEmpty` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_70 : drop% Std.DTreeMap.Raw.Const.get!_of_isEmpty 6 :=
  by w93g

-- `Std.DTreeMap.Raw.get!_of_isEmpty` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_71 : drop% Std.DTreeMap.Raw.get!_of_isEmpty 6 :=
  by w93g

-- `Std.TreeSet.Raw.get!_of_isEmpty` (binder 5): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_72 : drop% Std.TreeSet.Raw.get!_of_isEmpty 5 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.Const.get!_of_isEmpty` (binder 8): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_73 : ¬ drop0% Std.DTreeMap.Internal.Impl.Const.get!_of_isEmpty 8 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord Nat)) (t := ((DTreeMap.ofList [⟨1, 5⟩] compare : DTreeMap Nat (fun _ => Nat) compare).inner : Impl Nat (fun _ => Nat))) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.get!_of_isEmpty` (binder 9): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_74 : ¬ drop0% Std.DTreeMap.Internal.Impl.get!_of_isEmpty 9 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord Nat)) (t := ((DTreeMap.ofList [⟨1, 5⟩] compare : DTreeMap Nat (fun _ => Nat) compare).inner : Impl Nat (fun _ => Nat))) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get!_of_isEmpty` (binder 8): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_75 : ¬ drop0% Std.DTreeMap.Raw.Const.get!_of_isEmpty 8 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨1, 5⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.get!_of_isEmpty` (binder 8): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_76 : ¬ drop0% Std.DTreeMap.get!_of_isEmpty 8 :=
  fun h => by
  have := h (t := (DTreeMap.ofList [⟨1, 5⟩] compare : DTreeMap Nat (fun _ => Nat) compare)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get!_of_isEmpty` (binder 7): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_77 : ¬ drop0% Std.TreeSet.Raw.get!_of_isEmpty 7 :=
  fun h => by
  have := h (t := (TreeSet.Raw.ofList [1] compare : TreeSet.Raw Nat compare)) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.get!_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_78 : drop% Std.DTreeMap.Const.get!_of_isEmpty 4 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.get!_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_79 : drop% Std.DTreeMap.Raw.Const.get!_of_isEmpty 4 :=
  by w93g

-- `Std.DTreeMap.Raw.get!_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_80 : drop% Std.DTreeMap.Raw.get!_of_isEmpty 4 :=
  by w93g

-- `Std.DTreeMap.get!_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_81 : drop% Std.DTreeMap.get!_of_isEmpty 4 :=
  by w93g

-- `Std.TreeSet.Raw.get!_of_isEmpty` (binder 3): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_82 : drop% Std.TreeSet.Raw.get!_of_isEmpty 3 :=
  by w93g

-- `Std.TreeSet.get!_of_isEmpty` (binder 3): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_83 : drop% Std.TreeSet.get!_of_isEmpty 3 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.Const.get!_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_84 : drop% Std.DTreeMap.Internal.Impl.Const.get!_of_isEmpty 4 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.get!_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_85 : drop% Std.DTreeMap.Internal.Impl.get!_of_isEmpty 4 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.Const.get?_eq_none_of_contains_eq_false` (binder 5): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_86 : drop% Std.DTreeMap.Internal.Impl.Const.get?_eq_none_of_contains_eq_false 5 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.get?_eq_none_of_contains_eq_false` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_87 : drop% Std.DTreeMap.Internal.Impl.get?_eq_none_of_contains_eq_false 6 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.get?_eq_none_of_contains_eq_false` (binder 5): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_88 : drop% Std.DTreeMap.Raw.Const.get?_eq_none_of_contains_eq_false 5 :=
  by w93g

-- `Std.DTreeMap.Raw.get?_eq_none_of_contains_eq_false` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_89 : drop% Std.DTreeMap.Raw.get?_eq_none_of_contains_eq_false 6 :=
  by w93g

-- `Std.TreeSet.Raw.get?_eq_none_of_contains_eq_false` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_90 : drop% Std.TreeSet.Raw.get?_eq_none_of_contains_eq_false 4 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.get?_eq_none_of_contains_eq_false` (binder 7): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_91 : ¬ drop0% Std.DTreeMap.Raw.Const.get?_eq_none_of_contains_eq_false 7 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨1, 5⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get?_eq_none_of_contains_eq_false` (binder 8): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_92 : ¬ drop0% Std.DTreeMap.Raw.get?_eq_none_of_contains_eq_false 8 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨1, 5⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get?_eq_none_of_contains_eq_false` (binder 6): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_93 : ¬ drop0% Std.TreeSet.Raw.get?_eq_none_of_contains_eq_false 6 :=
  fun h => by
  have := h (t := (TreeSet.Raw.ofList [1] compare : TreeSet.Raw Nat compare)) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.get?_eq_none_of_contains_eq_false` (binder 7): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_94 : ¬ drop0% Std.DTreeMap.Internal.Impl.Const.get?_eq_none_of_contains_eq_false 7 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord Nat)) (t := ((DTreeMap.ofList [⟨1, 5⟩] compare : DTreeMap Nat (fun _ => Nat) compare).inner : Impl Nat (fun _ => Nat))) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.get?_eq_none_of_contains_eq_false` (binder 8): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_95 : ¬ drop0% Std.DTreeMap.Internal.Impl.get?_eq_none_of_contains_eq_false 8 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord Nat)) (t := ((DTreeMap.ofList [⟨1, 5⟩] compare : DTreeMap Nat (fun _ => Nat) compare).inner : Impl Nat (fun _ => Nat))) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.get?_eq_none_of_contains_eq_false` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_96 : drop% Std.DTreeMap.Const.get?_eq_none_of_contains_eq_false 4 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.get?_eq_none_of_contains_eq_false` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_97 : drop% Std.DTreeMap.Raw.Const.get?_eq_none_of_contains_eq_false 4 :=
  by w93g

-- `Std.DTreeMap.Raw.get?_eq_none_of_contains_eq_false` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_98 : drop% Std.DTreeMap.Raw.get?_eq_none_of_contains_eq_false 4 :=
  by w93g

-- `Std.DTreeMap.get?_eq_none_of_contains_eq_false` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_99 : drop% Std.DTreeMap.get?_eq_none_of_contains_eq_false 4 :=
  by w93g

-- `Std.TreeSet.Raw.get?_eq_none_of_contains_eq_false` (binder 3): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_100 : drop% Std.TreeSet.Raw.get?_eq_none_of_contains_eq_false 3 :=
  by w93g

-- `Std.TreeSet.get?_eq_none_of_contains_eq_false` (binder 3): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_101 : drop% Std.TreeSet.get?_eq_none_of_contains_eq_false 3 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.Const.get?_eq_none_of_contains_eq_false` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_102 : drop% Std.DTreeMap.Internal.Impl.Const.get?_eq_none_of_contains_eq_false 4 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.get?_eq_none_of_contains_eq_false` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_103 : drop% Std.DTreeMap.Internal.Impl.get?_eq_none_of_contains_eq_false 4 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.Const.get?_eq_some_get!_of_contains` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_104 : drop% Std.DTreeMap.Internal.Impl.Const.get?_eq_some_get!_of_contains 6 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.get?_eq_some_get!_of_contains` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_105 : drop% Std.DTreeMap.Internal.Impl.get?_eq_some_get!_of_contains 6 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.get?_eq_some_get!_of_contains` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_106 : drop% Std.DTreeMap.Raw.Const.get?_eq_some_get!_of_contains 6 :=
  by w93g

-- `Std.DTreeMap.Raw.get?_eq_some_get!_of_contains` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_107 : drop% Std.DTreeMap.Raw.get?_eq_some_get!_of_contains 6 :=
  by w93g

-- `Std.TreeSet.Raw.get?_eq_some_get!_of_contains` (binder 5): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_108 : drop% Std.TreeSet.Raw.get?_eq_some_get!_of_contains 5 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.get?_eq_some_get!_of_contains` (binder 8): compare, t = ∅, a = 1: get? is none
theorem w9c3_109 : ¬ drop0% Std.DTreeMap.Raw.Const.get?_eq_some_get!_of_contains 8 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get?_eq_some_get!_of_contains` (binder 9): compare, t = ∅, a = 1: get? is none
theorem w9c3_110 : ¬ drop0% Std.DTreeMap.Raw.get?_eq_some_get!_of_contains 9 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get?_eq_some_get!_of_contains` (binder 7): compare, t = ∅, a = 1: get? is none
theorem w9c3_111 : ¬ drop0% Std.TreeSet.Raw.get?_eq_some_get!_of_contains 7 :=
  fun h => by
  have := h (t := (TreeSet.Raw.ofList [] compare : TreeSet.Raw Nat compare)) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.get?_eq_some_get!_of_contains` (binder 8): compare, t = ∅, a = 1: get? is none
theorem w9c3_112 : ¬ drop0% Std.DTreeMap.Internal.Impl.Const.get?_eq_some_get!_of_contains 8 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord Nat)) (t := ((DTreeMap.ofList [] compare : DTreeMap Nat (fun _ => Nat) compare).inner : Impl Nat (fun _ => Nat))) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.get?_eq_some_get!_of_contains` (binder 9): compare, t = ∅, a = 1: get? is none
theorem w9c3_113 : ¬ drop0% Std.DTreeMap.Internal.Impl.get?_eq_some_get!_of_contains 9 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord Nat)) (t := ((DTreeMap.ofList [] compare : DTreeMap Nat (fun _ => Nat) compare).inner : Impl Nat (fun _ => Nat))) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.get?_eq_some_get!_of_contains` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_114 : drop% Std.DTreeMap.Const.get?_eq_some_get!_of_contains 4 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.get?_eq_some_get!_of_contains` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_115 : drop% Std.DTreeMap.Raw.Const.get?_eq_some_get!_of_contains 4 :=
  by w93g

-- `Std.DTreeMap.Raw.get?_eq_some_get!_of_contains` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_116 : drop% Std.DTreeMap.Raw.get?_eq_some_get!_of_contains 4 :=
  by w93g

-- `Std.DTreeMap.get?_eq_some_get!_of_contains` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_117 : drop% Std.DTreeMap.get?_eq_some_get!_of_contains 4 :=
  by w93g

-- `Std.TreeSet.Raw.get?_eq_some_get!_of_contains` (binder 3): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_118 : drop% Std.TreeSet.Raw.get?_eq_some_get!_of_contains 3 :=
  by w93g

-- `Std.TreeSet.get?_eq_some_get!_of_contains` (binder 3): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_119 : drop% Std.TreeSet.get?_eq_some_get!_of_contains 3 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.Const.get?_eq_some_get!_of_contains` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_120 : drop% Std.DTreeMap.Internal.Impl.Const.get?_eq_some_get!_of_contains 4 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.get?_eq_some_get!_of_contains` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_121 : drop% Std.DTreeMap.Internal.Impl.get?_eq_some_get!_of_contains 4 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.Const.get?_eq_some_getD` (binder 8): compare, t = ∅, a = 1: get? is none
theorem w9c3_122 : ¬ drop0% Std.DTreeMap.Internal.Impl.Const.get?_eq_some_getD 8 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord Nat)) (t := ((DTreeMap.ofList [] compare : DTreeMap Nat (fun _ => Nat) compare).inner : Impl Nat (fun _ => Nat))) (h := (by wfx)) (a := 1) (fallback := 3)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.get?_eq_some_getD` (binder 9): compare, t = ∅, a = 1: get? is none
theorem w9c3_123 : ¬ drop0% Std.DTreeMap.Internal.Impl.get?_eq_some_getD 9 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord Nat)) (t := ((DTreeMap.ofList [] compare : DTreeMap Nat (fun _ => Nat) compare).inner : Impl Nat (fun _ => Nat))) (h := (by wfx)) (a := 1) (fallback := 3)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get?_eq_some_getD` (binder 8): compare, t = ∅, a = 1: get? is none
theorem w9c3_124 : ¬ drop0% Std.DTreeMap.Raw.Const.get?_eq_some_getD 8 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (a := 1) (fallback := 3)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get?_eq_some_getD` (binder 9): compare, t = ∅, a = 1: get? is none
theorem w9c3_125 : ¬ drop0% Std.DTreeMap.Raw.get?_eq_some_getD 9 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (a := 1) (fallback := 3)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get?_eq_some_getD` (binder 7): compare, t = ∅, a = 1: get? is none
theorem w9c3_126 : ¬ drop0% Std.TreeSet.Raw.get?_eq_some_getD 7 :=
  fun h => by
  have := h (t := (TreeSet.Raw.ofList [] compare : TreeSet.Raw Nat compare)) (h := (by wfx)) (a := 1) (fallback := 3)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.get?_eq_some_getD` (binder 5): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_127 : drop% Std.DTreeMap.Internal.Impl.Const.get?_eq_some_getD 5 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.get?_eq_some_getD` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_128 : drop% Std.DTreeMap.Internal.Impl.get?_eq_some_getD 6 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.get?_eq_some_getD` (binder 5): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_129 : drop% Std.DTreeMap.Raw.Const.get?_eq_some_getD 5 :=
  by w93g

-- `Std.DTreeMap.Raw.get?_eq_some_getD` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_130 : drop% Std.DTreeMap.Raw.get?_eq_some_getD 6 :=
  by w93g

-- `Std.TreeSet.Raw.get?_eq_some_getD` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_131 : drop% Std.TreeSet.Raw.get?_eq_some_getD 4 :=
  by w93g

-- `Std.DTreeMap.Const.get?_eq_some_getD` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_132 : drop% Std.DTreeMap.Const.get?_eq_some_getD 4 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.get?_eq_some_getD` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_133 : drop% Std.DTreeMap.Raw.Const.get?_eq_some_getD 4 :=
  by w93g

-- `Std.DTreeMap.Raw.get?_eq_some_getD` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_134 : drop% Std.DTreeMap.Raw.get?_eq_some_getD 4 :=
  by w93g

-- `Std.DTreeMap.get?_eq_some_getD` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_135 : drop% Std.DTreeMap.get?_eq_some_getD 4 :=
  by w93g

-- `Std.TreeSet.Raw.get?_eq_some_getD` (binder 3): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_136 : drop% Std.TreeSet.Raw.get?_eq_some_getD 3 :=
  by w93g

-- `Std.TreeSet.get?_eq_some_getD` (binder 3): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_137 : drop% Std.TreeSet.get?_eq_some_getD 3 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.Const.get?_eq_some_getD` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_138 : drop% Std.DTreeMap.Internal.Impl.Const.get?_eq_some_getD 4 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.get?_eq_some_getD` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_139 : drop% Std.DTreeMap.Internal.Impl.get?_eq_some_getD 4 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.Const.get?_of_isEmpty` (binder 5): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_140 : drop% Std.DTreeMap.Internal.Impl.Const.get?_of_isEmpty 5 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.get?_of_isEmpty` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_141 : drop% Std.DTreeMap.Internal.Impl.get?_of_isEmpty 6 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.get?_of_isEmpty` (binder 5): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_142 : drop% Std.DTreeMap.Raw.Const.get?_of_isEmpty 5 :=
  by w93g

-- `Std.DTreeMap.Raw.get?_of_isEmpty` (binder 6): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_143 : drop% Std.DTreeMap.Raw.get?_of_isEmpty 6 :=
  by w93g

-- `Std.TreeSet.Raw.get?_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_144 : drop% Std.TreeSet.Raw.get?_of_isEmpty 4 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.Const.get?_of_isEmpty` (binder 7): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_145 : ¬ drop0% Std.DTreeMap.Internal.Impl.Const.get?_of_isEmpty 7 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord Nat)) (t := ((DTreeMap.ofList [⟨1, 5⟩] compare : DTreeMap Nat (fun _ => Nat) compare).inner : Impl Nat (fun _ => Nat))) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.get?_of_isEmpty` (binder 8): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_146 : ¬ drop0% Std.DTreeMap.Internal.Impl.get?_of_isEmpty 8 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord Nat)) (t := ((DTreeMap.ofList [⟨1, 5⟩] compare : DTreeMap Nat (fun _ => Nat) compare).inner : Impl Nat (fun _ => Nat))) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.get?_of_isEmpty` (binder 7): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_147 : ¬ drop0% Std.DTreeMap.Raw.Const.get?_of_isEmpty 7 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨1, 5⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.get?_of_isEmpty` (binder 8): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_148 : ¬ drop0% Std.DTreeMap.Raw.get?_of_isEmpty 8 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨1, 5⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.get?_of_isEmpty` (binder 6): compare, t = {1 ↦ 5}, a = 1: the lookup finds the entry
theorem w9c3_149 : ¬ drop0% Std.TreeSet.Raw.get?_of_isEmpty 6 :=
  fun h => by
  have := h (t := (TreeSet.Raw.ofList [1] compare : TreeSet.Raw Nat compare)) (h := (by wfx)) (a := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.get?_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_150 : drop% Std.DTreeMap.Const.get?_of_isEmpty 4 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.get?_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_151 : drop% Std.DTreeMap.Raw.Const.get?_of_isEmpty 4 :=
  by w93g

-- `Std.DTreeMap.Raw.get?_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_152 : drop% Std.DTreeMap.Raw.get?_of_isEmpty 4 :=
  by w93g

-- `Std.DTreeMap.get?_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_153 : drop% Std.DTreeMap.get?_of_isEmpty 4 :=
  by w93g

-- `Std.TreeSet.Raw.get?_of_isEmpty` (binder 3): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_154 : drop% Std.TreeSet.Raw.get?_of_isEmpty 3 :=
  by w93g

-- `Std.TreeSet.get?_of_isEmpty` (binder 3): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_155 : drop% Std.TreeSet.get?_of_isEmpty 3 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.Const.get?_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_156 : drop% Std.DTreeMap.Internal.Impl.Const.get?_of_isEmpty 4 :=
  by w93g

-- `Std.DTreeMap.Internal.Impl.get?_of_isEmpty` (binder 4): get?/get!/getD/getKey? and contains follow the same search path (isEmpty means leaf), so the lookup identity holds for any compare and any tree
theorem w9c3_157 : drop% Std.DTreeMap.Internal.Impl.get?_of_isEmpty 4 :=
  by w93g

-- `Std.DTreeMap.Raw.Const.getD_ofList_of_contains_eq_false` (binder 9): compare, l = [0 ↦ 5], k = 0, fallback 1: getD returns 5
theorem w9c3_158 : ¬ drop0% Std.DTreeMap.Raw.Const.getD_ofList_of_contains_eq_false 9 :=
  fun h => by
  have := h (α := Nat) (cmp := compare) (l := [(0, 5)]) (k := 0) (fallback := 1)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getD_ofList_of_contains_eq_false` (binder 9): compare, l = [0 ↦ 5], k = 0, fallback 1: getD returns 5
theorem w9c3_159 : ¬ drop0% Std.TreeMap.Raw.getD_ofList_of_contains_eq_false 9 :=
  fun h => by
  have := h (α := Nat) (cmp := compare) (l := [(0, 5)]) (k := 0) (fallback := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.getD_ofList_of_contains_eq_false` (binder 10): compare, l = [0 ↦ 5], k = 0, fallback 1: getD returns 5
theorem w9c3_160 : ¬ drop0% Std.DTreeMap.Raw.getD_ofList_of_contains_eq_false 10 :=
  fun h => by
  have := h (α := Nat) (β := (fun _ => Nat)) (cmp := compare) (l := [⟨0, 5⟩]) (k := 0) (fallback := 1)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.getD_ofList_of_contains_eq_false` (binder 8): compare, l = [0 ↦ 5], k = 0, fallback 1: getD returns 5
theorem w9c3_161 : ¬ drop0% Std.TreeSet.Raw.getD_ofList_of_contains_eq_false 8 :=
  fun h => by
  have := h (α := Nat) (cmp := compare) (l := [0]) (k := 0) (fallback := 1)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getD_ofList_of_contains_eq_false` (binder 5): compare with BEq always false: l = [0 ↦ 5], k = 0, fallback 1: l "does not contain" 0 but getD finds it
theorem w9c3_162 : ¬ drop0% Std.DTreeMap.Raw.Const.getD_ofList_of_contains_eq_false 5 :=
  fun h => by
  letI : BEq Nat := ⟨fun _ _ => false⟩
  have := h (α := Nat) (cmp := compare) (l := [(0, 5)]) (k := 0) (fallback := 1) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.getD_ofList_of_contains_eq_false` (binder 6): compare with BEq always false: l = [0 ↦ 5], k = 0, fallback 1: l "does not contain" 0 but getD finds it
theorem w9c3_163 : ¬ drop0% Std.DTreeMap.Raw.getD_ofList_of_contains_eq_false 6 :=
  fun h => by
  letI : BEq Nat := ⟨fun _ _ => false⟩
  have := h (α := Nat) (β := (fun _ => Nat)) (cmp := compare) (l := [⟨0, 5⟩]) (k := 0) (fallback := 1) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.ExtDTreeMap.getD_ofList_of_contains_eq_false` (binder 6): compare with BEq always false: l = [0 ↦ 5], k = 0, fallback 1: l "does not contain" 0 but getD finds it
theorem w9c3_164 : ¬ drop0% Std.ExtDTreeMap.getD_ofList_of_contains_eq_false 6 :=
  fun h => by
  letI : BEq Nat := ⟨fun _ _ => false⟩
  have := h (α := Nat) (β := (fun _ => Nat)) (cmp := compare) (l := [⟨0, 5⟩]) (k := 0) (fallback := 1) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getD_ofList_of_contains_eq_false` (binder 5): compare with BEq always false: l = [0 ↦ 5], k = 0, fallback 1: l "does not contain" 0 but getD finds it
theorem w9c3_165 : ¬ drop0% Std.TreeMap.Raw.getD_ofList_of_contains_eq_false 5 :=
  fun h => by
  letI : BEq Nat := ⟨fun _ _ => false⟩
  have := h (α := Nat) (cmp := compare) (l := [(0, 5)]) (k := 0) (fallback := 1) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.getD_ofList_of_contains_eq_false` (binder 4): compare with BEq always false: l = [0 ↦ 5], k = 0, fallback 1: l "does not contain" 0 but getD finds it
theorem w9c3_166 : ¬ drop0% Std.TreeSet.Raw.getD_ofList_of_contains_eq_false 4 :=
  fun h => by
  letI : BEq Nat := ⟨fun _ _ => false⟩
  have := h (α := Nat) (cmp := compare) (l := [0]) (k := 0) (fallback := 1) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.getD_ofList_of_contains_eq_false` (binder 4): refute_dep
theorem w9c3_167 : ¬ indep0% Std.DTreeMap.Raw.getD_ofList_of_contains_eq_false 4 :=
  by refute_dep

-- `Std.DTreeMap.Raw.Const.getD_ofList_of_contains_eq_false` (binder 3): every entry of ofList is an entry of l (insert only adds the inserted pair, for any compare), and under LawfulBEqCmp no key of l compares eq to k, so contains k is false and getD returns the fallback
theorem w9c3_168 : drop% Std.DTreeMap.Raw.Const.getD_ofList_of_contains_eq_false 3 :=
  by w93o

-- `Std.DTreeMap.Raw.getD_ofList_of_contains_eq_false` (binder 3): every entry of ofList is an entry of l (insert only adds the inserted pair, for any compare), and under LawfulBEqCmp no key of l compares eq to k, so contains k is false and getD returns the fallback
theorem w9c3_169 : drop% Std.DTreeMap.Raw.getD_ofList_of_contains_eq_false 3 :=
  by w93o

-- `Std.DTreeMap.getD_ofList_of_contains_eq_false` (binder 3): every entry of ofList is an entry of l (insert only adds the inserted pair, for any compare), and under LawfulBEqCmp no key of l compares eq to k, so contains k is false and getD returns the fallback
theorem w9c3_170 : drop% Std.DTreeMap.getD_ofList_of_contains_eq_false 3 :=
  by w93o

-- `Std.TreeMap.Raw.getD_ofList_of_contains_eq_false` (binder 3): every entry of ofList is an entry of l (insert only adds the inserted pair, for any compare), and under LawfulBEqCmp no key of l compares eq to k, so contains k is false and getD returns the fallback
theorem w9c3_171 : drop% Std.TreeMap.Raw.getD_ofList_of_contains_eq_false 3 :=
  by w93o

-- `Std.TreeMap.getD_ofList_of_contains_eq_false` (binder 3): every entry of ofList is an entry of l (insert only adds the inserted pair, for any compare), and under LawfulBEqCmp no key of l compares eq to k, so contains k is false and getD returns the fallback
theorem w9c3_172 : drop% Std.TreeMap.getD_ofList_of_contains_eq_false 3 :=
  by w93o

-- `Std.TreeSet.Raw.getD_ofList_of_contains_eq_false` (binder 2): every entry of ofList is an entry of l (insert only adds the inserted pair, for any compare), and under LawfulBEqCmp no key of l compares eq to k, so contains k is false and getD returns the fallback
theorem w9c3_173 : drop% Std.TreeSet.Raw.getD_ofList_of_contains_eq_false 2 :=
  by w93o

-- `Std.TreeSet.getD_ofList_of_contains_eq_false` (binder 2): every entry of ofList is an entry of l (insert only adds the inserted pair, for any compare), and under LawfulBEqCmp no key of l compares eq to k, so contains k is false and getD returns the fallback
theorem w9c3_174 : drop% Std.TreeSet.getD_ofList_of_contains_eq_false 2 :=
  by w93o

-- `Std.DTreeMap.Raw.Const.getKey?_insertMany_list_of_contains_eq_false` (binder 10): compare, t = ∅, l = [0 ↦ 5], k = 0: getKey? 0 becomes some 0
theorem w9c3_175 : ¬ drop0% Std.DTreeMap.Raw.Const.getKey?_insertMany_list_of_contains_eq_false 10 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (l := [(0, 5)]) (k := 0)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false` (binder 10): compare, t = ∅, l = [0 ↦ 5], k = 0: getKey? 0 becomes some 0
theorem w9c3_176 : ¬ drop0% Std.TreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false 10 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [] compare : TreeMap.Raw Nat Nat compare)) (h := (by wfx)) (l := [(0, 5)]) (k := 0)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false` (binder 10): compare, t = ∅, l = [0 ↦ 5], k = 0: getKey? 0 becomes some 0
theorem w9c3_177 : ¬ drop0% Std.DTreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false 10 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (l := [⟨0, 5⟩]) (k := 0)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getKey?_insertMany_list_of_contains_eq_false` (binder 7): compare, t unordered (root 1, right child 0), l = [5]: the insertion rebalances and 0 becomes reachable
theorem w9c3_178 : ¬ drop0% Std.DTreeMap.Raw.Const.getKey?_insertMany_list_of_contains_eq_false 7 :=
  fun h => by
  have := h (t := (⟨.inner 2 1 1 .leaf (.inner 1 0 9 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (l := [(5, 5)]) (k := 0) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false` (binder 7): compare, t unordered (root 1, right child 0), l = [5]: the insertion rebalances and 0 becomes reachable
theorem w9c3_179 : ¬ drop0% Std.DTreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false 7 :=
  fun h => by
  have := h (t := (⟨.inner 2 1 1 .leaf (.inner 1 0 9 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (l := [⟨5, 5⟩]) (k := 0) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false` (binder 7): compare, t unordered (root 1, right child 0), l = [5]: the insertion rebalances and 0 becomes reachable
theorem w9c3_180 : ¬ drop0% Std.TreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false 7 :=
  fun h => by
  have := h (t := (⟨⟨.inner 2 1 1 .leaf (.inner 1 0 9 .leaf .leaf)⟩⟩ : TreeMap.Raw Nat Nat compare)) (l := [(5, 5)]) (k := 0) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getKey?_insertMany_list_of_contains_eq_false` (binder 6): compare with BEq always false: t = ∅, l = [0 ↦ 5], k = 0: l "does not contain" 0 but insertMany adds it
theorem w9c3_181 : ¬ drop0% Std.DTreeMap.Raw.Const.getKey?_insertMany_list_of_contains_eq_false 6 :=
  fun h => by
  letI : BEq Nat := ⟨fun _ _ => false⟩
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (l := [(0, 5)]) (k := 0) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false` (binder 6): compare with BEq always false: t = ∅, l = [0 ↦ 5], k = 0: l "does not contain" 0 but insertMany adds it
theorem w9c3_182 : ¬ drop0% Std.DTreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false 6 :=
  fun h => by
  letI : BEq Nat := ⟨fun _ _ => false⟩
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (l := [⟨0, 5⟩]) (k := 0) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false` (binder 6): compare with BEq always false: t = ∅, l = [0 ↦ 5], k = 0: l "does not contain" 0 but insertMany adds it
theorem w9c3_183 : ¬ drop0% Std.TreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false 6 :=
  fun h => by
  letI : BEq Nat := ⟨fun _ _ => false⟩
  have := h (t := (TreeMap.Raw.ofList [] compare : TreeMap.Raw Nat Nat compare)) (h := (by wfx)) (l := [(0, 5)]) (k := 0) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.getKey?_insertMany_list_of_contains_eq_false` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: inserting 0 rebalances and 2 is no longer found
theorem w9c3_184 : ¬ drop0% Std.DTreeMap.Const.getKey?_insertMany_list_of_contains_eq_false 4 :=
  fun h => by
  have := h (t := (DTreeMap.ofList [⟨0, 10⟩, ⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (l := [(0, 20)]) (k := 2) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getKey?_insertMany_list_of_contains_eq_false` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: inserting 0 rebalances and 2 is no longer found
theorem w9c3_185 : ¬ drop0% Std.DTreeMap.Raw.Const.getKey?_insertMany_list_of_contains_eq_false 4 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨0, 10⟩, ⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (h := (by wfx)) (l := [(0, 20)]) (k := 2) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: inserting 0 rebalances and 2 is no longer found
theorem w9c3_186 : ¬ drop0% Std.DTreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false 4 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨0, 10⟩, ⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (h := (by wfx)) (l := [⟨0, 20⟩]) (k := 2) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.getKey?_insertMany_list_of_contains_eq_false` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: inserting 0 rebalances and 2 is no longer found
theorem w9c3_187 : ¬ drop0% Std.DTreeMap.getKey?_insertMany_list_of_contains_eq_false 4 :=
  fun h => by
  have := h (t := (DTreeMap.ofList [⟨0, 10⟩, ⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (l := [⟨0, 20⟩]) (k := 2) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: inserting 0 rebalances and 2 is no longer found
theorem w9c3_188 : ¬ drop0% Std.TreeMap.Raw.getKey?_insertMany_list_of_contains_eq_false 4 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [(0, 10), (1, 11), (2, 12), (3, 13)] cmpT : TreeMap.Raw Nat Nat cmpT)) (h := (by wfx)) (l := [(0, 20)]) (k := 2) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.getKey?_insertMany_list_of_contains_eq_false` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: inserting 0 rebalances and 2 is no longer found
theorem w9c3_189 : ¬ drop0% Std.TreeMap.getKey?_insertMany_list_of_contains_eq_false 4 :=
  fun h => by
  have := h (t := (TreeMap.ofList [(0, 10), (1, 11), (2, 12), (3, 13)] cmpT : TreeMap Nat Nat cmpT)) (l := [(0, 20)]) (k := 2) (contains_eq_false := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.getKey?_insertMany_list_of_contains_eq_false` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: inserting 0 rebalances and 2 is no longer found
theorem w9c3_190 : ¬ drop0% Std.DTreeMap.Internal.Impl.Const.getKey?_insertMany_list_of_contains_eq_false 4 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord OT)) (t := ((DTreeMap.ofList [⟨0, 10⟩, ⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] compare : DTreeMap OT (fun _ => Nat) compare).inner : Impl OT (fun _ => Nat))) (h := (by wfx)) (l := [(0, 20)]) (k := 2) (h' := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.getKey?_insertMany_list_of_contains_eq_false` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: inserting 0 rebalances and 2 is no longer found
theorem w9c3_191 : ¬ drop0% Std.DTreeMap.Internal.Impl.getKey?_insertMany_list_of_contains_eq_false 4 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord OT)) (t := ((DTreeMap.ofList [⟨0, 10⟩, ⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩] compare : DTreeMap OT (fun _ => Nat) compare).inner : Impl OT (fun _ => Nat))) (h := (by wfx)) (l := [⟨0, 20⟩]) (k := 2) (h' := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 12): compare, t = ∅, l = [], k = k' = 0: getKeyD is the fallback 7
theorem w9c3_192 : ¬ drop0% Std.DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 12 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Unit) compare)) (h := (by wfx)) (l := []) (k := 0) (k' := 0) (fallback := 7) (k_eq := (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 12): compare, t = ∅, l = [], k = k' = 0: getKeyD is the fallback 7
theorem w9c3_193 : ¬ drop0% Std.TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 12 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [] compare : TreeMap.Raw Nat Unit compare)) (h := (by wfx)) (l := []) (k := 0) (k' := 0) (fallback := 7) (k_eq := (by decide +kernel)) (not_mem := (by decide +kernel)) (distinct := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 11): cmpH (halves), t = ∅, l = [0, 1], k = k' = 1: 1 is not inserted (0 is equal to it), getKeyD 1 = 0
theorem w9c3_194 : ¬ drop0% Std.DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 11 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] cmpH : DTreeMap.Raw Nat (fun _ => Unit) cmpH)) (h := (by wfx)) (l := [0, 1]) (k := 1) (k' := 1) (fallback := 7) (k_eq := (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 10): cmpH (halves), t = ∅, l = [0, 1], k = k' = 1: 1 is not inserted (0 is equal to it), getKeyD 1 = 0
theorem w9c3_195 : ¬ drop0% Std.ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 10 :=
  fun h => by
  have := h (t := (⟨Quotient.mk _ (DTreeMap.ofList [] cmpH)⟩ : ExtDTreeMap Nat (fun _ => Unit) cmpH)) (l := [0, 1]) (k := 1) (k' := 1) (fallback := 7) (k_eq := (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 10): cmpH (halves), t = ∅, l = [0, 1], k = k' = 1: 1 is not inserted (0 is equal to it), getKeyD 1 = 0
theorem w9c3_196 : ¬ drop0% Std.ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 10 :=
  fun h => by
  have := h (t := (⟨⟨Quotient.mk _ (DTreeMap.ofList [] cmpH)⟩⟩ : ExtTreeMap Nat Unit cmpH)) (l := [0, 1]) (k := 1) (k' := 1) (fallback := 7) (k_eq := (by decide +kernel)) (not_mem := (by decide +kernel)) (mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 11): cmpH (halves), t = ∅, l = [0, 1], k = k' = 1: 1 is not inserted (0 is equal to it), getKeyD 1 = 0
theorem w9c3_197 : ¬ drop0% Std.TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 11 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [] cmpH : TreeMap.Raw Nat Unit cmpH)) (h := (by wfx)) (l := [0, 1]) (k := 1) (k' := 1) (fallback := 7) (k_eq := (by decide +kernel)) (not_mem := (by decide +kernel)) (mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 4): compare, t = balanceL! panic literal (root 5, right child with size field 0): inserting 0 panics and returns leaf, so getKeyD gives the fallback 7
theorem w9c3_198 : ¬ drop0% Std.DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 4 :=
  fun h => by
  have := h (t := (⟨.inner 1 5 () .leaf (.inner 0 9 () .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Unit) compare)) (l := [0]) (k := 0) (k' := 0) (fallback := 7) (k_eq := (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 4): compare, t = balanceL! panic literal (root 5, right child with size field 0): inserting 0 panics and returns leaf, so getKeyD gives the fallback 7
theorem w9c3_199 : ¬ drop0% Std.TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 4 :=
  fun h => by
  have := h (t := (⟨⟨.inner 1 5 () .leaf (.inner 0 9 () .leaf .leaf)⟩⟩ : TreeMap.Raw Nat Unit compare)) (l := [0]) (k := 0) (k' := 0) (fallback := 7) (k_eq := (by decide +kernel)) (not_mem := (by decide +kernel)) (distinct := (by decide +kernel)) (mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 3): cmpN (near-equality, not transitive), t = ∅, l = [2, 0], k = 0, k' = 1: the lookup for 1 meets 2 first
theorem w9c3_200 : ¬ drop0% Std.DTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 3 :=
  fun h => by
  have := h (t := (DTreeMap.ofList [] cmpN : DTreeMap Nat (fun _ => Unit) cmpN)) (l := [2, 0]) (k := 0) (k' := 1) (fallback := 7) (k_eq := (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 3): cmpN (near-equality, not transitive), t = ∅, l = [2, 0], k = 0, k' = 1: the lookup for 1 meets 2 first
theorem w9c3_201 : ¬ drop0% Std.DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 3 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] cmpN : DTreeMap.Raw Nat (fun _ => Unit) cmpN)) (h := (by wfx)) (l := [2, 0]) (k := 0) (k' := 1) (fallback := 7) (k_eq := (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 3): cmpN (near-equality, not transitive), t = ∅, l = [2, 0], k = 0, k' = 1: the lookup for 1 meets 2 first
theorem w9c3_202 : ¬ drop0% Std.TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 3 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [] cmpN : TreeMap.Raw Nat Unit cmpN)) (h := (by wfx)) (l := [2, 0]) (k := 0) (k' := 1) (fallback := 7) (k_eq := (by decide +kernel)) (not_mem := (by decide +kernel)) (distinct := (by decide +kernel)) (mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 3): cmpN (near-equality, not transitive), t = ∅, l = [2, 0], k = 0, k' = 1: the lookup for 1 meets 2 first
theorem w9c3_203 : ¬ drop0% Std.TreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 3 :=
  fun h => by
  have := h (t := (TreeMap.ofList [] cmpN : TreeMap Nat Unit cmpN)) (l := [2, 0]) (k := 0) (k' := 1) (fallback := 7) (k_eq := (by decide +kernel)) (not_mem := (by decide +kernel)) (distinct := (by decide +kernel)) (mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 9): compare, t = ∅, l = [0], k = 0, k' = 1: getKeyD 1 is the fallback 7
theorem w9c3_204 : ¬ drop0% Std.DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 9 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Unit) compare)) (h := (by wfx)) (l := [0]) (k := 0) (k' := 1) (fallback := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 9): compare, t = ∅, l = [0], k = 0, k' = 1: getKeyD 1 is the fallback 7
theorem w9c3_205 : ¬ drop0% Std.TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 9 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [] compare : TreeMap.Raw Nat Unit compare)) (h := (by wfx)) (l := [0]) (k := 0) (k' := 1) (fallback := 7) (not_mem := (by decide +kernel)) (distinct := (by decide +kernel)) (mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 10): cmpH (halves), t = {1}, l = [0], k = k' = 0: 0 is not inserted, getKeyD 0 = 1
theorem w9c3_206 : ¬ drop0% Std.DTreeMap.Internal.Impl.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 10 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord OH)) (t := ((DTreeMap.ofList [⟨1, ()⟩] compare : DTreeMap OH (fun _ => Unit) compare).inner : Impl OH (fun _ => Unit))) (h := (by wfx)) (l := [0]) (k := 0) (k' := 0) (fallback := 7) (k_beq := (by decide +kernel)) (by decide +kernel) (by simp)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 10): cmpH (halves), t = {1}, l = [0], k = k' = 0: 0 is not inserted, getKeyD 0 = 1
theorem w9c3_207 : ¬ drop0% Std.DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 10 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨1, ()⟩] cmpH : DTreeMap.Raw Nat (fun _ => Unit) cmpH)) (h := (by wfx)) (l := [0]) (k := 0) (k' := 0) (fallback := 7) (k_eq := (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem` (binder 10): cmpH (halves), t = {1}, l = [0], k = k' = 0: 0 is not inserted, getKeyD 0 = 1
theorem w9c3_208 : ¬ drop0% Std.TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem 10 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [(1, ())] cmpH : TreeMap.Raw Nat Unit cmpH)) (h := (by wfx)) (l := [0]) (k := 0) (k' := 0) (fallback := 7) (k_eq := (by decide +kernel)) (distinct := (by decide +kernel)) (mem := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.mem_insertMany_list` (binder 7): compare, t unordered (root 1, unreachable right child 0), l = [5], k = 0: the insertion rebalances and 0 becomes reachable
theorem w9c3_209 : ¬ drop0% Std.DTreeMap.Raw.Const.mem_insertMany_list 7 :=
  fun h => by
  have := h (t := (⟨.inner 2 1 1 .leaf (.inner 1 0 9 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (l := [(5, 5)]) (k := 0)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.mem_insertMany_list` (binder 7): compare, t unordered (root 1, unreachable right child 0), l = [5], k = 0: the insertion rebalances and 0 becomes reachable
theorem w9c3_210 : ¬ drop0% Std.DTreeMap.Raw.mem_insertMany_list 7 :=
  fun h => by
  have := h (t := (⟨.inner 2 1 1 .leaf (.inner 1 0 9 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (l := [⟨5, 5⟩]) (k := 0)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.mem_insertMany_list` (binder 7): compare, t unordered (root 1, unreachable right child 0), l = [5], k = 0: the insertion rebalances and 0 becomes reachable
theorem w9c3_211 : ¬ drop0% Std.TreeMap.Raw.mem_insertMany_list 7 :=
  fun h => by
  have := h (t := (⟨⟨.inner 2 1 1 .leaf (.inner 1 0 9 .leaf .leaf)⟩⟩ : TreeMap.Raw Nat Nat compare)) (l := [(5, 5)]) (k := 0)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.mem_insertMany_list` (binder 6): compare, t unordered (root 1, unreachable right child 0), l = [5], k = 0: the insertion rebalances and 0 becomes reachable
theorem w9c3_212 : ¬ drop0% Std.TreeSet.Raw.mem_insertMany_list 6 :=
  fun h => by
  have := h (t := (⟨⟨⟨.inner 2 1 () .leaf (.inner 1 0 () .leaf .leaf)⟩⟩⟩ : TreeSet.Raw Nat compare)) (l := [5]) (k := 0)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.mem_insertMany_list` (binder 6): compare with BEq always false: t = ∅, l = [0], k = 0: 0 is in the result but l "does not contain" 0
theorem w9c3_213 : ¬ drop0% Std.DTreeMap.Raw.Const.mem_insertMany_list 6 :=
  fun h => by
  letI : BEq Nat := ⟨fun _ _ => false⟩
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (l := [(0, 5)]) (k := 0)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.mem_insertMany_list` (binder 6): compare with BEq always false: t = ∅, l = [0], k = 0: 0 is in the result but l "does not contain" 0
theorem w9c3_214 : ¬ drop0% Std.DTreeMap.Raw.mem_insertMany_list 6 :=
  fun h => by
  letI : BEq Nat := ⟨fun _ _ => false⟩
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (l := [⟨0, 5⟩]) (k := 0)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.mem_insertMany_list` (binder 6): compare with BEq always false: t = ∅, l = [0], k = 0: 0 is in the result but l "does not contain" 0
theorem w9c3_215 : ¬ drop0% Std.TreeMap.Raw.mem_insertMany_list 6 :=
  fun h => by
  letI : BEq Nat := ⟨fun _ _ => false⟩
  have := h (t := (TreeMap.Raw.ofList [] compare : TreeMap.Raw Nat Nat compare)) (h := (by wfx)) (l := [(0, 5)]) (k := 0)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.mem_insertMany_list` (binder 5): compare with BEq always false: t = ∅, l = [0], k = 0: 0 is in the result but l "does not contain" 0
theorem w9c3_216 : ¬ drop0% Std.TreeSet.Raw.mem_insertMany_list 5 :=
  fun h => by
  letI : BEq Nat := ⟨fun _ _ => false⟩
  have := h (t := (TreeSet.Raw.ofList [] compare : TreeSet.Raw Nat compare)) (h := (by wfx)) (l := [0]) (k := 0)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.mem_insertMany_list` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: 2 ∈ t, but inserting 0 rebalances and 2 is no longer found
theorem w9c3_217 : ¬ drop0% Std.DTreeMap.Const.mem_insertMany_list 4 :=
  fun h => by
  have := h (t := (DTreeMap.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 3⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (l := [(0, 20)]) (k := 2)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.mem_insertMany_list` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: 2 ∈ t, but inserting 0 rebalances and 2 is no longer found
theorem w9c3_218 : ¬ drop0% Std.DTreeMap.Raw.Const.mem_insertMany_list 4 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 3⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (h := (by wfx)) (l := [(0, 20)]) (k := 2)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.mem_insertMany_list` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: 2 ∈ t, but inserting 0 rebalances and 2 is no longer found
theorem w9c3_219 : ¬ drop0% Std.DTreeMap.Raw.mem_insertMany_list 4 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 3⟩] cmpT : DTreeMap.Raw Nat (fun _ => Nat) cmpT)) (h := (by wfx)) (l := [⟨0, 20⟩]) (k := 2)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.mem_insertMany_list` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: 2 ∈ t, but inserting 0 rebalances and 2 is no longer found
theorem w9c3_220 : ¬ drop0% Std.DTreeMap.mem_insertMany_list 4 :=
  fun h => by
  have := h (t := (DTreeMap.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 3⟩] cmpT : DTreeMap Nat (fun _ => Nat) cmpT)) (l := [⟨0, 20⟩]) (k := 2)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.mem_insertMany_list` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: 2 ∈ t, but inserting 0 rebalances and 2 is no longer found
theorem w9c3_221 : ¬ drop0% Std.TreeMap.Raw.mem_insertMany_list 4 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [(0, 0), (1, 1), (2, 2), (3, 3)] cmpT : TreeMap.Raw Nat Nat cmpT)) (h := (by wfx)) (l := [(0, 20)]) (k := 2)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.mem_insertMany_list` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: 2 ∈ t, but inserting 0 rebalances and 2 is no longer found
theorem w9c3_222 : ¬ drop0% Std.TreeMap.mem_insertMany_list 4 :=
  fun h => by
  have := h (t := (TreeMap.ofList [(0, 0), (1, 1), (2, 2), (3, 3)] cmpT : TreeMap Nat Nat cmpT)) (l := [(0, 20)]) (k := 2)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.mem_insertMany_list` (binder 3): cmpT: t = {0,1,2,3}, l = [0], k = 2: 2 ∈ t, but inserting 0 rebalances and 2 is no longer found
theorem w9c3_223 : ¬ drop0% Std.TreeSet.Raw.mem_insertMany_list 3 :=
  fun h => by
  have := h (t := (TreeSet.Raw.ofList [0, 1, 2, 3] cmpT : TreeSet.Raw Nat cmpT)) (h := (by wfx)) (l := [0]) (k := 2)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.mem_insertMany_list` (binder 3): cmpT: t = {0,1,2,3}, l = [0], k = 2: 2 ∈ t, but inserting 0 rebalances and 2 is no longer found
theorem w9c3_224 : ¬ drop0% Std.TreeSet.mem_insertMany_list 3 :=
  fun h => by
  have := h (t := (TreeSet.ofList [0, 1, 2, 3] cmpT : TreeSet Nat cmpT)) (l := [0]) (k := 2)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.Const.mem_insertMany_list` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: 2 ∈ t, but inserting 0 rebalances and 2 is no longer found
theorem w9c3_225 : ¬ drop0% Std.DTreeMap.Internal.Impl.Const.mem_insertMany_list 4 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord OT)) (t := ((DTreeMap.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 3⟩] compare : DTreeMap OT (fun _ => Nat) compare).inner : Impl OT (fun _ => Nat))) (h := (by wfx)) (l := [(0, 20)]) (k := 2)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.mem_insertMany_list` (binder 4): cmpT: t = {0,1,2,3}, l = [0], k = 2: 2 ∈ t, but inserting 0 rebalances and 2 is no longer found
theorem w9c3_226 : ¬ drop0% Std.DTreeMap.Internal.Impl.mem_insertMany_list 4 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord OT)) (t := ((DTreeMap.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 3⟩] compare : DTreeMap OT (fun _ => Nat) compare).inner : Impl OT (fun _ => Nat))) (h := (by wfx)) (l := [⟨0, 20⟩]) (k := 2)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.mem_of_mem_insert` (binder 9): compare, t = ∅, k = 1, a = 0: 0 ∉ t
theorem w9c3_227 : ¬ drop0% Std.DTreeMap.Internal.Impl.mem_of_mem_insert 9 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord Nat)) (t := ((DTreeMap.ofList [] compare : DTreeMap Nat (fun _ => Nat) compare).inner : Impl Nat (fun _ => Nat))) (h := (by wfx)) (k := 1) (a := 0) (v := 5) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.mem_of_mem_insert` (binder 7): compare, t = ∅, k = 1, a = 0: 0 ∉ t
theorem w9c3_228 : ¬ drop0% Std.TreeSet.Raw.mem_of_mem_insert 7 :=
  fun h => by
  have := h (t := (TreeSet.Raw.ofList [] compare : TreeSet.Raw Nat compare)) (h := (by wfx)) (k := 1) (a := 0) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.mem_of_mem_insert` (binder 9): compare, t = ∅, k = 1, a = 0: 0 ∉ t
theorem w9c3_229 : ¬ drop0% Std.DTreeMap.Raw.mem_of_mem_insert 9 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 1) (a := 0) (v := 5) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.mem_of_mem_insert` (binder 9): compare, t = ∅, k = 1, a = 0: 0 ∉ t
theorem w9c3_230 : ¬ drop0% Std.TreeMap.Raw.mem_of_mem_insert 9 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [] compare : TreeMap.Raw Nat Nat compare)) (h := (by wfx)) (k := 1) (a := 0) (v := 5) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.mem_of_mem_insert` (binder 5): compare, t unordered (root 1, unreachable right child 0), insert 5: the rebalance makes 0 reachable
theorem w9c3_231 : ¬ drop0% Std.DTreeMap.Raw.mem_of_mem_insert 5 :=
  fun h => by
  have := h (t := (⟨.inner 2 1 1 .leaf (.inner 1 0 9 .leaf .leaf)⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (k := 5) (a := 0) (v := 5) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.mem_of_mem_insert` (binder 5): compare, t unordered (root 1, unreachable right child 0), insert 5: the rebalance makes 0 reachable
theorem w9c3_232 : ¬ drop0% Std.TreeMap.Raw.mem_of_mem_insert 5 :=
  fun h => by
  have := h (t := (⟨⟨.inner 2 1 1 .leaf (.inner 1 0 9 .leaf .leaf)⟩⟩ : TreeMap.Raw Nat Nat compare)) (k := 5) (a := 0) (v := 5) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.mem_of_mem_insert` (binder 4): compare, t unordered (root 1, unreachable right child 0), insert 5: the rebalance makes 0 reachable
theorem w9c3_233 : ¬ drop0% Std.TreeSet.Raw.mem_of_mem_insert 4 :=
  fun h => by
  have := h (t := (⟨⟨⟨.inner 2 1 () .leaf (.inner 1 0 () .leaf .leaf)⟩⟩⟩ : TreeSet.Raw Nat compare)) (k := 5) (a := 0) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.mem_of_mem_insert` (binder 4): cmp01 (cmp 0 1 = eq only one way, not oriented), t = ∅, k = 1, a = 0: 0 is found in {1} but cmp 1 0 ≠ eq
theorem w9c3_234 : ¬ drop0% Std.DTreeMap.Raw.mem_of_mem_insert 4 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] cmp01 : DTreeMap.Raw Nat (fun _ => Nat) cmp01)) (h := (by wfx)) (k := 1) (a := 0) (v := 5) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.mem_of_mem_insert` (binder 4): cmp01 (cmp 0 1 = eq only one way, not oriented), t = ∅, k = 1, a = 0: 0 is found in {1} but cmp 1 0 ≠ eq
theorem w9c3_235 : ¬ drop0% Std.DTreeMap.mem_of_mem_insert 4 :=
  fun h => by
  have := h (t := (DTreeMap.ofList [] cmp01 : DTreeMap Nat (fun _ => Nat) cmp01)) (k := 1) (a := 0) (v := 5) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.mem_of_mem_insert` (binder 4): cmp01 (cmp 0 1 = eq only one way, not oriented), t = ∅, k = 1, a = 0: 0 is found in {1} but cmp 1 0 ≠ eq
theorem w9c3_236 : ¬ drop0% Std.TreeMap.Raw.mem_of_mem_insert 4 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [] cmp01 : TreeMap.Raw Nat Nat cmp01)) (h := (by wfx)) (k := 1) (a := 0) (v := 5) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.mem_of_mem_insert` (binder 4): cmp01 (cmp 0 1 = eq only one way, not oriented), t = ∅, k = 1, a = 0: 0 is found in {1} but cmp 1 0 ≠ eq
theorem w9c3_237 : ¬ drop0% Std.TreeMap.mem_of_mem_insert 4 :=
  fun h => by
  have := h (t := (TreeMap.ofList [] cmp01 : TreeMap Nat Nat cmp01)) (k := 1) (a := 0) (v := 5) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.mem_of_mem_insert` (binder 3): cmp01 (cmp 0 1 = eq only one way, not oriented), t = ∅, k = 1, a = 0: 0 is found in {1} but cmp 1 0 ≠ eq
theorem w9c3_238 : ¬ drop0% Std.TreeSet.Raw.mem_of_mem_insert 3 :=
  fun h => by
  have := h (t := (TreeSet.Raw.ofList [] cmp01 : TreeSet.Raw Nat cmp01)) (h := (by wfx)) (k := 1) (a := 0) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.mem_of_mem_insert` (binder 3): cmp01 (cmp 0 1 = eq only one way, not oriented), t = ∅, k = 1, a = 0: 0 is found in {1} but cmp 1 0 ≠ eq
theorem w9c3_239 : ¬ drop0% Std.TreeSet.mem_of_mem_insert 3 :=
  fun h => by
  have := h (t := (TreeSet.ofList [] cmp01 : TreeSet Nat cmp01)) (k := 1) (a := 0) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.mem_of_mem_insert` (binder 4): cmp01 (cmp 0 1 = eq only one way, not oriented), t = ∅, k = 1, a = 0: 0 is found in {1} but cmp 1 0 ≠ eq
theorem w9c3_240 : ¬ drop0% Std.DTreeMap.Internal.Impl.mem_of_mem_insert 4 :=
  fun h => by
  have := h (instOrd := ⟨cmp01⟩) (t := (.leaf : Impl Nat (fun _ => Nat))) (h := (by wfx)) (k := 1) (a := 0) (v := 5) (by decide +kernel) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.mem_of_mem_insert` (binder 10): compare, t = ∅, k = a = 0: 0 ∈ t.insert 0 but 0 ∉ t
theorem w9c3_241 : ¬ drop0% Std.DTreeMap.Raw.mem_of_mem_insert 10 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (a := 0) (v := 5) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.mem_of_mem_insert` (binder 10): compare, t = ∅, k = a = 0: 0 ∈ t.insert 0 but 0 ∉ t
theorem w9c3_242 : ¬ drop0% Std.TreeMap.Raw.mem_of_mem_insert 10 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [] compare : TreeMap.Raw Nat Nat compare)) (h := (by wfx)) (k := 0) (a := 0) (v := 5) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.TreeSet.Raw.mem_of_mem_insert` (binder 8): compare, t = ∅, k = a = 0: 0 ∈ t.insert 0 but 0 ∉ t
theorem w9c3_243 : ¬ drop0% Std.TreeSet.Raw.mem_of_mem_insert 8 :=
  fun h => by
  have := h (t := (TreeSet.Raw.ofList [] compare : TreeSet.Raw Nat compare)) (h := (by wfx)) (k := 0) (a := 0) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Internal.Impl.mem_of_mem_insert` (binder 10): compare, t = ∅, k = a = 0: 0 ∈ t.insert 0 but 0 ∉ t
theorem w9c3_244 : ¬ drop0% Std.DTreeMap.Internal.Impl.mem_of_mem_insert 10 :=
  fun h => by
  have := h (instOrd := (inferInstance : Ord Nat)) (t := ((DTreeMap.ofList [] compare : DTreeMap Nat (fun _ => Nat) compare).inner : Impl Nat (fun _ => Nat))) (h := (by wfx)) (k := 0) (a := 0) (v := 5) (by decide +kernel)
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.size_alter_eq_add_one` (binder 10): compare, t = ∅, k = 0, f = none: size stays 0
theorem w9c3_245 : ¬ drop0% Std.DTreeMap.Raw.size_alter_eq_add_one 10 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (f := (fun _ => none)) (h₁ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.size_alter_eq_add_one` (binder 9): compare, t = ∅, k = 0, f = none: size stays 0
theorem w9c3_246 : ¬ drop0% Std.DTreeMap.Raw.Const.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (f := (fun _ => none)) (h₁ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.size_alter_eq_add_one` (binder 9): compare, t = ∅, k = 0, f = none: size stays 0
theorem w9c3_247 : ¬ drop0% Std.TreeMap.Raw.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [] compare : TreeMap.Raw Nat Nat compare)) (h := (by wfx)) (k := 0) (f := (fun _ => none)) (h₁ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.size_alter_eq_add_one` (binder 5): compare, t ordered with keys 1 (root) and 0 but root size field 0, k = 5, f = some 7: alter rebuilds the path with balance, which recomputes the size field (2 or 3), not 0
theorem w9c3_248 : ¬ drop0% Std.DTreeMap.Raw.Const.size_alter_eq_add_one 5 :=
  fun h => by
  have := h (t := (⟨.inner 0 1 1 (.inner 1 0 0 .leaf .leaf) .leaf⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (k := 5) (f := (fun _ => some 7)) (h₁ := (by decide +kernel)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.size_alter_eq_add_one` (binder 6): compare, t ordered with keys 1 (root) and 0 but root size field 0, k = 5, f = some 7: alter rebuilds the path with balance, which recomputes the size field (2 or 3), not 0
theorem w9c3_249 : ¬ drop0% Std.DTreeMap.Raw.size_alter_eq_add_one 6 :=
  fun h => by
  have := h (t := (⟨.inner 0 1 1 (.inner 1 0 0 .leaf .leaf) .leaf⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (k := 5) (f := (fun _ => some 7)) (h₁ := (by decide +kernel)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.size_alter_eq_add_one` (binder 5): compare, t ordered with keys 1 (root) and 0 but root size field 0, k = 5, f = some 7: alter rebuilds the path with balance, which recomputes the size field (2 or 3), not 0
theorem w9c3_250 : ¬ drop0% Std.TreeMap.Raw.size_alter_eq_add_one 5 :=
  fun h => by
  have := h (t := (⟨⟨.inner 0 1 1 (.inner 1 0 0 .leaf .leaf) .leaf⟩⟩ : TreeMap.Raw Nat Nat compare)) (k := 5) (f := (fun _ => some 7)) (h₁ := (by decide +kernel)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.size_alter_eq_add_one` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_251 : drop% Std.DTreeMap.Const.size_alter_eq_add_one 4 :=
  by w93a

-- `Std.DTreeMap.Raw.Const.size_alter_eq_add_one` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_252 : drop% Std.DTreeMap.Raw.Const.size_alter_eq_add_one 4 :=
  by w93a

-- `Std.DTreeMap.Raw.size_alter_eq_add_one` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_253 : drop% Std.DTreeMap.Raw.size_alter_eq_add_one 4 :=
  by w93a

-- `Std.DTreeMap.size_alter_eq_add_one` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_254 : drop% Std.DTreeMap.size_alter_eq_add_one 4 :=
  by w93a

-- `Std.TreeMap.Raw.size_alter_eq_add_one` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_255 : drop% Std.TreeMap.Raw.size_alter_eq_add_one 4 :=
  by w93a

-- `Std.TreeMap.size_alter_eq_add_one` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_256 : drop% Std.TreeMap.size_alter_eq_add_one 4 :=
  by w93a

-- `Std.DTreeMap.Internal.Impl.Const.size_alter_eq_add_one` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_257 : drop% Std.DTreeMap.Internal.Impl.Const.size_alter_eq_add_one 4 :=
  by w93a

-- `Std.DTreeMap.Internal.Impl.size_alter_eq_add_one` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_258 : drop% Std.DTreeMap.Internal.Impl.size_alter_eq_add_one 4 :=
  by w93a

-- `Std.DTreeMap.Raw.Const.size_alter_eq_add_one` (binder 8): compare, t = {0}, k = 0, f = some 1: size stays 1
theorem w9c3_259 : ¬ drop0% Std.DTreeMap.Raw.Const.size_alter_eq_add_one 8 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨0, 0⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (f := (fun _ => some 1)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.size_alter_eq_add_one` (binder 9): compare, t = {0}, k = 0, f = some 1: size stays 1
theorem w9c3_260 : ¬ drop0% Std.DTreeMap.Raw.size_alter_eq_add_one 9 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨0, 0⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (f := (fun _ => some 1)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.size_alter_eq_add_one` (binder 8): compare, t = {0}, k = 0, f = some 1: size stays 1
theorem w9c3_261 : ¬ drop0% Std.TreeMap.Raw.size_alter_eq_add_one 8 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [(0, 0)] compare : TreeMap.Raw Nat Nat compare)) (h := (by wfx)) (k := 0) (f := (fun _ => some 1)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.size_alter_eq_self_of_mem` (binder 10): compare, t = {0}, k = 0, f = none: size becomes 0
theorem w9c3_262 : ¬ drop0% Std.DTreeMap.Raw.size_alter_eq_self_of_mem 10 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨0, 0⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (f := (fun _ => none)) (h₁ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.size_alter_eq_self_of_mem` (binder 9): compare, t = {0}, k = 0, f = none: size becomes 0
theorem w9c3_263 : ¬ drop0% Std.DTreeMap.Raw.Const.size_alter_eq_self_of_mem 9 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨0, 0⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (f := (fun _ => none)) (h₁ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.size_alter_eq_self_of_mem` (binder 9): compare, t = {0}, k = 0, f = none: size becomes 0
theorem w9c3_264 : ¬ drop0% Std.TreeMap.Raw.size_alter_eq_self_of_mem 9 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [(0, 0)] compare : TreeMap.Raw Nat Nat compare)) (h := (by wfx)) (k := 0) (f := (fun _ => none)) (h₁ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.size_alter_eq_self_of_mem` (binder 8): compare, t = ∅, k = 0, f = some 1: size becomes 1
theorem w9c3_265 : ¬ drop0% Std.DTreeMap.Raw.Const.size_alter_eq_self_of_mem 8 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (f := (fun _ => some 1)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.size_alter_eq_self_of_mem` (binder 9): compare, t = ∅, k = 0, f = some 1: size becomes 1
theorem w9c3_266 : ¬ drop0% Std.DTreeMap.Raw.size_alter_eq_self_of_mem 9 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (f := (fun _ => some 1)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.size_alter_eq_self_of_mem` (binder 8): compare, t = ∅, k = 0, f = some 1: size becomes 1
theorem w9c3_267 : ¬ drop0% Std.TreeMap.Raw.size_alter_eq_self_of_mem 8 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [] compare : TreeMap.Raw Nat Nat compare)) (h := (by wfx)) (k := 0) (f := (fun _ => some 1)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.size_alter_eq_self_of_mem` (binder 5): compare, t ordered with keys 1 (root) and 0 but root size field 0, k = 0, f = some 7: alter rebuilds the path with balance, which recomputes the size field (2 or 3), not 0
theorem w9c3_268 : ¬ drop0% Std.DTreeMap.Raw.Const.size_alter_eq_self_of_mem 5 :=
  fun h => by
  have := h (t := (⟨.inner 0 1 1 (.inner 1 0 0 .leaf .leaf) .leaf⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (k := 0) (f := (fun _ => some 7)) (h₁ := (by decide +kernel)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.size_alter_eq_self_of_mem` (binder 6): compare, t ordered with keys 1 (root) and 0 but root size field 0, k = 0, f = some 7: alter rebuilds the path with balance, which recomputes the size field (2 or 3), not 0
theorem w9c3_269 : ¬ drop0% Std.DTreeMap.Raw.size_alter_eq_self_of_mem 6 :=
  fun h => by
  have := h (t := (⟨.inner 0 1 1 (.inner 1 0 0 .leaf .leaf) .leaf⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (k := 0) (f := (fun _ => some 7)) (h₁ := (by decide +kernel)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.size_alter_eq_self_of_mem` (binder 5): compare, t ordered with keys 1 (root) and 0 but root size field 0, k = 0, f = some 7: alter rebuilds the path with balance, which recomputes the size field (2 or 3), not 0
theorem w9c3_270 : ¬ drop0% Std.TreeMap.Raw.size_alter_eq_self_of_mem 5 :=
  fun h => by
  have := h (t := (⟨⟨.inner 0 1 1 (.inner 1 0 0 .leaf .leaf) .leaf⟩⟩ : TreeMap.Raw Nat Nat compare)) (k := 0) (f := (fun _ => some 7)) (h₁ := (by decide +kernel)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.size_alter_eq_self_of_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_271 : drop% Std.DTreeMap.Const.size_alter_eq_self_of_mem 4 :=
  by w93a

-- `Std.DTreeMap.Raw.Const.size_alter_eq_self_of_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_272 : drop% Std.DTreeMap.Raw.Const.size_alter_eq_self_of_mem 4 :=
  by w93a

-- `Std.DTreeMap.Raw.size_alter_eq_self_of_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_273 : drop% Std.DTreeMap.Raw.size_alter_eq_self_of_mem 4 :=
  by w93a

-- `Std.DTreeMap.size_alter_eq_self_of_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_274 : drop% Std.DTreeMap.size_alter_eq_self_of_mem 4 :=
  by w93a

-- `Std.TreeMap.Raw.size_alter_eq_self_of_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_275 : drop% Std.TreeMap.Raw.size_alter_eq_self_of_mem 4 :=
  by w93a

-- `Std.TreeMap.size_alter_eq_self_of_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_276 : drop% Std.TreeMap.size_alter_eq_self_of_mem 4 :=
  by w93a

-- `Std.DTreeMap.Internal.Impl.Const.size_alter_eq_self_of_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_277 : drop% Std.DTreeMap.Internal.Impl.Const.size_alter_eq_self_of_mem 4 :=
  by w93a

-- `Std.DTreeMap.Internal.Impl.size_alter_eq_self_of_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_278 : drop% Std.DTreeMap.Internal.Impl.size_alter_eq_self_of_mem 4 :=
  by w93a

-- `Std.DTreeMap.Raw.size_alter_eq_self_of_not_mem` (binder 10): compare, t = ∅, k = 0, f = some 1: size becomes 1
theorem w9c3_279 : ¬ drop0% Std.DTreeMap.Raw.size_alter_eq_self_of_not_mem 10 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (f := (fun _ => some 1)) (h₁ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.size_alter_eq_self_of_not_mem` (binder 9): compare, t = ∅, k = 0, f = some 1: size becomes 1
theorem w9c3_280 : ¬ drop0% Std.DTreeMap.Raw.Const.size_alter_eq_self_of_not_mem 9 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (f := (fun _ => some 1)) (h₁ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.size_alter_eq_self_of_not_mem` (binder 9): compare, t = ∅, k = 0, f = some 1: size becomes 1
theorem w9c3_281 : ¬ drop0% Std.TreeMap.Raw.size_alter_eq_self_of_not_mem 9 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [] compare : TreeMap.Raw Nat Nat compare)) (h := (by wfx)) (k := 0) (f := (fun _ => some 1)) (h₁ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.Const.size_alter_eq_self_of_not_mem` (binder 5): compare, t ordered with keys 1 (root) and 0 but root size field 0, k = 5, f = none: alter rebuilds the path with balance, which recomputes the size field (2 or 3), not 0
theorem w9c3_282 : ¬ drop0% Std.DTreeMap.Raw.Const.size_alter_eq_self_of_not_mem 5 :=
  fun h => by
  have := h (t := (⟨.inner 0 1 1 (.inner 1 0 0 .leaf .leaf) .leaf⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (k := 5) (f := (fun _ => none)) (h₁ := (by decide +kernel)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.size_alter_eq_self_of_not_mem` (binder 6): compare, t ordered with keys 1 (root) and 0 but root size field 0, k = 5, f = none: alter rebuilds the path with balance, which recomputes the size field (2 or 3), not 0
theorem w9c3_283 : ¬ drop0% Std.DTreeMap.Raw.size_alter_eq_self_of_not_mem 6 :=
  fun h => by
  have := h (t := (⟨.inner 0 1 1 (.inner 1 0 0 .leaf .leaf) .leaf⟩ : DTreeMap.Raw Nat (fun _ => Nat) compare)) (k := 5) (f := (fun _ => none)) (h₁ := (by decide +kernel)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.size_alter_eq_self_of_not_mem` (binder 5): compare, t ordered with keys 1 (root) and 0 but root size field 0, k = 5, f = none: alter rebuilds the path with balance, which recomputes the size field (2 or 3), not 0
theorem w9c3_284 : ¬ drop0% Std.TreeMap.Raw.size_alter_eq_self_of_not_mem 5 :=
  fun h => by
  have := h (t := (⟨⟨.inner 0 1 1 (.inner 1 0 0 .leaf .leaf) .leaf⟩⟩ : TreeMap.Raw Nat Nat compare)) (k := 5) (f := (fun _ => none)) (h₁ := (by decide +kernel)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Const.size_alter_eq_self_of_not_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_285 : drop% Std.DTreeMap.Const.size_alter_eq_self_of_not_mem 4 :=
  by w93a

-- `Std.DTreeMap.Raw.Const.size_alter_eq_self_of_not_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_286 : drop% Std.DTreeMap.Raw.Const.size_alter_eq_self_of_not_mem 4 :=
  by w93a

-- `Std.DTreeMap.Raw.size_alter_eq_self_of_not_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_287 : drop% Std.DTreeMap.Raw.size_alter_eq_self_of_not_mem 4 :=
  by w93a

-- `Std.DTreeMap.size_alter_eq_self_of_not_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_288 : drop% Std.DTreeMap.size_alter_eq_self_of_not_mem 4 :=
  by w93a

-- `Std.TreeMap.Raw.size_alter_eq_self_of_not_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_289 : drop% Std.TreeMap.Raw.size_alter_eq_self_of_not_mem 4 :=
  by w93a

-- `Std.TreeMap.size_alter_eq_self_of_not_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_290 : drop% Std.TreeMap.size_alter_eq_self_of_not_mem 4 :=
  by w93a

-- `Std.DTreeMap.Internal.Impl.Const.size_alter_eq_self_of_not_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_291 : drop% Std.DTreeMap.Internal.Impl.Const.size_alter_eq_self_of_not_mem 4 :=
  by w93a

-- `Std.DTreeMap.Internal.Impl.size_alter_eq_self_of_not_mem` (binder 4): alter follows the search path of contains/get?: a missing key with f giving some adds one node, a missing key with f giving none changes nothing, a present key with f giving some only replaces the value; balance and glue keep size fields exact on balanced trees, for any compare
theorem w9c3_292 : drop% Std.DTreeMap.Internal.Impl.size_alter_eq_self_of_not_mem 4 :=
  by w93a

-- `Std.DTreeMap.Raw.Const.size_alter_eq_self_of_not_mem` (binder 8): compare, t = {0}, k = 0, f = none: size becomes 0
theorem w9c3_293 : ¬ drop0% Std.DTreeMap.Raw.Const.size_alter_eq_self_of_not_mem 8 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨0, 0⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (f := (fun _ => none)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.DTreeMap.Raw.size_alter_eq_self_of_not_mem` (binder 9): compare, t = {0}, k = 0, f = none: size becomes 0
theorem w9c3_294 : ¬ drop0% Std.DTreeMap.Raw.size_alter_eq_self_of_not_mem 9 :=
  fun h => by
  have := h (t := (DTreeMap.Raw.ofList [⟨0, 0⟩] compare : DTreeMap.Raw Nat (fun _ => Nat) compare)) (h := (by wfx)) (k := 0) (f := (fun _ => none)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)

-- `Std.TreeMap.Raw.size_alter_eq_self_of_not_mem` (binder 8): compare, t = {0}, k = 0, f = none: size becomes 0
theorem w9c3_295 : ¬ drop0% Std.TreeMap.Raw.size_alter_eq_self_of_not_mem 8 :=
  fun h => by
  have := h (t := (TreeMap.Raw.ofList [(0, 0)] compare : TreeMap.Raw Nat Nat compare)) (h := (by wfx)) (k := 0) (f := (fun _ => none)) (h₂ := (by decide +kernel))
  exact absurd this (by decide +kernel)
