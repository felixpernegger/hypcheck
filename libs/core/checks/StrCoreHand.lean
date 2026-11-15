import Lean

/-!
Hand pass `StrCore` (hand9): 117 open hypotheses of the remaining `Init.Data.String` modules
(Lemmas.Order, Lemmas.Pattern.Find.*, Lemmas.Pattern.Split.*, Lemmas.Iterate, Basic, Termination,
Lemmas.Splits, Lemmas.Lossy, Defs, Lemmas.Basic, Decode, Modify, Lemmas.FindPos, Lemmas.Iter).
For hypothesis `hᵢ` of theorem `T` this file proves `¬T'` (`drop0% T i`), for a dependent one
`¬∀ indep, Hᵢ` (`indep0% T i`), or, for the removable ones, `∀ indep, Hᵢ` (`indep% T i`).

110 necessary, 4 removable (all dependent and derivable), 3 opaque (not proved here, listed in
`runs/hand9/StrCore_opaque.jsonl`).

Removable: in `String.Slice.cast_pos` each of the two validity hypotheses follows from the other and
`s.copy = t.copy` (`isValidForSlice_iff_exists_append`: validity only depends on the copy);
in `String.Pos.next_le_of_lt`/`String.Slice.Pos.next_le_of_lt` the bound `p ≠ endPos` follows
from `p < q` (`ne_endPos_of_lt`).

Reusable counterexamples (section "Models"):
* `LS s`: a searcher that may skip to itself or yield the whole-slice match, and whose `step` skips;
  not `Finite` (`LS.not_finite`), and no loop over it is well-founded (`LS.not_wf`), so every
  `IteratorLoop` on it is lawful (`LS.lawful` for `LS.loop`); `LS.sch` searches `'a'` with it.
* `LS.loop`: returns `init` at types with at most two elements (`Two`, true for `Bool`, false for
  `Option` of the positions of `"a"`) and otherwise applies the body once to the whole-slice match;
  so `find?` and `contains` disagree (`find_LS`, `contains_LS`).
* `triLoop i`: the same type test in front of a given loop `i` (not lawful); `bogusLoop`: always
  returns `init`. With the library's `'a'` searcher: `find_tri`, `contains_tri`, `find_bogus`,
  `contains_bogus`, `posFind_bogus`.
* `NatM` (bind adds one, copied from `SliceHand`) and `forIn_sA_natM`: `forIn` over `"a"` binds twice
  (the iterator loop wraps the body in one more bind), `List.forIn` once.
Evaluation: `decide`/`decide +kernel` on byte arrays, `fromUTF8Lossy`, positions and slices; `find?`
on the library patterns via the library's own iff lemmas with the true split; char splitting via
`toList_split_char`.

Run with the lean4 repo's stage1 binary: `lean checks/StrCoreHand.lean`.
-/


set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option warn.classDefReducibility false

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
  let us := ci.levelParams.map fun _ => levelZero
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
  let us := ci.levelParams.map fun _ => levelZero
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


namespace StrCoreHand

/-! ## Models -/
set_option warn.classDefReducibility false
open String (Slice)
open String.Slice.Pattern Std Std.Iterators

theorem acc_not_self {α : Sort _} {r : α → α → Prop} {x : α} (h : Acc r x) : ¬ r x x := by
  induction h with | intro x _ ih => exact fun hxx => ih x hxx hxx

/-- Looping searcher: a state may skip to itself or yield a match over the whole slice; step skips. -/
structure LS (s : Slice) where
  u : Unit

instance LS.iter (s : Slice) : Iterator (LS s) Id (SearchStep s) where
  IsPlausibleStep it st := st = .skip it ∨ st = .yield it (.matched s.startPos s.endPos)
  step it := pure (.deflate ⟨.skip it, Or.inl rfl⟩)

theorem LS.not_finite (s : Slice) : ¬ Iterators.Finite (LS s) Id := fun hf =>
  acc_not_self (hf.wf.apply ⟨⟨()⟩⟩) ⟨.skip ⟨⟨()⟩⟩, rfl, Or.inl rfl⟩

theorem LS.not_wf {s : Slice} {γ : Type} (Pl : SearchStep s → γ → ForInStep γ → Prop) (c : γ) :
    ¬ IteratorLoop.WellFounded (LS s) Id Pl := fun wf =>
  acc_not_self (wf.apply (⟨⟨()⟩⟩, c)) (Or.inr ⟨Or.inl rfl, rfl⟩)

theorem LS.out {s : Slice} (it : IterM (α := LS s) Id (SearchStep s)) :
    it.IsPlausibleIndirectOutput (.matched s.startPos s.endPos) :=
  .direct ⟨it, Or.inr rfl⟩

/-- Property of a type with at most two elements (Bool, but not Option "a".toSlice.Pos). -/
def Two (γ : Type) : Prop := ∀ x y z : γ, x = y ∨ y = z ∨ x = z

theorem two_bool : Two Bool := by unfold Two; decide

/-- Loop for LS: at a type with at most two elements returns init, otherwise applies the body
once to the whole-slice match. Lawful, since no loop over LS is well-founded. -/
noncomputable def LS.loop (s : Slice) : IteratorLoop (LS s) Id Id where
  forIn _ γ _ it init f := open Classical in
    if Two γ then init else (f _ (LS.out it) init).run.val.value

theorem LS.loop_neg {s : Slice} {lift γ Pl it init f} (h : ¬ Two γ) :
    (LS.loop s).forIn lift γ Pl it init f = (f _ (LS.out it) init).run.val.value := if_neg h

theorem LS.loop_pos {s : Slice} {lift γ Pl it init f} (h : Two γ) :
    (LS.loop s).forIn lift γ Pl it init f = init := if_pos h

theorem LS.lawful (s : Slice) : @LawfulIteratorLoop _ (LS s) Id Id _ _ _ (LS.loop s) :=
  @LawfulIteratorLoop.mk _ (LS s) Id Id _ _ _ (LS.loop s) (fun _ _ _ _ init Pl wf _ => absurd wf (LS.not_wf Pl init))

/-- 'a' searched with LS. -/
def LS.sch : ToForwardSearcher 'a' LS := ⟨fun _ => ⟨⟨()⟩⟩⟩

/-- Every loop returns its initial value. -/
def bogusLoop {α β : Type} [Iterator α Id β] : IteratorLoop α Id Id := ⟨fun _ _ _ _ init _ => init⟩

/-- At a type with at most two elements returns init, otherwise runs i. -/
noncomputable def triLoop {α β : Type} [Iterator α Id β] (i : IteratorLoop α Id Id) : IteratorLoop α Id Id where
  forIn lift γ Pl it init f := open Classical in
    if Two γ then init else i.forIn lift γ Pl it init f

abbrev sA : Slice := "a".toSlice

theorem not_two_opt : ¬ Two (Option sA.Pos) := fun h => by
  rcases h none (some sA.startPos) (some sA.endPos) with h | h | h <;> revert h <;> decide

theorem find_LS : @String.Slice.find? Char LS (fun s => LS.iter s) (fun s => LS.loop s) sA 'a' LS.sch = some sA.startPos := by
  simp only [String.Slice.find?, Iter.findSome?, Iter.findSomeM?, ForIn.forIn, ForIn'.forIn', IteratorLoop.finiteForIn', LS.loop_neg not_two_opt]
  rfl

theorem contains_LS : @String.Slice.contains Char LS (fun s => LS.iter s) (fun s => LS.loop s) sA 'a' LS.sch = false := by
  simp only [String.Slice.contains, Iter.any, Iter.anyM, ForIn.forIn, ForIn'.forIn', IteratorLoop.finiteForIn', LS.loop_pos two_bool]
  rfl

theorem triLoop_neg {α β : Type} [Iterator α Id β] {i : IteratorLoop α Id Id} {lift γ Pl it init f} (h : ¬ Two γ) :
    (triLoop i).forIn lift γ Pl it init f = i.forIn lift γ Pl it init f := if_neg h

theorem triLoop_pos {α β : Type} [Iterator α Id β] {i : IteratorLoop α Id Id} {lift γ Pl it init f} (h : Two γ) :
    (triLoop i).forIn lift γ Pl it init f = init := if_pos h

abbrev σC := ToForwardSearcher.DefaultForwardSearcher (· == 'a')

theorem find_tri : @String.Slice.find? Char σC _ (fun _ => triLoop inferInstance) sA 'a' _ = some sA.startPos := by
  have : @String.Slice.find? Char σC _ (fun _ => triLoop inferInstance) sA 'a' _ = sA.find? 'a' := by
    simp only [String.Slice.find?, Iter.findSome?, Iter.findSomeM?, ForIn.forIn, ForIn'.forIn',
      IteratorLoop.finiteForIn', triLoop_neg not_two_opt]
  rw [this, String.Slice.find?_char_eq_some_iff]
  exact ⟨by decide, by decide, fun _ h => absurd h String.Slice.Pos.not_lt_startPos⟩

theorem contains_tri : @String.Slice.contains Char σC _ (fun _ => triLoop inferInstance) sA 'a' _ = false := by
  simp only [String.Slice.contains, Iter.any, Iter.anyM, ForIn.forIn, ForIn'.forIn',
    IteratorLoop.finiteForIn', triLoop_pos two_bool]
  rfl

theorem find_bogus : @String.Slice.find? Char σC _ (fun _ => bogusLoop) sA 'a' _ = none := rfl
theorem contains_bogus : @String.Slice.contains Char σC _ (fun _ => bogusLoop) sA 'a' _ = false := rfl
theorem posFind_bogus : @String.Slice.Pos.find? Char σC _ (fun _ => bogusLoop) sA sA.startPos 'a' _ = none := rfl

theorem matches_a : String.Slice.Pattern.Model.MatchesAt 'a' sA.startPos :=
  String.Slice.Pattern.Model.Char.matchesAt_iff.2 ⟨by decide, by decide⟩

/-- Non-lawful monad counting the outer binds (copied from SliceHand). -/
def NatM (_ : Type) : Type := Nat

instance : Monad NatM where
  pure _ := (0 : Nat)
  bind x _ := (show Nat from x) + 1
  map _ x := (show Nat from x)

/-- One unfolding of the default loop in NatM, for an iterator whose first step yields (from SliceHand). -/
theorem natM_forIn {α β : Type} [Iterator α Id β] {γ : Type} (Pl : β → γ → ForInStep γ → Prop)
    (it : IterM (α := α) Id β) (init : γ)
    (f : (b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → NatM (Subtype (Pl b c)))
    (wf : IteratorLoop.WellFounded α Id Pl) (it' : IterM (α := α) Id β) (out : β) (h)
    (hs : it.step.run.inflate = ⟨.yield it' out, h⟩) :
    (IteratorLoop.defaultImplementation : IteratorLoop α Id NatM).forIn
        (fun _ _ g c => g c.run) γ Pl it init f
      = (show Nat from (f out (.direct ⟨_, h⟩) init)) + 1 := by
  haveI : Nonempty γ := ⟨init⟩
  show IterM.DefaultConsumers.forIn' _ _ _ _ _ _ _ _ = _
  rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
  dsimp only
  split
  · rename_i heq; rw [hs] at heq; cases heq; rfl
  · rename_i heq; rw [hs] at heq; cases heq
  · rename_i heq; rw [hs] at heq; cases heq

def NatM.val {α : Type} (x : NatM α) : Nat := x

/-- forIn over "a" with a body returning pure: the default loop binds twice. -/
theorem forIn_sA_natM : (ForIn.forIn (m := NatM) sA () (fun _ _ => pure (ForInStep.yield ()))).val = 2 := by
  show NatM.val ((IteratorLoop.defaultImplementation : IteratorLoop _ Id NatM).forIn _ _ _ _ _ _) = _
  show NatM.val (IterM.DefaultConsumers.forIn' _ _ _ _ _ _ _ _) = _
  rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ IteratorLoop.wellFounded_of_finite)]
  dsimp only
  split
  · rfl
  · rename_i heq
    simp [String.Slice.chars, Iter.map, IterM.step_map, String.Slice.positions, String.Slice.positionsFrom] at heq
    simp [IterM.step, Iterator.step, Shrink.inflate_deflate, show sA.startPos ≠ sA.endPos by decide] at heq
    cases congrArg Subtype.val heq
  · rename_i heq
    simp [String.Slice.chars, Iter.map, IterM.step_map, String.Slice.positions, String.Slice.positionsFrom] at heq
    simp [IterM.step, Iterator.step, Shrink.inflate_deflate, show sA.startPos ≠ sA.endPos by decide] at heq
    cases congrArg Subtype.val heq


/-! ## UTF-8 validity, decoding, Basic/Decode/Defs (A) -/

-- `ByteArray.IsValidUTF8.push`, idx 1: b = [255] (invalid), c = a: [255, 97] is invalid
theorem ByteArray.IsValidUTF8.push.h1 : ¬ drop0% ByteArray.IsValidUTF8.push 1 := fun h => by
  have := @h (ByteArray.mk #[255]) 'a' (by decide); revert this; decide

-- `ByteArray.IsValidUTF8.push`, idx 3: b = [], c = é (utf8Size 2): pushing its low byte gives [233], invalid
theorem ByteArray.IsValidUTF8.push.h3 : ¬ drop0% ByteArray.IsValidUTF8.push 3 := fun h => by
  have := @h ByteArray.empty (by decide) 'é'; revert this; decide

-- `ByteArray.utf8Encode_get_utf8Decode?`, idx 1: dependent; b = [255] does not decode
theorem ByteArray.utf8Encode_get_utf8Decode?.h1 : ¬ indep0% ByteArray.utf8Encode_get_utf8Decode? 1 := fun h => by
  have := @h (ByteArray.mk #[255]); revert this; decide

-- `ByteArray.IsValidUTF8.isUTF8FirstByte_getElem_zero`, idx 1: b = [128]: a continuation byte is not a first byte
theorem ByteArray.IsValidUTF8.isUTF8FirstByte_getElem_zero.h1 : ¬ drop0% ByteArray.IsValidUTF8.isUTF8FirstByte_getElem_zero 1 := fun h => by
  have := @h (ByteArray.mk #[128]) (by decide); revert this; decide

-- `String.utf8EncodeChar_eq_singleton`, idx 1: c = é encodes to two bytes
theorem String.utf8EncodeChar_eq_singleton.h1 : ¬ drop0% String.utf8EncodeChar_eq_singleton 1 := fun h => by
  have := @h 'é'; revert this; decide

-- `ByteArray.exists_of_utf8DecodeChar?_eq_some`, idx 2: b = [], c = a: [] has no prefix [97]
theorem ByteArray.exists_of_utf8DecodeChar?_eq_some.h2 : ¬ drop0% ByteArray.exists_of_utf8DecodeChar?_eq_some 2 := fun h => by
  have ⟨l, hl⟩ := @h ByteArray.empty 'a'
  have := congrArg ByteArray.size hl
  have ha : 'a'.utf8Size = 1 := by decide
  simp at this; omega

-- `UInt8.utf8ByteSize_pos`, idx 1: dependent; c = 128 is not a UTF-8 first byte
theorem UInt8.utf8ByteSize_pos.h1 : ¬ indep0% UInt8.utf8ByteSize_pos 1 := fun h => by
  have := @h 128; revert this; decide

-- `ByteArray.IsValidUTF8.append`, idx 2: b = [255], b' = []
theorem ByteArray.IsValidUTF8.append.h2 : ¬ drop0% ByteArray.IsValidUTF8.append 2 := fun h => by
  have := @h (ByteArray.mk #[255]) ByteArray.empty (by decide); revert this; decide

-- `ByteArray.IsValidUTF8.append`, idx 3: b = [], b' = [255]
theorem ByteArray.IsValidUTF8.append.h3 : ¬ drop0% ByteArray.IsValidUTF8.append 3 := fun h => by
  have := @h ByteArray.empty (ByteArray.mk #[255]) (by decide); revert this; decide

-- `String.fromUTF8_eq_ofByteArray`, idx 1: dependent; a = [255] is not valid UTF-8
theorem String.fromUTF8_eq_ofByteArray.h1 : ¬ indep0% String.fromUTF8_eq_ofByteArray 1 := fun h => by
  have := @h (ByteArray.mk #[255]); revert this; decide

-- `String.utf8ByteSize_ofByteArray`, idx 1: dependent; b = [255] is not valid UTF-8
theorem String.utf8ByteSize_ofByteArray.h1 : ¬ indep0% String.utf8ByteSize_ofByteArray 1 := fun h => by
  have := @h (ByteArray.mk #[255]); revert this; decide

-- `String.fromUTF8Lossy_eq_of_isValidUTF8`, idx 1: dependent; b = [255] is not valid UTF-8
theorem String.fromUTF8Lossy_eq_of_isValidUTF8.h1 : ¬ indep0% String.fromUTF8Lossy_eq_of_isValidUTF8 1 := fun h => by
  have := @h (ByteArray.mk #[255]); revert this; decide

-- `String.Pos.Raw.IsValid.exists`, idx 2: s = é, p = 1: the prefix [0xC3] is not the encoding of any char list (not valid UTF-8)
theorem String.Pos.Raw.IsValid.exists.h2 : ¬ drop0% String.Pos.Raw.IsValid.exists 2 := fun h => by
  obtain ⟨m₁, m₂, h1, h2⟩ := @h "é" ⟨1⟩
  have := h1 ▸ ByteArray.isValidUTF8_utf8Encode (l := m₁)
  revert this; decide

-- `String.push_induction`, idx 2: motive = (· ≠ ""), s = "": push case holds, motive "" fails
theorem String.push_induction.h2 : ¬ drop0% String.push_induction 2 := fun h => by
  have := @h "" (fun s => s ≠ "") (fun b c _ => by simp); simp at this

-- `String.push_induction`, idx 3: motive = (· = ""), s = "a": empty case holds, motive "a" fails
theorem String.push_induction.h3 : ¬ drop0% String.push_induction 3 := fun h => by
  have := @h "a" (fun s => s = "") rfl; simp at this

/-! ## Lossy decoding, modification, slices, termination, splits (B) -/

-- `String.fromUTF8Lossy_append_of_utf8DecodeChar?_eq_none`, idx 4: l = [0xC3, 0x41], b = []: decoding fails at 0 but 0x41 is not a continuation byte; lossy gives "�A" not "�"
theorem String.fromUTF8Lossy_append_of_utf8DecodeChar?_eq_none.h4 : ¬ drop0% String.fromUTF8Lossy_append_of_utf8DecodeChar?_eq_none 4 := fun h => by
  have := @h (ByteArray.mk #[0xC3, 0x41]) ByteArray.empty (by decide) (by decide) (by decide)
  revert this; decide +kernel

-- `String.fromUTF8Lossy_append_of_utf8DecodeChar?_eq_none`, idx 5: l = [0xF0], b = [0x90, 0x41]: b starts with a continuation byte; lossy (l ++ b) = "�A" but "�" ++ lossy b = "��A"
theorem String.fromUTF8Lossy_append_of_utf8DecodeChar?_eq_none.h5 : ¬ drop0% String.fromUTF8Lossy_append_of_utf8DecodeChar?_eq_none 5 := fun h => by
  have := @h (ByteArray.mk #[0xF0]) (ByteArray.mk #[0x90, 0x41]) (by decide) (by decide) (by decide)
  revert this; decide +kernel

-- `String.fromUTF8Lossy_surrogate_append`, idx 5: x = 0xA0, y = 0x80, b = [0x80] (starts with a continuation byte): evaluates differently (decide +kernel)
theorem String.fromUTF8Lossy_surrogate_append.h5 : ¬ drop0% String.fromUTF8Lossy_surrogate_append 5 := fun h => by
  have := @h 0xA0 0x80 (ByteArray.mk #[0x80]) (by decide) (by decide)
  revert this; decide +kernel

-- `String.Pos.Raw.IsValid.set_of_le`, idx 5: s = "éa", p = byte 2, c = b, q = 1 (inside é): q invalid in "éb"
theorem String.Pos.Raw.IsValid.set_of_le.h5 : ¬ drop0% String.Pos.Raw.IsValid.set_of_le 5 := fun h => by
  have := @h "éa" ("éa".pos ⟨2⟩ (by decide)) 'b' (by decide) ⟨1⟩ (by decide)
  revert this; decide +kernel

-- `String.Pos.Raw.IsValid.modify_of_le`, idx 5: s = "éa", p = byte 2, f = id, q = 1 (inside é): q invalid in "éa"
theorem String.Pos.Raw.IsValid.modify_of_le.h5 : ¬ drop0% String.Pos.Raw.IsValid.modify_of_le 5 := fun h => by
  have := @h "éa" ("éa".pos ⟨2⟩ (by decide)) id (by decide) ⟨1⟩ (by decide)
  revert this; decide +kernel

-- `String.Slice.ext`, idx 3: s = "ab", t = ("ab").drop 1: same string and end, different start
theorem String.Slice.ext.h3 : ¬ drop0% String.Slice.ext 3 := fun h => by
  have := @h "ab".toSlice ("ab".toSlice.drop 1) rfl rfl
  have := congrArg (fun x => x.startInclusive.offset) this
  revert this; decide

-- `String.Slice.ext`, idx 4: s = "ab", t = ("ab").dropEnd 1: same string and start, different end
theorem String.Slice.ext.h4 : ¬ drop0% String.Slice.ext 4 := fun h => by
  have := @h "ab".toSlice ("ab".toSlice.dropEnd 1) rfl rfl
  have := congrArg (fun x => x.endExclusive.offset) this
  revert this; decide +kernel

-- `String.Slice.cast_pos`, idx 3: derivable: IsValidForSlice s p depends only on s.copy (isValidForSlice_iff_exists_append), so it follows from h'' and h' : s.copy = t.copy
theorem String.Slice.cast_pos.h3 : indep% String.Slice.cast_pos 3 := by
  intro s t p h' h''
  rw [String.Pos.Raw.isValidForSlice_iff_exists_append] at *
  rwa [h']

-- `String.Slice.cast_pos`, idx 5: derivable: IsValidForSlice t p follows from h and h' : s.copy = t.copy (isValidForSlice_iff_exists_append)
theorem String.Slice.cast_pos.h5 : indep% String.Slice.cast_pos 5 := by
  intro s t p h h'
  rw [String.Pos.Raw.isValidForSlice_iff_exists_append] at *
  rwa [← h']

-- `String.Slice.Pos.next_le_of_lt`, idx 3: derivable: p ≠ endPos follows from p < q (Slice.Pos.ne_endPos_of_lt)
theorem String.Slice.Pos.next_le_of_lt.h3 : indep% String.Slice.Pos.next_le_of_lt 3 := fun {_ _ _} h => String.Slice.Pos.ne_endPos_of_lt h

-- `String.Pos.next_le_of_lt`, idx 3: derivable: p ≠ endPos follows from p < q (Pos.ne_endPos_of_lt)
theorem String.Pos.next_le_of_lt.h3 : indep% String.Pos.next_le_of_lt 3 := fun {_ _ _} h => String.Pos.ne_endPos_of_lt h

-- `String.Slice.Pos.next_induction`, idx 3: s = "a", C = (· = endPos), p = startPos
theorem String.Slice.Pos.next_induction.h3 : ¬ drop0% String.Slice.Pos.next_induction 3 := fun h => by
  have := @h "a".toSlice (fun x => x = "a".toSlice.endPos) "a".toSlice.startPos rfl
  revert this; decide +kernel

-- `String.Slice.Pos.next_induction`, idx 4: s = "a", C = (· ≠ endPos) (next case holds trivially), p = endPos
theorem String.Slice.Pos.next_induction.h4 : ¬ drop0% String.Slice.Pos.next_induction 4 := fun h => by
  have := @h "a".toSlice (fun x => x ≠ "a".toSlice.endPos) "a".toSlice.endPos (fun x hx _ => hx)
  exact this rfl

-- `String.Pos.next_induction`, idx 3: s = "a", C = (· = endPos), p = startPos
theorem String.Pos.next_induction.h3 : ¬ drop0% String.Pos.next_induction 3 := fun h => by
  have := @h "a" (fun x => x = "a".endPos) "a".startPos rfl
  revert this; decide +kernel

-- `String.Pos.next_induction`, idx 4: s = "a", C = (· ≠ endPos) (next case holds trivially), p = endPos
theorem String.Pos.next_induction.h4 : ¬ drop0% String.Pos.next_induction 4 := fun h => by
  have := @h "a" (fun x => x ≠ "a".endPos) "a".endPos (fun x hx _ => hx)
  exact this rfl

-- `String.Slice.Pos.prev_induction`, idx 3: s = "a", C = (· = startPos), p = endPos
theorem String.Slice.Pos.prev_induction.h3 : ¬ drop0% String.Slice.Pos.prev_induction 3 := fun h => by
  have := @h "a".toSlice (fun x => x = "a".toSlice.startPos) "a".toSlice.endPos rfl
  revert this; decide +kernel

-- `String.Slice.Pos.prev_induction`, idx 4: s = "a", C = (· ≠ startPos) (prev case holds trivially), p = startPos
theorem String.Slice.Pos.prev_induction.h4 : ¬ drop0% String.Slice.Pos.prev_induction 4 := fun h => by
  have := @h "a".toSlice (fun x => x ≠ "a".toSlice.startPos) "a".toSlice.startPos (fun x hx _ => hx)
  exact this rfl

-- `String.Pos.prev_induction`, idx 3: s = "a", C = (· = startPos), p = endPos
theorem String.Pos.prev_induction.h3 : ¬ drop0% String.Pos.prev_induction 3 := fun h => by
  have := @h "a" (fun x => x = "a".startPos) "a".endPos rfl
  revert this; decide +kernel

-- `String.Pos.prev_induction`, idx 4: s = "a", C = (· ≠ startPos) (prev case holds trivially), p = startPos
theorem String.Pos.prev_induction.h4 : ¬ drop0% String.Pos.prev_induction 4 := fun h => by
  have := @h "a" (fun x => x ≠ "a".startPos) "a".startPos (fun x hx _ => hx)
  exact this rfl

-- `String.Pos.Splits.lt_iff_exists_eq_append`, idx 7: s = "a", p₁ = startPos < p₂ = endPos (splits "a" ""), t₁ = "a", t₂ = "": no nonempty t₅
theorem String.Pos.Splits.lt_iff_exists_eq_append.h7 : ¬ drop0% String.Pos.Splits.lt_iff_exists_eq_append 7 := fun h => by
  have := (@h "a" "a".startPos "a".endPos "a" "" "a" "" (String.splits_endPos "a")).1 (by decide)
  obtain ⟨t₅, h1, h2, h3⟩ := this
  exact h1 (by simpa using h3.symm)

-- `String.Pos.Splits.lt_iff_exists_eq_append`, idx 8: s = "a", p₁ = startPos (splits "" "a") < p₂ = endPos, t₃ = "", t₄ = "a": no nonempty t₅
theorem String.Pos.Splits.lt_iff_exists_eq_append.h8 : ¬ drop0% String.Pos.Splits.lt_iff_exists_eq_append 8 := fun h => by
  have := (@h "a" "a".startPos "a".endPos "" "a" "" "a" (String.splits_startPos "a")).1 (by decide)
  obtain ⟨t₅, h1, h2, h3⟩ := this
  exact h1 (by simpa using h2.symm)

-- `String.Slice.Pos.Splits.lt_iff_exists_eq_append`, idx 7: s = "a", p₁ = startPos < p₂ = endPos (splits "a" ""), t₁ = "a", t₂ = "": no nonempty t₅
theorem String.Slice.Pos.Splits.lt_iff_exists_eq_append.h7 : ¬ drop0% String.Slice.Pos.Splits.lt_iff_exists_eq_append 7 := fun h => by
  have := (@h "a".toSlice "a".toSlice.startPos "a".toSlice.endPos "a" "" "a" "" (String.Slice.splits_endPos "a".toSlice)).1 (by decide)
  obtain ⟨t₅, h1, h2, h3⟩ := this
  exact h1 (by simpa using h3.symm)

-- `String.Slice.Pos.Splits.lt_iff_exists_eq_append`, idx 8: s = "a", p₁ = startPos (splits "" "a") < p₂ = endPos, t₃ = "", t₄ = "a": no nonempty t₅
theorem String.Slice.Pos.Splits.lt_iff_exists_eq_append.h8 : ¬ drop0% String.Slice.Pos.Splits.lt_iff_exists_eq_append 8 := fun h => by
  have := (@h "a".toSlice "a".toSlice.startPos "a".toSlice.endPos "" "a" "" "a" (String.Slice.splits_startPos "a".toSlice)).1 (by decide)
  obtain ⟨t₅, h1, h2, h3⟩ := this
  exact h1 (by simpa using h2.symm)

/-! ## Positions in subslices (Lemmas.Order) -/

-- `String.Slice.Pos.slice_le_iff`, idx 6: dependent; s = "a" slice, p₀ = p₁ = endPos, q = startPos: q ≤ p₁ but not p₀ ≤ q
theorem String.Slice.Pos.slice_le_iff.h6 : ¬ indep0% String.Slice.Pos.slice_le_iff 6 := fun h =>
  absurd (@h "a".toSlice "a".toSlice.endPos "a".toSlice.endPos (by decide) (String.Slice.startPos _) "a".toSlice.startPos (by decide)) (by decide)

-- `String.Slice.Pos.slice_le_iff`, idx 7: dependent; s = "a" slice, p₀ = p₁ = startPos, q = endPos: p₀ ≤ q but not q ≤ p₁
theorem String.Slice.Pos.slice_le_iff.h7 : ¬ indep0% String.Slice.Pos.slice_le_iff 7 := fun h =>
  absurd (@h "a".toSlice "a".toSlice.startPos "a".toSlice.startPos (by decide) (String.Slice.startPos _) "a".toSlice.endPos (by decide)) (by decide)

-- `String.Slice.Pos.lt_slice_iff`, idx 6: dependent; s = "a" slice, p₀ = p₁ = endPos, q = startPos: q ≤ p₁ but not p₀ ≤ q
theorem String.Slice.Pos.lt_slice_iff.h6 : ¬ indep0% String.Slice.Pos.lt_slice_iff 6 := fun h =>
  absurd (@h "a".toSlice "a".toSlice.endPos "a".toSlice.endPos (by decide) (String.Slice.startPos _) "a".toSlice.startPos (by decide)) (by decide)

-- `String.Slice.Pos.lt_slice_iff`, idx 7: dependent; s = "a" slice, p₀ = p₁ = startPos, q = endPos: p₀ ≤ q but not q ≤ p₁
theorem String.Slice.Pos.lt_slice_iff.h7 : ¬ indep0% String.Slice.Pos.lt_slice_iff 7 := fun h =>
  absurd (@h "a".toSlice "a".toSlice.startPos "a".toSlice.startPos (by decide) (String.Slice.startPos _) "a".toSlice.endPos (by decide)) (by decide)

-- `String.Slice.Pos.slice_lt_iff`, idx 6: dependent; s = "a" slice, p₀ = p₁ = endPos, q = startPos: q ≤ p₁ but not p₀ ≤ q
theorem String.Slice.Pos.slice_lt_iff.h6 : ¬ indep0% String.Slice.Pos.slice_lt_iff 6 := fun h =>
  absurd (@h "a".toSlice "a".toSlice.endPos "a".toSlice.endPos (by decide) (String.Slice.startPos _) "a".toSlice.startPos (by decide)) (by decide)

-- `String.Slice.Pos.slice_lt_iff`, idx 7: dependent; s = "a" slice, p₀ = p₁ = startPos, q = endPos: p₀ ≤ q but not q ≤ p₁
theorem String.Slice.Pos.slice_lt_iff.h7 : ¬ indep0% String.Slice.Pos.slice_lt_iff 7 := fun h =>
  absurd (@h "a".toSlice "a".toSlice.startPos "a".toSlice.startPos (by decide) (String.Slice.startPos _) "a".toSlice.endPos (by decide)) (by decide)

-- `String.Slice.Pos.le_slice_iff`, idx 6: dependent; s = "a" slice, p₀ = p₁ = endPos, q = startPos: q ≤ p₁ but not p₀ ≤ q
theorem String.Slice.Pos.le_slice_iff.h6 : ¬ indep0% String.Slice.Pos.le_slice_iff 6 := fun h =>
  absurd (@h "a".toSlice "a".toSlice.endPos "a".toSlice.endPos (by decide) (String.Slice.startPos _) "a".toSlice.startPos (by decide)) (by decide)

-- `String.Slice.Pos.le_slice_iff`, idx 7: dependent; s = "a" slice, p₀ = p₁ = startPos, q = endPos: p₀ ≤ q but not q ≤ p₁
theorem String.Slice.Pos.le_slice_iff.h7 : ¬ indep0% String.Slice.Pos.le_slice_iff 7 := fun h =>
  absurd (@h "a".toSlice "a".toSlice.startPos "a".toSlice.startPos (by decide) (String.Slice.startPos _) "a".toSlice.endPos (by decide)) (by decide)

-- `String.Slice.Pos.get_eq_get_ofSlice`, idx 5: dependent; s = "a" slice, p₀ = p₁ = startPos, pos = endPos of the empty slice
theorem String.Slice.Pos.get_eq_get_ofSlice.h5 : ¬ indep0% String.Slice.Pos.get_eq_get_ofSlice 5 := fun h =>
  @h "a".toSlice "a".toSlice.startPos "a".toSlice.startPos (by decide) (String.Slice.endPos _) rfl

-- `String.Slice.Pos.ofSlice_next`, idx 5: dependent; s = "a" slice, p₀ = p₁ = startPos, p = endPos of the empty slice
theorem String.Slice.Pos.ofSlice_next.h5 : ¬ indep0% String.Slice.Pos.ofSlice_next 5 := fun h =>
  @h "a".toSlice "a".toSlice.startPos "a".toSlice.startPos (by decide) (String.Slice.endPos _) rfl

-- `String.Slice.Pos.ofSlice_prev`, idx 5: dependent; s = "a" slice, p₀ = p₁ = startPos, p = startPos of the empty slice
theorem String.Slice.Pos.ofSlice_prev.h5 : ¬ indep0% String.Slice.Pos.ofSlice_prev 5 := fun h =>
  @h "a".toSlice "a".toSlice.startPos "a".toSlice.startPos (by decide) (String.Slice.startPos _) rfl

-- `String.Pos.slice_le_iff`, idx 6: dependent; s = "a", p₀ = p₁ = endPos, q = startPos: q ≤ p₁ but not p₀ ≤ q
theorem String.Pos.slice_le_iff.h6 : ¬ indep0% String.Pos.slice_le_iff 6 := fun h =>
  absurd (@h "a" "a".endPos "a".endPos (by decide) (String.Slice.startPos _) "a".startPos (by decide)) (by decide)

-- `String.Pos.slice_le_iff`, idx 7: dependent; s = "a", p₀ = p₁ = startPos, q = endPos: p₀ ≤ q but not q ≤ p₁
theorem String.Pos.slice_le_iff.h7 : ¬ indep0% String.Pos.slice_le_iff 7 := fun h =>
  absurd (@h "a" "a".startPos "a".startPos (by decide) (String.Slice.startPos _) "a".endPos (by decide)) (by decide)

-- `String.Pos.lt_slice_iff`, idx 6: dependent; s = "a", p₀ = p₁ = endPos, q = startPos: q ≤ p₁ but not p₀ ≤ q
theorem String.Pos.lt_slice_iff.h6 : ¬ indep0% String.Pos.lt_slice_iff 6 := fun h =>
  absurd (@h "a" "a".endPos "a".endPos (by decide) (String.Slice.startPos _) "a".startPos (by decide)) (by decide)

-- `String.Pos.lt_slice_iff`, idx 7: dependent; s = "a", p₀ = p₁ = startPos, q = endPos: p₀ ≤ q but not q ≤ p₁
theorem String.Pos.lt_slice_iff.h7 : ¬ indep0% String.Pos.lt_slice_iff 7 := fun h =>
  absurd (@h "a" "a".startPos "a".startPos (by decide) (String.Slice.startPos _) "a".endPos (by decide)) (by decide)

-- `String.Pos.slice_lt_iff`, idx 6: dependent; s = "a", p₀ = p₁ = endPos, q = startPos: q ≤ p₁ but not p₀ ≤ q
theorem String.Pos.slice_lt_iff.h6 : ¬ indep0% String.Pos.slice_lt_iff 6 := fun h =>
  absurd (@h "a" "a".endPos "a".endPos (by decide) (String.Slice.startPos _) "a".startPos (by decide)) (by decide)

-- `String.Pos.slice_lt_iff`, idx 7: dependent; s = "a", p₀ = p₁ = startPos, q = endPos: p₀ ≤ q but not q ≤ p₁
theorem String.Pos.slice_lt_iff.h7 : ¬ indep0% String.Pos.slice_lt_iff 7 := fun h =>
  absurd (@h "a" "a".startPos "a".startPos (by decide) (String.Slice.startPos _) "a".endPos (by decide)) (by decide)

-- `String.Pos.le_slice_iff`, idx 6: dependent; s = "a", p₀ = p₁ = endPos, q = startPos: q ≤ p₁ but not p₀ ≤ q
theorem String.Pos.le_slice_iff.h6 : ¬ indep0% String.Pos.le_slice_iff 6 := fun h =>
  absurd (@h "a" "a".endPos "a".endPos (by decide) (String.Slice.startPos _) "a".startPos (by decide)) (by decide)

-- `String.Pos.le_slice_iff`, idx 7: dependent; s = "a", p₀ = p₁ = startPos, q = endPos: p₀ ≤ q but not q ≤ p₁
theorem String.Pos.le_slice_iff.h7 : ¬ indep0% String.Pos.le_slice_iff 7 := fun h =>
  absurd (@h "a" "a".startPos "a".startPos (by decide) (String.Slice.startPos _) "a".endPos (by decide)) (by decide)

-- `String.Pos.get_eq_get_ofSlice`, idx 5: dependent; s = "a", p₀ = p₁ = startPos, pos = endPos of the empty slice
theorem String.Pos.get_eq_get_ofSlice.h5 : ¬ indep0% String.Pos.get_eq_get_ofSlice 5 := fun h =>
  @h "a" "a".startPos "a".startPos (by decide) (String.Slice.endPos _) rfl

-- `String.Pos.ofSlice_next`, idx 5: dependent; s = "a", p₀ = p₁ = startPos, p = endPos of the empty slice
theorem String.Pos.ofSlice_next.h5 : ¬ indep0% String.Pos.ofSlice_next 5 := fun h =>
  @h "a" "a".startPos "a".startPos (by decide) (String.Slice.endPos _) rfl

-- `String.Pos.ofSlice_prev`, idx 5: dependent; s = "a", p₀ = p₁ = startPos, p = startPos of the empty slice
theorem String.Pos.ofSlice_prev.h5 : ¬ indep0% String.Pos.ofSlice_prev 5 := fun h =>
  @h "a" "a".startPos "a".startPos (by decide) (String.Slice.startPos _) rfl

/-! ## Iteration models and pattern search with splits (Iterate, Find.Char, Find.Pred) -/

-- `String.Slice.Model.map_get_positionsFrom_of_splits`, idx 4: s = "", p = endPos, t₂ = "a": positionsFrom endPos = []
theorem String.Slice.Model.map_get_positionsFrom_of_splits.h4 : ¬ drop0% String.Slice.Model.map_get_positionsFrom_of_splits 4 := fun h => by
  have := @h "".toSlice "".toSlice.endPos "" "a"
  rw [String.Slice.Model.positionsFrom_endPos] at this; simp at this

-- `String.Model.map_get_positionsFrom_of_splits`, idx 4: s = "", p = endPos, t₂ = "a": positionsFrom endPos = []
theorem String.Model.map_get_positionsFrom_of_splits.h4 : ¬ drop0% String.Model.map_get_positionsFrom_of_splits 4 := fun h => by
  have := @h "" "".endPos "" "a"
  rw [String.Model.positionsFrom_endPos] at this; simp at this

-- `String.Slice.Model.map_get_revPositionsFrom_of_splits`, idx 4: s = "", p = startPos, t₁ = "a": revPositionsFrom startPos = []
theorem String.Slice.Model.map_get_revPositionsFrom_of_splits.h4 : ¬ drop0% String.Slice.Model.map_get_revPositionsFrom_of_splits 4 := fun h => by
  have := @h "".toSlice "".toSlice.startPos "a" ""
  rw [String.Slice.Model.revPositionsFrom_startPos] at this; simp at this

-- `String.Model.map_get_revPositionsFrom_of_splits`, idx 4: s = "", p = startPos, t₁ = "a": revPositionsFrom startPos = []
theorem String.Model.map_get_revPositionsFrom_of_splits.h4 : ¬ drop0% String.Model.map_get_revPositionsFrom_of_splits 4 := fun h => by
  have := @h "" "".startPos "a" ""
  rw [String.Model.revPositionsFrom_startPos] at this; simp at this

-- `String.Slice.Pos.Splits.mem_toList_left_iff`, idx 5: s = "", pos = startPos, t = "a", c = a: no position before startPos
theorem String.Slice.Pos.Splits.mem_toList_left_iff.h5 : ¬ drop0% String.Slice.Pos.Splits.mem_toList_left_iff 5 := fun h => by
  obtain ⟨p, hp, _⟩ := (@h "".toSlice "".toSlice.startPos "a" "" 'a').1 (by decide)
  exact String.Slice.Pos.not_lt_startPos hp

-- `String.Pos.Splits.mem_toList_left_iff`, idx 5: s = "", pos = startPos, t = "a", c = a: no position before startPos
theorem String.Pos.Splits.mem_toList_left_iff.h5 : ¬ drop0% String.Pos.Splits.mem_toList_left_iff 5 := fun h => by
  obtain ⟨p, hp, _⟩ := (@h "" "".startPos "a" "" 'a').1 (by decide)
  exact String.Pos.not_lt_startPos hp

-- `String.Slice.Pos.Splits.mem_toList_right_iff`, idx 5: s = "", pos = endPos, u = "a", c = a: no position after endPos
theorem String.Slice.Pos.Splits.mem_toList_right_iff.h5 : ¬ drop0% String.Slice.Pos.Splits.mem_toList_right_iff 5 := fun h => by
  obtain ⟨p, hp, hne, _⟩ := (@h "".toSlice "".toSlice.endPos "" "a" 'a').1 (by decide)
  exact hne ((String.Slice.Pos.endPos_le p).1 hp)

-- `String.Pos.Splits.mem_toList_right_iff`, idx 5: s = "", pos = endPos, u = "a", c = a: no position after endPos
theorem String.Pos.Splits.mem_toList_right_iff.h5 : ¬ drop0% String.Pos.Splits.mem_toList_right_iff 5 := fun h => by
  obtain ⟨p, hp, hne, _⟩ := (@h "" "".endPos "" "a" 'a').1 (by decide)
  exact hne ((String.Pos.endPos_le p).1 hp)

-- `String.Slice.Pos.find?_char_eq_none_iff_not_mem_of_splits`, idx 5: c = a, s = "", pos = startPos, u = "a": find? is none (theorem with the true split) but a ∈ u
theorem String.Slice.Pos.find?_char_eq_none_iff_not_mem_of_splits.h5 : ¬ drop0% String.Slice.Pos.find?_char_eq_none_iff_not_mem_of_splits 5 := fun h => by
  have h1 := (String.Slice.Pos.find?_char_eq_none_iff_not_mem_of_splits (c := 'a') (String.Slice.splits_startPos "".toSlice)).2 (by simp)
  have := (@h 'a' "".toSlice "".toSlice.startPos "" "a").1 h1
  simp at this

-- `String.Slice.Pos.find?_char_eq_some_iff_splits`, idx 5: s = "a", pos = endPos, t = "", u = "a", pos' = startPos: find? from endPos is none (true split) but startPos splits "" and "a"
theorem String.Slice.Pos.find?_char_eq_some_iff_splits.h5 : ¬ drop0% String.Slice.Pos.find?_char_eq_some_iff_splits 5 := fun h => by
  have h1 := (String.Slice.Pos.find?_char_eq_none_iff_not_mem_of_splits (c := 'a') (String.Slice.splits_endPos "a".toSlice)).2 (by simp)
  have := (@h 'a' "a".toSlice "a".toSlice.endPos "" "a" "a".toSlice.startPos).2
    ⟨"", "", by simpa using String.Slice.splits_startPos "a".toSlice, by simp⟩
  rw [h1] at this; cases this

-- `String.Slice.Pos.find?_bool_eq_none_iff_of_splits`, idx 5: p = (· == a), s = "", pos = startPos, u = "a": find? is none but p a
theorem String.Slice.Pos.find?_bool_eq_none_iff_of_splits.h5 : ¬ drop0% String.Slice.Pos.find?_bool_eq_none_iff_of_splits 5 := fun h => by
  have h1 := (String.Slice.Pos.find?_bool_eq_none_iff_of_splits (p := (· == 'a')) (String.Slice.splits_startPos "".toSlice)).2 (by simp)
  have := (@h (· == 'a') "".toSlice "".toSlice.startPos "" "a").1 h1
  simp at this

-- `String.Slice.Pos.find?_bool_eq_some_iff_splits`, idx 5: s = "a", pos = endPos, t = "", u = "a", pos' = startPos: find? from endPos is none (true split) but startPos splits "" and "a"
theorem String.Slice.Pos.find?_bool_eq_some_iff_splits.h5 : ¬ drop0% String.Slice.Pos.find?_bool_eq_some_iff_splits 5 := fun h => by
  have h1 := (String.Slice.Pos.find?_bool_eq_none_iff_of_splits (p := (· == 'a')) (String.Slice.splits_endPos "a".toSlice)).2 (by simp)
  have := (@h (· == 'a') "a".toSlice "a".toSlice.endPos "" "a" "a".toSlice.startPos).2
    ⟨"", 'a', "", by simpa using String.Slice.splits_startPos "a".toSlice, by simp, by simp⟩
  rw [h1] at this; cases this

-- `String.Slice.Pos.find?_prop_eq_none_iff_of_splits`, idx 6: p = (· = a), s = "", pos = startPos, u = "a": find? is none but p a
theorem String.Slice.Pos.find?_prop_eq_none_iff_of_splits.h6 : ¬ drop0% String.Slice.Pos.find?_prop_eq_none_iff_of_splits 6 := fun h => by
  have h1 := (String.Slice.Pos.find?_prop_eq_none_iff_of_splits (p := (· = 'a')) (String.Slice.splits_startPos "".toSlice)).2 (by simp)
  have := (@h (· = 'a') inferInstance "".toSlice "".toSlice.startPos "" "a").1 h1
  simp at this

-- `String.Slice.Pos.find?_prop_eq_some_iff_splits`, idx 6: s = "a", pos = endPos, t = "", u = "a", pos' = startPos: find? from endPos is none (true split) but startPos splits "" and "a"
theorem String.Slice.Pos.find?_prop_eq_some_iff_splits.h6 : ¬ drop0% String.Slice.Pos.find?_prop_eq_some_iff_splits 6 := fun h => by
  have h1 := (String.Slice.Pos.find?_prop_eq_none_iff_of_splits (p := (· = 'a')) (String.Slice.splits_endPos "a".toSlice)).2 (by simp)
  have := (@h (· = 'a') inferInstance "a".toSlice "a".toSlice.endPos "" "a" "a".toSlice.startPos).2
    ⟨"", 'a', "", by simpa using String.Slice.splits_startPos "a".toSlice, by simp, by simp⟩
  rw [h1] at this; cases this

-- `String.Pos.find?_char_eq_none_iff_not_mem_of_splits`, idx 5: c = a, s = "", pos = startPos, u = "a": find? is none (theorem with the true split) but a ∈ u
theorem String.Pos.find?_char_eq_none_iff_not_mem_of_splits.h5 : ¬ drop0% String.Pos.find?_char_eq_none_iff_not_mem_of_splits 5 := fun h => by
  have h1 := (String.Pos.find?_char_eq_none_iff_not_mem_of_splits (c := 'a') (String.splits_startPos "")).2 (by simp)
  have := (@h 'a' "" "".startPos "" "a").1 h1
  simp at this

-- `String.Pos.find?_char_eq_some_iff_splits`, idx 5: s = "a", pos = endPos, t = "", u = "a", pos' = startPos: find? from endPos is none (true split) but startPos splits "" and "a"
theorem String.Pos.find?_char_eq_some_iff_splits.h5 : ¬ drop0% String.Pos.find?_char_eq_some_iff_splits 5 := fun h => by
  have h1 := (String.Pos.find?_char_eq_none_iff_not_mem_of_splits (c := 'a') (String.splits_endPos "a")).2 (by simp)
  have := (@h 'a' "a" "a".endPos "" "a" "a".startPos).2
    ⟨"", "", by simpa using String.splits_startPos "a", by simp⟩
  rw [h1] at this; cases this

-- `String.Pos.find?_bool_eq_none_iff_of_splits`, idx 5: p = (· == a), s = "", pos = startPos, u = "a": find? is none but p a
theorem String.Pos.find?_bool_eq_none_iff_of_splits.h5 : ¬ drop0% String.Pos.find?_bool_eq_none_iff_of_splits 5 := fun h => by
  have h1 := (String.Pos.find?_bool_eq_none_iff_of_splits (p := (· == 'a')) (String.splits_startPos "")).2 (by simp)
  have := (@h (· == 'a') "" "".startPos "" "a").1 h1
  simp at this

-- `String.Pos.find?_bool_eq_some_iff_splits`, idx 5: s = "a", pos = endPos, t = "", u = "a", pos' = startPos: find? from endPos is none (true split) but startPos splits "" and "a"
theorem String.Pos.find?_bool_eq_some_iff_splits.h5 : ¬ drop0% String.Pos.find?_bool_eq_some_iff_splits 5 := fun h => by
  have h1 := (String.Pos.find?_bool_eq_none_iff_of_splits (p := (· == 'a')) (String.splits_endPos "a")).2 (by simp)
  have := (@h (· == 'a') "a" "a".endPos "" "a" "a".startPos).2
    ⟨"", 'a', "", by simpa using String.splits_startPos "a", by simp, by simp⟩
  rw [h1] at this; cases this

-- `String.Pos.find?_prop_eq_none_iff_of_splits`, idx 6: p = (· = a), s = "", pos = startPos, u = "a": find? is none but p a
theorem String.Pos.find?_prop_eq_none_iff_of_splits.h6 : ¬ drop0% String.Pos.find?_prop_eq_none_iff_of_splits 6 := fun h => by
  have h1 := (String.Pos.find?_prop_eq_none_iff_of_splits (p := (· = 'a')) (String.splits_startPos "")).2 (by simp)
  have := (@h (· = 'a') inferInstance "" "".startPos "" "a").1 h1
  simp at this

-- `String.Pos.find?_prop_eq_some_iff_splits`, idx 6: s = "a", pos = endPos, t = "", u = "a", pos' = startPos: find? from endPos is none (true split) but startPos splits "" and "a"
theorem String.Pos.find?_prop_eq_some_iff_splits.h6 : ¬ drop0% String.Pos.find?_prop_eq_some_iff_splits 6 := fun h => by
  have h1 := (String.Pos.find?_prop_eq_none_iff_of_splits (p := (· = 'a')) (String.splits_endPos "a")).2 (by simp)
  have := (@h (· = 'a') inferInstance "a" "a".endPos "" "a" "a".startPos).2
    ⟨"", 'a', "", by simpa using String.splits_startPos "a", by simp, by simp⟩
  rw [h1] at this; cases this

/-! ## Model.split and char splitting (Split.Basic, Split.Char, Split.Pred) -/

-- `String.Slice.Pattern.Model.split_eq_of_isLongestMatchAt`, idx 8: dependent; pat = a, s = "a", firstRejected = endPos, start = startPos, stop = endPos (a longest match)
theorem String.Slice.Pattern.Model.split_eq_of_isLongestMatchAt.h8 : ¬ indep0% String.Slice.Pattern.Model.split_eq_of_isLongestMatchAt 8 := fun h =>
  absurd (@h Char 'a' _ _ "a".toSlice "a".toSlice.endPos "a".toSlice.startPos _
    (String.Slice.Pattern.Model.Char.isLongestMatchAt_of_get_eq (h := by decide) (by decide))) (by decide)

-- `String.Slice.Pattern.Model.split_eq_of_not_matchesAt`, idx 8: dependent; pat = a, s = "a", firstRejected = stop = startPos, start = endPos (h vacuous)
theorem String.Slice.Pattern.Model.split_eq_of_not_matchesAt.h8 : ¬ indep0% String.Slice.Pattern.Model.split_eq_of_not_matchesAt 8 := fun h =>
  absurd (@h Char 'a' _ _ "a".toSlice "a".toSlice.startPos "a".toSlice.endPos "a".toSlice.startPos (by decide)
    (fun p h1 h2 => absurd h2 String.Slice.Pos.not_lt_startPos)) (by decide)

-- `String.Slice.Pattern.Model.split_eq_of_not_matchesAt`, idx 9: dependent; pat = a, s = "a", firstRejected = endPos, start = stop = startPos (h vacuous)
theorem String.Slice.Pattern.Model.split_eq_of_not_matchesAt.h9 : ¬ indep0% String.Slice.Pattern.Model.split_eq_of_not_matchesAt 9 := fun h =>
  absurd (@h Char 'a' _ _ "a".toSlice "a".toSlice.endPos "a".toSlice.startPos "a".toSlice.startPos (by decide)
    (fun p h1 h2 => absurd h2 String.Slice.Pos.not_lt_startPos)) (by decide)

-- `String.Slice.Pattern.Model.split_eq_next_of_not_matchesAt`, idx 7: dependent; pat = a, s = "b", firstRejected = endPos, start = startPos (no match there)
theorem String.Slice.Pattern.Model.split_eq_next_of_not_matchesAt.h7 : ¬ indep0% String.Slice.Pattern.Model.split_eq_next_of_not_matchesAt 7 := fun h =>
  absurd (@h Char 'a' _ _ "b".toSlice "b".toSlice.endPos "b".toSlice.startPos (by decide)
    (by rw [String.Slice.Pattern.Model.Char.matchesAt_iff]; decide)) (by decide)

-- `String.Slice.Pattern.Model.split_eq_next_of_not_matchesAt`, idx 8: dependent; pat = a, s = "", start = firstRejected = startPos = endPos (no match)
theorem String.Slice.Pattern.Model.split_eq_next_of_not_matchesAt.h8 : ¬ indep0% String.Slice.Pattern.Model.split_eq_next_of_not_matchesAt 8 := fun h =>
  absurd (@h Char 'a' _ _ "".toSlice "".toSlice.startPos "".toSlice.startPos (by decide)
    (by rw [String.Slice.Pattern.Model.Char.matchesAt_iff]; decide)) (by decide)

-- `String.Slice.Pattern.Model.split_eq_split_decide`, idx 5: dependent; s = "a", f = endPos, curr = startPos
theorem String.Slice.Pattern.Model.split_eq_split_decide.h5 : ¬ indep0% String.Slice.Pattern.Model.split_eq_split_decide 5 := fun h =>
  absurd (@h (· = 'a') inferInstance "a".toSlice "a".toSlice.endPos "a".toSlice.startPos) (by decide)

-- `String.toList_split_intercalate`, idx 2: c = a, l = ["a"]: splitting "a" at a gives ["", ""], not ["a"]
theorem String.toList_split_intercalate.h2 : ¬ drop0% String.toList_split_intercalate 2 := fun h => by
  have := @h 'a' ["a"]
  rw [String.toList_split_char] at this
  revert this; decide

-- `String.toList_split_intercalate_beq`, idx 2: c = a, l = ["a"]: splitting "a" at a gives ["", ""], not ["a"]
theorem String.toList_split_intercalate_beq.h2 : ¬ drop0% String.toList_split_intercalate_beq 2 := fun h => by
  have := @h 'a' ["a"]
  rw [String.Slice.beq_list_iff, String.toList_split_char] at this
  revert this; decide

-- `String.Slice.toList_split_intercalate`, idx 2: c = a, l = ["a"]: splitting "a" at a gives ["", ""], not ["a"]
theorem String.Slice.toList_split_intercalate.h2 : ¬ drop0% String.Slice.toList_split_intercalate 2 := fun h => by
  have := @h 'a' ["a".toSlice]
  rw [String.toList_split_char] at this
  revert this; decide

-- `String.Slice.toList_split_intercalate_beq`, idx 2: c = a, l = ["a"]: splitting "a" at a gives ["", ""], not ["a"]
theorem String.Slice.toList_split_intercalate_beq.h2 : ¬ drop0% String.Slice.toList_split_intercalate_beq 2 := fun h => by
  have := @h 'a' ["a".toSlice]
  rw [String.Slice.beq_list_iff, String.toList_split_char] at this
  revert this; decide

-- `String.Slice.toList_split_of_isEmpty`, idx 10: pat = a, s = "a" (nonempty): split gives ["", ""]
theorem String.Slice.toList_split_of_isEmpty.h10 : ¬ drop0% String.Slice.toList_split_of_isEmpty 10 := fun h => by
  have := @h Char 'a' _ _ _ _ _ _ _ "a".toSlice
  rw [String.Slice.toList_split_char] at this
  revert this; decide

-- `String.Slice.toList_splitToSubslice_of_isEmpty`, idx 10: pat = a, s = "a" (nonempty): split gives two pieces, not one
theorem String.Slice.toList_splitToSubslice_of_isEmpty.h10 : ¬ drop0% String.Slice.toList_splitToSubslice_of_isEmpty 10 := fun h => by
  have := congrArg (List.map (String.Slice.copy ∘ String.Slice.Subslice.toSlice)) (@h Char 'a' _ _ _ _ _ _ _ "a".toSlice)
  rw [String.Slice.toList_splitToSubslice_char] at this
  revert this; decide

/-! ## Searcher instances: Finite and LawfulIteratorLoop (Find.Basic, Split.Basic) -/

-- `String.Slice.isSome_find?`, idx 4: non-finite searcher LS (skips to itself, may yield a whole-slice match) with a loop that is lawful vacuously (no loop over LS is well-founded): returns init at types with ≤ 2 elements (Bool), else applies the body to the match; on "a": find? = some, contains = false
theorem String.Slice.isSome_find?.h4 : ¬ drop0% String.Slice.isSome_find? 4 := fun h =>
  absurd (@h Char 'a' LS (fun s => LS.iter s) (fun s => LS.loop s) (fun s => LS.lawful s) LS.sch sA)
    (by rw [find_LS, contains_LS]; decide)

-- `String.Slice.find?_eq_none_iff`, idx 4: same LS searcher and loop: find? = some startPos but contains = false on "a"
theorem String.Slice.find?_eq_none_iff.h4 : ¬ drop0% String.Slice.find?_eq_none_iff 4 := fun h =>
  absurd (@h Char 'a' LS (fun s => LS.iter s) (fun s => LS.loop s) (fun s => LS.lawful s) LS.sch sA)
    (by rw [find_LS, contains_LS]; decide)

-- `String.Slice.isSome_find?`, idx 6: pattern a with the library searcher and a non-lawful loop that returns init at types with ≤ 2 elements (Bool), else the library loop: find? = some, contains = false on "a"
theorem String.Slice.isSome_find?.h6 : ¬ drop0% String.Slice.isSome_find? 6 := fun h =>
  absurd (@h Char 'a' σC _ _ (fun _ => triLoop inferInstance) _ sA) (by rw [find_tri, contains_tri]; decide)

-- `String.Slice.find?_eq_none_iff`, idx 6: same non-lawful loop: find? = some startPos, contains = false on "a"
theorem String.Slice.find?_eq_none_iff.h6 : ¬ drop0% String.Slice.find?_eq_none_iff 6 := fun h =>
  absurd (@h Char 'a' σC _ _ (fun _ => triLoop inferInstance) _ sA) (by rw [find_tri, contains_tri]; decide)

-- `String.Slice.Pattern.Model.find?_eq_some_iff`, idx 8: pattern a with the library searcher and a loop that always returns init: find?/contains/Pos.find? give none/false on "a" though a matches at startPos
theorem String.Slice.Pattern.Model.find?_eq_some_iff.h8 : ¬ drop0% String.Slice.Pattern.Model.find?_eq_some_iff 8 := fun h => by
  have := (@h Char 'a' _ _ σC _ _ (fun _ => bogusLoop) _ _ sA sA.startPos).2
    ⟨matches_a, fun _ h => absurd h String.Slice.Pos.not_lt_startPos⟩
  rw [find_bogus] at this; cases this

-- `String.Slice.Pattern.Model.find?_eq_none_iff`, idx 8: pattern a with the library searcher and a loop that always returns init: find?/contains/Pos.find? give none/false on "a" though a matches at startPos
theorem String.Slice.Pattern.Model.find?_eq_none_iff.h8 : ¬ drop0% String.Slice.Pattern.Model.find?_eq_none_iff 8 := fun h =>
  (@h Char 'a' _ _ σC _ _ (fun _ => bogusLoop) _ _ sA).1 find_bogus _ matches_a

-- `String.Slice.Pattern.Model.contains_eq_false_iff`, idx 8: pattern a with the library searcher and a loop that always returns init: find?/contains/Pos.find? give none/false on "a" though a matches at startPos
theorem String.Slice.Pattern.Model.contains_eq_false_iff.h8 : ¬ drop0% String.Slice.Pattern.Model.contains_eq_false_iff 8 := fun h =>
  (@h Char 'a' _ _ σC _ _ (fun _ => bogusLoop) _ _ sA).1 contains_bogus _ matches_a

-- `String.Slice.Pattern.Model.contains_eq_true_iff`, idx 8: pattern a with the library searcher and a loop that always returns init: find?/contains/Pos.find? give none/false on "a" though a matches at startPos
theorem String.Slice.Pattern.Model.contains_eq_true_iff.h8 : ¬ drop0% String.Slice.Pattern.Model.contains_eq_true_iff 8 := fun h => by
  have := (@h Char 'a' _ _ σC _ _ (fun _ => bogusLoop) _ _ sA).2 ⟨_, matches_a⟩
  rw [contains_bogus] at this; cases this

-- `String.Slice.Pattern.Model.posFind?_eq_some_iff`, idx 8: pattern a with the library searcher and a loop that always returns init: find?/contains/Pos.find? give none/false on "a" though a matches at startPos
theorem String.Slice.Pattern.Model.posFind?_eq_some_iff.h8 : ¬ drop0% String.Slice.Pattern.Model.posFind?_eq_some_iff 8 := fun h => by
  have := (@h Char 'a' _ _ σC _ _ (fun _ => bogusLoop) _ _ sA sA.startPos sA.startPos).2
    ⟨Std.le_refl _, matches_a, fun _ _ h => absurd h String.Slice.Pos.not_lt_startPos⟩
  rw [posFind_bogus] at this; cases this

-- `String.Slice.Pattern.Model.posFind?_eq_none_iff`, idx 8: pattern a with the library searcher and a loop that always returns init: find?/contains/Pos.find? give none/false on "a" though a matches at startPos
theorem String.Slice.Pattern.Model.posFind?_eq_none_iff.h8 : ¬ drop0% String.Slice.Pattern.Model.posFind?_eq_none_iff 8 := fun h =>
  (@h Char 'a' _ _ σC _ _ (fun _ => bogusLoop) _ _ sA sA.startPos).1 posFind_bogus _ (Std.le_refl _) matches_a

-- `String.Slice.Pattern.Model.find?_eq_some_iff`, idx 6: dependent; the searcher LS (skips to itself) is not Finite; it has the iterator, a vacuously lawful loop and a searcher for a
theorem String.Slice.Pattern.Model.find?_eq_some_iff.h6 : ¬ indep0% String.Slice.Pattern.Model.find?_eq_some_iff 6 := fun h =>
  LS.not_finite sA (@h Char 'a' _ _ LS (fun s => LS.iter s) (fun s => LS.loop s) (fun s => LS.lawful s) LS.sch sA sA.startPos sA)

-- `String.Slice.Pattern.Model.find?_eq_none_iff`, idx 6: dependent; the searcher LS (skips to itself) is not Finite; it has the iterator, a vacuously lawful loop and a searcher for a
theorem String.Slice.Pattern.Model.find?_eq_none_iff.h6 : ¬ indep0% String.Slice.Pattern.Model.find?_eq_none_iff 6 := fun h =>
  LS.not_finite sA (@h Char 'a' _ _ LS (fun s => LS.iter s) (fun s => LS.loop s) (fun s => LS.lawful s) LS.sch sA sA)

-- `String.Slice.Pattern.Model.contains_eq_false_iff`, idx 6: dependent; the searcher LS (skips to itself) is not Finite; it has the iterator, a vacuously lawful loop and a searcher for a
theorem String.Slice.Pattern.Model.contains_eq_false_iff.h6 : ¬ indep0% String.Slice.Pattern.Model.contains_eq_false_iff 6 := fun h =>
  LS.not_finite sA (@h Char 'a' _ _ LS (fun s => LS.iter s) (fun s => LS.loop s) (fun s => LS.lawful s) LS.sch sA sA)

-- `String.Slice.Pattern.Model.contains_eq_true_iff`, idx 6: dependent; the searcher LS (skips to itself) is not Finite; it has the iterator, a vacuously lawful loop and a searcher for a
theorem String.Slice.Pattern.Model.contains_eq_true_iff.h6 : ¬ indep0% String.Slice.Pattern.Model.contains_eq_true_iff 6 := fun h =>
  LS.not_finite sA (@h Char 'a' _ _ LS (fun s => LS.iter s) (fun s => LS.loop s) (fun s => LS.lawful s) LS.sch sA sA)

-- `String.Slice.Pattern.Model.posFind?_eq_some_iff`, idx 6: dependent; the searcher LS (skips to itself) is not Finite; it has the iterator, a vacuously lawful loop and a searcher for a
theorem String.Slice.Pattern.Model.posFind?_eq_some_iff.h6 : ¬ indep0% String.Slice.Pattern.Model.posFind?_eq_some_iff 6 := fun h =>
  LS.not_finite sA (@h Char 'a' _ _ LS (fun s => LS.iter s) (fun s => LS.loop s) (fun s => LS.lawful s) LS.sch sA sA.startPos sA.startPos sA)

-- `String.Slice.Pattern.Model.posFind?_eq_none_iff`, idx 6: dependent; the searcher LS (skips to itself) is not Finite; it has the iterator, a vacuously lawful loop and a searcher for a
theorem String.Slice.Pattern.Model.posFind?_eq_none_iff.h6 : ¬ indep0% String.Slice.Pattern.Model.posFind?_eq_none_iff 6 := fun h =>
  LS.not_finite sA (@h Char 'a' _ _ LS (fun s => LS.iter s) (fun s => LS.loop s) (fun s => LS.lawful s) LS.sch sA sA.startPos sA)

-- `String.Slice.Pattern.toList_splitToSubslice_eq_modelSplit`, idx 7: dependent; the searcher LS (skips to itself) is not Finite
theorem String.Slice.Pattern.toList_splitToSubslice_eq_modelSplit.h7 : ¬ indep0% String.Slice.Pattern.toList_splitToSubslice_eq_modelSplit 7 := fun h =>
  LS.not_finite sA (@h Char 'a' _ _ LS LS.sch (fun s => LS.iter s) sA sA)

-- `String.Slice.toList_splitToSubslice_of_isEmpty`, idx 7: dependent; the searcher LS (skips to itself) is not Finite
theorem String.Slice.toList_splitToSubslice_of_isEmpty.h7 : ¬ indep0% String.Slice.toList_splitToSubslice_of_isEmpty 7 := fun h =>
  LS.not_finite sA (@h Char 'a' _ _ LS LS.sch (fun s => LS.iter s) "".toSlice (by decide) sA)

-- `String.Slice.toList_split_of_isEmpty`, idx 7: dependent; the searcher LS (skips to itself) is not Finite
theorem String.Slice.toList_split_of_isEmpty.h7 : ¬ indep0% String.Slice.toList_split_of_isEmpty 7 := fun h =>
  LS.not_finite sA (@h Char 'a' _ _ LS LS.sch (fun s => LS.iter s) "".toSlice (by decide) sA)

-- `String.toList_split_empty`, idx 7: dependent; the searcher LS (skips to itself) is not Finite
theorem String.toList_split_empty.h7 : ¬ indep0% String.toList_split_empty 7 := fun h =>
  LS.not_finite sA (@h Char 'a' _ _ LS LS.sch (fun s => LS.iter s) sA)

/-! ## forIn over strings in a non-lawful monad (Iterate) -/

-- `String.Slice.forIn_eq_forIn_toList`, idx 3: m = NatM (Nat, bind adds 1, not lawful), s = "a", body pure (yield ()): string loop gives 2 binds, list loop 1
theorem String.Slice.forIn_eq_forIn_toList.h3 : ¬ drop0% String.Slice.forIn_eq_forIn_toList 3 := fun h => by
  have := congrArg NatM.val (@h Unit NatM _ sA () (fun _ _ => pure (ForInStep.yield ())))
  rw [forIn_sA_natM] at this
  revert this; decide

-- `String.forIn_eq_forIn_toList`, idx 3: m = NatM (Nat, bind adds 1, not lawful), s = "a", body pure (yield ()): string loop gives 2 binds, list loop 1
theorem String.forIn_eq_forIn_toList.h3 : ¬ drop0% String.forIn_eq_forIn_toList 3 := fun h => by
  have := congrArg NatM.val (@h Unit NatM _ "a" () (fun _ _ => pure (ForInStep.yield ())))
  rw [show NatM.val (ForIn.forIn (m := NatM) "a" () (fun _ _ => pure (ForInStep.yield ()))) = 2 from forIn_sA_natM] at this
  revert this; decide

end StrCoreHand
