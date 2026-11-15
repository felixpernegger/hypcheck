/-!
Hand resolution of the 176 hypotheses in `Init.Data.String.Lemmas.Pattern.TakeDrop.Basic` that
`HypCheck.lean` left unresolved (cluster `PatTakeDrop`: `LawfulForwardPatternModel`,
`LawfulBackwardPatternModel`, `StrictPatternModel`, `LawfulForwardPattern`, `LawfulBackwardPattern`
and four explicit hypotheses). For each hypothesis `hᵢ` of theorem `T`, this file proves either `T'`
(the theorem without `hᵢ`: removable) or `¬T'` (necessary). None of them is dependent. All 176 are
decided: 160 necessary, 16 removable. The declarations below the models are generated from the
library statements with the binder dropped (see `runs/hand4/scratch_PatTakeDrop/gen/`).

Removable (none derivable from the other hypotheses; the conclusion simply holds without them):
* `[LawfulForward/BackwardPatternModel pat]` in `skip?_startPos`, `revSkip?_endPos`,
  `Slice.Pos.le_skipWhile`, `Slice.Pos.revSkipWhile_le`, `String.Pos.le_skipWhile`,
  `String.Pos.revSkipWhile_le`, and in `dropWhile_dropWhile`, `isEmpty_takeWhile_dropWhile`,
  `dropEndWhile_dropEndWhile`, `isEmpty_takeEndWhile_dropEndWhile` (Slice and String versions):
  these hold for every `ForwardPattern`/`BackwardPattern`. `skipWhile` only ever moves forward, and
  where it stops the pattern either fails or makes no progress; restarting on the remainder
  `s.sliceFrom q` asks `skipPrefix?` of the same slice (`sliceFrom_startPos`), so it stops at once.
* `[StrictPatternModel pat]` in `Pattern.Model.Pos.skipWhile_eq` and `Pos.revSkipWhile_eq`:
  strictness only excludes an empty longest match, and with one both sides are `pos`.

Models (all on `ρ := X` with `pat := X.p` for a one-constructor type `X`, with real instances, so the
remaining instance arguments are found by instance search; each has both a `ForwardPattern` and a
`BackwardPattern` instance, the backward one mirroring the forward one):
* `EndT`: skips everything (`skipPrefix? s = some s.endPos`, `skipSuffix? s = some s.startPos`),
  every string matches. Lawful (`LawfulForward/BackwardPatternModel`) but not strict: refutes the
  `StrictPatternModel` hypotheses through the empty match at the end.
* `NoneF`: never skips, nothing matches. Lawful and strict.
* `EndF`: skips everything, nothing matches (strict, not lawful: implementation and model disagree).
* `EndSW`: like `EndF`, but `startsWith`/`endsWith` return `false` (violates
  `LawfulForward/BackwardPattern`).
* `NoneT`: never skips, every string matches (not lawful).
* `NoneSW`: never skips, but `startsWith`/`endsWith` return `true`; nothing matches (strict).
* `NoneNE`: never skips, nonempty strings match (strict, not lawful).
* `StrA`: skips everything iff the underlying string `s.str` is `"a"`; nothing matches. Not uniform:
  `"a".toSlice` and the prefix `tA` of `"ab"` have the same copy but behave differently, which
  refutes the `*_congr`, `*_cast` and `*_copy` lemmas without lawfulness.
* `Step1`: skips one character iff the slice is `"ab"`; nothing matches. After `takeWhile` on `"ab"`
  the prefix `"a"` no longer matches, which refutes `takeWhile_takeWhile`, `all_takeWhile`,
  `isEmpty_dropWhile_takeWhile` and their backward/String versions without lawfulness.

Run with the lean4 repo's stage1 binary: `lean checks/PatTakeDropHand.lean`.
-/

set_option linter.unusedVariables false

namespace PatTakeDropHand

open String String.Slice String.Slice.Pattern String.Slice.Pattern.Model

/-! ## Models -/

/-- Skips everything; every string matches (lawful, not strict). -/
inductive EndT | p
/-- Skips everything; nothing matches. -/
inductive EndF | p
/-- Skips everything but `startsWith`/`endsWith` say `false`; nothing matches. -/
inductive EndSW | p
/-- Never skips; nothing matches (lawful, strict). -/
inductive NoneF | p
/-- Never skips; every string matches. -/
inductive NoneT | p
/-- Never skips but `startsWith`/`endsWith` say `true`; nothing matches. -/
inductive NoneSW | p
/-- Never skips; nonempty strings match (strict). -/
inductive NoneNE | p
/-- Skips everything iff the underlying string is `"a"`; nothing matches. -/
inductive StrA | p
/-- Skips one character iff the slice is `"ab"`; nothing matches. -/
inductive Step1 | p

instance : ForwardPattern EndT.p := { skipPrefix? := fun s => some s.endPos }
instance : ForwardPattern EndF.p := { skipPrefix? := fun s => some s.endPos }
instance : ForwardPattern EndSW.p := { skipPrefix? := fun s => some s.endPos, startsWith := fun _ => false }
instance : ForwardPattern NoneF.p := { skipPrefix? := fun _ => none }
instance : ForwardPattern NoneT.p := { skipPrefix? := fun _ => none }
instance : ForwardPattern NoneSW.p := { skipPrefix? := fun _ => none, startsWith := fun _ => true }
instance : ForwardPattern NoneNE.p := { skipPrefix? := fun _ => none }
instance : ForwardPattern StrA.p := { skipPrefix? := fun s => if s.str = "a" then some s.endPos else none }
instance : ForwardPattern Step1.p :=
  { skipPrefix? := fun s => if s.copy = "ab" then some (s.startPos.nextn 1) else none }


instance : BackwardPattern EndT.p := { skipSuffix? := fun s => some s.startPos }
instance : BackwardPattern EndF.p := { skipSuffix? := fun s => some s.startPos }
instance : BackwardPattern EndSW.p := { skipSuffix? := fun s => some s.startPos, endsWith := fun _ => false }
instance : BackwardPattern NoneF.p := { skipSuffix? := fun _ => none }
instance : BackwardPattern NoneT.p := { skipSuffix? := fun _ => none }
instance : BackwardPattern NoneSW.p := { skipSuffix? := fun _ => none, endsWith := fun _ => true }
instance : BackwardPattern NoneNE.p := { skipSuffix? := fun _ => none }
instance : BackwardPattern StrA.p := { skipSuffix? := fun s => if s.str = "a" then some s.startPos else none }
instance : BackwardPattern Step1.p :=
  { skipSuffix? := fun s => if s.copy = "ab" then some (s.startPos.nextn 1) else none }

instance : PatternModel EndT.p := ⟨fun _ => True⟩
instance : PatternModel EndF.p := ⟨fun _ => False⟩
instance : PatternModel EndSW.p := ⟨fun _ => False⟩
instance : PatternModel NoneF.p := ⟨fun _ => False⟩
instance : PatternModel NoneT.p := ⟨fun _ => True⟩
instance : PatternModel NoneSW.p := ⟨fun _ => False⟩
instance : PatternModel NoneNE.p := ⟨fun t => t ≠ ""⟩
instance : PatternModel StrA.p := ⟨fun _ => False⟩
instance : PatternModel Step1.p := ⟨fun _ => False⟩

instance : StrictPatternModel EndF.p := ⟨fun h => h⟩
instance : StrictPatternModel EndSW.p := ⟨fun h => h⟩
instance : StrictPatternModel NoneF.p := ⟨fun h => h⟩
instance : StrictPatternModel NoneSW.p := ⟨fun h => h⟩
instance : StrictPatternModel NoneNE.p := ⟨fun h => h rfl⟩
instance : StrictPatternModel StrA.p := ⟨fun h => h⟩
instance : StrictPatternModel Step1.p := ⟨fun h => h⟩

def sA : Slice := "a".toSlice
def tA : Slice := ⟨"ab", "ab".startPos, ⟨⟨1⟩, by decide⟩, by decide⟩
def sAB : Slice := "ab".toSlice
theorem hst : sA.copy = tA.copy := by decide
theorem sA_ne : sA.startPos ≠ sA.endPos := by decide

/-! ### Generic facts -/

section
variable {ρ : Type} {pat : ρ}

theorem not_isMatch [PatternModel pat] (hM : ∀ t, ¬ PatternModel.Matches pat t) {s : Slice} {p : s.Pos} :
    ¬ IsMatch pat p := fun h => hM _ h.matches_copy
theorem not_ilma [PatternModel pat] (hM : ∀ t, ¬ PatternModel.Matches pat t) {s : Slice} {p q : s.Pos} :
    ¬ IsLongestMatchAt pat p q := fun h => not_isMatch hM h.isLongestMatch_sliceFrom.isMatch
theorem not_matchesAt [PatternModel pat] (hM : ∀ t, ¬ PatternModel.Matches pat t) {s : Slice} {p : s.Pos} :
    ¬ MatchesAt pat p := fun ⟨⟨_, h⟩⟩ => not_ilma hM h
theorem chain_eq [PatternModel pat] (hM : ∀ t, ¬ PatternModel.Matches pat t) {s : Slice} {p q : s.Pos}
    (h : IsLongestMatchAtChain pat p q) : p = q := by
  cases h with
  | nil => rfl
  | cons _ _ _ h _ => exact (not_ilma hM h).elim
theorem matchesAt_all [PatternModel pat] (hM : ∀ t, PatternModel.Matches pat t) {s : Slice} (p : s.Pos) :
    MatchesAt pat p :=
  matchesAt_iff_exists_isMatch.2 ⟨p, Std.le_refl _, ⟨hM _⟩⟩

variable [ForwardPattern pat]

theorem sw_none {s : Slice} {pos : s.Pos} (h : pos.skip? pat = none) : pos.skipWhile pat = pos := by
  rw [Slice.Pos.skipWhile, h]
theorem sw_lt {s : Slice} {pos q : s.Pos} (h : pos.skip? pat = some q) (hl : pos < q) :
    pos.skipWhile pat = q.skipWhile pat := by
  rw [Slice.Pos.skipWhile, h]; simp [hl]
theorem sw_nlt {s : Slice} {pos q : s.Pos} (h : pos.skip? pat = some q) (hl : ¬ pos < q) :
    pos.skipWhile pat = pos := by
  rw [Slice.Pos.skipWhile, h]; simp [hl]

theorem sw_end {s : Slice}
    (hF : ∀ p : s.Pos, (s.sliceFrom p).skipPrefix? pat = some (s.sliceFrom p).endPos)
    (pos : s.Pos) : pos.skipWhile pat = s.endPos := by
  have hs : ∀ p : s.Pos, p.skip? pat = some s.endPos := fun p => by
    simp [Slice.Pos.skip?_eq_map_skipPrefix?, hF]
  by_cases hl : pos < s.endPos
  · rw [sw_lt (hs pos) hl, sw_nlt (hs _) (Std.lt_irrefl)]
  · rw [sw_nlt (hs pos) hl]
    exact Std.le_antisymm (Slice.Pos.le_endPos pos) (Std.not_lt.1 hl)

theorem sw_stay {s : Slice} {pos : s.Pos} (hF : (s.sliceFrom pos).skipPrefix? pat = none) :
    pos.skipWhile pat = pos :=
  sw_none (by simp [Slice.Pos.skip?_eq_map_skipPrefix?, hF])

/-- `skip?_startPos` holds for every pattern. -/
theorem skip?_startPos_gen {s : Slice} : s.startPos.skip? pat = s.skipPrefix? pat := by
  have key : ∀ (u : Slice) (hu : u = s) (f : u.Pos → s.Pos) (hf : ∀ x, (f x).offset = x.offset),
      (u.skipPrefix? pat).map f = s.skipPrefix? pat := by
    intro u hu f hf
    subst hu
    have : f = id := funext fun x => Slice.Pos.ext (hf x)
    simp [this]
  exact key _ Slice.sliceFrom_startPos _ (fun x => by simp [Slice.Pos.offset_ofSliceFrom])

theorem le_skipWhile_gen {s : Slice} (pos : s.Pos) : pos ≤ pos.skipWhile pat := by
  fun_induction Slice.Pos.skipWhile with
  | case1 pos q h₁ h₂ ih => exact Std.le_trans (Std.le_of_lt h₂) ih
  | case2 => exact Std.le_refl _
  | case3 => exact Std.le_refl _

end

/-! ### Facts about the forward models -/

theorem EndT_law : LawfulForwardPatternModel EndT.p where
  skipPrefixOfNonempty?_eq _ := rfl
  startsWith_eq _ := rfl
  skipPrefix?_eq_some_iff {s} pos := by
    show some s.endPos = some pos ↔ _
    constructor
    · rintro ⟨⟩
      exact ⟨⟨trivial⟩, fun p hp => absurd hp (Std.not_lt.2 (Slice.Pos.le_endPos p))⟩
    · intro h
      congr
      apply Std.le_antisymm _ (Slice.Pos.le_endPos pos)
      apply Std.not_lt.1
      intro hl
      exact h.not_isMatch s.endPos hl ⟨trivial⟩
instance : LawfulForwardPatternModel EndT.p := EndT_law

instance : LawfulForwardPatternModel NoneF.p where
  skipPrefixOfNonempty?_eq _ := rfl
  startsWith_eq _ := rfl
  skipPrefix?_eq_some_iff {s} pos := ⟨(fun h => nomatch (show (none : Option s.Pos) = some pos from h)), fun h => (not_isMatch (fun _ h => h) h.isMatch).elim⟩

theorem EndT_ilma {s : Slice} (p : s.Pos) : IsLongestMatchAt EndT.p p s.endPos :=
  Pattern.Model.Pos.skip?_eq_some_iff.1 (by simp [Slice.Pos.skip?_eq_map_skipPrefix?]; exact ⟨_, rfl, by simp⟩)


theorem EndF_sw {s : Slice} (pos : s.Pos) : pos.skipWhile EndF.p = s.endPos := sw_end (fun _ => rfl) pos
theorem EndSW_sw {s : Slice} (pos : s.Pos) : pos.skipWhile EndSW.p = s.endPos := sw_end (fun _ => rfl) pos
theorem EndT_sw {s : Slice} (pos : s.Pos) : pos.skipWhile EndT.p = s.endPos := sw_end (fun _ => rfl) pos
theorem NoneF_sw {s : Slice} (pos : s.Pos) : pos.skipWhile NoneF.p = pos := sw_stay rfl
theorem NoneT_sw {s : Slice} (pos : s.Pos) : pos.skipWhile NoneT.p = pos := sw_stay rfl
theorem NoneSW_sw {s : Slice} (pos : s.Pos) : pos.skipWhile NoneSW.p = pos := sw_stay rfl
theorem NoneNE_sw {s : Slice} (pos : s.Pos) : pos.skipWhile NoneNE.p = pos := sw_stay rfl
theorem StrA_sw_a {s : Slice} (h : s.str = "a") (pos : s.Pos) : pos.skipWhile StrA.p = s.endPos :=
  sw_end (fun p => by show (if s.str = "a" then _ else _) = _; simp [h]) pos
theorem StrA_sw_n {s : Slice} (h : s.str ≠ "a") (pos : s.Pos) : pos.skipWhile StrA.p = pos :=
  sw_stay (by show (if s.str = "a" then _ else _) = _; simp [h])
theorem EndT_ilma_eq {s : Slice} {p q : s.Pos} (h : IsLongestMatchAt EndT.p p q) : q = s.endPos :=
  h.eq (EndT_ilma p)
theorem NoneNE_matchesAt_sA : MatchesAt NoneNE.p sA.startPos :=
  matchesAt_iff_exists_isMatch.2 ⟨sA.endPos, Slice.Pos.le_endPos _, ⟨by show _ ≠ ""; decide⟩⟩

/-- `"ab"`, `Step1`: `skipWhile` from the start stops after one character. -/
theorem Step1_sw : sAB.startPos.skipWhile Step1.p = sAB.startPos.nextn 1 := by
  rw [sw_lt (q := sAB.startPos.nextn 1) (by decide) (by decide), sw_none (by decide)]

/-! ### Generic facts (backward) -/

section
variable {ρ : Type} {pat : ρ}

theorem not_isRevMatch [PatternModel pat] (hM : ∀ t, ¬ PatternModel.Matches pat t) {s : Slice} {p : s.Pos} :
    ¬ IsRevMatch pat p := fun h => hM _ h.matches_copy
theorem not_ilrma [PatternModel pat] (hM : ∀ t, ¬ PatternModel.Matches pat t) {s : Slice} {p q : s.Pos} :
    ¬ IsLongestRevMatchAt pat p q := fun h => not_isRevMatch hM h.isLongestRevMatch_sliceTo.isRevMatch
theorem not_revMatchesAt [PatternModel pat] (hM : ∀ t, ¬ PatternModel.Matches pat t) {s : Slice} {p : s.Pos} :
    ¬ RevMatchesAt pat p := fun ⟨⟨_, h⟩⟩ => not_ilrma hM h
theorem rchain_eq [PatternModel pat] (hM : ∀ t, ¬ PatternModel.Matches pat t) {s : Slice} {p q : s.Pos}
    (h : IsLongestRevMatchAtChain pat p q) : p = q := by
  cases h with
  | nil => rfl
  | cons _ _ _ h => exact (not_ilrma hM h).elim
theorem revMatchesAt_all [PatternModel pat] (hM : ∀ t, PatternModel.Matches pat t) {s : Slice} (p : s.Pos) :
    RevMatchesAt pat p :=
  revMatchesAt_iff_exists_isRevMatch.2 ⟨p, Std.le_refl _, ⟨hM _⟩⟩

variable [BackwardPattern pat]

theorem rsw_none {s : Slice} {pos : s.Pos} (h : pos.revSkip? pat = none) : pos.revSkipWhile pat = pos := by
  rw [Slice.Pos.revSkipWhile, h]
theorem rsw_lt {s : Slice} {pos q : s.Pos} (h : pos.revSkip? pat = some q) (hl : q < pos) :
    pos.revSkipWhile pat = q.revSkipWhile pat := by
  rw [Slice.Pos.revSkipWhile, h]; simp [hl]
theorem rsw_nlt {s : Slice} {pos q : s.Pos} (h : pos.revSkip? pat = some q) (hl : ¬ q < pos) :
    pos.revSkipWhile pat = pos := by
  rw [Slice.Pos.revSkipWhile, h]; simp [hl]

theorem rsw_start {s : Slice}
    (hF : ∀ p : s.Pos, (s.sliceTo p).skipSuffix? pat = some (s.sliceTo p).startPos)
    (pos : s.Pos) : pos.revSkipWhile pat = s.startPos := by
  have hs : ∀ p : s.Pos, p.revSkip? pat = some s.startPos := fun p => by
    simp [Slice.Pos.revSkip?_eq_map_skipSuffix?, hF]
  by_cases hl : s.startPos < pos
  · rw [rsw_lt (hs pos) hl, rsw_nlt (hs _) (Std.lt_irrefl)]
  · rw [rsw_nlt (hs pos) hl]
    exact Std.le_antisymm (Std.not_lt.1 hl) (Slice.Pos.startPos_le pos)

theorem rsw_stay {s : Slice} {pos : s.Pos} (hF : (s.sliceTo pos).skipSuffix? pat = none) :
    pos.revSkipWhile pat = pos :=
  rsw_none (by simp [Slice.Pos.revSkip?_eq_map_skipSuffix?, hF])

/-- `revSkip?_endPos` holds for every pattern. -/
theorem revSkip?_endPos_gen {s : Slice} : s.endPos.revSkip? pat = s.skipSuffix? pat := by
  have key : ∀ (u : Slice) (hu : u = s) (f : u.Pos → s.Pos) (hf : ∀ x, (f x).offset = x.offset),
      (u.skipSuffix? pat).map f = s.skipSuffix? pat := by
    intro u hu f hf
    subst hu
    have : f = id := funext fun x => Slice.Pos.ext (hf x)
    simp [this]
  exact key _ Slice.sliceTo_endPos _ (fun x => by simp [Slice.Pos.offset_ofSliceTo])

theorem revSkipWhile_le_gen {s : Slice} (pos : s.Pos) : pos.revSkipWhile pat ≤ pos := by
  fun_induction Slice.Pos.revSkipWhile with
  | case1 pos q h₁ h₂ ih => exact Std.le_trans ih (Std.le_of_lt h₂)
  | case2 => exact Std.le_refl _
  | case3 => exact Std.le_refl _

end

theorem EndT_rlaw : LawfulBackwardPatternModel EndT.p where
  skipSuffixOfNonempty?_eq _ := rfl
  endsWith_eq _ := rfl
  skipSuffix?_eq_some_iff {s} pos := by
    show some s.startPos = some pos ↔ _
    constructor
    · rintro ⟨⟩
      exact ⟨⟨trivial⟩, fun p hp => absurd hp (Std.not_lt.2 (Slice.Pos.startPos_le p))⟩
    · intro h
      congr
      apply Std.le_antisymm (Slice.Pos.startPos_le pos)
      apply Std.not_lt.1
      intro hl
      exact h.not_isRevMatch s.startPos hl ⟨trivial⟩
instance : LawfulBackwardPatternModel EndT.p := EndT_rlaw

instance : LawfulBackwardPatternModel NoneF.p where
  skipSuffixOfNonempty?_eq _ := rfl
  endsWith_eq _ := rfl
  skipSuffix?_eq_some_iff {s} pos :=
    ⟨(fun h => nomatch (show (none : Option s.Pos) = some pos from h)),
      fun h => (not_isRevMatch (fun _ h => h) h.isRevMatch).elim⟩

theorem EndT_ilrma {s : Slice} (p : s.Pos) : IsLongestRevMatchAt EndT.p s.startPos p :=
  Pattern.Model.Pos.revSkip?_eq_some_iff.1
    (by simp [Slice.Pos.revSkip?_eq_map_skipSuffix?]; exact ⟨_, rfl, by simp⟩)
theorem EndT_ilrma_eq {s : Slice} {p q : s.Pos} (h : IsLongestRevMatchAt EndT.p q p) : q = s.startPos :=
  h.eq (EndT_ilrma p)

theorem StrA_rsw_a {s : Slice} (h : s.str = "a") (pos : s.Pos) : pos.revSkipWhile StrA.p = s.startPos :=
  rsw_start (fun p => by show (if s.str = "a" then _ else _) = _; simp [h]) pos
theorem StrA_rsw_n {s : Slice} (h : s.str ≠ "a") (pos : s.Pos) : pos.revSkipWhile StrA.p = pos :=
  rsw_stay (by show (if s.str = "a" then _ else _) = _; simp [h])
theorem EndF_rsw {s : Slice} (pos : s.Pos) : pos.revSkipWhile EndF.p = s.startPos := rsw_start (fun _ => rfl) pos
theorem EndSW_rsw {s : Slice} (pos : s.Pos) : pos.revSkipWhile EndSW.p = s.startPos := rsw_start (fun _ => rfl) pos
theorem EndT_rsw {s : Slice} (pos : s.Pos) : pos.revSkipWhile EndT.p = s.startPos := rsw_start (fun _ => rfl) pos
theorem NoneF_rsw {s : Slice} (pos : s.Pos) : pos.revSkipWhile NoneF.p = pos := rsw_stay rfl
theorem NoneT_rsw {s : Slice} (pos : s.Pos) : pos.revSkipWhile NoneT.p = pos := rsw_stay rfl
theorem NoneSW_rsw {s : Slice} (pos : s.Pos) : pos.revSkipWhile NoneSW.p = pos := rsw_stay rfl
theorem NoneNE_rsw {s : Slice} (pos : s.Pos) : pos.revSkipWhile NoneNE.p = pos := rsw_stay rfl
theorem NoneNE_revMatchesAt_sA : RevMatchesAt NoneNE.p sA.endPos :=
  revMatchesAt_iff_exists_isRevMatch.2 ⟨sA.startPos, Slice.Pos.startPos_le _, ⟨by show _ ≠ ""; decide⟩⟩

theorem Step1_rsw : sAB.endPos.revSkipWhile Step1.p = sAB.startPos.nextn 1 := by
  rw [rsw_lt (q := sAB.startPos.nextn 1) (by decide) (by decide), rsw_none (by decide)]


/-! ### Idempotence of `skipWhile`/`revSkipWhile` for arbitrary patterns -/

section
variable {ρ : Type} {pat : ρ}

/-- Where `skipWhile` stops, the pattern either fails or makes no progress. -/
theorem sw_stop [ForwardPattern pat] {s : Slice} (pos : s.Pos) :
    (pos.skipWhile pat).skip? pat = none ∨
      ∃ r, (pos.skipWhile pat).skip? pat = some r ∧ ¬ pos.skipWhile pat < r := by
  fun_induction Slice.Pos.skipWhile with
  | case1 pos q h₁ h₂ ih => exact ih
  | case2 pos q h₁ h₂ => exact Or.inr ⟨q, h₁, h₂⟩
  | case3 pos h => exact Or.inl h

/-- Restarting `skipWhile` on the remainder after a stop position makes no progress. -/
theorem sw_sliceFrom_stop [ForwardPattern pat] {s : Slice} {q : s.Pos}
    (hq : q.skip? pat = none ∨ ∃ r, q.skip? pat = some r ∧ ¬ q < r) :
    (s.sliceFrom q).startPos.skipWhile pat = (s.sliceFrom q).startPos := by
  have e : q.skip? pat = ((s.sliceFrom q).skipPrefix? pat).map Slice.Pos.ofSliceFrom := rfl
  cases hx : (s.sliceFrom q).skipPrefix? pat with
  | none => exact sw_none (by rw [skip?_startPos_gen, hx])
  | some x =>
    rw [hx] at e
    refine sw_nlt (q := x) (by rw [skip?_startPos_gen, hx]) ?_
    rcases hq with hq | ⟨r, hr, hn⟩
    · rw [hq] at e; cases e
    · rw [hr] at e; cases e
      rw [← Slice.Pos.ofSliceFrom_lt_ofSliceFrom_iff, Slice.Pos.ofSliceFrom_startPos]
      exact hn

theorem dropWhile_dropWhile_gen [ForwardPattern pat] {s : Slice} :
    (s.dropWhile pat).dropWhile pat = s.dropWhile pat := by
  simp only [Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos]
  rw [sw_sliceFrom_stop (sw_stop _), Slice.sliceFrom_startPos]

theorem isEmpty_takeWhile_dropWhile_gen [ForwardPattern pat] {s : Slice} :
    ((s.dropWhile pat).takeWhile pat).isEmpty = true := by
  simp only [Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.takeWhile_eq_sliceTo_skipPrefixWhile,
    Slice.skipPrefixWhile_eq_skipWhile_startPos]
  rw [sw_sliceFrom_stop (sw_stop _)]
  simp

theorem rsw_stop [BackwardPattern pat] {s : Slice} (pos : s.Pos) :
    (pos.revSkipWhile pat).revSkip? pat = none ∨
      ∃ r, (pos.revSkipWhile pat).revSkip? pat = some r ∧ ¬ r < pos.revSkipWhile pat := by
  fun_induction Slice.Pos.revSkipWhile with
  | case1 pos q h₁ h₂ ih => exact ih
  | case2 pos q h₁ h₂ => exact Or.inr ⟨q, h₁, h₂⟩
  | case3 pos h => exact Or.inl h

theorem rsw_sliceTo_stop [BackwardPattern pat] {s : Slice} {q : s.Pos}
    (hq : q.revSkip? pat = none ∨ ∃ r, q.revSkip? pat = some r ∧ ¬ r < q) :
    (s.sliceTo q).endPos.revSkipWhile pat = (s.sliceTo q).endPos := by
  have e : q.revSkip? pat = ((s.sliceTo q).skipSuffix? pat).map Slice.Pos.ofSliceTo := rfl
  cases hx : (s.sliceTo q).skipSuffix? pat with
  | none => exact rsw_none (by rw [revSkip?_endPos_gen, hx])
  | some x =>
    rw [hx] at e
    refine rsw_nlt (q := x) (by rw [revSkip?_endPos_gen, hx]) ?_
    rcases hq with hq | ⟨r, hr, hn⟩
    · rw [hq] at e; cases e
    · rw [hr] at e; cases e
      rw [← Slice.Pos.ofSliceTo_lt_ofSliceTo_iff, Slice.Pos.ofSliceTo_endPos]
      exact hn

theorem dropEndWhile_dropEndWhile_gen [BackwardPattern pat] {s : Slice} :
    (s.dropEndWhile pat).dropEndWhile pat = s.dropEndWhile pat := by
  simp only [Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos]
  rw [rsw_sliceTo_stop (rsw_stop _), Slice.sliceTo_endPos]

theorem isEmpty_takeEndWhile_dropEndWhile_gen [BackwardPattern pat] {s : Slice} :
    ((s.dropEndWhile pat).takeEndWhile pat).isEmpty = true := by
  simp only [Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile,
    Slice.skipSuffixWhile_eq_revSkipWhile_endPos]
  rw [rsw_sliceTo_stop (rsw_stop _)]
  simp

end


/-! ### Models in which every string matches -/

section
variable {ρ : Type} {pat : ρ} [PatternModel pat]

theorem ilma_all (hM : ∀ t, PatternModel.Matches pat t) {s : Slice} (p : s.Pos) :
    IsLongestMatchAt pat p s.endPos := by
  letI : ForwardPattern pat := { skipPrefix? := fun s => some s.endPos }
  haveI : LawfulForwardPatternModel pat :=
    { skipPrefixOfNonempty?_eq := fun _ => rfl, startsWith_eq := fun _ => rfl
      skipPrefix?_eq_some_iff := fun {s} pos => by
        show some s.endPos = some pos ↔ _
        constructor
        · rintro ⟨⟩
          exact ⟨⟨hM _⟩, fun p hp => absurd hp (Std.not_lt.2 (Slice.Pos.le_endPos p))⟩
        · intro h
          congr
          apply Std.le_antisymm _ (Slice.Pos.le_endPos pos)
          apply Std.not_lt.1
          intro hl
          exact h.not_isMatch s.endPos hl ⟨hM _⟩ }
  exact Pattern.Model.Pos.skip?_eq_some_iff.1
    (by simp [Slice.Pos.skip?_eq_map_skipPrefix?]; exact ⟨_, rfl, by simp⟩)

theorem ilma_all_eq (hM : ∀ t, PatternModel.Matches pat t) {s : Slice} {p q : s.Pos}
    (h : IsLongestMatchAt pat p q) : q = s.endPos :=
  h.eq (ilma_all hM p)

theorem ilrma_all (hM : ∀ t, PatternModel.Matches pat t) {s : Slice} (p : s.Pos) :
    IsLongestRevMatchAt pat s.startPos p := by
  letI : BackwardPattern pat := { skipSuffix? := fun s => some s.startPos }
  haveI : LawfulBackwardPatternModel pat :=
    { skipSuffixOfNonempty?_eq := fun _ => rfl, endsWith_eq := fun _ => rfl
      skipSuffix?_eq_some_iff := fun {s} pos => by
        show some s.startPos = some pos ↔ _
        constructor
        · rintro ⟨⟩
          exact ⟨⟨hM _⟩, fun p hp => absurd hp (Std.not_lt.2 (Slice.Pos.startPos_le p))⟩
        · intro h
          congr
          apply Std.le_antisymm (Slice.Pos.startPos_le pos)
          apply Std.not_lt.1
          intro hl
          exact h.not_isRevMatch s.startPos hl ⟨hM _⟩ }
  exact Pattern.Model.Pos.revSkip?_eq_some_iff.1
    (by simp [Slice.Pos.revSkip?_eq_map_skipSuffix?]; exact ⟨_, rfl, by simp⟩)

theorem ilrma_all_eq (hM : ∀ t, PatternModel.Matches pat t) {s : Slice} {p q : s.Pos}
    (h : IsLongestRevMatchAt pat q p) : q = s.startPos :=
  h.eq (ilrma_all hM p)

end

def sE : Slice := "".toSlice
theorem sE_eq : sE.startPos = sE.endPos := by decide

end PatTakeDropHand


open String.Slice Pattern Model

namespace String.Slice.PTDHandS
open PatTakeDropHand

-- `String.Slice.Pattern.Model.skipPrefix?_eq_some_iff` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_skipPrefix?_eq_some_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice} {pos : s.Pos},
      s.skipPrefix? pat = some pos ↔ IsLongestMatch pat pos := by
  intro h
  exact not_isMatch (fun _ h => h) ((h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.endPos)).1 rfl).isMatch

-- `String.Slice.Pattern.Model.skipPrefix?_eq_none_iff` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_skipPrefix?_eq_none_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice},
      s.skipPrefix? pat = none ↔ ¬ MatchesAt pat s.startPos := by
  intro h
  exact absurd ((h (ρ := EndF) (pat := EndF.p) (s := sA)).2 (not_matchesAt (fun _ h => h))) (by decide)

-- `String.Slice.isSome_skipPrefix?` without `[LawfulForwardPattern pat]` (idx 3): necessary.
-- EndSW on "a": `skipPrefix?` returns `endPos` but `startsWith` is `false`
theorem isSome_skipPrefix?_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice},
      (s.skipPrefix? pat).isSome = s.startsWith pat := by
  intro h
  exact absurd (h (ρ := EndSW) (pat := EndSW.p) (s := sA)) (by decide)

-- `String.Slice.Pattern.Model.startsWith_eq_false_iff` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_startsWith_eq_false_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice},
      s.startsWith pat = false ↔ ¬ MatchesAt pat s.startPos := by
  intro h
  exact absurd ((h (ρ := EndF) (pat := EndF.p) (s := sA)).2 (not_matchesAt (fun _ h => h))) (by decide)

-- `String.Slice.Pattern.Model.startsWith_iff` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_startsWith_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice},
      s.startsWith pat = true ↔ MatchesAt pat s.startPos := by
  intro h
  exact not_matchesAt (fun _ h => h) ((h (ρ := EndF) (pat := EndF.p) (s := sA)).1 rfl)

-- `String.Slice.skipPrefix?_eq_none_iff` without `[LawfulForwardPattern pat]` (idx 3): necessary.
-- EndSW on "a": `skipPrefix?` returns `endPos` but `startsWith` is `false`
theorem skipPrefix?_eq_none_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice},
      s.skipPrefix? pat = none ↔ s.startsWith pat = false := by
  intro h
  exact absurd ((h (ρ := EndSW) (pat := EndSW.p) (s := sA)).2 rfl) (by decide)

-- `String.Slice.dropPrefix?_eq_none_iff` without `[LawfulForwardPattern pat]` (idx 3): necessary.
-- EndSW on "a": `skipPrefix?` returns `endPos` but `startsWith` is `false`
theorem dropPrefix?_eq_none_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice},
      s.dropPrefix? pat = none ↔ s.startsWith pat = false := by
  intro h
  exact absurd ((h (ρ := EndSW) (pat := EndSW.p) (s := sA)).2 rfl) (by decide)

-- `String.Slice.Pattern.Model.eq_append_of_dropPrefix?_eq_some` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_eq_append_of_dropPrefix?_eq_some_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s res : Slice} (h : s.dropPrefix? pat = some res),
      ∃ t, PatternModel.Matches pat t ∧ s.copy = t ++ res.copy := by
  intro h
  obtain ⟨_, ht, -⟩ := h (ρ := EndF) (pat := EndF.p) (s := sA) (res := sA.sliceFrom sA.endPos) rfl
  exact ht

-- `String.Slice.Pattern.Model.Pos.skip?_eq_some_iff` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_Pos_skip?_eq_some_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice} {pos res : s.Pos},
      pos.skip? pat = some res ↔ IsLongestMatchAt pat pos res := by
  intro h
  exact not_ilma (fun _ h => h) ((h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.startPos) (res := sA.endPos)).1 (by decide))

-- `String.Slice.Pattern.Model.Pos.skip?_eq_none_iff` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_Pos_skip?_eq_none_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice} {pos : s.Pos},
      pos.skip? pat = none ↔ ¬ MatchesAt pat pos := by
  intro h
  exact absurd ((h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.startPos)).2 (not_matchesAt (fun _ h => h))) (by decide)

-- `String.Slice.Pattern.Model.Pos.skip?_eq_matchAt?` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_Pos_skip?_eq_matchAt?_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice} {pos : s.Pos},
      pos.skip? pat = matchAt? pat pos := by
  intro h
  have := h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.startPos)
  rw [matchAt?_eq_none_iff.2 (not_matchesAt (fun _ h => h))] at this
  exact absurd this (by decide)

-- `String.Slice.skip?_startPos` without `[LawfulForwardPatternModel pat]` (idx 4): removable.
-- holds for every ForwardPattern: `s.sliceFrom s.startPos = s`, and `ofSliceFrom` from it preserves offsets (`skip?_startPos_gen`)
theorem skip?_startPos_h4 {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice} :
    s.startPos.skip? pat = s.skipPrefix? pat := by
  exact PatTakeDropHand.skip?_startPos_gen

-- `String.Slice.Pos.skip?_cast` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem Pos_skip?_cast_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos},
      (pos.cast hst).skip? pat = (pos.skip? pat).map (·.cast hst) := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) hst (pos := sA.startPos)) (by decide)

-- `String.Slice.Pos.skip?_congr` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem Pos_skip?_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos},
      pos.skip? pat = ((pos.cast hst).skip? pat).map (·.cast hst.symm) := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) hst (pos := sA.startPos)) (by decide)

-- `String.Slice.skipPrefix?_congr` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem skipPrefix?_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      s.skipPrefix? pat = (t.skipPrefix? pat).map (·.cast hst.symm) := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) hst) (by decide)

-- `String.Slice.startsWith_congr` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem startsWith_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      s.startsWith pat = t.startsWith pat := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) hst) (by decide)

-- `String.Slice.dropPrefix?_congr` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem dropPrefix?_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      (s.dropPrefix? pat).map String.Slice.copy = (t.dropPrefix? pat).map String.Slice.copy := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) hst) (by decide)

-- `String.Slice.Pattern.Model.Pos.skipWhile_eq` without `[StrictPatternModel pat]` (idx 3): removable.
-- the library proof uses strictness only to rule out an empty longest match; with an empty match at `pos` both sides are `pos` (`skipWhile` stops without progress, and `pos.skipWhile` again stops)
theorem Pattern_Model_Pos_skipWhile_eq_h3 {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.skipWhile pat = (matchAt? pat pos).elim pos (·.skipWhile pat) := by
  fun_induction Slice.Pos.skipWhile with
  | case1 pos q h₁ h₂ ih =>
    rw [Pattern.Model.Pos.skip?_eq_matchAt?] at h₁
    simp [h₁]
  | case2 pos q h₁ h₂ =>
    have hq : IsLongestMatchAt pat pos q := Pattern.Model.Pos.skip?_eq_some_iff.1 h₁
    obtain rfl : pos = q := Std.le_antisymm hq.le (Std.not_lt.1 h₂)
    rw [matchAt?_eq_some_iff.2 hq]
    exact (PatTakeDropHand.sw_nlt h₁ h₂).symm
  | case3 pos h =>
    rw [Pattern.Model.Pos.skip?_eq_matchAt?] at h
    simp [h]

-- `String.Slice.Pattern.Model.Pos.skipWhile_eq` without `[LawfulForwardPatternModel pat]` (idx 5): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_Pos_skipWhile_eq_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat] {s : Slice} {pos : s.Pos},
      pos.skipWhile pat = (matchAt? pat pos).elim pos (·.skipWhile pat) := by
  intro h
  have := h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.startPos)
  rw [EndF_sw, matchAt?_eq_none_iff.2 (not_matchesAt (fun _ h => h))] at this
  exact sA_ne this.symm

-- `String.Slice.Pos.skipWhile_cast` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem Pos_skipWhile_cast_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos},
      (pos.cast hst).skipWhile pat = (pos.skipWhile pat).cast hst := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) hst (pos := sA.startPos)
  rw [StrA_sw_n (s := tA) (by decide), StrA_sw_a (s := sA) rfl] at this
  exact absurd this (by decide)

-- `String.Slice.Pos.skipWhile_congr` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem Pos_skipWhile_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos},
      pos.skipWhile pat = ((pos.cast hst).skipWhile pat).cast hst.symm := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) hst (pos := sA.startPos)
  rw [StrA_sw_n (s := tA) (by decide), StrA_sw_a (s := sA) rfl] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.Pos.skipWhile_eq_self` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_Pos_skipWhile_eq_self_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice} {pos : s.Pos} (h : ¬ MatchesAt pat pos),
      pos.skipWhile pat = pos := by
  intro h
  have := h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.startPos) (not_matchesAt (fun _ h => h))
  rw [EndF_sw] at this
  exact sA_ne this.symm

-- `String.Slice.Pattern.Model.Pos.skipWhile_eq_self` without `(h : ¬ MatchesAt pat pos)` (idx 7): necessary.
-- lawful EndT on "a": `skipWhile` moves from `startPos` to `endPos`
theorem Pattern_Model_Pos_skipWhile_eq_self_h7 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos},
      pos.skipWhile pat = pos := by
  intro h
  have := h (ρ := EndT) (pat := EndT.p) (s := sA) (pos := sA.startPos)
  rw [EndT_sw] at this
  exact sA_ne this.symm

-- `String.Slice.Pattern.Model.Pos.skipWhile_eq_iff` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_Pos_skipWhile_eq_iff_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [ForwardPattern pat] {s : Slice} (startPos endPos : s.Pos),
      startPos.skipWhile pat = endPos ↔ IsLongestMatchAtChain pat startPos endPos ∧
      (¬MatchesAt pat endPos ∨ IsLongestMatchAt pat endPos endPos) := by
  intro h
  exact sA_ne (chain_eq (fun _ h => h) ((h (ρ := EndF) EndF.p (s := sA) sA.startPos sA.endPos).1 (EndF_sw _)).1)

-- `String.Slice.Pattern.Model.Pos.isLongestMatchAtChain_skipWhile` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_Pos_isLongestMatchAtChain_skipWhile_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [ForwardPattern pat] {s : Slice} (pos : s.Pos),
      IsLongestMatchAtChain pat pos (pos.skipWhile pat) := by
  intro h
  have := h (ρ := EndF) EndF.p (s := sA) sA.startPos
  rw [EndF_sw] at this
  exact sA_ne (chain_eq (fun _ h => h) this)

-- `String.Slice.Pattern.Model.Pos.not_matchesAt_or_isLongestMatchAt_skipWhile` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- NoneT on "a": never skips, every string matches, so `startPos` has the longest match up to `endPos`
theorem Pattern_Model_Pos_not_matchesAt_or_isLongestMatchAt_skipWhile_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [ForwardPattern pat] {s : Slice} (pos : s.Pos),
      ¬ MatchesAt pat (pos.skipWhile pat) ∨ IsLongestMatchAt pat (pos.skipWhile pat) (pos.skipWhile pat) := by
  intro h
  have := h (ρ := NoneT) NoneT.p (s := sA) sA.startPos
  rw [NoneT_sw] at this
  rcases this with h1 | h1
  · exact h1 (matchesAt_all (fun _ => trivial) _)
  · exact sA_ne (ilma_all_eq (fun _ => trivial) h1)

-- `String.Slice.Pattern.Model.Pos.not_matchesAt_skipWhile` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT (skip everything, every string matches): the empty match at the end
theorem Pattern_Model_Pos_not_matchesAt_skipWhile_h3 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} (pos : s.Pos),
      ¬MatchesAt pat (pos.skipWhile pat) := by
  intro h
  exact h (ρ := EndT) EndT.p (s := sA) sA.startPos (matchesAt_all (fun _ => trivial) _)

-- `String.Slice.Pattern.Model.Pos.not_matchesAt_skipWhile` without `[LawfulForwardPatternModel pat]` (idx 5): necessary.
-- strict model NoneNE (nonempty strings match) with a pattern that never skips, on "a"
theorem Pattern_Model_Pos_not_matchesAt_skipWhile_h5 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat] {s : Slice} (pos : s.Pos),
      ¬MatchesAt pat (pos.skipWhile pat) := by
  intro h
  have := h (ρ := NoneNE) NoneNE.p (s := sA) sA.startPos
  rw [NoneNE_sw] at this
  exact this NoneNE_matchesAt_sA

-- `String.Slice.Pattern.Model.Pos.skipWhile_eq_self_iff` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT (skip everything, every string matches): the empty match at the end
theorem Pattern_Model_Pos_skipWhile_eq_self_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos},
      pos.skipWhile pat = pos ↔ ¬MatchesAt pat pos := by
  intro h
  exact (h (ρ := EndT) (pat := EndT.p) (s := sA) (pos := sA.endPos)).1 (EndT_sw _) (matchesAt_all (fun _ => trivial) _)

-- `String.Slice.Pattern.Model.Pos.skipWhile_eq_self_iff` without `[LawfulForwardPatternModel pat]` (idx 5): necessary.
-- strict model NoneNE (nonempty strings match) with a pattern that never skips, on "a"
theorem Pattern_Model_Pos_skipWhile_eq_self_iff_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat] {s : Slice} {pos : s.Pos},
      pos.skipWhile pat = pos ↔ ¬MatchesAt pat pos := by
  intro h
  exact (h (ρ := NoneNE) (pat := NoneNE.p) (s := sA) (pos := sA.startPos)).1 (NoneNE_sw _) NoneNE_matchesAt_sA

-- `String.Slice.Pattern.Model.Pos.skipWhile_eq_self_iff_or` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_Pos_skipWhile_eq_self_iff_or_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice} {pos : s.Pos},
      pos.skipWhile pat = pos ↔ ¬MatchesAt pat pos ∨ IsLongestMatchAt pat pos pos := by
  intro h
  have := (h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.startPos)).2 (Or.inl (not_matchesAt (fun _ h => h)))
  rw [EndF_sw] at this
  exact sA_ne this.symm

-- `String.Slice.Pos.le_skipWhile` without `[LawfulForwardPatternModel pat]` (idx 4): removable.
-- holds for every ForwardPattern: `skipWhile` only moves to a strictly larger position (induction along `skipWhile`)
theorem Pos_le_skipWhile_h4 {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice} {pos : s.Pos} :
    pos ≤ pos.skipWhile pat := by
  exact PatTakeDropHand.le_skipWhile_gen _

-- `String.Slice.Pattern.Model.Pos.le_skipWhile_of_isLongestMatchAtChain` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- NoneT on "a": every string matches, so there is a chain from `startPos` to `endPos`, but the pattern never skips
theorem Pattern_Model_Pos_le_skipWhile_of_isLongestMatchAtChain_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [ForwardPattern pat] {s : Slice} {startPos endPos : s.Pos} (h : IsLongestMatchAtChain pat startPos endPos),
      endPos ≤ startPos.skipWhile pat := by
  intro h
  have := h (ρ := NoneT) NoneT.p (s := sA) (startPos := sA.startPos) (endPos := sA.endPos)
    (.cons _ _ _ (ilma_all (fun _ => trivial) _) (.nil _))
  rw [NoneT_sw] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.Pos.le_skipWhile_of_isLongestMatchAtChain` without `(h : IsLongestMatchAtChain pat startPos endPos)` (idx 8): necessary.
-- lawful strict NoneF (never skips, nothing matches) on "a", `endPos ≤ startPos` fails
theorem Pattern_Model_Pos_le_skipWhile_of_isLongestMatchAtChain_h8 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} {startPos endPos : s.Pos},
      endPos ≤ startPos.skipWhile pat := by
  intro h
  have := h (ρ := NoneF) NoneF.p (s := sA) (startPos := sA.startPos) (endPos := sA.endPos)
  rw [NoneF_sw] at this
  exact absurd this (by decide)

-- `String.Slice.cast_skipPrefixWhile` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem cast_skipPrefixWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      (s.skipPrefixWhile pat).cast hst = t.skipPrefixWhile pat := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) hst
  simp only [Slice.skipPrefixWhile_eq_skipWhile_startPos] at this
  rw [StrA_sw_n (s := tA) (by decide), StrA_sw_a (s := sA) rfl] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.skipPrefixWhile_eq_iff` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_skipPrefixWhile_eq_iff_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [ForwardPattern pat] (s : Slice) (res : s.Pos),
      s.skipPrefixWhile pat = res ↔ IsLongestMatchAtChain pat s.startPos res ∧
      (¬MatchesAt pat res ∨ IsLongestMatchAt pat res res) := by
  intro h
  exact sA_ne (chain_eq (fun _ h => h) ((h (ρ := EndF) EndF.p sA sA.endPos).1 (EndF_sw _)).1)

-- `String.Slice.Pattern.Model.isLongestMatchAtChain_skipPrefixWhile` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_isLongestMatchAtChain_skipPrefixWhile_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [ForwardPattern pat] (s : Slice),
      IsLongestMatchAtChain pat s.startPos (s.skipPrefixWhile pat) := by
  intro h
  have := h (ρ := EndF) EndF.p sA
  rw [Slice.skipPrefixWhile_eq_skipWhile_startPos, EndF_sw] at this
  exact sA_ne (chain_eq (fun _ h => h) this)

-- `String.Slice.Pattern.Model.not_matchesAt_or_isLongestMatchAt_skipPrefixWhile` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- NoneT on "a": never skips, every string matches, so `startPos` has the longest match up to `endPos`
theorem Pattern_Model_not_matchesAt_or_isLongestMatchAt_skipPrefixWhile_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [ForwardPattern pat] (s : Slice),
      ¬ MatchesAt pat (s.skipPrefixWhile pat) ∨ IsLongestMatchAt pat (s.skipPrefixWhile pat) (s.skipPrefixWhile pat) := by
  intro h
  have := h (ρ := NoneT) NoneT.p sA
  rw [Slice.skipPrefixWhile_eq_skipWhile_startPos, NoneT_sw] at this
  rcases this with h1 | h1
  · exact h1 (matchesAt_all (fun _ => trivial) _)
  · exact sA_ne (ilma_all_eq (fun _ => trivial) h1)

-- `String.Slice.Pattern.Model.not_matchesAt_skipPrefixWhile` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT (skip everything, every string matches): the empty match at the end
theorem Pattern_Model_not_matchesAt_skipPrefixWhile_h3 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] (s : Slice),
      ¬MatchesAt pat (s.skipPrefixWhile pat) := by
  intro h
  exact h (ρ := EndT) EndT.p sA (matchesAt_all (fun _ => trivial) _)

-- `String.Slice.Pattern.Model.not_matchesAt_skipPrefixWhile` without `[LawfulForwardPatternModel pat]` (idx 5): necessary.
-- strict model NoneNE (nonempty strings match) with a pattern that never skips, on "a"
theorem Pattern_Model_not_matchesAt_skipPrefixWhile_h5 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat] (s : Slice),
      ¬MatchesAt pat (s.skipPrefixWhile pat) := by
  intro h
  have := h (ρ := NoneNE) NoneNE.p sA
  rw [Slice.skipPrefixWhile_eq_skipWhile_startPos, NoneNE_sw] at this
  exact this NoneNE_matchesAt_sA

-- `String.Slice.skipPrefixWhile_eq_startPos` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndSW on "a": `skipPrefix?` returns `endPos` but `startsWith` is `false`
theorem skipPrefixWhile_eq_startPos_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice},
      s.startsWith pat = false → s.skipPrefixWhile pat = s.startPos := by
  intro h
  have := h (ρ := EndSW) (pat := EndSW.p) (s := sA) rfl
  rw [Slice.skipPrefixWhile_eq_skipWhile_startPos, EndSW_sw] at this
  exact sA_ne this.symm

-- `String.Slice.skipPrefixWhile_eq_startPos_iff` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT on "": `skipPrefixWhile` stays at `startPos` but `startsWith` is `true` (empty match)
theorem skipPrefixWhile_eq_startPos_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice},
      s.skipPrefixWhile pat = s.startPos ↔ s.startsWith pat = false := by
  intro h
  exact absurd ((h (ρ := EndT) (pat := EndT.p) (s := sE)).1 (by rw [Slice.skipPrefixWhile_eq_skipWhile_startPos, EndT_sw]; exact sE_eq.symm)) (by decide)

-- `String.Slice.skipPrefixWhile_eq_startPos_iff` without `[LawfulForwardPatternModel pat]` (idx 5): necessary.
-- NoneSW on "a": never skips but `startsWith` is `true`; model matches nothing (strict)
theorem skipPrefixWhile_eq_startPos_iff_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat] {s : Slice},
      s.skipPrefixWhile pat = s.startPos ↔ s.startsWith pat = false := by
  intro h
  exact absurd ((h (ρ := NoneSW) (pat := NoneSW.p) (s := sA)).1 (by rw [Slice.skipPrefixWhile_eq_skipWhile_startPos, NoneSW_sw])) (by decide)

-- `String.Slice.Pattern.Model.skipPrefixWhile_eq_startPos_iff_or` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_skipPrefixWhile_eq_startPos_iff_or_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice},
      s.skipPrefixWhile pat = s.startPos ↔ ¬MatchesAt pat s.startPos ∨ IsLongestMatch pat s.startPos := by
  intro h
  have := (h (ρ := EndF) (pat := EndF.p) (s := sA)).2 (Or.inl (not_matchesAt (fun _ h => h)))
  rw [Slice.skipPrefixWhile_eq_skipWhile_startPos, EndF_sw] at this
  exact sA_ne this.symm

-- `String.Slice.dropWhile_congr` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem dropWhile_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      (s.dropWhile pat).copy = (t.dropWhile pat).copy := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) hst
  simp only [Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos] at this
  rw [StrA_sw_n (s := tA) (by decide), StrA_sw_a (s := sA) rfl] at this
  exact absurd this (by decide)

-- `String.Slice.startsWith_dropWhile` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT: `startsWith` is always `true` (the empty remainder has an empty match)
theorem startsWith_dropWhile_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice},
      (s.dropWhile pat).startsWith pat = false := by
  intro h
  exact absurd (h (ρ := EndT) (pat := EndT.p) (s := sA)) (by decide)

-- `String.Slice.startsWith_dropWhile` without `[LawfulForwardPatternModel pat]` (idx 5): necessary.
-- NoneSW on "a": never skips but `startsWith` is `true`; model matches nothing (strict)
theorem startsWith_dropWhile_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat] {s : Slice},
      (s.dropWhile pat).startsWith pat = false := by
  intro h
  exact absurd (h (ρ := NoneSW) (pat := NoneSW.p) (s := sA)) (by decide)

-- `String.Slice.dropWhile_eq_self` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndSW on "a": `skipPrefix?` returns `endPos` but `startsWith` is `false`
theorem dropWhile_eq_self_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice} (h : s.startsWith pat = false),
      s.dropWhile pat = s := by
  intro h
  have := congrArg Slice.copy (h (ρ := EndSW) (pat := EndSW.p) (s := sA) rfl)
  rw [Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndSW_sw] at this
  exact absurd this (by decide)

-- `String.Slice.dropWhile_eq_self_iff` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT on "": `dropWhile` is the identity but `startsWith` is `true`
theorem dropWhile_eq_self_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice},
      s.dropWhile pat = s ↔ s.startsWith pat = false := by
  intro h
  have := (h (ρ := EndT) (pat := EndT.p) (s := sE)).1
    (by rw [Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndT_sw, ← sE_eq]; exact Slice.sliceFrom_startPos)
  exact absurd this (by decide)

-- `String.Slice.dropWhile_eq_self_iff` without `[LawfulForwardPatternModel pat]` (idx 5): necessary.
-- NoneSW on "a": never skips but `startsWith` is `true`; model matches nothing (strict)
theorem dropWhile_eq_self_iff_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat] {s : Slice},
      s.dropWhile pat = s ↔ s.startsWith pat = false := by
  intro h
  have := (h (ρ := NoneSW) (pat := NoneSW.p) (s := sA)).1
    (by rw [Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, NoneSW_sw]; exact Slice.sliceFrom_startPos)
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.dropWhile_eq_self_iff_or` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_dropWhile_eq_self_iff_or_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice},
      s.dropWhile pat = s ↔ ¬MatchesAt pat s.startPos ∨ IsLongestMatch pat s.startPos := by
  intro h
  have := congrArg Slice.copy ((h (ρ := EndF) (pat := EndF.p) (s := sA)).2 (Or.inl (not_matchesAt (fun _ h => h))))
  rw [Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndF_sw] at this
  exact absurd this (by decide)

-- `String.Slice.takeWhile_congr` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem takeWhile_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      (s.takeWhile pat).copy = (t.takeWhile pat).copy := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) hst
  simp only [Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos] at this
  rw [StrA_sw_n (s := tA) (by decide), StrA_sw_a (s := sA) rfl] at this
  exact absurd this (by decide)

-- `String.Slice.isEmpty_takeWhile_eq_true` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndSW on "a": `skipPrefix?` returns `endPos` but `startsWith` is `false`
theorem isEmpty_takeWhile_eq_true_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice} (h : s.startsWith pat = false),
      (s.takeWhile pat).isEmpty = true := by
  intro h
  have := h (ρ := EndSW) (pat := EndSW.p) (s := sA) rfl
  rw [Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndSW_sw] at this
  exact absurd this (by decide)

-- `String.Slice.isEmpty_takeWhile` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT on "": `takeWhile` is empty but `startsWith` is `true`
theorem isEmpty_takeWhile_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice},
      (s.takeWhile pat).isEmpty = !s.startsWith pat := by
  intro h
  have := h (ρ := EndT) (pat := EndT.p) (s := sE)
  rw [Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndT_sw] at this
  exact absurd this (by decide)

-- `String.Slice.isEmpty_takeWhile` without `[LawfulForwardPatternModel pat]` (idx 5): necessary.
-- EndSW on "a": `skipPrefix?` returns `endPos` but `startsWith` is `false` (model matches nothing, strict)
theorem isEmpty_takeWhile_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat] {s : Slice},
      (s.takeWhile pat).isEmpty = !s.startsWith pat := by
  intro h
  have := h (ρ := EndSW) (pat := EndSW.p) (s := sA)
  rw [Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndSW_sw] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.all_eq_true_iff` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipPrefix?` always returns `endPos`, the model matches nothing
theorem Pattern_Model_all_eq_true_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice},
      s.all pat ↔ IsLongestMatchAtChain pat s.startPos s.endPos := by
  intro h
  exact sA_ne (chain_eq (fun _ h => h) ((h (ρ := EndF) (pat := EndF.p) (s := sA)).1 (by rw [Slice.all_eq_skipPrefixWhile_beq, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndF_sw]; decide)))

-- `String.Slice.all_congr` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem all_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      s.all pat = t.all pat := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) hst
  simp only [Slice.all_eq_skipPrefixWhile_beq, Slice.skipPrefixWhile_eq_skipWhile_startPos] at this
  rw [StrA_sw_n (s := tA) (by decide), StrA_sw_a (s := sA) rfl] at this
  exact absurd this (by decide)

-- `String.Slice.all_takeWhile` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- Step1 on "ab": skips one character iff the slice is "ab", so a second pass over the prefix "a" makes no progress
theorem all_takeWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice},
      (s.takeWhile pat).all pat = true := by
  intro h
  have := h (ρ := Step1) (pat := Step1.p) (s := sAB)
  rw [Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, Step1_sw, Slice.all_eq_skipPrefixWhile_beq, Slice.skipPrefixWhile_eq_skipWhile_startPos, sw_none (by decide)] at this
  exact absurd this (by decide)

-- `String.Slice.dropWhile_dropWhile` without `[LawfulForwardPatternModel pat]` (idx 4): removable.
-- holds for every ForwardPattern: where `skipWhile` stops, the pattern fails or makes no progress, and restarting on the remainder sees the same `skipPrefix?` result (`sliceFrom_startPos`)
theorem dropWhile_dropWhile_h4 {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice} :
    (s.dropWhile pat).dropWhile pat = s.dropWhile pat := by
  exact PatTakeDropHand.dropWhile_dropWhile_gen

-- `String.Slice.takeWhile_takeWhile` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- Step1 on "ab": skips one character iff the slice is "ab", so a second pass over the prefix "a" makes no progress
theorem takeWhile_takeWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice},
      (s.takeWhile pat).takeWhile pat = s.takeWhile pat := by
  intro h
  have := congrArg Slice.copy (h (ρ := Step1) (pat := Step1.p) (s := sAB))
  simp only [Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos] at this
  rw [Step1_sw, sw_none (by decide)] at this
  exact absurd this (by decide)

-- `String.Slice.isEmpty_takeWhile_dropWhile` without `[LawfulForwardPatternModel pat]` (idx 4): removable.
-- holds for every ForwardPattern: restarting `skipWhile` on the remainder after `dropWhile` makes no progress (as for `dropWhile_dropWhile`)
theorem isEmpty_takeWhile_dropWhile_h4 {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice} :
    ((s.dropWhile pat).takeWhile pat).isEmpty = true := by
  exact PatTakeDropHand.isEmpty_takeWhile_dropWhile_gen

-- `String.Slice.isEmpty_dropWhile_takeWhile` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- Step1 on "ab": skips one character iff the slice is "ab", so a second pass over the prefix "a" makes no progress
theorem isEmpty_dropWhile_takeWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice},
      ((s.takeWhile pat).dropWhile pat).isEmpty = true := by
  intro h
  have := h (ρ := Step1) (pat := Step1.p) (s := sAB)
  rw [Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, Step1_sw, Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, sw_none (by decide)] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.skipSuffix?_eq_some_iff` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_skipSuffix?_eq_some_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice} {pos : s.Pos},
      s.skipSuffix? pat = some pos ↔ IsLongestRevMatch pat pos := by
  intro h
  exact not_isRevMatch (fun _ h => h) ((h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.startPos)).1 rfl).isRevMatch

-- `String.Slice.Pattern.Model.skipSuffix?_eq_none_iff` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_skipSuffix?_eq_none_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice},
      s.skipSuffix? pat = none ↔ ¬ RevMatchesAt pat s.endPos := by
  intro h
  exact absurd ((h (ρ := EndF) (pat := EndF.p) (s := sA)).2 (not_revMatchesAt (fun _ h => h))) (by decide)

-- `String.Slice.isSome_skipSuffix?` without `[LawfulBackwardPattern pat]` (idx 3): necessary.
-- EndSW on "a": `skipSuffix?` returns `startPos` but `endsWith` is `false`
theorem isSome_skipSuffix?_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice},
      (s.skipSuffix? pat).isSome = s.endsWith pat := by
  intro h
  exact absurd (h (ρ := EndSW) (pat := EndSW.p) (s := sA)) (by decide)

-- `String.Slice.Pattern.Model.endsWith_eq_false_iff` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_endsWith_eq_false_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice},
      s.endsWith pat = false ↔ ¬ RevMatchesAt pat s.endPos := by
  intro h
  exact absurd ((h (ρ := EndF) (pat := EndF.p) (s := sA)).2 (not_revMatchesAt (fun _ h => h))) (by decide)

-- `String.Slice.Pattern.Model.endsWith_iff` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_endsWith_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice},
      s.endsWith pat = true ↔ RevMatchesAt pat s.endPos := by
  intro h
  exact not_revMatchesAt (fun _ h => h) ((h (ρ := EndF) (pat := EndF.p) (s := sA)).1 rfl)

-- `String.Slice.skipSuffix?_eq_none_iff` without `[LawfulBackwardPattern pat]` (idx 3): necessary.
-- EndSW on "a": `skipSuffix?` returns `startPos` but `endsWith` is `false`
theorem skipSuffix?_eq_none_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice},
      s.skipSuffix? pat = none ↔ s.endsWith pat = false := by
  intro h
  exact absurd ((h (ρ := EndSW) (pat := EndSW.p) (s := sA)).2 rfl) (by decide)

-- `String.Slice.dropSuffix?_eq_none_iff` without `[LawfulBackwardPattern pat]` (idx 3): necessary.
-- EndSW on "a": `skipSuffix?` returns `startPos` but `endsWith` is `false`
theorem dropSuffix?_eq_none_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice},
      s.dropSuffix? pat = none ↔ s.endsWith pat = false := by
  intro h
  exact absurd ((h (ρ := EndSW) (pat := EndSW.p) (s := sA)).2 rfl) (by decide)

-- `String.Slice.Pattern.Model.eq_append_of_dropSuffix?_eq_some` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_eq_append_of_dropSuffix?_eq_some_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s res : Slice} (h : s.dropSuffix? pat = some res),
      ∃ t, PatternModel.Matches pat t ∧ s.copy = res.copy ++ t := by
  intro h
  obtain ⟨_, ht, -⟩ := h (ρ := EndF) (pat := EndF.p) (s := sA) (res := sA.sliceTo sA.startPos) rfl
  exact ht

-- `String.Slice.Pattern.Model.Pos.revSkip?_eq_some_iff` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_Pos_revSkip?_eq_some_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice} {pos res : s.Pos},
      pos.revSkip? pat = some res ↔ IsLongestRevMatchAt pat res pos := by
  intro h
  exact not_ilrma (fun _ h => h) ((h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.endPos) (res := sA.startPos)).1 (by decide))

-- `String.Slice.Pattern.Model.Pos.revSkip?_eq_none_iff` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_Pos_revSkip?_eq_none_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice} {pos : s.Pos},
      pos.revSkip? pat = none ↔ ¬ RevMatchesAt pat pos := by
  intro h
  exact absurd ((h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.endPos)).2 (not_revMatchesAt (fun _ h => h))) (by decide)

-- `String.Slice.Pattern.Model.Pos.revSkip?_eq_revMatchAt?` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_Pos_revSkip?_eq_revMatchAt?_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice} {pos : s.Pos},
      pos.revSkip? pat = revMatchAt? pat pos := by
  intro h
  have := h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.endPos)
  rw [revMatchAt?_eq_none_iff.2 (not_revMatchesAt (fun _ h => h))] at this
  exact absurd this (by decide)

-- `String.Slice.revSkip?_endPos` without `[LawfulBackwardPatternModel pat]` (idx 4): removable.
-- holds for every BackwardPattern: `s.sliceTo s.endPos = s`, and `ofSliceTo` preserves offsets (`revSkip?_endPos_gen`)
theorem revSkip?_endPos_h4 {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice} :
    s.endPos.revSkip? pat = s.skipSuffix? pat := by
  exact PatTakeDropHand.revSkip?_endPos_gen

-- `String.Slice.Pos.revSkip?_cast` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem Pos_revSkip?_cast_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos},
      (pos.cast hst).revSkip? pat = (pos.revSkip? pat).map (·.cast hst) := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) hst (pos := sA.endPos)) (by decide)

-- `String.Slice.Pos.revSkip?_congr` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem Pos_revSkip?_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos},
      pos.revSkip? pat = ((pos.cast hst).revSkip? pat).map (·.cast hst.symm) := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) hst (pos := sA.endPos)) (by decide)

-- `String.Slice.skipSuffix?_congr` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem skipSuffix?_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      s.skipSuffix? pat = (t.skipSuffix? pat).map (·.cast hst.symm) := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) hst) (by decide)

-- `String.Slice.endsWith_congr` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem endsWith_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      s.endsWith pat = t.endsWith pat := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) hst) (by decide)

-- `String.Slice.dropSuffix?_congr` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem dropSuffix?_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      (s.dropSuffix? pat).map String.Slice.copy = (t.dropSuffix? pat).map String.Slice.copy := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) hst) (by decide)

-- `String.Slice.Pattern.Model.Pos.revSkipWhile_eq` without `[StrictPatternModel pat]` (idx 3): removable.
-- mirror of `Pos.skipWhile_eq`: strictness only rules out an empty longest match, and with one both sides are `pos`
theorem Pattern_Model_Pos_revSkipWhile_eq_h3 {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.revSkipWhile pat = (revMatchAt? pat pos).elim pos (·.revSkipWhile pat) := by
  fun_induction Slice.Pos.revSkipWhile with
  | case1 pos q h₁ h₂ ih =>
    rw [Pattern.Model.Pos.revSkip?_eq_revMatchAt?] at h₁
    simp [h₁]
  | case2 pos q h₁ h₂ =>
    have hq : IsLongestRevMatchAt pat q pos := Pattern.Model.Pos.revSkip?_eq_some_iff.1 h₁
    obtain rfl : q = pos := Std.le_antisymm hq.le (Std.not_lt.1 h₂)
    rw [revMatchAt?_eq_some_iff.2 hq]
    exact (PatTakeDropHand.rsw_nlt h₁ h₂).symm
  | case3 pos h =>
    rw [Pattern.Model.Pos.revSkip?_eq_revMatchAt?] at h
    simp [h]

-- `String.Slice.Pattern.Model.Pos.revSkipWhile_eq` without `[LawfulBackwardPatternModel pat]` (idx 5): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_Pos_revSkipWhile_eq_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat] {s : Slice} {pos : s.Pos},
      pos.revSkipWhile pat = (revMatchAt? pat pos).elim pos (·.revSkipWhile pat) := by
  intro h
  have := h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.endPos)
  rw [EndF_rsw, revMatchAt?_eq_none_iff.2 (not_revMatchesAt (fun _ h => h))] at this
  exact sA_ne this

-- `String.Slice.Pos.revSkipWhile_cast` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem Pos_revSkipWhile_cast_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos},
      (pos.cast hst).revSkipWhile pat = (pos.revSkipWhile pat).cast hst := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) hst (pos := sA.endPos)
  rw [StrA_rsw_n (s := tA) (by decide), StrA_rsw_a (s := sA) rfl] at this
  exact absurd this (by decide)

-- `String.Slice.Pos.revSkipWhile_congr` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem Pos_revSkipWhile_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos},
      pos.revSkipWhile pat = ((pos.cast hst).revSkipWhile pat).cast hst.symm := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) hst (pos := sA.endPos)
  rw [StrA_rsw_n (s := tA) (by decide), StrA_rsw_a (s := sA) rfl] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.Pos.revSkipWhile_eq_self` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_Pos_revSkipWhile_eq_self_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice} {pos : s.Pos} (h : ¬ RevMatchesAt pat pos),
      pos.revSkipWhile pat = pos := by
  intro h
  have := h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.endPos) (not_revMatchesAt (fun _ h => h))
  rw [EndF_rsw] at this
  exact sA_ne this

-- `String.Slice.Pattern.Model.Pos.revSkipWhile_eq_self` without `(h : ¬ RevMatchesAt pat pos)` (idx 7): necessary.
-- lawful EndT on "a": `revSkipWhile` moves from `endPos` to `startPos`
theorem Pattern_Model_Pos_revSkipWhile_eq_self_h7 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos},
      pos.revSkipWhile pat = pos := by
  intro h
  have := h (ρ := EndT) (pat := EndT.p) (s := sA) (pos := sA.endPos)
  rw [EndT_rsw] at this
  exact sA_ne this

-- `String.Slice.Pattern.Model.Pos.revSkipWhile_eq_iff` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_Pos_revSkipWhile_eq_iff_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [BackwardPattern pat] {s : Slice} (startPos endPos : s.Pos),
      endPos.revSkipWhile pat = startPos ↔ IsLongestRevMatchAtChain pat startPos endPos ∧
      (¬RevMatchesAt pat startPos ∨ IsLongestRevMatchAt pat startPos startPos) := by
  intro h
  exact sA_ne (rchain_eq (fun _ h => h) ((h (ρ := EndF) EndF.p (s := sA) sA.startPos sA.endPos).1 (EndF_rsw _)).1)

-- `String.Slice.Pattern.Model.Pos.isLongestRevMatchAtChain_revSkipWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_Pos_isLongestRevMatchAtChain_revSkipWhile_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [BackwardPattern pat] {s : Slice} (pos : s.Pos),
      IsLongestRevMatchAtChain pat (pos.revSkipWhile pat) pos := by
  intro h
  have := h (ρ := EndF) EndF.p (s := sA) sA.endPos
  rw [EndF_rsw] at this
  exact sA_ne (rchain_eq (fun _ h => h) this)

-- `String.Slice.Pattern.Model.Pos.not_revMatchesAt_or_isLongestRevMatchAt_revSkipWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- NoneT on "a": never skips, every string matches, so `endPos` has the longest reverse match back to `startPos`
theorem Pattern_Model_Pos_not_revMatchesAt_or_isLongestRevMatchAt_revSkipWhile_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [BackwardPattern pat] {s : Slice} (pos : s.Pos),
      ¬ RevMatchesAt pat (pos.revSkipWhile pat) ∨ IsLongestRevMatchAt pat (pos.revSkipWhile pat) (pos.revSkipWhile pat) := by
  intro h
  have := h (ρ := NoneT) NoneT.p (s := sA) sA.endPos
  rw [NoneT_rsw] at this
  rcases this with h1 | h1
  · exact h1 (revMatchesAt_all (fun _ => trivial) _)
  · exact sA_ne (ilrma_all_eq (fun _ => trivial) h1).symm

-- `String.Slice.Pattern.Model.Pos.not_revMatchesAt_revSkipWhile` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT (skip everything, every string matches): the empty match at the start
theorem Pattern_Model_Pos_not_revMatchesAt_revSkipWhile_h3 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} (pos : s.Pos),
      ¬RevMatchesAt pat (pos.revSkipWhile pat) := by
  intro h
  exact h (ρ := EndT) EndT.p (s := sA) sA.endPos (revMatchesAt_all (fun _ => trivial) _)

-- `String.Slice.Pattern.Model.Pos.not_revMatchesAt_revSkipWhile` without `[LawfulBackwardPatternModel pat]` (idx 5): necessary.
-- strict model NoneNE (nonempty strings match) with a pattern that never skips, on "a"
theorem Pattern_Model_Pos_not_revMatchesAt_revSkipWhile_h5 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat] {s : Slice} (pos : s.Pos),
      ¬RevMatchesAt pat (pos.revSkipWhile pat) := by
  intro h
  have := h (ρ := NoneNE) NoneNE.p (s := sA) sA.endPos
  rw [NoneNE_rsw] at this
  exact this NoneNE_revMatchesAt_sA

-- `String.Slice.Pattern.Model.Pos.revSkipWhile_eq_self_iff` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT (skip everything, every string matches): the empty match at the start
theorem Pattern_Model_Pos_revSkipWhile_eq_self_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos},
      pos.revSkipWhile pat = pos ↔ ¬RevMatchesAt pat pos := by
  intro h
  exact (h (ρ := EndT) (pat := EndT.p) (s := sA) (pos := sA.startPos)).1 (EndT_rsw _) (revMatchesAt_all (fun _ => trivial) _)

-- `String.Slice.Pattern.Model.Pos.revSkipWhile_eq_self_iff` without `[LawfulBackwardPatternModel pat]` (idx 5): necessary.
-- strict model NoneNE (nonempty strings match) with a pattern that never skips, on "a"
theorem Pattern_Model_Pos_revSkipWhile_eq_self_iff_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat] {s : Slice} {pos : s.Pos},
      pos.revSkipWhile pat = pos ↔ ¬RevMatchesAt pat pos := by
  intro h
  exact (h (ρ := NoneNE) (pat := NoneNE.p) (s := sA) (pos := sA.endPos)).1 (NoneNE_rsw _) NoneNE_revMatchesAt_sA

-- `String.Slice.Pattern.Model.Pos.revSkipWhile_eq_self_iff_or` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_Pos_revSkipWhile_eq_self_iff_or_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice} {pos : s.Pos},
      pos.revSkipWhile pat = pos ↔ ¬RevMatchesAt pat pos ∨ IsLongestRevMatchAt pat pos pos := by
  intro h
  have := (h (ρ := EndF) (pat := EndF.p) (s := sA) (pos := sA.endPos)).2 (Or.inl (not_revMatchesAt (fun _ h => h)))
  rw [EndF_rsw] at this
  exact sA_ne this

-- `String.Slice.Pos.revSkipWhile_le` without `[LawfulBackwardPatternModel pat]` (idx 4): removable.
-- holds for every BackwardPattern: `revSkipWhile` only moves to a strictly smaller position
theorem Pos_revSkipWhile_le_h4 {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice} {pos : s.Pos} :
    pos.revSkipWhile pat ≤ pos := by
  exact PatTakeDropHand.revSkipWhile_le_gen _

-- `String.Slice.Pattern.Model.Pos.revSkipWhile_le_of_isLongestRevMatchAtChain` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- NoneT on "a": every string matches, so there is a reverse chain from `endPos` to `startPos`, but the pattern never skips
theorem Pattern_Model_Pos_revSkipWhile_le_of_isLongestRevMatchAtChain_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [BackwardPattern pat] {s : Slice} {startPos endPos : s.Pos} (h : IsLongestRevMatchAtChain pat startPos endPos),
      endPos.revSkipWhile pat ≤ startPos := by
  intro h
  have := h (ρ := NoneT) NoneT.p (s := sA) (startPos := sA.startPos) (endPos := sA.endPos)
    (.cons _ _ _ (.nil _) (ilrma_all (fun _ => trivial) _))
  rw [NoneT_rsw] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.Pos.revSkipWhile_le_of_isLongestRevMatchAtChain` without `(h : IsLongestRevMatchAtChain pat startPos endPos)` (idx 8): necessary.
-- lawful strict NoneF (never skips, nothing matches) on "a", `endPos ≤ startPos` fails
theorem Pattern_Model_Pos_revSkipWhile_le_of_isLongestRevMatchAtChain_h8 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} {startPos endPos : s.Pos},
      endPos.revSkipWhile pat ≤ startPos := by
  intro h
  have := h (ρ := NoneF) NoneF.p (s := sA) (startPos := sA.startPos) (endPos := sA.endPos)
  rw [NoneF_rsw] at this
  exact absurd this (by decide)

-- `String.Slice.cast_skipSuffixWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem cast_skipSuffixWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      (s.skipSuffixWhile pat).cast hst = t.skipSuffixWhile pat := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) hst
  simp only [Slice.skipSuffixWhile_eq_revSkipWhile_endPos] at this
  rw [StrA_rsw_n (s := tA) (by decide), StrA_rsw_a (s := sA) rfl] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.not_revMatchesAt_skipSuffixWhile` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT (skip everything, every string matches): the empty match at the start
theorem Pattern_Model_not_revMatchesAt_skipSuffixWhile_h3 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] (s : Slice),
      ¬RevMatchesAt pat (s.skipSuffixWhile pat) := by
  intro h
  exact h (ρ := EndT) EndT.p sA (revMatchesAt_all (fun _ => trivial) _)

-- `String.Slice.Pattern.Model.not_revMatchesAt_skipSuffixWhile` without `[LawfulBackwardPatternModel pat]` (idx 5): necessary.
-- strict model NoneNE (nonempty strings match) with a pattern that never skips, on "a"
theorem Pattern_Model_not_revMatchesAt_skipSuffixWhile_h5 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat] (s : Slice),
      ¬RevMatchesAt pat (s.skipSuffixWhile pat) := by
  intro h
  have := h (ρ := NoneNE) NoneNE.p sA
  rw [Slice.skipSuffixWhile_eq_revSkipWhile_endPos, NoneNE_rsw] at this
  exact this NoneNE_revMatchesAt_sA

-- `String.Slice.skipSuffixWhile_eq_endPos` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndSW on "a": `skipSuffix?` returns `startPos` but `endsWith` is `false`
theorem skipSuffixWhile_eq_endPos_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice},
      s.endsWith pat = false → s.skipSuffixWhile pat = s.endPos := by
  intro h
  have := h (ρ := EndSW) (pat := EndSW.p) (s := sA) rfl
  rw [Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndSW_rsw] at this
  exact sA_ne this

-- `String.Slice.skipSuffixWhile_eq_endPos_iff` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT on "": `skipSuffixWhile` stays at `endPos` but `endsWith` is `true` (empty match)
theorem skipSuffixWhile_eq_endPos_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice},
      s.skipSuffixWhile pat = s.endPos ↔ s.endsWith pat = false := by
  intro h
  exact absurd ((h (ρ := EndT) (pat := EndT.p) (s := sE)).1 (by rw [Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndT_rsw]; exact sE_eq)) (by decide)

-- `String.Slice.skipSuffixWhile_eq_endPos_iff` without `[LawfulBackwardPatternModel pat]` (idx 5): necessary.
-- NoneSW on "a": never skips but `endsWith` is `true`; model matches nothing (strict)
theorem skipSuffixWhile_eq_endPos_iff_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat] {s : Slice},
      s.skipSuffixWhile pat = s.endPos ↔ s.endsWith pat = false := by
  intro h
  exact absurd ((h (ρ := NoneSW) (pat := NoneSW.p) (s := sA)).1 (by rw [Slice.skipSuffixWhile_eq_revSkipWhile_endPos, NoneSW_rsw])) (by decide)

-- `String.Slice.Pattern.Model.skipSuffixWhile_eq_iff` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_skipSuffixWhile_eq_iff_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [BackwardPattern pat] (s : Slice) (res : s.Pos),
      s.skipSuffixWhile pat = res ↔ IsLongestRevMatchAtChain pat res s.endPos ∧
      (¬RevMatchesAt pat res ∨ IsLongestRevMatchAt pat res res) := by
  intro h
  exact sA_ne (rchain_eq (fun _ h => h) ((h (ρ := EndF) EndF.p sA sA.startPos).1 (EndF_rsw _)).1)

-- `String.Slice.Pattern.Model.isLongestRevMatchAtChain_skipSuffixWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_isLongestRevMatchAtChain_skipSuffixWhile_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [BackwardPattern pat] (s : Slice),
      IsLongestRevMatchAtChain pat (s.skipSuffixWhile pat) s.endPos := by
  intro h
  have := h (ρ := EndF) EndF.p sA
  rw [Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndF_rsw] at this
  exact sA_ne (rchain_eq (fun _ h => h) this)

-- `String.Slice.Pattern.Model.not_revMatchesAt_or_isLongestRevMatchAt_skipSuffixWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- NoneT on "a": never skips, every string matches, so `endPos` has the longest reverse match back to `startPos`
theorem Pattern_Model_not_revMatchesAt_or_isLongestRevMatchAt_skipSuffixWhile_h4 :
    ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [BackwardPattern pat] (s : Slice),
      ¬ RevMatchesAt pat (s.skipSuffixWhile pat) ∨ IsLongestRevMatchAt pat (s.skipSuffixWhile pat) (s.skipSuffixWhile pat) := by
  intro h
  have := h (ρ := NoneT) NoneT.p sA
  rw [Slice.skipSuffixWhile_eq_revSkipWhile_endPos, NoneT_rsw] at this
  rcases this with h1 | h1
  · exact h1 (revMatchesAt_all (fun _ => trivial) _)
  · exact sA_ne (ilrma_all_eq (fun _ => trivial) h1).symm

-- `String.Slice.Pattern.Model.skipSuffixWhile_eq_endPos_iff_or` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_skipSuffixWhile_eq_endPos_iff_or_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice},
      s.skipSuffixWhile pat = s.endPos ↔ ¬RevMatchesAt pat s.endPos ∨ IsLongestRevMatchAt pat s.endPos s.endPos := by
  intro h
  have := (h (ρ := EndF) (pat := EndF.p) (s := sA)).2 (Or.inl (not_revMatchesAt (fun _ h => h)))
  rw [Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndF_rsw] at this
  exact sA_ne this

-- `String.Slice.dropEndWhile_congr` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem dropEndWhile_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      (s.dropEndWhile pat).copy = (t.dropEndWhile pat).copy := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) hst
  simp only [Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos] at this
  rw [StrA_rsw_n (s := tA) (by decide), StrA_rsw_a (s := sA) rfl] at this
  exact absurd this (by decide)

-- `String.Slice.endsWith_dropEndWhile` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT: `endsWith` is always `true` (the empty remainder has an empty match)
theorem endsWith_dropEndWhile_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice},
      (s.dropEndWhile pat).endsWith pat = false := by
  intro h
  exact absurd (h (ρ := EndT) (pat := EndT.p) (s := sA)) (by decide)

-- `String.Slice.endsWith_dropEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 5): necessary.
-- NoneSW on "a": never skips but `endsWith` is `true`; model matches nothing (strict)
theorem endsWith_dropEndWhile_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat] {s : Slice},
      (s.dropEndWhile pat).endsWith pat = false := by
  intro h
  exact absurd (h (ρ := NoneSW) (pat := NoneSW.p) (s := sA)) (by decide)

-- `String.Slice.dropEndWhile_eq_self` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndSW on "a": `skipSuffix?` returns `startPos` but `endsWith` is `false`
theorem dropEndWhile_eq_self_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice} (h : s.endsWith pat = false),
      s.dropEndWhile pat = s := by
  intro h
  have := congrArg Slice.copy (h (ρ := EndSW) (pat := EndSW.p) (s := sA) rfl)
  rw [Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndSW_rsw] at this
  exact absurd this (by decide)

-- `String.Slice.dropEndWhile_eq_self_iff` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT on "": `dropEndWhile` is the identity but `endsWith` is `true`
theorem dropEndWhile_eq_self_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice},
      s.dropEndWhile pat = s ↔ s.endsWith pat = false := by
  intro h
  have := (h (ρ := EndT) (pat := EndT.p) (s := sE)).1
    (by rw [Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndT_rsw, sE_eq]; exact Slice.sliceTo_endPos)
  exact absurd this (by decide)

-- `String.Slice.dropEndWhile_eq_self_iff` without `[LawfulBackwardPatternModel pat]` (idx 5): necessary.
-- NoneSW on "a": never skips but `endsWith` is `true`; model matches nothing (strict)
theorem dropEndWhile_eq_self_iff_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat] {s : Slice},
      s.dropEndWhile pat = s ↔ s.endsWith pat = false := by
  intro h
  have := (h (ρ := NoneSW) (pat := NoneSW.p) (s := sA)).1
    (by rw [Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, NoneSW_rsw]; exact Slice.sliceTo_endPos)
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.dropEndWhile_eq_self_iff_or` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_dropEndWhile_eq_self_iff_or_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice},
      s.dropEndWhile pat = s ↔ ¬RevMatchesAt pat s.endPos ∨ IsLongestRevMatchAt pat s.endPos s.endPos := by
  intro h
  have := congrArg Slice.copy ((h (ρ := EndF) (pat := EndF.p) (s := sA)).2 (Or.inl (not_revMatchesAt (fun _ h => h))))
  rw [Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndF_rsw] at this
  exact absurd this (by decide)

-- `String.Slice.takeEndWhile_congr` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem takeEndWhile_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      (s.takeEndWhile pat).copy = (t.takeEndWhile pat).copy := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) hst
  simp only [Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos] at this
  rw [StrA_rsw_n (s := tA) (by decide), StrA_rsw_a (s := sA) rfl] at this
  exact absurd this (by decide)

-- `String.Slice.isEmpty_takeEndWhile_eq_true` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndSW on "a": `skipSuffix?` returns `startPos` but `endsWith` is `false`
theorem isEmpty_takeEndWhile_eq_true_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice} (h : s.endsWith pat = false),
      (s.takeEndWhile pat).isEmpty = true := by
  intro h
  have := h (ρ := EndSW) (pat := EndSW.p) (s := sA) rfl
  rw [Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndSW_rsw] at this
  exact absurd this (by decide)

-- `String.Slice.isEmpty_takeEndWhile` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT on "": `takeEndWhile` is empty but `endsWith` is `true`
theorem isEmpty_takeEndWhile_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice},
      (s.takeEndWhile pat).isEmpty = !s.endsWith pat := by
  intro h
  have := h (ρ := EndT) (pat := EndT.p) (s := sE)
  rw [Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndT_rsw] at this
  exact absurd this (by decide)

-- `String.Slice.isEmpty_takeEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 5): necessary.
-- EndSW on "a": `skipSuffix?` returns `startPos` but `endsWith` is `false` (model matches nothing, strict)
theorem isEmpty_takeEndWhile_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat] {s : Slice},
      (s.takeEndWhile pat).isEmpty = !s.endsWith pat := by
  intro h
  have := h (ρ := EndSW) (pat := EndSW.p) (s := sA)
  rw [Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndSW_rsw] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.revAll_eq_true_iff` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndF on "a": `skipSuffix?` always returns `startPos`, the model matches nothing
theorem Pattern_Model_revAll_eq_true_iff_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice},
      s.revAll pat ↔ IsLongestRevMatchAtChain pat s.startPos s.endPos := by
  intro h
  exact sA_ne (rchain_eq (fun _ h => h) ((h (ρ := EndF) (pat := EndF.p) (s := sA)).1 (by rw [Slice.revAll_eq_skipSuffixWhile_beq, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndF_rsw]; decide)))

-- `String.Slice.revAll_congr` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA: skips everything iff the underlying string is "a"; "a".toSlice vs. the prefix "a" of "ab" (same copy)
theorem revAll_congr_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s t : Slice} (hst : s.copy = t.copy),
      s.revAll pat = t.revAll pat := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) hst
  simp only [Slice.revAll_eq_skipSuffixWhile_beq, Slice.skipSuffixWhile_eq_revSkipWhile_endPos] at this
  rw [StrA_rsw_n (s := tA) (by decide), StrA_rsw_a (s := sA) rfl] at this
  exact absurd this (by decide)

-- `String.Slice.revAll_takeEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- Step1 on "ab": skips one character iff the slice is "ab", so a second pass over the suffix "b" makes no progress
theorem revAll_takeEndWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice},
      (s.takeEndWhile pat).revAll pat = true := by
  intro h
  have := h (ρ := Step1) (pat := Step1.p) (s := sAB)
  rw [Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, Step1_rsw, Slice.revAll_eq_skipSuffixWhile_beq, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, rsw_none (by decide)] at this
  exact absurd this (by decide)

-- `String.Slice.dropEndWhile_dropEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): removable.
-- holds for every BackwardPattern: mirror of `dropWhile_dropWhile` (`revSkipWhile` restarted on the remainder makes no progress)
theorem dropEndWhile_dropEndWhile_h4 {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice} :
    (s.dropEndWhile pat).dropEndWhile pat = s.dropEndWhile pat := by
  exact PatTakeDropHand.dropEndWhile_dropEndWhile_gen

-- `String.Slice.takeEndWhile_takeEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- Step1 on "ab": skips one character iff the slice is "ab", so a second pass over the suffix "b" makes no progress
theorem takeEndWhile_takeEndWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice},
      (s.takeEndWhile pat).takeEndWhile pat = s.takeEndWhile pat := by
  intro h
  have := congrArg Slice.copy (h (ρ := Step1) (pat := Step1.p) (s := sAB))
  simp only [Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos] at this
  rw [Step1_rsw, rsw_none (by decide)] at this
  exact absurd this (by decide)

-- `String.Slice.isEmpty_takeEndWhile_dropEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): removable.
-- holds for every BackwardPattern: mirror of `isEmpty_takeWhile_dropWhile`
theorem isEmpty_takeEndWhile_dropEndWhile_h4 {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice} :
    ((s.dropEndWhile pat).takeEndWhile pat).isEmpty = true := by
  exact PatTakeDropHand.isEmpty_takeEndWhile_dropEndWhile_gen

-- `String.Slice.isEmpty_dropEndWhile_takeEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- Step1 on "ab": skips one character iff the slice is "ab", so a second pass over the suffix "b" makes no progress
theorem isEmpty_dropEndWhile_takeEndWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice},
      ((s.takeEndWhile pat).dropEndWhile pat).isEmpty = true := by
  intro h
  have := h (ρ := Step1) (pat := Step1.p) (s := sAB)
  rw [Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, Step1_rsw, Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, rsw_none (by decide)] at this
  exact absurd this (by decide)

end String.Slice.PTDHandS

namespace String.PTDHandT
open PatTakeDropHand

-- `String.Slice.skipPrefix?_copy` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_skipPrefix?_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] {s : Slice},
      s.copy.skipPrefix? pat = (s.skipPrefix? pat).map Slice.Pos.copy := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) (s := tA)) (by decide)

-- `String.Slice.startsWith_copy` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_startsWith_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] {s : Slice},
      s.copy.startsWith pat = s.startsWith pat := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) (s := tA)) (by decide)

-- `String.Slice.copy_dropPrefix?_copy` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_copy_dropPrefix?_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] {s : Slice},
      (s.copy.dropPrefix? pat).map String.Slice.copy = (s.dropPrefix? pat).map String.Slice.copy := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) (s := tA)) (by decide)

-- `String.Slice.Pos.skip?_copy` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_Pos_skip?_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] {s : Slice} {pos : s.Pos},
      pos.copy.skip? pat = (pos.skip? pat).map Slice.Pos.copy := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) (s := tA) (pos := tA.startPos)) (by decide)

-- `String.Slice.Pos.skipWhile_copy` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_Pos_skipWhile_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] {s : Slice} {pos : s.Pos},
      pos.copy.skipWhile pat = (pos.skipWhile pat).copy := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) (s := tA) (pos := tA.startPos)
  rw [String.Pos.skipWhile_eq_skipWhile_toSlice, StrA_sw_a (s := tA.copy.toSlice) (by decide),
    StrA_sw_n (s := tA) (by decide)] at this
  exact absurd this (by decide)

-- `String.Pos.le_skipWhile` without `[LawfulForwardPatternModel pat]` (idx 4): removable.
-- holds for every ForwardPattern: reduces to `Slice.Pos.le_skipWhile`, which needs no lawfulness
theorem Pos_le_skipWhile_h4 {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] {s : String} {pos : s.Pos} :
    pos ≤ pos.skipWhile pat := by
  rw [Pos.skipWhile_eq_skipWhile_toSlice, Pos.le_ofToSlice_iff]
  exact PatTakeDropHand.le_skipWhile_gen _

-- `String.Slice.skipPrefixWhile_copy` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_skipPrefixWhile_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] {s : Slice},
      s.copy.skipPrefixWhile pat = (s.skipPrefixWhile pat).copy := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) (s := tA)
  simp only [String.skipPrefixWhile_eq_skipPrefixWhile_toSlice, Slice.skipPrefixWhile_eq_skipWhile_startPos] at this
  rw [StrA_sw_a (s := tA.copy.toSlice) (by decide), StrA_sw_n (s := tA) (by decide)] at this
  exact absurd this (by decide)

-- `String.skipPrefixWhile_eq_startPos` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndSW on "a": `skipPrefix?` returns `endPos` but `startsWith` is `false`
theorem skipPrefixWhile_eq_startPos_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : String},
      s.startsWith pat = false → s.skipPrefixWhile pat = s.startPos := by
  intro h
  have := h (ρ := EndSW) (pat := EndSW.p) (s := "a") rfl
  rw [String.skipPrefixWhile_eq_skipPrefixWhile_toSlice, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndSW_sw] at this
  exact absurd this (by decide)

-- `String.skipPrefixWhile_eq_startPos_iff` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT on "": `skipPrefixWhile` stays at `startPos` but `startsWith` is `true` (empty match)
theorem skipPrefixWhile_eq_startPos_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : String},
      s.skipPrefixWhile pat = s.startPos ↔ s.startsWith pat = false := by
  intro h
  exact absurd ((h (ρ := EndT) (pat := EndT.p) (s := "")).1 (by rw [String.skipPrefixWhile_eq_skipPrefixWhile_toSlice, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndT_sw]; decide)) (by decide)

-- `String.skipPrefixWhile_eq_startPos_iff` without `[LawfulForwardPatternModel pat]` (idx 5): necessary.
-- NoneSW on "a": never skips but `startsWith` is `true`; model matches nothing (strict)
theorem skipPrefixWhile_eq_startPos_iff_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat] {s : String},
      s.skipPrefixWhile pat = s.startPos ↔ s.startsWith pat = false := by
  intro h
  exact absurd ((h (ρ := NoneSW) (pat := NoneSW.p) (s := "a")).1 (by rw [String.skipPrefixWhile_eq_skipPrefixWhile_toSlice, Slice.skipPrefixWhile_eq_skipWhile_startPos, NoneSW_sw]; decide)) (by decide)

-- `String.Slice.dropWhile_copy` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_dropWhile_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] {s : Slice},
      (s.copy.dropWhile pat).copy = (s.dropWhile pat).copy := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) (s := tA)
  simp only [String.dropWhile_eq_dropWhile_toSlice, Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos] at this
  rw [StrA_sw_a (s := tA.copy.toSlice) (by decide), StrA_sw_n (s := tA) (by decide)] at this
  exact absurd this (by decide)

-- `String.startsWith_dropWhile` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT: `startsWith` is always `true` (the empty remainder has an empty match)
theorem startsWith_dropWhile_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : String},
      (s.dropWhile pat).startsWith pat = false := by
  intro h
  exact absurd (h (ρ := EndT) (pat := EndT.p) (s := "a")) (by decide)

-- `String.startsWith_dropWhile` without `[LawfulForwardPatternModel pat]` (idx 5): necessary.
-- NoneSW on "a": never skips but `startsWith` is `true`; model matches nothing (strict)
theorem startsWith_dropWhile_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat] {s : String},
      (s.dropWhile pat).startsWith pat = false := by
  intro h
  exact absurd (h (ρ := NoneSW) (pat := NoneSW.p) (s := "a")) (by decide)

-- `String.dropWhile_eq_toSlice` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndSW on "a": `skipPrefix?` returns `endPos` but `startsWith` is `false`
theorem dropWhile_eq_toSlice_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : String} (h : s.startsWith pat = false),
      s.dropWhile pat = s.toSlice := by
  intro h
  have := congrArg Slice.copy (h (ρ := EndSW) (pat := EndSW.p) (s := "a") rfl)
  rw [String.dropWhile_eq_dropWhile_toSlice, Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndSW_sw] at this
  exact absurd this (by decide)

-- `String.dropWhile_eq_toSlice_iff` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT on "": `dropWhile` is the whole string but `startsWith` is `true`
theorem dropWhile_eq_toSlice_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : String},
      s.dropWhile pat = s.toSlice ↔ s.startsWith pat = false := by
  intro h
  have := (h (ρ := EndT) (pat := EndT.p) (s := "")).1
    (by rw [String.dropWhile_eq_dropWhile_toSlice, Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndT_sw, ← (by decide : ("".toSlice).startPos = ("".toSlice).endPos)]; exact Slice.sliceFrom_startPos)
  exact absurd this (by decide)

-- `String.dropWhile_eq_toSlice_iff` without `[LawfulForwardPatternModel pat]` (idx 5): necessary.
-- NoneSW on "a": never skips but `startsWith` is `true`; model matches nothing (strict)
theorem dropWhile_eq_toSlice_iff_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat] {s : String},
      s.dropWhile pat = s.toSlice ↔ s.startsWith pat = false := by
  intro h
  have := (h (ρ := NoneSW) (pat := NoneSW.p) (s := "a")).1
    (by rw [String.dropWhile_eq_dropWhile_toSlice, Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, NoneSW_sw]; exact Slice.sliceFrom_startPos)
  exact absurd this (by decide)

-- `String.Slice.takeWhile_copy` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_takeWhile_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] {s : Slice},
      (s.copy.takeWhile pat).copy = (s.takeWhile pat).copy := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) (s := tA)
  simp only [String.takeWhile_eq_takeWhile_toSlice, Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos] at this
  rw [StrA_sw_a (s := tA.copy.toSlice) (by decide), StrA_sw_n (s := tA) (by decide)] at this
  exact absurd this (by decide)

-- `String.isEmpty_takeWhile_eq_true` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- EndSW on "a": `skipPrefix?` returns `endPos` but `startsWith` is `false`
theorem isEmpty_takeWhile_eq_true_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : String} (h : s.startsWith pat = false),
      (s.takeWhile pat).isEmpty = true := by
  intro h
  have := h (ρ := EndSW) (pat := EndSW.p) (s := "a") rfl
  rw [String.takeWhile_eq_takeWhile_toSlice, Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndSW_sw] at this
  exact absurd this (by decide)

-- `String.isEmpty_takeWhile` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT on "": `takeWhile` is empty but `startsWith` is `true`
theorem isEmpty_takeWhile_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : String},
      (s.takeWhile pat).isEmpty = !s.startsWith pat := by
  intro h
  have := h (ρ := EndT) (pat := EndT.p) (s := "")
  rw [String.takeWhile_eq_takeWhile_toSlice, Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndT_sw] at this
  exact absurd this (by decide)

-- `String.isEmpty_takeWhile` without `[LawfulForwardPatternModel pat]` (idx 5): necessary.
-- EndSW on "a": `skipPrefix?` returns `endPos` but `startsWith` is `false` (model matches nothing, strict)
theorem isEmpty_takeWhile_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat] {s : String},
      (s.takeWhile pat).isEmpty = !s.startsWith pat := by
  intro h
  have := h (ρ := EndSW) (pat := EndSW.p) (s := "a")
  rw [String.takeWhile_eq_takeWhile_toSlice, Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, EndSW_sw] at this
  exact absurd this (by decide)

-- `String.Slice.all_copy` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_all_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice},
      s.copy.all pat = s.all pat := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) (s := tA)
  simp only [String.all_eq_all_toSlice, Slice.all_eq_skipPrefixWhile_beq, Slice.skipPrefixWhile_eq_skipWhile_startPos] at this
  rw [StrA_sw_a (s := tA.copy.toSlice) (by decide), StrA_sw_n (s := tA) (by decide)] at this
  exact absurd this (by decide)

-- `String.all_takeWhile` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- Step1 on "ab": skips one character iff the slice is "ab", so a second pass over the prefix "a" makes no progress
theorem all_takeWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : String},
      (s.takeWhile pat).all pat = true := by
  intro h
  have := h (ρ := Step1) (pat := Step1.p) (s := "ab")
  change (sAB.takeWhile Step1.p).all Step1.p = true at this
  rw [Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, Step1_sw, Slice.all_eq_skipPrefixWhile_beq, Slice.skipPrefixWhile_eq_skipWhile_startPos, sw_none (by decide)] at this
  exact absurd this (by decide)

-- `String.dropWhile_dropWhile` without `[LawfulForwardPatternModel pat]` (idx 4): removable.
-- holds for every ForwardPattern: `String.dropWhile` is `Slice.dropWhile` on `toSlice`; see `Slice.dropWhile_dropWhile`
theorem dropWhile_dropWhile_h4 {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : String} :
    (s.dropWhile pat).dropWhile pat = s.dropWhile pat := by
  exact PatTakeDropHand.dropWhile_dropWhile_gen (s := s.toSlice)

-- `String.takeWhile_takeWhile` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- Step1 on "ab": skips one character iff the slice is "ab", so a second pass over the prefix "a" makes no progress
theorem takeWhile_takeWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : Slice},
      (s.takeWhile pat).takeWhile pat = s.takeWhile pat := by
  intro h
  have := congrArg Slice.copy (h (ρ := Step1) (pat := Step1.p) (s := sAB))
  simp only [Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos] at this
  rw [Step1_sw, sw_none (by decide)] at this
  exact absurd this (by decide)

-- `String.isEmpty_takeWhile_dropWhile` without `[LawfulForwardPatternModel pat]` (idx 4): removable.
-- holds for every ForwardPattern: reduces to `Slice.isEmpty_takeWhile_dropWhile`
theorem isEmpty_takeWhile_dropWhile_h4 {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : String} :
    ((s.dropWhile pat).takeWhile pat).isEmpty = true := by
  exact PatTakeDropHand.isEmpty_takeWhile_dropWhile_gen (s := s.toSlice)

-- `String.isEmpty_dropWhile_takeWhile` without `[LawfulForwardPatternModel pat]` (idx 4): necessary.
-- Step1 on "ab": skips one character iff the slice is "ab", so a second pass over the prefix "a" makes no progress
theorem isEmpty_dropWhile_takeWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] {s : String},
      ((s.takeWhile pat).dropWhile pat).isEmpty = true := by
  intro h
  have := h (ρ := Step1) (pat := Step1.p) (s := "ab")
  change ((sAB.takeWhile Step1.p).dropWhile Step1.p).isEmpty = true at this
  rw [Slice.takeWhile_eq_sliceTo_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, Step1_sw, Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, Slice.skipPrefixWhile_eq_skipWhile_startPos, sw_none (by decide)] at this
  exact absurd this (by decide)

-- `String.Slice.skipSuffix?_copy` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_skipSuffix?_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] {s : Slice},
      s.copy.skipSuffix? pat = (s.skipSuffix? pat).map Slice.Pos.copy := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) (s := tA)) (by decide)

-- `String.Slice.endsWith_copy` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_endsWith_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] {s : Slice},
      s.copy.endsWith pat = s.endsWith pat := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) (s := tA)) (by decide)

-- `String.Slice.copy_dropSuffix?_copy` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_copy_dropSuffix?_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] {s : Slice},
      (s.copy.dropSuffix? pat).map String.Slice.copy = (s.dropSuffix? pat).map String.Slice.copy := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) (s := tA)) (by decide)

-- `String.Slice.Pos.revSkip?_copy` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_Pos_revSkip?_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] {s : Slice} {pos : s.Pos},
      pos.copy.revSkip? pat = (pos.revSkip? pat).map Slice.Pos.copy := by
  intro h
  exact absurd (h (ρ := StrA) (pat := StrA.p) (s := tA) (pos := tA.endPos)) (by decide)

-- `String.Slice.Pos.revSkipWhile_copy` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_Pos_revSkipWhile_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] {s : Slice} {pos : s.Pos},
      pos.copy.revSkipWhile pat = (pos.revSkipWhile pat).copy := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) (s := tA) (pos := tA.endPos)
  rw [String.Pos.revSkipWhile_eq_revSkipWhile_toSlice, StrA_rsw_a (s := tA.copy.toSlice) (by decide),
    StrA_rsw_n (s := tA) (by decide)] at this
  exact absurd this (by decide)

-- `String.Pos.revSkipWhile_le` without `[LawfulBackwardPatternModel pat]` (idx 4): removable.
-- holds for every BackwardPattern: reduces to `Slice.Pos.revSkipWhile_le`, which needs no lawfulness
theorem Pos_revSkipWhile_le_h4 {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] {s : String} {pos : s.Pos} :
    pos.revSkipWhile pat ≤ pos := by
  rw [Pos.revSkipWhile_eq_revSkipWhile_toSlice, Pos.ofToSlice_le_iff]
  exact PatTakeDropHand.revSkipWhile_le_gen _

-- `String.Slice.skipSuffixWhile_copy` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_skipSuffixWhile_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] {s : Slice},
      s.copy.skipSuffixWhile pat = (s.skipSuffixWhile pat).copy := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) (s := tA)
  simp only [String.skipSuffixWhile_eq_skipSuffixWhile_toSlice, Slice.skipSuffixWhile_eq_revSkipWhile_endPos] at this
  rw [StrA_rsw_a (s := tA.copy.toSlice) (by decide), StrA_rsw_n (s := tA) (by decide)] at this
  exact absurd this (by decide)

-- `String.skipSuffixWhile_eq_endPos` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndSW on "a": `skipSuffix?` returns `startPos` but `endsWith` is `false`
theorem skipSuffixWhile_eq_endPos_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : String},
      s.endsWith pat = false → s.skipSuffixWhile pat = s.endPos := by
  intro h
  have := h (ρ := EndSW) (pat := EndSW.p) (s := "a") rfl
  rw [String.skipSuffixWhile_eq_skipSuffixWhile_toSlice, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndSW_rsw] at this
  exact absurd this (by decide)

-- `String.skipSuffixWhile_eq_endPos_iff` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT on "": `skipSuffixWhile` stays at `endPos` but `endsWith` is `true` (empty match)
theorem skipSuffixWhile_eq_endPos_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : String},
      s.skipSuffixWhile pat = s.endPos ↔ s.endsWith pat = false := by
  intro h
  exact absurd ((h (ρ := EndT) (pat := EndT.p) (s := "")).1 (by rw [String.skipSuffixWhile_eq_skipSuffixWhile_toSlice, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndT_rsw]; decide)) (by decide)

-- `String.skipSuffixWhile_eq_endPos_iff` without `[LawfulBackwardPatternModel pat]` (idx 5): necessary.
-- NoneSW on "a": never skips but `endsWith` is `true`; model matches nothing (strict)
theorem skipSuffixWhile_eq_endPos_iff_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat] {s : String},
      s.skipSuffixWhile pat = s.endPos ↔ s.endsWith pat = false := by
  intro h
  exact absurd ((h (ρ := NoneSW) (pat := NoneSW.p) (s := "a")).1 (by rw [String.skipSuffixWhile_eq_skipSuffixWhile_toSlice, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, NoneSW_rsw]; decide)) (by decide)

-- `String.Slice.dropEndWhile_copy` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_dropEndWhile_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] {s : Slice},
      (s.copy.dropEndWhile pat).copy = (s.dropEndWhile pat).copy := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) (s := tA)
  simp only [String.dropEndWhile_eq_dropEndWhile_toSlice, Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos] at this
  rw [StrA_rsw_a (s := tA.copy.toSlice) (by decide), StrA_rsw_n (s := tA) (by decide)] at this
  exact absurd this (by decide)

-- `String.endsWith_dropEndWhile` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT: `endsWith` is always `true` (the empty remainder has an empty match)
theorem endsWith_dropEndWhile_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : String},
      (s.dropEndWhile pat).endsWith pat = false := by
  intro h
  exact absurd (h (ρ := EndT) (pat := EndT.p) (s := "a")) (by decide)

-- `String.endsWith_dropEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 5): necessary.
-- NoneSW on "a": never skips but `endsWith` is `true`; model matches nothing (strict)
theorem endsWith_dropEndWhile_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat] {s : String},
      (s.dropEndWhile pat).endsWith pat = false := by
  intro h
  exact absurd (h (ρ := NoneSW) (pat := NoneSW.p) (s := "a")) (by decide)

-- `String.dropEndWhile_eq_toSlice` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndSW on "a": `skipSuffix?` returns `startPos` but `endsWith` is `false`
theorem dropEndWhile_eq_toSlice_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : String} (h : s.endsWith pat = false),
      s.dropEndWhile pat = s.toSlice := by
  intro h
  have := congrArg Slice.copy (h (ρ := EndSW) (pat := EndSW.p) (s := "a") rfl)
  rw [String.dropEndWhile_eq_dropEndWhile_toSlice, Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndSW_rsw] at this
  exact absurd this (by decide)

-- `String.dropEndWhile_eq_toSlice_iff` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT on "": `dropEndWhile` is the whole string but `endsWith` is `true`
theorem dropEndWhile_eq_toSlice_iff_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : String},
      s.dropEndWhile pat = s.toSlice ↔ s.endsWith pat = false := by
  intro h
  have := (h (ρ := EndT) (pat := EndT.p) (s := "")).1
    (by rw [String.dropEndWhile_eq_dropEndWhile_toSlice, Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndT_rsw, (by decide : ("".toSlice).startPos = ("".toSlice).endPos)]; exact Slice.sliceTo_endPos)
  exact absurd this (by decide)

-- `String.dropEndWhile_eq_toSlice_iff` without `[LawfulBackwardPatternModel pat]` (idx 5): necessary.
-- NoneSW on "a": never skips but `endsWith` is `true`; model matches nothing (strict)
theorem dropEndWhile_eq_toSlice_iff_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat] {s : String},
      s.dropEndWhile pat = s.toSlice ↔ s.endsWith pat = false := by
  intro h
  have := (h (ρ := NoneSW) (pat := NoneSW.p) (s := "a")).1
    (by rw [String.dropEndWhile_eq_dropEndWhile_toSlice, Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, NoneSW_rsw]; exact Slice.sliceTo_endPos)
  exact absurd this (by decide)

-- `String.Slice.takeEndWhile_copy` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_takeEndWhile_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] {s : Slice},
      (s.copy.takeEndWhile pat).copy = (s.takeEndWhile pat).copy := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) (s := tA)
  simp only [String.takeEndWhile_eq_takeEndWhile_toSlice, Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos] at this
  rw [StrA_rsw_a (s := tA.copy.toSlice) (by decide), StrA_rsw_n (s := tA) (by decide)] at this
  exact absurd this (by decide)

-- `String.isEmpty_takeEndWhile_eq_true` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- EndSW on "a": `skipSuffix?` returns `startPos` but `endsWith` is `false`
theorem isEmpty_takeEndWhile_eq_true_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : String} (h : s.endsWith pat = false),
      (s.takeEndWhile pat).isEmpty = true := by
  intro h
  have := h (ρ := EndSW) (pat := EndSW.p) (s := "a") rfl
  rw [String.takeEndWhile_eq_takeEndWhile_toSlice, Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndSW_rsw] at this
  exact absurd this (by decide)

-- `String.isEmpty_takeEndWhile` without `[StrictPatternModel pat]` (idx 3): necessary.
-- lawful non-strict EndT on "": `takeEndWhile` is empty but `endsWith` is `true`
theorem isEmpty_takeEndWhile_h3 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : String},
      (s.takeEndWhile pat).isEmpty = !s.endsWith pat := by
  intro h
  have := h (ρ := EndT) (pat := EndT.p) (s := "")
  rw [String.takeEndWhile_eq_takeEndWhile_toSlice, Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndT_rsw] at this
  exact absurd this (by decide)

-- `String.isEmpty_takeEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 5): necessary.
-- EndSW on "a": `skipSuffix?` returns `startPos` but `endsWith` is `false` (model matches nothing, strict)
theorem isEmpty_takeEndWhile_h5 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat] {s : String},
      (s.takeEndWhile pat).isEmpty = !s.endsWith pat := by
  intro h
  have := h (ρ := EndSW) (pat := EndSW.p) (s := "a")
  rw [String.takeEndWhile_eq_takeEndWhile_toSlice, Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, EndSW_rsw] at this
  exact absurd this (by decide)

-- `String.Slice.revAll_copy` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- StrA on the prefix "a" of "ab": the slice's underlying string is "ab", its copy's is "a", so the pattern behaves differently on the copy
theorem Slice_revAll_copy_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice},
      s.copy.revAll pat = s.revAll pat := by
  intro h
  have := h (ρ := StrA) (pat := StrA.p) (s := tA)
  simp only [String.revAll_eq_revAll_toSlice, Slice.revAll_eq_skipSuffixWhile_beq, Slice.skipSuffixWhile_eq_revSkipWhile_endPos] at this
  rw [StrA_rsw_a (s := tA.copy.toSlice) (by decide), StrA_rsw_n (s := tA) (by decide)] at this
  exact absurd this (by decide)

-- `String.revAll_takeEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- Step1 on "ab": skips one character iff the slice is "ab", so a second pass over the suffix "b" makes no progress
theorem revAll_takeEndWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : String},
      (s.takeEndWhile pat).revAll pat = true := by
  intro h
  have := h (ρ := Step1) (pat := Step1.p) (s := "ab")
  change (sAB.takeEndWhile Step1.p).revAll Step1.p = true at this
  rw [Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, Step1_rsw, Slice.revAll_eq_skipSuffixWhile_beq, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, rsw_none (by decide)] at this
  exact absurd this (by decide)

-- `String.dropEndWhile_dropEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): removable.
-- holds for every BackwardPattern: reduces to `Slice.dropEndWhile_dropEndWhile`
theorem dropEndWhile_dropEndWhile_h4 {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : String} :
    (s.dropEndWhile pat).dropEndWhile pat = s.dropEndWhile pat := by
  exact PatTakeDropHand.dropEndWhile_dropEndWhile_gen (s := s.toSlice)

-- `String.takeEndWhile_takeEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- Step1 on "ab": skips one character iff the slice is "ab", so a second pass over the suffix "b" makes no progress
theorem takeEndWhile_takeEndWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : Slice},
      (s.takeEndWhile pat).takeEndWhile pat = s.takeEndWhile pat := by
  intro h
  have := congrArg Slice.copy (h (ρ := Step1) (pat := Step1.p) (s := sAB))
  simp only [Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos] at this
  rw [Step1_rsw, rsw_none (by decide)] at this
  exact absurd this (by decide)

-- `String.isEmpty_takeEndWhile_dropEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): removable.
-- holds for every BackwardPattern: reduces to `Slice.isEmpty_takeEndWhile_dropEndWhile`
theorem isEmpty_takeEndWhile_dropEndWhile_h4 {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : String} :
    ((s.dropEndWhile pat).takeEndWhile pat).isEmpty = true := by
  exact PatTakeDropHand.isEmpty_takeEndWhile_dropEndWhile_gen (s := s.toSlice)

-- `String.isEmpty_dropEndWhile_takeEndWhile` without `[LawfulBackwardPatternModel pat]` (idx 4): necessary.
-- Step1 on "ab": skips one character iff the slice is "ab", so a second pass over the suffix "b" makes no progress
theorem isEmpty_dropEndWhile_takeEndWhile_h4 :
    ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] {s : String},
      ((s.takeEndWhile pat).dropEndWhile pat).isEmpty = true := by
  intro h
  have := h (ρ := Step1) (pat := Step1.p) (s := "ab")
  change ((sAB.takeEndWhile Step1.p).dropEndWhile Step1.p).isEmpty = true at this
  rw [Slice.takeEndWhile_eq_sliceFrom_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, Step1_rsw, Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, rsw_none (by decide)] at this
  exact absurd this (by decide)

end String.PTDHandT
