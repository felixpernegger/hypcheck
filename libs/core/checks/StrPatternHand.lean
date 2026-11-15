import Lean

/-!
Hand pass over cluster `StrPattern` (hand9): the 87 open hypotheses of the String pattern lemmas
(`Init.Data.String.Lemmas.Pattern.{Basic,Char,Pred}`, `…Pattern.String.{Basic,ForwardSearcher}`,
`Init.Data.String.Pattern.Basic`, `Init.Data.String.Slice.Pattern`). For hypothesis `hᵢ` of theorem
`T` this file proves `¬T'` (`drop% T i`), or for a dependent hypothesis `¬∀ indep, Hᵢ`
(`indep% T i`, all independent binders), or, for the removable ones, `T'` itself.

76 necessary, 11 removable.

Removable (11): the empty pattern `""` (or an empty slice pattern) only has the empty longest match
`IsLongestMatchAt pat p p`, and its size is `0`, so `pat.isEmpty = false` / `pat ≠ ""` is not needed in
`ForwardSliceSearcher.{offset_of_isLongestMatchAt, offset_of_isLongestRevMatchAt,
matchesAt_iff_isLongestMatchAt, revMatchesAt_iff_isLongestRevMatchAt, matchesAt_iff_getElem,
le_of_matchesAt}` and the `ForwardStringSearcher` versions of the first five (proved by case split on
`pat.isEmpty` with `fss_lma_empty`, or by the library proof with the removable lemma substituted).
The `_iff_extract` lemmas do need it: with `pat = ""`, `pos₁ = "a".endPos`, `pos₂ = startPos` the
extracted byte range is empty but there is no match (`pos₁ > pos₂`).

Models (namespace `StrPatternHand`):
* `P.tru` (every string matches), `P.fal` (none), `P.emp` (only `""`) with `tru_lm`, `tru_lrm`,
  `tru_lma`, `tru_lrma`, `emp_lma`, `emp_lrma`, `not_matchesAt_fal`, `not_revMatchesAt_fal`;
* slices `sA = "a".toSlice`, `sE = "".toSlice`; positions and `s.copy = t.copy` evaluate with `decide`
  (`decide +kernel` through `prev`);
* `vsf_nil`/`vsf_cons`/`vrsf_nil`/`vrsf_cons`: inversion of `IsValidSearchFrom`/`IsValidRevSearchFrom`;
* `LS s`: a searcher iterator that skips to itself (not `Finite`, `LS.not_finite`); with it the
  `SplitIterator`/`SplitInclusiveIterator`/`RevSplitIterator` of `P.tru` are not `Finite` either
  (`split_not_finite`, `splitInclusive_not_finite`, `revSplit_not_finite`);
* the library's `Char`, `Char → Bool`, decidable `Char → Prop` patterns (lawful, strict) for the
  pattern-class fields on the empty slice and the character-test lemmas.

Run with the lean4 repo's stage1 binary: `lean checks/StrPatternHand.lean`.
-/


set_option linter.unusedVariables false
set_option linter.deprecated false

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

open String.Slice.Pattern String.Slice.Pattern.Model Std Std.Iterators
open String (Slice)

namespace StrPatternHand

/-! ## Models -/

/-- Pattern values: `tru` matches every string, `fal` none, `emp` only `""`. -/
inductive P | tru | fal | emp

instance : PatternModel P.tru := ⟨fun _ => True⟩
instance : PatternModel P.fal := ⟨fun _ => False⟩
instance : PatternModel P.emp := ⟨fun t => t = ""⟩

abbrev sA : Slice := "a".toSlice
abbrev sE : Slice := "".toSlice

theorem isLongestMatch_endPos {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice}
    (h : PatternModel.Matches pat s.copy) : IsLongestMatch pat s.endPos :=
  ⟨⟨by simpa using h⟩, fun p hp => absurd (String.Slice.Pos.le_endPos p) (Std.not_le.2 hp)⟩

theorem isLongestRevMatch_startPos {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice}
    (h : PatternModel.Matches pat s.copy) : IsLongestRevMatch pat s.startPos :=
  ⟨⟨by simpa using h⟩, fun p hp => absurd (String.Slice.Pos.startPos_le p) (Std.not_le.2 hp)⟩

theorem tru_lm (s : Slice) : IsLongestMatch P.tru s.endPos := isLongestMatch_endPos trivial
theorem tru_lrm (s : Slice) : IsLongestRevMatch P.tru s.startPos := isLongestRevMatch_startPos trivial

theorem tru_lma {s : Slice} (p : s.Pos) : IsLongestMatchAt P.tru p s.endPos :=
  ⟨String.Slice.Pos.le_endPos p, by simpa using isLongestMatch_endPos (pat := P.tru) (s := s.sliceFrom p) trivial⟩
theorem tru_lrma {s : Slice} (p : s.Pos) : IsLongestRevMatchAt P.tru s.startPos p :=
  ⟨String.Slice.Pos.startPos_le p, by simpa using isLongestRevMatch_startPos (pat := P.tru) (s := s.sliceTo p) trivial⟩

theorem not_isLongestMatch_tru_startPos : ¬ IsLongestMatch P.tru sA.startPos :=
  fun h => h.not_isMatch sA.endPos (by decide) ⟨trivial⟩
theorem not_isLongestRevMatch_tru_endPos : ¬ IsLongestRevMatch P.tru sA.endPos :=
  fun h => h.not_isRevMatch sA.startPos (by decide) ⟨trivial⟩

theorem not_matchesAt_fal {s : Slice} {p : s.Pos} : ¬ MatchesAt P.fal p :=
  fun ⟨⟨_, h⟩⟩ => h.isLongestMatch_sliceFrom.isMatch.matches_copy
theorem not_revMatchesAt_fal {s : Slice} {p : s.Pos} : ¬ RevMatchesAt P.fal p :=
  fun ⟨⟨_, h⟩⟩ => h.isLongestRevMatch_sliceTo.isRevMatch.matches_copy

theorem emp_lm_startPos {s : Slice} : IsLongestMatch P.emp s.startPos := by
  refine ⟨⟨by simp [PatternModel.Matches]⟩, fun p hp h => ?_⟩
  have := h.matches_copy
  simp [PatternModel.Matches, String.Slice.copy_eq_empty_iff] at this
  exact Std.lt_irrefl (this ▸ hp)

theorem emp_lrm_endPos {s : Slice} : IsLongestRevMatch P.emp s.endPos := by
  refine ⟨⟨by simp [PatternModel.Matches]⟩, fun p hp h => ?_⟩
  have := h.matches_copy
  simp [PatternModel.Matches, String.Slice.copy_eq_empty_iff] at this
  exact Std.lt_irrefl (this ▸ hp)

theorem emp_lma : IsLongestMatchAt P.emp sA.startPos sA.startPos :=
  isLongestMatchAt_startPos_iff.2 emp_lm_startPos
theorem emp_lrma : IsLongestRevMatchAt P.emp sA.endPos sA.endPos :=
  isLongestRevMatchAt_endPos_iff.2 emp_lrm_endPos

/-! ### Inversion of valid searches -/

theorem vsf_nil {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos}
    (h : IsValidSearchFrom pat p []) : p = s.endPos := by
  cases h; rfl

theorem vrsf_nil {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos}
    (h : IsValidRevSearchFrom pat p []) : p = s.startPos := by
  cases h; rfl

theorem vsf_cons {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos} {st l}
    (h : IsValidSearchFrom pat p (st :: l)) :
    p = st.startPos ∧ IsValidSearchFrom pat st.endPos l ∧
    (∀ a b, st = .matched a b → IsLongestMatchAt pat a b) ∧
    (∀ a b, st = .rejected a b → a < b ∧ ∀ pos, a ≤ pos → pos < b → ¬ MatchesAt pat pos) := by
  cases h with
  | matched h₁ h₂ =>
    refine ⟨rfl, h₂, ?_, ?_⟩ <;> intro a b e <;> cases e; exact h₁
  | mismatched h₀ h₁ h₂ =>
    refine ⟨rfl, h₂, ?_, ?_⟩ <;> intro a b e <;> cases e; exact ⟨h₀, h₁⟩

theorem vrsf_cons {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos} {st l}
    (h : IsValidRevSearchFrom pat p (st :: l)) :
    p = st.endPos ∧ IsValidRevSearchFrom pat st.startPos l ∧
    (∀ a b, st = .matched a b → IsLongestRevMatchAt pat a b) ∧
    (∀ a b, st = .rejected a b → a < b ∧ ∀ pos, a < pos → pos ≤ b → ¬ RevMatchesAt pat pos) := by
  cases h with
  | matched h₁ h₂ =>
    refine ⟨rfl, h₂, ?_, ?_⟩ <;> intro a b e <;> cases e; exact h₁
  | mismatched h₀ h₁ h₂ =>
    refine ⟨rfl, h₂, ?_, ?_⟩ <;> intro a b e <;> cases e; exact ⟨h₀, h₁⟩

/-! ### A searcher that skips forever -/

/-- Searcher state whose only step is a skip to itself (not `Finite`). -/
structure LS (s : Slice) where u : Unit

instance (s : Slice) : Iterator (LS s) Id (SearchStep s) where
  IsPlausibleStep it st := st = .skip it
  step it := pure (.deflate ⟨.skip it, rfl⟩)

theorem wf_irrefl {α : Sort _} {r : α → α → Prop} (h : WellFounded r) (a : α) : ¬ r a a := by
  have := h.apply a
  induction this with
  | intro x _ ih => exact fun hx => ih x hx hx

theorem LS.not_finite (s : Slice) : ¬ Iterators.Finite (LS s) Id :=
  fun h => wf_irrefl h.wf ⟨⟨()⟩⟩ ⟨_, rfl, rfl⟩

instance : ToForwardSearcher P.tru LS := ⟨fun _ => ⟨⟨()⟩⟩⟩
instance : ToBackwardSearcher P.tru LS := ⟨fun _ => ⟨⟨()⟩⟩⟩

theorem split_not_finite (s : Slice) : ¬ Iterators.Finite (String.Slice.SplitIterator P.tru s) Id :=
  fun h => wf_irrefl h.wf ⟨.operating s.startPos ⟨⟨()⟩⟩⟩ ⟨.skip ⟨.operating s.startPos ⟨⟨()⟩⟩⟩, rfl, ⟨_, rfl, rfl⟩⟩

theorem splitInclusive_not_finite (s : Slice) :
    ¬ Iterators.Finite (String.Slice.SplitInclusiveIterator P.tru s) Id :=
  fun h => wf_irrefl h.wf ⟨.operating s.startPos ⟨⟨()⟩⟩⟩ ⟨.skip ⟨.operating s.startPos ⟨⟨()⟩⟩⟩, rfl, ⟨_, rfl, rfl⟩⟩

theorem revSplit_not_finite (s : Slice) :
    ¬ Iterators.Finite (String.Slice.RevSplitIterator P.tru s) Id :=
  fun h => wf_irrefl h.wf ⟨.operating s.endPos ⟨⟨()⟩⟩⟩ ⟨.skip ⟨.operating s.endPos ⟨⟨()⟩⟩⟩, rfl, ⟨_, rfl, rfl⟩⟩

end StrPatternHand

open StrPatternHand

/-! ## Casts along `s.copy = t.copy` (dependent): `s = "a"`, `t = ""` -/

-- `String.Slice.Pattern.Model.isMatch_cast_iff` (h : s.copy = t.copy): P.tru, s = "a", t = ""
theorem isMatch_cast_iff.h5 : ¬ indep% String.Slice.Pattern.Model.isMatch_cast_iff 5 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (pos := sA.startPos)) (by decide)

-- `String.Slice.Pattern.Model.isRevMatch_cast_iff` (h : s.copy = t.copy): P.tru, s = "a", t = ""
theorem isRevMatch_cast_iff.h5 : ¬ indep% String.Slice.Pattern.Model.isRevMatch_cast_iff 5 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (pos := sA.startPos)) (by decide)

-- `String.Slice.Pattern.Model.isLongestMatch_cast_iff` (hst): P.tru, s = "a", t = ""
theorem isLongestMatch_cast_iff.h5 : ¬ indep% String.Slice.Pattern.Model.isLongestMatch_cast_iff 5 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (pos := sA.startPos)) (by decide)

-- `String.Slice.Pattern.Model.isLongestRevMatch_cast_iff` (hst): P.tru, s = "a", t = ""
theorem isLongestRevMatch_cast_iff.h5 : ¬ indep% String.Slice.Pattern.Model.isLongestRevMatch_cast_iff 5 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (pos := sA.startPos)) (by decide)

-- `String.Slice.Pattern.Model.isLongestMatchAt_cast_iff` (hst): P.tru, s = "a", t = ""
theorem isLongestMatchAt_cast_iff.h5 : ¬ indep% String.Slice.Pattern.Model.isLongestMatchAt_cast_iff 5 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (startPos := sA.startPos)
    (endPos := sA.startPos)) (by decide)

-- `String.Slice.Pattern.Model.isLongestRevMatchAt_cast_iff` (hst): P.tru, s = "a", t = ""
theorem isLongestRevMatchAt_cast_iff.h5 : ¬ indep% String.Slice.Pattern.Model.isLongestRevMatchAt_cast_iff 5 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (startPos := sA.startPos)
    (endPos := sA.startPos)) (by decide)

-- `String.Slice.Pattern.Model.matchesAt_cast_iff` (hst): P.tru, s = "a", t = ""
theorem matchesAt_cast_iff.h5 : ¬ indep% String.Slice.Pattern.Model.matchesAt_cast_iff 5 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (pos := sA.startPos)) (by decide)

-- `String.Slice.Pattern.Model.revMatchesAt_cast_iff` (hst): P.tru, s = "a", t = ""
theorem revMatchesAt_cast_iff.h5 : ¬ indep% String.Slice.Pattern.Model.revMatchesAt_cast_iff 5 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (pos := sA.startPos)) (by decide)

-- `String.Slice.Pattern.Model.matchAt?_cast` (hst): P.tru, s = "a", t = ""
theorem matchAt?_cast.h5 : ¬ indep% String.Slice.Pattern.Model.matchAt?_cast 5 :=
  fun h => absurd (h (ρ := P) P.tru (s := sA) (t := sE) (startPos := sA.startPos)) (by decide)

-- `String.Slice.Pattern.Model.revMatchAt?_cast` (hst): P.tru, s = "a", t = ""
theorem revMatchAt?_cast.h5 : ¬ indep% String.Slice.Pattern.Model.revMatchAt?_cast 5 :=
  fun h => absurd (h (ρ := P) P.tru (s := sA) (t := sE) (startPos := sA.startPos)) (by decide)

-- `String.Slice.Pattern.Model.isValidSearchFrom_cast_iff` (hst): P.tru, s = "a", t = "", l = []
theorem isValidSearchFrom_cast_iff.h5 : ¬ indep% String.Slice.Pattern.Model.isValidSearchFrom_cast_iff 5 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (pos := sA.startPos) (l := []))
    (by decide)

-- `String.Slice.Pattern.Model.isValidRevSearchFrom_cast_iff` (hst): P.tru, s = "a", t = "", l = []
theorem isValidRevSearchFrom_cast_iff.h5 : ¬ indep% String.Slice.Pattern.Model.isValidRevSearchFrom_cast_iff 5 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (pos := sA.startPos) (l := []))
    (by decide)

-- `String.Slice.Pattern.SearchStep.startPos_cast` (hst): s = "a", t = ""
theorem SearchStep.startPos_cast.h2 : ¬ indep% String.Slice.Pattern.SearchStep.startPos_cast 2 :=
  fun h => absurd (h (s := sA) (t := sE) (st := .matched sA.startPos sA.startPos)) (by decide)

-- `String.Slice.Pattern.SearchStep.endPos_cast` (hst): s = "a", t = ""
theorem SearchStep.endPos_cast.h2 : ¬ indep% String.Slice.Pattern.SearchStep.endPos_cast 2 :=
  fun h => absurd (h (s := sA) (t := sE) (st := .matched sA.startPos sA.startPos)) (by decide)

-- `String.Slice.Pattern.SearchStep.cast_cast` (hst): s = "a", t = u = ""
theorem SearchStep.cast_cast.h3 : ¬ indep% String.Slice.Pattern.SearchStep.cast_cast 3 :=
  fun h => absurd (h (s := sA) (t := sE) (u := sE) (htu := rfl) (st := .matched sA.startPos sA.startPos))
    (by decide)

-- `String.Slice.Pattern.SearchStep.cast_cast` (htu): s = t = "", u = "a"
theorem SearchStep.cast_cast.h4 : ¬ indep% String.Slice.Pattern.SearchStep.cast_cast 4 :=
  fun h => absurd (h (s := sE) (t := sE) (u := sA) (hst := rfl) (st := .matched sE.startPos sE.startPos))
    (by decide)

-- `String.Slice.Pattern.Model.IsLongestMatch.of_eq` (h₁): IsLongestMatch P.tru "a".endPos, t = ""
theorem IsLongestMatch.of_eq.h8 : ¬ indep% String.Slice.Pattern.Model.IsLongestMatch.of_eq 8 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (pos := sA.endPos) (pos' := sE.startPos)
    (tru_lm sA)) (by decide)

-- `String.Slice.Pattern.Model.IsLongestRevMatch.of_eq` (h₁): IsLongestRevMatch P.tru "a".startPos, t = ""
theorem IsLongestRevMatch.of_eq.h8 : ¬ indep% String.Slice.Pattern.Model.IsLongestRevMatch.of_eq 8 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (pos := sA.startPos) (pos' := sE.startPos)
    (tru_lrm sA)) (by decide)

-- `String.Slice.Pattern.Model.IsLongestMatchAt.of_eq` (h₁): IsLongestMatchAt P.tru 0 1 in "a", t = ""
theorem IsLongestMatchAt.of_eq.h10 : ¬ indep% String.Slice.Pattern.Model.IsLongestMatchAt.of_eq 10 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (s₁ := sA.startPos) (e₁ := sA.endPos)
    (s₂ := sE.startPos) (e₂ := sE.startPos) (tru_lma _)) (by decide)

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.of_eq` (h₁): IsLongestRevMatchAt P.tru 0 1 in "a", t = ""
theorem IsLongestRevMatchAt.of_eq.h10 : ¬ indep% String.Slice.Pattern.Model.IsLongestRevMatchAt.of_eq 10 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (t := sE) (s₁ := sA.startPos) (e₁ := sA.endPos)
    (s₂ := sE.startPos) (e₂ := sE.startPos) (tru_lrma _)) (by decide)

/-! ## Position bounds used in `sliceTo`/`sliceFrom` (dependent) -/

-- `String.Slice.Pattern.Model.isMatch_sliceTo_iff` (h : pos ≤ p): pos = "a".endPos, p = startPos
theorem isMatch_sliceTo_iff.h6 : ¬ indep% String.Slice.Pattern.Model.isMatch_sliceTo_iff 6 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (pos := sA.endPos) (p := sA.startPos)) (by decide)

-- `String.Slice.Pattern.Model.isRevMatch_sliceFrom_iff` (h : p ≤ pos): pos = startPos, p = endPos in "a"
theorem isRevMatch_sliceFrom_iff.h6 : ¬ indep% String.Slice.Pattern.Model.isRevMatch_sliceFrom_iff 6 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (pos := sA.startPos) (p := sA.endPos)) (by decide)

-- `String.Slice.Pattern.Model.IsLongestMatch.sliceTo` (hp : pos ≤ p): P.tru, pos = "a".endPos, p = startPos
theorem IsLongestMatch.sliceTo.h7 : ¬ indep% String.Slice.Pattern.Model.IsLongestMatch.sliceTo 7 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (pos := sA.endPos) (tru_lm sA) sA.startPos) (by decide)

-- `String.Slice.Pattern.Model.IsLongestRevMatch.sliceFrom` (hp : p ≤ pos): P.tru, pos = "a".startPos, p = endPos
theorem IsLongestRevMatch.sliceFrom.h7 : ¬ indep% String.Slice.Pattern.Model.IsLongestRevMatch.sliceFrom 7 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (pos := sA.startPos) (tru_lrm sA) sA.endPos) (by decide)

-- `String.Slice.Pattern.Model.IsLongestMatchAt.sliceTo` (hp : endPos ≤ p): P.tru match 0..1 in "a", p = 0
theorem IsLongestMatchAt.sliceTo.h8 : ¬ indep% String.Slice.Pattern.Model.IsLongestMatchAt.sliceTo 8 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (startPos := sA.startPos) (endPos := sA.endPos)
    (tru_lma _) sA.startPos) (by decide)

-- `String.Slice.Pattern.Model.IsLongestMatchAtChain.sliceTo` (hp : endPos ≤ p): empty chain at "a".endPos, p = startPos
theorem IsLongestMatchAtChain.sliceTo.h8 : ¬ indep% String.Slice.Pattern.Model.IsLongestMatchAtChain.sliceTo 8 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (startPos := sA.endPos) (endPos := sA.endPos)
    (.nil _) sA.startPos) (by decide)

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.sliceFrom` (hp : p ≤ startPos): P.tru match 0..1 in "a", p = 1
theorem IsLongestRevMatchAt.sliceFrom.h8 : ¬ indep% String.Slice.Pattern.Model.IsLongestRevMatchAt.sliceFrom 8 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (startPos := sA.startPos) (endPos := sA.endPos)
    (tru_lrma _) sA.endPos) (by decide)

-- `String.Slice.Pattern.Model.IsLongestRevMatchAtChain.sliceFrom` (hp : p ≤ startPos): empty chain at "a".startPos, p = endPos
theorem IsLongestRevMatchAtChain.sliceFrom.h8 : ¬ indep% String.Slice.Pattern.Model.IsLongestRevMatchAtChain.sliceFrom 8 :=
  fun h => absurd (h (ρ := P) (pat := P.tru) (s := sA) (startPos := sA.startPos) (endPos := sA.startPos)
    (.nil _) sA.endPos) (by decide)

/-! ## Non-dependent hypotheses of the model lemmas -/

-- `String.Slice.Pattern.Model.IsLongestMatch.not_isMatch` (a : pos < pos'): pos = pos' = endPos
theorem IsLongestMatch.not_isMatch.h7 : ¬ drop% String.Slice.Pattern.Model.IsLongestMatch.not_isMatch 7 :=
  fun h => h (tru_lm sA) sA.endPos ⟨trivial⟩

-- `String.Slice.Pattern.Model.IsLongestRevMatch.not_isRevMatch` (a : pos' < pos): pos = pos' = startPos
theorem IsLongestRevMatch.not_isRevMatch.h7 : ¬ drop% String.Slice.Pattern.Model.IsLongestRevMatch.not_isRevMatch 7 :=
  fun h => h (tru_lrm sA) sA.startPos ⟨trivial⟩

-- `String.Slice.Pattern.Model.IsLongestMatch.of_eq` (h₂ : pos.cast h₁ = pos'): pos' = startPos
theorem IsLongestMatch.of_eq.h9 : ¬ drop% String.Slice.Pattern.Model.IsLongestMatch.of_eq 9 :=
  fun h => not_isLongestMatch_tru_startPos (h (s := sA) (t := sA) (pos := sA.endPos) (pos' := sA.startPos)
    (tru_lm sA) rfl)

-- `String.Slice.Pattern.Model.IsLongestRevMatch.of_eq` (h₂ : pos.cast h₁ = pos'): pos' = endPos
theorem IsLongestRevMatch.of_eq.h9 : ¬ drop% String.Slice.Pattern.Model.IsLongestRevMatch.of_eq 9 :=
  fun h => not_isLongestRevMatch_tru_endPos (h (s := sA) (t := sA) (pos := sA.startPos) (pos' := sA.endPos)
    (tru_lrm sA) rfl)

-- `String.Slice.Pattern.Model.IsLongestMatchAt.of_eq` (h₂ : s₁.cast h₁ = s₂): P.emp, s₂ = endPos
theorem IsLongestMatchAt.of_eq.h11 : ¬ drop% String.Slice.Pattern.Model.IsLongestMatchAt.of_eq 11 :=
  fun h => absurd (h (s := sA) (t := sA) (s₁ := sA.startPos) (e₁ := sA.startPos) (s₂ := sA.endPos)
    (e₂ := sA.startPos) emp_lma rfl (by decide)).le (by decide)

-- `String.Slice.Pattern.Model.IsLongestMatchAt.of_eq` (h₃ : e₁.cast h₁ = e₂): P.tru, e₂ = startPos
theorem IsLongestMatchAt.of_eq.h12 : ¬ drop% String.Slice.Pattern.Model.IsLongestMatchAt.of_eq 12 :=
  fun h => absurd (h (s := sA) (t := sA) (s₁ := sA.endPos) (e₁ := sA.endPos) (s₂ := sA.endPos)
    (e₂ := sA.startPos) (tru_lma _) rfl (by decide)).le (by decide)

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.of_eq` (h₂ : s₁.cast h₁ = s₂): P.tru, s₂ = endPos
theorem IsLongestRevMatchAt.of_eq.h11 : ¬ drop% String.Slice.Pattern.Model.IsLongestRevMatchAt.of_eq 11 :=
  fun h => absurd (h (s := sA) (t := sA) (s₁ := sA.startPos) (e₁ := sA.startPos) (s₂ := sA.endPos)
    (e₂ := sA.startPos) (tru_lrma _) rfl (by decide)).le (by decide)

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.of_eq` (h₃ : e₁.cast h₁ = e₂): P.emp, e₂ = startPos
theorem IsLongestRevMatchAt.of_eq.h12 : ¬ drop% String.Slice.Pattern.Model.IsLongestRevMatchAt.of_eq 12 :=
  fun h => absurd (h (s := sA) (t := sA) (s₁ := sA.endPos) (e₁ := sA.endPos) (s₂ := sA.endPos)
    (e₂ := sA.startPos) emp_lrma (by decide) rfl).le (by decide)

/-! ## Valid searches -/

-- `String.Slice.Pattern.Model.IsValidSearchFrom.matched_of_eq` (h₃ : startPos = startPos'): P.tru in "a", step .matched 1 1 from 0
theorem IsValidSearchFrom.matched_of_eq.h10 : ¬ drop% String.Slice.Pattern.Model.IsValidSearchFrom.matched_of_eq 10 :=
  fun h => absurd (vsf_cons (h (pat := P.tru) (s := sA) (startPos := sA.endPos) (startPos' := sA.startPos)
    (endPos := sA.endPos) (l := []) .endPos (tru_lma _))).1 (by decide)

-- `String.Slice.Pattern.Model.IsValidSearchFrom.mismatched_of_eq` (h₀ : startPos' < endPos): P.tru in "a", step .rejected 1 1 from 1
theorem IsValidSearchFrom.mismatched_of_eq.h9 : ¬ drop% String.Slice.Pattern.Model.IsValidSearchFrom.mismatched_of_eq 9 :=
  fun h => absurd ((vsf_cons (h (pat := P.tru) (s := sA) (startPos := sA.endPos) (startPos' := sA.endPos)
    (endPos := sA.endPos) (l := []) .endPos (fun p h₁ h₂ => absurd (Std.lt_of_le_of_lt h₁ h₂) (Std.lt_irrefl))
    rfl)).2.2.2 _ _ rfl).1 (by decide)

-- `String.Slice.Pattern.Model.IsValidSearchFrom.mismatched_of_eq` (h₃ : startPos = startPos'): P.fal step .rejected 1 1 from 0 in "a"
theorem IsValidSearchFrom.mismatched_of_eq.h11 : ¬ drop% String.Slice.Pattern.Model.IsValidSearchFrom.mismatched_of_eq 11 :=
  fun h => absurd (vsf_cons (h (pat := P.fal) (s := sA) (startPos := sA.endPos) (startPos' := sA.startPos)
    (endPos := sA.endPos) (l := []) .endPos (by decide) (fun _ _ _ => not_matchesAt_fal))).1 (by decide)

-- `String.Slice.Pattern.Model.IsValidSearchFrom.endPos_of_eq` (hp : p = s.endPos): p = startPos in "a", l = []
theorem IsValidSearchFrom.endPos_of_eq.h6 : ¬ drop% String.Slice.Pattern.Model.IsValidSearchFrom.endPos_of_eq 6 :=
  fun h => absurd (vsf_nil (h (pat := P.tru) (s := sA) (p := sA.startPos) (l := []) rfl)) (by decide)

-- `String.Slice.Pattern.Model.IsValidSearchFrom.endPos_of_eq` (hl : l = []): l = [.rejected e e] (rejected range empty) in "a", p = endPos
theorem IsValidSearchFrom.endPos_of_eq.h7 : ¬ drop% String.Slice.Pattern.Model.IsValidSearchFrom.endPos_of_eq 7 :=
  fun h => absurd ((vsf_cons (h (pat := P.tru) (s := sA) (p := sA.endPos)
    (l := [.rejected sA.endPos sA.endPos]) rfl)).2.2.2 _ _ rfl).1 (by decide)

-- `String.Slice.Pattern.Model.IsValidRevSearchFrom.matched_of_eq` (h₃ : endPos = endPos'): P.tru in "a", step .matched 0 0 from 1
theorem IsValidRevSearchFrom.matched_of_eq.h10 : ¬ drop% String.Slice.Pattern.Model.IsValidRevSearchFrom.matched_of_eq 10 :=
  fun h => absurd (vrsf_cons (h (pat := P.tru) (s := sA) (startPos := sA.startPos) (endPos := sA.startPos)
    (endPos' := sA.endPos) (l := []) .startPos (tru_lrma _))).1 (by decide)

-- `String.Slice.Pattern.Model.IsValidRevSearchFrom.mismatched_of_eq` (h₀ : startPos < endPos'): P.tru in "a", step .rejected 0 0 from 0
theorem IsValidRevSearchFrom.mismatched_of_eq.h9 : ¬ drop% String.Slice.Pattern.Model.IsValidRevSearchFrom.mismatched_of_eq 9 :=
  fun h => absurd ((vrsf_cons (h (pat := P.tru) (s := sA) (startPos := sA.startPos) (endPos := sA.startPos)
    (endPos' := sA.startPos) (l := []) .startPos (fun p h₁ h₂ => absurd (Std.lt_of_lt_of_le h₁ h₂) (Std.lt_irrefl))
    rfl)).2.2.2 _ _ rfl).1 (by decide)

-- `String.Slice.Pattern.Model.IsValidRevSearchFrom.mismatched_of_eq` (h₃ : endPos = endPos'): P.fal step .rejected 0 0 from 1 in "a"
theorem IsValidRevSearchFrom.mismatched_of_eq.h11 : ¬ drop% String.Slice.Pattern.Model.IsValidRevSearchFrom.mismatched_of_eq 11 :=
  fun h => absurd (vrsf_cons (h (pat := P.fal) (s := sA) (startPos := sA.startPos) (endPos := sA.startPos)
    (endPos' := sA.endPos) (l := []) .startPos (by decide) (fun _ _ _ => not_revMatchesAt_fal))).1 (by decide)

-- `String.Slice.Pattern.Model.IsValidRevSearchFrom.startPos_of_eq` (hp : p = s.startPos): p = "a".endPos, l = []
theorem IsValidRevSearchFrom.startPos_of_eq.h6 : ¬ drop% String.Slice.Pattern.Model.IsValidRevSearchFrom.startPos_of_eq 6 :=
  fun h => absurd (vrsf_nil (h (pat := P.tru) (s := sA) (p := sA.endPos) (l := []) rfl)) (by decide)

-- `String.Slice.Pattern.Model.IsValidRevSearchFrom.startPos_of_eq` (hl : l = []): l = [.rejected 0 0] in "a"
theorem IsValidRevSearchFrom.startPos_of_eq.h7 : ¬ drop% String.Slice.Pattern.Model.IsValidRevSearchFrom.startPos_of_eq 7 :=
  fun h => absurd ((vrsf_cons (h (pat := P.tru) (s := sA) (p := sA.startPos)
    (l := [.rejected sA.startPos sA.startPos]) rfl)).2.2.2 _ _ rfl).1 (by decide)

/-! ## Searcher finiteness (`LS` skips forever) -/

-- `String.Slice.Pattern.Model.LawfulToForwardSearcherModel.isValidSearchFrom_toList` (∀ s, Finite (σ s) Id): σ = LS skips forever
theorem LawfulToForwardSearcherModel.isValidSearchFrom_toList.h6 :
    ¬ indep% String.Slice.Pattern.Model.LawfulToForwardSearcherModel.isValidSearchFrom_toList 6 :=
  fun h => LS.not_finite sE (@h P P.tru inferInstance LS inferInstance _ sE sE)

-- `String.Slice.Pattern.Model.LawfulToBackwardSearcherModel.isValidRevSearchFrom_toList` (∀ s, Finite (σ s) Id): σ = LS skips forever
theorem LawfulToBackwardSearcherModel.isValidRevSearchFrom_toList.h6 :
    ¬ indep% String.Slice.Pattern.Model.LawfulToBackwardSearcherModel.isValidRevSearchFrom_toList 6 :=
  fun h => LS.not_finite sE (@h P P.tru inferInstance LS inferInstance _ sE sE)

-- `String.Slice.SplitIterator.instFiniteIdSubsliceOfSearchStep` (Finite (σ s) Id): σ = LS, the split iterator skips forever
theorem SplitIterator.instFinite.h6 : ¬ drop% String.Slice.SplitIterator.instFiniteIdSubsliceOfSearchStep 6 :=
  fun h => split_not_finite sE (h (pat := P.tru) (σ := LS) (s := sE))

-- `String.Slice.SplitInclusiveIterator.instFiniteIdOfSearchStep` (Finite (σ s) Id): σ = LS, the split iterator skips forever
theorem SplitInclusiveIterator.instFinite.h6 : ¬ drop% String.Slice.SplitInclusiveIterator.instFiniteIdOfSearchStep 6 :=
  fun h => splitInclusive_not_finite sE (h (pat := P.tru) (σ := LS) (s := sE))

-- `String.Slice.RevSplitIterator.instFiniteIdOfSearchStep` (Finite (σ s) Id): σ = LS, the split iterator skips forever
theorem RevSplitIterator.instFinite.h6 : ¬ drop% String.Slice.RevSplitIterator.instFiniteIdOfSearchStep 6 :=
  fun h => revSplit_not_finite sE (@h P P.tru LS _ _ sE)

/-! ## `ForwardPattern`/`BackwardPattern` fields on the empty slice (dependent): `Char` pattern `'a'` -/

-- `String.Slice.Pattern.LawfulForwardPattern.skipPrefixOfNonempty?_eq` (h : s.isEmpty = false): pat = 'a', s = ""
theorem LawfulForwardPattern.skipPrefixOfNonempty?_eq.h5 :
    ¬ indep% String.Slice.Pattern.LawfulForwardPattern.skipPrefixOfNonempty?_eq 5 :=
  fun h => absurd (h (pat := 'a') (s := sE)) (by decide)

-- `String.Slice.Pattern.LawfulBackwardPattern.skipSuffixOfNonempty?_eq` (h : s.isEmpty = false): pat = 'a', s = ""
theorem LawfulBackwardPattern.skipSuffixOfNonempty?_eq.h5 :
    ¬ indep% String.Slice.Pattern.LawfulBackwardPattern.skipSuffixOfNonempty?_eq 5 :=
  fun h => absurd (h (pat := 'a') (s := sE)) (by decide)

-- `String.Slice.Pattern.StrictForwardPattern.ne_startPos` (h : s.isEmpty = false): pat = 'a', s = ""
theorem StrictForwardPattern.ne_startPos.h5 : ¬ indep% String.Slice.Pattern.StrictForwardPattern.ne_startPos 5 :=
  fun h => absurd (h (pat := 'a') (s := sE) sE.startPos) (by decide)

-- `String.Slice.Pattern.StrictBackwardPattern.ne_endPos` (h : s.isEmpty = false): pat = 'a', s = ""
theorem StrictBackwardPattern.ne_endPos.h5 : ¬ indep% String.Slice.Pattern.StrictBackwardPattern.ne_endPos 5 :=
  fun h => absurd (h (pat := 'a') (s := sE) sE.startPos) (by decide)

/-! ## `Char` and predicate patterns: drop the character test (`"a"`, position `0` or `1`) -/

-- `String.Slice.Pattern.Model.Char.isLongestMatchAt_of_get_eq` (hc): c = 'b'
theorem Char.isLongestMatchAt_of_get_eq.h4 : ¬ drop% String.Slice.Pattern.Model.Char.isLongestMatchAt_of_get_eq 4 :=
  fun h => absurd (h (c := 'b') (s := sA) (pos := sA.startPos) (h := by decide))
    (by rw [Char.isLongestMatchAt_iff]; decide)

-- `String.Slice.Pattern.Model.Char.isLongestRevMatchAt_of_get_eq` (hc): c = 'b'
theorem Char.isLongestRevMatchAt_of_get_eq.h4 : ¬ drop% String.Slice.Pattern.Model.Char.isLongestRevMatchAt_of_get_eq 4 :=
  fun h => absurd (h (c := 'b') (s := sA) (pos := sA.endPos) (h := by decide))
    (by rw [Char.isLongestRevMatchAt_iff]; decide +kernel)

-- `String.Slice.Pattern.Model.Char.not_matchesAt_of_get_ne` (hc): c = 'a'
theorem Char.not_matchesAt_of_get_ne.h4 : ¬ drop% String.Slice.Pattern.Model.Char.not_matchesAt_of_get_ne 4 :=
  fun h => h (c := 'a') (s := sA) (pos := sA.startPos) (h := by decide)
    (by rw [Char.matchesAt_iff]; decide)

-- `String.Slice.Pattern.Model.Char.not_revMatchesAt_of_get_ne` (hc): c = 'a'
theorem Char.not_revMatchesAt_of_get_ne.h4 : ¬ drop% String.Slice.Pattern.Model.Char.not_revMatchesAt_of_get_ne 4 :=
  fun h => h (c := 'a') (s := sA) (pos := sA.endPos) (h := by decide)
    (by rw [Char.revMatchesAt_iff]; decide +kernel)

-- `String.Slice.Pattern.Model.CharPred.isLongestMatchAt_of_get` (hc): p = fun _ => false
theorem CharPred.isLongestMatchAt_of_get.h4 : ¬ drop% String.Slice.Pattern.Model.CharPred.isLongestMatchAt_of_get 4 :=
  fun h => absurd (h (p := fun _ => false) (s := sA) (pos := sA.startPos) (h := by decide))
    (by rw [CharPred.isLongestMatchAt_iff]; simp)

-- `String.Slice.Pattern.Model.CharPred.isLongestRevMatchAt_of_get` (hc): p = fun _ => false
theorem CharPred.isLongestRevMatchAt_of_get.h4 : ¬ drop% String.Slice.Pattern.Model.CharPred.isLongestRevMatchAt_of_get 4 :=
  fun h => absurd (h (p := fun _ => false) (s := sA) (pos := sA.endPos) (h := by decide))
    (by rw [CharPred.isLongestRevMatchAt_iff]; simp)

-- `String.Slice.Pattern.Model.CharPred.not_matchesAt_of_get` (hc): p = fun _ => true
theorem CharPred.not_matchesAt_of_get.h4 : ¬ drop% String.Slice.Pattern.Model.CharPred.not_matchesAt_of_get 4 :=
  fun h => h (p := fun _ => true) (s := sA) (pos := sA.startPos) (h := by decide)
    (by rw [CharPred.matchesAt_iff]; decide)

-- `String.Slice.Pattern.Model.CharPred.not_revMatchesAt_of_get` (hc): p = fun _ => true
theorem CharPred.not_revMatchesAt_of_get.h4 : ¬ drop% String.Slice.Pattern.Model.CharPred.not_revMatchesAt_of_get 4 :=
  fun h => h (p := fun _ => true) (s := sA) (pos := sA.endPos) (h := by decide)
    (by rw [CharPred.revMatchesAt_iff]; decide)

-- `String.Slice.Pattern.Model.CharPred.Decidable.isLongestMatchAt_of_get` (hc): p = fun _ => False
theorem CharPred.Decidable.isLongestMatchAt_of_get.h5 :
    ¬ drop% String.Slice.Pattern.Model.CharPred.Decidable.isLongestMatchAt_of_get 5 :=
  fun h => absurd (h (p := fun _ => False) (s := sA) (pos := sA.startPos) (h := by decide))
    (by rw [CharPred.Decidable.isLongestMatchAt_iff]; simp)

-- `String.Slice.Pattern.Model.CharPred.Decidable.isLongestRevMatchAt_of_get` (hc): p = fun _ => False
theorem CharPred.Decidable.isLongestRevMatchAt_of_get.h5 :
    ¬ drop% String.Slice.Pattern.Model.CharPred.Decidable.isLongestRevMatchAt_of_get 5 :=
  fun h => absurd (h (p := fun _ => False) (s := sA) (pos := sA.endPos) (h := by decide))
    (by rw [CharPred.Decidable.isLongestRevMatchAt_iff]; simp)

-- `String.Slice.Pattern.Model.CharPred.Decidable.not_matchesAt_of_get` (hc): p = fun _ => True
theorem CharPred.Decidable.not_matchesAt_of_get.h5 :
    ¬ drop% String.Slice.Pattern.Model.CharPred.Decidable.not_matchesAt_of_get 5 :=
  fun h => h (p := fun _ => True) (s := sA) (pos := sA.startPos) (h := by decide)
    (by rw [CharPred.Decidable.matchesAt_iff]; decide)

-- `String.Slice.Pattern.Model.CharPred.Decidable.not_revMatchesAt_of_get` (hc): p = fun _ => True
theorem CharPred.Decidable.not_revMatchesAt_of_get.h5 :
    ¬ drop% String.Slice.Pattern.Model.CharPred.Decidable.not_revMatchesAt_of_get 5 :=
  fun h => h (p := fun _ => True) (s := sA) (pos := sA.endPos) (h := by decide)
    (by rw [CharPred.Decidable.revMatchesAt_iff]; decide)

/-! ## Slice and string patterns with the empty pattern -/

namespace StrPatternHand

/-- With an empty slice pattern the longest match at `p` is the empty one, ending at `p`. -/
theorem fss_lma_empty {pat s : Slice} (hp : pat.isEmpty = true) {p q : s.Pos} :
    IsLongestMatchAt pat p q ↔ p = q := by
  have hc : pat.copy = "" := String.Slice.copy_eq_empty_iff.2 hp
  rw [ForwardSliceSearcher.isLongestMatchAt_iff_splits, hc]
  constructor
  · rintro ⟨t₁, t₂, h₁, h₂⟩
    simp only [String.empty_append, String.append_empty] at h₁ h₂
    exact h₁.pos_eq h₂
  · rintro rfl
    exact ⟨_, _, by simpa using p.splits, by simpa using p.splits⟩

theorem fss_lrma_empty {pat s : Slice} (hp : pat.isEmpty = true) {p q : s.Pos} :
    IsLongestRevMatchAt pat p q ↔ p = q := by
  rw [ForwardSliceSearcher.isLongestRevMatchAt_iff_splits, ← ForwardSliceSearcher.isLongestMatchAt_iff_splits]
  exact fss_lma_empty hp

end StrPatternHand

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.strictPatternModel` (hpat : pat.isEmpty = false): pat = "" matches ""
theorem FSS.strictPatternModel.h1 : ¬ drop% String.Slice.Pattern.Model.ForwardSliceSearcher.strictPatternModel 1 :=
  fun h => (h (pat := "".toSlice)).not_matches_empty (by simp [PatternModel.Matches])

-- `String.Slice.Pattern.Model.ForwardStringSearcher.strictPatternModel` (h : pat ≠ ""): pat = "" matches ""
theorem FStr.strictPatternModel.h1 : ¬ drop% String.Slice.Pattern.Model.ForwardStringSearcher.strictPatternModel 1 :=
  fun h => (h (pat := "")).not_matches_empty rfl

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.isLongestMatchAt_iff_extract` (h): empty pattern,
-- pos₁ = "a".endPos > pos₂ = startPos: no match, but the extracted byte range is empty
theorem FSS.isLongestMatchAt_iff_extract.h4 :
    ¬ drop% String.Slice.Pattern.Model.ForwardSliceSearcher.isLongestMatchAt_iff_extract 4 :=
  fun h => absurd ((h (pat := "".toSlice) (s := sA) (pos₁ := sA.endPos) (pos₂ := sA.startPos)).2 (by decide)).le
    (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.isLongestRevMatchAt_iff_extract` (h): empty pattern, pos₁ = "a".endPos > pos₂ = startPos
theorem FSS.isLongestRevMatchAt_iff_extract.h4 :
    ¬ drop% String.Slice.Pattern.Model.ForwardSliceSearcher.isLongestRevMatchAt_iff_extract 4 :=
  fun h => absurd ((h (pat := "".toSlice) (s := sA) (pos₁ := sA.endPos) (pos₂ := sA.startPos)).2 (by decide)).le
    (by decide)

-- `String.Slice.Pattern.Model.ForwardStringSearcher.isLongestMatchAt_iff_extract` (h : pat ≠ ""): pat = "", pos₁ = "a".endPos > pos₂ = startPos
theorem FStr.isLongestMatchAt_iff_extract.h4 :
    ¬ drop% String.Slice.Pattern.Model.ForwardStringSearcher.isLongestMatchAt_iff_extract 4 :=
  fun h => absurd ((h (pat := "") (s := sA) (pos₁ := sA.endPos) (pos₂ := sA.startPos)).2 (by decide)).le
    (by decide)

-- `String.Slice.Pattern.Model.ForwardStringSearcher.isLongestRevMatchAt_iff_extract` (h : pat ≠ ""): pat = "", pos₁ = "a".endPos > pos₂ = startPos
theorem FStr.isLongestRevMatchAt_iff_extract.h4 :
    ¬ drop% String.Slice.Pattern.Model.ForwardStringSearcher.isLongestRevMatchAt_iff_extract 4 :=
  fun h => absurd ((h (pat := "") (s := sA) (pos₁ := sA.endPos) (pos₂ := sA.startPos)).2 (by decide)).le
    (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.toSearcher_of_isEmpty` (hpat : pat.isEmpty = true):
-- pat = "a" gives the KMP state, not emptyBefore
theorem FSS.toSearcher_of_isEmpty.h1 : ¬ drop% String.Slice.Pattern.Model.ForwardSliceSearcher.toSearcher_of_isEmpty 1 :=
  fun h => absurd (h (pat := "a".toSlice) sA)
    (by simp [ToForwardSearcher.toSearcher, ForwardSliceSearcher.iter])

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.lawfulToForwardSearcherModel` (hpat): empty pattern on
-- "a": the searcher rejects [0, 1) although the empty match is at 0
theorem FSS.lawfulToForwardSearcherModel.h1 :
    ¬ drop% String.Slice.Pattern.Model.ForwardSliceSearcher.lawfulToForwardSearcherModel 1 := by
  intro h
  have hv := (h (pat := "".toSlice)).isValidSearchFrom_toList sA
  rw [ForwardSliceSearcher.toSearcher_of_isEmpty (by decide), ForwardSliceSearcher.toList_emptyBefore_eq,
    dif_neg (by decide), ForwardSliceSearcher.toList_emptyAt_eq] at hv
  exact ((vsf_cons (vsf_cons hv).2.1).2.2.2 _ _ rfl).2 sA.startPos (Std.le_refl _) (by decide +kernel)
    ⟨⟨sA.startPos, (fss_lma_empty (by decide)).2 rfl⟩⟩

-- `String.Slice.Pattern.Model.ForwardStringSearcher.lawfulToForwardSearcherModel` (hpat : pat ≠ ""): pat = "" on "a": rejects [0, 1) although "" matches at 0
theorem FStr.lawfulToForwardSearcherModel.h1 :
    ¬ drop% String.Slice.Pattern.Model.ForwardStringSearcher.lawfulToForwardSearcherModel 1 := by
  intro h
  have hv := (h (pat := "")).isValidSearchFrom_toList sA
  rw [ForwardStringSearcher.toSearcher_empty, ForwardSliceSearcher.toList_emptyBefore_eq,
    dif_neg (by decide), ForwardSliceSearcher.toList_emptyAt_eq] at hv
  exact ((vsf_cons (vsf_cons hv).2.1).2.2.2 _ _ rfl).2 sA.startPos (Std.le_refl _) (by decide +kernel)
    ⟨⟨sA.startPos, ForwardStringSearcher.isLongestMatchAt_iff_isLongestMatchAt_toSlice.2
      ((fss_lma_empty (by decide)).2 rfl)⟩⟩

/-! ### Removable: with an empty pattern the longest match is empty, so the offsets agree -/

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.offset_of_isLongestMatchAt` (h): removable; an empty
-- pattern only matches pos₁ = pos₂ and has size 0
theorem FSS.offset_of_isLongestMatchAt.h4 :
    drop% String.Slice.Pattern.Model.ForwardSliceSearcher.offset_of_isLongestMatchAt 4 := by
  intro pat s pos₁ pos₂ h'
  cases hp : pat.isEmpty
  · exact ForwardSliceSearcher.offset_of_isLongestMatchAt hp h'
  · obtain rfl := (fss_lma_empty hp).1 h'
    have : pat.utf8ByteSize = 0 := String.Slice.isEmpty_iff.1 hp
    simp [this]

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.offset_of_isLongestRevMatchAt` (h): removable, as above; an empty pattern only matches pos₁ = pos₂ and has size 0
theorem FSS.offset_of_isLongestRevMatchAt.h4 :
    drop% String.Slice.Pattern.Model.ForwardSliceSearcher.offset_of_isLongestRevMatchAt 4 := by
  intro pat s pos₁ pos₂ h'
  cases hp : pat.isEmpty
  · exact ForwardSliceSearcher.offset_of_isLongestRevMatchAt hp h'
  · obtain rfl := (fss_lrma_empty hp).1 h'
    have : pat.utf8ByteSize = 0 := String.Slice.isEmpty_iff.1 hp
    simp [this]

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.matchesAt_iff_isLongestMatchAt` (h): removable; the
-- library proof with the removable offset_of_isLongestMatchAt above
theorem FSS.matchesAt_iff_isLongestMatchAt.h3 :
    drop% String.Slice.Pattern.Model.ForwardSliceSearcher.matchesAt_iff_isLongestMatchAt 3 := by
  intro pat s pos
  refine ⟨fun ⟨⟨p, h'⟩⟩ => ?_, fun ⟨_, h⟩ => ⟨⟨_, h⟩⟩⟩
  have := FSS.offset_of_isLongestMatchAt.h4 h' ▸ p.isValidForSlice
  refine ⟨this, ?_⟩
  obtain rfl : p = s.pos _ this := by
    simpa [String.Slice.Pos.ext_iff] using FSS.offset_of_isLongestMatchAt.h4 h'
  exact h'

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.revMatchesAt_iff_isLongestRevMatchAt` (h): removable;
-- the library proof with the removable offset_of_isLongestRevMatchAt above
theorem FSS.revMatchesAt_iff_isLongestRevMatchAt.h3 :
    drop% String.Slice.Pattern.Model.ForwardSliceSearcher.revMatchesAt_iff_isLongestRevMatchAt 3 := by
  intro pat s pos
  refine ⟨fun ⟨⟨p, h'⟩⟩ => ?_, fun ⟨_, h⟩ => ⟨⟨_, h⟩⟩⟩
  have hoff := FSS.offset_of_isLongestRevMatchAt.h4 h'
  have hvalid : (pos.offset.decreaseBy pat.utf8ByteSize).IsValidForSlice s := by
    rw [show pos.offset.decreaseBy pat.utf8ByteSize = p.offset from by
      simp [String.Pos.Raw.ext_iff, String.Pos.Raw.byteIdx_decreaseBy, String.Pos.Raw.byteIdx_increaseBy] at hoff ⊢
      omega]
    exact p.isValidForSlice
  refine ⟨hvalid, ?_⟩
  obtain rfl : p = s.pos _ hvalid := by
    simp only [String.Slice.Pos.ext_iff, String.Slice.offset_pos]
    simp [String.Pos.Raw.ext_iff, String.Pos.Raw.byteIdx_decreaseBy, String.Pos.Raw.byteIdx_increaseBy] at hoff ⊢
    omega
  exact h'

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.matchesAt_iff_getElem` (h): removable; for an empty
-- pattern both sides hold (empty match; pos is in bounds and there are no bytes to compare)
theorem FSS.matchesAt_iff_getElem.h3 :
    drop% String.Slice.Pattern.Model.ForwardSliceSearcher.matchesAt_iff_getElem 3 := by
  intro pat s pos
  cases hp : pat.isEmpty
  · exact ForwardSliceSearcher.matchesAt_iff_getElem hp
  · have hc : pat.copy = "" := String.Slice.copy_eq_empty_iff.2 hp
    exact ⟨fun _ => ⟨by simp [hc], fun j hj => absurd hj (by simp [hc])⟩,
      fun _ => ⟨⟨pos, (fss_lma_empty hp).2 rfl⟩⟩⟩

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.le_of_matchesAt` (h): removable; for an empty pattern
-- the claim is pos.offset ≤ s.rawEndPos
theorem FSS.le_of_matchesAt.h3 :
    drop% String.Slice.Pattern.Model.ForwardSliceSearcher.le_of_matchesAt 3 := by
  intro pat s pos h'
  cases hp : pat.isEmpty
  · exact ForwardSliceSearcher.le_of_matchesAt hp h'
  · have : pat.utf8ByteSize = 0 := String.Slice.isEmpty_iff.1 hp
    simp [this]

-- `String.Slice.Pattern.Model.ForwardStringSearcher.offset_of_isLongestMatchAt` (h : pat ≠ ""): removable;
-- the library proof with the removable slice version; empty pattern: only the empty match, size 0
theorem FStr.offset_of_isLongestMatchAt.h4 :
    drop% String.Slice.Pattern.Model.ForwardStringSearcher.offset_of_isLongestMatchAt 4 := by
  intro pat s pos₁ pos₂ h'
  rw [show pat.utf8ByteSize = pat.toSlice.utf8ByteSize from String.utf8ByteSize_toSlice.symm]
  exact FSS.offset_of_isLongestMatchAt.h4
    (ForwardStringSearcher.isLongestMatchAt_iff_isLongestMatchAt_toSlice.1 h')

-- `String.Slice.Pattern.Model.ForwardStringSearcher.offset_of_isLongestRevMatchAt` (h : pat ≠ ""): removable; the library proof with the removable slice version
theorem FStr.offset_of_isLongestRevMatchAt.h4 :
    drop% String.Slice.Pattern.Model.ForwardStringSearcher.offset_of_isLongestRevMatchAt 4 := by
  intro pat s pos₁ pos₂ h'
  rw [show pat.utf8ByteSize = pat.toSlice.utf8ByteSize from String.utf8ByteSize_toSlice.symm]
  exact FSS.offset_of_isLongestRevMatchAt.h4
    (ForwardStringSearcher.isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice.1 h')

-- `String.Slice.Pattern.Model.ForwardStringSearcher.matchesAt_iff_isLongestMatchAt` (h : pat ≠ ""): removable; the library proof with the removable slice version
theorem FStr.matchesAt_iff_isLongestMatchAt.h3 :
    drop% String.Slice.Pattern.Model.ForwardStringSearcher.matchesAt_iff_isLongestMatchAt 3 := by
  intro pat s pos
  have key := FSS.matchesAt_iff_isLongestMatchAt.h3 (pat := pat.toSlice) (pos := pos)
  simp only [String.utf8ByteSize_toSlice,
    ← ForwardStringSearcher.isLongestMatchAt_iff_isLongestMatchAt_toSlice] at key
  rwa [ForwardStringSearcher.matchesAt_iff_toSlice]

-- `String.Slice.Pattern.Model.ForwardStringSearcher.revMatchesAt_iff_isLongestRevMatchAt` (h : pat ≠ ""): removable; the library proof with the removable slice version
theorem FStr.revMatchesAt_iff_isLongestRevMatchAt.h3 :
    drop% String.Slice.Pattern.Model.ForwardStringSearcher.revMatchesAt_iff_isLongestRevMatchAt 3 := by
  intro pat s pos
  have key := FSS.revMatchesAt_iff_isLongestRevMatchAt.h3 (pat := pat.toSlice) (pos := pos)
  simp only [String.utf8ByteSize_toSlice,
    ← ForwardStringSearcher.isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice] at key
  rwa [ForwardStringSearcher.revMatchesAt_iff_toSlice]

-- `String.Slice.Pattern.Model.ForwardStringSearcher.matchesAt_iff_getElem` (h : pat ≠ ""): removable; the library proof with the removable slice version
theorem FStr.matchesAt_iff_getElem.h3 :
    drop% String.Slice.Pattern.Model.ForwardStringSearcher.matchesAt_iff_getElem 3 := by
  intro pat s pos
  have key := FSS.matchesAt_iff_getElem.h3 (pat := pat.toSlice) (pos := pos)
  simp only [String.copy_toSlice] at key
  rwa [ForwardStringSearcher.matchesAt_iff_toSlice]
