/-!
Hand resolution of the 151 hypotheses (108 theorems) about string search patterns
(`String.Slice.Pattern.*`, `String.Slice.Pattern.Model.*` in `Init.Data.String.Pattern.Basic`,
`Init.Data.String.Lemmas.Pattern.Basic`, `…Pattern.Find.Basic`, `…Pattern.Split.Basic`) that
`HypCheck.lean` left unresolved. For each hypothesis `hᵢ` of theorem `T`, this file proves `¬T'`
(`T` without `hᵢ`), or, for the 15 dependent ones, `¬ ∀ indep, Hᵢ`. All 151 are necessary.

Dependent hypotheses: `[StrictPatternModel pat]` in the five `Model.split` lemmas (the
statement mentions `Model.split`, which takes the instance), `[StrictForwardPattern pat]` /
`[StrictBackwardPattern pat]` in `LawfulTo{Forward,Backward}SearcherModel.defaultImplementation`
(the `Finite` instance of the default searcher in the statement uses it), and the
`IsLongestMatchAt`/`IsLongestRevMatchAt`/chain hypotheses whose `.le` appears in the conclusion
(`sliceTo`, `sliceFrom`, `matches_slice`, the structure fields `isLongestMatch_sliceFrom`,
`isLongestRevMatch_sliceTo`).

Models (pattern values of the type `P`, each with its own instances):
* `P.tru`: every string matches (`PatternModel`, not strict). Its `ForwardPattern` /
  `BackwardPattern` never skip anything (strict, but not a lawful model), and its forward searcher
  `stepsNone` (one match over the whole slice, nothing on the empty slice) is a lawful
  `LawfulToForwardSearcherModel`. On the empty slice the empty match is never reported, so `find?`,
  `contains` and `Pos.find?` disagree with `MatchesAt`.
* `P.truE`: every string matches, searcher `stepsAll` (one match over the whole slice, also the
  empty match on the empty slice): lawful, and splitting `""` gives two pieces.
* `P.fal`: no string matches (strict). Its searchers report a match anyway (`stepsAll`, unlawful);
  its `ForwardPattern`/`BackwardPattern` skip the empty prefix/suffix (lawful as patterns, not
  strict, not a lawful model), so the default searcher loops forever (not `Finite`).
* `P.ne`: the non-empty strings match (strict); used to make `Model.split` start with a match.
* `P.a`: only `"a"` matches (has `NoPrefixPatternModel` and `NoSuffixPatternModel`).
* `P.emp`: only `""` matches; its longest match starts and ends at `startPos`.
* `P.broken`: `ForwardPattern`/`BackwardPattern` whose three fields disagree (not lawful).

Slices: `sA = "a".toSlice` (two positions) and `sE = "".toSlice`. The library's private
`SplitIterator.toList_eq_splitFromSteps` is copied (`toList_splitIterator`) to compute splits.

Run with the lean4 repo's stage1 binary: `lean checks/PatBasicHand.lean`.
-/

open String.Slice.Pattern String.Slice.Pattern.Model Std Std.Iterators Std.Iterators.Types
open String (Slice)

set_option linter.unusedVariables false

namespace PatBasicHand

/-! ## Models -/

/-- Pattern values; each carries its own instances. -/
inductive P | tru | truE | fal | ne | a | emp | broken

instance : PatternModel P.tru := ⟨fun _ => True⟩
instance : PatternModel P.truE := ⟨fun _ => True⟩
instance : PatternModel P.fal := ⟨fun _ => False⟩
instance : PatternModel P.ne := ⟨fun t => t ≠ ""⟩
instance : PatternModel P.a := ⟨fun t => t = "a"⟩
instance : PatternModel P.emp := ⟨fun t => t = ""⟩
instance : PatternModel P.broken := ⟨fun _ => True⟩

instance : StrictPatternModel P.fal := ⟨id⟩
instance : StrictPatternModel P.ne := ⟨fun h => h rfl⟩

abbrev sA : Slice := "a".toSlice
abbrev sE : Slice := "".toSlice

theorem sA_ne : sA.startPos ≠ sA.endPos := by decide
theorem sA_lt : sA.startPos < sA.endPos := by decide
theorem sA_not_le : ¬ sA.endPos ≤ sA.startPos := by decide
theorem sA_nonempty : sA.isEmpty = false := by decide
theorem sE_empty : sE.isEmpty = true := by decide
theorem sA_next : sA.startPos.next sA_ne = sA.endPos := by decide

abbrev σL (s : Slice) : Type := ListIterator (SearchStep s)

/-- `[]` on empty slices, otherwise one match over the whole slice. -/
def stepsNone (s : Slice) : List (SearchStep s) :=
  if s.isEmpty then [] else [.matched s.startPos s.endPos]
/-- One match over the whole slice, also on empty slices. -/
def stepsAll (s : Slice) : List (SearchStep s) := [.matched s.startPos s.endPos]

instance : ToForwardSearcher P.tru σL := ⟨fun s => (stepsNone s).iter⟩
instance : ToForwardSearcher P.truE σL := ⟨fun s => (stepsAll s).iter⟩
instance : ToForwardSearcher P.fal σL := ⟨fun s => (stepsAll s).iter⟩
instance : ToBackwardSearcher P.fal σL := ⟨fun s => (stepsAll s).iter⟩

/-- `tru`: never matches a prefix, `fal`: always skips everything, `broken`: inconsistent fields. -/
instance : ForwardPattern P.tru := ⟨fun _ => none, fun _ _ => none, fun _ => false⟩
instance : BackwardPattern P.tru := ⟨fun _ => none, fun _ _ => none, fun _ => false⟩
instance : StrictForwardPattern P.tru := ⟨fun _ _ h => by cases h⟩
instance : StrictBackwardPattern P.tru := ⟨fun _ _ h => by cases h⟩
instance : ForwardPattern P.fal := ⟨fun s => some s.startPos, fun s _ => some s.startPos, fun _ => true⟩
instance : BackwardPattern P.fal := ⟨fun s => some s.endPos, fun s _ => some s.endPos, fun _ => true⟩
instance : ForwardPattern P.broken := ⟨fun _ => none, fun s _ => some s.startPos, fun _ => true⟩
instance : BackwardPattern P.broken := ⟨fun _ => none, fun s _ => some s.endPos, fun _ => true⟩

/-! ## Facts about the models -/

theorem not_isLongestMatch_fal {s : Slice} {p : s.Pos} : ¬ IsLongestMatch P.fal p :=
  fun h => h.isMatch.matches_copy
theorem not_isLongestRevMatch_fal {s : Slice} {p : s.Pos} : ¬ IsLongestRevMatch P.fal p :=
  fun h => h.isRevMatch.matches_copy
theorem not_isLongestMatchAt_fal {s : Slice} {p q : s.Pos} : ¬ IsLongestMatchAt P.fal p q :=
  fun h => not_isLongestMatch_fal h.isLongestMatch_sliceFrom
theorem not_isLongestRevMatchAt_fal {s : Slice} {p q : s.Pos} : ¬ IsLongestRevMatchAt P.fal p q :=
  fun h => not_isLongestRevMatch_fal h.isLongestRevMatch_sliceTo
theorem not_matchesAt_fal {s : Slice} {p : s.Pos} : ¬ MatchesAt P.fal p :=
  fun ⟨⟨_, h⟩⟩ => not_isLongestMatchAt_fal h
theorem not_revMatchesAt_fal {s : Slice} {p : s.Pos} : ¬ RevMatchesAt P.fal p :=
  fun ⟨⟨_, h⟩⟩ => not_isLongestRevMatchAt_fal h

theorem isLongestMatch_endPos {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice}
    (h : PatternModel.Matches pat s.copy) : IsLongestMatch pat s.endPos :=
  ⟨⟨by simpa using h⟩, fun p hp => absurd (String.Slice.Pos.le_endPos p) (Std.not_le.2 hp)⟩

theorem isLongestRevMatch_startPos {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice}
    (h : PatternModel.Matches pat s.copy) : IsLongestRevMatch pat s.startPos :=
  ⟨⟨by simpa using h⟩, fun p hp => absurd (String.Slice.Pos.startPos_le p) (Std.not_le.2 hp)⟩

theorem isLongestMatchAt_endPos {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice}
    (p : s.Pos) (h : PatternModel.Matches pat (s.sliceFrom p).copy) : IsLongestMatchAt pat p s.endPos :=
  ⟨String.Slice.Pos.le_endPos p, by simpa using isLongestMatch_endPos h⟩

theorem isLongestRevMatchAt_startPos {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice}
    (p : s.Pos) (h : PatternModel.Matches pat (s.sliceTo p).copy) : IsLongestRevMatchAt pat s.startPos p :=
  ⟨String.Slice.Pos.startPos_le p, by simpa using isLongestRevMatch_startPos h⟩

theorem tru_lma {s : Slice} (p : s.Pos) : IsLongestMatchAt P.tru p s.endPos :=
  isLongestMatchAt_endPos p trivial
theorem tru_lrma {s : Slice} (p : s.Pos) : IsLongestRevMatchAt P.tru s.startPos p :=
  isLongestRevMatchAt_startPos p trivial
theorem tru_matchesAt {s : Slice} (p : s.Pos) : MatchesAt P.tru p := ⟨⟨_, tru_lma p⟩⟩
theorem tru_revMatchesAt {s : Slice} (p : s.Pos) : RevMatchesAt P.tru p := ⟨⟨_, tru_lrma p⟩⟩

theorem emp_isLongestMatch_startPos {s : Slice} : IsLongestMatch P.emp s.startPos := by
  refine ⟨⟨by simp [PatternModel.Matches]⟩, fun p hp h => ?_⟩
  have := h.matches_copy
  simp [PatternModel.Matches, String.Slice.copy_eq_empty_iff] at this
  exact Std.lt_irrefl (this ▸ hp)

theorem emp_isLongestRevMatch_endPos {s : Slice} : IsLongestRevMatch P.emp s.endPos := by
  refine ⟨⟨by simp [PatternModel.Matches]⟩, fun p hp h => ?_⟩
  have := h.matches_copy
  simp [PatternModel.Matches, String.Slice.copy_eq_empty_iff] at this
  exact Std.lt_irrefl (this ▸ hp)

/-! ### Inversion of valid searches -/

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

/-! ### Lawful searchers -/

instance : LawfulToForwardSearcherModel P.tru := ⟨fun s => by
  show IsValidSearchFrom P.tru s.startPos (stepsNone s).iter.toList
  rw [List.toList_iter, stepsNone]
  split
  · exact IsValidSearchFrom.endPos_of_eq (String.Slice.startPos_eq_endPos_iff.2 ‹_›) rfl
  · exact .matched (tru_lma _) .endPos⟩

instance : LawfulToForwardSearcherModel P.truE := ⟨fun s => by
  show IsValidSearchFrom P.truE s.startPos (stepsAll s).iter.toList
  rw [List.toList_iter, stepsAll]
  exact .matched (isLongestMatchAt_endPos _ trivial) .endPos⟩

/-! ### The default searchers -/

theorem default_fwd_head : ∃ a b l,
    (ToForwardSearcher.DefaultForwardSearcher.iter P.tru sA).toList = .rejected a b :: l := by
  rw [Iter.toList_eq_match_step]
  generalize (ToForwardSearcher.DefaultForwardSearcher.iter P.tru sA).step = st
  obtain ⟨st, hp⟩ := st
  cases st with
  | yield it' out =>
    cases out with
    | rejected a b => exact ⟨a, b, _, rfl⟩
    | matched a b =>
      simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, ToForwardSearcher.DefaultForwardSearcher.instIteratorIdSearchStepOfForwardPattern, ForwardPattern.skipPrefixOfNonempty?] at hp
  | skip it' => simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, ToForwardSearcher.DefaultForwardSearcher.instIteratorIdSearchStepOfForwardPattern] at hp
  | done =>
    simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, ToForwardSearcher.DefaultForwardSearcher.instIteratorIdSearchStepOfForwardPattern, ToForwardSearcher.DefaultForwardSearcher.iter] at hp

theorem default_bwd_head : ∃ a b l,
    (ToBackwardSearcher.DefaultBackwardSearcher.iter P.tru sA).toList = .rejected a b :: l := by
  rw [Iter.toList_eq_match_step]
  generalize (ToBackwardSearcher.DefaultBackwardSearcher.iter P.tru sA).step = st
  obtain ⟨st, hp⟩ := st
  cases st with
  | yield it' out =>
    cases out with
    | rejected a b => exact ⟨a, b, _, rfl⟩
    | matched a b =>
      simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, ToBackwardSearcher.DefaultBackwardSearcher.instIteratorIdSearchStepOfBackwardPattern, BackwardPattern.skipSuffixOfNonempty?] at hp
  | skip it' => simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, ToBackwardSearcher.DefaultBackwardSearcher.instIteratorIdSearchStepOfBackwardPattern] at hp
  | done =>
    simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, ToBackwardSearcher.DefaultBackwardSearcher.instIteratorIdSearchStepOfBackwardPattern, ToBackwardSearcher.DefaultBackwardSearcher.iter] at hp
    exact absurd hp (by decide)

/-- An accessible element is not related to itself. -/
theorem acc_not_self {α : Sort _} {r : α → α → Prop} {x : α} (h : Acc r x) : ¬ r x x := by
  induction h with | intro x _ ih => exact fun hxx => ih x hxx hxx

theorem not_finite_fwd : ¬ Iterators.Finite (ToForwardSearcher.DefaultForwardSearcher P.fal sA) Id := by
  intro hf
  let it : IterM (α := ToForwardSearcher.DefaultForwardSearcher P.fal sA) Id (SearchStep sA) := ⟨⟨sA.startPos⟩⟩
  refine acc_not_self (hf.wf.apply it) ⟨.yield it (.matched sA.startPos sA.startPos), rfl, ?_⟩
  refine ⟨by decide, (sA.sliceFrom sA.startPos).startPos, rfl, rfl, ?_, ?_⟩ <;> simp [it]

theorem not_finite_bwd : ¬ Iterators.Finite (ToBackwardSearcher.DefaultBackwardSearcher P.fal sA) Id := by
  intro hf
  let it : IterM (α := ToBackwardSearcher.DefaultBackwardSearcher P.fal sA) Id (SearchStep sA) := ⟨⟨sA.endPos⟩⟩
  refine acc_not_self (hf.wf.apply it) ⟨.yield it (.matched sA.endPos sA.endPos), rfl, ?_⟩
  refine ⟨by decide, (sA.sliceTo sA.endPos).endPos, rfl, ?_, rfl, ?_⟩ <;> simp [it]

/-! ### Splitting with a given searcher -/

/-- Copy of the library's private `Model.splitFromSteps`. -/
def splitFromSteps {s : Slice} (currPos : s.Pos) (l : List (SearchStep s)) : List s.Subslice :=
  match l with
  | [] => [s.subsliceFrom currPos]
  | .rejected .. :: l => splitFromSteps currPos l
  | .matched p q :: l => s.subslice! currPos p :: splitFromSteps q l

/-- Copy of the library's private `Model.SplitIterator.toList_eq_splitFromSteps`. -/
theorem toList_splitIterator {ρ : Type} {pat : ρ} {σ : Slice → Type}
    [ToForwardSearcher pat σ]
    [∀ s, Std.Iterator (σ s) Id (SearchStep s)] [∀ s, Std.Iterators.Finite (σ s) Id] {s : Slice}
    (it : Std.Iter (α := σ s) (SearchStep s)) (currPos : s.Pos) :
    (Std.Iter.mk (α := String.Slice.SplitIterator pat s) (.operating currPos it)).toList =
      splitFromSteps currPos it.toList := by
  induction it using Std.Iter.inductSteps generalizing currPos with | step it ihy ihs
  rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
  conv => rhs; rw [Std.Iter.toList_eq_match_step]
  simp only [Std.Iter.toIterM_mk]
  cases it.step using Std.PlausibleIterStep.casesOn with
  | yield it out h =>
    match out with
    | .matched startPos endPos => simp [splitFromSteps, ← ihy h]
    | .rejected startPos endPos => simp [splitFromSteps, ← ihy h]
  | skip it h => simp [← ihs h]
  | done =>
    simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
      Std.PlausibleIterStep.yield, Std.IterM.toIter_mk, splitFromSteps, List.cons.injEq, true_and]
    rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
    simp

theorem length_splitToSubslice_sE {pat : P} [ToForwardSearcher pat σL]
    (h : (ToForwardSearcher.toSearcher pat sE).toList = stepsAll sE) :
    (sE.splitToSubslice pat).toList.length = 2 := by
  rw [String.Slice.splitToSubslice, toList_splitIterator, h]
  simp [stepsAll, splitFromSteps]

end PatBasicHand

open PatBasicHand

/-! ## `StrictPatternModel` (non-dependent): the all-matching model `P.tru` -/

-- `String.Slice.Pattern.Model.StrictPatternModel.not_matches_empty` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat], ¬ PatternModel.Matches pat "" :=
  fun h => h (pat := P.tru) trivial

-- `String.Slice.Pattern.Model.not_matches_empty` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat], ¬ PatternModel.Matches pat "" :=
  fun h => h (pat := P.tru) trivial

-- `String.Slice.Pattern.Model.IsMatch.ne_startPos` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos},
    IsMatch pat pos → pos ≠ s.startPos :=
  fun h => h (pat := P.tru) (s := sE) (pos := sE.startPos) ⟨trivial⟩ rfl

-- `String.Slice.Pattern.Model.IsMatch.ne_startPos` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {pos : s.Pos},
    pos ≠ s.startPos :=
  fun h => h (pat := P.fal) (s := sE) (pos := sE.startPos) rfl

-- `String.Slice.Pattern.Model.IsRevMatch.ne_endPos` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos},
    IsRevMatch pat pos → pos ≠ s.endPos :=
  fun h => h (pat := P.tru) (s := sE) (pos := sE.endPos) ⟨trivial⟩ rfl

-- `String.Slice.Pattern.Model.IsRevMatch.ne_endPos` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {pos : s.Pos},
    pos ≠ s.endPos :=
  fun h => h (pat := P.fal) (s := sE) (pos := sE.endPos) rfl

-- `String.Slice.Pattern.Model.IsLongestMatch.ne_startPos` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos},
    IsLongestMatch pat pos → pos ≠ s.startPos :=
  fun h => h (pat := P.tru) (s := sE) (pos := sE.endPos) (isLongestMatch_endPos trivial) rfl

-- `String.Slice.Pattern.Model.IsLongestMatch.ne_startPos` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {pos : s.Pos},
    pos ≠ s.startPos :=
  fun h => h (pat := P.fal) (s := sE) (pos := sE.startPos) rfl

-- `String.Slice.Pattern.Model.not_isLongestMatch_startPos` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice}, ¬ IsLongestMatch pat s.startPos :=
  fun h => h (pat := P.tru) (s := sE) (isLongestMatch_endPos trivial)

-- `String.Slice.Pattern.Model.IsLongestRevMatch.ne_endPos` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos},
    IsLongestRevMatch pat pos → pos ≠ s.endPos :=
  fun h => h (pat := P.tru) (s := sE) (pos := sE.startPos) (isLongestRevMatch_startPos trivial) rfl

-- `String.Slice.Pattern.Model.IsLongestRevMatch.ne_endPos` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {pos : s.Pos},
    pos ≠ s.endPos :=
  fun h => h (pat := P.fal) (s := sE) (pos := sE.endPos) rfl

-- `String.Slice.Pattern.Model.not_isLongestRevMatch_endPos` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice}, ¬ IsLongestRevMatch pat s.endPos :=
  fun h => h (pat := P.tru) (s := sE) (isLongestRevMatch_startPos trivial)

-- `String.Slice.Pattern.Model.not_matchesAt_endPos` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice}, ¬ MatchesAt pat s.endPos :=
  fun h => h (pat := P.tru) (s := sE) (tru_matchesAt _)

-- `String.Slice.Pattern.Model.not_revMatchesAt_startPos` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice}, ¬ RevMatchesAt pat s.startPos :=
  fun h => h (pat := P.tru) (s := sE) (tru_revMatchesAt _)

-- `String.Slice.Pattern.Model.IsLongestMatchAt.lt` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    IsLongestMatchAt pat startPos endPos → startPos < endPos :=
  fun h => Std.lt_irrefl (h (pat := P.tru) (s := sE) (tru_lma sE.endPos))

-- `String.Slice.Pattern.Model.IsLongestMatchAt.lt` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice}
    {startPos endPos : s.Pos}, startPos < endPos :=
  fun h => absurd (h (pat := P.fal) (s := sE) (startPos := sE.startPos) (endPos := sE.startPos)) Std.lt_irrefl

-- `String.Slice.Pattern.Model.IsLongestMatchAt.ne` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    IsLongestMatchAt pat startPos endPos → startPos ≠ endPos :=
  fun h => h (pat := P.tru) (s := sE) (tru_lma sE.endPos) rfl

-- `String.Slice.Pattern.Model.IsLongestMatchAt.ne` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice}
    {startPos endPos : s.Pos}, startPos ≠ endPos :=
  fun h => h (pat := P.fal) (s := sE) (startPos := sE.startPos) (endPos := sE.startPos) rfl

-- `String.Slice.Pattern.Model.not_isLongestMatchAt_self` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos : s.Pos},
    ¬ IsLongestMatchAt pat startPos startPos :=
  fun h => h (pat := P.tru) (s := sE) (tru_lma sE.endPos)

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.lt` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    IsLongestRevMatchAt pat startPos endPos → startPos < endPos :=
  fun h => Std.lt_irrefl (h (pat := P.tru) (s := sE) (tru_lrma sE.startPos))

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.lt` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice}
    {startPos endPos : s.Pos}, startPos < endPos :=
  fun h => absurd (h (pat := P.fal) (s := sE) (startPos := sE.startPos) (endPos := sE.startPos)) Std.lt_irrefl

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.ne` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    IsLongestRevMatchAt pat startPos endPos → startPos ≠ endPos :=
  fun h => h (pat := P.tru) (s := sE) (tru_lrma sE.startPos) rfl

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.ne` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice}
    {startPos endPos : s.Pos}, startPos ≠ endPos :=
  fun h => h (pat := P.fal) (s := sE) (startPos := sE.startPos) (endPos := sE.startPos) rfl

-- `String.Slice.Pattern.Model.not_isLongestRevMatchAt_self` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {endPos : s.Pos},
    ¬ IsLongestRevMatchAt pat endPos endPos :=
  fun h => h (pat := P.tru) (s := sE) (tru_lrma sE.startPos)

-- `String.Slice.Pattern.Model.lt_of_matchAt?_eq_some` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    matchAt? pat startPos = some endPos → startPos < endPos :=
  fun h => Std.lt_irrefl (h (pat := P.tru) (s := sE) (matchAt?_eq_some_iff.2 (tru_lma sE.endPos)))

-- `String.Slice.Pattern.Model.lt_of_matchAt?_eq_some` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice}
    {startPos endPos : s.Pos}, startPos < endPos :=
  fun h => absurd (h (pat := P.fal) (s := sE) (startPos := sE.startPos) (endPos := sE.startPos)) Std.lt_irrefl

-- `String.Slice.Pattern.Model.lt_of_revMatchAt?_eq_some` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    revMatchAt? pat endPos = some startPos → startPos < endPos :=
  fun h => Std.lt_irrefl (h (pat := P.tru) (s := sE) (revMatchAt?_eq_some_iff.2 (tru_lrma sE.startPos)))

-- `String.Slice.Pattern.Model.lt_of_revMatchAt?_eq_some` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice}
    {startPos endPos : s.Pos}, startPos < endPos :=
  fun h => absurd (h (pat := P.fal) (s := sE) (startPos := sE.startPos) (endPos := sE.startPos)) Std.lt_irrefl

/-! ## `StrictPatternModel` (dependent: `Model.split` needs it) -/

-- `String.Slice.Pattern.Model.split_endPos`, `String.Slice.Pattern.Model.split_eq_of_isLongestMatchAt`,
-- `String.Slice.Pattern.Model.split_eq_of_not_matchesAt`,
-- `String.Slice.Pattern.Model.split_eq_next_of_not_matchesAt`,
-- `String.Slice.Pattern.toList_splitToSubslice_eq_modelSplit` (`inst : StrictPatternModel pat`,
-- dependent): `P.tru` matches the empty string.
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat], StrictPatternModel pat :=
  fun h => (h P.tru).not_matches_empty trivial

/-! ## Structure fields and match predicates -/

-- `String.Slice.Pattern.Model.IsMatch.matches_copy` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {endPos : s.Pos},
    PatternModel.Matches pat (s.sliceTo endPos).copy :=
  fun h => h (pat := P.fal) (s := sE) (endPos := sE.startPos)

-- `String.Slice.Pattern.Model.IsRevMatch.matches_copy` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos : s.Pos},
    PatternModel.Matches pat (s.sliceFrom startPos).copy :=
  fun h => h (pat := P.fal) (s := sE) (startPos := sE.startPos)

-- `String.Slice.Pattern.Model.IsLongestMatch.isMatch` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos}, IsMatch pat pos :=
  fun h => (h (pat := P.fal) (s := sE) (pos := sE.startPos)).matches_copy

-- `String.Slice.Pattern.Model.IsLongestRevMatch.isRevMatch` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos}, IsRevMatch pat pos :=
  fun h => (h (pat := P.fal) (s := sE) (pos := sE.startPos)).matches_copy

-- `String.Slice.Pattern.Model.IsLongestMatch.not_isMatch` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos},
    ∀ pos', pos < pos' → ¬ IsMatch pat pos' :=
  fun h => h (pat := P.tru) (s := sA) (pos := sA.startPos) sA.endPos sA_lt ⟨trivial⟩

-- `String.Slice.Pattern.Model.IsLongestRevMatch.not_isRevMatch` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos},
    ∀ pos', pos' < pos → ¬ IsRevMatch pat pos' :=
  fun h => h (pat := P.tru) (s := sA) (pos := sA.endPos) sA.startPos sA_lt ⟨trivial⟩

-- `String.Slice.Pattern.Model.MatchesAt.exists_isLongestMatchAt` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos},
    ∃ endPos, IsLongestMatchAt pat pos endPos :=
  fun h => (h (pat := P.fal) (s := sE) (pos := sE.startPos)).elim fun _ => not_isLongestMatchAt_fal

-- `String.Slice.Pattern.Model.RevMatchesAt.exists_isLongestRevMatchAt` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos},
    ∃ startPos, IsLongestRevMatchAt pat startPos pos :=
  fun h => (h (pat := P.fal) (s := sE) (pos := sE.startPos)).elim fun _ => not_isLongestRevMatchAt_fal

-- `String.Slice.Pattern.Model.IsMatch.exists_isLongestMatch` (`a : IsMatch pat pos`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos},
    ∃ pos' : s.Pos, IsLongestMatch pat pos' :=
  fun h => (h (pat := P.fal) (s := sE) (pos := sE.startPos)).elim fun _ => not_isLongestMatch_fal

-- `String.Slice.Pattern.Model.IsRevMatch.exists_isLongestRevMatch` (`a : IsRevMatch pat pos`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos},
    ∃ pos' : s.Pos, IsLongestRevMatch pat pos' :=
  fun h => (h (pat := P.fal) (s := sE) (pos := sE.startPos)).elim fun _ => not_isLongestRevMatch_fal

-- `String.Slice.Pattern.Model.IsLongestMatchAt.matchesAt` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    MatchesAt pat startPos :=
  fun h => not_matchesAt_fal (h (pat := P.fal) (s := sE) (startPos := sE.startPos) (endPos := sE.startPos))

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.revMatchesAt` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    RevMatchesAt pat endPos :=
  fun h => not_revMatchesAt_fal (h (pat := P.fal) (s := sE) (startPos := sE.startPos) (endPos := sE.startPos))

/-! ## Orderings: any model, positions in the wrong order -/

-- `String.Slice.Pattern.Model.IsLongestMatchAt.le` (`self`),
-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.le` (`self`),
-- `String.Slice.Pattern.Model.IsLongestMatchAtChain.le` (`h`),
-- `String.Slice.Pattern.Model.IsLongestRevMatchAtChain.le` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    startPos ≤ endPos :=
  fun h => sA_not_le (h (pat := P.fal) (s := sA) (startPos := sA.endPos) (endPos := sA.startPos))

-- `String.Slice.Pattern.Model.IsLongestMatchAt.isLongestMatch_sliceFrom` (`self`, dependent),
-- `String.Slice.Pattern.Model.IsLongestMatchAt.matches_slice` (`h`, dependent),
-- `String.Slice.Pattern.Model.IsLongestMatchAt.sliceTo` (`h`, dependent)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    IsLongestMatchAt pat startPos endPos :=
  fun h => sA_not_le (h (pat := P.fal) (s := sA) (startPos := sA.endPos) (endPos := sA.startPos)).le

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.isLongestRevMatch_sliceTo` (`self`, dependent),
-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.matches_slice` (`h`, dependent),
-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.sliceFrom` (`h`, dependent)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    IsLongestRevMatchAt pat startPos endPos :=
  fun h => sA_not_le (h (pat := P.fal) (s := sA) (startPos := sA.endPos) (endPos := sA.startPos)).le

-- `String.Slice.Pattern.Model.IsLongestMatchAtChain.sliceTo` (`h`, dependent)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    IsLongestMatchAtChain pat startPos endPos :=
  fun h => sA_not_le (h (pat := P.fal) (s := sA) (startPos := sA.endPos) (endPos := sA.startPos)).le

-- `String.Slice.Pattern.Model.IsLongestRevMatchAtChain.sliceFrom` (`h`, dependent)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    IsLongestRevMatchAtChain pat startPos endPos :=
  fun h => sA_not_le (h (pat := P.fal) (s := sA) (startPos := sA.endPos) (endPos := sA.startPos)).le

-- `String.Slice.Pattern.Model.isLongestMatchAtChain_of_ofSliceTo` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos}
    {startPos endPos : (s.sliceTo p).Pos}, IsLongestMatchAtChain pat startPos endPos :=
  fun h => absurd (h (pat := P.fal) (s := sA) (p := sA.endPos) (startPos := (sA.sliceTo sA.endPos).endPos)
    (endPos := (sA.sliceTo sA.endPos).startPos)).le (by decide)

-- `String.Slice.Pattern.Model.isLongestRevMatchAtChain_of_ofSliceFrom` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos}
    {startPos endPos : (s.sliceFrom p).Pos}, IsLongestRevMatchAtChain pat startPos endPos :=
  fun h => absurd (h (pat := P.fal) (s := sA) (p := sA.startPos)
    (startPos := (sA.sliceFrom sA.startPos).endPos) (endPos := (sA.sliceFrom sA.startPos).startPos)).le
    (by decide)

/-! ## Conclusions that assert a match: the never-matching model `P.fal` -/

-- `String.Slice.Pattern.Model.IsLongestMatch.of_eq` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s t : Slice} {pos : s.Pos} {pos' : t.Pos}
    (h₁ : s.copy = t.copy), pos.cast h₁ = pos' → IsLongestMatch pat pos' :=
  fun h => not_isLongestMatch_fal (h (pat := P.fal) (s := sE) (t := sE) (pos := sE.startPos) rfl rfl)

-- `String.Slice.Pattern.Model.IsLongestRevMatch.of_eq` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s t : Slice} {pos : s.Pos} {pos' : t.Pos}
    (h₁ : s.copy = t.copy), pos.cast h₁ = pos' → IsLongestRevMatch pat pos' :=
  fun h => not_isLongestRevMatch_fal (h (pat := P.fal) (s := sE) (t := sE) (pos := sE.startPos) rfl rfl)

-- `String.Slice.Pattern.Model.IsLongestMatchAt.of_eq` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s t : Slice} {s₁ e₁ : s.Pos} {s₂ e₂ : t.Pos}
    (h₁ : s.copy = t.copy), s₁.cast h₁ = s₂ → e₁.cast h₁ = e₂ → IsLongestMatchAt pat s₂ e₂ :=
  fun h => not_isLongestMatchAt_fal
    (h (pat := P.fal) (s := sE) (t := sE) (s₁ := sE.startPos) (e₁ := sE.startPos) rfl rfl rfl)

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.of_eq` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s t : Slice} {s₁ e₁ : s.Pos} {s₂ e₂ : t.Pos}
    (h₁ : s.copy = t.copy), s₁.cast h₁ = s₂ → e₁.cast h₁ = e₂ → IsLongestRevMatchAt pat s₂ e₂ :=
  fun h => not_isLongestRevMatchAt_fal
    (h (pat := P.fal) (s := sE) (t := sE) (s₁ := sE.startPos) (e₁ := sE.startPos) rfl rfl rfl)

-- `String.Slice.Pattern.Model.IsLongestMatch.sliceTo` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos} (p : s.Pos) (hp : pos ≤ p),
    IsLongestMatch pat (String.Slice.Pos.sliceTo p pos hp) :=
  fun h => not_isLongestMatch_fal (h (pat := P.fal) (s := sE) (pos := sE.startPos) sE.startPos (Std.le_refl _))

-- `String.Slice.Pattern.Model.IsLongestRevMatch.sliceFrom` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos} (p : s.Pos) (hp : p ≤ pos),
    IsLongestRevMatch pat (String.Slice.Pos.sliceFrom p pos hp) :=
  fun h => not_isLongestRevMatch_fal (h (pat := P.fal) (s := sE) (pos := sE.startPos) sE.startPos (Std.le_refl _))

-- `String.Slice.Pattern.Model.isLongestMatch_of_ofSliceTo` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos} {pos : (s.sliceTo p).Pos},
    IsLongestMatch pat pos :=
  fun h => not_isLongestMatch_fal (h (pat := P.fal) (s := sE) (p := sE.startPos) (pos := (sE.sliceTo _).startPos))

-- `String.Slice.Pattern.Model.isLongestRevMatch_of_ofSliceFrom` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos} {pos : (s.sliceFrom p).Pos},
    IsLongestRevMatch pat pos :=
  fun h => not_isLongestRevMatch_fal
    (h (pat := P.fal) (s := sE) (p := sE.startPos) (pos := (sE.sliceFrom _).startPos))

-- `String.Slice.Pattern.Model.isLongestMatchAt_of_ofSliceTo` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos}
    {startPos endPos : (s.sliceTo p).Pos}, IsLongestMatchAt pat startPos endPos :=
  fun h => not_isLongestMatchAt_fal (h (pat := P.fal) (s := sE) (p := sE.startPos)
    (startPos := (sE.sliceTo _).startPos) (endPos := (sE.sliceTo _).startPos))

-- `String.Slice.Pattern.Model.isLongestRevMatchAt_of_ofSliceFrom` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos}
    {startPos endPos : (s.sliceFrom p).Pos}, IsLongestRevMatchAt pat startPos endPos :=
  fun h => not_isLongestRevMatchAt_fal (h (pat := P.fal) (s := sE) (p := sE.startPos)
    (startPos := (sE.sliceFrom _).startPos) (endPos := (sE.sliceFrom _).startPos))

-- `String.Slice.Pattern.Model.IsLongestMatch.isLongestMatchAt_ofSliceFrom` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p₀ : s.Pos} {pos : (s.sliceFrom p₀).Pos},
    IsLongestMatchAt pat p₀ (String.Slice.Pos.ofSliceFrom pos) :=
  fun h => not_isLongestMatchAt_fal
    (h (pat := P.fal) (s := sE) (p₀ := sE.startPos) (pos := (sE.sliceFrom _).startPos))

-- `String.Slice.Pattern.Model.IsLongestRevMatch.isLongestRevMatchAt_ofSliceTo` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p₀ : s.Pos} {pos : (s.sliceTo p₀).Pos},
    IsLongestRevMatchAt pat (String.Slice.Pos.ofSliceTo pos) p₀ :=
  fun h => not_isLongestRevMatchAt_fal
    (h (pat := P.fal) (s := sE) (p₀ := sE.startPos) (pos := (sE.sliceTo _).startPos))

/-! ## Uniqueness and maximality of longest matches -/

-- `String.Slice.Pattern.Model.IsLongestMatch.eq` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos pos' : s.Pos},
    IsLongestMatch pat pos' → pos = pos' :=
  fun h => sA_ne (h (pat := P.tru) (s := sA) (pos := sA.startPos) (isLongestMatch_endPos trivial))

-- `String.Slice.Pattern.Model.IsLongestMatch.eq` (`h'`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos pos' : s.Pos},
    IsLongestMatch pat pos → pos = pos' :=
  fun h => sA_ne (h (pat := P.tru) (s := sA) (pos' := sA.startPos) (isLongestMatch_endPos trivial)).symm

-- `String.Slice.Pattern.Model.IsLongestRevMatch.eq` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos pos' : s.Pos},
    IsLongestRevMatch pat pos' → pos = pos' :=
  fun h => sA_ne (h (pat := P.tru) (s := sA) (pos := sA.endPos) (isLongestRevMatch_startPos trivial)).symm

-- `String.Slice.Pattern.Model.IsLongestRevMatch.eq` (`h'`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos pos' : s.Pos},
    IsLongestRevMatch pat pos → pos = pos' :=
  fun h => sA_ne (h (pat := P.tru) (s := sA) (pos' := sA.endPos) (isLongestRevMatch_startPos trivial))

-- `String.Slice.Pattern.Model.IsLongestMatchAt.eq` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos endPos' : s.Pos},
    IsLongestMatchAt pat startPos endPos' → endPos = endPos' :=
  fun h => sA_ne (h (pat := P.tru) (s := sA) (endPos := sA.startPos) (tru_lma sA.startPos))

-- `String.Slice.Pattern.Model.IsLongestMatchAt.eq` (`h'`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos endPos' : s.Pos},
    IsLongestMatchAt pat startPos endPos → endPos = endPos' :=
  fun h => sA_ne (h (pat := P.tru) (s := sA) (endPos' := sA.startPos) (tru_lma sA.startPos)).symm

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.eq` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos startPos' endPos : s.Pos},
    IsLongestRevMatchAt pat startPos' endPos → startPos = startPos' :=
  fun h => sA_ne (h (pat := P.tru) (s := sA) (startPos := sA.endPos) (tru_lrma sA.endPos)).symm

-- `String.Slice.Pattern.Model.IsLongestRevMatchAt.eq` (`h'`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos startPos' endPos : s.Pos},
    IsLongestRevMatchAt pat startPos endPos → startPos = startPos' :=
  fun h => sA_ne (h (pat := P.tru) (s := sA) (startPos' := sA.endPos) (tru_lrma sA.endPos))

-- `String.Slice.Pattern.Model.IsLongestMatch.le_of_isMatch` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos pos' : s.Pos},
    IsMatch pat pos' → pos' ≤ pos :=
  fun h => sA_not_le (h (pat := P.tru) (s := sA) (pos := sA.startPos) (pos' := sA.endPos) ⟨trivial⟩)

-- `String.Slice.Pattern.Model.IsLongestMatch.le_of_isMatch` (`h'`): the model "matches only the
-- empty string" has its longest match at the start.
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos pos' : s.Pos},
    IsLongestMatch pat pos → pos' ≤ pos :=
  fun h => sA_not_le (h (pat := P.emp) (s := sA) (pos' := sA.endPos) emp_isLongestMatch_startPos)

-- `String.Slice.Pattern.Model.IsLongestRevMatch.le_of_isRevMatch` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos pos' : s.Pos},
    IsRevMatch pat pos' → pos ≤ pos' :=
  fun h => sA_not_le (h (pat := P.tru) (s := sA) (pos := sA.endPos) (pos' := sA.startPos) ⟨trivial⟩)

-- `String.Slice.Pattern.Model.IsLongestRevMatch.le_of_isRevMatch` (`h'`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos pos' : s.Pos},
    IsLongestRevMatch pat pos → pos ≤ pos' :=
  fun h => sA_not_le (h (pat := P.emp) (s := sA) (pos' := sA.startPos) emp_isLongestRevMatch_endPos)

-- `String.Slice.Pattern.Model.IsLongestMatchAtChain.eq_of_isLongestMatchAt_self` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    IsLongestMatchAt pat startPos startPos → startPos = endPos :=
  fun h => sA_ne (h (pat := P.tru) (s := sA) (endPos := sA.startPos) (tru_lma sA.endPos)).symm

-- `String.Slice.Pattern.Model.IsLongestMatchAtChain.eq_of_isLongestMatchAt_self` (`h'`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    IsLongestMatchAtChain pat startPos endPos → startPos = endPos :=
  fun h => sA_ne (h (pat := P.tru) (s := sA) (.cons _ _ _ (tru_lma sA.startPos) (.nil _)))

-- `String.Slice.Pattern.Model.IsLongestRevMatchAtChain.eq_of_isLongestRevMatchAt_self` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    IsLongestRevMatchAt pat endPos endPos → startPos = endPos :=
  fun h => sA_ne (h (pat := P.tru) (s := sA) (startPos := sA.endPos) (tru_lrma sA.startPos)).symm

-- `String.Slice.Pattern.Model.IsLongestRevMatchAtChain.eq_of_isLongestRevMatchAt_self` (`h'`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos},
    IsLongestRevMatchAtChain pat startPos endPos → startPos = endPos :=
  fun h => sA_ne (h (pat := P.tru) (s := sA) (.cons _ _ _ (.nil _) (tru_lrma sA.endPos)))

/-! ## Valid searches -/

-- `String.Slice.Pattern.Model.IsValidSearchFrom.matched_of_eq` (`h₁`): the rest of the steps is
-- not a valid search (a rejected step that goes backwards).
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos startPos' endPos : s.Pos}
    {l : List (SearchStep s)}, IsLongestMatchAt pat startPos' endPos → startPos = startPos' →
      IsValidSearchFrom pat startPos' (.matched startPos endPos :: l) :=
  fun h => sA_not_le (Std.le_of_lt ((vsf_cons (vsf_cons (h (pat := P.tru) (s := sA)
    (l := [.rejected sA.endPos sA.startPos]) (tru_lma sA.startPos) rfl)).2.1).2.2.2 _ _ rfl).1)

-- `String.Slice.Pattern.Model.IsValidSearchFrom.matched_of_eq` (`h₂`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos startPos' endPos : s.Pos}
    {l : List (SearchStep s)}, IsValidSearchFrom pat endPos l → startPos = startPos' →
      IsValidSearchFrom pat startPos' (.matched startPos endPos :: l) :=
  fun h => not_isLongestMatchAt_fal ((vsf_cons (h (pat := P.fal) (s := sE) (startPos := sE.endPos)
    .endPos rfl)).2.2.1 _ _ rfl)

-- `String.Slice.Pattern.Model.IsValidSearchFrom.mismatched_of_eq` (`h₁`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos startPos' endPos : s.Pos}
    {l : List (SearchStep s)}, startPos' < endPos →
      (∀ pos, startPos' ≤ pos → pos < endPos → ¬ MatchesAt pat pos) → startPos = startPos' →
      IsValidSearchFrom pat startPos' (.rejected startPos endPos :: l) :=
  fun h => sA_not_le (Std.le_of_lt ((vsf_cons (vsf_cons (h (pat := P.fal) (s := sA)
    (startPos := sA.startPos) (l := [.rejected sA.endPos sA.startPos]) sA_lt
    (fun _ _ _ => not_matchesAt_fal) rfl)).2.1).2.2.2 _ _ rfl).1)

-- `String.Slice.Pattern.Model.IsValidSearchFrom.mismatched_of_eq` (`h₂`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos startPos' endPos : s.Pos}
    {l : List (SearchStep s)}, IsValidSearchFrom pat endPos l → startPos' < endPos →
      startPos = startPos' → IsValidSearchFrom pat startPos' (.rejected startPos endPos :: l) :=
  fun h => ((vsf_cons (h (pat := P.tru) (s := sA) (startPos := sA.startPos) .endPos sA_lt rfl)).2.2.2 _ _ rfl).2
    sA.startPos (Std.le_refl _) sA_lt (tru_matchesAt _)

-- `String.Slice.Pattern.Model.IsValidRevSearchFrom.matched_of_eq` (`h₁`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos endPos' : s.Pos}
    {l : List (SearchStep s)}, IsLongestRevMatchAt pat startPos endPos' → endPos = endPos' →
      IsValidRevSearchFrom pat endPos' (.matched startPos endPos :: l) :=
  fun h => sA_not_le (Std.le_of_lt ((vrsf_cons (vrsf_cons (h (pat := P.tru) (s := sA)
    (l := [.rejected sA.endPos sA.startPos]) (tru_lrma sA.endPos) rfl)).2.1).2.2.2 _ _ rfl).1)

-- `String.Slice.Pattern.Model.IsValidRevSearchFrom.matched_of_eq` (`h₂`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos endPos' : s.Pos}
    {l : List (SearchStep s)}, IsValidRevSearchFrom pat startPos l → endPos = endPos' →
      IsValidRevSearchFrom pat endPos' (.matched startPos endPos :: l) :=
  fun h => not_isLongestRevMatchAt_fal ((vrsf_cons (h (pat := P.fal) (s := sE) (endPos := sE.startPos)
    .startPos rfl)).2.2.1 _ _ rfl)

-- `String.Slice.Pattern.Model.IsValidRevSearchFrom.mismatched_of_eq` (`h₁`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos endPos' : s.Pos}
    {l : List (SearchStep s)}, startPos < endPos' →
      (∀ pos, startPos < pos → pos ≤ endPos' → ¬ RevMatchesAt pat pos) → endPos = endPos' →
      IsValidRevSearchFrom pat endPos' (.rejected startPos endPos :: l) :=
  fun h => sA_not_le (Std.le_of_lt ((vrsf_cons (vrsf_cons (h (pat := P.fal) (s := sA)
    (endPos := sA.endPos) (l := [.rejected sA.endPos sA.startPos]) sA_lt
    (fun _ _ _ => not_revMatchesAt_fal) rfl)).2.1).2.2.2 _ _ rfl).1)

-- `String.Slice.Pattern.Model.IsValidRevSearchFrom.mismatched_of_eq` (`h₂`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos endPos' : s.Pos}
    {l : List (SearchStep s)}, IsValidRevSearchFrom pat startPos l → startPos < endPos' →
      endPos = endPos' → IsValidRevSearchFrom pat endPos' (.rejected startPos endPos :: l) :=
  fun h => ((vrsf_cons (h (pat := P.tru) (s := sA) (endPos := sA.endPos) .startPos sA_lt rfl)).2.2.2 _ _ rfl).2
    sA.endPos sA_lt (Std.le_refl _) (tru_revMatchesAt _)

-- `String.Slice.Pattern.Model.LawfulToForwardSearcherModel.isValidSearchFrom_toList` (`self`):
-- `P.fal` with the searcher that reports one match over the whole slice.
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {σ : Slice → Type} [ToForwardSearcher pat σ]
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id] (s : Slice),
    IsValidSearchFrom pat s.startPos (ToForwardSearcher.toSearcher pat s).toList := by
  intro h
  have := h (pat := P.fal) sE
  simp only [ToForwardSearcher.toSearcher, List.toList_iter, stepsAll] at this
  exact not_isLongestMatchAt_fal ((vsf_cons this).2.2.1 _ _ rfl)

-- `String.Slice.Pattern.Model.LawfulToBackwardSearcherModel.isValidRevSearchFrom_toList` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {σ : Slice → Type} [ToBackwardSearcher pat σ]
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id] (s : Slice),
    IsValidRevSearchFrom pat s.endPos (ToBackwardSearcher.toSearcher pat s).toList := by
  intro h
  have := h (pat := P.fal) sE
  simp only [ToBackwardSearcher.toSearcher, List.toList_iter, stepsAll] at this
  exact not_isLongestRevMatchAt_fal ((vrsf_cons this).2.2.1 _ _ rfl)

/-! ## `NoPrefixPatternModel` / `NoSuffixPatternModel` -/

namespace PatBasicHand

instance : NoPrefixPatternModel P.a :=
  NoPrefixPatternModel.of_length_toList_eq fun s t hs ht => by
    change s = "a" at hs; change t = "a" at ht; subst hs ht; rfl

instance : NoSuffixPatternModel P.a :=
  NoSuffixPatternModel.of_length_toList_eq fun s t hs ht => by
    change s = "a" at hs; change t = "a" at ht; subst hs ht; rfl

end PatBasicHand

-- `String.Slice.Pattern.Model.NoPrefixPatternModel.eq_empty` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] (s t : String),
    PatternModel.Matches pat s → PatternModel.Matches pat (s ++ t) → t = "" :=
  fun h => absurd (h (pat := P.tru) "" "a" trivial trivial) (by decide)

-- `String.Slice.Pattern.Model.NoPrefixPatternModel.eq_empty` (`a : Matches pat s`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [NoPrefixPatternModel pat] (s t : String),
    PatternModel.Matches pat (s ++ t) → t = "" :=
  fun h => absurd (h (pat := P.a) "" "a" (show ("" ++ "a" : String) = "a" by decide)) (by decide)

-- `String.Slice.Pattern.Model.NoPrefixPatternModel.eq_empty` (`a : Matches pat (s ++ t)`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [NoPrefixPatternModel pat] (s t : String),
    PatternModel.Matches pat s → t = "" :=
  fun h => absurd (h (pat := P.a) "a" "b" rfl) (by decide)

-- `String.Slice.Pattern.Model.NoSuffixPatternModel.eq_empty` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] (s t : String),
    PatternModel.Matches pat t → PatternModel.Matches pat (s ++ t) → s = "" :=
  fun h => absurd (h (pat := P.tru) "a" "" trivial trivial) (by decide)

-- `String.Slice.Pattern.Model.NoSuffixPatternModel.eq_empty` (`a : Matches pat t`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [NoSuffixPatternModel pat] (s t : String),
    PatternModel.Matches pat (s ++ t) → s = "" :=
  fun h => absurd (h (pat := P.a) "a" "" (show ("a" ++ "" : String) = "a" by decide)) (by decide)

-- `String.Slice.Pattern.Model.NoSuffixPatternModel.eq_empty` (`a : Matches pat (s ++ t)`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [NoSuffixPatternModel pat] (s t : String),
    PatternModel.Matches pat t → s = "" :=
  fun h => absurd (h (pat := P.a) "b" "a" rfl) (by decide)

-- `String.Slice.Pattern.Model.NoPrefixPatternModel.of_length_toList_eq` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat], NoPrefixPatternModel pat :=
  fun h => absurd ((h (pat := P.tru)).eq_empty "" "a" trivial trivial) (by decide)

-- `String.Slice.Pattern.Model.NoSuffixPatternModel.of_length_toList_eq` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat], NoSuffixPatternModel pat :=
  fun h => absurd ((h (pat := P.tru)).eq_empty "a" "" trivial trivial) (by decide)

-- `String.Slice.Pattern.Model.isLongestMatch_iff_isMatch` (`inst : NoPrefixPatternModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] {s : Slice} {pos : s.Pos},
    IsLongestMatch pat pos ↔ IsMatch pat pos :=
  fun h => ((h P.tru (s := sA) (pos := sA.startPos)).2 ⟨trivial⟩).not_isMatch sA.endPos sA_lt ⟨trivial⟩

-- `String.Slice.Pattern.Model.isLongestRevMatch_iff_isRevMatch` (`inst : NoSuffixPatternModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] {s : Slice} {pos : s.Pos},
    IsLongestRevMatch pat pos ↔ IsRevMatch pat pos :=
  fun h => ((h P.tru (s := sA) (pos := sA.endPos)).2 ⟨trivial⟩).not_isRevMatch sA.startPos sA_lt ⟨trivial⟩

/-! ## `ForwardPattern` / `BackwardPattern` laws -/

-- `String.Slice.Pattern.StrictForwardPattern.ne_startPos` (`self`): `P.fal` skips nothing.
example : ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} (h : s.isEmpty = false) (q : s.Pos),
    ForwardPattern.skipPrefixOfNonempty? pat s h = some q → q ≠ s.startPos :=
  fun h => h (pat := P.fal) sA_nonempty sA.startPos rfl rfl

-- `String.Slice.Pattern.StrictForwardPattern.ne_startPos` (`a`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [StrictForwardPattern pat] {s : Slice}
    (h : s.isEmpty = false) (q : s.Pos), q ≠ s.startPos :=
  fun h => h (pat := P.tru) sA_nonempty sA.startPos rfl

-- `String.Slice.Pattern.StrictBackwardPattern.ne_endPos` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} (h : s.isEmpty = false) (q : s.Pos),
    BackwardPattern.skipSuffixOfNonempty? pat s h = some q → q ≠ s.endPos :=
  fun h => h (pat := P.fal) sA_nonempty sA.endPos rfl rfl

-- `String.Slice.Pattern.StrictBackwardPattern.ne_endPos` (`a`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [StrictBackwardPattern pat] {s : Slice}
    (h : s.isEmpty = false) (q : s.Pos), q ≠ s.endPos :=
  fun h => h (pat := P.tru) sA_nonempty sA.endPos rfl

-- `String.Slice.Pattern.LawfulForwardPattern.skipPrefixOfNonempty?_eq` (`self`): `P.broken`.
example : ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} (h : s.isEmpty = false),
    ForwardPattern.skipPrefixOfNonempty? pat s h = ForwardPattern.skipPrefix? pat s :=
  fun h => nomatch (h (pat := P.broken) sA_nonempty : some sA.startPos = none)

-- `String.Slice.Pattern.LawfulForwardPattern.startsWith_eq` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] (s : Slice),
    ForwardPattern.startsWith pat s = (ForwardPattern.skipPrefix? pat s).isSome :=
  fun h => Bool.noConfusion (h (pat := P.broken) sA)

-- `String.Slice.Pattern.LawfulBackwardPattern.skipSuffixOfNonempty?_eq` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} (h : s.isEmpty = false),
    BackwardPattern.skipSuffixOfNonempty? pat s h = BackwardPattern.skipSuffix? pat s :=
  fun h => nomatch (h (pat := P.broken) sA_nonempty : some sA.endPos = none)

-- `String.Slice.Pattern.LawfulBackwardPattern.endsWith_eq` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] (s : Slice),
    BackwardPattern.endsWith pat s = (BackwardPattern.skipSuffix? pat s).isSome :=
  fun h => Bool.noConfusion (h (pat := P.broken) sA)

-- `String.Slice.Pattern.Model.LawfulForwardPatternModel.toLawfulForwardPattern` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat], LawfulForwardPattern pat :=
  fun h => Bool.noConfusion ((h (pat := P.broken)).startsWith_eq sA)

-- `String.Slice.Pattern.Model.LawfulBackwardPatternModel.toLawfulBackwardPattern` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat], LawfulBackwardPattern pat :=
  fun h => Bool.noConfusion ((h (pat := P.broken)).endsWith_eq sA)

-- `String.Slice.Pattern.Model.LawfulForwardPatternModel.skipPrefix?_eq_some_iff` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] {s : Slice} (pos : s.Pos),
    ForwardPattern.skipPrefix? pat s = some pos ↔ IsLongestMatch pat pos :=
  fun h => not_isLongestMatch_fal ((h (pat := P.fal) (s := sE) sE.startPos).1 rfl)

-- `String.Slice.Pattern.Model.LawfulBackwardPatternModel.skipSuffix?_eq_some_iff` (`self`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] {s : Slice} (pos : s.Pos),
    BackwardPattern.skipSuffix? pat s = some pos ↔ IsLongestRevMatch pat pos :=
  fun h => not_isLongestRevMatch_fal ((h (pat := P.fal) (s := sE) sE.endPos).1 rfl)

-- `String.Slice.Pattern.Model.LawfulForwardPatternModel.skipPrefix?_eq_none_iff`
-- (`inst : LawfulForwardPatternModel pat`): `P.tru` never skips but matches everywhere.
example : ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] {s : Slice},
    ForwardPattern.skipPrefix? pat s = none ↔ ¬ MatchesAt pat s.startPos :=
  fun h => (h (pat := P.tru) (s := sE)).1 rfl (tru_matchesAt _)

-- `String.Slice.Pattern.Model.LawfulForwardPatternModel.skipPrefix?_sliceFrom_eq_none_iff`
-- (`inst : LawfulForwardPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] {s : Slice} {p₀ : s.Pos},
    ForwardPattern.skipPrefix? pat (s.sliceFrom p₀) = none ↔ ¬ MatchesAt pat p₀ :=
  fun h => (h (pat := P.tru) (s := sE) (p₀ := sE.startPos)).1 rfl (tru_matchesAt _)

-- `String.Slice.Pattern.Model.LawfulBackwardPatternModel.skipSuffix?_eq_none_iff`
-- (`inst : LawfulBackwardPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] {s : Slice},
    BackwardPattern.skipSuffix? pat s = none ↔ ¬ RevMatchesAt pat s.endPos :=
  fun h => (h (pat := P.tru) (s := sE)).1 rfl (tru_revMatchesAt _)

-- `String.Slice.Pattern.Model.LawfulBackwardPatternModel.skipSuffix?_sliceTo_eq_none_iff`
-- (`inst : LawfulBackwardPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] {s : Slice} {p₀ : s.Pos},
    BackwardPattern.skipSuffix? pat (s.sliceTo p₀) = none ↔ ¬ RevMatchesAt pat p₀ :=
  fun h => (h (pat := P.tru) (s := sE) (p₀ := sE.endPos)).1 rfl (tru_revMatchesAt _)

/-! ## Default searchers -/

-- `String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.instFiniteIdSearchStepOfStrictForwardPattern`
-- (`inst : StrictForwardPattern pat`): `P.fal` skips the empty prefix, so the searcher loops.
example : ¬ ∀ {ρ : Type} (pat : ρ) {s : Slice} [ForwardPattern pat],
    Iterators.Finite (ToForwardSearcher.DefaultForwardSearcher pat s) Id :=
  fun h => not_finite_fwd (h P.fal)

-- `String.Slice.Pattern.ToBackwardSearcher.DefaultBackwardSearcher.instFiniteIdSearchStepOfStrictBackwardPattern`
-- (`inst : StrictBackwardPattern pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) {s : Slice} [BackwardPattern pat],
    Iterators.Finite (ToBackwardSearcher.DefaultBackwardSearcher pat s) Id :=
  fun h => not_finite_bwd (h P.fal)

-- `String.Slice.Pattern.Model.LawfulToForwardSearcherModel.defaultImplementation`
-- (`inst : StrictForwardPattern pat`, dependent: the `Finite` instance in the statement uses it)
example : ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat], StrictForwardPattern pat :=
  fun h => (h (pat := P.fal)).ne_startPos (s := sA) sA_nonempty sA.startPos rfl rfl

-- `String.Slice.Pattern.Model.LawfulToBackwardSearcherModel.defaultImplementation`
-- (`inst : StrictBackwardPattern pat`, dependent)
example : ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat], StrictBackwardPattern pat :=
  fun h => (h (pat := P.fal)).ne_endPos (s := sA) sA_nonempty sA.endPos rfl rfl

-- `String.Slice.Pattern.Model.LawfulToForwardSearcherModel.defaultImplementation`
-- (`inst : LawfulForwardPatternModel pat`): `P.tru` never skips a prefix, so the default searcher
-- starts with a rejected step, although `P.tru` matches everywhere.
example : ¬ ∀ {ρ : Type} {pat : ρ} [ForwardPattern pat] [StrictForwardPattern pat] [PatternModel pat],
    letI : ToForwardSearcher pat (ToForwardSearcher.DefaultForwardSearcher pat) := .defaultImplementation
    LawfulToForwardSearcherModel pat := by
  intro h
  have hv := (h (pat := P.tru)).isValidSearchFrom_toList sA
  obtain ⟨a, b, l, hl⟩ := default_fwd_head
  change IsValidSearchFrom P.tru sA.startPos
    (ToForwardSearcher.DefaultForwardSearcher.iter P.tru sA).toList at hv
  rw [hl] at hv
  obtain ⟨-, -, -, h₂⟩ := vsf_cons hv
  exact (h₂ a b rfl).2 a (Std.le_refl _) (h₂ a b rfl).1 (tru_matchesAt _)

-- `String.Slice.Pattern.Model.LawfulToBackwardSearcherModel.defaultImplementation`
-- (`inst : LawfulBackwardPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [BackwardPattern pat] [StrictBackwardPattern pat] [PatternModel pat],
    letI : ToBackwardSearcher pat (ToBackwardSearcher.DefaultBackwardSearcher pat) := .defaultImplementation
    LawfulToBackwardSearcherModel pat := by
  intro h
  have hv := (h (pat := P.tru)).isValidRevSearchFrom_toList sA
  obtain ⟨a, b, l, hl⟩ := default_bwd_head
  change IsValidRevSearchFrom P.tru sA.endPos
    (ToBackwardSearcher.DefaultBackwardSearcher.iter P.tru sA).toList at hv
  rw [hl] at hv
  obtain ⟨-, -, -, h₂⟩ := vrsf_cons hv
  exact (h₂ a b rfl).2 b (h₂ a b rfl).1 (Std.le_refl _) (tru_revMatchesAt _)

/-! ## `find?`, `contains` with list searchers

`P.tru` with `stepsNone` is a lawful searcher for the all-matching model (the empty slice gives no
step at all, so the match of the empty string at its only position is never reported);
`P.fal` with `stepsAll` reports a match that the never-matching model does not have. -/

namespace PatBasicHand

theorem find?_tru_sE : sE.find? P.tru = none := by
  simp [String.Slice.find?, ← Iter.findSome?_toList, ToForwardSearcher.toSearcher, stepsNone]

theorem contains_tru_sE : sE.contains P.tru = false := by
  simp [String.Slice.contains, ← Iter.any_toList, ToForwardSearcher.toSearcher, stepsNone]

theorem find?_fal (s : Slice) : s.find? P.fal = some s.startPos := by
  simp [String.Slice.find?, ← Iter.findSome?_toList, ToForwardSearcher.toSearcher, stepsAll]

theorem contains_fal (s : Slice) : s.contains P.fal = true := by
  simp [String.Slice.contains, ← Iter.any_toList, ToForwardSearcher.toSearcher, stepsAll]

theorem posFind?_tru_sE : sE.startPos.find? P.tru = none := by
  rw [String.Slice.Pos.find?_eq_find?_sliceFrom]
  simp [String.Slice.find?, ← Iter.findSome?_toList, ToForwardSearcher.toSearcher, stepsNone]

theorem posFind?_fal {s : Slice} (p : s.Pos) : p.find? P.fal = some p := by
  rw [String.Slice.Pos.find?_eq_find?_sliceFrom, find?_fal]
  simp

end PatBasicHand

-- `String.Slice.Pattern.Model.find?_eq_some_iff` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] [LawfulToForwardSearcherModel pat] {s : Slice} {pos : s.Pos},
    s.find? pat = some pos ↔ MatchesAt pat pos ∧ (∀ pos', pos' < pos → ¬ MatchesAt pat pos') := by
  intro h
  have := (h P.tru (s := sE) (pos := sE.startPos)).2
    ⟨tru_matchesAt _, fun p hp => absurd (String.Slice.Pos.startPos_le p) (Std.not_le.2 hp)⟩
  rw [find?_tru_sE] at this
  cases this

-- `String.Slice.Pattern.Model.find?_eq_some_iff` (`inst : LawfulToForwardSearcherModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] {s : Slice} {pos : s.Pos},
    s.find? pat = some pos ↔ MatchesAt pat pos ∧ (∀ pos', pos' < pos → ¬ MatchesAt pat pos') :=
  fun h => not_matchesAt_fal ((h P.fal (s := sE) (pos := sE.startPos)).1 (find?_fal _)).1

-- `String.Slice.Pattern.Model.find?_eq_none_iff` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] [LawfulToForwardSearcherModel pat] {s : Slice},
    s.find? pat = none ↔ ∀ (pos : s.Pos), ¬ MatchesAt pat pos :=
  fun h => (h P.tru (s := sE)).1 find?_tru_sE sE.startPos (tru_matchesAt _)

-- `String.Slice.Pattern.Model.find?_eq_none_iff` (`inst : LawfulToForwardSearcherModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] {s : Slice},
    s.find? pat = none ↔ ∀ (pos : s.Pos), ¬ MatchesAt pat pos := by
  intro h
  have := (h P.fal (s := sE)).2 fun _ => not_matchesAt_fal
  rw [find?_fal] at this
  cases this

-- `String.Slice.Pattern.Model.contains_eq_true_iff` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] [LawfulToForwardSearcherModel pat] {s : Slice},
    s.contains pat ↔ ∃ (pos : s.Pos), MatchesAt pat pos := by
  intro h
  have := (h P.tru (s := sE)).2 ⟨_, tru_matchesAt sE.startPos⟩
  rw [contains_tru_sE] at this
  cases this

-- `String.Slice.Pattern.Model.contains_eq_true_iff` (`inst : LawfulToForwardSearcherModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] {s : Slice},
    s.contains pat ↔ ∃ (pos : s.Pos), MatchesAt pat pos :=
  fun h => ((h P.fal (s := sE)).1 (contains_fal _)).elim fun _ => not_matchesAt_fal

-- `String.Slice.Pattern.Model.contains_eq_false_iff` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] [LawfulToForwardSearcherModel pat] {s : Slice},
    s.contains pat = false ↔ ∀ (pos : s.Pos), ¬ MatchesAt pat pos :=
  fun h => (h P.tru (s := sE)).1 contains_tru_sE sE.startPos (tru_matchesAt _)

-- `String.Slice.Pattern.Model.contains_eq_false_iff` (`inst : LawfulToForwardSearcherModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] {s : Slice},
    s.contains pat = false ↔ ∀ (pos : s.Pos), ¬ MatchesAt pat pos := by
  intro h
  have := (h P.fal (s := sE)).2 fun _ => not_matchesAt_fal
  rw [contains_fal] at this
  cases this

-- `String.Slice.Pattern.Model.posFind?_eq_some_iff` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] [LawfulToForwardSearcherModel pat] {s : Slice} {pos pos' : s.Pos},
    pos.find? pat = some pos' ↔ pos ≤ pos' ∧ MatchesAt pat pos' ∧
      (∀ pos'', pos ≤ pos'' → pos'' < pos' → ¬ MatchesAt pat pos'') := by
  intro h
  have := (h (pat := P.tru) (s := sE) (pos := sE.startPos) (pos' := sE.startPos)).2
    ⟨Std.le_refl _, tru_matchesAt _, fun p hp₁ hp₂ => absurd hp₁ (Std.not_le.2 hp₂)⟩
  rw [posFind?_tru_sE] at this
  cases this

-- `String.Slice.Pattern.Model.posFind?_eq_some_iff` (`inst : LawfulToForwardSearcherModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] {s : Slice} {pos pos' : s.Pos},
    pos.find? pat = some pos' ↔ pos ≤ pos' ∧ MatchesAt pat pos' ∧
      (∀ pos'', pos ≤ pos'' → pos'' < pos' → ¬ MatchesAt pat pos'') :=
  fun h => not_matchesAt_fal
    ((h (pat := P.fal) (s := sE) (pos := sE.startPos) (pos' := sE.startPos)).1 (posFind?_fal _)).2.1

-- `String.Slice.Pattern.Model.posFind?_eq_none_iff` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] [LawfulToForwardSearcherModel pat] {s : Slice} {pos : s.Pos},
    pos.find? pat = none ↔ ∀ pos', pos ≤ pos' → ¬ MatchesAt pat pos' :=
  fun h => (h (pat := P.tru) (s := sE) (pos := sE.startPos)).1 posFind?_tru_sE sE.startPos (Std.le_refl _)
    (tru_matchesAt _)

-- `String.Slice.Pattern.Model.posFind?_eq_none_iff` (`inst : LawfulToForwardSearcherModel pat`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] {s : Slice} {pos : s.Pos},
    pos.find? pat = none ↔ ∀ pos', pos ≤ pos' → ¬ MatchesAt pat pos' := by
  intro h
  have := (h (pat := P.fal) (s := sE) (pos := sE.startPos)).2 fun _ _ => not_matchesAt_fal
  rw [posFind?_fal] at this
  cases this

/-! ## Splitting

On the empty slice, `stepsAll` reports the match `[startPos, startPos)`, so splitting yields two
empty pieces instead of one. This searcher is lawful for `P.truE` (all-matching, not strict) and
unlawful for `P.fal` (strict). -/

namespace PatBasicHand

theorem truE_steps : (ToForwardSearcher.toSearcher P.truE sE).toList = stepsAll sE := List.toList_iter
theorem fal_steps : (ToForwardSearcher.toSearcher P.fal sE).toList = stepsAll sE := List.toList_iter

end PatBasicHand

-- `String.toList_split_empty` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] {σ : Slice → Type} [ToForwardSearcher pat σ]
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [LawfulToForwardSearcherModel pat], ("".split pat).toList.map Slice.copy = [""] := by
  intro h
  have := congrArg List.length (h P.truE)
  rw [String.split_eq_split_toSlice, String.Slice.toList_split_eq_splitToSubslice] at this
  simp only [List.length_map] at this
  rw [length_splitToSubslice_sE truE_steps] at this
  cases this

-- `String.toList_split_empty` (`inst : LawfulToForwardSearcherModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] {σ : Slice → Type}
    [ToForwardSearcher pat σ] [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id],
    ("".split pat).toList.map Slice.copy = [""] := by
  intro h
  have := congrArg List.length (h P.fal)
  rw [String.split_eq_split_toSlice, String.Slice.toList_split_eq_splitToSubslice] at this
  simp only [List.length_map] at this
  rw [length_splitToSubslice_sE fal_steps] at this
  cases this

-- `String.Slice.toList_split_of_isEmpty` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] {σ : Slice → Type} [ToForwardSearcher pat σ]
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [LawfulToForwardSearcherModel pat] {s : Slice}, s.isEmpty = true →
    (s.split pat).toList.map Slice.copy = [""] := by
  intro h
  have := congrArg List.length (h P.truE sE_empty)
  rw [String.Slice.toList_split_eq_splitToSubslice] at this
  simp only [List.length_map] at this
  rw [length_splitToSubslice_sE truE_steps] at this
  cases this

-- `String.Slice.toList_split_of_isEmpty` (`inst : LawfulToForwardSearcherModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] {σ : Slice → Type}
    [ToForwardSearcher pat σ] [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    {s : Slice}, s.isEmpty = true → (s.split pat).toList.map Slice.copy = [""] := by
  intro h
  have := congrArg List.length (h P.fal sE_empty)
  rw [String.Slice.toList_split_eq_splitToSubslice] at this
  simp only [List.length_map] at this
  rw [length_splitToSubslice_sE fal_steps] at this
  cases this

-- `String.Slice.toList_splitToSubslice_of_isEmpty` (`inst : StrictPatternModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] {σ : Slice → Type} [ToForwardSearcher pat σ]
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [LawfulToForwardSearcherModel pat] {s : Slice}, s.isEmpty = true →
    (s.splitToSubslice pat).toList = [s.subsliceFrom s.endPos] := by
  intro h
  have := congrArg List.length (h P.truE sE_empty)
  rw [length_splitToSubslice_sE truE_steps] at this
  cases this

-- `String.Slice.toList_splitToSubslice_of_isEmpty` (`inst : LawfulToForwardSearcherModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] {σ : Slice → Type}
    [ToForwardSearcher pat σ] [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    {s : Slice}, s.isEmpty = true → (s.splitToSubslice pat).toList = [s.subsliceFrom s.endPos] := by
  intro h
  have := congrArg List.length (h P.fal sE_empty)
  rw [length_splitToSubslice_sE fal_steps] at this
  cases this

-- `String.Slice.Pattern.toList_splitToSubslice_eq_modelSplit` (`inst : LawfulToForwardSearcherModel pat`)
example : ¬ ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] {σ : Slice → Type}
    [ToForwardSearcher pat σ] [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    (s : Slice), (s.splitToSubslice pat).toList = Model.split pat s.startPos s.startPos (Std.le_refl _) := by
  intro h
  have := congrArg List.length (h P.fal sE)
  rw [length_splitToSubslice_sE fal_steps] at this
  have e : Model.split (s := sE) P.fal sE.startPos sE.startPos (Std.le_refl _) = _ := Model.split_endPos
  rw [e] at this
  cases this

/-! ## `Model.split` equations: `P.fal` and `P.ne` (non-empty strings) are strict -/

namespace PatBasicHand

theorem ne_lma : IsLongestMatchAt P.ne sA.startPos sA.endPos :=
  isLongestMatchAt_endPos _ (by simp [PatternModel.Matches])

/-- On `"a"`, `P.ne` splits from the start into two pieces. -/
theorem split_ne_sA : (Model.split P.ne sA.startPos sA.startPos (Std.le_refl _)).length = 2 := by
  rw [Model.split_eq_of_isLongestMatchAt ne_lma, Model.split_endPos]
  rfl

theorem split_ne_sA_end : (Model.split P.ne sA.startPos sA.endPos (Std.le_of_lt sA_lt)).length = 1 := by
  rw [Model.split_endPos]
  rfl

end PatBasicHand

-- `String.Slice.Pattern.Model.split_eq_of_isLongestMatchAt` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice}
    {firstRejected start stop : s.Pos} {hle : firstRejected ≤ start},
    Model.split pat firstRejected start hle =
      s.subslice _ _ hle :: Model.split pat stop stop (Std.le_refl _) := by
  intro h
  have := congrArg List.length (h (pat := P.fal) (s := sE) (firstRejected := sE.endPos) (start := sE.endPos)
    (stop := sE.endPos) (hle := Std.le_refl _))
  simp only [Model.split_endPos] at this
  cases this

-- `String.Slice.Pattern.Model.split_eq_of_not_matchesAt` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice}
    {firstRejected start : s.Pos} (stop : s.Pos) (h₀ : start ≤ stop) {hle : firstRejected ≤ start},
    Model.split pat firstRejected start hle =
      Model.split pat firstRejected stop (by exact Std.le_trans hle h₀) := by
  intro h
  have := congrArg List.length (h (pat := P.ne) (s := sA) (firstRejected := sA.startPos)
    (start := sA.startPos) sA.endPos (Std.le_of_lt sA_lt) (hle := Std.le_refl _))
  rw [split_ne_sA, split_ne_sA_end] at this
  cases this

-- `String.Slice.Pattern.Model.split_eq_next_of_not_matchesAt` (`h`)
example : ¬ ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice}
    {firstRejected start : s.Pos} {hle : firstRejected ≤ start} (hs : start ≠ s.endPos),
    Model.split pat firstRejected start hle =
      Model.split pat firstRejected (start.next hs) (by exact Std.le_trans hle (by simp)) := by
  intro h
  have := congrArg List.length (h (pat := P.ne) (s := sA) (firstRejected := sA.startPos)
    (start := sA.startPos) (hle := Std.le_refl _) sA_ne)
  simp only [sA_next] at this
  rw [split_ne_sA, split_ne_sA_end] at this
  cases this
