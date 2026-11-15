import Lean
/-!
Hand pass `OpE` (hand10): 170 open `Finite`/`Productive` hypotheses of `Init.Data.Iterators`
lemmas (and of `Std.Slice`, `Std.Iter.joinString`/`intercalateString`, `String.Slice` split) whose
two sides are, without the hypothesis, opaque on non-`Finite` iterators: the collectors
`toList`/`toArray`/`toListRev` and the default `IteratorLoop` are `WellFounded.extrinsicFix₂/₃`,
which is the opaque `WellFounded.opaqueFix` when the iterator type is not `Finite`.

7 necessary, 0 removable, 163 independent (`runs/hand10/OpE_independent.jsonl`).

Necessary (`¬T'`, `drop0% T i` = `T` without binder `i`, universes `0`): lists are finite, but
consumers that only need `Productive` (`atIdxSlow?`, `take`) still compute on `YL` (yields `0`
forever) and `UP` (yields `0, 1, 2, …`): `getElem?_toList_eq_atIdxSlow?`,
`mem_toList/mem_toArray_iff_isPlausibleIndirectOutput`, `toList/toArray/toListRev_take_of_finite`,
`atIdxSlow?_append` (`Finite α₁`).

Independent: both sides are `opaqueFix` values at different arguments (or one side is a single
opaque value), and no equation of the library relates them; interpreting `opaqueFix` at those
arguments by the finite-case formula makes `T'` true, changing one value makes it false (argument,
not a Lean proof; families and details in the jsonl). The support lemmas below (`….hI_neg`, not
verdicts) derive `¬T'` from an assignment of values to the opaque terms, e.g.
`(yl.map (· + 1)).toList = []` and `yl.toList = [0]`, at a non-`Finite` instance.

Reusable models (section "Models"): iterators `YL` (yields `0` forever: productive, not finite),
`EM` (always done: finite), `UP` (counter: deterministic, productive, not finite), `LP` (skips
forever: not productive; `Take.LP.not_finite`), `YD` (yields forever from `true`, done from
`false`: productive, not finite), `YL.doneInst`/`YL.doneFinite` (a second, finite `Iterator`
instance on `YL`), `YSe` (a forward searcher that rejects forever); the monad `TM` (`Id` with the
trivial `MonadAttach`, lawful and weakly lawful, so `attachLift (pure x) ≠ pure x`, unlike `Id`);
evaluation lemmas `YL.atIdx`, `YL.take_get`, `YL.append_atIdx`, `EM.toList`, `ETM.toList`, ….

Run with the lean4 repo's stage1 binary: `lean checks/OpEHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
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

namespace OpEHand
open Std Std.Iterators

/-! ## Models -/

theorem wf_irrefl {α : Sort u} {r : α → α → Prop} (h : WellFounded r) (a : α) : ¬ r a a := by
  have := h.apply a
  induction this with
  | intro x _ ih => exact fun hx => ih x hx hx

/-! `YL`: yields `0` and stays (productive, deterministic, not finite). -/
structure YL where u : Unit

instance YL.inst {m : Type → Type} [Pure m] : Iterator YL m Nat where
  IsPlausibleStep it s := s = .yield it 0
  step it := pure (.deflate ⟨.yield it 0, rfl⟩)

instance YL.productive {m : Type → Type} [Pure m] : Productive YL m :=
  ⟨⟨fun a => ⟨a, fun b h => by cases h⟩⟩⟩

theorem YL.not_finite {m : Type → Type} [Pure m] : ¬ Finite YL m :=
  fun h => wf_irrefl h.wf ⟨⟨()⟩⟩ ⟨_, rfl, rfl⟩

abbrev yl : Iter (α := YL) Nat := ⟨⟨()⟩⟩

theorem YL.step : yl.step.val = .yield yl 0 := by
  simp only [Iter.step, IterM.step, Iterator.step, IterM.Step.toPure, Id.run, pure]
  erw [Shrink.inflate_deflate]; rfl

theorem YL.atIdx (n : Nat) : yl.atIdxSlow? n = some 0 := by
  induction n with
  | zero => rw [Iter.atIdxSlow?_eq_match, YL.step]
  | succ n ih => rw [Iter.atIdxSlow?_eq_match, YL.step]; exact ih

/-! `EM`: always done (finite). -/
structure EM where u : Unit

instance EM.inst {m : Type → Type} [Pure m] : Iterator EM m Nat where
  IsPlausibleStep _ s := s = .done
  step _ := pure (.deflate ⟨.done, rfl⟩)

instance EM.finite {m : Type → Type} [Pure m] : Finite EM m := .of_finitenessRelation {
  Rel := fun _ _ => False
  wf := ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩
  subrelation := by rintro _ _ ⟨s, hs, hp⟩; subst hp; cases hs }

abbrev em : Iter (α := EM) Nat := ⟨⟨()⟩⟩

theorem EM.step : em.step.val = .done := by
  simp only [Iter.step, IterM.step, Iterator.step, IterM.Step.toPure, Id.run, pure]
  erw [Shrink.inflate_deflate]; rfl

theorem EM.atIdx (n : Nat) : em.atIdxSlow? n = none := by
  rw [Iter.atIdxSlow?_eq_match, EM.step]

/-! `UP`: state `n` yields `n` and moves to `n+1` (deterministic, productive, not finite). -/
structure UP where n : Nat

instance UP.inst {m : Type → Type} [Pure m] : Iterator UP m Nat where
  IsPlausibleStep it s := s = .yield ⟨⟨it.internalState.n + 1⟩⟩ it.internalState.n
  step it := pure (.deflate ⟨.yield ⟨⟨it.internalState.n + 1⟩⟩ it.internalState.n, rfl⟩)

instance UP.det {m : Type → Type} [Pure m] : LawfulDeterministicIterator UP m :=
  ⟨fun _ => ⟨_, rfl⟩⟩

theorem UP.out (k n : Nat) : (⟨⟨k⟩⟩ : Iter (α := UP) Nat).IsPlausibleIndirectOutput (k + n) := by
  induction n generalizing k with
  | zero => exact .direct ⟨⟨⟨k + 1⟩⟩, rfl⟩
  | succ n ih =>
    refine .indirect (it' := ⟨⟨k + 1⟩⟩) ⟨_, rfl, rfl⟩ ?_
    have := ih (k + 1); rwa [Nat.add_right_comm, Nat.add_assoc] at this

theorem le_sum_of_mem {x : Nat} : ∀ {L : List Nat}, x ∈ L → x ≤ L.sum
  | _ :: _, .head _ => by simp
  | y :: L, .tail _ h => by have := le_sum_of_mem h; simp; omega

theorem YL.stepFull : yl.step = .yield yl 0 rfl := Subtype.ext YL.step

theorem YL.take_get (n l : Nat) : (yl.take n).toList[l]? = if l < n then some 0 else none := by
  rw [Iter.getElem?_toList_eq_atIdxSlow?, Iter.atIdxSlow?_take, YL.atIdx]

theorem YL.take_length (n : Nat) : (yl.take n).toList.length = n := by
  have h1 := YL.take_get n n
  simp only [Nat.lt_irrefl, if_false, List.getElem?_eq_none_iff] at h1
  cases n with
  | zero => omega
  | succ k =>
    have h2 := YL.take_get (k + 1) k
    simp only [Nat.lt_succ_self, if_true] at h2
    have := (List.getElem?_eq_some_iff.1 h2).1
    omega

theorem YL.append_atIdx (n : Nat) : (yl.append em).atIdxSlow? n = some 0 := by
  induction n with
  | zero => rw [Iter.atIdxSlow?_eq_match, Iter.step_append, YL.stepFull]
  | succ n ih => rw [Iter.atIdxSlow?_eq_match, Iter.step_append, YL.stepFull]; exact ih

/-! `LP`: skips to itself (neither productive nor finite). -/
structure LP where u : Unit

instance LP.inst {m : Type → Type} [Pure m] : Iterator LP m Nat where
  IsPlausibleStep it s := s = .skip it
  step it := pure (.deflate ⟨.skip it, rfl⟩)

abbrev lp : Iter (α := LP) Nat := ⟨⟨()⟩⟩
abbrev lpm : IterM (α := LP) Id Nat := ⟨⟨()⟩⟩

theorem LP.not_productive {m : Type → Type} [Pure m] : ¬ Productive LP m :=
  fun h => wf_irrefl h.wf ⟨⟨()⟩⟩ rfl

theorem Take.LP.not_finite : ¬ Finite (Types.Take LP Id) Id := fun h =>
  wf_irrefl h.wf (lpm.take 1) ⟨.skip (lpm.take 1), rfl, .skip rfl (by decide)⟩

/-! `YD`: state `true` yields `0` and stays, state `false` is done (productive, not finite). -/
structure YD where b : Bool

def YD.stepv {m : Type → Type} : Bool → IterStep (IterM (α := YD) m Nat) Nat
  | true => .yield ⟨⟨true⟩⟩ 0
  | false => .done

instance YD.inst {m : Type → Type} [Pure m] : Iterator YD m Nat where
  IsPlausibleStep it s := s = YD.stepv it.internalState.b
  step it := pure (.deflate ⟨YD.stepv it.internalState.b, rfl⟩)

instance YD.productive {m : Type → Type} [Pure m] : Productive YD m :=
  ⟨⟨fun a => ⟨a, fun b h => by rcases a with ⟨⟨_ | _⟩⟩ <;> cases h⟩⟩⟩

theorem YD.not_finite {m : Type → Type} [Pure m] : ¬ Finite YD m :=
  fun h => wf_irrefl h.wf ⟨⟨true⟩⟩ ⟨_, rfl, rfl⟩

abbrev yd0 : Iter (α := YD) Nat := ⟨⟨false⟩⟩

theorem YD.atIdx (n : Nat) : yd0.atIdxSlow? n = none := by
  rw [Iter.atIdxSlow?_eq_match]
  simp only [Iter.step, IterM.step, Iterator.step, IterM.Step.toPure, Id.run, pure]
  erw [Shrink.inflate_deflate]; rfl

theorem EM.toList : em.toList = [] := by rw [Iter.toList_eq_match_step, EM.step]
theorem EM.toListRev : em.toListRev = [] := by rw [Iter.toListRev_eq_match_step, EM.step]
theorem EM.toArray : em.toArray = #[] := by rw [Iter.toArray_eq_match_step, EM.step]

set_option hygiene false in
macro "opq_close" : tactic => `(tactic| first
  | (cases this; done)
  | (simp at this; done)
  | (simp at this; cases this; done)
  | (simp at this; have := congrArg Array.toList this; simp at this; done)
  | (exact absurd (congrArg Id.run this) (by simp))
  | (exact absurd (congrArg Array.toList this) (by simp)))

abbrev ylm : IterM (α := YL) Id Nat := ⟨⟨()⟩⟩

/-! `TM`: `Id` with the trivial `MonadAttach` (`CanReturn _ _ = True`), lawful and weakly lawful.
Unlike `Id`'s own `MonadAttach`, `attachLift (pure x)` is not `pure x` here, so `mapM (pure ∘ f)`
and `map f` are different combinators. -/
def TM (α : Type) : Type := α
instance TM.monad : Monad TM := inferInstanceAs (Monad Id)
instance TM.lawful : LawfulMonad TM := inferInstanceAs (LawfulMonad Id)
instance TM.attach : MonadAttach TM := .trivial
instance TM.weakly : WeaklyLawfulMonadAttach TM := ⟨fun {_ x} => rfl⟩

abbrev ytm : IterM (α := YL) TM Nat := ⟨⟨()⟩⟩
abbrev etm : IterM (α := EM) TM Nat := ⟨⟨()⟩⟩
abbrev lptm : IterM (α := LP) TM Nat := ⟨⟨()⟩⟩
theorem ETM.step : etm.step = pure (.deflate ⟨.done, rfl⟩) := rfl
theorem ETM.toList : etm.toList = pure [] := by
  rw [IterM.toList_eq_match_step, ETM.step]; simp only [pure_bind]; erw [Shrink.inflate_deflate]
theorem ETM.toListRev : etm.toListRev = pure [] := by
  rw [IterM.toListRev_eq_match_step, ETM.step]; simp only [pure_bind]; erw [Shrink.inflate_deflate]
theorem ETM.toArray : etm.toArray = pure #[] := by
  rw [IterM.toArray_eq_match_step, ETM.step]; simp only [pure_bind]; erw [Shrink.inflate_deflate]


/-! ## Necessary -/

-- `Std.Iter.getElem?_toList_eq_atIdxSlow?`, idx 3 (inst): `YL` (productive, not finite): `atIdxSlow? k = some 0` for every `k`, but the list `L := yl.toList` has no entry at `L.length`
theorem getElem?_toList_eq_atIdxSlow?.h3 : ¬ drop0% Std.Iter.getElem?_toList_eq_atIdxSlow? 3 := fun h => by
  have := h (it := yl) (k := yl.toList.length)
  rw [YL.atIdx] at this; simp at this

-- `Std.Iter.mem_toList_iff_isPlausibleIndirectOutput`, idx 3 (inst): `UP` from state `0` (deterministic): every `k` is a plausible output, but the finite list `toList` does not contain its sum plus one
theorem mem_toList_iff_isPlausibleIndirectOutput.h3 : ¬ drop0% Std.Iter.mem_toList_iff_isPlausibleIndirectOutput 3 := fun h => by
  let L := (⟨⟨0⟩⟩ : Iter (α := UP) Nat).toList
  have : L.sum + 1 ∈ L := (h (it := (⟨⟨0⟩⟩ : Iter (α := UP) Nat)) (out := L.sum + 1)).2 (by simpa using UP.out 0 (L.sum + 1))
  have := le_sum_of_mem this
  omega

-- `Std.Iter.mem_toArray_iff_isPlausibleIndirectOutput`, idx 3 (inst): as for the list version, with `toArray`
theorem mem_toArray_iff_isPlausibleIndirectOutput.h3 : ¬ drop0% Std.Iter.mem_toArray_iff_isPlausibleIndirectOutput 3 := fun h => by
  let A := (⟨⟨0⟩⟩ : Iter (α := UP) Nat).toArray
  have : A.toList.sum + 1 ∈ A := (h (it := (⟨⟨0⟩⟩ : Iter (α := UP) Nat)) (out := A.toList.sum + 1)).2 (by simpa using UP.out 0 (A.toList.sum + 1))
  have := le_sum_of_mem (Array.mem_toList_iff.2 this)
  omega

-- `Std.Iter.toList_take_of_finite`, idx 4 (inst): `YL`: `Take YL` is finite and `(yl.take n).toList` has `n` entries, but `L.take (L.length + 1) = L` for `L := yl.toList`
theorem toList_take_of_finite.h4 : ¬ drop0% Std.Iter.toList_take_of_finite 4 := fun h => by
  have := congrArg (·[yl.toList.length]?) (h (it := yl) (n := yl.toList.length + 1))
  simp only [YL.take_get] at this
  simp at this

-- `Std.Iter.toArray_take_of_finite`, idx 4 (inst): `YL`: as for `toList`, at `n := yl.toArray.size + 1`
theorem toArray_take_of_finite.h4 : ¬ drop0% Std.Iter.toArray_take_of_finite 4 := fun h => by
  have := congrArg (·.toList[yl.toArray.size]?) (h (it := yl) (n := yl.toArray.size + 1))
  simp only [Iter.toList_toArray, YL.take_get] at this
  simp at this

-- `Std.Iter.toListRev_take_of_finite`, idx 4 (inst): `YL`: the left side has length `n`, the right side at most `yl.toListRev.length`; take `n := yl.toListRev.length + 1`
theorem toListRev_take_of_finite.h4 : ¬ drop0% Std.Iter.toListRev_take_of_finite 4 := fun h => by
  have := congrArg List.length (h (it := yl) (n := yl.toListRev.length + 1))
  simp only [Iter.toListRev_eq, List.length_reverse, YL.take_length, List.length_drop] at this
  omega

-- `Std.Iter.atIdxSlow?_append`, idx 5 (inst): `it₁ := yl`, `it₂ := em`: `Append YL EM` is productive and `(yl.append em).atIdxSlow? n = some 0` for all `n`, but at `n := yl.toList.length` the right side is `em.atIdxSlow? 0 = none`
theorem atIdxSlow?_append.h5 : ¬ drop0% Std.Iter.atIdxSlow?_append 5 := fun h => by
  have := h (it₁ := yl) (it₂ := em) (n := yl.toList.length)
  rw [YL.append_atIdx] at this
  simp [EM.atIdx] at this

/-! ## Independent: support lemmas (conditional `¬T'` from assignments of values to the opaque terms; not verdicts) -/

-- support for the independent row Std.Iter.toList_append idx 5 (family append): ¬T' from the assignment (yl.append em).toList = []; yl.toList = [0]
theorem Iter.toList_append.h5_neg (h₁ : (yl.append em).toList = []) (h₂ : yl.toList = [0]) :
    ¬ drop0% Std.Iter.toList_append 5 := fun h => by
  have := h (it₁ := yl) (it₂ := em); rw [h₁, h₂, EM.toList] at this; opq_close

-- support for the independent row Std.Iter.toList_append idx 6 (family append): ¬T' from the assignment (em.append yl).toList = []; yl.toList = [0]
theorem Iter.toList_append.h6_neg (h₁ : (em.append yl).toList = []) (h₂ : yl.toList = [0]) :
    ¬ drop0% Std.Iter.toList_append 6 := fun h => by
  have := h (it₁ := em) (it₂ := yl); rw [h₁, h₂, EM.toList] at this; opq_close

-- support for the independent row Std.Iter.toList_filterMap idx 5 (family coll): ¬T' from the assignment (yl.filterMap some).toList = []; yl.toList = [0]
theorem Iter.toList_filterMap.h5_neg (h₁ : (yl.filterMap some).toList = []) (h₂ : yl.toList = [0]) :
    ¬ drop0% Std.Iter.toList_filterMap 5 := fun h => by
  have := h (it := yl) (f := some); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toList_map idx 5 (family coll): ¬T' from the assignment (yl.map (· + 1)).toList = []; yl.toList = [0]
theorem Iter.toList_map.h5_neg (h₁ : (yl.map (· + 1)).toList = []) (h₂ : yl.toList = [0]) :
    ¬ drop0% Std.Iter.toList_map 5 := fun h => by
  have := h (it := yl) (f := (· + 1)); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toList_filter idx 4 (family coll): ¬T' from the assignment (yl.filter (fun _ => true)).toList = []; yl.toList = [0]
theorem Iter.toList_filter.h4_neg (h₁ : (yl.filter (fun _ => true)).toList = []) (h₂ : yl.toList = [0]) :
    ¬ drop0% Std.Iter.toList_filter 4 := fun h => by
  have := h (it := yl) (f := fun _ => true); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toList_uLift idx 4 (family coll): ¬T' from the assignment (yl.uLift : Std.Iter (ULift.{0} Nat)).toList = []; yl.toList = [0]
theorem Iter.toList_uLift.h4_neg (h₁ : (yl.uLift : Std.Iter (ULift.{0} Nat)).toList = []) (h₂ : yl.toList = [0]) :
    ¬ drop0% Std.Iter.toList_uLift 4 := fun h => by
  have := h (it := yl); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toListRev_append idx 5 (family append): ¬T' from the assignment (yl.append em).toListRev = []; yl.toListRev = [0]
theorem Iter.toListRev_append.h5_neg (h₁ : (yl.append em).toListRev = []) (h₂ : yl.toListRev = [0]) :
    ¬ drop0% Std.Iter.toListRev_append 5 := fun h => by
  have := h (it₁ := yl) (it₂ := em); rw [h₁, h₂, EM.toListRev] at this; opq_close

-- support for the independent row Std.Iter.toListRev_append idx 6 (family append): ¬T' from the assignment (em.append yl).toListRev = []; yl.toListRev = [0]
theorem Iter.toListRev_append.h6_neg (h₁ : (em.append yl).toListRev = []) (h₂ : yl.toListRev = [0]) :
    ¬ drop0% Std.Iter.toListRev_append 6 := fun h => by
  have := h (it₁ := em) (it₂ := yl); rw [h₁, h₂, EM.toListRev] at this; opq_close

-- support for the independent row Std.Iter.toListRev_filterMap idx 5 (family coll): ¬T' from the assignment (yl.filterMap some).toListRev = []; yl.toListRev = [0]
theorem Iter.toListRev_filterMap.h5_neg (h₁ : (yl.filterMap some).toListRev = []) (h₂ : yl.toListRev = [0]) :
    ¬ drop0% Std.Iter.toListRev_filterMap 5 := fun h => by
  have := h (it := yl) (f := some); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toListRev_map idx 5 (family coll): ¬T' from the assignment (yl.map (· + 1)).toListRev = []; yl.toListRev = [0]
theorem Iter.toListRev_map.h5_neg (h₁ : (yl.map (· + 1)).toListRev = []) (h₂ : yl.toListRev = [0]) :
    ¬ drop0% Std.Iter.toListRev_map 5 := fun h => by
  have := h (it := yl) (f := (· + 1)); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toListRev_filter idx 4 (family coll): ¬T' from the assignment (yl.filter (fun _ => true)).toListRev = []; yl.toListRev = [0]
theorem Iter.toListRev_filter.h4_neg (h₁ : (yl.filter (fun _ => true)).toListRev = []) (h₂ : yl.toListRev = [0]) :
    ¬ drop0% Std.Iter.toListRev_filter 4 := fun h => by
  have := h (it := yl) (f := fun _ => true); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toListRev_uLift idx 4 (family coll): ¬T' from the assignment (yl.uLift : Std.Iter (ULift.{0} Nat)).toListRev = []; yl.toListRev = [0]
theorem Iter.toListRev_uLift.h4_neg (h₁ : (yl.uLift : Std.Iter (ULift.{0} Nat)).toListRev = []) (h₂ : yl.toListRev = [0]) :
    ¬ drop0% Std.Iter.toListRev_uLift 4 := fun h => by
  have := h (it := yl); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_append idx 5 (family append): ¬T' from the assignment (yl.append em).toArray = #[]; yl.toArray = #[0]
theorem Iter.toArray_append.h5_neg (h₁ : (yl.append em).toArray = #[]) (h₂ : yl.toArray = #[0]) :
    ¬ drop0% Std.Iter.toArray_append 5 := fun h => by
  have := h (it₁ := yl) (it₂ := em); rw [h₁, h₂, EM.toArray] at this; opq_close

-- support for the independent row Std.Iter.toArray_append idx 6 (family append): ¬T' from the assignment (em.append yl).toArray = #[]; yl.toArray = #[0]
theorem Iter.toArray_append.h6_neg (h₁ : (em.append yl).toArray = #[]) (h₂ : yl.toArray = #[0]) :
    ¬ drop0% Std.Iter.toArray_append 6 := fun h => by
  have := h (it₁ := em) (it₂ := yl); rw [h₁, h₂, EM.toArray] at this; opq_close

-- support for the independent row Std.Iter.toArray_filterMap idx 5 (family coll): ¬T' from the assignment (yl.filterMap some).toArray = #[]; yl.toArray = #[0]
theorem Iter.toArray_filterMap.h5_neg (h₁ : (yl.filterMap some).toArray = #[]) (h₂ : yl.toArray = #[0]) :
    ¬ drop0% Std.Iter.toArray_filterMap 5 := fun h => by
  have := h (it := yl) (f := some); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_map idx 5 (family coll): ¬T' from the assignment (yl.map (· + 1)).toArray = #[]; yl.toArray = #[0]
theorem Iter.toArray_map.h5_neg (h₁ : (yl.map (· + 1)).toArray = #[]) (h₂ : yl.toArray = #[0]) :
    ¬ drop0% Std.Iter.toArray_map 5 := fun h => by
  have := h (it := yl) (f := (· + 1)); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_filter idx 4 (family coll): ¬T' from the assignment (yl.filter (fun _ => true)).toArray = #[]; yl.toArray = #[0]
theorem Iter.toArray_filter.h4_neg (h₁ : (yl.filter (fun _ => true)).toArray = #[]) (h₂ : yl.toArray = #[0]) :
    ¬ drop0% Std.Iter.toArray_filter 4 := fun h => by
  have := h (it := yl) (f := fun _ => true); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_uLift idx 4 (family coll): ¬T' from the assignment (yl.uLift : Std.Iter (ULift.{0} Nat)).toArray = #[]; yl.toArray = #[0]
theorem Iter.toArray_uLift.h4_neg (h₁ : (yl.uLift : Std.Iter (ULift.{0} Nat)).toArray = #[]) (h₂ : yl.toArray = #[0]) :
    ¬ drop0% Std.Iter.toArray_uLift 4 := fun h => by
  have := h (it := yl); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toList_mapWithPostcondition idx 8 (family coll): ¬T' from the assignment (yl.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT Id Nat))).toList = (pure [] : Id _); yl.toList = [0]
theorem Iter.toList_mapWithPostcondition.h8_neg (h₁ : (yl.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT Id Nat))).toList = (pure [] : Id _)) (h₂ : yl.toList = [0]) :
    ¬ drop0% Std.Iter.toList_mapWithPostcondition 8 := fun h => by
  have := h (it := yl) (m := Id) (f := (fun b => (pure b : Std.Iterators.PostconditionT Id Nat))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toList_mapM idx 10 (family coll): ¬T' from the assignment (yl.mapM (fun b => (pure b : Id Nat))).toList = (pure [] : Id _); yl.toList = [0]
theorem Iter.toList_mapM.h10_neg (h₁ : (yl.mapM (fun b => (pure b : Id Nat))).toList = (pure [] : Id _)) (h₂ : yl.toList = [0]) :
    ¬ drop0% Std.Iter.toList_mapM 10 := fun h => by
  have := h (it := yl) (m := Id) (f := (fun b => (pure b : Id Nat))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toList_filterMapWithPostcondition_filterMapWithPostcondition idx 14 (family comp): ¬T' from the assignment (Std.IterM.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT Id (Option Nat))) (yl.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT Id (Option Nat))))).toList = pure []; ∀ F : Nat → Std.Iterators.PostconditionT Id (Option Nat), (yl.filterMapWithPostcondition F).toList = pure [0]
theorem Iter.toList_filterMapWithPostcondition_filterMapWithPostcondition.h14_neg (h₁ : (Std.IterM.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT Id (Option Nat))) (yl.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT Id (Option Nat))))).toList = pure []) (h₂ : ∀ F : Nat → Std.Iterators.PostconditionT Id (Option Nat), (yl.filterMapWithPostcondition F).toList = pure [0]) :
    ¬ drop0% Std.Iter.toList_filterMapWithPostcondition_filterMapWithPostcondition 14 := fun h => by
  have := h (it := yl) (m := Id) (n := Id) (f := (fun b => (pure (some b) : Std.Iterators.PostconditionT Id (Option Nat)))) (g := (fun b => (pure (some b) : Std.Iterators.PostconditionT Id (Option Nat)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toList_mapWithPostcondition_mapWithPostcondition idx 14 (family comp): ¬T' from the assignment (Std.IterM.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT Id Nat)) (yl.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT Id Nat)))).toList = pure []; ∀ F : Nat → Std.Iterators.PostconditionT Id Nat, (yl.mapWithPostcondition F).toList = pure [0]
theorem Iter.toList_mapWithPostcondition_mapWithPostcondition.h14_neg (h₁ : (Std.IterM.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT Id Nat)) (yl.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT Id Nat)))).toList = pure []) (h₂ : ∀ F : Nat → Std.Iterators.PostconditionT Id Nat, (yl.mapWithPostcondition F).toList = pure [0]) :
    ¬ drop0% Std.Iter.toList_mapWithPostcondition_mapWithPostcondition 14 := fun h => by
  have := h (it := yl) (m := Id) (n := Id) (f := (fun b => (pure b : Std.Iterators.PostconditionT Id Nat))) (g := (fun b => (pure b : Std.Iterators.PostconditionT Id Nat))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_mapWithPostcondition idx 8 (family coll): ¬T' from the assignment (yl.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT Id Nat))).toArray = (pure #[] : Id _); yl.toArray = #[0]
theorem Iter.toArray_mapWithPostcondition.h8_neg (h₁ : (yl.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT Id Nat))).toArray = (pure #[] : Id _)) (h₂ : yl.toArray = #[0]) :
    ¬ drop0% Std.Iter.toArray_mapWithPostcondition 8 := fun h => by
  have := h (it := yl) (m := Id) (f := (fun b => (pure b : Std.Iterators.PostconditionT Id Nat))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_mapM idx 10 (family coll): ¬T' from the assignment (yl.mapM (fun b => (pure b : Id Nat))).toArray = (pure #[] : Id _); yl.toArray = #[0]
theorem Iter.toArray_mapM.h10_neg (h₁ : (yl.mapM (fun b => (pure b : Id Nat))).toArray = (pure #[] : Id _)) (h₂ : yl.toArray = #[0]) :
    ¬ drop0% Std.Iter.toArray_mapM 10 := fun h => by
  have := h (it := yl) (m := Id) (f := (fun b => (pure b : Id Nat))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_filterMapWithPostcondition_filterMapWithPostcondition idx 14 (family comp): ¬T' from the assignment (Std.IterM.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT Id (Option Nat))) (yl.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT Id (Option Nat))))).toArray = pure #[]; ∀ F : Nat → Std.Iterators.PostconditionT Id (Option Nat), (yl.filterMapWithPostcondition F).toArray = pure #[0]
theorem Iter.toArray_filterMapWithPostcondition_filterMapWithPostcondition.h14_neg (h₁ : (Std.IterM.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT Id (Option Nat))) (yl.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT Id (Option Nat))))).toArray = pure #[]) (h₂ : ∀ F : Nat → Std.Iterators.PostconditionT Id (Option Nat), (yl.filterMapWithPostcondition F).toArray = pure #[0]) :
    ¬ drop0% Std.Iter.toArray_filterMapWithPostcondition_filterMapWithPostcondition 14 := fun h => by
  have := h (it := yl) (m := Id) (n := Id) (f := (fun b => (pure (some b) : Std.Iterators.PostconditionT Id (Option Nat)))) (g := (fun b => (pure (some b) : Std.Iterators.PostconditionT Id (Option Nat)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_mapWithPostcondition_mapWithPostcondition idx 14 (family comp): ¬T' from the assignment (Std.IterM.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT Id Nat)) (yl.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT Id Nat)))).toArray = pure #[]; ∀ F : Nat → Std.Iterators.PostconditionT Id Nat, (yl.mapWithPostcondition F).toArray = pure #[0]
theorem Iter.toArray_mapWithPostcondition_mapWithPostcondition.h14_neg (h₁ : (Std.IterM.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT Id Nat)) (yl.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT Id Nat)))).toArray = pure #[]) (h₂ : ∀ F : Nat → Std.Iterators.PostconditionT Id Nat, (yl.mapWithPostcondition F).toArray = pure #[0]) :
    ¬ drop0% Std.Iter.toArray_mapWithPostcondition_mapWithPostcondition 14 := fun h => by
  have := h (it := yl) (m := Id) (n := Id) (f := (fun b => (pure b : Std.Iterators.PostconditionT Id Nat))) (g := (fun b => (pure b : Std.Iterators.PostconditionT Id Nat))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.unattach_toList_attachWith idx 6 (family coll): ¬T' from the assignment (yl.attachWith (fun _ => True) (fun _ _ => trivial)).toList = []; yl.toList = [0]
theorem Iter.unattach_toList_attachWith.h6_neg (h₁ : (yl.attachWith (fun _ => True) (fun _ _ => trivial)).toList = []) (h₂ : yl.toList = [0]) :
    ¬ drop0% Std.Iter.unattach_toList_attachWith 6 := fun h => by
  have := h (it := yl) (P := fun _ => True) (hP := fun _ _ => trivial); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.unattach_toListRev_attachWith idx 6 (family coll): ¬T' from the assignment (yl.attachWith (fun _ => True) (fun _ _ => trivial)).toListRev = []; yl.toListRev = [0]
theorem Iter.unattach_toListRev_attachWith.h6_neg (h₁ : (yl.attachWith (fun _ => True) (fun _ _ => trivial)).toListRev = []) (h₂ : yl.toListRev = [0]) :
    ¬ drop0% Std.Iter.unattach_toListRev_attachWith 6 := fun h => by
  have := h (it := yl) (P := fun _ => True) (hP := fun _ _ => trivial); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.unattach_toArray_attachWith idx 6 (family coll): ¬T' from the assignment (yl.attachWith (fun _ => True) (fun _ _ => trivial)).toListRev = []; yl.toListRev = [0]
theorem Iter.unattach_toArray_attachWith.h6_neg (h₁ : (yl.attachWith (fun _ => True) (fun _ _ => trivial)).toListRev = []) (h₂ : yl.toListRev = [0]) :
    ¬ drop0% Std.Iter.unattach_toArray_attachWith 6 := fun h => by
  have := h (it := yl) (P := fun _ => True) (hP := fun _ _ => trivial); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_append idx 8 (family append): ¬T' from the assignment (ytm.append etm).toList = (pure [] : TM _); ytm.toList = (pure [0] : TM _)
theorem IterM.toList_append.h8_neg (h₁ : (ytm.append etm).toList = (pure [] : TM _)) (h₂ : ytm.toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_append 8 := fun h => by
  have := h (m := TM) (it₁ := ytm) (it₂ := etm); rw [h₁, h₂, ETM.toList] at this; opq_close

-- support for the independent row Std.IterM.toList_append idx 9 (family append): ¬T' from the assignment (etm.append ytm).toList = (pure [] : TM _); ytm.toList = (pure [0] : TM _)
theorem IterM.toList_append.h9_neg (h₁ : (etm.append ytm).toList = (pure [] : TM _)) (h₂ : ytm.toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_append 9 := fun h => by
  have := h (m := TM) (it₁ := etm) (it₂ := ytm); rw [h₁, h₂, ETM.toList] at this; opq_close

-- support for the independent row Std.IterM.toList_filterMap idx 7 (family coll): ¬T' from the assignment (ytm.filterMap some).toList = (pure [] : TM _); ytm.toList = (pure [0] : TM _)
theorem IterM.toList_filterMap.h7_neg (h₁ : (ytm.filterMap some).toList = (pure [] : TM _)) (h₂ : ytm.toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_filterMap 7 := fun h => by
  have := h (m := TM) (f := some) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_map idx 7 (family coll): ¬T' from the assignment (ytm.map (· + 1)).toList = (pure [] : TM _); ytm.toList = (pure [0] : TM _)
theorem IterM.toList_map.h7_neg (h₁ : (ytm.map (· + 1)).toList = (pure [] : TM _)) (h₂ : ytm.toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_map 7 := fun h => by
  have := h (m := TM) (f := (· + 1)) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_filter idx 6 (family coll): ¬T' from the assignment (ytm.filter (fun _ => true)).toList = (pure [] : TM _); ytm.toList = (pure [0] : TM _)
theorem IterM.toList_filter.h6_neg (h₁ : (ytm.filter (fun _ => true)).toList = (pure [] : TM _)) (h₂ : ytm.toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_filter 6 := fun h => by
  have := h (m := TM) (f := fun _ => true) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_filterMapWithPostcondition idx 7 (family coll): ¬T' from the assignment (ylm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).toList = (pure [] : TM _); ylm.toList = (pure [0] : Id _)
theorem IterM.toList_filterMapWithPostcondition.h7_neg (h₁ : (ylm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).toList = (pure [] : TM _)) (h₂ : ylm.toList = (pure [0] : Id _)) :
    ¬ drop0% Std.IterM.toList_filterMapWithPostcondition 7 := fun h => by
  have := h (m := TM) (f := (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_mapWithPostcondition idx 7 (family coll): ¬T' from the assignment (ylm.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).toList = (pure [] : TM _); ylm.toList = (pure [0] : Id _)
theorem IterM.toList_mapWithPostcondition.h7_neg (h₁ : (ylm.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).toList = (pure [] : TM _)) (h₂ : ylm.toList = (pure [0] : Id _)) :
    ¬ drop0% Std.IterM.toList_mapWithPostcondition 7 := fun h => by
  have := h (m := TM) (f := (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_filterMapM idx 9 (family coll): ¬T' from the assignment (ylm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toList = (pure [] : TM _); ylm.toList = (pure [0] : Id _)
theorem IterM.toList_filterMapM.h9_neg (h₁ : (ylm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toList = (pure [] : TM _)) (h₂ : ylm.toList = (pure [0] : Id _)) :
    ¬ drop0% Std.IterM.toList_filterMapM 9 := fun h => by
  have := h (m := TM) (f := (fun b => (pure (some b) : TM (Option Nat)))) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_mapM idx 9 (family coll): ¬T' from the assignment (ylm.mapM (fun b => (pure (b + 1) : TM Nat))).toList = (pure [] : TM _); ylm.toList = (pure [0] : Id _)
theorem IterM.toList_mapM.h9_neg (h₁ : (ylm.mapM (fun b => (pure (b + 1) : TM Nat))).toList = (pure [] : TM _)) (h₂ : ylm.toList = (pure [0] : Id _)) :
    ¬ drop0% Std.IterM.toList_mapM 9 := fun h => by
  have := h (m := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_mapM_eq_toList_filterMapM idx 14 (family comp): ¬T' from the assignment (ytm.mapM (fun b => (pure (b + 1) : TM Nat))).toList = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)
theorem IterM.toList_mapM_eq_toList_filterMapM.h14_neg (h₁ : (ytm.mapM (fun b => (pure (b + 1) : TM Nat))).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_mapM_eq_toList_filterMapM 14 := fun h => by
  have := h (m := TM) (n := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_map_eq_toList_mapM idx 9 (family comp): ¬T' from the assignment (ytm.map (· + 1)).toList = (pure [] : TM _); ∀ F : Nat → TM Nat, (ytm.mapM F).toList = (pure [0] : TM _)
theorem IterM.toList_map_eq_toList_mapM.h9_neg (h₁ : (ytm.map (· + 1)).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM Nat, (ytm.mapM F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_map_eq_toList_mapM 9 := fun h => by
  have := h (m := TM) (f := (· + 1)) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_map_eq_toList_filterMapM idx 9 (family comp): ¬T' from the assignment (ytm.map (· + 1)).toList = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)
theorem IterM.toList_map_eq_toList_filterMapM.h9_neg (h₁ : (ytm.map (· + 1)).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_map_eq_toList_filterMapM 9 := fun h => by
  have := h (m := TM) (f := (· + 1)) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition idx 18 (family comp): ¬T' from the assignment ((ytm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).toList = (pure [] : TM _); ∀ F : Nat → Std.Iterators.PostconditionT TM (Option Nat), (ytm.filterMapWithPostcondition F).toList = (pure [0] : TM _)
theorem IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition.h18_neg (h₁ : ((ytm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → Std.Iterators.PostconditionT TM (Option Nat), (ytm.filterMapWithPostcondition F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition 18 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))) (g := (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_mapWithPostcondition_mapWithPostcondition idx 18 (family comp): ¬T' from the assignment ((ytm.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).toList = (pure [] : TM _); ∀ F : Nat → Std.Iterators.PostconditionT TM Nat, (ytm.mapWithPostcondition F).toList = (pure [0] : TM _)
theorem IterM.toList_mapWithPostcondition_mapWithPostcondition.h18_neg (h₁ : ((ytm.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → Std.Iterators.PostconditionT TM Nat, (ytm.mapWithPostcondition F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_mapWithPostcondition_mapWithPostcondition 18 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))) (g := (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_filterMapM_filterMapWithPostcondition idx 22 (family comp): ¬T' from the assignment ((ytm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toList = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)
theorem IterM.toList_filterMapM_filterMapWithPostcondition.h22_neg (h₁ : ((ytm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_filterMapM_filterMapWithPostcondition 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))) (g := (fun b => (pure (some b) : TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_filterMapM_filterMapM idx 22 (family comp): ¬T' from the assignment ((ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toList = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)
theorem IterM.toList_filterMapM_filterMapM.h22_neg (h₁ : ((ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_filterMapM_filterMapM 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (some b) : TM (Option Nat)))) (g := (fun b => (pure (some b) : TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_filterMapM_mapM idx 22 (family comp): ¬T' from the assignment ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toList = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)
theorem IterM.toList_filterMapM_mapM.h22_neg (h₁ : ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_filterMapM_mapM 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (g := (fun b => (pure (some b) : TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_filterMapM_map idx 15 (family comp): ¬T' from the assignment ((ytm.map (· + 1)).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toList = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)
theorem IterM.toList_filterMapM_map.h15_neg (h₁ : ((ytm.map (· + 1)).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_filterMapM_map 15 := fun h => by
  have := h (m := TM) (n := TM) (f := (· + 1)) (g := (fun b => (pure (some b) : TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_mapM_filterMapM idx 22 (family comp): ¬T' from the assignment ((ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).mapM (fun b => (pure (b + 1) : TM Nat))).toList = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)
theorem IterM.toList_mapM_filterMapM.h22_neg (h₁ : ((ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).mapM (fun b => (pure (b + 1) : TM Nat))).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_mapM_filterMapM 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (some b) : TM (Option Nat)))) (g := (fun b => (pure (b + 1) : TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_mapM_mapM idx 22 (family comp): ¬T' from the assignment ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).mapM (fun b => (pure (b + 1) : TM Nat))).toList = (pure [] : TM _); ∀ F : Nat → TM Nat, (ytm.mapM F).toList = (pure [0] : TM _)
theorem IterM.toList_mapM_mapM.h22_neg (h₁ : ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).mapM (fun b => (pure (b + 1) : TM Nat))).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM Nat, (ytm.mapM F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_mapM_mapM 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (g := (fun b => (pure (b + 1) : TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_mapM_map idx 15 (family comp): ¬T' from the assignment ((ytm.map (· + 1)).mapM (fun b => (pure (b + 1) : TM Nat))).toList = (pure [] : TM _); ∀ F : Nat → TM Nat, (ytm.mapM F).toList = (pure [0] : TM _)
theorem IterM.toList_mapM_map.h15_neg (h₁ : ((ytm.map (· + 1)).mapM (fun b => (pure (b + 1) : TM Nat))).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM Nat, (ytm.mapM F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_mapM_map 15 := fun h => by
  have := h (m := TM) (n := TM) (f := (· + 1)) (g := (fun b => (pure (b + 1) : TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_map_mapM idx 15 (family comp): ¬T' from the assignment ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).map (· + 1)).toList = (pure [] : TM _); ∀ F : Nat → TM Nat, (ytm.mapM F).toList = (pure [0] : TM _)
theorem IterM.toList_map_mapM.h15_neg (h₁ : ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).map (· + 1)).toList = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM Nat, (ytm.mapM F).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_map_mapM 15 := fun h => by
  have := h (m := TM) (n := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (g := (· + 1)) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_append idx 8 (family append): ¬T' from the assignment (ytm.append etm).toListRev = (pure [] : TM _); ytm.toListRev = (pure [0] : TM _)
theorem IterM.toListRev_append.h8_neg (h₁ : (ytm.append etm).toListRev = (pure [] : TM _)) (h₂ : ytm.toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_append 8 := fun h => by
  have := h (m := TM) (it₁ := ytm) (it₂ := etm); rw [h₁, h₂, ETM.toListRev] at this; opq_close

-- support for the independent row Std.IterM.toListRev_append idx 9 (family append): ¬T' from the assignment (etm.append ytm).toListRev = (pure [] : TM _); ytm.toListRev = (pure [0] : TM _)
theorem IterM.toListRev_append.h9_neg (h₁ : (etm.append ytm).toListRev = (pure [] : TM _)) (h₂ : ytm.toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_append 9 := fun h => by
  have := h (m := TM) (it₁ := etm) (it₂ := ytm); rw [h₁, h₂, ETM.toListRev] at this; opq_close

-- support for the independent row Std.IterM.toListRev_filterMap idx 7 (family coll): ¬T' from the assignment (ytm.filterMap some).toListRev = (pure [] : TM _); ytm.toListRev = (pure [0] : TM _)
theorem IterM.toListRev_filterMap.h7_neg (h₁ : (ytm.filterMap some).toListRev = (pure [] : TM _)) (h₂ : ytm.toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_filterMap 7 := fun h => by
  have := h (m := TM) (f := some) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_map idx 7 (family coll): ¬T' from the assignment (ytm.map (· + 1)).toListRev = (pure [] : TM _); ytm.toListRev = (pure [0] : TM _)
theorem IterM.toListRev_map.h7_neg (h₁ : (ytm.map (· + 1)).toListRev = (pure [] : TM _)) (h₂ : ytm.toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_map 7 := fun h => by
  have := h (m := TM) (f := (· + 1)) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_filter idx 6 (family coll): ¬T' from the assignment (ytm.filter (fun _ => true)).toListRev = (pure [] : TM _); ytm.toListRev = (pure [0] : TM _)
theorem IterM.toListRev_filter.h6_neg (h₁ : (ytm.filter (fun _ => true)).toListRev = (pure [] : TM _)) (h₂ : ytm.toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_filter 6 := fun h => by
  have := h (m := TM) (f := fun _ => true) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_filterMapWithPostcondition idx 7 (family coll): ¬T' from the assignment (ylm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).toListRev = (pure [] : TM _); ylm.toList = (pure [0] : Id _)
theorem IterM.toListRev_filterMapWithPostcondition.h7_neg (h₁ : (ylm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).toListRev = (pure [] : TM _)) (h₂ : ylm.toList = (pure [0] : Id _)) :
    ¬ drop0% Std.IterM.toListRev_filterMapWithPostcondition 7 := fun h => by
  have := h (m := TM) (f := (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_mapWithPostcondition idx 7 (family coll): ¬T' from the assignment (ylm.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).toListRev = (pure [] : TM _); ylm.toList = (pure [0] : Id _)
theorem IterM.toListRev_mapWithPostcondition.h7_neg (h₁ : (ylm.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).toListRev = (pure [] : TM _)) (h₂ : ylm.toList = (pure [0] : Id _)) :
    ¬ drop0% Std.IterM.toListRev_mapWithPostcondition 7 := fun h => by
  have := h (m := TM) (f := (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_filterMapM idx 9 (family coll): ¬T' from the assignment (ylm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toListRev = (pure [] : TM _); ylm.toList = (pure [0] : Id _)
theorem IterM.toListRev_filterMapM.h9_neg (h₁ : (ylm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toListRev = (pure [] : TM _)) (h₂ : ylm.toList = (pure [0] : Id _)) :
    ¬ drop0% Std.IterM.toListRev_filterMapM 9 := fun h => by
  have := h (m := TM) (f := (fun b => (pure (some b) : TM (Option Nat)))) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_mapM idx 9 (family coll): ¬T' from the assignment (ylm.mapM (fun b => (pure (b + 1) : TM Nat))).toListRev = (pure [] : TM _); ylm.toList = (pure [0] : Id _)
theorem IterM.toListRev_mapM.h9_neg (h₁ : (ylm.mapM (fun b => (pure (b + 1) : TM Nat))).toListRev = (pure [] : TM _)) (h₂ : ylm.toList = (pure [0] : Id _)) :
    ¬ drop0% Std.IterM.toListRev_mapM 9 := fun h => by
  have := h (m := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_mapM_eq_toListRev_filterMapM idx 14 (family comp): ¬T' from the assignment (ytm.mapM (fun b => (pure (b + 1) : TM Nat))).toListRev = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_mapM_eq_toListRev_filterMapM.h14_neg (h₁ : (ytm.mapM (fun b => (pure (b + 1) : TM Nat))).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_mapM_eq_toListRev_filterMapM 14 := fun h => by
  have := h (m := TM) (n := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_map_eq_toListRev_mapM idx 9 (family comp): ¬T' from the assignment (ytm.map (· + 1)).toListRev = (pure [] : TM _); ∀ F : Nat → TM Nat, (ytm.mapM F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_map_eq_toListRev_mapM.h9_neg (h₁ : (ytm.map (· + 1)).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM Nat, (ytm.mapM F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_map_eq_toListRev_mapM 9 := fun h => by
  have := h (m := TM) (f := (· + 1)) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_map_eq_toListRev_filterMapM idx 9 (family comp): ¬T' from the assignment (ytm.map (· + 1)).toListRev = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_map_eq_toListRev_filterMapM.h9_neg (h₁ : (ytm.map (· + 1)).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_map_eq_toListRev_filterMapM 9 := fun h => by
  have := h (m := TM) (f := (· + 1)) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_filterMapWithPostcondition_filterMapWithPostcondition idx 18 (family comp): ¬T' from the assignment ((ytm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).toListRev = (pure [] : TM _); ∀ F : Nat → Std.Iterators.PostconditionT TM (Option Nat), (ytm.filterMapWithPostcondition F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_filterMapWithPostcondition_filterMapWithPostcondition.h18_neg (h₁ : ((ytm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → Std.Iterators.PostconditionT TM (Option Nat), (ytm.filterMapWithPostcondition F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_filterMapWithPostcondition_filterMapWithPostcondition 18 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))) (g := (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_mapWithPostcondition_mapWithPostcondition idx 18 (family comp): ¬T' from the assignment ((ytm.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).toListRev = (pure [] : TM _); ∀ F : Nat → Std.Iterators.PostconditionT TM Nat, (ytm.mapWithPostcondition F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_mapWithPostcondition_mapWithPostcondition.h18_neg (h₁ : ((ytm.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → Std.Iterators.PostconditionT TM Nat, (ytm.mapWithPostcondition F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_mapWithPostcondition_mapWithPostcondition 18 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))) (g := (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_filterMapM_filterMapWithPostcondition idx 22 (family comp): ¬T' from the assignment ((ytm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toListRev = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_filterMapM_filterMapWithPostcondition.h22_neg (h₁ : ((ytm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_filterMapM_filterMapWithPostcondition 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))) (g := (fun b => (pure (some b) : TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_filterMapM_filterMapM idx 22 (family comp): ¬T' from the assignment ((ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toListRev = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_filterMapM_filterMapM.h22_neg (h₁ : ((ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_filterMapM_filterMapM 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (some b) : TM (Option Nat)))) (g := (fun b => (pure (some b) : TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_filterMapM_mapM idx 22 (family comp): ¬T' from the assignment ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toListRev = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_filterMapM_mapM.h22_neg (h₁ : ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_filterMapM_mapM 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (g := (fun b => (pure (some b) : TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_filterMapM_map idx 15 (family comp): ¬T' from the assignment ((ytm.map (· + 1)).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toListRev = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_filterMapM_map.h15_neg (h₁ : ((ytm.map (· + 1)).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_filterMapM_map 15 := fun h => by
  have := h (m := TM) (n := TM) (f := (· + 1)) (g := (fun b => (pure (some b) : TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_mapM_filterMapM idx 22 (family comp): ¬T' from the assignment ((ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).mapM (fun b => (pure (b + 1) : TM Nat))).toListRev = (pure [] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_mapM_filterMapM.h22_neg (h₁ : ((ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).mapM (fun b => (pure (b + 1) : TM Nat))).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_mapM_filterMapM 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (some b) : TM (Option Nat)))) (g := (fun b => (pure (b + 1) : TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_mapM_mapM idx 22 (family comp): ¬T' from the assignment ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).mapM (fun b => (pure (b + 1) : TM Nat))).toListRev = (pure [] : TM _); ∀ F : Nat → TM Nat, (ytm.mapM F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_mapM_mapM.h22_neg (h₁ : ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).mapM (fun b => (pure (b + 1) : TM Nat))).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM Nat, (ytm.mapM F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_mapM_mapM 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (g := (fun b => (pure (b + 1) : TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_mapM_map idx 15 (family comp): ¬T' from the assignment ((ytm.map (· + 1)).mapM (fun b => (pure (b + 1) : TM Nat))).toListRev = (pure [] : TM _); ∀ F : Nat → TM Nat, (ytm.mapM F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_mapM_map.h15_neg (h₁ : ((ytm.map (· + 1)).mapM (fun b => (pure (b + 1) : TM Nat))).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM Nat, (ytm.mapM F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_mapM_map 15 := fun h => by
  have := h (m := TM) (n := TM) (f := (· + 1)) (g := (fun b => (pure (b + 1) : TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_map_mapM idx 15 (family comp): ¬T' from the assignment ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).map (· + 1)).toListRev = (pure [] : TM _); ∀ F : Nat → TM Nat, (ytm.mapM F).toListRev = (pure [0] : TM _)
theorem IterM.toListRev_map_mapM.h15_neg (h₁ : ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).map (· + 1)).toListRev = (pure [] : TM _)) (h₂ : ∀ F : Nat → TM Nat, (ytm.mapM F).toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_map_mapM 15 := fun h => by
  have := h (m := TM) (n := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (g := (· + 1)) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_append idx 8 (family append): ¬T' from the assignment (ytm.append etm).toArray = (pure #[] : TM _); ytm.toArray = (pure #[0] : TM _)
theorem IterM.toArray_append.h8_neg (h₁ : (ytm.append etm).toArray = (pure #[] : TM _)) (h₂ : ytm.toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_append 8 := fun h => by
  have := h (m := TM) (it₁ := ytm) (it₂ := etm); rw [h₁, h₂, ETM.toArray] at this; opq_close

-- support for the independent row Std.IterM.toArray_append idx 9 (family append): ¬T' from the assignment (etm.append ytm).toArray = (pure #[] : TM _); ytm.toArray = (pure #[0] : TM _)
theorem IterM.toArray_append.h9_neg (h₁ : (etm.append ytm).toArray = (pure #[] : TM _)) (h₂ : ytm.toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_append 9 := fun h => by
  have := h (m := TM) (it₁ := etm) (it₂ := ytm); rw [h₁, h₂, ETM.toArray] at this; opq_close

-- support for the independent row Std.IterM.toArray_filterMap idx 7 (family coll): ¬T' from the assignment (ytm.filterMap some).toArray = (pure #[] : TM _); ytm.toArray = (pure #[0] : TM _)
theorem IterM.toArray_filterMap.h7_neg (h₁ : (ytm.filterMap some).toArray = (pure #[] : TM _)) (h₂ : ytm.toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_filterMap 7 := fun h => by
  have := h (m := TM) (f := some) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_map idx 7 (family coll): ¬T' from the assignment (ytm.map (· + 1)).toArray = (pure #[] : TM _); ytm.toArray = (pure #[0] : TM _)
theorem IterM.toArray_map.h7_neg (h₁ : (ytm.map (· + 1)).toArray = (pure #[] : TM _)) (h₂ : ytm.toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_map 7 := fun h => by
  have := h (m := TM) (f := (· + 1)) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_filter idx 6 (family coll): ¬T' from the assignment (ytm.filter (fun _ => true)).toArray = (pure #[] : TM _); ytm.toArray = (pure #[0] : TM _)
theorem IterM.toArray_filter.h6_neg (h₁ : (ytm.filter (fun _ => true)).toArray = (pure #[] : TM _)) (h₂ : ytm.toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_filter 6 := fun h => by
  have := h (m := TM) (f := fun _ => true) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_filterMapWithPostcondition idx 7 (family coll): ¬T' from the assignment (ylm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).toArray = (pure #[] : TM _); ylm.toArray = (pure #[0] : Id _)
theorem IterM.toArray_filterMapWithPostcondition.h7_neg (h₁ : (ylm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).toArray = (pure #[] : TM _)) (h₂ : ylm.toArray = (pure #[0] : Id _)) :
    ¬ drop0% Std.IterM.toArray_filterMapWithPostcondition 7 := fun h => by
  have := h (m := TM) (f := (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_mapWithPostcondition idx 7 (family coll): ¬T' from the assignment (ylm.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).toArray = (pure #[] : TM _); ylm.toArray = (pure #[0] : Id _)
theorem IterM.toArray_mapWithPostcondition.h7_neg (h₁ : (ylm.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).toArray = (pure #[] : TM _)) (h₂ : ylm.toArray = (pure #[0] : Id _)) :
    ¬ drop0% Std.IterM.toArray_mapWithPostcondition 7 := fun h => by
  have := h (m := TM) (f := (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_filterMapM idx 9 (family coll): ¬T' from the assignment (ylm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toArray = (pure #[] : TM _); ylm.toArray = (pure #[0] : Id _)
theorem IterM.toArray_filterMapM.h9_neg (h₁ : (ylm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toArray = (pure #[] : TM _)) (h₂ : ylm.toArray = (pure #[0] : Id _)) :
    ¬ drop0% Std.IterM.toArray_filterMapM 9 := fun h => by
  have := h (m := TM) (f := (fun b => (pure (some b) : TM (Option Nat)))) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_mapM idx 9 (family coll): ¬T' from the assignment (ylm.mapM (fun b => (pure (b + 1) : TM Nat))).toArray = (pure #[] : TM _); ylm.toArray = (pure #[0] : Id _)
theorem IterM.toArray_mapM.h9_neg (h₁ : (ylm.mapM (fun b => (pure (b + 1) : TM Nat))).toArray = (pure #[] : TM _)) (h₂ : ylm.toArray = (pure #[0] : Id _)) :
    ¬ drop0% Std.IterM.toArray_mapM 9 := fun h => by
  have := h (m := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_mapM_eq_toArray_filterMapM idx 14 (family comp): ¬T' from the assignment (ytm.mapM (fun b => (pure (b + 1) : TM Nat))).toArray = (pure #[] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_mapM_eq_toArray_filterMapM.h14_neg (h₁ : (ytm.mapM (fun b => (pure (b + 1) : TM Nat))).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_mapM_eq_toArray_filterMapM 14 := fun h => by
  have := h (m := TM) (n := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_map_eq_toArray_mapM idx 9 (family comp): ¬T' from the assignment (ytm.map (· + 1)).toArray = (pure #[] : TM _); ∀ F : Nat → TM Nat, (ytm.mapM F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_map_eq_toArray_mapM.h9_neg (h₁ : (ytm.map (· + 1)).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → TM Nat, (ytm.mapM F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_map_eq_toArray_mapM 9 := fun h => by
  have := h (m := TM) (f := (· + 1)) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_map_eq_toArray_filterMapM idx 9 (family comp): ¬T' from the assignment (ytm.map (· + 1)).toArray = (pure #[] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_map_eq_toArray_filterMapM.h9_neg (h₁ : (ytm.map (· + 1)).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_map_eq_toArray_filterMapM 9 := fun h => by
  have := h (m := TM) (f := (· + 1)) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_filterMapWithPostcondition_filterMapWithPostcondition idx 18 (family comp): ¬T' from the assignment ((ytm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).toArray = (pure #[] : TM _); ∀ F : Nat → Std.Iterators.PostconditionT TM (Option Nat), (ytm.filterMapWithPostcondition F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_filterMapWithPostcondition_filterMapWithPostcondition.h18_neg (h₁ : ((ytm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → Std.Iterators.PostconditionT TM (Option Nat), (ytm.filterMapWithPostcondition F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_filterMapWithPostcondition_filterMapWithPostcondition 18 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))) (g := (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_mapWithPostcondition_mapWithPostcondition idx 18 (family comp): ¬T' from the assignment ((ytm.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).toArray = (pure #[] : TM _); ∀ F : Nat → Std.Iterators.PostconditionT TM Nat, (ytm.mapWithPostcondition F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_mapWithPostcondition_mapWithPostcondition.h18_neg (h₁ : ((ytm.mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).mapWithPostcondition (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → Std.Iterators.PostconditionT TM Nat, (ytm.mapWithPostcondition F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_mapWithPostcondition_mapWithPostcondition 18 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))) (g := (fun b => (pure b : Std.Iterators.PostconditionT TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_filterMapM_filterMapWithPostcondition idx 22 (family comp): ¬T' from the assignment ((ytm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toArray = (pure #[] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_filterMapM_filterMapWithPostcondition.h22_neg (h₁ : ((ytm.filterMapWithPostcondition (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_filterMapM_filterMapWithPostcondition 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (some b) : Std.Iterators.PostconditionT TM (Option Nat)))) (g := (fun b => (pure (some b) : TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_filterMapM_filterMapM idx 22 (family comp): ¬T' from the assignment ((ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toArray = (pure #[] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_filterMapM_filterMapM.h22_neg (h₁ : ((ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_filterMapM_filterMapM 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (some b) : TM (Option Nat)))) (g := (fun b => (pure (some b) : TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_filterMapM_mapM idx 22 (family comp): ¬T' from the assignment ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toArray = (pure #[] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_filterMapM_mapM.h22_neg (h₁ : ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_filterMapM_mapM 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (g := (fun b => (pure (some b) : TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_filterMapM_map idx 15 (family comp): ¬T' from the assignment ((ytm.map (· + 1)).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toArray = (pure #[] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_filterMapM_map.h15_neg (h₁ : ((ytm.map (· + 1)).filterMapM (fun b => (pure (some b) : TM (Option Nat)))).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_filterMapM_map 15 := fun h => by
  have := h (m := TM) (n := TM) (f := (· + 1)) (g := (fun b => (pure (some b) : TM (Option Nat)))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_mapM_filterMapM idx 22 (family comp): ¬T' from the assignment ((ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).mapM (fun b => (pure (b + 1) : TM Nat))).toArray = (pure #[] : TM _); ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_mapM_filterMapM.h22_neg (h₁ : ((ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))).mapM (fun b => (pure (b + 1) : TM Nat))).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → TM (Option Nat), (ytm.filterMapM F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_mapM_filterMapM 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (some b) : TM (Option Nat)))) (g := (fun b => (pure (b + 1) : TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_mapM_mapM idx 22 (family comp): ¬T' from the assignment ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).mapM (fun b => (pure (b + 1) : TM Nat))).toArray = (pure #[] : TM _); ∀ F : Nat → TM Nat, (ytm.mapM F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_mapM_mapM.h22_neg (h₁ : ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).mapM (fun b => (pure (b + 1) : TM Nat))).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → TM Nat, (ytm.mapM F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_mapM_mapM 22 := fun h => by
  have := h (m := TM) (n := TM) (o := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (g := (fun b => (pure (b + 1) : TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_mapM_map idx 15 (family comp): ¬T' from the assignment ((ytm.map (· + 1)).mapM (fun b => (pure (b + 1) : TM Nat))).toArray = (pure #[] : TM _); ∀ F : Nat → TM Nat, (ytm.mapM F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_mapM_map.h15_neg (h₁ : ((ytm.map (· + 1)).mapM (fun b => (pure (b + 1) : TM Nat))).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → TM Nat, (ytm.mapM F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_mapM_map 15 := fun h => by
  have := h (m := TM) (n := TM) (f := (· + 1)) (g := (fun b => (pure (b + 1) : TM Nat))) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_map_mapM idx 15 (family comp): ¬T' from the assignment ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).map (· + 1)).toArray = (pure #[] : TM _); ∀ F : Nat → TM Nat, (ytm.mapM F).toArray = (pure #[0] : TM _)
theorem IterM.toArray_map_mapM.h15_neg (h₁ : ((ytm.mapM (fun b => (pure (b + 1) : TM Nat))).map (· + 1)).toArray = (pure #[] : TM _)) (h₂ : ∀ F : Nat → TM Nat, (ytm.mapM F).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.toArray_map_mapM 15 := fun h => by
  have := h (m := TM) (n := TM) (f := (fun b => (pure (b + 1) : TM Nat))) (g := (· + 1)) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.map_unattach_toList_attachWith idx 8 (family coll): ¬T' from the assignment (ytm.attachWith (fun _ => True) (fun _ _ => trivial)).toList = (pure [] : TM _); ytm.toList = (pure [0] : TM _)
theorem IterM.map_unattach_toList_attachWith.h8_neg (h₁ : (ytm.attachWith (fun _ => True) (fun _ _ => trivial)).toList = (pure [] : TM _)) (h₂ : ytm.toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.map_unattach_toList_attachWith 8 := fun h => by
  have := h (m := TM) (it := ytm) (P := fun _ => True) (hP := fun _ _ => trivial); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.map_unattach_toListRev_attachWith idx 10 (family coll): ¬T' from the assignment (ytm.attachWith (fun _ => True) (fun _ _ => trivial)).toListRev = (pure [] : TM _); ytm.toListRev = (pure [0] : TM _)
theorem IterM.map_unattach_toListRev_attachWith.h10_neg (h₁ : (ytm.attachWith (fun _ => True) (fun _ _ => trivial)).toListRev = (pure [] : TM _)) (h₂ : ytm.toListRev = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.map_unattach_toListRev_attachWith 10 := fun h => by
  have := h (m := TM) (it := ytm) (P := fun _ => True) (hP := fun _ _ => trivial) (n := Id); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.map_unattach_toArray_attachWith idx 10 (family coll): ¬T' from the assignment (ytm.attachWith (fun _ => True) (fun _ _ => trivial)).toArray = (pure #[] : TM _); ytm.toArray = (pure #[0] : TM _)
theorem IterM.map_unattach_toArray_attachWith.h10_neg (h₁ : (ytm.attachWith (fun _ => True) (fun _ _ => trivial)).toArray = (pure #[] : TM _)) (h₂ : ytm.toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.IterM.map_unattach_toArray_attachWith 10 := fun h => by
  have := h (m := TM) (it := ytm) (P := fun _ => True) (hP := fun _ _ => trivial) (n := Id); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.InternalConsumers.toList_filterMap idx 7 (family coll): ¬T' from the assignment (ytm.filterMap some).toList = (pure [] : TM _); ytm.toList = (pure [0] : TM _)
theorem IterM.InternalConsumers.toList_filterMap.h7_neg (h₁ : (ytm.filterMap some).toList = (pure [] : TM _)) (h₂ : ytm.toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.InternalConsumers.toList_filterMap 7 := fun h => by
  have := h (m := TM) (f := some) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_appendSnd idx 8 (family appendSnd): ¬T' from the assignment (Std.IterM.Intermediate.appendSnd YL etm).toList = (pure [0] : TM _)
theorem IterM.toList_appendSnd.h8_neg (h₁ : (Std.IterM.Intermediate.appendSnd YL etm).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_appendSnd 8 := fun h => by
  have := h (m := TM) (α₁ := YL) (it₂ := etm); rw [h₁, ETM.toList] at this; opq_close

-- support for the independent row Std.IterM.toList_appendSnd idx 9 (family appendSnd): ¬T' from the assignment (Std.IterM.Intermediate.appendSnd EM ytm).toList = (pure [0] : TM _); ytm.toList = (pure [] : TM _)
theorem IterM.toList_appendSnd.h9_neg (h₁ : (Std.IterM.Intermediate.appendSnd EM ytm).toList = (pure [0] : TM _)) (h₂ : ytm.toList = (pure [] : TM _)) :
    ¬ drop0% Std.IterM.toList_appendSnd 9 := fun h => by
  have := h (m := TM) (α₁ := EM) (it₂ := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.reverse_toListRev idx 6 (family rev): ¬T' from the assignment ytm.toListRev = (pure [0, 1] : TM _); ytm.toList = (pure [0, 1] : TM _)
theorem IterM.reverse_toListRev.h6_neg (h₁ : ytm.toListRev = (pure [0, 1] : TM _)) (h₂ : ytm.toList = (pure [0, 1] : TM _)) :
    ¬ drop0% Std.IterM.reverse_toListRev 6 := fun h => by
  have := h (m := TM) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_eq idx 6 (family rev): ¬T' from the assignment ytm.toListRev = (pure [0, 1] : TM _); ytm.toList = (pure [0, 1] : TM _)
theorem IterM.toListRev_eq.h6_neg (h₁ : ytm.toListRev = (pure [0, 1] : TM _)) (h₂ : ytm.toList = (pure [0, 1] : TM _)) :
    ¬ drop0% Std.IterM.toListRev_eq 6 := fun h => by
  have := h (m := TM) (it := ytm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.reverse_toListRev idx 3 (family rev): ¬T' from the assignment yl.toListRev = [0, 1]; yl.toList = [0, 1]
theorem Iter.reverse_toListRev.h3_neg (h₁ : yl.toListRev = [0, 1]) (h₂ : yl.toList = [0, 1]) :
    ¬ drop0% Std.Iter.reverse_toListRev 3 := fun h => by
  have := h (it := yl); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toListRev_eq idx 3 (family rev): ¬T' from the assignment yl.toListRev = [0, 1]; yl.toList = [0, 1]
theorem Iter.toListRev_eq.h3_neg (h₁ : yl.toListRev = [0, 1]) (h₂ : yl.toList = [0, 1]) :
    ¬ drop0% Std.Iter.toListRev_eq 3 := fun h => by
  have := h (it := yl); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_take_zero idx 6 (family take0): ¬T' from the assignment (lptm.take 0).toList = (pure [0] : TM _)
theorem IterM.toList_take_zero.h6_neg (h₁ : (lptm.take 0).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.IterM.toList_take_zero 6 := fun h => by
  have := h (m := TM) (it := lptm); rw [h₁] at this; opq_close

-- support for the independent row Std.Iter.toList_take_zero idx 3 (family take0): ¬T' from the assignment (lp.take 0).toList = [0]
theorem Iter.toList_take_zero.h3_neg (h₁ : (lp.take 0).toList = [0]) :
    ¬ drop0% Std.Iter.toList_take_zero 3 := fun h => by
  have := h (it := lp); rw [h₁] at this; opq_close

-- support for the independent row Std.Iter.toList_eq_of_atIdxSlow?_eq idx 4 (family atidx): ¬T' from the assignment yd0.toList = [0]
theorem Iter.toList_eq_of_atIdxSlow?_eq.h4_neg (h₁ : yd0.toList = [0]) :
    ¬ drop0% Std.Iter.toList_eq_of_atIdxSlow?_eq 4 := fun h => by
  have := h (it₁ := yd0) (it₂ := em) (fun k => by rw [YD.atIdx, EM.atIdx]); rw [h₁, EM.toList] at this; opq_close

-- support for the independent row Std.Iter.toList_eq_of_atIdxSlow?_eq idx 6 (family atidx): ¬T' from the assignment yd0.toList = [0]
theorem Iter.toList_eq_of_atIdxSlow?_eq.h6_neg (h₁ : yd0.toList = [0]) :
    ¬ drop0% Std.Iter.toList_eq_of_atIdxSlow?_eq 6 := fun h => by
  have := h (it₁ := em) (it₂ := yd0) (fun k => by rw [YD.atIdx, EM.atIdx]); rw [h₁, EM.toList] at this; opq_close

-- support for the independent row Std.Iter.atIdxSlow?_append idx 6 (family atidxapp): ¬T' from the assignment (em.append lp).atIdxSlow? 0 = some 0; lp.atIdxSlow? 0 = none
theorem Iter.atIdxSlow?_append.h6_neg (h₁ : (em.append lp).atIdxSlow? 0 = some 0) (h₂ : lp.atIdxSlow? 0 = none) :
    ¬ drop0% Std.Iter.atIdxSlow?_append 6 := fun h => by
  have := h (it₁ := em) (it₂ := lp) (n := 0); rw [h₁, EM.toList] at this; simp [h₂] at this

-- support for the independent row Std.IterM.anyM_filterMapM idx 6 (family loop): ¬T' from the assignment Std.IterM.anyM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))) = (pure ⟨true⟩ : TM _); ∀ P : Nat → TM (ULift Bool), Std.IterM.anyM P (ytm.mapM (fun b => (pure b : TM Nat))) = (pure ⟨false⟩ : TM _)
theorem IterM.anyM_filterMapM.h6_neg (h₁ : Std.IterM.anyM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))) = (pure ⟨true⟩ : TM _)) (h₂ : ∀ P : Nat → TM (ULift Bool), Std.IterM.anyM P (ytm.mapM (fun b => (pure b : TM Nat))) = (pure ⟨false⟩ : TM _)) :
    ¬ drop0% Std.IterM.anyM_filterMapM 6 := fun h => by
  have := h (m := TM) (n := TM) (it := ytm) (f := (fun b => (pure (some b) : TM (Option Nat)))) (p := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.anyM_filterMapM idx 5 (family loop): ¬T' from the assignment Std.IterM.anyM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (yl.filterMapM (fun b => (pure (some b) : TM (Option Nat)))) = (pure ⟨true⟩ : TM _); ∀ P : Nat → TM (ULift Bool), Std.IterM.anyM P (yl.mapM (fun b => (pure b : TM Nat))) = (pure ⟨false⟩ : TM _)
theorem Iter.anyM_filterMapM.h5_neg (h₁ : Std.IterM.anyM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (yl.filterMapM (fun b => (pure (some b) : TM (Option Nat)))) = (pure ⟨true⟩ : TM _)) (h₂ : ∀ P : Nat → TM (ULift Bool), Std.IterM.anyM P (yl.mapM (fun b => (pure b : TM Nat))) = (pure ⟨false⟩ : TM _)) :
    ¬ drop0% Std.Iter.anyM_filterMapM 5 := fun h => by
  have := h (m := TM) (it := yl) (f := (fun b => (pure (some b) : TM (Option Nat)))) (p := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.anyM_mapM idx 6 (family loop): ¬T' from the assignment Std.IterM.anyM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (ytm.mapM (fun b => (pure (b + 1) : TM Nat))) = (pure ⟨true⟩ : TM _); ∀ P : Nat → TM (ULift Bool), Std.IterM.anyM P (ytm.mapM (fun b => (pure b : TM Nat))) = (pure ⟨false⟩ : TM _)
theorem IterM.anyM_mapM.h6_neg (h₁ : Std.IterM.anyM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (ytm.mapM (fun b => (pure (b + 1) : TM Nat))) = (pure ⟨true⟩ : TM _)) (h₂ : ∀ P : Nat → TM (ULift Bool), Std.IterM.anyM P (ytm.mapM (fun b => (pure b : TM Nat))) = (pure ⟨false⟩ : TM _)) :
    ¬ drop0% Std.IterM.anyM_mapM 6 := fun h => by
  have := h (m := TM) (n := TM) (it := ytm) (f := (fun b => (pure (b + 1) : TM Nat))) (p := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.anyM_mapM idx 5 (family loop): ¬T' from the assignment Std.IterM.anyM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (yl.mapM (fun b => (pure (b + 1) : TM Nat))) = (pure ⟨true⟩ : TM _); ∀ P : Nat → TM (ULift Bool), Std.IterM.anyM P (yl.mapM (fun b => (pure b : TM Nat))) = (pure ⟨false⟩ : TM _)
theorem Iter.anyM_mapM.h5_neg (h₁ : Std.IterM.anyM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (yl.mapM (fun b => (pure (b + 1) : TM Nat))) = (pure ⟨true⟩ : TM _)) (h₂ : ∀ P : Nat → TM (ULift Bool), Std.IterM.anyM P (yl.mapM (fun b => (pure b : TM Nat))) = (pure ⟨false⟩ : TM _)) :
    ¬ drop0% Std.Iter.anyM_mapM 5 := fun h => by
  have := h (m := TM) (it := yl) (f := (fun b => (pure (b + 1) : TM Nat))) (p := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.anyM_filterM idx 5 (family loop): ¬T' from the assignment Std.IterM.anyM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (ytm.filterM (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))) = (pure ⟨true⟩ : TM _); ∀ P : Nat → TM (ULift Bool), Std.IterM.anyM P (ytm.mapM (fun b => (pure b : TM Nat))) = (pure ⟨false⟩ : TM _)
theorem IterM.anyM_filterM.h5_neg (h₁ : Std.IterM.anyM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (ytm.filterM (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))) = (pure ⟨true⟩ : TM _)) (h₂ : ∀ P : Nat → TM (ULift Bool), Std.IterM.anyM P (ytm.mapM (fun b => (pure b : TM Nat))) = (pure ⟨false⟩ : TM _)) :
    ¬ drop0% Std.IterM.anyM_filterM 5 := fun h => by
  have := h (m := TM) (n := TM) (it := ytm) (f := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))) (p := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.anyM_filterM idx 4 (family loop): ¬T' from the assignment Std.IterM.anyM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (yl.filterM (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))) = (pure ⟨true⟩ : TM _); ∀ P : Nat → TM (ULift Bool), Std.IterM.anyM P (yl.mapM (fun b => (pure b : TM Nat))) = (pure ⟨false⟩ : TM _)
theorem Iter.anyM_filterM.h4_neg (h₁ : Std.IterM.anyM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (yl.filterM (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))) = (pure ⟨true⟩ : TM _)) (h₂ : ∀ P : Nat → TM (ULift Bool), Std.IterM.anyM P (yl.mapM (fun b => (pure b : TM Nat))) = (pure ⟨false⟩ : TM _)) :
    ¬ drop0% Std.Iter.anyM_filterM 4 := fun h => by
  have := h (m := TM) (it := yl) (f := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))) (p := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.allM_filterMapM idx 6 (family loop): ¬T' from the assignment Std.IterM.allM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))) = (pure ⟨false⟩ : TM _); ∀ P : Nat → TM (ULift Bool), Std.IterM.allM P (ytm.mapM (fun b => (pure b : TM Nat))) = (pure ⟨true⟩ : TM _)
theorem IterM.allM_filterMapM.h6_neg (h₁ : Std.IterM.allM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (ytm.filterMapM (fun b => (pure (some b) : TM (Option Nat)))) = (pure ⟨false⟩ : TM _)) (h₂ : ∀ P : Nat → TM (ULift Bool), Std.IterM.allM P (ytm.mapM (fun b => (pure b : TM Nat))) = (pure ⟨true⟩ : TM _)) :
    ¬ drop0% Std.IterM.allM_filterMapM 6 := fun h => by
  have := h (m := TM) (n := TM) (it := ytm) (f := (fun b => (pure (some b) : TM (Option Nat)))) (p := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.allM_filterMapM idx 5 (family loop): ¬T' from the assignment Std.IterM.allM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (yl.filterMapM (fun b => (pure (some b) : TM (Option Nat)))) = (pure ⟨false⟩ : TM _); ∀ P : Nat → TM (ULift Bool), Std.IterM.allM P (yl.mapM (fun b => (pure b : TM Nat))) = (pure ⟨true⟩ : TM _)
theorem Iter.allM_filterMapM.h5_neg (h₁ : Std.IterM.allM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (yl.filterMapM (fun b => (pure (some b) : TM (Option Nat)))) = (pure ⟨false⟩ : TM _)) (h₂ : ∀ P : Nat → TM (ULift Bool), Std.IterM.allM P (yl.mapM (fun b => (pure b : TM Nat))) = (pure ⟨true⟩ : TM _)) :
    ¬ drop0% Std.Iter.allM_filterMapM 5 := fun h => by
  have := h (m := TM) (it := yl) (f := (fun b => (pure (some b) : TM (Option Nat)))) (p := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.allM_mapM idx 6 (family loop): ¬T' from the assignment Std.IterM.allM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (ytm.mapM (fun b => (pure (b + 1) : TM Nat))) = (pure ⟨false⟩ : TM _); ∀ P : Nat → TM (ULift Bool), Std.IterM.allM P (ytm.mapM (fun b => (pure b : TM Nat))) = (pure ⟨true⟩ : TM _)
theorem IterM.allM_mapM.h6_neg (h₁ : Std.IterM.allM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (ytm.mapM (fun b => (pure (b + 1) : TM Nat))) = (pure ⟨false⟩ : TM _)) (h₂ : ∀ P : Nat → TM (ULift Bool), Std.IterM.allM P (ytm.mapM (fun b => (pure b : TM Nat))) = (pure ⟨true⟩ : TM _)) :
    ¬ drop0% Std.IterM.allM_mapM 6 := fun h => by
  have := h (m := TM) (n := TM) (it := ytm) (f := (fun b => (pure (b + 1) : TM Nat))) (p := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.allM_mapM idx 5 (family loop): ¬T' from the assignment Std.IterM.allM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (yl.mapM (fun b => (pure (b + 1) : TM Nat))) = (pure ⟨false⟩ : TM _); ∀ P : Nat → TM (ULift Bool), Std.IterM.allM P (yl.mapM (fun b => (pure b : TM Nat))) = (pure ⟨true⟩ : TM _)
theorem Iter.allM_mapM.h5_neg (h₁ : Std.IterM.allM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (yl.mapM (fun b => (pure (b + 1) : TM Nat))) = (pure ⟨false⟩ : TM _)) (h₂ : ∀ P : Nat → TM (ULift Bool), Std.IterM.allM P (yl.mapM (fun b => (pure b : TM Nat))) = (pure ⟨true⟩ : TM _)) :
    ¬ drop0% Std.Iter.allM_mapM 5 := fun h => by
  have := h (m := TM) (it := yl) (f := (fun b => (pure (b + 1) : TM Nat))) (p := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.allM_filterM idx 5 (family loop): ¬T' from the assignment Std.IterM.allM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (ytm.filterM (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))) = (pure ⟨false⟩ : TM _); ∀ P : Nat → TM (ULift Bool), Std.IterM.allM P (ytm.mapM (fun b => (pure b : TM Nat))) = (pure ⟨true⟩ : TM _)
theorem IterM.allM_filterM.h5_neg (h₁ : Std.IterM.allM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (ytm.filterM (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))) = (pure ⟨false⟩ : TM _)) (h₂ : ∀ P : Nat → TM (ULift Bool), Std.IterM.allM P (ytm.mapM (fun b => (pure b : TM Nat))) = (pure ⟨true⟩ : TM _)) :
    ¬ drop0% Std.IterM.allM_filterM 5 := fun h => by
  have := h (m := TM) (n := TM) (it := ytm) (f := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))) (p := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.allM_filterM idx 4 (family loop): ¬T' from the assignment Std.IterM.allM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (yl.filterM (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))) = (pure ⟨false⟩ : TM _); ∀ P : Nat → TM (ULift Bool), Std.IterM.allM P (yl.mapM (fun b => (pure b : TM Nat))) = (pure ⟨true⟩ : TM _)
theorem Iter.allM_filterM.h4_neg (h₁ : Std.IterM.allM (fun _ => (pure ⟨true⟩ : TM (ULift Bool))) (yl.filterM (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))) = (pure ⟨false⟩ : TM _)) (h₂ : ∀ P : Nat → TM (ULift Bool), Std.IterM.allM P (yl.mapM (fun b => (pure b : TM Nat))) = (pure ⟨true⟩ : TM _)) :
    ¬ drop0% Std.Iter.allM_filterM 4 := fun h => by
  have := h (m := TM) (it := yl) (f := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))) (p := (fun _ => (pure ⟨true⟩ : TM (ULift Bool)))); rw [h₁, h₂] at this; opq_close


/-! ### Support lemmas written by hand (flatMap, uLift, slices, strings) -/

/-- `YL` with a second, finite `Iterator` instance (always done): the theorems with duplicated
binder lists (`toList_flatMap`, ...) keep a `Finite` hypothesis about the first instance. -/
def YL.doneInst {m : Type → Type} [Pure m] : Iterator YL m Nat where
  IsPlausibleStep _ s := s = .done
  step _ := pure (.deflate ⟨.done, rfl⟩)

theorem YL.doneFinite {m : Type → Type} [Pure m] : @Finite YL m Nat YL.doneInst :=
  @Finite.mk YL m Nat YL.doneInst ⟨fun a => ⟨a, fun b h => by
    obtain ⟨s, hs, hp⟩ := h
    cases hp; cases hs⟩⟩

-- support for the independent row Std.Iter.toList_flatMap idx 10 (family flatMap): ¬T' from the assignment (yl.flatMap (fun _ => em)).toList = [0]; ∀ F, (yl.map F).toList = []
theorem Iter.toList_flatMap.h10_neg (h₁ : (yl.flatMap (fun _ => em)).toList = [0])
    (h₂ : ∀ F : Nat → List Nat, (yl.map F).toList = []) : ¬ drop0% Std.Iter.toList_flatMap 10 := fun h => by
  have := @h YL EM Nat Nat YL.doneInst _ YL.doneFinite _ _ _ _ (fun _ => em) yl
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toList_flatMap idx 11 (family flatMap): ¬T' from the assignment (em.flatMap (fun _ => yl)).toList = [0]
theorem Iter.toList_flatMap.h11_neg (h₁ : (em.flatMap (fun _ => yl)).toList = [0]) :
    ¬ drop0% Std.Iter.toList_flatMap 11 := fun h => by
  have := @h EM YL Nat Nat _ YL.doneInst _ YL.doneFinite _ _ _ (fun _ => yl) em
  rw [h₁, Iter.toList_map, EM.toList] at this; opq_close

-- support for the independent row Std.Iter.toArray_flatMap idx 10 (family flatMap): ¬T' from the assignment (yl.flatMap (fun _ => em)).toArray = #[0]; ∀ F, (yl.map F).toArray = #[]
theorem Iter.toArray_flatMap.h10_neg (h₁ : (yl.flatMap (fun _ => em)).toArray = #[0])
    (h₂ : ∀ F : Nat → Array Nat, (yl.map F).toArray = #[]) : ¬ drop0% Std.Iter.toArray_flatMap 10 := fun h => by
  have := @h YL EM Nat Nat YL.doneInst _ YL.doneFinite _ _ _ _ (fun _ => em) yl
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_flatMap idx 11 (family flatMap): ¬T' from the assignment (em.flatMap (fun _ => yl)).toArray = #[0]
theorem Iter.toArray_flatMap.h11_neg (h₁ : (em.flatMap (fun _ => yl)).toArray = #[0]) :
    ¬ drop0% Std.Iter.toArray_flatMap 11 := fun h => by
  have := @h EM YL Nat Nat _ YL.doneInst _ YL.doneFinite _ _ _ (fun _ => yl) em
  rw [h₁, Iter.toArray_map, EM.toArray] at this; opq_close

-- support for the independent row Std.Iter.toList_flatMapAfter idx 6 (family flatMap): ¬T' from the assignment (yl.flatMapAfter (fun _ => em) none).toList = [0]; ∀ F, (yl.map F).toList = []
theorem Iter.toList_flatMapAfter.h6_neg (h₁ : (yl.flatMapAfter (fun _ => em) none).toList = [0])
    (h₂ : ∀ F : Nat → List Nat, (yl.map F).toList = []) : ¬ drop0% Std.Iter.toList_flatMapAfter 6 := fun h => by
  have := h (it₁ := yl) (f := fun _ => em) (it₂ := none)
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toList_flatMapAfter idx 7 (family flatMap): ¬T' from the assignment (em.flatMapAfter (fun _ => yl) none).toList = [0]
theorem Iter.toList_flatMapAfter.h7_neg (h₁ : (em.flatMapAfter (fun _ => yl) none).toList = [0]) :
    ¬ drop0% Std.Iter.toList_flatMapAfter 7 := fun h => by
  have := h (it₁ := em) (f := fun _ => yl) (it₂ := none)
  rw [h₁, Iter.toList_map, EM.toList] at this; opq_close

-- support for the independent row Std.Iter.toArray_flatMapAfter idx 6 (family flatMap): ¬T' from the assignment (yl.flatMapAfter (fun _ => em) none).toArray = #[0]; ∀ F, (yl.map F).toArray = #[]
theorem Iter.toArray_flatMapAfter.h6_neg (h₁ : (yl.flatMapAfter (fun _ => em) none).toArray = #[0])
    (h₂ : ∀ F : Nat → Array Nat, (yl.map F).toArray = #[]) : ¬ drop0% Std.Iter.toArray_flatMapAfter 6 := fun h => by
  have := h (it₁ := yl) (f := fun _ => em) (it₂ := none)
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_flatMapAfter idx 7 (family flatMap): ¬T' from the assignment (em.flatMapAfter (fun _ => yl) none).toArray = #[0]
theorem Iter.toArray_flatMapAfter.h7_neg (h₁ : (em.flatMapAfter (fun _ => yl) none).toArray = #[0]) :
    ¬ drop0% Std.Iter.toArray_flatMapAfter 7 := fun h => by
  have := h (it₁ := em) (f := fun _ => yl) (it₂ := none)
  rw [h₁, Iter.toArray_map, EM.toArray] at this; opq_close

-- support for the independent row Std.Iter.toList_flatMapM idx 11 (family flatMap): ¬T' from the assignment (flatMapM over yl).toList = [0]; ∀ F, (yl.mapM F).toList = []
theorem Iter.toList_flatMapM.h11_neg (h₁ : (yl.flatMapM (fun _ => (pure etm : TM _))).toList = (pure [0] : TM _))
    (h₂ : ∀ F : Nat → TM (List Nat), (yl.mapM F).toList = (pure [] : TM _)) : ¬ drop0% Std.Iter.toList_flatMapM 11 := fun h => by
  have := h (m := TM) (it₁ := yl) (f := fun _ => (pure etm : TM _))
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toList_flatMapM idx 12 (family flatMap): ¬T' from the assignment (flatMapM over em).toList = [0]
theorem Iter.toList_flatMapM.h12_neg (h₁ : (em.flatMapM (fun _ => (pure ytm : TM _))).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.Iter.toList_flatMapM 12 := fun h => by
  have := h (m := TM) (it₁ := em) (f := fun _ => (pure ytm : TM _))
  rw [h₁, Iter.toList_mapM, EM.toList] at this; opq_close

-- support for the independent row Std.Iter.toList_flatMapAfterM idx 11 (family flatMap): ¬T' from the assignment (flatMapAfterM over yl).toList = [0]; ∀ F, (yl.mapM F).toList = []
theorem Iter.toList_flatMapAfterM.h11_neg (h₁ : (yl.flatMapAfterM (fun _ => (pure etm : TM _)) none).toList = (pure [0] : TM _))
    (h₂ : ∀ F : Nat → TM (List Nat), (yl.mapM F).toList = (pure [] : TM _)) : ¬ drop0% Std.Iter.toList_flatMapAfterM 11 := fun h => by
  have := h (m := TM) (it₁ := yl) (f := fun _ => (pure etm : TM _)) (it₂ := none)
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toList_flatMapAfterM idx 12 (family flatMap): ¬T' from the assignment (flatMapAfterM over em).toList = [0]
theorem Iter.toList_flatMapAfterM.h12_neg (h₁ : (em.flatMapAfterM (fun _ => (pure ytm : TM _)) none).toList = (pure [0] : TM _)) :
    ¬ drop0% Std.Iter.toList_flatMapAfterM 12 := fun h => by
  have := h (m := TM) (it₁ := em) (f := fun _ => (pure ytm : TM _)) (it₂ := none)
  rw [h₁, Iter.toList_mapM, EM.toList] at this; opq_close

-- support for the independent row Std.IterM.toList_flatMapM idx 11 (family flatMap): ¬T' from the assignment (flatMapM over ytm).toList = [0]; ∀ F, (ytm.mapM F).toList = []
theorem IterM.toList_flatMapM.h11_neg (h₁ : (ytm.flatMapM (fun _ => (pure etm : TM _))).toList = (pure [0] : TM _))
    (h₂ : ∀ F : Nat → TM (List Nat), (ytm.mapM F).toList = (pure [] : TM _)) : ¬ drop0% Std.IterM.toList_flatMapM 11 := fun h => by
  have := h (m := TM) (it₁ := ytm) (f := fun _ => (pure etm : TM _))
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_flatMapM idx 12 (family flatMap): ¬T' from the assignment (with the true value of (etm.mapM F)) (flatMapM over etm).toList = [0]
theorem IterM.toList_flatMapM.h12_neg (h₁ : (etm.flatMapM (fun _ => (pure ytm : TM _))).toList = (pure [0] : TM _))
    (h₂ : ∀ F : Nat → TM (List Nat), (etm.mapM F).toList = (pure [] : TM _)) :
    ¬ drop0% Std.IterM.toList_flatMapM 12 := fun h => by
  have := h (m := TM) (it₁ := etm) (f := fun _ => (pure ytm : TM _))
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_flatMapAfterM idx 11 (family flatMap): ¬T' from the assignment (flatMapAfterM over ytm).toList = [0]; ∀ F, (ytm.mapM F).toList = []
theorem IterM.toList_flatMapAfterM.h11_neg (h₁ : (ytm.flatMapAfterM (fun _ => (pure etm : TM _)) none).toList = (pure [0] : TM _))
    (h₂ : ∀ F : Nat → TM (List Nat), (ytm.mapM F).toList = (pure [] : TM _)) : ¬ drop0% Std.IterM.toList_flatMapAfterM 11 := fun h => by
  have := h (m := TM) (it₁ := ytm) (f := fun _ => (pure etm : TM _)) (it₂ := none)
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_flatMapAfterM idx 12 (family flatMap): ¬T' from the assignment (flatMapAfterM over etm).toList = [0]
theorem IterM.toList_flatMapAfterM.h12_neg (h₁ : (etm.flatMapAfterM (fun _ => (pure ytm : TM _)) none).toList = (pure [0] : TM _))
    (h₂ : ∀ F : Nat → TM (List Nat), (etm.mapM F).toList = (pure [] : TM _)) :
    ¬ drop0% Std.IterM.toList_flatMapAfterM 12 := fun h => by
  have := h (m := TM) (it₁ := etm) (f := fun _ => (pure ytm : TM _)) (it₂ := none)
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_flatMapAfter idx 11 (family flatMap): ¬T' from the assignment (flatMapAfter over ytm).toList = [0]; ∀ F, (ytm.mapM F).toList = []
theorem IterM.toList_flatMapAfter.h11_neg (h₁ : (ytm.flatMapAfter (fun _ => etm) none).toList = (pure [0] : TM _))
    (h₂ : ∀ F : Nat → TM (List Nat), (ytm.mapM F).toList = (pure [] : TM _)) : ¬ drop0% Std.IterM.toList_flatMapAfter 11 := fun h => by
  have := h (m := TM) (it₁ := ytm) (f := fun _ => etm) (it₂ := none)
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_flatMapAfter idx 12 (family flatMap): ¬T' from the assignment (flatMapAfter over etm).toList = [0]
theorem IterM.toList_flatMapAfter.h12_neg (h₁ : (etm.flatMapAfter (fun _ => ytm) none).toList = (pure [0] : TM _))
    (h₂ : ∀ F : Nat → TM (List Nat), (etm.mapM F).toList = (pure [] : TM _)) :
    ¬ drop0% Std.IterM.toList_flatMapAfter 12 := fun h => by
  have := h (m := TM) (it₁ := etm) (f := fun _ => ytm) (it₂ := none)
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_flatMap idx 15 (family flatMap): ¬T' from the assignment (ytm.flatMap (fun _ => etm)).toList = [0]; ∀ F, (ytm.mapM F).toList = []
theorem IterM.toList_flatMap.h15_neg (h₁ : (ytm.flatMap (fun _ => etm)).toList = (pure [0] : TM _))
    (h₂ : ∀ F : Nat → TM (List Nat), (ytm.mapM F).toList = (pure [] : TM _)) : ¬ drop0% Std.IterM.toList_flatMap 15 := fun h => by
  have := @h YL EM Nat Nat TM _ _ _ _ YL.doneInst _ YL.doneFinite _ _ _ _ (fun _ => etm) ytm
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_flatMap idx 16 (family flatMap): ¬T' from the assignment (etm.flatMap (fun _ => ytm)).toList = [0]
theorem IterM.toList_flatMap.h16_neg (h₁ : (etm.flatMap (fun _ => ytm)).toList = (pure [0] : TM _))
    (h₂ : ∀ F : Nat → TM (List Nat), (etm.mapM F).toList = (pure [] : TM _)) :
    ¬ drop0% Std.IterM.toList_flatMap 16 := fun h => by
  have := @h EM YL Nat Nat TM _ _ _ _ _ YL.doneInst _ YL.doneFinite _ _ _ (fun _ => ytm) etm
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_flatMapM idx 11 (family flatMap): ¬T' from the assignment (flatMapM over yl).toArray = #[0]; ∀ F, (yl.mapM F).toArray = #[]
theorem Iter.toArray_flatMapM.h11_neg (h₁ : (yl.flatMapM (fun _ => (pure etm : TM _))).toArray = (pure #[0] : TM _))
    (h₂ : ∀ F : Nat → TM (Array Nat), (yl.mapM F).toArray = (pure #[] : TM _)) : ¬ drop0% Std.Iter.toArray_flatMapM 11 := fun h => by
  have := h (m := TM) (it₁ := yl) (f := fun _ => (pure etm : TM _))
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_flatMapM idx 12 (family flatMap): ¬T' from the assignment (flatMapM over em).toArray = #[0]
theorem Iter.toArray_flatMapM.h12_neg (h₁ : (em.flatMapM (fun _ => (pure ytm : TM _))).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.Iter.toArray_flatMapM 12 := fun h => by
  have := h (m := TM) (it₁ := em) (f := fun _ => (pure ytm : TM _))
  rw [h₁, Iter.toArray_mapM, EM.toArray] at this; opq_close

-- support for the independent row Std.Iter.toArray_flatMapAfterM idx 11 (family flatMap): ¬T' from the assignment (flatMapAfterM over yl).toArray = #[0]; ∀ F, (yl.mapM F).toArray = #[]
theorem Iter.toArray_flatMapAfterM.h11_neg (h₁ : (yl.flatMapAfterM (fun _ => (pure etm : TM _)) none).toArray = (pure #[0] : TM _))
    (h₂ : ∀ F : Nat → TM (Array Nat), (yl.mapM F).toArray = (pure #[] : TM _)) : ¬ drop0% Std.Iter.toArray_flatMapAfterM 11 := fun h => by
  have := h (m := TM) (it₁ := yl) (f := fun _ => (pure etm : TM _)) (it₂ := none)
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.toArray_flatMapAfterM idx 12 (family flatMap): ¬T' from the assignment (flatMapAfterM over em).toArray = #[0]
theorem Iter.toArray_flatMapAfterM.h12_neg (h₁ : (em.flatMapAfterM (fun _ => (pure ytm : TM _)) none).toArray = (pure #[0] : TM _)) :
    ¬ drop0% Std.Iter.toArray_flatMapAfterM 12 := fun h => by
  have := h (m := TM) (it₁ := em) (f := fun _ => (pure ytm : TM _)) (it₂ := none)
  rw [h₁, Iter.toArray_mapM, EM.toArray] at this; opq_close

-- support for the independent row Std.IterM.toArray_flatMapM idx 11 (family flatMap): ¬T' from the assignment (flatMapM over ytm).toArray = #[0]; ∀ F, (ytm.mapM F).toArray = #[]
theorem IterM.toArray_flatMapM.h11_neg (h₁ : (ytm.flatMapM (fun _ => (pure etm : TM _))).toArray = (pure #[0] : TM _))
    (h₂ : ∀ F : Nat → TM (Array Nat), (ytm.mapM F).toArray = (pure #[] : TM _)) : ¬ drop0% Std.IterM.toArray_flatMapM 11 := fun h => by
  have := h (m := TM) (it₁ := ytm) (f := fun _ => (pure etm : TM _))
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_flatMapM idx 12 (family flatMap): ¬T' from the assignment (with the true value of (etm.mapM F)) (flatMapM over etm).toArray = #[0]
theorem IterM.toArray_flatMapM.h12_neg (h₁ : (etm.flatMapM (fun _ => (pure ytm : TM _))).toArray = (pure #[0] : TM _))
    (h₂ : ∀ F : Nat → TM (Array Nat), (etm.mapM F).toArray = (pure #[] : TM _)) :
    ¬ drop0% Std.IterM.toArray_flatMapM 12 := fun h => by
  have := h (m := TM) (it₁ := etm) (f := fun _ => (pure ytm : TM _))
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_flatMapAfterM idx 11 (family flatMap): ¬T' from the assignment (flatMapAfterM over ytm).toArray = #[0]; ∀ F, (ytm.mapM F).toArray = #[]
theorem IterM.toArray_flatMapAfterM.h11_neg (h₁ : (ytm.flatMapAfterM (fun _ => (pure etm : TM _)) none).toArray = (pure #[0] : TM _))
    (h₂ : ∀ F : Nat → TM (Array Nat), (ytm.mapM F).toArray = (pure #[] : TM _)) : ¬ drop0% Std.IterM.toArray_flatMapAfterM 11 := fun h => by
  have := h (m := TM) (it₁ := ytm) (f := fun _ => (pure etm : TM _)) (it₂ := none)
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_flatMapAfterM idx 12 (family flatMap): ¬T' from the assignment (flatMapAfterM over etm).toArray = #[0]
theorem IterM.toArray_flatMapAfterM.h12_neg (h₁ : (etm.flatMapAfterM (fun _ => (pure ytm : TM _)) none).toArray = (pure #[0] : TM _))
    (h₂ : ∀ F : Nat → TM (Array Nat), (etm.mapM F).toArray = (pure #[] : TM _)) :
    ¬ drop0% Std.IterM.toArray_flatMapAfterM 12 := fun h => by
  have := h (m := TM) (it₁ := etm) (f := fun _ => (pure ytm : TM _)) (it₂ := none)
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_flatMapAfter idx 11 (family flatMap): ¬T' from the assignment (flatMapAfter over ytm).toArray = #[0]; ∀ F, (ytm.mapM F).toArray = #[]
theorem IterM.toArray_flatMapAfter.h11_neg (h₁ : (ytm.flatMapAfter (fun _ => etm) none).toArray = (pure #[0] : TM _))
    (h₂ : ∀ F : Nat → TM (Array Nat), (ytm.mapM F).toArray = (pure #[] : TM _)) : ¬ drop0% Std.IterM.toArray_flatMapAfter 11 := fun h => by
  have := h (m := TM) (it₁ := ytm) (f := fun _ => etm) (it₂ := none)
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_flatMapAfter idx 12 (family flatMap): ¬T' from the assignment (flatMapAfter over etm).toArray = #[0]
theorem IterM.toArray_flatMapAfter.h12_neg (h₁ : (etm.flatMapAfter (fun _ => ytm) none).toArray = (pure #[0] : TM _))
    (h₂ : ∀ F : Nat → TM (Array Nat), (etm.mapM F).toArray = (pure #[] : TM _)) :
    ¬ drop0% Std.IterM.toArray_flatMapAfter 12 := fun h => by
  have := h (m := TM) (it₁ := etm) (f := fun _ => ytm) (it₂ := none)
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_flatMap idx 15 (family flatMap): ¬T' from the assignment (ytm.flatMap (fun _ => etm)).toArray = #[0]; ∀ F, (ytm.mapM F).toArray = #[]
theorem IterM.toArray_flatMap.h15_neg (h₁ : (ytm.flatMap (fun _ => etm)).toArray = (pure #[0] : TM _))
    (h₂ : ∀ F : Nat → TM (Array Nat), (ytm.mapM F).toArray = (pure #[] : TM _)) : ¬ drop0% Std.IterM.toArray_flatMap 15 := fun h => by
  have := @h YL EM Nat Nat TM _ _ _ _ YL.doneInst _ YL.doneFinite _ _ _ _ (fun _ => etm) ytm
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_flatMap idx 16 (family flatMap): ¬T' from the assignment (etm.flatMap (fun _ => ytm)).toArray = #[0]
theorem IterM.toArray_flatMap.h16_neg (h₁ : (etm.flatMap (fun _ => ytm)).toArray = (pure #[0] : TM _))
    (h₂ : ∀ F : Nat → TM (Array Nat), (etm.mapM F).toArray = (pure #[] : TM _)) :
    ¬ drop0% Std.IterM.toArray_flatMap 16 := fun h => by
  have := @h EM YL Nat Nat TM _ _ _ _ _ YL.doneInst _ YL.doneFinite _ _ _ (fun _ => ytm) etm
  rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toList_uLift idx 9 (family coll): ¬T' from the assignment (ylm.uLift Id).toList = pure []; ylm.toList = pure [0]
theorem IterM.toList_uLift.h9_neg (h₁ : (ylm.uLift Id).toList = (pure [] : Id (List (ULift.{0} Nat))))
    (h₂ : ylm.toList = pure [0]) : ¬ drop0% Std.IterM.toList_uLift 9 := fun h => by
  have := h (m := Id) (n := Id) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toListRev_uLift idx 9 (family coll): ¬T' from the assignment (ylm.uLift Id).toListRev = pure []; ylm.toListRev = pure [0]
theorem IterM.toListRev_uLift.h9_neg (h₁ : (ylm.uLift Id).toListRev = (pure [] : Id (List (ULift.{0} Nat))))
    (h₂ : ylm.toListRev = pure [0]) : ¬ drop0% Std.IterM.toListRev_uLift 9 := fun h => by
  have := h (m := Id) (n := Id) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.IterM.toArray_uLift idx 9 (family coll): ¬T' from the assignment (ylm.uLift Id).toArray = pure #[]; ylm.toArray = pure #[0]
theorem IterM.toArray_uLift.h9_neg (h₁ : (ylm.uLift Id).toArray = (pure #[] : Id (Array (ULift.{0} Nat))))
    (h₂ : ylm.toArray = pure #[0]) : ¬ drop0% Std.IterM.toArray_uLift 9 := fun h => by
  have := h (m := Id) (n := Id) (it := ylm); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.joinString_eq idx 3 (family loop): ¬T' from the assignment yl.joinString = "a"; yl.toList = []
theorem Iter.joinString_eq.h3_neg (h₁ : yl.joinString = "a") (h₂ : yl.toList = []) :
    ¬ drop0% Std.Iter.joinString_eq 3 := fun h => by
  have := h (it := yl); rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Iter.intercalateString_eq idx 3 (family loop): ¬T' from the assignment yl.intercalateString "".toSlice = "a"; yl.toList = []
theorem Iter.intercalateString_eq.h3_neg (h₁ : Iter.intercalateString "".toSlice yl = "a") (h₂ : yl.toList = []) :
    ¬ drop0% Std.Iter.intercalateString_eq 3 := fun h => by
  have := h (it := yl) (s := "".toSlice); rw [h₁, h₂] at this; opq_close

/-! Slices whose iterator is `yl`; `SliceSize` is the default-loop length, so `LawfulSliceSize`
holds by definition. -/
instance YS.toIter : ToIterator (Slice Unit) Id YL Nat := ⟨fun _ => ⟨⟨()⟩⟩⟩
instance YS.size : Slice.SliceSize Unit :=
  ⟨fun s => letI : IteratorLoop YL Id Id := .defaultImplementation; (ToIterator.iter s).length⟩
instance YS.lawful : Slice.LawfulSliceSize Unit := ⟨fun _ => rfl⟩
instance YL.loop : IteratorLoop YL Id Id := .defaultImplementation
instance YL.lawfulLoop : LawfulIteratorLoop YL Id Id := ⟨fun _ _ _ _ _ _ _ _ => rfl⟩

abbrev ys : Slice Unit := ⟨()⟩

-- support for the independent row Std.Slice.size_toArray_eq_size idx 7 (family slice): ¬T' from the assignment yl.toArray = #[0]; yl.length = 0
theorem Slice.size_toArray_eq_size.h7_neg (h₁ : yl.toArray = #[0]) (h₂ : yl.length = 0) :
    ¬ drop0% Std.Slice.size_toArray_eq_size 7 := fun h => by
  have := h (s := ys); change yl.toArray.size = yl.length at this; rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Slice.length_toList_eq_size idx 8 (family slice): ¬T' from the assignment yl.toList = [0]; yl.length = 0
theorem Slice.length_toList_eq_size.h8_neg (h₁ : yl.toList = [0]) (h₂ : yl.length = 0) :
    ¬ drop0% Std.Slice.length_toList_eq_size 8 := fun h => by
  have := h (s := ys); change yl.toList.length = yl.length at this; rw [h₁, h₂] at this; opq_close

-- support for the independent row Std.Slice.length_toListRev_eq_size idx 9 (family slice): ¬T' from the assignment yl.toListRev = [0]; yl.length = 0
theorem Slice.length_toListRev_eq_size.h9_neg (h₁ : yl.toListRev = [0]) (h₂ : yl.length = 0) :
    ¬ drop0% Std.Slice.length_toListRev_eq_size 9 := fun h => by
  have := h (s := ys); change yl.toListRev.length = yl.length at this; rw [h₁, h₂] at this; opq_close

/-! A forward searcher that rejects the empty prefix forever (productive, not finite). -/
structure YSe (s : String.Slice) where u : Unit

instance YSe.inst (s : String.Slice) : Iterator (YSe s) Id (String.Slice.Pattern.SearchStep s) where
  IsPlausibleStep it st := st = .yield it (.rejected s.startPos s.startPos)
  step it := pure (.deflate ⟨.yield it (.rejected s.startPos s.startPos), rfl⟩)

instance YSe.searcher : String.Slice.Pattern.ToForwardSearcher () YSe := ⟨fun _ => ⟨⟨()⟩⟩⟩

-- support for the independent row String.Slice.toList_split_eq_splitToSubslice idx 5 (family coll; split is splitToSubslice.map toSlice): ¬T' from the assignment (split).toList = ["".toSlice]; (splitToSubslice).toList = []
theorem String.Slice.toList_split_eq_splitToSubslice.h5_neg
    (h₁ : ("".toSlice.split ()).toList = ["".toSlice]) (h₂ : ("".toSlice.splitToSubslice ()).toList = []) :
    ¬ drop0% String.Slice.toList_split_eq_splitToSubslice 5 := fun h => by
  have := h () (s := "".toSlice); rw [h₁, h₂] at this; opq_close

end OpEHand
