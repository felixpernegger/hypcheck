import Lean

/-!
Hand pass `OpD1` (hand10, ItOpaque): 51 `[Finite α Id]` hypotheses of `Init.Data.Iterators`
combinator and consumer lemmas (first half by theorem name: `Lemmas/Combinators/FilterMap`
forIn/foldM/fold/anyM/any/allM/all lemmas and the `*_toList` lemmas of `Lemmas/Consumers/Loop`).
For hypothesis `hᵢ` of theorem `T` this file proves `¬T'` (`drop0% T i`, universes set to 0).

45 necessary, 0 removable, 6 independent (opaque fixpoint; listed in
`runs/hand10/OpD1_independent.jsonl`, with support lemmas `*_support` at the end of this file).

Necessary (45): in each of these lemmas one side runs the theorem's variable base loop
`[IteratorLoop α Id n]` and the other side does not: it is a loop over a combinator iterator
(`filterMap`, `map`, `filter`, `mapM`, ... with the default `IteratorLoop` instance) or a
`List` function of `it.toList`. Without `Finite α Id` that other side is an opaque value
(`extrinsicFix` = `opaqueFix` on a non-well-founded relation), but it does not depend on the base
loop. So instead of computing it, the refutation instantiates `T'` twice at the same data, once
with base loop `ADLoop 0` and once with `ADLoop 1`: the base-loop side evaluates (by `rfl`) to two
different values (`0`/`1`, `true`/`false`, `some 0`/`some 1`), while the opaque side is the same
term, so `T'` would make two different values equal (`two`, `two'`). This is the anti-diagonal
technique without a classical case split: no opaque value needs to be named.

Model (section "Models", reusable for any opaque-loop lemma):
* `AD`: an iterator with outputs `Nat` whose every state may plausibly skip to itself or yield any
  `n` and stay; `step` skips. Not `Finite` (`AD.not_finite`), not `Productive`
  (`AD.not_productive`); every `n` is a plausible output (`AD.out`); no loop over it is
  well-founded, for any plausibility predicate (`AD.not_wf`).
* `ADLoop k`: the `IteratorLoop AD Id n` (any functor `n`) that runs the loop body once, on the
  output `k`, and returns the accumulator carried by the resulting `ForInStep`, whether `yield` or
  `done`. Lawful for every `k` and every monad `n` (`ADLoop.lawful`), vacuously, since
  `LawfulIteratorLoop` only constrains well-founded loops.

Run with the lean4 repo's stage1 binary: `lean checks/OpD1Hand.lean`.
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

namespace OpD1Hand
open Std Std.Iterators

/-! ## Models -/

theorem acc_not_self {α : Sort _} {r : α → α → Prop} {x : α} (h : Acc r x) : ¬ r x x := by
  induction h with | intro x _ ih => exact fun hxx => ih x hxx hxx

/-- Iterator state with a single value; see the module docstring. -/
structure AD where
  u : Unit

instance AD.inst {m : Type → Type} [Pure m] : Iterator AD m Nat where
  IsPlausibleStep it s := s = .skip it ∨ ∃ n, s = .yield it n
  step it := pure (.deflate ⟨.skip it, Or.inl rfl⟩)

/-- The only iterator over AD. -/
abbrev AD.it : Iter (α := AD) Nat := ⟨⟨()⟩⟩

theorem AD.not_finite : ¬ Iterators.Finite AD Id := fun hf =>
  acc_not_self (hf.wf.apply ⟨⟨()⟩⟩) ⟨.skip ⟨⟨()⟩⟩, rfl, Or.inl rfl⟩

theorem AD.not_productive : ¬ Iterators.Productive AD Id := fun hp =>
  acc_not_self (hp.wf.apply ⟨⟨()⟩⟩) (Or.inl rfl)

theorem AD.not_wf {γ : Type} [Nonempty γ] (Pl : Nat → γ → ForInStep γ → Prop) :
    ¬ IteratorLoop.WellFounded AD Id Pl := fun wf =>
  acc_not_self (wf.apply (⟨⟨()⟩⟩, Classical.ofNonempty)) (Or.inr ⟨Or.inl rfl, rfl⟩)

theorem AD.out (it : IterM (α := AD) Id Nat) (n : Nat) : it.IsPlausibleIndirectOutput n :=
  .direct ⟨it, Or.inr ⟨n, rfl⟩⟩

/-- Runs the body once on the output k and returns the accumulator it produces. -/
def ADLoop (k : Nat) {n : Type → Type} [Functor n] : IteratorLoop AD Id n where
  forIn _ γ _ it init f := (fun r => r.val.value) <$> f k (AD.out it k) init

theorem ADLoop.lawful (k : Nat) {n : Type → Type} [Monad n] : @LawfulIteratorLoop _ AD Id n _ _ _ (ADLoop k (n := n)) :=
  @LawfulIteratorLoop.mk _ AD Id n _ _ _ (ADLoop k (n := n)) (fun _ _ _ _ init Pl wf _ => absurd wf (@AD.not_wf _ ⟨init⟩ Pl))

/-- The refutation pattern: one term equal to two different values. -/
theorem two' {α : Type} {L a b : α} (hab : a ≠ b) (h0 : a = L) (h1 : b = L) : False := hab (h0.trans h1.symm)

theorem two {α : Type} {L a b : α} (hab : a ≠ b) (h0 : L = a) (h1 : L = b) : False := hab (h0.symm.trans h1)


/-! ## Necessary -/

-- `Std.Iter.forIn_filterMapWithPostcondition`, idx 13: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem forIn_filterMapWithPostcondition.h13 : ¬ drop0% Std.Iter.forIn_filterMapWithPostcondition 13 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))

-- `Std.Iter.forIn_filterMapM`, idx 15: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem forIn_filterMapM.h15 : ¬ drop0% Std.Iter.forIn_filterMapM 15 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))

-- `Std.Iter.forIn_filterMap`, idx 8: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem forIn_filterMap.h8 : ¬ drop0% Std.Iter.forIn_filterMap 8 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := some) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := some) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))

-- `Std.Iter.forIn_mapWithPostcondition`, idx 13: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem forIn_mapWithPostcondition.h13 : ¬ drop0% Std.Iter.forIn_mapWithPostcondition 13 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure x) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure x) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))

-- `Std.Iter.forIn_mapM`, idx 15: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem forIn_mapM.h15 : ¬ drop0% Std.Iter.forIn_mapM 15 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := pure) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := pure) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))

-- `Std.Iter.forIn_map`, idx 8: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem forIn_map.h8 : ¬ drop0% Std.Iter.forIn_map 8 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := id) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := id) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))

-- `Std.Iter.forIn_filterWithPostcondition`, idx 12: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem forIn_filterWithPostcondition.h12 : ¬ drop0% Std.Iter.forIn_filterWithPostcondition 12 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))

-- `Std.Iter.forIn_filterM`, idx 14: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem forIn_filterM.h14 : ¬ drop0% Std.Iter.forIn_filterM 14 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))

-- `Std.Iter.forIn_filter`, idx 7: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem forIn_filter.h7 : ¬ drop0% Std.Iter.forIn_filter 7 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun _ => true) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun _ => true) (g := fun c _ => pure (.done c)) (init := (0 : Nat)))

-- `Std.Iter.foldM_filterMapWithPostcondition`, idx 7: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem foldM_filterMapWithPostcondition.h7 : ¬ drop0% Std.Iter.foldM_filterMapWithPostcondition 7 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun _ c => pure c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun _ c => pure c) (init := (0 : Nat)))

-- `Std.Iter.foldM_filterMapM`, idx 7: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem foldM_filterMapM.h7 : ¬ drop0% Std.Iter.foldM_filterMapM 7 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun _ c => pure c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun _ c => pure c) (init := (0 : Nat)))

-- `Std.Iter.foldM_mapWithPostcondition`, idx 8: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem foldM_mapWithPostcondition.h8 : ¬ drop0% Std.Iter.foldM_mapWithPostcondition 8 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (n := Id) (o := Id) (f := fun x => pure x) (g := fun _ c => pure c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (n := Id) (o := Id) (f := fun x => pure x) (g := fun _ c => pure c) (init := (0 : Nat)))

-- `Std.Iter.foldM_mapM`, idx 7: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem foldM_mapM.h7 : ¬ drop0% Std.Iter.foldM_mapM 7 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := pure) (g := fun _ c => pure c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := pure) (g := fun _ c => pure c) (init := (0 : Nat)))

-- `Std.Iter.foldM_filterWithPostcondition`, idx 6: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem foldM_filterWithPostcondition.h6 : ¬ drop0% Std.Iter.foldM_filterWithPostcondition 6 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun _ c => pure c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun _ c => pure c) (init := (0 : Nat)))

-- `Std.Iter.foldM_filterM`, idx 6: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem foldM_filterM.h6 : ¬ drop0% Std.Iter.foldM_filterM 6 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun _ c => pure c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun _ c => pure c) (init := (0 : Nat)))

-- `Std.Iter.foldM_filterMap`, idx 6: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem foldM_filterMap.h6 : ¬ drop0% Std.Iter.foldM_filterMap 6 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := some) (g := fun _ c => pure c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := some) (g := fun _ c => pure c) (init := (0 : Nat)))

-- `Std.Iter.foldM_map`, idx 6: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem foldM_map.h6 : ¬ drop0% Std.Iter.foldM_map 6 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := id) (g := fun _ c => pure c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := id) (g := fun _ c => pure c) (init := (0 : Nat)))

-- `Std.Iter.foldM_filter`, idx 5: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem foldM_filter.h5 : ¬ drop0% Std.Iter.foldM_filter 5 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun _ => true) (g := fun _ c => pure c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun _ => true) (g := fun _ c => pure c) (init := (0 : Nat)))

-- `Std.Iter.fold_filterMapWithPostcondition`, idx 6: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem fold_filterMapWithPostcondition.h6 : ¬ drop0% Std.Iter.fold_filterMapWithPostcondition 6 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun x => pure (some x)) (g := fun _ c => c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun x => pure (some x)) (g := fun _ c => c) (init := (0 : Nat)))

-- `Std.Iter.fold_filterMapM`, idx 6: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem fold_filterMapM.h6 : ¬ drop0% Std.Iter.fold_filterMapM 6 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun x => pure (some x)) (g := fun _ c => c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun x => pure (some x)) (g := fun _ c => c) (init := (0 : Nat)))

-- `Std.Iter.fold_mapWithPostcondition`, idx 6: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem fold_mapWithPostcondition.h6 : ¬ drop0% Std.Iter.fold_mapWithPostcondition 6 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun x => pure x) (g := fun _ c => c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun x => pure x) (g := fun _ c => c) (init := (0 : Nat)))

-- `Std.Iter.fold_mapM`, idx 6: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem fold_mapM.h6 : ¬ drop0% Std.Iter.fold_mapM 6 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := pure) (g := fun _ c => c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := pure) (g := fun _ c => c) (init := (0 : Nat)))

-- `Std.Iter.fold_filterWithPostcondition`, idx 5: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem fold_filterWithPostcondition.h5 : ¬ drop0% Std.Iter.fold_filterWithPostcondition 5 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun _ => pure (.up true)) (g := fun _ c => c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun _ => pure (.up true)) (g := fun _ c => c) (init := (0 : Nat)))

-- `Std.Iter.fold_filterM`, idx 5: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem fold_filterM.h5 : ¬ drop0% Std.Iter.fold_filterM 5 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun _ => pure (.up true)) (g := fun _ c => c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (n := Id) (f := fun _ => pure (.up true)) (g := fun _ c => c) (init := (0 : Nat)))

-- `Std.Iter.fold_filterMap`, idx 5: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem fold_filterMap.h5 : ¬ drop0% Std.Iter.fold_filterMap 5 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (f := some) (g := fun _ c => c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (f := some) (g := fun _ c => c) (init := (0 : Nat)))

-- `Std.Iter.fold_map`, idx 5: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem fold_map.h5 : ¬ drop0% Std.Iter.fold_map 5 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (f := id) (g := fun _ c => c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (f := id) (g := fun _ c => c) (init := (0 : Nat)))

-- `Std.Iter.fold_filter`, idx 4: non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop
theorem fold_filter.h4 : ¬ drop0% Std.Iter.fold_filter 4 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (f := fun _ => true) (g := fun _ c => c) (init := (0 : Nat)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (f := fun _ => true) (g := fun _ c => c) (init := (0 : Nat)))

-- `Std.Iter.anyM_eq_anyM_mapM_pure`, idx 4: non-finite AD; the side through the base loop gives true with ADLoop 0 and false with ADLoop 1, the other side does not depend on the base loop
theorem anyM_eq_anyM_mapM_pure.h4 : ¬ drop0% Std.Iter.anyM_eq_anyM_mapM_pure 4 := fun h =>
  two' (α := Bool) (a := true) (b := false) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (p := fun x => pure (x == 0)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (p := fun x => pure (x == 0)))

-- `Std.Iter.anyM_filterMap`, idx 5: non-finite AD; the side through the base loop gives true with ADLoop 0 and false with ADLoop 1, the other side does not depend on the base loop
theorem anyM_filterMap.h5 : ¬ drop0% Std.Iter.anyM_filterMap 5 := fun h =>
  two (α := Bool) (a := true) (b := false) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := some) (p := fun x => pure (x == 0)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := some) (p := fun x => pure (x == 0)))

-- `Std.Iter.anyM_map`, idx 5: non-finite AD; the side through the base loop gives true with ADLoop 0 and false with ADLoop 1, the other side does not depend on the base loop
theorem anyM_map.h5 : ¬ drop0% Std.Iter.anyM_map 5 := fun h =>
  two (α := Bool) (a := true) (b := false) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := id) (p := fun x => pure (x == 0)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := id) (p := fun x => pure (x == 0)))

-- `Std.Iter.anyM_filter`, idx 4: non-finite AD; the side through the base loop gives true with ADLoop 0 and false with ADLoop 1, the other side does not depend on the base loop
theorem anyM_filter.h4 : ¬ drop0% Std.Iter.anyM_filter 4 := fun h =>
  two (α := Bool) (a := true) (b := false) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := fun _ => true) (p := fun x => pure (x == 0)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := fun _ => true) (p := fun x => pure (x == 0)))

-- `Std.Iter.any_filterMap`, idx 4: non-finite AD; the side through the base loop gives true with ADLoop 0 and false with ADLoop 1, the other side does not depend on the base loop
theorem any_filterMap.h4 : ¬ drop0% Std.Iter.any_filterMap 4 := fun h =>
  two (α := Bool) (a := true) (b := false) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (f := some) (p := (· == 0)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (f := some) (p := (· == 0)))

-- `Std.Iter.any_map`, idx 4: non-finite AD; the side through the base loop gives true with ADLoop 0 and false with ADLoop 1, the other side does not depend on the base loop
theorem any_map.h4 : ¬ drop0% Std.Iter.any_map 4 := fun h =>
  two (α := Bool) (a := true) (b := false) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (f := id) (p := (· == 0)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (f := id) (p := (· == 0)))

-- `Std.Iter.allM_eq_allM_mapM_pure`, idx 4: non-finite AD; the side through the base loop gives true with ADLoop 0 and false with ADLoop 1, the other side does not depend on the base loop
theorem allM_eq_allM_mapM_pure.h4 : ¬ drop0% Std.Iter.allM_eq_allM_mapM_pure 4 := fun h =>
  two' (α := Bool) (a := true) (b := false) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (p := fun x => pure (x == 0)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (p := fun x => pure (x == 0)))

-- `Std.Iter.allM_filterMap`, idx 5: non-finite AD; the side through the base loop gives true with ADLoop 0 and false with ADLoop 1, the other side does not depend on the base loop
theorem allM_filterMap.h5 : ¬ drop0% Std.Iter.allM_filterMap 5 := fun h =>
  two (α := Bool) (a := true) (b := false) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := some) (p := fun x => pure (x == 0)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := some) (p := fun x => pure (x == 0)))

-- `Std.Iter.allM_map`, idx 5: non-finite AD; the side through the base loop gives true with ADLoop 0 and false with ADLoop 1, the other side does not depend on the base loop
theorem allM_map.h5 : ¬ drop0% Std.Iter.allM_map 5 := fun h =>
  two (α := Bool) (a := true) (b := false) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := id) (p := fun x => pure (x == 0)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := id) (p := fun x => pure (x == 0)))

-- `Std.Iter.allM_filter`, idx 4: non-finite AD; the side through the base loop gives true with ADLoop 0 and false with ADLoop 1, the other side does not depend on the base loop
theorem allM_filter.h4 : ¬ drop0% Std.Iter.allM_filter 4 := fun h =>
  two (α := Bool) (a := true) (b := false) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := fun _ => true) (p := fun x => pure (x == 0)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := fun _ => true) (p := fun x => pure (x == 0)))

-- `Std.Iter.all_filterMap`, idx 4: non-finite AD; the side through the base loop gives true with ADLoop 0 and false with ADLoop 1, the other side does not depend on the base loop
theorem all_filterMap.h4 : ¬ drop0% Std.Iter.all_filterMap 4 := fun h =>
  two (α := Bool) (a := true) (b := false) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (f := some) (p := (· == 0)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (f := some) (p := (· == 0)))

-- `Std.Iter.all_map`, idx 4: non-finite AD; the side through the base loop gives true with ADLoop 0 and false with ADLoop 1, the other side does not depend on the base loop
theorem all_map.h4 : ¬ drop0% Std.Iter.all_map 4 := fun h =>
  two (α := Bool) (a := true) (b := false) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (f := id) (p := (· == 0)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (f := id) (p := (· == 0)))

-- `Std.Iter.findSomeM?_toList`, idx 8: non-finite AD; the side through the base loop gives some 0 with ADLoop 0 and some 1 with ADLoop 1, the other side does not depend on the base loop
theorem findSomeMQ_toList.h8 : ¬ drop0% Std.Iter.findSomeM?_toList 8 := fun h =>
  two (α := Option Nat) (a := some 0) (b := some 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := fun x => pure (some x)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := fun x => pure (some x)))

-- `Std.Iter.findSome?_toList`, idx 5: non-finite AD; the side through the base loop gives some 0 with ADLoop 0 and some 1 with ADLoop 1, the other side does not depend on the base loop
theorem findSomeQ_toList.h5 : ¬ drop0% Std.Iter.findSome?_toList 5 := fun h =>
  two (α := Option Nat) (a := some 0) (b := some 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (f := some))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (f := some))

-- `Std.Iter.findM?_toList`, idx 7: non-finite AD; the side through the base loop gives some 0 with ADLoop 0 and some 1 with ADLoop 1, the other side does not depend on the base loop
theorem findMQ_toList.h7 : ¬ drop0% Std.Iter.findM?_toList 7 := fun h =>
  two (α := Option Nat) (a := some 0) (b := some 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := fun _ => pure true))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := fun _ => pure true))

-- `Std.Iter.findM?_eq_findM?_toList`, idx 7: non-finite AD; the side through the base loop gives some 0 with ADLoop 0 and some 1 with ADLoop 1, the other side does not depend on the base loop
theorem findMQ_eq_findMQ_toList.h7 : ¬ drop0% Std.Iter.findM?_eq_findM?_toList 7 := fun h =>
  two' (α := Option Nat) (a := some 0) (b := some 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := fun _ => pure (.up true)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (m := Id) (f := fun _ => pure (.up true)))

-- `Std.Iter.find?_toList`, idx 4: non-finite AD; the side through the base loop gives some 0 with ADLoop 0 and some 1 with ADLoop 1, the other side does not depend on the base loop
theorem findQ_toList.h4 : ¬ drop0% Std.Iter.find?_toList 4 := fun h =>
  two (α := Option Nat) (a := some 0) (b := some 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) (f := fun _ => true))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) (f := fun _ => true))

-- `Std.Iter.head?_toList`, idx 4: non-finite AD; the side through the base loop gives some 0 with ADLoop 0 and some 1 with ADLoop 1, the other side does not depend on the base loop
theorem headQ_toList.h4 : ¬ drop0% Std.Iter.head?_toList 4 := fun h =>
  two (α := Option Nat) (a := some 0) (b := some 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        exact h (α := AD) (it := AD.it) )
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        exact h (α := AD) (it := AD.it) )


/-! ## Independent rows: support

For the six rows below both sides of the lemma are loops of combinator iterators
(`FilterMap`/`Map` over the non-finite `AD`, default `IteratorLoop` instance, hence `opaqueFix₃`
at two different arguments), and neither side runs the base loop. Each lemma shows that `T'`
instantiated at `AD`, `Id` is exactly the equation between these two opaque values, so `¬T'`
follows from any interpretation of `opaqueFix₃` in which they differ. -/

-- support for Std.Iter.any_filterMapM, idx 5
theorem any_filterMapM.h5_support
    (hne : (AD.it.filterMapM (m := Id) (fun x => pure (some x))).any (· == 0) ≠
      (AD.it.mapM (m := Id) pure).anyM (fun x => do
        match ← (pure (some x) : Id (Option Nat)) with
        | some fx => pure (.up (fx == 0))
        | none => pure (.up false))) :
    ¬ drop0% Std.Iter.any_filterMapM 5 := fun h => by
  letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
  exact hne (h (α := AD) (m := Id) (it := AD.it) (f := fun x => pure (some x)) (p := (· == 0)))

-- support for Std.Iter.any_mapM, idx 5
theorem any_mapM.h5_support
    (hne : (AD.it.mapM (m := Id) (fun x => pure (x + 1))).any (· == 0) ≠
      (AD.it.mapM (m := Id) pure).anyM (fun x => (.up <| (· == 0) ·) <$> (pure (x + 1) : Id Nat))) :
    ¬ drop0% Std.Iter.any_mapM 5 := fun h => by
  letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
  exact hne (h (α := AD) (m := Id) (it := AD.it) (f := fun x => pure (x + 1)) (p := (· == 0)))

-- support for Std.Iter.any_filterM, idx 4
theorem any_filterM.h4_support
    (hne : (AD.it.filterM (m := Id) (fun _ => pure (.up true))).any (· == 0) ≠
      (AD.it.mapM (m := Id) pure).anyM (fun x => do
        if (← (pure (.up true) : Id (ULift Bool))).down then pure (.up (x == 0)) else pure (.up false))) :
    ¬ drop0% Std.Iter.any_filterM 4 := fun h => by
  letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
  exact hne (h (α := AD) (m := Id) (it := AD.it) (f := fun _ => pure (.up true)) (p := (· == 0)))

-- support for Std.Iter.all_filterMapM, idx 5
theorem all_filterMapM.h5_support
    (hne : (AD.it.filterMapM (m := Id) (fun x => pure (some x))).all (· == 0) ≠
      (AD.it.mapM (m := Id) pure).allM (fun x => do
        match ← (pure (some x) : Id (Option Nat)) with
        | some fx => pure (.up (fx == 0))
        | none => pure (.up true))) :
    ¬ drop0% Std.Iter.all_filterMapM 5 := fun h => by
  letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
  exact hne (h (α := AD) (m := Id) (it := AD.it) (f := fun x => pure (some x)) (p := (· == 0)))

-- support for Std.Iter.all_mapM, idx 5
theorem all_mapM.h5_support
    (hne : (AD.it.mapM (m := Id) (fun x => pure (x + 1))).all (· == 0) ≠
      (AD.it.mapM (m := Id) pure).allM (fun x => (.up <| (· == 0) ·) <$> (pure (x + 1) : Id Nat))) :
    ¬ drop0% Std.Iter.all_mapM 5 := fun h => by
  letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
  exact hne (h (α := AD) (m := Id) (it := AD.it) (f := fun x => pure (x + 1)) (p := (· == 0)))

-- support for Std.Iter.all_filterM, idx 4
theorem all_filterM.h4_support
    (hne : (AD.it.filterM (m := Id) (fun _ => pure (.up true))).all (· == 0) ≠
      (AD.it.mapM (m := Id) pure).allM (fun x => do
        if (← (pure (.up true) : Id (ULift Bool))).down then pure (.up (x == 0)) else pure (.up true))) :
    ¬ drop0% Std.Iter.all_filterM 4 := fun h => by
  letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
  exact hne (h (α := AD) (m := Id) (it := AD.it) (f := fun _ => pure (.up true)) (p := (· == 0)))

end OpD1Hand
