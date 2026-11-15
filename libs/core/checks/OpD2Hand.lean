import Lean

/-!
Hand pass `OpD2` (hand10): 52 `[Finite α m]` hypotheses of `Init.Data.Iterators` lemmas that compare
a consumer (`forIn`, `foldM`, `fold`, `anyM`/`any`, `allM`/`all`, `length`, `drain`) of a combinator
iterator (`filterMap(M)`, `map(M)`, `filter(M)`, `…WithPostcondition`, `attachWith`, `uLift`) or a
collector (`toList`, `toListRev`) with a consumer of the base iterator. For hypothesis `hᵢ` of
theorem `T` this file proves `¬T'` (`drop0% T i`, universes set to `0`).

46 necessary, 0 removable, 6 independent (`runs/hand10/OpD2_independent.jsonl`, support lemmas
`*_support` at the end).

Construction (two vacuously lawful base loops, a variant of the anti-diagonal technique):
* `LP`: iterator whose every state skips to itself (`Iterator LP m Nat` for any `[Pure m]`), not
  `Finite` (`LP.not_finite`); `IteratorLoop.WellFounded LP m Pl` fails for every `Pl`
  (`LP.not_wf`: the skip step relates `(it, c)` to itself).
* Hence every `IteratorLoop LP m n` instance is `LawfulIteratorLoop` (the law only applies under
  `WellFounded`): `OL b : IteratorLoop LP Option Option` returns `some init` (`b = true`) or `none`
  (`b = false`) without iterating, `OL.lawful b`; `EL b : IteratorLoop LP Id Id` returns `init` or
  `Classical.epsilon (· ≠ init)`, `EL.lawful b`.
* The combinator side uses the combinator's own `IteratorLoop` instance (`.defaultImplementation`,
  an `extrinsicFix₃` that is opaque on the non-well-founded loop) and the collector side uses
  `extrinsicFix`; neither mentions the theorem's base `IteratorLoop` variable. Instantiating `T'`
  twice at the same data, once with `OL true`/`EL true` and once with `OL false`/`EL false`, gives
  `opaque = base₁` and `opaque = base₂` with the identical opaque term, so `base₁ = base₂`, which
  `decide` (resp. `EL.length_ne`) refutes. The opaque value is never named or evaluated.
* Monads: `m = n = o = Option` (lawful, `LawfulMonadAttach`, reflexive lifts), base state `lp`;
  the pure `Iter` lemmas and `IterM.length_uLift` use `Id` and `EL`, base state `lpi`/`lp`.

Independent (6): `IterM.any_{filterMapM,mapM,filterM}` and `IterM.all_{filterMapM,mapM,filterM}`.
Both sides are loops over combinator iterators (`it.filterMapM f` etc. vs. `it.mapM pure`); the
base loop `[IteratorLoop α m m]` occurs only as a binder, so there is nothing to control.

Run with the lean4 repo's stage1 binary: `lean checks/OpD2Hand.lean`.
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


namespace OpD2Hand
open Std Std.Iterators

theorem wf_irrefl {α : Sort u} {r : α → α → Prop} (h : WellFounded r) (a : α) : ¬ r a a := by
  have := h.apply a
  induction this with
  | intro x _ ih => exact fun hx => ih x hx hx

structure LP where u : Unit

instance LP.inst {m : Type → Type} [Pure m] : Iterator LP m Nat where
  IsPlausibleStep it s := s = .skip it
  step it := pure (.deflate ⟨.skip it, rfl⟩)

theorem LP.not_finite {m : Type → Type} [Pure m] : ¬ Finite LP m :=
  fun h => wf_irrefl h.wf ⟨⟨()⟩⟩ ⟨_, rfl, rfl⟩

theorem LP.not_wf {m : Type → Type} [Pure m] {γ : Type} (Pl : Nat → γ → ForInStep γ → Prop) (c : γ) :
    ¬ IteratorLoop.WellFounded LP m Pl :=
  fun h => wf_irrefl h (⟨⟨()⟩⟩, c) (Or.inr ⟨rfl, rfl⟩)

@[instance_reducible] def OL (b : Bool) : IteratorLoop LP Option Option.{0} :=
  ⟨fun _ _ _ _ init _ => if b then some init else none⟩

theorem OL.lawful (b : Bool) : @LawfulIteratorLoop _ LP Option Option.{0} _ _ _ (OL b) :=
  @LawfulIteratorLoop.mk _ LP Option Option.{0} _ _ _ (OL b) (fun _ _ _ _ init Pl wf _ => absurd wf (LP.not_wf Pl init))

abbrev lp {m : Type → Type} : IterM (α := LP) m Nat := ⟨⟨()⟩⟩

abbrev lpi : Iter (α := LP) Nat := ⟨⟨()⟩⟩

@[instance_reducible] noncomputable def EL (b : Bool) : IteratorLoop LP Id Id.{0} :=
  ⟨fun _ γ _ _ init _ => if b then init else @Classical.epsilon γ ⟨init⟩ (· ≠ init)⟩

theorem EL.lawful (b : Bool) : @LawfulIteratorLoop _ LP Id Id.{0} _ _ _ (EL b) :=
  @LawfulIteratorLoop.mk _ LP Id Id.{0} _ _ _ (EL b) (fun _ _ _ _ init Pl wf _ => absurd wf (LP.not_wf Pl init))

theorem eps_ne {γ : Type} (init x : γ) (hx : x ≠ init) : @Classical.epsilon γ ⟨init⟩ (· ≠ init) ≠ init :=
  Classical.epsilon_spec (p := (· ≠ init)) ⟨x, hx⟩

theorem EL.length_ne : (0 : Nat) ≠ (@Classical.epsilon (ULift.{0} Nat) ⟨.up 0⟩ (· ≠ .up 0)).down := fun e =>
  eps_ne (ULift.up 0) (ULift.up 1) (by simp) (ULift.ext e.symm)



/-! Refutations -/

-- `Std.Iter.length_attachWith`, idx 6 (inst): base `LP` skips forever; base side length 0 (`EL true`) vs. epsilon ≠ 0 (`EL false`), combinator side is the same term
theorem Iter.length_attachWith.h6 : ¬ drop0% Std.Iter.length_attachWith 6 := fun h => by
  have h1 := @h LP Nat (fun _ => True) _ lpi (fun _ _ => trivial) (EL true) (EL.lawful true)
  have h2 := @h LP Nat (fun _ => True) _ lpi (fun _ _ => trivial) (EL false) (EL.lawful false)
  exact EL.length_ne (h1.symm.trans h2)

-- `Std.Iter.length_map`, idx 5 (inst): base `LP` skips forever; base side length 0 (`EL true`) vs. epsilon ≠ 0 (`EL false`), combinator side is the same term
theorem Iter.length_map.h5 : ¬ drop0% Std.Iter.length_map 5 := fun h => by
  have h1 := @h LP Nat Nat _ (EL true) (EL.lawful true) lpi (fun _ => default)
  have h2 := @h LP Nat Nat _ (EL false) (EL.lawful false) lpi (fun _ => default)
  exact EL.length_ne (h1.symm.trans h2)

-- `Std.IterM.length_attachWith`, idx 10 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.length_attachWith.h10 : ¬ drop0% Std.IterM.length_attachWith 10 := fun h => by
  have h1 := @h LP Option Nat (fun _ => True) Option _ _ _ lp (fun _ _ => trivial) (OL true) _ (OL.lawful true)
  have h2 := @h LP Option Nat (fun _ => True) Option _ _ _ lp (fun _ _ => trivial) (OL false) _ (OL.lawful false)
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.forIn_filterMapWithPostcondition`, idx 18 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.forIn_filterMapWithPostcondition.h18 : ¬ drop0% Std.IterM.forIn_filterMapWithPostcondition 18 := fun h => by
  have h1 := @h Option Option Option LP Nat Nat Nat _ _ _ _ _ _ _ _ _ _ _ (OL true) (OL.lawful true) lp (fun _ => pure default) 0 (fun _ acc => pure (.yield acc))
  have h2 := @h Option Option Option LP Nat Nat Nat _ _ _ _ _ _ _ _ _ _ _ (OL false) (OL.lawful false) lp (fun _ => pure default) 0 (fun _ acc => pure (.yield acc))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.forIn_filterMapM`, idx 20 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.forIn_filterMapM.h20 : ¬ drop0% Std.IterM.forIn_filterMapM 20 := fun h => by
  have h1 := @h Option Option Option LP Nat Nat Nat _ _ _ _ _ _ _ _ _ _ _ _ _ (OL true) (OL.lawful true) lp (fun _ => pure default) 0 (fun _ acc => pure (.yield acc))
  have h2 := @h Option Option Option LP Nat Nat Nat _ _ _ _ _ _ _ _ _ _ _ _ _ (OL false) (OL.lawful false) lp (fun _ => pure default) 0 (fun _ acc => pure (.yield acc))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.forIn_filterMap`, idx 13 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.forIn_filterMap.h13 : ¬ drop0% Std.IterM.forIn_filterMap 13 := fun h => by
  have h1 := @h Option Option LP Nat Nat Nat _ _ _ _ _ _ _ (OL true) (OL.lawful true) lp (fun _ => default) 0 (fun _ acc => pure (.yield acc))
  have h2 := @h Option Option LP Nat Nat Nat _ _ _ _ _ _ _ (OL false) (OL.lawful false) lp (fun _ => default) 0 (fun _ acc => pure (.yield acc))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.forIn_mapWithPostcondition`, idx 18 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.forIn_mapWithPostcondition.h18 : ¬ drop0% Std.IterM.forIn_mapWithPostcondition 18 := fun h => by
  have h1 := @h Option Option Option LP Nat Nat Nat _ _ _ _ _ _ _ _ _ _ _ (OL true) (OL.lawful true) lp (fun _ => pure default) 0 (fun _ acc => pure (.yield acc))
  have h2 := @h Option Option Option LP Nat Nat Nat _ _ _ _ _ _ _ _ _ _ _ (OL false) (OL.lawful false) lp (fun _ => pure default) 0 (fun _ acc => pure (.yield acc))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.forIn_mapM`, idx 20 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.forIn_mapM.h20 : ¬ drop0% Std.IterM.forIn_mapM 20 := fun h => by
  have h1 := @h Option Option Option LP Nat Nat Nat _ _ _ _ _ _ _ _ _ _ _ _ _ (OL true) (OL.lawful true) lp (fun _ => pure default) 0 (fun _ acc => pure (.yield acc))
  have h2 := @h Option Option Option LP Nat Nat Nat _ _ _ _ _ _ _ _ _ _ _ _ _ (OL false) (OL.lawful false) lp (fun _ => pure default) 0 (fun _ acc => pure (.yield acc))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.forIn_map`, idx 13 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.forIn_map.h13 : ¬ drop0% Std.IterM.forIn_map 13 := fun h => by
  have h1 := @h Option Option LP Nat Nat Nat _ _ _ _ _ _ _ (OL true) (OL.lawful true) lp (fun _ => default) 0 (fun _ acc => pure (.yield acc))
  have h2 := @h Option Option LP Nat Nat Nat _ _ _ _ _ _ _ (OL false) (OL.lawful false) lp (fun _ => default) 0 (fun _ acc => pure (.yield acc))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.forIn_filterWithPostcondition`, idx 17 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.forIn_filterWithPostcondition.h17 : ¬ drop0% Std.IterM.forIn_filterWithPostcondition 17 := fun h => by
  have h1 := @h Option Option Option LP Nat Nat _ _ _ _ _ _ _ _ _ _ _ (OL true) (OL.lawful true) lp (fun _ => pure default) 0 (fun _ acc => pure (.yield acc))
  have h2 := @h Option Option Option LP Nat Nat _ _ _ _ _ _ _ _ _ _ _ (OL false) (OL.lawful false) lp (fun _ => pure default) 0 (fun _ acc => pure (.yield acc))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.forIn_filterM`, idx 19 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.forIn_filterM.h19 : ¬ drop0% Std.IterM.forIn_filterM 19 := fun h => by
  have h1 := @h Option Option Option LP Nat Nat _ _ _ _ _ _ _ _ _ _ _ _ _ (OL true) (OL.lawful true) lp (fun _ => pure default) 0 (fun _ acc => pure (.yield acc))
  have h2 := @h Option Option Option LP Nat Nat _ _ _ _ _ _ _ _ _ _ _ _ _ (OL false) (OL.lawful false) lp (fun _ => pure default) 0 (fun _ acc => pure (.yield acc))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.forIn_filter`, idx 12 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.forIn_filter.h12 : ¬ drop0% Std.IterM.forIn_filter 12 := fun h => by
  have h1 := @h Option Option LP Nat Nat _ _ _ _ _ _ _ (OL true) (OL.lawful true) lp (fun _ => default) 0 (fun _ acc => pure (.yield acc))
  have h2 := @h Option Option LP Nat Nat _ _ _ _ _ _ _ (OL false) (OL.lawful false) lp (fun _ => default) 0 (fun _ acc => pure (.yield acc))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.foldM_filterMapWithPostcondition`, idx 8 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.foldM_filterMapWithPostcondition.h8 : ¬ drop0% Std.IterM.foldM_filterMapWithPostcondition 8 := fun h => by
  have h1 := @h LP Nat Nat Nat Option Option Option _ _ _ _ _ _ _ (OL true) (OL true) (OL.lawful true) (OL.lawful true) _ _ _ _ (fun _ => pure default) (fun d _ => pure d) 0 lp
  have h2 := @h LP Nat Nat Nat Option Option Option _ _ _ _ _ _ _ (OL false) (OL false) (OL.lawful false) (OL.lawful false) _ _ _ _ (fun _ => pure default) (fun d _ => pure d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.foldM_filterMapM`, idx 8 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.foldM_filterMapM.h8 : ¬ drop0% Std.IterM.foldM_filterMapM 8 := fun h => by
  have h1 := @h LP Nat Nat Nat Option Option Option _ _ _ _ _ _ _ _ _ (OL true) (OL true) (OL.lawful true) (OL.lawful true) _ _ _ _ (fun _ => pure default) (fun d _ => pure d) 0 lp
  have h2 := @h LP Nat Nat Nat Option Option Option _ _ _ _ _ _ _ _ _ (OL false) (OL false) (OL.lawful false) (OL.lawful false) _ _ _ _ (fun _ => pure default) (fun d _ => pure d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.foldM_mapWithPostcondition`, idx 8 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.foldM_mapWithPostcondition.h8 : ¬ drop0% Std.IterM.foldM_mapWithPostcondition 8 := fun h => by
  have h1 := @h LP Nat Nat Nat Option Option Option _ _ _ _ _ _ _ (OL true) (OL true) (OL.lawful true) (OL.lawful true) _ _ _ _ (fun _ => pure default) (fun d _ => pure d) 0 lp
  have h2 := @h LP Nat Nat Nat Option Option Option _ _ _ _ _ _ _ (OL false) (OL false) (OL.lawful false) (OL.lawful false) _ _ _ _ (fun _ => pure default) (fun d _ => pure d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.foldM_mapM`, idx 8 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.foldM_mapM.h8 : ¬ drop0% Std.IterM.foldM_mapM 8 := fun h => by
  have h1 := @h LP Nat Nat Nat Option Option Option _ _ _ _ _ _ _ _ _ (OL true) (OL true) (OL.lawful true) (OL.lawful true) _ _ _ _ (fun _ => pure default) (fun d _ => pure d) 0 lp
  have h2 := @h LP Nat Nat Nat Option Option Option _ _ _ _ _ _ _ _ _ (OL false) (OL false) (OL.lawful false) (OL.lawful false) _ _ _ _ (fun _ => pure default) (fun d _ => pure d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.foldM_filterWithPostcondition`, idx 7 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.foldM_filterWithPostcondition.h7 : ¬ drop0% Std.IterM.foldM_filterWithPostcondition 7 := fun h => by
  have h1 := @h LP Nat Nat Option Option Option _ _ _ _ _ _ _ (OL true) (OL true) (OL.lawful true) (OL.lawful true) _ _ _ _ (fun _ => pure default) (fun d _ => pure d) 0 lp
  have h2 := @h LP Nat Nat Option Option Option _ _ _ _ _ _ _ (OL false) (OL false) (OL.lawful false) (OL.lawful false) _ _ _ _ (fun _ => pure default) (fun d _ => pure d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.foldM_filterM`, idx 7 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.foldM_filterM.h7 : ¬ drop0% Std.IterM.foldM_filterM 7 := fun h => by
  have h1 := @h LP Nat Nat Option Option Option _ _ _ _ _ _ _ _ _ (OL true) (OL true) (OL.lawful true) (OL.lawful true) _ _ _ _ (fun _ => pure default) (fun d _ => pure d) 0 lp
  have h2 := @h LP Nat Nat Option Option Option _ _ _ _ _ _ _ _ _ (OL false) (OL false) (OL.lawful false) (OL.lawful false) _ _ _ _ (fun _ => pure default) (fun d _ => pure d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.foldM_filterMap`, idx 7 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.foldM_filterMap.h7 : ¬ drop0% Std.IterM.foldM_filterMap 7 := fun h => by
  have h1 := @h LP Nat Nat Nat Option Option _ _ _ _ _ (OL true) (OL.lawful true) _ _ (fun _ => default) (fun d _ => pure d) 0 lp
  have h2 := @h LP Nat Nat Nat Option Option _ _ _ _ _ (OL false) (OL.lawful false) _ _ (fun _ => default) (fun d _ => pure d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.foldM_map`, idx 7 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.foldM_map.h7 : ¬ drop0% Std.IterM.foldM_map 7 := fun h => by
  have h1 := @h LP Nat Nat Nat Option Option _ _ _ _ _ (OL true) (OL.lawful true) _ _ (fun _ => default) (fun d _ => pure d) 0 lp
  have h2 := @h LP Nat Nat Nat Option Option _ _ _ _ _ (OL false) (OL.lawful false) _ _ (fun _ => default) (fun d _ => pure d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.foldM_filter`, idx 6 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.foldM_filter.h6 : ¬ drop0% Std.IterM.foldM_filter 6 := fun h => by
  have h1 := @h LP Nat Nat Option Option _ _ _ _ _ (OL true) (OL.lawful true) _ _ (fun _ => default) (fun d _ => pure d) 0 lp
  have h2 := @h LP Nat Nat Option Option _ _ _ _ _ (OL false) (OL.lawful false) _ _ (fun _ => default) (fun d _ => pure d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.fold_filterMapWithPostcondition`, idx 7 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.fold_filterMapWithPostcondition.h7 : ¬ drop0% Std.IterM.fold_filterMapWithPostcondition 7 := fun h => by
  have h1 := @h LP Nat Nat Nat Option Option _ _ _ _ _ (OL true) (OL.lawful true) _ _ (fun _ => pure default) (fun d _ => d) 0 lp
  have h2 := @h LP Nat Nat Nat Option Option _ _ _ _ _ (OL false) (OL.lawful false) _ _ (fun _ => pure default) (fun d _ => d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.fold_filterMapM`, idx 7 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.fold_filterMapM.h7 : ¬ drop0% Std.IterM.fold_filterMapM 7 := fun h => by
  have h1 := @h LP Nat Nat Nat Option Option _ _ _ _ _ _ _ (OL true) (OL.lawful true) _ _ (fun _ => pure default) (fun d _ => d) 0 lp
  have h2 := @h LP Nat Nat Nat Option Option _ _ _ _ _ _ _ (OL false) (OL.lawful false) _ _ (fun _ => pure default) (fun d _ => d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.fold_mapWithPostcondition`, idx 7 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.fold_mapWithPostcondition.h7 : ¬ drop0% Std.IterM.fold_mapWithPostcondition 7 := fun h => by
  have h1 := @h LP Nat Nat Nat Option Option _ _ _ _ _ (OL true) (OL.lawful true) _ _ (fun _ => pure default) (fun d _ => d) 0 lp
  have h2 := @h LP Nat Nat Nat Option Option _ _ _ _ _ (OL false) (OL.lawful false) _ _ (fun _ => pure default) (fun d _ => d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.fold_mapM`, idx 7 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.fold_mapM.h7 : ¬ drop0% Std.IterM.fold_mapM 7 := fun h => by
  have h1 := @h LP Nat Nat Nat Option Option _ _ _ _ _ _ _ (OL true) (OL.lawful true) _ _ (fun _ => pure default) (fun d _ => d) 0 lp
  have h2 := @h LP Nat Nat Nat Option Option _ _ _ _ _ _ _ (OL false) (OL.lawful false) _ _ (fun _ => pure default) (fun d _ => d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.fold_filterWithPostcondition`, idx 6 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.fold_filterWithPostcondition.h6 : ¬ drop0% Std.IterM.fold_filterWithPostcondition 6 := fun h => by
  have h1 := @h LP Nat Nat Option Option _ _ _ _ _ (OL true) (OL.lawful true) _ _ (fun _ => pure default) (fun d _ => d) 0 lp
  have h2 := @h LP Nat Nat Option Option _ _ _ _ _ (OL false) (OL.lawful false) _ _ (fun _ => pure default) (fun d _ => d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.fold_filterM`, idx 6 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.fold_filterM.h6 : ¬ drop0% Std.IterM.fold_filterM 6 := fun h => by
  have h1 := @h LP Nat Nat Option Option _ _ _ _ _ _ _ (OL true) (OL.lawful true) _ _ (fun _ => pure default) (fun d _ => d) 0 lp
  have h2 := @h LP Nat Nat Option Option _ _ _ _ _ _ _ (OL false) (OL.lawful false) _ _ (fun _ => pure default) (fun d _ => d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.fold_filterMap`, idx 6 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.fold_filterMap.h6 : ¬ drop0% Std.IterM.fold_filterMap 6 := fun h => by
  have h1 := @h LP Nat Nat Nat Option _ _ _ (OL true) (OL.lawful true) (fun _ => default) (fun d _ => d) 0 lp
  have h2 := @h LP Nat Nat Nat Option _ _ _ (OL false) (OL.lawful false) (fun _ => default) (fun d _ => d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.fold_map`, idx 6 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.fold_map.h6 : ¬ drop0% Std.IterM.fold_map 6 := fun h => by
  have h1 := @h LP Nat Nat Nat Option _ _ _ (OL true) (OL.lawful true) (fun _ => default) (fun d _ => d) 0 lp
  have h2 := @h LP Nat Nat Nat Option _ _ _ (OL false) (OL.lawful false) (fun _ => default) (fun d _ => d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.fold_filter`, idx 5 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.fold_filter.h5 : ¬ drop0% Std.IterM.fold_filter 5 := fun h => by
  have h1 := @h LP Nat Nat Option _ _ _ (OL true) (OL.lawful true) (fun _ => default) (fun d _ => d) 0 lp
  have h2 := @h LP Nat Nat Option _ _ _ (OL false) (OL.lawful false) (fun _ => default) (fun d _ => d) 0 lp
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.length_map`, idx 7 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.length_map.h7 : ¬ drop0% Std.IterM.length_map 7 := fun h => by
  have h1 := @h LP Nat Nat Option _ _ (OL true) _ (OL.lawful true) lp (fun _ => default)
  have h2 := @h LP Nat Nat Option _ _ (OL false) _ (OL.lawful false) lp (fun _ => default)
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.anyM_filterMap`, idx 5 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.anyM_filterMap.h5 : ¬ drop0% Std.IterM.anyM_filterMap 5 := fun h => by
  have h1 := @h LP Nat Nat Option _ _ (OL true) _ (OL.lawful true) lp (fun _ => default) (fun _ => pure default)
  have h2 := @h LP Nat Nat Option _ _ (OL false) _ (OL.lawful false) lp (fun _ => default) (fun _ => pure default)
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.anyM_map`, idx 5 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.anyM_map.h5 : ¬ drop0% Std.IterM.anyM_map 5 := fun h => by
  have h1 := @h LP Nat Nat Option _ _ (OL true) _ (OL.lawful true) lp (fun _ => default) (fun _ => pure default)
  have h2 := @h LP Nat Nat Option _ _ (OL false) _ (OL.lawful false) lp (fun _ => default) (fun _ => pure default)
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.anyM_filter`, idx 4 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.anyM_filter.h4 : ¬ drop0% Std.IterM.anyM_filter 4 := fun h => by
  have h1 := @h LP Nat Option _ _ (OL true) _ (OL.lawful true) lp (fun _ => default) (fun _ => pure default)
  have h2 := @h LP Nat Option _ _ (OL false) _ (OL.lawful false) lp (fun _ => default) (fun _ => pure default)
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.any_filterMap`, idx 5 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.any_filterMap.h5 : ¬ drop0% Std.IterM.any_filterMap 5 := fun h => by
  have h1 := @h LP Nat Nat Option _ _ (OL true) _ (OL.lawful true) lp (fun _ => default) (fun _ => default)
  have h2 := @h LP Nat Nat Option _ _ (OL false) _ (OL.lawful false) lp (fun _ => default) (fun _ => default)
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.any_map`, idx 5 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.any_map.h5 : ¬ drop0% Std.IterM.any_map 5 := fun h => by
  have h1 := @h LP Nat Nat Option _ _ (OL true) _ (OL.lawful true) lp (fun _ => default) (fun _ => default)
  have h2 := @h LP Nat Nat Option _ _ (OL false) _ (OL.lawful false) lp (fun _ => default) (fun _ => default)
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.allM_filterMap`, idx 5 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.allM_filterMap.h5 : ¬ drop0% Std.IterM.allM_filterMap 5 := fun h => by
  have h1 := @h LP Nat Nat Option _ _ (OL true) _ (OL.lawful true) lp (fun _ => default) (fun _ => pure default)
  have h2 := @h LP Nat Nat Option _ _ (OL false) _ (OL.lawful false) lp (fun _ => default) (fun _ => pure default)
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.allM_map`, idx 5 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.allM_map.h5 : ¬ drop0% Std.IterM.allM_map 5 := fun h => by
  have h1 := @h LP Nat Nat Option _ _ (OL true) _ (OL.lawful true) lp (fun _ => default) (fun _ => pure default)
  have h2 := @h LP Nat Nat Option _ _ (OL false) _ (OL.lawful false) lp (fun _ => default) (fun _ => pure default)
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.allM_filter`, idx 4 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.allM_filter.h4 : ¬ drop0% Std.IterM.allM_filter 4 := fun h => by
  have h1 := @h LP Nat Option _ _ (OL true) _ (OL.lawful true) lp (fun _ => default) (fun _ => pure default)
  have h2 := @h LP Nat Option _ _ (OL false) _ (OL.lawful false) lp (fun _ => default) (fun _ => pure default)
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.all_filterMap`, idx 5 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.all_filterMap.h5 : ¬ drop0% Std.IterM.all_filterMap 5 := fun h => by
  have h1 := @h LP Nat Nat Option _ _ (OL true) _ (OL.lawful true) lp (fun _ => default) (fun _ => default)
  have h2 := @h LP Nat Nat Option _ _ (OL false) _ (OL.lawful false) lp (fun _ => default) (fun _ => default)
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.all_map`, idx 5 (inst): base `LP` skips forever; base side `some init` (`OL true`) vs. `none` (`OL false`), combinator side is the same term
theorem IterM.all_map.h5 : ¬ drop0% Std.IterM.all_map 5 := fun h => by
  have h1 := @h LP Nat Nat Option _ _ (OL true) _ (OL.lawful true) lp (fun _ => default) (fun _ => default)
  have h2 := @h LP Nat Nat Option _ _ (OL false) _ (OL.lawful false) lp (fun _ => default) (fun _ => default)
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.IterM.length_uLift`, idx 9 (inst): base `LP` skips forever; base side length 0 (`EL true`) vs. epsilon ≠ 0 (`EL false`), combinator side is the same term
theorem IterM.length_uLift.h9 : ¬ drop0% Std.IterM.length_uLift 9 := fun h => by
  have h1 := @h LP Id Id Nat _ _ _ lp _ (EL true) _ _ (EL.lawful true) _
  have h2 := @h LP Id Id Nat _ _ _ lp _ (EL false) _ _ (EL.lawful false) _
  exact EL.length_ne (congrArg ULift.down (h1.symm.trans h2))

-- `Std.Iter.length_uLift`, idx 4 (inst): base `LP` skips forever; base side length 0 (`EL true`) vs. epsilon ≠ 0 (`EL false`), combinator side is the same term
theorem Iter.length_uLift.h4 : ¬ drop0% Std.Iter.length_uLift 4 := fun h => by
  have h1 := @h LP Nat _ lpi (EL true) (EL.lawful true)
  have h2 := @h LP Nat _ lpi (EL false) (EL.lawful false)
  exact EL.length_ne (h1.symm.trans h2)

-- `Std.IterM.drain_eq_map_toList`, idx 4 (inst): base `LP` skips forever; `drain` runs the base loop (some () vs. none), the collector side is the same term
theorem IterM.drain_eq_map_toList.h4 : ¬ drop0% Std.IterM.drain_eq_map_toList 4 := fun h => by
  have h1 := @h LP Nat Option _ _ _ (OL true) (OL.lawful true) lp
  have h2 := @h LP Nat Option _ _ _ (OL false) (OL.lawful false) lp
  exact absurd (h1.trans h2.symm) (by decide)

-- `Std.IterM.drain_eq_map_toListRev`, idx 4 (inst): base `LP` skips forever; `drain` runs the base loop (some () vs. none), the collector side is the same term
theorem IterM.drain_eq_map_toListRev.h4 : ¬ drop0% Std.IterM.drain_eq_map_toListRev 4 := fun h => by
  have h1 := @h LP Nat Option _ _ _ (OL true) (OL.lawful true) lp
  have h2 := @h LP Nat Option _ _ _ (OL false) (OL.lawful false) lp
  exact absurd (h1.trans h2.symm) (by decide)

-- `Std.IterM.drain_eq_map_toArray`, idx 4 (inst): base `LP` skips forever; `drain` runs the base loop (some () vs. none), the collector side is the same term
theorem IterM.drain_eq_map_toArray.h4 : ¬ drop0% Std.IterM.drain_eq_map_toArray 4 := fun h => by
  have h1 := @h LP Nat Option _ _ _ (OL true) (OL.lawful true) lp
  have h2 := @h LP Nat Option _ _ _ (OL false) (OL.lawful false) lp
  exact absurd (h1.trans h2.symm) (by decide)

/-! Support for the independent rows: at `LP`/`Option` the instance of `T'` is exactly the
equation between two opaque `extrinsicFix₃` values at different arguments, so `¬T'` follows from
any interpretation of `opaqueFix₃` in which they differ. -/

-- support for Std.IterM.any_filterMapM, idx 6: at `LP`/`Option` the instance of T' is the equation between two opaque values
theorem IterM.any_filterMapM.h6_support
    (hne : (lp.filterMapM (m := Option) (n := Option) (fun (_ : Nat) => (pure none : Option (Option Nat)))).any (fun (_ : Nat) => false) ≠
      (lp.mapM (m := Option) (pure (f := Option))).anyM (fun x => do match ← (pure none : Option (Option Nat)) with | some fx => return .up ((fun (_ : Nat) => false) fx) | none => return .up false)) :
    ¬ drop0% Std.IterM.any_filterMapM 6 := fun h =>
  hne (@h LP Nat Nat Option Option _ _ (OL true) _ _ _ _ _ _ _ (OL.lawful true) lp (fun _ => pure none) (fun _ => false))

-- support for Std.IterM.any_mapM, idx 6: at `LP`/`Option` the instance of T' is the equation between two opaque values
theorem IterM.any_mapM.h6_support
    (hne : (lp.mapM (m := Option) (n := Option) (fun (_ : Nat) => (pure 0 : Option Nat))).any (fun (_ : Nat) => false) ≠
      (lp.mapM (m := Option) (pure (f := Option))).anyM (fun x => (.up <| (fun (_ : Nat) => false) ·) <$> ((fun (_ : Nat) => (pure 0 : Option Nat)) x))) :
    ¬ drop0% Std.IterM.any_mapM 6 := fun h =>
  hne (@h LP Nat Nat Option Option _ _ (OL true) _ _ _ _ _ _ _ (OL.lawful true) lp (fun _ => pure 0) (fun _ => false))

-- support for Std.IterM.any_filterM, idx 5: at `LP`/`Option` the instance of T' is the equation between two opaque values
theorem IterM.any_filterM.h5_support
    (hne : (lp.filterM (m := Option) (n := Option) (fun (_ : Nat) => (pure (.up false) : Option (ULift Bool)))).any (fun (_ : Nat) => false) ≠
      (lp.mapM (m := Option) (pure (f := Option))).anyM (fun x => do if (← (pure (.up false) : Option (ULift Bool))).down then return .up ((fun (_ : Nat) => false) x) else return .up false)) :
    ¬ drop0% Std.IterM.any_filterM 5 := fun h =>
  hne (@h LP Nat Option Option _ _ (OL true) _ _ _ _ _ _ _ (OL.lawful true) lp (fun _ => pure (.up false)) (fun _ => false))

-- support for Std.IterM.all_filterMapM, idx 6: at `LP`/`Option` the instance of T' is the equation between two opaque values
theorem IterM.all_filterMapM.h6_support
    (hne : (lp.filterMapM (m := Option) (n := Option) (fun (_ : Nat) => (pure none : Option (Option Nat)))).all (fun (_ : Nat) => false) ≠
      (lp.mapM (m := Option) (pure (f := Option))).allM (fun x => do match ← (pure none : Option (Option Nat)) with | some fx => return .up ((fun (_ : Nat) => false) fx) | none => return .up true)) :
    ¬ drop0% Std.IterM.all_filterMapM 6 := fun h =>
  hne (@h LP Nat Nat Option Option _ _ (OL true) _ _ _ _ _ _ _ (OL.lawful true) lp (fun _ => pure none) (fun _ => false))

-- support for Std.IterM.all_mapM, idx 6: at `LP`/`Option` the instance of T' is the equation between two opaque values
theorem IterM.all_mapM.h6_support
    (hne : (lp.mapM (m := Option) (n := Option) (fun (_ : Nat) => (pure 0 : Option Nat))).all (fun (_ : Nat) => false) ≠
      (lp.mapM (m := Option) (pure (f := Option))).allM (fun x => (.up <| (fun (_ : Nat) => false) ·) <$> ((fun (_ : Nat) => (pure 0 : Option Nat)) x))) :
    ¬ drop0% Std.IterM.all_mapM 6 := fun h =>
  hne (@h LP Nat Nat Option Option _ _ (OL true) _ _ _ _ _ _ _ (OL.lawful true) lp (fun _ => pure 0) (fun _ => false))

-- support for Std.IterM.all_filterM, idx 5: at `LP`/`Option` the instance of T' is the equation between two opaque values
theorem IterM.all_filterM.h5_support
    (hne : (lp.filterM (m := Option) (n := Option) (fun (_ : Nat) => (pure (.up false) : Option (ULift Bool)))).all (fun (_ : Nat) => false) ≠
      (lp.mapM (m := Option) (pure (f := Option))).allM (fun x => do if (← (pure (.up false) : Option (ULift Bool))).down then return .up ((fun (_ : Nat) => false) x) else return .up true)) :
    ¬ drop0% Std.IterM.all_filterM 5 := fun h =>
  hne (@h LP Nat Option Option _ _ (OL true) _ _ _ _ _ _ _ (OL.lawful true) lp (fun _ => pure (.up false)) (fun _ => false))

end OpD2Hand
