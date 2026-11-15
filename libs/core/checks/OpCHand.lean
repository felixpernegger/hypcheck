import Lean

/-!
Hand pass `OpC` (hand10): 40 `[Finite α m]` hypotheses of `Init.Data.Iterators` consumer lemmas
(`Lemmas.Consumers.Loop`, `Lemmas.Consumers.Monadic.Loop`) whose conclusion goes through the
theorem's own variable `IteratorLoop` instance on the base iterator. For hypothesis `hᵢ` of `T`
this file proves `¬T'` (`drop0% T i`).

40 necessary, 0 removable, 0 independent, 0 opaque.

Key fact (technique 4 of the brief): `LawfulIteratorLoop` only constrains a loop under
`IteratorLoop.WellFounded`, and on an iterator that may skip to itself no loop relation is
well-founded. So on such a base iterator *every* `IteratorLoop` instance is lawful, and a side that
goes through the variable loop instance is fully controllable, whatever the opaque
(`opaqueFix`) collectors `toList`/`toArray`/`toListRev` or `DefaultConsumers.forIn'` evaluate to.

Two-loop trick (replaces the anti-diagonal loop of technique 5; reusable by the OpD agents): if one
side of `T'` does not depend on the variable loop instance (an opaque collector such as
`it.toList.foldlM f init`, or `IterM.DefaultConsumers.forIn'`, or a combinator's default loop),
instantiate `T'` twice on the same non-finite iterator, with `fnLoop keep` (returns `init`) and with
`fnLoop other` (returns some value `≠ init`). Both are lawful, the loop-independent side is the same
term in both instances, so `init = other init`, contradicting `other_ne`. No value of the opaque
side is needed. (`checks/OpD1Hand.lean` uses the same idea with `ADLoop 0`/`ADLoop 1`.)
When both sides go through the same variable loop (`allM_eq_not_anyM_not`, `IterM.fold_hom`),
`fnLoop pick` (a fixed value per type, ignoring `init` and the body) gives `c = !c` resp.
`c = c + 1`; when they use it at different types (`IterM.forIn_eq_foldM`: `γ` vs `ForInStep γ`),
`SL.triLoop` tests the type (`Two γ`: at most two elements) and applies the body once otherwise.
With two loop binders (`Iter.fold_hom`, `length_eq_fold`, `length_eq_forIn` at universes `0`) one
instantiation with `keep`/`other` suffices.

Reusable counterexamples (section "Models"):
* `SL`: iterator `Iterator SL Id Nat` whose states may skip to themselves or yield `0`; `step`
  skips. `SL.not_finite`, `SL.not_productive`, `SL.not_wf` (no loop relation is well-founded),
  `SL.out` (`0` is a plausible output of every state), `SL.lawful i` (every
  `i : IteratorLoop SL Id n` is lawful), `itM`/`itS` (the iterator as `IterM`/`Iter`).
* `SL.fnLoop g` (returns `g γ init`) with `keep`, `other` (`other_ne`), `pick`;
  `SL.triLoop` (`SL.triLoop_pos`, `SL.triLoop_neg`, `two_bool`, `not_two_forInStep`).
Evaluation: the loop side reduces by unfolding (`exact` up to defeq), except `triLoop`, which needs
`simp only [ForIn.forIn, ForIn'.forIn', Iter.foldM]` and the `triLoop_pos`/`triLoop_neg` rewrites.

Run with the lean4 repo's stage1 binary: `lean checks/OpCHand.lean`.
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



namespace OpCHand
open Std Std.Iterators

/-! ## Models -/

theorem acc_not_self {α : Sort _} {r : α → α → Prop} {x : α} (h : Acc r x) : ¬ r x x := by
  induction h with | intro x _ ih => exact fun hxx => ih x hxx hxx

/-- Self-loop iterator: every state may skip to itself or yield `0` and stay; `step` skips. -/
structure SL where u : Unit

instance SL.inst : Iterator SL Id Nat where
  IsPlausibleStep it st := st = .skip it ∨ st = .yield it 0
  step it := pure (.deflate ⟨.skip it, Or.inl rfl⟩)

/-- The iterator, as `IterM` and as `Iter`. -/
def itM : IterM (α := SL) Id Nat := ⟨⟨()⟩⟩
def itS : Iter (α := SL) Nat := ⟨⟨()⟩⟩

theorem SL.not_finite : ¬ Finite SL Id := fun hf =>
  acc_not_self (hf.wf.apply itM) ⟨.skip itM, rfl, Or.inl rfl⟩

theorem SL.not_productive : ¬ Productive SL Id := fun hp =>
  acc_not_self (hp.wf.apply itM) (Or.inl rfl)

/-- No loop over `SL` is well-founded: `(it, c)` is related to itself by the skip. -/
theorem SL.not_wf {γ : Type} (Pl : Nat → γ → ForInStep γ → Prop) (c : γ) :
    ¬ IteratorLoop.WellFounded SL Id Pl := fun wf =>
  acc_not_self (wf.apply (itM, c)) (Or.inr ⟨Or.inl rfl, rfl⟩)

theorem SL.out (it : IterM (α := SL) Id Nat) : it.IsPlausibleIndirectOutput 0 :=
  .direct ⟨it, Or.inr rfl⟩

/-- Every `IteratorLoop` instance over `SL` is lawful (vacuously: no loop is well-founded). -/
theorem SL.lawful {n : Type → Type} [Monad n] (i : IteratorLoop SL Id n) :
    @LawfulIteratorLoop Nat SL Id n _ _ _ i :=
  @LawfulIteratorLoop.mk Nat SL Id n _ _ _ i
    (fun _ _ _ _ init Pl wf _ => absurd wf (SL.not_wf Pl init))

/-- Loop that ignores the iterator and the body and returns `g γ init`. -/
def SL.fnLoop (g : ∀ γ : Type, γ → γ) : IteratorLoop SL Id Id := ⟨fun _ γ _ _ init _ => g γ init⟩

def keep (γ : Type) (x : γ) : γ := x
/-- Some value other than `x` (if there is one). -/
noncomputable def other (γ : Type) (x : γ) : γ := @Classical.epsilon γ ⟨x⟩ (· ≠ x)
/-- A fixed value of `γ`, independent of `x` (`pick γ x = pick γ y` by `rfl`). -/
noncomputable def pick (γ : Type) (x : γ) : γ := @Classical.choice γ ⟨x⟩

theorem other_ne {γ : Type} {x : γ} (y : γ) (h : y ≠ x) : other γ x ≠ x :=
  Classical.epsilon_spec (p := (· ≠ x)) ⟨y, h⟩

/-- Property of a type with at most two elements. -/
def Two (γ : Type) : Prop := ∀ x y z : γ, x = y ∨ y = z ∨ x = z

theorem two_bool : Two Bool := by unfold Two; decide

theorem not_two_forInStep : ¬ Two (ForInStep Bool) := fun h => by
  rcases h (.yield false) (.yield true) (.done false) with h | h | h <;> cases h

/-- At a type with at most two elements returns `init`, otherwise applies the body once to the
output `0` (plausible for every state). -/
noncomputable def SL.triLoop : IteratorLoop SL Id Id where
  forIn _ γ _ it init f := open Classical in
    if Two γ then init else (f 0 (SL.out it) init).run.val.value

theorem SL.triLoop_pos {lift γ Pl it init f} (h : Two γ) :
    SL.triLoop.forIn lift γ Pl it init f = init := if_pos h

theorem SL.triLoop_neg {lift γ Pl it init f} (h : ¬ Two γ) :
    SL.triLoop.forIn lift γ Pl it init f = (f 0 (SL.out it) init).run.val.value := if_neg h

theorem bool_ne_not (c : Bool) : c ≠ !c := by cases c <;> decide

theorem ulift_ne_not (c : ULift Bool) : c ≠ ULift.up (!c.down) := by
  rcases c with ⟨_ | _⟩ <;> decide

-- `Std.Iter.forIn'_eq`, idx 3 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_forInq_eq : ¬ drop0% Std.Iter.forIn'_eq 3 := fun h => by
  have h1 := @h SL Nat _ Id _ _ (SL.fnLoop keep) (SL.lawful _) Nat itS 0 (fun _ _ _ => pure (.yield 0))
  have h2 := @h SL Nat _ Id _ _ (SL.fnLoop other) (SL.lawful _) Nat itS 0 (fun _ _ _ => pure (.yield 0))
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.trans h1.symm)

-- `Std.Iter.forIn_eq`, idx 3 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_forIn_eq : ¬ drop0% Std.Iter.forIn_eq 3 := fun h => by
  have h1 := @h SL Nat _ Id _ _ (SL.fnLoop keep) (SL.lawful _) Nat itS 0 (fun _ _ => pure (.yield 0))
  have h2 := @h SL Nat _ Id _ _ (SL.fnLoop other) (SL.lawful _) Nat itS 0 (fun _ _ => pure (.yield 0))
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.trans h1.symm)

-- `Std.Iter.foldlM_toList`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_foldlM_toList : ¬ drop0% Std.Iter.foldlM_toList 4 := fun h => by
  have h1 := @h SL Nat Nat _ Id _ _ (SL.fnLoop keep) (SL.lawful _) (fun a _ => pure a) 0 itS
  have h2 := @h SL Nat Nat _ Id _ _ (SL.fnLoop other) (SL.lawful _) (fun a _ => pure a) 0 itS
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.symm.trans h1)

-- `Std.Iter.foldlM_toArray`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_foldlM_toArray : ¬ drop0% Std.Iter.foldlM_toArray 4 := fun h => by
  have h1 := @h SL Nat Nat _ Id _ _ (SL.fnLoop keep) (SL.lawful _) (fun a _ => pure a) 0 itS
  have h2 := @h SL Nat Nat _ Id _ _ (SL.fnLoop other) (SL.lawful _) (fun a _ => pure a) 0 itS
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.symm.trans h1)

-- `Std.Iter.toList_eq_fold`, idx 3 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_toList_eq_fold : ¬ drop0% Std.Iter.toList_eq_fold 3 := fun h => by
  have h1 := @h SL Nat _ (SL.fnLoop keep) (SL.lawful _) itS
  have h2 := @h SL Nat _ (SL.fnLoop other) (SL.lawful _) itS
  exact other_ne (x := ([] : List Nat)) [0] (by decide) (h2.symm.trans h1)

-- `Std.Iter.toArray_eq_fold`, idx 3 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_toArray_eq_fold : ¬ drop0% Std.Iter.toArray_eq_fold 3 := fun h => by
  have h1 := @h SL Nat _ (SL.fnLoop keep) (SL.lawful _) itS
  have h2 := @h SL Nat _ (SL.fnLoop other) (SL.lawful _) itS
  exact other_ne (x := (#[] : Array Nat)) #[0] (by decide) (h2.symm.trans h1)

-- `Std.Iter.foldl_toList`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_foldl_toList : ¬ drop0% Std.Iter.foldl_toList 4 := fun h => by
  have h1 := @h SL Nat Nat _ (SL.fnLoop keep) (SL.lawful _) (fun a _ => a) 0 itS
  have h2 := @h SL Nat Nat _ (SL.fnLoop other) (SL.lawful _) (fun a _ => a) 0 itS
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.symm.trans h1)

-- `Std.Iter.foldl_toArray`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_foldl_toArray : ¬ drop0% Std.Iter.foldl_toArray 4 := fun h => by
  have h1 := @h SL Nat Nat _ (SL.fnLoop keep) (SL.lawful _) (fun a _ => a) 0 itS
  have h2 := @h SL Nat Nat _ (SL.fnLoop other) (SL.lawful _) (fun a _ => a) 0 itS
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.symm.trans h1)

-- `Std.Iter.size_toArray_eq_length`, idx 3 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_size_toArray_eq_length : ¬ drop0% Std.Iter.size_toArray_eq_length 3 := fun h => by
  have h1 := @h SL Nat _ (SL.fnLoop keep) (SL.lawful _) itS
  have h2 := @h SL Nat _ (SL.fnLoop other) (SL.lawful _) itS
  exact other_ne (x := (ULift.up 0 : ULift Nat)) (ULift.up 1) (by decide) (congrArg ULift.up (h2.symm.trans h1))

-- `Std.Iter.length_toList_eq_length`, idx 3 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_length_toList_eq_length : ¬ drop0% Std.Iter.length_toList_eq_length 3 := fun h => by
  have h1 := @h SL Nat _ (SL.fnLoop keep) (SL.lawful _) itS
  have h2 := @h SL Nat _ (SL.fnLoop other) (SL.lawful _) itS
  exact other_ne (x := (ULift.up 0 : ULift Nat)) (ULift.up 1) (by decide) (congrArg ULift.up (h2.symm.trans h1))

-- `Std.Iter.length_toListRev_eq_length`, idx 3 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_length_toListRev_eq_length : ¬ drop0% Std.Iter.length_toListRev_eq_length 3 := fun h => by
  have h1 := @h SL Nat _ (SL.fnLoop keep) (SL.lawful _) itS
  have h2 := @h SL Nat _ (SL.fnLoop other) (SL.lawful _) itS
  exact other_ne (x := (ULift.up 0 : ULift Nat)) (ULift.up 1) (by decide) (congrArg ULift.up (h2.symm.trans h1))

-- `Std.Iter.anyM_toList`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_anyM_toList : ¬ drop0% Std.Iter.anyM_toList 4 := fun h => by
  have h1 := @h SL Nat Id _ _ _ (SL.fnLoop keep) (SL.lawful _) itS (fun _ => pure true)
  have h2 := @h SL Nat Id _ _ _ (SL.fnLoop other) (SL.lawful _) itS (fun _ => pure true)
  exact other_ne (x := false) true (by decide) (h2.symm.trans h1)

-- `Std.Iter.anyM_toArray`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_anyM_toArray : ¬ drop0% Std.Iter.anyM_toArray 4 := fun h => by
  have h1 := @h SL Nat Id _ _ _ (SL.fnLoop keep) (SL.lawful _) itS (fun _ => pure true)
  have h2 := @h SL Nat Id _ _ _ (SL.fnLoop other) (SL.lawful _) itS (fun _ => pure true)
  exact other_ne (x := false) true (by decide) (h2.symm.trans h1)

-- `Std.Iter.any_toList`, idx 3 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_any_toList : ¬ drop0% Std.Iter.any_toList 3 := fun h => by
  have h1 := @h SL Nat _ (SL.fnLoop keep) (SL.lawful _) itS (fun _ => true)
  have h2 := @h SL Nat _ (SL.fnLoop other) (SL.lawful _) itS (fun _ => true)
  exact other_ne (x := false) true (by decide) (h2.symm.trans h1)

-- `Std.Iter.any_toArray`, idx 3 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_any_toArray : ¬ drop0% Std.Iter.any_toArray 3 := fun h => by
  have h1 := @h SL Nat _ (SL.fnLoop keep) (SL.lawful _) itS (fun _ => true)
  have h2 := @h SL Nat _ (SL.fnLoop other) (SL.lawful _) itS (fun _ => true)
  exact other_ne (x := false) true (by decide) (h2.symm.trans h1)

-- `Std.Iter.all_toList`, idx 3 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_all_toList : ¬ drop0% Std.Iter.all_toList 3 := fun h => by
  have h1 := @h SL Nat _ (SL.fnLoop keep) (SL.lawful _) itS (fun _ => true)
  have h2 := @h SL Nat _ (SL.fnLoop other) (SL.lawful _) itS (fun _ => true)
  exact other_ne (x := true) false (by decide) (h2.symm.trans h1)

-- `Std.Iter.all_toArray`, idx 3 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_all_toArray : ¬ drop0% Std.Iter.all_toArray 3 := fun h => by
  have h1 := @h SL Nat _ (SL.fnLoop keep) (SL.lawful _) itS (fun _ => true)
  have h2 := @h SL Nat _ (SL.fnLoop other) (SL.lawful _) itS (fun _ => true)
  exact other_ne (x := true) false (by decide) (h2.symm.trans h1)

-- `Std.Iter.isEmpty_toList`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_Iter_isEmpty_toList : ¬ drop0% Std.Iter.isEmpty_toList 4 := fun h => by
  have h1 := @h SL Nat _ (SL.fnLoop keep) (SL.lawful _) itS
  have h2 := @h SL Nat _ (SL.fnLoop other) (SL.lawful _) itS
  exact other_ne (x := (ULift.up true : ULift Bool)) (ULift.up false) (by decide) (congrArg ULift.up (h2.symm.trans h1))

-- `Std.IterM.forIn'_eq`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_forInq_eq : ¬ drop0% Std.IterM.forIn'_eq 4 := fun h => by
  have h1 := @h SL Nat Id _ Id _ _ _ (SL.fnLoop keep) (SL.lawful _) _ _ Nat itM 0 (fun _ _ _ => pure (.yield 0))
  have h2 := @h SL Nat Id _ Id _ _ _ (SL.fnLoop other) (SL.lawful _) _ _ Nat itM 0 (fun _ _ _ => pure (.yield 0))
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.trans h1.symm)

-- `Std.IterM.forIn_eq`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_forIn_eq : ¬ drop0% Std.IterM.forIn_eq 4 := fun h => by
  have h1 := @h SL Nat Id _ Id _ _ _ (SL.fnLoop keep) (SL.lawful _) _ _ Nat itM 0 (fun _ _ => pure (.yield 0))
  have h2 := @h SL Nat Id _ Id _ _ _ (SL.fnLoop other) (SL.lawful _) _ _ Nat itM 0 (fun _ _ => pure (.yield 0))
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.trans h1.symm)

-- `Std.IterM.forIn_toList`, idx 7 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_forIn_toList : ¬ drop0% Std.IterM.forIn_toList 7 := fun h => by
  have h1 := @h Id Nat SL Nat _ _ _ (SL.fnLoop keep) (SL.lawful _) itM (fun _ _ => pure (.yield 0)) 0
  have h2 := @h Id Nat SL Nat _ _ _ (SL.fnLoop other) (SL.lawful _) itM (fun _ _ => pure (.yield 0)) 0
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.symm.trans h1)

-- `Std.IterM.forIn_toArray`, idx 7 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_forIn_toArray : ¬ drop0% Std.IterM.forIn_toArray 7 := fun h => by
  have h1 := @h Id Nat SL Nat _ _ _ (SL.fnLoop keep) (SL.lawful _) itM (fun _ _ => pure (.yield 0)) 0
  have h2 := @h Id Nat SL Nat _ _ _ (SL.fnLoop other) (SL.lawful _) itM (fun _ _ => pure (.yield 0)) 0
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.symm.trans h1)

-- `Std.IterM.toList_eq_fold`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_toList_eq_fold : ¬ drop0% Std.IterM.toList_eq_fold 4 := fun h => by
  have h1 := @h SL Nat Id _ _ _ (SL.fnLoop keep) (SL.lawful _) itM
  have h2 := @h SL Nat Id _ _ _ (SL.fnLoop other) (SL.lawful _) itM
  exact other_ne (x := ([] : List Nat)) [0] (by decide) (h2.symm.trans h1)

-- `Std.IterM.toArray_eq_fold`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_toArray_eq_fold : ¬ drop0% Std.IterM.toArray_eq_fold 4 := fun h => by
  have h1 := @h SL Nat Id _ _ _ (SL.fnLoop keep) (SL.lawful _) itM
  have h2 := @h SL Nat Id _ _ _ (SL.fnLoop other) (SL.lawful _) itM
  exact other_ne (x := (#[] : Array Nat)) #[0] (by decide) (h2.symm.trans h1)

-- `Std.IterM.foldlM_toList`, idx 7 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_foldlM_toList : ¬ drop0% Std.IterM.foldlM_toList 7 := fun h => by
  have h1 := @h Id Nat SL Nat _ _ _ (SL.fnLoop keep) (SL.lawful _) itM (fun a _ => pure a) 0
  have h2 := @h Id Nat SL Nat _ _ _ (SL.fnLoop other) (SL.lawful _) itM (fun a _ => pure a) 0
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.symm.trans h1)

-- `Std.IterM.foldlM_toArray`, idx 7 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_foldlM_toArray : ¬ drop0% Std.IterM.foldlM_toArray 7 := fun h => by
  have h1 := @h Id Nat SL Nat _ _ _ (SL.fnLoop keep) (SL.lawful _) itM (fun a _ => pure a) 0
  have h2 := @h Id Nat SL Nat _ _ _ (SL.fnLoop other) (SL.lawful _) itM (fun a _ => pure a) 0
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.symm.trans h1)

-- `Std.IterM.foldl_toList`, idx 7 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_foldl_toList : ¬ drop0% Std.IterM.foldl_toList 7 := fun h => by
  have h1 := @h Id Nat SL Nat _ _ _ (SL.fnLoop keep) (SL.lawful _) itM (fun a _ => a) 0
  have h2 := @h Id Nat SL Nat _ _ _ (SL.fnLoop other) (SL.lawful _) itM (fun a _ => a) 0
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.symm.trans h1)

-- `Std.IterM.foldl_toArray`, idx 7 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_foldl_toArray : ¬ drop0% Std.IterM.foldl_toArray 7 := fun h => by
  have h1 := @h Id Nat SL Nat _ _ _ (SL.fnLoop keep) (SL.lawful _) itM (fun a _ => a) 0
  have h2 := @h Id Nat SL Nat _ _ _ (SL.fnLoop other) (SL.lawful _) itM (fun a _ => a) 0
  exact other_ne (x := (0 : Nat)) 1 (by decide) (h2.symm.trans h1)

-- `Std.IterM.up_size_toArray_eq_length`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_up_size_toArray_eq_length : ¬ drop0% Std.IterM.up_size_toArray_eq_length 4 := fun h => by
  have h1 := @h Id SL Nat _ _ _ (SL.fnLoop keep) (SL.lawful _) itM
  have h2 := @h Id SL Nat _ _ _ (SL.fnLoop other) (SL.lawful _) itM
  exact other_ne (x := (ULift.up 0 : ULift Nat)) (ULift.up 1) (by decide) (h2.symm.trans h1)

-- `Std.IterM.up_length_toList_eq_length`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_up_length_toList_eq_length : ¬ drop0% Std.IterM.up_length_toList_eq_length 4 := fun h => by
  have h1 := @h Id SL Nat _ _ _ (SL.fnLoop keep) (SL.lawful _) itM
  have h2 := @h Id SL Nat _ _ _ (SL.fnLoop other) (SL.lawful _) itM
  exact other_ne (x := (ULift.up 0 : ULift Nat)) (ULift.up 1) (by decide) (h2.symm.trans h1)

-- `Std.IterM.up_length_toListRev_eq_length`, idx 4 (Finite): two-loop: on the non-finite SL (skips to itself), every IteratorLoop is lawful; instantiating with fnLoop keep and fnLoop other (both lawful) gives two different loop-side values for the same loop-independent side
theorem d_IterM_up_length_toListRev_eq_length : ¬ drop0% Std.IterM.up_length_toListRev_eq_length 4 := fun h => by
  have h1 := @h Id SL Nat _ _ _ (SL.fnLoop keep) (SL.lawful _) itM
  have h2 := @h Id SL Nat _ _ _ (SL.fnLoop other) (SL.lawful _) itM
  exact other_ne (x := (ULift.up 0 : ULift Nat)) (ULift.up 1) (by decide) (h2.symm.trans h1)

-- `Std.Iter.fold_hom`, idx 5 (Finite): on SL (non-finite, all loops lawful) the Id.{x1} loop is fnLoop keep and the Id.{x2} loop fnLoop other; f = id, g = fun x _ => x: other 0 vs 0
theorem d_Iter_fold_hom : ¬ drop0% Std.Iter.fold_hom 5 := fun h => by
  have h1 := @h SL Nat Nat Nat _ (SL.fnLoop keep) (SL.lawful _) (SL.fnLoop other) (SL.lawful _) itS id (fun x _ => x) (fun x _ => x) 0 (fun _ _ => rfl)
  exact other_ne (x := 0) 1 (by decide) h1

-- `Std.Iter.length_eq_fold`, idx 3 (Finite): on SL (non-finite, all loops lawful) length uses fnLoop keep (0) and the Nat fold fnLoop other (other 0)
theorem d_Iter_length_eq_fold : ¬ drop0% Std.Iter.length_eq_fold 3 := fun h => by
  have h1 := @h SL Nat _ (SL.fnLoop keep) (SL.lawful _) (SL.fnLoop other) (SL.lawful _) itS
  exact other_ne (x := 0) 1 (by decide) h1.symm

-- `Std.Iter.length_eq_forIn`, idx 3 (Finite): on SL (non-finite, all loops lawful) length uses fnLoop keep (0) and the Nat forIn fnLoop other (other 0)
theorem d_Iter_length_eq_forIn : ¬ drop0% Std.Iter.length_eq_forIn 3 := fun h => by
  have h1 := @h SL Nat _ (SL.fnLoop keep) (SL.lawful _) (SL.fnLoop other) (SL.lawful _) itS
  exact other_ne (x := 0) 1 (by decide) h1.symm

-- `Std.IterM.forIn_eq_foldM`, idx 3 (Finite): on SL (non-finite, all loops lawful) with triLoop (init at types with at most two elements, else the body applied once to output 0): forIn at Bool gives false, foldM at ForInStep Bool gives yield true
theorem d_IterM_forIn_eq_foldM : ¬ drop0% Std.IterM.forIn_eq_foldM 3 := fun h => by
  have h1 := @h SL Nat _ Id _ _ SL.triLoop (SL.lawful _) Bool itS false (fun _ _ => pure (.yield true))
  simp only [ForIn.forIn, ForIn'.forIn', Iter.foldM] at h1
  rw [SL.triLoop_pos two_bool, SL.triLoop_neg not_two_forInStep] at h1
  exact Bool.false_ne_true h1

-- `Std.IterM.fold_hom`, idx 6 (Finite): on SL (non-finite, all loops lawful) with fnLoop pick (a fixed value c per type): c = c + 1 for f = succ, g = fun x _ => x
theorem d_IterM_fold_hom : ¬ drop0% Std.IterM.fold_hom 6 := fun h => by
  have h1 := @h SL Nat Nat Nat Id _ _ _ (SL.fnLoop pick) (SL.lawful _) itM (· + 1) (fun x _ => x) (fun x _ => x) 0 (fun _ _ => rfl)
  exact Nat.succ_ne_self _ h1.symm

-- `Std.Iter.allM_eq_not_anyM_not`, idx 4 (Finite): on SL (non-finite, all loops lawful) with fnLoop pick (a fixed value c per type): allM = c, !anyM = !c
theorem d_Iter_allM_eq_not_anyM_not : ¬ drop0% Std.Iter.allM_eq_not_anyM_not 4 := fun h => by
  have h1 := @h SL Nat Id _ _ _ (SL.fnLoop pick) (SL.lawful _) itS (fun _ => pure true)
  exact bool_ne_not _ h1

-- `Std.Iter.all_eq_not_any_not`, idx 4 (Finite): on SL (non-finite, all loops lawful) with fnLoop pick (a fixed value c per type): all = c, !any = !c
theorem d_Iter_all_eq_not_any_not : ¬ drop0% Std.Iter.all_eq_not_any_not 4 := fun h => by
  have h1 := @h Id SL Nat _ _ _ (SL.fnLoop pick) (SL.lawful _) itS (fun _ => true)
  exact bool_ne_not _ h1

-- `Std.IterM.allM_eq_not_anyM_not`, idx 4 (Finite): on SL (non-finite, all loops lawful) with fnLoop pick (a fixed value c per type): allM = c, anyM-negated = up !c.down
theorem d_IterM_allM_eq_not_anyM_not : ¬ drop0% Std.IterM.allM_eq_not_anyM_not 4 := fun h => by
  have h1 := @h SL Nat Id _ _ _ (SL.fnLoop pick) (SL.lawful _) itM (fun _ => pure (.up true))
  exact ulift_ne_not _ h1

-- `Std.IterM.all_eq_not_any_not`, idx 4 (Finite): on SL (non-finite, all loops lawful) with fnLoop pick (a fixed value c per type): all = c, any-negated = up !c.down
theorem d_IterM_all_eq_not_any_not : ¬ drop0% Std.IterM.all_eq_not_any_not 4 := fun h => by
  have h1 := @h SL Nat Id _ _ _ (SL.fnLoop pick) (SL.lawful _) itM (fun _ => true)
  exact ulift_ne_not _ h1

end OpCHand
