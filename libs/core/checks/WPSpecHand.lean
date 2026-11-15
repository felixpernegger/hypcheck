import Std
import Lean

/-!
Hand pass `WPSpec` (hand15): the 276 open hypotheses of `Std.WP.Triple.SpecLemmas` (Hoare-triple
specifications of the `Std.WP` framework for list/array/string/container loops, iterator
combinators, `repeatM` and `Lean.Loop`). For hypothesis `hᵢ` of theorem `T` each declaration proves
`¬T'` (`drop0% T i` / `indep0% T i`, universes `0`) or `T'` (`drop% T i`).

272 necessary, 4 removable, 0 independent, 0 left unresolved.

Reusable models built here (namespace `WPSpecHand`):
* `exWP` / `exWPM o γ`: the exact weakest precondition of any lawful monad `o` (assertions are sets
  of programs `o γ`; `wp x post` holds of `c` iff `c` is `x` followed by continuations satisfying
  `post`). `ex_self` / `ex_eq`: `Triple y {y} (pure ·)` holds, and `Triple x {y} (pure ·)` forces
  `x = y`. So a spec `Triple RHS P Q → Triple LHS P Q` refutes like the equation `LHS = RHS`:
  each hand8/hand10 counterexample to the library lemma `Std.IterM.*`/`Std.Iter.*` that the spec is
  proved from (`rwa`) transfers verbatim, since there `LawfulMonad o` was a hypothesis.
* `two`: one term equal to two different values (two-loop refutations).
* `Manual.M3`: the diamond lattice `M₃` as a `CompleteLattice` (meets do not preserve joins:
  `x ⊔ y = ⊤`, `x ⊓ z = y ⊓ z = ⊥`), `M3.V` a `Variant` with measure `x`/`y`, `M3.idWP` the
  `WPMonad Id M3 Unit` with `wp x post = post x` (use with a local `WP (Id α) α M3 Unit` instance,
  since `Id`'s `Prop` instance wins the out-param otherwise). Refutes `PreservesSup (meet P)`
  premises (`Variant.le_of_total_le`, `Spec.repeatM`, `Spec.forIn_loop`).
* `Manual.R1`/`R2`: list wrappers whose `ForIn`/`ForIn'` in `Option` return `init` while the `Id`
  loop enumerates the list (not `PureForIn`/`PureForIn'`); `Manual.ADLoopI`: a vacuously lawful
  loop returning `init` for the non-finite `OpD1Hand.AD` iterator.

Kinds of verdicts:
* Iterator-combinator instance premises (194 necessary): copies of the models of
  `checks/ItMonadMAHand.lean`, `ItMonadIterHand.lean`, `ItLoopHand.lean`, `OpD1Hand.lean`,
  `OpD2Hand.lean` (their own verdicts removed, comments without backticks) with the refutation of
  the matching library hypothesis rewrapped by `ex_eq`/`ex_self` (`WPS.*` declarations).
* Removable (4): `LawfulMonad m` of `Spec.IterM.forIn_filterMap`, `forIn_filter`, `foldM_filterMap`,
  `foldM_filter`: the library equation holds without it (ItMonadMA's proofs `forIn_filterMap.h7`
  etc.: the combinator step only binds and returns `pure` in `m`, which the lawful lift maps into
  the lawful `n`), so the spec follows by rewriting.
* `h` premises of the combinator specs (51) and `step` premises (13): in `Id` with `Prop`
  assertions, pre `True`/post `False`, or an invariant `pref = []` / `pos = startPos` whose final
  instance is false by definition (`[0] = []`).
* `foldM_iter`/`foldM_iterM_id`: `LawfulIteratorLoop` by `ItLoopHand`'s BL 0 (loop returns
  `init`); `Finite` by the two-loop trick on `OpD1Hand.AD`.
* `PureForIn`/`PureForIn'` by `R1`/`R2`; `LawfulMemForInId` (dependent) by an empty membership on
  lists; `Nonempty β` of `repeatM` (dependent) by `β = Empty`.

Run with the lean4 repo's stage1 binary: `runs/hand15/lean.sh checks/WPSpecHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
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


/-! ## The exact weakest precondition of a lawful monad -/

namespace WPSpecHand
open Std.WP Lean.Order

section Exact
variable (o : Type → Type) [Monad o] [LawfulMonad o] (γ : Type)

/-- `exP o γ x post c`: the program `c : o γ` is `x` followed by continuations chosen per result
`a` among those satisfying `post a`. -/
def exP {α : Type} (x : o α) (post : α → o γ → Prop) (c : o γ) : Prop :=
  ∃ x' : o (Σ a : α, {c' : o γ // post a c'}), c = x' >>= (fun p => p.2.1) ∧ Sigma.fst <$> x' = x

/-- The exact interpretation: assertions are sets of programs `o γ`. -/
@[instance_reducible] def exWP (α : Type) : WP (o α) α (o γ → Prop) Unit where
  trans x := ⟨fun post _ => exP o γ x post⟩
  trans_monotone x := by
    intro post post' _ _ _ hpost c ⟨x', hc, hx⟩
    refine ⟨(fun p => ⟨p.1, p.2.1, hpost p.1 p.2.1 p.2.2⟩) <$> x', ?_, ?_⟩
    · rw [hc, bind_map_left]
    · rw [← hx, Functor.map_map]

/-- Every lawful monad is a `WPMonad` for the exact interpretation. -/
@[instance_reducible] noncomputable def exWPM : WPMonad o (o γ → Prop) Unit where
  toWP := exWP o γ
  pure_le_wp_pure x post _ := by
    intro c hc
    exact ⟨pure ⟨x, c, hc⟩, by rw [pure_bind], by rw [map_pure]⟩
  bind_le_wp_bind {α β} x f post _ := by
    intro c ⟨x', hc, hx⟩
    refine ⟨x' >>= fun p => Classical.choose p.2.2, ?_, ?_⟩
    · rw [hc, bind_assoc]
      apply bind_congr; intro p
      exact (Classical.choose_spec p.2.2).1
    · rw [map_bind, ← hx, bind_map_left]
      apply bind_congr; intro p
      exact (Classical.choose_spec p.2.2).2

theorem ex_self (y : o γ) : letI := exWPM o γ; Triple y (fun c => c = y) (fun b c => c = pure b) () :=
  letI := exWPM o γ
  ⟨fun c hc => ⟨(fun b => ⟨b, pure b, rfl⟩) <$> y, by rw [hc, bind_map_left, bind_pure], by
    rw [Functor.map_map]; exact id_map y⟩⟩

theorem ex_eq {x y : o γ} (h : letI := exWPM o γ; Triple x (fun c => c = y) (fun b c => c = pure b) ()) : x = y := by
  letI := exWPM o γ
  obtain ⟨x', hy, hx⟩ := h.le_wp y rfl
  rw [hy, ← hx, map_eq_pure_bind]
  apply bind_congr; intro p
  exact p.2.2.symm

end Exact

/-- The refutation pattern of the two-loop models: one term equal to two different values. -/
theorem two {α : Type} {L a b : α} (hab : a ≠ b) (h0 : L = a) (h1 : L = b) : False := hab (h0.symm.trans h1)

end WPSpecHand

open scoped Std.WP

/-! ## Models and refutations after ItLoopHand.lean -/

section IL

namespace ItLoopHand
variable {k : Nat}
open Std Std.Iterators

/-- A copy of the list iterator, with no `IteratorLoop` instance of its own. -/
structure BL (k : Nat) (β : Type w) where
  list : List β

instance BL.instIterator {β : Type w} {m : Type w → Type w'} [Pure m] : Iterator (BL k β) m β where
  IsPlausibleStep it
    | .yield it' out => it.internalState.list = out :: it'.internalState.list
    | .skip _ => False
    | .done => it.internalState.list = []
  step it := pure (match it with
        | ⟨⟨[]⟩⟩ => .deflate ⟨.done, rfl⟩
        | ⟨⟨x :: xs⟩⟩ => .deflate ⟨.yield ⟨⟨xs⟩⟩ x, rfl⟩)

def BL.finRel {β : Type w} {m : Type w → Type w'} [Pure m] : FinitenessRelation (BL k β) m where
  Rel := InvImage WellFoundedRelation.rel (BL.list ∘ IterM.internalState)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step <;> simp_all [IterStep.successor, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, BL.instIterator]

instance BL.instFinite {β : Type w} {m : Type w → Type w'} [Pure m] : Finite (BL k β) m :=
  Finite.of_finitenessRelation BL.finRel

instance BL.instDet {β : Type w} {m : Type w → Type w'} [Pure m] : LawfulDeterministicIterator (BL k β) m where
  isPlausibleStep_eq_eq it := by
    rcases it with ⟨⟨_ | ⟨x, xs⟩⟩⟩
    · exact ⟨.done, by funext s; cases s <;> simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, BL.instIterator]⟩
    · refine ⟨.yield ⟨⟨xs⟩⟩ x, ?_⟩
      funext s; cases s <;> simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, BL.instIterator]
      rename_i it' out
      rcases it' with ⟨⟨l⟩⟩
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
      · rintro ⟨h1, rfl⟩; cases h1; exact ⟨rfl, rfl⟩

/-- `IterM` over `l`. -/
def blM (k : Nat) {β : Type w} (l : List β) (m : Type w → Type w') [Pure m] : IterM (α := BL k β) m β := ⟨⟨l⟩⟩
/-- `Iter` over `l`. -/
def bl (k : Nat) {β : Type w} (l : List β) : Iter (α := BL k β) β := ⟨⟨l⟩⟩

/-- Broken loop: returns `init` without iterating. -/
@[instance_reducible] def brkI {β : Type w} {m : Type w → Type w'} {n : Type x → Type x'} [Pure m] [Monad n] :
    IteratorLoop (BL k β) m n := ⟨fun _ _ _ _ init _ => pure init⟩

/-- Broken loop in `Option`: fails. -/
@[instance_reducible] def brkF {β : Type w} {m : Type w → Type w'} [Pure m] : IteratorLoop (BL k β) m Option :=
  ⟨fun _ _ _ _ _ _ => none⟩

/-- The lawful default loop. -/
abbrev dfl {β : Type w} {m : Type w → Type w'} {n : Type x → Type x'} [Pure m] [Monad n] :
    IteratorLoop (BL k β) m n := .defaultImplementation

section
variable {k : Nat} {β : Type w} {m : Type w → Type w'} [Monad m]

@[simp] theorem step_blM_nil : (blM k ([] : List β) m).step = pure (.deflate ⟨.done, rfl⟩) := rfl
@[simp] theorem step_blM_cons {x : β} {xs : List β} :
    (blM k (x :: xs) m).step = pure (.deflate ⟨.yield (blM k xs m) x, rfl⟩) := rfl

variable {k : Nat} in
@[simp] theorem toList_blM [LawfulMonad m] {l : List β} : (blM k l m).toList = pure l := by
  induction l with
  | nil => rw [IterM.toList_eq_match_step]; simp
  | cons x xs ih => rw [IterM.toList_eq_match_step]; simp [ih]

variable {k : Nat} in
@[simp] theorem toArray_blM [LawfulMonad m] {l : List β} : (blM k l m).toArray = pure l.toArray := by
  rw [← IterM.toArray_toList]; simp

variable {k : Nat} in
@[simp] theorem toListRev_blM [LawfulMonad m] {l : List β} : (blM k l m).toListRev = pure l.reverse := by
  simp [IterM.toListRev_eq]
end

variable {k : Nat} in
@[simp] theorem toIterM_bl {l : List β} : (bl k l).toIterM = blM k l Id := rfl
variable {k : Nat} in
@[simp] theorem step_bl_nil : (bl k ([] : List β)).step = ⟨.done, rfl⟩ := by
  simp [Iter.step, IterM.step, Iterator.step, bl, blM, BL.instIterator] <;> rfl
variable {k : Nat} in
@[simp] theorem step_bl_cons {x : β} {xs : List β} : (bl k (x :: xs)).step = ⟨.yield (bl k xs) x, rfl⟩ := by
  simp [Iter.step, IterM.step, Iterator.step, bl, blM, BL.instIterator, IterM.toIter] <;> rfl
variable {k : Nat} in
@[simp] theorem toList_bl {l : List β} : (bl k l).toList = l := by
  simp [Iter.toList_eq_toList_toIterM]
variable {k : Nat} in
@[simp] theorem toArray_bl {l : List β} : (bl k l).toArray = l.toArray := by
  simp [Iter.toArray_eq_toArray_toIterM]
variable {k : Nat} in
@[simp] theorem toListRev_bl {l : List β} : (bl k l).toListRev = l.reverse := by
  simp [Iter.toListRev_eq_toListRev_toIterM]

/-! Loop instances by tag: `0` returns `init` in every monad; `1` fails in `Option` and is the
default elsewhere; `4`/`5` return `init` in `Id.{1}`/`Id.{0}` and are the default elsewhere. -/
instance BL.loop0 {β : Type w} {m : Type w → Type w'} {n : Type x → Type x'} [Pure m] [Monad n] :
    IteratorLoop (BL 0 β) m n := brkI
instance BL.loop1 {β : Type w} {m : Type w → Type w'} [Pure m] : IteratorLoop (BL 1 β) m Option := brkF
instance (priority := low) BL.loop1d {β : Type w} {m : Type w → Type w'} {n : Type x → Type x'} [Pure m] [Monad n] :
    IteratorLoop (BL 1 β) m n := .defaultImplementation
instance BL.loop4 {β : Type w} {m : Type w → Type w'} [Pure m] : IteratorLoop (BL 4 β) m Id.{1} := brkI
instance (priority := low) BL.loop4d {β : Type w} {m : Type w → Type w'} {n : Type x → Type x'} [Pure m] [Monad n] :
    IteratorLoop (BL 4 β) m n := .defaultImplementation
instance BL.loop5 {β : Type w} {m : Type w → Type w'} [Pure m] : IteratorLoop (BL 5 β) m Id.{0} := brkI
instance (priority := low) BL.loop5d {β : Type w} {m : Type w → Type w'} {n : Type x → Type x'} [Pure m] [Monad n] :
    IteratorLoop (BL 5 β) m n := .defaultImplementation

/-- Tag `2`: in a loop over `Bool` return `true`, otherwise `init` (not parametric in `γ`). -/
noncomputable instance BL.loop2 {β : Type w} {m : Type w → Type w'} {n : Type → Type x'} [Pure m] [Monad n] :
    IteratorLoop (BL 2 β) m n where
  forIn _ γ _ _ init _ :=
    @dite _ (γ = Bool) (Classical.propDecidable _) (fun h => cast (congrArg n h.symm) (pure true)) (fun _ => pure init)
/-- Tag `3`: in a loop over `ULift Bool` return `up true`, otherwise `init`. -/
noncomputable instance BL.loop3 {β : Type w} {m : Type w → Type w'} {n : Type → Type x'} [Pure m] [Monad n] :
    IteratorLoop (BL 3 β) m n where
  forIn _ γ _ _ init _ :=
    @dite _ (γ = ULift.{0} Bool) (Classical.propDecidable _) (fun h => cast (congrArg n h.symm) (pure (ULift.up true)))
      (fun _ => pure init)

theorem loop2_bool {β : Type w} {m : Type w → Type w'} {n : Type → Type x'} [Pure m] [Monad n] {lift Pl it init f} :
    (BL.loop2 (β := β) (m := m) (n := n)).forIn lift Bool Pl it init f = pure true := by
  show @dite _ _ (Classical.propDecidable _) _ _ = _; rw [dif_pos rfl]; rfl
theorem loop2_ne {β : Type w} {m : Type w → Type w'} {n : Type → Type x'} [Pure m] [Monad n] {lift γ Pl it init f}
    (h : γ ≠ Bool) : (BL.loop2 (β := β) (m := m) (n := n)).forIn lift γ Pl it init f = pure init := by
  show @dite _ _ (Classical.propDecidable _) _ _ = _; rw [dif_neg h]
theorem loop3_ubool {β : Type w} {m : Type w → Type w'} {n : Type → Type x'} [Pure m] [Monad n] {lift Pl it init f} :
    (BL.loop3 (β := β) (m := m) (n := n)).forIn lift (ULift Bool) Pl it init f = pure (ULift.up true) := by
  show @dite _ _ (Classical.propDecidable _) _ _ = _; rw [dif_pos rfl]; rfl

theorem bool_ne_forInStep : Bool ≠ ForInStep Bool := by
  intro h
  have : ∀ x y z : Bool, x = y ∨ x = z ∨ y = z := by decide
  rw [h] at this
  have := this (.yield true) (.yield false) (.done true)
  simp at this

instance instDecEqId {α : Type w} [DecidableEq α] : DecidableEq (Id α) := inferInstanceAs (DecidableEq α)

macro "ev" : tactic => `(tactic| (
  (try simp [← Iter.forIn_toList, ← Iter.foldlM_toList, ← Iter.foldl_toList,
   ← Iter.anyM_toList, ← Iter.any_toList, ← Iter.all_toList, ← Iter.length_toList_eq_length,
   ← Iter.findSomeM?_toList, ← Iter.findSome?_toList, ← Iter.find?_toList, ← Iter.head?_toList,
   ← Iter.isEmpty_toList, Iter.findM?_eq_findM?_toList, Iter.allM_eq_not_anyM_not,
   ← IterM.forIn_toList, ← IterM.foldlM_toList, ← IterM.foldl_toList, ← IterM.up_length_toList_eq_length,
   IterM.drain_eq_map_toList, IterM.anyM_eq_forIn, IterM.any_eq_forIn, IterM.allM_eq_forIn,
   IterM.all_eq_forIn, IterM.fold_eq_forIn, IterM.length_eq_forIn, IterM.foldM_eq_forIn, Iter.toList_map, Iter.toList_filterMap, Iter.toList_filter,
   Iter.toList_mapM, Iter.toList_mapWithPostcondition, IterM.toList_map, IterM.toList_filterMap,
   IterM.toList_filter, IterM.toList_mapM, IterM.toList_filterMapM, IterM.toList_mapWithPostcondition,
   IterM.toList_filterMapWithPostcondition, Iter.toList_attachWith, Iter.filterMapWithPostcondition, Iter.filterMapM, Iter.filterM,
   Iter.filterWithPostcondition, IterM.filterM, IterM.filterWithPostcondition, Iter.toList_uLift, IterM.toList_uLift]) <;>
  decide))

/-! ## Bulk refutations (generated by runs/hand8/scratch_ItLoop/gen.py) -/

/-! ## Special cases -/


/-! ### Transferred refutations (WPSpec) -/

-- `Std.WP.Spec.IterM.forIn_filterMapWithPostcondition` idx 24: necessary; the hand8/hand10 model of Std.IterM.forIn_filterMapWithPostcondition idx 20, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.forIn_filterMapWithPostcondition.h24 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapWithPostcondition 24 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (it := blM 1 [1, 2] Id) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.forIn_filterMapM` idx 26: necessary; the hand8/hand10 model of Std.IterM.forIn_filterMapM idx 22, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.forIn_filterMapM.h26 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapM 26 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (it := blM 1 [1, 2] Id) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.forIn_filterMap` idx 19: necessary; the hand8/hand10 model of Std.IterM.forIn_filterMap idx 15, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.forIn_filterMap.h19 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMap 19 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Option) (it := blM 1 [1, 2] Id) (f := fun x => some x) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.forIn_mapWithPostcondition` idx 24: necessary; the hand8/hand10 model of Std.IterM.forIn_mapWithPostcondition idx 20, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.forIn_mapWithPostcondition.h24 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapWithPostcondition 24 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (it := blM 1 [1, 2] Id) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.forIn_mapM` idx 26: necessary; the hand8/hand10 model of Std.IterM.forIn_mapM idx 22, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.forIn_mapM.h26 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapM 26 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (it := blM 1 [1, 2] Id) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.forIn_map` idx 19: necessary; the hand8/hand10 model of Std.IterM.forIn_map idx 15, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.forIn_map.h19 : ¬ drop0% Std.WP.Spec.IterM.forIn_map 19 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Option) (it := blM 1 [1, 2] Id) (f := fun x => x + 1) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.forIn_filterWithPostcondition` idx 23: necessary; the hand8/hand10 model of Std.IterM.forIn_filterWithPostcondition idx 19, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.forIn_filterWithPostcondition.h23 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterWithPostcondition 23 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (it := blM 1 [1, 2] Id) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.forIn_filterM` idx 25: necessary; the hand8/hand10 model of Std.IterM.forIn_filterM idx 21, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.forIn_filterM.h25 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterM 25 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (it := blM 1 [1, 2] Id) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.forIn_filter` idx 18: necessary; the hand8/hand10 model of Std.IterM.forIn_filter idx 14, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.forIn_filter.h18 : ¬ drop0% Std.WP.Spec.IterM.forIn_filter 18 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Option) (it := blM 1 [1, 2] Id) (f := fun _ => true) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.foldM_filterMapWithPostcondition` idx 22: necessary; the hand8/hand10 model of Std.IterM.foldM_filterMapWithPostcondition idx 18, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.foldM_filterMapWithPostcondition.h22 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapWithPostcondition 22 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.foldM_filterMapM` idx 24: necessary; the hand8/hand10 model of Std.IterM.foldM_filterMapM idx 20, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.foldM_filterMapM.h24 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapM 24 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.foldM_mapWithPostcondition` idx 22: necessary; the hand8/hand10 model of Std.IterM.foldM_mapWithPostcondition idx 18, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.foldM_mapWithPostcondition.h22 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapWithPostcondition 22 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.foldM_mapM` idx 24: necessary; the hand8/hand10 model of Std.IterM.foldM_mapM idx 20, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.foldM_mapM.h24 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapM 24 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.foldM_filterWithPostcondition` idx 21: necessary; the hand8/hand10 model of Std.IterM.foldM_filterWithPostcondition idx 17, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.foldM_filterWithPostcondition.h21 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterWithPostcondition 21 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.foldM_filterM` idx 23: necessary; the hand8/hand10 model of Std.IterM.foldM_filterM idx 19, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.foldM_filterM.h23 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterM 23 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.foldM_filterMap` idx 17: necessary; the hand8/hand10 model of Std.IterM.foldM_filterMap idx 13, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.foldM_filterMap.h17 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMap 17 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => some x) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.foldM_map` idx 17: necessary; the hand8/hand10 model of Std.IterM.foldM_map idx 13, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.foldM_map.h17 : ¬ drop0% Std.WP.Spec.IterM.foldM_map 17 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => x + 1) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.foldM_filter` idx 16: necessary; the hand8/hand10 model of Std.IterM.foldM_filter idx 12, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.foldM_filter.h16 : ¬ drop0% Std.WP.Spec.IterM.foldM_filter 16 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun _ => true) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.fold_filterMapWithPostcondition` idx 17: necessary; the hand8/hand10 model of Std.IterM.fold_filterMapWithPostcondition idx 13, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.fold_filterMapWithPostcondition.h17 : ¬ drop0% Std.WP.Spec.IterM.fold_filterMapWithPostcondition 17 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.fold_filterMapM` idx 19: necessary; the hand8/hand10 model of Std.IterM.fold_filterMapM idx 15, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.fold_filterMapM.h19 : ¬ drop0% Std.WP.Spec.IterM.fold_filterMapM 19 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.fold_mapWithPostcondition` idx 17: necessary; the hand8/hand10 model of Std.IterM.fold_mapWithPostcondition idx 13, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.fold_mapWithPostcondition.h17 : ¬ drop0% Std.WP.Spec.IterM.fold_mapWithPostcondition 17 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.fold_mapM` idx 19: necessary; the hand8/hand10 model of Std.IterM.fold_mapM idx 15, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.fold_mapM.h19 : ¬ drop0% Std.WP.Spec.IterM.fold_mapM 19 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.fold_filterWithPostcondition` idx 16: necessary; the hand8/hand10 model of Std.IterM.fold_filterWithPostcondition idx 12, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.fold_filterWithPostcondition.h16 : ¬ drop0% Std.WP.Spec.IterM.fold_filterWithPostcondition 16 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.fold_filterM` idx 18: necessary; the hand8/hand10 model of Std.IterM.fold_filterM idx 14, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.IterM.fold_filterM.h18 : ¬ drop0% Std.WP.Spec.IterM.fold_filterM 18 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.fold_filterMap` idx 14: necessary; the hand8/hand10 model of Std.IterM.fold_filterMap idx 10, transferred with the exact WP (tag 0 (returns init without iterating) on [1, 2])
theorem WPS.IterM.fold_filterMap.h14 : ¬ drop0% Std.WP.Spec.IterM.fold_filterMap 14 := fun h => by
  letI := WPSpecHand.exWPM (Id) Nat
  have := WPSpecHand.ex_eq (Id) Nat (h (α := BL 0 Nat) (m := Id) (f := fun x => some x) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 0 [1, 2] Id) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.fold_map` idx 14: necessary; the hand8/hand10 model of Std.IterM.fold_map idx 10, transferred with the exact WP (tag 0 (returns init without iterating) on [1, 2])
theorem WPS.IterM.fold_map.h14 : ¬ drop0% Std.WP.Spec.IterM.fold_map 14 := fun h => by
  letI := WPSpecHand.exWPM (Id) Nat
  have := WPSpecHand.ex_eq (Id) Nat (h (α := BL 0 Nat) (m := Id) (f := fun x => x + 1) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 0 [1, 2] Id) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.IterM.fold_filter` idx 13: necessary; the hand8/hand10 model of Std.IterM.fold_filter idx 9, transferred with the exact WP (tag 0 (returns init without iterating) on [1, 2])
theorem WPS.IterM.fold_filter.h13 : ¬ drop0% Std.WP.Spec.IterM.fold_filter 13 := fun h => by
  letI := WPSpecHand.exWPM (Id) Nat
  have := WPSpecHand.ex_eq (Id) Nat (h (α := BL 0 Nat) (m := Id) (f := fun _ => true) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 0 [1, 2] Id) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.forIn_filterMapWithPostcondition` idx 19: necessary; the hand8/hand10 model of Std.Iter.forIn_filterMapWithPostcondition idx 15, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.forIn_filterMapWithPostcondition.h19 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMapWithPostcondition 19 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.forIn_filterMapM` idx 21: necessary; the hand8/hand10 model of Std.Iter.forIn_filterMapM idx 17, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.forIn_filterMapM.h21 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMapM 21 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.forIn_filterMap` idx 14: necessary; the hand8/hand10 model of Std.Iter.forIn_filterMap idx 10, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.forIn_filterMap.h14 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMap 14 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Option) (it := bl 1 [1, 2]) (f := fun x => some x) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.forIn_mapWithPostcondition` idx 19: necessary; the hand8/hand10 model of Std.Iter.forIn_mapWithPostcondition idx 15, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.forIn_mapWithPostcondition.h19 : ¬ drop0% Std.WP.Spec.Iter.forIn_mapWithPostcondition 19 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.forIn_mapM` idx 21: necessary; the hand8/hand10 model of Std.Iter.forIn_mapM idx 17, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.forIn_mapM.h21 : ¬ drop0% Std.WP.Spec.Iter.forIn_mapM 21 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.forIn_map` idx 14: necessary; the hand8/hand10 model of Std.Iter.forIn_map idx 10, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.forIn_map.h14 : ¬ drop0% Std.WP.Spec.Iter.forIn_map 14 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Option) (it := bl 1 [1, 2]) (f := fun x => x + 1) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.forIn_filterWithPostcondition` idx 18: necessary; the hand8/hand10 model of Std.Iter.forIn_filterWithPostcondition idx 14, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.forIn_filterWithPostcondition.h18 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterWithPostcondition 18 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.forIn_filterM` idx 20: necessary; the hand8/hand10 model of Std.Iter.forIn_filterM idx 16, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.forIn_filterM.h20 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterM 20 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.forIn_filter` idx 13: necessary; the hand8/hand10 model of Std.Iter.forIn_filter idx 9, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.forIn_filter.h13 : ¬ drop0% Std.WP.Spec.Iter.forIn_filter 13 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Option) (it := bl 1 [1, 2]) (f := fun _ => true) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.foldM_filterMapWithPostcondition` idx 19: necessary; the hand8/hand10 model of Std.Iter.foldM_filterMapWithPostcondition idx 15, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.foldM_filterMapWithPostcondition.h19 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMapWithPostcondition 19 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.foldM_filterMapM` idx 21: necessary; the hand8/hand10 model of Std.Iter.foldM_filterMapM idx 17, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.foldM_filterMapM.h21 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMapM 21 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.foldM_mapWithPostcondition` idx 22: necessary; the hand8/hand10 model of Std.Iter.foldM_mapWithPostcondition idx 18, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.foldM_mapWithPostcondition.h22 : ¬ drop0% Std.WP.Spec.Iter.foldM_mapWithPostcondition 22 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.foldM_mapM` idx 21: necessary; the hand8/hand10 model of Std.Iter.foldM_mapM idx 17, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.foldM_mapM.h21 : ¬ drop0% Std.WP.Spec.Iter.foldM_mapM 21 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.foldM_filterWithPostcondition` idx 18: necessary; the hand8/hand10 model of Std.Iter.foldM_filterWithPostcondition idx 14, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.foldM_filterWithPostcondition.h18 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterWithPostcondition 18 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.foldM_filterM` idx 20: necessary; the hand8/hand10 model of Std.Iter.foldM_filterM idx 16, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.foldM_filterM.h20 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterM 20 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.foldM_filterMap` idx 14: necessary; the hand8/hand10 model of Std.Iter.foldM_filterMap idx 10, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.foldM_filterMap.h14 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMap 14 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Option) (f := fun x => some x) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.foldM_map` idx 14: necessary; the hand8/hand10 model of Std.Iter.foldM_map idx 10, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.foldM_map.h14 : ¬ drop0% Std.WP.Spec.Iter.foldM_map 14 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Option) (f := fun x => x + 1) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.foldM_filter` idx 13: necessary; the hand8/hand10 model of Std.Iter.foldM_filter idx 9, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.foldM_filter.h13 : ¬ drop0% Std.WP.Spec.Iter.foldM_filter 13 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Option) (f := fun _ => true) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.fold_filterMapWithPostcondition` idx 14: necessary; the hand8/hand10 model of Std.Iter.fold_filterMapWithPostcondition idx 10, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.fold_filterMapWithPostcondition.h14 : ¬ drop0% Std.WP.Spec.Iter.fold_filterMapWithPostcondition 14 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.fold_filterMapM` idx 16: necessary; the hand8/hand10 model of Std.Iter.fold_filterMapM idx 12, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.fold_filterMapM.h16 : ¬ drop0% Std.WP.Spec.Iter.fold_filterMapM 16 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.fold_mapWithPostcondition` idx 14: necessary; the hand8/hand10 model of Std.Iter.fold_mapWithPostcondition idx 10, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.fold_mapWithPostcondition.h14 : ¬ drop0% Std.WP.Spec.Iter.fold_mapWithPostcondition 14 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.fold_mapM` idx 16: necessary; the hand8/hand10 model of Std.Iter.fold_mapM idx 12, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.fold_mapM.h16 : ¬ drop0% Std.WP.Spec.Iter.fold_mapM 16 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.fold_filterWithPostcondition` idx 13: necessary; the hand8/hand10 model of Std.Iter.fold_filterWithPostcondition idx 9, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.fold_filterWithPostcondition.h13 : ¬ drop0% Std.WP.Spec.Iter.fold_filterWithPostcondition 13 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

-- `Std.WP.Spec.Iter.fold_filterM` idx 15: necessary; the hand8/hand10 model of Std.Iter.fold_filterM idx 11, transferred with the exact WP (tag 1 (fails (none) in Option, default elsewhere) on [1, 2])
theorem WPS.Iter.fold_filterM.h15 : ¬ drop0% Std.WP.Spec.Iter.fold_filterM 15 := fun h => by
  letI := WPSpecHand.exWPM (Option) Nat
  have := WPSpecHand.ex_eq (Option) Nat (h (α := BL 1 Nat) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2]) (Pred := (Option) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Option) Nat _))
  clear h; revert this; ev

end ItLoopHand

end IL


/-! ## Models and refutations after OpD1Hand.lean -/

section D1

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


/-! ### Transferred refutations (WPSpec) -/

-- `Std.WP.Spec.Iter.forIn_filterMapWithPostcondition` idx 17: necessary; the hand8/hand10 model of Std.Iter.forIn_filterMapWithPostcondition idx 13, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.forIn_filterMapWithPostcondition.h17 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMapWithPostcondition 17 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.forIn_filterMapM` idx 19: necessary; the hand8/hand10 model of Std.Iter.forIn_filterMapM idx 15, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.forIn_filterMapM.h19 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMapM 19 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.forIn_filterMap` idx 12: necessary; the hand8/hand10 model of Std.Iter.forIn_filterMap idx 8, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.forIn_filterMap.h12 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMap 12 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := some) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := some) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.forIn_mapWithPostcondition` idx 17: necessary; the hand8/hand10 model of Std.Iter.forIn_mapWithPostcondition idx 13, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.forIn_mapWithPostcondition.h17 : ¬ drop0% Std.WP.Spec.Iter.forIn_mapWithPostcondition 17 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure x) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure x) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.forIn_mapM` idx 19: necessary; the hand8/hand10 model of Std.Iter.forIn_mapM idx 15, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.forIn_mapM.h19 : ¬ drop0% Std.WP.Spec.Iter.forIn_mapM 19 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := pure) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := pure) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.forIn_map` idx 12: necessary; the hand8/hand10 model of Std.Iter.forIn_map idx 8, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.forIn_map.h12 : ¬ drop0% Std.WP.Spec.Iter.forIn_map 12 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := id) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := id) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.forIn_filterWithPostcondition` idx 16: necessary; the hand8/hand10 model of Std.Iter.forIn_filterWithPostcondition idx 12, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.forIn_filterWithPostcondition.h16 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterWithPostcondition 16 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.forIn_filterM` idx 18: necessary; the hand8/hand10 model of Std.Iter.forIn_filterM idx 14, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.forIn_filterM.h18 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterM 18 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.forIn_filter` idx 11: necessary; the hand8/hand10 model of Std.Iter.forIn_filter idx 7, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.forIn_filter.h11 : ¬ drop0% Std.WP.Spec.Iter.forIn_filter 11 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun _ => true) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun _ => true) (g := fun c _ => pure (.done c)) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.foldM_filterMapWithPostcondition` idx 9: necessary; the hand8/hand10 model of Std.Iter.foldM_filterMapWithPostcondition idx 7, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.foldM_filterMapWithPostcondition.h9 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMapWithPostcondition 9 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.foldM_filterMapM` idx 9: necessary; the hand8/hand10 model of Std.Iter.foldM_filterMapM idx 7, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.foldM_filterMapM.h9 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMapM 9 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.foldM_mapWithPostcondition` idx 10: necessary; the hand8/hand10 model of Std.Iter.foldM_mapWithPostcondition idx 8, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.foldM_mapWithPostcondition.h10 : ¬ drop0% Std.WP.Spec.Iter.foldM_mapWithPostcondition 10 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (m := Id) (n := Id) (o := Id) (f := fun x => pure x) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (m := Id) (n := Id) (o := Id) (f := fun x => pure x) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.foldM_mapM` idx 9: necessary; the hand8/hand10 model of Std.Iter.foldM_mapM idx 7, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.foldM_mapM.h9 : ¬ drop0% Std.WP.Spec.Iter.foldM_mapM 9 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := pure) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := pure) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.foldM_filterWithPostcondition` idx 8: necessary; the hand8/hand10 model of Std.Iter.foldM_filterWithPostcondition idx 6, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.foldM_filterWithPostcondition.h8 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterWithPostcondition 8 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.foldM_filterM` idx 8: necessary; the hand8/hand10 model of Std.Iter.foldM_filterM idx 6, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.foldM_filterM.h8 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterM 8 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (o := Id) (f := fun _ => pure (.up true)) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.foldM_filterMap` idx 8: necessary; the hand8/hand10 model of Std.Iter.foldM_filterMap idx 6, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.foldM_filterMap.h8 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMap 8 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := some) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := some) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.foldM_map` idx 8: necessary; the hand8/hand10 model of Std.Iter.foldM_map idx 6, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.foldM_map.h8 : ¬ drop0% Std.WP.Spec.Iter.foldM_map 8 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := id) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := id) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.foldM_filter` idx 7: necessary; the hand8/hand10 model of Std.Iter.foldM_filter idx 5, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.foldM_filter.h7 : ¬ drop0% Std.WP.Spec.Iter.foldM_filter 7 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun _ => true) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun _ => true) (g := fun _ c => pure c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.fold_filterMapWithPostcondition` idx 8: necessary; the hand8/hand10 model of Std.Iter.fold_filterMapWithPostcondition idx 6, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.fold_filterMapWithPostcondition.h8 : ¬ drop0% Std.WP.Spec.Iter.fold_filterMapWithPostcondition 8 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun x => pure (some x)) (g := fun _ c => c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun x => pure (some x)) (g := fun _ c => c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.fold_filterMapM` idx 8: necessary; the hand8/hand10 model of Std.Iter.fold_filterMapM idx 6, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.fold_filterMapM.h8 : ¬ drop0% Std.WP.Spec.Iter.fold_filterMapM 8 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun x => pure (some x)) (g := fun _ c => c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun x => pure (some x)) (g := fun _ c => c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.fold_mapWithPostcondition` idx 8: necessary; the hand8/hand10 model of Std.Iter.fold_mapWithPostcondition idx 6, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.fold_mapWithPostcondition.h8 : ¬ drop0% Std.WP.Spec.Iter.fold_mapWithPostcondition 8 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun x => pure x) (g := fun _ c => c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun x => pure x) (g := fun _ c => c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.fold_mapM` idx 8: necessary; the hand8/hand10 model of Std.Iter.fold_mapM idx 6, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.fold_mapM.h8 : ¬ drop0% Std.WP.Spec.Iter.fold_mapM 8 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := pure) (g := fun _ c => c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := pure) (g := fun _ c => c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.fold_filterWithPostcondition` idx 7: necessary; the hand8/hand10 model of Std.Iter.fold_filterWithPostcondition idx 5, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.fold_filterWithPostcondition.h7 : ¬ drop0% Std.WP.Spec.Iter.fold_filterWithPostcondition 7 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun _ => pure (.up true)) (g := fun _ c => c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun _ => pure (.up true)) (g := fun _ c => c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

-- `Std.WP.Spec.Iter.fold_filterM` idx 7: necessary; the hand8/hand10 model of Std.Iter.fold_filterM idx 5, transferred with the exact WP (non-finite AD; the side through the base loop gives 0 with ADLoop 0 and 1 with ADLoop 1, the other side does not depend on the base loop)
theorem WPS.Iter.fold_filterM.h7 : ¬ drop0% Std.WP.Spec.Iter.fold_filterM 7 := fun h =>
  two (α := Nat) (a := 0) (b := 1) (by decide)
    (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun _ => pure (.up true)) (g := fun _ c => c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))
    (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id)
        letI := WPSpecHand.exWPM (Id) Nat; exact WPSpecHand.ex_eq (Id) Nat (h (α := AD) (it := AD.it) (n := Id) (f := fun _ => pure (.up true)) (g := fun _ c => c) (init := (0 : Nat)) (Pred := (Id) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Id) Nat _)))

end OpD1Hand

end D1


/-! ## Models and refutations after OpD2Hand.lean -/

section D2

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

/-! Support for the independent rows: at `LP`/`Option` the instance of `T'` is exactly the
equation between two opaque `extrinsicFix₃` values at different arguments, so `¬T'` follows from
any interpretation of `opaqueFix₃` in which they differ. -/

-- support for Std.IterM.any_filterMapM, idx 6: at LP/Option the instance of T' is the equation between two opaque values
theorem IterM.any_filterMapM.h6_support
    (hne : (lp.filterMapM (m := Option) (n := Option) (fun (_ : Nat) => (pure none : Option (Option Nat)))).any (fun (_ : Nat) => false) ≠
      (lp.mapM (m := Option) (pure (f := Option))).anyM (fun x => do match ← (pure none : Option (Option Nat)) with | some fx => return .up ((fun (_ : Nat) => false) fx) | none => return .up false)) :
    ¬ drop0% Std.IterM.any_filterMapM 6 := fun h =>
  hne (@h LP Nat Nat Option Option _ _ (OL true) _ _ _ _ _ _ _ (OL.lawful true) lp (fun _ => pure none) (fun _ => false))

-- support for Std.IterM.any_mapM, idx 6: at LP/Option the instance of T' is the equation between two opaque values
theorem IterM.any_mapM.h6_support
    (hne : (lp.mapM (m := Option) (n := Option) (fun (_ : Nat) => (pure 0 : Option Nat))).any (fun (_ : Nat) => false) ≠
      (lp.mapM (m := Option) (pure (f := Option))).anyM (fun x => (.up <| (fun (_ : Nat) => false) ·) <$> ((fun (_ : Nat) => (pure 0 : Option Nat)) x))) :
    ¬ drop0% Std.IterM.any_mapM 6 := fun h =>
  hne (@h LP Nat Nat Option Option _ _ (OL true) _ _ _ _ _ _ _ (OL.lawful true) lp (fun _ => pure 0) (fun _ => false))

-- support for Std.IterM.any_filterM, idx 5: at LP/Option the instance of T' is the equation between two opaque values
theorem IterM.any_filterM.h5_support
    (hne : (lp.filterM (m := Option) (n := Option) (fun (_ : Nat) => (pure (.up false) : Option (ULift Bool)))).any (fun (_ : Nat) => false) ≠
      (lp.mapM (m := Option) (pure (f := Option))).anyM (fun x => do if (← (pure (.up false) : Option (ULift Bool))).down then return .up ((fun (_ : Nat) => false) x) else return .up false)) :
    ¬ drop0% Std.IterM.any_filterM 5 := fun h =>
  hne (@h LP Nat Option Option _ _ (OL true) _ _ _ _ _ _ _ (OL.lawful true) lp (fun _ => pure (.up false)) (fun _ => false))

-- support for Std.IterM.all_filterMapM, idx 6: at LP/Option the instance of T' is the equation between two opaque values
theorem IterM.all_filterMapM.h6_support
    (hne : (lp.filterMapM (m := Option) (n := Option) (fun (_ : Nat) => (pure none : Option (Option Nat)))).all (fun (_ : Nat) => false) ≠
      (lp.mapM (m := Option) (pure (f := Option))).allM (fun x => do match ← (pure none : Option (Option Nat)) with | some fx => return .up ((fun (_ : Nat) => false) fx) | none => return .up true)) :
    ¬ drop0% Std.IterM.all_filterMapM 6 := fun h =>
  hne (@h LP Nat Nat Option Option _ _ (OL true) _ _ _ _ _ _ _ (OL.lawful true) lp (fun _ => pure none) (fun _ => false))

-- support for Std.IterM.all_mapM, idx 6: at LP/Option the instance of T' is the equation between two opaque values
theorem IterM.all_mapM.h6_support
    (hne : (lp.mapM (m := Option) (n := Option) (fun (_ : Nat) => (pure 0 : Option Nat))).all (fun (_ : Nat) => false) ≠
      (lp.mapM (m := Option) (pure (f := Option))).allM (fun x => (.up <| (fun (_ : Nat) => false) ·) <$> ((fun (_ : Nat) => (pure 0 : Option Nat)) x))) :
    ¬ drop0% Std.IterM.all_mapM 6 := fun h =>
  hne (@h LP Nat Nat Option Option _ _ (OL true) _ _ _ _ _ _ _ (OL.lawful true) lp (fun _ => pure 0) (fun _ => false))

-- support for Std.IterM.all_filterM, idx 5: at LP/Option the instance of T' is the equation between two opaque values
theorem IterM.all_filterM.h5_support
    (hne : (lp.filterM (m := Option) (n := Option) (fun (_ : Nat) => (pure (.up false) : Option (ULift Bool)))).all (fun (_ : Nat) => false) ≠
      (lp.mapM (m := Option) (pure (f := Option))).allM (fun x => do if (← (pure (.up false) : Option (ULift Bool))).down then return .up ((fun (_ : Nat) => false) x) else return .up true)) :
    ¬ drop0% Std.IterM.all_filterM 5 := fun h =>
  hne (@h LP Nat Option Option _ _ (OL true) _ _ _ _ _ _ _ (OL.lawful true) lp (fun _ => pure (.up false)) (fun _ => false))


/-! ### Transferred refutations (WPSpec) -/

-- `Std.WP.Spec.IterM.forIn_filterMapWithPostcondition` idx 22: necessary; the hand10 two-loop model of Std.IterM.forIn_filterMapWithPostcondition idx 18, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.forIn_filterMapWithPostcondition.h22 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapWithPostcondition 22 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (β₂ := Nat) (γ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (β₂ := Nat) (γ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.forIn_filterMapM` idx 24: necessary; the hand10 two-loop model of Std.IterM.forIn_filterMapM idx 20, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.forIn_filterMapM.h24 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapM 24 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (β₂ := Nat) (γ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (β₂ := Nat) (γ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.forIn_filterMap` idx 17: necessary; the hand10 two-loop model of Std.IterM.forIn_filterMap idx 13, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.forIn_filterMap.h17 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMap 17 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (β₂ := Nat) (γ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (β₂ := Nat) (γ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.forIn_mapWithPostcondition` idx 22: necessary; the hand10 two-loop model of Std.IterM.forIn_mapWithPostcondition idx 18, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.forIn_mapWithPostcondition.h22 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapWithPostcondition 22 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (β₂ := Nat) (γ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (β₂ := Nat) (γ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.forIn_mapM` idx 24: necessary; the hand10 two-loop model of Std.IterM.forIn_mapM idx 20, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.forIn_mapM.h24 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapM 24 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (β₂ := Nat) (γ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (β₂ := Nat) (γ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.forIn_map` idx 17: necessary; the hand10 two-loop model of Std.IterM.forIn_map idx 13, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.forIn_map.h17 : ¬ drop0% Std.WP.Spec.IterM.forIn_map 17 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (β₂ := Nat) (γ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (β₂ := Nat) (γ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.forIn_filterWithPostcondition` idx 21: necessary; the hand10 two-loop model of Std.IterM.forIn_filterWithPostcondition idx 17, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.forIn_filterWithPostcondition.h21 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterWithPostcondition 21 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.forIn_filterM` idx 23: necessary; the hand10 two-loop model of Std.IterM.forIn_filterM idx 19, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.forIn_filterM.h23 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterM 23 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.forIn_filter` idx 16: necessary; the hand10 two-loop model of Std.IterM.forIn_filter idx 12, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.forIn_filter.h16 : ¬ drop0% Std.WP.Spec.IterM.forIn_filter 16 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun _ acc => pure (.yield acc)) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.foldM_filterMapWithPostcondition` idx 10: necessary; the hand10 two-loop model of Std.IterM.foldM_filterMapWithPostcondition idx 8, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.foldM_filterMapWithPostcondition.h10 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapWithPostcondition 10 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.foldM_filterMapM` idx 10: necessary; the hand10 two-loop model of Std.IterM.foldM_filterMapM idx 8, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.foldM_filterMapM.h10 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapM 10 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.foldM_mapWithPostcondition` idx 10: necessary; the hand10 two-loop model of Std.IterM.foldM_mapWithPostcondition idx 8, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.foldM_mapWithPostcondition.h10 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapWithPostcondition 10 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.foldM_mapM` idx 10: necessary; the hand10 two-loop model of Std.IterM.foldM_mapM idx 8, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.foldM_mapM.h10 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapM 10 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.foldM_filterWithPostcondition` idx 9: necessary; the hand10 two-loop model of Std.IterM.foldM_filterWithPostcondition idx 7, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.foldM_filterWithPostcondition.h9 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterWithPostcondition 9 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (δ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (δ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.foldM_filterM` idx 9: necessary; the hand10 two-loop model of Std.IterM.foldM_filterM idx 7, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.foldM_filterM.h9 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterM 9 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (δ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (δ := Nat) (m := Option) (n := Option) (o := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.foldM_filterMap` idx 9: necessary; the hand10 two-loop model of Std.IterM.foldM_filterMap idx 7, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.foldM_filterMap.h9 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMap 9 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.foldM_map` idx 9: necessary; the hand10 two-loop model of Std.IterM.foldM_map idx 7, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.foldM_map.h9 : ¬ drop0% Std.WP.Spec.IterM.foldM_map 9 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.foldM_filter` idx 8: necessary; the hand10 two-loop model of Std.IterM.foldM_filter idx 6, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.foldM_filter.h8 : ¬ drop0% Std.WP.Spec.IterM.foldM_filter 8 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun d _ => pure d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.fold_filterMapWithPostcondition` idx 9: necessary; the hand10 two-loop model of Std.IterM.fold_filterMapWithPostcondition idx 7, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.fold_filterMapWithPostcondition.h9 : ¬ drop0% Std.WP.Spec.IterM.fold_filterMapWithPostcondition 9 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.fold_filterMapM` idx 9: necessary; the hand10 two-loop model of Std.IterM.fold_filterMapM idx 7, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.fold_filterMapM.h9 : ¬ drop0% Std.WP.Spec.IterM.fold_filterMapM 9 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.fold_mapWithPostcondition` idx 9: necessary; the hand10 two-loop model of Std.IterM.fold_mapWithPostcondition idx 7, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.fold_mapWithPostcondition.h9 : ¬ drop0% Std.WP.Spec.IterM.fold_mapWithPostcondition 9 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.fold_mapM` idx 9: necessary; the hand10 two-loop model of Std.IterM.fold_mapM idx 7, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.fold_mapM.h9 : ¬ drop0% Std.WP.Spec.IterM.fold_mapM 9 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.fold_filterWithPostcondition` idx 8: necessary; the hand10 two-loop model of Std.IterM.fold_filterWithPostcondition idx 6, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.fold_filterWithPostcondition.h8 : ¬ drop0% Std.WP.Spec.IterM.fold_filterWithPostcondition 8 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.fold_filterM` idx 8: necessary; the hand10 two-loop model of Std.IterM.fold_filterM idx 6, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.fold_filterM.h8 : ¬ drop0% Std.WP.Spec.IterM.fold_filterM 8 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (δ := Nat) (m := Option) (n := Option) (it := lp) (f := fun _ => pure default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.fold_filterMap` idx 8: necessary; the hand10 two-loop model of Std.IterM.fold_filterMap idx 6, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.fold_filterMap.h8 : ¬ drop0% Std.WP.Spec.IterM.fold_filterMap 8 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.fold_map` idx 8: necessary; the hand10 two-loop model of Std.IterM.fold_map idx 6, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.fold_map.h8 : ¬ drop0% Std.WP.Spec.IterM.fold_map 8 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (γ := Nat) (δ := Nat) (m := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

-- `Std.WP.Spec.IterM.fold_filter` idx 7: necessary; the hand10 two-loop model of Std.IterM.fold_filter idx 5, transferred with the exact WP ((inst): base LP skips forever; base side some init (OL true) vs. none (OL false), combinator side is the same term)
theorem WPS.IterM.fold_filter.h7 : ¬ drop0% Std.WP.Spec.IterM.fold_filter 7 := fun h =>
  WPSpecHand.two (a := some 0) (b := none) (by decide)
    (by letI := OL true; haveI := OL.lawful true; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (δ := Nat) (m := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))
    (by letI := OL false; haveI := OL.lawful false; letI := WPSpecHand.exWPM Option Nat
        exact WPSpecHand.ex_eq Option Nat (h (α := LP) (β := Nat) (δ := Nat) (m := Option) (it := lp) (f := fun _ => default) (init := (0 : Nat)) (g := fun d _ => d) (Pred := Option Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self Option Nat _)))

end OpD2Hand

end D2


/-! ## Models and refutations after ItMonadMAHand.lean -/

section MA

open Std Std.Iterators Std.Iterators.Types Std.Internal

namespace ItMonadMAHand

/-! ## Unfolding lemmas for the consumers, without monad laws -/

theorem toArray_go_eq {α β : Type} {m : Type → Type} [Monad m] [Iterator α m β] [Finite α m]
    (it : IterM (α := α) m β) (acc : Array β) :
    IterM.toArray.go it acc = (do
      match (← it.step).inflate with
      | .yield it' out _ => IterM.toArray.go it' (acc.push out)
      | .skip it' _ => IterM.toArray.go it' acc
      | .done _ => return acc) := by
  rw [IterM.toArray.go, WellFounded.extrinsicFix₂_eq_apply]
  · rfl
  · simp only [show (IterM.finitelyManySteps! = IterM.finitelyManySteps) by rfl]
    exact InvImage.wf _ WellFoundedRelation.wf

theorem toListRev_go_eq {α β : Type} {m : Type → Type} [Monad m] [Iterator α m β] [Finite α m]
    (it : IterM (α := α) m β) (acc : List β) :
    IterM.toListRev.go it acc = (do
      match (← it.step).inflate with
      | .yield it' out _ => IterM.toListRev.go it' (out :: acc)
      | .skip it' _ => IterM.toListRev.go it' acc
      | .done _ => return acc) := by
  rw [IterM.toListRev.go, WellFounded.extrinsicFix₂_eq_apply]
  · apply bind_congr; intro s
    cases s.inflate using PlausibleIterStep.casesOn <;> rfl
  · simp only [show (IterM.finitelyManySteps! = IterM.finitelyManySteps) by rfl]
    exact InvImage.wf _ WellFoundedRelation.wf

theorem forIn'_eq {α β : Type} {m : Type → Type} [Iterator α m β] [Finite α m] {n : Type → Type}
    [Monad n] (lift : (γ : Type) → (δ : Type) → (γ → n δ) → m γ → n δ) (γ : Type)
    (Pl : β → γ → ForInStep γ → Prop) (it : IterM (α := α) m β) (init : γ) (P : β → Prop)
    (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b)
    (f : (b : β) → P b → (c : γ) → n (Subtype (Pl b c))) :
    IterM.DefaultConsumers.forIn' lift γ Pl it init P hP f =
      (lift _ _ · it.step) fun s =>
        match s.inflate with
        | .yield it' out h => do
          match ← f out (hP out <| .direct ⟨_, h⟩) init with
          | ⟨.yield c, _⟩ =>
            (IterM.DefaultConsumers.forIn' lift γ Pl it' c P
              (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f)
          | ⟨.done c, _⟩ => return c
        | .skip it' h =>
            (IterM.DefaultConsumers.forIn' lift γ Pl it' init P
              (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f)
        | .done _ => return init := by
  haveI : Nonempty γ := ⟨init⟩
  rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply]
  · congr 1; funext s
    cases s.inflate using PlausibleIterStep.casesOn
    · apply bind_congr; intro r
      rcases r with ⟨_ | _, _⟩ <;> rfl
    · rfl
    · rfl
  · exact InvImage.wf _ IteratorLoop.wellFounded_of_finite

/-- The step of a `map`-type iterator, stated on the `Map` type (unfolding the combinator to
`FilterMap` would produce terms that only typecheck up to unfolding `Map`). -/
theorem map_step_eq {α β γ : Type} {m n : Type → Type} [Monad n] [Iterator α m β]
    {lift : ⦃α : Type⦄ → m α → n α} {f : β → PostconditionT n γ} (it : IterM (α := α) m β) :
    (IterM.InternalCombinators.map lift f it).step = (do
      match (← lift it.step).inflate with
      | .yield it' out h => do
        match ← (PostconditionT.map some (f out)).operation with
        | ⟨none, h'⟩ => pure (.deflate
            (.skip (IterM.InternalCombinators.map lift f it') (by exact .yieldNone h h')))
        | ⟨some out', h'⟩ => pure (.deflate
            (.yield (IterM.InternalCombinators.map lift f it') out' (by exact .yieldSome h h')))
      | .skip it' h => pure (.deflate
          (.skip (IterM.InternalCombinators.map lift f it') (by exact .skip h)))
      | .done h => pure (.deflate (.done (by exact .done h)))) := by
  apply bind_congr; intro s
  obtain ⟨t, rfl⟩ : ∃ t, s = Shrink.deflate t := ⟨s.inflate, Shrink.deflate_inflate.symm⟩
  rcases t with ⟨_ | _ | _, h⟩ <;> (try simp only [Shrink.inflate_deflate]) <;>
    (try erw [Shrink.inflate_deflate]) <;> (try rfl) <;>
    (apply bind_congr; intro r; rcases r with ⟨_ | _, _⟩ <;> rfl)

theorem filterMap_step_eq {α β γ : Type} {m n : Type → Type} [Monad n] [Iterator α m β]
    {lift : ⦃α : Type⦄ → m α → n α} {f : β → PostconditionT n (Option γ)}
    (it : IterM (α := α) m β) :
    (IterM.InternalCombinators.filterMap lift f it).step = (do
      match (← lift it.step).inflate with
      | .yield it' out h => do
        match ← (f out).operation with
        | ⟨none, h'⟩ => pure (.deflate
            (.skip (IterM.InternalCombinators.filterMap lift f it') (by exact .yieldNone h h')))
        | ⟨some out', h'⟩ => pure (.deflate
            (.yield (IterM.InternalCombinators.filterMap lift f it') out' (by exact .yieldSome h h')))
      | .skip it' h => pure (.deflate
          (.skip (IterM.InternalCombinators.filterMap lift f it') (by exact .skip h)))
      | .done h => pure (.deflate (.done (by exact .done h)))) := by
  apply bind_congr; intro s
  obtain ⟨t, rfl⟩ : ∃ t, s = Shrink.deflate t := ⟨s.inflate, Shrink.deflate_inflate.symm⟩
  rcases t with ⟨_ | _ | _, h⟩ <;> (try simp only [Shrink.inflate_deflate]) <;>
    (try erw [Shrink.inflate_deflate]) <;> (try rfl) <;>
    (apply bind_congr; intro r; rcases r with ⟨_ | _, _⟩ <;> rfl)

theorem attach_step_eq {α β : Type} {m : Type → Type} [Monad m] [Iterator α m β] {P : β → Prop}
    (it : IterM (α := Attach α m P) m {out : β // P out}) :
    it.step = (fun step => .deflate ⟨Attach.Monadic.modifyStep it step.inflate, step.inflate, rfl⟩) <$>
      it.internalState.inner.step := rfl

theorem list_step_nil {β : Type} {m : Type → Type} [Pure m] :
    (([] : List β).iterM m).step = pure (.deflate ⟨.done, rfl⟩) := rfl
theorem list_step_cons {β : Type} {m : Type → Type} [Pure m] (x : β) (xs : List β) :
    ((x :: xs).iterM m).step = pure (.deflate ⟨.yield (xs.iterM m) x, rfl⟩) := rfl

/-! ## An `IteratorLoop` instance that is lawful but returns `init` for non-lawful lift functions -/

set_option warn.classDefReducibility false in
open Classical in
noncomputable def evilLoop {α β : Type} {m n : Type → Type} [Monad m] [Monad n] [Iterator α m β] :
    IteratorLoop α m n where
  forIn lift γ Pl it init f :=
    if LawfulMonadLiftBindFunction lift then
      IteratorLoop.defaultImplementation.forIn lift γ Pl it init f
    else pure init

open Classical in
theorem evilLoop_lawful {α β : Type} {m n : Type → Type} [Monad m] [Monad n] [Iterator α m β] :
    letI : IteratorLoop α m n := evilLoop
    LawfulIteratorLoop α m n := by
  letI : IteratorLoop α m n := evilLoop
  constructor
  intro lift hl γ it init Pl wf f
  show (if LawfulMonadLiftBindFunction lift then _ else _) = _
  rw [if_pos hl]

open Classical in
theorem evilLoop_forIn {α β : Type} {m n : Type → Type} [Monad m] [Monad n] [Iterator α m β]
    {lift} {γ Pl it init f} (h : ¬ LawfulMonadLiftBindFunction lift) :
    (evilLoop (α := α) (β := β) (m := m) (n := n)).forIn lift γ Pl it init f = pure init := by
  show (if LawfulMonadLiftBindFunction lift then _ else _) = _
  rw [if_neg h]

theorem not_lawful_of {m n : Type → Type} [Monad m] [Monad n]
    {L : (γ : Type) → (δ : Type) → (γ → n δ) → m γ → n δ} {γ δ : Type} (f : γ → n δ) (a : γ)
    (h : L γ δ f (pure a) ≠ f a) : ¬ LawfulMonadLiftBindFunction L :=
  fun hl => h (hl.liftBind_pure f a)

/-! ## Monads -/

theorem pc_attachLift_op {m : Type → Type} [MonadAttach m] {α : Type} (x : m α) :
    (PostconditionT.attachLift x).operation = MonadAttach.attach x := rfl
theorem pc_lift_op {m : Type → Type} [Functor m] {α : Type} (x : m α) :
    (PostconditionT.lift x).operation = (fun a => ⟨a, .intro⟩) <$> x := rfl
theorem pc_pure_op {m : Type → Type} [Pure m] {α : Type} (a : α) :
    (PostconditionT.pure a : PostconditionT m α).operation = pure ⟨a, rfl⟩ := rfl
theorem pc_map_op {m : Type → Type} [Functor m] {α β : Type} (f : α → β) (x : PostconditionT m α) :
    (PostconditionT.map f x).operation =
      Functor.map (β := Subtype (PostconditionT.map f x).Property)
        (fun a => ⟨f a.val, _, rfl⟩) x.operation := rfl
theorem ml_lift {m n : Type → Type} (f : {α : Type} → m α → n α) {α : Type} (x : m α) :
    @MonadLift.monadLift m n ⟨@f⟩ α x = f x := rfl
theorem ml_trans {m n o : Type → Type} [MonadLift n o] [MonadLiftT m n] {α : Type} (x : m α) :
    (monadLift x : o α) = MonadLift.monadLift (monadLift x : n α) := rfl
theorem ml_Id {n : Type → Type} [Pure n] {α : Type} (x : Id α) : (monadLift x : n α) = pure x.run := rfl
theorem Id_bind_eq {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl
theorem Id_pure_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl
theorem Id_map_eq {α β : Type} (f : α → β) (x : Id α) : f <$> x = f x := rfl

/-- Counting monad: `bind` adds one; `pure` and `map` add nothing. Not lawful. -/
structure CM (α : Type) where
  c : Nat
  v : α
instance : Monad CM where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c + 1, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
instance : MonadAttach CM := .trivial
theorem CM.attach_eq {α} (x : CM α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : WeaklyLawfulMonadAttach CM := ⟨rfl⟩
theorem CM.bind_eq {α β} (x : CM α) (f : α → CM β) : x >>= f = ⟨x.c + (f x.v).c + 1, (f x.v).v⟩ := rfl
theorem CM.pure_eq {α} (a : α) : (pure a : CM α) = ⟨0, a⟩ := rfl
theorem CM.map_eq {α β} (f : α → β) (x : CM α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem CM.not_lawful {m : Type → Type} [Monad m] (lift : ⦃α : Type⦄ → m α → CM α) :
    ¬ LawfulMonadLiftBindFunction (m := m) (n := CM) (fun _ _ f x => lift x >>= f) :=
  not_lawful_of (m := m) (n := CM) (L := fun _ _ f x => lift x >>= f) (γ := Nat)
    (fun _ => (⟨0, 0⟩ : CM Nat)) 0 (by simp [CM.bind_eq])

/-- Counting monad where `map` also adds one. Not lawful. -/
structure CM2 (α : Type) where
  c : Nat
  v : α
instance : Monad CM2 where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c + 1, (f x.v).v⟩
  map f x := ⟨x.c + 1, f x.v⟩
instance : MonadAttach CM2 := .trivial
theorem CM2.bind_eq {α β} (x : CM2 α) (f : α → CM2 β) : x >>= f = ⟨x.c + (f x.v).c + 1, (f x.v).v⟩ := rfl
theorem CM2.pure_eq {α} (a : α) : (pure a : CM2 α) = ⟨0, a⟩ := rfl
theorem CM2.map_eq {α β} (f : α → β) (x : CM2 α) : f <$> x = ⟨x.c + 1, f x.v⟩ := rfl
theorem CM2.attach_eq {α} (x : CM2 α) : MonadAttach.attach x = ⟨x.c + 1, ⟨x.v, trivial⟩⟩ := rfl

/-- Bind adds one exactly when the continuation's result has a nonzero count: `pure`/`pure` binds
are free (so `pure` from a lawful monad is a lawful lift), but `pure a >>= f ≠ f a`. -/
structure QM (α : Type) where
  c : Nat
  v : α
instance : Monad QM where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c + min (f x.v).c 1, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
instance : MonadAttach QM := .trivial
theorem QM.attach_eq {α} (x : QM α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : WeaklyLawfulMonadAttach QM := ⟨rfl⟩
theorem QM.bind_eq {α β} (x : QM α) (f : α → QM β) :
    x >>= f = ⟨x.c + (f x.v).c + min (f x.v).c 1, (f x.v).v⟩ := rfl
theorem QM.pure_eq {α} (a : α) : (pure a : QM α) = ⟨0, a⟩ := rfl
theorem QM.map_eq {α β} (f : α → β) (x : QM α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
instance : LawfulMonadLiftT Id QM where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
theorem QM.not_lawful {m : Type → Type} [Monad m] (lift : ⦃α : Type⦄ → m α → QM α) :
    ¬ LawfulMonadLiftBindFunction (m := m) (n := QM) (fun _ _ f x => lift x >>= f) :=
  not_lawful_of (m := m) (n := QM) (L := fun _ _ f x => lift x >>= f) (γ := Nat)
    (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by simp [QM.bind_eq])

/-- Weighted counting monad: `bind x f` doubles the count of `x`. `pure` from `Id` is a lawful lift
and `pure a >>= f = f a`, but `x >>= pure ≠ x` and `bind` is not associative. -/
structure WM (α : Type) where
  c : Nat
  v : α
instance : Monad WM where
  pure a := ⟨0, a⟩
  bind x f := ⟨2 * x.c + (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
instance : MonadAttach WM := .trivial
instance : WeaklyLawfulMonadAttach WM := ⟨rfl⟩
theorem WM.bind_eq {α β} (x : WM α) (f : α → WM β) : x >>= f = ⟨2 * x.c + (f x.v).c, (f x.v).v⟩ := rfl
theorem WM.pure_eq {α} (a : α) : (pure a : WM α) = ⟨0, a⟩ := rfl
theorem WM.map_eq {α β} (f : α → β) (x : WM α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem WM.attach_eq {α} (x : WM α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : LawfulMonadLiftT Id WM where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

/-- Lawful `Nat` writer. -/
structure NW (α : Type) where
  c : Nat
  v : α
instance : Monad NW where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
theorem NW.bind_eq {α β} (x : NW α) (f : α → NW β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := rfl
theorem NW.pure_eq {α} (a : α) : (pure a : NW α) = ⟨0, a⟩ := rfl
theorem NW.map_eq {α β} (f : α → β) (x : NW α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem NW.ext' {α} {x y : NW α} (h1 : x.c = y.c) (h2 : x.v = y.v) : x = y := by
  cases x; cases y; simp_all
instance : LawfulMonad NW := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => NW.ext' (Nat.zero_add _) rfl)
  (bind_assoc := fun _ _ _ => NW.ext' (Nat.add_assoc _ _ _) rfl)
  (bind_pure_comp := fun _ _ => rfl)
instance : MonadAttach NW := .trivial
theorem NW.attach_eq {α} (x : NW α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : WeaklyLawfulMonadAttach NW := ⟨rfl⟩

/-- Lawful `Bool` writer (`or`). -/
structure W (α : Type) where
  c : Bool
  v : α
instance : Monad W where
  pure a := ⟨false, a⟩
  bind x f := ⟨x.c || (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
theorem W.bind_eq {α β} (x : W α) (f : α → W β) : x >>= f = ⟨x.c || (f x.v).c, (f x.v).v⟩ := rfl
theorem W.pure_eq {α} (a : α) : (pure a : W α) = ⟨false, a⟩ := rfl
theorem W.map_eq {α β} (f : α → β) (x : W α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem W.ext' {α} {x y : W α} (h1 : x.c = y.c) (h2 : x.v = y.v) : x = y := by
  cases x; cases y; simp_all
instance : LawfulMonad W := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => W.ext' (Bool.false_or _) rfl)
  (bind_assoc := fun _ _ _ => W.ext' (Bool.or_assoc _ _ _) rfl)
  (bind_pure_comp := fun _ _ => W.ext' (Bool.or_false _) rfl)
instance : MonadAttach W := .trivial
theorem W.attach_eq {α} (x : W α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : WeaklyLawfulMonadAttach W := ⟨rfl⟩

/-- `Bool` writer whose `map` and `attach` flip the flag: bind and pure are lawful, `map` is not. -/
structure FM (α : Type) where
  c : Bool
  v : α
instance : Monad FM where
  pure a := ⟨false, a⟩
  bind x f := ⟨x.c || (f x.v).c, (f x.v).v⟩
  map f x := ⟨!x.c, f x.v⟩
instance : MonadAttach FM where
  CanReturn _ _ := True
  attach x := ⟨!x.c, ⟨x.v, trivial⟩⟩
instance : WeaklyLawfulMonadAttach FM := ⟨by intro α x; cases x; simp [Functor.map, MonadAttach.attach]⟩
theorem FM.bind_eq {α β} (x : FM α) (f : α → FM β) : x >>= f = ⟨x.c || (f x.v).c, (f x.v).v⟩ := rfl
theorem FM.pure_eq {α} (a : α) : (pure a : FM α) = ⟨false, a⟩ := rfl
theorem FM.map_eq {α β} (f : α → β) (x : FM α) : f <$> x = ⟨!x.c, f x.v⟩ := rfl
theorem FM.attach_eq {α} (x : FM α) : MonadAttach.attach x = ⟨!x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : LawfulMonadLiftT Id FM where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
instance : MonadLift FM W := ⟨fun x => ⟨x.c, x.v⟩⟩
theorem FM.lift_eq {α} (x : FM α) : (MonadLift.monadLift x : W α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLift FM W where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

/-- Copies of `NW` (lawful), and variants with a broken `attach` (reset resp. increment the count). -/
structure NW2 (α : Type) where
  c : Nat
  v : α
instance : Monad NW2 where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
theorem NW2.bind_eq {α β} (x : NW2 α) (f : α → NW2 β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := rfl
theorem NW2.pure_eq {α} (a : α) : (pure a : NW2 α) = ⟨0, a⟩ := rfl
theorem NW2.map_eq {α β} (f : α → β) (x : NW2 α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem NW2.ext' {α} {x y : NW2 α} (h1 : x.c = y.c) (h2 : x.v = y.v) : x = y := by
  cases x; cases y; simp_all
instance : LawfulMonad NW2 := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => NW2.ext' (Nat.zero_add _) rfl)
  (bind_assoc := fun _ _ _ => NW2.ext' (Nat.add_assoc _ _ _) rfl)
  (bind_pure_comp := fun _ _ => rfl)
instance : MonadAttach NW2 := .trivial
theorem NW2.attach_eq {α} (x : NW2 α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : WeaklyLawfulMonadAttach NW2 := ⟨rfl⟩

/-- `NW` with an `attach` that drops the count (not weakly lawful). -/
structure NWa (α : Type) where
  c : Nat
  v : α
instance : Monad NWa where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
theorem NWa.bind_eq {α β} (x : NWa α) (f : α → NWa β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := rfl
theorem NWa.pure_eq {α} (a : α) : (pure a : NWa α) = ⟨0, a⟩ := rfl
theorem NWa.map_eq {α β} (f : α → β) (x : NWa α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem NWa.ext' {α} {x y : NWa α} (h1 : x.c = y.c) (h2 : x.v = y.v) : x = y := by
  cases x; cases y; simp_all
instance : LawfulMonad NWa := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => NWa.ext' (Nat.zero_add _) rfl)
  (bind_assoc := fun _ _ _ => NWa.ext' (Nat.add_assoc _ _ _) rfl)
  (bind_pure_comp := fun _ _ => rfl)
instance : MonadAttach NWa where
  CanReturn _ _ := True
  attach x := ⟨0, ⟨x.v, trivial⟩⟩
theorem NWa.attach_eq {α} (x : NWa α) : MonadAttach.attach x = ⟨0, ⟨x.v, trivial⟩⟩ := rfl
instance : LawfulMonadLiftT Id NWa where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
instance : MonadLift NWa NW := ⟨fun x => ⟨x.c, x.v⟩⟩
theorem NWa.lift_eq {α} (x : NWa α) : (MonadLift.monadLift x : NW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLift NWa NW where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

/-- `NW` with an `attach` that adds one to the count (not weakly lawful). -/
structure NWb (α : Type) where
  c : Nat
  v : α
instance : Monad NWb where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
theorem NWb.bind_eq {α β} (x : NWb α) (f : α → NWb β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := rfl
theorem NWb.pure_eq {α} (a : α) : (pure a : NWb α) = ⟨0, a⟩ := rfl
theorem NWb.map_eq {α β} (f : α → β) (x : NWb α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem NWb.ext' {α} {x y : NWb α} (h1 : x.c = y.c) (h2 : x.v = y.v) : x = y := by
  cases x; cases y; simp_all
instance : LawfulMonad NWb := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => NWb.ext' (Nat.zero_add _) rfl)
  (bind_assoc := fun _ _ _ => NWb.ext' (Nat.add_assoc _ _ _) rfl)
  (bind_pure_comp := fun _ _ => rfl)
instance : MonadAttach NWb where
  CanReturn _ _ := True
  attach x := ⟨x.c + 1, ⟨x.v, trivial⟩⟩
theorem NWb.attach_eq {α} (x : NWb α) : MonadAttach.attach x = ⟨x.c + 1, ⟨x.v, trivial⟩⟩ := rfl
instance : LawfulMonadLiftT Id NWb where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
instance : MonadLift NWb NW := ⟨fun x => ⟨x.c, x.v⟩⟩
theorem NWb.lift_eq {α} (x : NWb α) : (MonadLift.monadLift x : NW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLift NWb NW where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

/-- `NW` whose `map` adds one to the count (bind and pure are lawful, `map` is not). -/
structure MB (α : Type) where
  c : Nat
  v : α
instance : Monad MB where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c + 1, f x.v⟩
theorem MB.bind_eq {α β} (x : MB α) (f : α → MB β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := rfl
theorem MB.pure_eq {α} (a : α) : (pure a : MB α) = ⟨0, a⟩ := rfl
theorem MB.map_eq {α β} (f : α → β) (x : MB α) : f <$> x = ⟨x.c + 1, f x.v⟩ := rfl
instance : MonadLift MB NW := ⟨fun x => ⟨x.c, x.v⟩⟩
theorem MB.lift_eq {α} (x : MB α) : (MonadLift.monadLift x : NW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLift MB NW where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

/-- Lifts that add one to the count (not lawful). -/
@[instance_reducible] def tickNW2 : MonadLift NW2 NW := ⟨fun x => ⟨x.c + 1, x.v⟩⟩
@[instance_reducible] def tickNW : MonadLift NW NW2 := ⟨fun x => ⟨x.c + 1, x.v⟩⟩
theorem tickNW2_eq {α} (x : NW2 α) : @MonadLift.monadLift NW2 NW tickNW2 α x = ⟨x.c + 1, x.v⟩ := rfl
theorem tickNW_eq {α} (x : NW α) : @MonadLift.monadLift NW NW2 tickNW α x = ⟨x.c + 1, x.v⟩ := rfl

/-- Lawful lifts out of `NW`: forgetting the count into `QM`, and the identity into `NWb`. -/
instance : MonadLift NW QM := ⟨fun x => ⟨0, x.v⟩⟩
theorem NW.liftQ_eq {α} (x : NW α) : (MonadLift.monadLift x : QM α) = ⟨0, x.v⟩ := rfl
instance : LawfulMonadLift NW QM where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
instance : MonadLift NW NWb := ⟨fun x => ⟨x.c, x.v⟩⟩
theorem NW.liftB_eq {α} (x : NW α) : (MonadLift.monadLift x : NWb α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLift NW NWb where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

/-- `Bool` writer whose `map` flips the flag iff the target type is a subsingleton, and whose
`attach` flips it iff the value type is a subsingleton (`CanReturn x a := a = x.v`). Bind and pure
are lawful, `attach` is weakly lawful, but `map` is not (it is not parametric). -/
structure SM (α : Type) where
  c : Bool
  v : α
open Classical in
noncomputable instance : Monad SM where
  pure a := ⟨false, a⟩
  bind x f := ⟨x.c || (f x.v).c, (f x.v).v⟩
  map {_ β} f x := ⟨xor x.c (decide (Subsingleton β)), f x.v⟩
open Classical in
noncomputable instance : MonadAttach SM where
  CanReturn x a := a = x.v
  attach {α} x := ⟨xor x.c (decide (Subsingleton α)), ⟨x.v, rfl⟩⟩
instance : WeaklyLawfulMonadAttach SM := ⟨by
  intro α x; cases x; simp [Functor.map, MonadAttach.attach]⟩
/-- A type with two distinct elements. -/
class NonSub (α : Type) : Prop where
  ns : ¬ Subsingleton α
instance : NonSub Nat := ⟨fun h => absurd (h.allEq 0 1) (by decide)⟩
instance : NonSub (ULift Bool) := ⟨fun h => absurd (h.allEq ⟨false⟩ ⟨true⟩) (by simp)⟩
instance {α : Type} [Inhabited α] : NonSub (Option α) :=
  ⟨fun h => absurd (h.allEq none (some default)) (by simp)⟩
theorem SM.bind_eq {α β} (x : SM α) (f : α → SM β) : x >>= f = ⟨x.c || (f x.v).c, (f x.v).v⟩ := rfl
theorem SM.pure_eq {α} (a : α) : (pure a : SM α) = ⟨false, a⟩ := rfl
theorem SM.map_sub {α β} [h : Subsingleton β] (f : α → β) (x : SM α) : f <$> x = ⟨!x.c, f x.v⟩ := by
  simp [Functor.map, h]
theorem SM.map_nsub {α β} [h : NonSub β] (f : α → β) (x : SM α) : f <$> x = ⟨x.c, f x.v⟩ := by
  simp [Functor.map, h.ns]
theorem SM.attach_nsub {α} [h : NonSub α] (x : SM α) :
    MonadAttach.attach x = ⟨x.c, ⟨x.v, rfl⟩⟩ := by
  simp [MonadAttach.attach, h.ns]
instance {α : Type} (x : SM α) : Subsingleton (Subtype (MonadAttach.CanReturn x)) :=
  ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
instance {m : Type → Type} [Pure m] {α : Type} (a : α) :
    Subsingleton (Subtype (PostconditionT.pure a : PostconditionT m α).Property) :=
  ⟨fun x y => Subtype.ext (x.2.symm.trans y.2)⟩
instance {m : Type → Type} [MonadAttach m] {α : Type} (x : m α)
    [Subsingleton (Subtype (MonadAttach.CanReturn x))] :
    Subsingleton (Subtype (PostconditionT.attachLift x).Property) :=
  inferInstanceAs (Subsingleton (Subtype (MonadAttach.CanReturn x)))
instance {m : Type → Type} [Functor m] {α β : Type} (g : α → β) (x : PostconditionT m α)
    [Subsingleton (Subtype x.Property)] :
    Subsingleton (Subtype (PostconditionT.map g x).Property) :=
  ⟨fun a b => by
    obtain ⟨_, a', rfl⟩ := a; obtain ⟨_, b', rfl⟩ := b
    rw [Subsingleton.elim a' b']⟩
instance : LawfulMonadLiftT Id SM where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
instance : MonadLift SM W := ⟨fun x => ⟨x.c, x.v⟩⟩
theorem SM.lift_eq {α} (x : SM α) : (MonadLift.monadLift x : W α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLift SM W where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

instance : LawfulMonadLiftT Id W where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
instance : LawfulMonadLiftT Id NW where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

end ItMonadMAHand

namespace ItMonadMAHand

/-- Structural unfolding of consumers, combinators and the list iterator (nothing that occurs in
types, so that types and instance arguments stay in sync). -/
macro "ev_unfold" : tactic => `(tactic| dsimp only [IterM.toArray, IterM.toList, IterM.toListRev,
  IterM.foldM, IterM.fold, IterM.anyM, IterM.allM, IterM.any, IterM.all, IterM.length,
  ForIn.forIn, ForIn'.forIn', instForInOfForIn', IterM.instForInOfIteratorLoop, IterM.instForIn',
  IteratorLoop.finiteForIn', IteratorLoop.defaultImplementation, IteratorLoop.forIn,
  ListIterator.instIteratorLoop, FilterMap.instIteratorLoop, Map.instIteratorLoop,
  IterM.filterMap, IterM.map, IterM.filter, IterM.filterMapM, IterM.mapM, IterM.filterM,
  IterM.filterWithPostcondition, IterM.mapWithPostcondition, IterM.filterMapWithPostcondition,
  Attach.Monadic.modifyStep, IterM.attachWith] at *)

/-- Monad operations of the models, lifts, `PostconditionT`, `Shrink`; never inside types. -/
macro "ev_simp" : tactic => `(tactic| simp (config := { dsimp := false }) only [liftM, ↓map_step_eq, ↓filterMap_step_eq, ↓list_step_nil, ↓list_step_cons,
  ↓IterM.step_append, ↓IterM.Intermediate.step_appendSnd, ↓attach_step_eq,
  ↓NWa.lift_eq, ↓NW.liftQ_eq, ↓NW.liftB_eq, ↓NWb.lift_eq, ↓MB.lift_eq, ↓tickNW2_eq, ↓tickNW_eq,
  ↓monadLift_self, ↓ml_lift, ↓ml_trans, ↓ml_Id, ↓FM.lift_eq, ↓pc_attachLift_op, ↓pc_lift_op, ↓pc_pure_op, ↓pc_map_op, ↓PostconditionT.operation_pure, ↓PostconditionT.run_eq_map, ↓CM.bind_eq, ↓CM.pure_eq, ↓CM.map_eq, ↓CM.attach_eq, ↓QM.bind_eq, ↓QM.pure_eq, ↓QM.map_eq, ↓QM.attach_eq, ↓NW.bind_eq, ↓NW.pure_eq, ↓NW.map_eq, ↓NW.attach_eq, ↓W.bind_eq, ↓W.pure_eq, ↓W.map_eq, ↓W.attach_eq, ↓FM.bind_eq, ↓FM.pure_eq, ↓FM.map_eq, ↓FM.attach_eq, ↓NW2.bind_eq, ↓NW2.pure_eq, ↓NW2.map_eq, ↓NW2.attach_eq, ↓NWa.bind_eq, ↓NWa.pure_eq, ↓NWa.map_eq, ↓NWa.attach_eq, ↓NWb.bind_eq, ↓NWb.pure_eq, ↓NWb.map_eq, ↓NWb.attach_eq, ↓MB.bind_eq, ↓MB.pure_eq, ↓MB.map_eq, Id.run_pure, Id.run_bind, Id.run_map, Id.run, ↓Id_bind_eq, ↓Id_pure_eq, ↓SM.bind_eq, ↓SM.pure_eq, ↓SM.map_sub, ↓SM.map_nsub, ↓SM.attach_nsub, ↓SM.lift_eq, ↓WM.bind_eq, ↓WM.pure_eq, ↓WM.map_eq, ↓WM.attach_eq, ↓CM2.bind_eq, ↓CM2.pure_eq, ↓CM2.map_eq, ↓CM2.attach_eq,
  Shrink.inflate_deflate, ite_true, ite_false, ↓reduceIte] at *)

macro "ev_all" : tactic => `(tactic| repeat (first
  | (rw [toArray_go_eq] at *) | (rw [toListRev_go_eq] at *) | (rw [forIn'_eq] at *)
  | ev_unfold | ev_simp))

end ItMonadMAHand

/-! ## Necessary -/

namespace ItMonadMAHand
open Std Std.Iterators Std.Iterators.Types

end ItMonadMAHand

/-! ## Removable -/

namespace ItMonadMAHand
open Std Std.Iterators Std.Iterators.Types

universe w w' w''

/-- Universe-polymorphic version of filterMap_step_eq (for the removable proofs). -/
theorem filterMap_step_gen {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad n] [Iterator α m β]
    {lift : ⦃α : Type w⦄ → m α → n α} {f : β → PostconditionT n (Option γ)}
    (it : IterM (α := α) m β) :
    (IterM.InternalCombinators.filterMap lift f it).step = (do
      match (← lift it.step).inflate with
      | .yield it' out h => do
        match ← (f out).operation with
        | ⟨none, h'⟩ => pure (.deflate
            (.skip (IterM.InternalCombinators.filterMap lift f it') (by exact .yieldNone h h')))
        | ⟨some out', h'⟩ => pure (.deflate
            (.yield (IterM.InternalCombinators.filterMap lift f it') out' (by exact .yieldSome h h')))
      | .skip it' h => pure (.deflate
          (.skip (IterM.InternalCombinators.filterMap lift f it') (by exact .skip h)))
      | .done h => pure (.deflate (.done (by exact .done h)))) := by
  apply bind_congr; intro s
  obtain ⟨t, rfl⟩ : ∃ t, s = Shrink.deflate t := ⟨s.inflate, Shrink.deflate_inflate.symm⟩
  rcases t with ⟨_ | _ | _, h⟩ <;> (try simp only [Shrink.inflate_deflate]) <;>
    (try erw [Shrink.inflate_deflate]) <;> (try rfl) <;>
    (apply bind_congr; intro r; rcases r with ⟨_ | _, _⟩ <;> rfl)

-- Std.IterM.forIn_filterMap, idx 7 (LawfulMonad m): removable. The filterMap iterator's step only binds and returns pure values in m; the lawful lift m → n (LawfulMonadLiftT) and LawfulMonad n turn it into the base step followed by pure, so the induction of the library proof goes through in n.
theorem forIn_filterMap.h7 : drop% Std.IterM.forIn_filterMap 7 := by
  intro m n α β β₂ γ _ _ _ _ _ _ _ _ _ it f init g
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs
  rw [IterM.forIn_eq_match_step, IterM.forIn_eq_match_step]
  rw [show (it.filterMap f).step = _ from filterMap_step_gen (m := m) (n := m) it]
  simp only [liftM]
  erw [monadLift_bind]; rw [bind_assoc]
  apply bind_congr; intro s
  cases s.inflate using PlausibleIterStep.casesOn
  · rename_i it' out h
    simp only [PostconditionT.operation_pure]
    erw [monadLift_bind]; rw [monadLift_pure, pure_bind]
    split
    · rename_i hfo
      have hn : f out = none := congrArg Subtype.val hfo
      erw [monadLift_pure, pure_bind]
      erw [Shrink.inflate_deflate]
      simp only [hn, pure_bind]
      exact ihy h
    · rename_i out' _ hfo
      have hs : f out = some out' := congrArg Subtype.val hfo
      erw [monadLift_pure, pure_bind]
      erw [Shrink.inflate_deflate]
      simp only [hs]
      apply bind_congr; intro r
      cases r
      · rfl
      · exact ihy h
  · rename_i it' h
    erw [monadLift_pure, pure_bind]
    erw [Shrink.inflate_deflate]
    exact ihs h
  · erw [monadLift_pure, pure_bind]
    erw [Shrink.inflate_deflate]

-- Std.IterM.forIn_filter, idx 6 (LawfulMonad m): removable; filter is filterMap with an if-then-else, so it follows from the proof for forIn_filterMap above.
theorem forIn_filter.h6 : drop% Std.IterM.forIn_filter 6 := by
  intro m n α β γ _ _ _ _ _ _ _ _ _ it f init g
  refine (forIn_filterMap.h7 (it := it) (f := fun b => if f b then some b else none)
    (init := init) (g := g)).trans ?_
  congr 1; funext out acc; cases f out <;> rfl

-- Std.IterM.foldM_filterMap, idx 10 (LawfulMonad m): removable; foldM is forIn with a mapped step function, so it follows from the proof for forIn_filterMap above (map_pure in n).
theorem foldM_filterMap.h10 : drop% Std.IterM.foldM_filterMap 10 := by
  intro α β γ δ m n _ _ _ _ _ _ _ _ _ f g init it
  refine (forIn_filterMap.h7 (it := it) (f := f) (init := init)
    (g := fun c acc => ForInStep.yield <$> g acc c)).trans ?_
  show _ = ForIn.forIn it init _
  congr 1; funext out acc; cases h : f out <;> simp [h]

-- Std.IterM.foldM_filter, idx 9 (LawfulMonad m): removable; as for foldM_filterMap, with filter = filterMap of an if-then-else.
theorem foldM_filter.h9 : drop% Std.IterM.foldM_filter 9 := by
  intro α β δ m n _ _ _ _ _ _ _ _ _ f g init it
  refine (forIn_filterMap.h7 (it := it) (f := fun b => if f b then some b else none) (init := init)
    (g := fun c acc => ForInStep.yield <$> g acc c)).trans ?_
  show _ = ForIn.forIn it init _
  congr 1; funext out acc; cases h : f out <;> simp [h]


/-! ### Transferred refutations (WPSpec) -/

-- `Std.WP.Spec.IterM.forIn_filterMapWithPostcondition` idx 12: necessary; the hand8/hand10 model of Std.IterM.forIn_filterMapWithPostcondition idx 10, transferred with the exact WP ((LawfulMonad n): m = Id, n = FM (Bool writer whose map and attach flip the flag: bind/pure lawful, weakly lawful attach, lawful lifts from Id and to o = W), list iterator [0]: the left side binds f's operation (resp. attach) directly, the right side maps it.)
theorem WPS.IterM.forIn_filterMapWithPostcondition.h12 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapWithPostcondition 12 := by
  intro h
  letI := WPSpecHand.exWPM (W) Nat
  have := WPSpecHand.ex_eq (W) Nat (h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (W) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (W) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterMapWithPostcondition` idx 18: necessary; the hand8/hand10 model of Std.IterM.forIn_filterMapWithPostcondition idx 14, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.forIn_filterMapWithPostcondition.h18 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapWithPostcondition 18 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterMapWithPostcondition` idx 20: necessary; the hand8/hand10 model of Std.IterM.forIn_filterMapWithPostcondition idx 16, transferred with the exact WP ((LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.forIn_filterMapWithPostcondition.h20 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapWithPostcondition 20 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW2) Nat
  have := WPSpecHand.ex_eq (NW2) Nat (h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW2) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW2) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterMapM` idx 12: necessary; the hand8/hand10 model of Std.IterM.forIn_filterMapM idx 10, transferred with the exact WP ((LawfulMonad n): m = Id, n = FM (Bool writer whose map and attach flip the flag: bind/pure lawful, weakly lawful attach, lawful lifts from Id and to o = W), list iterator [0]: the left side binds f's operation (resp. attach) directly, the right side maps it.)
theorem WPS.IterM.forIn_filterMapM.h12 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapM 12 := by
  intro h
  letI := WPSpecHand.exWPM (W) Nat
  have := WPSpecHand.ex_eq (W) Nat (h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (W) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (W) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterMapM` idx 18: necessary; the hand8/hand10 model of Std.IterM.forIn_filterMapM idx 14, transferred with the exact WP ((WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.)
theorem WPS.IterM.forIn_filterMapM.h18 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapM 18 := by
  intro h
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterMapM` idx 20: necessary; the hand8/hand10 model of Std.IterM.forIn_filterMapM idx 16, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.forIn_filterMapM.h20 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapM 20 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterMapM` idx 22: necessary; the hand8/hand10 model of Std.IterM.forIn_filterMapM idx 18, transferred with the exact WP ((LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.forIn_filterMapM.h22 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapM 22 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW2) Nat
  have := WPSpecHand.ex_eq (NW2) Nat (h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW2) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW2) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterMap` idx 9: removable; rewrite with the hand8 proof of Std.IterM.forIn_filterMap without its idx 7 ((LawfulMonad m): removable. The filterMap iterator's step only binds and returns pure values in m; the lawful lift m → n (LawfulMonadLiftT) and LawfulMonad n turn it into the base step followed by pure, so the induction of the library proof goes through in n.)
theorem WPS.IterM.forIn_filterMap.h9 : drop% Std.WP.Spec.IterM.forIn_filterMap 9 := by
  intros; rename_i h
  rw [forIn_filterMap.h7]; exact h

-- `Std.WP.Spec.IterM.forIn_filterMap` idx 15: necessary; the hand8/hand10 model of Std.IterM.forIn_filterMap idx 11, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.)
theorem WPS.IterM.forIn_filterMap.h15 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMap 15 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := some) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_mapWithPostcondition` idx 12: necessary; the hand8/hand10 model of Std.IterM.forIn_mapWithPostcondition idx 10, transferred with the exact WP ((LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).)
theorem WPS.IterM.forIn_mapWithPostcondition.h12 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapWithPostcondition 12 := by
  intro h
  letI := WPSpecHand.exWPM (W) Nat
  have := WPSpecHand.ex_eq (W) Nat (h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (W) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (W) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_mapWithPostcondition` idx 18: necessary; the hand8/hand10 model of Std.IterM.forIn_mapWithPostcondition idx 14, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.forIn_mapWithPostcondition.h18 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapWithPostcondition 18 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_mapWithPostcondition` idx 20: necessary; the hand8/hand10 model of Std.IterM.forIn_mapWithPostcondition idx 16, transferred with the exact WP ((LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.forIn_mapWithPostcondition.h20 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapWithPostcondition 20 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW2) Nat
  have := WPSpecHand.ex_eq (NW2) Nat (h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW2) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW2) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_mapM` idx 12: necessary; the hand8/hand10 model of Std.IterM.forIn_mapM idx 10, transferred with the exact WP ((LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).)
theorem WPS.IterM.forIn_mapM.h12 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapM 12 := by
  intro h
  letI := WPSpecHand.exWPM (W) Nat
  have := WPSpecHand.ex_eq (W) Nat (h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (W) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (W) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_mapM` idx 18: necessary; the hand8/hand10 model of Std.IterM.forIn_mapM idx 14, transferred with the exact WP ((WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.)
theorem WPS.IterM.forIn_mapM.h18 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapM 18 := by
  intro h
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_mapM` idx 20: necessary; the hand8/hand10 model of Std.IterM.forIn_mapM idx 16, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.forIn_mapM.h20 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapM 20 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_mapM` idx 22: necessary; the hand8/hand10 model of Std.IterM.forIn_mapM idx 18, transferred with the exact WP ((LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.forIn_mapM.h22 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapM 22 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW2) Nat
  have := WPSpecHand.ex_eq (NW2) Nat (h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW2) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW2) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_map` idx 9: necessary; the hand8/hand10 model of Std.IterM.forIn_map idx 7, transferred with the exact WP ((LawfulMonad m): m = MB (lawful Nat writer bind/pure, but map adds one), n = NW, lawful lift MB → NW, list iterator [0]: the map combinator maps in m.)
theorem WPS.IterM.forIn_map.h9 : ¬ drop0% Std.WP.Spec.IterM.forIn_map 9 := by
  intro h
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := MB) (n := NW) (it := [0].iterM MB) (f := id) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_map` idx 15: necessary; the hand8/hand10 model of Std.IterM.forIn_map idx 11, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.)
theorem WPS.IterM.forIn_map.h15 : ¬ drop0% Std.WP.Spec.IterM.forIn_map 15 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := id) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterWithPostcondition` idx 11: necessary; the hand8/hand10 model of Std.IterM.forIn_filterWithPostcondition idx 9, transferred with the exact WP ((LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).)
theorem WPS.IterM.forIn_filterWithPostcondition.h11 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterWithPostcondition 11 := by
  intro h
  letI := WPSpecHand.exWPM (W) Nat
  have := WPSpecHand.ex_eq (W) Nat (h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (W) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (W) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterWithPostcondition` idx 17: necessary; the hand8/hand10 model of Std.IterM.forIn_filterWithPostcondition idx 13, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.forIn_filterWithPostcondition.h17 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterWithPostcondition 17 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterWithPostcondition` idx 19: necessary; the hand8/hand10 model of Std.IterM.forIn_filterWithPostcondition idx 15, transferred with the exact WP ((LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.forIn_filterWithPostcondition.h19 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterWithPostcondition 19 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW2) Nat
  have := WPSpecHand.ex_eq (NW2) Nat (h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW2) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW2) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterM` idx 11: necessary; the hand8/hand10 model of Std.IterM.forIn_filterM idx 9, transferred with the exact WP ((LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).)
theorem WPS.IterM.forIn_filterM.h11 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterM 11 := by
  intro h
  letI := WPSpecHand.exWPM (W) Nat
  have := WPSpecHand.ex_eq (W) Nat (h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (W) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (W) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterM` idx 17: necessary; the hand8/hand10 model of Std.IterM.forIn_filterM idx 13, transferred with the exact WP ((WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.)
theorem WPS.IterM.forIn_filterM.h17 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterM 17 := by
  intro h
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterM` idx 19: necessary; the hand8/hand10 model of Std.IterM.forIn_filterM idx 15, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.forIn_filterM.h19 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterM 19 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filterM` idx 21: necessary; the hand8/hand10 model of Std.IterM.forIn_filterM idx 17, transferred with the exact WP ((LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.forIn_filterM.h21 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterM 21 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW2) Nat
  have := WPSpecHand.ex_eq (NW2) Nat (h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW2) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW2) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.forIn_filter` idx 8: removable; rewrite with the hand8 proof of Std.IterM.forIn_filter without its idx 6 ((LawfulMonad m): removable; filter is filterMap with an if-then-else, so it follows from the proof for forIn_filterMap above.)
theorem WPS.IterM.forIn_filter.h8 : drop% Std.WP.Spec.IterM.forIn_filter 8 := by
  intros; rename_i h
  rw [forIn_filter.h6]; exact h

-- `Std.WP.Spec.IterM.forIn_filter` idx 14: necessary; the hand8/hand10 model of Std.IterM.forIn_filter idx 10, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.)
theorem WPS.IterM.forIn_filter.h14 : ¬ drop0% Std.WP.Spec.IterM.forIn_filter 14 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun _ => true) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterMapWithPostcondition` idx 15: necessary; the hand8/hand10 model of Std.IterM.foldM_filterMapWithPostcondition idx 13, transferred with the exact WP ((LawfulMonad n): m = Id, n = FM (Bool writer whose map and attach flip the flag: bind/pure lawful, weakly lawful attach, lawful lifts from Id and to o = W), list iterator [0]: the left side binds f's operation (resp. attach) directly, the right side maps it.)
theorem WPS.IterM.foldM_filterMapWithPostcondition.h15 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapWithPostcondition 15 := by
  intro h
  letI := WPSpecHand.exWPM (W) Nat
  have := WPSpecHand.ex_eq (W) Nat (h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (W) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (W) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterMapWithPostcondition` idx 25: necessary; the hand8/hand10 model of Std.IterM.foldM_filterMapWithPostcondition idx 21, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.foldM_filterMapWithPostcondition.h25 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapWithPostcondition 25 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterMapWithPostcondition` idx 26: necessary; the hand8/hand10 model of Std.IterM.foldM_filterMapWithPostcondition idx 22, transferred with the exact WP ((LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.foldM_filterMapWithPostcondition.h26 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapWithPostcondition 26 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW2) Nat
  have := WPSpecHand.ex_eq (NW2) Nat (h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW2) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW2) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterMapM` idx 15: necessary; the hand8/hand10 model of Std.IterM.foldM_filterMapM idx 13, transferred with the exact WP ((LawfulMonad n): m = Id, n = FM (Bool writer whose map and attach flip the flag: bind/pure lawful, weakly lawful attach, lawful lifts from Id and to o = W), list iterator [0]: the left side binds f's operation (resp. attach) directly, the right side maps it.)
theorem WPS.IterM.foldM_filterMapM.h15 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapM 15 := by
  intro h
  letI := WPSpecHand.exWPM (W) Nat
  have := WPSpecHand.ex_eq (W) Nat (h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (W) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (W) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterMapM` idx 16: necessary; the hand8/hand10 model of Std.IterM.foldM_filterMapM idx 14, transferred with the exact WP ((WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.)
theorem WPS.IterM.foldM_filterMapM.h16 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapM 16 := by
  intro h
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterMapM` idx 27: necessary; the hand8/hand10 model of Std.IterM.foldM_filterMapM idx 23, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.foldM_filterMapM.h27 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapM 27 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterMapM` idx 28: necessary; the hand8/hand10 model of Std.IterM.foldM_filterMapM idx 24, transferred with the exact WP ((LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.foldM_filterMapM.h28 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapM 28 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW2) Nat
  have := WPSpecHand.ex_eq (NW2) Nat (h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW2) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW2) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_mapWithPostcondition` idx 15: necessary; the hand8/hand10 model of Std.IterM.foldM_mapWithPostcondition idx 13, transferred with the exact WP ((LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).)
theorem WPS.IterM.foldM_mapWithPostcondition.h15 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapWithPostcondition 15 := by
  intro h
  letI := WPSpecHand.exWPM (W) Nat
  have := WPSpecHand.ex_eq (W) Nat (h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun d c => pure (d + c)) (Pred := (W) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (W) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_mapWithPostcondition` idx 25: necessary; the hand8/hand10 model of Std.IterM.foldM_mapWithPostcondition idx 21, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.foldM_mapWithPostcondition.h25 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapWithPostcondition 25 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_mapWithPostcondition` idx 26: necessary; the hand8/hand10 model of Std.IterM.foldM_mapWithPostcondition idx 22, transferred with the exact WP ((LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.foldM_mapWithPostcondition.h26 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapWithPostcondition 26 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW2) Nat
  have := WPSpecHand.ex_eq (NW2) Nat (h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW2) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW2) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_mapM` idx 15: necessary; the hand8/hand10 model of Std.IterM.foldM_mapM idx 13, transferred with the exact WP ((LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).)
theorem WPS.IterM.foldM_mapM.h15 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapM 15 := by
  intro h
  letI := WPSpecHand.exWPM (W) Nat
  have := WPSpecHand.ex_eq (W) Nat (h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun d c => pure (d + c)) (Pred := (W) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (W) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_mapM` idx 16: necessary; the hand8/hand10 model of Std.IterM.foldM_mapM idx 14, transferred with the exact WP ((WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.)
theorem WPS.IterM.foldM_mapM.h16 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapM 16 := by
  intro h
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_mapM` idx 27: necessary; the hand8/hand10 model of Std.IterM.foldM_mapM idx 23, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.foldM_mapM.h27 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapM 27 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => pure b) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_mapM` idx 28: necessary; the hand8/hand10 model of Std.IterM.foldM_mapM idx 24, transferred with the exact WP ((LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.foldM_mapM.h28 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapM 28 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW2) Nat
  have := WPSpecHand.ex_eq (NW2) Nat (h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW2) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW2) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterWithPostcondition` idx 14: necessary; the hand8/hand10 model of Std.IterM.foldM_filterWithPostcondition idx 12, transferred with the exact WP ((LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).)
theorem WPS.IterM.foldM_filterWithPostcondition.h14 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterWithPostcondition 14 := by
  intro h
  letI := WPSpecHand.exWPM (W) Nat
  have := WPSpecHand.ex_eq (W) Nat (h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (W) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (W) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterWithPostcondition` idx 24: necessary; the hand8/hand10 model of Std.IterM.foldM_filterWithPostcondition idx 20, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.foldM_filterWithPostcondition.h24 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterWithPostcondition 24 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterWithPostcondition` idx 25: necessary; the hand8/hand10 model of Std.IterM.foldM_filterWithPostcondition idx 21, transferred with the exact WP ((LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.foldM_filterWithPostcondition.h25 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterWithPostcondition 25 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW2) Nat
  have := WPSpecHand.ex_eq (NW2) Nat (h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW2) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW2) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterM` idx 14: necessary; the hand8/hand10 model of Std.IterM.foldM_filterM idx 12, transferred with the exact WP ((LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).)
theorem WPS.IterM.foldM_filterM.h14 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterM 14 := by
  intro h
  letI := WPSpecHand.exWPM (W) Nat
  have := WPSpecHand.ex_eq (W) Nat (h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (W) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (W) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterM` idx 15: necessary; the hand8/hand10 model of Std.IterM.foldM_filterM idx 13, transferred with the exact WP ((WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.)
theorem WPS.IterM.foldM_filterM.h15 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterM 15 := by
  intro h
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterM` idx 26: necessary; the hand8/hand10 model of Std.IterM.foldM_filterM idx 22, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.foldM_filterM.h26 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterM 26 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterM` idx 27: necessary; the hand8/hand10 model of Std.IterM.foldM_filterM idx 23, transferred with the exact WP ((LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).)
theorem WPS.IterM.foldM_filterM.h27 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterM 27 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW2) Nat
  have := WPSpecHand.ex_eq (NW2) Nat (h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW2) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW2) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filterMap` idx 12: removable; rewrite with the hand8 proof of Std.IterM.foldM_filterMap without its idx 10 ((LawfulMonad m): removable; foldM is forIn with a mapped step function, so it follows from the proof for forIn_filterMap above (map_pure in n).)
theorem WPS.IterM.foldM_filterMap.h12 : drop% Std.WP.Spec.IterM.foldM_filterMap 12 := by
  intros; rename_i h
  rw [foldM_filterMap.h10]; exact h

-- `Std.WP.Spec.IterM.foldM_filterMap` idx 19: necessary; the hand8/hand10 model of Std.IterM.foldM_filterMap idx 15, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.)
theorem WPS.IterM.foldM_filterMap.h19 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMap 19 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := some) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_map` idx 12: necessary; the hand8/hand10 model of Std.IterM.foldM_map idx 10, transferred with the exact WP ((LawfulMonad m): m = MB (lawful Nat writer bind/pure, but map adds one), n = NW, lawful lift MB → NW, list iterator [0]: the map combinator maps in m.)
theorem WPS.IterM.foldM_map.h12 : ¬ drop0% Std.WP.Spec.IterM.foldM_map 12 := by
  intro h
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := MB) (n := NW) (it := [0].iterM MB) (f := id) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_map` idx 19: necessary; the hand8/hand10 model of Std.IterM.foldM_map idx 15, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.)
theorem WPS.IterM.foldM_map.h19 : ¬ drop0% Std.WP.Spec.IterM.foldM_map 19 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := id) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.foldM_filter` idx 11: removable; rewrite with the hand8 proof of Std.IterM.foldM_filter without its idx 9 ((LawfulMonad m): removable; as for foldM_filterMap, with filter = filterMap of an if-then-else.)
theorem WPS.IterM.foldM_filter.h11 : drop% Std.WP.Spec.IterM.foldM_filter 11 := by
  intros; rename_i h
  rw [foldM_filter.h9]; exact h

-- `Std.WP.Spec.IterM.foldM_filter` idx 18: necessary; the hand8/hand10 model of Std.IterM.foldM_filter idx 14, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.)
theorem WPS.IterM.foldM_filter.h18 : ¬ drop0% Std.WP.Spec.IterM.foldM_filter 18 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun _ => true) (init := 0) (g := fun d c => pure (d + c)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.fold_filterMapWithPostcondition` idx 19: necessary; the hand8/hand10 model of Std.IterM.fold_filterMapWithPostcondition idx 15, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.)
theorem WPS.IterM.fold_filterMapWithPostcondition.h19 : ¬ drop0% Std.WP.Spec.IterM.fold_filterMapWithPostcondition 19 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure (some b)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.fold_filterMapM` idx 14: necessary; the hand8/hand10 model of Std.IterM.fold_filterMapM idx 13, transferred with the exact WP ((WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), list iterator [0].)
theorem WPS.IterM.fold_filterMapM.h14 : ¬ drop0% Std.WP.Spec.IterM.fold_filterMapM 14 := by
  intro h
  letI := WPSpecHand.exWPM (NWb) Nat
  have := WPSpecHand.ex_eq (NWb) Nat (h (init := 0) (g := fun d c => d + c) (m := Id) (n := NWb) (it := [0].iterM Id) (f := fun b => pure (some b)) (Pred := (NWb) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NWb) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.fold_filterMapM` idx 21: necessary; the hand8/hand10 model of Std.IterM.fold_filterMapM idx 17, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.)
theorem WPS.IterM.fold_filterMapM.h21 : ¬ drop0% Std.WP.Spec.IterM.fold_filterMapM 21 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun b => pure (some b)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.fold_mapWithPostcondition` idx 19: necessary; the hand8/hand10 model of Std.IterM.fold_mapWithPostcondition idx 15, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.)
theorem WPS.IterM.fold_mapWithPostcondition.h19 : ¬ drop0% Std.WP.Spec.IterM.fold_mapWithPostcondition 19 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure b) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.fold_mapM` idx 14: necessary; the hand8/hand10 model of Std.IterM.fold_mapM idx 13, transferred with the exact WP ((WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), list iterator [0].)
theorem WPS.IterM.fold_mapM.h14 : ¬ drop0% Std.WP.Spec.IterM.fold_mapM 14 := by
  intro h
  letI := WPSpecHand.exWPM (NWb) Nat
  have := WPSpecHand.ex_eq (NWb) Nat (h (init := 0) (g := fun d c => d + c) (m := Id) (n := NWb) (it := [0].iterM Id) (f := fun b => pure b) (Pred := (NWb) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NWb) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.fold_mapM` idx 21: necessary; the hand8/hand10 model of Std.IterM.fold_mapM idx 17, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.)
theorem WPS.IterM.fold_mapM.h21 : ¬ drop0% Std.WP.Spec.IterM.fold_mapM 21 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun b => pure b) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.fold_filterWithPostcondition` idx 18: necessary; the hand8/hand10 model of Std.IterM.fold_filterWithPostcondition idx 14, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.)
theorem WPS.IterM.fold_filterWithPostcondition.h18 : ¬ drop0% Std.WP.Spec.IterM.fold_filterWithPostcondition 18 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun _ => PostconditionT.pure (.up true)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.WP.Spec.IterM.fold_filterM` idx 13: necessary; the hand8/hand10 model of Std.IterM.fold_filterM idx 12, transferred with the exact WP ((WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), list iterator [0].)
theorem WPS.IterM.fold_filterM.h13 : ¬ drop0% Std.WP.Spec.IterM.fold_filterM 13 := by
  intro h
  letI := WPSpecHand.exWPM (NWb) Nat
  have := WPSpecHand.ex_eq (NWb) Nat (h (init := 0) (g := fun d c => d + c) (m := Id) (n := NWb) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (Pred := (NWb) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NWb) Nat _))
  clear h; revert this
  ev_all; simp

-- `Std.WP.Spec.IterM.fold_filterM` idx 20: necessary; the hand8/hand10 model of Std.IterM.fold_filterM idx 16, transferred with the exact WP ((LawfulMonadLiftT m n): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.)
theorem WPS.IterM.fold_filterM.h20 : ¬ drop0% Std.WP.Spec.IterM.fold_filterM 20 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  letI := WPSpecHand.exWPM (NW) Nat
  have := WPSpecHand.ex_eq (NW) Nat (h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun _ => pure (.up true)) (Pred := (NW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (NW) Nat _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

end ItMonadMAHand

end MA


/-! ## Models and refutations after ItMonadIterHand.lean -/

section MI

open Lean Meta Elab Term in
/-- The private `Std.IterM.flattenAfter` of `Init.Data.Iterators.Combinators.Monadic.FlatMap` (the
step lemma `IterM.step_flattenAfter` is private too, so it is restated without `LawfulMonad`). -/
elab "flattenAfterP%" : term => do
  let n := mkPrivateNameCore `Init.Data.Iterators.Combinators.Monadic.FlatMap `Std.IterM.flattenAfter
  let c ← getConstInfo n
  return mkConst n (← c.levelParams.mapM fun _ => mkFreshLevelMVar)

namespace ItMonadIterHand
open Std Std.Iterators

/-! Countdown iterator `CD` (copied from `ItDepOtherHand`): state `n+1` yields `n`; `0` is done. -/
structure CD where n : Nat

def CD.stepv {m : Type → Type} (n : Nat) : IterStep (IterM (α := CD) m Nat) Nat :=
  match n with
  | 0 => .done
  | k + 1 => .yield ⟨⟨k⟩⟩ k

instance CD.inst {m : Type → Type} [Pure m] : Iterator CD m Nat where
  IsPlausibleStep it s := s = CD.stepv it.internalState.n
  step it := pure (.deflate ⟨CD.stepv it.internalState.n, rfl⟩)

def CD.finRel {m : Type → Type} [Pure m] : FinitenessRelation CD m where
  Rel := InvImage (· < ·) (fun it => it.internalState.n)
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation := by
    rintro ⟨⟨n⟩⟩ ⟨⟨k⟩⟩ ⟨s, hs, hp⟩
    cases n <;> simp_all [CD.stepv, InvImage]

instance CD.finite {m : Type → Type} [Pure m] : Finite CD m := .of_finitenessRelation CD.finRel

instance CD.det {m : Type → Type} [Pure m] : LawfulDeterministicIterator CD m :=
  ⟨fun _ => ⟨_, rfl⟩⟩

instance CD.loop {m : Type → Type} {n : Type → Type} [Pure m] [Monad n] : IteratorLoop CD m n :=
  .defaultImplementation
instance CD.lawfulLoop {m n : Type → Type} [Monad m] [Monad n] : LawfulIteratorLoop CD m n :=
  ⟨fun _ _ _ _ _ _ _ _ => rfl⟩

abbrev ci (n : Nat) : Iter (α := CD) Nat := ⟨⟨n⟩⟩

theorem CD.step0 : (ci 0).step.val = .done := by
  simp only [Iter.step, IterM.step, Iterator.step, IterM.Step.toPure, Id.run, pure]
  erw [Shrink.inflate_deflate]; rfl
theorem CD.stepS (k : Nat) : (ci (k + 1)).step.val = .yield (ci k) k := by
  simp only [Iter.step, IterM.step, Iterator.step, IterM.Step.toPure, Id.run, pure]
  erw [Shrink.inflate_deflate]; rfl
theorem CD.step0' : (ci 0).step = ⟨.done, rfl⟩ := Subtype.ext CD.step0
theorem CD.stepS' (k : Nat) : (ci (k + 1)).step = ⟨.yield (ci k) k, rfl⟩ := Subtype.ext (CD.stepS k)

theorem CD.toList0 : (ci 0).toList = [] := by
  rw [Iter.toList_eq_match_step, CD.step0]
theorem CD.toListS (k : Nat) : (ci (k + 1)).toList = k :: (ci k).toList := by
  rw [Iter.toList_eq_match_step, CD.stepS]

/-! ## Monads -/

/-- `Z`: `Option` whose `bind` always fails (`none`); `pure` and `map` are `Option`'s. Not lawful
(`pure a >>= f = none`); its trivial `MonadAttach` is weakly lawful. -/
def Z (α : Type) : Type := Option α
instance Z.monad : Monad Z where
  pure a := (some a : Option _)
  map f x := Option.map f (x : Option _)
  bind _ _ := (none : Option _)
instance Z.attach : MonadAttach Z := .trivial
instance Z.weakly : WeaklyLawfulMonadAttach Z := ⟨fun {_ x} => by
  change Option.map _ (Option.map _ (x : Option _)) = x; cases (x : Option _) <;> rfl⟩
theorem Z.not_lawful : ¬ LawfulMonad Z := fun h => by
  have := @pure_bind Z _ h _ _ 0 (fun a => (some a : Option Nat))
  cases this

/-- `W bc mc ac lc ak`: a writer monad over `Int` (`bind` adds up the counters `c`), with three defects:
`bind` adds `bc`, `map` adds `mc`, `attach` adds `ac` to the counter; `pure a` has counter `0`.
Lawful iff `bc = 0` and `mc = 0`; the `MonadAttach` is weakly lawful iff `mc + ac = 0`. -/
structure W (bc mc ac lc ak : Int) (α : Type) where
  c : Int
  v : α

instance W.monad {bc mc ac lc ak : Int} : Monad (W bc mc ac lc ak) where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c + bc, (f x.v).v⟩
  map f x := ⟨x.c + mc, f x.v⟩

instance W.attach {bc mc ac lc ak : Int} : MonadAttach (W bc mc ac lc ak) where
  CanReturn _ _ := True
  attach x := ⟨x.c + ac + ak * x.c, ⟨x.v, .intro⟩⟩

section
variable {bc mc ac lc ak : Int} {α β : Type}
@[simp] theorem W.bind_c (x : W bc mc ac lc ak α) (f : α → W bc mc ac lc ak β) : (x >>= f).c = x.c + (f x.v).c + bc := rfl
@[simp] theorem W.bind_v (x : W bc mc ac lc ak α) (f : α → W bc mc ac lc ak β) : (x >>= f).v = (f x.v).v := rfl
@[simp] theorem W.pure_c (a : α) : (pure a : W bc mc ac lc ak α).c = 0 := rfl
@[simp] theorem W.pure_v (a : α) : (pure a : W bc mc ac lc ak α).v = a := rfl
@[simp] theorem W.map_c (f : α → β) (x : W bc mc ac lc ak α) : (f <$> x).c = x.c + mc := rfl
@[simp] theorem W.map_v (f : α → β) (x : W bc mc ac lc ak α) : (f <$> x).v = f x.v := rfl
@[simp] theorem W.attach_c (x : W bc mc ac lc ak α) : (MonadAttach.attach x).c = x.c + ac + ak * x.c := rfl
@[simp] theorem W.attach_v (x : W bc mc ac lc ak α) : (MonadAttach.attach x).v = ⟨x.v, .intro⟩ := rfl
end

theorem W.ext' {bc mc ac lc ak : Int} {α : Type} {x y : W bc mc ac lc ak α} (h1 : x.c = y.c) (h2 : x.v = y.v) : x = y := by
  cases x; cases y; cases h1; cases h2; rfl

instance W.lawful {ac lc ak : Int} : LawfulMonad (W 0 0 ac lc ak) := LawfulMonad.mk'
  (id_map := fun x => W.ext' (by simp) rfl)
  (pure_bind := fun x f => W.ext' (by simp) rfl)
  (bind_assoc := fun x f g => W.ext' (by simp; omega) rfl)
  (bind_pure_comp := fun f x => W.ext' (by simp) rfl)

theorem W.weakly_of {bc mc ac lc : Int} (h : mc + ac = 0) : WeaklyLawfulMonadAttach (W bc mc ac lc 0) :=
  ⟨fun {_ x} => W.ext' (by simp; omega) rfl⟩

theorem W.not_lawful_b {bc mc ac lc ak : Int} (h : bc ≠ 0) : ¬ LawfulMonad (W bc mc ac lc ak) := fun hl => by
  have := congrArg W.c (@pure_bind (W bc mc ac lc ak) _ hl _ _ 0 (fun a => pure a))
  simp only [W.bind_c, W.pure_c] at this; omega

theorem W.not_lawful_m {bc mc ac lc ak : Int} (h : mc ≠ 0) : ¬ LawfulMonad (W bc mc ac lc ak) := fun hl => by
  have := congrArg W.c (@id_map (W bc mc ac lc ak) _ hl.toLawfulFunctor _ (pure 0))
  simp only [W.map_c, W.pure_c] at this; omega

theorem W.not_weakly {bc mc ac lc : Int} (h : mc + ac ≠ 0) : ¬ WeaklyLawfulMonadAttach (W bc mc ac lc 0) :=
  fun ⟨hw⟩ => by
  have := congrArg W.c (@hw Nat (pure 0))
  exact h (by simp at this; omega)

/-- Ticking countdown `TK` over `W`: like `CD`, but every step counts 1. -/
structure TK where n : Nat

def TK.stepv {m : Type → Type} (n : Nat) : IterStep (IterM (α := TK) m Nat) Nat :=
  match n with
  | 0 => .done
  | k + 1 => .yield ⟨⟨k⟩⟩ k

instance TK.inst {bc mc ac lc ak : Int} : Iterator TK (W bc mc ac lc ak) Nat where
  IsPlausibleStep it s := s = TK.stepv it.internalState.n
  step it := ⟨1, .deflate ⟨TK.stepv it.internalState.n, rfl⟩⟩

instance TK.finite {bc mc ac lc ak : Int} : Finite TK (W bc mc ac lc ak) := .of_finitenessRelation {
  Rel := InvImage (· < ·) (fun it => it.internalState.n)
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation := by
    rintro ⟨⟨n⟩⟩ ⟨⟨k⟩⟩ ⟨s, hs, hp⟩
    cases n <;> simp_all [TK.stepv, InvImage, IterStep.successor] }

theorem TK.istep {bc mc ac lc ak : Int} (k : Nat) :
    IterM.step (⟨⟨k⟩⟩ : IterM (α := TK) (W bc mc ac lc ak) Nat) = ⟨1, .deflate ⟨TK.stepv k, rfl⟩⟩ := rfl

/-- `U`: a writer monad with two counters `c` and `d`, both added up by `bind`, which also adds `1`
`x.c * (f x.v).d ^ 2` to `d`. `pure_bind` and
`bind_pure` hold, `bind_assoc` fails. The lift `W 0 0 0 0 0 → U` (`d = 0`) is lawful. -/
structure U (α : Type) where
  c : Int
  d : Int
  v : α

instance U.monad : Monad U where
  pure a := ⟨0, 0, a⟩
  bind x f := ⟨x.c + (f x.v).c, x.d + (f x.v).d + x.c * (f x.v).d * (f x.v).d, (f x.v).v⟩
  map f x := ⟨x.c, x.d, f x.v⟩

section
variable {α β : Type}
@[simp] theorem U.bind_c (x : U α) (f : α → U β) : (x >>= f).c = x.c + (f x.v).c := rfl
@[simp] theorem U.bind_d (x : U α) (f : α → U β) :
    (x >>= f).d = x.d + (f x.v).d + x.c * (f x.v).d * (f x.v).d := rfl
@[simp] theorem U.bind_v (x : U α) (f : α → U β) : (x >>= f).v = (f x.v).v := rfl
@[simp] theorem U.pure_c (a : α) : (pure a : U α).c = 0 := rfl
@[simp] theorem U.pure_d (a : α) : (pure a : U α).d = 0 := rfl
@[simp] theorem U.pure_v (a : α) : (pure a : U α).v = a := rfl
@[simp] theorem U.map_c (f : α → β) (x : U α) : (f <$> x).c = x.c := rfl
@[simp] theorem U.map_d (f : α → β) (x : U α) : (f <$> x).d = x.d := rfl
@[simp] theorem U.map_v (f : α → β) (x : U α) : (f <$> x).v = f x.v := rfl
end

theorem U.ext' {α : Type} {x y : U α} (h1 : x.c = y.c) (h2 : x.d = y.d) (h3 : x.v = y.v) : x = y := by
  cases x; cases y; cases h1; cases h2; cases h3; rfl

theorem U.not_lawful : ¬ LawfulMonad U := fun hl => by
  have := congrArg U.d (bind_assoc (⟨1, 0, ()⟩ : U Unit) (fun _ => (⟨1, 0, ()⟩ : U Unit))
    (fun _ => (⟨0, 1, ()⟩ : U Unit)))
  simp only [U.bind_d, U.bind_c] at this
  revert this; decide

instance U.liftW : MonadLiftT (W 0 0 0 0 0) U := ⟨fun x => ⟨x.c, 0, x.v⟩⟩
instance U.lawfulLiftW : LawfulMonadLiftT (W 0 0 0 0 0) U :=
  ⟨fun _ => rfl, fun x f => U.ext' (by simp [monadLift, MonadLiftT.monadLift])
    (by simp [monadLift, MonadLiftT.monadLift]) rfl⟩
@[simp] theorem U.lift_c {α : Type} (x : W 0 0 0 0 0 α) : (monadLift x : U α).c = x.c := rfl
@[simp] theorem U.lift_d {α : Type} (x : W 0 0 0 0 0 α) : (monadLift x : U α).d = 0 := rfl
@[simp] theorem U.lift_v {α : Type} (x : W 0 0 0 0 0 α) : (monadLift x : U α).v = x.v := rfl
@[simp] theorem U.liftM_c {α : Type} (x : W 0 0 0 0 0 α) : (liftM x : U α).c = x.c := rfl
@[simp] theorem U.liftM_d {α : Type} (x : W 0 0 0 0 0 α) : (liftM x : U α).d = 0 := rfl
@[simp] theorem U.liftM_v {α : Type} (x : W 0 0 0 0 0 α) : (liftM x : U α).v = x.v := rfl

/-- `SB` (after `SM` of the ItMonadMA pass): a `Bool` writer whose `bind`/`pure` are lawful, whose
`map` flips the flag iff the target type is a subsingleton and whose `attach` flips it iff the value
type is (`CanReturn x a := a = x.v`). `attach` is weakly lawful; `map` is not parametric, so
`SB` is not lawful. -/
structure SB (α : Type) where
  c : Bool
  v : α

open Classical in
noncomputable instance SB.monad : Monad SB where
  pure a := ⟨false, a⟩
  bind x f := ⟨x.c || (f x.v).c, (f x.v).v⟩
  map {_ β} f x := ⟨xor x.c (decide (Subsingleton β)), f x.v⟩

open Classical in
noncomputable instance SB.attach : MonadAttach SB where
  CanReturn x a := a = x.v
  attach {α} x := ⟨xor x.c (decide (Subsingleton α)), ⟨x.v, rfl⟩⟩

instance SB.weakly : WeaklyLawfulMonadAttach SB := ⟨by
  intro α x; cases x; simp [Functor.map, MonadAttach.attach]⟩

/-- A type with two distinct elements. -/
class NonSub (α : Type) : Prop where
  ns : ¬ Subsingleton α
instance : NonSub Nat := ⟨fun h => absurd (h.allEq 0 1) (by decide)⟩
instance : NonSub (ULift Bool) := ⟨fun h => absurd (h.allEq ⟨false⟩ ⟨true⟩) (by simp)⟩

instance {α : Type} (x : SB α) : Subsingleton (Subtype (MonadAttach.CanReturn x)) :=
  ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
instance {m : Type → Type} [Pure m] {α : Type} (a : α) :
    Subsingleton (Subtype (PostconditionT.pure a : PostconditionT m α).Property) :=
  ⟨fun x y => Subtype.ext (x.2.symm.trans y.2)⟩
instance {m : Type → Type} [Monad m] {α : Type} (a : α) :
    Subsingleton (Subtype (pure a : PostconditionT m α).Property) :=
  ⟨fun x y => Subtype.ext (x.2.symm.trans y.2)⟩
instance {m : Type → Type} [MonadAttach m] {α : Type} (x : m α)
    [Subsingleton (Subtype (MonadAttach.CanReturn x))] :
    Subsingleton (Subtype (PostconditionT.attachLift x).Property) :=
  inferInstanceAs (Subsingleton (Subtype (MonadAttach.CanReturn x)))
instance {m : Type → Type} [Functor m] {α β : Type} (g : α → β) (x : PostconditionT m α)
    [Subsingleton (Subtype x.Property)] :
    Subsingleton (Subtype (PostconditionT.map g x).Property) :=
  ⟨fun a b => by
    obtain ⟨_, a', rfl⟩ := a; obtain ⟨_, b', rfl⟩ := b
    rw [Subsingleton.elim a' b']⟩

theorem SB.not_lawful : ¬ LawfulMonad SB := fun hl => by
  have := congrArg SB.c (id_map (f := SB) (⟨false, ()⟩ : SB Unit))
  simp [Functor.map] at this
  exact this inferInstance

section
variable {α β : Type}
theorem SB.bind_c (x : SB α) (f : α → SB β) : (x >>= f).c = (x.c || (f x.v).c) := rfl
theorem SB.bind_v (x : SB α) (f : α → SB β) : (x >>= f).v = (f x.v).v := rfl
theorem SB.pure_c (a : α) : (pure a : SB α).c = false := rfl
theorem SB.pure_v (a : α) : (pure a : SB α).v = a := rfl
theorem SB.map_v (f : α → β) (x : SB α) : (f <$> x).v = f x.v := rfl
theorem SB.map_c_nsub [h : NonSub β] (f : α → β) (x : SB α) : (f <$> x).c = x.c := by
  simp [Functor.map, h.ns]
theorem SB.attach_c_nsub [h : NonSub α] (x : SB α) : (MonadAttach.attach x).c = x.c := by
  simp [MonadAttach.attach, h.ns]
theorem SB.attach_v (x : SB α) : (MonadAttach.attach x).v = ⟨x.v, rfl⟩ := rfl
theorem SB.pcmap_c_sub (f : α → β) (x : PostconditionT SB α) [h : Subsingleton (Subtype x.Property)] :
    (PostconditionT.map f x).operation.c = !x.operation.c := by
  have : Subsingleton {b // ∃ a : Subtype x.Property, f a.val = b} :=
    (inferInstance : Subsingleton (Subtype (PostconditionT.map f x).Property))
  simp only [PostconditionT.map, Functor.map]
  rw [@decide_eq_true _ (Classical.propDecidable _) this]; simp
theorem SB.pcmap_v (f : α → β) (x : PostconditionT SB α) :
    (PostconditionT.map f x).operation.v = ⟨f x.operation.v.val, _, rfl⟩ := rfl
theorem SB.attachLift_c_nsub [NonSub α] (x : SB α) :
    (PostconditionT.attachLift x).operation.c = x.c := SB.attach_c_nsub x
theorem SB.attachLift_v (x : SB α) : (PostconditionT.attachLift x).operation.v = ⟨x.v, rfl⟩ := rfl
theorem SB.pcpure_c (a : α) : (pure a : PostconditionT SB α).operation.c = false := rfl
theorem SB.pcpure_v (a : α) : (pure a : PostconditionT SB α).operation.v = ⟨a, rfl⟩ := rfl
theorem SB.run_c_nsub [NonSub α] (x : PostconditionT SB α) : x.run.c = x.operation.c :=
  SB.map_c_nsub _ _
theorem SB.run_v (x : PostconditionT SB α) : x.run.v = x.operation.v.val := rfl
end

/-- `BW`: the lawful `Bool` writer; the lift `SB → BW` is the identity (lawful). -/
structure BW (α : Type) where
  c : Bool
  v : α

instance BW.monad : Monad BW where
  pure a := ⟨false, a⟩
  bind x f := ⟨x.c || (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩

theorem BW.ext' {α : Type} {x y : BW α} (h1 : x.c = y.c) (h2 : x.v = y.v) : x = y := by
  cases x; cases y; cases h1; cases h2; rfl

instance BW.liftSB : MonadLiftT SB BW := ⟨fun x => ⟨x.c, x.v⟩⟩
instance BW.lawfulLiftSB : LawfulMonadLiftT SB BW := ⟨fun _ => rfl, fun _ _ => rfl⟩

section
variable {α β : Type}
theorem BW.bind_c (x : BW α) (f : α → BW β) : (x >>= f).c = (x.c || (f x.v).c) := rfl
theorem BW.bind_v (x : BW α) (f : α → BW β) : (x >>= f).v = (f x.v).v := rfl
theorem BW.pure_c (a : α) : (pure a : BW α).c = false := rfl
theorem BW.pure_v (a : α) : (pure a : BW α).v = a := rfl
theorem BW.map_c (f : α → β) (x : BW α) : (f <$> x).c = x.c := rfl
theorem BW.map_v (f : α → β) (x : BW α) : (f <$> x).v = f x.v := rfl
theorem BW.lift_c (x : SB α) : (monadLift x : BW α).c = x.c := rfl
theorem BW.lift_v (x : SB α) : (monadLift x : BW α).v = x.v := rfl
theorem BW.liftM_c (x : SB α) : (liftM x : BW α).c = x.c := rfl
theorem BW.liftM_v (x : SB α) : (liftM x : BW α).v = x.v := rfl
end

instance BW.lawful : LawfulMonad BW := LawfulMonad.mk'
  (id_map := fun x => BW.ext' rfl rfl)
  (pure_bind := fun x f => BW.ext' (by simp only [BW.bind_c, BW.pure_c, BW.pure_v]; simp) rfl)
  (bind_assoc := fun x f g => BW.ext' (by simp only [BW.bind_c, BW.bind_v]; simp [Bool.or_assoc]) rfl)
  (bind_pure_comp := fun f x => BW.ext' (by simp only [BW.bind_c, BW.pure_c, BW.map_c]; simp) rfl)

/-! ## Unfolding the consumers without monad laws -/

theorem go_eq' {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} {acc : Array β} :
    IterM.toArray.go it acc = (do
      match (← it.step).inflate with
      | .yield it' out h => IterM.toArray.go it' (acc.push out)
      | .skip it' h => IterM.toArray.go it' acc
      | .done _ => return acc) := by
  rw [IterM.toArray.go, WellFounded.extrinsicFix₂_eq_apply]
  · rfl
  · exact InvImage.wf _ WellFoundedRelation.wf

theorem dforIn'_eq {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    {n : Type x → Type x'} [Monad n]
    {lift : ∀ γ δ, (γ → n δ) → m γ → n δ} {γ : Type x}
    {it : IterM (α := α) m β} {init : γ} {P hP}
    (Pl : β → γ → ForInStep γ → Prop)
    {f : (b : β) → P b → (c : γ) → n (Subtype (Pl b c))}
    (wf : IteratorLoop.WellFounded α m Pl) :
    IterM.DefaultConsumers.forIn' lift γ Pl it init P hP f =
      (lift _ _ · it.step) (fun s => do
          match s.inflate with
          | .yield it' out h =>
            match ← f out (hP _ <| .direct ⟨_, h⟩) init with
            | ⟨.yield c, _⟩ =>
              IterM.DefaultConsumers.forIn' lift _ Pl it' c P
                (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
            | ⟨.done c, _⟩ => return c
          | .skip it' h =>
            IterM.DefaultConsumers.forIn' lift _ Pl it' init P
              (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
          | .done _ => return init) := by
  haveI : Nonempty γ := ⟨init⟩
  rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply]
  · congr; ext step
    cases step.inflate using PlausibleIterStep.casesOn
    · simp only
      apply bind_congr; intro step
      split <;> rfl
    · rfl
    · rfl
  · exact InvImage.wf _ wf

theorem step_fmwp {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] {it : IterM (α := α) m β} {f : β → PostconditionT n (Option γ)}
    [Monad n] [MonadLiftT m n] :
  (it.filterMapWithPostcondition f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨none, h'⟩ =>
        pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (.yieldNone (out := out) h h')
      | ⟨some out', h'⟩ =>
        pure <| .deflate <| .yield (it'.filterMapWithPostcondition f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (by exact .done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [PlausibleIterStep.skip, PlausibleIterStep.yield]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem step_mwp {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] {it : IterM (α := α) m β} {f : β → PostconditionT n γ}
    [Monad n] [MonadLiftT m n] :
  (it.mapWithPostcondition f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← (PostconditionT.map some (f out)).operation with
      | ⟨none, h'⟩ =>
        pure <| .deflate <| .skip (it'.mapWithPostcondition f) (.yieldNone (out := out) h h')
      | ⟨some out', h'⟩ =>
        pure <| .deflate <| .yield (it'.mapWithPostcondition f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.mapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (by exact .done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [PlausibleIterStep.skip, PlausibleIterStep.yield]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

@[simp] theorem id_pure {α : Type u} (a : α) : (pure a : Id α) = a := rfl

theorem liftM_id {m : Type u → Type v} [Pure m] {α : Type u} (x : Id α) : (liftM x : m α) = pure x.run := rfl
theorem monadLift_id {m : Type u → Type v} [Pure m] {α : Type u} (x : Id α) :
    (monadLift x : m α) = pure x.run := rfl

theorem CD.istep {m : Type → Type} [Pure m] (k : Nat) :
    IterM.step (⟨⟨k⟩⟩ : IterM (α := CD) m Nat) = pure (.deflate ⟨CD.stepv k, rfl⟩) := rfl
theorem CD.toIterM_ci (k : Nat) : (ci k).toIterM = (⟨⟨k⟩⟩ : IterM (α := CD) Id Nat) := rfl

section
variable {bc mc ac lc ak : Int} {α β : Type}
@[simp] theorem W.pcmap_c (f : α → β) (x : PostconditionT (W bc mc ac lc ak) α) :
    (PostconditionT.map f x).operation.c = x.operation.c + mc := rfl
@[simp] theorem W.pcmap_v (f : α → β) (x : PostconditionT (W bc mc ac lc ak) α) :
    (PostconditionT.map f x).operation.v = ⟨f x.operation.v.val, _, rfl⟩ := rfl
@[simp] theorem W.attachLift_c (x : W bc mc ac lc ak α) :
    (PostconditionT.attachLift x).operation.c = x.c + ac + ak * x.c := rfl
@[simp] theorem W.attachLift_v (x : W bc mc ac lc ak α) :
    (PostconditionT.attachLift x).operation.v = ⟨x.v, .intro⟩ := rfl
@[simp] theorem W.pcpure_c (a : α) : (pure a : PostconditionT (W bc mc ac lc ak) α).operation.c = 0 := rfl
@[simp] theorem W.pcpure_v (a : α) : (pure a : PostconditionT (W bc mc ac lc ak) α).operation.v = ⟨a, rfl⟩ := rfl
@[simp] theorem W.pcbind_c (x : PostconditionT (W bc mc ac lc ak) α) (f : α → PostconditionT (W bc mc ac lc ak) β) :
    (x >>= f).operation.c = x.operation.c + ((f x.operation.v.val).operation.c + mc) + bc := rfl
@[simp] theorem W.pcbind_v (x : PostconditionT (W bc mc ac lc ak) α) (f : α → PostconditionT (W bc mc ac lc ak) β) :
    (x >>= f).operation.v.val = (f x.operation.v.val).operation.v.val := rfl
@[simp] theorem W.run_c (x : PostconditionT (W bc mc ac lc ak) α) : x.run.c = x.operation.c + mc := rfl
@[simp] theorem W.run_v (x : PostconditionT (W bc mc ac lc ak) α) : x.run.v = x.operation.v.val := rfl
end

theorem dforIn'_eq_fin {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type x → Type x'} [Monad n]
    {lift : ∀ γ δ, (γ → n δ) → m γ → n δ} {γ : Type x}
    {it : IterM (α := α) m β} {init : γ} {P hP} {Pl : β → γ → ForInStep γ → Prop}
    {f : (b : β) → P b → (c : γ) → n (Subtype (Pl b c))} :
    IterM.DefaultConsumers.forIn' lift γ Pl it init P hP f =
      (lift _ _ · it.step) (fun s => do
          match s.inflate with
          | .yield it' out h =>
            match ← f out (hP _ <| .direct ⟨_, h⟩) init with
            | ⟨.yield c, _⟩ =>
              IterM.DefaultConsumers.forIn' lift _ Pl it' c P
                (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
            | ⟨.done c, _⟩ => return c
          | .skip it' h =>
            IterM.DefaultConsumers.forIn' lift _ Pl it' init P
              (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
          | .done _ => return init) :=
  dforIn'_eq Pl IteratorLoop.wellFounded_of_finite

theorem loop_cd {m n : Type → Type} [Pure m] [Monad n] lift γ Pl it (init : γ) f :
    @IteratorLoop.forIn CD m Nat _ n CD.loop lift γ Pl it init f =
      IterM.DefaultConsumers.forIn' lift γ Pl it init _ (fun _ => id) f := rfl
theorem loop_fm {α β γ' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {o : Type x → Type x'}
    [Monad n] [Monad o] [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α}
    {f : β → PostconditionT n (Option γ')} lift' γ Pl it (init : γ) g :
    @IteratorLoop.forIn (Types.FilterMap α m n lift f) n γ' _ o Types.FilterMap.instIteratorLoop lift' γ Pl it init g =
      IterM.DefaultConsumers.forIn' lift' γ Pl it init _ (fun _ => id) g := rfl
theorem loop_map {α β γ' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {o : Type x → Type x'}
    [Monad n] [Monad o] [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α}
    {f : β → PostconditionT n γ'} lift' γ Pl it (init : γ) g :
    @IteratorLoop.forIn (Types.Map α m n lift f) n γ' _ o Types.Map.instIteratorLoop lift' γ Pl it init g =
      IterM.DefaultConsumers.forIn' lift' γ Pl it init _ (fun _ => id) g := rfl

theorem pc_run_id {α : Type u} (x : PostconditionT Id α) : x.run = x.operation.val := rfl
theorem pc_op_pure_id {α : Type u} (a : α) : (pure a : PostconditionT Id α).operation = ⟨a, rfl⟩ := rfl

theorem id_bind {α β : Type u} (x : Id α) (f : α → Id β) : x >>= f = f x.run := rfl
theorem id_map' {α β : Type u} (f : α → β) (x : Id α) : f <$> x = f x.run := rfl
theorem id_run' {α : Type u} (x : α) : Id.run x = x := rfl
theorem pc_pure_op {m : Type w → Type w'} [Monad m] {α : Type w} (a : α) :
    (pure a : PostconditionT m α).operation = pure ⟨a, rfl⟩ := rfl

theorem pc_lift_op {m : Type w → Type w'} {n : Type w → Type w''} [MonadLift m n] {α : Type w}
    (x : PostconditionT m α) : (MonadLift.monadLift x : PostconditionT n α).operation = MonadLift.monadLift x.operation := rfl
theorem toList1 : (ci 1).toList = [0] := by rw [CD.toListS, CD.toList0]
theorem toList2 : (ci 2).toList = [1, 0] := by rw [CD.toListS, toList1]
theorem toArray0 : (ci 0).toArray = #[] := by rw [← Iter.toArray_toList, CD.toList0]
theorem toArray1 : (ci 1).toArray = #[0] := by rw [← Iter.toArray_toList, toList1]

/-! ## Models -/
instance W.weakly100 : WeaklyLawfulMonadAttach (W 1 0 0 0 0) := W.weakly_of (by decide)
instance W.weakly01m : WeaklyLawfulMonadAttach (W 0 1 (-1) 0 0) := W.weakly_of (by decide)
instance W.weakly000 {lc : Int} : WeaklyLawfulMonadAttach (W 0 0 0 lc 0) := W.weakly_of (by decide)

abbrev Bm := W 1 0 0 0 0
abbrev Mm := W 0 1 (-1) 0 0
abbrev Am := W 0 0 1 0 0
abbrev Dm := W 0 0 0 0 1
abbrev L := W 0 0 0 0 0
abbrev Lc := W 0 0 0 1 0
abbrev Mo := W 0 1 0 0 0

/-- Lifts between `W` monads with `bind` defect `0`: the lift into `W 0 _ _ lc` adds `lc` to the
counter; lawful iff `lc = 0`. -/
instance (priority := low) W.liftW {mc ac lc ak mc' ac' lc' ak' : Int} :
    MonadLiftT (W 0 mc ac lc ak) (W 0 mc' ac' lc' ak') :=
  ⟨fun x => ⟨x.c + lc', x.v⟩⟩
instance W.lawfulLiftW {mc ac lc ak mc' ac' ak' : Int} : LawfulMonadLiftT (W 0 mc ac lc ak) (W 0 mc' ac' 0 ak') :=
  ⟨fun _ => W.ext' (by simp [monadLift, MonadLiftT.monadLift]) rfl,
   fun _ _ => W.ext' (by simp [monadLift, MonadLiftT.monadLift]) rfl⟩
theorem W.not_weakly_k {bc mc ac lc ak : Int} (h : ak ≠ 0) (h' : mc + ac = 0) :
    ¬ WeaklyLawfulMonadAttach (W bc mc ac lc ak) := fun ⟨hw⟩ => by
  have := congrArg W.c (@hw Nat ⟨1, 0⟩)
  simp at this
  exact h (by simpa using (show ak * 1 = 0 by omega))

theorem W.not_lawfulLift {mc ac lc ak mc' ac' lc' ak' : Int} (h : lc' ≠ 0) :
    ¬ LawfulMonadLiftT (W 0 mc ac lc ak) (W 0 mc' ac' lc' ak') := fun hl => by
  have := congrArg W.c (@monadLift_pure _ _ _ _ _ hl Nat 0)
  simp [monadLift, MonadLiftT.monadLift] at this; omega
@[simp] theorem W.lift_c {mc ac lc ak mc' ac' lc' ak' : Int} {α : Type} (x : W 0 mc ac lc ak α) :
    (monadLift x : W 0 mc' ac' lc' ak' α).c = x.c + lc' := rfl
@[simp] theorem W.lift_v {mc ac lc ak mc' ac' lc' ak' : Int} {α : Type} (x : W 0 mc ac lc ak α) :
    (monadLift x : W 0 mc' ac' lc' ak' α).v = x.v := rfl
@[simp] theorem W.liftM_c {mc ac lc ak mc' ac' lc' ak' : Int} {α : Type} (x : W 0 mc ac lc ak α) :
    (liftM x : W 0 mc' ac' lc' ak' α).c = x.c + lc' := rfl
@[simp] theorem W.liftM_v {mc ac lc ak mc' ac' lc' ak' : Int} {α : Type} (x : W 0 mc ac lc ak α) :
    (liftM x : W 0 mc' ac' lc' ak' α).v = x.v := rfl

theorem pc_liftM_op {m : Type w → Type w'} {n : Type w → Type w''} [MonadLift m n] {α : Type w}
    (x : PostconditionT m α) : (liftM x : PostconditionT n α).operation = MonadLift.monadLift x.operation := rfl
theorem pc_monadLift_op {m : Type w → Type w'} {n : Type w → Type w''} [MonadLift m n] {α : Type w}
    (x : PostconditionT m α) : (monadLift x : PostconditionT n α).operation = MonadLift.monadLift x.operation := rfl
theorem mkLift_eq {m : Type w → Type w'} {n : Type w → Type w''} (f : ∀ {α}, m α → n α) {α : Type w} (x : m α) :
    @MonadLift.monadLift m n ⟨f⟩ α x = f x := rfl
@[simp] theorem W.pcbind_v' {bc mc ac lc ak : Int} {α β : Type} (x : PostconditionT (W bc mc ac lc ak) α)
    (f : α → PostconditionT (W bc mc ac lc ak) β) :
    (x >>= f).operation.v = ⟨(f x.operation.v.val).operation.v.val, x.operation.v.val,
      x.operation.v.property, (f x.operation.v.val).operation.v.property⟩ := rfl

theorem step_flattenAfter' {α α₂ β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    {it₁ : IterM (α := α) m (IterM (α := α₂) m β)} {it₂ : Option (IterM (α := α₂) m β)} :
  ((flattenAfterP%) it₁ it₂).step = (
    match it₂ with
    | none => do
      match (← it₁.step).inflate with
      | .yield it₁' it₂' h => return .deflate (.skip ((flattenAfterP%) it₁' (some it₂')) (.outerYield h))
      | .skip it₁' h => return .deflate (.skip ((flattenAfterP%) it₁' none) (.outerSkip h))
      | .done h => return .deflate (.done (.outerDone h))
    | some it₂ => do
      match (← it₂.step).inflate with
      | .yield it₂' out h => return .deflate (.yield ((flattenAfterP%) it₁ (some it₂')) out (.innerYield h))
      | .skip it₂' h => return .deflate (.skip ((flattenAfterP%) it₁ (some it₂')) (.innerSkip h))
      | .done h => return .deflate (.skip ((flattenAfterP%) it₁ none) (.innerDone h))) := by
  cases it₂
  all_goals
  · apply bind_congr; intro step
    cases step.inflate using PlausibleIterStep.casesOn <;> rfl

/-- One evaluation round on hypothesis `h`: unfold the combinators to `filterMapWithPostcondition`
steps, the lifts and the base steps, then the monad operations and `Shrink` round trips. -/
macro "evs" h:ident : tactic => `(tactic| (
  (try simp only [Iter.mapM, IterM.mapM, Iter.filterMapM, IterM.filterMapM,
    Iter.filterM, IterM.filterM, Iter.mapWithPostcondition, Iter.filterMapWithPostcondition,
    Iter.filterWithPostcondition, IterM.filterWithPostcondition, Iter.flatMapM, Iter.flatMapAfterM,
    IterM.flatMapM, IterM.flatMapAfterM, step_mwp, step_fmwp, step_flattenAfter'] at $h:ident)
  (try simp only [liftM_id, monadLift_id, CD.istep, CD.toIterM_ci, CD.stepv, TK.istep, TK.stepv] at $h:ident)
  (try simp only [W.bind_c, W.bind_v, W.pure_c, W.pure_v, W.map_c, W.map_v, W.attach_c, W.attach_v,
    W.pcmap_c, W.pcmap_v, W.attachLift_c, W.attachLift_v, W.pcpure_c, W.pcpure_v, W.pcbind_c, W.pcbind_v,
    W.run_c, W.run_v, W.lift_c, W.lift_v, W.liftM_c, W.liftM_v, U.bind_c, U.bind_d, U.bind_v, U.pure_c, U.pure_d, U.pure_v, U.map_c, U.map_d, U.map_v,
    U.lift_c, U.lift_d, U.lift_v, U.liftM_c, U.liftM_d, U.liftM_v,
    SB.bind_c, SB.bind_v, SB.pure_c, SB.pure_v, SB.map_v, SB.map_c_nsub, SB.attach_c_nsub, SB.attach_v,
    SB.pcmap_c_sub, SB.pcmap_v, SB.attachLift_c_nsub, SB.attachLift_v, SB.pcpure_c, SB.pcpure_v,
    SB.run_c_nsub, SB.run_v, BW.bind_c, BW.bind_v, BW.pure_c, BW.pure_v, BW.map_c, BW.map_v,
    BW.lift_c, BW.lift_v, BW.liftM_c, BW.liftM_v, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, Bool.not_false, pc_run_id, pc_op_pure_id, pc_lift_op, pc_liftM_op, pc_monadLift_op, mkLift_eq, W.pcbind_v', Shrink.inflate_deflate, List.mapM,
    List.mapM.loop, Id.run, id_pure, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, id_bind, id_map', id_run', pc_pure_op, monadLift_self, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true, ULift.up_down] at $h:ident)))

/-- Unfold the loop consumers to `IterM.DefaultConsumers.forIn'`. -/
macro "evloop" h:ident : tactic => `(tactic| (
  (try simp only [ForIn.forIn, ForIn'.forIn', instForInOfForIn', Iter.instForIn', IterM.instForIn',
    IteratorLoop.finiteForIn', loop_cd, loop_fm, loop_map, Iter.foldM, IterM.foldM, Iter.fold, IterM.fold,
    Iter.anyM, IterM.anyM, Iter.allM, IterM.allM, Iter.any, IterM.any, Iter.all, IterM.all, Iter.findSomeM?,
    Iter.findM?, Iter.filterMap, Iter.map, Iter.filter, IterM.filterMap, IterM.map, IterM.filter,
    Iter.toIterM_toIter] at $h:ident)))

/-- Evaluate `h` completely: unfold `toArray.go` / the loop and evaluate, until nothing changes. -/
macro "evh" h:ident : tactic => `(tactic| (
  evs $h; repeat ((first
    | rw [IterM.toList] at $h:ident
    | rw [IterM.toArray] at $h:ident
    | rw [go_eq'] at $h:ident
    | rw [go_eq' (it := IterM.mapWithPostcondition _ _)] at $h:ident
    | rw [go_eq' (it := IterM.filterMapWithPostcondition _ _)] at $h:ident); evs $h)))
macro "evl" h:ident : tactic => `(tactic| (
  evloop $h; evs $h; repeat (rw [dforIn'_eq_fin] at $h:ident; evs $h)))

/-- Finish an `Array.mapM` comparison: evaluate `Array.mapM` on `#[]` / `#[0]` and compare counters. -/
macro "arrfin" : tactic => `(tactic| first
  | omega
  | (rw [Array.mapM, Array.mapM.map] at *; simp at *; done)
  | (simp [Array.mapM_eq_mapM_toList, List.mapM, List.mapM.loop] at *; done)
  | (simp [Array.mapM_eq_mapM_toList, List.mapM, List.mapM.loop] at *; omega))

/-- Finish a comparison with a `List` consumer (`foldlM`, `anyM`, `findSomeM?`, `findM?`). -/
macro "lfin" : tactic => `(tactic| first
  | omega
  | (simp [List.foldlM, List.anyM, List.allM, List.findSomeM?, List.findM?] at *; done)
  | (simp [List.foldlM, List.anyM, List.allM, List.findSomeM?, List.findM?] at *; omega))

/-- Finish a comparison with a `List`/`Array` loop on `[0]` / `#[0]`. -/
macro "cfin" h:ident : tactic => `(tactic| (
  (try simp only [List.forIn', Array.forIn'] at $h:ident)
  (try simp only [toList1, toArray1] at $h:ident)
  first
    | omega
    | (simp [List.forIn'.loop, Array.forIn'.loop, Array.foldlM, Array.foldlM.loop, Array.anyM,
        Array.anyM.loop] at $h:ident; done)
    | (simp [List.forIn'.loop, Array.forIn'.loop, Array.foldlM, Array.foldlM.loop, Array.anyM,
        Array.anyM.loop] at $h:ident; omega)))

/-! ## Removable verdicts -/

/-- The lift of the Iter loops (f c.run) is a lawful lift-bind function for every monad. -/
theorem lbf {m : Type x → Type x'} [Monad m] :
    @Internal.LawfulMonadLiftBindFunction Id m _ _ (fun _ _ f x => f x.run) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- The default loop over a mapped pure iterator is the default loop over the base iterator with
the map moved into the body, in any monad (induction over the steps). -/
theorem dforIn'_map {α β β₂ : Type w} {γ : Type x} [Iterator α Id β] [Finite α Id] {n : Type x → Type x'}
    [Monad n] (f : β → β₂) (body : β₂ → γ → n (Subtype fun (_ : ForInStep γ) => True))
    (it : IterM (α := α) Id β) (init : γ) {P hP Q hQ} :
    IterM.DefaultConsumers.forIn' (fun _ _ k c => k c.run) γ (fun _ _ _ => True) (it.map f) init P hP
        (fun out _ acc => body out acc) =
      IterM.DefaultConsumers.forIn' (fun _ _ k c => k c.run) γ (fun _ _ _ => True) it init Q hQ
        (fun out _ acc => body (f out) acc) := by
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs
  rw [dforIn'_eq_fin, dforIn'_eq_fin]
  simp only [IterM.step_map, Id.run_bind]
  rcases hs : it.step.run.inflate with ⟨_ | _ | _, h⟩
  · simp only [Id.run_pure, Shrink.inflate_deflate]
    apply bind_congr; intro r
    rcases r with ⟨_ | _, _⟩ <;> first | exact ihy h _ | rfl
  · simp only [Id.run_pure, Shrink.inflate_deflate]
    exact ihs h _
  · simp only [Id.run_pure, Shrink.inflate_deflate]

namespace MBc
/-! Copies of law-free lemmas of the ItMonadMB pass (runs/hand8/scratch_ItMonadMB/rem_all.lean): the inner
filterMapWithPostcondition moved along a lawful lift, and the fusion lemma without laws of the base lift. -/
theorem liftM_eq {m n : Type w → Type w'} [MonadLiftT m n] (x : m α) : (liftM x : n α) = monadLift x := rfl

theorem step_fmwp {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] {it : IterM (α := α) m β} {f : β → PostconditionT n (Option γ)}
    [Monad n] [MonadLiftT m n] :
  (it.filterMapWithPostcondition f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨none, h'⟩ =>
        pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (.yieldNone (out := out) h h')
      | ⟨some out', h'⟩ =>
        pure <| .deflate <| .yield (it'.filterMapWithPostcondition f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (by exact .done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [PlausibleIterStep.skip, PlausibleIterStep.yield]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem pc_lift_op {m : Type w → Type w'} {n : Type w → Type w''} [MonadLift m n] (x : PostconditionT m α) :
    (monadLift x : PostconditionT n α).operation = MonadLift.monadLift x.operation := rfl

theorem pc_liftL_op {m : Type w → Type w'} {n : Type w → Type w''} [MonadLift m n] (x : PostconditionT m α) :
    (MonadLift.monadLift x : PostconditionT n α).operation = MonadLift.monadLift x.operation := rfl

/-- A variant of `Subtype.casesOn` that is not reduced by `simp` (copy of a private library def). -/
@[elab_as_elim]
def subtypeCasesOn' := @Subtype.casesOn

/-- Copy of a private library def. -/
def optionPelim' {α : Type u_1} (t : Option α) {β : Sort u_2}
    (n : t = none → β) (s : (val : α) → t = some val → β) : β :=
  match t with
  | some a => s a rfl
  | none => n rfl

theorem bind_subtypeCasesOn'_eq_map_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m] {P : α → Prop}
    (x : m (Subtype P)) (f : α → m β) :
    x >>= (fun a => subtypeCasesOn' a fun a _ => f a) = (Subtype.val <$> x) >>= f := by
  simp [subtypeCasesOn']

theorem bind_eq_bind_subtypeCasesOn'_optionPelim' {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {P : Option α → Prop} (x : m (Subtype P)) (f : Subtype P → m β) :
    x >>= f = x >>= (fun a => subtypeCasesOn' a fun (a : Option α) ha => optionPelim' a (fun h =>
          f ⟨none, by simp_all⟩) (fun a h => f ⟨some a, by simp_all⟩)) := by
  apply bind_congr; intro x
  rcases x with ⟨_ | ⟨a⟩⟩
  all_goals simp [subtypeCasesOn', optionPelim']

/-- The library's private `IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'`
without `[LawfulMonad m]` and `[LawfulMonadLiftT m n]` (its proof uses neither). -/
theorem toList_fmwp_fmwp' {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    {_ : MonadLiftT m n} [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n (Option γ)} {g : γ → PostconditionT o (Option δ)}
    {fg : β → PostconditionT o (Option δ)}
    {it : IterM (α := α) m β}
    (h : ∀ b, (fg b).run = do match ← (f b).run with | none => return none | some fb => (g fb).run) :
    letI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapWithPostcondition f).filterMapWithPostcondition g).toList =
      (it.filterMapWithPostcondition (n := o) fg).toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  letI : MonadLift n o := ⟨monadLift⟩
  haveI : LawfulMonadLift n o := ⟨LawfulMonadLiftT.monadLift_pure, LawfulMonadLiftT.monadLift_bind⟩
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step, IterM.step_filterMapWithPostcondition,
    bind_assoc, IterM.step_filterMapWithPostcondition, IterM.step_filterMapWithPostcondition]
  simp only [bind_assoc, liftM_bind]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, liftM_bind]
    rw [PostconditionT.operation_eq_map_mk_operation, liftM_map, bind_map_left]
    simp
    conv =>
      rhs
      rw [bind_eq_bind_subtypeCasesOn'_optionPelim' (x := (fg _).operation)]
      simp only [pure_bind, Shrink.inflate_deflate]
      rw [bind_subtypeCasesOn'_eq_map_bind]
    conv =>
      lhs
      rw [bind_eq_bind_subtypeCasesOn'_optionPelim']
      simp only [liftM_pure, pure_bind, Shrink.inflate_deflate, bind_assoc]
      simp +singlePass only [bind_eq_bind_subtypeCasesOn'_optionPelim' (x := (g _).operation)]
      simp only [pure_bind, Shrink.inflate_deflate]
      simp only [bind_subtypeCasesOn'_eq_map_bind]
      rw [← liftM_map]
    simp only [← PostconditionT.run_eq_map, h, bind_assoc, optionPelim']
    apply bind_congr; intro fx
    split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

/-- Transport of the inner `filterMapWithPostcondition` from `n` to `o` along the lawful lift
(no laws of `n` needed: every `n`-action reaches `o` through the lift). -/
theorem toList_fmwp_lift {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad n] [Monad o] [LawfulMonad o] [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n (Option γ)} {g : γ → PostconditionT o (Option δ)}
    {it : IterM (α := α) m β} :
    letI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapWithPostcondition f).filterMapWithPostcondition g).toList =
      ((it.filterMapWithPostcondition (n := o) (fun b => liftM (f b))).filterMapWithPostcondition g).toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  letI : MonadLift n o := ⟨monadLift⟩
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step, step_fmwp, step_fmwp, step_fmwp, step_fmwp]
  simp only [bind_assoc, liftM_bind, liftM_pure]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [bind_assoc, liftM_bind, liftM_pure, pure_bind, Shrink.inflate_deflate, liftM_eq,
      monadLift_self, pc_lift_op]
    apply bind_congr; intro x
    rcases x with ⟨_ | x, hx⟩
    · simp [ihy ‹_›]
    · simp only [liftM_pure, liftM_eq, monadLift_self, pure_bind, Shrink.inflate_deflate, bind_assoc,
        PlausibleIterStep.yield]
      apply bind_congr; intro y
      rcases y with ⟨_ | y, hy⟩ <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

end MBc

/-- The toList of a filterMap iterator only depends on the lift through its values. -/
theorem fm_lift_congr {α β γ : Type w} {n : Type w → Type w''} [Monad n] [Iterator α Id β] [Finite α Id]
    {F : β → PostconditionT n (Option γ)} {it : IterM (α := α) Id β} (l1 l2 : ⦃δ : Type w⦄ → Id δ → n δ)
    (h : l1 = l2) :
    (IterM.InternalCombinators.filterMap l1 F it).toList = (IterM.InternalCombinators.filterMap l2 F it).toList := by
  cases h; rfl

/-! ## Necessary verdicts -/


/-! ### Transferred refutations (WPSpec) -/

-- `Std.WP.Spec.Iter.forIn_filterMapWithPostcondition` idx 10: necessary; the hand8/hand10 model of Std.Iter.forIn_filterMapWithPostcondition idx 8, transferred with the exact WP (n = Mo (map counts 1), o = L, lawful lift, it = [0]: only the right side maps ((f out).run))
theorem WPS.Iter.forIn_filterMapWithPostcondition.h10 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMapWithPostcondition 10 := fun h => by
  letI := WPSpecHand.exWPM (L) Nat
  have := WPSpecHand.ex_eq (L) Nat (h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Mo) (o := L) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (L) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (L) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.forIn_filterMapWithPostcondition` idx 16: necessary; the hand8/hand10 model of Std.Iter.forIn_filterMapWithPostcondition idx 12, transferred with the exact WP (n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value)
theorem WPS.Iter.forIn_filterMapWithPostcondition.h16 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMapWithPostcondition 16 := fun h => by
  letI := WPSpecHand.exWPM (Lc) Nat
  have := WPSpecHand.ex_eq (Lc) Nat (h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (Lc) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Lc) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.forIn_filterMapM` idx 10: necessary; the hand8/hand10 model of Std.Iter.forIn_filterMapM idx 8, transferred with the exact WP (n = Mm (map counts 1, attach -1: weakly lawful, not lawful), o = L, it = [0]: only the left side attaches)
theorem WPS.Iter.forIn_filterMapM.h10 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMapM 10 := fun h => by
  letI := WPSpecHand.exWPM (L) Nat
  have := WPSpecHand.ex_eq (L) Nat (h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Mm) (o := L) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (L) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (L) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.forIn_filterMapM` idx 16: necessary; the hand8/hand10 model of Std.Iter.forIn_filterMapM idx 12, transferred with the exact WP (n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches)
theorem WPS.Iter.forIn_filterMapM.h16 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMapM 16 := fun h => by
  letI := WPSpecHand.exWPM (L) Nat
  have := WPSpecHand.ex_eq (L) Nat (h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Am) (o := L) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (L) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (L) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.forIn_filterMapM` idx 18: necessary; the hand8/hand10 model of Std.Iter.forIn_filterMapM idx 14, transferred with the exact WP (n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value)
theorem WPS.Iter.forIn_filterMapM.h18 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMapM 18 := fun h => by
  letI := WPSpecHand.exWPM (Lc) Nat
  have := WPSpecHand.ex_eq (Lc) Nat (h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (Lc) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Lc) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.forIn_mapWithPostcondition` idx 10: necessary; the hand8/hand10 model of Std.Iter.forIn_mapWithPostcondition idx 8, transferred with the exact WP (n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip))
theorem WPS.Iter.forIn_mapWithPostcondition.h10 : ¬ drop0% Std.WP.Spec.Iter.forIn_mapWithPostcondition 10 := fun h => by
  letI := WPSpecHand.exWPM (BW) Nat
  have := WPSpecHand.ex_eq (BW) Nat (h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun b => pure b) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (BW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (BW) Nat _))
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.WP.Spec.Iter.forIn_mapWithPostcondition` idx 16: necessary; the hand8/hand10 model of Std.Iter.forIn_mapWithPostcondition idx 12, transferred with the exact WP (n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value)
theorem WPS.Iter.forIn_mapWithPostcondition.h16 : ¬ drop0% Std.WP.Spec.Iter.forIn_mapWithPostcondition 16 := fun h => by
  letI := WPSpecHand.exWPM (Lc) Nat
  have := WPSpecHand.ex_eq (Lc) Nat (h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := L) (o := Lc) (f := pure) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (Lc) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Lc) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.forIn_mapM` idx 10: necessary; the hand8/hand10 model of Std.Iter.forIn_mapM idx 8, transferred with the exact WP (n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip))
theorem WPS.Iter.forIn_mapM.h10 : ¬ drop0% Std.WP.Spec.Iter.forIn_mapM 10 := fun h => by
  letI := WPSpecHand.exWPM (BW) Nat
  have := WPSpecHand.ex_eq (BW) Nat (h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun b => pure b) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (BW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (BW) Nat _))
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.WP.Spec.Iter.forIn_mapM` idx 16: necessary; the hand8/hand10 model of Std.Iter.forIn_mapM idx 12, transferred with the exact WP (n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches)
theorem WPS.Iter.forIn_mapM.h16 : ¬ drop0% Std.WP.Spec.Iter.forIn_mapM 16 := fun h => by
  letI := WPSpecHand.exWPM (L) Nat
  have := WPSpecHand.ex_eq (L) Nat (h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Am) (o := L) (f := pure) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (L) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (L) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.forIn_mapM` idx 18: necessary; the hand8/hand10 model of Std.Iter.forIn_mapM idx 14, transferred with the exact WP (n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value)
theorem WPS.Iter.forIn_mapM.h18 : ¬ drop0% Std.WP.Spec.Iter.forIn_mapM 18 := fun h => by
  letI := WPSpecHand.exWPM (Lc) Nat
  have := WPSpecHand.ex_eq (Lc) Nat (h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := L) (o := Lc) (f := pure) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (Lc) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Lc) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.forIn_filterWithPostcondition` idx 9: necessary; the hand8/hand10 model of Std.Iter.forIn_filterWithPostcondition idx 7, transferred with the exact WP (n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip))
theorem WPS.Iter.forIn_filterWithPostcondition.h9 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterWithPostcondition 9 := fun h => by
  letI := WPSpecHand.exWPM (BW) Nat
  have := WPSpecHand.ex_eq (BW) Nat (h (α := CD) (β := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (BW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (BW) Nat _))
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.WP.Spec.Iter.forIn_filterWithPostcondition` idx 15: necessary; the hand8/hand10 model of Std.Iter.forIn_filterWithPostcondition idx 11, transferred with the exact WP (n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value)
theorem WPS.Iter.forIn_filterWithPostcondition.h15 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterWithPostcondition 15 := fun h => by
  letI := WPSpecHand.exWPM (Lc) Nat
  have := WPSpecHand.ex_eq (Lc) Nat (h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (Lc) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Lc) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.forIn_filterM` idx 9: necessary; the hand8/hand10 model of Std.Iter.forIn_filterM idx 7, transferred with the exact WP (n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip))
theorem WPS.Iter.forIn_filterM.h9 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterM 9 := fun h => by
  letI := WPSpecHand.exWPM (BW) Nat
  have := WPSpecHand.ex_eq (BW) Nat (h (α := CD) (β := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (BW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (BW) Nat _))
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.WP.Spec.Iter.forIn_filterM` idx 15: necessary; the hand8/hand10 model of Std.Iter.forIn_filterM idx 11, transferred with the exact WP (n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches)
theorem WPS.Iter.forIn_filterM.h15 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterM 15 := fun h => by
  letI := WPSpecHand.exWPM (L) Nat
  have := WPSpecHand.ex_eq (L) Nat (h (α := CD) (β := Nat) (it := ci 1) (n := Am) (o := L) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (L) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (L) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.forIn_filterM` idx 17: necessary; the hand8/hand10 model of Std.Iter.forIn_filterM idx 13, transferred with the exact WP (n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value)
theorem WPS.Iter.forIn_filterM.h17 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterM 17 := fun h => by
  letI := WPSpecHand.exWPM (Lc) Nat
  have := WPSpecHand.ex_eq (Lc) Nat (h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (Pred := (Lc) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Lc) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.foldM_filterMapWithPostcondition` idx 12: necessary; the hand8/hand10 model of Std.Iter.foldM_filterMapWithPostcondition idx 10, transferred with the exact WP (n = Mo (map counts 1), o = L, lawful lift, it = [0]: only the right side maps ((f b).run))
theorem WPS.Iter.foldM_filterMapWithPostcondition.h12 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMapWithPostcondition 12 := fun h => by
  letI := WPSpecHand.exWPM (L) Nat
  have := WPSpecHand.ex_eq (L) Nat (h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Mo) (o := L) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (L) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (L) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.foldM_filterMapWithPostcondition` idx 21: necessary; the hand8/hand10 model of Std.Iter.foldM_filterMapWithPostcondition idx 17, transferred with the exact WP (n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value)
theorem WPS.Iter.foldM_filterMapWithPostcondition.h21 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMapWithPostcondition 21 := fun h => by
  letI := WPSpecHand.exWPM (Lc) Nat
  have := WPSpecHand.ex_eq (Lc) Nat (h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (Lc) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Lc) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.foldM_filterMapM` idx 12: necessary; the hand8/hand10 model of Std.Iter.foldM_filterMapM idx 10, transferred with the exact WP (n = Mm (map counts 1, attach -1: weakly lawful, not lawful), o = L, it = [0]: only the left side attaches)
theorem WPS.Iter.foldM_filterMapM.h12 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMapM 12 := fun h => by
  letI := WPSpecHand.exWPM (L) Nat
  have := WPSpecHand.ex_eq (L) Nat (h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Mm) (o := L) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (L) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (L) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.foldM_filterMapM` idx 13: necessary; the hand8/hand10 model of Std.Iter.foldM_filterMapM idx 11, transferred with the exact WP (n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches)
theorem WPS.Iter.foldM_filterMapM.h13 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMapM 13 := fun h => by
  letI := WPSpecHand.exWPM (L) Nat
  have := WPSpecHand.ex_eq (L) Nat (h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Am) (o := L) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (L) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (L) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.foldM_filterMapM` idx 23: necessary; the hand8/hand10 model of Std.Iter.foldM_filterMapM idx 19, transferred with the exact WP (n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value)
theorem WPS.Iter.foldM_filterMapM.h23 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMapM 23 := fun h => by
  letI := WPSpecHand.exWPM (Lc) Nat
  have := WPSpecHand.ex_eq (Lc) Nat (h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (Lc) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Lc) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.foldM_mapWithPostcondition` idx 15: necessary; the hand8/hand10 model of Std.Iter.foldM_mapWithPostcondition idx 13, transferred with the exact WP (n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip))
theorem WPS.Iter.foldM_mapWithPostcondition.h15 : ¬ drop0% Std.WP.Spec.Iter.foldM_mapWithPostcondition 15 := fun h => by
  letI := WPSpecHand.exWPM (BW) Nat
  have := WPSpecHand.ex_eq (BW) Nat (h (m := Id) (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun b => pure b) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (BW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (BW) Nat _))
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.WP.Spec.Iter.foldM_mapWithPostcondition` idx 24: necessary; the hand8/hand10 model of Std.Iter.foldM_mapWithPostcondition idx 20, transferred with the exact WP (n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value)
theorem WPS.Iter.foldM_mapWithPostcondition.h24 : ¬ drop0% Std.WP.Spec.Iter.foldM_mapWithPostcondition 24 := fun h => by
  letI := WPSpecHand.exWPM (Lc) Nat
  have := WPSpecHand.ex_eq (Lc) Nat (h (m := Id) (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Lc) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (Lc) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Lc) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.foldM_mapM` idx 12: necessary; the hand8/hand10 model of Std.Iter.foldM_mapM idx 10, transferred with the exact WP (n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip))
theorem WPS.Iter.foldM_mapM.h12 : ¬ drop0% Std.WP.Spec.Iter.foldM_mapM 12 := fun h => by
  letI := WPSpecHand.exWPM (BW) Nat
  have := WPSpecHand.ex_eq (BW) Nat (h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun b => pure b) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (BW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (BW) Nat _))
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.WP.Spec.Iter.foldM_mapM` idx 13: necessary; the hand8/hand10 model of Std.Iter.foldM_mapM idx 11, transferred with the exact WP (n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches)
theorem WPS.Iter.foldM_mapM.h13 : ¬ drop0% Std.WP.Spec.Iter.foldM_mapM 13 := fun h => by
  letI := WPSpecHand.exWPM (L) Nat
  have := WPSpecHand.ex_eq (L) Nat (h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Am) (o := L) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (L) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (L) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.foldM_mapM` idx 23: necessary; the hand8/hand10 model of Std.Iter.foldM_mapM idx 19, transferred with the exact WP (n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value)
theorem WPS.Iter.foldM_mapM.h23 : ¬ drop0% Std.WP.Spec.Iter.foldM_mapM 23 := fun h => by
  letI := WPSpecHand.exWPM (Lc) Nat
  have := WPSpecHand.ex_eq (Lc) Nat (h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Lc) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (Lc) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Lc) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.foldM_filterWithPostcondition` idx 11: necessary; the hand8/hand10 model of Std.Iter.foldM_filterWithPostcondition idx 9, transferred with the exact WP (n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip))
theorem WPS.Iter.foldM_filterWithPostcondition.h11 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterWithPostcondition 11 := fun h => by
  letI := WPSpecHand.exWPM (BW) Nat
  have := WPSpecHand.ex_eq (BW) Nat (h (α := CD) (β := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (BW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (BW) Nat _))
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.WP.Spec.Iter.foldM_filterWithPostcondition` idx 20: necessary; the hand8/hand10 model of Std.Iter.foldM_filterWithPostcondition idx 16, transferred with the exact WP (n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value)
theorem WPS.Iter.foldM_filterWithPostcondition.h20 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterWithPostcondition 20 := fun h => by
  letI := WPSpecHand.exWPM (Lc) Nat
  have := WPSpecHand.ex_eq (Lc) Nat (h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (Lc) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Lc) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.foldM_filterM` idx 11: necessary; the hand8/hand10 model of Std.Iter.foldM_filterM idx 9, transferred with the exact WP (n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip))
theorem WPS.Iter.foldM_filterM.h11 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterM 11 := fun h => by
  letI := WPSpecHand.exWPM (BW) Nat
  have := WPSpecHand.ex_eq (BW) Nat (h (α := CD) (β := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (BW) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (BW) Nat _))
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.WP.Spec.Iter.foldM_filterM` idx 12: necessary; the hand8/hand10 model of Std.Iter.foldM_filterM idx 10, transferred with the exact WP (n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches)
theorem WPS.Iter.foldM_filterM.h12 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterM 12 := fun h => by
  letI := WPSpecHand.exWPM (L) Nat
  have := WPSpecHand.ex_eq (L) Nat (h (α := CD) (β := Nat) (it := ci 1) (n := Am) (o := L) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (L) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (L) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.foldM_filterM` idx 22: necessary; the hand8/hand10 model of Std.Iter.foldM_filterM idx 18, transferred with the exact WP (n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value)
theorem WPS.Iter.foldM_filterM.h22 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterM 22 := fun h => by
  letI := WPSpecHand.exWPM (Lc) Nat
  have := WPSpecHand.ex_eq (Lc) Nat (h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (Pred := (Lc) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Lc) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.fold_filterMapM` idx 11: necessary; the hand8/hand10 model of Std.Iter.fold_filterMapM idx 10, transferred with the exact WP (n = Am (lawful, attach counts 1), it = [0]: only the left side attaches)
theorem WPS.Iter.fold_filterMapM.h11 : ¬ drop0% Std.WP.Spec.Iter.fold_filterMapM 11 := fun h => by
  letI := WPSpecHand.exWPM (Am) Nat
  have := WPSpecHand.ex_eq (Am) Nat (h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Am) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => d) (Pred := (Am) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Am) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.fold_mapM` idx 11: necessary; the hand8/hand10 model of Std.Iter.fold_mapM idx 10, transferred with the exact WP (n = Am (lawful, attach counts 1), it = [0]: only the left side attaches)
theorem WPS.Iter.fold_mapM.h11 : ¬ drop0% Std.WP.Spec.Iter.fold_mapM 11 := fun h => by
  letI := WPSpecHand.exWPM (Am) Nat
  have := WPSpecHand.ex_eq (Am) Nat (h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Am) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => d) (Pred := (Am) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Am) Nat _))
  have := congrArg W.c this
  evl this
  omega

-- `Std.WP.Spec.Iter.fold_filterM` idx 10: necessary; the hand8/hand10 model of Std.Iter.fold_filterM idx 9, transferred with the exact WP (n = Am (lawful, attach counts 1), it = [0]: only the left side attaches)
theorem WPS.Iter.fold_filterM.h10 : ¬ drop0% Std.WP.Spec.Iter.fold_filterM 10 := fun h => by
  letI := WPSpecHand.exWPM (Am) Nat
  have := WPSpecHand.ex_eq (Am) Nat (h (α := CD) (β := Nat) (it := ci 1) (n := Am) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => d) (Pred := (Am) Nat → Prop) (EPosts := Unit) (Q := fun b c => c = pure b) (eQ := ()) (WPSpecHand.ex_self (Am) Nat _))
  have := congrArg W.c this
  evl this
  omega

end ItMonadIterHand

end MI

/-! ## Main premises `h` of the combinator specs -/

section Prem
open Std Std.Iterators
namespace WPSpecHand.Prem

-- `Std.WP.Spec.IterM.forIn_filterMapWithPostcondition` idx 32: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.forIn_filterMapWithPostcondition.h32 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapWithPostcondition 32 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (β₂ := Nat) (γ := Nat) (it := [0].iterM Id) (f := fun x => pure (some x)) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.forIn_filterMapM` idx 34: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.forIn_filterMapM.h34 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMapM 34 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (β₂ := Nat) (γ := Nat) (it := [0].iterM Id) (f := fun x => pure (some x)) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.forIn_filterMap` idx 27: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.forIn_filterMap.h27 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterMap 27 := fun H =>
  (H (m := Id) (n := Id) (β := Nat) (β₂ := Nat) (γ := Nat) (it := [0].iterM Id) (f := some) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.forIn_mapWithPostcondition` idx 32: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.forIn_mapWithPostcondition.h32 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapWithPostcondition 32 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (β₂ := Nat) (γ := Nat) (it := [0].iterM Id) (f := fun x => pure x) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.forIn_mapM` idx 34: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.forIn_mapM.h34 : ¬ drop0% Std.WP.Spec.IterM.forIn_mapM 34 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (β₂ := Nat) (γ := Nat) (it := [0].iterM Id) (f := fun x => pure x) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.forIn_map` idx 27: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.forIn_map.h27 : ¬ drop0% Std.WP.Spec.IterM.forIn_map 27 := fun H =>
  (H (m := Id) (n := Id) (β := Nat) (β₂ := Nat) (γ := Nat) (it := [0].iterM Id) (f := id) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.forIn_filterWithPostcondition` idx 31: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.forIn_filterWithPostcondition.h31 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterWithPostcondition 31 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (γ := Nat) (it := [0].iterM Id) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.forIn_filterM` idx 33: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.forIn_filterM.h33 : ¬ drop0% Std.WP.Spec.IterM.forIn_filterM 33 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (γ := Nat) (it := [0].iterM Id) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.forIn_filter` idx 26: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.forIn_filter.h26 : ¬ drop0% Std.WP.Spec.IterM.forIn_filter 26 := fun H =>
  (H (m := Id) (n := Id) (β := Nat) (γ := Nat) (it := [0].iterM Id) (f := fun _ => true) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.foldM_filterMapWithPostcondition` idx 34: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.foldM_filterMapWithPostcondition.h34 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapWithPostcondition 34 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun x => pure (some x)) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.foldM_filterMapM` idx 36: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.foldM_filterMapM.h36 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMapM 36 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun x => pure (some x)) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.foldM_mapWithPostcondition` idx 34: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.foldM_mapWithPostcondition.h34 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapWithPostcondition 34 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun x => pure x) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.foldM_mapM` idx 36: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.foldM_mapM.h36 : ¬ drop0% Std.WP.Spec.IterM.foldM_mapM 36 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun x => pure x) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.foldM_filterWithPostcondition` idx 33: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.foldM_filterWithPostcondition.h33 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterWithPostcondition 33 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.foldM_filterM` idx 35: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.foldM_filterM.h35 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterM 35 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.foldM_filterMap` idx 27: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.foldM_filterMap.h27 : ¬ drop0% Std.WP.Spec.IterM.foldM_filterMap 27 := fun H =>
  (H (m := Id) (n := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iterM Id) (f := some) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.foldM_map` idx 27: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.foldM_map.h27 : ¬ drop0% Std.WP.Spec.IterM.foldM_map 27 := fun H =>
  (H (m := Id) (n := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iterM Id) (f := id) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.foldM_filter` idx 26: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.foldM_filter.h26 : ¬ drop0% Std.WP.Spec.IterM.foldM_filter 26 := fun H =>
  (H (m := Id) (n := Id) (β := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun _ => true) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.fold_filterMapWithPostcondition` idx 27: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.fold_filterMapWithPostcondition.h27 : ¬ drop0% Std.WP.Spec.IterM.fold_filterMapWithPostcondition 27 := fun H =>
  (H (m := Id) (n := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun x => pure (some x)) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.fold_filterMapM` idx 29: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.fold_filterMapM.h29 : ¬ drop0% Std.WP.Spec.IterM.fold_filterMapM 29 := fun H =>
  (H (m := Id) (n := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun x => pure (some x)) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.fold_mapWithPostcondition` idx 27: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.fold_mapWithPostcondition.h27 : ¬ drop0% Std.WP.Spec.IterM.fold_mapWithPostcondition 27 := fun H =>
  (H (m := Id) (n := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun x => pure x) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.fold_mapM` idx 29: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.fold_mapM.h29 : ¬ drop0% Std.WP.Spec.IterM.fold_mapM 29 := fun H =>
  (H (m := Id) (n := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun x => pure x) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.fold_filterWithPostcondition` idx 26: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.fold_filterWithPostcondition.h26 : ¬ drop0% Std.WP.Spec.IterM.fold_filterWithPostcondition 26 := fun H =>
  (H (m := Id) (n := Id) (β := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.fold_filterM` idx 28: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.fold_filterM.h28 : ¬ drop0% Std.WP.Spec.IterM.fold_filterM 28 := fun H =>
  (H (m := Id) (n := Id) (β := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.fold_filterMap` idx 22: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.fold_filterMap.h22 : ¬ drop0% Std.WP.Spec.IterM.fold_filterMap 22 := fun H =>
  (H (m := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iterM Id) (f := some) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.fold_map` idx 22: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.fold_map.h22 : ¬ drop0% Std.WP.Spec.IterM.fold_map 22 := fun H =>
  (H (m := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iterM Id) (f := id) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.IterM.fold_filter` idx 21: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem IterM.fold_filter.h21 : ¬ drop0% Std.WP.Spec.IterM.fold_filter 21 := fun H =>
  (H (m := Id) (β := Nat) (δ := Nat) (it := [0].iterM Id) (f := fun _ => true) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.forIn_filterMapWithPostcondition` idx 27: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.forIn_filterMapWithPostcondition.h27 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMapWithPostcondition 27 := fun H =>
  (H (n := Id) (o := Id) (β := Nat) (β₂ := Nat) (γ := Nat) (it := [0].iter) (f := fun x => pure (some x)) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.forIn_filterMapM` idx 29: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.forIn_filterMapM.h29 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMapM 29 := fun H =>
  (H (n := Id) (o := Id) (β := Nat) (β₂ := Nat) (γ := Nat) (it := [0].iter) (f := fun x => pure (some x)) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.forIn_filterMap` idx 22: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.forIn_filterMap.h22 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterMap 22 := fun H =>
  (H (n := Id) (β := Nat) (β₂ := Nat) (γ := Nat) (it := [0].iter) (f := some) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.forIn_mapWithPostcondition` idx 27: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.forIn_mapWithPostcondition.h27 : ¬ drop0% Std.WP.Spec.Iter.forIn_mapWithPostcondition 27 := fun H =>
  (H (n := Id) (o := Id) (β := Nat) (β₂ := Nat) (γ := Nat) (it := [0].iter) (f := fun x => pure x) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.forIn_mapM` idx 29: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.forIn_mapM.h29 : ¬ drop0% Std.WP.Spec.Iter.forIn_mapM 29 := fun H =>
  (H (n := Id) (o := Id) (β := Nat) (β₂ := Nat) (γ := Nat) (it := [0].iter) (f := fun x => pure x) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.forIn_map` idx 22: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.forIn_map.h22 : ¬ drop0% Std.WP.Spec.Iter.forIn_map 22 := fun H =>
  (H (n := Id) (β := Nat) (β₂ := Nat) (γ := Nat) (it := [0].iter) (f := id) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.forIn_filterWithPostcondition` idx 26: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.forIn_filterWithPostcondition.h26 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterWithPostcondition 26 := fun H =>
  (H (n := Id) (o := Id) (β := Nat) (γ := Nat) (it := [0].iter) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.forIn_filterM` idx 28: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.forIn_filterM.h28 : ¬ drop0% Std.WP.Spec.Iter.forIn_filterM 28 := fun H =>
  (H (n := Id) (o := Id) (β := Nat) (γ := Nat) (it := [0].iter) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.forIn_filter` idx 21: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.forIn_filter.h21 : ¬ drop0% Std.WP.Spec.Iter.forIn_filter 21 := fun H =>
  (H (n := Id) (β := Nat) (γ := Nat) (it := [0].iter) (f := fun _ => true) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.foldM_filterMapWithPostcondition` idx 29: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.foldM_filterMapWithPostcondition.h29 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMapWithPostcondition 29 := fun H =>
  (H (n := Id) (o := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iter) (f := fun x => pure (some x)) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.foldM_filterMapM` idx 31: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.foldM_filterMapM.h31 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMapM 31 := fun H =>
  (H (n := Id) (o := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iter) (f := fun x => pure (some x)) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.foldM_mapWithPostcondition` idx 32: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.foldM_mapWithPostcondition.h32 : ¬ drop0% Std.WP.Spec.Iter.foldM_mapWithPostcondition 32 := fun H =>
  (H (m := Id) (n := Id) (o := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iter) (f := fun x => pure x) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.foldM_mapM` idx 31: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.foldM_mapM.h31 : ¬ drop0% Std.WP.Spec.Iter.foldM_mapM 31 := fun H =>
  (H (n := Id) (o := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iter) (f := fun x => pure x) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.foldM_filterWithPostcondition` idx 28: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.foldM_filterWithPostcondition.h28 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterWithPostcondition 28 := fun H =>
  (H (n := Id) (o := Id) (β := Nat) (δ := Nat) (it := [0].iter) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.foldM_filterM` idx 30: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.foldM_filterM.h30 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterM 30 := fun H =>
  (H (n := Id) (o := Id) (β := Nat) (δ := Nat) (it := [0].iter) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.foldM_filterMap` idx 22: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.foldM_filterMap.h22 : ¬ drop0% Std.WP.Spec.Iter.foldM_filterMap 22 := fun H =>
  (H (n := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iter) (f := some) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.foldM_map` idx 22: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.foldM_map.h22 : ¬ drop0% Std.WP.Spec.Iter.foldM_map 22 := fun H =>
  (H (n := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iter) (f := id) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.foldM_filter` idx 21: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.foldM_filter.h21 : ¬ drop0% Std.WP.Spec.Iter.foldM_filter 21 := fun H =>
  (H (n := Id) (β := Nat) (δ := Nat) (it := [0].iter) (f := fun _ => true) (init := 0) (g := fun d _ => pure d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.fold_filterMapWithPostcondition` idx 22: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.fold_filterMapWithPostcondition.h22 : ¬ drop0% Std.WP.Spec.Iter.fold_filterMapWithPostcondition 22 := fun H =>
  (H (n := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iter) (f := fun x => pure (some x)) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.fold_filterMapM` idx 24: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.fold_filterMapM.h24 : ¬ drop0% Std.WP.Spec.Iter.fold_filterMapM 24 := fun H =>
  (H (n := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iter) (f := fun x => pure (some x)) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.fold_mapWithPostcondition` idx 22: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.fold_mapWithPostcondition.h22 : ¬ drop0% Std.WP.Spec.Iter.fold_mapWithPostcondition 22 := fun H =>
  (H (n := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iter) (f := fun x => pure x) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.fold_mapM` idx 24: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.fold_mapM.h24 : ¬ drop0% Std.WP.Spec.Iter.fold_mapM 24 := fun H =>
  (H (n := Id) (β := Nat) (γ := Nat) (δ := Nat) (it := [0].iter) (f := fun x => pure x) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.fold_filterWithPostcondition` idx 21: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.fold_filterWithPostcondition.h21 : ¬ drop0% Std.WP.Spec.Iter.fold_filterWithPostcondition 21 := fun H =>
  (H (n := Id) (β := Nat) (δ := Nat) (it := [0].iter) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

-- `Std.WP.Spec.Iter.fold_filterM` idx 23: necessary; without the premise every triple holds, but in `Id` with pre `True` and post `False` it does not.
theorem Iter.fold_filterM.h23 : ¬ drop0% Std.WP.Spec.Iter.fold_filterM 23 := fun H =>
  (H (n := Id) (β := Nat) (δ := Nat) (it := [0].iter) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun d _ => d) (P := True) (Q := fun _ => False) (eQ := ())).le_wp trivial

end WPSpecHand.Prem
end Prem

/-! ## Step premises, container classes, iterator loops of `foldM_iter`, variants and `repeatM` -/

namespace WPSpecHand.Manual
open Std Std.Iterators Std.Internal Lean.Order

/-! ### Step premises: an invariant whose final instance is false by definition -/

-- `Std.WP.Spec.forIn'_list` idx 14: necessary; in `Id` over `[0]` with the invariant `pref = []`, the conclusion reduces to `[0] = []`.
theorem forIn'_list.h14 : ¬ drop0% Std.WP.Spec.forIn'_list 14 := fun H =>
  List.cons_ne_nil 0 [] ((H (m := Id) (xs := [0]) (init := 0) (f := fun _ _ b => pure (.yield b))
    (fun p _ _ => p = []) (eposts := ())).le_wp rfl)

-- `Std.WP.Spec.forIn_list` idx 14: necessary; as for forIn'_list.
theorem forIn_list.h14 : ¬ drop0% Std.WP.Spec.forIn_list 14 := fun H =>
  List.cons_ne_nil 0 [] ((H (m := Id) (xs := [0]) (init := 0) (f := fun _ b => pure (.yield b))
    (fun p _ _ => p = []) (eposts := ())).le_wp rfl)

-- `Std.WP.Spec.foldlM_list` idx 14: necessary; as for forIn'_list.
theorem foldlM_list.h14 : ¬ drop0% Std.WP.Spec.foldlM_list 14 := fun H =>
  List.cons_ne_nil 0 [] ((H (m := Id) (xs := [0]) (init := 0) (f := fun b _ => pure b)
    (fun p _ _ => p = []) (eposts := ())).le_wp rfl)

-- `Std.WP.Spec.forIn'_list_const_inv` idx 14: necessary; in `Id` over `[0]` the body yields `1`, the invariant is `b = 0`.
theorem forIn'_list_const_inv.h14 : ¬ drop0% Std.WP.Spec.forIn'_list_const_inv 14 := fun H =>
  Nat.succ_ne_zero 0 ((H (m := Id) (xs := [0]) (init := 0) (f := fun _ _ _ => pure (.yield 1))
    (inv := fun b => b = 0) (eposts := ())).le_wp rfl)

-- `Std.WP.Spec.forIn_list_const_inv` idx 14: necessary; as for forIn'_list_const_inv.
theorem forIn_list_const_inv.h14 : ¬ drop0% Std.WP.Spec.forIn_list_const_inv 14 := fun H =>
  Nat.succ_ne_zero 0 ((H (m := Id) (xs := [0]) (init := 0) (f := fun _ _ => pure (.yield 1))
    (inv := fun b => b = 0) (eposts := ())).le_wp rfl)

-- `Std.WP.Spec.foldlM_list_const_inv` idx 14: necessary; as for forIn'_list_const_inv.
theorem foldlM_list_const_inv.h14 : ¬ drop0% Std.WP.Spec.foldlM_list_const_inv 14 := fun H =>
  Nat.succ_ne_zero 0 ((H (m := Id) (xs := [0]) (init := 0) (f := fun _ _ => pure 1)
    (inv := fun b => b = 0) (eposts := ())).le_wp rfl)

-- `Std.WP.Spec.forIn'_pure` idx 20: necessary; lists, `[0]`, invariant `pref = []`: the conclusion says `ForIn.toList [0] = []`.
theorem forIn'_pure.h20 : ¬ drop0% Std.WP.Spec.forIn'_pure 20 := fun H => by
  have h : ForIn.toList ([0] : List Nat) = [] := (H (m := Id) (ρ := List Nat) (xs := [0]) (init := 0)
    (f := fun _ _ b => pure (.yield b)) (fun p _ _ => p = []) (eposts := ())).le_wp rfl
  simp at h

-- `Std.WP.Spec.forIn_pure` idx 18: necessary; as for forIn'_pure.
theorem forIn_pure.h18 : ¬ drop0% Std.WP.Spec.forIn_pure 18 := fun H => by
  have h : ForIn.toList ([0] : List Nat) = [] := (H (m := Id) (ρ := List Nat) (xs := [0]) (init := 0)
    (f := fun _ b => pure (.yield b)) (fun p _ _ => p = []) (eposts := ())).le_wp rfl
  simp at h

-- `Std.WP.Spec.foldM_iter` idx 19: necessary; the list iterator over `[0]`, invariant `pref = []`.
theorem foldM_iter.h19 : ¬ drop0% Std.WP.Spec.foldM_iter 19 := fun H => by
  have h : ([0].iter).toList = [] := (H (m := Id) (it := [0].iter) (init := 0)
    (f := fun b _ => pure b) (fun p _ _ => p = []) (eposts := ())).le_wp rfl
  simp at h

-- `Std.WP.Spec.foldM_iterM_id` idx 19: necessary; the list iterator over `[0]` in `Id`, invariant `pref = []`.
theorem foldM_iterM_id.h19 : ¬ drop0% Std.WP.Spec.foldM_iterM_id 19 := fun H => by
  have h : ([0].iterM Id).toList.run = [] := (H (m := Id) (it := [0].iterM Id) (init := 0)
    (f := fun b _ => pure b) (fun p _ _ => p = []) (eposts := ())).le_wp rfl
  simp at h
  exact List.cons_ne_nil 0 [] h

-- `Std.WP.Spec.foldlM_array` idx 14: necessary; `#[0]`, invariant `pref = []`.
theorem foldlM_array.h14 : ¬ drop0% Std.WP.Spec.foldlM_array 14 := fun H => by
  have h : (#[0] : Array Nat).toList = [] := (H (m := Id) (xs := #[0]) (init := 0)
    (f := fun b _ => pure b) (fun p _ _ => p = []) (eposts := ())).le_wp rfl
  simp at h

-- `Std.WP.Spec.forIn_string` idx 13: necessary; the string "a" with the invariant `pos = startPos`.
theorem forIn_string.h13 : ¬ drop0% Std.WP.Spec.forIn_string 13 := fun H => by
  have h : "a".endPos = "a".startPos := (H (m := Id) (s := "a") (init := 0)
    (f := fun _ b => pure (.yield b)) (fun p _ => p = "a".startPos) (eposts := ())).le_wp rfl
  revert h; decide

-- `Std.WP.Spec.forIn_stringSlice` idx 13: necessary; the slice of "a" with the invariant `pos = startPos`.
theorem forIn_stringSlice.h13 : ¬ drop0% Std.WP.Spec.forIn_stringSlice 13 := fun H => by
  have h : "a".toSlice.endPos = "a".toSlice.startPos := (H (m := Id) (s := "a".toSlice) (init := 0)
    (f := fun _ b => pure (.yield b)) (fun p _ => p = "a".toSlice.startPos) (eposts := ())).le_wp rfl
  revert h; decide

/-! ### Container classes -/

-- `Std.WP.Spec.forIn'_pure` idx 13 (dependent): necessary; lists with an empty membership relation are not `LawfulMemForInId`.
theorem forIn'_pure.h13 : ¬ indep0% Std.WP.Spec.forIn'_pure 13 := fun H => by
  letI d : Membership Nat (List Nat) := ⟨fun _ _ => False⟩
  letI : ForIn' Option (List Nat) Nat d := ⟨fun _ init _ => pure init⟩
  have := H (m := Option) (ρ := List Nat) (d := d) (xs := [0]) (init := 0)
    (f := fun _ _ b => pure (.yield b)) (inv := fun _ _ _ => True) (eposts := fun _ => False)
  exact (this.mem_toList_iff (a := 0) (xs := [0])).mp (by simp)

/-- A list whose `forIn` (in `Option`) returns `init` at once, and whose `Id` loop is the list's. -/
structure R1 where l : List Nat
instance : ForIn Id R1 Nat := ⟨fun r init f => forIn r.l init f⟩
instance : ForIn Option R1 Nat := ⟨fun _ init _ => pure init⟩
theorem R1.toList (r : R1) : ForIn.toList r = r.l := ForIn.toList_eq_of_forIn_eq (fun _ _ => rfl)

-- `Std.WP.Spec.forIn_pure` idx 12: necessary; R1 over `[0]` in `Option`: the loop returns `0`, the invariant `b = pref.length` asks for `1`.
theorem forIn_pure.h12 : ¬ drop0% Std.WP.Spec.forIn_pure 12 := fun H => by
  have h : (0 : Nat) = (ForIn.toList (R1.mk [0])).length := (H (m := Option) (ρ := R1) (xs := ⟨[0]⟩) (init := 0)
    (f := fun _ b => some (.yield (b + 1))) (fun p _ b => b = p.length) (eposts := fun _ => False)
    (fun pref cur suff _ b => ⟨fun hb => by subst hb; show pref.length + 1 = (pref ++ [cur]).length; simp⟩)).le_wp rfl
  simp [R1.toList] at h

/-- A list with the list's membership and `Id` loop, whose `forIn'` (in `Option`) returns `init`. -/
structure R2 where l : List Nat
instance : Membership Nat R2 := ⟨fun r a => a ∈ r.l⟩
instance : ForIn Id R2 Nat := ⟨fun r init f => forIn r.l init f⟩
theorem R2.toList (r : R2) : ForIn.toList r = r.l := ForIn.toList_eq_of_forIn_eq (fun _ _ => rfl)
instance : LawfulMemForInId R2 Nat := ⟨fun {_ xs} => by rw [R2.toList]; rfl⟩
instance : ForIn' Option R2 Nat inferInstance := ⟨fun _ init _ => pure init⟩

-- `Std.WP.Spec.forIn'_pure` idx 14: necessary; R2 over `[0]` in `Option`: the loop returns `0`, the invariant `b = pref.length` asks for `1`.
theorem forIn'_pure.h14 : ¬ drop0% Std.WP.Spec.forIn'_pure 14 := fun H => by
  have h : (0 : Nat) = (ForIn.toList (R2.mk [0])).length := (H (m := Option) (ρ := R2) (xs := ⟨[0]⟩) (init := 0)
    (f := fun _ _ b => some (.yield (b + 1))) (fun p _ b => b = p.length) (eposts := fun _ => False)
    (fun pref cur suff _ b => ⟨fun hb => by subst hb; show pref.length + 1 = (pref ++ [cur]).length; simp⟩)).le_wp rfl
  simp [R2.toList] at h

/-! ### `foldM_iter`, `foldM_iterM_id`: the base loop -/

/-- A loop over the non-finite AD iterator that returns `init` (vacuously lawful). -/
@[instance_reducible] def ADLoopI {n : Type → Type} [Pure n] : IteratorLoop OpD1Hand.AD Id n where
  forIn _ _ _ _ init _ := pure init

theorem ADLoopI.lawful {n : Type → Type} [Monad n] :
    @LawfulIteratorLoop _ OpD1Hand.AD Id n _ _ _ (ADLoopI (n := n)) :=
  @LawfulIteratorLoop.mk _ OpD1Hand.AD Id n _ _ _ (ADLoopI (n := n))
    (fun _ _ _ _ init Pl wf _ => absurd wf (@OpD1Hand.AD.not_wf _ ⟨init⟩ Pl))

theorem stepLen (pref : List Nat) (cur : Nat) (b : Nat) :
    Std.WP.Triple (pure (b + 1) : Id Nat) (b = pref.length) (fun b' => b' = (pref ++ [cur]).length) () :=
  ⟨fun hb => by subst hb; show pref.length + 1 = (pref ++ [cur]).length; simp⟩

-- `Std.WP.Spec.foldM_iter` idx 13: necessary; BL 0 over `[1, 2]` (its loop returns `init`), body `b + 1`, invariant `b = pref.length`: `0 = 2`.
theorem foldM_iter.h13 : ¬ drop0% Std.WP.Spec.foldM_iter 13 := fun H => by
  have h : (ItLoopHand.bl 0 [1, 2]).foldM (fun b _ => (pure (b + 1) : Id Nat)) 0 = (ItLoopHand.bl 0 [1, 2]).toList.length :=
    (H (m := Id) (it := ItLoopHand.bl 0 [1, 2]) (init := 0) (f := fun b _ => pure (b + 1)) (fun p _ b => b = p.length)
      (eposts := ()) (fun pref cur _ _ b => stepLen pref cur b)).le_wp rfl
  rw [ItLoopHand.toList_bl] at h
  revert h; decide

-- `Std.WP.Spec.foldM_iterM_id` idx 13: necessary; as for foldM_iter with the monadic BL 0 iterator.
theorem foldM_iterM_id.h13 : ¬ drop0% Std.WP.Spec.foldM_iterM_id 13 := fun H => by
  have h : (ItLoopHand.blM 0 [1, 2] Id).foldM (fun b _ => (pure (b + 1) : Id Nat)) 0 = (ItLoopHand.blM 0 [1, 2] Id).toList.run.length :=
    (H (m := Id) (it := ItLoopHand.blM 0 [1, 2] Id) (init := 0) (f := fun b _ => pure (b + 1)) (fun p _ b => b = p.length)
      (eposts := ()) (fun pref cur _ _ b => stepLen pref cur b)).le_wp rfl
  simp only [← ItLoopHand.toIterM_bl, ← Iter.toList_eq_toList_toIterM, ItLoopHand.toList_bl] at h
  revert h; decide

-- `Std.WP.Spec.foldM_iter` idx 11: necessary; the non-finite AD iterator with two vacuously lawful loops (run the body once / return `init`): the length of its `toList` would be both `1` and `0`.
theorem foldM_iter.h11 : ¬ drop0% Std.WP.Spec.foldM_iter 11 := fun H =>
  WPSpecHand.two (L := OpD1Hand.AD.it.toList.length) (a := 1) (b := 0) (by decide)
    (by letI := OpD1Hand.ADLoop 0 (n := Id); haveI := OpD1Hand.ADLoop.lawful 0 (n := Id)
        exact (show _ = _ from (H (m := Id) (it := OpD1Hand.AD.it) (init := 0) (f := fun b _ => pure (b + 1))
          (fun p _ b => b = p.length) (eposts := ()) (fun pref cur _ _ b => stepLen pref cur b)).le_wp rfl).symm)
    (by letI := ADLoopI (n := Id); haveI := ADLoopI.lawful (n := Id)
        exact (show _ = _ from (H (m := Id) (it := OpD1Hand.AD.it) (init := 0) (f := fun b _ => pure (b + 1))
          (fun p _ b => b = p.length) (eposts := ()) (fun pref cur _ _ b => stepLen pref cur b)).le_wp rfl).symm)

-- `Std.WP.Spec.foldM_iterM_id` idx 11: necessary; as for foldM_iter with the monadic AD iterator.
theorem foldM_iterM_id.h11 : ¬ drop0% Std.WP.Spec.foldM_iterM_id 11 := fun H =>
  WPSpecHand.two (L := OpD1Hand.AD.it.toIterM.toList.run.length) (a := 1) (b := 0) (by decide)
    (by letI := OpD1Hand.ADLoop 0 (n := Id); haveI := OpD1Hand.ADLoop.lawful 0 (n := Id)
        exact (show _ = _ from (H (m := Id) (it := OpD1Hand.AD.it.toIterM) (init := 0) (f := fun b _ => pure (b + 1))
          (fun p _ b => b = p.length) (eposts := ()) (fun pref cur _ _ b => stepLen pref cur b)).le_wp rfl).symm)
    (by letI := ADLoopI (n := Id); haveI := ADLoopI.lawful (n := Id)
        exact (show _ = _ from (H (m := Id) (it := OpD1Hand.AD.it.toIterM) (init := 0) (f := fun b _ => pure (b + 1))
          (fun p _ b => b = p.length) (eposts := ()) (fun pref cur _ _ b => stepLen pref cur b)).le_wp rfl).symm)

/-! ### Variants, `repeatM`, `forIn` over `Lean.Loop` -/

/-- The diamond lattice `M₃` (not distributive: `meet z` does not preserve `x ⊔ y = ⊤`). -/
inductive M3 | bot | x | y | z | top
  deriving DecidableEq

namespace M3

def le : M3 → M3 → Bool
  | bot, _ => true
  | _, top => true
  | x, x => true
  | y, y => true
  | z, z => true
  | _, _ => false

instance : PartialOrder M3 where
  rel a b := le a b = true
  rel_refl {a} := by cases a <;> rfl
  rel_trans {a b c} := by cases a <;> cases b <;> cases c <;> decide
  rel_antisymm {a b} := by cases a <;> cases b <;> decide

def ub (c : M3 → Prop) (t : M3) : Prop := ∀ w, c w → le w t = true

theorem ub_iff (c : M3 → Prop) (t : M3) : ub c t ↔ (c bot → le bot t = true) ∧ (c x → le x t = true) ∧
    (c y → le y t = true) ∧ (c z → le z t = true) ∧ (c top → le top t = true) :=
  ⟨fun h => ⟨h _, h _, h _, h _, h _⟩, fun ⟨a, b, c', d, e⟩ w hw => by cases w <;> simp_all⟩

open Classical in
noncomputable def sup (c : M3 → Prop) : M3 :=
  if ub c bot then bot else if ub c x then x else if ub c y then y else if ub c z then z else top

theorem sup_is (c : M3 → Prop) (t : M3) : le (sup c) t = true ↔ ub c t := by
  unfold sup
  by_cases hx : c x <;> by_cases hy : c y <;> by_cases hz : c z <;> by_cases ht : c top <;>
    cases t <;> simp [ub_iff, le, *]

noncomputable instance : CompleteLattice M3 where
  has_sup c := ⟨sup c, fun t => sup_is c t⟩

theorem below_xz (w : M3) (h1 : w ⊑ x) (h2 : w ⊑ z) : w ⊑ bot := by
  have h1 : le w x = true := h1; have h2 : le w z = true := h2
  show le w bot = true; cases w <;> simp_all [le]

theorem below_yz (w : M3) (h1 : w ⊑ y) (h2 : w ⊑ z) : w ⊑ bot := by
  have h1 : le w y = true := h1; have h2 : le w z = true := h2
  show le w bot = true; cases w <;> simp_all [le]

theorem above_xy (w : M3) (h1 : x ⊑ w) (h2 : y ⊑ w) : top ⊑ w := by
  have h1 : le x w = true := h1; have h2 : le y w = true := h2
  show le top w = true; cases w <;> simp_all [le]

theorem le_topM (w : M3) : w ⊑ top := by cases w <;> rfl

/-- `x` or `y`, by a Boolean. -/
def ev (b : Bool) : M3 := if b then x else y

theorem ev_meet_z (b : Bool) : ev b ⊓ z ⊑ bot := by
  cases b
  · exact below_yz _ (meet_le_left _ _) (meet_le_right _ _)
  · exact below_xz _ (meet_le_left _ _) (meet_le_right _ _)

/-- The variant whose measure is `x` or `y`: their join is `⊤`. -/
def V (α : Type) : WP.Variant α M3 where
  γ := Bool
  wfRel := ⟨fun _ _ => False, ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩⟩
  EvalsTo _ b := ev b
  total _ := PartialOrder.rel_antisymm (le_top _)
    (PartialOrder.rel_trans (le_topM _) (above_xy _ (le_iSup ev true) (le_iSup ev false)))

/-- `Id` with `M3` assertions: `wp x post = post x`. -/
@[instance_reducible] def idWP : WP.WPMonad Id M3 Unit where
  toWP _ := { trans x := ⟨fun post _ => post x.run⟩, trans_monotone x := fun _ _ _ _ _ hpost => hpost x }
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind _ _ _ _ := PartialOrder.rel_refl

end M3

-- `Std.WP.Variant.le_of_total_le` idx 7: necessary; in the diamond lattice M3 the measure is `x` or `y` (join `⊤`), `P = z` meets both to `⊥`, but `z ⋢ ⊥`.
theorem le_of_total_le.h7 : ¬ drop0% Std.WP.Variant.le_of_total_le 7 := fun H =>
  Bool.false_ne_true (H (Pred := M3) (v := M3.V Unit) (a := ()) (P := .z) (Q := .bot)
    (iSup_le _ _ fun n => M3.ev_meet_z n))

-- `Std.WP.Variant.le_of_total_le` idx 8: necessary; in `Prop`, `True ⊑ False` fails.
theorem le_of_total_le.h8 : ¬ drop0% Std.WP.Variant.le_of_total_le 8 := fun H =>
  H (Pred := Prop) (v := WP.Variant.ofMeasure (Pred := Prop) (fun _ : Unit => (0 : Nat))) (a := ())
    (P := True) (Q := False) trivial

-- `Std.WP.Spec.repeatM` idx 13: necessary; `Id` with M3 assertions (meets do not preserve joins), measure `x`/`y`, invariant `z` before and `⊥` after: every step holds, `z ⊑ ⊥` does not.
theorem repeatM.h13 : ¬ drop0% Std.WP.Spec.repeatM 13 := fun H => by
  letI := M3.idWP
  letI : ∀ α, WP.WP (Id α) α M3 Unit := fun α => M3.idWP.toWP α
  exact Bool.false_ne_true (H (m := Id) (α := Unit) (β := Unit) (init := ()) (f := fun _ => pure (.inr ()))
    (M3.V Unit) (fun s => match s with | .inl _ => M3.z | .inr _ => M3.bot) ()
    (fun _ ma => ⟨M3.ev_meet_z ma⟩)).le_wp

-- `Std.WP.Spec.forIn_loop` idx 12: necessary; as for repeatM idx 13, with a body that is done at once.
theorem forIn_loop.h12 : ¬ drop0% Std.WP.Spec.forIn_loop 12 := fun H => by
  letI := M3.idWP
  letI : ∀ α, WP.WP (Id α) α M3 Unit := fun α => M3.idWP.toWP α
  exact Bool.false_ne_true (H (m := Id) (β := Unit) (l := ⟨⟩) (init := ()) (f := fun _ _ => pure (.done ()))
    (M3.V Unit) (fun e _ => if e then M3.bot else M3.z) ()
    (fun _ mb => ⟨M3.ev_meet_z mb⟩)).le_wp

-- `Std.WP.Spec.repeatM` idx 17: necessary; in `Id` with `Prop` assertions, invariant `True` before and `False` after.
theorem repeatM.h17 : ¬ drop0% Std.WP.Spec.repeatM 17 := fun H =>
  (H (m := Id) (α := Unit) (β := Unit) (init := ()) (f := fun _ => pure (.inr ()))
    (WP.Variant.ofMeasure (Pred := Prop) (fun _ : Unit => (0 : Nat)))
    (fun s => match s with | .inl _ => True | .inr _ => False) ()).le_wp trivial

-- `Std.WP.Spec.forIn_loop` idx 16: necessary; as for repeatM idx 17.
theorem forIn_loop.h16 : ¬ drop0% Std.WP.Spec.forIn_loop 16 := fun H =>
  (H (m := Id) (β := Unit) (l := ⟨⟩) (init := ()) (f := fun _ _ => pure (.done ()))
    (WP.Variant.ofMeasure (Pred := Prop) (fun _ : Unit => (0 : Nat)))
    (fun e _ => if e then False else True) ()).le_wp trivial

-- `Std.WP.Spec.repeatM` idx 12 (dependent): necessary; `β = Empty` satisfies all independent binders (the step holds for the invariant `False`), but `Nonempty Empty` fails.
theorem repeatM.h12 : ¬ indep0% Std.WP.Spec.repeatM 12 := fun H =>
  (H (m := Id) (α := Unit) (β := Empty) (init := ()) (f := fun _ => pure (.inl ()))
    (WP.Variant.ofMeasure (Pred := Prop) (fun _ : Unit => (0 : Nat))) (fun _ => False) ()
    (fun _ _ => ⟨PartialOrder.rel_trans (meet_le_right _ _) (fun h => h.elim)⟩)).elim nofun

end WPSpecHand.Manual
