import Lean

/-!
Hand pass `ItLoop` (hand8): the 177 non-dependent `[LawfulIteratorLoop α m n]` hypotheses of the
`Init.Data.Iterators` lemmas (consumers in `Lemmas/Consumers/Loop` and `Lemmas/Consumers/Monadic/Loop`,
combinators in `Lemmas/Combinators/{FilterMap,Attach,ULift}` and their monadic versions). For
hypothesis `hᵢ` of theorem `T` this file proves `¬T'` (necessary) or `T'` (removable).

175 necessary, 2 removable, 0 independent, 0 opaque, 0 left unresolved.

Removable (2): `IterM.findSomeM?_pure` and `IterM.findM?_pure`: both sides use the same loop
instance and are equal by definition (`findSome? f` is `findSomeM? (pure <| f ·)`, `find? g` is
`findM? (pure <| ULift.up <| g ·)`), so `rfl` proves `T'`.

Necessary (175): the counterexample is `BL k β`, a copy of the list iterator (`Iterator`, `Finite`,
`LawfulDeterministicIterator` as for `ListIterator`) whose `IteratorLoop` instance is chosen by the
tag `k`:
* `0`: `brkI`, `forIn` returns `init` without iterating, in every monad;
* `1`: `brkF`, `forIn` fails (`none`) in `Option`; the default (lawful) implementation elsewhere;
* `4` / `5`: `brkI` in `Id.{1}` resp. `Id.{0}`, the default elsewhere (for the theorems with two
  loop instances that differ only in the universe of `Id`; the universes are set apart);
* `2` / `3`: a classical, non-parametric instance: a loop whose state type is `Bool` resp.
  `ULift Bool` returns `true` resp. `up true`, any other loop returns `init`. Needed when both
  sides of the lemma run the same loop instance and are related by a bijection of the state
  (`allM = not ∘ anyM (not ∘ p)`, `fold_hom`, `forIn = value <$> foldM`), where every parametric
  broken instance satisfies the lemma.
Each refutation instantiates `T'` at a tagged `BL` over the list `[1, 2]` (or `[]` for the
`*_eq_match_step`/`*_eq` lemmas evaluated in `Option`), `Nat` values and `Id`/`Option`, then
evaluates (`ev`): the side running a lawful loop (a combinator's default instance, or the default
instance for the other monad) is rewritten to `List` functions by the library's `*_toList` lemmas and
the `toList` of `BL`; the broken side reduces by `decide`. With `brkI` the values differ (`0` vs. `3`,
`false` vs. `true`, `[]` vs. `[1, 2]`, ...), with `brkF` it is `none` vs. `some _`.

`drop% T i` elaborates to `T'` (universe parameters kept, for the removable verdicts), `dropu% [l, …]
T i` to `T'` at the given universe levels, and `drop0% T i` to `T'` with all universes `0`.

Run with the lean4 repo's stage1 binary: `lean checks/ItLoopHand.lean`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

open Lean Meta Elab Term in
def HandDrop.dropType (T : Ident) (i : Nat) (us? : Option (List Level)) : TermElabM Expr := do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← match us? with
    | some us => pure us
    | none => ci.levelParams.mapM fun _ => mkFreshLevelMVar
  unless us.length == ci.levelParams.length do
    throwError "{n} has {ci.levelParams.length} universe parameters"
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i]!
    unless ← isProp (← inferType x) do throwError "binder {i} of {n} is not a Prop"
    for j in [i+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i) body
open Lean Elab Term in
elab "drop0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  HandDrop.dropType T i.getNat (some (ci.levelParams.map fun _ => Lean.Level.zero))
open Lean Elab Term in
elab "dropu% " "[" ls:num,* "]" T:ident i:num : term =>
  HandDrop.dropType T i.getNat (some (ls.getElems.map fun l => Lean.Level.ofNat l.getNat).toList)
elab "drop% " T:ident i:num : term => HandDrop.dropType T i.getNat none

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
  simp [Iter.step, IterM.step, Iterator.step, bl, blM, BL.instIterator]
variable {k : Nat} in
@[simp] theorem step_bl_cons {x : β} {xs : List β} : (bl k (x :: xs)).step = ⟨.yield (bl k xs) x, rfl⟩ := by
  simp [Iter.step, IterM.step, Iterator.step, bl, blM, BL.instIterator, IterM.toIter]
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

-- `Std.Iter.length_attachWith`, idx 8: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.length_attachWith.h8 : ¬ drop0% Std.Iter.length_attachWith 8 := fun h => by
  have := h (α := BL 0 Nat) (P := fun _ => True) (it := bl 0 [1, 2]) (hP := fun _ _ => trivial)
  clear h; revert this; ev

-- `Std.Iter.forIn_filterMapWithPostcondition`, idx 15: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn_filterMapWithPostcondition.h15 : ¬ drop0% Std.Iter.forIn_filterMapWithPostcondition 15 := fun h => by
  have := h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn_filterMapM`, idx 17: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn_filterMapM.h17 : ¬ drop0% Std.Iter.forIn_filterMapM 17 := fun h => by
  have := h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn_filterMap`, idx 10: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn_filterMap.h10 : ¬ drop0% Std.Iter.forIn_filterMap 10 := fun h => by
  have := h (α := BL 1 Nat) (n := Option) (it := bl 1 [1, 2]) (f := fun x => some x) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn_mapWithPostcondition`, idx 15: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn_mapWithPostcondition.h15 : ¬ drop0% Std.Iter.forIn_mapWithPostcondition 15 := fun h => by
  have := h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn_mapM`, idx 17: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn_mapM.h17 : ¬ drop0% Std.Iter.forIn_mapM 17 := fun h => by
  have := h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn_map`, idx 10: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn_map.h10 : ¬ drop0% Std.Iter.forIn_map 10 := fun h => by
  have := h (α := BL 1 Nat) (n := Option) (it := bl 1 [1, 2]) (f := fun x => x + 1) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn_filterWithPostcondition`, idx 14: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn_filterWithPostcondition.h14 : ¬ drop0% Std.Iter.forIn_filterWithPostcondition 14 := fun h => by
  have := h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn_filterM`, idx 16: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn_filterM.h16 : ¬ drop0% Std.Iter.forIn_filterM 16 := fun h => by
  have := h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn_filter`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn_filter.h9 : ¬ drop0% Std.Iter.forIn_filter 9 := fun h => by
  have := h (α := BL 1 Nat) (n := Option) (it := bl 1 [1, 2]) (f := fun _ => true) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.foldM_filterMapWithPostcondition`, idx 15: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.foldM_filterMapWithPostcondition.h15 : ¬ drop0% Std.Iter.foldM_filterMapWithPostcondition 15 := fun h => by
  have := h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.foldM_filterMapM`, idx 17: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.foldM_filterMapM.h17 : ¬ drop0% Std.Iter.foldM_filterMapM 17 := fun h => by
  have := h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.foldM_mapWithPostcondition`, idx 18: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.foldM_mapWithPostcondition.h18 : ¬ drop0% Std.Iter.foldM_mapWithPostcondition 18 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.foldM_mapM`, idx 17: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.foldM_mapM.h17 : ¬ drop0% Std.Iter.foldM_mapM 17 := fun h => by
  have := h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.foldM_filterWithPostcondition`, idx 14: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.foldM_filterWithPostcondition.h14 : ¬ drop0% Std.Iter.foldM_filterWithPostcondition 14 := fun h => by
  have := h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.foldM_filterM`, idx 16: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.foldM_filterM.h16 : ¬ drop0% Std.Iter.foldM_filterM 16 := fun h => by
  have := h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.foldM_filterMap`, idx 10: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.foldM_filterMap.h10 : ¬ drop0% Std.Iter.foldM_filterMap 10 := fun h => by
  have := h (α := BL 1 Nat) (n := Option) (f := fun x => some x) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.foldM_map`, idx 10: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.foldM_map.h10 : ¬ drop0% Std.Iter.foldM_map 10 := fun h => by
  have := h (α := BL 1 Nat) (n := Option) (f := fun x => x + 1) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.foldM_filter`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.foldM_filter.h9 : ¬ drop0% Std.Iter.foldM_filter 9 := fun h => by
  have := h (α := BL 1 Nat) (n := Option) (f := fun _ => true) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.fold_filterMapWithPostcondition`, idx 10: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.fold_filterMapWithPostcondition.h10 : ¬ drop0% Std.Iter.fold_filterMapWithPostcondition 10 := fun h => by
  have := h (α := BL 1 Nat) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.fold_filterMapM`, idx 12: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.fold_filterMapM.h12 : ¬ drop0% Std.Iter.fold_filterMapM 12 := fun h => by
  have := h (α := BL 1 Nat) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.fold_mapWithPostcondition`, idx 10: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.fold_mapWithPostcondition.h10 : ¬ drop0% Std.Iter.fold_mapWithPostcondition 10 := fun h => by
  have := h (α := BL 1 Nat) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.fold_mapM`, idx 12: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.fold_mapM.h12 : ¬ drop0% Std.Iter.fold_mapM 12 := fun h => by
  have := h (α := BL 1 Nat) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.fold_filterWithPostcondition`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.fold_filterWithPostcondition.h9 : ¬ drop0% Std.Iter.fold_filterWithPostcondition 9 := fun h => by
  have := h (α := BL 1 Nat) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.fold_filterM`, idx 11: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.fold_filterM.h11 : ¬ drop0% Std.Iter.fold_filterM 11 := fun h => by
  have := h (α := BL 1 Nat) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.fold_filterMap`, idx 7: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.fold_filterMap.h7 : ¬ drop0% Std.Iter.fold_filterMap 7 := fun h => by
  have := h (α := BL 0 Nat) (f := fun x => some x) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.fold_map`, idx 7: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.fold_map.h7 : ¬ drop0% Std.Iter.fold_map 7 := fun h => by
  have := h (α := BL 0 Nat) (f := fun x => x + 1) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.fold_filter`, idx 6: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.fold_filter.h6 : ¬ drop0% Std.Iter.fold_filter 6 := fun h => by
  have := h (α := BL 0 Nat) (f := fun _ => true) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.length_map`, idx 6: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.length_map.h6 : ¬ drop0% Std.Iter.length_map 6 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (f := fun x => x + 1)
  clear h; revert this; ev

-- `Std.Iter.anyM_filterMap`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.anyM_filterMap.h9 : ¬ drop0% Std.Iter.anyM_filterMap 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (f := fun x => some x) (p := fun _ => pure true)
  clear h; revert this; ev

-- `Std.Iter.anyM_map`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.anyM_map.h9 : ¬ drop0% Std.Iter.anyM_map 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (f := fun x => x + 1) (p := fun _ => pure true)
  clear h; revert this; ev

-- `Std.Iter.anyM_filter`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.anyM_filter.h8 : ¬ drop0% Std.Iter.anyM_filter 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (f := fun _ => true) (p := fun _ => pure true)
  clear h; revert this; ev

-- `Std.Iter.any_filterMap`, idx 6: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.any_filterMap.h6 : ¬ drop0% Std.Iter.any_filterMap 6 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (f := fun x => some x) (p := fun _ => true)
  clear h; revert this; ev

-- `Std.Iter.any_map`, idx 6: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.any_map.h6 : ¬ drop0% Std.Iter.any_map 6 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (f := fun x => x + 1) (p := fun _ => true)
  clear h; revert this; ev

-- `Std.Iter.allM_filterMap`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.allM_filterMap.h9 : ¬ drop0% Std.Iter.allM_filterMap 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (f := fun x => some x) (p := fun _ => pure false)
  clear h; revert this; ev

-- `Std.Iter.allM_map`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.allM_map.h9 : ¬ drop0% Std.Iter.allM_map 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (f := fun x => x + 1) (p := fun _ => pure false)
  clear h; revert this; ev

-- `Std.Iter.allM_filter`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.allM_filter.h8 : ¬ drop0% Std.Iter.allM_filter 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (f := fun _ => true) (p := fun _ => pure false)
  clear h; revert this; ev

-- `Std.Iter.all_filterMap`, idx 6: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.all_filterMap.h6 : ¬ drop0% Std.Iter.all_filterMap 6 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (f := fun x => some x) (p := fun _ => false)
  clear h; revert this; ev

-- `Std.Iter.all_map`, idx 6: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.all_map.h6 : ¬ drop0% Std.Iter.all_map 6 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (f := fun x => x + 1) (p := fun _ => false)
  clear h; revert this; ev

-- `Std.IterM.forIn_filterMapWithPostcondition`, idx 20: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.forIn_filterMapWithPostcondition.h20 : ¬ drop0% Std.IterM.forIn_filterMapWithPostcondition 20 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (it := blM 1 [1, 2] Id) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.IterM.forIn_filterMapM`, idx 22: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.forIn_filterMapM.h22 : ¬ drop0% Std.IterM.forIn_filterMapM 22 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (it := blM 1 [1, 2] Id) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.IterM.forIn_filterMap`, idx 15: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.forIn_filterMap.h15 : ¬ drop0% Std.IterM.forIn_filterMap 15 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (it := blM 1 [1, 2] Id) (f := fun x => some x) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.IterM.forIn_mapWithPostcondition`, idx 20: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.forIn_mapWithPostcondition.h20 : ¬ drop0% Std.IterM.forIn_mapWithPostcondition 20 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (it := blM 1 [1, 2] Id) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.IterM.forIn_mapM`, idx 22: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.forIn_mapM.h22 : ¬ drop0% Std.IterM.forIn_mapM 22 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (it := blM 1 [1, 2] Id) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.IterM.forIn_map`, idx 15: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.forIn_map.h15 : ¬ drop0% Std.IterM.forIn_map 15 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (it := blM 1 [1, 2] Id) (f := fun x => x + 1) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.IterM.forIn_filterWithPostcondition`, idx 19: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.forIn_filterWithPostcondition.h19 : ¬ drop0% Std.IterM.forIn_filterWithPostcondition 19 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (it := blM 1 [1, 2] Id) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.IterM.forIn_filterM`, idx 21: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.forIn_filterM.h21 : ¬ drop0% Std.IterM.forIn_filterM 21 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (it := blM 1 [1, 2] Id) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.IterM.forIn_filter`, idx 14: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.forIn_filter.h14 : ¬ drop0% Std.IterM.forIn_filter 14 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (it := blM 1 [1, 2] Id) (f := fun _ => true) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.IterM.foldM_filterMapWithPostcondition`, idx 18: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldM_filterMapWithPostcondition.h18 : ¬ drop0% Std.IterM.foldM_filterMapWithPostcondition 18 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.foldM_filterMapM`, idx 20: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldM_filterMapM.h20 : ¬ drop0% Std.IterM.foldM_filterMapM 20 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.foldM_mapWithPostcondition`, idx 18: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldM_mapWithPostcondition.h18 : ¬ drop0% Std.IterM.foldM_mapWithPostcondition 18 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.foldM_mapM`, idx 20: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldM_mapM.h20 : ¬ drop0% Std.IterM.foldM_mapM 20 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.foldM_filterWithPostcondition`, idx 17: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldM_filterWithPostcondition.h17 : ¬ drop0% Std.IterM.foldM_filterWithPostcondition 17 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.foldM_filterM`, idx 19: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldM_filterM.h19 : ¬ drop0% Std.IterM.foldM_filterM 19 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.foldM_filterMap`, idx 13: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldM_filterMap.h13 : ¬ drop0% Std.IterM.foldM_filterMap 13 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => some x) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.foldM_map`, idx 13: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldM_map.h13 : ¬ drop0% Std.IterM.foldM_map 13 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => x + 1) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.foldM_filter`, idx 12: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldM_filter.h12 : ¬ drop0% Std.IterM.foldM_filter 12 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun _ => true) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.fold_filterMapWithPostcondition`, idx 13: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.fold_filterMapWithPostcondition.h13 : ¬ drop0% Std.IterM.fold_filterMapWithPostcondition 13 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.fold_filterMapM`, idx 15: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.fold_filterMapM.h15 : ¬ drop0% Std.IterM.fold_filterMapM 15 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.fold_mapWithPostcondition`, idx 13: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.fold_mapWithPostcondition.h13 : ¬ drop0% Std.IterM.fold_mapWithPostcondition 13 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.fold_mapM`, idx 15: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.fold_mapM.h15 : ¬ drop0% Std.IterM.fold_mapM 15 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.fold_filterWithPostcondition`, idx 12: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.fold_filterWithPostcondition.h12 : ¬ drop0% Std.IterM.fold_filterWithPostcondition 12 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.fold_filterM`, idx 14: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.fold_filterM.h14 : ¬ drop0% Std.IterM.fold_filterM 14 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.fold_filterMap`, idx 10: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.fold_filterMap.h10 : ¬ drop0% Std.IterM.fold_filterMap 10 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (f := fun x => some x) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 0 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.fold_map`, idx 10: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.fold_map.h10 : ¬ drop0% Std.IterM.fold_map 10 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (f := fun x => x + 1) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 0 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.fold_filter`, idx 9: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.fold_filter.h9 : ¬ drop0% Std.IterM.fold_filter 9 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (f := fun _ => true) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 0 [1, 2] Id)
  clear h; revert this; ev

-- `Std.IterM.length_map`, idx 9: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.length_map.h9 : ¬ drop0% Std.IterM.length_map 9 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := blM 0 [1, 2] Id) (f := fun x => x + 1)
  clear h; revert this; ev

-- `Std.IterM.anyM_filterMap`, idx 9: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.anyM_filterMap.h9 : ¬ drop0% Std.IterM.anyM_filterMap 9 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := blM 0 [1, 2] Id) (f := fun x => some x) (p := fun _ => pure (ULift.up true))
  clear h; revert this; ev

-- `Std.IterM.anyM_map`, idx 9: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.anyM_map.h9 : ¬ drop0% Std.IterM.anyM_map 9 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := blM 0 [1, 2] Id) (f := fun x => x + 1) (p := fun _ => pure (ULift.up true))
  clear h; revert this; ev

-- `Std.IterM.anyM_filter`, idx 8: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.anyM_filter.h8 : ¬ drop0% Std.IterM.anyM_filter 8 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := blM 0 [1, 2] Id) (f := fun _ => true) (p := fun _ => pure (ULift.up true))
  clear h; revert this; ev

-- `Std.IterM.any_filterMap`, idx 9: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.any_filterMap.h9 : ¬ drop0% Std.IterM.any_filterMap 9 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := blM 0 [1, 2] Id) (f := fun x => some x) (p := fun _ => true)
  clear h; revert this; ev

-- `Std.IterM.any_map`, idx 9: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.any_map.h9 : ¬ drop0% Std.IterM.any_map 9 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := blM 0 [1, 2] Id) (f := fun x => x + 1) (p := fun _ => true)
  clear h; revert this; ev

-- `Std.IterM.allM_filterMap`, idx 9: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.allM_filterMap.h9 : ¬ drop0% Std.IterM.allM_filterMap 9 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := blM 0 [1, 2] Id) (f := fun x => some x) (p := fun _ => pure (ULift.up false))
  clear h; revert this; ev

-- `Std.IterM.allM_map`, idx 9: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.allM_map.h9 : ¬ drop0% Std.IterM.allM_map 9 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := blM 0 [1, 2] Id) (f := fun x => x + 1) (p := fun _ => pure (ULift.up false))
  clear h; revert this; ev

-- `Std.IterM.allM_filter`, idx 8: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.allM_filter.h8 : ¬ drop0% Std.IterM.allM_filter 8 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := blM 0 [1, 2] Id) (f := fun _ => true) (p := fun _ => pure (ULift.up false))
  clear h; revert this; ev

-- `Std.IterM.all_filterMap`, idx 9: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.all_filterMap.h9 : ¬ drop0% Std.IterM.all_filterMap 9 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := blM 0 [1, 2] Id) (f := fun x => some x) (p := fun _ => false)
  clear h; revert this; ev

-- `Std.IterM.all_map`, idx 9: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.all_map.h9 : ¬ drop0% Std.IterM.all_map 9 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := blM 0 [1, 2] Id) (f := fun x => x + 1) (p := fun _ => false)
  clear h; revert this; ev

-- `Std.IterM.length_uLift`, idx 13: tag 0 (returns init without iterating) on [1, 2]
theorem IterM.length_uLift.h13 : ¬ drop0% Std.IterM.length_uLift 13 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (n := Id) (it := blM 0 [1, 2] Id)
  clear h; revert this; ev

-- `Std.Iter.length_uLift`, idx 6: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.length_uLift.h6 : ¬ drop0% Std.Iter.length_uLift 6 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.forIn'_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem Iter.forIn'_eq_match_step.h8 : ¬ drop0% Std.Iter.forIn'_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 ([] : List Nat)) (init := (0 : Nat)) (f := fun x _ acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem Iter.forIn_eq_match_step.h8 : ¬ drop0% Std.Iter.forIn_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 ([] : List Nat)) (init := (0 : Nat)) (f := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn'_toList`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn'_toList.h8 : ¬ drop0% Std.Iter.forIn'_toList 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (init := (0 : Nat)) (f := fun x _ acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn'_toArray`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn'_toArray.h8 : ¬ drop0% Std.Iter.forIn'_toArray 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (init := (0 : Nat)) (f := fun x _ acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn'_eq_forIn'_toList`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn'_eq_forIn'_toList.h8 : ¬ drop0% Std.Iter.forIn'_eq_forIn'_toList 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (init := (0 : Nat)) (f := fun x _ acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.forIn'_eq_forIn'_toArray`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.forIn'_eq_forIn'_toArray.h8 : ¬ drop0% Std.Iter.forIn'_eq_forIn'_toArray 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (init := (0 : Nat)) (f := fun x _ acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.Iter.foldM_eq_match_step`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on []
theorem Iter.foldM_eq_match_step.h9 : ¬ drop0% Std.Iter.foldM_eq_match_step 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (f := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 ([] : List Nat))
  clear h; revert this; ev

-- `Std.Iter.foldlM_toList`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.foldlM_toList.h9 : ¬ drop0% Std.Iter.foldlM_toList 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (f := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.foldlM_toArray`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.foldlM_toArray.h9 : ¬ drop0% Std.Iter.foldlM_toArray 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (f := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.fold_eq_match_step`, idx 6: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.fold_eq_match_step.h6 : ¬ drop0% Std.Iter.fold_eq_match_step 6 := fun h => by
  have := h (α := BL 0 Nat) (f := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.toList_eq_fold`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.toList_eq_fold.h5 : ¬ drop0% Std.Iter.toList_eq_fold 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.toArray_eq_fold`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.toArray_eq_fold.h5 : ¬ drop0% Std.Iter.toArray_eq_fold 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.foldl_toList`, idx 6: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.foldl_toList.h6 : ¬ drop0% Std.Iter.foldl_toList 6 := fun h => by
  have := h (α := BL 0 Nat) (f := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.foldl_toArray`, idx 6: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.foldl_toArray.h6 : ¬ drop0% Std.Iter.foldl_toArray 6 := fun h => by
  have := h (α := BL 0 Nat) (f := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.length_eq_match_step`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.length_eq_match_step.h5 : ¬ drop0% Std.Iter.length_eq_match_step 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.size_toArray_eq_length`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.size_toArray_eq_length.h5 : ¬ drop0% Std.Iter.size_toArray_eq_length 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.length_toList_eq_length`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.length_toList_eq_length.h5 : ¬ drop0% Std.Iter.length_toList_eq_length 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.length_toListRev_eq_length`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.length_toListRev_eq_length.h5 : ¬ drop0% Std.Iter.length_toListRev_eq_length 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.anyM_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem Iter.anyM_eq_match_step.h8 : ¬ drop0% Std.Iter.anyM_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 ([] : List Nat)) (p := fun _ => pure true)
  clear h; revert this; ev

-- `Std.Iter.anyM_toList`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.anyM_toList.h8 : ¬ drop0% Std.Iter.anyM_toList 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (p := fun _ => pure true)
  clear h; revert this; ev

-- `Std.Iter.anyM_toArray`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.anyM_toArray.h8 : ¬ drop0% Std.Iter.anyM_toArray 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (p := fun _ => pure true)
  clear h; revert this; ev

-- `Std.Iter.any_eq_match_step`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.any_eq_match_step.h5 : ¬ drop0% Std.Iter.any_eq_match_step 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (p := fun _ => true)
  clear h; revert this; ev

-- `Std.Iter.any_toList`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.any_toList.h5 : ¬ drop0% Std.Iter.any_toList 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (p := fun _ => true)
  clear h; revert this; ev

-- `Std.Iter.any_toArray`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.any_toArray.h5 : ¬ drop0% Std.Iter.any_toArray 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (p := fun _ => true)
  clear h; revert this; ev

-- `Std.Iter.allM_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem Iter.allM_eq_match_step.h8 : ¬ drop0% Std.Iter.allM_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 ([] : List Nat)) (p := fun _ => pure false)
  clear h; revert this; ev

-- `Std.Iter.all_eq_match_step`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.all_eq_match_step.h5 : ¬ drop0% Std.Iter.all_eq_match_step 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (p := fun _ => false)
  clear h; revert this; ev

-- `Std.Iter.all_toList`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.all_toList.h5 : ¬ drop0% Std.Iter.all_toList 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (p := fun _ => false)
  clear h; revert this; ev

-- `Std.Iter.all_toArray`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.all_toArray.h5 : ¬ drop0% Std.Iter.all_toArray 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (p := fun _ => false)
  clear h; revert this; ev

-- `Std.Iter.findSomeM?_eq_match_step`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on []
theorem Iter.findSomeM?_eq_match_step.h9 : ¬ drop0% Std.Iter.findSomeM?_eq_match_step 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 ([] : List Nat)) (f := fun x => pure (some x))
  clear h; revert this; ev

-- `Std.Iter.findSomeM?_toList`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.findSomeM?_toList.h9 : ¬ drop0% Std.Iter.findSomeM?_toList 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (f := fun x => pure (some x))
  clear h; revert this; ev

-- `Std.Iter.findSome?_eq_match_step`, idx 6: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.findSome?_eq_match_step.h6 : ¬ drop0% Std.Iter.findSome?_eq_match_step 6 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (f := fun x => some x)
  clear h; revert this; ev

-- `Std.Iter.findSome?_toList`, idx 6: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.findSome?_toList.h6 : ¬ drop0% Std.Iter.findSome?_toList 6 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (f := fun x => some x)
  clear h; revert this; ev

-- `Std.Iter.findSomeM?_pure`, idx 10: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.findSomeM?_pure.h10 : ¬ drop0% Std.Iter.findSomeM?_pure 10 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (f := fun x => some x)
  clear h; revert this; ev

-- `Std.Iter.findM?_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem Iter.findM?_eq_match_step.h8 : ¬ drop0% Std.Iter.findM?_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 ([] : List Nat)) (f := fun _ => pure (ULift.up true))
  clear h; revert this; ev

-- `Std.Iter.findM?_toList`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.findM?_toList.h8 : ¬ drop0% Std.Iter.findM?_toList 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (f := fun _ => pure true)
  clear h; revert this; ev

-- `Std.Iter.findM?_eq_findM?_toList`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.findM?_eq_findM?_toList.h8 : ¬ drop0% Std.Iter.findM?_eq_findM?_toList 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (f := fun _ => pure (ULift.up true))
  clear h; revert this; ev

-- `Std.Iter.find?_eq_match_step`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.find?_eq_match_step.h5 : ¬ drop0% Std.Iter.find?_eq_match_step 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (f := fun _ => true)
  clear h; revert this; ev

-- `Std.Iter.find?_toList`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.find?_toList.h5 : ¬ drop0% Std.Iter.find?_toList 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2]) (f := fun _ => true)
  clear h; revert this; ev

-- `Std.Iter.findM?_pure`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem Iter.findM?_pure.h9 : ¬ drop0% Std.Iter.findM?_pure 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 [1, 2]) (f := fun _ => ULift.up true)
  clear h; revert this; ev

-- `Std.Iter.first?_eq_match_step`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.first?_eq_match_step.h5 : ¬ drop0% Std.Iter.first?_eq_match_step 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.head?_toList`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.head?_toList.h5 : ¬ drop0% Std.Iter.head?_toList 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.isEmpty_eq_match_step`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.isEmpty_eq_match_step.h5 : ¬ drop0% Std.Iter.isEmpty_eq_match_step 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.Iter.isEmpty_toList`, idx 5: tag 0 (returns init without iterating) on [1, 2]
theorem Iter.isEmpty_toList.h5 : ¬ drop0% Std.Iter.isEmpty_toList 5 := fun h => by
  have := h (α := BL 0 Nat) (it := bl 0 [1, 2])
  clear h; revert this; ev

-- `Std.IterM.forIn'_eq_match_step`, idx 10: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.forIn'_eq_match_step.h10 : ¬ drop0% Std.IterM.forIn'_eq_match_step 10 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (it := blM 1 ([] : List Nat) Id) (init := (0 : Nat)) (f := fun x _ acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.IterM.forIn_eq_match_step`, idx 10: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.forIn_eq_match_step.h10 : ¬ drop0% Std.IterM.forIn_eq_match_step 10 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (it := blM 1 ([] : List Nat) Id) (init := (0 : Nat)) (f := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this; ev

-- `Std.IterM.forIn_toList`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.forIn_toList.h9 : ¬ drop0% Std.IterM.forIn_toList 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Id) (f := fun x acc => pure (ForInStep.yield (acc + x))) (init := (0 : Nat))
  clear h; revert this; ev

-- `Std.IterM.forIn_toArray`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.forIn_toArray.h9 : ¬ drop0% Std.IterM.forIn_toArray 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Id) (f := fun x acc => pure (ForInStep.yield (acc + x))) (init := (0 : Nat))
  clear h; revert this; ev

-- `Std.IterM.forM_eq_match_step`, idx 10: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.forM_eq_match_step.h10 : ¬ drop0% Std.IterM.forM_eq_match_step 10 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (it := blM 1 ([] : List Nat) Id) (f := fun _ => pure PUnit.unit)
  clear h; revert this; ev

-- `Std.IterM.foldM_eq_match_step`, idx 11: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.foldM_eq_match_step.h11 : ¬ drop0% Std.IterM.foldM_eq_match_step 11 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 ([] : List Nat) Id)
  clear h; revert this; ev

-- `Std.IterM.fold_eq_match_step`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.fold_eq_match_step.h9 : ¬ drop0% Std.IterM.fold_eq_match_step 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (f := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 ([] : List Nat) Option)
  clear h; revert this; ev

-- `Std.IterM.toList_eq_fold`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.toList_eq_fold.h8 : ¬ drop0% Std.IterM.toList_eq_fold 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Option)
  clear h; revert this; ev

-- `Std.IterM.toArray_eq_fold`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.toArray_eq_fold.h8 : ¬ drop0% Std.IterM.toArray_eq_fold 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Option)
  clear h; revert this; ev

-- `Std.IterM.foldlM_toList`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldlM_toList.h9 : ¬ drop0% Std.IterM.foldlM_toList 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Id) (f := fun acc x => pure (acc + x)) (init := (0 : Nat))
  clear h; revert this; ev

-- `Std.IterM.foldlM_toArray`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldlM_toArray.h9 : ¬ drop0% Std.IterM.foldlM_toArray 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Id) (f := fun acc x => pure (acc + x)) (init := (0 : Nat))
  clear h; revert this; ev

-- `Std.IterM.foldl_toList`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldl_toList.h9 : ¬ drop0% Std.IterM.foldl_toList 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Option) (f := fun acc x => acc + x) (init := (0 : Nat))
  clear h; revert this; ev

-- `Std.IterM.foldl_toArray`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.foldl_toArray.h9 : ¬ drop0% Std.IterM.foldl_toArray 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Option) (f := fun acc x => acc + x) (init := (0 : Nat))
  clear h; revert this; ev

-- `Std.IterM.drain_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.drain_eq_match_step.h8 : ¬ drop0% Std.IterM.drain_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 ([] : List Nat) Option)
  clear h; revert this; ev

-- `Std.IterM.drain_eq_map_toList`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.drain_eq_map_toList.h8 : ¬ drop0% Std.IterM.drain_eq_map_toList 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Option)
  clear h; revert this; ev

-- `Std.IterM.drain_eq_map_toListRev`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.drain_eq_map_toListRev.h8 : ¬ drop0% Std.IterM.drain_eq_map_toListRev 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Option)
  clear h; revert this; ev

-- `Std.IterM.drain_eq_map_toArray`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.drain_eq_map_toArray.h8 : ¬ drop0% Std.IterM.drain_eq_map_toArray 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Option)
  clear h; revert this; ev

-- `Std.IterM.length_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.length_eq_match_step.h8 : ¬ drop0% Std.IterM.length_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 ([] : List Nat) Option)
  clear h; revert this; ev

-- `Std.IterM.up_size_toArray_eq_length`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.up_size_toArray_eq_length.h8 : ¬ drop0% Std.IterM.up_size_toArray_eq_length 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Option)
  clear h; revert this; ev

-- `Std.IterM.up_length_toList_eq_length`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.up_length_toList_eq_length.h8 : ¬ drop0% Std.IterM.up_length_toList_eq_length 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Option)
  clear h; revert this; ev

-- `Std.IterM.up_length_toListRev_eq_length`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on [1, 2]
theorem IterM.up_length_toListRev_eq_length.h8 : ¬ drop0% Std.IterM.up_length_toListRev_eq_length 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 [1, 2] Option)
  clear h; revert this; ev

-- `Std.IterM.anyM_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.anyM_eq_match_step.h8 : ¬ drop0% Std.IterM.anyM_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 ([] : List Nat) Option) (p := fun _ => pure (ULift.up true))
  clear h; revert this; ev

-- `Std.IterM.any_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.any_eq_match_step.h8 : ¬ drop0% Std.IterM.any_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 ([] : List Nat) Option) (p := fun _ => true)
  clear h; revert this; ev

-- `Std.IterM.allM_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.allM_eq_match_step.h8 : ¬ drop0% Std.IterM.allM_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 ([] : List Nat) Option) (p := fun _ => pure (ULift.up false))
  clear h; revert this; ev

-- `Std.IterM.all_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.all_eq_match_step.h8 : ¬ drop0% Std.IterM.all_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 ([] : List Nat) Option) (p := fun _ => false)
  clear h; revert this; ev

-- `Std.IterM.findSomeM?_eq_match_step`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.findSomeM?_eq_match_step.h9 : ¬ drop0% Std.IterM.findSomeM?_eq_match_step 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 ([] : List Nat) Option) (f := fun x => pure (some x))
  clear h; revert this; ev

-- `Std.IterM.findSome?_eq_match_step`, idx 9: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.findSome?_eq_match_step.h9 : ¬ drop0% Std.IterM.findSome?_eq_match_step 9 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 ([] : List Nat) Option) (f := fun x => some x)
  clear h; revert this; ev

-- `Std.IterM.findM?_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.findM?_eq_match_step.h8 : ¬ drop0% Std.IterM.findM?_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 ([] : List Nat) Option) (f := fun _ => pure (ULift.up true))
  clear h; revert this; ev

-- `Std.IterM.find?_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.find?_eq_match_step.h8 : ¬ drop0% Std.IterM.find?_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 ([] : List Nat) Option) (f := fun _ => true)
  clear h; revert this; ev

-- `Std.IterM.first?_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.first?_eq_match_step.h8 : ¬ drop0% Std.IterM.first?_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 ([] : List Nat) Option)
  clear h; revert this; ev

-- `Std.IterM.isEmpty_eq_match_step`, idx 8: tag 1 (fails (none) in Option, default elsewhere) on []
theorem IterM.isEmpty_eq_match_step.h8 : ¬ drop0% Std.IterM.isEmpty_eq_match_step 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := blM 1 ([] : List Nat) Option)
  clear h; revert this; ev

/-! ## Special cases -/

-- `Std.Iter.anyM_eq_anyM_mapM_pure`, idx 10: tag 0 in Id on [1, 2]
theorem Iter.anyM_eq_anyM_mapM_pure.h10 : ¬ drop0% Std.Iter.anyM_eq_anyM_mapM_pure 10 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := bl 0 [1, 2]) (p := fun _ => pure true)
  clear h; revert this; ev

-- `Std.Iter.allM_eq_allM_mapM_pure`, idx 10: tag 0 in Id on [1, 2]
theorem Iter.allM_eq_allM_mapM_pure.h10 : ¬ drop0% Std.Iter.allM_eq_allM_mapM_pure 10 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (it := bl 0 [1, 2]) (p := fun _ => pure false)
  clear h; revert this; ev

-- `Std.Iter.findSomeM?_pure`, idx 11: tag 5 (broken in Id), m := Option
theorem Iter.findSomeM?_pure.h11 : ¬ drop0% Std.Iter.findSomeM?_pure 11 := fun h => by
  have := h (α := BL 5 Nat) (m := Option) (it := bl 5 [1, 2]) (f := fun x => some x)
  clear h; revert this; ev

-- `Std.Iter.findM?_pure`, idx 10: tag 5 (broken in Id), m := Option
theorem Iter.findM?_pure.h10 : ¬ drop0% Std.Iter.findM?_pure 10 := fun h => by
  have := h (α := BL 5 Nat) (m := Option) (it := bl 5 [1, 2]) (f := fun _ => ULift.up true)
  clear h; revert this; ev

-- `Std.Iter.length_eq_fold`, idx 5: w = 1, tag 4 (broken in Id.{1})
theorem Iter.length_eq_fold.h5 : ¬ dropu% [1] Std.Iter.length_eq_fold 5 := fun h => by
  have := h (α := BL 4 (ULift.{1} Nat)) (it := bl 4 [ULift.up 1, ULift.up 2])
  clear h; revert this; ev

-- `Std.Iter.length_eq_fold`, idx 7: w = 1, tag 5 (broken in Id.{0})
theorem Iter.length_eq_fold.h7 : ¬ dropu% [1] Std.Iter.length_eq_fold 7 := fun h => by
  have := h (α := BL 5 (ULift.{1} Nat)) (it := bl 5 [ULift.up 1, ULift.up 2])
  clear h; revert this; ev

-- `Std.Iter.length_eq_forIn`, idx 5: w = 1, tag 4 (broken in Id.{1})
theorem Iter.length_eq_forIn.h5 : ¬ dropu% [1] Std.Iter.length_eq_forIn 5 := fun h => by
  have := h (α := BL 4 (ULift.{1} Nat)) (it := bl 4 [ULift.up 1, ULift.up 2])
  clear h; revert this; ev

-- `Std.Iter.length_eq_forIn`, idx 7: w = 1, tag 5 (broken in Id.{0})
theorem Iter.length_eq_forIn.h7 : ¬ dropu% [1] Std.Iter.length_eq_forIn 7 := fun h => by
  have := h (α := BL 5 (ULift.{1} Nat)) (it := bl 5 [ULift.up 1, ULift.up 2])
  clear h; revert this; ev

-- `Std.Iter.fold_hom`, idx 7: x₁ = 1, x₂ = 0, tag 4 (broken in Id.{1}), f := ULift.down
theorem Iter.fold_hom.h7 : ¬ dropu% [1, 0, 0] Std.Iter.fold_hom 7 := fun h => by
  have := h (α := BL 4 Nat) (it := bl 4 [1, 2]) (γ₁ := ULift.{1} Nat) (f := ULift.down)
    (g₁ := fun a b => ULift.up (a.down + b)) (g₂ := fun a b => a + b) (init := ULift.up 0) (fun _ _ => rfl)
  clear h; revert this; ev

-- `Std.Iter.fold_hom`, idx 9: x₁ = 0, x₂ = 1, tag 4 (broken in Id.{1}), f := ULift.up
theorem Iter.fold_hom.h9 : ¬ dropu% [0, 1, 0] Std.Iter.fold_hom 9 := fun h => by
  have := h (α := BL 4 Nat) (it := bl 4 [1, 2]) (γ₂ := ULift.{1} Nat) (f := ULift.up)
    (g₁ := fun a b => a + b) (g₂ := fun a b => ULift.up (a.down + b)) (init := 0) (fun _ _ => rfl)
  clear h; revert this; ev

-- `Std.Iter.forIn_eq`, idx 8: tag 1 in Option on []: none vs. some 0
theorem Iter.forIn_eq.h8 : ¬ drop0% Std.Iter.forIn_eq 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 ([] : List Nat)) (init := 0)
    (f := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this
  rw [IterM.DefaultConsumers.forIn'_eq_match_step _ IteratorLoop.wellFounded_of_finite]
  ev

-- `Std.Iter.forIn'_eq`, idx 8: tag 1 in Option on []: none vs. some 0
theorem Iter.forIn'_eq.h8 : ¬ drop0% Std.Iter.forIn'_eq 8 := fun h => by
  have := h (α := BL 1 Nat) (m := Option) (it := bl 1 ([] : List Nat)) (init := 0)
    (f := fun x _ acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this
  rw [IterM.DefaultConsumers.forIn'_eq_match_step _ IteratorLoop.wellFounded_of_finite]
  ev

-- `Std.IterM.forIn_eq`, idx 10: tag 1 in Option on []: none vs. some 0
theorem IterM.forIn_eq.h10 : ¬ drop0% Std.IterM.forIn_eq 10 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (it := blM 1 ([] : List Nat) Id) (init := 0)
    (f := fun x acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this
  rw [IterM.DefaultConsumers.forIn'_eq_match_step _ IteratorLoop.wellFounded_of_finite]
  ev

-- `Std.IterM.forIn'_eq`, idx 10: tag 1 in Option on []: none vs. some 0
theorem IterM.forIn'_eq.h10 : ¬ drop0% Std.IterM.forIn'_eq 10 := fun h => by
  have := h (α := BL 1 Nat) (m := Id) (n := Option) (it := blM 1 ([] : List Nat) Id) (init := 0)
    (f := fun x _ acc => pure (ForInStep.yield (acc + x)))
  clear h; revert this
  rw [IterM.DefaultConsumers.forIn'_eq_match_step _ IteratorLoop.wellFounded_of_finite]
  ev

-- `Std.LawfulIteratorLoop.lawful`, idx 8: i := brkF (tag 1) in Option on []: none vs. some 0
theorem LawfulIteratorLoop.lawful.h8 : ¬ drop0% Std.LawfulIteratorLoop.lawful 8 := fun h => by
  have := @h Nat (BL 1 Nat) Id Option _ _ _ brkF (fun _ _ f x => f x.run) _ Nat (blM 1 ([] : List Nat) Id) 0
    (fun _ _ _ => True) IteratorLoop.wellFounded_of_finite (fun b _ c => some ⟨.yield (c + b), trivial⟩)
  clear h; revert this
  show (none : Option Nat) = IterM.DefaultConsumers.forIn' (fun _ _ f x => f x.run) Nat (fun _ _ _ => True)
    (blM 1 ([] : List Nat) Id) 0 _ (fun _ => id) (fun b _ c => some ⟨.yield (c + b), trivial⟩) → False
  rw [IterM.DefaultConsumers.forIn'_eq_match_step _ IteratorLoop.wellFounded_of_finite]
  ev

-- `Std.IterM.length_attachWith`, idx 13: tag 0 in Id on [1, 2]: length 0 vs. 2
theorem IterM.length_attachWith.h13 : ¬ drop0% Std.IterM.length_attachWith 13 := fun h => by
  have := h (α := BL 0 Nat) (m := Id) (n := Id) (it := blM 0 [1, 2] Id) (P := fun _ => True) (hP := fun _ _ => trivial)
  clear h; revert this
  have e := congrArg (fun l => (Id.run l).length) (IterM.map_unattach_toList_attachWith (m := Id)
    (it := blM 0 [1, 2] Id) (P := fun _ => True) (hP := fun _ _ => trivial))
  simp only [toList_blM, Id.run_map, List.length_unattach] at e
  intro this
  have := congrArg (fun x => (Id.run x).down) this
  simp only [← IterM.up_length_toList_eq_length, Id.run_map] at this
  rw [e] at this
  revert this; decide

-- `Std.Iter.allM_eq_not_anyM_not`, idx 8: tag 2 (loops over Bool return true): true vs. !true
theorem Iter.allM_eq_not_anyM_not.h8 : ¬ drop0% Std.Iter.allM_eq_not_anyM_not 8 := fun h => by
  have := h (α := BL 2 Nat) (m := Id) (it := bl 2 [1]) (p := fun _ => pure true)
  have k1 : ∀ q, Iter.allM (m := Id) q (bl 2 [1]) = pure true := fun q => loop2_bool
  have k2 : ∀ q, Iter.anyM (m := Id) q (bl 2 [1]) = pure true := fun q => loop2_bool
  simp only [k1, k2] at this
  revert this; decide

-- `Std.Iter.all_eq_not_any_not`, idx 8: tag 2: true vs. !true
theorem Iter.all_eq_not_any_not.h8 : ¬ drop0% Std.Iter.all_eq_not_any_not 8 := fun h => by
  have := h (α := BL 2 Nat) (m := Id) (it := bl 2 [1]) (p := fun _ => true)
  have k1 : ∀ q, Iter.all q (bl 2 [1]) = true := fun q => loop2_bool
  have k2 : ∀ q, Iter.any q (bl 2 [1]) = true := fun q => loop2_bool
  simp only [k1, k2] at this
  revert this; decide

-- `Std.IterM.allM_eq_not_anyM_not`, idx 8: tag 3 (loops over ULift Bool return up true)
theorem IterM.allM_eq_not_anyM_not.h8 : ¬ drop0% Std.IterM.allM_eq_not_anyM_not 8 := fun h => by
  have := h (α := BL 3 Nat) (m := Id) (it := blM 3 [1] Id) (p := fun _ => pure (ULift.up true))
  have k1 : ∀ q, IterM.allM q (blM 3 [1] Id) = pure (ULift.up true) := fun q => loop3_ubool
  have k2 : ∀ q, IterM.anyM q (blM 3 [1] Id) = pure (ULift.up true) := fun q => loop3_ubool
  simp only [k1, k2] at this
  revert this; decide

-- `Std.IterM.all_eq_not_any_not`, idx 8: tag 3
theorem IterM.all_eq_not_any_not.h8 : ¬ drop0% Std.IterM.all_eq_not_any_not 8 := fun h => by
  have := h (α := BL 3 Nat) (m := Id) (it := blM 3 [1] Id) (p := fun _ => true)
  have k1 : ∀ q, IterM.all q (blM 3 [1] Id) = pure (ULift.up true) := fun q => loop3_ubool
  have k2 : ∀ q, IterM.any q (blM 3 [1] Id) = pure (ULift.up true) := fun q => loop3_ubool
  simp only [k1, k2] at this
  revert this; decide

-- `Std.IterM.fold_hom`, idx 10: tag 2, γ₁ = γ₂ = Bool, f := not: true vs. !true
theorem IterM.fold_hom.h10 : ¬ drop0% Std.IterM.fold_hom 10 := fun h => by
  have := h (α := BL 2 Nat) (m := Id) (it := blM 2 [1] Id) (f := not) (g₁ := fun x _ => x)
    (g₂ := fun x _ => x) (init := true) (fun _ _ => rfl)
  have k : ∀ g (i : Bool), IterM.fold g i (blM 2 [1] Id) = pure true := fun g i => loop2_bool
  simp only [k] at this
  revert this; decide

-- `Std.IterM.forIn_eq_foldM`, idx 8: tag 2: forIn over Bool gives true, the fold over
-- ForInStep Bool gives init = false
theorem IterM.forIn_eq_foldM.h8 : ¬ drop0% Std.IterM.forIn_eq_foldM 8 := fun h => by
  have := h (α := BL 2 Nat) (m := Id) (it := bl 2 [1]) (init := false) (f := fun _ acc => pure (.yield acc))
  have k1 : ∀ (f : Nat → Bool → Id (ForInStep Bool)) (i : Bool), forIn (bl 2 [1]) i f = pure true :=
    fun f i => loop2_bool
  have k2 : ∀ g (i : ForInStep Bool), Iter.foldM (m := Id) g i (bl 2 [1]) = pure i :=
    fun g i => loop2_ne (Ne.symm bool_ne_forInStep)
  simp only [k1, k2] at this
  revert this; decide

-- `Std.IterM.findSomeM?_pure`, idx 9 (removable): findSome? f is findSomeM? (pure <| f ·) by definition
theorem IterM.findSomeM?_pure.h9 : drop% Std.IterM.findSomeM?_pure 9 := by intros; rfl

-- `Std.IterM.findM?_pure`, idx 8 (removable): find? (ULift.down <| f ·) unfolds to findM? (pure <| f ·)
theorem IterM.findM?_pure.h8 : drop% Std.IterM.findM?_pure 8 := by intros; rfl


end ItLoopHand
