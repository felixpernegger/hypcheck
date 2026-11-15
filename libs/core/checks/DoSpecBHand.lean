import Std
import Lean

/-!
Hand pass `DoSpecB` (hand15): the 177 unresolved hypotheses of the second half of
`Std.Do.Triple.SpecLemmas` (Hoare-triple specs of the iterator combinators `filterMap`, `map`,
`filter`, `…M`, `…WithPostcondition` under `foldM`/`fold`/`forIn`, of `Array`/`String`/`String.Slice`
loops, `repeatM` and `Lean.Loop`). For hypothesis `hᵢ` of theorem `T` each declaration proves `¬T'`
(`drop0%`/`indep0%`, universes 0) or `T'` (`drop%`).

175 necessary, 2 removable, 0 independent, 0 left unresolved.

Method. Every iterator spec lemma here is `Triple RHS P Q → Triple LHS P Q`, where `LHS = RHS` is
the corresponding `Std.Iter`/`Std.IterM` equation lemma, whose hypotheses were all decided in hand8/
hand10 (`checks/ItMonadMAHand.lean`, `ItMonadIterHand.lean`, `ItLoopHand.lean`, `OpD1Hand.lean`,
`OpD2Hand.lean`). A *pin lemma* turns `∀ P Q, Triple y P Q → Triple x P Q` into `x = y` for the WP
monad of the counterexample; then the base refutation runs unchanged. Pins:
* `pinId` (`Id`), `pinOpt` (`Option`);
* `wpVia`/`wpmVia`/`pinVia`: a `WP`/`WPMonad` instance read off a monad morphism `φ : o →ₘ StateM σ`,
  and `φ x s = φ y s` from the pin. Used for the lawful writers of the base files (`φ x = fun s =>
  (x.v, s + x.c)` resp. `s || x.c`): `MA.NW.wpm`, `MA.NW2.wpm`, `MA.NWb.wpm` (Nat writers),
  `MA.W.wpm` (Bool writer), `MI.W.wpm` (the Int writers `W 0 0 ac lc ak`: `L`, `Lc`, `Am`, …),
  `MI.BW.wpm` (Bool writer); each with `….pin : (∀ P Q, Triple y P Q → Triple x P Q) → x = y`.
These make every lawful writer model a `WPMonad`, so any base refutation whose WP-side monad is a
lawful writer, `Id` or `Option` carries over.

Rows by kind:
* `h` (the triple premise, 38 rows) and the 7 loop `step` premises: `Id` with postcondition `False`
  (`id_triple_false`), resp. an invariant true at the start and false at the end.
* `Finite α m` / `Finite α Id` (38): two vacuously lawful base loops on a non-finite iterator
  (`LP` with `OL true/false` in `Option`, `AD` with `ADLoop 0/1` in `Id`; copied from OpD2/OpD1);
  the combinator side is the same term, the base side differs.
* `LawfulIteratorLoop` (38): the tagged list iterator `BL k` of `ItLoopHand` (tag 1: fails in
  `Option`; tag 0: returns `init`).
* `LawfulMonad`/`WeaklyLawfulMonadAttach`/`LawfulMonadLiftT` (53): the broken monads/lifts of
  `ItMonadMAHand` (namespace `DoSpecBHand.MA`: `SM`, `MB`, `NWb`, `tickNW`, `tickNW2`, `evilLoop`)
  and `ItMonadIterHand` (namespace `DoSpecBHand.MI`: `Mo`, `Mm`, `Am`, `SB`, `Lc`), with the WP
  monad pinned as above.
* `Nonempty β` of `Spec.repeatM` (dependent): `β = Empty`, invariant `False` on continue states.

Removable (2): `LawfulMonad m` of `Std.Do.Spec.IterM.foldM_filterMap` and
`Std.Do.Spec.IterM.foldM_filter`: the base equations hold without it (law-free proofs copied from
`ItMonadMAHand`, namespace `DoSpecBHand.MA.Rem`), and the spec follows by rewriting with them.

Run: `runs/hand15/lean.sh checks/DoSpecBHand.lean` (stage1).
-/

set_option linter.unusedVariables false

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


set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option warn.classDefReducibility false

open Std Std.Do Std.Iterators

namespace DoSpecBHand

theorem id_triple_false {α : Type} (x : Id α) : ¬ Triple x (⌜True⌝ : Assertion .pure) (PostCond.noThrow fun _ => ⌜False⌝) :=
  fun h => h trivial

theorem pinId {α : Type} {x y : Id α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := H ⌜True⌝ (PostCond.noThrow fun r => ⌜r = y.run⌝) (fun _ => rfl)
  exact this trivial

theorem pinOpt {α : Type} {x y : Option α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := H ⌜True⌝ (fun r => ⌜some r = y⌝, fun _ => ⌜none = y⌝, ()) (by cases y <;> exact fun _ => rfl)
  have h := this trivial
  cases x <;> exact h

section
/-! ## Models: non-finite iterators (copied from checks/OpD1Hand.lean, checks/OpD2Hand.lean) -/

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


/-! ## Models: list iterator copy with tagged loops (copied from checks/ItLoopHand.lean) -/
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


end
end DoSpecBHand

/-! ## WP interpretations through `StateM σ` -/
namespace DoSpecBHand
open Std Std.Do

/-- A `WP` instance read off a map `φ` into `StateM σ`. -/
@[instance_reducible] def wpVia {o : Type → Type} {σ : Type} (φ : ∀ {α : Type}, o α → StateM σ α) :
    WP o (.arg σ .pure) := ⟨fun x => wp (φ x)⟩

/-- `wpVia φ` is a `WPMonad` when `φ` is a monad morphism. -/
@[instance_reducible] def wpmVia {o : Type → Type} [Monad o] [LawfulMonad o] {σ : Type}
    (φ : ∀ {α : Type}, o α → StateM σ α)
    (hp : ∀ {α : Type} (a : α), φ (pure a) = pure a)
    (hb : ∀ {α β : Type} (x : o α) (f : α → o β), φ (x >>= f) = φ x >>= fun a => φ (f a)) :
    WPMonad o (.arg σ .pure) :=
  @WPMonad.mk o _ _ inferInstance (wpVia φ)
    (fun a => by show wp (φ (pure a)) = _; rw [hp, WPMonad.wp_pure])
    (fun x f => by show wp (φ (x >>= f)) = _; rw [hb, WPMonad.wp_bind]; rfl)

/-- If every triple of `y` is one of `x`, then `x` and `y` agree under `φ` at every start state. -/
theorem pinVia {o : Type → Type} {σ : Type} (φ : ∀ {α : Type}, o α → StateM σ α) {α : Type} {x y : o α}
    (H : ∀ P Q, @Triple o (.arg σ .pure) (wpVia φ) α y P Q → @Triple o (.arg σ .pure) (wpVia φ) α x P Q)
    (s : σ) : φ x s = φ y s := by
  have := H (fun s' => ⌜s' = s⌝) (fun r s' => ⌜(r, s') = φ y s⌝, ()) (fun s' hs => by cases hs; exact rfl)
  exact this s rfl

end DoSpecBHand
namespace DoSpecBHand.MA
open Std Std.Iterators Std.Iterators.Types Std.Internal

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

end DoSpecBHand.MA


namespace DoSpecBHand.MA
open Std Std.Iterators Std.Iterators.Types Std.Internal

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

end DoSpecBHand.MA
namespace DoSpecBHand.MI
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

/-- One evaluation round on hypothesis `h`: unfold the combinators to `filterMapWithPostcondition`
steps, the lifts and the base steps, then the monad operations and `Shrink` round trips. -/
macro "evs" h:ident : tactic => `(tactic| (
  (try simp only [Iter.mapM, IterM.mapM, Iter.filterMapM, IterM.filterMapM,
    Iter.filterM, IterM.filterM, Iter.mapWithPostcondition, Iter.filterMapWithPostcondition,
    Iter.filterWithPostcondition, IterM.filterWithPostcondition, Iter.flatMapM, Iter.flatMapAfterM,
    IterM.flatMapM, IterM.flatMapAfterM, step_mwp, step_fmwp] at $h:ident)
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


end DoSpecBHand.MI

namespace DoSpecBHand.MA
open Std Std.Do

def NW.φ {α : Type} (x : NW α) : StateM Nat α := fun s => (x.v, s + x.c)
instance NW.wpm : WPMonad NW (.arg Nat .pure) := wpmVia NW.φ
  (fun a => by funext s; simp [NW.φ, NW.pure_eq]; rfl)
  (fun x f => by funext s; show ((f x.v).v, s + (x.c + (f x.v).c)) = ((f x.v).v, s + x.c + (f x.v).c); rw [Nat.add_assoc])
theorem NW.pin {α : Type} {x y : NW α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := pinVia NW.φ H 0
  simp [NW.φ] at this
  have := Prod.mk.inj this
  exact NW.ext' this.2 this.1

end DoSpecBHand.MA

namespace DoSpecBHand.MI
open Std Std.Do

def W.φ {ac lc ak : Int} {α : Type} (x : W 0 0 ac lc ak α) : StateM Int α := fun s => (x.v, s + x.c)
instance W.wpm {ac lc ak : Int} : WPMonad (W 0 0 ac lc ak) (.arg Int .pure) := wpmVia W.φ
  (fun a => by funext s; simp [W.φ]; rfl)
  (fun x f => by funext s; show ((f x.v).v, s + (x.c + (f x.v).c + 0)) = ((f x.v).v, s + x.c + (f x.v).c); rw [Int.add_zero, Int.add_assoc])
theorem W.pin {ac lc ak : Int} {α : Type} {x y : W 0 0 ac lc ak α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := pinVia W.φ H 0
  simp [W.φ] at this
  have := Prod.mk.inj this
  exact W.ext' this.2 this.1

end DoSpecBHand.MI

namespace DoSpecBHand.MA
open Std Std.Do

def NW2.φ {α : Type} (x : NW2 α) : StateM Nat α := fun s => (x.v, s + x.c)
instance NW2.wpm : WPMonad NW2 (.arg Nat .pure) := wpmVia NW2.φ
  (fun a => by funext s; simp [NW2.φ, NW2.pure_eq]; rfl)
  (fun x f => by funext s; show ((f x.v).v, s + (x.c + (f x.v).c)) = ((f x.v).v, s + x.c + (f x.v).c); rw [Nat.add_assoc])
theorem NW2.pin {α : Type} {x y : NW2 α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := pinVia NW2.φ H 0
  simp [NW2.φ] at this
  have := Prod.mk.inj this
  exact NW2.ext' this.2 this.1

def NWb.φ {α : Type} (x : NWb α) : StateM Nat α := fun s => (x.v, s + x.c)
instance NWb.wpm : WPMonad NWb (.arg Nat .pure) := wpmVia NWb.φ
  (fun a => by funext s; simp [NWb.φ, NWb.pure_eq]; rfl)
  (fun x f => by funext s; show ((f x.v).v, s + (x.c + (f x.v).c)) = ((f x.v).v, s + x.c + (f x.v).c); rw [Nat.add_assoc])
theorem NWb.pin {α : Type} {x y : NWb α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := pinVia NWb.φ H 0
  simp [NWb.φ] at this
  have := Prod.mk.inj this
  exact NWb.ext' this.2 this.1

def W.φ {α : Type} (x : W α) : StateM Bool α := fun s => (x.v, s || x.c)
instance W.wpm : WPMonad W (.arg Bool .pure) := wpmVia W.φ
  (fun a => by funext s; simp [W.φ, W.pure_eq]; rfl)
  (fun x f => by funext s; show ((f x.v).v, s || (x.c || (f x.v).c)) = ((f x.v).v, (s || x.c) || (f x.v).c); rw [Bool.or_assoc])
theorem W.pin {α : Type} {x y : W α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := pinVia W.φ H false
  simp [W.φ] at this
  have := Prod.mk.inj this
  exact W.ext' this.2 this.1

end DoSpecBHand.MA

namespace DoSpecBHand.MI
open Std Std.Do

def BW.φ {α : Type} (x : BW α) : StateM Bool α := fun s => (x.v, s || x.c)
instance BW.wpm : WPMonad BW (.arg Bool .pure) := wpmVia BW.φ
  (fun a => by funext s; simp [BW.φ, BW.pure_c, BW.pure_v]; rfl)
  (fun x f => by funext s; show ((f x.v).v, s || (x.c || (f x.v).c)) = ((f x.v).v, (s || x.c) || (f x.v).c); rw [Bool.or_assoc])
theorem BW.pin {α : Type} {x y : BW α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := pinVia BW.φ H false
  simp [BW.φ] at this
  have := Prod.mk.inj this
  exact BW.ext' this.2 this.1

end DoSpecBHand.MI

namespace DoSpecBHand

/-! ## Necessary: core -/

-- `Std.Do.Spec.IterM.foldM_filterWithPostcondition`, idx 8 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.foldM_filterWithPostcondition.h8 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterWithPostcondition 8 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (n := Option) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (n := Option) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.foldM_filterWithPostcondition`, idx 19 (Std.LawfulIteratorLoop α m o): as for the base lemma Std.IterM.foldM_filterWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem IterM.foldM_filterWithPostcondition.h19 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterWithPostcondition 19 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.foldM_filterWithPostcondition`, idx 30 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.foldM_filterWithPostcondition.h30 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterWithPostcondition 30 := fun h =>
  id_triple_false _ (h (m := Id) (n := Id) (o := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.foldM_filterM`, idx 8 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.foldM_filterM.h8 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterM 8 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (n := Option) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (n := Option) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.foldM_filterM`, idx 21 (Std.LawfulIteratorLoop α m o): as for the base lemma Std.IterM.foldM_filterM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem IterM.foldM_filterM.h21 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterM 21 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.foldM_filterM`, idx 32 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.foldM_filterM.h32 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterM 32 := fun h =>
  id_triple_false _ (h (m := Id) (n := Id) (o := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.foldM_filterMap`, idx 8 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.foldM_filterMap.h8 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMap 8 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (n := Option) (f := fun x => some x) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (n := Option) (f := fun x => some x) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.foldM_filterMap`, idx 15 (Std.LawfulIteratorLoop α m n): as for the base lemma Std.IterM.foldM_filterMap (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem IterM.foldM_filterMap.h15 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMap 15 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => some x) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.foldM_filterMap`, idx 24 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.foldM_filterMap.h24 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMap 24 := fun h =>
  id_triple_false _ (h (m := Id) (n := Id) (f := fun x => some x) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.foldM_map`, idx 8 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.foldM_map.h8 : ¬ drop0% Std.Do.Spec.IterM.foldM_map 8 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (n := Option) (f := fun x => x + 1) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (n := Option) (f := fun x => x + 1) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.foldM_map`, idx 15 (Std.LawfulIteratorLoop α m n): as for the base lemma Std.IterM.foldM_map (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem IterM.foldM_map.h15 : ¬ drop0% Std.Do.Spec.IterM.foldM_map 15 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => x + 1) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.foldM_map`, idx 24 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.foldM_map.h24 : ¬ drop0% Std.Do.Spec.IterM.foldM_map 24 := fun h =>
  id_triple_false _ (h (m := Id) (n := Id) (f := fun x => x + 1) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.foldM_filter`, idx 7 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.foldM_filter.h7 : ¬ drop0% Std.Do.Spec.IterM.foldM_filter 7 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (n := Option) (f := fun _ => true) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (n := Option) (f := fun _ => true) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.foldM_filter`, idx 14 (Std.LawfulIteratorLoop α m n): as for the base lemma Std.IterM.foldM_filter (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem IterM.foldM_filter.h14 : ¬ drop0% Std.Do.Spec.IterM.foldM_filter 14 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun _ => true) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.foldM_filter`, idx 23 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.foldM_filter.h23 : ¬ drop0% Std.Do.Spec.IterM.foldM_filter 23 := fun h =>
  id_triple_false _ (h (m := Id) (n := Id) (f := fun _ => true) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.fold_filterMapWithPostcondition`, idx 8 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.fold_filterMapWithPostcondition.h8 : ¬ drop0% Std.Do.Spec.IterM.fold_filterMapWithPostcondition 8 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.fold_filterMapWithPostcondition`, idx 15 (Std.LawfulIteratorLoop α m n): as for the base lemma Std.IterM.fold_filterMapWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem IterM.fold_filterMapWithPostcondition.h15 : ¬ drop0% Std.Do.Spec.IterM.fold_filterMapWithPostcondition 15 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.fold_filterMapWithPostcondition`, idx 24 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.fold_filterMapWithPostcondition.h24 : ¬ drop0% Std.Do.Spec.IterM.fold_filterMapWithPostcondition 24 := fun h =>
  id_triple_false _ (h (m := Id) (n := Id) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.fold_filterMapM`, idx 8 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.fold_filterMapM.h8 : ¬ drop0% Std.Do.Spec.IterM.fold_filterMapM 8 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.fold_filterMapM`, idx 17 (Std.LawfulIteratorLoop α m n): as for the base lemma Std.IterM.fold_filterMapM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem IterM.fold_filterMapM.h17 : ¬ drop0% Std.Do.Spec.IterM.fold_filterMapM 17 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.fold_filterMapM`, idx 26 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.fold_filterMapM.h26 : ¬ drop0% Std.Do.Spec.IterM.fold_filterMapM 26 := fun h =>
  id_triple_false _ (h (m := Id) (n := Id) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.fold_mapWithPostcondition`, idx 8 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.fold_mapWithPostcondition.h8 : ¬ drop0% Std.Do.Spec.IterM.fold_mapWithPostcondition 8 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.fold_mapWithPostcondition`, idx 15 (Std.LawfulIteratorLoop α m n): as for the base lemma Std.IterM.fold_mapWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem IterM.fold_mapWithPostcondition.h15 : ¬ drop0% Std.Do.Spec.IterM.fold_mapWithPostcondition 15 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.fold_mapWithPostcondition`, idx 24 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.fold_mapWithPostcondition.h24 : ¬ drop0% Std.Do.Spec.IterM.fold_mapWithPostcondition 24 := fun h =>
  id_triple_false _ (h (m := Id) (n := Id) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.fold_mapM`, idx 8 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.fold_mapM.h8 : ¬ drop0% Std.Do.Spec.IterM.fold_mapM 8 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.fold_mapM`, idx 17 (Std.LawfulIteratorLoop α m n): as for the base lemma Std.IterM.fold_mapM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem IterM.fold_mapM.h17 : ¬ drop0% Std.Do.Spec.IterM.fold_mapM 17 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.fold_mapM`, idx 26 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.fold_mapM.h26 : ¬ drop0% Std.Do.Spec.IterM.fold_mapM 26 := fun h =>
  id_triple_false _ (h (m := Id) (n := Id) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.fold_filterWithPostcondition`, idx 7 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.fold_filterWithPostcondition.h7 : ¬ drop0% Std.Do.Spec.IterM.fold_filterWithPostcondition 7 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.fold_filterWithPostcondition`, idx 14 (Std.LawfulIteratorLoop α m n): as for the base lemma Std.IterM.fold_filterWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem IterM.fold_filterWithPostcondition.h14 : ¬ drop0% Std.Do.Spec.IterM.fold_filterWithPostcondition 14 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.fold_filterWithPostcondition`, idx 23 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.fold_filterWithPostcondition.h23 : ¬ drop0% Std.Do.Spec.IterM.fold_filterWithPostcondition 23 := fun h =>
  id_triple_false _ (h (m := Id) (n := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.fold_filterM`, idx 7 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.fold_filterM.h7 : ¬ drop0% Std.Do.Spec.IterM.fold_filterM 7 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.fold_filterM`, idx 16 (Std.LawfulIteratorLoop α m n): as for the base lemma Std.IterM.fold_filterM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem IterM.fold_filterM.h16 : ¬ drop0% Std.Do.Spec.IterM.fold_filterM 16 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (m := Id) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 1 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.fold_filterM`, idx 25 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.fold_filterM.h25 : ¬ drop0% Std.Do.Spec.IterM.fold_filterM 25 := fun h =>
  id_triple_false _ (h (m := Id) (n := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.fold_filterMap`, idx 7 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.fold_filterMap.h7 : ¬ drop0% Std.Do.Spec.IterM.fold_filterMap 7 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (f := fun x => some x) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (f := fun x => some x) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.fold_filterMap`, idx 12 (Std.LawfulIteratorLoop α m m): as for the base lemma Std.IterM.fold_filterMap (checks/ItLoopHand.lean): tag 0 (returns init without iterating) on [1, 2]; the WP monad pins the value
theorem IterM.fold_filterMap.h12 : ¬ drop0% Std.Do.Spec.IterM.fold_filterMap 12 := fun h => by
  have := pinId fun P Q => h (α := BL 0 Nat) (m := Id) (f := fun x => some x) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 0 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.fold_filterMap`, idx 19 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.fold_filterMap.h19 : ¬ drop0% Std.Do.Spec.IterM.fold_filterMap 19 := fun h =>
  id_triple_false _ (h (m := Id) (f := fun x => some x) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.fold_map`, idx 7 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.fold_map.h7 : ¬ drop0% Std.Do.Spec.IterM.fold_map 7 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (f := fun x => x + 1) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (f := fun x => x + 1) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.fold_map`, idx 12 (Std.LawfulIteratorLoop α m m): as for the base lemma Std.IterM.fold_map (checks/ItLoopHand.lean): tag 0 (returns init without iterating) on [1, 2]; the WP monad pins the value
theorem IterM.fold_map.h12 : ¬ drop0% Std.Do.Spec.IterM.fold_map 12 := fun h => by
  have := pinId fun P Q => h (α := BL 0 Nat) (m := Id) (f := fun x => x + 1) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 0 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.fold_map`, idx 19 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.fold_map.h19 : ¬ drop0% Std.Do.Spec.IterM.fold_map 19 := fun h =>
  id_triple_false _ (h (m := Id) (f := fun x => x + 1) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.IterM.fold_filter`, idx 6 (Std.Iterators.Finite α m): base LP skips forever (not Finite); with the vacuously lawful base loops OL true / OL false the base side is some init / none in Option, the combinator side is the same term
theorem IterM.fold_filter.h6 : ¬ drop0% Std.Do.Spec.IterM.fold_filter 6 := fun h => by
  have h1 := pinOpt fun P Q => (by letI := OL true; haveI := OL.lawful true; exact h (α := LP) (m := Option) (f := fun _ => true) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  have h2 := pinOpt fun P Q => (by letI := OL false; haveI := OL.lawful false; exact h (α := LP) (m := Option) (f := fun _ => true) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := lp) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.IterM.fold_filter`, idx 11 (Std.LawfulIteratorLoop α m m): as for the base lemma Std.IterM.fold_filter (checks/ItLoopHand.lean): tag 0 (returns init without iterating) on [1, 2]; the WP monad pins the value
theorem IterM.fold_filter.h11 : ¬ drop0% Std.Do.Spec.IterM.fold_filter 11 := fun h => by
  have := pinId fun P Q => h (α := BL 0 Nat) (m := Id) (f := fun _ => true) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := blM 0 [1, 2] Id) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.IterM.fold_filter`, idx 18 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem IterM.fold_filter.h18 : ¬ drop0% Std.Do.Spec.IterM.fold_filter 18 := fun h =>
  id_triple_false _ (h (m := Id) (f := fun _ => true) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iterM Id) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.Iter.forIn_filterMapWithPostcondition`, idx 15 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.forIn_filterMapWithPostcondition.h15 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMapWithPostcondition 15 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (o := Id) (it := AD.it) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (o := Id) (it := AD.it) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.Iter.forIn_filterMapWithPostcondition`, idx 17 (Std.LawfulIteratorLoop α Id o): as for the base lemma Std.Iter.forIn_filterMapWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.forIn_filterMapWithPostcondition.h17 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMapWithPostcondition 17 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.Iter.forIn_filterMapWithPostcondition`, idx 24 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.forIn_filterMapWithPostcondition.h24 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMapWithPostcondition 24 := fun h =>
  id_triple_false _ (h (n := Id) (o := Id) (it := [1, 2].iter) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.Iter.forIn_filterMapM`, idx 17 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.forIn_filterMapM.h17 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMapM 17 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (o := Id) (it := AD.it) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (o := Id) (it := AD.it) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.Iter.forIn_filterMapM`, idx 19 (Std.LawfulIteratorLoop α Id o): as for the base lemma Std.Iter.forIn_filterMapM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.forIn_filterMapM.h19 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMapM 19 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.Iter.forIn_filterMapM`, idx 26 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.forIn_filterMapM.h26 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMapM 26 := fun h =>
  id_triple_false _ (h (n := Id) (o := Id) (it := [1, 2].iter) (f := fun x => pure (some x)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.Iter.forIn_filterMap`, idx 10 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.forIn_filterMap.h10 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMap 10 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (it := AD.it) (f := fun x => some x) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (it := AD.it) (f := fun x => some x) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.Iter.forIn_filterMap`, idx 12 (Std.LawfulIteratorLoop α Id n): as for the base lemma Std.Iter.forIn_filterMap (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.forIn_filterMap.h12 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMap 12 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Option) (it := bl 1 [1, 2]) (f := fun x => some x) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.Iter.forIn_filterMap`, idx 19 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.forIn_filterMap.h19 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMap 19 := fun h =>
  id_triple_false _ (h (n := Id) (it := [1, 2].iter) (f := fun x => some x) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.Iter.forIn_mapWithPostcondition`, idx 15 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.forIn_mapWithPostcondition.h15 : ¬ drop0% Std.Do.Spec.Iter.forIn_mapWithPostcondition 15 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (o := Id) (it := AD.it) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (o := Id) (it := AD.it) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.Iter.forIn_mapWithPostcondition`, idx 17 (Std.LawfulIteratorLoop α Id o): as for the base lemma Std.Iter.forIn_mapWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.forIn_mapWithPostcondition.h17 : ¬ drop0% Std.Do.Spec.Iter.forIn_mapWithPostcondition 17 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.Iter.forIn_mapWithPostcondition`, idx 24 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.forIn_mapWithPostcondition.h24 : ¬ drop0% Std.Do.Spec.Iter.forIn_mapWithPostcondition 24 := fun h =>
  id_triple_false _ (h (n := Id) (o := Id) (it := [1, 2].iter) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.Iter.forIn_mapM`, idx 17 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.forIn_mapM.h17 : ¬ drop0% Std.Do.Spec.Iter.forIn_mapM 17 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (o := Id) (it := AD.it) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (o := Id) (it := AD.it) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.Iter.forIn_mapM`, idx 19 (Std.LawfulIteratorLoop α Id o): as for the base lemma Std.Iter.forIn_mapM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.forIn_mapM.h19 : ¬ drop0% Std.Do.Spec.Iter.forIn_mapM 19 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.Iter.forIn_mapM`, idx 26 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.forIn_mapM.h26 : ¬ drop0% Std.Do.Spec.Iter.forIn_mapM 26 := fun h =>
  id_triple_false _ (h (n := Id) (o := Id) (it := [1, 2].iter) (f := fun x => pure (x + 1)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.Iter.forIn_map`, idx 10 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.forIn_map.h10 : ¬ drop0% Std.Do.Spec.Iter.forIn_map 10 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (it := AD.it) (f := fun x => x + 1) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (it := AD.it) (f := fun x => x + 1) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.Iter.forIn_map`, idx 12 (Std.LawfulIteratorLoop α Id n): as for the base lemma Std.Iter.forIn_map (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.forIn_map.h12 : ¬ drop0% Std.Do.Spec.Iter.forIn_map 12 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Option) (it := bl 1 [1, 2]) (f := fun x => x + 1) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.Iter.forIn_map`, idx 19 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.forIn_map.h19 : ¬ drop0% Std.Do.Spec.Iter.forIn_map 19 := fun h =>
  id_triple_false _ (h (n := Id) (it := [1, 2].iter) (f := fun x => x + 1) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.Iter.forIn_filterWithPostcondition`, idx 14 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.forIn_filterWithPostcondition.h14 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterWithPostcondition 14 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (o := Id) (it := AD.it) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (o := Id) (it := AD.it) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.Iter.forIn_filterWithPostcondition`, idx 16 (Std.LawfulIteratorLoop α Id o): as for the base lemma Std.Iter.forIn_filterWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.forIn_filterWithPostcondition.h16 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterWithPostcondition 16 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.Iter.forIn_filterWithPostcondition`, idx 23 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.forIn_filterWithPostcondition.h23 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterWithPostcondition 23 := fun h =>
  id_triple_false _ (h (n := Id) (o := Id) (it := [1, 2].iter) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.Iter.forIn_filterM`, idx 16 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.forIn_filterM.h16 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterM 16 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (o := Id) (it := AD.it) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (o := Id) (it := AD.it) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.Iter.forIn_filterM`, idx 18 (Std.LawfulIteratorLoop α Id o): as for the base lemma Std.Iter.forIn_filterM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.forIn_filterM.h18 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterM 18 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Id) (o := Option) (it := bl 1 [1, 2]) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.Iter.forIn_filterM`, idx 25 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.forIn_filterM.h25 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterM 25 := fun h =>
  id_triple_false _ (h (n := Id) (o := Id) (it := [1, 2].iter) (f := fun _ => pure (ULift.up true)) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Spec.Iter.forIn_filter`, idx 9 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.forIn_filter.h9 : ¬ drop0% Std.Do.Spec.Iter.forIn_filter 9 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (it := AD.it) (f := fun _ => true) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (it := AD.it) (f := fun _ => true) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Spec.Iter.forIn_filter`, idx 11 (Std.LawfulIteratorLoop α Id n): as for the base lemma Std.Iter.forIn_filter (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.forIn_filter.h11 : ¬ drop0% Std.Do.Spec.Iter.forIn_filter 11 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Option) (it := bl 1 [1, 2]) (f := fun _ => true) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Spec.Iter.forIn_filter`, idx 18 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.forIn_filter.h18 : ¬ drop0% Std.Do.Spec.Iter.forIn_filter 18 := fun h =>
  id_triple_false _ (h (n := Id) (it := [1, 2].iter) (f := fun _ => true) (init := (0 : Nat)) (g := fun x acc => pure (ForInStep.yield (acc + x))) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.foldM_filterMapWithPostcondition`, idx 8 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.foldM_filterMapWithPostcondition.h8 : ¬ drop0% Std.Do.Iter.foldM_filterMapWithPostcondition 8 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.foldM_filterMapWithPostcondition`, idx 17 (Std.LawfulIteratorLoop α Id o): as for the base lemma Std.Iter.foldM_filterMapWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.foldM_filterMapWithPostcondition.h17 : ¬ drop0% Std.Do.Iter.foldM_filterMapWithPostcondition 17 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.foldM_filterMapWithPostcondition`, idx 26 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.foldM_filterMapWithPostcondition.h26 : ¬ drop0% Std.Do.Iter.foldM_filterMapWithPostcondition 26 := fun h =>
  id_triple_false _ (h (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.foldM_filterMapM`, idx 8 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.foldM_filterMapM.h8 : ¬ drop0% Std.Do.Iter.foldM_filterMapM 8 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.foldM_filterMapM`, idx 19 (Std.LawfulIteratorLoop α Id o): as for the base lemma Std.Iter.foldM_filterMapM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.foldM_filterMapM.h19 : ¬ drop0% Std.Do.Iter.foldM_filterMapM 19 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.foldM_filterMapM`, idx 28 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.foldM_filterMapM.h28 : ¬ drop0% Std.Do.Iter.foldM_filterMapM 28 := fun h =>
  id_triple_false _ (h (n := Id) (o := Id) (f := fun x => pure (some x)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.foldM_mapWithPostcondition`, idx 9 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.foldM_mapWithPostcondition.h9 : ¬ drop0% Std.Do.Iter.foldM_mapWithPostcondition 9 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (m := Id) (n := Id) (o := Id) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (m := Id) (n := Id) (o := Id) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.foldM_mapWithPostcondition`, idx 20 (Std.LawfulIteratorLoop α Id o): as for the base lemma Std.Iter.foldM_mapWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.foldM_mapWithPostcondition.h20 : ¬ drop0% Std.Do.Iter.foldM_mapWithPostcondition 20 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (m := Id) (n := Id) (o := Option) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.foldM_mapWithPostcondition`, idx 29 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.foldM_mapWithPostcondition.h29 : ¬ drop0% Std.Do.Iter.foldM_mapWithPostcondition 29 := fun h =>
  id_triple_false _ (h (m := Id) (n := Id) (o := Id) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.foldM_mapM`, idx 8 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.foldM_mapM.h8 : ¬ drop0% Std.Do.Iter.foldM_mapM 8 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (o := Id) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (o := Id) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.foldM_mapM`, idx 19 (Std.LawfulIteratorLoop α Id o): as for the base lemma Std.Iter.foldM_mapM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.foldM_mapM.h19 : ¬ drop0% Std.Do.Iter.foldM_mapM 19 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.foldM_mapM`, idx 28 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.foldM_mapM.h28 : ¬ drop0% Std.Do.Iter.foldM_mapM 28 := fun h =>
  id_triple_false _ (h (n := Id) (o := Id) (f := fun x => pure (x + 1)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.foldM_filterWithPostcondition`, idx 7 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.foldM_filterWithPostcondition.h7 : ¬ drop0% Std.Do.Iter.foldM_filterWithPostcondition 7 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (o := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (o := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.foldM_filterWithPostcondition`, idx 16 (Std.LawfulIteratorLoop α Id o): as for the base lemma Std.Iter.foldM_filterWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.foldM_filterWithPostcondition.h16 : ¬ drop0% Std.Do.Iter.foldM_filterWithPostcondition 16 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.foldM_filterWithPostcondition`, idx 25 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.foldM_filterWithPostcondition.h25 : ¬ drop0% Std.Do.Iter.foldM_filterWithPostcondition 25 := fun h =>
  id_triple_false _ (h (n := Id) (o := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.foldM_filterM`, idx 7 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.foldM_filterM.h7 : ¬ drop0% Std.Do.Iter.foldM_filterM 7 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (o := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (o := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.foldM_filterM`, idx 18 (Std.LawfulIteratorLoop α Id o): as for the base lemma Std.Iter.foldM_filterM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.foldM_filterM.h18 : ¬ drop0% Std.Do.Iter.foldM_filterM 18 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Id) (o := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.foldM_filterM`, idx 27 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.foldM_filterM.h27 : ¬ drop0% Std.Do.Iter.foldM_filterM 27 := fun h =>
  id_triple_false _ (h (n := Id) (o := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.foldM_filterMap`, idx 7 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.foldM_filterMap.h7 : ¬ drop0% Std.Do.Iter.foldM_filterMap 7 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (f := fun x => some x) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (f := fun x => some x) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.foldM_filterMap`, idx 12 (Std.LawfulIteratorLoop α Id n): as for the base lemma Std.Iter.foldM_filterMap (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.foldM_filterMap.h12 : ¬ drop0% Std.Do.Iter.foldM_filterMap 12 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Option) (f := fun x => some x) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.foldM_filterMap`, idx 19 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.foldM_filterMap.h19 : ¬ drop0% Std.Do.Iter.foldM_filterMap 19 := fun h =>
  id_triple_false _ (h (n := Id) (f := fun x => some x) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.foldM_map`, idx 7 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.foldM_map.h7 : ¬ drop0% Std.Do.Iter.foldM_map 7 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (f := fun x => x + 1) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (f := fun x => x + 1) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.foldM_map`, idx 12 (Std.LawfulIteratorLoop α Id n): as for the base lemma Std.Iter.foldM_map (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.foldM_map.h12 : ¬ drop0% Std.Do.Iter.foldM_map 12 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Option) (f := fun x => x + 1) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.foldM_map`, idx 19 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.foldM_map.h19 : ¬ drop0% Std.Do.Iter.foldM_map 19 := fun h =>
  id_triple_false _ (h (n := Id) (f := fun x => x + 1) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.foldM_filter`, idx 6 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.foldM_filter.h6 : ¬ drop0% Std.Do.Iter.foldM_filter 6 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (f := fun _ => true) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (f := fun _ => true) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.foldM_filter`, idx 11 (Std.LawfulIteratorLoop α Id n): as for the base lemma Std.Iter.foldM_filter (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.foldM_filter.h11 : ¬ drop0% Std.Do.Iter.foldM_filter 11 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Option) (f := fun _ => true) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.foldM_filter`, idx 18 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.foldM_filter.h18 : ¬ drop0% Std.Do.Iter.foldM_filter 18 := fun h =>
  id_triple_false _ (h (n := Id) (f := fun _ => true) (g := fun acc x => pure (acc + x)) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.fold_filterMapWithPostcondition`, idx 7 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.fold_filterMapWithPostcondition.h7 : ¬ drop0% Std.Do.Iter.fold_filterMapWithPostcondition 7 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.fold_filterMapWithPostcondition`, idx 12 (Std.LawfulIteratorLoop α Id n): as for the base lemma Std.Iter.fold_filterMapWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.fold_filterMapWithPostcondition.h12 : ¬ drop0% Std.Do.Iter.fold_filterMapWithPostcondition 12 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.fold_filterMapWithPostcondition`, idx 19 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.fold_filterMapWithPostcondition.h19 : ¬ drop0% Std.Do.Iter.fold_filterMapWithPostcondition 19 := fun h =>
  id_triple_false _ (h (n := Id) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.fold_filterMapM`, idx 7 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.fold_filterMapM.h7 : ¬ drop0% Std.Do.Iter.fold_filterMapM 7 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.fold_filterMapM`, idx 14 (Std.LawfulIteratorLoop α Id n): as for the base lemma Std.Iter.fold_filterMapM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.fold_filterMapM.h14 : ¬ drop0% Std.Do.Iter.fold_filterMapM 14 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Option) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.fold_filterMapM`, idx 21 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.fold_filterMapM.h21 : ¬ drop0% Std.Do.Iter.fold_filterMapM 21 := fun h =>
  id_triple_false _ (h (n := Id) (f := fun x => pure (some x)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.fold_mapWithPostcondition`, idx 7 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.fold_mapWithPostcondition.h7 : ¬ drop0% Std.Do.Iter.fold_mapWithPostcondition 7 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.fold_mapWithPostcondition`, idx 12 (Std.LawfulIteratorLoop α Id n): as for the base lemma Std.Iter.fold_mapWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.fold_mapWithPostcondition.h12 : ¬ drop0% Std.Do.Iter.fold_mapWithPostcondition 12 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.fold_mapWithPostcondition`, idx 19 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.fold_mapWithPostcondition.h19 : ¬ drop0% Std.Do.Iter.fold_mapWithPostcondition 19 := fun h =>
  id_triple_false _ (h (n := Id) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.fold_mapM`, idx 7 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.fold_mapM.h7 : ¬ drop0% Std.Do.Iter.fold_mapM 7 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.fold_mapM`, idx 14 (Std.LawfulIteratorLoop α Id n): as for the base lemma Std.Iter.fold_mapM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.fold_mapM.h14 : ¬ drop0% Std.Do.Iter.fold_mapM 14 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Option) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.fold_mapM`, idx 21 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.fold_mapM.h21 : ¬ drop0% Std.Do.Iter.fold_mapM 21 := fun h =>
  id_triple_false _ (h (n := Id) (f := fun x => pure (x + 1)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.fold_filterWithPostcondition`, idx 6 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.fold_filterWithPostcondition.h6 : ¬ drop0% Std.Do.Iter.fold_filterWithPostcondition 6 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.fold_filterWithPostcondition`, idx 11 (Std.LawfulIteratorLoop α Id n): as for the base lemma Std.Iter.fold_filterWithPostcondition (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.fold_filterWithPostcondition.h11 : ¬ drop0% Std.Do.Iter.fold_filterWithPostcondition 11 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.fold_filterWithPostcondition`, idx 18 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.fold_filterWithPostcondition.h18 : ¬ drop0% Std.Do.Iter.fold_filterWithPostcondition 18 := fun h =>
  id_triple_false _ (h (n := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

-- `Std.Do.Iter.fold_filterM`, idx 6 (Std.Iterators.Finite α Id): base AD (not Finite); with the vacuously lawful base loops ADLoop 0 / ADLoop 1 the base side gives two different values in Id, the combinator side is the same term
theorem Iter.fold_filterM.h6 : ¬ drop0% Std.Do.Iter.fold_filterM 6 := fun h => by
  have h1 := pinId fun P Q => (by letI := ADLoop 0 (n := Id); haveI := ADLoop.lawful 0 (n := Id); exact h (α := AD) (n := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  have h2 := pinId fun P Q => (by letI := ADLoop 1 (n := Id); haveI := ADLoop.lawful 1 (n := Id); exact h (α := AD) (n := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := AD.it) (P := P) (Q := Q))
  exact absurd (h1.symm.trans h2) (by decide)

-- `Std.Do.Iter.fold_filterM`, idx 13 (Std.LawfulIteratorLoop α Id n): as for the base lemma Std.Iter.fold_filterM (checks/ItLoopHand.lean): tag 1 (fails (none) in Option, default elsewhere) on [1, 2]; the WP monad pins the value
theorem Iter.fold_filterM.h13 : ¬ drop0% Std.Do.Iter.fold_filterM 13 := fun h => by
  have := pinOpt fun P Q => h (α := BL 1 Nat) (n := Option) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := bl 1 [1, 2]) (P := P) (Q := Q)
  clear h; revert this; ev

-- `Std.Do.Iter.fold_filterM`, idx 20 (h): m = n = o = Id, list iterator [1, 2], P = True, Q = False: the dropped triple is the only source of the conclusion, which is False in Id
theorem Iter.fold_filterM.h20 : ¬ drop0% Std.Do.Iter.fold_filterM 20 := fun h =>
  id_triple_false _ (h (n := Id) (f := fun _ => pure (ULift.up true)) (g := fun acc x => acc + x) (init := (0 : Nat)) (it := [1, 2].iter) (P := ⌜True⌝) (Q := PostCond.noThrow fun _ => ⌜False⌝))

end DoSpecBHand

namespace DoSpecBHand.MA
open Std Std.Do Std.Iterators Std.Iterators.Types

-- `Std.Do.Spec.IterM.foldM_filterWithPostcondition`, idx 13 (LawfulMonad n): as for the base lemma Std.IterM.foldM_filterWithPostcondition (checks/ItMonadMAHand.lean): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).; the WP monad pins the value
theorem IterM.foldM_filterWithPostcondition.h13 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterWithPostcondition 13 := by
  intro h
  have := W.pin fun P Q => h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterWithPostcondition`, idx 22 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.foldM_filterWithPostcondition (checks/ItMonadMAHand.lean): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.foldM_filterWithPostcondition.h22 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterWithPostcondition 22 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterWithPostcondition`, idx 23 (LawfulMonadLiftT n o): as for the base lemma Std.IterM.foldM_filterWithPostcondition (checks/ItMonadMAHand.lean): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.foldM_filterWithPostcondition.h23 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterWithPostcondition 23 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := NW2.pin fun P Q => h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterM`, idx 13 (LawfulMonad n): as for the base lemma Std.IterM.foldM_filterM (checks/ItMonadMAHand.lean): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).; the WP monad pins the value
theorem IterM.foldM_filterM.h13 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterM 13 := by
  intro h
  have := W.pin fun P Q => h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterM`, idx 14 (WeaklyLawfulMonadAttach n): as for the base lemma Std.IterM.foldM_filterM (checks/ItMonadMAHand.lean): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.; the WP monad pins the value
theorem IterM.foldM_filterM.h14 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterM 14 := by
  intro h
  have := NW.pin fun P Q => h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterM`, idx 24 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.foldM_filterM (checks/ItMonadMAHand.lean): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.foldM_filterM.h24 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterM 24 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterM`, idx 25 (LawfulMonadLiftT n o): as for the base lemma Std.IterM.foldM_filterM (checks/ItMonadMAHand.lean): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.foldM_filterM.h25 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterM 25 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := NW2.pin fun P Q => h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterMap`, idx 17 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.foldM_filterMap (checks/ItMonadMAHand.lean): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.; the WP monad pins the value
theorem IterM.foldM_filterMap.h17 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMap 17 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := some) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_map`, idx 11 (LawfulMonad m): as for the base lemma Std.IterM.foldM_map (checks/ItMonadMAHand.lean): m = MB (lawful Nat writer bind/pure, but map adds one), n = NW, lawful lift MB → NW, list iterator [0]: the map combinator maps in m.; the WP monad pins the value
theorem IterM.foldM_map.h11 : ¬ drop0% Std.Do.Spec.IterM.foldM_map 11 := by
  intro h
  have := NW.pin fun P Q => h (m := MB) (n := NW) (it := [0].iterM MB) (f := id) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_map`, idx 17 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.foldM_map (checks/ItMonadMAHand.lean): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.; the WP monad pins the value
theorem IterM.foldM_map.h17 : ¬ drop0% Std.Do.Spec.IterM.foldM_map 17 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := id) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filter`, idx 16 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.foldM_filter (checks/ItMonadMAHand.lean): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.; the WP monad pins the value
theorem IterM.foldM_filter.h16 : ¬ drop0% Std.Do.Spec.IterM.foldM_filter 16 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun _ => true) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.fold_filterMapWithPostcondition`, idx 17 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.fold_filterMapWithPostcondition (checks/ItMonadMAHand.lean): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.; the WP monad pins the value
theorem IterM.fold_filterMapWithPostcondition.h17 : ¬ drop0% Std.Do.Spec.IterM.fold_filterMapWithPostcondition 17 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure (some b)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.fold_filterMapM`, idx 14 (WeaklyLawfulMonadAttach n): as for the base lemma Std.IterM.fold_filterMapM (checks/ItMonadMAHand.lean): m = Id, n = NWb (lawful Nat writer whose attach adds one), list iterator [0].; the WP monad pins the value
theorem IterM.fold_filterMapM.h14 : ¬ drop0% Std.Do.Spec.IterM.fold_filterMapM 14 := by
  intro h
  have := NWb.pin fun P Q => h (init := 0) (g := fun d c => d + c) (m := Id) (n := NWb) (it := [0].iterM Id) (f := fun b => pure (some b)) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.fold_filterMapM`, idx 19 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.fold_filterMapM (checks/ItMonadMAHand.lean): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.; the WP monad pins the value
theorem IterM.fold_filterMapM.h19 : ¬ drop0% Std.Do.Spec.IterM.fold_filterMapM 19 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun b => pure (some b)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.fold_mapWithPostcondition`, idx 17 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.fold_mapWithPostcondition (checks/ItMonadMAHand.lean): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.; the WP monad pins the value
theorem IterM.fold_mapWithPostcondition.h17 : ¬ drop0% Std.Do.Spec.IterM.fold_mapWithPostcondition 17 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure b) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.fold_mapM`, idx 14 (WeaklyLawfulMonadAttach n): as for the base lemma Std.IterM.fold_mapM (checks/ItMonadMAHand.lean): m = Id, n = NWb (lawful Nat writer whose attach adds one), list iterator [0].; the WP monad pins the value
theorem IterM.fold_mapM.h14 : ¬ drop0% Std.Do.Spec.IterM.fold_mapM 14 := by
  intro h
  have := NWb.pin fun P Q => h (init := 0) (g := fun d c => d + c) (m := Id) (n := NWb) (it := [0].iterM Id) (f := fun b => pure b) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.fold_mapM`, idx 19 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.fold_mapM (checks/ItMonadMAHand.lean): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.; the WP monad pins the value
theorem IterM.fold_mapM.h19 : ¬ drop0% Std.Do.Spec.IterM.fold_mapM 19 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun b => pure b) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.fold_filterWithPostcondition`, idx 16 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.fold_filterWithPostcondition (checks/ItMonadMAHand.lean): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.; the WP monad pins the value
theorem IterM.fold_filterWithPostcondition.h16 : ¬ drop0% Std.Do.Spec.IterM.fold_filterWithPostcondition 16 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun _ => PostconditionT.pure (.up true)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.fold_filterM`, idx 13 (WeaklyLawfulMonadAttach n): as for the base lemma Std.IterM.fold_filterM (checks/ItMonadMAHand.lean): m = Id, n = NWb (lawful Nat writer whose attach adds one), list iterator [0].; the WP monad pins the value
theorem IterM.fold_filterM.h13 : ¬ drop0% Std.Do.Spec.IterM.fold_filterM 13 := by
  intro h
  have := NWb.pin fun P Q => h (init := 0) (g := fun d c => d + c) (m := Id) (n := NWb) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.fold_filterM`, idx 18 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.fold_filterM (checks/ItMonadMAHand.lean): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.; the WP monad pins the value
theorem IterM.fold_filterM.h18 : ¬ drop0% Std.Do.Spec.IterM.fold_filterM 18 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun _ => pure (.up true)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

end DoSpecBHand.MA

namespace DoSpecBHand.MI
open Std Std.Do Std.Iterators

-- `Std.Do.Spec.Iter.forIn_filterMapWithPostcondition`, idx 9 (LawfulMonad n): as for the base lemma Std.Iter.forIn_filterMapWithPostcondition (checks/ItMonadIterHand.lean): n = Mo (map counts 1), o = L, lawful lift, it = [0]: only the right side maps ((f out).run); the WP monad pins the value
theorem Iter.forIn_filterMapWithPostcondition.h9 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMapWithPostcondition 9 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Mo) (o := L) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Spec.Iter.forIn_filterMapWithPostcondition`, idx 14 (LawfulMonadLiftT n o): as for the base lemma Std.Iter.forIn_filterMapWithPostcondition (checks/ItMonadIterHand.lean): n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value; the WP monad pins the value
theorem Iter.forIn_filterMapWithPostcondition.h14 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMapWithPostcondition 14 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Spec.Iter.forIn_filterMapM`, idx 9 (LawfulMonad n): as for the base lemma Std.Iter.forIn_filterMapM (checks/ItMonadIterHand.lean): n = Mm (map counts 1, attach -1: weakly lawful, not lawful), o = L, it = [0]: only the left side attaches; the WP monad pins the value
theorem Iter.forIn_filterMapM.h9 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMapM 9 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Mm) (o := L) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Spec.Iter.forIn_filterMapM`, idx 14 (WeaklyLawfulMonadAttach n): as for the base lemma Std.Iter.forIn_filterMapM (checks/ItMonadIterHand.lean): n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches; the WP monad pins the value
theorem Iter.forIn_filterMapM.h14 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMapM 14 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Am) (o := L) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Spec.Iter.forIn_filterMapM`, idx 16 (LawfulMonadLiftT n o): as for the base lemma Std.Iter.forIn_filterMapM (checks/ItMonadIterHand.lean): n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value; the WP monad pins the value
theorem Iter.forIn_filterMapM.h16 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterMapM 16 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Spec.Iter.forIn_mapWithPostcondition`, idx 9 (LawfulMonad n): as for the base lemma Std.Iter.forIn_mapWithPostcondition (checks/ItMonadIterHand.lean): n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip); the WP monad pins the value
theorem Iter.forIn_mapWithPostcondition.h9 : ¬ drop0% Std.Do.Spec.Iter.forIn_mapWithPostcondition 9 := fun h => by
  have := BW.pin fun P Q => h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun b => pure b) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Do.Spec.Iter.forIn_mapWithPostcondition`, idx 14 (LawfulMonadLiftT n o): as for the base lemma Std.Iter.forIn_mapWithPostcondition (checks/ItMonadIterHand.lean): n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value; the WP monad pins the value
theorem Iter.forIn_mapWithPostcondition.h14 : ¬ drop0% Std.Do.Spec.Iter.forIn_mapWithPostcondition 14 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := L) (o := Lc) (f := pure) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Spec.Iter.forIn_mapM`, idx 9 (LawfulMonad n): as for the base lemma Std.Iter.forIn_mapM (checks/ItMonadIterHand.lean): n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip); the WP monad pins the value
theorem Iter.forIn_mapM.h9 : ¬ drop0% Std.Do.Spec.Iter.forIn_mapM 9 := fun h => by
  have := BW.pin fun P Q => h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun b => pure b) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Do.Spec.Iter.forIn_mapM`, idx 14 (WeaklyLawfulMonadAttach n): as for the base lemma Std.Iter.forIn_mapM (checks/ItMonadIterHand.lean): n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches; the WP monad pins the value
theorem Iter.forIn_mapM.h14 : ¬ drop0% Std.Do.Spec.Iter.forIn_mapM 14 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Am) (o := L) (f := pure) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Spec.Iter.forIn_mapM`, idx 16 (LawfulMonadLiftT n o): as for the base lemma Std.Iter.forIn_mapM (checks/ItMonadIterHand.lean): n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value; the WP monad pins the value
theorem Iter.forIn_mapM.h16 : ¬ drop0% Std.Do.Spec.Iter.forIn_mapM 16 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := L) (o := Lc) (f := pure) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Spec.Iter.forIn_filterWithPostcondition`, idx 8 (LawfulMonad n): as for the base lemma Std.Iter.forIn_filterWithPostcondition (checks/ItMonadIterHand.lean): n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip); the WP monad pins the value
theorem Iter.forIn_filterWithPostcondition.h8 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterWithPostcondition 8 := fun h => by
  have := BW.pin fun P Q => h (α := CD) (β := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Do.Spec.Iter.forIn_filterWithPostcondition`, idx 13 (LawfulMonadLiftT n o): as for the base lemma Std.Iter.forIn_filterWithPostcondition (checks/ItMonadIterHand.lean): n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value; the WP monad pins the value
theorem Iter.forIn_filterWithPostcondition.h13 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterWithPostcondition 13 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Spec.Iter.forIn_filterM`, idx 8 (LawfulMonad n): as for the base lemma Std.Iter.forIn_filterM (checks/ItMonadIterHand.lean): n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip); the WP monad pins the value
theorem Iter.forIn_filterM.h8 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterM 8 := fun h => by
  have := BW.pin fun P Q => h (α := CD) (β := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Do.Spec.Iter.forIn_filterM`, idx 13 (WeaklyLawfulMonadAttach n): as for the base lemma Std.Iter.forIn_filterM (checks/ItMonadIterHand.lean): n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches; the WP monad pins the value
theorem Iter.forIn_filterM.h13 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterM 13 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (it := ci 1) (n := Am) (o := L) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Spec.Iter.forIn_filterM`, idx 15 (LawfulMonadLiftT n o): as for the base lemma Std.Iter.forIn_filterM (checks/ItMonadIterHand.lean): n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value; the WP monad pins the value
theorem Iter.forIn_filterM.h15 : ¬ drop0% Std.Do.Spec.Iter.forIn_filterM 15 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc)) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.foldM_filterMapWithPostcondition`, idx 11 (LawfulMonad n): as for the base lemma Std.Iter.foldM_filterMapWithPostcondition (checks/ItMonadIterHand.lean): n = Mo (map counts 1), o = L, lawful lift, it = [0]: only the right side maps ((f b).run); the WP monad pins the value
theorem Iter.foldM_filterMapWithPostcondition.h11 : ¬ drop0% Std.Do.Iter.foldM_filterMapWithPostcondition 11 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Mo) (o := L) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.foldM_filterMapWithPostcondition`, idx 19 (LawfulMonadLiftT n o): as for the base lemma Std.Iter.foldM_filterMapWithPostcondition (checks/ItMonadIterHand.lean): n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value; the WP monad pins the value
theorem Iter.foldM_filterMapWithPostcondition.h19 : ¬ drop0% Std.Do.Iter.foldM_filterMapWithPostcondition 19 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.foldM_filterMapM`, idx 11 (LawfulMonad n): as for the base lemma Std.Iter.foldM_filterMapM (checks/ItMonadIterHand.lean): n = Mm (map counts 1, attach -1: weakly lawful, not lawful), o = L, it = [0]: only the left side attaches; the WP monad pins the value
theorem Iter.foldM_filterMapM.h11 : ¬ drop0% Std.Do.Iter.foldM_filterMapM 11 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Mm) (o := L) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.foldM_filterMapM`, idx 12 (WeaklyLawfulMonadAttach n): as for the base lemma Std.Iter.foldM_filterMapM (checks/ItMonadIterHand.lean): n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches; the WP monad pins the value
theorem Iter.foldM_filterMapM.h12 : ¬ drop0% Std.Do.Iter.foldM_filterMapM 12 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Am) (o := L) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.foldM_filterMapM`, idx 21 (LawfulMonadLiftT n o): as for the base lemma Std.Iter.foldM_filterMapM (checks/ItMonadIterHand.lean): n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value; the WP monad pins the value
theorem Iter.foldM_filterMapM.h21 : ¬ drop0% Std.Do.Iter.foldM_filterMapM 21 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.foldM_mapWithPostcondition`, idx 14 (LawfulMonad n): as for the base lemma Std.Iter.foldM_mapWithPostcondition (checks/ItMonadIterHand.lean): n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip); the WP monad pins the value
theorem Iter.foldM_mapWithPostcondition.h14 : ¬ drop0% Std.Do.Iter.foldM_mapWithPostcondition 14 := fun h => by
  have := BW.pin fun P Q => h (m := Id) (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun b => pure b) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Do.Iter.foldM_mapWithPostcondition`, idx 22 (LawfulMonadLiftT n o): as for the base lemma Std.Iter.foldM_mapWithPostcondition (checks/ItMonadIterHand.lean): n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value; the WP monad pins the value
theorem Iter.foldM_mapWithPostcondition.h22 : ¬ drop0% Std.Do.Iter.foldM_mapWithPostcondition 22 := fun h => by
  have := W.pin fun P Q => h (m := Id) (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Lc) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.foldM_mapM`, idx 11 (LawfulMonad n): as for the base lemma Std.Iter.foldM_mapM (checks/ItMonadIterHand.lean): n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip); the WP monad pins the value
theorem Iter.foldM_mapM.h11 : ¬ drop0% Std.Do.Iter.foldM_mapM 11 := fun h => by
  have := BW.pin fun P Q => h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun b => pure b) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Do.Iter.foldM_mapM`, idx 12 (WeaklyLawfulMonadAttach n): as for the base lemma Std.Iter.foldM_mapM (checks/ItMonadIterHand.lean): n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches; the WP monad pins the value
theorem Iter.foldM_mapM.h12 : ¬ drop0% Std.Do.Iter.foldM_mapM 12 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Am) (o := L) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.foldM_mapM`, idx 21 (LawfulMonadLiftT n o): as for the base lemma Std.Iter.foldM_mapM (checks/ItMonadIterHand.lean): n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value; the WP monad pins the value
theorem Iter.foldM_mapM.h21 : ¬ drop0% Std.Do.Iter.foldM_mapM 21 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Lc) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.foldM_filterWithPostcondition`, idx 10 (LawfulMonad n): as for the base lemma Std.Iter.foldM_filterWithPostcondition (checks/ItMonadIterHand.lean): n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip); the WP monad pins the value
theorem Iter.foldM_filterWithPostcondition.h10 : ¬ drop0% Std.Do.Iter.foldM_filterWithPostcondition 10 := fun h => by
  have := BW.pin fun P Q => h (α := CD) (β := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Do.Iter.foldM_filterWithPostcondition`, idx 18 (LawfulMonadLiftT n o): as for the base lemma Std.Iter.foldM_filterWithPostcondition (checks/ItMonadIterHand.lean): n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value; the WP monad pins the value
theorem Iter.foldM_filterWithPostcondition.h18 : ¬ drop0% Std.Do.Iter.foldM_filterWithPostcondition 18 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.foldM_filterM`, idx 10 (LawfulMonad n): as for the base lemma Std.Iter.foldM_filterM (checks/ItMonadIterHand.lean): n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip); the WP monad pins the value
theorem Iter.foldM_filterM.h10 : ¬ drop0% Std.Do.Iter.foldM_filterM 10 := fun h => by
  have := BW.pin fun P Q => h (α := CD) (β := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Do.Iter.foldM_filterM`, idx 11 (WeaklyLawfulMonadAttach n): as for the base lemma Std.Iter.foldM_filterM (checks/ItMonadIterHand.lean): n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches; the WP monad pins the value
theorem Iter.foldM_filterM.h11 : ¬ drop0% Std.Do.Iter.foldM_filterM 11 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (it := ci 1) (n := Am) (o := L) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.foldM_filterM`, idx 20 (LawfulMonadLiftT n o): as for the base lemma Std.Iter.foldM_filterM (checks/ItMonadIterHand.lean): n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value; the WP monad pins the value
theorem Iter.foldM_filterM.h20 : ¬ drop0% Std.Do.Iter.foldM_filterM 20 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.fold_filterMapM`, idx 11 (WeaklyLawfulMonadAttach n): as for the base lemma Std.Iter.fold_filterMapM (checks/ItMonadIterHand.lean): n = Am (lawful, attach counts 1), it = [0]: only the left side attaches; the WP monad pins the value
theorem Iter.fold_filterMapM.h11 : ¬ drop0% Std.Do.Iter.fold_filterMapM 11 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Am) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.fold_mapM`, idx 11 (WeaklyLawfulMonadAttach n): as for the base lemma Std.Iter.fold_mapM (checks/ItMonadIterHand.lean): n = Am (lawful, attach counts 1), it = [0]: only the left side attaches; the WP monad pins the value
theorem Iter.fold_mapM.h11 : ¬ drop0% Std.Do.Iter.fold_mapM 11 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Am) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Do.Iter.fold_filterM`, idx 10 (WeaklyLawfulMonadAttach n): as for the base lemma Std.Iter.fold_filterM (checks/ItMonadIterHand.lean): n = Am (lawful, attach counts 1), it = [0]: only the left side attaches; the WP monad pins the value
theorem Iter.fold_filterM.h10 : ¬ drop0% Std.Do.Iter.fold_filterM 10 := fun h => by
  have := W.pin fun P Q => h (α := CD) (β := Nat) (it := ci 1) (n := Am) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => d) (P := P) (Q := Q)
  have := congrArg W.c this
  evl this
  omega

end DoSpecBHand.MI
namespace DoSpecBHand.MA.Rem
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

-- helper copied from checks/ItMonadMAHand.lean: Std.IterM.forIn_filterMap, idx 7 (LawfulMonad m): removable. The filterMap iterator's step only binds and returns pure values in m; the lawful lift m → n (LawfulMonadLiftT) and LawfulMonad n turn it into the base step followed by pure, so the induction of the library proof goes through in n.
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

-- helper copied from checks/ItMonadMAHand.lean: Std.IterM.forIn_filter, idx 6 (LawfulMonad m): removable; filter is filterMap with an if-then-else, so it follows from the proof for forIn_filterMap above.
theorem forIn_filter.h6 : drop% Std.IterM.forIn_filter 6 := by
  intro m n α β γ _ _ _ _ _ _ _ _ _ it f init g
  refine (forIn_filterMap.h7 (it := it) (f := fun b => if f b then some b else none)
    (init := init) (g := g)).trans ?_
  congr 1; funext out acc; cases f out <;> rfl

-- helper copied from checks/ItMonadMAHand.lean: Std.IterM.foldM_filterMap, idx 10 (LawfulMonad m): removable; foldM is forIn with a mapped step function, so it follows from the proof for forIn_filterMap above (map_pure in n).
theorem foldM_filterMap.h10 : drop% Std.IterM.foldM_filterMap 10 := by
  intro α β γ δ m n _ _ _ _ _ _ _ _ _ f g init it
  refine (forIn_filterMap.h7 (it := it) (f := f) (init := init)
    (g := fun c acc => ForInStep.yield <$> g acc c)).trans ?_
  show _ = ForIn.forIn it init _
  congr 1; funext out acc; cases h : f out <;> simp [h]

-- helper copied from checks/ItMonadMAHand.lean: Std.IterM.foldM_filter, idx 9 (LawfulMonad m): removable; as for foldM_filterMap, with filter = filterMap of an if-then-else.
theorem foldM_filter.h9 : drop% Std.IterM.foldM_filter 9 := by
  intro α β δ m n _ _ _ _ _ _ _ _ _ f g init it
  refine (forIn_filterMap.h7 (it := it) (f := fun b => if f b then some b else none) (init := init)
    (g := fun c acc => ForInStep.yield <$> g acc c)).trans ?_
  show _ = ForIn.forIn it init _
  congr 1; funext out acc; cases h : f out <;> simp [h]
end DoSpecBHand.MA.Rem

/-! ## Necessary: loop invariant premises (`step`) and `Nonempty β` -/

namespace DoSpecBHand
open Std Std.Do

-- `Std.Do.Spec.forIn'_array`, idx 10 (step): m = Id, xs = #[0], invariant "the prefix is empty": it holds at the start, not at the end, whatever the loop returns
theorem forIn'_array.h10 : ¬ drop0% Std.Do.Spec.forIn'_array 10 := fun h => by
  have := h (m := Id) (ps := .pure) (xs := #[(0:Nat)]) (init := (0:Nat)) (f := fun _ _ b => pure (.yield b))
    (inv := (fun p => ⌜p.1.prefix = []⌝, ()))
  exact (by decide : ¬ #[(0:Nat)].toList = []) (this rfl)

-- `Std.Do.Spec.forIn_array`, idx 10 (step): m = Id, xs = #[0], invariant "the prefix is empty": it holds at the start, not at the end, whatever the loop returns
theorem forIn_array.h10 : ¬ drop0% Std.Do.Spec.forIn_array 10 := fun h => by
  have := h (m := Id) (ps := .pure) (xs := #[(0:Nat)]) (init := (0:Nat)) (f := fun _ b => pure (.yield b))
    (inv := (fun p => ⌜p.1.prefix = []⌝, ()))
  exact (by decide : ¬ #[(0:Nat)].toList = []) (this rfl)

-- `Std.Do.Spec.foldlM_array`, idx 10 (step): m = Id, xs = #[0], invariant "the prefix is empty": it holds at the start, not at the end, whatever the fold returns
theorem foldlM_array.h10 : ¬ drop0% Std.Do.Spec.foldlM_array 10 := fun h => by
  have := h (m := Id) (ps := .pure) (xs := #[(0:Nat)]) (init := (0:Nat)) (f := fun b _ => pure b)
    (inv := (fun p => ⌜p.1.prefix = []⌝, ()))
  exact (by decide : ¬ #[(0:Nat)].toList = []) (this rfl)

-- `Std.Do.Spec.forIn_string`, idx 9 (step): m = Id, s = "a", invariant "the position is the start": it holds at the start, not at the end position
theorem forIn_string.h9 : ¬ drop0% Std.Do.Spec.forIn_string 9 := fun h => by
  have := h (m := Id) (ps := .pure) (s := "a") (init := (0:Nat)) (f := fun _ b => pure (.yield b))
    (inv := (fun p => ⌜p.1 = "a".startPos⌝, ()))
  exact (by decide : ¬ "a".endPos = "a".startPos) (this rfl)

-- `Std.Do.Spec.forIn_stringSlice`, idx 9 (step): m = Id, s = "a" as a slice, invariant "the position is the start": it holds at the start, not at the end position
theorem forIn_stringSlice.h9 : ¬ drop0% Std.Do.Spec.forIn_stringSlice 9 := fun h => by
  have := h (m := Id) (ps := .pure) (s := "a".toSlice) (init := (0:Nat)) (f := fun _ b => pure (.yield b))
    (inv := (fun p => ⌜p.1 = "a".toSlice.startPos⌝, ()))
  exact (by decide : ¬ "a".toSlice.endPos = "a".toSlice.startPos) (this rfl)

-- `Std.Do.Spec.repeatM`, idx 9 (Nonempty β, dependent): β = Empty, α = Unit, m = Id, invariant False on every continue state, so the step premise holds vacuously while Empty is empty
theorem repeatM.h9 : ¬ indep0% Std.Do.Spec.repeatM 9 := fun h => by
  have := h (m := Id) (ps := .pure) (α := Unit) (β := Empty) (init := ()) (f := fun _ => pure (.inl ())) (measure := fun _ => ⟨0⟩)
    (inv := (fun _ => ⌜False⌝, ())) (step := fun _ _ => fun h => h.2.elim)
  exact this.elim (fun e => nomatch e)

-- `Std.Do.Spec.repeatM`, idx 12 (step): m = Id, invariant True on continue states and False on break states: the postcondition is False in Id
theorem repeatM.h12 : ¬ drop0% Std.Do.Spec.repeatM 12 := fun h =>
  id_triple_false _ (h (m := Id) (ps := .pure) (α := Unit) (β := Nat) (init := ()) (f := fun _ => pure (.inr 0)) (measure := fun _ => ⟨0⟩)
    (inv := (fun s => match s with | .inl _ => ⌜True⌝ | .inr _ => ⌜False⌝, ())))

-- `Std.Do.Spec.forIn_loop`, idx 11 (step): m = Id, invariant True on continue states and False on finished states: the postcondition is False in Id
theorem forIn_loop.h11 : ¬ drop0% Std.Do.Spec.forIn_loop 11 := fun h =>
  id_triple_false _ (h (m := Id) (ps := .pure) (β := Nat) (l := Lean.Loop.mk) (init := 0) (f := fun _ b => pure (.done b)) (measure := fun _ => ⟨0⟩)
    (inv := (fun s => match s with | .inl _ => ⌜True⌝ | .inr _ => ⌜False⌝, ())))

end DoSpecBHand

/-! ## Removable: `LawfulMonad m` of the `filterMap`/`filter` fold specs -/

namespace DoSpecBHand.MA

-- `Std.Do.Spec.IterM.foldM_filterMap`, idx 11 (LawfulMonad m): removable; the proof rewrites with the base lemma, whose LawfulMonad m is removable (Rem.foldM_filterMap.h10, from checks/ItMonadMAHand.lean)
theorem IterM.foldM_filterMap.h11 : drop% Std.Do.Spec.IterM.foldM_filterMap 11 := by
  intros; rename_i h; rwa [Rem.foldM_filterMap.h10]

-- `Std.Do.Spec.IterM.foldM_filter`, idx 10 (LawfulMonad m): removable; the proof rewrites with the base lemma, whose LawfulMonad m is removable (Rem.foldM_filter.h9, from checks/ItMonadMAHand.lean)
theorem IterM.foldM_filter.h10 : drop% Std.Do.Spec.IterM.foldM_filter 10 := by
  intros; rename_i h; rwa [Rem.foldM_filter.h9]

end DoSpecBHand.MA
