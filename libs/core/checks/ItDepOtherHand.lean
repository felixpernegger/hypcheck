import Lean

/-!
Hand pass `ItDepOther` (hand8): 188 open hypotheses of `Init.Data.Iterators` theorems, 85 dependent
(`Finite`/`Productive`/`LawfulDeterministicIterator`/`LawfulMonad`/`WeaklyLawfulMonadAttach`
instances the statement uses, `hP`-style invariants, `ita = itb`, ...) and 103 non-dependent ones.
For hypothesis `hᵢ` of theorem `T` this file proves `¬T'` (`drop0% T i`) or, for a dependent
hypothesis, `¬∀ indep, Hᵢ` (`indep0% T i`, all independent binders). `drop0%`/`indep0%` are
`drop%`/`indep%` with all universe parameters set to `0`.

187 necessary, 0 removable. One row is opaque (`runs/hand8/ItDepOther_opaque.jsonl`):
`IterM.DefaultConsumers.forIn'_eq_forIn'` without `wf`, where both sides are `opaqueFix` terms.

Reusable counterexamples (section "Models"):
* iterators (all `Iterator _ m Nat` for any `[Pure m]`, state wrapped in a structure):
  `CD` countdown (state `n+1` yields `n`; finite, productive, deterministic, `CD.finRel`,
  `CD.prodRel`), `SK` (skips down to `0`; productive), `SY` (`k+2` skips, `1` yields, `0` done),
  `LP` (skips to itself: deterministic, neither finite nor productive), `YL` (yields `0` and stays:
  productive, not finite), `ND` (state `true` may be done or yield; `step` is always done: finite,
  not `LawfulDeterministicIterator`);
* loops: default `IteratorLoop` instances with `LawfulIteratorLoop` (by `rfl`) for `CD`, `LP`, `ND`,
  `YL`; `CD.firstLoop` (only applies `f` to the first output, computable), `CD.preLoop` (lawful only
  for lawful lifts), `LP.wfLoop k` (default loop if well-founded, else `modify (· + k)`);
* monads and lifts: `CM` (`Nat × α`, bind adds `1`: not lawful, trivial `MonadAttach` weakly
  lawful), `SM` (`StateM Nat` with an `attach` that increments: lawful, not weakly lawful),
  `cntLiftBind`/`cntLift` (lift `Id → StateM Nat` that increments first), `postCnt` (increments after
  the continuation);
* the tactic `inv h` inverts the plausible-step relations of `flatMap`/`map`/`take` down to `CD`.

Run with the lean4 repo's stage1 binary: `lean checks/ItDepOtherHand.lean`.
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

namespace ItDepOtherHand
open Std Std.Iterators

theorem wf_irrefl {α : Sort u} {r : α → α → Prop} (h : WellFounded r) (a : α) : ¬ r a a := by
  have := h.apply a
  induction this with
  | intro x _ ih => exact fun hx => ih x hx hx

/-! Countdown iterator `CD`: state `n+1` yields `n` and moves to `n`; state `0` is done. -/
structure CD where n : Nat

def CD.stepv {m : Type → Type} (n : Nat) : IterStep (IterM (α := CD) m Nat) Nat :=
  match n with
  | 0 => .done
  | k + 1 => .yield ⟨⟨k⟩⟩ k

instance CD.inst {m : Type → Type} [Pure m] : Iterator CD m Nat where
  IsPlausibleStep it s := s = CD.stepv it.internalState.n
  step it := pure (.deflate ⟨CD.stepv it.internalState.n, rfl⟩)

@[simp] theorem CD.ps {m : Type → Type} [Pure m] {it : IterM (α := CD) m Nat} {s} :
    it.IsPlausibleStep s ↔ s = CD.stepv it.internalState.n := Iff.rfl

def CD.finRel {m : Type → Type} [Pure m] : FinitenessRelation CD m where
  Rel := InvImage (· < ·) (fun it => it.internalState.n)
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation := by
    rintro ⟨⟨n⟩⟩ ⟨⟨k⟩⟩ ⟨s, hs, hp⟩
    cases n <;> simp_all [CD.stepv, InvImage]

instance CD.finite {m : Type → Type} [Pure m] : Finite CD m := .of_finitenessRelation CD.finRel

def CD.prodRel {m : Type → Type} [Pure m] : ProductivenessRelation CD m where
  Rel := InvImage (· < ·) (fun it => it.internalState.n)
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation := by
    rintro ⟨⟨n⟩⟩ ⟨⟨k⟩⟩ hp
    cases n <;> simp_all [IterM.IsPlausibleSkipSuccessorOf, CD.stepv]

instance CD.det {m : Type → Type} [Pure m] : LawfulDeterministicIterator CD m :=
  ⟨fun _ => ⟨_, rfl⟩⟩

theorem CD.no_succ0 {m : Type → Type} [Pure m] (it' : IterM (α := CD) m Nat) :
    ¬ it'.IsPlausibleSuccessorOf ⟨⟨0⟩⟩ := by
  rintro ⟨s, hs, hp⟩
  simp [CD.stepv] at hp
  subst hp; simp at hs

theorem CD.no_out0 {m : Type → Type} [Pure m] (out : Nat) :
    ¬ (⟨⟨0⟩⟩ : IterM (α := CD) m Nat).IsPlausibleIndirectOutput out := by
  intro h
  cases h with
  | direct h =>
    obtain ⟨it', h⟩ := h
    simp [CD.stepv] at h
  | indirect h _ => exact CD.no_succ0 _ h

theorem CD.indSucc0 {m : Type → Type} [Pure m] (it' : IterM (α := CD) m Nat)
    (h : it'.IsPlausibleIndirectSuccessorOf ⟨⟨0⟩⟩) : it' = ⟨⟨0⟩⟩ := by
  cases h with
  | refl => rfl
  | cons_right _ h => exact absurd h (CD.no_succ0 _)

theorem CD.out1 {m : Type → Type} [Pure m] :
    (⟨⟨1⟩⟩ : IterM (α := CD) m Nat).IsPlausibleIndirectOutput 0 :=
  .direct ⟨⟨⟨0⟩⟩, rfl⟩

/-! Skip loop `LP`: every state skips to itself (neither productive nor finite). -/
structure LP where u : Unit

instance LP.inst {m : Type → Type} [Pure m] : Iterator LP m Nat where
  IsPlausibleStep it s := s = .skip it
  step it := pure (.deflate ⟨.skip it, rfl⟩)

instance LP.det {m : Type → Type} [Pure m] : LawfulDeterministicIterator LP m :=
  ⟨fun _ => ⟨_, rfl⟩⟩

@[simp] theorem LP.ps {m : Type → Type} [Pure m] {it : IterM (α := LP) m Nat} {s} :
    it.IsPlausibleStep s ↔ s = .skip it := Iff.rfl

theorem LP.not_productive {m : Type → Type} [Pure m] : ¬ Productive LP m :=
  fun h => wf_irrefl h.wf ⟨⟨()⟩⟩ rfl

theorem LP.not_finite {m : Type → Type} [Pure m] : ¬ Finite LP m :=
  fun h => wf_irrefl h.wf ⟨⟨()⟩⟩ ⟨_, rfl, rfl⟩

/-! Yield loop `YL`: every state yields `0` and stays (productive, not finite). -/
structure YL where u : Unit

instance YL.inst {m : Type → Type} [Pure m] : Iterator YL m Nat where
  IsPlausibleStep it s := s = .yield it 0
  step it := pure (.deflate ⟨.yield it 0, rfl⟩)

@[simp] theorem YL.ps {m : Type → Type} [Pure m] {it : IterM (α := YL) m Nat} {s} :
    it.IsPlausibleStep s ↔ s = .yield it 0 := Iff.rfl

instance YL.productive {m : Type → Type} [Pure m] : Productive YL m :=
  ⟨⟨fun a => ⟨a, fun b h => by cases h⟩⟩⟩

theorem YL.not_finite {m : Type → Type} [Pure m] : ¬ Finite YL m :=
  fun h => wf_irrefl h.wf ⟨⟨()⟩⟩ ⟨_, rfl, rfl⟩

/-! Nondeterministic `ND`: state `true` may be done or yield `0` (to `false`); `step` is always done. -/
structure ND where b : Bool

instance ND.inst {m : Type → Type} [Pure m] : Iterator ND m Nat where
  IsPlausibleStep it s := s = .done ∨ (it.internalState.b = true ∧ s = .yield ⟨⟨false⟩⟩ 0)
  step it := pure (.deflate ⟨.done, Or.inl rfl⟩)

@[simp] theorem ND.ps {m : Type → Type} [Pure m] {it : IterM (α := ND) m Nat} {s} :
    it.IsPlausibleStep s ↔ (s = .done ∨ (it.internalState.b = true ∧ s = .yield ⟨⟨false⟩⟩ 0)) := Iff.rfl

instance ND.finite {m : Type → Type} [Pure m] : Finite ND m := .of_finitenessRelation {
  Rel := InvImage (· < ·) (fun it => if it.internalState.b then 1 else 0)
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation := by
    rintro ⟨⟨n⟩⟩ ⟨⟨k⟩⟩ ⟨s, hs, hp⟩
    rcases hp with rfl | ⟨h1, rfl⟩
    · simp at hs
    · simp at hs; cases hs; simp_all [InvImage] }

theorem ND.not_det {m : Type → Type} [Pure m] : ¬ LawfulDeterministicIterator ND m := by
  rintro ⟨h⟩
  obtain ⟨s, hs⟩ := h ⟨⟨true⟩⟩
  have h1 : IterStep.done = s := (congrFun hs .done) ▸ Or.inl rfl
  have h2 : IterStep.yield ⟨⟨false⟩⟩ 0 = s := (congrFun hs (.yield ⟨⟨false⟩⟩ 0)) ▸ Or.inr ⟨rfl, rfl⟩
  rw [← h1] at h2; cases h2

abbrev c (n : Nat) : IterM (α := CD) Id Nat := ⟨⟨n⟩⟩
abbrev ci (n : Nat) : Iter (α := CD) Nat := ⟨⟨n⟩⟩

theorem CD.no_succ0' (it' : Iter (α := CD) Nat) : ¬ it'.IsPlausibleSuccessorOf (ci 0) :=
  CD.no_succ0 (m := Id) _

theorem CD.indSucc0' (it' : Iter (α := CD) Nat)
    (h : it'.IsPlausibleIndirectSuccessorOf (ci 0)) : it' = ci 0 := by
  rw [Iter.isPlausibleIndirectSuccessor_iff_isPlausibleIndirectSuccessor_toIterM] at h
  have := CD.indSucc0 _ h
  cases it'; cases this; rfl

theorem CD.no_out0' (out : Nat) : ¬ (ci 0).IsPlausibleIndirectOutput out := by
  rw [Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM]
  exact CD.no_out0 (m := Id) out

theorem CD.out1' : (ci 1).IsPlausibleIndirectOutput 0 := by
  rw [Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM]
  exact CD.out1 (m := Id)

/-- The last step of a `TransGen` chain ending in `CD` state `0` would be a successor of state `0`. -/
theorem CD.no_rel0 (a : IterM.TerminationMeasures.Finite CD Id) : ¬ a.Rel ⟨c 0⟩ := by
  intro h
  cases h with
  | single h => exact CD.no_succ0 _ h
  | tail _ h => exact CD.no_succ0 _ h

theorem CD.no_prel0 (a : IterM.TerminationMeasures.Productive CD Id) : ¬ a.Rel ⟨c 0⟩ := by
  intro h
  cases h with
  | single h => simp [IterM.IsPlausibleSkipSuccessorOf, InvImage, CD.stepv] at h
  | tail _ h => simp [IterM.IsPlausibleSkipSuccessorOf, InvImage, CD.stepv] at h

theorem CD.rel01 : (⟨c 0⟩ : IterM.TerminationMeasures.Finite CD Id).Rel ⟨c 1⟩ :=
  .single ⟨_, rfl, rfl⟩

theorem fin_rel_irrefl {α : Type} {m : Type → Type} {β : Type} [Iterator α m β] [Finite α m]
    (a : IterM.TerminationMeasures.Finite α m) : ¬ a.Rel a :=
  wf_irrefl (IterM.TerminationMeasures.instWellFoundedRelationFinite (α := α) (m := m)).wf a

theorem prod_rel_irrefl {α : Type} {m : Type → Type} {β : Type} [Iterator α m β] [Productive α m]
    (a : IterM.TerminationMeasures.Productive α m) : ¬ a.Rel a :=
  wf_irrefl (IterM.TerminationMeasures.instWellFoundedRelationProductive (α := α) (m := m)).wf a


/-! Default `IteratorLoop` instances (lawful by definition). -/
instance CD.loop {m : Type → Type} {n : Type → Type} [Pure m] [Monad n] : IteratorLoop CD m n :=
  .defaultImplementation
instance CD.lawfulLoop {m n : Type → Type} [Monad m] [Monad n] : LawfulIteratorLoop CD m n :=
  ⟨fun _ _ _ _ _ _ _ _ => rfl⟩
instance LP.loop {m : Type → Type} {n : Type → Type} [Pure m] [Monad n] : IteratorLoop LP m n :=
  .defaultImplementation
instance LP.lawfulLoop {m n : Type → Type} [Monad m] [Monad n] : LawfulIteratorLoop LP m n :=
  ⟨fun _ _ _ _ _ _ _ _ => rfl⟩
instance ND.loop {m : Type → Type} {n : Type → Type} [Pure m] [Monad n] : IteratorLoop ND m n :=
  .defaultImplementation
instance ND.lawfulLoop {m n : Type → Type} [Monad m] [Monad n] : LawfulIteratorLoop ND m n :=
  ⟨fun _ _ _ _ _ _ _ _ => rfl⟩

/-! `CM`: writer-like monad `Nat × α` whose `bind` adds `1` to the counter; `map` is the lawful
`Prod.map id`, so the trivial `MonadAttach` is weakly lawful, but `pure_bind` fails. -/
def CM (α : Type) : Type := Nat × α

instance CM.monad : Monad CM where
  pure a := ((0 : Nat), a)
  bind x f := (((f x.2) : Nat × _).1 + (x : Nat × _).1 + 1, ((f x.2) : Nat × _).2)
  map f x := ((x : Nat × _).1, f (x : Nat × _).2)

instance CM.attach : MonadAttach CM := .trivial

instance CM.weakly : WeaklyLawfulMonadAttach CM := ⟨fun {_ x} => rfl⟩

theorem CM.not_lawful : ¬ LawfulMonad CM := fun h => by
  have := @pure_bind CM _ h _ _ 0 (fun a => (((0 : Nat), a) : Nat × Nat))
  cases this

/-! `SM`: `StateM Nat` (lawful) with a `MonadAttach` whose `attach` increments the state, so
`WeaklyLawfulMonadAttach` fails. -/
def SM (α : Type) : Type := StateM Nat α
instance SM.monad : Monad SM := inferInstanceAs (Monad (StateM Nat))
instance SM.lawful : LawfulMonad SM := inferInstanceAs (LawfulMonad (StateM Nat))
instance SM.attach : MonadAttach SM where
  CanReturn _ _ := True
  attach x := (⟨·, .intro⟩) <$> ((modify (· + 1) : StateM Nat PUnit) *> (x : StateM Nat _))

theorem SM.not_weakly : ¬ WeaklyLawfulMonadAttach SM := fun ⟨h⟩ => by
  have := congrArg (fun y : SM Nat => (y : StateM Nat Nat).run 0) (@h Nat (pure 0))
  cases this

instance CD.productive {m : Type → Type} [Pure m] : Productive CD m :=
  .of_productivenessRelation CD.prodRel

/-! Skip countdown `SK`: state `n+1` skips to `n`; state `0` is done (finite, productive). -/
structure SK where n : Nat

def SK.stepv {m : Type → Type} (n : Nat) : IterStep (IterM (α := SK) m Nat) Nat :=
  match n with
  | 0 => .done
  | k + 1 => .skip ⟨⟨k⟩⟩

instance SK.inst {m : Type → Type} [Pure m] : Iterator SK m Nat where
  IsPlausibleStep it s := s = SK.stepv it.internalState.n
  step it := pure (.deflate ⟨SK.stepv it.internalState.n, rfl⟩)

@[simp] theorem SK.ps {m : Type → Type} [Pure m] {it : IterM (α := SK) m Nat} {s} :
    it.IsPlausibleStep s ↔ s = SK.stepv it.internalState.n := Iff.rfl

instance SK.productive {m : Type → Type} [Pure m] : Productive SK m := .of_productivenessRelation {
  Rel := InvImage (· < ·) (fun it => it.internalState.n)
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation := by
    rintro ⟨⟨n⟩⟩ ⟨⟨k⟩⟩ hp
    cases n <;> simp_all [IterM.IsPlausibleSkipSuccessorOf, SK.stepv, InvImage] }

theorem SK.prel01 : (⟨⟨⟨0⟩⟩⟩ : IterM.TerminationMeasures.Productive SK Id).Rel ⟨⟨⟨1⟩⟩⟩ :=
  .single rfl

instance YL.loop {m : Type → Type} {n : Type → Type} [Pure m] [Monad n] : IteratorLoop YL m n :=
  .defaultImplementation

theorem lex_irrefl {α β : Type} {r : α → α → Prop} {s : β → β → Prop}
    (hr : ∀ a, ¬ r a a) (hs : ∀ b, ¬ s b b) (p : α × β) : ¬ Prod.Lex r s p p := by
  intro h
  rcases Prod.lex_def.1 h with h | ⟨_, h⟩
  · exact hr _ h
  · exact hs _ h

/-- Counting lift `Id → StateM Nat`: increments the state before continuing. -/
def cntLiftBind (γ δ : Type) (f : γ → StateM Nat δ) (x : Id γ) : StateM Nat δ :=
  (modify (· + 1) : StateM Nat PUnit) *> f x.run

theorem option_lt_irrefl {α : Type} {r : α → α → Prop} (hr : ∀ a, ¬ r a a) (a : Option α) :
    ¬ Option.lt r a a := by
  cases a with
  | none => exact id
  | some a => exact hr a

/-- Counting lift `Id → StateM Nat` as a `MonadLift` (not lawful). -/
@[reducible] def cntLift : MonadLift Id (StateM Nat) :=
  ⟨fun x => (modify (· + 1) : StateM Nat PUnit) *> pure x.run⟩

/-! `SY`: state `k+2` skips to `k+1`, state `1` yields `0` (to `0`), state `0` is done. -/
structure SY where n : Nat

def SY.stepv {m : Type → Type} (n : Nat) : IterStep (IterM (α := SY) m Nat) Nat :=
  match n with
  | 0 => .done
  | 1 => .yield ⟨⟨0⟩⟩ 0
  | k + 2 => .skip ⟨⟨k + 1⟩⟩

instance SY.inst {m : Type → Type} [Pure m] : Iterator SY m Nat where
  IsPlausibleStep it s := s = SY.stepv it.internalState.n
  step it := pure (.deflate ⟨SY.stepv it.internalState.n, rfl⟩)

instance SY.productive {m : Type → Type} [Pure m] : Productive SY m := .of_productivenessRelation {
  Rel := InvImage (· < ·) (fun it => it.internalState.n)
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation := by
    rintro ⟨⟨n⟩⟩ ⟨⟨k⟩⟩ hp
    change IterStep.skip _ = SY.stepv n at hp
    match n, hp with
    | k + 2, hp => cases hp; exact Nat.lt_succ_self _ }

@[simp] theorem CD.step_eq {m : Type → Type} [Pure m] (it : IterM (α := CD) m Nat) :
    it.step = pure (Shrink.deflate (⟨CD.stepv it.internalState.n, rfl⟩ : it.Step)) := rfl
@[simp] theorem LP.step_eq {m : Type → Type} [Pure m] (it : IterM (α := LP) m Nat) :
    it.step = pure (Shrink.deflate (⟨.skip it, rfl⟩ : it.Step)) := rfl

set_option warn.classDefReducibility false

/-- A loop over `CD` that only looks at the first output: `f` applied to it (or `init` if there is none). -/
def CD.firstLoop {n : Type → Type} [Monad n] : IteratorLoop CD Id n where
  forIn _ γ Pl it init f :=
    match h : it.internalState.n with
    | 0 => pure init
    | k + 1 => (fun r => r.val.value) <$> f k (.direct ⟨⟨⟨k⟩⟩, by simp [CD.stepv, h]⟩) init

/-- The default loop, preceded by a lift of `pure ()`: lawful for lawful lifts only. -/
def CD.preLoop {n : Type → Type} [Monad n] : IteratorLoop CD Id n where
  forIn lift γ Pl it init f :=
    lift PUnit γ (fun _ => (IteratorLoop.defaultImplementation (α := CD) (m := Id) (n := n)).forIn
      lift γ Pl it init f) (pure PUnit.unit)

theorem CD.preLoop_lawful {n : Type → Type} [Monad n] :
    @LawfulIteratorLoop Nat CD Id n _ _ _ CD.preLoop :=
  @LawfulIteratorLoop.mk Nat CD Id n _ _ _ CD.preLoop
    (fun _ _ _ _ _ _ _ _ => Internal.LawfulMonadLiftBindFunction.liftBind_pure _ _)

open Classical in
/-- The default loop when the loop relation is well-founded, otherwise `modify (· + k)` and `init`. -/
noncomputable def LP.wfLoop (k : Nat) : IteratorLoop LP Id (StateM Nat) where
  forIn lift γ Pl it init f :=
    if IteratorLoop.WellFounded LP Id Pl then
      (IteratorLoop.defaultImplementation (α := LP) (m := Id) (n := StateM Nat)).forIn lift γ Pl it init f
    else (modify (· + k) : StateM Nat PUnit) *> pure init

theorem LP.wfLoop_lawful (k : Nat) : @LawfulIteratorLoop Nat LP Id (StateM Nat) _ _ _ (LP.wfLoop k) :=
  @LawfulIteratorLoop.mk Nat LP Id (StateM Nat) _ _ _ (LP.wfLoop k) (fun _ _ _ _ _ _ wf _ => if_pos wf)

theorem LP.not_wf {n : Type → Type} {γ : Type} (c : γ) :
    ¬ IteratorLoop.WellFounded LP Id (γ := γ) (fun _ _ _ => True) :=
  fun h => wf_irrefl h (⟨⟨()⟩⟩, c) (Or.inr ⟨rfl, rfl⟩)

/-- Lift `Id → StateM Nat` that runs the continuation and then increments the state. -/
def postCnt (γ δ : Type) (k : γ → StateM Nat δ) (x : Id γ) : StateM Nat δ :=
  do let r ← k x.run; modify (· + 1); pure r

theorem CD.preLoop_forIn {n : Type → Type} [Monad n] lift γ Pl it (init : γ) f :
    (CD.preLoop (n := n)).forIn lift γ Pl it init f =
      lift PUnit γ (fun _ => IterM.DefaultConsumers.forIn' lift γ Pl it init _ (fun _ => id) f)
        (pure PUnit.unit) := rfl

theorem LP.wfLoop_forIn_nwf (k : Nat) lift γ (Pl : Nat → γ → ForInStep γ → Prop) it (init : γ) f
    (h : ¬ IteratorLoop.WellFounded LP Id Pl) :
    (LP.wfLoop k).forIn lift γ Pl it init f = (modify (· + k) : StateM Nat PUnit) *> pure init := by
  exact if_neg h

theorem CD.default_forIn {n : Type → Type} [Monad n] lift γ Pl it (init : γ) f :
    (IteratorLoop.defaultImplementation (α := CD) (m := Id) (n := n)).forIn lift γ Pl it init f =
      IterM.DefaultConsumers.forIn' lift γ Pl it init _ (fun _ => id) f := rfl

/-! ## Basic: plausibility relations (countdown `CD`) -/

-- `Std.IterM.IsPlausibleIndirectSuccessorOf.trans`, idx 7 (h'): `it'' = 1`, `it' = it = 0`
theorem IterM.IsPlausibleIndirectSuccessorOf.trans.h7 :
    ¬ drop0% Std.IterM.IsPlausibleIndirectSuccessorOf.trans 7 := fun h => by
  have := CD.indSucc0 _ (h (it'' := c 1) (it' := c 0) (it := c 0) (.refl _)); cases this

-- `Std.IterM.IsPlausibleIndirectSuccessorOf.trans`, idx 8 (h): `it'' = it' = 1`, `it = 0`
theorem IterM.IsPlausibleIndirectSuccessorOf.trans.h8 :
    ¬ drop0% Std.IterM.IsPlausibleIndirectSuccessorOf.trans 8 := fun h => by
  have := CD.indSucc0 _ (h (it'' := c 1) (it' := c 1) (it := c 0) (.refl _)); cases this

-- `Std.IterM.IsPlausibleIndirectSuccessorOf.single`, idx 6 (h): `it' = 1`, `it = 0`
theorem IterM.IsPlausibleIndirectSuccessorOf.single.h6 :
    ¬ drop0% Std.IterM.IsPlausibleIndirectSuccessorOf.single 6 := fun h => by
  have := CD.indSucc0 _ (h (it' := c 1) (it := c 0)); cases this

-- `Std.IterM.IsPlausibleIndirectOutput.trans`, idx 7 (h): `it' = 1` outputs `0`, `it = 0` outputs nothing
theorem IterM.IsPlausibleIndirectOutput.trans.h7 :
    ¬ drop0% Std.IterM.IsPlausibleIndirectOutput.trans 7 := fun h =>
  CD.no_out0 _ (h (it' := c 1) (it := c 0) (out := 0) CD.out1)

-- `Std.IterM.IsPlausibleIndirectOutput.trans`, idx 8 (h'): `it' = it = 0` outputs nothing
theorem IterM.IsPlausibleIndirectOutput.trans.h8 :
    ¬ drop0% Std.IterM.IsPlausibleIndirectOutput.trans 8 := fun h =>
  CD.no_out0 _ (h (it' := c 0) (it := c 0) (out := 0) (.refl _))

-- `Std.Iter.IsPlausibleIndirectSuccessorOf.trans`, idx 6 (h'): `it'' = 1`, `it' = it = 0`
theorem Iter.IsPlausibleIndirectSuccessorOf.trans.h6 :
    ¬ drop0% Std.Iter.IsPlausibleIndirectSuccessorOf.trans 6 := fun h => by
  have := CD.indSucc0' _ (h (it'' := ci 1) (it' := ci 0) (it := ci 0) (.refl _)); cases this

-- `Std.Iter.IsPlausibleIndirectSuccessorOf.trans`, idx 7 (h): `it'' = it' = 1`, `it = 0`
theorem Iter.IsPlausibleIndirectSuccessorOf.trans.h7 :
    ¬ drop0% Std.Iter.IsPlausibleIndirectSuccessorOf.trans 7 := fun h => by
  have := CD.indSucc0' _ (h (it'' := ci 1) (it' := ci 1) (it := ci 0) (.refl _)); cases this

-- `Std.Iter.IsPlausibleIndirectOutput.trans`, idx 6 (h): `it' = 1` outputs `0`, `it = 0` outputs nothing
theorem Iter.IsPlausibleIndirectOutput.trans.h6 :
    ¬ drop0% Std.Iter.IsPlausibleIndirectOutput.trans 6 := fun h =>
  CD.no_out0' _ (h (it' := ci 1) (it := ci 0) (out := 0) CD.out1')

-- `Std.Iter.IsPlausibleIndirectOutput.trans`, idx 7 (h'): `it' = it = 0` outputs nothing
theorem Iter.IsPlausibleIndirectOutput.trans.h7 :
    ¬ drop0% Std.Iter.IsPlausibleIndirectOutput.trans 7 := fun h =>
  CD.no_out0' _ (h (it' := ci 0) (it := ci 0) (out := 0) (.refl _))

-- `Std.IterM.Step.toPure_yield`, idx 6 (h, dependent): state `0` only plausibly steps to `done`
theorem IterM.Step.toPure_yield.h6 : ¬ indep0% Std.IterM.Step.toPure_yield 6 := fun h => by
  have := h (it := c 0) (it' := c 0) (out := 0); simp [CD.stepv] at this

-- `Std.IterM.Step.toPure_skip`, idx 5 (h, dependent): state `0` only plausibly steps to `done`
theorem IterM.Step.toPure_skip.h5 : ¬ indep0% Std.IterM.Step.toPure_skip 5 := fun h => by
  have := h (it := c 0) (it' := c 0); simp [CD.stepv] at this

-- `Std.IterM.Step.toPure_done`, idx 4 (h, dependent): state `1` only plausibly yields
theorem IterM.Step.toPure_done.h4 : ¬ indep0% Std.IterM.Step.toPure_done 4 := fun h => by
  have := h (it := c 1); simp [CD.stepv] at this

-- `Std.Iter.IsPlausibleStep.isPlausibleSuccessor_of_yield`, idx 6 (h): state `0` has no successor
theorem Iter.IsPlausibleStep.isPlausibleSuccessor_of_yield.h6 :
    ¬ drop0% Std.Iter.IsPlausibleStep.isPlausibleSuccessor_of_yield 6 := fun h =>
  CD.no_succ0' _ (h (it' := ci 0) (it := ci 0) (out := 0))

-- `Std.Iter.IsPlausibleStep.isPlausibleSuccessor_of_skip`, idx 5 (h): state `0` has no successor
theorem Iter.IsPlausibleStep.isPlausibleSuccessor_of_skip.h5 :
    ¬ drop0% Std.Iter.IsPlausibleStep.isPlausibleSuccessor_of_skip 5 := fun h =>
  CD.no_succ0' _ (h (it' := ci 0) (it := ci 0))

-- `Std.IterM.isPlausibleSuccessorOf_of_yield`, idx 7 (h): state `0` has no successor
theorem IterM.isPlausibleSuccessorOf_of_yield.h7 :
    ¬ drop0% Std.IterM.isPlausibleSuccessorOf_of_yield 7 := fun h =>
  CD.no_succ0 _ (h (it' := c 0) (it := c 0) (out := 0))

-- `Std.IterM.isPlausibleSuccessorOf_of_skip`, idx 6 (h): state `0` has no successor
theorem IterM.isPlausibleSuccessorOf_of_skip.h6 :
    ¬ drop0% Std.IterM.isPlausibleSuccessorOf_of_skip 6 := fun h =>
  CD.no_succ0 _ (h (it' := c 0) (it := c 0))

-- `Std.IterM.TerminationMeasures.Finite.rel_of_yield`, idx 7 (h): nothing precedes state `0`
theorem IterM.TerminationMeasures.Finite.rel_of_yield.h7 :
    ¬ drop0% Std.IterM.TerminationMeasures.Finite.rel_of_yield 7 := fun h =>
  CD.no_rel0 _ (h (it := c 0) (it' := c 0) (out := 0))

-- `Std.IterM.TerminationMeasures.Finite.rel_of_skip`, idx 6 (h): nothing precedes state `0`
theorem IterM.TerminationMeasures.Finite.rel_of_skip.h6 :
    ¬ drop0% Std.IterM.TerminationMeasures.Finite.rel_of_skip 6 := fun h =>
  CD.no_rel0 _ (h (it := c 0) (it' := c 0))

-- `Std.Iter.TerminationMeasures.Finite.rel_of_yield`, idx 6 (h): nothing precedes state `0`
theorem Iter.TerminationMeasures.Finite.rel_of_yield.h6 :
    ¬ drop0% Std.Iter.TerminationMeasures.Finite.rel_of_yield 6 := fun h =>
  CD.no_rel0 _ (h (it := ci 0) (it' := ci 0) (out := 0))

-- `Std.Iter.TerminationMeasures.Finite.rel_of_skip`, idx 5 (h): nothing precedes state `0`
theorem Iter.TerminationMeasures.Finite.rel_of_skip.h5 :
    ¬ drop0% Std.Iter.TerminationMeasures.Finite.rel_of_skip 5 := fun h =>
  CD.no_rel0 _ (h (it := ci 0) (it' := ci 0))

-- `Std.IterM.TerminationMeasures.Finite.rel_trans`, idx 7 (first a): `it = it'' = 1`, `it' = 0`
theorem IterM.TerminationMeasures.Finite.rel_trans.h7 :
    ¬ drop0% Std.IterM.TerminationMeasures.Finite.rel_trans 7 := fun h =>
  fin_rel_irrefl _ (h (it := ⟨c 1⟩) (it' := ⟨c 0⟩) (it'' := ⟨c 1⟩) CD.rel01)

-- `Std.IterM.TerminationMeasures.Finite.rel_trans`, idx 8 (second a): `it = it'' = 0`, `it' = 1`
theorem IterM.TerminationMeasures.Finite.rel_trans.h8 :
    ¬ drop0% Std.IterM.TerminationMeasures.Finite.rel_trans 8 := fun h =>
  fin_rel_irrefl _ (h (it := ⟨c 0⟩) (it' := ⟨c 1⟩) (it'' := ⟨c 0⟩) CD.rel01)

-- `Std.IterM.TerminationMeasures.Finite.Rel.of_productive`, idx 6 (a): `a = b`, the relation is irreflexive
theorem IterM.TerminationMeasures.Finite.Rel.of_productive.h6 :
    ¬ drop0% Std.IterM.TerminationMeasures.Finite.Rel.of_productive 6 := fun h =>
  fin_rel_irrefl _ (h (a := ⟨c 0⟩) (b := ⟨c 0⟩))

-- `Std.IterM.TerminationMeasures.Productive.rel_of_skip`, idx 6 (h): `it = it'`, the relation is irreflexive
theorem IterM.TerminationMeasures.Productive.rel_of_skip.h6 :
    ¬ drop0% Std.IterM.TerminationMeasures.Productive.rel_of_skip 6 := fun h =>
  prod_rel_irrefl _ (h (it := c 0) (it' := c 0))

-- `Std.Iter.TerminationMeasures.Productive.rel_of_skip`, idx 5 (h): `it = it'`, the relation is irreflexive
theorem Iter.TerminationMeasures.Productive.rel_of_skip.h5 :
    ¬ drop0% Std.Iter.TerminationMeasures.Productive.rel_of_skip 5 := fun h =>
  prod_rel_irrefl _ (h (it := ci 0) (it' := ci 0))

-- `Std.LawfulDeterministicIterator.isPlausibleStep_eq_eq`, idx 4 (self): `ND` state `true` has two plausible steps
theorem LawfulDeterministicIterator.isPlausibleStep_eq_eq.h4 :
    ¬ drop0% Std.LawfulDeterministicIterator.isPlausibleStep_eq_eq 4 := fun h =>
  ND.not_det (m := Id) ⟨fun it => h (α := ND) (m := Id) it⟩

-- `Std.Iterators.FinitenessRelation.subrelation`, idx 7 (a): `CD.finRel` (`n' < n`) with `n' = 5`, `n = 0`
theorem Iterators.FinitenessRelation.subrelation.h7 :
    ¬ drop0% Std.Iterators.FinitenessRelation.subrelation 7 := fun h => by
  have := h (self := CD.finRel (m := Id)) (it := c 0) (it' := c 5)
  simp [CD.finRel, InvImage] at this

-- `Std.Iterators.ProductivenessRelation.subrelation`, idx 7 (a): `CD.prodRel` (`n' < n`) with `n' = 5`, `n = 0`
theorem Iterators.ProductivenessRelation.subrelation.h7 :
    ¬ drop0% Std.Iterators.ProductivenessRelation.subrelation 7 := fun h => by
  have := h (self := CD.prodRel (m := Id)) (it := c 0) (it' := c 5)
  simp [CD.prodRel, InvImage] at this

/-! ## Dependent instance hypotheses: `Finite`/`Productive`/`LawfulDeterministicIterator`/monad laws -/

-- `Std.Iter.toList_attachWith`, idx 6 (inst): `LP` (skips forever) is not finite
theorem Iter.toList_attachWith.h6 : ¬ indep0% Std.Iter.toList_attachWith 6 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩) (P := fun _ => True) (hP := fun _ _ => trivial))

-- `Std.Iter.toListRev_attachWith`, idx 6 (inst): `LP` (skips forever) is not finite
theorem Iter.toListRev_attachWith.h6 : ¬ indep0% Std.Iter.toListRev_attachWith 6 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩) (P := fun _ => True) (hP := fun _ _ => trivial))

-- `Std.Iter.toArray_attachWith`, idx 6 (inst): `LP` (skips forever) is not finite
theorem Iter.toArray_attachWith.h6 : ¬ indep0% Std.Iter.toArray_attachWith 6 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩) (P := fun _ => True) (hP := fun _ _ => trivial))

-- `Std.IterM.step_toTake`, idx 5 (inst): `LP` (skips forever) is not finite
theorem IterM.step_toTake.h5 : ¬ indep0% Std.IterM.step_toTake 5 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (it := ⟨⟨()⟩⟩))

-- `Std.IterM.toList_toTake`, idx 6 (inst): `LP` (skips forever) is not finite
theorem IterM.toList_toTake.h6 : ¬ indep0% Std.IterM.toList_toTake 6 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.toTake_eq_toIter_toTake_toIterM`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.toTake_eq_toIter_toTake_toIterM.h3 : ¬ indep0% Std.Iter.toTake_eq_toIter_toTake_toIterM 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.step_toTake`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.step_toTake.h3 : ¬ indep0% Std.Iter.step_toTake 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.toList_toTake`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.toList_toTake.h3 : ¬ indep0% Std.Iter.toList_toTake 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.toArray_ensureTermination`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.toArray_ensureTermination.h3 : ¬ indep0% Std.Iter.toArray_ensureTermination 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.toList_ensureTermination`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.toList_ensureTermination.h3 : ¬ indep0% Std.Iter.toList_ensureTermination 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.toListRev_ensureTermination_eq_toListRev`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.toListRev_ensureTermination_eq_toListRev.h3 : ¬ indep0% Std.Iter.toListRev_ensureTermination_eq_toListRev 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.toList_toArray_ensureTermination`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.toList_toArray_ensureTermination.h3 : ¬ indep0% Std.Iter.toList_toArray_ensureTermination 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.toArray_toList_ensureTermination`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.toArray_toList_ensureTermination.h3 : ¬ indep0% Std.Iter.toArray_toList_ensureTermination 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.reverse_toListRev_ensureTermination`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.reverse_toListRev_ensureTermination.h3 : ¬ indep0% Std.Iter.reverse_toListRev_ensureTermination 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.toListRev_ensureTermination`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.toListRev_ensureTermination.h3 : ¬ indep0% Std.Iter.toListRev_ensureTermination 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.toArray_ensureTermination_eq_match_step`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.toArray_ensureTermination_eq_match_step.h3 : ¬ indep0% Std.Iter.toArray_ensureTermination_eq_match_step 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.toList_ensureTermination_eq_match_step`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.toList_ensureTermination_eq_match_step.h3 : ¬ indep0% Std.Iter.toList_ensureTermination_eq_match_step 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.toListRev_ensureTermination_eq_match_step`, idx 3 (inst): `LP` (skips forever) is not finite
theorem Iter.toListRev_ensureTermination_eq_match_step.h3 : ¬ indep0% Std.Iter.toListRev_ensureTermination_eq_match_step 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩))

-- `Std.Iter.forIn'_toList`, idx 3 (inst): `LP` (skips forever) is not finite; it is deterministic and its default loop is lawful
theorem Iter.forIn'_toList.h3 : ¬ indep0% Std.Iter.forIn'_toList 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩) (m := Id) (γ := Nat) (init := 0) (f := fun _ _ c => pure (.yield c)))

-- `Std.Iter.forIn'_toArray`, idx 3 (inst): `LP` (skips forever) is not finite; it is deterministic and its default loop is lawful
theorem Iter.forIn'_toArray.h3 : ¬ indep0% Std.Iter.forIn'_toArray 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩) (m := Id) (γ := Nat) (init := 0) (f := fun _ _ c => pure (.yield c)))

-- `Std.Iter.forIn'_eq_forIn'_toList`, idx 3 (inst): `LP` (skips forever) is not finite; it is deterministic and its default loop is lawful
theorem Iter.forIn'_eq_forIn'_toList.h3 : ¬ indep0% Std.Iter.forIn'_eq_forIn'_toList 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩) (m := Id) (γ := Nat) (init := 0) (f := fun _ _ c => pure (.yield c)))

-- `Std.Iter.forIn'_eq_forIn'_toArray`, idx 3 (inst): `LP` (skips forever) is not finite; it is deterministic and its default loop is lawful
theorem Iter.forIn'_eq_forIn'_toArray.h3 : ¬ indep0% Std.Iter.forIn'_eq_forIn'_toArray 3 := fun h => LP.not_finite (m := Id) (h (α := LP) (it := ⟨⟨()⟩⟩) (m := Id) (γ := Nat) (init := 0) (f := fun _ _ c => pure (.yield c)))

-- `Std.IterM.toArray_ensureTermination`, idx 5 (inst): `LP` (skips forever) is not finite
theorem IterM.toArray_ensureTermination.h5 : ¬ indep0% Std.IterM.toArray_ensureTermination 5 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (it := ⟨⟨()⟩⟩))

-- `Std.IterM.toArray_ensureTermination_eq_match_step`, idx 7 (inst): `LP` (skips forever) is not finite
theorem IterM.toArray_ensureTermination_eq_match_step.h7 : ¬ indep0% Std.IterM.toArray_ensureTermination_eq_match_step 7 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (it := ⟨⟨()⟩⟩))

-- `Std.IterM.toList_ensureTermination`, idx 5 (inst): `LP` (skips forever) is not finite
theorem IterM.toList_ensureTermination.h5 : ¬ indep0% Std.IterM.toList_ensureTermination 5 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (it := ⟨⟨()⟩⟩))

-- `Std.IterM.toList_toArray_ensureTermination`, idx 5 (inst): `LP` (skips forever) is not finite
theorem IterM.toList_toArray_ensureTermination.h5 : ¬ indep0% Std.IterM.toList_toArray_ensureTermination 5 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (it := ⟨⟨()⟩⟩))

-- `Std.IterM.toArray_toList_ensureTermination`, idx 6 (inst): `LP` (skips forever) is not finite
theorem IterM.toArray_toList_ensureTermination.h6 : ¬ indep0% Std.IterM.toArray_toList_ensureTermination 6 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (it := ⟨⟨()⟩⟩))

-- `Std.IterM.toList_ensureTermination_eq_match_step`, idx 6 (inst): `LP` (skips forever) is not finite
theorem IterM.toList_ensureTermination_eq_match_step.h6 : ¬ indep0% Std.IterM.toList_ensureTermination_eq_match_step 6 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (it := ⟨⟨()⟩⟩))

-- `Std.IterM.toListRev_ensureTermination_eq_toListRev`, idx 5 (inst): `LP` (skips forever) is not finite
theorem IterM.toListRev_ensureTermination_eq_toListRev.h5 : ¬ indep0% Std.IterM.toListRev_ensureTermination_eq_toListRev 5 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (it := ⟨⟨()⟩⟩))

-- `Std.IterM.toListRev_ensureTermination_eq_match_step`, idx 6 (inst): `LP` (skips forever) is not finite
theorem IterM.toListRev_ensureTermination_eq_match_step.h6 : ¬ indep0% Std.IterM.toListRev_ensureTermination_eq_match_step 6 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (it := ⟨⟨()⟩⟩))

-- `Std.IterM.reverse_toListRev_ensureTermination`, idx 6 (inst): `LP` (skips forever) is not finite
theorem IterM.reverse_toListRev_ensureTermination.h6 : ¬ indep0% Std.IterM.reverse_toListRev_ensureTermination 6 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (it := ⟨⟨()⟩⟩))

-- `Std.IterM.toListRev_ensureTermination`, idx 6 (inst): `LP` (skips forever) is not finite
theorem IterM.toListRev_ensureTermination.h6 : ¬ indep0% Std.IterM.toListRev_ensureTermination 6 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (it := ⟨⟨()⟩⟩))

-- `Std.IterM.DefaultConsumers.forIn'_eq_wf_of_finite`, idx 4 (inst): `LP` (skips forever) is not finite
theorem IterM.DefaultConsumers.forIn'_eq_wf_of_finite.h4 : ¬ indep0% Std.IterM.DefaultConsumers.forIn'_eq_wf_of_finite 4 := fun h => LP.not_finite (m := Id) (h (α := LP) (m := Id) (n := Id) (lift := fun _ _ f x => f x.run) (γ := Nat) (it := ⟨⟨()⟩⟩) (init := 0) (P := fun _ => True) (hP := fun _ _ => trivial) (f := fun _ _ c => pure ⟨.yield c, trivial⟩))

/-! ## Dependent hypotheses, continued -/

-- `Std.Iterators.Types.Append.rel_fstDone`, idx 7 (inst): `α₁ = LP` (skips forever) is not finite, `α₂ = CD` is
theorem Iterators.Types.Append.rel_fstDone.h7 : ¬ indep0% Std.Iterators.Types.Append.rel_fstDone 7 :=
  fun h => haveI : Finite CD Id := CD.finite
    LP.not_finite (m := Id) (h (α₁ := LP) (α₂ := CD) (m := Id) (β := Nat) (it₁ := ⟨⟨()⟩⟩) (it₂ := c 0))

-- `Std.Iterators.Types.Append.rel_fstDone`, idx 8 (inst): `α₂ = LP` (skips forever) is not finite, `α₁ = CD` is
theorem Iterators.Types.Append.rel_fstDone.h8 : ¬ indep0% Std.Iterators.Types.Append.rel_fstDone 8 :=
  fun h => haveI : Finite CD Id := CD.finite
    LP.not_finite (m := Id) (h (α₁ := CD) (α₂ := LP) (m := Id) (β := Nat) (it₁ := c 0) (it₂ := ⟨⟨()⟩⟩))

-- `Std.Iterators.Types.Append.rel_of_fst`, idx 7 (inst): `α₁ = LP` (skips forever) is not finite, `α₂ = CD` is
theorem Iterators.Types.Append.rel_of_fst.h7 : ¬ indep0% Std.Iterators.Types.Append.rel_of_fst 7 :=
  fun h => haveI : Finite CD Id := CD.finite
    LP.not_finite (m := Id) (h (α₁ := LP) (α₂ := CD) (m := Id) (β := Nat) (it₁ := ⟨⟨()⟩⟩) (it₁' := ⟨⟨()⟩⟩) (it₂ := c 0))

-- `Std.Iterators.Types.Append.rel_of_fst`, idx 8 (inst): `α₂ = LP` (skips forever) is not finite, `α₁ = CD` is
theorem Iterators.Types.Append.rel_of_fst.h8 : ¬ indep0% Std.Iterators.Types.Append.rel_of_fst 8 :=
  fun h => haveI : Finite CD Id := CD.finite
    LP.not_finite (m := Id) (h (α₁ := CD) (α₂ := LP) (m := Id) (β := Nat) (it₁ := c 1) (it₁' := c 0) (it₂ := ⟨⟨()⟩⟩) CD.rel01)

-- `Std.Iterators.Types.Append.rel_of_snd`, idx 7 (inst): `α₁ = LP` (skips forever) is not finite, `α₂ = CD` is
theorem Iterators.Types.Append.rel_of_snd.h7 : ¬ indep0% Std.Iterators.Types.Append.rel_of_snd 7 :=
  fun h => haveI : Finite CD Id := CD.finite
    LP.not_finite (m := Id) (h (α₁ := LP) (α₂ := CD) (m := Id) (β := Nat) (it₂ := c 1) (it₂' := c 0) CD.rel01)

-- `Std.Iterators.Types.Append.rel_of_snd`, idx 8 (inst): `α₂ = LP` (skips forever) is not finite, `α₁ = CD` is
theorem Iterators.Types.Append.rel_of_snd.h8 : ¬ indep0% Std.Iterators.Types.Append.rel_of_snd 8 :=
  fun h => haveI : Finite CD Id := CD.finite
    LP.not_finite (m := Id) (h (α₁ := CD) (α₂ := LP) (m := Id) (β := Nat) (it₂ := ⟨⟨()⟩⟩) (it₂' := ⟨⟨()⟩⟩))

-- `Std.Iterators.Types.Append.productiveRel_fstDone`, idx 7 (inst): `α₁ = LP` (skips forever) is not productive, `α₂ = CD` is
theorem Iterators.Types.Append.productiveRel_fstDone.h7 : ¬ indep0% Std.Iterators.Types.Append.productiveRel_fstDone 7 :=
  fun h => haveI : Productive CD Id := CD.productive
    LP.not_productive (m := Id) (h (α₁ := LP) (α₂ := CD) (m := Id) (β := Nat) (it₁ := ⟨⟨()⟩⟩) (it₂ := c 0))

-- `Std.Iterators.Types.Append.productiveRel_fstDone`, idx 8 (inst): `α₂ = LP` (skips forever) is not productive, `α₁ = CD` is
theorem Iterators.Types.Append.productiveRel_fstDone.h8 : ¬ indep0% Std.Iterators.Types.Append.productiveRel_fstDone 8 :=
  fun h => haveI : Productive CD Id := CD.productive
    LP.not_productive (m := Id) (h (α₁ := CD) (α₂ := LP) (m := Id) (β := Nat) (it₁ := c 0) (it₂ := ⟨⟨()⟩⟩))

-- `Std.Iterators.Types.Append.productiveRel_of_fst`, idx 7 (inst): `α₁ = LP` (skips forever) is not productive, `α₂ = CD` is
theorem Iterators.Types.Append.productiveRel_of_fst.h7 : ¬ indep0% Std.Iterators.Types.Append.productiveRel_of_fst 7 :=
  fun h => haveI : Productive CD Id := CD.productive
    LP.not_productive (m := Id) (h (α₁ := LP) (α₂ := CD) (m := Id) (β := Nat) (it₁ := ⟨⟨()⟩⟩) (it₁' := ⟨⟨()⟩⟩) (it₂ := c 0))

-- `Std.Iterators.Types.Append.productiveRel_of_fst`, idx 8 (inst): `α₂ = LP` (skips forever) is not productive, `α₁ = SK` (skip countdown) is
theorem Iterators.Types.Append.productiveRel_of_fst.h8 : ¬ indep0% Std.Iterators.Types.Append.productiveRel_of_fst 8 :=
  fun h => haveI : Productive SK Id := SK.productive
    LP.not_productive (m := Id) (h (α₁ := SK) (α₂ := LP) (m := Id) (β := Nat) (it₁ := ⟨⟨1⟩⟩) (it₁' := ⟨⟨0⟩⟩) (it₂ := ⟨⟨()⟩⟩) SK.prel01)

-- `Std.Iterators.Types.Append.productiveRel_of_snd`, idx 7 (inst): `α₁ = LP` (skips forever) is not productive, `α₂ = SK` (skip countdown) is
theorem Iterators.Types.Append.productiveRel_of_snd.h7 : ¬ indep0% Std.Iterators.Types.Append.productiveRel_of_snd 7 :=
  fun h => haveI : Productive SK Id := SK.productive
    LP.not_productive (m := Id) (h (α₁ := LP) (α₂ := SK) (m := Id) (β := Nat) (it₂ := ⟨⟨1⟩⟩) (it₂' := ⟨⟨0⟩⟩) SK.prel01)

-- `Std.Iterators.Types.Append.productiveRel_of_snd`, idx 8 (inst): `α₂ = LP` (skips forever) is not productive, `α₁ = CD` is
theorem Iterators.Types.Append.productiveRel_of_snd.h8 : ¬ indep0% Std.Iterators.Types.Append.productiveRel_of_snd 8 :=
  fun h => haveI : Productive CD Id := CD.productive
    LP.not_productive (m := Id) (h (α₁ := CD) (α₂ := LP) (m := Id) (β := Nat) (it₂ := ⟨⟨()⟩⟩) (it₂' := ⟨⟨()⟩⟩))

-- `Std.Iterators.Types.Take.rel_of_countdown`, idx 5 (inst): `LP` is not productive; countdowns `1 < 2` of `take 0`, `take 1`
theorem Iterators.Types.Take.rel_of_countdown.h5 : ¬ indep0% Std.Iterators.Types.Take.rel_of_countdown 5 :=
  fun h => LP.not_productive (m := Id) (h (α := LP) (m := Id) (β := Nat)
    (it := IterM.take 1 ⟨⟨()⟩⟩) (it' := IterM.take 0 ⟨⟨()⟩⟩) (by simp [IterM.take]))

-- `Std.Iterators.Types.Take.rel_of_inner`, idx 5 (inst): `LP` is not productive
theorem Iterators.Types.Take.rel_of_inner.h5 : ¬ indep0% Std.Iterators.Types.Take.rel_of_inner 5 :=
  fun h => LP.not_productive (m := Id) (h (α := LP) (m := Id) (β := Nat) (remaining := 0)
    (it := ⟨⟨()⟩⟩) (it' := ⟨⟨()⟩⟩))

-- `Std.Iterators.Types.Take.rel_of_zero_of_inner`, idx 7 (h): `it = take 0 (CD 0)` has countdown `1`, `it' = (CD 0).toTake` has countdown `0`
theorem Iterators.Types.Take.rel_of_zero_of_inner.h7 : ¬ indep0% Std.Iterators.Types.Take.rel_of_zero_of_inner 7 :=
  fun h => by
  have := h (α := CD) (m := Id) (β := Nat) (it := IterM.take 0 (c 0)) (it' := (c 0).toTake) rfl
  simp [IterM.take] at this

-- `Std.Iter.forIn'_toList`, idx 9 (inst): `ND` (finite, default lawful loop) is not deterministic
theorem Iter.forIn'_toList.h9 : ¬ indep0% Std.Iter.forIn'_toList 9 :=
  fun h => ND.not_det (m := Id) (h (α := ND) (m := Id) (γ := Nat) (it := ⟨⟨true⟩⟩) (init := 0)
    (f := fun _ _ c => pure (.yield c)))

-- `Std.Iter.forIn'_toArray`, idx 9 (inst): `ND` (finite, default lawful loop) is not deterministic
theorem Iter.forIn'_toArray.h9 : ¬ indep0% Std.Iter.forIn'_toArray 9 :=
  fun h => ND.not_det (m := Id) (h (α := ND) (m := Id) (γ := Nat) (it := ⟨⟨true⟩⟩) (init := 0)
    (f := fun _ _ c => pure (.yield c)))

-- `Std.Iter.forIn'_eq_forIn'_toList`, idx 9 (inst): `ND` (finite, default lawful loop) is not deterministic
theorem Iter.forIn'_eq_forIn'_toList.h9 : ¬ indep0% Std.Iter.forIn'_eq_forIn'_toList 9 :=
  fun h => ND.not_det (m := Id) (h (α := ND) (m := Id) (γ := Nat) (it := ⟨⟨true⟩⟩) (init := 0)
    (f := fun _ _ c => pure (.yield c)))

-- `Std.Iter.forIn'_eq_forIn'_toArray`, idx 9 (inst): `ND` (finite, default lawful loop) is not deterministic
theorem Iter.forIn'_eq_forIn'_toArray.h9 : ¬ indep0% Std.Iter.forIn'_eq_forIn'_toArray 9 :=
  fun h => ND.not_det (m := Id) (h (α := ND) (m := Id) (γ := Nat) (it := ⟨⟨true⟩⟩) (init := 0)
    (f := fun _ _ c => pure (.yield c)))

-- `Std.Iter.unattach_eq_toIter_unattach_toIterM`, idx 5 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem Iter.unattach_eq_toIter_unattach_toIterM.h5 : ¬ indep0% Std.Iter.unattach_eq_toIter_unattach_toIterM 5 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (it := ci 1) 0 CD.out1'

-- `Std.Iter.unattach_toList_attachWith`, idx 5 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem Iter.unattach_toList_attachWith.h5 : ¬ indep0% Std.Iter.unattach_toList_attachWith 5 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (it := ci 1) 0 CD.out1'

-- `Std.Iter.toList_attachWith`, idx 5 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem Iter.toList_attachWith.h5 : ¬ indep0% Std.Iter.toList_attachWith 5 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (it := ci 1) 0 CD.out1'

-- `Std.Iter.unattach_toListRev_attachWith`, idx 5 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem Iter.unattach_toListRev_attachWith.h5 : ¬ indep0% Std.Iter.unattach_toListRev_attachWith 5 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (it := ci 1) 0 CD.out1'

-- `Std.Iter.toListRev_attachWith`, idx 5 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem Iter.toListRev_attachWith.h5 : ¬ indep0% Std.Iter.toListRev_attachWith 5 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (it := ci 1) 0 CD.out1'

-- `Std.Iter.unattach_toArray_attachWith`, idx 5 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem Iter.unattach_toArray_attachWith.h5 : ¬ indep0% Std.Iter.unattach_toArray_attachWith 5 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (it := ci 1) 0 CD.out1'

-- `Std.Iter.toArray_attachWith`, idx 5 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem Iter.toArray_attachWith.h5 : ¬ indep0% Std.Iter.toArray_attachWith 5 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (it := ci 1) 0 CD.out1'

-- `Std.Iter.length_attachWith`, idx 5 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem Iter.length_attachWith.h5 : ¬ indep0% Std.Iter.length_attachWith 5 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (it := ci 1) 0 CD.out1'

-- `Std.IterM.step_attachWith`, idx 7 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem IterM.step_attachWith.h7 : ¬ indep0% Std.IterM.step_attachWith 7 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (m := Id) (it := c 1) 0 CD.out1

-- `Std.IterM.map_unattach_toList_attachWith`, idx 7 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem IterM.map_unattach_toList_attachWith.h7 : ¬ indep0% Std.IterM.map_unattach_toList_attachWith 7 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (m := Id) (it := c 1) 0 CD.out1

-- `Std.IterM.map_unattach_toListRev_attachWith`, idx 9 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem IterM.map_unattach_toListRev_attachWith.h9 : ¬ indep0% Std.IterM.map_unattach_toListRev_attachWith 9 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (m := Id) (n := Id) (it := c 1) 0 CD.out1

-- `Std.IterM.map_unattach_toArray_attachWith`, idx 9 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem IterM.map_unattach_toArray_attachWith.h9 : ¬ indep0% Std.IterM.map_unattach_toArray_attachWith 9 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (m := Id) (n := Id) (it := c 1) 0 CD.out1

-- `Std.IterM.length_attachWith`, idx 9 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem IterM.length_attachWith.h9 : ¬ indep0% Std.IterM.length_attachWith 9 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (m := Id) (n := Id) (it := c 1) 0 CD.out1

-- `Std.IterM.DefaultConsumers.forIn'_eq_match_step`, idx 12 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem IterM.DefaultConsumers.forIn'_eq_match_step.h12 : ¬ indep0% Std.IterM.DefaultConsumers.forIn'_eq_match_step 12 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (m := Id) (n := Id) (lift := fun _ _ f x => f x.run) (γ := Nat) (it := c 1) (init := 0)
    (PlausibleForInStep := fun _ _ _ => True) (f := fun _ h _ => h.elim) (wf := IteratorLoop.wellFounded_of_finite) 0 CD.out1

-- `Std.IterM.DefaultConsumers.forIn'_eq_wf`, idx 14 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem IterM.DefaultConsumers.forIn'_eq_wf.h14 : ¬ indep0% Std.IterM.DefaultConsumers.forIn'_eq_wf 14 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (m := Id) (n := Id) (lift := fun _ _ f x => f x.run) (γ := Nat) (it := c 1) (init := 0)
    (Pl := fun _ _ _ => True) (f := fun _ h _ => h.elim) (wf := IteratorLoop.wellFounded_of_finite) 0 CD.out1

-- `Std.IterM.DefaultConsumers.forIn'_eq_wf_of_finite`, idx 13 (hP): `P = False`, but `CD 1` plausibly outputs `0`
theorem IterM.DefaultConsumers.forIn'_eq_wf_of_finite.h13 : ¬ indep0% Std.IterM.DefaultConsumers.forIn'_eq_wf_of_finite 13 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (m := Id) (n := Id) (lift := fun _ _ f x => f x.run) (γ := Nat) (it := c 1) (init := 0)
    (f := fun _ h _ => h.elim) 0 CD.out1

-- `Std.IterM.DefaultConsumers.forIn'_eq_forIn'`, idx 12 (hP): `P = False`, `Q = True`, but `CD 1` plausibly outputs `0`
theorem IterM.DefaultConsumers.forIn'_eq_forIn'.h12 : ¬ indep0% Std.IterM.DefaultConsumers.forIn'_eq_forIn' 12 :=
  fun h => h (α := CD) (β := Nat) (P := fun _ => False) (Q := fun _ => True) (hQ := fun _ _ => trivial) (m := Id) (n := Id) (lift := fun _ _ f x => f x.run) (γ := Nat) (it := c 1) (init := 0)
    (Pl := fun _ _ _ => True) (wf := IteratorLoop.wellFounded_of_finite)
    (f := fun _ h _ => h.elim) (g := fun _ _ c => pure ⟨.yield c, trivial⟩) (hfg := fun _ _ h _ => h.elim) 0 CD.out1

-- `Std.IterM.DefaultConsumers.forIn'_eq_forIn'`, idx 14 (hQ): `Q = False`, `P = True`, but `CD 1` plausibly outputs `0`
theorem IterM.DefaultConsumers.forIn'_eq_forIn'.h14 : ¬ indep0% Std.IterM.DefaultConsumers.forIn'_eq_forIn' 14 :=
  fun h => h (α := CD) (β := Nat) (Q := fun _ => False) (P := fun _ => True) (hP := fun _ _ => trivial) (m := Id) (n := Id) (lift := fun _ _ f x => f x.run) (γ := Nat) (it := c 1) (init := 0)
    (Pl := fun _ _ _ => True) (wf := IteratorLoop.wellFounded_of_finite)
    (g := fun _ h _ => h.elim) (f := fun _ _ c => pure ⟨.yield c, trivial⟩) (hfg := fun _ _ _ h => h.elim) 0 CD.out1

-- `Std.IterM.DefaultConsumers.forIn'_eq_wf`, idx 10 (wf): `LP` skips to itself, so the loop relation is reflexive
theorem IterM.DefaultConsumers.forIn'_eq_wf.h10 : ¬ indep0% Std.IterM.DefaultConsumers.forIn'_eq_wf 10 :=
  fun h => wf_irrefl (h (α := LP) (β := Nat) (m := Id) (n := Id) (lift := fun _ _ f x => f x.run) (γ := Nat)
    (Pl := fun _ _ _ => True) (it := ⟨⟨()⟩⟩) (init := 0) (P := fun _ => True) (hP := fun _ _ => trivial)
    (f := fun _ _ c => pure ⟨.yield c, trivial⟩)) (⟨⟨()⟩⟩, 0) (Or.inr ⟨rfl, rfl⟩)

-- `Std.Iter.forIn'_congr`, idx 10 (w): `ita = CD 0`, `itb = CD 1`
theorem Iter.forIn'_congr.h10 : ¬ indep0% Std.Iter.forIn'_congr 10 :=
  fun h => by
  have := h (γ := Nat) (α := CD) (m := Id) (ita := ci 0) (itb := ci 1) (b := 0) (b' := 0) (hb := rfl)
    (f := fun _ _ c => pure (.yield c)) (g := fun _ _ c => pure (.yield c))
  cases this

-- `Std.IterM.forIn'_congr`, idx 12 (w): `ita = CD 0`, `itb = CD 1`
theorem IterM.forIn'_congr.h12 : ¬ indep0% Std.IterM.forIn'_congr 12 :=
  fun h => by
  have := h (γ := Nat) (α := CD) (m := Id) (n := Id) (ita := c 0) (itb := c 1) (b := 0) (b' := 0) (hb := rfl)
    (f := fun _ _ c => pure (.yield c)) (g := fun _ _ c => pure (.yield c))
  cases this

-- `Std.Iterators.PostconditionT.ext`, idx 6 (h): properties `True` and `· = 0` differ (at `1`)
theorem Iterators.PostconditionT.ext.h6 : ¬ indep0% Std.Iterators.PostconditionT.ext 6 :=
  fun h => by
  have := congrFun (h (m := Id) (α := Nat) (x := ⟨fun _ => True, pure ⟨0, trivial⟩⟩)
    (y := ⟨fun n => n = 0, pure ⟨0, rfl⟩⟩)) 1
  simp at this

-- `Std.Iter.step_flatMapAfterM`, idx 7 (inst): monad `CM` (bind adds 1 to a counter) is not lawful; its trivial `MonadAttach` is weakly lawful
theorem Iter.step_flatMapAfterM.h7 : ¬ indep0% Std.Iter.step_flatMapAfterM 7 :=
  fun h => CM.not_lawful (h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := CM)
    (f := fun _ => pure ⟨⟨0⟩⟩) (it₁ := ci 0) (it₂ := none))

-- `Std.Iter.step_flatMapM`, idx 7 (inst): monad `CM` (bind adds 1 to a counter) is not lawful; its trivial `MonadAttach` is weakly lawful
theorem Iter.step_flatMapM.h7 : ¬ indep0% Std.Iter.step_flatMapM 7 :=
  fun h => CM.not_lawful (h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := CM)
    (f := fun _ => pure ⟨⟨0⟩⟩) (it₁ := ci 0))

-- `Std.IterM.step_flatMapAfterM`, idx 7 (inst): monad `CM` (bind adds 1 to a counter) is not lawful; its trivial `MonadAttach` is weakly lawful
theorem IterM.step_flatMapAfterM.h7 : ¬ indep0% Std.IterM.step_flatMapAfterM 7 :=
  fun h => CM.not_lawful (h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := CM)
    (f := fun _ => pure ⟨⟨0⟩⟩) (it₁ := ⟨⟨0⟩⟩) (it₂ := none))

-- `Std.IterM.step_flatMapM`, idx 7 (inst): monad `CM` (bind adds 1 to a counter) is not lawful; its trivial `MonadAttach` is weakly lawful
theorem IterM.step_flatMapM.h7 : ¬ indep0% Std.IterM.step_flatMapM 7 :=
  fun h => CM.not_lawful (h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := CM)
    (f := fun _ => pure ⟨⟨0⟩⟩) (it₁ := ⟨⟨0⟩⟩))

-- `Std.IterM.step_flatMapAfter`, idx 6 (inst): monad `CM` (bind adds 1 to a counter) is not lawful
theorem IterM.step_flatMapAfter.h6 : ¬ indep0% Std.IterM.step_flatMapAfter 6 :=
  fun h => CM.not_lawful (h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := CM)
    (f := fun _ => ⟨⟨0⟩⟩) (it₁ := ⟨⟨0⟩⟩) (it₂ := none))

-- `Std.IterM.step_flatMap`, idx 6 (inst): monad `CM` (bind adds 1 to a counter) is not lawful
theorem IterM.step_flatMap.h6 : ¬ indep0% Std.IterM.step_flatMap 6 :=
  fun h => CM.not_lawful (h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := CM)
    (f := fun _ => ⟨⟨0⟩⟩) (it₁ := ⟨⟨0⟩⟩))

-- `Std.Iter.step_flatMapAfterM`, idx 8 (inst): `SM = StateM Nat` is lawful, but its `attach` increments the state
theorem Iter.step_flatMapAfterM.h8 : ¬ indep0% Std.Iter.step_flatMapAfterM 8 :=
  fun h => SM.not_weakly (h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := SM)
    (f := fun _ => pure ⟨⟨0⟩⟩) (it₁ := ci 0) (it₂ := none))

-- `Std.Iter.step_flatMapM`, idx 8 (inst): `SM = StateM Nat` is lawful, but its `attach` increments the state
theorem Iter.step_flatMapM.h8 : ¬ indep0% Std.Iter.step_flatMapM 8 :=
  fun h => SM.not_weakly (h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := SM)
    (f := fun _ => pure ⟨⟨0⟩⟩) (it₁ := ci 0))

/-! ## Combinator relations, structure fields, lift functions -/

-- `Std.Iterators.Types.Append.rel_of_fst`, idx 12 (h): `it₁' = it₁`; `Append.Rel` is well-founded, hence irreflexive
theorem Iterators.Types.Append.rel_of_fst.h12 :
    ¬ drop0% Std.Iterators.Types.Append.rel_of_fst 12 := fun h =>
  wf_irrefl (r := Iterators.Types.Append.Rel CD CD Id Nat)
    (Iterators.Types.Append.instFinitenessRelation (α₁ := CD) (α₂ := CD) (m := Id) (β := Nat)).wf _
    (h (α₁ := CD) (α₂ := CD) (m := Id) (β := Nat) (it₁ := c 0) (it₁' := c 0) (it₂ := c 0))

-- `Std.Iterators.Types.Append.rel_of_snd`, idx 11 (h): `it₂' = it₂`; `Append.Rel` is well-founded, hence irreflexive
theorem Iterators.Types.Append.rel_of_snd.h11 :
    ¬ drop0% Std.Iterators.Types.Append.rel_of_snd 11 := fun h =>
  wf_irrefl (r := Iterators.Types.Append.Rel CD CD Id Nat)
    (Iterators.Types.Append.instFinitenessRelation (α₁ := CD) (α₂ := CD) (m := Id) (β := Nat)).wf _
    (h (α₁ := CD) (α₂ := CD) (m := Id) (β := Nat) (it₂ := c 0) (it₂' := c 0))

-- `Std.Iterators.Types.Append.productiveRel_of_fst`, idx 12 (h): `it₁' = it₁`; the lexicographic relation is irreflexive
theorem Iterators.Types.Append.productiveRel_of_fst.h12 :
    ¬ drop0% Std.Iterators.Types.Append.productiveRel_of_fst 12 := fun h => by
  have := h (α₁ := CD) (α₂ := CD) (m := Id) (β := Nat) (it₁ := c 0) (it₁' := c 0) (it₂ := c 0)
  unfold Iterators.Types.Append.ProductiveRel InvImage at this
  refine lex_irrefl (fun a => ?_) (fun b => ?_) _ this
  · exact option_lt_irrefl (fun (a : IterM (α := CD) Id Nat) => prod_rel_irrefl a.finitelyManySkips) a
  · exact prod_rel_irrefl _

-- `Std.Iterators.Types.Append.productiveRel_of_snd`, idx 11 (h): `it₂' = it₂`; the lexicographic relation is irreflexive
theorem Iterators.Types.Append.productiveRel_of_snd.h11 :
    ¬ drop0% Std.Iterators.Types.Append.productiveRel_of_snd 11 := fun h => by
  have := h (α₁ := CD) (α₂ := CD) (m := Id) (β := Nat) (it₂ := c 0) (it₂' := c 0)
  unfold Iterators.Types.Append.ProductiveRel InvImage at this
  refine lex_irrefl (fun a => ?_) (fun b => ?_) _ this
  · exact option_lt_irrefl (fun (a : IterM (α := CD) Id Nat) => prod_rel_irrefl a.finitelyManySkips) a
  · exact prod_rel_irrefl _

theorem take_rel_irrefl (it : IterM (α := Iterators.Types.Take CD Id) Id Nat) :
    ¬ Iterators.Types.Take.Rel (α := CD) (β := Nat) Id it it := by
  unfold Iterators.Types.Take.Rel
  split <;> first
    | exact lex_irrefl (fun a => Nat.lt_irrefl a) (fun b => fin_rel_irrefl (α := CD) (m := Id) b) _
    | exact lex_irrefl (fun a => Nat.lt_irrefl a) (fun b => prod_rel_irrefl (α := CD) (m := Id) b) _

-- `Std.Iterators.Types.Take.rel_of_countdown`, idx 8 (h): `it' = it`; `Take.Rel` is irreflexive
theorem Iterators.Types.Take.rel_of_countdown.h8 :
    ¬ drop0% Std.Iterators.Types.Take.rel_of_countdown 8 := fun h =>
  take_rel_irrefl _ (h (α := CD) (m := Id) (β := Nat) (it := IterM.take 0 (c 0)) (it' := IterM.take 0 (c 0)))

-- `Std.Iterators.Types.Take.rel_of_inner`, idx 9 (h): `it' = it`; `Take.Rel` is irreflexive
theorem Iterators.Types.Take.rel_of_inner.h9 :
    ¬ drop0% Std.Iterators.Types.Take.rel_of_inner 9 := fun h =>
  take_rel_irrefl _ (h (α := CD) (m := Id) (β := Nat) (remaining := 0) (it := c 0) (it' := c 0))

-- `Std.Iterators.Types.Take.rel_of_zero_of_inner`, idx 8 (h'): `it = (CD 1).toTake` (countdown 0), `it'` with countdown 5 and inner `CD 0`
theorem Iterators.Types.Take.rel_of_zero_of_inner.h8 :
    ¬ drop0% Std.Iterators.Types.Take.rel_of_zero_of_inner 8 := fun h => by
  have := h (α := CD) (m := Id) (β := Nat) (it := (c 1).toTake) (it' := ⟨⟨5, c 0, Or.inl (by decide)⟩⟩)
    rfl CD.rel01
  revert this
  unfold Iterators.Types.Take.Rel
  split
  · simp [InvImage, Prod.lex_def, IterM.toTake]; exact Nat.not_lt_zero 5
  · simp [InvImage, Prod.lex_def, IterM.toTake]; exact Nat.not_lt_zero 5

-- `Std.Iterators.Types.Take.rel_of_zero_of_inner`, idx 9 (h''): `it = it' = (CD 0).toTake`; `Take.Rel` is irreflexive
theorem Iterators.Types.Take.rel_of_zero_of_inner.h9 :
    ¬ drop0% Std.Iterators.Types.Take.rel_of_zero_of_inner 9 := fun h =>
  take_rel_irrefl _ (h (α := CD) (m := Id) (β := Nat) (it := (c 0).toTake) (it' := (c 0).toTake) rfl rfl)

-- `Std.IterM.take.surjective_of_zero_lt`, idx 5 (h): `(CD 0).toTake` has countdown `0`, every `take k` has `k + 1`
theorem IterM.take.surjective_of_zero_lt.h5 : ¬ drop0% Std.IterM.take.surjective_of_zero_lt 5 := fun h => by
  obtain ⟨it₀, k, hk⟩ := h (α := CD) (m := Id) (β := Nat) (it := (c 0).toTake)
  have := congrArg (fun it => it.internalState.countdown) hk
  simp [IterM.take, IterM.toTake] at this

-- `Std.Iterators.Types.Attach.invariant`, idx 7 (a): `P = False` with inner iterator `CD 0` (no outputs)
theorem Iterators.Types.Attach.invariant.h7 : ¬ drop0% Std.Iterators.Types.Attach.invariant 7 := fun h =>
  h (α := CD) (m := Id) (β := Nat) (P := fun _ => False)
    (self := ⟨c 0, fun out ho => absurd ho (CD.no_out0 out)⟩) (out := 0)

-- `Std.Iterators.Types.FilterMap.ext`, idx 9 (inner): inner iterators `CD 0` and `CD 1`
theorem Iterators.Types.FilterMap.ext.h9 : ¬ drop0% Std.Iterators.Types.FilterMap.ext 9 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (m := Id) (n := Id) (lift := fun _ x => x)
    (f := fun _ => pure none) (x := ⟨c 0⟩) (y := ⟨c 1⟩)
  cases this

-- `Std.IteratorLoop.ext`, idx 7 (forIn): two loops into `StateM Nat`: `pure init` and increment-then-`pure init`
theorem IteratorLoop.ext.h7 : ¬ drop0% Std.IteratorLoop.ext 7 := fun h => by
  have := congrArg (fun i : IteratorLoop CD Id (StateM Nat) =>
      (i.forIn (fun _ _ f x => f x.run) Nat (fun _ _ _ => True) (c 0) 0
        (fun _ _ c => pure ⟨.yield c, trivial⟩)).run 0 |>.run.2)
    (h (α := CD) (m := Id) (β := Nat) (n := StateM Nat) (x := ⟨fun _ _ _ _ init _ => pure init⟩)
      (y := ⟨fun _ _ _ _ init _ => (modify (· + 1) : StateM Nat PUnit) *> pure init⟩))
  simp at this

-- `Std.IteratorLoop.wellFounded_of_productive`, idx 8 (hp): `YL` (yields forever) is productive; with `P = True` the loop relation is reflexive
theorem IteratorLoop.wellFounded_of_productive.h8 :
    ¬ drop0% Std.IteratorLoop.wellFounded_of_productive 8 := fun h =>
  wf_irrefl (h (γ := Nat) (α := YL) (β := Nat) (m := Id) (P := fun _ _ _ => True)) (⟨⟨()⟩⟩, 0)
    (Or.inl ⟨0, rfl, trivial⟩)

-- `Std.Internal.LawfulMonadLiftBindFunction.liftBind_pure`, idx 5 (self): `cntLiftBind` (`Id → StateM Nat`, increments the state)
theorem Internal.LawfulMonadLiftBindFunction.liftBind_pure.h5 :
    ¬ drop0% Std.Internal.LawfulMonadLiftBindFunction.liftBind_pure 5 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    (@h Id (StateM Nat) inferInstance inferInstance cntLiftBind Nat Nat pure 0)
  simp [cntLiftBind] at this

-- `Std.Internal.LawfulMonadLiftBindFunction.liftBind_bind`, idx 5 (self): `cntLiftBind` counts one vs two lifts
theorem Internal.LawfulMonadLiftBindFunction.liftBind_bind.h5 :
    ¬ drop0% Std.Internal.LawfulMonadLiftBindFunction.liftBind_bind 5 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    (@h Id (StateM Nat) inferInstance inferInstance cntLiftBind Nat Nat Nat pure (pure 0) pure)
  simp [cntLiftBind] at this

-- `Std.Internal.instLawfulMonadLiftFunctionOfLawfulMonadLiftBindFunctionBindOfLawfulMonad`, idx 5 (inst): lift `Id → StateM Nat` that increments the state
theorem Internal.instLawfulMonadLiftFunctionOfLawfulMonadLiftBindFunctionBindOfLawfulMonad.h5 :
    ¬ drop0% Std.Internal.instLawfulMonadLiftFunctionOfLawfulMonadLiftBindFunctionBindOfLawfulMonad 5 :=
  fun h => by
  have h' := h (m := Id) (n := StateM Nat)
    (lift := fun _ x => (modify (· + 1) : StateM Nat PUnit) *> pure x.run)
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2) (h'.lift_pure 0)
  simp at this

-- `Std.Iterators.PostconditionT.ext`, idx 7 (h'): same property `True`, operations `pure 0` and `pure 1`
theorem Iterators.PostconditionT.ext.h7 : ¬ drop0% Std.Iterators.PostconditionT.ext 7 := fun h => by
  have := congrArg (fun z : Iterators.PostconditionT Id Nat => z.run.run)
    (h (m := Id) (α := Nat) (x := ⟨fun _ => True, pure ⟨0, trivial⟩⟩) (y := ⟨fun _ => True, pure ⟨1, trivial⟩⟩) rfl)
  simp [Iterators.PostconditionT.run] at this

-- `Std.Iterators.PostconditionT.instLawfulMonadLift`, idx 7 (inst): lift `Id → StateM Nat` that increments the state
theorem Iterators.PostconditionT.instLawfulMonadLift.h7 :
    ¬ drop0% Std.Iterators.PostconditionT.instLawfulMonadLift 7 := fun h => by
  have h' := @h Id (StateM Nat) cntLift _ _ _ _
  have := congrArg (fun z : Iterators.PostconditionT (StateM Nat) Nat => (z.run.run 0).run.2)
    (h'.monadLift_pure 0)
  simp [Iterators.PostconditionT.run, MonadLift.monadLift, monadLift] at this

/-! ## Plausible steps of `flatMap` and `take` (inversion of the step relations) -/

/-- Invert the plausible-step relations of the combinators down to the `CD` step, which is
then contradictory. -/
macro "inv " x:ident : tactic => `(tactic| (cases $x:ident <;>
  repeat (first | (rename_i h; cases h) | (rename_i h _; cases h) | (rename_i h _ _; cases h))))

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMap`, idx 12 (h): inner iterator `CD 1` is never done
theorem Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMap.h12 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMap 12 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => c 0) (it₁ := c 0) (it₂ := c 1)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMap`, idx 13 (h): inner iterator `CD 0` never skips
theorem Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMap.h13 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMap 13 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => c 0) (it₁ := c 0) (it₂ := c 0) (it₂' := c 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMap`, idx 14 (h): inner iterator `CD 0` never yields
theorem Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMap.h14 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMap 14 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => c 0) (it₁ := c 0) (it₂ := c 0) (it₂' := c 0) (b := 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMap`, idx 11 (h): outer iterator `CD 1` is never done
theorem Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMap.h11 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMap 11 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => c 0) (it₁ := c 1)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMap`, idx 12 (h): outer iterator `CD 0` never skips
theorem Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMap.h12 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMap 12 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => c 0) (it₁ := c 0) (it₁' := c 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMap`, idx 13 (h): outer iterator `CD 0` never yields
theorem Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMap.h13 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMap 13 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => c 0) (it₁ := c 0) (it₁' := c 0) (b := 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMapM`, idx 13 (h): inner iterator `CD 1` is never done
theorem Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMapM.h13 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMapM 13 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := c 0) (it₂ := c 1)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMapM`, idx 14 (h): inner iterator `CD 0` never skips
theorem Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMapM.h14 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMapM 14 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := c 0) (it₂ := c 0) (it₂' := c 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMapM`, idx 15 (h): inner iterator `CD 0` never yields
theorem Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMapM.h15 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMapM 15 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := c 0) (it₂ := c 0) (it₂' := c 0) (b := 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMapM`, idx 12 (h): outer iterator `CD 1` is never done
theorem Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMapM.h12 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMapM 12 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := c 1)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMapM`, idx 13 (h): outer iterator `CD 0` never skips
theorem Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMapM.h13 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMapM 13 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := c 0) (it₁' := c 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM`, idx 15 (h): outer iterator `CD 0` never yields
theorem Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM.h15 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM 15 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := c 0) (it₁' := c 0) (b := 0) (it₂' := c 0) rfl
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM`, idx 16 (h'): `f b = pure (CD 0)` cannot return `CD 1` (`MonadAttach Id`: `CanReturn x a ↔ x.run = a`)
theorem Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM.h16 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM 16 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := c 1) (it₁' := c 0) (b := 0) (it₂' := c 1) rfl
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMap_pure`, idx 9 (h): inner iterator `CD 1` is never done
theorem Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMap_pure.h9 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMap_pure 9 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (f := fun _ => ci 0) (it₁ := ci 0) (it₂ := ci 1)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMap_pure`, idx 10 (h): inner iterator `CD 0` never skips
theorem Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMap_pure.h10 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMap_pure 10 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (f := fun _ => ci 0) (it₁ := ci 0) (it₂ := ci 0) (it₂' := ci 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMap_pure`, idx 11 (h): inner iterator `CD 0` never yields
theorem Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMap_pure.h11 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMap_pure 11 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (f := fun _ => ci 0) (it₁ := ci 0) (it₂ := ci 0) (it₂' := ci 0) (b := 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMap_pure`, idx 8 (h): outer iterator `CD 1` is never done
theorem Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMap_pure.h8 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMap_pure 8 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (f := fun _ => ci 0) (it₁ := ci 1)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMap_pure`, idx 9 (h): outer iterator `CD 0` never skips
theorem Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMap_pure.h9 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMap_pure 9 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (f := fun _ => ci 0) (it₁ := ci 0) (it₁' := ci 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMap_pure`, idx 10 (h): outer iterator `CD 0` never yields
theorem Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMap_pure.h10 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMap_pure 10 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (f := fun _ => ci 0) (it₁ := ci 0) (it₁' := ci 0) (b := 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMapM_pure`, idx 13 (h): inner iterator `CD 1` is never done
theorem Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMapM_pure.h13 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMapM_pure 13 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := ci 0) (it₂ := c 1)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMapM_pure`, idx 14 (h): inner iterator `CD 0` never skips
theorem Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMapM_pure.h14 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMapM_pure 14 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := ci 0) (it₂ := c 0) (it₂' := c 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMapM_pure`, idx 15 (h): inner iterator `CD 0` never yields
theorem Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMapM_pure.h15 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMapM_pure 15 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := ci 0) (it₂ := c 0) (it₂' := c 0) (b := 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMapM_pure`, idx 12 (h): outer iterator `CD 1` is never done
theorem Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMapM_pure.h12 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMapM_pure 12 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := ci 1)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMapM_pure`, idx 13 (h): outer iterator `CD 0` never skips
theorem Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMapM_pure.h13 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMapM_pure 13 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := ci 0) (it₁' := ci 0)
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure`, idx 16 (h): outer iterator `CD 0` never yields
theorem Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure.h16 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure 16 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := ci 0) (it₁' := ci 0) (b := 0) (it₂' := c 0) rfl
  inv this

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure`, idx 17 (h'): `f b = pure (CD 0)` cannot return `CD 1` (`MonadAttach Id`: `CanReturn x a ↔ x.run = a`)
theorem Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure.h17 :
    ¬ drop0% Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure 17 := fun h => by
  have := h (α := CD) (β := Nat) (α₂ := CD) (γ := Nat) (m := Id) (f := fun _ => pure (c 0)) (it₁ := ci 1) (it₁' := ci 0) (b := 0) (it₂' := c 1) rfl
  inv this

-- `Std.Iterators.Types.Take.isPlausibleStep_take_yield`, idx 9 (h): inner iterator `CD 0` never yields
theorem Iterators.Types.Take.isPlausibleStep_take_yield.h9 :
    ¬ drop0% Std.Iterators.Types.Take.isPlausibleStep_take_yield 9 := fun h => by
  have := h (m := Id) (α := CD) (β := Nat) (it' := c 0) (out := 0) (n := 0) (it := c 0)
  inv this

-- `Std.Iterators.Types.Take.isPlausibleStep_take_skip`, idx 8 (h): inner iterator `CD 0` never skips
theorem Iterators.Types.Take.isPlausibleStep_take_skip.h8 :
    ¬ drop0% Std.Iterators.Types.Take.isPlausibleStep_take_skip 8 := fun h => by
  have := h (m := Id) (α := CD) (β := Nat) (it' := c 0) (n := 0) (it := c 0)
  inv this

/-! ## Consumers: evaluation on `CD` -/

theorem CD.step0 : (ci 0).step.val = .done := by
  simp only [Iter.step, IterM.step, Iterator.step, IterM.Step.toPure, Id.run, pure]
  erw [Shrink.inflate_deflate]; rfl
theorem CD.stepS (k : Nat) : (ci (k + 1)).step.val = .yield (ci k) k := by
  simp only [Iter.step, IterM.step, Iterator.step, IterM.Step.toPure, Id.run, pure]
  erw [Shrink.inflate_deflate]; rfl

theorem CD.toList0 : (ci 0).toList = [] := by
  rw [Iter.toList_eq_match_step, CD.step0]

theorem CD.toListS (k : Nat) : (ci (k + 1)).toList = k :: (ci k).toList := by
  rw [Iter.toList_eq_match_step, CD.stepS]

theorem CD.atIdx0 (i : Nat) : (ci 0).atIdxSlow? i = none := by
  rw [Iter.atIdxSlow?_eq_match, CD.step0]

theorem CD.atIdxS0 (k : Nat) : (ci (k + 1)).atIdxSlow? 0 = some k := by
  rw [Iter.atIdxSlow?_eq_match, CD.stepS]

theorem CD.atIdxSS (k i : Nat) : (ci (k + 1)).atIdxSlow? (i + 1) = (ci k).atIdxSlow? i := by
  rw [Iter.atIdxSlow?_eq_match, CD.stepS]

theorem ND.step_true : (⟨⟨true⟩⟩ : Iter (α := ND) Nat).step.val = .done := by
  simp only [Iter.step, IterM.step, Iterator.step, IterM.Step.toPure, Id.run, pure]
  erw [Shrink.inflate_deflate]; rfl

theorem ND.toList_true : (⟨⟨true⟩⟩ : Iter (α := ND) Nat).toList = [] := by
  rw [Iter.toList_eq_match_step, ND.step_true]

theorem ND.out_true : (⟨⟨true⟩⟩ : Iter (α := ND) Nat).IsPlausibleIndirectOutput 0 := by
  rw [Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM]
  exact .direct ⟨⟨⟨false⟩⟩, Or.inr ⟨rfl, rfl⟩⟩

abbrev sy (n : Nat) : Iter (α := SY) Nat := ⟨⟨n⟩⟩

theorem SY.step2 : (sy 2).step.val = .skip (sy 1) := by
  simp only [Iter.step, IterM.step, Iterator.step, IterM.Step.toPure, Id.run, pure]
  erw [Shrink.inflate_deflate]; rfl

theorem SY.step1 : (sy 1).step.val = .yield (sy 0) 0 := by
  simp only [Iter.step, IterM.step, Iterator.step, IterM.Step.toPure, Id.run, pure]
  erw [Shrink.inflate_deflate]; rfl

theorem SY.atIdx2 : (sy 2).atIdxSlow? 0 = some 0 := by
  rw [Iter.atIdxSlow?_eq_match, SY.step2]
  dsimp only
  rw [Iter.atIdxSlow?_eq_match, SY.step1]

theorem SY.yield_one (it it' : Iter (α := SY) Nat) (out : Nat)
    (h : it.IsPlausibleStep (.yield it' out)) : it.internalState.n = 1 := by
  obtain ⟨⟨n⟩⟩ := it
  change _ = SY.stepv n at h
  match n, h with
  | 0, h => cases h
  | 1, _ => rfl
  | k + 2, h => cases h

-- `Std.Iter.atIdxSlow?.induct_unfolding`, idx 5 (yield_zero): motive `n = 0 → r = none`; `(CD 1).atIdxSlow? 0 = some 0`
theorem Iter.atIdxSlow?.induct_unfolding.h5 : ¬ drop0% Std.Iter.atIdxSlow?.induct_unfolding 5 := fun h => by
  have := h (α := CD) (β := Nat) (motive := fun n _ r => n = 0 → r = none)
    (fun _ _ _ _ _ k _ hk => absurd hk (Nat.succ_ne_zero k)) (fun _ _ _ _ _ ih => ih)
    (fun _ _ _ _ => fun _ => rfl) 0 (ci 1)
  simp [CD.atIdxS0] at this

-- `Std.Iter.atIdxSlow?.induct_unfolding`, idx 6 (yield_succ): motive `n ≠ 0 → r = none`; `(CD 2).atIdxSlow? 1 = some 0`
theorem Iter.atIdxSlow?.induct_unfolding.h6 : ¬ drop0% Std.Iter.atIdxSlow?.induct_unfolding 6 := fun h => by
  have := h (α := CD) (β := Nat) (motive := fun n _ r => n ≠ 0 → r = none)
    (fun _ _ _ _ _ h0 => absurd rfl h0) (fun _ _ _ _ _ ih => ih)
    (fun _ _ _ _ => fun _ => rfl) 1 (ci 2)
  simp [CD.atIdxSS, CD.atIdxS0] at this

-- `Std.Iter.atIdxSlow?.induct_unfolding`, idx 7 (skip_case): `SY` (2 skips to 1, which yields 0); motive `2 ≤ state → r = none`
theorem Iter.atIdxSlow?.induct_unfolding.h7 : ¬ drop0% Std.Iter.atIdxSlow?.induct_unfolding 7 := fun h => by
  have := h (α := SY) (β := Nat) (motive := fun _ it r => 2 ≤ it.internalState.n → r = none)
    (fun it it' out p _ h2 => by have := SY.yield_one it it' out p; omega)
    (fun it it' out p _ _ _ h2 => by have := SY.yield_one it it' out p; omega)
    (fun _ _ _ _ => fun _ => rfl) 0 (sy 2)
  simp [SY.atIdx2] at this

-- `Std.Iter.atIdxSlow?.induct_unfolding`, idx 8 (done_case): motive `r ≠ none`; `(CD 0).atIdxSlow? 0 = none`
theorem Iter.atIdxSlow?.induct_unfolding.h8 : ¬ drop0% Std.Iter.atIdxSlow?.induct_unfolding 8 := fun h => by
  have := h (α := CD) (β := Nat) (motive := fun _ _ r => r ≠ none)
    (fun _ _ _ _ _ => Option.some_ne_none _) (fun _ _ _ _ _ _ ih => ih) (fun _ _ _ _ _ ih => ih) 0 (ci 0)
  simp [CD.atIdx0] at this

-- `Std.Iter.atIdxSlow?_append_of_eq_some`, idx 11 (h): `CD 1 ++ CD 0` at index 0 is `some 0` (by the theorem itself), not `some 5`
theorem Iter.atIdxSlow?_append_of_eq_some.h11 :
    ¬ drop0% Std.Iter.atIdxSlow?_append_of_eq_some 11 := fun h => by
  have h1 := h (α₁ := CD) (α₂ := CD) (β := Nat) (it₁ := ci 1) (it₂ := ci 0) (n := 0) (b := 5)
  rw [Iter.atIdxSlow?_append_of_eq_some (CD.atIdxS0 0)] at h1
  cases h1

-- `Std.Iter.atIdxSlow?_append_of_productive`, idx 11 (hk): `CD 1 ++ CD 2`, `k = n = 0`: index 0 is `some 0`, `(CD 2)[0] = some 1`
theorem Iter.atIdxSlow?_append_of_productive.h11 :
    ¬ drop0% Std.Iter.atIdxSlow?_append_of_productive 11 := fun h => by
  have h1 := h (α₁ := CD) (α₂ := CD) (β := Nat) (it₁ := ci 1) (it₂ := ci 2) (n := 0) (k := 0)
    (fun j hj => absurd hj (Nat.not_lt_zero j)) (Nat.le_refl 0)
  rw [Iter.atIdxSlow?_append_of_eq_some (CD.atIdxS0 0), Nat.sub_self, CD.atIdxS0] at h1
  cases h1

-- `Std.Iter.atIdxSlow?_append_of_productive`, idx 12 (hmin): `CD 1 ++ CD 2`, `k = n = 2`: index 2 is `(CD 2)[1] = some 0`, not `(CD 2)[0] = some 1`
theorem Iter.atIdxSlow?_append_of_productive.h12 :
    ¬ drop0% Std.Iter.atIdxSlow?_append_of_productive 12 := fun h => by
  have h1 := h (α₁ := CD) (α₂ := CD) (β := Nat) (it₁ := ci 1) (it₂ := ci 2) (n := 2) (k := 2)
    (by rw [CD.atIdxSS, CD.atIdx0]) (Nat.le_refl 2)
  rw [Iter.atIdxSlow?_append_of_productive (k := 1) (by rw [CD.atIdxSS, CD.atIdx0])
    (fun j hj => by rw [show j = 0 by omega, CD.atIdxS0]; rfl) (by omega)] at h1
  simp [CD.atIdxSS, CD.atIdxS0] at h1

-- `Std.Iter.atIdxSlow?_append_of_productive`, idx 13 (hle): `CD 1 ++ CD 2`, `k = 1`, `n = 0`: index 0 is `some 0`, `(CD 2)[0] = some 1`
theorem Iter.atIdxSlow?_append_of_productive.h13 :
    ¬ drop0% Std.Iter.atIdxSlow?_append_of_productive 13 := fun h => by
  have h1 := h (α₁ := CD) (α₂ := CD) (β := Nat) (it₁ := ci 1) (it₂ := ci 2) (n := 0) (k := 1)
    (by rw [CD.atIdxSS, CD.atIdx0]) (fun j hj => by rw [show j = 0 by omega, CD.atIdxS0]; rfl)
  rw [Iter.atIdxSlow?_append_of_eq_some (CD.atIdxS0 0), Nat.zero_sub, CD.atIdxS0] at h1
  cases h1

-- `Std.Iter.toList_eq_of_atIdxSlow?_eq`, idx 9 (h): `(CD 0).toList = []`, `(CD 1).toList = [0]`
theorem Iter.toList_eq_of_atIdxSlow?_eq.h9 : ¬ drop0% Std.Iter.toList_eq_of_atIdxSlow?_eq 9 := fun h => by
  have := h (α₁ := CD) (α₂ := CD) (β := Nat) (it₁ := ci 0) (it₂ := ci 1)
  rw [CD.toList0, CD.toListS, CD.toList0] at this
  cases this

-- `Std.Iter.isPlausibleIndirectOutput_of_mem_toList`, idx 6 (a): `CD 0` has no plausible output
theorem Iter.isPlausibleIndirectOutput_of_mem_toList.h6 :
    ¬ drop0% Std.Iter.isPlausibleIndirectOutput_of_mem_toList 6 := fun h =>
  CD.no_out0' 0 (h (α := CD) (β := Nat) (it := ci 0) (b := 0))

-- `Std.Iter.isPlausibleIndirectOutput_of_mem_toListRev`, idx 6 (a): `CD 0` has no plausible output
theorem Iter.isPlausibleIndirectOutput_of_mem_toListRev.h6 :
    ¬ drop0% Std.Iter.isPlausibleIndirectOutput_of_mem_toListRev 6 := fun h =>
  CD.no_out0' 0 (h (α := CD) (β := Nat) (it := ci 0) (b := 0))

-- `Std.Iter.isPlausibleIndirectOutput_of_mem_toArray`, idx 6 (a): `CD 0` has no plausible output
theorem Iter.isPlausibleIndirectOutput_of_mem_toArray.h6 :
    ¬ drop0% Std.Iter.isPlausibleIndirectOutput_of_mem_toArray 6 := fun h =>
  CD.no_out0' 0 (h (α := CD) (β := Nat) (it := ci 0) (b := 0))

-- `Std.Iter.isPlausibleStep_iff_step_eq`, idx 4 (inst): `ND` state `true` may yield, but `step` is `done`
theorem Iter.isPlausibleStep_iff_step_eq.h4 : ¬ drop0% Std.Iter.isPlausibleStep_iff_step_eq 4 := fun h => by
  have := (h (α := ND) (β := Nat) (it := ⟨⟨true⟩⟩) (step := .yield ⟨⟨false⟩⟩ 0)).1 (Or.inr ⟨rfl, rfl⟩)
  rw [ND.step_true] at this
  cases this

-- `Std.Iter.mem_toList_iff_isPlausibleIndirectOutput`, idx 4 (inst): `ND` state `true`: `toList = []`, but `0` is a plausible output
theorem Iter.mem_toList_iff_isPlausibleIndirectOutput.h4 :
    ¬ drop0% Std.Iter.mem_toList_iff_isPlausibleIndirectOutput 4 := fun h => by
  have := (h (α := ND) (β := Nat) (it := ⟨⟨true⟩⟩) (out := 0)).2 ND.out_true
  rw [ND.toList_true] at this
  cases this

-- `Std.Iter.mem_toArray_iff_isPlausibleIndirectOutput`, idx 4 (inst): `ND` state `true`: `toArray = #[]`, but `0` is a plausible output
theorem Iter.mem_toArray_iff_isPlausibleIndirectOutput.h4 :
    ¬ drop0% Std.Iter.mem_toArray_iff_isPlausibleIndirectOutput 4 := fun h => by
  have := (h (α := ND) (β := Nat) (it := ⟨⟨true⟩⟩) (out := 0)).2 ND.out_true
  rw [← Iter.toArray_toList, ND.toList_true] at this
  simp at this

/-! ## Loops: `forIn` congruence (with `CD.firstLoop`), `fold`, default loop unfolding -/

-- `Std.Iter.forIn_congr`, idx 10 (w): `CD.firstLoop`; `f a _ = pure (.done a)`: `CD 1` gives `0`, `CD 2` gives `1`
theorem Iter.forIn_congr.h10 : ¬ drop0% Std.Iter.forIn_congr 10 := fun h => by
  letI : IteratorLoop CD Id Id := CD.firstLoop
  have := h (γ := Nat) (α := CD) (m := Id) (ita := ci 1) (itb := ci 2) (b := 5) (b' := 5) rfl
    (f := fun a _ => pure (.done a)) (g := fun a _ => pure (.done a)) (fun _ _ => rfl)
  have h01 : (0 : Nat) = 1 := this
  exact absurd h01 (by decide)

-- `Std.Iter.forIn_congr`, idx 13 (hb): `CD.firstLoop` on `CD 0` returns `init`: `0 ≠ 1`
theorem Iter.forIn_congr.h13 : ¬ drop0% Std.Iter.forIn_congr 13 := fun h => by
  letI : IteratorLoop CD Id Id := CD.firstLoop
  have := h (γ := Nat) (α := CD) (m := Id) (ita := ci 0) (itb := ci 0) rfl (b := 0) (b' := 1)
    (f := fun a _ => pure (.done a)) (g := fun a _ => pure (.done a)) (fun _ _ => rfl)
  have h01 : (0 : Nat) = 1 := this
  exact absurd h01 (by decide)

-- `Std.Iter.forIn_congr`, idx 16 (h): `CD.firstLoop` on `CD 1` with `f` returning `0`, `g` returning `1`
theorem Iter.forIn_congr.h16 : ¬ drop0% Std.Iter.forIn_congr 16 := fun h => by
  letI : IteratorLoop CD Id Id := CD.firstLoop
  have := h (γ := Nat) (α := CD) (m := Id) (ita := ci 1) (itb := ci 1) rfl (b := 5) (b' := 5) rfl
    (f := fun _ _ => pure (.done 0)) (g := fun _ _ => pure (.done 1))
  have h01 : (0 : Nat) = 1 := this
  exact absurd h01 (by decide)

-- `Std.Iter.forIn'_congr`, idx 13 (hb): `CD.firstLoop` on `CD 0` returns `init`: `0 ≠ 1`
theorem Iter.forIn'_congr.h13 : ¬ drop0% Std.Iter.forIn'_congr 13 := fun h => by
  letI : IteratorLoop CD Id Id := CD.firstLoop
  have := h (γ := Nat) (α := CD) (m := Id) (ita := ci 0) (itb := ci 0) rfl (b := 0) (b' := 1)
    (f := fun a _ _ => pure (.done a)) (g := fun a _ _ => pure (.done a)) (fun _ _ _ => rfl)
  have h01 : (0 : Nat) = 1 := this
  exact absurd h01 (by decide)

-- `Std.Iter.forIn'_congr`, idx 16 (h): `CD.firstLoop` on `CD 1` with `f` returning `0`, `g` returning `1`
theorem Iter.forIn'_congr.h16 : ¬ drop0% Std.Iter.forIn'_congr 16 := fun h => by
  letI : IteratorLoop CD Id Id := CD.firstLoop
  have := h (γ := Nat) (α := CD) (m := Id) (ita := ci 1) (itb := ci 1) rfl (b := 5) (b' := 5) rfl
    (f := fun _ _ _ => pure (.done 0)) (g := fun _ _ _ => pure (.done 1))
  have h01 : (0 : Nat) = 1 := this
  exact absurd h01 (by decide)

-- `Std.IterM.forIn_congr`, idx 12 (w): `CD.firstLoop`; `f a _ = pure (.done a)`: `CD 1` gives `0`, `CD 2` gives `1`
theorem IterM.forIn_congr.h12 : ¬ drop0% Std.IterM.forIn_congr 12 := fun h => by
  letI : IteratorLoop CD Id Id := CD.firstLoop
  have := h (γ := Nat) (α := CD) (m := Id) (n := Id) (ita := c 1) (itb := c 2) (b := 5) (b' := 5) rfl
    (f := fun a _ => pure (.done a)) (g := fun a _ => pure (.done a)) (fun _ _ => rfl)
  have h01 : (0 : Nat) = 1 := this
  exact absurd h01 (by decide)

-- `Std.IterM.forIn_congr`, idx 15 (hb): `CD.firstLoop` on `CD 0` returns `init`: `0 ≠ 1`
theorem IterM.forIn_congr.h15 : ¬ drop0% Std.IterM.forIn_congr 15 := fun h => by
  letI : IteratorLoop CD Id Id := CD.firstLoop
  have := h (γ := Nat) (α := CD) (m := Id) (n := Id) (ita := c 0) (itb := c 0) rfl (b := 0) (b' := 1)
    (f := fun a _ => pure (.done a)) (g := fun a _ => pure (.done a)) (fun _ _ => rfl)
  have h01 : (0 : Nat) = 1 := this
  exact absurd h01 (by decide)

-- `Std.IterM.forIn_congr`, idx 18 (h): `CD.firstLoop` on `CD 1` with `f` returning `0`, `g` returning `1`
theorem IterM.forIn_congr.h18 : ¬ drop0% Std.IterM.forIn_congr 18 := fun h => by
  letI : IteratorLoop CD Id Id := CD.firstLoop
  have := h (γ := Nat) (α := CD) (m := Id) (n := Id) (ita := c 1) (itb := c 1) rfl (b := 5) (b' := 5) rfl
    (f := fun _ _ => pure (.done 0)) (g := fun _ _ => pure (.done 1))
  have h01 : (0 : Nat) = 1 := this
  exact absurd h01 (by decide)

-- `Std.IterM.forIn'_congr`, idx 15 (hb): `CD.firstLoop` on `CD 0` returns `init`: `0 ≠ 1`
theorem IterM.forIn'_congr.h15 : ¬ drop0% Std.IterM.forIn'_congr 15 := fun h => by
  letI : IteratorLoop CD Id Id := CD.firstLoop
  have := h (γ := Nat) (α := CD) (m := Id) (n := Id) (ita := c 0) (itb := c 0) rfl (b := 0) (b' := 1)
    (f := fun a _ _ => pure (.done a)) (g := fun a _ _ => pure (.done a)) (fun _ _ _ => rfl)
  have h01 : (0 : Nat) = 1 := this
  exact absurd h01 (by decide)

-- `Std.IterM.forIn'_congr`, idx 18 (h): `CD.firstLoop` on `CD 1` with `f` returning `0`, `g` returning `1`
theorem IterM.forIn'_congr.h18 : ¬ drop0% Std.IterM.forIn'_congr 18 := fun h => by
  letI : IteratorLoop CD Id Id := CD.firstLoop
  have := h (γ := Nat) (α := CD) (m := Id) (n := Id) (ita := c 1) (itb := c 1) rfl (b := 5) (b' := 5) rfl
    (f := fun _ _ _ => pure (.done 0)) (g := fun _ _ _ => pure (.done 1))
  have h01 : (0 : Nat) = 1 := this
  exact absurd h01 (by decide)

-- `Std.Iter.fold_hom`, idx 15 (H): `CD 1`, `f = id`, `g₁ x _ = x`, `g₂ x _ = x + 1`: `1 ≠ 0`
theorem Iter.fold_hom.h15 : ¬ drop0% Std.Iter.fold_hom 15 := fun h => by
  have := h (α := CD) (β := Nat) (γ₁ := Nat) (γ₂ := Nat) (it := ci 1) (f := id) (g₁ := fun x _ => x)
    (g₂ := fun x _ => x + 1) (init := 0)
  rw [← Iter.foldl_toList, ← Iter.foldl_toList, CD.toListS, CD.toList0] at this
  cases this

-- `Std.IterM.fold_hom`, idx 16 (H): `CD 1` in `Id`, `f = id`, `g₁ x _ = x`, `g₂ x _ = x + 1`: `1 ≠ 0`
theorem IterM.fold_hom.h16 : ¬ drop0% Std.IterM.fold_hom 16 := fun h => by
  have := h (α := CD) (β := Nat) (γ₁ := Nat) (γ₂ := Nat) (m := Id) (it := c 1) (f := id) (g₁ := fun x _ => x)
    (g₂ := fun x _ => x + 1) (init := 0)
  have e (g : Nat → Nat → Nat) (i : Nat) : (c 1).fold g i = pure ((ci 1).fold g i) := by
    rw [Iter.fold_eq_fold_toIterM]; rfl
  rw [e, e, ← Iter.foldl_toList, ← Iter.foldl_toList, CD.toListS, CD.toList0] at this
  cases this

/-! ## The default loop and `LawfulIteratorLoop` -/

-- `Std.IterM.DefaultConsumers.forIn'_eq_match_step`, idx 15 (wf): `LP` (skips to itself) with the lift `postCnt` (continuation, then increment): the equation says `X = X <* increment`
theorem IterM.DefaultConsumers.forIn'_eq_match_step.h15 :
    ¬ drop0% Std.IterM.DefaultConsumers.forIn'_eq_match_step 15 := fun h => by
  have := h (α := LP) (β := Nat) (m := Id) (n := StateM Nat) (lift := postCnt) (γ := Nat) (it := ⟨⟨()⟩⟩)
    (init := 0) (P := fun _ => True) (hP := fun _ _ => trivial) (PlausibleForInStep := fun _ _ _ => True)
    (f := fun _ _ c => pure ⟨.yield c, trivial⟩)
  have := congrArg (fun y : StateM Nat Nat => (y.run 0).2) this
  simp [postCnt, Shrink.inflate_deflate] at this
  have e : ∀ p : Id (Nat × Nat),
      (Functor.map (f := Id) (fun a : Nat × Nat => (a.1, a.2 + 1)) p).snd = p.snd + 1 :=
    fun _ => rfl
  rw [e] at this
  exact Nat.succ_ne_self _ this.symm

-- `Std.IterM.DefaultConsumers.forIn'_eq_forIn'`, idx 19 (hfg): `CD 1` (well-founded), `f` returns `.done 0`, `g` returns `.done 1`
theorem IterM.DefaultConsumers.forIn'_eq_forIn'.h19 :
    ¬ drop0% Std.IterM.DefaultConsumers.forIn'_eq_forIn' 19 := fun h => by
  have := h (α := CD) (β := Nat) (m := Id) (n := Id) (lift := fun _ _ f x => f x.run) (γ := Nat) (it := c 1)
    (init := 5) (P := fun _ => True) (hP := fun _ _ => trivial) (Q := fun _ => True) (hQ := fun _ _ => trivial)
    (Pl := fun _ _ _ => True) (f := fun _ _ _ => pure ⟨.done 0, trivial⟩)
    (g := fun _ _ _ => pure ⟨.done 1, trivial⟩) (wf := IteratorLoop.wellFounded_of_finite)
  rw [IterM.DefaultConsumers.forIn'_eq_match_step (wf := IteratorLoop.wellFounded_of_finite),
    IterM.DefaultConsumers.forIn'_eq_match_step (wf := IteratorLoop.wellFounded_of_finite)] at this
  simp [Shrink.inflate_deflate, CD.stepv] at this

-- `Std.LawfulIteratorLoop.lawful`, idx 10 (inst): `CD.preLoop` (lifts `pure ()` first) is lawful, but not for the lift `cntLiftBind`
theorem LawfulIteratorLoop.lawful.h10 : ¬ drop0% Std.LawfulIteratorLoop.lawful 10 := fun h => by
  have := h (β := Nat) (α := CD) (m := Id) (n := StateM Nat) (i := CD.preLoop) (self := CD.preLoop_lawful)
    (lift := cntLiftBind) (γ := Nat) (it := c 0) (init := 0) (Pl := fun _ _ _ => True)
    (wf := IteratorLoop.wellFounded_of_finite) (f := fun _ _ c => pure ⟨.yield c, trivial⟩)
  rw [CD.preLoop_forIn] at this
  rw [CD.default_forIn, IterM.DefaultConsumers.forIn'_eq_match_step (wf := IteratorLoop.wellFounded_of_finite)] at this
  have := congrArg (fun y : StateM Nat Nat => (y.run 0).2) this
  simp [cntLiftBind, Shrink.inflate_deflate, CD.stepv] at this
  have e : (2 : Nat) = 1 := this
  cases e

-- `Std.LawfulIteratorLoop.lawful`, idx 15 (wf): `LP.wfLoop 0` and `LP.wfLoop 1` are both lawful but differ on the non-well-founded loop over `LP`
theorem LawfulIteratorLoop.lawful.h15 : ¬ drop0% Std.LawfulIteratorLoop.lawful 15 := fun h => by
  have h0 := h (β := Nat) (α := LP) (m := Id) (n := StateM Nat) (i := LP.wfLoop 0) (self := LP.wfLoop_lawful 0)
    (lift := fun _ _ f x => f x.run) (γ := Nat) (it := ⟨⟨()⟩⟩) (init := 0) (Pl := fun _ _ _ => True)
    (f := fun _ _ c => pure ⟨.yield c, trivial⟩)
  have h1 := h (β := Nat) (α := LP) (m := Id) (n := StateM Nat) (i := LP.wfLoop 1) (self := LP.wfLoop_lawful 1)
    (lift := fun _ _ f x => f x.run) (γ := Nat) (it := ⟨⟨()⟩⟩) (init := 0) (Pl := fun _ _ _ => True)
    (f := fun _ _ c => pure ⟨.yield c, trivial⟩)
  have := h0.trans h1.symm
  rw [LP.wfLoop_forIn_nwf _ _ _ _ _ _ _ (LP.not_wf (n := Id) 0),
    LP.wfLoop_forIn_nwf _ _ _ _ _ _ _ (LP.not_wf (n := Id) 0)] at this
  have := congrArg (fun y : StateM Nat Nat => (y.run 0).2) this
  simp at this

end ItDepOtherHand
