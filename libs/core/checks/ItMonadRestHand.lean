import Lean

/-!
Hand pass `ItMonadRest` (hand8): 102 non-dependent monad-law hypotheses (`[LawfulMonad m]`,
`[LawfulMonadLiftT m n]`, `LawfulMonadLiftFunction`, ...) of `Init.Data.Iterators` lemmas: the
`IterM` consumer lemmas (`Lemmas/Consumers/Monadic/Loop`, `Collect`), `Internal/LawfulMonadLiftFunction`,
`PostconditionMonad`, `ULiftT`, the list producer and one `flatMap` plausibility lemma. For hypothesis
`hᵢ` of theorem `T` this file proves `¬T'` (`drop0% T i`, universes set to `0`) or `T'` (`drop% T i`).

96 necessary, 4 removable, 2 left unresolved (`IterM.reverse_toListRev` and its `ensureTermination`
twin: both sides run the same fixpoint shape with one final `map`, so every parametric monad satisfies
them; a counterexample would have to tell `Array β` from `List β` apart).

Removable (4): `IterM.findSomeM?_pure` and `IterM.findM?_pure` (`rfl`, both sides unfold to the same
loop), `IterM.DefaultConsumers.forIn'_eq_forIn'` (well-founded induction, unfolding each loop once with
`extrinsicFix₃_eq_apply`, which needs no monad laws), `Flatten.IsPlausibleStep.outerYield_flatMapM_pure`
(the plausible-step relations involved need no monad laws).

Reusable counterexamples:
* `KM bd mp`: the monad `Nat × α` with `pure a = (0, a)`, `bind` combining counters by `bd`, and
  `map`/`seq`/`seqLeft`/`seqRight` applying `mp` to the counter `bind` would give. Instances:
  `CW` (bind `+1`, map `+1`), `CM` (bind `+1`), `WM` (bind `+`, map `+1`), `AM` (bind `2a + b`, not
  associative), `DM` (map doubles), `FM` (bind forgets the first counter). `KM.c` is the counter,
  with simp lemmas `KM.c_pure`/`c_bind`/`c_map`/`snd_pure`.
* lifts: `cntL`/`cntLT` (`Id → StateM Nat`, increments; not lawful), `wmL` (`WM → StateM Nat`, adds the
  counter; `LawfulMonadLiftFunction`), `chL` (`Id → Id`, `Classical.choice`: not natural), `noneLT`
  (`MonadLiftT Id Option`, always `none`).
* `CD` (countdown iterator of `ItDepOtherHand`) with the loop instance `CD.vloop`: the default loop
  if the lift-bind function is a `LawfulMonadLiftBindFunction`, otherwise `CD.alt` (applies the step
  function once to the first output, without stepping). `LawfulIteratorLoop` holds by `if_pos`, but in
  a non-lawful monad (`CW`) the lifts `monadLift x >>= f` and `flip bind` are not lawful
  (`CW.not_lb`, `CW.not_lb_flip`, `CW.not_lb_id`, `noneLT.not_lb`), so the loop is `CD.alt`.
  This shows the consumer lemmas need `LawfulMonad` already because `LawfulIteratorLoop` constrains
  the loop only for lawful lifts.
* evaluation: `ev` unfolds `toArray`/`toListRev`/`toList` and the default loop one step at a time
  (`extrinsicFix₂/₃_eq_apply` with `finWf`/`loopWf`) and computes `KM` counters; `loopsimp` unfolds
  the loop-based consumers to `IteratorLoop.forIn`.

Run with the lean4 repo's stage1 binary: `lean checks/ItMonadRestHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
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


namespace ItMonadRestHand
open Std Std.Iterators

/-! `KM bd mp`: writer-like monad `Nat × α`, `pure a = (0, a)`, `bind` combines the counters with
`bd`, `map`, `seq`, `seqLeft`, `seqRight` apply `mp` to the counter they would get from `bind`. -/
def KM (bd : Nat → Nat → Nat) (mp : Nat → Nat) (α : Type) : Type := Nat × α

instance KM.monad {bd : Nat → Nat → Nat} {mp : Nat → Nat} : Monad (KM bd mp) where
  pure a := ((0 : Nat), a)
  bind x f := (bd (x : Nat × _).1 ((f (x : Nat × _).2) : Nat × _).1, ((f (x : Nat × _).2) : Nat × _).2)
  map f x := (mp (x : Nat × _).1, f (x : Nat × _).2)
  seq f x := (mp (bd (f : Nat × _).1 ((x ()) : Nat × _).1), (f : Nat × _).2 ((x ()) : Nat × _).2)
  seqLeft x y := (mp (bd (x : Nat × _).1 (bd ((y ()) : Nat × _).1 0)), (x : Nat × _).2)
  seqRight x y := (mp (bd (x : Nat × _).1 ((y ()) : Nat × _).1), ((y ()) : Nat × _).2)

/-- counter of a `KM` value -/
abbrev KM.c {bd mp} {α : Type} (x : KM bd mp α) : Nat := (x : Nat × α).1

/-- `bind` adds `1`, `map` adds `1`. -/
abbrev CW := KM (fun a b => a + b + 1) Nat.succ
/-- `bind` adds `1`, `map` keeps the counter (the `CM` of `ItDepOtherHand`). -/
abbrev CM := KM (fun a b => a + b + 1) id
/-- `bind` adds, `map` adds `1`. -/
abbrev WM := KM (· + ·) Nat.succ
/-- non-associative `bind` (`2a + b`), `map` keeps the counter. -/
abbrev AM := KM (fun a b => 2 * a + b) id
/-- `bind` adds, `map` doubles. -/
abbrev DM := KM (· + ·) (2 * ·)
/-- `bind` forgets the counter of its first argument. -/
abbrev FM := KM (fun _ b => b) id




/-! ## Lifts -/

/-- Counting lift `Id → StateM Nat`: increments the state. -/
def cntL ⦃α : Type⦄ (x : Id α) : StateM Nat α := (modify (· + 1) : StateM Nat PUnit) *> pure x.run

/-- `cntL` as a `MonadLiftT` instance (not lawful). -/
@[reducible] def cntLT : MonadLiftT Id (StateM Nat) := ⟨fun x => cntL x⟩

/-- Lift `WM → StateM Nat` adding the counter to the state (lawful). -/
def wmL ⦃α : Type⦄ (x : WM α) : StateM Nat α := (modify (· + x.c) : StateM Nat PUnit) *> pure (x : Nat × α).2

instance wmL.lawful : Internal.LawfulMonadLiftFunction wmL where
  lift_pure a := by
    funext s; simp [wmL, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      SeqRight.seqRight, StateT.bind, bind]; rfl
  lift_bind x f := by
    funext s; simp [wmL, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      SeqRight.seqRight, StateT.bind, bind, Nat.add_assoc]

/-- Value-independent lift `Id → Id`: a fixed element of each type (not natural). -/
noncomputable def chL ⦃α : Type⦄ (x : Id α) : Id α := Classical.choice ⟨x⟩

-- `Std.Internal.LawfulMonadLiftFunction.lift_pure`, idx 5 (self): `cntL` increments the state
theorem Internal.LawfulMonadLiftFunction.lift_pure.h5 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_pure 5 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2) (@h Id (StateM Nat) inferInstance inferInstance cntL Nat 0)
  simp [cntL] at this

-- `Std.Internal.LawfulMonadLiftFunction.lift_bind`, idx 5 (self): `cntL` counts one vs two lifts
theorem Internal.LawfulMonadLiftFunction.lift_bind.h5 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_bind 5 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    (@h Id (StateM Nat) inferInstance inferInstance cntL Nat Nat (pure 0) pure)
  simp [cntL] at this

-- `Std.Internal.instLawfulMonadLiftFunctionMonadLiftOfLawfulMonadLiftT`, idx 5 (inst): `MonadLiftT Id (StateM Nat)` by `cntL`
theorem Internal.instLawfulMonadLiftFunctionMonadLiftOfLawfulMonadLiftT.h5 :
    ¬ drop0% Std.Internal.instLawfulMonadLiftFunctionMonadLiftOfLawfulMonadLiftT 5 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    ((@h Id _ (StateM Nat) _ cntLT).lift_pure 0)
  simp [cntL, monadLift] at this

-- `Std.Internal.instLawfulMonadLiftOfLawfulMonadLiftFunction`, idx 5 (inst): lift `cntL`
theorem Internal.instLawfulMonadLiftOfLawfulMonadLiftFunction.h5 :
    ¬ drop0% Std.Internal.instLawfulMonadLiftOfLawfulMonadLiftFunction 5 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    ((@h Id (StateM Nat) inferInstance inferInstance cntL).monadLift_pure 0)
  simp [cntL, MonadLift.monadLift] at this

-- `Std.Internal.LawfulMonadLiftFunction.lift_map`, idx 7 (inst): `m = WM` (`map` adds 1), `n = StateM Nat`, lawful lift `wmL`
theorem Internal.LawfulMonadLiftFunction.lift_map.h7 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_map 7 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    (@h WM (StateM Nat) _ _ wmL Nat Nat _ _ id ((0 : Nat), 0))
  exact absurd this (by decide)

-- `Std.Internal.LawfulMonadLiftFunction.lift_map`, idx 8 (inst): `n = WM` (`map` adds 1), `m = Id`, lawful lift `idToMonad`
theorem Internal.LawfulMonadLiftFunction.lift_map.h8 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_map 8 := fun h => by
  have := congrArg KM.c
    (@h Id WM _ _ Internal.idToMonad Nat Nat _ ⟨fun _ => rfl, fun _ _ => rfl⟩ id 0)
  cases this

-- `Std.Internal.LawfulMonadLiftFunction.lift_map`, idx 9 (inst): `m = n = Id`, `chL` (a fixed element of each type) commutes with `not` only if `c = !c`
theorem Internal.LawfulMonadLiftFunction.lift_map.h9 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_map 9 := fun h => by
  have := @h Id Id _ _ chL Bool Bool _ _ not true
  revert this
  change chL (α := Bool) false ≠ not (chL (α := Bool) true)
  unfold chL
  generalize Classical.choice _ = c
  cases c <;> exact fun h => nomatch h


-- `Std.Internal.LawfulMonadLiftFunction.lift_seq`, idx 7 (inst): `m = WM` (`seq` adds 1), `n = StateM Nat`, lawful lift `wmL`
theorem Internal.LawfulMonadLiftFunction.lift_seq.h7 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_seq 7 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    (@h WM (StateM Nat) _ _ wmL Nat Nat _ _ ((0 : Nat), id) ((0 : Nat), 0))
  exact absurd this (by decide)

-- `Std.Internal.LawfulMonadLiftFunction.lift_seq`, idx 8 (inst): `n = WM` (`seq` adds 1), `m = Id`, lawful lift `idToMonad`
theorem Internal.LawfulMonadLiftFunction.lift_seq.h8 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_seq 8 := fun h => by
  have := congrArg KM.c
    (@h Id WM _ _ Internal.idToMonad Nat Nat _ ⟨fun _ => rfl, fun _ _ => rfl⟩ id 0)
  cases this

-- `Std.Internal.LawfulMonadLiftFunction.lift_seq`, idx 9 (inst): `cntL` counts one vs two lifts
theorem Internal.LawfulMonadLiftFunction.lift_seq.h9 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_seq 9 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    (@h Id (StateM Nat) _ _ cntL Nat Nat _ _ id 0)
  simp [cntL] at this

-- `Std.Internal.LawfulMonadLiftFunction.lift_seqLeft`, idx 7 (inst): `m = WM` (`seqLeft` adds 1), `n = StateM Nat`, lawful lift `wmL`
theorem Internal.LawfulMonadLiftFunction.lift_seqLeft.h7 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_seqLeft 7 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    (@h WM (StateM Nat) _ _ wmL Nat Nat _ _ ((0 : Nat), 0) ((0 : Nat), 0))
  exact absurd this (by decide)

-- `Std.Internal.LawfulMonadLiftFunction.lift_seqLeft`, idx 8 (inst): `n = WM` (`seqLeft` adds 1), `m = Id`, lawful lift `idToMonad`
theorem Internal.LawfulMonadLiftFunction.lift_seqLeft.h8 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_seqLeft 8 := fun h => by
  have := congrArg KM.c
    (@h Id WM _ _ Internal.idToMonad Nat Nat _ ⟨fun _ => rfl, fun _ _ => rfl⟩ 0 0)
  cases this

-- `Std.Internal.LawfulMonadLiftFunction.lift_seqLeft`, idx 9 (inst): `cntL` counts one vs two lifts
theorem Internal.LawfulMonadLiftFunction.lift_seqLeft.h9 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_seqLeft 9 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    (@h Id (StateM Nat) _ _ cntL Nat Nat _ _ 0 0)
  simp [cntL] at this

-- `Std.Internal.LawfulMonadLiftFunction.lift_seqRight`, idx 7 (inst): `m = WM` (`seqRight` adds 1), `n = StateM Nat`, lawful lift `wmL`
theorem Internal.LawfulMonadLiftFunction.lift_seqRight.h7 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_seqRight 7 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    (@h WM (StateM Nat) _ _ wmL Nat Nat _ _ ((0 : Nat), 0) ((0 : Nat), 0))
  exact absurd this (by decide)

-- `Std.Internal.LawfulMonadLiftFunction.lift_seqRight`, idx 8 (inst): `n = WM` (`seqRight` adds 1), `m = Id`, lawful lift `idToMonad`
theorem Internal.LawfulMonadLiftFunction.lift_seqRight.h8 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_seqRight 8 := fun h => by
  have := congrArg KM.c
    (@h Id WM _ _ Internal.idToMonad Nat Nat _ ⟨fun _ => rfl, fun _ _ => rfl⟩ 0 0)
  cases this

-- `Std.Internal.LawfulMonadLiftFunction.lift_seqRight`, idx 9 (inst): `cntL` counts one vs two lifts
theorem Internal.LawfulMonadLiftFunction.lift_seqRight.h9 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.lift_seqRight 9 := fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    (@h Id (StateM Nat) _ _ cntL Nat Nat _ _ 0 0)
  simp [cntL] at this

-- `Std.Internal.LawfulMonadLiftFunction.idToMonad`, idx 2 (inst): `CM` (bind adds 1): `pure (f x)` vs `pure x >>= pure ∘ f`
theorem Internal.LawfulMonadLiftFunction.idToMonad.h2 :
    ¬ drop0% Std.Internal.LawfulMonadLiftFunction.idToMonad 2 := fun h => by
  have := congrArg KM.c ((@h CM _).lift_bind (pure (0 : Nat)) (fun x => pure x))
  cases this

-- `Std.Internal.instLawfulMonadLiftFunctionOfLawfulMonadLiftBindFunctionBindOfLawfulMonad`, idx 6 (inst): `n = FM` (`bind` forgets the first counter), lift `Id → FM` with counter `5`: `lift x >>= f` is a lawful lift-bind function, `lift` is not lawful
theorem Internal.instLawfulMonadLiftFunctionOfLawfulMonadLiftBindFunctionBindOfLawfulMonad.h6 :
    ¬ drop0% Std.Internal.instLawfulMonadLiftFunctionOfLawfulMonadLiftBindFunctionBindOfLawfulMonad 6 :=
  fun h => by
  have := congrArg KM.c
    ((@h Id FM _ _ (fun _ x => ((5 : Nat), x.run)) ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩).lift_pure 0)
  cases this

-- `Std.Internal.instLawfulMonadLiftBindFunctionBindMonadLiftOfLawfulMonadLiftTOfLawfulMonad`, idx 5 (inst): `MonadLiftT Id (StateM Nat)` by `cntL`
theorem Internal.instLawfulMonadLiftBindFunctionBindMonadLiftOfLawfulMonadLiftTOfLawfulMonad.h5 :
    ¬ drop0% Std.Internal.instLawfulMonadLiftBindFunctionBindMonadLiftOfLawfulMonadLiftTOfLawfulMonad 5 :=
  fun h => by
  have := congrArg (fun x => ((x : StateM Nat Nat).run 0).run.2)
    ((@h Id _ (StateM Nat) _ cntLT _).liftBind_pure (γ := Nat) pure 0)
  simp [cntL, monadLift] at this

-- `Std.Internal.instLawfulMonadLiftBindFunctionBindMonadLiftOfLawfulMonadLiftTOfLawfulMonad`, idx 6 (inst): `m = n = CM` (bind adds 1), lift the identity
theorem Internal.instLawfulMonadLiftBindFunctionBindMonadLiftOfLawfulMonadLiftTOfLawfulMonad.h6 :
    ¬ drop0% Std.Internal.instLawfulMonadLiftBindFunctionBindMonadLiftOfLawfulMonadLiftTOfLawfulMonad 6 :=
  fun h => by
  have := congrArg KM.c ((@h CM _ CM _ _ _).liftBind_pure (γ := Nat) (δ := Nat) pure 0)
  cases this

-- `Std.Internal.instLawfulMonadLiftBindFunctionFlipForallBindOfLawfulMonad`, idx 2 (inst): `CM` (bind adds 1)
theorem Internal.instLawfulMonadLiftBindFunctionFlipForallBindOfLawfulMonad.h2 :
    ¬ drop0% Std.Internal.instLawfulMonadLiftBindFunctionFlipForallBindOfLawfulMonad 2 := fun h => by
  have := congrArg KM.c ((@h CM _).liftBind_pure (γ := Nat) (δ := Nat) pure 0)
  cases this

-- `Std.Iterators.instLawfulMonadULiftT`, idx 2 (inst): `n = CM` (bind adds 1), so `pure_bind` fails in `ULiftT CM`
theorem Iterators.instLawfulMonadULiftT.h2 : ¬ drop0% Std.Iterators.instLawfulMonadULiftT 2 := fun h => by
  have := congrArg (fun x : ULiftT CM Nat => (x : Nat × ULift Nat).1)
    (@LawfulMonad.pure_bind _ _ (@h CM _) Nat Nat 0 pure)
  cases this


/-! ## `PostconditionT` over the broken `KM` monads -/

/-- `PostconditionT` value with property `True`, operation counter `c` and value `0`. -/
def pt {bd : Nat → Nat → Nat} {mp : Nat → Nat} (c : Nat) : PostconditionT (KM bd mp) Nat :=
  ⟨fun _ => True, (c, ⟨0, trivial⟩)⟩

/-- counter of the operation of a `PostconditionT (KM bd mp)` value -/
abbrev ptc {bd mp} {α : Type} (z : PostconditionT (KM bd mp) α) : Nat := KM.c z.operation

-- `Std.Iterators.PostconditionT.ext`, idx 2 (inst): `CW` (map adds 1): operations with counters `0` and `1` are identified by the transported `map`
theorem Iterators.PostconditionT.ext.h2 : ¬ drop0% Std.Iterators.PostconditionT.ext 2 := fun h => by
  have := congrArg ptc (@h CW _ Nat (pt 0) (pt 1) rfl rfl)
  cases this

-- `Std.Iterators.PostconditionT.ext_iff`, idx 2 (inst): `CW` (map adds 1), as for `PostconditionT.ext`
theorem Iterators.PostconditionT.ext_iff.h2 : ¬ drop0% Std.Iterators.PostconditionT.ext_iff 2 := fun h => by
  have := congrArg ptc ((@h CW _ Nat (pt 0) (pt 1)).2 ⟨rfl, rfl⟩)
  cases this

-- `Std.Iterators.PostconditionT.map_eq_pure_bind`, idx 2 (inst): `CW`: counter `1` (map) vs `2` (bind of a map)
theorem Iterators.PostconditionT.map_eq_pure_bind.h2 :
    ¬ drop0% Std.Iterators.PostconditionT.map_eq_pure_bind 2 := fun h => by
  have := congrArg ptc (@h CW _ Nat Nat id (pt 0))
  cases this

-- `Std.Iterators.PostconditionT.pure_bind`, idx 2 (inst): `CW` (bind adds 1)
theorem Iterators.PostconditionT.pure_bind.h2 : ¬ drop0% Std.Iterators.PostconditionT.pure_bind 2 := fun h => by
  have := congrArg ptc (@h CW _ Nat Nat (fun _ => pt 0) 0)
  cases this

-- `Std.Iterators.PostconditionT.bind_pure`, idx 2 (inst): `CW` (bind adds 1)
theorem Iterators.PostconditionT.bind_pure.h2 : ¬ drop0% Std.Iterators.PostconditionT.bind_pure 2 := fun h => by
  have := congrArg ptc (@h CW _ Nat (pt 0))
  cases this

-- `Std.Iterators.PostconditionT.bind_assoc`, idx 2 (inst): `AM` (bind `2a + b`, not associative): counters `4` vs `2`
theorem Iterators.PostconditionT.bind_assoc.h2 : ¬ drop0% Std.Iterators.PostconditionT.bind_assoc 2 := fun h => by
  have := congrArg ptc (@h AM _ Nat Nat Nat (pt 1) (fun _ => pt 0) (fun _ => pt 0))
  cases this

-- `Std.Iterators.PostconditionT.map_pure`, idx 2 (inst): `CW` (map adds 1)
theorem Iterators.PostconditionT.map_pure.h2 : ¬ drop0% Std.Iterators.PostconditionT.map_pure 2 := fun h => by
  have := congrArg ptc (@h CW _ Nat Nat id 0)
  cases this

-- `Std.Iterators.instLawfulMonadPostconditionT`, idx 2 (inst): `CW` (bind adds 1), `pure_bind` fails
theorem Iterators.instLawfulMonadPostconditionT.h2 :
    ¬ drop0% Std.Iterators.instLawfulMonadPostconditionT 2 := fun h => by
  have := congrArg ptc (@LawfulMonad.pure_bind _ _ (@h CW _) Nat Nat 0 (fun _ => pt 0))
  cases this

-- `Std.Iterators.PostconditionT.operation_eq_map_mk_operation`, idx 3 (inst): `CW` (map adds 1)
theorem Iterators.PostconditionT.operation_eq_map_mk_operation.h3 :
    ¬ drop0% Std.Iterators.PostconditionT.operation_eq_map_mk_operation 3 := fun h => by
  have := congrArg KM.c (@h Nat CW _ (pt 0))
  cases this

-- `Std.Iterators.PostconditionT.run_bind`, idx 2 (inst): `DM` (map doubles): counters `2 * (0 + 2 * 1) = 4` vs `2 * 0 + 2 * 1 = 2`
theorem Iterators.PostconditionT.run_bind.h2 : ¬ drop0% Std.Iterators.PostconditionT.run_bind 2 := fun h => by
  have := congrArg KM.c (@h DM _ Nat Nat (pt 0) (fun _ => pt 1))
  cases this

-- `Std.Iterators.PostconditionT.run_bind'`, idx 2 (inst): `DM` (map doubles), as for `PostconditionT.run_bind`
theorem Iterators.PostconditionT.run_bind'.h2 : ¬ drop0% Std.Iterators.PostconditionT.run_bind' 2 := fun h => by
  have := congrArg KM.c (@h DM _ Nat Nat (pt 0) (fun _ => pt 1))
  cases this

-- `Std.Iterators.PostconditionT.instLawfulMonadLift`, idx 5 (inst): `m = WM` (`map` adds 1), `n = StateM Nat`, lawful lift `wmL`; the lift of `map` adds one more
theorem Iterators.PostconditionT.instLawfulMonadLift.h5 :
    ¬ drop0% Std.Iterators.PostconditionT.instLawfulMonadLift 5 := fun h => by
  letI : MonadLift WM (StateM Nat) := ⟨fun x => wmL x⟩
  have h' := @h WM (StateM Nat) _ _ _ _ ⟨wmL.lawful.lift_pure, wmL.lawful.lift_bind⟩
  have := congrArg (fun z : PostconditionT (StateM Nat) Nat => ((z.operation.run 0).run).2)
    (h'.monadLift_bind (pt 0 : PostconditionT WM Nat) (fun _ => pt 0))
  exact absurd this (by decide)

-- `Std.Iterators.PostconditionT.instLawfulMonadLift`, idx 6 (inst): `n = WM` (`map` adds 1), `m = Id`, lift `pure`
theorem Iterators.PostconditionT.instLawfulMonadLift.h6 :
    ¬ drop0% Std.Iterators.PostconditionT.instLawfulMonadLift 6 := fun h => by
  letI : MonadLift Id WM := ⟨fun x => pure x.run⟩
  have h' := @h Id WM _ _ _ _ ⟨fun _ => rfl, fun _ _ => rfl⟩
  have := congrArg ptc
    (h'.monadLift_bind (⟨fun _ => True, pure ⟨0, trivial⟩⟩ : PostconditionT Id Nat)
      (fun _ => ⟨fun _ => True, pure ⟨0, trivial⟩⟩))
  cases this


/-! ## Iterators: `KM` evaluation, the countdown `CD` with a vacuously lawful loop -/


/-! ## `KM` evaluation lemmas -/

@[simp] theorem KM.c_pure {bd mp} {α : Type} (a : α) : KM.c (pure a : KM bd mp α) = 0 := rfl
@[simp] theorem KM.c_bind {bd mp} {α β : Type} (x : KM bd mp α) (f : α → KM bd mp β) :
    KM.c (x >>= f) = bd x.c (f (x : Nat × α).2).c := rfl
@[simp] theorem KM.c_map {bd mp} {α β : Type} (x : KM bd mp α) (f : α → β) :
    KM.c (f <$> x) = mp x.c := rfl
@[simp] theorem KM.snd_pure {bd mp} {α : Type} (a : α) : ((pure a : KM bd mp α) : Nat × α).2 = a := rfl

/-! ## Well-foundedness of the collectors' and the default loop's fixpoints over finite iterators -/

theorem finWf {α β γ : Type} {m : Type → Type} [Iterator α m β] [Finite α m] :
    WellFounded (InvImage (IterM.TerminationMeasures.Finite.Rel (α := α) (m := m))
      fun x : (_ : IterM (α := α) m β) ×' γ => x.fst.finitelyManySteps!) :=
  InvImage.wf _ WellFoundedRelation.wf

theorem loopWf {α β γ : Type} {m : Type → Type} [Iterator α m β] [Finite α m]
    {Pl : β → γ → ForInStep γ → Prop} {P : β → Prop} :
    WellFounded (InvImage (IteratorLoop.rel α m Pl)
      fun x : (it : IterM (α := α) m β) ×' (_ : γ) ×' (∀ b, it.IsPlausibleIndirectOutput b → P b) =>
        (x.1, x.2.1)) :=
  InvImage.wf _ IteratorLoop.wellFounded_of_finite


/-! ## Countdown iterator `CD` (from `ItDepOtherHand`) with a vacuously lawful loop -/

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

instance CD.finite {m : Type → Type} [Pure m] : Finite CD m := .of_finitenessRelation {
  Rel := InvImage (· < ·) (fun it => it.internalState.n)
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation := by
    rintro ⟨⟨n⟩⟩ ⟨⟨k⟩⟩ ⟨s, hs, hp⟩
    cases n <;> simp_all [CD.stepv, InvImage] }

instance CD.productive {m : Type → Type} [Pure m] : Productive CD m := .of_productivenessRelation {
  Rel := InvImage (· < ·) (fun it => it.internalState.n)
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation := by
    rintro ⟨⟨n⟩⟩ ⟨⟨k⟩⟩ hp
    cases n <;> simp_all [IterM.IsPlausibleSkipSuccessorOf, CD.stepv] }

@[simp] theorem CD.step_eq {m : Type → Type} [Pure m] (it : IterM (α := CD) m Nat) :
    it.step = pure (Shrink.deflate (⟨CD.stepv it.internalState.n, rfl⟩ : it.Step)) := rfl

abbrev cd (m : Type → Type) (n : Nat) : IterM (α := CD) m Nat := ⟨⟨n⟩⟩

/-- Loop over `CD` that ignores the iterator's steps: `f` applied once to the first output. -/
def CD.alt {m n : Type → Type} [Pure m] [Monad n] {γ : Type} {Pl : Nat → γ → ForInStep γ → Prop}
    (it : IterM (α := CD) m Nat) (init : γ)
    (f : (b : Nat) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) : n γ :=
  match h : it.internalState.n with
  | 0 => pure init
  | k + 1 => (fun r => r.val.value) <$> f k (.direct ⟨⟨⟨k⟩⟩, by simp [CD.stepv, h]⟩) init

open Classical in
/-- The default loop for lawful lift-bind functions, `CD.alt` otherwise. -/
noncomputable instance CD.vloop {m n : Type → Type} [Monad m] [Monad n] : IteratorLoop CD m n where
  forIn lift γ Pl it init f :=
    if Internal.LawfulMonadLiftBindFunction lift then
      IteratorLoop.defaultImplementation.forIn lift γ Pl it init f
    else CD.alt it init f

instance CD.vlawful {m n : Type → Type} [Monad m] [Monad n] : LawfulIteratorLoop CD m n :=
  ⟨fun _ inst _ _ _ _ _ _ => if_pos inst⟩

theorem CD.vloop_neg {m n : Type → Type} [Monad m] [Monad n] {lift : ∀ γ δ, (γ → n δ) → m γ → n δ}
    {γ : Type} {Pl} {it : IterM (α := CD) m Nat} {init : γ} {f}
    (h : ¬ Internal.LawfulMonadLiftBindFunction lift) :
    (CD.vloop (m := m) (n := n)).forIn lift γ Pl it init f = CD.alt it init f := if_neg h

theorem CD.vloop_pos {m n : Type → Type} [Monad m] [Monad n] {lift : ∀ γ δ, (γ → n δ) → m γ → n δ}
    {γ : Type} {Pl} {it : IterM (α := CD) m Nat} {init : γ} {f}
    (h : Internal.LawfulMonadLiftBindFunction lift) :
    (CD.vloop (m := m) (n := n)).forIn lift γ Pl it init f =
      IterM.DefaultConsumers.forIn' lift γ Pl it init _ (fun _ => id) f := if_pos h

/-- In a `KM` monad with `bd 0 0 ≠ 0`, the identity lift-bind function is not lawful. -/
theorem KM.not_lb {bd mp} (hb : bd 0 0 ≠ 0) :
    ¬ Internal.LawfulMonadLiftBindFunction (m := KM bd mp) (n := KM bd mp)
      (fun _ _ f x => monadLift x >>= f) :=
  fun h => hb (congrArg KM.c (h.liftBind_pure (γ := Nat) (δ := Nat) pure 0))

theorem KM.not_lb_flip {bd mp} (hb : bd 0 0 ≠ 0) :
    ¬ Internal.LawfulMonadLiftBindFunction (m := KM bd mp) (n := KM bd mp) (fun _ _ => flip bind) :=
  fun h => hb (congrArg KM.c (h.liftBind_pure (γ := Nat) (δ := Nat) pure 0))

theorem KM.not_lb_id {bd mp} (hb : bd 0 0 ≠ 0) :
    ¬ Internal.LawfulMonadLiftBindFunction (m := Id) (n := KM bd mp)
      (fun _ _ f x => monadLift x >>= f) :=
  fun h => hb (congrArg KM.c (h.liftBind_pure (γ := Nat) (δ := Nat) pure 0))


theorem cdId_toList : (cd Id 1).toList = pure [0] := by
  rw [IterM.toList_eq_match_step]; simp [CD.stepv]
  rw [IterM.toList_eq_match_step]; simp [CD.stepv]

theorem cdId_toArray : (cd Id 1).toArray = pure #[0] := by
  rw [← IterM.toArray_toList, cdId_toList]; rfl

@[simp] theorem nilCW_step : (([] : List Nat).iterM CW).step = pure (.deflate ⟨.done, rfl⟩) := rfl


/-- one unfolding of a collector's or the default loop's fixpoint -/
macro "unf1" : tactic => `(tactic| first
  | rw [WellFounded.extrinsicFix₂_eq_apply finWf]
  | rw [WellFounded.extrinsicFix₃_eq_apply loopWf])

/-- Evaluate counters of `KM` computations over `CD`: unfold the collectors' fixpoints and the
default loop step by step (`extrinsicFix₂/₃_eq_apply`, well-founded since `CD` is finite). -/
macro "ev" : tactic => `(tactic| (
  simp only [IterM.toListRev, IterM.toArray, IterM.toList, IterM.toListRev.go, IterM.toArray.go,
    KM.c_bind, KM.c_pure, KM.c_map, KM.snd_pure, CD.step_eq, Shrink.inflate_deflate, CD.stepv, Id.run_pure, IterM.Total.toArray, IterM.Total.toList, IterM.Total.toListRev, IterM.ensureTermination, nilCW_step]
  repeat (unf1; simp only [KM.c_bind, KM.c_pure, KM.c_map, KM.snd_pure, CD.step_eq, Shrink.inflate_deflate,
      CD.stepv, Id.run_pure])))



/-- Lift `Id → Option` that always fails (not lawful). -/
@[reducible] def noneLT : MonadLiftT Id Option := ⟨fun _ => none⟩

theorem noneLT.not_lb : ¬ Internal.LawfulMonadLiftBindFunction (m := Id) (n := Option)
    (fun (γ δ : Type) (f : γ → Option δ) (x : Id γ) => (noneLT.monadLift x) >>= f) :=
  fun h => by have := h.liftBind_pure (γ := Nat) (δ := Nat) some 0; cases this

theorem CW.not_lb : ¬ Internal.LawfulMonadLiftBindFunction (m := CW) (n := CW)
    (fun _ _ f x => monadLift x >>= f) := KM.not_lb (by decide)
theorem CW.not_lb_flip : ¬ Internal.LawfulMonadLiftBindFunction (m := CW) (n := CW)
    (fun _ _ => flip bind) := KM.not_lb_flip (by decide)
theorem CW.not_lb_id : ¬ Internal.LawfulMonadLiftBindFunction (m := Id) (n := CW)
    (fun _ _ f x => monadLift x >>= f) := KM.not_lb_id (by decide)

/-- Unfold the loop-based consumers to `IteratorLoop.forIn`. -/
macro "loopsimp" : tactic => `(tactic| simp only [ForIn'.forIn', ForIn.forIn, IterM.instForIn',
  IteratorLoop.finiteForIn', IterM.instForInOfIteratorLoop, instForInOfForIn', IterM.fold, IterM.foldM,
  IterM.drain, IterM.length, IterM.anyM, IterM.any, IterM.allM, IterM.all, IterM.findSomeM?,
  IterM.findSome?, IterM.findM?, IterM.find?, IterM.first?, IterM.isEmpty, ForM.forM,
  IterM.instForMOfIteratorLoop, Iter.instForIn', Iter.foldM, Iter.toIterM])


/-! ## Loop-based consumers (`Lemmas/Consumers/Monadic/Loop`) -/


-- `Std.IterM.fold_eq_match_step`, idx 7 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.fold_eq_match_step.h7 : ¬ drop0% Std.IterM.fold_eq_match_step 7 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (γ := Nat) (f := fun c _ => c) (init := 0))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.drain_eq_match_step`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.drain_eq_match_step.h6 : ¬ drop0% Std.IterM.drain_eq_match_step 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.length_eq_match_step`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.length_eq_match_step.h6 : ¬ drop0% Std.IterM.length_eq_match_step 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.anyM_eq_match_step`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.anyM_eq_match_step.h6 : ¬ drop0% Std.IterM.anyM_eq_match_step 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (p := fun _ => pure (ULift.up true)))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.any_eq_match_step`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.any_eq_match_step.h6 : ¬ drop0% Std.IterM.any_eq_match_step 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (p := fun _ => true))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.allM_eq_match_step`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.allM_eq_match_step.h6 : ¬ drop0% Std.IterM.allM_eq_match_step 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (p := fun _ => pure (ULift.up true)))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.all_eq_match_step`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.all_eq_match_step.h6 : ¬ drop0% Std.IterM.all_eq_match_step 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (p := fun _ => true))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.allM_eq_not_anyM_not`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.allM_eq_not_anyM_not.h6 : ¬ drop0% Std.IterM.allM_eq_not_anyM_not 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (p := fun _ => pure (ULift.up true)))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.all_eq_not_any_not`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.all_eq_not_any_not.h6 : ¬ drop0% Std.IterM.all_eq_not_any_not 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (p := fun _ => true))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.findSomeM?_eq_match_step`, idx 7 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.findSomeM?_eq_match_step.h7 : ¬ drop0% Std.IterM.findSomeM?_eq_match_step 7 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (γ := Nat) (f := fun _ => pure none))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.findSome?_eq_match_step`, idx 7 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.findSome?_eq_match_step.h7 : ¬ drop0% Std.IterM.findSome?_eq_match_step 7 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (γ := Nat) (f := fun _ => none))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.findM?_eq_match_step`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.findM?_eq_match_step.h6 : ¬ drop0% Std.IterM.findM?_eq_match_step 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (f := fun _ => pure (ULift.up true)))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.find?_eq_match_step`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.find?_eq_match_step.h6 : ¬ drop0% Std.IterM.find?_eq_match_step 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (f := fun _ => true))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.first?_eq_match_step`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.first?_eq_match_step.h6 : ¬ drop0% Std.IterM.first?_eq_match_step 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.isEmpty_eq_match_step`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.isEmpty_eq_match_step.h6 : ¬ drop0% Std.IterM.isEmpty_eq_match_step 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.fold_hom`, idx 8 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.fold_hom.h8 : ¬ drop0% Std.IterM.fold_hom 8 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (γ₁ := Nat) (γ₂ := Nat) (g₁ := fun c _ => c) (g₂ := fun c _ => c) (init := 0) id (fun _ _ => rfl))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.toList_eq_fold`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.toList_eq_fold.h6 : ¬ drop0% Std.IterM.toList_eq_fold 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.toArray_eq_fold`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.toArray_eq_fold.h6 : ¬ drop0% Std.IterM.toArray_eq_fold 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.foldl_toList`, idx 5 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.foldl_toList.h5 : ¬ drop0% Std.IterM.foldl_toList 5 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (γ := Nat) (f := fun c _ => c) (init := 0))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.foldl_toArray`, idx 5 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.foldl_toArray.h5 : ¬ drop0% Std.IterM.foldl_toArray 5 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) (γ := Nat) (f := fun c _ => c) (init := 0))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.drain_eq_map_toList`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.drain_eq_map_toList.h6 : ¬ drop0% Std.IterM.drain_eq_map_toList 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.drain_eq_map_toListRev`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.drain_eq_map_toListRev.h6 : ¬ drop0% Std.IterM.drain_eq_map_toListRev 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.drain_eq_map_toArray`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.drain_eq_map_toArray.h6 : ¬ drop0% Std.IterM.drain_eq_map_toArray 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.up_size_toArray_eq_length`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.up_size_toArray_eq_length.h6 : ¬ drop0% Std.IterM.up_size_toArray_eq_length 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.up_length_toList_eq_length`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.up_length_toList_eq_length.h6 : ¬ drop0% Std.IterM.up_length_toList_eq_length 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.up_length_toListRev_eq_length`, idx 6 (inst): `CW` (bind and map add 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful in `CW`, so the loop is `CD.alt` (`pure init`); the other side binds the step or maps a collector
theorem IterM.up_length_toListRev_eq_length.h6 : ¬ drop0% Std.IterM.up_length_toListRev_eq_length 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  ev
  decide

-- `Std.IterM.fold_eq_foldM`, idx 7 (inst): `CW` (bind and map add 1), `CD 1`, loop `CD.vloop`, which in `CW` applies the step function once (`CD.alt`): `pure` vs `yield <$> pure`
theorem IterM.fold_eq_foldM.h7 : ¬ drop0% Std.IterM.fold_eq_foldM 7 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 1) (γ := Nat) (f := fun c _ => c) (init := 0))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  decide

-- `Std.IterM.drain_eq_foldM`, idx 6 (inst): `CW` (bind and map add 1), `CD 1`, loop `CD.vloop`, which in `CW` applies the step function once (`CD.alt`): `pure` vs `yield <$> pure`
theorem IterM.drain_eq_foldM.h6 : ¬ drop0% Std.IterM.drain_eq_foldM 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 1) )
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  decide

-- `Std.IterM.any_eq_forIn`, idx 6 (inst): `CW` (bind and map add 1), `CD 1`, loop `CD.vloop`, which in `CW` applies the step function once (`CD.alt`): the `anyM` step function binds `pure (p x)`
theorem IterM.any_eq_forIn.h6 : ¬ drop0% Std.IterM.any_eq_forIn 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 1) (p := fun _ => false))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  decide

-- `Std.IterM.all_eq_forIn`, idx 6 (inst): `CW` (bind and map add 1), `CD 1`, loop `CD.vloop`, which in `CW` applies the step function once (`CD.alt`): the `allM` step function binds `pure (p x)`
theorem IterM.all_eq_forIn.h6 : ¬ drop0% Std.IterM.all_eq_forIn 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 1) (p := fun _ => true))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  decide

-- `Std.IterM.find?_eq_findSome?`, idx 6 (inst): `CW` (bind and map add 1), `CD 1`, loop `CD.vloop`, which in `CW` applies the step function once (`CD.alt`): the `findM?` step function binds `pure (f x)`
theorem IterM.find?_eq_findSome?.h6 : ¬ drop0% Std.IterM.find?_eq_findSome? 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 1) (f := fun _ => false))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  decide

-- `Std.IterM.forIn_yield_eq_foldM`, idx 10 (inst): `m = n = CW` (bind and map add 1), `CD 1`, loop `CD.vloop` (`CD.alt` in `CW`): one `map` vs two
theorem IterM.forIn_yield_eq_foldM.h10 : ¬ drop0% Std.IterM.forIn_yield_eq_foldM 10 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (γ := Nat) (δ := Nat) (m := CW) (n := CW) (it := cd CW 1)
    (f := fun _ _ => pure 0) (g := fun c _ _ => c) (init := 0))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  decide

-- `Std.IterM.forIn'_eq`, idx 8 (inst): `m = n = CW` (bind adds 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful, so the loop is `CD.alt` (counter 0); the other side binds the lifted step (counter 1)
theorem IterM.forIn'_eq.h8 : ¬ drop0% Std.IterM.forIn'_eq 8 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (n := CW) (it := cd CW 0) (γ := Nat) (init := 0) (f := fun _ _ c => pure (.yield c)))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  try simp only [IterM.DefaultConsumers.forIn']
  ev
  decide

-- `Std.IterM.forIn'_eq`, idx 12 (inst): `m = Id`, `n = Option`, lift `noneLT` (always `none`), `CD 0`: `CD.vloop` runs `CD.alt` (`some init`), the other side binds the lifted step (`none`)
theorem IterM.forIn'_eq.h12 : ¬ drop0% Std.IterM.forIn'_eq 12 := fun h => by
  letI : MonadLiftT Id Option := noneLT
  have := h (α := CD) (β := Nat) (m := Id) (n := Option) (it := cd Id 0) (γ := Nat) (init := 0) (f := fun _ _ c => pure (.yield c))
  revert this
  loopsimp
  rw [CD.vloop_neg noneLT.not_lb]
  try simp only [IterM.DefaultConsumers.forIn']
  try unf1
  intro e; cases e

-- `Std.IterM.forIn_eq`, idx 8 (inst): `m = n = CW` (bind adds 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful, so the loop is `CD.alt` (counter 0); the other side binds the lifted step (counter 1)
theorem IterM.forIn_eq.h8 : ¬ drop0% Std.IterM.forIn_eq 8 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (n := CW) (it := cd CW 0) (γ := Nat) (init := 0) (f := fun _ c => pure (.yield c)))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  try simp only [IterM.DefaultConsumers.forIn']
  ev
  decide

-- `Std.IterM.forIn_eq`, idx 12 (inst): `m = Id`, `n = Option`, lift `noneLT` (always `none`), `CD 0`: `CD.vloop` runs `CD.alt` (`some init`), the other side binds the lifted step (`none`)
theorem IterM.forIn_eq.h12 : ¬ drop0% Std.IterM.forIn_eq 12 := fun h => by
  letI : MonadLiftT Id Option := noneLT
  have := h (α := CD) (β := Nat) (m := Id) (n := Option) (it := cd Id 0) (γ := Nat) (init := 0) (f := fun _ c => pure (.yield c))
  revert this
  loopsimp
  rw [CD.vloop_neg noneLT.not_lb]
  try simp only [IterM.DefaultConsumers.forIn']
  try unf1
  intro e; cases e

-- `Std.IterM.forIn'_eq_match_step`, idx 8 (inst): `m = n = CW` (bind adds 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful, so the loop is `CD.alt` (counter 0); the other side binds the lifted step (counter 1)
theorem IterM.forIn'_eq_match_step.h8 : ¬ drop0% Std.IterM.forIn'_eq_match_step 8 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (n := CW) (it := cd CW 0) (γ := Nat) (init := 0) (f := fun _ _ c => pure (.yield c)))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  try simp only [IterM.DefaultConsumers.forIn']
  ev
  decide

-- `Std.IterM.forIn'_eq_match_step`, idx 12 (inst): `m = Id`, `n = Option`, lift `noneLT` (always `none`), `CD 0`: `CD.vloop` runs `CD.alt` (`some init`), the other side binds the lifted step (`none`)
theorem IterM.forIn'_eq_match_step.h12 : ¬ drop0% Std.IterM.forIn'_eq_match_step 12 := fun h => by
  letI : MonadLiftT Id Option := noneLT
  have := h (α := CD) (β := Nat) (m := Id) (n := Option) (it := cd Id 0) (γ := Nat) (init := 0) (f := fun _ _ c => pure (.yield c))
  revert this
  loopsimp
  rw [CD.vloop_neg noneLT.not_lb]
  try simp only [IterM.DefaultConsumers.forIn']
  try unf1
  intro e; cases e

-- `Std.IterM.forIn_eq_match_step`, idx 8 (inst): `m = n = CW` (bind adds 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful, so the loop is `CD.alt` (counter 0); the other side binds the lifted step (counter 1)
theorem IterM.forIn_eq_match_step.h8 : ¬ drop0% Std.IterM.forIn_eq_match_step 8 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (n := CW) (it := cd CW 0) (γ := Nat) (init := 0) (f := fun _ c => pure (.yield c)))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  try simp only [IterM.DefaultConsumers.forIn']
  ev
  decide

-- `Std.IterM.forIn_eq_match_step`, idx 12 (inst): `m = Id`, `n = Option`, lift `noneLT` (always `none`), `CD 0`: `CD.vloop` runs `CD.alt` (`some init`), the other side binds the lifted step (`none`)
theorem IterM.forIn_eq_match_step.h12 : ¬ drop0% Std.IterM.forIn_eq_match_step 12 := fun h => by
  letI : MonadLiftT Id Option := noneLT
  have := h (α := CD) (β := Nat) (m := Id) (n := Option) (it := cd Id 0) (γ := Nat) (init := 0) (f := fun _ c => pure (.yield c))
  revert this
  loopsimp
  rw [CD.vloop_neg noneLT.not_lb]
  try simp only [IterM.DefaultConsumers.forIn']
  try unf1
  intro e; cases e

-- `Std.IterM.forM_eq_match_step`, idx 8 (inst): `m = n = CW` (bind adds 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful, so the loop is `CD.alt` (counter 0); the other side binds the lifted step (counter 1)
theorem IterM.forM_eq_match_step.h8 : ¬ drop0% Std.IterM.forM_eq_match_step 8 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (n := CW) (it := cd CW 0) (f := fun _ => pure ()))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  try simp only [IterM.DefaultConsumers.forIn']
  ev
  decide

-- `Std.IterM.forM_eq_match_step`, idx 12 (inst): `m = Id`, `n = Option`, lift `noneLT` (always `none`), `CD 0`: `CD.vloop` runs `CD.alt` (`some init`), the other side binds the lifted step (`none`)
theorem IterM.forM_eq_match_step.h12 : ¬ drop0% Std.IterM.forM_eq_match_step 12 := fun h => by
  letI : MonadLiftT Id Option := noneLT
  have := h (α := CD) (β := Nat) (m := Id) (n := Option) (it := cd Id 0) (f := fun _ => pure ())
  revert this
  loopsimp
  rw [CD.vloop_neg noneLT.not_lb]
  try simp only [IterM.DefaultConsumers.forIn']
  try unf1
  intro e; cases e

-- `Std.IterM.foldM_eq_match_step`, idx 9 (inst): `m = n = CW` (bind adds 1), `CD 0`, loop `CD.vloop`: the lift-bind function is not lawful, so the loop is `CD.alt` (counter 0); the other side binds the lifted step (counter 1)
theorem IterM.foldM_eq_match_step.h9 : ¬ drop0% Std.IterM.foldM_eq_match_step 9 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (n := CW) (it := cd CW 0) (γ := Nat) (init := 0) (f := fun c _ => pure c))
  revert this
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  try simp only [IterM.DefaultConsumers.forIn']
  ev
  decide

-- `Std.IterM.foldM_eq_match_step`, idx 13 (inst): `m = Id`, `n = Option`, lift `noneLT` (always `none`), `CD 0`: `CD.vloop` runs `CD.alt` (`some init`), the other side binds the lifted step (`none`)
theorem IterM.foldM_eq_match_step.h13 : ¬ drop0% Std.IterM.foldM_eq_match_step 13 := fun h => by
  letI : MonadLiftT Id Option := noneLT
  have := h (α := CD) (β := Nat) (m := Id) (n := Option) (it := cd Id 0) (γ := Nat) (init := 0) (f := fun c _ => pure c)
  revert this
  loopsimp
  rw [CD.vloop_neg noneLT.not_lb]
  try simp only [IterM.DefaultConsumers.forIn']
  try unf1
  intro e; cases e


/-! ## Collectors, list producer, `Id` iterators (`Lemmas/Consumers/Monadic/Collect`, ...) -/


-- `Std.IterM.toArray_eq_match_step`, idx 5 (inst): `CW` (bind and map add 1), `CD 1`: counters 2 (`go`) vs 3 (extra bind of `pure (#[out] ++ ·)`)
theorem IterM.toArray_eq_match_step.h5 : ¬ drop0% Std.IterM.toArray_eq_match_step 5 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 1))
  revert this
  ev
  decide

-- `Std.IterM.toArray_ensureTermination_eq_match_step`, idx 5 (inst): `CW` (bind and map add 1), `CD 1`: counters 2 (`go`) vs 3 (extra bind of `pure (#[out] ++ ·)`)
theorem IterM.toArray_ensureTermination_eq_match_step.h5 : ¬ drop0% Std.IterM.toArray_ensureTermination_eq_match_step 5 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 1))
  revert this
  ev
  decide

-- `Std.IterM.toArray_toList`, idx 4 (inst): `CW` (bind and map add 1), `CD 0`: two maps (counter 3) vs none (counter 1)
theorem IterM.toArray_toList.h4 : ¬ drop0% Std.IterM.toArray_toList 4 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0))
  revert this
  ev
  decide

-- `Std.IterM.toArray_toList_ensureTermination`, idx 4 (inst): `CW` (bind and map add 1), `CD 0`: two maps (counter 3) vs none (counter 1)
theorem IterM.toArray_toList_ensureTermination.h4 : ¬ drop0% Std.IterM.toArray_toList_ensureTermination 4 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0))
  revert this
  ev
  decide

-- `Std.IterM.toList_eq_match_step`, idx 4 (inst): `CW` (bind and map add 1), `CD 0`: `toList` maps `toArray` (counter 2), the `done` branch is `pure []` after the step (counter 1)
theorem IterM.toList_eq_match_step.h4 : ¬ drop0% Std.IterM.toList_eq_match_step 4 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0))
  revert this
  ev
  decide

-- `Std.IterM.toList_ensureTermination_eq_match_step`, idx 4 (inst): `CW` (bind and map add 1), `CD 0`: `toList` maps `toArray` (counter 2), the `done` branch is `pure []` after the step (counter 1)
theorem IterM.toList_ensureTermination_eq_match_step.h4 : ¬ drop0% Std.IterM.toList_ensureTermination_eq_match_step 4 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0))
  revert this
  ev
  decide

-- `Std.IterM.toListRev_eq_match_step`, idx 4 (inst): `CW` (bind and map add 1), `CD 1`: counters 2 (`go`) vs 3 (extra bind of `pure (· ++ [out])`)
theorem IterM.toListRev_eq_match_step.h4 : ¬ drop0% Std.IterM.toListRev_eq_match_step 4 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 1))
  revert this
  ev
  decide

-- `Std.IterM.toListRev_ensureTermination_eq_match_step`, idx 4 (inst): `CW` (bind and map add 1), `CD 1`: counters 2 (`go`) vs 3 (extra bind of `pure (· ++ [out])`)
theorem IterM.toListRev_ensureTermination_eq_match_step.h4 : ¬ drop0% Std.IterM.toListRev_ensureTermination_eq_match_step 4 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 1))
  revert this
  ev
  decide

-- `Std.IterM.toListRev_eq`, idx 4 (inst): `CW` (bind and map add 1), `CD 0`: no map (counter 1) vs two maps (counter 3)
theorem IterM.toListRev_eq.h4 : ¬ drop0% Std.IterM.toListRev_eq 4 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0))
  revert this
  ev
  decide

-- `Std.IterM.toListRev_ensureTermination`, idx 4 (inst): `CW` (bind and map add 1), `CD 0`: no map (counter 1) vs two maps (counter 3)
theorem IterM.toListRev_ensureTermination.h4 : ¬ drop0% Std.IterM.toListRev_ensureTermination 4 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd CW 0))
  revert this
  ev
  decide

-- `List.toArray_iterM`, idx 2 (inst): `CW` (bind adds 1), list `[]`: the collector binds the step (counter 1), `pure` has counter 0
theorem List.toArray_iterM.h2 : ¬ drop0% List.toArray_iterM 2 := fun h => by
  have := congrArg KM.c (h (m := CW) (β := Nat) (l := []))
  revert this
  ev
  decide

-- `List.toListRev_iterM`, idx 3 (inst): `CW` (bind adds 1), list `[]`: the collector binds the step (counter 1), `pure` has counter 0
theorem List.toListRev_iterM.h3 : ¬ drop0% List.toListRev_iterM 3 := fun h => by
  have := congrArg KM.c (h (m := CW) (β := Nat) (l := []))
  revert this
  ev
  decide

-- `Std.IterM.forIn_toList`, idx 5 (inst): `m = CW`, iterator `CD 1` over `Id`, loop `CD.vloop` (the lift `Id → CW` is not lawful, so `CD.alt`): `List.forIn` over `[0]` (counter 1) vs `CD.alt`, which maps (counter 2)
theorem IterM.forIn_toList.h5 : ¬ drop0% Std.IterM.forIn_toList 5 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd Id 1) (γ := Nat) (f := fun _ c => pure (.yield c)) (init := 0))
  revert this
  simp only [cdId_toList, cdId_toArray]
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  decide

-- `Std.IterM.forIn_toArray`, idx 5 (inst): `m = CW`, iterator `CD 1` over `Id`, loop `CD.vloop` (the lift `Id → CW` is not lawful, so `CD.alt`): `Array.forIn` over `#[0]` (counter 1) vs `CD.alt`, which maps (counter 2)
theorem IterM.forIn_toArray.h5 : ¬ drop0% Std.IterM.forIn_toArray 5 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd Id 1) (γ := Nat) (f := fun _ c => pure (.yield c)) (init := 0))
  revert this
  simp only [cdId_toList, cdId_toArray]
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  decide

-- `Std.IterM.foldlM_toList`, idx 5 (inst): `m = CW`, iterator `CD 1` over `Id`, loop `CD.vloop` (the lift `Id → CW` is not lawful, so `CD.alt`): `List.foldlM` over `[0]` (counter 1) vs `CD.alt` on `yield <$> f` (counter 3)
theorem IterM.foldlM_toList.h5 : ¬ drop0% Std.IterM.foldlM_toList 5 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd Id 1) (γ := Nat) (f := fun c _ => pure c) (init := 0))
  revert this
  simp only [cdId_toList, cdId_toArray]
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  decide

-- `Std.IterM.foldlM_toArray`, idx 5 (inst): `m = CW`, iterator `CD 1` over `Id`, loop `CD.vloop` (the lift `Id → CW` is not lawful, so `CD.alt`): `Array.foldlM` over `#[0]` (counter 1) vs `CD.alt` on `yield <$> f` (counter 3)
theorem IterM.foldlM_toArray.h5 : ¬ drop0% Std.IterM.foldlM_toArray 5 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (it := cd Id 1) (γ := Nat) (f := fun c _ => pure c) (init := 0))
  revert this
  simp only [cdId_toList, cdId_toArray]
  loopsimp
  simp only [CD.vloop_neg CW.not_lb, CD.vloop_neg CW.not_lb_flip, CD.vloop_neg CW.not_lb_id]
  decide


/-! ## `Iter.forIn` vs `foldM` and the removable verdicts -/


theorem idRun_lb : Internal.LawfulMonadLiftBindFunction (m := Id) (n := CW) (fun _ _ f c => f c.run) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

-- `Std.IterM.forIn_eq_foldM`, idx 6 (inst): `m = CW` (map adds 1), `Iter` over `CD 0`: the loop (lift `f x.run`, lawful, so the default loop) gives counter 0, the `ForInStep.value <$>` side 1
theorem IterM.forIn_eq_foldM.h6 : ¬ drop0% Std.IterM.forIn_eq_foldM 6 := fun h => by
  have := congrArg KM.c (h (α := CD) (β := Nat) (m := CW) (γ := Nat) (it := ⟨⟨0⟩⟩) (init := 0)
    (f := fun _ c => pure (.yield c)))
  revert this
  loopsimp
  simp only [CD.vloop_pos idRun_lb, IterM.DefaultConsumers.forIn']
  ev
  decide

-- `Std.IterM.findSomeM?_pure`, idx 7 (removable): `findSome? f` is `findSomeM? (pure <| f ·)` by definition
theorem IterM.findSomeM?_pure.h7 : drop% Std.IterM.findSomeM?_pure 7 := by intros; rfl

-- `Std.IterM.findM?_pure`, idx 6 (removable): `find? (ULift.down <| f ·)` unfolds to `findM? (pure <| f ·)`
theorem IterM.findM?_pure.h6 : drop% Std.IterM.findM?_pure 6 := by intros; rfl

-- `Std.IterM.DefaultConsumers.forIn'_eq_forIn'`, idx 6 (removable): well-founded induction with one unfolding of each loop (`extrinsicFix₃_eq_apply`), which needs no monad laws
theorem IterM.DefaultConsumers.forIn'_eq_forIn'.h6 :
    drop% Std.IterM.DefaultConsumers.forIn'_eq_forIn' 6 := by
  intro m α β _ n _ lift γ it init P hP Q hQ Pl f g wf hfg
  suffices H : ∀ p : IterM (α := α) m β × γ, ∀ (hP : ∀ b, p.1.IsPlausibleIndirectOutput b → P b)
      (hQ : ∀ b, p.1.IsPlausibleIndirectOutput b → Q b),
      IterM.DefaultConsumers.forIn' lift γ Pl p.1 p.2 P hP f =
        IterM.DefaultConsumers.forIn' lift γ Pl p.1 p.2 Q hQ g from H (it, init) hP hQ
  intro p
  induction p using wf.induction with
  | _ p ih =>
    intro hP hQ
    haveI : Nonempty γ := ⟨p.2⟩
    have wfP := InvImage.wf (fun x : (it : IterM (α := α) m β) ×' (_ : γ) ×'
      (∀ b, it.IsPlausibleIndirectOutput b → P b) => (x.1, x.2.1)) wf
    have wfQ := InvImage.wf (fun x : (it : IterM (α := α) m β) ×' (_ : γ) ×'
      (∀ b, it.IsPlausibleIndirectOutput b → Q b) => (x.1, x.2.1)) wf
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply wfP,
      IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply wfQ]
    congr 1; funext s
    split
    · rename_i it' out h _
      congr 1
      · exact hfg _ _ _ _
      · funext r
        obtain ⟨⟨c⟩ | ⟨c⟩, h'⟩ := r
        · rfl
        · exact ih (it', c) (Or.inl ⟨out, h, h'⟩) _ _
    · rename_i it' h _
      exact ih (it', p.2) (Or.inr ⟨h, rfl⟩) _ _
    · rfl

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure`, idx 7 (removable): the plausible-step relations of `mapWithPostcondition pure`, `mapM` and `flattenAfter` need no monad laws
theorem Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure.h7 :
    drop% Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure 7 := by
  intro α β α₂ γ m _ _ _ _ _ f it₁ it₁' it₂' b h h'
  exact .outerYield (.yieldSome (.yieldSome h (by simp)) ⟨⟨_, h'⟩, rfl⟩)


end ItMonadRestHand
