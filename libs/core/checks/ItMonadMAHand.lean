import Lean

/-!
Hand pass `ItMonadMA` (hand8): the 150 open monad-law hypotheses (`LawfulMonad`,
`WeaklyLawfulMonadAttach`, `LawfulMonadLiftT`) of the `Std.IterM` lemmas in
`Init.Data.Iterators.Lemmas.Combinators.Monadic.{Append,Attach,FilterMap}` (first half by name).
For hypothesis `hᵢ` of theorem `T` this file proves `¬T'` (necessary) or `T'` (removable).

146 necessary, 4 removable, 0 independent, 0 opaque.

Necessary: each refutation instantiates the hypothetical `T'` (universes set to `0` by `drop0%`) at
models in which all other hypotheses hold, a list iterator `[0].iterM _`, and simple `f`/`g`/`p`, and
evaluates both sides. The consumers are defined with `WellFounded.extrinsicFix₂/₃`; they are
unfolded without monad laws by `toArray_go_eq`, `toListRev_go_eq`, `forIn'_eq` (from
`extrinsicFix₂/₃_eq_apply` and `Finite`), the combinator steps by `filterMap_step_eq`,
`map_step_eq`, `attach_step_eq` and the library's `step_append` lemmas. The tactic `ev_all`
alternates these rewrites with `dsimp` (structure) and `simp (config := { dsimp := false })` (monad
operations, never inside types, so that types and instance arguments stay syntactically equal).
Models (all `structure X (α : Type) where c : _; v : α`, a writer-like monad):
* `CM` (bind adds one), `CM2` (bind and map add one), `WM` (bind doubles the first count):
  broken bind laws for the single-monad lemmas and for `anyM`/`allM` lemmas;
* `QM` (bind adds one iff the continuation is effectful): `pure` from `Id`/the count-forgetting lift
  from `NW` are lawful lifts, but `pure a >>= f ≠ f a`;
* `NW`, `NW2`, `W` (lawful `Nat`/`Bool` writers); `NWa`/`NWb` (`attach` drops the count / adds
  one: not weakly lawful); `tickNW`/`tickNW2` (lifts that add one: not lawful);
* `FM` (lawful bind/pure, `map` and `attach` flip the flag: weakly lawful, `map` not lawful), `SM`
  (`map` flips iff the target type is a subsingleton, `attach` iff the value type is; uses
  classical choice), `MB` (`map` adds one);
* `evilLoop`: an `IteratorLoop` instance that is lawful (`evilLoop_lawful`) but returns `init` for
  lift functions that are not `LawfulMonadLiftBindFunction`. When the dropped law makes the base
  iterator's lift non-lawful, the right-hand side `forIn it …` then returns `init`, while the
  combinator's default loop does not.

Removable (4): `LawfulMonad m` of `Std.IterM.forIn_filterMap`, `Std.IterM.forIn_filter`,
`Std.IterM.foldM_filterMap`, `Std.IterM.foldM_filter`: the `filterMap`/`filter` step only binds and
returns `pure` values in `m`, and these are mapped by the lawful lift into the lawful `n`. (For the
`map` variants the combinator maps in `m`, and `MB` refutes them.)

Run with the lean4 repo's stage1 binary: `lean checks/ItMonadMAHand.lean`.
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

-- `Std.IterM.toList_appendSnd`, idx 5 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem toList_appendSnd.h5 : ¬ drop0% Std.IterM.toList_appendSnd 5 := by
  intro h
  have := h (m := CM) (α₁ := ListIterator Nat) (it₂ := [0].iterM CM)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.toList_append`, idx 5 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem toList_append.h5 : ¬ drop0% Std.IterM.toList_append 5 := by
  intro h
  have := h (m := CM) (it₁ := [0].iterM CM) (it₂ := [0].iterM CM)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.toListRev_append`, idx 5 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem toListRev_append.h5 : ¬ drop0% Std.IterM.toListRev_append 5 := by
  intro h
  have := h (m := CM) (it₁ := [0].iterM CM) (it₂ := [0].iterM CM)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.toArray_append`, idx 5 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem toArray_append.h5 : ¬ drop0% Std.IterM.toArray_append 5 := by
  intro h
  have := h (m := CM) (it₁ := [0].iterM CM) (it₂ := [0].iterM CM)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.map_unattach_toList_attachWith`, idx 9 (LawfulMonad m): m = counting monad CM2 (bind adds one, map adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem map_unattach_toList_attachWith.h9 : ¬ drop0% Std.IterM.map_unattach_toList_attachWith 9 := by
  intro h
  have := h (m := CM2) (P := fun _ => True) (it := [0].iterM CM2) (hP := fun _ _ => trivial)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.map_unattach_toListRev_attachWith`, idx 11 (LawfulMonad m): m = counting monad CM2 (bind adds one, map adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem map_unattach_toListRev_attachWith.h11 : ¬ drop0% Std.IterM.map_unattach_toListRev_attachWith 11 := by
  intro h
  have := h (m := CM2) (n := Id) (P := fun _ => True) (it := [0].iterM CM2) (hP := fun _ _ => trivial)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.map_unattach_toArray_attachWith`, idx 11 (LawfulMonad m): m = counting monad CM2 (bind adds one, map adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem map_unattach_toArray_attachWith.h11 : ¬ drop0% Std.IterM.map_unattach_toArray_attachWith 11 := by
  intro h
  have := h (m := CM2) (n := Id) (P := fun _ => True) (it := [0].iterM CM2) (hP := fun _ _ => trivial)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.length_attachWith`, idx 12 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem length_attachWith.h12 : ¬ drop0% Std.IterM.length_attachWith 12 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (n := Id) (P := fun _ => True) (it := [0].iterM CM) (hP := fun _ _ => trivial)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.step_filterWithPostcondition`, idx 8 (LawfulMonad n): m = n = counting monad CM2 (bind and map add one; not lawful), list iterator [0]: the combinator's step maps the result of f, the stated right side does not.
theorem step_filterWithPostcondition.h8 : ¬ drop0% Std.IterM.step_filterWithPostcondition 8 := by
  intro h
  have := h (m := CM2) (n := CM2) (it := [0].iterM CM2) (f := fun _ => PostconditionT.pure (.up true))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.step_mapWithPostcondition`, idx 9 (LawfulMonad n): m = n = counting monad CM2 (bind and map add one; not lawful), list iterator [0]: the combinator's step maps the result of f, the stated right side does not.
theorem step_mapWithPostcondition.h9 : ¬ drop0% Std.IterM.step_mapWithPostcondition 9 := by
  intro h
  have := h (m := CM2) (n := CM2) (it := [0].iterM CM2) (f := fun b => PostconditionT.pure b)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.step_filterM`, idx 9 (LawfulMonad n): m = n = counting monad CM2 (bind and map add one; not lawful), list iterator [0]: the combinator's step maps the result of f, the stated right side does not.
theorem step_filterM.h9 : ¬ drop0% Std.IterM.step_filterM 9 := by
  intro h
  have := h (m := CM2) (n := CM2) (it := [0].iterM CM2) (f := fun _ => pure (.up true))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.step_mapM`, idx 10 (LawfulMonad n): m = n = counting monad CM2 (bind and map add one; not lawful), list iterator [0]: the combinator's step maps the result of f, the stated right side does not.
theorem step_mapM.h10 : ¬ drop0% Std.IterM.step_mapM 10 := by
  intro h
  have := h (m := CM2) (n := CM2) (it := [0].iterM CM2) (f := fun b => pure b)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.step_filterMap`, idx 7 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem step_filterMap.h7 : ¬ drop0% Std.IterM.step_filterMap 7 := by
  intro h
  have := h (m := CM) (it := [0].iterM CM) (f := some)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.step_map`, idx 7 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem step_map.h7 : ¬ drop0% Std.IterM.step_map 7 := by
  intro h
  have := h (m := CM) (it := [0].iterM CM) (f := id)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.step_filter`, idx 6 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem step_filter.h6 : ¬ drop0% Std.IterM.step_filter 6 := by
  intro h
  have := h (m := CM) (it := [0].iterM CM) (f := fun _ => true)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.InternalConsumers.toList_filterMap`, idx 5 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem InternalConsumers_toList_filterMap.h5 : ¬ drop0% Std.IterM.InternalConsumers.toList_filterMap 5 := by
  intro h
  have := h (m := CM) (it := [0].iterM CM) (f := some)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.toArray_filterMapM_filterMapM`, idx 11 (LawfulMonad n): m = Id, n = FM (flips the flag in map/attach), o = W, list iterator [0].
theorem toArray_filterMapM_filterMapM.h11 : ¬ drop0% Std.IterM.toArray_filterMapM_filterMapM 11 := by
  intro h
  have := h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => pure (some b)) (g := fun c => pure (some c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.toArray_filterMapM_filterMapM`, idx 12 (WeaklyLawfulMonadAttach n): m = Id, n = NWb (attach adds one), o = NW, list iterator [0].
theorem toArray_filterMapM_filterMapM.h12 : ¬ drop0% Std.IterM.toArray_filterMapM_filterMapM 12 := by
  intro h
  have := h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure (some b)) (g := fun c => pure (some c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.toArray_filterMapM_filterMapM`, idx 15 (LawfulMonad o): m = n = NW, o = QM (count-forgetting lawful lift), list iterator [0], effectful g.
theorem toArray_filterMapM_filterMapM.h15 : ¬ drop0% Std.IterM.toArray_filterMapM_filterMapM 15 := by
  intro h
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun b => pure (some b)) (g := fun c => (⟨1, some c⟩ : QM _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.toArray_filterMapM_filterMapM`, idx 16 (WeaklyLawfulMonadAttach o): m = n = NW, o = NWb (attach adds one), list iterator [0], f filters everything: the left side never attaches in o, the right side does once.
theorem toArray_filterMapM_filterMapM.h16 : ¬ drop0% Std.IterM.toArray_filterMapM_filterMapM 16 := by
  intro h
  have := h (m := NW) (n := NW) (o := NWb) (it := [0].iterM NW) (f := fun _ => (pure none : NW (Option Nat))) (g := fun c => pure (some c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.toArray_filterMapM_filterMapM`, idx 20 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2, lift NW → NW2 adds one (not lawful), list iterator [0]: the sides lift a different number of times.
theorem toArray_filterMapM_filterMapM.h20 : ¬ drop0% Std.IterM.toArray_filterMapM_filterMapM 20 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure (some b)) (g := fun c => pure (some c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.toArray_filterMapM`, idx 6 (LawfulMonad m): m = CM (counting monad), base list iterator [0] over Id; Array.filterMapM is evaluated by decide.
theorem toArray_filterMapM.h6 : ¬ drop0% Std.IterM.toArray_filterMapM 6 := by
  intro h
  have := h (m := CM) (f := fun b => pure (some b)) ([0].iterM Id)
  clear h; revert this
  rw [List.toArray_iterM]
  ev_all; intro hh; have := congrArg CM.c hh; revert this; decide

-- `Std.IterM.toArray_filterMapM`, idx 7 (WeaklyLawfulMonadAttach m): m = NWa (lawful Nat writer whose attach drops the count), effectful f, base list iterator [0] over Id; the left side attaches f's result, Array.filterMapM does not.
theorem toArray_filterMapM.h7 : ¬ drop0% Std.IterM.toArray_filterMapM 7 := by
  intro h
  have := h (m := NWa) (f := fun b => (⟨1, some b⟩ : NWa _)) ([0].iterM Id)
  clear h; revert this
  rw [List.toArray_iterM]
  ev_all; intro hh; have := congrArg NWa.c hh; revert this; decide

-- `Std.IterM.toArray_filterMap`, idx 5 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem toArray_filterMap.h5 : ¬ drop0% Std.IterM.toArray_filterMap 5 := by
  intro h
  have := h (m := CM) (it := [0].iterM CM) (f := some)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.toArray_filter`, idx 3 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]: the two sides perform different numbers of binds.
theorem toArray_filter.h3 : ¬ drop0% Std.IterM.toArray_filter 3 := by
  intro h
  have := h (m := CM) (it := [0].iterM CM) (f := fun _ => true)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.forIn_filterMapWithPostcondition`, idx 10 (LawfulMonad n): m = Id, n = FM (Bool writer whose map and attach flip the flag: bind/pure lawful, weakly lawful attach, lawful lifts from Id and to o = W), list iterator [0]: the left side binds f's operation (resp. attach) directly, the right side maps it.
theorem forIn_filterMapWithPostcondition.h10 : ¬ drop0% Std.IterM.forIn_filterMapWithPostcondition 10 := by
  intro h
  have := h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.forIn_filterMapWithPostcondition`, idx 12 (LawfulMonad o): m = n = NW (lawful Nat writer), o = QM (bind adds one iff the continuation is effectful: the count-forgetting lift NW → QM is lawful, but pure a >>= g ≠ g a), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift into QM).
theorem forIn_filterMapWithPostcondition.h12 : ¬ drop0% Std.IterM.forIn_filterMapWithPostcondition 12 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun c acc => (⟨1, .yield (acc + c)⟩ : QM _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterMapWithPostcondition`, idx 14 (LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).
theorem forIn_filterMapWithPostcondition.h14 : ¬ drop0% Std.IterM.forIn_filterMapWithPostcondition 14 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterMapWithPostcondition`, idx 16 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).
theorem forIn_filterMapWithPostcondition.h16 : ¬ drop0% Std.IterM.forIn_filterMapWithPostcondition 16 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterMapM`, idx 10 (LawfulMonad n): m = Id, n = FM (Bool writer whose map and attach flip the flag: bind/pure lawful, weakly lawful attach, lawful lifts from Id and to o = W), list iterator [0]: the left side binds f's operation (resp. attach) directly, the right side maps it.
theorem forIn_filterMapM.h10 : ¬ drop0% Std.IterM.forIn_filterMapM 10 := by
  intro h
  have := h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.forIn_filterMapM`, idx 12 (LawfulMonad o): m = n = NW (lawful Nat writer), o = QM (bind adds one iff the continuation is effectful: the count-forgetting lift NW → QM is lawful, but pure a >>= g ≠ g a), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift into QM).
theorem forIn_filterMapM.h12 : ¬ drop0% Std.IterM.forIn_filterMapM 12 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => (⟨1, .yield (acc + c)⟩ : QM _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterMapM`, idx 14 (WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.
theorem forIn_filterMapM.h14 : ¬ drop0% Std.IterM.forIn_filterMapM 14 := by
  intro h
  have := h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.forIn_filterMapM`, idx 16 (LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).
theorem forIn_filterMapM.h16 : ¬ drop0% Std.IterM.forIn_filterMapM 16 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterMapM`, idx 18 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).
theorem forIn_filterMapM.h18 : ¬ drop0% Std.IterM.forIn_filterMapM 18 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterMap`, idx 9 (LawfulMonad n): m = NW, n = QM (bind adds one iff the continuation is effectful; the count-forgetting lift NW → QM is lawful), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop.
theorem forIn_filterMap.h9 : ¬ drop0% Std.IterM.forIn_filterMap 9 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := QM) (it := [0].iterM NW) (f := some) (init := 0) (g := fun c acc => (⟨1, .yield (acc + c)⟩ : QM _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterMap`, idx 11 (LawfulMonadLiftT m n): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.
theorem forIn_filterMap.h11 : ¬ drop0% Std.IterM.forIn_filterMap 11 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := some) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_mapWithPostcondition`, idx 10 (LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).
theorem forIn_mapWithPostcondition.h10 : ¬ drop0% Std.IterM.forIn_mapWithPostcondition 10 := by
  intro h
  have := h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.forIn_mapWithPostcondition`, idx 12 (LawfulMonad o): m = n = NW (lawful Nat writer), o = QM (bind adds one iff the continuation is effectful: the count-forgetting lift NW → QM is lawful, but pure a >>= g ≠ g a), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift into QM).
theorem forIn_mapWithPostcondition.h12 : ¬ drop0% Std.IterM.forIn_mapWithPostcondition 12 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun c acc => (⟨1, .yield (acc + c)⟩ : QM _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_mapWithPostcondition`, idx 14 (LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).
theorem forIn_mapWithPostcondition.h14 : ¬ drop0% Std.IterM.forIn_mapWithPostcondition 14 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_mapWithPostcondition`, idx 16 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).
theorem forIn_mapWithPostcondition.h16 : ¬ drop0% Std.IterM.forIn_mapWithPostcondition 16 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_mapM`, idx 10 (LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).
theorem forIn_mapM.h10 : ¬ drop0% Std.IterM.forIn_mapM 10 := by
  intro h
  have := h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.forIn_mapM`, idx 12 (LawfulMonad o): m = n = NW (lawful Nat writer), o = QM (bind adds one iff the continuation is effectful: the count-forgetting lift NW → QM is lawful, but pure a >>= g ≠ g a), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift into QM).
theorem forIn_mapM.h12 : ¬ drop0% Std.IterM.forIn_mapM 12 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun b => pure b) (init := 0) (g := fun c acc => (⟨1, .yield (acc + c)⟩ : QM _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_mapM`, idx 14 (WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.
theorem forIn_mapM.h14 : ¬ drop0% Std.IterM.forIn_mapM 14 := by
  intro h
  have := h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.forIn_mapM`, idx 16 (LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).
theorem forIn_mapM.h16 : ¬ drop0% Std.IterM.forIn_mapM 16 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_mapM`, idx 18 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).
theorem forIn_mapM.h18 : ¬ drop0% Std.IterM.forIn_mapM 18 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_map`, idx 7 (LawfulMonad m): m = MB (lawful Nat writer bind/pure, but map adds one), n = NW, lawful lift MB → NW, list iterator [0]: the map combinator maps in m.
theorem forIn_map.h7 : ¬ drop0% Std.IterM.forIn_map 7 := by
  intro h
  have := h (m := MB) (n := NW) (it := [0].iterM MB) (f := id) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.forIn_map`, idx 9 (LawfulMonad n): m = NW, n = QM (bind adds one iff the continuation is effectful; the count-forgetting lift NW → QM is lawful), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop.
theorem forIn_map.h9 : ¬ drop0% Std.IterM.forIn_map 9 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := QM) (it := [0].iterM NW) (f := id) (init := 0) (g := fun c acc => (⟨1, .yield (acc + c)⟩ : QM _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_map`, idx 11 (LawfulMonadLiftT m n): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.
theorem forIn_map.h11 : ¬ drop0% Std.IterM.forIn_map 11 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := id) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterWithPostcondition`, idx 9 (LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).
theorem forIn_filterWithPostcondition.h9 : ¬ drop0% Std.IterM.forIn_filterWithPostcondition 9 := by
  intro h
  have := h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.forIn_filterWithPostcondition`, idx 11 (LawfulMonad o): m = n = NW (lawful Nat writer), o = QM (bind adds one iff the continuation is effectful: the count-forgetting lift NW → QM is lawful, but pure a >>= g ≠ g a), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift into QM).
theorem forIn_filterWithPostcondition.h11 : ¬ drop0% Std.IterM.forIn_filterWithPostcondition 11 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun c acc => (⟨1, .yield (acc + c)⟩ : QM _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterWithPostcondition`, idx 13 (LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).
theorem forIn_filterWithPostcondition.h13 : ¬ drop0% Std.IterM.forIn_filterWithPostcondition 13 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterWithPostcondition`, idx 15 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).
theorem forIn_filterWithPostcondition.h15 : ¬ drop0% Std.IterM.forIn_filterWithPostcondition 15 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterM`, idx 9 (LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).
theorem forIn_filterM.h9 : ¬ drop0% Std.IterM.forIn_filterM 9 := by
  intro h
  have := h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.forIn_filterM`, idx 11 (LawfulMonad o): m = n = NW (lawful Nat writer), o = QM (bind adds one iff the continuation is effectful: the count-forgetting lift NW → QM is lawful, but pure a >>= g ≠ g a), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift into QM).
theorem forIn_filterM.h11 : ¬ drop0% Std.IterM.forIn_filterM 11 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => (⟨1, .yield (acc + c)⟩ : QM _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterM`, idx 13 (WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.
theorem forIn_filterM.h13 : ¬ drop0% Std.IterM.forIn_filterM 13 := by
  intro h
  have := h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.forIn_filterM`, idx 15 (LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).
theorem forIn_filterM.h15 : ¬ drop0% Std.IterM.forIn_filterM 15 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filterM`, idx 17 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).
theorem forIn_filterM.h17 : ¬ drop0% Std.IterM.forIn_filterM 17 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filter`, idx 8 (LawfulMonad n): m = NW, n = QM (bind adds one iff the continuation is effectful; the count-forgetting lift NW → QM is lawful), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop.
theorem forIn_filter.h8 : ¬ drop0% Std.IterM.forIn_filter 8 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := QM) (it := [0].iterM NW) (f := fun _ => true) (init := 0) (g := fun c acc => (⟨1, .yield (acc + c)⟩ : QM _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.forIn_filter`, idx 10 (LawfulMonadLiftT m n): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.
theorem forIn_filter.h10 : ¬ drop0% Std.IterM.forIn_filter 10 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun _ => true) (init := 0) (g := fun c acc => pure (.yield (acc + c)))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterMapWithPostcondition`, idx 13 (LawfulMonad n): m = Id, n = FM (Bool writer whose map and attach flip the flag: bind/pure lawful, weakly lawful attach, lawful lifts from Id and to o = W), list iterator [0]: the left side binds f's operation (resp. attach) directly, the right side maps it.
theorem foldM_filterMapWithPostcondition.h13 : ¬ drop0% Std.IterM.foldM_filterMapWithPostcondition 13 := by
  intro h
  have := h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.foldM_filterMapWithPostcondition`, idx 14 (LawfulMonad o): m = n = NW (lawful Nat writer), o = QM (bind adds one iff the continuation is effectful: the count-forgetting lift NW → QM is lawful, but pure a >>= g ≠ g a), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift into QM).
theorem foldM_filterMapWithPostcondition.h14 : ¬ drop0% Std.IterM.foldM_filterMapWithPostcondition 14 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun d c => (⟨1, d + c⟩ : QM Nat))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterMapWithPostcondition`, idx 21 (LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).
theorem foldM_filterMapWithPostcondition.h21 : ¬ drop0% Std.IterM.foldM_filterMapWithPostcondition 21 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterMapWithPostcondition`, idx 22 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).
theorem foldM_filterMapWithPostcondition.h22 : ¬ drop0% Std.IterM.foldM_filterMapWithPostcondition 22 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterMapM`, idx 13 (LawfulMonad n): m = Id, n = FM (Bool writer whose map and attach flip the flag: bind/pure lawful, weakly lawful attach, lawful lifts from Id and to o = W), list iterator [0]: the left side binds f's operation (resp. attach) directly, the right side maps it.
theorem foldM_filterMapM.h13 : ¬ drop0% Std.IterM.foldM_filterMapM 13 := by
  intro h
  have := h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.foldM_filterMapM`, idx 14 (WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.
theorem foldM_filterMapM.h14 : ¬ drop0% Std.IterM.foldM_filterMapM 14 := by
  intro h
  have := h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.foldM_filterMapM`, idx 16 (LawfulMonad o): m = n = NW (lawful Nat writer), o = QM (bind adds one iff the continuation is effectful: the count-forgetting lift NW → QM is lawful, but pure a >>= g ≠ g a), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift into QM).
theorem foldM_filterMapM.h16 : ¬ drop0% Std.IterM.foldM_filterMapM 16 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun b => pure (some b)) (init := 0) (g := fun d c => (⟨1, d + c⟩ : QM Nat))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterMapM`, idx 23 (LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).
theorem foldM_filterMapM.h23 : ¬ drop0% Std.IterM.foldM_filterMapM 23 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => pure (some b)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterMapM`, idx 24 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).
theorem foldM_filterMapM.h24 : ¬ drop0% Std.IterM.foldM_filterMapM 24 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_mapWithPostcondition`, idx 13 (LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).
theorem foldM_mapWithPostcondition.h13 : ¬ drop0% Std.IterM.foldM_mapWithPostcondition 13 := by
  intro h
  have := h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.foldM_mapWithPostcondition`, idx 14 (LawfulMonad o): m = n = NW (lawful Nat writer), o = QM (bind adds one iff the continuation is effectful: the count-forgetting lift NW → QM is lawful, but pure a >>= g ≠ g a), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift into QM).
theorem foldM_mapWithPostcondition.h14 : ¬ drop0% Std.IterM.foldM_mapWithPostcondition 14 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun d c => (⟨1, d + c⟩ : QM Nat))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_mapWithPostcondition`, idx 21 (LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).
theorem foldM_mapWithPostcondition.h21 : ¬ drop0% Std.IterM.foldM_mapWithPostcondition 21 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_mapWithPostcondition`, idx 22 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).
theorem foldM_mapWithPostcondition.h22 : ¬ drop0% Std.IterM.foldM_mapWithPostcondition 22 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_mapM`, idx 13 (LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).
theorem foldM_mapM.h13 : ¬ drop0% Std.IterM.foldM_mapM 13 := by
  intro h
  have := h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.foldM_mapM`, idx 14 (WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.
theorem foldM_mapM.h14 : ¬ drop0% Std.IterM.foldM_mapM 14 := by
  intro h
  have := h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.foldM_mapM`, idx 16 (LawfulMonad o): m = n = NW (lawful Nat writer), o = QM (bind adds one iff the continuation is effectful: the count-forgetting lift NW → QM is lawful, but pure a >>= g ≠ g a), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift into QM).
theorem foldM_mapM.h16 : ¬ drop0% Std.IterM.foldM_mapM 16 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun b => pure b) (init := 0) (g := fun d c => (⟨1, d + c⟩ : QM Nat))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_mapM`, idx 23 (LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).
theorem foldM_mapM.h23 : ¬ drop0% Std.IterM.foldM_mapM 23 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => pure b) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_mapM`, idx 24 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).
theorem foldM_mapM.h24 : ¬ drop0% Std.IterM.foldM_mapM 24 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterWithPostcondition`, idx 12 (LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).
theorem foldM_filterWithPostcondition.h12 : ¬ drop0% Std.IterM.foldM_filterWithPostcondition 12 := by
  intro h
  have := h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.foldM_filterWithPostcondition`, idx 13 (LawfulMonad o): m = n = NW (lawful Nat writer), o = QM (bind adds one iff the continuation is effectful: the count-forgetting lift NW → QM is lawful, but pure a >>= g ≠ g a), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift into QM).
theorem foldM_filterWithPostcondition.h13 : ¬ drop0% Std.IterM.foldM_filterWithPostcondition 13 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun d c => (⟨1, d + c⟩ : QM Nat))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterWithPostcondition`, idx 20 (LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).
theorem foldM_filterWithPostcondition.h20 : ¬ drop0% Std.IterM.foldM_filterWithPostcondition 20 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterWithPostcondition`, idx 21 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).
theorem foldM_filterWithPostcondition.h21 : ¬ drop0% Std.IterM.foldM_filterWithPostcondition 21 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterM`, idx 12 (LawfulMonad n): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).
theorem foldM_filterM.h12 : ¬ drop0% Std.IterM.foldM_filterM 12 := by
  intro h
  have := h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.foldM_filterM`, idx 13 (WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.
theorem foldM_filterM.h13 : ¬ drop0% Std.IterM.foldM_filterM 13 := by
  intro h
  have := h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.foldM_filterM`, idx 15 (LawfulMonad o): m = n = NW (lawful Nat writer), o = QM (bind adds one iff the continuation is effectful: the count-forgetting lift NW → QM is lawful, but pure a >>= g ≠ g a), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift into QM).
theorem foldM_filterM.h15 : ¬ drop0% Std.IterM.foldM_filterM 15 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := NW) (o := QM) (it := [0].iterM NW) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => (⟨1, d + c⟩ : QM Nat))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterM`, idx 22 (LawfulMonadLiftT m n): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).
theorem foldM_filterM.h22 : ¬ drop0% Std.IterM.foldM_filterM 22 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterM`, idx 23 (LawfulMonadLiftT n o): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).
theorem foldM_filterM.h23 : ¬ drop0% Std.IterM.foldM_filterM 23 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterMap`, idx 11 (LawfulMonad n): m = NW, n = QM (bind adds one iff the continuation is effectful; the count-forgetting lift NW → QM is lawful), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop.
theorem foldM_filterMap.h11 : ¬ drop0% Std.IterM.foldM_filterMap 11 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := QM) (it := [0].iterM NW) (f := some) (init := 0) (g := fun d c => (⟨1, d + c⟩ : QM Nat))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filterMap`, idx 15 (LawfulMonadLiftT m n): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.
theorem foldM_filterMap.h15 : ¬ drop0% Std.IterM.foldM_filterMap 15 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := some) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_map`, idx 10 (LawfulMonad m): m = MB (lawful Nat writer bind/pure, but map adds one), n = NW, lawful lift MB → NW, list iterator [0]: the map combinator maps in m.
theorem foldM_map.h10 : ¬ drop0% Std.IterM.foldM_map 10 := by
  intro h
  have := h (m := MB) (n := NW) (it := [0].iterM MB) (f := id) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.foldM_map`, idx 11 (LawfulMonad n): m = NW, n = QM (bind adds one iff the continuation is effectful; the count-forgetting lift NW → QM is lawful), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop.
theorem foldM_map.h11 : ¬ drop0% Std.IterM.foldM_map 11 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := QM) (it := [0].iterM NW) (f := id) (init := 0) (g := fun d c => (⟨1, d + c⟩ : QM Nat))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_map`, idx 15 (LawfulMonadLiftT m n): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.
theorem foldM_map.h15 : ¬ drop0% Std.IterM.foldM_map 15 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := id) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filter`, idx 10 (LawfulMonad n): m = NW, n = QM (bind adds one iff the continuation is effectful; the count-forgetting lift NW → QM is lawful), list iterator [0], effectful g; the base iterator's IteratorLoop is evilLoop.
theorem foldM_filter.h10 : ¬ drop0% Std.IterM.foldM_filter 10 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) NW QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW QM := evilLoop_lawful
  have := h (m := NW) (n := QM) (it := [0].iterM NW) (f := fun _ => true) (init := 0) (g := fun d c => (⟨1, d + c⟩ : QM Nat))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.foldM_filter`, idx 14 (LawfulMonadLiftT m n): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.
theorem foldM_filter.h14 : ¬ drop0% Std.IterM.foldM_filter 14 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun _ => true) (init := 0) (g := fun d c => pure (d + c))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_filterMapWithPostcondition`, idx 11 (LawfulMonad n): m = Id, n = QM (bind adds one iff the continuation is effectful), list iterator [0], effectful f; the base iterator's IteratorLoop is evilLoop.
theorem fold_filterMapWithPostcondition.h11 : ¬ drop0% Std.IterM.fold_filterMapWithPostcondition 11 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) Id QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id QM := evilLoop_lawful
  have := h (init := 0) (g := fun d c => d + c) (m := Id) (n := QM) (it := [0].iterM Id) (f := fun b => ⟨fun _ => True, (⟨1, ⟨some b, trivial⟩⟩ : QM _)⟩)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_filterMapWithPostcondition`, idx 15 (LawfulMonadLiftT m n): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.
theorem fold_filterMapWithPostcondition.h15 : ¬ drop0% Std.IterM.fold_filterMapWithPostcondition 15 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure (some b))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_filterMapM`, idx 12 (LawfulMonad n): m = Id, n = QM (bind adds one iff the continuation is effectful), list iterator [0], effectful f; the base iterator's IteratorLoop is evilLoop.
theorem fold_filterMapM.h12 : ¬ drop0% Std.IterM.fold_filterMapM 12 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) Id QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id QM := evilLoop_lawful
  have := h (init := 0) (g := fun d c => d + c) (m := Id) (n := QM) (it := [0].iterM Id) (f := fun b => (⟨1, some b⟩ : QM _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_filterMapM`, idx 13 (WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), list iterator [0].
theorem fold_filterMapM.h13 : ¬ drop0% Std.IterM.fold_filterMapM 13 := by
  intro h
  have := h (init := 0) (g := fun d c => d + c) (m := Id) (n := NWb) (it := [0].iterM Id) (f := fun b => pure (some b))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.fold_filterMapM`, idx 17 (LawfulMonadLiftT m n): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.
theorem fold_filterMapM.h17 : ¬ drop0% Std.IterM.fold_filterMapM 17 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun b => pure (some b))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_mapWithPostcondition`, idx 11 (LawfulMonad n): m = Id, n = QM (bind adds one iff the continuation is effectful), list iterator [0], effectful f; the base iterator's IteratorLoop is evilLoop.
theorem fold_mapWithPostcondition.h11 : ¬ drop0% Std.IterM.fold_mapWithPostcondition 11 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) Id QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id QM := evilLoop_lawful
  have := h (init := 0) (g := fun d c => d + c) (m := Id) (n := QM) (it := [0].iterM Id) (f := fun b => ⟨fun _ => True, (⟨1, ⟨b, trivial⟩⟩ : QM _)⟩)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_mapWithPostcondition`, idx 15 (LawfulMonadLiftT m n): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.
theorem fold_mapWithPostcondition.h15 : ¬ drop0% Std.IterM.fold_mapWithPostcondition 15 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure b)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_mapM`, idx 12 (LawfulMonad n): m = Id, n = QM (bind adds one iff the continuation is effectful), list iterator [0], effectful f; the base iterator's IteratorLoop is evilLoop.
theorem fold_mapM.h12 : ¬ drop0% Std.IterM.fold_mapM 12 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) Id QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id QM := evilLoop_lawful
  have := h (init := 0) (g := fun d c => d + c) (m := Id) (n := QM) (it := [0].iterM Id) (f := fun b => (⟨1, b⟩ : QM _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_mapM`, idx 13 (WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), list iterator [0].
theorem fold_mapM.h13 : ¬ drop0% Std.IterM.fold_mapM 13 := by
  intro h
  have := h (init := 0) (g := fun d c => d + c) (m := Id) (n := NWb) (it := [0].iterM Id) (f := fun b => pure b)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.fold_mapM`, idx 17 (LawfulMonadLiftT m n): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.
theorem fold_mapM.h17 : ¬ drop0% Std.IterM.fold_mapM 17 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun b => pure b)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_filterWithPostcondition`, idx 10 (LawfulMonad n): m = Id, n = QM (bind adds one iff the continuation is effectful), list iterator [0], effectful f; the base iterator's IteratorLoop is evilLoop.
theorem fold_filterWithPostcondition.h10 : ¬ drop0% Std.IterM.fold_filterWithPostcondition 10 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) Id QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id QM := evilLoop_lawful
  have := h (init := 0) (g := fun d c => d + c) (m := Id) (n := QM) (it := [0].iterM Id) (f := fun _ => ⟨fun _ => True, (⟨1, ⟨.up true, trivial⟩⟩ : QM _)⟩)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_filterWithPostcondition`, idx 14 (LawfulMonadLiftT m n): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.
theorem fold_filterWithPostcondition.h14 : ¬ drop0% Std.IterM.fold_filterWithPostcondition 14 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun _ => PostconditionT.pure (.up true))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_filterM`, idx 11 (LawfulMonad n): m = Id, n = QM (bind adds one iff the continuation is effectful), list iterator [0], effectful f; the base iterator's IteratorLoop is evilLoop.
theorem fold_filterM.h11 : ¬ drop0% Std.IterM.fold_filterM 11 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) Id QM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id QM := evilLoop_lawful
  have := h (init := 0) (g := fun d c => d + c) (m := Id) (n := QM) (it := [0].iterM Id) (f := fun _ => (⟨1, .up true⟩ : QM _))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_filterM`, idx 12 (WeaklyLawfulMonadAttach n): m = Id, n = NWb (lawful Nat writer whose attach adds one), list iterator [0].
theorem fold_filterM.h12 : ¬ drop0% Std.IterM.fold_filterM 12 := by
  intro h
  have := h (init := 0) (g := fun d c => d + c) (m := Id) (n := NWb) (it := [0].iterM Id) (f := fun _ => pure (.up true))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.fold_filterM`, idx 16 (LawfulMonadLiftT m n): m = NW2, n = NW, lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.
theorem fold_filterM.h16 : ¬ drop0% Std.IterM.fold_filterM 16 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := h (init := 0) (g := fun d c => d + c) (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun _ => pure (.up true))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_filterMap`, idx 8 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem fold_filterMap.h8 : ¬ drop0% Std.IterM.fold_filterMap 8 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := some) (g := fun d c => d + c) (init := 0)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_map`, idx 8 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem fold_map.h8 : ¬ drop0% Std.IterM.fold_map 8 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := id) (g := fun d c => d + c) (init := 0)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.fold_filter`, idx 7 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem fold_filter.h7 : ¬ drop0% Std.IterM.fold_filter 7 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := fun _ => true) (g := fun d c => d + c) (init := 0)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.length_map`, idx 8 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem length_map.h8 : ¬ drop0% Std.IterM.length_map 8 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := id)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.anyM_filterMapM`, idx 12 (LawfulMonad n): m = Id, n = CM (counting monad, bind adds one), list iterator [0].
theorem anyM_filterMapM.h12 : ¬ drop0% Std.IterM.anyM_filterMapM 12 := by
  intro h
  have := h (p := fun _ => pure (.up true)) (m := Id) (n := CM) (it := [0].iterM Id) (f := fun b => pure (some b))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.anyM_filterMapM`, idx 13 (WeaklyLawfulMonadAttach n): m = Id, n = NWa (lawful Nat writer whose attach drops the count), list iterator [0], effectful f.
theorem anyM_filterMapM.h13 : ¬ drop0% Std.IterM.anyM_filterMapM 13 := by
  intro h
  have := h (p := fun _ => pure (.up true)) (m := Id) (n := NWa) (it := [0].iterM Id) (f := fun b => (⟨1, some b⟩ : NWa _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.anyM_mapM`, idx 12 (LawfulMonad n): m = Id, n = CM (counting monad, bind adds one), list iterator [0].
theorem anyM_mapM.h12 : ¬ drop0% Std.IterM.anyM_mapM 12 := by
  intro h
  have := h (p := fun _ => pure (.up true)) (m := Id) (n := CM) (it := [0].iterM Id) (f := fun b => pure b)
  clear h; revert this
  ev_all; simp

-- `Std.IterM.anyM_mapM`, idx 13 (WeaklyLawfulMonadAttach n): m = Id, n = NWa (lawful Nat writer whose attach drops the count), list iterator [0], effectful f.
theorem anyM_mapM.h13 : ¬ drop0% Std.IterM.anyM_mapM 13 := by
  intro h
  have := h (p := fun _ => pure (.up true)) (m := Id) (n := NWa) (it := [0].iterM Id) (f := fun b => (⟨1, b⟩ : NWa _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.anyM_filterM`, idx 11 (LawfulMonad n): m = Id, n = CM (counting monad, bind adds one), list iterator [0].
theorem anyM_filterM.h11 : ¬ drop0% Std.IterM.anyM_filterM 11 := by
  intro h
  have := h (p := fun _ => pure (.up true)) (m := Id) (n := CM) (it := [0].iterM Id) (f := fun _ => pure (.up true))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.anyM_filterM`, idx 12 (WeaklyLawfulMonadAttach n): m = Id, n = NWa (lawful Nat writer whose attach drops the count), list iterator [0], effectful f.
theorem anyM_filterM.h12 : ¬ drop0% Std.IterM.anyM_filterM 12 := by
  intro h
  have := h (p := fun _ => pure (.up true)) (m := Id) (n := NWa) (it := [0].iterM Id) (f := fun _ => (⟨1, .up true⟩ : NWa _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.anyM_filterMap`, idx 8 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem anyM_filterMap.h8 : ¬ drop0% Std.IterM.anyM_filterMap 8 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := some) (p := fun _ => pure (.up true))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.anyM_map`, idx 8 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem anyM_map.h8 : ¬ drop0% Std.IterM.anyM_map 8 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := id) (p := fun _ => pure (.up true))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.anyM_filter`, idx 7 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem anyM_filter.h7 : ¬ drop0% Std.IterM.anyM_filter 7 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := fun _ => true) (p := fun _ => pure (.up true))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.any_filterMapM`, idx 13 (LawfulMonad n): m = Id, n = WM (bind doubles the count of its first argument: pure from Id is a lawful lift, weakly lawful attach, but bind is not associative), list iterator [0], effectful f: the two sides bracket the effect of f differently.
theorem any_filterMapM.h13 : ¬ drop0% Std.IterM.any_filterMapM 13 := by
  intro h
  have := h (p := fun _ => true) (m := Id) (n := WM) (it := [0].iterM Id) (f := fun b => (⟨1, some b⟩ : WM _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.any_filterMapM`, idx 14 (WeaklyLawfulMonadAttach n): m = Id, n = NWa (lawful Nat writer whose attach drops the count), list iterator [0], effectful f.
theorem any_filterMapM.h14 : ¬ drop0% Std.IterM.any_filterMapM 14 := by
  intro h
  have := h (p := fun _ => true) (m := Id) (n := NWa) (it := [0].iterM Id) (f := fun b => (⟨1, some b⟩ : NWa _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.any_mapM`, idx 13 (LawfulMonad n): m = Id, n = WM (bind doubles the count of its first argument: pure from Id is a lawful lift, weakly lawful attach, but bind is not associative), list iterator [0], effectful f: the two sides bracket the effect of f differently.
theorem any_mapM.h13 : ¬ drop0% Std.IterM.any_mapM 13 := by
  intro h
  have := h (p := fun _ => true) (m := Id) (n := WM) (it := [0].iterM Id) (f := fun b => (⟨1, b⟩ : WM _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.any_mapM`, idx 14 (WeaklyLawfulMonadAttach n): m = Id, n = NWa (lawful Nat writer whose attach drops the count), list iterator [0], effectful f.
theorem any_mapM.h14 : ¬ drop0% Std.IterM.any_mapM 14 := by
  intro h
  have := h (p := fun _ => true) (m := Id) (n := NWa) (it := [0].iterM Id) (f := fun b => (⟨1, b⟩ : NWa _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.any_filterM`, idx 12 (LawfulMonad n): m = Id, n = WM (bind doubles the count of its first argument: pure from Id is a lawful lift, weakly lawful attach, but bind is not associative), list iterator [0], effectful f: the two sides bracket the effect of f differently.
theorem any_filterM.h12 : ¬ drop0% Std.IterM.any_filterM 12 := by
  intro h
  have := h (p := fun _ => true) (m := Id) (n := WM) (it := [0].iterM Id) (f := fun _ => (⟨1, .up true⟩ : WM _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.any_filterM`, idx 13 (WeaklyLawfulMonadAttach n): m = Id, n = NWa (lawful Nat writer whose attach drops the count), list iterator [0], effectful f.
theorem any_filterM.h13 : ¬ drop0% Std.IterM.any_filterM 13 := by
  intro h
  have := h (p := fun _ => true) (m := Id) (n := NWa) (it := [0].iterM Id) (f := fun _ => (⟨1, .up true⟩ : NWa _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.any_filterMap`, idx 8 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem any_filterMap.h8 : ¬ drop0% Std.IterM.any_filterMap 8 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := some) (p := fun _ => true)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.any_map`, idx 8 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem any_map.h8 : ¬ drop0% Std.IterM.any_map 8 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := id) (p := fun _ => true)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.allM_filterMapM`, idx 12 (LawfulMonad n): m = Id, n = WM (bind doubles the count of its first argument: pure from Id is a lawful lift, weakly lawful attach, but bind is not associative), list iterator [0], effectful f: the two sides bracket the effect of f differently.
theorem allM_filterMapM.h12 : ¬ drop0% Std.IterM.allM_filterMapM 12 := by
  intro h
  have := h (p := fun _ => pure (.up true)) (m := Id) (n := WM) (it := [0].iterM Id) (f := fun b => (⟨1, some b⟩ : WM _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.allM_filterMapM`, idx 13 (WeaklyLawfulMonadAttach n): m = Id, n = NWa (lawful Nat writer whose attach drops the count), list iterator [0], effectful f.
theorem allM_filterMapM.h13 : ¬ drop0% Std.IterM.allM_filterMapM 13 := by
  intro h
  have := h (p := fun _ => pure (.up true)) (m := Id) (n := NWa) (it := [0].iterM Id) (f := fun b => (⟨1, some b⟩ : NWa _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.allM_mapM`, idx 12 (LawfulMonad n): m = Id, n = WM (bind doubles the count of its first argument: pure from Id is a lawful lift, weakly lawful attach, but bind is not associative), list iterator [0], effectful f: the two sides bracket the effect of f differently.
theorem allM_mapM.h12 : ¬ drop0% Std.IterM.allM_mapM 12 := by
  intro h
  have := h (p := fun _ => pure (.up true)) (m := Id) (n := WM) (it := [0].iterM Id) (f := fun b => (⟨1, b⟩ : WM _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.allM_mapM`, idx 13 (WeaklyLawfulMonadAttach n): m = Id, n = NWa (lawful Nat writer whose attach drops the count), list iterator [0], effectful f.
theorem allM_mapM.h13 : ¬ drop0% Std.IterM.allM_mapM 13 := by
  intro h
  have := h (p := fun _ => pure (.up true)) (m := Id) (n := NWa) (it := [0].iterM Id) (f := fun b => (⟨1, b⟩ : NWa _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.allM_filterM`, idx 11 (LawfulMonad n): m = Id, n = WM (bind doubles the count of its first argument: pure from Id is a lawful lift, weakly lawful attach, but bind is not associative), list iterator [0], effectful f: the two sides bracket the effect of f differently.
theorem allM_filterM.h11 : ¬ drop0% Std.IterM.allM_filterM 11 := by
  intro h
  have := h (p := fun _ => pure (.up true)) (m := Id) (n := WM) (it := [0].iterM Id) (f := fun _ => (⟨1, .up true⟩ : WM _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.allM_filterM`, idx 12 (WeaklyLawfulMonadAttach n): m = Id, n = NWa (lawful Nat writer whose attach drops the count), list iterator [0], effectful f.
theorem allM_filterM.h12 : ¬ drop0% Std.IterM.allM_filterM 12 := by
  intro h
  have := h (p := fun _ => pure (.up true)) (m := Id) (n := NWa) (it := [0].iterM Id) (f := fun _ => (⟨1, .up true⟩ : NWa _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.allM_filterMap`, idx 8 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem allM_filterMap.h8 : ¬ drop0% Std.IterM.allM_filterMap 8 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := some) (p := fun _ => pure (.up true))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.allM_map`, idx 8 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem allM_map.h8 : ¬ drop0% Std.IterM.allM_map 8 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := id) (p := fun _ => pure (.up true))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.allM_filter`, idx 7 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem allM_filter.h7 : ¬ drop0% Std.IterM.allM_filter 7 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := fun _ => true) (p := fun _ => pure (.up true))
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.all_filterMapM`, idx 13 (LawfulMonad n): m = Id, n = WM (bind doubles the count of its first argument: pure from Id is a lawful lift, weakly lawful attach, but bind is not associative), list iterator [0], effectful f: the two sides bracket the effect of f differently.
theorem all_filterMapM.h13 : ¬ drop0% Std.IterM.all_filterMapM 13 := by
  intro h
  have := h (p := fun _ => true) (m := Id) (n := WM) (it := [0].iterM Id) (f := fun b => (⟨1, some b⟩ : WM _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.all_filterMapM`, idx 14 (WeaklyLawfulMonadAttach n): m = Id, n = NWa (lawful Nat writer whose attach drops the count), list iterator [0], effectful f.
theorem all_filterMapM.h14 : ¬ drop0% Std.IterM.all_filterMapM 14 := by
  intro h
  have := h (p := fun _ => true) (m := Id) (n := NWa) (it := [0].iterM Id) (f := fun b => (⟨1, some b⟩ : NWa _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.all_mapM`, idx 13 (LawfulMonad n): m = Id, n = WM (bind doubles the count of its first argument: pure from Id is a lawful lift, weakly lawful attach, but bind is not associative), list iterator [0], effectful f: the two sides bracket the effect of f differently.
theorem all_mapM.h13 : ¬ drop0% Std.IterM.all_mapM 13 := by
  intro h
  have := h (p := fun _ => true) (m := Id) (n := WM) (it := [0].iterM Id) (f := fun b => (⟨1, b⟩ : WM _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.all_mapM`, idx 14 (WeaklyLawfulMonadAttach n): m = Id, n = NWa (lawful Nat writer whose attach drops the count), list iterator [0], effectful f.
theorem all_mapM.h14 : ¬ drop0% Std.IterM.all_mapM 14 := by
  intro h
  have := h (p := fun _ => true) (m := Id) (n := NWa) (it := [0].iterM Id) (f := fun b => (⟨1, b⟩ : NWa _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.all_filterM`, idx 12 (LawfulMonad n): m = Id, n = WM (bind doubles the count of its first argument: pure from Id is a lawful lift, weakly lawful attach, but bind is not associative), list iterator [0], effectful f: the two sides bracket the effect of f differently.
theorem all_filterM.h12 : ¬ drop0% Std.IterM.all_filterM 12 := by
  intro h
  have := h (p := fun _ => true) (m := Id) (n := WM) (it := [0].iterM Id) (f := fun _ => (⟨1, .up true⟩ : WM _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.all_filterM`, idx 13 (WeaklyLawfulMonadAttach n): m = Id, n = NWa (lawful Nat writer whose attach drops the count), list iterator [0], effectful f.
theorem all_filterM.h13 : ¬ drop0% Std.IterM.all_filterM 13 := by
  intro h
  have := h (p := fun _ => true) (m := Id) (n := NWa) (it := [0].iterM Id) (f := fun _ => (⟨1, .up true⟩ : NWa _))
  clear h; revert this
  ev_all; simp

-- `Std.IterM.all_filterMap`, idx 8 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem all_filterMap.h8 : ¬ drop0% Std.IterM.all_filterMap 8 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := some) (p := fun _ => true)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.IterM.all_map`, idx 8 (LawfulMonad m): m = counting monad CM (bind adds one; not lawful), list iterator [0]; the IteratorLoop instance of the base iterator is evilLoop (lawful, but returns init for the non-lawful lift of CM), the combinator's default loop does not.
theorem all_map.h8 : ¬ drop0% Std.IterM.all_map 8 := by
  intro h
  letI : IteratorLoop (ListIterator Nat) CM CM := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) CM CM := evilLoop_lawful
  have := h (m := CM) (it := [0].iterM CM) (f := id) (p := fun _ => true)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : CM Nat)) 0 (by ev_simp; simp)
  ev_all; simp

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

-- `Std.IterM.forIn_filterMap`, idx 7 (LawfulMonad m): removable. The filterMap iterator's step only binds and returns pure values in m; the lawful lift m → n (LawfulMonadLiftT) and LawfulMonad n turn it into the base step followed by pure, so the induction of the library proof goes through in n.
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

-- `Std.IterM.forIn_filter`, idx 6 (LawfulMonad m): removable; filter is filterMap with an if-then-else, so it follows from the proof for forIn_filterMap above.
theorem forIn_filter.h6 : drop% Std.IterM.forIn_filter 6 := by
  intro m n α β γ _ _ _ _ _ _ _ _ _ it f init g
  refine (forIn_filterMap.h7 (it := it) (f := fun b => if f b then some b else none)
    (init := init) (g := g)).trans ?_
  congr 1; funext out acc; cases f out <;> rfl

-- `Std.IterM.foldM_filterMap`, idx 10 (LawfulMonad m): removable; foldM is forIn with a mapped step function, so it follows from the proof for forIn_filterMap above (map_pure in n).
theorem foldM_filterMap.h10 : drop% Std.IterM.foldM_filterMap 10 := by
  intro α β γ δ m n _ _ _ _ _ _ _ _ _ f g init it
  refine (forIn_filterMap.h7 (it := it) (f := f) (init := init)
    (g := fun c acc => ForInStep.yield <$> g acc c)).trans ?_
  show _ = ForIn.forIn it init _
  congr 1; funext out acc; cases h : f out <;> simp [h]

-- `Std.IterM.foldM_filter`, idx 9 (LawfulMonad m): removable; as for foldM_filterMap, with filter = filterMap of an if-then-else.
theorem foldM_filter.h9 : drop% Std.IterM.foldM_filter 9 := by
  intro α β δ m n _ _ _ _ _ _ _ _ _ f g init it
  refine (forIn_filterMap.h7 (it := it) (f := fun b => if f b then some b else none) (init := init)
    (g := fun c acc => ForInStep.yield <$> g acc c)).trans ?_
  show _ = ForIn.forIn it init _
  congr 1; funext out acc; cases h : f out <;> simp [h]

end ItMonadMAHand
