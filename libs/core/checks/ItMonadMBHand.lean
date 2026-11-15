import Lean

/-!
Hand pass over cluster `ItMonadMB` (hand8): 189 monad-law hypotheses (`LawfulMonad`,
`WeaklyLawfulMonadAttach`, `LawfulMonadLiftT`) of the `Std.IterM` lemmas in
`Init.Data.Iterators.Lemmas.Combinators.Monadic` (`FilterMap`, `FlatMap`, `Take`, `ULift`), second
half by name. For hypothesis `hᵢ` of theorem `T` this file proves `¬T'` (necessary; universes set to
0 by `drop0%`) or `T'` (removable; `drop%`, universe parameters kept).

174 necessary, 14 removable, 1 independent (`LawfulMonad n` of `toList_uLift`, see
`runs/hand8/ItMonadMB_independent.jsonl`: the two sides only differ in the type at which `n`'s `map`
is applied, `Array (ULift β)` vs `ULift (List β)`, and these are equinumerous).

Models (all writer monads on `Int × α` as structures `LW`, `BW`, ...; see the docstrings):
* `LW`, `LW2`, `TW`: lawful writers (count added by `bind`). `BW`: `bind` counts 1. `MW`: `map`
  counts 1, `attach` -1 (weakly lawful attach). `HW`: `map` halves, `attach` doubles. `AW`: `attach`
  counts 1. `ZW`: `attach` counts 1 on count-0 actions.
* Classical (type-dependent, via `ntv α` = 1 iff `α` has two distinct elements): `CA` (`attach`
  adds `ntv α`), `CM` (`map` adds `ntv β`, `attach` subtracts `ntv α`), `NB` (`bind` adds `ntv α`
  when a count-0 action is followed by a counting one), and the lift `LW → NL` adding `ntv α`.
  These are not natural in the type, which is what separates statements that only differ in the
  type at which an action is attached, mapped, bound or lifted.
* Lifts: identity lifts between the writers (lawful), the ticking lift `LW → TW` (and
  `LW → ULiftT TW`), forgetful lifts `LW → NB`, `BW → ULiftT LW`.
* Iterators: list iterators, and `two m k` (`TwoIt`), which from state 0 may plausibly yield `false`
  or `true`: its step type has two elements while that of a `map` with a constant function has one.
  `twoLoopBW` is a loop for `two` in `BW` that agrees with the default loop on lawful lift-bind
  functions (so `LawfulIteratorLoop` holds) and returns `init` otherwise.

Evaluation: the consumers (`toList`, `toArray`, `toListRev`, the `length` loop) are unfolded by
`rw` with law-free unfolding lemmas (`go_eq'`, `revgo_eq'`, `forIn'_eq'`, from
`WellFounded.extrinsicFix₂_eq_apply` and `Finite`), the steps by law-free step lemmas (`step_fmwp`,
`step_mwp`, `step_flattenAfter'`, ...), and the writer arithmetic by `simp` (`ev`, `evh`). The
monad lemmas are stated as non-`rfl` theorems and the combinators get `@[congr]` lemmas, so `simp`
never rewrites the functions that also occur in the iterators' types. `flattenAfterP%` refers to the
private `Std.IterM.flattenAfter`.

Removable (14): `LawfulMonad n` of `toList/toListRev/toArray_filterMapWithPostcondition_filterMapWithPostcondition`
(every `n`-action reaches `o` through the lawful lift, no `map` in `n`: transport the inner iterator to `o`),
`LawfulMonadLiftT m n` of `..._mapWithPostcondition_mapWithPostcondition` and `..._mapM_mapM` (the lift
`m → n` occurs identically on both sides; library proofs via law-free copies of private lemmas),
`WeaklyLawfulMonadAttach n` of `..._mapM_map` (both sides attach `g (f b)`), `LawfulMonad m` of
`toListRev_uLift`, `toArray_uLift` (the base monad is only used through the lawful lift).

Run with the lean4 repo's stage1 binary: `lean checks/ItMonadMBHand.lean`.
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
  let us := ci.levelParams.map fun _ => levelZero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body


open Lean Meta Elab Term in
/-- The private `Std.IterM.flattenAfter` of `Init.Data.Iterators.Combinators.Monadic.FlatMap` (the
step lemma `IterM.step_flattenAfter` is private too, so it is restated without `LawfulMonad`). -/
elab "flattenAfterP%" : term => do
  let n := mkPrivateNameCore `Init.Data.Iterators.Combinators.Monadic.FlatMap `Std.IterM.flattenAfter
  let c ← getConstInfo n
  return mkConst n (← c.levelParams.mapM fun _ => mkFreshLevelMVar)

namespace ItMonadMBHand
open Std Std.Iterators Std.Iterators.Types

/-- `1` if `α` has two distinct elements, else `0` (classical; used by `CA` and `CM`). -/
noncomputable def ntv (α : Type) : Int := @ite _ (∃ a b : α, a ≠ b) (Classical.propDecidable _) 1 0

theorem ntv_of_ne {α : Type} (a b : α) (h : a ≠ b) : ntv α = 1 := by
  unfold ntv; rw [if_pos ⟨a, b, h⟩]
theorem ntv_of_sub {α : Type} (h : ∀ a b : α, a = b) : ntv α = 0 := by
  unfold ntv; rw [if_neg]; rintro ⟨a, b, hab⟩; exact hab (h a b)
@[simp] theorem ntv_unit : ntv Unit = 0 := ntv_of_sub fun _ _ => rfl
@[simp] theorem ntv_bool : ntv Bool = 1 := ntv_of_ne true false (by decide)
@[simp] theorem ntv_nat : ntv Nat = 1 := ntv_of_ne 0 1 (by decide)
@[simp] theorem ntv_option_unit : ntv (Option Unit) = 1 := ntv_of_ne none (some ()) (by decide)

/-- Lawful writer: `pure` counts 0, `bind` adds, `map` keeps the count, `attach` is lawful. -/
structure LW (α : Type) where
  c : Int
  v : α

/-- A second copy of `LW` (target of lawful identity lifts). -/
structure LW2 (α : Type) where
  c : Int
  v : α

/-- A third copy of `LW`, target of the ticking (unlawful) lift `LW → TW`. -/
structure TW (α : Type) where
  c : Int
  v : α

/-- `bind` counts itself (`pure_bind` fails); `map`, `attach` keep the count. -/
structure BW (α : Type) where
  c : Int
  v : α

/-- `map` adds 1 (`id_map` fails), `attach` subtracts 1 (so `map_attach` holds). -/
structure MW (α : Type) where
  c : Int
  v : α

/-- `map` halves the count (`id_map` fails), `attach` doubles it (so `map_attach` holds). -/
structure HW (α : Type) where
  c : Int
  v : α

/-- Lawful writer whose `attach` adds 1 (`map_attach` fails). -/
structure AW (α : Type) where
  c : Int
  v : α

/-- Lawful writer whose `attach` adds 1 exactly when the count is 0 (`map_attach` fails). -/
structure ZW (α : Type) where
  c : Int
  v : α

/-- A copy of `LW`, target of the classical lift `LW → NL` that adds `ntv α` (not natural in `α`). -/
structure NL (α : Type) where
  c : Int
  v : α

/-- `bind` adds `ntv α` when the first action has count 0 and the continuation does not (not natural in `α`; classical); `pure`, `map`, `attach` lawful. -/
structure NB (α : Type) where
  c : Int
  v : α

/-- Lawful writer whose `attach` adds `ntv α` (1 iff the value type is nontrivial; classical). -/
structure CA (α : Type) where
  c : Int
  v : α

/-- `map` adds `ntv β` for the target type, `attach` subtracts `ntv α` (so `map_attach` holds); classical. -/
structure CM (α : Type) where
  c : Int
  v : α

instance : Monad LW where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c, f x.v⟩
instance : MonadAttach LW where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c, ⟨x.v, rfl⟩⟩
@[simp] theorem LW.pure_def (a : α) : (pure a : LW α) = ⟨0, a⟩ := id rfl
@[simp] theorem LW.bind_def (x : LW α) (f : α → LW β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem LW.map_def (x : LW α) (f : α → β) : f <$> x = ⟨x.c, f x.v⟩ := id rfl
@[simp] theorem LW.attach_def (x : LW α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl
@[simp] theorem LW.attachLift_op (x : LW α) :
    (PostconditionT.attachLift x).operation = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl

instance : LawfulMonad LW := LawfulMonad.mk' _ (fun _ => rfl)
  (fun _ _ => by simp [bind, pure]) (fun _ _ _ => by simp [bind, Int.add_assoc])
  (bind_pure_comp := fun _ _ => by simp [bind, pure, Functor.map])

instance : WeaklyLawfulMonadAttach LW := ⟨by intro _ x; simp [Functor.map, MonadAttach.attach]⟩

instance : Monad LW2 where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c, f x.v⟩
instance : MonadAttach LW2 where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c, ⟨x.v, rfl⟩⟩
@[simp] theorem LW2.pure_def (a : α) : (pure a : LW2 α) = ⟨0, a⟩ := id rfl
@[simp] theorem LW2.bind_def (x : LW2 α) (f : α → LW2 β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem LW2.map_def (x : LW2 α) (f : α → β) : f <$> x = ⟨x.c, f x.v⟩ := id rfl
@[simp] theorem LW2.attach_def (x : LW2 α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl
@[simp] theorem LW2.attachLift_op (x : LW2 α) :
    (PostconditionT.attachLift x).operation = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl

instance : LawfulMonad LW2 := LawfulMonad.mk' _ (fun _ => rfl)
  (fun _ _ => by simp [bind, pure]) (fun _ _ _ => by simp [bind, Int.add_assoc])
  (bind_pure_comp := fun _ _ => by simp [bind, pure, Functor.map])

instance : WeaklyLawfulMonadAttach LW2 := ⟨by intro _ x; simp [Functor.map, MonadAttach.attach]⟩

instance : Monad TW where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c, f x.v⟩
instance : MonadAttach TW where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c, ⟨x.v, rfl⟩⟩
@[simp] theorem TW.pure_def (a : α) : (pure a : TW α) = ⟨0, a⟩ := id rfl
@[simp] theorem TW.bind_def (x : TW α) (f : α → TW β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem TW.map_def (x : TW α) (f : α → β) : f <$> x = ⟨x.c, f x.v⟩ := id rfl
@[simp] theorem TW.attach_def (x : TW α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl
@[simp] theorem TW.attachLift_op (x : TW α) :
    (PostconditionT.attachLift x).operation = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl

instance : LawfulMonad TW := LawfulMonad.mk' _ (fun _ => rfl)
  (fun _ _ => by simp [bind, pure]) (fun _ _ _ => by simp [bind, Int.add_assoc])
  (bind_pure_comp := fun _ _ => by simp [bind, pure, Functor.map])

instance : WeaklyLawfulMonadAttach TW := ⟨by intro _ x; simp [Functor.map, MonadAttach.attach]⟩

instance : Monad BW where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c + 1, (f x.v).v⟩
  map {α β} f x := ⟨x.c, f x.v⟩
instance : MonadAttach BW where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c, ⟨x.v, rfl⟩⟩
@[simp] theorem BW.pure_def (a : α) : (pure a : BW α) = ⟨0, a⟩ := id rfl
@[simp] theorem BW.bind_def (x : BW α) (f : α → BW β) : x >>= f = ⟨x.c + (f x.v).c + 1, (f x.v).v⟩ := id rfl
@[simp] theorem BW.map_def (x : BW α) (f : α → β) : f <$> x = ⟨x.c, f x.v⟩ := id rfl
@[simp] theorem BW.attach_def (x : BW α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl
@[simp] theorem BW.attachLift_op (x : BW α) :
    (PostconditionT.attachLift x).operation = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl

instance : WeaklyLawfulMonadAttach BW := ⟨by intro _ x; simp [Functor.map, MonadAttach.attach]⟩

instance : Monad MW where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c + 1, f x.v⟩
instance : MonadAttach MW where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c - 1, ⟨x.v, rfl⟩⟩
@[simp] theorem MW.pure_def (a : α) : (pure a : MW α) = ⟨0, a⟩ := id rfl
@[simp] theorem MW.bind_def (x : MW α) (f : α → MW β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem MW.map_def (x : MW α) (f : α → β) : f <$> x = ⟨x.c + 1, f x.v⟩ := id rfl
@[simp] theorem MW.attach_def (x : MW α) : MonadAttach.attach x = ⟨x.c - 1, ⟨x.v, rfl⟩⟩ := id rfl
@[simp] theorem MW.attachLift_op (x : MW α) :
    (PostconditionT.attachLift x).operation = ⟨x.c - 1, ⟨x.v, rfl⟩⟩ := id rfl

instance : WeaklyLawfulMonadAttach MW := ⟨by intro _ x; simp [Functor.map, MonadAttach.attach]⟩

instance : Monad HW where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c / 2, f x.v⟩
instance : MonadAttach HW where
  CanReturn x a := a = x.v
  attach {α} x := ⟨2 * x.c, ⟨x.v, rfl⟩⟩
@[simp] theorem HW.pure_def (a : α) : (pure a : HW α) = ⟨0, a⟩ := id rfl
@[simp] theorem HW.bind_def (x : HW α) (f : α → HW β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem HW.map_def (x : HW α) (f : α → β) : f <$> x = ⟨x.c / 2, f x.v⟩ := id rfl
@[simp] theorem HW.attach_def (x : HW α) : MonadAttach.attach x = ⟨2 * x.c, ⟨x.v, rfl⟩⟩ := id rfl
@[simp] theorem HW.attachLift_op (x : HW α) :
    (PostconditionT.attachLift x).operation = ⟨2 * x.c, ⟨x.v, rfl⟩⟩ := id rfl

instance : WeaklyLawfulMonadAttach HW := ⟨by intro _ x; simp [Functor.map, MonadAttach.attach]⟩

instance : Monad AW where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c, f x.v⟩
instance : MonadAttach AW where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c + 1, ⟨x.v, rfl⟩⟩
@[simp] theorem AW.pure_def (a : α) : (pure a : AW α) = ⟨0, a⟩ := id rfl
@[simp] theorem AW.bind_def (x : AW α) (f : α → AW β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem AW.map_def (x : AW α) (f : α → β) : f <$> x = ⟨x.c, f x.v⟩ := id rfl
@[simp] theorem AW.attach_def (x : AW α) : MonadAttach.attach x = ⟨x.c + 1, ⟨x.v, rfl⟩⟩ := id rfl
@[simp] theorem AW.attachLift_op (x : AW α) :
    (PostconditionT.attachLift x).operation = ⟨x.c + 1, ⟨x.v, rfl⟩⟩ := id rfl

instance : LawfulMonad AW := LawfulMonad.mk' _ (fun _ => rfl)
  (fun _ _ => by simp [bind, pure]) (fun _ _ _ => by simp [bind, Int.add_assoc])
  (bind_pure_comp := fun _ _ => by simp [bind, pure, Functor.map])

instance : Monad ZW where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c, f x.v⟩
instance : MonadAttach ZW where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c + (if x.c = 0 then 1 else 0), ⟨x.v, rfl⟩⟩
@[simp] theorem ZW.pure_def (a : α) : (pure a : ZW α) = ⟨0, a⟩ := id rfl
@[simp] theorem ZW.bind_def (x : ZW α) (f : α → ZW β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem ZW.map_def (x : ZW α) (f : α → β) : f <$> x = ⟨x.c, f x.v⟩ := id rfl
@[simp] theorem ZW.attach_def (x : ZW α) : MonadAttach.attach x = ⟨x.c + (if x.c = 0 then 1 else 0), ⟨x.v, rfl⟩⟩ := id rfl
@[simp] theorem ZW.attachLift_op (x : ZW α) :
    (PostconditionT.attachLift x).operation = ⟨x.c + (if x.c = 0 then 1 else 0), ⟨x.v, rfl⟩⟩ := id rfl

instance : LawfulMonad ZW := LawfulMonad.mk' _ (fun _ => rfl)
  (fun _ _ => by simp [bind, pure]) (fun _ _ _ => by simp [bind, Int.add_assoc])
  (bind_pure_comp := fun _ _ => by simp [bind, pure, Functor.map])

instance : Monad NL where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c, f x.v⟩
instance : MonadAttach NL where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c, ⟨x.v, rfl⟩⟩
@[simp] theorem NL.pure_def (a : α) : (pure a : NL α) = ⟨0, a⟩ := id rfl
@[simp] theorem NL.bind_def (x : NL α) (f : α → NL β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem NL.map_def (x : NL α) (f : α → β) : f <$> x = ⟨x.c, f x.v⟩ := id rfl
@[simp] theorem NL.attach_def (x : NL α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl
@[simp] theorem NL.attachLift_op (x : NL α) :
    (PostconditionT.attachLift x).operation = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl

instance : LawfulMonad NL := LawfulMonad.mk' _ (fun _ => rfl)
  (fun _ _ => by simp [bind, pure]) (fun _ _ _ => by simp [bind, Int.add_assoc])
  (bind_pure_comp := fun _ _ => by simp [bind, pure, Functor.map])

instance : WeaklyLawfulMonadAttach NL := ⟨by intro _ x; simp [Functor.map, MonadAttach.attach]⟩

noncomputable instance : Monad NB where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c + (if x.c = 0 ∧ (f x.v).c ≠ 0 then ntv α else 0), (f x.v).v⟩
  map {α β} f x := ⟨x.c, f x.v⟩
noncomputable instance : MonadAttach NB where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c, ⟨x.v, rfl⟩⟩
@[simp] theorem NB.pure_def (a : α) : (pure a : NB α) = ⟨0, a⟩ := id rfl
@[simp] theorem NB.bind_def (x : NB α) (f : α → NB β) : x >>= f = ⟨x.c + (f x.v).c + (if x.c = 0 ∧ (f x.v).c ≠ 0 then ntv α else 0), (f x.v).v⟩ := id rfl
@[simp] theorem NB.map_def (x : NB α) (f : α → β) : f <$> x = ⟨x.c, f x.v⟩ := id rfl
@[simp] theorem NB.attach_def (x : NB α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl
@[simp] theorem NB.attachLift_op (x : NB α) :
    (PostconditionT.attachLift x).operation = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl

instance : WeaklyLawfulMonadAttach NB := ⟨by intro _ x; simp [Functor.map, MonadAttach.attach]⟩

noncomputable instance : Monad CA where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c, f x.v⟩
noncomputable instance : MonadAttach CA where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c + ntv α, ⟨x.v, rfl⟩⟩
@[simp] theorem CA.pure_def (a : α) : (pure a : CA α) = ⟨0, a⟩ := id rfl
@[simp] theorem CA.bind_def (x : CA α) (f : α → CA β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem CA.map_def (x : CA α) (f : α → β) : f <$> x = ⟨x.c, f x.v⟩ := id rfl
@[simp] theorem CA.attach_def (x : CA α) : MonadAttach.attach x = ⟨x.c + ntv α, ⟨x.v, rfl⟩⟩ := id rfl
@[simp] theorem CA.attachLift_op (x : CA α) :
    (PostconditionT.attachLift x).operation = ⟨x.c + ntv α, ⟨x.v, rfl⟩⟩ := id rfl

instance : LawfulMonad CA := LawfulMonad.mk' _ (fun _ => rfl)
  (fun _ _ => by simp [bind, pure]) (fun _ _ _ => by simp [bind, Int.add_assoc])
  (bind_pure_comp := fun _ _ => by simp [bind, pure, Functor.map])

noncomputable instance : Monad CM where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c + ntv β, f x.v⟩
noncomputable instance : MonadAttach CM where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c - ntv α, ⟨x.v, rfl⟩⟩
@[simp] theorem CM.pure_def (a : α) : (pure a : CM α) = ⟨0, a⟩ := id rfl
@[simp] theorem CM.bind_def (x : CM α) (f : α → CM β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem CM.map_def (x : CM α) (f : α → β) : f <$> x = ⟨x.c + ntv β, f x.v⟩ := id rfl
@[simp] theorem CM.attach_def (x : CM α) : MonadAttach.attach x = ⟨x.c - ntv α, ⟨x.v, rfl⟩⟩ := id rfl
@[simp] theorem CM.attachLift_op (x : CM α) :
    (PostconditionT.attachLift x).operation = ⟨x.c - ntv α, ⟨x.v, rfl⟩⟩ := id rfl

instance : WeaklyLawfulMonadAttach CM := ⟨by intro _ x; simp [Functor.map, MonadAttach.attach]⟩

/-! Lifts -/

instance : LawfulMonadLiftT Id MW := ⟨fun _ => rfl, fun _ _ => by simp [monadLift, MonadLiftT.monadLift]⟩

instance : LawfulMonadLiftT Id HW := ⟨fun _ => rfl, fun _ _ => by simp [monadLift, MonadLiftT.monadLift]⟩

instance : LawfulMonadLiftT Id CM := ⟨fun _ => rfl, fun _ _ => by simp [monadLift, MonadLiftT.monadLift]⟩

instance : MonadLift LW LW2 := ⟨fun x => ⟨x.c, x.v⟩⟩
@[simp] theorem lift_LW_LW2 (x : LW α) : (monadLift x : LW2 α) = ⟨x.c, x.v⟩ := rfl
@[simp] theorem liftL_LW_LW2 (x : LW α) : (MonadLift.monadLift x : LW2 α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLiftT LW LW2 := ⟨fun _ => rfl, fun _ _ => rfl⟩

instance : MonadLift LW MW := ⟨fun x => ⟨x.c, x.v⟩⟩
@[simp] theorem lift_LW_MW (x : LW α) : (monadLift x : MW α) = ⟨x.c, x.v⟩ := rfl
@[simp] theorem liftL_LW_MW (x : LW α) : (MonadLift.monadLift x : MW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLiftT LW MW := ⟨fun _ => rfl, fun _ _ => rfl⟩

instance : MonadLift LW HW := ⟨fun x => ⟨x.c, x.v⟩⟩
@[simp] theorem lift_LW_HW (x : LW α) : (monadLift x : HW α) = ⟨x.c, x.v⟩ := rfl
@[simp] theorem liftL_LW_HW (x : LW α) : (MonadLift.monadLift x : HW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLiftT LW HW := ⟨fun _ => rfl, fun _ _ => rfl⟩

instance : MonadLift LW AW := ⟨fun x => ⟨x.c, x.v⟩⟩
@[simp] theorem lift_LW_AW (x : LW α) : (monadLift x : AW α) = ⟨x.c, x.v⟩ := rfl
@[simp] theorem liftL_LW_AW (x : LW α) : (MonadLift.monadLift x : AW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLiftT LW AW := ⟨fun _ => rfl, fun _ _ => rfl⟩

instance : MonadLift LW ZW := ⟨fun x => ⟨x.c, x.v⟩⟩
@[simp] theorem lift_LW_ZW (x : LW α) : (monadLift x : ZW α) = ⟨x.c, x.v⟩ := rfl
@[simp] theorem liftL_LW_ZW (x : LW α) : (MonadLift.monadLift x : ZW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLiftT LW ZW := ⟨fun _ => rfl, fun _ _ => rfl⟩

instance : MonadLift LW CA := ⟨fun x => ⟨x.c, x.v⟩⟩
@[simp] theorem lift_LW_CA (x : LW α) : (monadLift x : CA α) = ⟨x.c, x.v⟩ := rfl
@[simp] theorem liftL_LW_CA (x : LW α) : (MonadLift.monadLift x : CA α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLiftT LW CA := ⟨fun _ => rfl, fun _ _ => rfl⟩

instance : MonadLift LW CM := ⟨fun x => ⟨x.c, x.v⟩⟩
@[simp] theorem lift_LW_CM (x : LW α) : (monadLift x : CM α) = ⟨x.c, x.v⟩ := rfl
@[simp] theorem liftL_LW_CM (x : LW α) : (MonadLift.monadLift x : CM α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLiftT LW CM := ⟨fun _ => rfl, fun _ _ => rfl⟩

instance : MonadLift MW LW := ⟨fun x => ⟨x.c, x.v⟩⟩
@[simp] theorem lift_MW_LW (x : MW α) : (monadLift x : LW α) = ⟨x.c, x.v⟩ := rfl
@[simp] theorem liftL_MW_LW (x : MW α) : (MonadLift.monadLift x : LW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLiftT MW LW := ⟨fun _ => rfl, fun _ _ => rfl⟩

instance : MonadLift CM LW := ⟨fun x => ⟨x.c, x.v⟩⟩
@[simp] theorem lift_CM_LW (x : CM α) : (monadLift x : LW α) = ⟨x.c, x.v⟩ := rfl
@[simp] theorem liftL_CM_LW (x : CM α) : (MonadLift.monadLift x : LW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLiftT CM LW := ⟨fun _ => rfl, fun _ _ => rfl⟩

instance : MonadLift HW LW := ⟨fun x => ⟨x.c, x.v⟩⟩
@[simp] theorem lift_HW_LW (x : HW α) : (monadLift x : LW α) = ⟨x.c, x.v⟩ := rfl
@[simp] theorem liftL_HW_LW (x : HW α) : (MonadLift.monadLift x : LW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLiftT HW LW := ⟨fun _ => rfl, fun _ _ => rfl⟩

instance : MonadLift AW LW := ⟨fun x => ⟨x.c, x.v⟩⟩
@[simp] theorem lift_AW_LW (x : AW α) : (monadLift x : LW α) = ⟨x.c, x.v⟩ := rfl
@[simp] theorem liftL_AW_LW (x : AW α) : (MonadLift.monadLift x : LW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLiftT AW LW := ⟨fun _ => rfl, fun _ _ => rfl⟩

instance : MonadLift MW (ULiftT LW) := ⟨fun x => (⟨x.c, ULift.up x.v⟩ : LW (ULift _))⟩
@[simp] theorem lift_MW_ULW (x : MW α) : (monadLift x : ULiftT LW α) = (⟨x.c, ULift.up x.v⟩ : LW (ULift α)) := rfl
@[simp] theorem liftL_MW_ULW (x : MW α) : (MonadLift.monadLift x : ULiftT LW α) = (⟨x.c, ULift.up x.v⟩ : LW (ULift α)) := rfl
instance : LawfulMonadLiftT MW (ULiftT LW) := ⟨fun _ => rfl, fun _ _ => rfl⟩

instance : MonadLift LW (ULiftT MW) := ⟨fun x => (⟨x.c, ULift.up x.v⟩ : MW (ULift _))⟩
@[simp] theorem lift_LW_UMW (x : LW α) : (monadLift x : ULiftT MW α) = (⟨x.c, ULift.up x.v⟩ : MW (ULift α)) := rfl
@[simp] theorem liftL_LW_UMW (x : LW α) : (MonadLift.monadLift x : ULiftT MW α) = (⟨x.c, ULift.up x.v⟩ : MW (ULift α)) := rfl
instance : LawfulMonadLiftT LW (ULiftT MW) := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- The forgetful lift `BW → ULiftT LW` (lawful: the values are bound as in a lawful monad). -/
instance : MonadLift BW (ULiftT LW) := ⟨fun x => (⟨0, ULift.up x.v⟩ : LW (ULift _))⟩
@[simp] theorem lift_BW_ULW (x : BW α) : (monadLift x : ULiftT LW α) = (⟨0, ULift.up x.v⟩ : LW (ULift α)) := id rfl
@[simp] theorem liftL_BW_ULW (x : BW α) : (MonadLift.monadLift x : ULiftT LW α) = (⟨0, ULift.up x.v⟩ : LW (ULift α)) := id rfl
instance : LawfulMonadLiftT BW (ULiftT LW) := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- The ticking lift `LW → ULiftT TW` (`monadLift_pure` fails). -/
instance : MonadLift LW (ULiftT TW) := ⟨fun x => (⟨x.c + 1, ULift.up x.v⟩ : TW (ULift _))⟩
@[simp] theorem lift_LW_UTW (x : LW α) : (monadLift x : ULiftT TW α) = (⟨x.c + 1, ULift.up x.v⟩ : TW (ULift α)) := rfl
@[simp] theorem liftL_LW_UTW (x : LW α) : (MonadLift.monadLift x : ULiftT TW α) = (⟨x.c + 1, ULift.up x.v⟩ : TW (ULift α)) := rfl

/-- The lift `LW → NL` adding `ntv α` (classical; not natural in `α`, `monadLift_bind` fails). -/
noncomputable instance : MonadLift LW NL := ⟨fun {α} x => ⟨x.c + ntv α, x.v⟩⟩
@[simp] theorem lift_LW_NL (x : LW α) : (monadLift x : NL α) = ⟨x.c + ntv α, x.v⟩ := id rfl
@[simp] theorem liftL_LW_NL (x : LW α) : (MonadLift.monadLift x : NL α) = ⟨x.c + ntv α, x.v⟩ := id rfl
instance : LawfulMonadLiftT Id NB := ⟨fun _ => rfl, fun x f => by
  simp only [monadLift, MonadLiftT.monadLift, bind, pure, Id.run]; simp⟩
/-- The forgetful lift `LW → NB` (count 0; lawful since `NB` binds count-0 actions lawfully). -/
instance : MonadLift LW NB := ⟨fun x => ⟨0, x.v⟩⟩
@[simp] theorem lift_LW_NB (x : LW α) : (monadLift x : NB α) = ⟨0, x.v⟩ := id rfl
@[simp] theorem liftL_LW_NB (x : LW α) : (MonadLift.monadLift x : NB α) = ⟨0, x.v⟩ := id rfl
instance : LawfulMonadLiftT LW NB := ⟨fun _ => rfl, fun x f => by
  simp only [monadLift, MonadLiftT.monadLift, MonadLift.monadLift, bind]; simp⟩

/-- The ticking lift `LW → TW` (`monadLift_pure` fails). -/
instance : MonadLift LW TW := ⟨fun x => ⟨x.c + 1, x.v⟩⟩
@[simp] theorem lift_LW_TW (x : LW α) : (monadLift x : TW α) = ⟨x.c + 1, x.v⟩ := rfl
@[simp] theorem liftL_LW_TW (x : LW α) : (MonadLift.monadLift x : TW α) = ⟨x.c + 1, x.v⟩ := rfl


@[simp] theorem liftId_def {m : Type w → Type w'} [Pure m] (x : Id α) : (monadLift x : m α) = pure x.run := rfl
@[simp] theorem liftM_eq {m n : Type w → Type w'} [MonadLiftT m n] (x : m α) : (liftM x : n α) = monadLift x := rfl

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

theorem revgo_eq' {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} {acc : List β} :
    IterM.toListRev.go it acc = (do
      match (← it.step).inflate with
      | .yield it' out h => IterM.toListRev.go it' (out :: acc)
      | .skip it' h => IterM.toListRev.go it' acc
      | .done _ => return acc) := by
  rw [IterM.toListRev.go, WellFounded.extrinsicFix₂_eq_apply]
  · apply bind_congr; intro step
    generalize step.inflate = s
    rcases s with ⟨_ | _ | _, _⟩ <;> rfl
  · exact InvImage.wf _ WellFoundedRelation.wf

theorem forIn'_eq' {α β : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] {n : Type x → Type x'} [Monad n]
    {lift : ∀ γ δ, (γ → n δ) → m γ → n δ} {γ : Type x}
    {it : IterM (α := α) m β} {init : γ}
    {P hP}
    {PlausibleForInStep : β → γ → ForInStep γ → Prop}
    {f : (b : β) → P b → (c : γ) → n (Subtype (PlausibleForInStep b c))} :
    IterM.DefaultConsumers.forIn' lift γ PlausibleForInStep it init P hP f =
      (lift _ _ · it.step) (fun s =>
          match s.inflate with
          | .yield it' out h => do
            match ← f out (hP _ <| .direct ⟨_, h⟩) init with
            | ⟨.yield c, _⟩ =>
              IterM.DefaultConsumers.forIn' lift _ PlausibleForInStep it' c P
                (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
            | ⟨.done c, _⟩ => return c
          | .skip it' h =>
            IterM.DefaultConsumers.forIn' lift _ PlausibleForInStep it' init P
              (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
          | .done _ => return init) := by
  haveI : Nonempty γ := ⟨init⟩
  rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply]
  · congr; ext step
    cases step.inflate using PlausibleIterStep.casesOn
    · simp only
      apply bind_congr; intro step
      split <;> simp [IterM.DefaultConsumers.forIn']
    · simp [IterM.DefaultConsumers.forIn']
    · simp
  · apply InvImage.wf
    exact IteratorLoop.wellFounded_of_finite


theorem step_nil {α : Type w} {m : Type w → Type w'} [Pure m] :
    (⟨⟨[]⟩⟩ : IterM (α := ListIterator α) m α).step = pure (.deflate ⟨.done, rfl⟩) := rfl
theorem step_cons {α : Type w} {m : Type w → Type w'} [Pure m] {x : α} {xs : List α} :
    (⟨⟨x :: xs⟩⟩ : IterM (α := ListIterator α) m α).step = pure (.deflate ⟨.yield ⟨⟨xs⟩⟩ x, rfl⟩) := rfl

theorem step_iterM_nil {α : Type w} {m : Type w → Type w'} [Pure m] :
    ([].iterM m : IterM (α := ListIterator α) m α).step = pure (.deflate ⟨.done, rfl⟩) := rfl
theorem step_iterM_cons {α : Type w} {m : Type w → Type w'} [Pure m] {x : α} {xs : List α} :
    ((x :: xs).iterM m).step = pure (.deflate ⟨.yield (xs.iterM m) x, rfl⟩) := rfl

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

@[simp] theorem pc_lift_op {m : Type w → Type w'} {n : Type w → Type w''} [MonadLift m n] (x : PostconditionT m α) :
    (monadLift x : PostconditionT n α).operation = MonadLift.monadLift x.operation := rfl

@[simp] theorem pc_liftL_op {m : Type w → Type w'} {n : Type w → Type w''} [MonadLift m n] (x : PostconditionT m α) :
    (MonadLift.monadLift x : PostconditionT n α).operation = MonadLift.monadLift x.operation := rfl

theorem liftT_trans {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [MonadLift n o] [MonadLiftT m n] (x : m α) :
    (@monadLift m o (@instMonadLiftTOfMonadLift m n o _ _) α x) = MonadLift.monadLift (monadLift x : n α) := rfl

/-- `simp` must not rewrite the function argument of an iterator combinator: it also occurs in the
iterator's type, which `simp` leaves alone. -/
@[congr] theorem mwp_congr {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Monad n]
    [MonadLiftT m n] [Iterator α m β] {f : β → PostconditionT n γ} {it it' : IterM (α := α) m β}
    (h : it = it') : it.mapWithPostcondition f = it'.mapWithPostcondition f := h ▸ rfl
@[congr] theorem fmwp_congr {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [MonadLiftT m n] [Iterator α m β] {f : β → PostconditionT n (Option γ)} {it it' : IterM (α := α) m β}
    (h : it = it') : it.filterMapWithPostcondition f = it'.filterMapWithPostcondition f := h ▸ rfl

@[congr] theorem mapM_congr {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Iterator α m β]
    [Monad n] [MonadAttach n] [MonadLiftT m n] {f : β → n γ} {it it' : IterM (α := α) m β}
    (h : it = it') : it.mapM f = it'.mapM f := h ▸ rfl
@[congr] theorem filterMapM_congr {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Iterator α m β]
    [Monad n] [MonadAttach n] [MonadLiftT m n] {f : β → n (Option γ)} {it it' : IterM (α := α) m β}
    (h : it = it') : it.filterMapM f = it'.filterMapM f := h ▸ rfl
@[congr] theorem map_congr {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β] [Monad m]
    {f : β → γ} {it it' : IterM (α := α) m β} (h : it = it') : it.map f = it'.map f := h ▸ rfl
@[congr] theorem filterMap_congr {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β] [Monad m]
    {f : β → Option γ} {it it' : IterM (α := α) m β} (h : it = it') : it.filterMap f = it'.filterMap f := h ▸ rfl
@[congr] theorem filter_congr {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Monad m]
    {f : β → Bool} {it it' : IterM (α := α) m β} (h : it = it') : it.filter f = it'.filter f := h ▸ rfl
@[congr] theorem flatMap_congr {α β α₂ γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [Iterator α₂ m γ] {f : β → IterM (α := α₂) m γ} {it it' : IterM (α := α) m β} (h : it = it') :
    it.flatMap f = it'.flatMap f := h ▸ rfl
@[congr] theorem flatMapM_congr {α β α₂ γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] {f : β → m (IterM (α := α₂) m γ)} {it it' : IterM (α := α) m β}
    (h : it = it') : it.flatMapM f = it'.flatMapM f := h ▸ rfl
@[congr] theorem flatMapAfter_congr {α β α₂ γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [Iterator α₂ m γ] {f : β → IterM (α := α₂) m γ} {it it' : IterM (α := α) m β} {it₂ : Option (IterM (α := α₂) m γ)}
    (h : it = it') : it.flatMapAfter f it₂ = it'.flatMapAfter f it₂ := h ▸ rfl
@[congr] theorem flatMapAfterM_congr {α β α₂ γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] {f : β → m (IterM (α := α₂) m γ)} {it it' : IterM (α := α) m β}
    {it₂ : Option (IterM (α := α₂) m γ)} (h : it = it') : it.flatMapAfterM f it₂ = it'.flatMapAfterM f it₂ := h ▸ rfl

/-! Unfolding lemmas for the combinators, as non-`rfl` theorems so that `dsimp` does not apply them
inside the iterators' types. -/
theorem mapM_eq {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Iterator α m β]
    [Monad n] [MonadAttach n] [MonadLiftT m n] {f : β → n γ} {it : IterM (α := α) m β} :
    it.mapM f = it.mapWithPostcondition (fun b => PostconditionT.attachLift (f b)) := id rfl
theorem filterMapM_eq {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Iterator α m β]
    [Monad n] [MonadAttach n] [MonadLiftT m n] {f : β → n (Option γ)} {it : IterM (α := α) m β} :
    it.filterMapM f = it.filterMapWithPostcondition (fun b => PostconditionT.attachLift (f b)) := id rfl
theorem map_eq {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β] [Monad m]
    {f : β → γ} {it : IterM (α := α) m β} : it.map f = it.mapWithPostcondition (fun b => pure (f b)) := id rfl
theorem filterMap_eq {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β] [Monad m]
    {f : β → Option γ} {it : IterM (α := α) m β} :
    it.filterMap f = it.filterMapWithPostcondition (fun b => pure (f b)) := id rfl
theorem filter_eq {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Monad m]
    {f : β → Bool} {it : IterM (α := α) m β} :
    it.filter f = it.filterMap (fun b => if f b then some b else none) := id rfl
theorem flatMap_eq {α β α₂ γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [Iterator α₂ m γ] {f : β → IterM (α := α₂) m γ} {it : IterM (α := α) m β} :
    it.flatMap f = (flattenAfterP%) (it.map f) none := id rfl
theorem flatMapM_eq {α β α₂ γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] {f : β → m (IterM (α := α₂) m γ)} {it : IterM (α := α) m β} :
    it.flatMapM f = (flattenAfterP%) (it.mapM f) none := id rfl
theorem flatMapAfter_eq {α β α₂ γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [Iterator α₂ m γ] {f : β → IterM (α := α₂) m γ} {it : IterM (α := α) m β} {it₂ : Option (IterM (α := α₂) m γ)} :
    it.flatMapAfter f it₂ = (flattenAfterP%) (it.map f) it₂ := id rfl
theorem flatMapAfterM_eq {α β α₂ γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] {f : β → m (IterM (α := α₂) m γ)} {it : IterM (α := α) m β}
    {it₂ : Option (IterM (α := α₂) m γ)} : it.flatMapAfterM f it₂ = (flattenAfterP%) (it.mapM f) it₂ := id rfl

/-- The image of an `attach`ed `CM` action under `PostconditionT.map` is a subsingleton. -/
@[simp] theorem ntv_map_attach_CM {α β : Type} (y : CM α) (g : α → β) :
    ntv (Subtype (PostconditionT.map g (PostconditionT.attachLift y)).Property) = 0 := by
  apply ntv_of_sub
  rintro ⟨b₁, ⟨a₁, h₁⟩, rfl⟩ ⟨b₂, ⟨a₂, h₂⟩, rfl⟩
  apply Subtype.ext
  change g a₁ = g a₂
  change a₁ = y.v at h₁
  change a₂ = y.v at h₂
  rw [h₁, h₂]

theorem pc_pure_op {m : Type w → Type w'} [Monad m] (a : α) :
    (pure a : PostconditionT m α).operation = pure ⟨a, rfl⟩ := rfl

/-! ## A two-way branching iterator and non-natural models -/

/-- State of an iterator over `Bool` that, from state 0, may plausibly yield either `false` or `true`
(and actually yields `false`), then stops. Its step type at state 0 has two elements, while the step
type of any `map` with a constant function has one. -/
structure TwoIt : Type where
  s : Nat

instance [Pure m] : Iterator TwoIt m Bool where
  IsPlausibleStep it step := (it.internalState.s = 0 ∧
      (step = .yield ⟨⟨1⟩⟩ false ∨ step = .yield ⟨⟨1⟩⟩ true)) ∨ (it.internalState.s ≠ 0 ∧ step = .done)
  step it := pure (if h : it.internalState.s = 0 then .deflate ⟨.yield ⟨⟨1⟩⟩ false, Or.inl ⟨h, Or.inl rfl⟩⟩
    else .deflate ⟨.done, Or.inr ⟨h, rfl⟩⟩)

def TwoIt.finRel [Pure m] : FinitenessRelation TwoIt m where
  Rel := InvImage (· < ·) (fun it : IterM (α := TwoIt) m Bool => if it.internalState.s = 0 then 1 else 0)
  wf := InvImage.wf _ (measure id).wf
  subrelation {it it'} h := by
    obtain ⟨step, hs, hp⟩ := h
    rcases hp with ⟨h0, rfl | rfl⟩ | ⟨_, rfl⟩ <;> simp [IterStep.successor] at hs <;> subst hs <;>
      simp [InvImage, h0]

instance [Pure m] : Finite TwoIt m := Finite.of_finitenessRelation TwoIt.finRel

/-- The iterator at state `k`. -/
abbrev two (m : Type → Type) [Pure m] (k : Nat) : IterM (α := TwoIt) m Bool := ⟨⟨k⟩⟩

theorem step_two0 [Pure m] : (two m 0).step = pure (.deflate ⟨.yield (two m 1) false, Or.inl ⟨rfl, Or.inl rfl⟩⟩) := rfl
theorem step_two1 [Pure m] : (two m 1).step = pure (.deflate ⟨.done, Or.inr ⟨Nat.one_ne_zero, rfl⟩⟩) := rfl

theorem ntv_shrink_sub {X : Type} (h : ∀ a b : X, a = b) : ntv (Shrink X) = 0 :=
  ntv_of_sub fun a b => by rw [← Shrink.inflate_inj]; exact h _ _
theorem ntv_shrink_ne {X : Type} (a b : X) (h : a ≠ b) : ntv (Shrink X) = 1 :=
  ntv_of_ne (.deflate a) (.deflate b) fun e => h (by simpa using congrArg Shrink.inflate e)

@[simp] theorem ntv_two0 [Pure m] : ntv (Shrink (two m 0).Step) = 1 :=
  ntv_shrink_ne ⟨.yield (two m 1) false, Or.inl ⟨rfl, Or.inl rfl⟩⟩
    ⟨.yield (two m 1) true, Or.inl ⟨rfl, Or.inr rfl⟩⟩ (by simp)

@[simp] theorem ntv_two1 [Pure m] : ntv (Shrink (two m 1).Step) = 0 :=
  ntv_shrink_sub fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => by
    apply Subtype.ext
    rcases h₁ with ⟨h, _⟩ | ⟨_, rfl⟩
    · exact absurd h Nat.one_ne_zero
    rcases h₂ with ⟨h, _⟩ | ⟨_, rfl⟩
    · exact absurd h Nat.one_ne_zero
    rfl

/-- The step type of a `mapWithPostcondition` over `two m k` is a subsingleton when all `f b`
return the same single value. -/
theorem sub_mwp_two [Pure m] {n : Type → Type} [Monad n] [MonadLiftT m n] {γ : Type}
    {f : Bool → PostconditionT n γ} (hf : ∀ b b' y y', (f b).Property y → (f b').Property y' → y = y')
    (k : Nat) : ∀ a b : (IterM.mapWithPostcondition f (two m k)).Step, a = b := by
  rintro ⟨s₁, h₁⟩ ⟨s₂, h₂⟩
  apply Subtype.ext
  change Types.FilterMap.PlausibleStep _ _ at h₁ h₂
  cases h₁ with
  | yieldNone hi hp => obtain ⟨_, h⟩ := hp; cases h
  | skip hi => rcases hi with ⟨_, h | h⟩ | ⟨_, h⟩ <;> cases h
  | yieldSome hi hp =>
    obtain ⟨⟨a, ha⟩, e₁⟩ := hp
    cases h₂ with
    | yieldNone hi' hp' => obtain ⟨_, h⟩ := hp'; cases h
    | skip hi' => rcases hi' with ⟨_, h | h⟩ | ⟨_, h⟩ <;> cases h
    | yieldSome hi' hp' =>
      obtain ⟨⟨a', ha'⟩, e₂⟩ := hp'
      cases e₁; cases e₂
      obtain rfl := hf _ _ _ _ ha ha'
      rcases hi with ⟨_, h | h⟩ | ⟨_, h⟩ <;> cases h <;>
      rcases hi' with ⟨_, h | h⟩ | ⟨_, h⟩ <;> cases h <;> rfl
    | done hi' =>
      rcases hi with ⟨h0, _⟩ | ⟨_, h⟩
      · rcases hi' with ⟨h0', _⟩ | ⟨h1, _⟩
        · rcases ‹_ ∨ _› with h | h <;> cases h
        · exact absurd h0 h1
      · cases h
  | done hi =>
    cases h₂ with
    | yieldNone hi' hp' => obtain ⟨_, h⟩ := hp'; cases h
    | skip hi' => rcases hi' with ⟨_, h | h⟩ | ⟨_, h⟩ <;> cases h
    | yieldSome hi' hp' =>
      rcases hi' with ⟨h0, _⟩ | ⟨_, h⟩
      · rcases hi with ⟨_, h | h⟩ | ⟨h1, _⟩
        · cases h
        · cases h
        · exact absurd h0 h1
      · cases h
    | done hi' => rfl

@[simp] theorem ntv_mwp_pure_two [Pure m] {n : Type → Type} [Monad n] [MonadLiftT m n] {γ : Type}
    (c : γ) (k : Nat) :
    ntv (Shrink (IterM.mapWithPostcondition (fun _ => (pure c : PostconditionT n γ)) (two m k)).Step) = 0 :=
  ntv_shrink_sub (sub_mwp_two (fun _ _ y y' (h : c = y) (h' : c = y') => h.symm.trans h') k)

@[simp] theorem ntv_mwp_attach_two [Pure m] [MonadLiftT m LW] {γ : Type} (x : LW γ) (k : Nat) :
    ntv (Shrink (IterM.mapWithPostcondition (fun _ => PostconditionT.attachLift x) (two m k)).Step) = 0 :=
  ntv_shrink_sub (sub_mwp_two (f := fun _ => PostconditionT.attachLift x)
    (fun _ _ y y' (h : y = x.v) (h' : y' = x.v) => h.trans h'.symm) k)

/-- A loop for `TwoIt` in `BW` that agrees with the default loop for every lawful lift-bind function
(so `LawfulIteratorLoop` holds) and returns `init` otherwise (classical). -/
noncomputable instance twoLoopBW : IteratorLoop TwoIt BW BW where
  forIn lift γ Pl it init f :=
    @ite _ (Nonempty (Std.Internal.LawfulMonadLiftBindFunction lift)) (Classical.propDecidable _)
      ((IteratorLoop.defaultImplementation (α := TwoIt) (m := BW) (n := BW)).forIn lift γ Pl it init f)
      (pure init)

instance : LawfulIteratorLoop TwoIt BW BW where
  lawful lift hl γ it init Pl wf f := by
    show @ite _ _ (Classical.propDecidable _) _ _ = _
    rw [if_pos ⟨hl⟩]

/-- `x >>= f` is not a lawful lift-bind function `BW → BW` (`pure a >>= f` counts 1). -/
theorem not_lawful_bind_BW :
    ¬ Nonempty (Std.Internal.LawfulMonadLiftBindFunction (m := BW) (n := BW)
      (fun _ _ f x => monadLift x >>= f)) := by
  rintro ⟨hl⟩
  have := hl.liftBind_pure (fun _ : Unit => (pure () : BW Unit)) ()
  simp [monadLift_self] at this



/-- Evaluate the writer monads, steps and Shrink round trips. -/
syntax "ev" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| ev $[$loc]?) => `(tactic| simp only [LW.pure_def, LW.bind_def, LW.map_def, LW.attach_def, LW.attachLift_op, LW2.pure_def, LW2.bind_def, LW2.map_def, LW2.attach_def, LW2.attachLift_op, TW.pure_def, TW.bind_def, TW.map_def, TW.attach_def, TW.attachLift_op, BW.pure_def, BW.bind_def, BW.map_def, BW.attach_def, BW.attachLift_op, MW.pure_def, MW.bind_def, MW.map_def, MW.attach_def, MW.attachLift_op, HW.pure_def, HW.bind_def, HW.map_def, HW.attach_def, HW.attachLift_op, AW.pure_def, AW.bind_def, AW.map_def, AW.attach_def, AW.attachLift_op, ZW.pure_def, ZW.bind_def, ZW.map_def, ZW.attach_def, ZW.attachLift_op, NL.pure_def, NL.bind_def, NL.map_def, NL.attach_def, NL.attachLift_op, NB.pure_def, NB.bind_def, NB.map_def, NB.attach_def, NB.attachLift_op, CA.pure_def, CA.bind_def, CA.map_def, CA.attach_def, CA.attachLift_op, CM.pure_def, CM.bind_def, CM.map_def, CM.attach_def, CM.attachLift_op,
  lift_LW_LW2, lift_LW_MW, lift_LW_HW, lift_LW_AW, lift_LW_ZW, lift_LW_CA, lift_LW_CM, lift_MW_LW, lift_CM_LW, lift_HW_LW, lift_AW_LW, liftL_LW_LW2, liftL_LW_MW, liftL_LW_HW, liftL_LW_AW, liftL_LW_ZW, liftL_LW_CA, liftL_LW_CM, liftL_MW_LW, liftL_CM_LW, liftL_HW_LW, liftL_AW_LW, lift_LW_TW, liftL_LW_TW, lift_MW_ULW, liftL_MW_ULW, lift_LW_UMW, liftL_LW_UMW, lift_LW_UTW, liftL_LW_UTW, lift_LW_NL, liftL_LW_NL, lift_LW_NB, liftL_LW_NB, lift_BW_ULW, liftL_BW_ULW, liftId_def, liftM_eq, Id.run_pure, Id.run_bind, Id.run_map,
  step_nil, step_cons, step_iterM_nil, step_iterM_cons, step_fmwp, step_mwp, pc_pure_op, pc_lift_op, pc_liftL_op, liftT_trans, PostconditionT.operation_bind',
  IterM.step_take, IterM.step_toTake, step_flattenAfter', IterM.step_uLift, ULiftT.run,
  flatMap_eq, flatMapM_eq, flatMapAfter_eq, flatMapAfterM_eq, map_eq, filterMap_eq, filter_eq, mapM_eq, filterMapM_eq, monadLift_self,
  PostconditionT.operation_map, PostconditionT.run_eq_map,
  Shrink.inflate_deflate, Array.push, List.concat, List.mapM, List.mapM.loop, List.filterMapM,
  List.filterMapM.loop, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
  ntv_map_attach_CM, step_two0, step_two1, ntv_two0, ntv_two1, ntv_mwp_pure_two, ntv_mwp_attach_two, ntv_unit, ntv_bool, ntv_nat, ntv_option_unit, beq_self_eq_true, ↓reduceIte] $[$loc]?)

/-- Unfold the consumers in `h` and evaluate (one unfolding per round). Only `rw` unfolds the
consumers and `go`, so terms inside the iterators' types are never rewritten by `simp`. -/
macro "evh" h:ident : tactic => `(tactic| (
  repeat ((first | rw [go_eq'] at $h:ident | rw [revgo_eq'] at $h:ident | rw [IterM.toList] at $h:ident | rw [IterM.toArray] at $h:ident | rw [IterM.toListRev] at $h:ident | rw [IterM.length_eq_match_step] at $h:ident | rw [forIn'_eq'] at $h:ident); try ev at $h:ident)))


theorem toArray_nil_Id : (([] : List Nat).iterM Id).toArray.run = #[] := by
  simp only [IterM.toArray]; rw [go_eq']; ev
theorem filterMapM_empty_BW (f : Nat → BW (Option Nat)) : Array.filterMapM f #[] = pure #[] := rfl

/-! ## Necessary: computable writer models -/

-- `Std.IterM.toList_mapM_eq_toList_filterMapM`, idx 9 (`LawfulMonad n`): `n = HW` (`map` halves, `attach` doubles), `f b` counts 1, `it = [1, 2]`: `map ∘ attach` keeps the count 1 per element, `attach ∘ map` rounds it to 0.
theorem toList_mapM_eq_toList_filterMapM.h9 : ¬ drop0% Std.IterM.toList_mapM_eq_toList_filterMapM 9 := fun h => by
  have := h (m := Id) (n := HW) (f := fun b : Nat => (⟨1, b⟩ : HW Nat)) (it := [1, 2].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_eq_toListRev_filterMapM`, idx 9 (`LawfulMonad n`): `n = HW` (`map` halves, `attach` doubles), `f b` counts 1, `it = [1, 2]`: `map ∘ attach` keeps the count 1 per element, `attach ∘ map` rounds it to 0.
theorem toListRev_mapM_eq_toListRev_filterMapM.h9 : ¬ drop0% Std.IterM.toListRev_mapM_eq_toListRev_filterMapM 9 := fun h => by
  have := h (m := Id) (n := HW) (f := fun b : Nat => (⟨1, b⟩ : HW Nat)) (it := [1, 2].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_eq_toArray_filterMapM`, idx 9 (`LawfulMonad n`): `n = HW` (`map` halves, `attach` doubles), `f b` counts 1, `it = [1, 2]`: `map ∘ attach` keeps the count 1 per element, `attach ∘ map` rounds it to 0.
theorem toArray_mapM_eq_toArray_filterMapM.h9 : ¬ drop0% Std.IterM.toArray_mapM_eq_toArray_filterMapM 9 := fun h => by
  have := h (m := Id) (n := HW) (f := fun b : Nat => (⟨1, b⟩ : HW Nat)) (it := [1, 2].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_eq_toList_filterMapM`, idx 10 (`WeaklyLawfulMonadAttach n`): `n = CA` (`attach` counts 1 on nontrivial types), `f : Nat → CA Unit`: the left side attaches at `Unit`, the right side at `Option Unit`.
theorem toList_mapM_eq_toList_filterMapM.h10 : ¬ drop0% Std.IterM.toList_mapM_eq_toList_filterMapM 10 := fun h => by
  have := h (m := Id) (n := CA) (f := fun _ : Nat => (⟨0, ()⟩ : CA Unit)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_eq_toListRev_filterMapM`, idx 10 (`WeaklyLawfulMonadAttach n`): `n = CA` (`attach` counts 1 on nontrivial types), `f : Nat → CA Unit`: the left side attaches at `Unit`, the right side at `Option Unit`.
theorem toListRev_mapM_eq_toListRev_filterMapM.h10 : ¬ drop0% Std.IterM.toListRev_mapM_eq_toListRev_filterMapM 10 := fun h => by
  have := h (m := Id) (n := CA) (f := fun _ : Nat => (⟨0, ()⟩ : CA Unit)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_eq_toArray_filterMapM`, idx 10 (`WeaklyLawfulMonadAttach n`): `n = CA` (`attach` counts 1 on nontrivial types), `f : Nat → CA Unit`: the left side attaches at `Unit`, the right side at `Option Unit`.
theorem toArray_mapM_eq_toArray_filterMapM.h10 : ¬ drop0% Std.IterM.toArray_mapM_eq_toArray_filterMapM 10 := fun h => by
  have := h (m := Id) (n := CA) (f := fun _ : Nat => (⟨0, ()⟩ : CA Unit)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_map_eq_toList_mapM`, idx 6 (`LawfulMonad m`): `m = MW` (`map` counts 1, `attach` -1), `it = [1]`: the left side maps once more per element.
theorem toList_map_eq_toList_mapM.h6 : ¬ drop0% Std.IterM.toList_map_eq_toList_mapM 6 := fun h => by
  have := h (m := MW) (f := fun b : Nat => b) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toListRev_map_eq_toListRev_mapM`, idx 6 (`LawfulMonad m`): `m = MW` (`map` counts 1, `attach` -1), `it = [1]`: the left side maps once more per element.
theorem toListRev_map_eq_toListRev_mapM.h6 : ¬ drop0% Std.IterM.toListRev_map_eq_toListRev_mapM 6 := fun h => by
  have := h (m := MW) (f := fun b : Nat => b) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toArray_map_eq_toArray_mapM`, idx 6 (`LawfulMonad m`): `m = MW` (`map` counts 1, `attach` -1), `it = [1]`: the left side maps once more per element.
theorem toArray_map_eq_toArray_mapM.h6 : ¬ drop0% Std.IterM.toArray_map_eq_toArray_mapM 6 := fun h => by
  have := h (m := MW) (f := fun b : Nat => b) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toList_map_eq_toList_mapM`, idx 7 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it = [1]`: only the right side attaches.
theorem toList_map_eq_toList_mapM.h7 : ¬ drop0% Std.IterM.toList_map_eq_toList_mapM 7 := fun h => by
  have := h (m := AW) (f := fun b : Nat => b) (it := [1].iterM AW)
  evh this
  simp at this

-- `Std.IterM.toListRev_map_eq_toListRev_mapM`, idx 7 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it = [1]`: only the right side attaches.
theorem toListRev_map_eq_toListRev_mapM.h7 : ¬ drop0% Std.IterM.toListRev_map_eq_toListRev_mapM 7 := fun h => by
  have := h (m := AW) (f := fun b : Nat => b) (it := [1].iterM AW)
  evh this
  simp at this

-- `Std.IterM.toArray_map_eq_toArray_mapM`, idx 7 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it = [1]`: only the right side attaches.
theorem toArray_map_eq_toArray_mapM.h7 : ¬ drop0% Std.IterM.toArray_map_eq_toArray_mapM 7 := fun h => by
  have := h (m := AW) (f := fun b : Nat => b) (it := [1].iterM AW)
  evh this
  simp at this

-- `Std.IterM.toList_map_eq_toList_filterMapM`, idx 6 (`LawfulMonad m`): `m = MW` (`map` counts 1, `attach` -1), `it = [1]`: the left side maps once more per element.
theorem toList_map_eq_toList_filterMapM.h6 : ¬ drop0% Std.IterM.toList_map_eq_toList_filterMapM 6 := fun h => by
  have := h (m := MW) (f := fun b : Nat => b) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toListRev_map_eq_toListRev_filterMapM`, idx 6 (`LawfulMonad m`): `m = MW` (`map` counts 1, `attach` -1), `it = [1]`: the left side maps once more per element.
theorem toListRev_map_eq_toListRev_filterMapM.h6 : ¬ drop0% Std.IterM.toListRev_map_eq_toListRev_filterMapM 6 := fun h => by
  have := h (m := MW) (f := fun b : Nat => b) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toArray_map_eq_toArray_filterMapM`, idx 6 (`LawfulMonad m`): `m = MW` (`map` counts 1, `attach` -1), `it = [1]`: the left side maps once more per element.
theorem toArray_map_eq_toArray_filterMapM.h6 : ¬ drop0% Std.IterM.toArray_map_eq_toArray_filterMapM 6 := fun h => by
  have := h (m := MW) (f := fun b : Nat => b) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toList_map_eq_toList_filterMapM`, idx 7 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it = [1]`: only the right side attaches.
theorem toList_map_eq_toList_filterMapM.h7 : ¬ drop0% Std.IterM.toList_map_eq_toList_filterMapM 7 := fun h => by
  have := h (m := AW) (f := fun b : Nat => b) (it := [1].iterM AW)
  evh this
  simp at this

-- `Std.IterM.toListRev_map_eq_toListRev_filterMapM`, idx 7 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it = [1]`: only the right side attaches.
theorem toListRev_map_eq_toListRev_filterMapM.h7 : ¬ drop0% Std.IterM.toListRev_map_eq_toListRev_filterMapM 7 := fun h => by
  have := h (m := AW) (f := fun b : Nat => b) (it := [1].iterM AW)
  evh this
  simp at this

-- `Std.IterM.toArray_map_eq_toArray_filterMapM`, idx 7 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it = [1]`: only the right side attaches.
theorem toArray_map_eq_toArray_filterMapM.h7 : ¬ drop0% Std.IterM.toArray_map_eq_toArray_filterMapM 7 := fun h => by
  have := h (m := AW) (f := fun b : Nat => b) (it := [1].iterM AW)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapWithPostcondition`, idx 5 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = []`: the left side binds once, `List.filterMapM [] = pure []` does not.
theorem toList_filterMapWithPostcondition.h5 : ¬ drop0% Std.IterM.toList_filterMapWithPostcondition 5 := fun h => by
  have := h (m := BW) (f := fun b : Nat => (pure (some b) : PostconditionT BW _)) (it := [].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapWithPostcondition`, idx 5 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = []`: the left side binds once, `List.filterMapM [] = pure []` does not.
theorem toListRev_filterMapWithPostcondition.h5 : ¬ drop0% Std.IterM.toListRev_filterMapWithPostcondition 5 := fun h => by
  have := h (m := BW) (f := fun b : Nat => (pure (some b) : PostconditionT BW _)) (it := [].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapWithPostcondition`, idx 5 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = []`: the left side binds once, `List.filterMapM [] = pure []` does not.
theorem toArray_filterMapWithPostcondition.h5 : ¬ drop0% Std.IterM.toArray_filterMapWithPostcondition 5 := fun h => by
  have := h (m := BW) (f := fun b : Nat => (pure (some b) : PostconditionT BW _)) (it := [].iterM Id)
  rw [toArray_nil_Id, filterMapM_empty_BW] at this
  evh this
  simp at this

-- `Std.IterM.toList_mapWithPostcondition`, idx 5 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = []`: the left side binds once, `List.mapM [] = pure []` does not.
theorem toList_mapWithPostcondition.h5 : ¬ drop0% Std.IterM.toList_mapWithPostcondition 5 := fun h => by
  have := h (m := BW) (f := fun b : Nat => (pure b : PostconditionT BW _)) (it := [].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapWithPostcondition`, idx 5 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = []`: the left side binds once, `List.mapM [] = pure []` does not.
theorem toListRev_mapWithPostcondition.h5 : ¬ drop0% Std.IterM.toListRev_mapWithPostcondition 5 := fun h => by
  have := h (m := BW) (f := fun b : Nat => (pure b : PostconditionT BW _)) (it := [].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapWithPostcondition`, idx 5 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = []`: the left side binds once, `List.mapM [] = pure []` does not.
theorem toArray_mapWithPostcondition.h5 : ¬ drop0% Std.IterM.toArray_mapWithPostcondition 5 := fun h => by
  have := h (m := BW) (f := fun b : Nat => (pure b : PostconditionT BW _)) (it := [].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM`, idx 6 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = []`: the left side binds once, the right side is `pure []`.
theorem toList_filterMapM.h6 : ¬ drop0% Std.IterM.toList_filterMapM 6 := fun h => by
  have := h (m := BW) (f := fun b : Nat => (pure (some b) : BW _)) (it := [].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM`, idx 6 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = []`: the left side binds once, the right side is `pure []`.
theorem toListRev_filterMapM.h6 : ¬ drop0% Std.IterM.toListRev_filterMapM 6 := fun h => by
  have := h (m := BW) (f := fun b : Nat => (pure (some b) : BW _)) (it := [].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapM`, idx 6 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = []`: the left side binds once, the right side is `pure []`.
theorem toList_mapM.h6 : ¬ drop0% Std.IterM.toList_mapM 6 := fun h => by
  have := h (m := BW) (f := fun b : Nat => (pure b : BW _)) (it := [].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM`, idx 6 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = []`: the left side binds once, the right side is `pure []`.
theorem toListRev_mapM.h6 : ¬ drop0% Std.IterM.toListRev_mapM 6 := fun h => by
  have := h (m := BW) (f := fun b : Nat => (pure b : BW _)) (it := [].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM`, idx 6 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = []`: the left side binds once, the right side is `pure []`.
theorem toArray_mapM.h6 : ¬ drop0% Std.IterM.toArray_mapM 6 := fun h => by
  have := h (m := BW) (f := fun b : Nat => (pure b : BW _)) (it := [].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM`, idx 7 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it = [1]`: only the left side attaches.
theorem toList_filterMapM.h7 : ¬ drop0% Std.IterM.toList_filterMapM 7 := fun h => by
  have := h (m := AW) (f := fun b : Nat => (pure (some b) : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM`, idx 7 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it = [1]`: only the left side attaches.
theorem toListRev_filterMapM.h7 : ¬ drop0% Std.IterM.toListRev_filterMapM 7 := fun h => by
  have := h (m := AW) (f := fun b : Nat => (pure (some b) : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapM`, idx 7 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it = [1]`: only the left side attaches.
theorem toList_mapM.h7 : ¬ drop0% Std.IterM.toList_mapM 7 := fun h => by
  have := h (m := AW) (f := fun b : Nat => (pure b : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM`, idx 7 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it = [1]`: only the left side attaches.
theorem toListRev_mapM.h7 : ¬ drop0% Std.IterM.toListRev_mapM 7 := fun h => by
  have := h (m := AW) (f := fun b : Nat => (pure b : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM`, idx 7 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it = [1]`: only the left side attaches.
theorem toArray_mapM.h7 : ¬ drop0% Std.IterM.toArray_mapM 7 := fun h => by
  have := h (m := AW) (f := fun b : Nat => (pure b : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMap`, idx 5 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = [1]`: the combinator's steps bind more often than the base iterator's.
theorem toList_filterMap.h5 : ¬ drop0% Std.IterM.toList_filterMap 5 := fun h => by
  have := h (m := BW) (f := fun b : Nat => some b) (it := [1].iterM BW)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMap`, idx 5 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = [1]`: the combinator's steps bind more often than the base iterator's.
theorem toListRev_filterMap.h5 : ¬ drop0% Std.IterM.toListRev_filterMap 5 := fun h => by
  have := h (m := BW) (f := fun b : Nat => some b) (it := [1].iterM BW)
  evh this
  simp at this

-- `Std.IterM.toList_map`, idx 5 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = [1]`: the combinator's steps bind more often than the base iterator's.
theorem toList_map.h5 : ¬ drop0% Std.IterM.toList_map 5 := fun h => by
  have := h (m := BW) (f := fun b : Nat => b) (it := [1].iterM BW)
  evh this
  simp at this

-- `Std.IterM.toListRev_map`, idx 5 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = [1]`: the combinator's steps bind more often than the base iterator's.
theorem toListRev_map.h5 : ¬ drop0% Std.IterM.toListRev_map 5 := fun h => by
  have := h (m := BW) (f := fun b : Nat => b) (it := [1].iterM BW)
  evh this
  simp at this

-- `Std.IterM.toArray_map`, idx 5 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = [1]`: the combinator's steps bind more often than the base iterator's.
theorem toArray_map.h5 : ¬ drop0% Std.IterM.toArray_map 5 := fun h => by
  have := h (m := BW) (f := fun b : Nat => b) (it := [1].iterM BW)
  evh this
  simp at this

-- `Std.IterM.toList_filter`, idx 3 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = [1]`: the combinator's steps bind more often than the base iterator's.
theorem toList_filter.h3 : ¬ drop0% Std.IterM.toList_filter 3 := fun h => by
  have := h (m := BW) (f := fun b : Nat => b == 1) (it := [1].iterM BW)
  evh this
  simp at this

-- `Std.IterM.toListRev_filter`, idx 4 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it = [1]`: the combinator's steps bind more often than the base iterator's.
theorem toListRev_filter.h4 : ¬ drop0% Std.IterM.toListRev_filter 4 := fun h => by
  have := h (m := BW) (f := fun b : Nat => b == 1) (it := [1].iterM BW)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_map`, idx 7 (`LawfulMonad m`): `m = MW` (`map` counts 1), `n = LW`, identity lift: the inner `map` maps in `m` once per element.
theorem toList_filterMapM_map.h7 : ¬ drop0% Std.IterM.toList_filterMapM_map 7 := fun h => by
  have := h (m := MW) (n := LW) (f := fun b : Nat => b) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_map`, idx 7 (`LawfulMonad m`): `m = MW` (`map` counts 1), `n = LW`, identity lift: the inner `map` maps in `m` once per element.
theorem toListRev_filterMapM_map.h7 : ¬ drop0% Std.IterM.toListRev_filterMapM_map 7 := fun h => by
  have := h (m := MW) (n := LW) (f := fun b : Nat => b) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapM_map`, idx 7 (`LawfulMonad m`): `m = MW` (`map` counts 1), `n = LW`, identity lift: the inner `map` maps in `m` once per element.
theorem toArray_filterMapM_map.h7 : ¬ drop0% Std.IterM.toArray_filterMapM_map 7 := fun h => by
  have := h (m := MW) (n := LW) (f := fun b : Nat => b) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_map`, idx 7 (`LawfulMonad m`): `m = MW` (`map` counts 1), `n = LW`, identity lift: the inner `map` maps in `m` once per element.
theorem toList_mapM_map.h7 : ¬ drop0% Std.IterM.toList_mapM_map 7 := fun h => by
  have := h (m := MW) (n := LW) (f := fun b : Nat => b) (g := fun b : Nat => (pure b : LW _)) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_map`, idx 7 (`LawfulMonad m`): `m = MW` (`map` counts 1), `n = LW`, identity lift: the inner `map` maps in `m` once per element.
theorem toListRev_mapM_map.h7 : ¬ drop0% Std.IterM.toListRev_mapM_map 7 := fun h => by
  have := h (m := MW) (n := LW) (f := fun b : Nat => b) (g := fun b : Nat => (pure b : LW _)) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_map`, idx 7 (`LawfulMonad m`): `m = MW` (`map` counts 1), `n = LW`, identity lift: the inner `map` maps in `m` once per element.
theorem toArray_mapM_map.h7 : ¬ drop0% Std.IterM.toArray_mapM_map 7 := fun h => by
  have := h (m := MW) (n := LW) (f := fun b : Nat => b) (g := fun b : Nat => (pure b : LW _)) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toList_map_mapM`, idx 10 (`LawfulMonad n`): `n = MW` (`map` counts 1, `attach` -1), `it = [1]`: the outer `map` maps once more per element.
theorem toList_map_mapM.h10 : ¬ drop0% Std.IterM.toList_map_mapM 10 := fun h => by
  have := h (m := Id) (n := MW) (f := fun b : Nat => (pure b : MW _)) (g := fun b : Nat => b) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_map_mapM`, idx 10 (`LawfulMonad n`): `n = MW` (`map` counts 1, `attach` -1), `it = [1]`: the outer `map` maps once more per element.
theorem toListRev_map_mapM.h10 : ¬ drop0% Std.IterM.toListRev_map_mapM 10 := fun h => by
  have := h (m := Id) (n := MW) (f := fun b : Nat => (pure b : MW _)) (g := fun b : Nat => b) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_map_mapM`, idx 10 (`LawfulMonad n`): `n = MW` (`map` counts 1, `attach` -1), `it = [1]`: the outer `map` maps once more per element.
theorem toArray_map_mapM.h10 : ¬ drop0% Std.IterM.toArray_map_mapM 10 := fun h => by
  have := h (m := Id) (n := MW) (f := fun b : Nat => (pure b : MW _)) (g := fun b : Nat => b) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_map_mapM`, idx 11 (`WeaklyLawfulMonadAttach n`): `n = CA` (`attach` counts 1 on nontrivial types): the left side attaches at `Unit`, the right side at `Bool`.
theorem toList_map_mapM.h11 : ¬ drop0% Std.IterM.toList_map_mapM 11 := fun h => by
  have := h (m := Id) (n := CA) (f := fun _ : Nat => (⟨0, ()⟩ : CA Unit)) (g := fun _ : Unit => true) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_map_mapM`, idx 11 (`WeaklyLawfulMonadAttach n`): `n = CA` (`attach` counts 1 on nontrivial types): the left side attaches at `Unit`, the right side at `Bool`.
theorem toListRev_map_mapM.h11 : ¬ drop0% Std.IterM.toListRev_map_mapM 11 := fun h => by
  have := h (m := Id) (n := CA) (f := fun _ : Nat => (⟨0, ()⟩ : CA Unit)) (g := fun _ : Unit => true) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_map_mapM`, idx 11 (`WeaklyLawfulMonadAttach n`): `n = CA` (`attach` counts 1 on nontrivial types): the left side attaches at `Unit`, the right side at `Bool`.
theorem toArray_map_mapM.h11 : ¬ drop0% Std.IterM.toArray_map_mapM 11 := fun h => by
  have := h (m := Id) (n := CA) (f := fun _ : Nat => (⟨0, ()⟩ : CA Unit)) (g := fun _ : Unit => true) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition`, idx 12 (`LawfulMonad o`): `o = MW` (`map` counts 1), `n = LW`, identity lift: only the right side's `PostconditionT` bind maps in `o`.
theorem toList_filterMapWithPostcondition_filterMapWithPostcondition.h12 : ¬ drop0% Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition 12 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun b : Nat => (pure (some b) : PostconditionT LW _)) (g := fun b : Nat => (pure (some b) : PostconditionT MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapWithPostcondition_filterMapWithPostcondition`, idx 12 (`LawfulMonad o`): `o = MW` (`map` counts 1), `n = LW`, identity lift: only the right side's `PostconditionT` bind maps in `o`.
theorem toListRev_filterMapWithPostcondition_filterMapWithPostcondition.h12 : ¬ drop0% Std.IterM.toListRev_filterMapWithPostcondition_filterMapWithPostcondition 12 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun b : Nat => (pure (some b) : PostconditionT LW _)) (g := fun b : Nat => (pure (some b) : PostconditionT MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapWithPostcondition_filterMapWithPostcondition`, idx 12 (`LawfulMonad o`): `o = MW` (`map` counts 1), `n = LW`, identity lift: only the right side's `PostconditionT` bind maps in `o`.
theorem toArray_filterMapWithPostcondition_filterMapWithPostcondition.h12 : ¬ drop0% Std.IterM.toArray_filterMapWithPostcondition_filterMapWithPostcondition 12 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun b : Nat => (pure (some b) : PostconditionT LW _)) (g := fun b : Nat => (pure (some b) : PostconditionT MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition`, idx 16 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toList_filterMapWithPostcondition_filterMapWithPostcondition.h16 : ¬ drop0% Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition 16 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (some b) : PostconditionT LW _)) (g := fun b : Nat => (pure (some b) : PostconditionT TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapWithPostcondition_filterMapWithPostcondition`, idx 16 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toListRev_filterMapWithPostcondition_filterMapWithPostcondition.h16 : ¬ drop0% Std.IterM.toListRev_filterMapWithPostcondition_filterMapWithPostcondition 16 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (some b) : PostconditionT LW _)) (g := fun b : Nat => (pure (some b) : PostconditionT TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapWithPostcondition_filterMapWithPostcondition`, idx 16 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toArray_filterMapWithPostcondition_filterMapWithPostcondition.h16 : ¬ drop0% Std.IterM.toArray_filterMapWithPostcondition_filterMapWithPostcondition 16 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (some b) : PostconditionT LW _)) (g := fun b : Nat => (pure (some b) : PostconditionT TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapWithPostcondition_mapWithPostcondition`, idx 10 (`LawfulMonad n`): `n = MW` (`map` counts 1), identity lift to `o = LW`: only the inner `mapWithPostcondition` maps in `n`.
theorem toList_mapWithPostcondition_mapWithPostcondition.h10 : ¬ drop0% Std.IterM.toList_mapWithPostcondition_mapWithPostcondition 10 := fun h => by
  have := h (m := Id) (n := MW) (o := LW) (f := fun b : Nat => (pure b : PostconditionT MW _)) (g := fun b : Nat => (pure b : PostconditionT LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapWithPostcondition_mapWithPostcondition`, idx 10 (`LawfulMonad n`): `n = MW` (`map` counts 1), identity lift to `o = LW`: only the inner `mapWithPostcondition` maps in `n`.
theorem toListRev_mapWithPostcondition_mapWithPostcondition.h10 : ¬ drop0% Std.IterM.toListRev_mapWithPostcondition_mapWithPostcondition 10 := fun h => by
  have := h (m := Id) (n := MW) (o := LW) (f := fun b : Nat => (pure b : PostconditionT MW _)) (g := fun b : Nat => (pure b : PostconditionT LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapWithPostcondition_mapWithPostcondition`, idx 10 (`LawfulMonad n`): `n = MW` (`map` counts 1), identity lift to `o = LW`: only the inner `mapWithPostcondition` maps in `n`.
theorem toArray_mapWithPostcondition_mapWithPostcondition.h10 : ¬ drop0% Std.IterM.toArray_mapWithPostcondition_mapWithPostcondition 10 := fun h => by
  have := h (m := Id) (n := MW) (o := LW) (f := fun b : Nat => (pure b : PostconditionT MW _)) (g := fun b : Nat => (pure b : PostconditionT LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapWithPostcondition_mapWithPostcondition`, idx 12 (`LawfulMonad o`): `o = MW` (`map` counts 1), `n = LW`: the right side's `PostconditionT` bind maps in `o` once more.
theorem toList_mapWithPostcondition_mapWithPostcondition.h12 : ¬ drop0% Std.IterM.toList_mapWithPostcondition_mapWithPostcondition 12 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun b : Nat => (pure b : PostconditionT LW _)) (g := fun b : Nat => (pure b : PostconditionT MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapWithPostcondition_mapWithPostcondition`, idx 12 (`LawfulMonad o`): `o = MW` (`map` counts 1), `n = LW`: the right side's `PostconditionT` bind maps in `o` once more.
theorem toListRev_mapWithPostcondition_mapWithPostcondition.h12 : ¬ drop0% Std.IterM.toListRev_mapWithPostcondition_mapWithPostcondition 12 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun b : Nat => (pure b : PostconditionT LW _)) (g := fun b : Nat => (pure b : PostconditionT MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapWithPostcondition_mapWithPostcondition`, idx 12 (`LawfulMonad o`): `o = MW` (`map` counts 1), `n = LW`: the right side's `PostconditionT` bind maps in `o` once more.
theorem toArray_mapWithPostcondition_mapWithPostcondition.h12 : ¬ drop0% Std.IterM.toArray_mapWithPostcondition_mapWithPostcondition 12 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun b : Nat => (pure b : PostconditionT LW _)) (g := fun b : Nat => (pure b : PostconditionT MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapWithPostcondition_mapWithPostcondition`, idx 16 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toList_mapWithPostcondition_mapWithPostcondition.h16 : ¬ drop0% Std.IterM.toList_mapWithPostcondition_mapWithPostcondition 16 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure b : PostconditionT LW _)) (g := fun b : Nat => (pure b : PostconditionT TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapWithPostcondition_mapWithPostcondition`, idx 16 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toListRev_mapWithPostcondition_mapWithPostcondition.h16 : ¬ drop0% Std.IterM.toListRev_mapWithPostcondition_mapWithPostcondition 16 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure b : PostconditionT LW _)) (g := fun b : Nat => (pure b : PostconditionT TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapWithPostcondition_mapWithPostcondition`, idx 16 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toArray_mapWithPostcondition_mapWithPostcondition.h16 : ¬ drop0% Std.IterM.toArray_mapWithPostcondition_mapWithPostcondition 16 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure b : PostconditionT LW _)) (g := fun b : Nat => (pure b : PostconditionT TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_filterMapWithPostcondition`, idx 11 (`LawfulMonad n`): `n = MW` (`map` counts 1), identity lift to `o = LW`: only the right side runs `(f b).run`, a `map` in `n`.
theorem toList_filterMapM_filterMapWithPostcondition.h11 : ¬ drop0% Std.IterM.toList_filterMapM_filterMapWithPostcondition 11 := fun h => by
  have := h (m := Id) (n := MW) (o := LW) (f := fun b : Nat => (pure (some b) : PostconditionT MW _)) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_filterMapWithPostcondition`, idx 11 (`LawfulMonad n`): `n = MW` (`map` counts 1), identity lift to `o = LW`: only the right side runs `(f b).run`, a `map` in `n`.
theorem toListRev_filterMapM_filterMapWithPostcondition.h11 : ¬ drop0% Std.IterM.toListRev_filterMapM_filterMapWithPostcondition 11 := fun h => by
  have := h (m := Id) (n := MW) (o := LW) (f := fun b : Nat => (pure (some b) : PostconditionT MW _)) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapM_filterMapWithPostcondition`, idx 11 (`LawfulMonad n`): `n = MW` (`map` counts 1), identity lift to `o = LW`: only the right side runs `(f b).run`, a `map` in `n`.
theorem toArray_filterMapM_filterMapWithPostcondition.h11 : ¬ drop0% Std.IterM.toArray_filterMapM_filterMapWithPostcondition 11 := fun h => by
  have := h (m := Id) (n := MW) (o := LW) (f := fun b : Nat => (pure (some b) : PostconditionT MW _)) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_filterMapWithPostcondition`, idx 15 (`LawfulMonad o`): `o = MW` (`attach` counts -1), `f` always `none`: only the right side attaches in `o`.
theorem toList_filterMapM_filterMapWithPostcondition.h15 : ¬ drop0% Std.IterM.toList_filterMapM_filterMapWithPostcondition 15 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun _ : Nat => (pure none : PostconditionT LW (Option Nat))) (g := fun b : Nat => (pure (some b) : MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_filterMapWithPostcondition`, idx 15 (`LawfulMonad o`): `o = MW` (`attach` counts -1), `f` always `none`: only the right side attaches in `o`.
theorem toListRev_filterMapM_filterMapWithPostcondition.h15 : ¬ drop0% Std.IterM.toListRev_filterMapM_filterMapWithPostcondition 15 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun _ : Nat => (pure none : PostconditionT LW (Option Nat))) (g := fun b : Nat => (pure (some b) : MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapM_filterMapWithPostcondition`, idx 15 (`LawfulMonad o`): `o = MW` (`attach` counts -1), `f` always `none`: only the right side attaches in `o`.
theorem toArray_filterMapM_filterMapWithPostcondition.h15 : ¬ drop0% Std.IterM.toArray_filterMapM_filterMapWithPostcondition 15 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun _ : Nat => (pure none : PostconditionT LW (Option Nat))) (g := fun b : Nat => (pure (some b) : MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_filterMapWithPostcondition`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = AW` (`attach` counts 1), `f` always `none`: only the right side attaches in `o`.
theorem toList_filterMapM_filterMapWithPostcondition.h16 : ¬ drop0% Std.IterM.toList_filterMapM_filterMapWithPostcondition 16 := fun h => by
  have := h (m := Id) (n := LW) (o := AW) (f := fun _ : Nat => (pure none : PostconditionT LW (Option Nat))) (g := fun b : Nat => (pure (some b) : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_filterMapWithPostcondition`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = AW` (`attach` counts 1), `f` always `none`: only the right side attaches in `o`.
theorem toListRev_filterMapM_filterMapWithPostcondition.h16 : ¬ drop0% Std.IterM.toListRev_filterMapM_filterMapWithPostcondition 16 := fun h => by
  have := h (m := Id) (n := LW) (o := AW) (f := fun _ : Nat => (pure none : PostconditionT LW (Option Nat))) (g := fun b : Nat => (pure (some b) : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapM_filterMapWithPostcondition`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = AW` (`attach` counts 1), `f` always `none`: only the right side attaches in `o`.
theorem toArray_filterMapM_filterMapWithPostcondition.h16 : ¬ drop0% Std.IterM.toArray_filterMapM_filterMapWithPostcondition 16 := fun h => by
  have := h (m := Id) (n := LW) (o := AW) (f := fun _ : Nat => (pure none : PostconditionT LW (Option Nat))) (g := fun b : Nat => (pure (some b) : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_filterMapWithPostcondition`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toList_filterMapM_filterMapWithPostcondition.h20 : ¬ drop0% Std.IterM.toList_filterMapM_filterMapWithPostcondition 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (some b) : PostconditionT LW _)) (g := fun b : Nat => (pure (some b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_filterMapWithPostcondition`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toListRev_filterMapM_filterMapWithPostcondition.h20 : ¬ drop0% Std.IterM.toListRev_filterMapM_filterMapWithPostcondition 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (some b) : PostconditionT LW _)) (g := fun b : Nat => (pure (some b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapM_filterMapWithPostcondition`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toArray_filterMapM_filterMapWithPostcondition.h20 : ¬ drop0% Std.IterM.toArray_filterMapM_filterMapWithPostcondition 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (some b) : PostconditionT LW _)) (g := fun b : Nat => (pure (some b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_filterMapM`, idx 11 (`LawfulMonad n`): `n = MW` (`attach` counts -1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toList_filterMapM_filterMapM.h11 : ¬ drop0% Std.IterM.toList_filterMapM_filterMapM 11 := fun h => by
  have := h (m := Id) (n := MW) (o := LW) (f := fun b : Nat => (pure (some b) : MW _)) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_filterMapM`, idx 11 (`LawfulMonad n`): `n = MW` (`attach` counts -1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toListRev_filterMapM_filterMapM.h11 : ¬ drop0% Std.IterM.toListRev_filterMapM_filterMapM 11 := fun h => by
  have := h (m := Id) (n := MW) (o := LW) (f := fun b : Nat => (pure (some b) : MW _)) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_filterMapM`, idx 12 (`WeaklyLawfulMonadAttach n`): `n = AW` (`attach` counts 1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toList_filterMapM_filterMapM.h12 : ¬ drop0% Std.IterM.toList_filterMapM_filterMapM 12 := fun h => by
  have := h (m := Id) (n := AW) (o := LW) (f := fun b : Nat => (pure (some b) : AW _)) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_filterMapM`, idx 12 (`WeaklyLawfulMonadAttach n`): `n = AW` (`attach` counts 1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toListRev_filterMapM_filterMapM.h12 : ¬ drop0% Std.IterM.toListRev_filterMapM_filterMapM 12 := fun h => by
  have := h (m := Id) (n := AW) (o := LW) (f := fun b : Nat => (pure (some b) : AW _)) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_filterMapM`, idx 15 (`LawfulMonad o`): `o = MW` (`attach` counts -1), `f` always `none`: only the right side attaches in `o`.
theorem toList_filterMapM_filterMapM.h15 : ¬ drop0% Std.IterM.toList_filterMapM_filterMapM 15 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun _ : Nat => (pure none : LW (Option Nat))) (g := fun b : Nat => (pure (some b) : MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_filterMapM`, idx 15 (`LawfulMonad o`): `o = MW` (`attach` counts -1), `f` always `none`: only the right side attaches in `o`.
theorem toListRev_filterMapM_filterMapM.h15 : ¬ drop0% Std.IterM.toListRev_filterMapM_filterMapM 15 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun _ : Nat => (pure none : LW (Option Nat))) (g := fun b : Nat => (pure (some b) : MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_filterMapM`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = AW` (`attach` counts 1), `f` always `none`: only the right side attaches in `o`.
theorem toList_filterMapM_filterMapM.h16 : ¬ drop0% Std.IterM.toList_filterMapM_filterMapM 16 := fun h => by
  have := h (m := Id) (n := LW) (o := AW) (f := fun _ : Nat => (pure none : LW (Option Nat))) (g := fun b : Nat => (pure (some b) : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_filterMapM`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = AW` (`attach` counts 1), `f` always `none`: only the right side attaches in `o`.
theorem toListRev_filterMapM_filterMapM.h16 : ¬ drop0% Std.IterM.toListRev_filterMapM_filterMapM 16 := fun h => by
  have := h (m := Id) (n := LW) (o := AW) (f := fun _ : Nat => (pure none : LW (Option Nat))) (g := fun b : Nat => (pure (some b) : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_filterMapM`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toList_filterMapM_filterMapM.h20 : ¬ drop0% Std.IterM.toList_filterMapM_filterMapM 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (some b) : LW _)) (g := fun b : Nat => (pure (some b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_filterMapM`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toListRev_filterMapM_filterMapM.h20 : ¬ drop0% Std.IterM.toListRev_filterMapM_filterMapM 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (some b) : LW _)) (g := fun b : Nat => (pure (some b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_mapM`, idx 12 (`WeaklyLawfulMonadAttach n`): `n = AW` (`attach` counts 1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toList_filterMapM_mapM.h12 : ¬ drop0% Std.IterM.toList_filterMapM_mapM 12 := fun h => by
  have := h (m := Id) (n := AW) (o := LW) (f := fun b : Nat => (pure (b) : AW _)) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_mapM`, idx 12 (`WeaklyLawfulMonadAttach n`): `n = AW` (`attach` counts 1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toListRev_filterMapM_mapM.h12 : ¬ drop0% Std.IterM.toListRev_filterMapM_mapM 12 := fun h => by
  have := h (m := Id) (n := AW) (o := LW) (f := fun b : Nat => (pure (b) : AW _)) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapM_mapM`, idx 12 (`WeaklyLawfulMonadAttach n`): `n = AW` (`attach` counts 1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toArray_filterMapM_mapM.h12 : ¬ drop0% Std.IterM.toArray_filterMapM_mapM 12 := fun h => by
  have := h (m := Id) (n := AW) (o := LW) (f := fun b : Nat => (pure (b) : AW _)) (g := fun b : Nat => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_mapM`, idx 15 (`LawfulMonad o`): `o = HW` (`attach` doubles, `map` halves), `f`, `g` count 1: the right side also attaches the lifted `f b`.
theorem toList_filterMapM_mapM.h15 : ¬ drop0% Std.IterM.toList_filterMapM_mapM 15 := fun h => by
  have := h (m := Id) (n := LW) (o := HW) (f := fun b : Nat => (⟨1, b⟩ : LW Nat)) (g := fun b : Nat => (⟨1, some b⟩ : HW (Option Nat))) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_mapM`, idx 15 (`LawfulMonad o`): `o = HW` (`attach` doubles, `map` halves), `f`, `g` count 1: the right side also attaches the lifted `f b`.
theorem toListRev_filterMapM_mapM.h15 : ¬ drop0% Std.IterM.toListRev_filterMapM_mapM 15 := fun h => by
  have := h (m := Id) (n := LW) (o := HW) (f := fun b : Nat => (⟨1, b⟩ : LW Nat)) (g := fun b : Nat => (⟨1, some b⟩ : HW (Option Nat))) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapM_mapM`, idx 15 (`LawfulMonad o`): `o = HW` (`attach` doubles, `map` halves), `f`, `g` count 1: the right side also attaches the lifted `f b`.
theorem toArray_filterMapM_mapM.h15 : ¬ drop0% Std.IterM.toArray_filterMapM_mapM 15 := fun h => by
  have := h (m := Id) (n := LW) (o := HW) (f := fun b : Nat => (⟨1, b⟩ : LW Nat)) (g := fun b : Nat => (⟨1, some b⟩ : HW (Option Nat))) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_mapM`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = ZW` (`attach` counts 1 on count-0 actions), `f b` counts 1, `g b` counts 0: the left side attaches `g b`, the right side `f b >>= g`.
theorem toList_filterMapM_mapM.h16 : ¬ drop0% Std.IterM.toList_filterMapM_mapM 16 := fun h => by
  have := h (m := Id) (n := LW) (o := ZW) (f := fun b : Nat => (⟨1, b⟩ : LW Nat)) (g := fun b : Nat => (⟨0, some b⟩ : ZW (Option Nat))) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_mapM`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = ZW` (`attach` counts 1 on count-0 actions), `f b` counts 1, `g b` counts 0: the left side attaches `g b`, the right side `f b >>= g`.
theorem toListRev_filterMapM_mapM.h16 : ¬ drop0% Std.IterM.toListRev_filterMapM_mapM 16 := fun h => by
  have := h (m := Id) (n := LW) (o := ZW) (f := fun b : Nat => (⟨1, b⟩ : LW Nat)) (g := fun b : Nat => (⟨0, some b⟩ : ZW (Option Nat))) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapM_mapM`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = ZW` (`attach` counts 1 on count-0 actions), `f b` counts 1, `g b` counts 0: the left side attaches `g b`, the right side `f b >>= g`.
theorem toArray_filterMapM_mapM.h16 : ¬ drop0% Std.IterM.toArray_filterMapM_mapM 16 := fun h => by
  have := h (m := Id) (n := LW) (o := ZW) (f := fun b : Nat => (⟨1, b⟩ : LW Nat)) (g := fun b : Nat => (⟨0, some b⟩ : ZW (Option Nat))) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_mapM`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toList_filterMapM_mapM.h20 : ¬ drop0% Std.IterM.toList_filterMapM_mapM 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (b) : LW _)) (g := fun b : Nat => (pure (some b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_mapM`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toListRev_filterMapM_mapM.h20 : ¬ drop0% Std.IterM.toListRev_filterMapM_mapM 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (b) : LW _)) (g := fun b : Nat => (pure (some b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapM_mapM`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toArray_filterMapM_mapM.h20 : ¬ drop0% Std.IterM.toArray_filterMapM_mapM 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (b) : LW _)) (g := fun b : Nat => (pure (some b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_filterMapM`, idx 11 (`LawfulMonad n`): `n = MW` (`attach` counts -1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toList_mapM_filterMapM.h11 : ¬ drop0% Std.IterM.toList_mapM_filterMapM 11 := fun h => by
  have := h (m := Id) (n := MW) (o := LW) (f := fun b : Nat => (pure (some b) : MW _)) (g := fun b : Nat => (pure (b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_filterMapM`, idx 11 (`LawfulMonad n`): `n = MW` (`attach` counts -1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toListRev_mapM_filterMapM.h11 : ¬ drop0% Std.IterM.toListRev_mapM_filterMapM 11 := fun h => by
  have := h (m := Id) (n := MW) (o := LW) (f := fun b : Nat => (pure (some b) : MW _)) (g := fun b : Nat => (pure (b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_filterMapM`, idx 11 (`LawfulMonad n`): `n = MW` (`attach` counts -1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toArray_mapM_filterMapM.h11 : ¬ drop0% Std.IterM.toArray_mapM_filterMapM 11 := fun h => by
  have := h (m := Id) (n := MW) (o := LW) (f := fun b : Nat => (pure (some b) : MW _)) (g := fun b : Nat => (pure (b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_filterMapM`, idx 12 (`WeaklyLawfulMonadAttach n`): `n = AW` (`attach` counts 1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toList_mapM_filterMapM.h12 : ¬ drop0% Std.IterM.toList_mapM_filterMapM 12 := fun h => by
  have := h (m := Id) (n := AW) (o := LW) (f := fun b : Nat => (pure (some b) : AW _)) (g := fun b : Nat => (pure (b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_filterMapM`, idx 12 (`WeaklyLawfulMonadAttach n`): `n = AW` (`attach` counts 1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toListRev_mapM_filterMapM.h12 : ¬ drop0% Std.IterM.toListRev_mapM_filterMapM 12 := fun h => by
  have := h (m := Id) (n := AW) (o := LW) (f := fun b : Nat => (pure (some b) : AW _)) (g := fun b : Nat => (pure (b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_filterMapM`, idx 12 (`WeaklyLawfulMonadAttach n`): `n = AW` (`attach` counts 1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toArray_mapM_filterMapM.h12 : ¬ drop0% Std.IterM.toArray_mapM_filterMapM 12 := fun h => by
  have := h (m := Id) (n := AW) (o := LW) (f := fun b : Nat => (pure (some b) : AW _)) (g := fun b : Nat => (pure (b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_filterMapM`, idx 15 (`LawfulMonad o`): `o = MW` (`attach` counts -1), `f` always `none`: only the right side attaches in `o`.
theorem toList_mapM_filterMapM.h15 : ¬ drop0% Std.IterM.toList_mapM_filterMapM 15 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun _ : Nat => (pure none : LW (Option Nat))) (g := fun b : Nat => (pure (b) : MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_filterMapM`, idx 15 (`LawfulMonad o`): `o = MW` (`attach` counts -1), `f` always `none`: only the right side attaches in `o`.
theorem toListRev_mapM_filterMapM.h15 : ¬ drop0% Std.IterM.toListRev_mapM_filterMapM 15 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun _ : Nat => (pure none : LW (Option Nat))) (g := fun b : Nat => (pure (b) : MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_filterMapM`, idx 15 (`LawfulMonad o`): `o = MW` (`attach` counts -1), `f` always `none`: only the right side attaches in `o`.
theorem toArray_mapM_filterMapM.h15 : ¬ drop0% Std.IterM.toArray_mapM_filterMapM 15 := fun h => by
  have := h (m := Id) (n := LW) (o := MW) (f := fun _ : Nat => (pure none : LW (Option Nat))) (g := fun b : Nat => (pure (b) : MW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_filterMapM`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = AW` (`attach` counts 1), `f` always `none`: only the right side attaches in `o`.
theorem toList_mapM_filterMapM.h16 : ¬ drop0% Std.IterM.toList_mapM_filterMapM 16 := fun h => by
  have := h (m := Id) (n := LW) (o := AW) (f := fun _ : Nat => (pure none : LW (Option Nat))) (g := fun b : Nat => (pure (b) : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_filterMapM`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = AW` (`attach` counts 1), `f` always `none`: only the right side attaches in `o`.
theorem toListRev_mapM_filterMapM.h16 : ¬ drop0% Std.IterM.toListRev_mapM_filterMapM 16 := fun h => by
  have := h (m := Id) (n := LW) (o := AW) (f := fun _ : Nat => (pure none : LW (Option Nat))) (g := fun b : Nat => (pure (b) : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_filterMapM`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = AW` (`attach` counts 1), `f` always `none`: only the right side attaches in `o`.
theorem toArray_mapM_filterMapM.h16 : ¬ drop0% Std.IterM.toArray_mapM_filterMapM 16 := fun h => by
  have := h (m := Id) (n := LW) (o := AW) (f := fun _ : Nat => (pure none : LW (Option Nat))) (g := fun b : Nat => (pure (b) : AW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_filterMapM`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toList_mapM_filterMapM.h20 : ¬ drop0% Std.IterM.toList_mapM_filterMapM 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (some b) : LW _)) (g := fun b : Nat => (pure (b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_filterMapM`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toListRev_mapM_filterMapM.h20 : ¬ drop0% Std.IterM.toListRev_mapM_filterMapM 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (some b) : LW _)) (g := fun b : Nat => (pure (b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_filterMapM`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toArray_mapM_filterMapM.h20 : ¬ drop0% Std.IterM.toArray_mapM_filterMapM 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (some b) : LW _)) (g := fun b : Nat => (pure (b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_mapM`, idx 12 (`WeaklyLawfulMonadAttach n`): `n = AW` (`attach` counts 1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toList_mapM_mapM.h12 : ¬ drop0% Std.IterM.toList_mapM_mapM 12 := fun h => by
  have := h (m := Id) (n := AW) (o := LW) (f := fun b : Nat => (pure (b) : AW _)) (g := fun b : Nat => (pure (b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_mapM`, idx 12 (`WeaklyLawfulMonadAttach n`): `n = AW` (`attach` counts 1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toListRev_mapM_mapM.h12 : ¬ drop0% Std.IterM.toListRev_mapM_mapM 12 := fun h => by
  have := h (m := Id) (n := AW) (o := LW) (f := fun b : Nat => (pure (b) : AW _)) (g := fun b : Nat => (pure (b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_mapM`, idx 12 (`WeaklyLawfulMonadAttach n`): `n = AW` (`attach` counts 1), identity lift to `o = LW`: only the left side attaches in `n`.
theorem toArray_mapM_mapM.h12 : ¬ drop0% Std.IterM.toArray_mapM_mapM 12 := fun h => by
  have := h (m := Id) (n := AW) (o := LW) (f := fun b : Nat => (pure (b) : AW _)) (g := fun b : Nat => (pure (b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_mapM`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = ZW` (`attach` counts 1 on count-0 actions), `f b` counts 1, `g b` counts 0: the left side attaches `g b`, the right side `f b >>= g`.
theorem toList_mapM_mapM.h16 : ¬ drop0% Std.IterM.toList_mapM_mapM 16 := fun h => by
  have := h (m := Id) (n := LW) (o := ZW) (f := fun b : Nat => (⟨1, b⟩ : LW Nat)) (g := fun b : Nat => (⟨0, b⟩ : ZW (Nat))) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_mapM`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = ZW` (`attach` counts 1 on count-0 actions), `f b` counts 1, `g b` counts 0: the left side attaches `g b`, the right side `f b >>= g`.
theorem toListRev_mapM_mapM.h16 : ¬ drop0% Std.IterM.toListRev_mapM_mapM 16 := fun h => by
  have := h (m := Id) (n := LW) (o := ZW) (f := fun b : Nat => (⟨1, b⟩ : LW Nat)) (g := fun b : Nat => (⟨0, b⟩ : ZW (Nat))) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_mapM`, idx 16 (`WeaklyLawfulMonadAttach o`): `o = ZW` (`attach` counts 1 on count-0 actions), `f b` counts 1, `g b` counts 0: the left side attaches `g b`, the right side `f b >>= g`.
theorem toArray_mapM_mapM.h16 : ¬ drop0% Std.IterM.toArray_mapM_mapM 16 := fun h => by
  have := h (m := Id) (n := LW) (o := ZW) (f := fun b : Nat => (⟨1, b⟩ : LW Nat)) (g := fun b : Nat => (⟨0, b⟩ : ZW (Nat))) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_mapM`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toList_mapM_mapM.h20 : ¬ drop0% Std.IterM.toList_mapM_mapM 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (b) : LW _)) (g := fun b : Nat => (pure (b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_mapM`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toListRev_mapM_mapM.h20 : ¬ drop0% Std.IterM.toListRev_mapM_mapM 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (b) : LW _)) (g := fun b : Nat => (pure (b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_mapM`, idx 20 (`LawfulMonadLiftT n o`): lift `LW → TW` counts 1 per lift: the right side lifts `f b` separately.
theorem toArray_mapM_mapM.h20 : ¬ drop0% Std.IterM.toArray_mapM_mapM 20 := fun h => by
  have := h (m := Id) (n := LW) (o := TW) (f := fun b : Nat => (pure (b) : LW _)) (g := fun b : Nat => (pure (b) : TW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_mapM`, idx 11 (`LawfulMonad n`): `n = CM` (`map` counts 1 into nontrivial types, `attach` -1 from nontrivial types; classical), identity lift to `o = LW`, `f : Nat → CM Bool`: the inner `mapM` maps the attached `f b : CM Bool` into a subsingleton subtype (count -1), the right side only lifts `f b` (count 0).
theorem toList_filterMapM_mapM.h11 : ¬ drop0% Std.IterM.toList_filterMapM_mapM 11 := fun h => by
  have := h (m := Id) (n := CM) (o := LW) (f := fun _ : Nat => (⟨0, true⟩ : CM Bool)) (g := fun b : Bool => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_mapM`, idx 11 (`LawfulMonad n`): `n = CM` (`map` counts 1 into nontrivial types, `attach` -1 from nontrivial types; classical), identity lift to `o = LW`, `f : Nat → CM Bool`: the inner `mapM` maps the attached `f b : CM Bool` into a subsingleton subtype (count -1), the right side only lifts `f b` (count 0).
theorem toListRev_filterMapM_mapM.h11 : ¬ drop0% Std.IterM.toListRev_filterMapM_mapM 11 := fun h => by
  have := h (m := Id) (n := CM) (o := LW) (f := fun _ : Nat => (⟨0, true⟩ : CM Bool)) (g := fun b : Bool => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapM_mapM`, idx 11 (`LawfulMonad n`): `n = CM` (`map` counts 1 into nontrivial types, `attach` -1 from nontrivial types; classical), identity lift to `o = LW`, `f : Nat → CM Bool`: the inner `mapM` maps the attached `f b : CM Bool` into a subsingleton subtype (count -1), the right side only lifts `f b` (count 0).
theorem toArray_filterMapM_mapM.h11 : ¬ drop0% Std.IterM.toArray_filterMapM_mapM 11 := fun h => by
  have := h (m := Id) (n := CM) (o := LW) (f := fun _ : Nat => (⟨0, true⟩ : CM Bool)) (g := fun b : Bool => (pure (some b) : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_mapM`, idx 11 (`LawfulMonad n`): `n = CM` (`map` counts 1 into nontrivial types, `attach` -1 from nontrivial types; classical), identity lift to `o = LW`, `f : Nat → CM Bool`: the inner `mapM` maps the attached `f b : CM Bool` into a subsingleton subtype (count -1), the right side only lifts `f b` (count 0).
theorem toList_mapM_mapM.h11 : ¬ drop0% Std.IterM.toList_mapM_mapM 11 := fun h => by
  have := h (m := Id) (n := CM) (o := LW) (f := fun _ : Nat => (⟨0, true⟩ : CM Bool)) (g := fun b : Bool => (pure b : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_mapM`, idx 11 (`LawfulMonad n`): `n = CM` (`map` counts 1 into nontrivial types, `attach` -1 from nontrivial types; classical), identity lift to `o = LW`, `f : Nat → CM Bool`: the inner `mapM` maps the attached `f b : CM Bool` into a subsingleton subtype (count -1), the right side only lifts `f b` (count 0).
theorem toListRev_mapM_mapM.h11 : ¬ drop0% Std.IterM.toListRev_mapM_mapM 11 := fun h => by
  have := h (m := Id) (n := CM) (o := LW) (f := fun _ : Nat => (⟨0, true⟩ : CM Bool)) (g := fun b : Bool => (pure b : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_mapM`, idx 11 (`LawfulMonad n`): `n = CM` (`map` counts 1 into nontrivial types, `attach` -1 from nontrivial types; classical), identity lift to `o = LW`, `f : Nat → CM Bool`: the inner `mapM` maps the attached `f b : CM Bool` into a subsingleton subtype (count -1), the right side only lifts `f b` (count 0).
theorem toArray_mapM_mapM.h11 : ¬ drop0% Std.IterM.toArray_mapM_mapM 11 := fun h => by
  have := h (m := Id) (n := CM) (o := LW) (f := fun _ : Nat => (⟨0, true⟩ : CM Bool)) (g := fun b : Bool => (pure b : LW _)) (it := [1].iterM Id)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_map`, idx 13 (`LawfulMonadLiftT m n`): lift `LW → NL` adds `ntv α` (1 iff the lifted action's value type is nontrivial; classical, not natural), `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side lifts the steps of `it.map f`, the right side those of `it`.
theorem toList_filterMapM_map.h13 : ¬ drop0% Std.IterM.toList_filterMapM_map 13 := fun h => by
  have := h (m := LW) (n := NL) (f := fun _ : Bool => ()) (g := fun _ : Unit => (⟨1, some ()⟩ : NL (Option Unit))) (it := two LW 0)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_map`, idx 13 (`LawfulMonadLiftT m n`): lift `LW → NL` adds `ntv α` (1 iff the lifted action's value type is nontrivial; classical, not natural), `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side lifts the steps of `it.map f`, the right side those of `it`.
theorem toListRev_filterMapM_map.h13 : ¬ drop0% Std.IterM.toListRev_filterMapM_map 13 := fun h => by
  have := h (m := LW) (n := NL) (f := fun _ : Bool => ()) (g := fun _ : Unit => (⟨1, some ()⟩ : NL (Option Unit))) (it := two LW 0)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapM_map`, idx 13 (`LawfulMonadLiftT m n`): lift `LW → NL` adds `ntv α` (1 iff the lifted action's value type is nontrivial; classical, not natural), `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side lifts the steps of `it.map f`, the right side those of `it`.
theorem toArray_filterMapM_map.h13 : ¬ drop0% Std.IterM.toArray_filterMapM_map 13 := fun h => by
  have := h (m := LW) (n := NL) (f := fun _ : Bool => ()) (g := fun _ : Unit => (⟨1, some ()⟩ : NL (Option Unit))) (it := two LW 0)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_map`, idx 13 (`LawfulMonadLiftT m n`): lift `LW → NL` adds `ntv α` (1 iff the lifted action's value type is nontrivial; classical, not natural), `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side lifts the steps of `it.map f`, the right side those of `it`.
theorem toList_mapM_map.h13 : ¬ drop0% Std.IterM.toList_mapM_map 13 := fun h => by
  have := h (m := LW) (n := NL) (f := fun _ : Bool => ()) (g := fun _ : Unit => (⟨1, ()⟩ : NL Unit)) (it := two LW 0)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_map`, idx 13 (`LawfulMonadLiftT m n`): lift `LW → NL` adds `ntv α` (1 iff the lifted action's value type is nontrivial; classical, not natural), `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side lifts the steps of `it.map f`, the right side those of `it`.
theorem toListRev_mapM_map.h13 : ¬ drop0% Std.IterM.toListRev_mapM_map 13 := fun h => by
  have := h (m := LW) (n := NL) (f := fun _ : Bool => ()) (g := fun _ : Unit => (⟨1, ()⟩ : NL Unit)) (it := two LW 0)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_map`, idx 13 (`LawfulMonadLiftT m n`): lift `LW → NL` adds `ntv α` (1 iff the lifted action's value type is nontrivial; classical, not natural), `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side lifts the steps of `it.map f`, the right side those of `it`.
theorem toArray_mapM_map.h13 : ¬ drop0% Std.IterM.toArray_mapM_map 13 := fun h => by
  have := h (m := LW) (n := NL) (f := fun _ : Bool => ()) (g := fun _ : Unit => (⟨1, ()⟩ : NL Unit)) (it := two LW 0)
  evh this
  simp at this

-- `Std.IterM.toList_filterMapM_map`, idx 10 (`LawfulMonad n`): `n = NB` (`bind` adds `ntv α` when a count-0 action is followed by a counting one; classical), lift `Id → NB` is `pure`, `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side binds the step of `it.map f` with the counting `g`, the right side the step of `it`.
theorem toList_filterMapM_map.h10 : ¬ drop0% Std.IterM.toList_filterMapM_map 10 := fun h => by
  have := h (m := Id) (n := NB) (f := fun _ : Bool => ()) (g := fun _ : Unit => (⟨1, some ()⟩ : NB (Option Unit))) (it := two Id 0)
  evh this
  simp at this

-- `Std.IterM.toListRev_filterMapM_map`, idx 10 (`LawfulMonad n`): `n = NB` (`bind` adds `ntv α` when a count-0 action is followed by a counting one; classical), lift `Id → NB` is `pure`, `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side binds the step of `it.map f` with the counting `g`, the right side the step of `it`.
theorem toListRev_filterMapM_map.h10 : ¬ drop0% Std.IterM.toListRev_filterMapM_map 10 := fun h => by
  have := h (m := Id) (n := NB) (f := fun _ : Bool => ()) (g := fun _ : Unit => (⟨1, some ()⟩ : NB (Option Unit))) (it := two Id 0)
  evh this
  simp at this

-- `Std.IterM.toArray_filterMapM_map`, idx 10 (`LawfulMonad n`): `n = NB` (`bind` adds `ntv α` when a count-0 action is followed by a counting one; classical), lift `Id → NB` is `pure`, `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side binds the step of `it.map f` with the counting `g`, the right side the step of `it`.
theorem toArray_filterMapM_map.h10 : ¬ drop0% Std.IterM.toArray_filterMapM_map 10 := fun h => by
  have := h (m := Id) (n := NB) (f := fun _ : Bool => ()) (g := fun _ : Unit => (⟨1, some ()⟩ : NB (Option Unit))) (it := two Id 0)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_map`, idx 10 (`LawfulMonad n`): `n = NB` (`bind` adds `ntv α` when a count-0 action is followed by a counting one; classical), lift `Id → NB` is `pure`, `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side binds the step of `it.map f` with the counting `g`, the right side the step of `it`.
theorem toList_mapM_map.h10 : ¬ drop0% Std.IterM.toList_mapM_map 10 := fun h => by
  have := h (m := Id) (n := NB) (f := fun _ : Bool => ()) (g := fun _ : Unit => (⟨1, ()⟩ : NB Unit)) (it := two Id 0)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_map`, idx 10 (`LawfulMonad n`): `n = NB` (`bind` adds `ntv α` when a count-0 action is followed by a counting one; classical), lift `Id → NB` is `pure`, `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side binds the step of `it.map f` with the counting `g`, the right side the step of `it`.
theorem toListRev_mapM_map.h10 : ¬ drop0% Std.IterM.toListRev_mapM_map 10 := fun h => by
  have := h (m := Id) (n := NB) (f := fun _ : Bool => ()) (g := fun _ : Unit => (⟨1, ()⟩ : NB Unit)) (it := two Id 0)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_map`, idx 10 (`LawfulMonad n`): `n = NB` (`bind` adds `ntv α` when a count-0 action is followed by a counting one; classical), lift `Id → NB` is `pure`, `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side binds the step of `it.map f` with the counting `g`, the right side the step of `it`.
theorem toArray_mapM_map.h10 : ¬ drop0% Std.IterM.toArray_mapM_map 10 := fun h => by
  have := h (m := Id) (n := NB) (f := fun _ : Bool => ()) (g := fun _ : Unit => (⟨1, ()⟩ : NB Unit)) (it := two Id 0)
  evh this
  simp at this

-- `Std.IterM.toList_mapM_mapM`, idx 15 (`LawfulMonad o`): `o = NB` (`bind` adds `ntv α` when a count-0 action is followed by a counting one; classical), forgetful lift `LW → NB`, `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side binds the step of `it.mapM f` with the counting `g`, the right side the step of `it`.
theorem toList_mapM_mapM.h15 : ¬ drop0% Std.IterM.toList_mapM_mapM 15 := fun h => by
  have := h (m := Id) (n := LW) (o := NB) (f := fun _ : Bool => (pure () : LW Unit)) (g := fun _ : Unit => (⟨1, ()⟩ : NB Unit)) (it := two Id 0)
  evh this
  simp at this

-- `Std.IterM.toListRev_mapM_mapM`, idx 15 (`LawfulMonad o`): `o = NB` (`bind` adds `ntv α` when a count-0 action is followed by a counting one; classical), forgetful lift `LW → NB`, `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side binds the step of `it.mapM f` with the counting `g`, the right side the step of `it`.
theorem toListRev_mapM_mapM.h15 : ¬ drop0% Std.IterM.toListRev_mapM_mapM 15 := fun h => by
  have := h (m := Id) (n := LW) (o := NB) (f := fun _ : Bool => (pure () : LW Unit)) (g := fun _ : Unit => (⟨1, ()⟩ : NB Unit)) (it := two Id 0)
  evh this
  simp at this

-- `Std.IterM.toArray_mapM_mapM`, idx 15 (`LawfulMonad o`): `o = NB` (`bind` adds `ntv α` when a count-0 action is followed by a counting one; classical), forgetful lift `LW → NB`, `it = two _ 0` (may plausibly yield `false` or `true`), `f` constant: the step type of `it` has two elements, that of `it.map f` (or `it.mapM f`) one: the left side binds the step of `it.mapM f` with the counting `g`, the right side the step of `it`.
theorem toArray_mapM_mapM.h15 : ¬ drop0% Std.IterM.toArray_mapM_mapM 15 := fun h => by
  have := h (m := Id) (n := LW) (o := NB) (f := fun _ : Bool => (pure () : LW Unit)) (g := fun _ : Unit => (⟨1, ()⟩ : NB Unit)) (it := two Id 0)
  evh this
  simp at this

-- `Std.IterM.length_uLift`, idx 11 (`LawfulMonad m`): `m = BW` (`bind` counts 1) with a classical loop `twoLoopBW` for `two` that agrees with the default loop for lawful lift-bind functions (so `LawfulIteratorLoop` holds) and returns `init` otherwise; `x >>= f` is not lawful in `BW`, so the length of `two BW 0` is 0 on the right side, while the left side (default loop in `LW`, forgetful lift) counts 1.
theorem length_uLift.h11 : ¬ drop0% Std.IterM.length_uLift 11 := fun h => by
  have := h (m := BW) (n := LW) (it := two BW 0)
  simp only [IterM.length, IterM.fold, ForIn.forIn, ForIn'.forIn', IterM.instForIn', IteratorLoop.finiteForIn',
    IteratorLoop.forIn, twoLoopBW, Types.ULiftIterator.instIteratorLoop, IteratorLoop.defaultImplementation] at this
  rw [if_neg not_lawful_bind_BW] at this
  evh this
  simp at this

-- `Std.IterM.length_uLift`, idx 12 (`LawfulMonad n`): `n = MW` (`map` counts 1), identity lift from `LW`, `it = []`: the loop of the left side binds only, the right side maps once.
theorem length_uLift.h12 : ¬ drop0% Std.IterM.length_uLift 12 := fun h => by
  have := h (m := LW) (n := MW) (it := ([] : List Nat).iterM LW)
  simp only [IterM.length, IterM.fold, ForIn.forIn, ForIn'.forIn', IterM.instForIn', IteratorLoop.finiteForIn',
    IteratorLoop.forIn, Types.ULiftIterator.instIteratorLoop, IteratorLoop.defaultImplementation] at this
  evh this
  simp at this

-- `Std.IterM.length_uLift`, idx 14 (`LawfulMonadLiftT m (Std.Iterators.ULiftT n)`): lift `LW → ULiftT TW` counts 1 per lift: the left side lifts every step, the right side the whole length computation once.
theorem length_uLift.h14 : ¬ drop0% Std.IterM.length_uLift 14 := fun h => by
  have := h (m := LW) (n := TW) (it := [1].iterM LW)
  simp only [IterM.length, IterM.fold, ForIn.forIn, ForIn'.forIn', IterM.instForIn', IteratorLoop.finiteForIn',
    IteratorLoop.forIn, Types.ULiftIterator.instIteratorLoop, IteratorLoop.defaultImplementation] at this
  evh this
  simp at this

-- `Std.IterM.toList_take_zero`, idx 4 (`LawfulMonad m`): `m = BW` (`bind` counts 1): `toList` of `take 0` binds once, `pure []` does not.
theorem toList_take_zero.h4 : ¬ drop0% Std.IterM.toList_take_zero 4 := fun h => by
  have := h (m := BW) (it := [1].iterM BW)
  evh this
  simp at this

-- `Std.IterM.toList_toTake`, idx 4 (`LawfulMonad m`): `m = BW` (`bind` counts 1): every `toTake` step binds once more than the base step.
theorem toList_toTake.h4 : ¬ drop0% Std.IterM.toList_toTake 4 := fun h => by
  have := h (m := BW) (it := [1].iterM BW)
  evh this
  simp at this

-- `Std.IterM.toList_flatMap`, idx 7 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it₁ = []`: the flattening iterator binds once more per step.
theorem toList_flatMap.h7 : ¬ drop0% Std.IterM.toList_flatMap 7 := fun h => by
  have := h (m := BW) (f := fun b : Nat => [b].iterM BW) (it₁ := ([] : List Nat).iterM BW)
  evh this
  simp at this

-- `Std.IterM.toArray_flatMap`, idx 7 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it₁ = []`: the flattening iterator binds once more per step.
theorem toArray_flatMap.h7 : ¬ drop0% Std.IterM.toArray_flatMap 7 := fun h => by
  have := h (m := BW) (f := fun b : Nat => [b].iterM BW) (it₁ := ([] : List Nat).iterM BW)
  evh this
  simp at this

-- `Std.IterM.toList_flatMapAfter`, idx 7 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it₁ = []`, `it₂ = none`: the flattening iterator binds once more per step.
theorem toList_flatMapAfter.h7 : ¬ drop0% Std.IterM.toList_flatMapAfter 7 := fun h => by
  have := h (m := BW) (f := fun b : Nat => [b].iterM BW) (it₁ := ([] : List Nat).iterM BW) (it₂ := none)
  evh this
  simp at this

-- `Std.IterM.toArray_flatMapAfter`, idx 7 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it₁ = []`, `it₂ = none`: the flattening iterator binds once more per step.
theorem toArray_flatMapAfter.h7 : ¬ drop0% Std.IterM.toArray_flatMapAfter 7 := fun h => by
  have := h (m := BW) (f := fun b : Nat => [b].iterM BW) (it₁ := ([] : List Nat).iterM BW) (it₂ := none)
  evh this
  simp at this

-- `Std.IterM.toList_flatMapM`, idx 7 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it₁ = []`: the flattening iterator binds once more per step.
theorem toList_flatMapM.h7 : ¬ drop0% Std.IterM.toList_flatMapM 7 := fun h => by
  have := h (m := BW) (f := fun b : Nat => pure ([b].iterM BW)) (it₁ := ([] : List Nat).iterM BW)
  evh this
  simp at this

-- `Std.IterM.toArray_flatMapM`, idx 7 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it₁ = []`: the flattening iterator binds once more per step.
theorem toArray_flatMapM.h7 : ¬ drop0% Std.IterM.toArray_flatMapM 7 := fun h => by
  have := h (m := BW) (f := fun b : Nat => pure ([b].iterM BW)) (it₁ := ([] : List Nat).iterM BW)
  evh this
  simp at this

-- `Std.IterM.toList_flatMapAfterM`, idx 7 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it₁ = []`, `it₂ = none`: the flattening iterator binds once more per step.
theorem toList_flatMapAfterM.h7 : ¬ drop0% Std.IterM.toList_flatMapAfterM 7 := fun h => by
  have := h (m := BW) (f := fun b : Nat => pure ([b].iterM BW)) (it₁ := ([] : List Nat).iterM BW) (it₂ := none)
  evh this
  simp at this

-- `Std.IterM.toArray_flatMapAfterM`, idx 7 (`LawfulMonad m`): `m = BW` (`bind` counts 1), `it₁ = []`, `it₂ = none`: the flattening iterator binds once more per step.
theorem toArray_flatMapAfterM.h7 : ¬ drop0% Std.IterM.toArray_flatMapAfterM 7 := fun h => by
  have := h (m := BW) (f := fun b : Nat => pure ([b].iterM BW)) (it₁ := ([] : List Nat).iterM BW) (it₂ := none)
  evh this
  simp at this

-- `Std.IterM.toList_flatMap`, idx 8 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it₁ = [1]`: only the right side (`mapM`) attaches.
theorem toList_flatMap.h8 : ¬ drop0% Std.IterM.toList_flatMap 8 := fun h => by
  have := h (m := AW) (f := fun b : Nat => [b].iterM AW) (it₁ := [1].iterM AW)
  evh this
  simp at this

-- `Std.IterM.toArray_flatMap`, idx 8 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it₁ = [1]`: only the right side (`mapM`) attaches.
theorem toArray_flatMap.h8 : ¬ drop0% Std.IterM.toArray_flatMap 8 := fun h => by
  have := h (m := AW) (f := fun b : Nat => [b].iterM AW) (it₁ := [1].iterM AW)
  evh this
  simp at this

-- `Std.IterM.toList_flatMapAfter`, idx 8 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it₁ = [1]`, `it₂ = none`: only the right side (`mapM`) attaches.
theorem toList_flatMapAfter.h8 : ¬ drop0% Std.IterM.toList_flatMapAfter 8 := fun h => by
  have := h (m := AW) (f := fun b : Nat => [b].iterM AW) (it₁ := [1].iterM AW) (it₂ := none)
  evh this
  simp at this

-- `Std.IterM.toArray_flatMapAfter`, idx 8 (`WeaklyLawfulMonadAttach m`): `m = AW` (`attach` counts 1), `it₁ = [1]`, `it₂ = none`: only the right side (`mapM`) attaches.
theorem toArray_flatMapAfter.h8 : ¬ drop0% Std.IterM.toArray_flatMapAfter 8 := fun h => by
  have := h (m := AW) (f := fun b : Nat => [b].iterM AW) (it₁ := [1].iterM AW) (it₂ := none)
  evh this
  simp at this

-- `Std.IterM.toList_flatMapM`, idx 8 (`WeaklyLawfulMonadAttach m`): `m = ZW` (`attach` counts 1 on count-0 actions), `f b` = `pure` of an iterator whose `toList` counts 1: the left side attaches `f b` (count 0), the right side `f b >>= toList` (count 1).
theorem toList_flatMapM.h8 : ¬ drop0% Std.IterM.toList_flatMapM 8 := fun h => by
  have := h (m := ZW) (f := fun b : Nat => pure (([b].iterM ZW).mapM fun b : Nat => (⟨1, b⟩ : ZW Nat))) (it₁ := [1].iterM ZW)
  evh this
  simp at this

-- `Std.IterM.toArray_flatMapM`, idx 8 (`WeaklyLawfulMonadAttach m`): `m = ZW` (`attach` counts 1 on count-0 actions), `f b` = `pure` of an iterator whose `toList` counts 1: the left side attaches `f b` (count 0), the right side `f b >>= toList` (count 1).
theorem toArray_flatMapM.h8 : ¬ drop0% Std.IterM.toArray_flatMapM 8 := fun h => by
  have := h (m := ZW) (f := fun b : Nat => pure (([b].iterM ZW).mapM fun b : Nat => (⟨1, b⟩ : ZW Nat))) (it₁ := [1].iterM ZW)
  evh this
  simp at this

-- `Std.IterM.toList_flatMapAfterM`, idx 8 (`WeaklyLawfulMonadAttach m`): `m = ZW` (`attach` counts 1 on count-0 actions), `it₂ = none`, `f b` = `pure` of an iterator whose `toList` counts 1: the left side attaches `f b`, the right side `f b >>= toList`.
theorem toList_flatMapAfterM.h8 : ¬ drop0% Std.IterM.toList_flatMapAfterM 8 := fun h => by
  have := h (m := ZW) (f := fun b : Nat => pure (([b].iterM ZW).mapM fun b : Nat => (⟨1, b⟩ : ZW Nat))) (it₁ := [1].iterM ZW) (it₂ := none)
  evh this
  simp at this

-- `Std.IterM.toArray_flatMapAfterM`, idx 8 (`WeaklyLawfulMonadAttach m`): `m = ZW` (`attach` counts 1 on count-0 actions), `it₂ = none`, `f b` = `pure` of an iterator whose `toList` counts 1: the left side attaches `f b`, the right side `f b >>= toList`.
theorem toArray_flatMapAfterM.h8 : ¬ drop0% Std.IterM.toArray_flatMapAfterM 8 := fun h => by
  have := h (m := ZW) (f := fun b : Nat => pure (([b].iterM ZW).mapM fun b : Nat => (⟨1, b⟩ : ZW Nat))) (it₁ := [1].iterM ZW) (it₂ := none)
  evh this
  simp at this

-- `Std.IterM.toList_uLift`, idx 10 (`LawfulMonad m`): `m = MW` (`map` counts 1), identity lift to `ULiftT LW`: only the right side runs the toList of the base iterator, which maps in `m`.
theorem toList_uLift.h10 : ¬ drop0% Std.IterM.toList_uLift 10 := fun h => by
  have := h (m := MW) (n := LW) (it := [1].iterM MW)
  evh this
  simp at this

-- `Std.IterM.toListRev_uLift`, idx 11 (`LawfulMonad n`): `n = MW` (`map` counts 1), identity lift from `LW`: only the right side maps in `n`.
theorem toListRev_uLift.h11 : ¬ drop0% Std.IterM.toListRev_uLift 11 := fun h => by
  have := h (m := LW) (n := MW) (it := [1].iterM LW)
  evh this
  simp at this

-- `Std.IterM.toArray_uLift`, idx 11 (`LawfulMonad n`): `n = MW` (`map` counts 1), identity lift from `LW`: only the right side maps in `n`.
theorem toArray_uLift.h11 : ¬ drop0% Std.IterM.toArray_uLift 11 := fun h => by
  have := h (m := LW) (n := MW) (it := [1].iterM LW)
  evh this
  simp at this

-- `Std.IterM.toList_uLift`, idx 12 (`LawfulMonadLiftT m (Std.Iterators.ULiftT n)`): lift `LW → ULiftT TW` counts 1 per lift: the left side lifts every step, the right side the whole consumer once.
theorem toList_uLift.h12 : ¬ drop0% Std.IterM.toList_uLift 12 := fun h => by
  have := h (m := LW) (n := TW) (it := [1].iterM LW)
  evh this
  simp at this

-- `Std.IterM.toListRev_uLift`, idx 12 (`LawfulMonadLiftT m (Std.Iterators.ULiftT n)`): lift `LW → ULiftT TW` counts 1 per lift: the left side lifts every step, the right side the whole consumer once.
theorem toListRev_uLift.h12 : ¬ drop0% Std.IterM.toListRev_uLift 12 := fun h => by
  have := h (m := LW) (n := TW) (it := [1].iterM LW)
  evh this
  simp at this

-- `Std.IterM.toArray_uLift`, idx 12 (`LawfulMonadLiftT m (Std.Iterators.ULiftT n)`): lift `LW → ULiftT TW` counts 1 per lift: the left side lifts every step, the right side the whole consumer once.
theorem toArray_uLift.h12 : ¬ drop0% Std.IterM.toArray_uLift 12 := fun h => by
  have := h (m := LW) (n := TW) (it := [1].iterM LW)
  evh this
  simp at this

/-! ## Removable -/

/-! Copies of private helpers of `Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap`. -/

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
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
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

/-- `IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition` without its unused
instance arguments (it is `rfl`). -/
theorem toList_mwp_eq_fmwp {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad n] [MonadLiftT m n] [Iterator α m β]
    {f : β → PostconditionT n γ} {it : IterM (α := α) m β} :
    (it.mapWithPostcondition f).toList =
      (it.filterMapWithPostcondition (PostconditionT.map some <| f ·)).toList := rfl

/-- `IterM.toList_filterMapM_mapM` without `[LawfulMonadLiftT m n]` (and `[LawfulMonad m]`). -/
theorem toList_filterMapM_mapM' {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).filterMapM g).toList =
      (it.filterMapM (n := o) (fun b => do g (← f b))).toList := by
  apply toList_fmwp_fmwp'
  intro b
  simp only [PostconditionT.attachLift, PostconditionT.run_eq_map, WeaklyLawfulMonadAttach.map_attach,
    PostconditionT.operation_map]
  conv => lhs; simp only [← WeaklyLawfulMonadAttach.map_attach (x := f _)]
  simp

theorem pbind_eq_pbind_if_isSome {m : Type w → Type w'} [Monad m] [MonadAttach m] (x : m (Option α))
    (f : (_ : _) → _ → m β) :
    MonadAttach.pbind x f = MonadAttach.pbind x
        (fun a ha => optionPelim' a (fun _ => f none (by simp_all)) (fun a _ => f (some a) (by simp_all))) := by
  intros; congr; ext
  simp only [optionPelim']
  split <;> simp

/-- `IterM.toList_mapM_eq_toList_filterMapM` without `[LawfulMonad m]` and `[LawfulMonadLiftT m n]`
(the library's proof, which uses neither). -/
theorem toList_mapM_eq_filterMapM' {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [Iterator α m β] [Finite α m]
    {f : β → n γ} {it : IterM (α := α) m β} :
    (it.mapM f).toList = (it.filterMapM fun b => some <$> f b).toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step, IterM.step_mapM, IterM.step_filterMapM,
    bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split
  · conv =>
      rhs
      simp only [bind_pure_comp, bind_assoc]
      simp only [MonadAttach.attach_bind_eq_pbind]
      rw [pbind_eq_pbind_if_isSome]
    simp [MonadAttach.attach_bind_eq_pbind, WeaklyLawfulMonadAttach.pbind_eq_bind, optionPelim', ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

-- `Std.IterM.toList_mapWithPostcondition_mapWithPostcondition`, idx 15 (`LawfulMonadLiftT m n`):
-- removable. Both sides lift the base steps with the same `m → n → o` lifts; the library proof
-- only needs the laws of the lift `n → o` (the library's proof, via toList_fmwp_fmwp').
theorem toList_mapWithPostcondition_mapWithPostcondition.h15 :
    drop% Std.IterM.toList_mapWithPostcondition_mapWithPostcondition 15 := by
  intro α β γ δ m n o; intros; rename_i f g it
  simp only [toList_mwp_eq_fmwp]
  apply toList_fmwp_fmwp'
  intro b
  simp [liftM, monadLift, MonadLift.monadLift, monadLift_self, PostconditionT.run_eq_map,
    PostconditionT.operation_bind']

-- `Std.IterM.toListRev_mapWithPostcondition_mapWithPostcondition`, idx 15 (`LawfulMonadLiftT m n`):
-- removable, from the toList version (toListRev is List.reverse of toList).
theorem toListRev_mapWithPostcondition_mapWithPostcondition.h15 :
    drop% Std.IterM.toListRev_mapWithPostcondition_mapWithPostcondition 15 := by
  intros; simp [IterM.toListRev_eq, toList_mapWithPostcondition_mapWithPostcondition.h15]

-- `Std.IterM.toArray_mapWithPostcondition_mapWithPostcondition`, idx 15 (`LawfulMonadLiftT m n`):
-- removable, from the toList version (toArray is List.toArray of toList).
theorem toArray_mapWithPostcondition_mapWithPostcondition.h15 :
    drop% Std.IterM.toArray_mapWithPostcondition_mapWithPostcondition 15 := by
  intros; simp [← IterM.toArray_toList, toList_mapWithPostcondition_mapWithPostcondition.h15]

-- `Std.IterM.toList_mapM_mapM`, idx 19 (`LawfulMonadLiftT m n`): removable. As in the library proof
-- (rewrite both mapM to filterMapM, then fuse), with copies of the two library lemmas whose own proofs
-- do not use the laws of the lift `m → n`.
theorem toList_mapM_mapM.h19 : drop% Std.IterM.toList_mapM_mapM 19 := by
  intro α β γ δ m n o; intros; rename_i f g it
  simp only [toList_mapM_eq_filterMapM', toList_filterMapM_mapM']
  congr <;> simp

-- `Std.IterM.toListRev_mapM_mapM`, idx 19 (`LawfulMonadLiftT m n`): removable, from the toList version.
theorem toListRev_mapM_mapM.h19 : drop% Std.IterM.toListRev_mapM_mapM 19 := by
  intros; simp [IterM.toListRev_eq, toList_mapM_mapM.h19]

-- `Std.IterM.toArray_mapM_mapM`, idx 19 (`LawfulMonadLiftT m n`): removable, from the toList version.
theorem toArray_mapM_mapM.h19 : drop% Std.IterM.toArray_mapM_mapM 19 := by
  intros; simp [← IterM.toArray_toList, toList_mapM_mapM.h19]

-- `Std.IterM.toList_mapM_map`, idx 11 (`WeaklyLawfulMonadAttach n`): removable. Both sides attach
-- `g (f b)` once per element; the induction over the steps needs no `map_attach`.
theorem toList_mapM_map.h11 : drop% Std.IterM.toList_mapM_map 11 := by
  intro α β γ δ m n; intros; rename_i f g it
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step, IterM.step_mapM, bind_assoc,
    IterM.step_mapM, IterM.step_map]
  simp only [bind_assoc, liftM_bind]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, liftM_pure, pure_bind, Shrink.inflate_deflate]
    apply bind_congr; intro fx
    simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

-- `Std.IterM.toListRev_mapM_map`, idx 11 (`WeaklyLawfulMonadAttach n`): removable, from the toList version.
theorem toListRev_mapM_map.h11 : drop% Std.IterM.toListRev_mapM_map 11 := by
  intros; simp [IterM.toListRev_eq, toList_mapM_map.h11]

-- `Std.IterM.toArray_mapM_map`, idx 11 (`WeaklyLawfulMonadAttach n`): removable, from the toList version.
theorem toArray_mapM_map.h11 : drop% Std.IterM.toArray_mapM_map 11 := by
  intros; simp [← IterM.toArray_toList, toList_mapM_map.h11]

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

-- `Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition`, idx 10 (`LawfulMonad n`):
-- removable. Every action in `n` reaches `o` through the lawful lift (no `map` in `n` is used), so
-- the inner iterator can be moved to `o` (toList_fmwp_lift), where the library's argument applies.
theorem toList_filterMapWithPostcondition_filterMapWithPostcondition.h10 :
    drop% Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition 10 := by
  intro α β γ δ m n o; intros; rename_i f g it
  letI : MonadLift n o := ⟨monadLift⟩
  rw [toList_fmwp_lift]
  apply toList_fmwp_fmwp'
  intro b
  simp only [PostconditionT.run_bind']
  simp only [liftM, monadLift, MonadLift.monadLift, monadLift_self, PostconditionT.run_eq_map,
    bind_map_left, liftM_map]
  apply bind_congr; intro fx
  split <;> simp [*]

-- `Std.IterM.toListRev_filterMapWithPostcondition_filterMapWithPostcondition`, idx 10 (`LawfulMonad n`):
-- removable, from the toList version.
theorem toListRev_filterMapWithPostcondition_filterMapWithPostcondition.h10 :
    drop% Std.IterM.toListRev_filterMapWithPostcondition_filterMapWithPostcondition 10 := by
  intros; simp [IterM.toListRev_eq, toList_filterMapWithPostcondition_filterMapWithPostcondition.h10]

-- `Std.IterM.toArray_filterMapWithPostcondition_filterMapWithPostcondition`, idx 10 (`LawfulMonad n`):
-- removable, from the toList version.
theorem toArray_filterMapWithPostcondition_filterMapWithPostcondition.h10 :
    drop% Std.IterM.toArray_filterMapWithPostcondition_filterMapWithPostcondition 10 := by
  intros; simp [← IterM.toArray_toList, toList_filterMapWithPostcondition_filterMapWithPostcondition.h10]

/-- The uLift iterator's reverse-list loop is the lifted loop of the base iterator (no laws of `m`). -/
theorem revgo_uLift {α β : Type u} {m : Type u → Type u'} {n : Type max u v → Type v'} [Iterator α m β]
    [Monad m] [Monad n] [LawfulMonad n] [MonadLiftT m (ULiftT n)] [LawfulMonadLiftT m (ULiftT n)]
    [Finite α m] (it : IterM (α := α) m β) (acc : List β) :
    IterM.toListRev.go (it.uLift n) (acc.map ULift.up) =
      (fun l => List.map ULift.up l.down) <$> (monadLift (IterM.toListRev.go it acc) : ULiftT n _).run := by
  induction it using IterM.inductSteps generalizing acc with | step it ihy ihs
  rw [revgo_eq', revgo_eq', IterM.step_uLift]
  simp only [monadLift_bind, ULiftT.run_bind, bind_assoc, pure_bind, map_bind]
  apply bind_congr; intro step
  cases step.down.inflate using PlausibleIterStep.casesOn
  · simp only [pure_bind, Shrink.inflate_deflate, PlausibleIterStep.yield]
    rw [← List.map_cons, ihy ‹_›]
  · simp only [pure_bind, Shrink.inflate_deflate, PlausibleIterStep.skip]
    rw [ihs ‹_›]
  · simp [monadLift_pure, PlausibleIterStep.done]

/-- The uLift iterator's array loop is the lifted loop of the base iterator (no laws of `m`). -/
theorem go_uLift {α β : Type u} {m : Type u → Type u'} {n : Type max u v → Type v'} [Iterator α m β]
    [Monad m] [Monad n] [LawfulMonad n] [MonadLiftT m (ULiftT n)] [LawfulMonadLiftT m (ULiftT n)]
    [Finite α m] (it : IterM (α := α) m β) (acc : Array β) :
    IterM.toArray.go (it.uLift n) (acc.map ULift.up) =
      (fun l => Array.map ULift.up l.down) <$> (monadLift (IterM.toArray.go it acc) : ULiftT n _).run := by
  induction it using IterM.inductSteps generalizing acc with | step it ihy ihs
  rw [go_eq', go_eq', IterM.step_uLift]
  simp only [monadLift_bind, ULiftT.run_bind, bind_assoc, pure_bind, map_bind]
  apply bind_congr; intro step
  cases step.down.inflate using PlausibleIterStep.casesOn
  · simp only [pure_bind, Shrink.inflate_deflate, PlausibleIterStep.yield]
    rw [← Array.map_push, ihy ‹_›]
  · simp only [pure_bind, Shrink.inflate_deflate, PlausibleIterStep.skip]
    rw [ihs ‹_›]
  · simp [monadLift_pure, PlausibleIterStep.done]

-- `Std.IterM.toListRev_uLift`, idx 10 (`LawfulMonad m`): removable. Both sides only use `m` through the
-- lawful lift, step by step (induction over the steps with the law-free unfolding of the loop).
theorem toListRev_uLift.h10 : drop% Std.IterM.toListRev_uLift 10 := by
  intro α m n β _ _ _ it _ _ _ _
  have := revgo_uLift (n := n) it []
  simpa [IterM.toListRev] using this

-- `Std.IterM.toArray_uLift`, idx 10 (`LawfulMonad m`): removable. Both sides only use `m` through the
-- lawful lift, step by step (induction over the steps with the law-free unfolding of the loop).
theorem toArray_uLift.h10 : drop% Std.IterM.toArray_uLift 10 := by
  intro α m n β _ _ _ it _ _ _ _
  have := go_uLift (n := n) it #[]
  simpa [IterM.toArray] using this


end ItMonadMBHand
