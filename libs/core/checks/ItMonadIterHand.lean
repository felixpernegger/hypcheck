import Lean

/-!
Hand pass `ItMonadIter` (hand8): 150 non-dependent monad-law hypotheses (`LawfulMonad`,
`WeaklyLawfulMonadAttach`, `LawfulMonadLiftT`) of the `Std.Iter.*` lemmas about pure iterators with
monadic combinators and consumers (`Lemmas/Combinators/FilterMap`, `Lemmas/Consumers/Loop`,
`Lemmas/Combinators/FlatMap`). For hypothesis `hᵢ` of theorem `T` each declaration proves `¬T'`
(necessary, `¬ drop0% T i`, universes set to `0`) or `T'` (removable, `drop% T i`).

142 necessary, 8 removable.

Necessary (142): `T'` is instantiated at the countdown iterator `CD` (`ci k`, from `ItDepOtherHand`)
and a broken monad, and both sides are evaluated without monad laws: `go_eq'` / `dforIn'_eq_fin`
unfold `toArray.go` / the default loop once (`extrinsicFix₂/₃_eq_apply` with the `Finite` relation),
`step_fmwp` / `step_mwp` / `step_flattenAfter'` (law-free copies from `ItMonadMB`) the combinator
steps, and projection lemmas the monad operations (`evh` / `evl` / `evs`; only `rw` unfolds the
consumers and only projections are rewritten by `simp`, so the functions inside the iterator types
stay untouched). The counters then differ (`omega`, `decide`). Models:
* `Z` (`Option`, `bind = none`): the step lemmas, where the left side binds and the right side is `pure`;
* `W bc mc ac lc ak` (writer monad over `Int`; `bind` adds `bc`, `map` adds `mc`, `attach x` adds
  `ac + ak * x.c`, lifting into it adds `lc`): `Bm` (bind counts, weakly lawful), `Mm` (map +1,
  attach -1: weakly lawful, not lawful), `Mo` (map +1), `Am` (lawful, attach counts), `Dm` (lawful,
  attach counts its action twice), `L` (lawful), `Lc` (lawful, the lift `L → Lc` counts);
* `U` (two counters; `bind` adds `x.c * (f x.v).d ^ 2` to `d`: not associative; lawful lift
  `L → U`): the `LawfulMonad o` hypotheses of `forIn_*`/`foldM_*`, where the two loops associate the
  lifted effect of `f` and the effect of `g` differently;
* `SB` (after `SM` of the ItMonadMA pass: `Bool` writer with lawful `bind`/`pure`, whose `map` flips
  the flag iff the target type is a subsingleton and whose `attach` flips it iff the value type is, so
  `attach` stays weakly lawful; lawful lifts `Id → SB → BW`): the `LawfulMonad n` hypotheses of
  `forIn_*`/`foldM_*` for `mapWithPostcondition`, `mapM`, `filterWithPostcondition`, `filterM`, where
  the combinator maps into a subsingleton `PostconditionT` property subtype and the other side does not;
* `TK` (countdown over `W` whose steps count 1): the inner iterator for `flatMapM`.

Removable (8): `Iter.forIn'_eq`, `Iter.forIn_eq` (`LawfulMonad m`: the lawful loop is the default loop,
the right side by definition), `Iter.forIn_map`, `Iter.foldM_map`, `Iter.anyM_map`, `Iter.allM_map`
(`LawfulMonad`: the mapped pure iterator steps like the base one, `dforIn'_map` by induction),
`Iter.toList/toArray_filterMapWithPostcondition_filterMapWithPostcondition` (`LawfulMonad m`: `m` is
only reached through the lawful lift; law-free copies of the ItMonadMB transport/fusion lemmas).

Run with the lean4 repo's stage1 binary: `lean checks/ItMonadIterHand.lean`.
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

-- `Std.Iter.forIn'_eq`, idx 6 (LawfulMonad m): removable. The loop instance is lawful, so it is the
-- default loop, which is the right side by definition; the lift of the Iter loop is lawful in any monad.
theorem Iter.forIn'_eq.h6 : drop% Std.Iter.forIn'_eq 6 := by
  intro α β _ _ m _ _ hl γ it init f
  simp only [ForIn'.forIn']
  rw [@LawfulIteratorLoop.lawful _ _ _ _ _ _ _ _ hl _ lbf _ _ _ _ IteratorLoop.wellFounded_of_finite]
  rfl

-- `Std.Iter.forIn_eq`, idx 6 (LawfulMonad m): removable, as for the forIn' version.
theorem Iter.forIn_eq.h6 : drop% Std.Iter.forIn_eq 6 := by
  intro α β _ _ m _ _ hl γ it init f
  simp only [ForIn.forIn, ForIn'.forIn']
  rw [@LawfulIteratorLoop.lawful _ _ _ _ _ _ _ _ hl _ lbf _ _ _ _ IteratorLoop.wellFounded_of_finite]
  rfl

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

-- `Std.Iter.forIn_map`, idx 7 (LawfulMonad n): removable. Both loops are default loops and the mapped
-- iterator steps exactly like the base one (dforIn'_map), so no monad law is used.
theorem Iter.forIn_map.h7 : drop% Std.Iter.forIn_map 7 := by
  intro α β γ _ n β₂ _ _ _ hl it f init g
  simp only [ForIn.forIn, ForIn'.forIn']
  rw [@LawfulIteratorLoop.lawful _ _ _ _ _ _ _ _ hl _ lbf _ _ _ _ IteratorLoop.wellFounded_of_finite]
  exact dforIn'_map f _ it.toIterM init

-- `Std.Iter.foldM_map`, idx 8 (LawfulMonad n): removable, by dforIn'_map.
theorem Iter.foldM_map.h8 : drop% Std.Iter.foldM_map 8 := by
  intro α β γ δ n _ _ _ _ hl f g init it
  simp only [ForIn.forIn, ForIn'.forIn', Iter.foldM]
  rw [@LawfulIteratorLoop.lawful _ _ _ _ _ _ _ _ hl _ lbf _ _ _ _ IteratorLoop.wellFounded_of_finite]
  exact dforIn'_map f _ it.toIterM init

-- `Std.Iter.anyM_map`, idx 8 (LawfulMonad m): removable, by dforIn'_map.
theorem Iter.anyM_map.h8 : drop% Std.Iter.anyM_map 8 := by
  intro α β β' m _ _ _ _ hl it f p
  simp only [ForIn.forIn, ForIn'.forIn', Iter.anyM]
  rw [@LawfulIteratorLoop.lawful _ _ _ _ _ _ _ _ hl _ lbf _ _ _ _ IteratorLoop.wellFounded_of_finite]
  exact dforIn'_map f _ it.toIterM _

-- `Std.Iter.allM_map`, idx 8 (LawfulMonad m): removable, by dforIn'_map.
theorem Iter.allM_map.h8 : drop% Std.Iter.allM_map 8 := by
  intro α β β' m _ _ _ _ hl it f p
  simp only [ForIn.forIn, ForIn'.forIn', Iter.allM]
  rw [@LawfulIteratorLoop.lawful _ _ _ _ _ _ _ _ hl _ lbf _ _ _ _ IteratorLoop.wellFounded_of_finite]
  exact dforIn'_map f _ it.toIterM _

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

-- `Std.Iter.toList_filterMapWithPostcondition_filterMapWithPostcondition`, idx 9 (LawfulMonad m):
-- removable. The inner monad m is only used through the lawful lift into n (no map in m): move the
-- inner iterator to n (MBc.toList_fmwp_lift), fuse in n (MBc.toList_fmwp_fmwp'), and identify the base
-- lift Id to m to n with pure by the lift's monadLift_pure law (fm_lift_congr).
theorem Iter.toList_fMWP_fMWP.h9 : drop% Std.Iter.toList_filterMapWithPostcondition_filterMapWithPostcondition 9 := by
  intro α β γ _ it m n δ _ _ _ _ _ _ f g
  simp only [Iter.filterMapWithPostcondition]
  letI : MonadLift m n := ⟨monadLift⟩
  rw [MBc.toList_fmwp_lift]
  rw [show ∀ F : β → PostconditionT n (Option δ), (it.toIterM.filterMapWithPostcondition F).toList =
      (IterM.InternalCombinators.filterMap
        (fun ⦃δ⦄ (x : Id δ) => (@monadLift Id n (@instMonadLiftTOfMonadLift Id m n _ _) δ x)) F
        it.toIterM).toList from fun F => (fm_lift_congr _ _
          (by funext δ x; exact LawfulMonadLiftT.monadLift_pure (m := m) (n := n) x)).symm]
  apply @MBc.toList_fmwp_fmwp'
  intro b
  simp only [PostconditionT.run_bind', liftM, monadLift_self, PostconditionT.run_eq_map]
  simp only [PostconditionT.operation_bind', map_bind, bind_map_left]
  apply bind_congr; intro x
  rcases x with ⟨_ | x, hx⟩ <;> simp

-- `Std.Iter.toArray_filterMapWithPostcondition_filterMapWithPostcondition`, idx 9 (LawfulMonad m):
-- removable, from the toList version (n is lawful).
theorem Iter.toArray_fMWP_fMWP.h9 : drop% Std.Iter.toArray_filterMapWithPostcondition_filterMapWithPostcondition 9 := by
  intro α β γ _ it m n δ _ _ _ _ _ _ f g
  rw [← IterM.toArray_toList, ← IterM.toArray_toList, Iter.toList_fMWP_fMWP.h9]

/-! ## Necessary verdicts -/

-- `Std.Iter.step_filterMapWithPostcondition`, idx 9: n = Z (Option whose bind is none), it empty: the left side binds the lifted base step (none), the right side is pure (some)
theorem Iter.step_filterMapWithPostcondition.h9 : ¬ drop0% Std.Iter.step_filterMapWithPostcondition 9 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 0) (n := Z) (γ := Nat) (m := Id) (f := fun _ => pure none)
  rw [CD.step0'] at this
  exact nomatch (this : @Eq (Option _) _ _)

-- `Std.Iter.step_filterWithPostcondition`, idx 8: n = Z (Option whose bind is none), it empty: the left side binds the lifted base step (none), the right side is pure (some)
theorem Iter.step_filterWithPostcondition.h8 : ¬ drop0% Std.Iter.step_filterWithPostcondition 8 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 0) (n := Z) (m := Id) (f := fun _ => pure (.up false))
  rw [CD.step0'] at this
  exact nomatch (this : @Eq (Option _) _ _)

-- `Std.Iter.step_mapWithPostcondition`, idx 8: n = Z (Option whose bind is none), it empty: the left side binds the lifted base step (none), the right side is pure (some)
theorem Iter.step_mapWithPostcondition.h8 : ¬ drop0% Std.Iter.step_mapWithPostcondition 8 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 0) (n := Z) (γ := Nat) (f := pure)
  rw [CD.step0'] at this
  exact nomatch (this : @Eq (Option _) _ _)

-- `Std.Iter.step_filterMapM`, idx 10: n = Z (Option whose bind is none), it empty: the left side binds the lifted base step (none), the right side is pure (some)
theorem Iter.step_filterMapM.h10 : ¬ drop0% Std.Iter.step_filterMapM 10 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 0) (n := Z) (β' := Nat) (m := Id) (f := fun _ => pure none)
  rw [CD.step0'] at this
  exact nomatch (this : @Eq (Option _) _ _)

-- `Std.Iter.step_filterM`, idx 9: n = Z (Option whose bind is none), it empty: the left side binds the lifted base step (none), the right side is pure (some)
theorem Iter.step_filterM.h9 : ¬ drop0% Std.Iter.step_filterM 9 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 0) (n := Z) (m := Id) (f := fun _ => pure (.up false))
  rw [CD.step0'] at this
  exact nomatch (this : @Eq (Option _) _ _)

-- `Std.Iter.step_mapM`, idx 9: n = Z (Option whose bind is none), it empty: the left side binds the lifted base step (none), the right side is pure (some)
theorem Iter.step_mapM.h9 : ¬ drop0% Std.Iter.step_mapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 0) (n := Z) (γ := Nat) (f := pure)
  rw [CD.step0'] at this
  exact nomatch (this : @Eq (Option _) _ _)

-- `Std.Iter.toList_mapWithPostcondition`, idx 7: m = Bm (bind counts 1), it empty: the left side binds the base step, List.mapM _ [] is pure []
theorem Iter.toList_mapWithPostcondition.h7 : ¬ drop0% Std.Iter.toList_mapWithPostcondition 7 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 0) (m := Bm) (f := pure)
  rw [CD.toList0] at this
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toList_mapM`, idx 8: m = Bm (bind counts 1, trivial attach), it empty: the left side binds the base step, List.mapM _ [] is pure []
theorem Iter.toList_mapM.h8 : ¬ drop0% Std.Iter.toList_mapM 8 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 0) (m := Bm) (f := pure)
  rw [CD.toList0] at this
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toList_mapM`, idx 9: m = Am (lawful, attach counts 1), it = [0]: only the left side attaches
theorem Iter.toList_mapM.h9 : ¬ drop0% Std.Iter.toList_mapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (m := Am) (f := pure)
  rw [toList1] at this
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toArray_mapWithPostcondition`, idx 7: m = Bm (bind counts 1), it empty: the left side binds the base step, Array.mapM _ #[] is pure #[]
theorem Iter.toArray_mapWithPostcondition.h7 : ¬ drop0% Std.Iter.toArray_mapWithPostcondition 7 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 0) (m := Bm) (f := pure)
  rw [toArray0] at this
  have := congrArg W.c this
  evh this
  arrfin

-- `Std.Iter.toArray_mapM`, idx 8: m = Bm (bind counts 1, trivial attach), it empty: the left side binds the base step, Array.mapM _ #[] is pure #[]
theorem Iter.toArray_mapM.h8 : ¬ drop0% Std.Iter.toArray_mapM 8 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 0) (m := Bm) (f := pure)
  rw [toArray0] at this
  have := congrArg W.c this
  evh this
  arrfin

-- `Std.Iter.toArray_mapM`, idx 9: m = Am (lawful, attach counts 1), it = [0]: only the left side attaches
theorem Iter.toArray_mapM.h9 : ¬ drop0% Std.Iter.toArray_mapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (m := Am) (f := pure)
  rw [toArray1] at this
  have := congrArg W.c this
  evh this
  arrfin

-- `Std.Iter.toList_filterMapWithPostcondition_filterMapWithPostcondition`, idx 11: m = L (lawful), n = Mo (map counts 1; lawful lift L → Mo), it = [0]: the right side's PostconditionT bind maps once more
theorem Iter.toList_filterMapWithPostcondition_filterMapWithPostcondition.h11 : ¬ drop0% Std.Iter.toList_filterMapWithPostcondition_filterMapWithPostcondition 11 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (δ := Nat) (it := ci 1) (m := L) (n := Mo) (f := fun x => pure (some x)) (g := fun x => pure (some x))
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toList_filterMapWithPostcondition_filterMapWithPostcondition`, idx 13: m = L, n = Lc (lawful; the lift L → Lc counts 1), it = [0]: the left side lifts both base steps, the right side lifts f 0 once
theorem Iter.toList_filterMapWithPostcondition_filterMapWithPostcondition.h13 : ¬ drop0% Std.Iter.toList_filterMapWithPostcondition_filterMapWithPostcondition 13 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (δ := Nat) (it := ci 1) (m := L) (n := Lc) (f := fun x => pure (some x)) (g := fun x => pure (some x))
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toList_mapWithPostcondition_mapWithPostcondition`, idx 11: m = L (lawful), n = Mo (map counts 1; lawful lift L → Mo), it = [0]: the right side's PostconditionT bind maps once more
theorem Iter.toList_mapWithPostcondition_mapWithPostcondition.h11 : ¬ drop0% Std.Iter.toList_mapWithPostcondition_mapWithPostcondition 11 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (δ := Nat) (it := ci 1) (m := L) (n := Mo) (f := pure) (g := pure)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toList_mapWithPostcondition_mapWithPostcondition`, idx 13: m = L, n = Lc (lawful; the lift L → Lc counts 1), it = [0]: the left side lifts both base steps, the right side lifts f 0 once
theorem Iter.toList_mapWithPostcondition_mapWithPostcondition.h13 : ¬ drop0% Std.Iter.toList_mapWithPostcondition_mapWithPostcondition 13 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (δ := Nat) (it := ci 1) (m := L) (n := Lc) (f := pure) (g := pure)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toArray_filterMapWithPostcondition_filterMapWithPostcondition`, idx 11: m = L (lawful), n = Mo (map counts 1; lawful lift L → Mo), it = [0]: the right side's PostconditionT bind maps once more
theorem Iter.toArray_filterMapWithPostcondition_filterMapWithPostcondition.h11 : ¬ drop0% Std.Iter.toArray_filterMapWithPostcondition_filterMapWithPostcondition 11 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (δ := Nat) (it := ci 1) (m := L) (n := Mo) (f := fun x => pure (some x)) (g := fun x => pure (some x))
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toArray_filterMapWithPostcondition_filterMapWithPostcondition`, idx 13: m = L, n = Lc (lawful; the lift L → Lc counts 1), it = [0]: the left side lifts both base steps, the right side lifts f 0 once
theorem Iter.toArray_filterMapWithPostcondition_filterMapWithPostcondition.h13 : ¬ drop0% Std.Iter.toArray_filterMapWithPostcondition_filterMapWithPostcondition 13 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (δ := Nat) (it := ci 1) (m := L) (n := Lc) (f := fun x => pure (some x)) (g := fun x => pure (some x))
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toArray_mapWithPostcondition_mapWithPostcondition`, idx 11: m = L (lawful), n = Mo (map counts 1; lawful lift L → Mo), it = [0]: the right side's PostconditionT bind maps once more
theorem Iter.toArray_mapWithPostcondition_mapWithPostcondition.h11 : ¬ drop0% Std.Iter.toArray_mapWithPostcondition_mapWithPostcondition 11 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (δ := Nat) (it := ci 1) (m := L) (n := Mo) (f := pure) (g := pure)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toArray_mapWithPostcondition_mapWithPostcondition`, idx 13: m = L, n = Lc (lawful; the lift L → Lc counts 1), it = [0]: the left side lifts both base steps, the right side lifts f 0 once
theorem Iter.toArray_mapWithPostcondition_mapWithPostcondition.h13 : ¬ drop0% Std.Iter.toArray_mapWithPostcondition_mapWithPostcondition 13 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (δ := Nat) (it := ci 1) (m := L) (n := Lc) (f := pure) (g := pure)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.forIn_filterMapWithPostcondition`, idx 8: n = Mo (map counts 1), o = L, lawful lift, it = [0]: only the right side maps ((f out).run)
theorem Iter.forIn_filterMapWithPostcondition.h8 : ¬ drop0% Std.Iter.forIn_filterMapWithPostcondition 8 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Mo) (o := L) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_filterMapWithPostcondition`, idx 12: n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value
theorem Iter.forIn_filterMapWithPostcondition.h12 : ¬ drop0% Std.Iter.forIn_filterMapWithPostcondition 12 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_filterMapM`, idx 8: n = Mm (map counts 1, attach -1: weakly lawful, not lawful), o = L, it = [0]: only the left side attaches
theorem Iter.forIn_filterMapM.h8 : ¬ drop0% Std.Iter.forIn_filterMapM 8 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Mm) (o := L) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_filterMapM`, idx 12: n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches
theorem Iter.forIn_filterMapM.h12 : ¬ drop0% Std.Iter.forIn_filterMapM 12 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Am) (o := L) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_filterMapM`, idx 14: n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value
theorem Iter.forIn_filterMapM.h14 : ¬ drop0% Std.Iter.forIn_filterMapM 14 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun x => pure (some x)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_filterMap`, idx 7: n = Bm (bind counts 1), it = [0], f = none: the left loop never calls its body, the right one binds pure (.yield _)
theorem Iter.forIn_filterMap.h7 : ¬ drop0% Std.Iter.forIn_filterMap 7 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Bm) (f := fun _ => none) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_mapWithPostcondition`, idx 12: n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value
theorem Iter.forIn_mapWithPostcondition.h12 : ¬ drop0% Std.Iter.forIn_mapWithPostcondition 12 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := L) (o := Lc) (f := pure) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_mapM`, idx 12: n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches
theorem Iter.forIn_mapM.h12 : ¬ drop0% Std.Iter.forIn_mapM 12 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := Am) (o := L) (f := pure) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_mapM`, idx 14: n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value
theorem Iter.forIn_mapM.h14 : ¬ drop0% Std.Iter.forIn_mapM 14 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := L) (o := Lc) (f := pure) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_filterWithPostcondition`, idx 11: n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value
theorem Iter.forIn_filterWithPostcondition.h11 : ¬ drop0% Std.Iter.forIn_filterWithPostcondition 11 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_filterM`, idx 11: n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches
theorem Iter.forIn_filterM.h11 : ¬ drop0% Std.Iter.forIn_filterM 11 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := Am) (o := L) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_filterM`, idx 13: n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value
theorem Iter.forIn_filterM.h13 : ¬ drop0% Std.Iter.forIn_filterM 13 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_filter`, idx 6: n = Bm (bind counts 1), it = [0], f = false: the left loop never calls its body, the right one binds pure (.yield _)
theorem Iter.forIn_filter.h6 : ¬ drop0% Std.Iter.forIn_filter 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := Bm) (f := fun _ => false) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterMapWithPostcondition`, idx 10: n = Mo (map counts 1), o = L, lawful lift, it = [0]: only the right side maps ((f b).run)
theorem Iter.foldM_filterMapWithPostcondition.h10 : ¬ drop0% Std.Iter.foldM_filterMapWithPostcondition 10 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Mo) (o := L) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterMapWithPostcondition`, idx 11: n = L, o = Mo (map counts 1; lawful lift), it = [0], f = none: the left fold has no element to map ForInStep.yield over, the right one has one
theorem Iter.foldM_filterMapWithPostcondition.h11 : ¬ drop0% Std.Iter.foldM_filterMapWithPostcondition 11 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Mo) (f := fun _ => pure none) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterMapWithPostcondition`, idx 17: n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value
theorem Iter.foldM_filterMapWithPostcondition.h17 : ¬ drop0% Std.Iter.foldM_filterMapWithPostcondition 17 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterMapM`, idx 10: n = Mm (map counts 1, attach -1: weakly lawful, not lawful), o = L, it = [0]: only the left side attaches
theorem Iter.foldM_filterMapM.h10 : ¬ drop0% Std.Iter.foldM_filterMapM 10 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Mm) (o := L) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterMapM`, idx 11: n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches
theorem Iter.foldM_filterMapM.h11 : ¬ drop0% Std.Iter.foldM_filterMapM 11 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Am) (o := L) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterMapM`, idx 13: n = L, o = Mo (map counts 1; lawful lift), it = [0], f = none: the left fold has no element to map ForInStep.yield over, the right one has one
theorem Iter.foldM_filterMapM.h13 : ¬ drop0% Std.Iter.foldM_filterMapM 13 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Mo) (f := fun _ => pure none) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterMapM`, idx 19: n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value
theorem Iter.foldM_filterMapM.h19 : ¬ drop0% Std.Iter.foldM_filterMapM 19 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_mapWithPostcondition`, idx 20: n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value
theorem Iter.foldM_mapWithPostcondition.h20 : ¬ drop0% Std.Iter.foldM_mapWithPostcondition 20 := fun h => by
  have := h (m := Id) (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Lc) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_mapM`, idx 11: n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches
theorem Iter.foldM_mapM.h11 : ¬ drop0% Std.Iter.foldM_mapM 11 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Am) (o := L) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_mapM`, idx 19: n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value
theorem Iter.foldM_mapM.h19 : ¬ drop0% Std.Iter.foldM_mapM 19 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := L) (o := Lc) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterWithPostcondition`, idx 10: n = L, o = Mo (map counts 1; lawful lift), it = [0], f = false: the left fold has no element to map ForInStep.yield over, the right one has one
theorem Iter.foldM_filterWithPostcondition.h10 : ¬ drop0% Std.Iter.foldM_filterWithPostcondition 10 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Mo) (f := fun _ => pure (.up false)) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterWithPostcondition`, idx 16: n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value
theorem Iter.foldM_filterWithPostcondition.h16 : ¬ drop0% Std.Iter.foldM_filterWithPostcondition 16 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterM`, idx 10: n = Am (lawful, attach counts 1), o = L, it = [0]: only the left side attaches
theorem Iter.foldM_filterM.h10 : ¬ drop0% Std.Iter.foldM_filterM 10 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := Am) (o := L) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterM`, idx 12: n = L, o = Mo (map counts 1; lawful lift), it = [0], f = false: the left fold has no element to map ForInStep.yield over, the right one has one
theorem Iter.foldM_filterM.h12 : ¬ drop0% Std.Iter.foldM_filterM 12 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Mo) (f := fun _ => pure (.up false)) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterM`, idx 18: n = L, o = Lc (the lift counts 1), it = [0]: the left side lifts two steps, the right side one value
theorem Iter.foldM_filterM.h18 : ¬ drop0% Std.Iter.foldM_filterM 18 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := L) (o := Lc) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filterMap`, idx 8: n = Bm (bind counts 1), it = [0], f = none: the left fold never calls its body, the right one does
theorem Iter.foldM_filterMap.h8 : ¬ drop0% Std.Iter.foldM_filterMap 8 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Bm) (f := fun _ => none) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_filter`, idx 7: n = Bm (bind counts 1), it = [0], f = false: the left fold never calls its body, the right one does
theorem Iter.foldM_filter.h7 : ¬ drop0% Std.Iter.foldM_filter 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := Bm) (f := fun _ => false) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.fold_filterMapWithPostcondition`, idx 8: n = Mo (map counts 1), it = [0]: the right side maps twice ((f b).run, ForInStep.yield <$> _), the left side never
theorem Iter.fold_filterMapWithPostcondition.h8 : ¬ drop0% Std.Iter.fold_filterMapWithPostcondition 8 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Mo) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.fold_filterMapM`, idx 9: n = Mm (map counts 1, attach -1), it = [0]: the left side attaches (-1), the right side maps (ForInStep.yield <$> _, +1)
theorem Iter.fold_filterMapM.h9 : ¬ drop0% Std.Iter.fold_filterMapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Mm) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.fold_filterMapM`, idx 10: n = Am (lawful, attach counts 1), it = [0]: only the left side attaches
theorem Iter.fold_filterMapM.h10 : ¬ drop0% Std.Iter.fold_filterMapM 10 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Am) (f := fun x => pure (some x)) (δ := Nat) (init := 0) (g := fun d _ => d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.fold_mapWithPostcondition`, idx 8: n = Mo (map counts 1), it = [0]: the right side maps twice, the left side once
theorem Iter.fold_mapWithPostcondition.h8 : ¬ drop0% Std.Iter.fold_mapWithPostcondition 8 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Mo) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.fold_mapM`, idx 9: n = Mm (map counts 1, attach -1), it = [0]: the left side attaches and maps (0), the right side maps once (+1)
theorem Iter.fold_mapM.h9 : ¬ drop0% Std.Iter.fold_mapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Mm) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.fold_mapM`, idx 10: n = Am (lawful, attach counts 1), it = [0]: only the left side attaches
theorem Iter.fold_mapM.h10 : ¬ drop0% Std.Iter.fold_mapM 10 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := Am) (f := pure) (δ := Nat) (init := 0) (g := fun d _ => d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.fold_filterWithPostcondition`, idx 7: n = Mo (map counts 1), it = [0]: the right side maps twice, the left side once
theorem Iter.fold_filterWithPostcondition.h7 : ¬ drop0% Std.Iter.fold_filterWithPostcondition 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := Mo) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.fold_filterM`, idx 8: n = Mm (map counts 1, attach -1), it = [0]: the left side attaches and maps (0), the right side maps once (+1)
theorem Iter.fold_filterM.h8 : ¬ drop0% Std.Iter.fold_filterM 8 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := Mm) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.fold_filterM`, idx 9: n = Am (lawful, attach counts 1), it = [0]: only the left side attaches
theorem Iter.fold_filterM.h9 : ¬ drop0% Std.Iter.fold_filterM 9 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := Am) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.anyM_filterMapM`, idx 8: m = Bm (bind counts 1, trivial attach), it = [0]: the right side binds f x once more
theorem Iter.anyM_filterMapM.h8 : ¬ drop0% Std.Iter.anyM_filterMapM 8 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Bm) (f := fun x => pure (some x)) (p := fun _ => pure (.up false))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.anyM_filterMapM`, idx 9: m = Dm (lawful, attach x counts x twice), it = [0], f counts 1: the left side attaches f 0 (2), the right side attaches pure 0 and runs f 0 (1)
theorem Iter.anyM_filterMapM.h9 : ¬ drop0% Std.Iter.anyM_filterMapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Dm) (f := fun x => ⟨1, some x⟩) (p := fun _ => pure (.up false))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.anyM_eq_anyM_mapM_pure`, idx 7: m = Mm (map counts 1, attach -1), it = [0]: the right side maps ULift.up/ULift.down around the loop
theorem Iter.anyM_eq_anyM_mapM_pure.h7 : ¬ drop0% Std.Iter.anyM_eq_anyM_mapM_pure 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Mm) (p := fun _ => pure false)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.anyM_eq_anyM_mapM_pure`, idx 8: m = Am (lawful, attach counts 1), it = [0]: only the right side attaches (mapM pure)
theorem Iter.anyM_eq_anyM_mapM_pure.h8 : ¬ drop0% Std.Iter.anyM_eq_anyM_mapM_pure 8 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Am) (p := fun _ => pure false)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.anyM_mapM`, idx 8: m = Bm (bind counts 1, trivial attach), it = [0]: the right side binds f x once more
theorem Iter.anyM_mapM.h8 : ¬ drop0% Std.Iter.anyM_mapM 8 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Bm) (f := pure) (p := fun _ => pure (.up false))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.anyM_mapM`, idx 9: m = Dm (lawful, attach x counts x twice), it = [0], f counts 1: the left side attaches f 0 (2), the right side attaches pure 0 and runs f 0 (1)
theorem Iter.anyM_mapM.h9 : ¬ drop0% Std.Iter.anyM_mapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Dm) (f := fun x => ⟨1, x⟩) (p := fun _ => pure (.up false))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.anyM_filterM`, idx 7: m = Bm (bind counts 1, trivial attach), it = [0]: the right side binds f x once more
theorem Iter.anyM_filterM.h7 : ¬ drop0% Std.Iter.anyM_filterM 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (f := fun _ => pure (.up true)) (p := fun _ => pure (.up false))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.anyM_filterM`, idx 8: m = Dm (lawful, attach x counts x twice), it = [0], f counts 1: the left side attaches f 0 (2), the right side attaches pure 0 and runs f 0 (1)
theorem Iter.anyM_filterM.h8 : ¬ drop0% Std.Iter.anyM_filterM 8 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Dm) (f := fun _ => ⟨1, .up true⟩) (p := fun _ => pure (.up false))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.anyM_filterMap`, idx 8: m = Bm (bind counts 1), it = [0], f = none: the left loop never calls its body, the right one does
theorem Iter.anyM_filterMap.h8 : ¬ drop0% Std.Iter.anyM_filterMap 8 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Bm) (f := fun _ => none) (p := fun _ => pure false)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.anyM_filter`, idx 7: m = Bm (bind counts 1), it = [0], f = false: the left loop never calls its body, the right one does
theorem Iter.anyM_filter.h7 : ¬ drop0% Std.Iter.anyM_filter 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (f := fun _ => false) (p := fun _ => pure false)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.any_filterMapM`, idx 9: m = Bm (bind counts 1, trivial attach), it = [0]: the right side binds f x once more
theorem Iter.any_filterMapM.h9 : ¬ drop0% Std.Iter.any_filterMapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Bm) (f := fun x => pure (some x)) (p := fun _ => false)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.any_filterMapM`, idx 10: m = Dm (lawful, attach x counts x twice), it = [0], f counts 1: the left side attaches f 0 (2), the right side attaches pure 0 and runs f 0 (1)
theorem Iter.any_filterMapM.h10 : ¬ drop0% Std.Iter.any_filterMapM 10 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Dm) (f := fun x => ⟨1, some x⟩) (p := fun _ => false)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.any_mapM`, idx 9: m = Mm (map counts 1, attach -1), it = [0]: the left side attaches and maps (0), the right side maps once more (<$> f x)
theorem Iter.any_mapM.h9 : ¬ drop0% Std.Iter.any_mapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Mm) (f := pure) (p := fun _ => false)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.any_mapM`, idx 10: m = Dm (lawful, attach x counts x twice), it = [0], f counts 1: the left side attaches f 0 (2), the right side attaches pure 0 and runs f 0 (1)
theorem Iter.any_mapM.h10 : ¬ drop0% Std.Iter.any_mapM 10 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Dm) (f := fun x => ⟨1, x⟩) (p := fun _ => false)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.any_filterM`, idx 8: m = Bm (bind counts 1, trivial attach), it = [0]: the right side binds f x once more
theorem Iter.any_filterM.h8 : ¬ drop0% Std.Iter.any_filterM 8 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (f := fun _ => pure (.up true)) (p := fun _ => false)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.any_filterM`, idx 9: m = Dm (lawful, attach x counts x twice), it = [0], f counts 1: the left side attaches f 0 (2), the right side attaches pure 0 and runs f 0 (1)
theorem Iter.any_filterM.h9 : ¬ drop0% Std.Iter.any_filterM 9 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Dm) (f := fun _ => ⟨1, .up true⟩) (p := fun _ => false)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.allM_filterMapM`, idx 8: m = Bm (bind counts 1, trivial attach), it = [0]: the right side binds f x once more
theorem Iter.allM_filterMapM.h8 : ¬ drop0% Std.Iter.allM_filterMapM 8 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Bm) (f := fun x => pure (some x)) (p := fun _ => pure (.up true))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.allM_filterMapM`, idx 9: m = Dm (lawful, attach x counts x twice), it = [0], f counts 1: the left side attaches f 0 (2), the right side attaches pure 0 and runs f 0 (1)
theorem Iter.allM_filterMapM.h9 : ¬ drop0% Std.Iter.allM_filterMapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Dm) (f := fun x => ⟨1, some x⟩) (p := fun _ => pure (.up true))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.allM_eq_allM_mapM_pure`, idx 7: m = Mm (map counts 1, attach -1), it = [0]: the right side maps ULift.up/ULift.down around the loop
theorem Iter.allM_eq_allM_mapM_pure.h7 : ¬ drop0% Std.Iter.allM_eq_allM_mapM_pure 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Mm) (p := fun _ => pure true)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.allM_eq_allM_mapM_pure`, idx 8: m = Am (lawful, attach counts 1), it = [0]: only the right side attaches (mapM pure)
theorem Iter.allM_eq_allM_mapM_pure.h8 : ¬ drop0% Std.Iter.allM_eq_allM_mapM_pure 8 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Am) (p := fun _ => pure true)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.allM_mapM`, idx 8: m = Bm (bind counts 1, trivial attach), it = [0]: the right side binds f x once more
theorem Iter.allM_mapM.h8 : ¬ drop0% Std.Iter.allM_mapM 8 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Bm) (f := pure) (p := fun _ => pure (.up true))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.allM_mapM`, idx 9: m = Dm (lawful, attach x counts x twice), it = [0], f counts 1: the left side attaches f 0 (2), the right side attaches pure 0 and runs f 0 (1)
theorem Iter.allM_mapM.h9 : ¬ drop0% Std.Iter.allM_mapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Dm) (f := fun x => ⟨1, x⟩) (p := fun _ => pure (.up true))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.allM_filterM`, idx 7: m = Bm (bind counts 1, trivial attach), it = [0]: the right side binds f x once more
theorem Iter.allM_filterM.h7 : ¬ drop0% Std.Iter.allM_filterM 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (f := fun _ => pure (.up true)) (p := fun _ => pure (.up true))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.allM_filterM`, idx 8: m = Dm (lawful, attach x counts x twice), it = [0], f counts 1: the left side attaches f 0 (2), the right side attaches pure 0 and runs f 0 (1)
theorem Iter.allM_filterM.h8 : ¬ drop0% Std.Iter.allM_filterM 8 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Dm) (f := fun _ => ⟨1, .up true⟩) (p := fun _ => pure (.up true))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.allM_filterMap`, idx 8: m = Bm (bind counts 1), it = [0], f = none: the left loop never calls its body, the right one does
theorem Iter.allM_filterMap.h8 : ¬ drop0% Std.Iter.allM_filterMap 8 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Bm) (f := fun _ => none) (p := fun _ => pure true)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.allM_filter`, idx 7: m = Bm (bind counts 1), it = [0], f = false: the left loop never calls its body, the right one does
theorem Iter.allM_filter.h7 : ¬ drop0% Std.Iter.allM_filter 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (f := fun _ => false) (p := fun _ => pure true)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.all_filterMapM`, idx 9: m = Bm (bind counts 1, trivial attach), it = [0]: the right side binds f x once more
theorem Iter.all_filterMapM.h9 : ¬ drop0% Std.Iter.all_filterMapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Bm) (f := fun x => pure (some x)) (p := fun _ => true)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.all_filterMapM`, idx 10: m = Dm (lawful, attach x counts x twice), it = [0], f counts 1: the left side attaches f 0 (2), the right side attaches pure 0 and runs f 0 (1)
theorem Iter.all_filterMapM.h10 : ¬ drop0% Std.Iter.all_filterMapM 10 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Dm) (f := fun x => ⟨1, some x⟩) (p := fun _ => true)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.all_mapM`, idx 9: m = Mm (map counts 1, attach -1), it = [0]: the left side attaches and maps (0), the right side maps once more (<$> f x)
theorem Iter.all_mapM.h9 : ¬ drop0% Std.Iter.all_mapM 9 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Mm) (f := pure) (p := fun _ => true)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.all_mapM`, idx 10: m = Dm (lawful, attach x counts x twice), it = [0], f counts 1: the left side attaches f 0 (2), the right side attaches pure 0 and runs f 0 (1)
theorem Iter.all_mapM.h10 : ¬ drop0% Std.Iter.all_mapM 10 := fun h => by
  have := h (α := CD) (β := Nat) (β' := Nat) (it := ci 1) (m := Dm) (f := fun x => ⟨1, x⟩) (p := fun _ => true)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.all_filterM`, idx 8: m = Bm (bind counts 1, trivial attach), it = [0]: the right side binds f x once more
theorem Iter.all_filterM.h8 : ¬ drop0% Std.Iter.all_filterM 8 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (f := fun _ => pure (.up true)) (p := fun _ => true)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.all_filterM`, idx 9: m = Dm (lawful, attach x counts x twice), it = [0], f counts 1: the left side attaches f 0 (2), the right side attaches pure 0 and runs f 0 (1)
theorem Iter.all_filterM.h9 : ¬ drop0% Std.Iter.all_filterM 9 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Dm) (f := fun _ => ⟨1, .up true⟩) (p := fun _ => true)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn'_eq_forIn'_toIterM`, idx 6: m = Bm (bind counts 1), it empty: the IterM loop binds the lifted step, the Iter loop applies its continuation
theorem Iter.forIn'_eq_forIn'_toIterM.h6 : ¬ drop0% Std.Iter.forIn'_eq_forIn'_toIterM 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 0) (m := Bm) (γ := Nat) (init := 0) (f := fun _ _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_eq_forIn_toIterM`, idx 6: m = Bm (bind counts 1), it empty: the IterM loop binds the lifted step, the Iter loop applies its continuation
theorem Iter.forIn_eq_forIn_toIterM.h6 : ¬ drop0% Std.Iter.forIn_eq_forIn_toIterM 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 0) (m := Bm) (γ := Nat) (init := 0) (f := fun _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn'_eq_match_step`, idx 6: m = Bm (bind counts 1), it = [0]: the loop binds f and its result wrapper (2), the unfolded right side binds f once
theorem Iter.forIn'_eq_match_step.h6 : ¬ drop0% Std.Iter.forIn'_eq_match_step 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (γ := Nat) (init := 0) (f := fun _ _ acc => pure (.yield acc))
  rw [CD.stepS'] at this
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_eq_match_step`, idx 6: m = Bm (bind counts 1), it = [0]: the loop binds f and its result wrapper (2), the unfolded right side binds f once
theorem Iter.forIn_eq_match_step.h6 : ¬ drop0% Std.Iter.forIn_eq_match_step 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (γ := Nat) (init := 0) (f := fun _ acc => pure (.yield acc))
  rw [CD.stepS'] at this
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_eq_foldM_toIterM`, idx 6: m = Bm (bind counts 1), it empty: the IterM fold binds the lifted step, the Iter fold applies its continuation
theorem Iter.foldM_eq_foldM_toIterM.h6 : ¬ drop0% Std.Iter.foldM_eq_foldM_toIterM 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 0) (m := Bm) (γ := Nat) (init := 0) (f := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn_yield_eq_foldM`, idx 8: m = Mo (map counts 1), it = [0]: the fold maps twice per element, the loop once
theorem Iter.forIn_yield_eq_foldM.h8 : ¬ drop0% Std.Iter.forIn_yield_eq_foldM 8 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Mo) (γ := Nat) (δ := Nat) (init := 0) (f := fun _ _ => pure 0) (g := fun c _ _ => c)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldM_eq_match_step`, idx 7: m = Bm (bind counts 1), it = [0]: the fold binds twice per element, the unfolded right side once
theorem Iter.foldM_eq_match_step.h7 : ¬ drop0% Std.Iter.foldM_eq_match_step 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (γ := Nat) (init := 0) (f := fun d _ => pure d)
  rw [CD.stepS'] at this
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.foldlM_toList`, idx 7: m = Bm (bind counts 1), it = [0]: List.foldlM binds once, the iterator fold twice
theorem Iter.foldlM_toList.h7 : ¬ drop0% Std.Iter.foldlM_toList 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (γ := Nat) (init := 0) (f := fun d _ => pure d)
  rw [toList1] at this
  have := congrArg W.c this
  evl this
  lfin

-- `Std.Iter.anyM_eq_match_step`, idx 6: m = Bm (bind counts 1), it = [0]: the loop binds three times per element, the unfolded right side once
theorem Iter.anyM_eq_match_step.h6 : ¬ drop0% Std.Iter.anyM_eq_match_step 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (p := fun _ => pure false)
  rw [CD.stepS] at this
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.allM_eq_match_step`, idx 6: m = Bm (bind counts 1), it = [0]: the loop binds three times per element, the unfolded right side once
theorem Iter.allM_eq_match_step.h6 : ¬ drop0% Std.Iter.allM_eq_match_step 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (p := fun _ => pure true)
  rw [CD.stepS] at this
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.anyM_toList`, idx 6: m = Bm (bind counts 1), it = [0]: List.anyM binds once, the iterator loop three times
theorem Iter.anyM_toList.h6 : ¬ drop0% Std.Iter.anyM_toList 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (p := fun _ => pure false)
  rw [toList1] at this
  have := congrArg W.c this
  evl this
  lfin

-- `Std.Iter.allM_eq_not_anyM_not`, idx 6: m = Mo (map counts 1), it = [0]: the right side maps twice more
theorem Iter.allM_eq_not_anyM_not.h6 : ¬ drop0% Std.Iter.allM_eq_not_anyM_not 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Mo) (p := fun _ => pure true)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.findSomeM?_eq_match_step`, idx 7: m = Bm (bind counts 1), it = [0]: the loop binds three times per element, the unfolded right side once
theorem Iter.findSomeM?_eq_match_step.h7 : ¬ drop0% Std.Iter.findSomeM?_eq_match_step 7 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (m := Bm) (f := fun _ => pure none)
  rw [CD.stepS] at this
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.findSomeM?_toList`, idx 7: m = Bm (bind counts 1), it = [0]: List.findSomeM? binds once, the iterator loop three times
theorem Iter.findSomeM?_toList.h7 : ¬ drop0% Std.Iter.findSomeM?_toList 7 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (m := Bm) (f := fun _ => pure none)
  rw [toList1] at this
  have := congrArg W.c this
  evl this
  lfin

-- `Std.Iter.findSomeM?_pure`, idx 8: m = Bm (bind counts 1), it = [0]: the monadic loop binds, the right side is pure _
theorem Iter.findSomeM?_pure.h8 : ¬ drop0% Std.Iter.findSomeM?_pure 8 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (m := Bm) (f := fun _ => none)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.findM?_eq_match_step`, idx 6: m = Bm (bind counts 1), it = [0]: the loop binds three times per element, the unfolded right side once
theorem Iter.findM?_eq_match_step.h6 : ¬ drop0% Std.Iter.findM?_eq_match_step 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (f := fun _ => pure (.up false))
  rw [CD.stepS] at this
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.findM?_toList`, idx 6: m = Bm (bind counts 1), it = [0]: List.findM? binds once, the iterator loop three times
theorem Iter.findM?_toList.h6 : ¬ drop0% Std.Iter.findM?_toList 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (f := fun _ => pure false)
  rw [toList1] at this
  have := congrArg W.c this
  evl this
  lfin

-- `Std.Iter.findM?_eq_findM?_toList`, idx 6: m = Bm (bind counts 1), it = [0]: List.findM? binds once, the iterator loop three times
theorem Iter.findM?_eq_findM?_toList.h6 : ¬ drop0% Std.Iter.findM?_eq_findM?_toList 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (f := fun _ => pure (.up false))
  rw [toList1] at this
  have := congrArg W.c this
  evl this
  lfin

-- `Std.Iter.findM?_pure`, idx 7: m = Bm (bind counts 1), it = [0]: the monadic loop binds, the right side is pure _
theorem Iter.findM?_pure.h7 : ¬ drop0% Std.Iter.findM?_pure 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (f := fun _ => .up false)
  have := congrArg W.c this
  evl this
  omega

-- `Std.Iter.forIn'_toList`, idx 6: m = Bm (bind counts 1), it = [0]: List.forIn' binds once per element, the iterator loop twice
theorem Iter.forIn'_toList.h6 : ¬ drop0% Std.Iter.forIn'_toList 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (γ := Nat) (init := 0) (f := fun _ _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  cfin this

-- `Std.Iter.forIn'_toArray`, idx 6: m = Bm (bind counts 1), it = [0]: Array.forIn' binds once per element, the iterator loop twice
theorem Iter.forIn'_toArray.h6 : ¬ drop0% Std.Iter.forIn'_toArray 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (γ := Nat) (init := 0) (f := fun _ _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  cfin this

-- `Std.Iter.forIn'_eq_forIn'_toList`, idx 6: m = Bm (bind counts 1), it = [0]: List.forIn' binds once per element, the iterator loop twice
theorem Iter.forIn'_eq_forIn'_toList.h6 : ¬ drop0% Std.Iter.forIn'_eq_forIn'_toList 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (γ := Nat) (init := 0) (f := fun _ _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  cfin this

-- `Std.Iter.forIn'_eq_forIn'_toArray`, idx 6: m = Bm (bind counts 1), it = [0]: Array.forIn' binds once per element, the iterator loop twice
theorem Iter.forIn'_eq_forIn'_toArray.h6 : ¬ drop0% Std.Iter.forIn'_eq_forIn'_toArray 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (γ := Nat) (init := 0) (f := fun _ _ acc => pure (.yield acc))
  have := congrArg W.c this
  evl this
  cfin this

-- `Std.Iter.foldlM_toArray`, idx 7: m = Bm (bind counts 1), it = [0]: Array.foldlM binds once, the iterator fold twice
theorem Iter.foldlM_toArray.h7 : ¬ drop0% Std.Iter.foldlM_toArray 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (γ := Nat) (init := 0) (f := fun d _ => pure d)
  have := congrArg W.c this
  evl this
  cfin this

-- `Std.Iter.anyM_toArray`, idx 6: m = Bm (bind counts 1), it = [0]: Array.anyM binds once, the iterator loop three times
theorem Iter.anyM_toArray.h6 : ¬ drop0% Std.Iter.anyM_toArray 6 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (m := Bm) (p := fun _ => pure false)
  have := congrArg W.c this
  evl this
  cfin this

-- `Std.Iter.toList_mapWithPostcondition_mapWithPostcondition`, idx 9: m = Mo (map counts 1), n = L, lawful lift Mo → L, it = [0]: the inner mapWithPostcondition maps in m (lifted to n), the right side never maps in m
theorem Iter.toList_mapWithPostcondition_mapWithPostcondition.h9 : ¬ drop0% Std.Iter.toList_mapWithPostcondition_mapWithPostcondition 9 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (δ := Nat) (it := ci 1) (m := Mo) (n := L) (f := pure) (g := pure)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toArray_mapWithPostcondition_mapWithPostcondition`, idx 9: m = Mo (map counts 1), n = L, lawful lift Mo → L, it = [0]: the inner mapWithPostcondition maps in m (lifted to n), the right side never maps in m
theorem Iter.toArray_mapWithPostcondition_mapWithPostcondition.h9 : ¬ drop0% Std.Iter.toArray_mapWithPostcondition_mapWithPostcondition 9 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (δ := Nat) (it := ci 1) (m := Mo) (n := L) (f := pure) (g := pure)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toList_flatMapM`, idx 7: m = Bm (bind counts 1, trivial attach), it₁ empty: the flattening iterator binds once more per step
theorem Iter.toList_flatMapM.h7 : ¬ drop0% Std.Iter.toList_flatMapM 7 := fun h => by
  have := h (α := CD) (α₂ := CD) (β := Nat) (γ := Nat) (m := Bm) (f := fun _ => pure ⟨⟨0⟩⟩) (it₁ := ci 0)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toList_flatMapM`, idx 8: m = Dm (lawful, attach x counts x twice), it₁ = [0], f counts 1 and returns TK 1 (each step counts 1, toList counts 2): the left side attaches only f 0 (2 + 2), the right side attaches f 0 >>= toList (2 * 3)
theorem Iter.toList_flatMapM.h8 : ¬ drop0% Std.Iter.toList_flatMapM 8 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (m := Dm) (α₂ := TK) (f := fun _ => (⟨1, ⟨⟨1⟩⟩⟩ : Dm _)) (it₁ := ci 1)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toList_flatMapAfterM`, idx 7: m = Bm (bind counts 1, trivial attach), it₁ empty: the flattening iterator binds once more per step
theorem Iter.toList_flatMapAfterM.h7 : ¬ drop0% Std.Iter.toList_flatMapAfterM 7 := fun h => by
  have := h (α := CD) (α₂ := CD) (β := Nat) (γ := Nat) (m := Bm) (f := fun _ => pure ⟨⟨0⟩⟩) (it₁ := ci 0) (it₂ := none)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toList_flatMapAfterM`, idx 8: m = Dm (lawful, attach x counts x twice), it₁ = [0], f counts 1 and returns TK 1 (each step counts 1, toList counts 2): the left side attaches only f 0 (2 + 2), the right side attaches f 0 >>= toList (2 * 3)
theorem Iter.toList_flatMapAfterM.h8 : ¬ drop0% Std.Iter.toList_flatMapAfterM 8 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (m := Dm) (α₂ := TK) (f := fun _ => (⟨1, ⟨⟨1⟩⟩⟩ : Dm _)) (it₁ := ci 1) (it₂ := none)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toArray_flatMapM`, idx 7: m = Bm (bind counts 1, trivial attach), it₁ empty: the flattening iterator binds once more per step
theorem Iter.toArray_flatMapM.h7 : ¬ drop0% Std.Iter.toArray_flatMapM 7 := fun h => by
  have := h (α := CD) (α₂ := CD) (β := Nat) (γ := Nat) (m := Bm) (f := fun _ => pure ⟨⟨0⟩⟩) (it₁ := ci 0)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toArray_flatMapM`, idx 8: m = Dm (lawful, attach x counts x twice), it₁ = [0], f counts 1 and returns TK 1 (each step counts 1, toList counts 2): the left side attaches only f 0 (2 + 2), the right side attaches f 0 >>= toList (2 * 3)
theorem Iter.toArray_flatMapM.h8 : ¬ drop0% Std.Iter.toArray_flatMapM 8 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (m := Dm) (α₂ := TK) (f := fun _ => (⟨1, ⟨⟨1⟩⟩⟩ : Dm _)) (it₁ := ci 1)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toArray_flatMapAfterM`, idx 7: m = Bm (bind counts 1, trivial attach), it₁ empty: the flattening iterator binds once more per step
theorem Iter.toArray_flatMapAfterM.h7 : ¬ drop0% Std.Iter.toArray_flatMapAfterM 7 := fun h => by
  have := h (α := CD) (α₂ := CD) (β := Nat) (γ := Nat) (m := Bm) (f := fun _ => pure ⟨⟨0⟩⟩) (it₁ := ci 0) (it₂ := none)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.toArray_flatMapAfterM`, idx 8: m = Dm (lawful, attach x counts x twice), it₁ = [0], f counts 1 and returns TK 1 (each step counts 1, toList counts 2): the left side attaches only f 0 (2 + 2), the right side attaches f 0 >>= toList (2 * 3)
theorem Iter.toArray_flatMapAfterM.h8 : ¬ drop0% Std.Iter.toArray_flatMapAfterM 8 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (m := Dm) (α₂ := TK) (f := fun _ => (⟨1, ⟨⟨1⟩⟩⟩ : Dm _)) (it₁ := ci 1) (it₂ := none)
  have := congrArg W.c this
  evh this
  omega

-- `Std.Iter.forIn_filterMapWithPostcondition`, idx 10: n = L (lawful), o = U (bind adds x.c * (f x.v).d ^ 2 to a second counter d: not associative; lawful lift L → U), it = [1, 0], f counts 1 in c, g counts 1 in d: the two loops associate the binds of f's lifted effect and g differently
theorem Iter.forIn_filterMapWithPostcondition.h10 : ¬ drop0% Std.Iter.forIn_filterMapWithPostcondition 10 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 2) (n := L) (o := U) (f := fun x => ⟨fun _ => True, ⟨1, ⟨some x, trivial⟩⟩⟩) (γ := Nat) (init := 0) (g := fun _ acc => (⟨0, 1, .yield acc⟩ : U _))
  have := congrArg U.d this
  evl this
  revert this; decide

-- `Std.Iter.forIn_filterMapM`, idx 10: n = L (lawful), o = U (bind adds x.c * (f x.v).d ^ 2 to a second counter d: not associative; lawful lift L → U), it = [1, 0], f counts 1 in c, g counts 1 in d: the two loops associate the binds of f's lifted effect and g differently
theorem Iter.forIn_filterMapM.h10 : ¬ drop0% Std.Iter.forIn_filterMapM 10 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 2) (n := L) (o := U) (f := fun x => (⟨1, some x⟩ : L _)) (γ := Nat) (init := 0) (g := fun _ acc => (⟨0, 1, .yield acc⟩ : U _))
  have := congrArg U.d this
  evl this
  revert this; decide

-- `Std.Iter.forIn_mapWithPostcondition`, idx 10: n = L (lawful), o = U (bind adds x.c * (f x.v).d ^ 2 to a second counter d: not associative; lawful lift L → U), it = [1, 0], f counts 1 in c, g counts 1 in d: the two loops associate the binds of f's lifted effect and g differently
theorem Iter.forIn_mapWithPostcondition.h10 : ¬ drop0% Std.Iter.forIn_mapWithPostcondition 10 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 2) (n := L) (o := U) (f := fun x => ⟨fun _ => True, ⟨1, ⟨x, trivial⟩⟩⟩) (γ := Nat) (init := 0) (g := fun _ acc => (⟨0, 1, .yield acc⟩ : U _))
  have := congrArg U.d this
  evl this
  revert this; decide

-- `Std.Iter.forIn_mapM`, idx 10: n = L (lawful), o = U (bind adds x.c * (f x.v).d ^ 2 to a second counter d: not associative; lawful lift L → U), it = [1, 0], f counts 1 in c, g counts 1 in d: the two loops associate the binds of f's lifted effect and g differently
theorem Iter.forIn_mapM.h10 : ¬ drop0% Std.Iter.forIn_mapM 10 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 2) (n := L) (o := U) (f := fun x => (⟨1, x⟩ : L _)) (γ := Nat) (init := 0) (g := fun _ acc => (⟨0, 1, .yield acc⟩ : U _))
  have := congrArg U.d this
  evl this
  revert this; decide

-- `Std.Iter.forIn_filterWithPostcondition`, idx 9: n = L (lawful), o = U (bind adds x.c * (f x.v).d ^ 2 to a second counter d: not associative; lawful lift L → U), it = [1, 0], f counts 1 in c, g counts 1 in d: the two loops associate the binds of f's lifted effect and g differently
theorem Iter.forIn_filterWithPostcondition.h9 : ¬ drop0% Std.Iter.forIn_filterWithPostcondition 9 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 2) (n := L) (o := U) (f := fun _ => ⟨fun _ => True, ⟨1, ⟨.up true, trivial⟩⟩⟩) (γ := Nat) (init := 0) (g := fun _ acc => (⟨0, 1, .yield acc⟩ : U _))
  have := congrArg U.d this
  evl this
  revert this; decide

-- `Std.Iter.forIn_filterM`, idx 9: n = L (lawful), o = U (bind adds x.c * (f x.v).d ^ 2 to a second counter d: not associative; lawful lift L → U), it = [1, 0], f counts 1 in c, g counts 1 in d: the two loops associate the binds of f's lifted effect and g differently
theorem Iter.forIn_filterM.h9 : ¬ drop0% Std.Iter.forIn_filterM 9 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 2) (n := L) (o := U) (f := fun _ => (⟨1, .up true⟩ : L _)) (γ := Nat) (init := 0) (g := fun _ acc => (⟨0, 1, .yield acc⟩ : U _))
  have := congrArg U.d this
  evl this
  revert this; decide

-- `Std.Iter.foldM_mapWithPostcondition`, idx 14: n = L (lawful), o = U (bind adds x.c * (f x.v).d ^ 2 to a second counter d: not associative; lawful lift L → U), it = [1, 0], f counts 1 in c, g counts 1 in d: the two loops associate the binds of f's lifted effect and g differently
theorem Iter.foldM_mapWithPostcondition.h14 : ¬ drop0% Std.Iter.foldM_mapWithPostcondition 14 := fun h => by
  have := h (m := Id) (α := CD) (β := Nat) (γ := Nat) (it := ci 2) (n := L) (o := U) (f := fun x => ⟨fun _ => True, ⟨1, ⟨x, trivial⟩⟩⟩) (δ := Nat) (init := 0) (g := fun d _ => (⟨0, 1, d⟩ : U _))
  have := congrArg U.d this
  evl this
  revert this; decide

-- `Std.Iter.foldM_mapM`, idx 13: n = L (lawful), o = U (bind adds x.c * (f x.v).d ^ 2 to a second counter d: not associative; lawful lift L → U), it = [1, 0], f counts 1 in c, g counts 1 in d: the two loops associate the binds of f's lifted effect and g differently
theorem Iter.foldM_mapM.h13 : ¬ drop0% Std.Iter.foldM_mapM 13 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 2) (n := L) (o := U) (f := fun x => (⟨1, x⟩ : L _)) (δ := Nat) (init := 0) (g := fun d _ => (⟨0, 1, d⟩ : U _))
  have := congrArg U.d this
  evl this
  revert this; decide

-- `Std.Iter.forIn_mapWithPostcondition`, idx 8: n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip)
theorem Iter.forIn_mapWithPostcondition.h8 : ¬ drop0% Std.Iter.forIn_mapWithPostcondition 8 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun b => pure b) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Iter.forIn_mapM`, idx 8: n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip)
theorem Iter.forIn_mapM.h8 : ¬ drop0% Std.Iter.forIn_mapM 8 := fun h => by
  have := h (α := CD) (β := Nat) (β₂ := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun b => pure b) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Iter.forIn_filterWithPostcondition`, idx 7: n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip)
theorem Iter.forIn_filterWithPostcondition.h7 : ¬ drop0% Std.Iter.forIn_filterWithPostcondition 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Iter.forIn_filterM`, idx 7: n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip)
theorem Iter.forIn_filterM.h7 : ¬ drop0% Std.Iter.forIn_filterM 7 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun _ => pure (.up true)) (γ := Nat) (init := 0) (g := fun _ acc => pure (.yield acc))
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Iter.foldM_mapWithPostcondition`, idx 13: n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip)
theorem Iter.foldM_mapWithPostcondition.h13 : ¬ drop0% Std.Iter.foldM_mapWithPostcondition 13 := fun h => by
  have := h (m := Id) (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun b => pure b) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Iter.foldM_mapM`, idx 10: n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip)
theorem Iter.foldM_mapM.h10 : ¬ drop0% Std.Iter.foldM_mapM 10 := fun h => by
  have := h (α := CD) (β := Nat) (γ := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun b => pure b) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Iter.foldM_filterWithPostcondition`, idx 9: n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip)
theorem Iter.foldM_filterWithPostcondition.h9 : ¬ drop0% Std.Iter.foldM_filterWithPostcondition 9 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

-- `Std.Iter.foldM_filterM`, idx 9: n = SB (Bool writer after ItMonadMA's SM: lawful bind/pure, map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to the lawful Bool writer o = BW), it = [0]: the combinator maps into a subsingleton subtype of Option/β (flip), the right side maps into Nat/ULift Bool or not at all (no flip)
theorem Iter.foldM_filterM.h9 : ¬ drop0% Std.Iter.foldM_filterM 9 := fun h => by
  have := h (α := CD) (β := Nat) (it := ci 1) (n := SB) (o := BW) (f := fun _ => pure (.up true)) (δ := Nat) (init := 0) (g := fun d _ => pure d)
  have := congrArg BW.c this
  evl this
  exact absurd this (by decide)

end ItMonadIterHand
