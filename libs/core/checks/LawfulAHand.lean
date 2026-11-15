import Lean

/-!
Hand pass `LawfulA` (hand13): 89 hypotheses of 80 theorems in `Init.Control.Lawful.Basic`,
`Init.Control.Lawful.Instances`, `Init.Control.Basic`, `Init.Control.ExceptCps`,
`Init.Control.MonadAttach` and `Init.Control.State`: mostly `[LawfulFunctor/LawfulApplicative/LawfulMonad m]`
instance hypotheses, the class projections themselves, the premises of `LawfulMonad.mk'`, and the
premises of congruence/extensionality lemmas. For hypothesis `hᵢ` of theorem `T` each declaration
proves `¬T'` (necessary, `¬ drop0% T i`, universes set to `0`) or `T'` (removable, `drop% T i`).

88 necessary, 1 removable, 0 independent.

Reusable counterexamples (namespace `LawfulAHand`):
* `mkM p bd mp sc lc rc kc`: the monad `Nat × α` with `pure a = (p, a)`, `bind` combining counters by
  `bd`, `map` sending the counter through `mp`, and `seq`/`seqLeft`/`seqRight`/`mapConst` adding
  `sc`/`lc`/`rc`/`kc` to their default (bind-based) counters. Each model is its own type synonym:
  * `MC` (`map` adds one), `PM` (`pure` counts one), `AM` (`bind` gives `2a + b`, `map` doubles):
    non-lawful base monads for the functor/applicative/monad consequences and for the
    `ExceptT`/`OptionT`/`ReaderT`/`StateT`/`StateRefT'`/`ExceptCpsT` lemmas;
  * one model per `LawfulMonad.mk'` premise, satisfying all the other premises (tactic `law`):
    `FM` (`bind` forgets the first counter, `map` resets it: only `id_map` fails), `LP` (`bind`
    keeps the first counter: only `pure_bind`), `NA` (`a + b + a*b*b`: only `bind_assoc`), `KM`
    (`mapConst` +1), `LM` (`seqLeft` +1), `RM` (`seqRight` +1), `FN` (`bind` forgets, `map` keeps:
    only `bind_pure_comp`), `SM` (`seq` +1).
* `NE`: counter monad (`m α = Nat`) with empty `CanReturn`: a `LawfulMonadAttach`. `NT`: the same with
  `CanReturn` true (not lawful). `BA`: `Option` whose `attach` is `none` (not weakly lawful).
* `cnt% h` / `cntS% h at s`: the counter of both sides of an equation in a `Nat × _` model (of the
  value, resp. of `StateT.run _ s`); `decide` then shows the counters differ.

Removable (1): `[LawfulMonad m]` of `OptionT.run_seqRight`: `x *> y` is by definition
`x >>= fun _ => y`, and the law-free `OptionT.run_bind` gives exactly the right-hand side.

Run with the lean4 repo's stage1 binary: `lean checks/LawfulAHand.lean`.
-/

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
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option warn.classDefReducibility false

namespace LawfulAHand

/-- The monad `Nat × α` with tunable laws: `pure a = (p, a)`, `bind` combines counters by `bd`,
`map` sends the counter through `mp`, and `seq`/`seqLeft`/`seqRight`/`mapConst` add `sc`/`lc`/`rc`/`kc`
to their default (bind-based) counter. -/
def mkM (p : Nat) (bd : Nat → Nat → Nat) (mp : Nat → Nat) (sc lc rc kc : Nat) :
    Monad (fun α : Type => Nat × α) where
  pure a := (p, a)
  bind x f := (bd x.1 (f x.2).1, (f x.2).2)
  map f x := (mp x.1, f x.2)
  mapConst a x := (mp x.1 + kc, a)
  seq f x := (bd f.1 (mp (x ()).1) + sc, f.2 (x ()).2)
  seqLeft x y := (bd x.1 (bd (y ()).1 p) + lc, x.2)
  seqRight x y := (bd x.1 (y ()).1 + rc, (y ()).2)

/-- `map` adds one. -/
def MC (α : Type) : Type := Nat × α
instance : Monad MC := mkM 0 (· + ·) (· + 1) 0 0 0 0
/-- `pure` counts one. -/
def PM (α : Type) : Type := Nat × α
instance : Monad PM := mkM 1 (· + ·) (· + 1) 0 0 0 0
/-- `bind` combines counters by `2a + b`. -/
def AM (α : Type) : Type := Nat × α
instance : Monad AM := mkM 0 (fun a b => 2 * a + b) (fun a => 2 * a) 0 0 0 0
/-- lawful writer except `mapConst` adds one. -/
def KM (α : Type) : Type := Nat × α
instance : Monad KM := mkM 0 (· + ·) id 0 0 0 1
/-- lawful writer except `seq` adds one. -/
def SM (α : Type) : Type := Nat × α
instance : Monad SM := mkM 0 (· + ·) id 1 0 0 0
/-- lawful writer except `seqLeft` adds one. -/
def LM (α : Type) : Type := Nat × α
instance : Monad LM := mkM 0 (· + ·) id 0 1 0 0
/-- lawful writer except `seqRight` adds one. -/
def RM (α : Type) : Type := Nat × α
instance : Monad RM := mkM 0 (· + ·) id 0 0 1 0
/-- `bind` forgets the first counter, `map` resets it (so `bind_pure_comp` holds, `id_map` fails). -/
def FM (α : Type) : Type := Nat × α
instance : Monad FM := mkM 0 (fun _ b => b) (fun _ => 0) 0 0 0 0
/-- `bind` forgets the first counter, `map` keeps it (so `id_map` holds, `bind_pure_comp` fails). -/
def FN (α : Type) : Type := Nat × α
instance : Monad FN := mkM 0 (fun _ b => b) id 0 0 0 0
/-- `bind` keeps only the first counter: `pure` is a right but not a left unit. -/
def LP (α : Type) : Type := Nat × α
instance : Monad LP := mkM 0 (fun a _ => a) id 0 0 0 0
/-- `bind` combines counters by `a + b + a*b*b`: unital, not associative. -/
def NA (α : Type) : Type := Nat × α
instance : Monad NA := mkM 0 (fun a b => a + b + a * b * b) id 0 0 0 0

macro "cnt% " h:term : term => `(congrArg (fun z => (show Nat × _ from z).1) $h)
macro "cntS% " h:term " at " s:term : term => `(congrArg (fun z => (show Nat × _ from StateT.run z $s).1) $h)
/-- Proves the laws of the `mkM` models that hold (`rfl`, or `0 + n = n`, associativity of `+`). -/
macro "law" : tactic => `(tactic| (intros; first
  | rfl
  | exact Prod.ext (Nat.zero_add _) rfl
  | exact Prod.ext (Nat.add_assoc _ _ _) rfl
  | exact Prod.ext (show 0 + _ + 0 * _ * _ = _ by simp <;> rfl) rfl))

/-- A `Monad` whose values are counters (`m α = Nat`): `pure` gives 0, `bind` keeps its first argument,
`map` is free. Its `MonadAttach` has `CanReturn` empty and `attach` the identity, so it is lawful. -/
def NE (_ : Type) : Type := Nat
instance : Monad NE where
  pure _ := (0 : Nat)
  bind x _ := (show Nat from x)
  map _ x := (show Nat from x)
instance : MonadAttach NE where
  CanReturn _ _ := False
  attach x := (show Nat from x)
instance : LawfulMonadAttach NE where
  map_attach := rfl
  canReturn_map_imp h := h.elim

/-- Like `NE`, but every value can be returned (`CanReturn` true), so `canReturn_map_imp` fails. -/
def NT (_ : Type) : Type := Nat
instance : Monad NT where
  pure _ := (0 : Nat)
  bind x _ := (show Nat from x)
instance : MonadAttach NT where
  CanReturn _ _ := True
  attach x := (show Nat from x)

/-- `Option` (a lawful monad) whose `attach` always fails: not weakly lawful. -/
def BA (α : Type) : Type := Option α
instance : Monad BA := inferInstanceAs (Monad Option)
instance : MonadAttach BA where
  CanReturn _ _ := True
  attach _ := (none : Option _)

/-! ## Refutations: congruence and extensionality lemmas without their premise -/

-- `forIn'_eq_forIn`: over [0] in Id, f stops with .done 1 and g with .done 0.
theorem forIn'_eq_forIn_h10 : ¬ drop0% forIn'_eq_forIn 10 := fun h =>
  absurd (congrArg Id.run (@h Nat (List Nat) Id _ _ Nat [0] 0 (fun _ _ _ => pure (.done 1))
    (fun _ _ => pure (.done 0)))) (by decide)

-- `bind_congr`: some 0 >>= some ≠ some 0 >>= fun _ => none.
theorem bind_congr_h7 : ¬ drop0% bind_congr 7 := fun h =>
  absurd (@h Option Nat Nat _ (some 0) some (fun _ => none)) (by decide)

-- `map_congr`: two different constant maps on some 0.
theorem map_congr_h7 : ¬ drop0% map_congr 7 := fun h =>
  absurd (@h Option Nat Nat _ (some 0) (fun _ => 0) (fun _ => 1)) (by decide)

-- `Id.ext`: true ≠ false.
theorem Id_ext_h3 : ¬ drop0% Id.ext 3 := fun h => absurd (congrArg Id.run (@h Bool true false)) (by decide)

-- `ExceptT.ext`: none ≠ some (.ok 0) in ExceptT Nat Option Nat.
theorem ExceptT_ext_h5 : ¬ drop0% ExceptT.ext 5 := fun h =>
  absurd (congrArg (fun z => (ExceptT.run z).isSome)
    (@h Nat Option Nat (ExceptT.mk none) (ExceptT.mk (some (.ok 0))))) (by decide)

-- `OptionT.ext`: none ≠ some (some 0) in OptionT Option Nat.
theorem OptionT_ext_h4 : ¬ drop0% OptionT.ext 4 := fun h =>
  absurd (congrArg (fun z => (OptionT.run z).isSome)
    (@h Option Nat (OptionT.mk none) (OptionT.mk (some (some 0))))) (by decide)

-- `ReaderT.ext`: two different constant readers into Option.
theorem ReaderT_ext_h5 : ¬ drop0% ReaderT.ext 5 := fun h =>
  absurd (congrArg (fun z => (ReaderT.run z ()).isSome)
    (@h Unit Option Nat (fun _ => none) (fun _ => some 0))) (by decide)

-- `StateT.ext`: two different state transformers into Option.
theorem StateT_ext_h5 : ¬ drop0% StateT.ext 5 := fun h =>
  absurd (congrArg (fun z => (StateT.run z ()).isSome)
    (@h Unit Option Nat (fun _ => none) (fun s => some (0, s)))) (by decide)

-- `instSubsingletonStateM`: with σ = Bool, α = Unit the identity and a constant state update differ.
theorem instSubsingletonStateM_h2 : ¬ drop0% instSubsingletonStateM 2 := fun h =>
  absurd (congrArg (fun z => (Id.run (z false)).2)
    ((@h Bool Unit _).allEq (fun s => pure ((), s)) (fun _ => pure ((), true)))) (by decide)

-- `instSubsingletonStateM`: with σ = Unit, α = Bool two constant results differ.
theorem instSubsingletonStateM_h3 : ¬ drop0% instSubsingletonStateM 3 := fun h =>
  absurd (congrArg (fun z => (Id.run (z ())).1)
    ((@h Unit Bool _).allEq (fun s => pure (true, s)) (fun s => pure (false, s)))) (by decide)

/-! ## Refutations: functor/applicative/monad laws and their consequences -/

-- `LawfulFunctor.map_const`: KM's mapConst counts one more than map ∘ const.
theorem LawfulFunctor_map_const_h2 : ¬ drop0% LawfulFunctor.map_const 2 := fun h =>
  absurd (cnt% (congrFun (congrFun (@h KM inferInstance Nat Nat) 0) ((0 : Nat), 0))) (by decide)

-- `LawfulFunctor.id_map`: MC's map counts.
theorem LawfulFunctor_id_map_h2 : ¬ drop0% LawfulFunctor.id_map 2 := fun h =>
  absurd (cnt% (@h MC inferInstance Nat ((0 : Nat), 0))) (by decide)

-- `LawfulFunctor.comp_map`: one map versus two in MC.
theorem LawfulFunctor_comp_map_h2 : ¬ drop0% LawfulFunctor.comp_map 2 := fun h =>
  absurd (cnt% (@h MC inferInstance Nat Nat Nat id id ((0 : Nat), 0))) (by decide)

-- `id_map'`: MC.
theorem id_map'_h3 : ¬ drop0% id_map' 3 := fun h =>
  absurd (cnt% (@h MC Nat _ ((0 : Nat), 0))) (by decide)

-- `Functor.map_map`: MC.
theorem Functor_map_map_h5 : ¬ drop0% Functor.map_map 5 := fun h =>
  absurd (cnt% (@h MC Nat Nat Nat _ id id ((0 : Nat), 0))) (by decide)

-- `Functor.map_unit`: MC.
theorem Functor_map_unit_h2 : ¬ drop0% Functor.map_unit 2 := fun h =>
  absurd (cnt% (@h MC _ ((0 : Nat), PUnit.unit))) (by decide)

-- `LawfulApplicative.toLawfulFunctor`: MC is an applicative that is not a lawful functor.
theorem LawfulApplicative_toLawfulFunctor_h2 : ¬ drop0% LawfulApplicative.toLawfulFunctor 2 := fun h =>
  absurd (cnt% (@LawfulFunctor.id_map MC _ (@h MC inferInstance) Nat ((0 : Nat), 0))) (by decide)

-- `LawfulApplicative.seqLeft_eq`: MC (the right side maps).
theorem LawfulApplicative_seqLeft_eq_h2 : ¬ drop0% LawfulApplicative.seqLeft_eq 2 := fun h =>
  absurd (cnt% (@h MC inferInstance Nat Nat ((0 : Nat), 0) ((0 : Nat), 0))) (by decide)

-- `LawfulApplicative.seqRight_eq`: RM (seqRight counts).
theorem LawfulApplicative_seqRight_eq_h2 : ¬ drop0% LawfulApplicative.seqRight_eq 2 := fun h =>
  absurd (cnt% (@h RM inferInstance Nat Nat ((0 : Nat), 0) ((0 : Nat), 0))) (by decide)

-- `LawfulApplicative.pure_seq`: PM (pure counts).
theorem LawfulApplicative_pure_seq_h2 : ¬ drop0% LawfulApplicative.pure_seq 2 := fun h =>
  absurd (cnt% (@h PM inferInstance Nat Nat id ((0 : Nat), 0))) (by decide)

-- `LawfulApplicative.map_pure`: MC.
theorem LawfulApplicative_map_pure_h2 : ¬ drop0% LawfulApplicative.map_pure 2 := fun h =>
  absurd (cnt% (@h MC inferInstance Nat Nat id 0)) (by decide)

-- `LawfulApplicative.seq_pure`: PM.
theorem LawfulApplicative_seq_pure_h2 : ¬ drop0% LawfulApplicative.seq_pure 2 := fun h =>
  absurd (cnt% (@h PM inferInstance Nat Nat ((0 : Nat), id) 0)) (by decide)

-- `LawfulApplicative.seq_assoc`: MC (the right side maps once more).
theorem LawfulApplicative_seq_assoc_h2 : ¬ drop0% LawfulApplicative.seq_assoc 2 := fun h =>
  absurd (cnt% (@h MC inferInstance Nat Nat Nat ((0 : Nat), 0) ((0 : Nat), id) ((0 : Nat), id))) (by decide)

-- `pure_id_seq`: MC.
theorem pure_id_seq_h3 : ¬ drop0% pure_id_seq 3 := fun h =>
  absurd (cnt% (@h MC Nat _ ((0 : Nat), 0))) (by decide)

-- `pure_seqRight`: PM.
theorem pure_seqRight_h4 : ¬ drop0% pure_seqRight 4 := fun h =>
  absurd (cnt% (@h PM Nat Nat _ 0 ((0 : Nat), 0))) (by decide)

-- `seqLeft_pure`: PM.
theorem seqLeft_pure_h4 : ¬ drop0% seqLeft_pure 4 := fun h =>
  absurd (cnt% (@h PM Nat Nat _ ((0 : Nat), 0) 0)) (by decide)

-- `seqRight_pure_unit`: PM.
theorem seqRight_pure_unit_h2 : ¬ drop0% seqRight_pure_unit 2 := fun h =>
  absurd (cnt% (@h PM _ ((0 : Nat), ()))) (by decide)

-- `pure_unit_seqLeft`: PM.
theorem pure_unit_seqLeft_h2 : ¬ drop0% pure_unit_seqLeft 2 := fun h =>
  absurd (cnt% (@h PM _ ((0 : Nat), ()))) (by decide)

-- `LawfulMonad.bind_map`: SM (seq counts).
theorem LawfulMonad_bind_map_h2 : ¬ drop0% LawfulMonad.bind_map 2 := fun h =>
  absurd (cnt% (@h SM inferInstance Nat Nat ((0 : Nat), id) ((0 : Nat), 0))) (by decide)

-- `seq_eq_bind_map`: SM.
theorem seq_eq_bind_map_h4 : ¬ drop0% seq_eq_bind_map 4 := fun h =>
  absurd (cnt% (@h SM Nat Nat _ ((0 : Nat), id) ((0 : Nat), 0))) (by decide)

-- `bind_pure_unit`: PM.
theorem bind_pure_unit_h2 : ¬ drop0% bind_pure_unit 2 := fun h =>
  absurd (cnt% (@h PM _ ((0 : Nat), PUnit.unit))) (by decide)

-- `seq_eq_bind`: SM.
theorem seq_eq_bind_h4 : ¬ drop0% seq_eq_bind 4 := fun h =>
  absurd (cnt% (@h SM Nat Nat _ ((0 : Nat), id) ((0 : Nat), 0))) (by decide)

-- `seqRight_eq_bind`: RM.
theorem seqRight_eq_bind_h4 : ¬ drop0% seqRight_eq_bind 4 := fun h =>
  absurd (cnt% (@h RM Nat Nat _ ((0 : Nat), 0) ((0 : Nat), 0))) (by decide)

-- `seqLeft_eq_bind`: LM.
theorem seqLeft_eq_bind_h4 : ¬ drop0% seqLeft_eq_bind 4 := fun h =>
  absurd (cnt% (@h LM Nat Nat _ ((0 : Nat), 0) ((0 : Nat), 0))) (by decide)

-- `map_bind`: AM (map doubles the counter, bind doubles the first one).
theorem map_bind_h5 : ¬ drop0% map_bind 5 := fun h =>
  absurd (cnt% (@h AM Nat Nat Nat _ id ((1 : Nat), 0) pure)) (by decide)

-- `LawfulMonad.map_pure'`: MC.
theorem LawfulMonad_map_pure'_h5 : ¬ drop0% LawfulMonad.map_pure' 5 := fun h =>
  absurd (cnt% (@h MC Nat Nat id _ 0)) (by decide)

-- `LawfulMonad.map_map`: MC.
theorem LawfulMonad_map_map_h7 : ¬ drop0% LawfulMonad.map_map 7 := fun h =>
  absurd (cnt% (@h Nat Nat Nat id id MC _ ((0 : Nat), 0))) (by decide)

/-! ## `LawfulMonad.mk'`: each premise fails in a model satisfying all the others -/

-- `LawfulMonad.mk'`: FM satisfies all premises but id_map.
theorem LawfulMonad_mk'_h2 : ¬ drop0% LawfulMonad.mk' 2 := fun h => by
  haveI := h FM (by law) (by law) (by law) (by law) (by law) (by law) (by law)
  exact absurd (cnt% (id_map (f := FM) ((1 : Nat), 0))) (by decide)

-- `LawfulMonad.mk'`: LP satisfies all premises but pure_bind.
theorem LawfulMonad_mk'_h3 : ¬ drop0% LawfulMonad.mk' 3 := fun h => by
  haveI := h LP (by law) (by law) (by law) (by law) (by law) (by law) (by law)
  exact absurd (cnt% (pure_bind (m := LP) 0 (fun _ => ((1 : Nat), 0)))) (by decide)

-- `LawfulMonad.mk'`: NA satisfies all premises but bind_assoc.
theorem LawfulMonad_mk'_h4 : ¬ drop0% LawfulMonad.mk' 4 := fun h => by
  haveI := h NA (by law) (by law) (by law) (by law) (by law) (by law) (by law)
  exact absurd (cnt% (bind_assoc (m := NA) ((1 : Nat), 0) (fun _ => ((1 : Nat), 0))
    (fun _ => ((1 : Nat), 0)))) (by decide)

-- `LawfulMonad.mk'`: KM satisfies all premises but map_const.
theorem LawfulMonad_mk'_h5 : ¬ drop0% LawfulMonad.mk' 5 := fun h => by
  haveI := h KM (by law) (by law) (by law) (by law) (by law) (by law) (by law)
  exact absurd (cnt% (congrFun (congrFun (map_const (f := KM) (α := Nat) (β := Nat)) 0) ((0 : Nat), 0)))
    (by decide)

-- `LawfulMonad.mk'`: LM satisfies all premises but seqLeft_eq.
theorem LawfulMonad_mk'_h6 : ¬ drop0% LawfulMonad.mk' 6 := fun h => by
  haveI := h LM (by law) (by law) (by law) (by law) (by law) (by law) (by law)
  exact absurd (cnt% (seqLeft_eq (f := LM) ((0 : Nat), 0) ((0 : Nat), 0))) (by decide)

-- `LawfulMonad.mk'`: RM satisfies all premises but seqRight_eq.
theorem LawfulMonad_mk'_h7 : ¬ drop0% LawfulMonad.mk' 7 := fun h => by
  haveI := h RM (by law) (by law) (by law) (by law) (by law) (by law) (by law)
  exact absurd (cnt% (seqRight_eq (f := RM) ((0 : Nat), 0) ((0 : Nat), 0))) (by decide)

-- `LawfulMonad.mk'`: FN satisfies all premises but bind_pure_comp.
theorem LawfulMonad_mk'_h8 : ¬ drop0% LawfulMonad.mk' 8 := fun h => by
  haveI := h FN (by law) (by law) (by law) (by law) (by law) (by law) (by law)
  exact absurd (cnt% (bind_pure_comp (m := FN) id ((1 : Nat), 0))) (by decide)

-- `LawfulMonad.mk'`: SM satisfies all premises but bind_map.
theorem LawfulMonad_mk'_h9 : ¬ drop0% LawfulMonad.mk' 9 := fun h => by
  haveI := h SM (by law) (by law) (by law) (by law) (by law) (by law) (by law)
  exact absurd (cnt% (bind_map (m := SM) ((0 : Nat), id) ((0 : Nat), 0))) (by decide)

/-! ## Refutations: monad transformer lemmas over a non-lawful base monad -/

-- `ExceptCpsT.runCatch_lift`: runCatch (lift x) = x >>= pure in PM.
theorem ExceptCpsT_runCatch_lift_h3 : ¬ drop0% ExceptCpsT.runCatch_lift 3 := fun h =>
  absurd (cnt% (@h PM Nat _ ((1 : Nat), 0))) (by decide)

-- `ExceptT.run_bind_lift`: lift maps, which counts in MC.
theorem ExceptT_run_bind_lift_h5 : ¬ drop0% ExceptT.run_bind_lift 5 := fun h =>
  absurd (cnt% (@h MC Nat Nat Nat _ ((0 : Nat), 0) (fun a => ExceptT.mk (pure (.ok a))))) (by decide)

-- `ExceptT.bind_throw`: PM.
theorem ExceptT_bind_throw_h6 : ¬ drop0% ExceptT.bind_throw 6 := fun h =>
  absurd (cnt% (@h PM Nat Nat Nat 0 _ (fun a => pure a))) (by decide)

-- `ExceptT.lift_pure`: PM.
theorem ExceptT_lift_pure_h4 : ¬ drop0% ExceptT.lift_pure 4 := fun h =>
  absurd (cnt% (@h PM Nat Nat _ 0)) (by decide)

-- `ExceptT.run_map`: MC (the right side maps in m, the left side binds).
theorem ExceptT_run_map_h5 : ¬ drop0% ExceptT.run_map 5 := fun h =>
  absurd (cnt% (@h MC Nat Nat Nat _ id (ExceptT.mk ((1 : Nat), .ok 0)))) (by decide)

-- `ExceptT.seqLeft_eq`: PM.
theorem ExceptT_seqLeft_eq_h5 : ¬ drop0% ExceptT.seqLeft_eq 5 := fun h =>
  absurd (cnt% (@h Nat Nat Nat PM _ (ExceptT.mk ((1 : Nat), .ok 0)) (ExceptT.mk ((1 : Nat), .ok 0)))) (by decide)

-- `ExceptT.seqRight_eq`: PM.
theorem ExceptT_seqRight_eq_h5 : ¬ drop0% ExceptT.seqRight_eq 5 := fun h =>
  absurd (cnt% (@h PM Nat Nat Nat _ (ExceptT.mk ((1 : Nat), .ok 0)) (ExceptT.mk ((1 : Nat), .ok 0)))) (by decide)

-- `ExceptT.instLawfulMonad`: pure_bind fails in ExceptT Nat PM.
theorem ExceptT_instLawfulMonad_h3 : ¬ drop0% ExceptT.instLawfulMonad 3 := fun h =>
  absurd (cnt% (@LawfulMonad.pure_bind _ _ (@h PM Nat _) Nat Nat 0 (fun a => pure a))) (by decide)

-- `ExceptT.map_throw`: PM.
theorem ExceptT_map_throw_h3 : ¬ drop0% ExceptT.map_throw 3 := fun h =>
  absurd (cnt% (@h PM Nat _ Nat Nat id 0)) (by decide)

-- `ExceptT.run_controlAt`: PM.
theorem ExceptT_run_controlAt_h4 : ¬ drop0% ExceptT.run_controlAt 4 := fun h =>
  absurd (cnt% (@h PM Nat Nat _ (fun _ => ((1 : Nat), .ok 0)))) (by decide)

-- `ExceptT.run_control`: PM.
theorem ExceptT_run_control_h4 : ¬ drop0% ExceptT.run_control 4 := fun h =>
  absurd (cnt% (@h PM Nat Nat _ (fun _ => ((1 : Nat), .ok 0)))) (by decide)

-- `OptionT.run_bind_lift`: PM.
theorem OptionT_run_bind_lift_h4 : ¬ drop0% OptionT.run_bind_lift 4 := fun h =>
  absurd (cnt% (@h PM Nat Nat _ ((1 : Nat), 0) (fun a => pure a))) (by decide)

-- `OptionT.bind_throw`: PM.
theorem OptionT_bind_throw_h5 : ¬ drop0% OptionT.bind_throw 5 := fun h =>
  absurd (cnt% (@h PM Nat Nat () _ (fun a => pure a))) (by decide)

-- `OptionT.lift_pure`: PM.
theorem OptionT_lift_pure_h2 : ¬ drop0% OptionT.lift_pure 2 := fun h =>
  absurd (cnt% (@h PM _ Nat 0)) (by decide)

-- `OptionT.run_map`: MC.
theorem OptionT_run_map_h4 : ¬ drop0% OptionT.run_map 4 := fun h =>
  absurd (cnt% (@h MC Nat Nat _ id (OptionT.mk ((1 : Nat), some 0)))) (by decide)

-- `OptionT.seqLeft_eq`: PM.
theorem OptionT_seqLeft_eq_h4 : ¬ drop0% OptionT.seqLeft_eq 4 := fun h =>
  absurd (cnt% (@h Nat Nat PM _ (OptionT.mk ((1 : Nat), some 0)) (OptionT.mk ((1 : Nat), some 0)))) (by decide)

-- `OptionT.seqRight_eq`: PM.
theorem OptionT_seqRight_eq_h4 : ¬ drop0% OptionT.seqRight_eq 4 := fun h =>
  absurd (cnt% (@h PM Nat Nat _ (OptionT.mk ((1 : Nat), some 0)) (OptionT.mk ((1 : Nat), some 0)))) (by decide)

-- `OptionT.instLawfulMonad`: pure_bind fails in OptionT PM.
theorem OptionT_instLawfulMonad_h2 : ¬ drop0% OptionT.instLawfulMonad 2 := fun h =>
  absurd (cnt% (@LawfulMonad.pure_bind _ _ (@h PM _) Nat Nat 0 (fun a => pure a))) (by decide)

-- `OptionT.run_seq`: MC.
theorem OptionT_run_seq_h4 : ¬ drop0% OptionT.run_seq 4 := fun h =>
  absurd (cnt% (@h MC Nat Nat _ (OptionT.mk ((1 : Nat), some id)) (OptionT.mk ((1 : Nat), some 0)))) (by decide)

-- `OptionT.run_seqLeft`: MC.
theorem OptionT_run_seqLeft_h4 : ¬ drop0% OptionT.run_seqLeft 4 := fun h =>
  absurd (cnt% (@h MC Nat Nat _ (OptionT.mk ((1 : Nat), some 0)) (OptionT.mk ((1 : Nat), some 0)))) (by decide)

-- `OptionT.map_failure`: PM.
theorem OptionT_map_failure_h2 : ¬ drop0% OptionT.map_failure 2 := fun h =>
  absurd (cnt% (@h PM _ Nat Nat id)) (by decide)

-- `OptionT.run_liftWith`: MC.
theorem OptionT_run_liftWith_h3 : ¬ drop0% OptionT.run_liftWith 3 := fun h =>
  absurd (cnt% (@h MC Nat _ (fun _ => ((1 : Nat), 0)))) (by decide)

-- `OptionT.run_controlAt`: PM.
theorem OptionT_run_controlAt_h3 : ¬ drop0% OptionT.run_controlAt 3 := fun h =>
  absurd (cnt% (@h PM Nat _ (fun _ => ((1 : Nat), some 0)))) (by decide)

-- `OptionT.run_control`: PM.
theorem OptionT_run_control_h3 : ¬ drop0% OptionT.run_control 3 := fun h =>
  absurd (cnt% (@h PM Nat _ (fun _ => ((1 : Nat), some 0)))) (by decide)

-- `ReaderT.instLawfulFunctor`: id_map fails in ReaderT Unit MC.
theorem ReaderT_instLawfulFunctor_h3 : ¬ drop0% ReaderT.instLawfulFunctor 3 := fun h =>
  absurd (cnt% (congrFun (@LawfulFunctor.id_map _ _ (@h MC Unit _) Nat (fun _ => ((0 : Nat), 0))) ()))
    (by decide)

-- `ReaderT.instLawfulApplicative`: id_map fails in ReaderT Unit MC.
theorem ReaderT_instLawfulApplicative_h3 : ¬ drop0% ReaderT.instLawfulApplicative 3 := fun h =>
  absurd (cnt% (congrFun (@LawfulFunctor.id_map _ _ (@h MC Unit _).toLawfulFunctor Nat
    (fun _ => ((0 : Nat), 0))) ())) (by decide)

-- `ReaderT.instLawfulMonad`: id_map fails in ReaderT Unit MC.
theorem ReaderT_instLawfulMonad_h3 : ¬ drop0% ReaderT.instLawfulMonad 3 := fun h =>
  absurd (cnt% (congrFun (@LawfulFunctor.id_map _ _ (@h MC Unit _).toLawfulFunctor Nat
    (fun _ => ((0 : Nat), 0))) ())) (by decide)

-- `ReaderT.run_controlAt`: x >>= pure ≠ x in PM.
theorem ReaderT_run_controlAt_h4 : ¬ drop0% ReaderT.run_controlAt 4 := fun h =>
  absurd (cnt% (@h PM Unit Nat _ (fun _ => (((1 : Nat), (0 : Nat)) : Nat × Nat)) ())) (by decide)

-- `ReaderT.run_control`: PM.
theorem ReaderT_run_control_h4 : ¬ drop0% ReaderT.run_control 4 := fun h =>
  absurd (cnt% (@h PM Unit Nat _ (fun _ => (((1 : Nat), (0 : Nat)) : Nat × Nat)) ())) (by decide)

-- `instLawfulMonadStateRefT'`: id_map fails in StateRefT' Unit Nat MC, read at some reference.
theorem instLawfulMonadStateRefT'_h4 : ¬ drop0% instLawfulMonadStateRefT' 4 := fun h =>
  absurd (congrArg (fun z => (show Nat × _ from z (Classical.choice inferInstance)).1)
    (@LawfulFunctor.id_map _ _ (@h MC Unit Nat _).toLawfulFunctor Nat (fun _ => ((0 : Nat), 0))))
    (by decide)

-- `StateT.run_map`: MC.
theorem StateT_run_map_h5 : ¬ drop0% StateT.run_map 5 := fun h =>
  absurd (cnt% (@h MC Nat Nat Unit _ id (fun s => ((1 : Nat), (0, s))) ())) (by decide)

-- `StateT.run_bind_lift`: PM.
theorem StateT_run_bind_lift_h5 : ¬ drop0% StateT.run_bind_lift 5 := fun h =>
  absurd (cnt% (@h PM Nat Nat Unit _ ((1 : Nat), 0) (fun a => pure a) ())) (by decide)

-- `StateT.run_seq`: MC.
theorem StateT_run_seq_h5 : ¬ drop0% StateT.run_seq 5 := fun h =>
  absurd (cnt% (@h MC Nat Nat Unit _ (fun s => ((1 : Nat), (id, s))) (fun s => ((1 : Nat), (0, s))) ()))
    (by decide)

-- `StateT.seqRight_eq`: PM.
theorem StateT_seqRight_eq_h5 : ¬ drop0% StateT.seqRight_eq 5 := fun h =>
  absurd (cntS% (@h PM Unit Nat Nat _ (fun s => ((1 : Nat), (0, s))) (fun s => ((1 : Nat), (0, s)))) at ())
    (by decide)

-- `StateT.seqLeft_eq`: PM.
theorem StateT_seqLeft_eq_h5 : ¬ drop0% StateT.seqLeft_eq 5 := fun h =>
  absurd (cntS% (@h PM Unit Nat Nat _ (fun s => ((1 : Nat), (0, s))) (fun s => ((1 : Nat), (0, s)))) at ())
    (by decide)

-- `StateT.instLawfulMonad`: pure_bind fails in StateT Unit PM.
theorem StateT_instLawfulMonad_h3 : ¬ drop0% StateT.instLawfulMonad 3 := fun h =>
  absurd (cntS% (@LawfulMonad.pure_bind _ _ (@h PM Unit _) Nat Nat 0 (fun a => pure a)) at ()) (by decide)

-- `StateT.run_restoreM`: PM.
theorem StateT_run_restoreM_h4 : ¬ drop0% StateT.run_restoreM 4 := fun h =>
  absurd (cnt% (@h PM Unit Nat _ (0, ()) ())) (by decide)

-- `StateT.run_liftWith`: PM.
theorem StateT_run_liftWith_h4 : ¬ drop0% StateT.run_liftWith 4 := fun h =>
  absurd (cnt% (@h PM Unit Nat _ (fun _ => ((1 : Nat), 0)) ())) (by decide)

-- `StateT.run_controlAt`: PM.
theorem StateT_run_controlAt_h4 : ¬ drop0% StateT.run_controlAt 4 := fun h =>
  absurd (cnt% (@h PM Unit Nat _ (fun _ => ((1 : Nat), (0, ()))) ())) (by decide)

-- `StateT.run_control`: PM.
theorem StateT_run_control_h4 : ¬ drop0% StateT.run_control 4 := fun h =>
  absurd (cnt% (@h PM Unit Nat _ (fun _ => ((1 : Nat), (0, ()))) ())) (by decide)

/-! ## `MonadAttach` -/

-- `LawfulMonadAttach.toWeaklyLawfulMonadAttach`: BA is not weakly lawful.
theorem LawfulMonadAttach_toWeaklyLawfulMonadAttach_h3 :
    ¬ drop0% LawfulMonadAttach.toWeaklyLawfulMonadAttach 3 := fun h =>
  absurd (congrArg (fun z => (show Option Nat from z).isSome)
    ((@h BA inferInstance inferInstance).map_attach (α := Nat) (x := (some 0 : Option Nat)))) (by decide)

-- `LawfulMonadAttach.canReturn_map_imp`: in NT everything can be returned, P is false.
theorem LawfulMonadAttach_canReturn_map_imp_h3 : ¬ drop0% LawfulMonadAttach.canReturn_map_imp 3 :=
  fun h => @h NT inferInstance inferInstance Nat (fun _ => False) (0 : Nat) 0 trivial

-- `LawfulMonadAttach.canReturn_map_imp`: NE is lawful, P is false.
theorem LawfulMonadAttach_canReturn_map_imp_h8 : ¬ drop0% LawfulMonadAttach.canReturn_map_imp 8 :=
  fun h => @h NE inferInstance inferInstance inferInstance Nat (fun _ => False) (0 : Nat) 0

/-! ## Removable -/

-- `OptionT.run_seqRight`: x *> y is x >>= fun _ => y, and OptionT.run_bind (no monad laws) gives the right side.
theorem OptionT_run_seqRight_h4 : drop% OptionT.run_seqRight 4 := by
  intros m α β _ x y
  exact OptionT.run_bind (fun _ => y)

end LawfulAHand
