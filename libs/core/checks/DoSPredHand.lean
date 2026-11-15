import Std
import Lean

/-!
Hand pass `DoSPred` (hand15): the 200 unresolved hypotheses of `Std.Do.SPred` (`SPred`, `Laws`,
`DerivedLaws` incl. the proof-mode lemmas in `SPred.Tactic`), `Std.Do.PostCond`, `Std.Do.PredTrans` and
`Std.Do.Internal.Ensures`. For hypothesis `hᵢ` of theorem `T` each declaration proves `¬T'`
(`¬ drop0% T i`; for the two dependent rows `¬ indep0% T i`).

200 necessary, 0 removable, 0 independent.

* 147 `SPred` rows by the tactic `spred_cex` (namespace `SPredCex`, adapted from `refute_indep` of
  `StdDepHand.lean`): it instantiates `σs := []` (so `SPred σs = ULift Prop`), `SPred` binders by
  `⌜True⌝`/`⌜False⌝`, `Prop` binders by `True`/`False`, types by `Unit`/`Bool`, functions by constants,
  instances by synthesis, and closes the remaining premises and the negated conclusion by `simp`.
  The comment above each declaration records the values it found.
* 10 further `SPred` rows by hand: equations of predicates (`⌜True⌝ ≠ ⌜False⌝`) and rows needing a
  `PropAsSPredTautology φ P` instance with false `φ` (`φ := ⊢ₛ ⌜False⌝`, `P := ⌜False⌝`).
* `PostCond`/`ExceptConds`/`PredTrans`: one `Unit` exception layer, `eT`/`eF` (exception conditions
  `⌜True⌝`/`⌜False⌝`), `pT`/`pF` (postconditions over `Unit`), the antitone transformer `Q ↦ ¬ Q.1 ()`,
  and `PredTrans.const`.

Reusable monad models (namespace `DoSPredHand`) for `Ensures`/`MayReturn`/`ErasesTo`/`MonadAttach`:
* `WM w`: counter monad (`structure` with `c : Nat`, `v : α`) whose `bind` subtracts a weight `w α` of
  its source type, `x >>= f = ⟨x.c + (f x.v).c - w α, (f x.v).v⟩`, with a `LawfulMonadAttach`
  (`CanReturn x a := a = x.v`). An action `⟨0, v⟩` at a weight-1 type has no `Ensures`-refinement at a
  weight-0 subtype (`wm_not_ens`); equal weights give one (`wm_ens`). Weights: `wS` (0 on
  subsingletons) and `wT` (0 on two-element types). Breaks `pure_bind`, `Ensures.pure/bind/weaken`,
  `ErasesTo.of_attach`, `Ensures.canReturn`, `MayReturn.canReturn` without `LawfulMonad`.
* `ZB`: `Option` with `bind` constantly `none` and `Option`'s lawful `attach`; every `Ensures` holds,
  so `MayReturn` is empty (`zb_ens`).
* `BF` / `BT`: lawful `Option` with empty / full `CanReturn` and `attach = none` (not weakly lawful).
* `MC`: writer `Nat × α` whose `map` adds one.
* `Id` and `Option` with the library instances (`id_ens`, `id_ens_val`, `opt_ens`).

Run with the lean4 repo's stage1 binary: `runs/hand15/lean.sh checks/DoSPredHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxErrors 10000

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




namespace SPredCex
open Lean Meta Elab Tactic

def proveBy (budget : IO.Ref Nat) (ty : Expr) : TacticM (Option Expr) := do
  if (← budget.get) == 0 then return none
  budget.modify (· - 1)
  let s ← saveState
  let msgs := (← getThe Core.State).messages
  let mv ← mkFreshExprMVar ty
  try
    let gs ← withoutRecover <| Tactic.run mv.mvarId! (evalTactic (← `(tactic|
      first
        | trivial
        | (simp [Std.Do.SPred.entails_cons, Std.Do.SPred.bientails_cons]; done)
        | (intro h; simp [Std.Do.SPred.entails_cons, Std.Do.SPred.bientails_cons] at h; done)
        | (intro h; cases h; simp_all [Std.Do.SPred.entails_cons, Std.Do.SPred.bientails_cons]; done)
        | (intro h; have := congrFun h; simp_all; done)
        | (intros; simp_all [Std.Do.SPred.entails_cons, Std.Do.SPred.bientails_cons]; done))))
    modifyThe Core.State ({ · with messages := msgs })
    if gs.isEmpty then
      let p ← instantiateMVars mv
      unless p.hasExprMVar || p.hasSorry do return some p
    s.restore; modifyThe Core.State ({ · with messages := msgs }); return none
  catch _ => s.restore; modifyThe Core.State ({ · with messages := msgs }); return none

partial def cands (budget : IO.Ref Nat) (d : Expr) (bi : BinderInfo) : TacticM (Array Expr) := do
  let d ← instantiateMVars d
  if bi.isInstImplicit || (← isClass? d).isSome then
    return (← try synthInstance? d catch _ => pure none).toArray
  if ← isProp d then return (← proveBy budget d).toArray
  if d.isAppOfArity ``Std.Do.SPred 1 then
    let us := d.getAppFn.constLevels!
    let σs := d.appArg!
    return #[mkApp2 (mkConst ``Std.Do.SPred.pure us) σs (mkConst ``True),
             mkApp2 (mkConst ``Std.Do.SPred.pure us) σs (mkConst ``False)]
  if d.isAppOfArity ``List 1 then
    if let .sort u := d.appArg! then
      return #[mkApp (mkConst ``List.nil [u]) d.appArg!]
  let dw ← whnfR d
  if dw.isAppOfArity ``ULift 1 && dw.appArg!.isProp then
    let us := dw.getAppFn.constLevels!
    return #[mkApp2 (mkConst ``ULift.up us) (mkSort .zero) (mkConst ``True),
             mkApp2 (mkConst ``ULift.up us) (mkSort .zero) (mkConst ``False)]
  if let .sort u := dw then
    if ← isLevelDefEq u Level.one then return #[mkConst ``Unit, mkConst ``Bool]
    if ← isLevelDefEq u Level.zero then return #[mkConst ``True, mkConst ``False]
    return #[]
  if d.isConstOf ``Nat then return #[0, 1].map mkNatLit
  if d.isConstOf ``Bool then return #[mkConst ``Bool.false, mkConst ``Bool.true]
  if dw.isForall then
    let r ← forallTelescope dw fun xs body => do
      if ← isProp body then return #[]
      let cs ← cands budget body .default
      cs.extract 0 2 |>.mapM (mkLambdaFVars xs ·)
    unless r.isEmpty do return r
  if let some i ← (try synthInstance? (mkApp (mkConst ``Inhabited [← getLevel d]) d) catch _ => pure none) then
    return #[mkApp2 (mkConst ``Inhabited.default [← getLevel d]) d i]
  return #[]

partial def go (budget : IO.Ref Nat) (e ty : Expr) (w : MessageData) : TacticM (Option Expr) := do
  if (← budget.get) == 0 then return none
  let ty ← instantiateMVars ty
  let ty ← if ty.isForall then pure ty else whnfR ty
  match ty with
  | .forallE n d b bi =>
    let cs ← cands budget d bi
    let cs := if b.hasLooseBVars then cs else cs.extract 0 1
    let show_ := !bi.isInstImplicit && !(← isProp d) && b.hasLooseBVars
    for c in cs do
      let w' := if show_ then m!"{w} {n.eraseMacroScopes} := {c}," else w
      if let some p ← go budget (mkApp e c) (b.instantiate1 c) w' then return some p
    return none
  | _ =>
    let some np ← proveBy budget (mkNot ty) | return none
    return some (mkApp np e)

/-- Refutes a goal `¬ ∀ xs, C` by instantiating `σs := []`, `SPred` binders by `⌜True⌝`/`⌜False⌝`,
`Prop` binders by `True`/`False`, types by `Unit`/`Bool`, functions by constants, instances by
synthesis, and closing premises and `¬ C` by `simp`. -/
elab "spred_cex" : tactic => do
  let g ← getMainGoal
  let some (h, g') ← observing? g.intro1 | throwError "spred_cex: goal is not a negation"
  g'.withContext do
    let budget ← IO.mkRef 600
    let some p ← go budget (mkFVar h) (← h.getType) m!"" | throwError "spred_cex: no counterexample"
    g'.assign p
  replaceMainGoal []

end SPredCex


set_option linter.unusedVariables false
set_option warn.classDefReducibility false

namespace DoSPredHand
open Std.Do Std.Do.Internal

/-! ## Monad models for `Std.Do.Internal.Ensures` -/

/-- Counter monad `WM w α` (counter `c`, value `v`) whose `bind` subtracts a weight of its source type:
`x >>= f = ⟨x.c + (f x.v).c - w α, (f x.v).v⟩`; `pure a = ⟨0, a⟩`, `map` keeps the counter.
`attach` tags the value with `CanReturn x a := a = x.v` (a `LawfulMonadAttach`). Not a lawful monad
when `w` is not constantly `0`. -/
structure WM (w : Type → Nat) (α : Type) where
  c : Nat
  v : α

instance (w : Type → Nat) : Monad (WM w) where
  pure a := ⟨0, a⟩
  bind {α _} x f := ⟨x.c + (f x.v).c - w α, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩

instance (w : Type → Nat) : MonadAttach (WM w) where
  CanReturn x a := a = x.v
  attach x := ⟨x.c, ⟨x.v, rfl⟩⟩

instance (w : Type → Nat) : LawfulMonadAttach (WM w) where
  map_attach := rfl
  canReturn_map_imp {_ _ x _} h := h ▸ x.v.2

/-- Weight `0` on subsingletons, `1` otherwise. -/
noncomputable def wS (α : Type) : Nat := open Classical in if Subsingleton α then 0 else 1
/-- Weight `0` on types with exactly two elements, `1` otherwise. -/
noncomputable def wT (α : Type) : Nat :=
  open Classical in if ∃ a b : α, a ≠ b ∧ ∀ c, c = a ∨ c = b then 0 else 1

theorem wS_sub {α : Type} (h : ∀ a b : α, a = b) : wS α = 0 := by
  have : Subsingleton α := ⟨h⟩
  simp [wS, this]
theorem wS_ne {α : Type} (a b : α) (h : a ≠ b) : wS α = 1 := by
  have : ¬ Subsingleton α := fun hs => h (hs.allEq a b)
  simp [wS, this]
theorem wT_two {α : Type} (a b : α) (h : a ≠ b) (h' : ∀ c, c = a ∨ c = b) : wT α = 0 := by
  have : ∃ a b : α, a ≠ b ∧ ∀ c, c = a ∨ c = b := ⟨a, b, h, h'⟩
  simp [wT, this]
theorem wT_nat : wT Nat = 1 := by
  have : ¬ ∃ a b : Nat, a ≠ b ∧ ∀ c, c = a ∨ c = b := fun ⟨a, b, _, h⟩ => by
    have := h (a + b + 1); omega
  simp [wT, this]
theorem wT_single : wT {a : Nat // a = 0} = 1 := by
  have : ¬ ∃ a b : {a : Nat // a = 0}, a ≠ b ∧ ∀ c, c = a ∨ c = b := fun ⟨⟨a, ha⟩, ⟨b, hb⟩, h, _⟩ => by
    subst ha; subst hb; exact h rfl
  simp [wT, this]

/-- In `WM w`, an action `⟨0, v⟩` at a type of weight `1` has no refinement at a type of weight `0`. -/
theorem wm_not_ens {w : Type → Nat} {α : Type} {P : α → Prop} {v : α}
    (hP : w {a // P a} = 0) (hα : w α = 1) : ¬ Ensures P (⟨0, v⟩ : WM w α) := by
  intro ⟨y, hy⟩
  have h := congrArg WM.c (hy.bind_eq (β := α) fun a => ⟨1, a⟩)
  change y.c + 1 - w {a // P a} = 0 + 1 - w α at h
  omega

/-- In `WM w`, `⟨c, v⟩` is refined by `⟨c, ⟨v, h⟩⟩` when both types have the same weight. -/
theorem wm_ens {w : Type → Nat} {α : Type} {P : α → Prop} {c : Nat} {v : α} (h : P v)
    (hw : w {a // P a} = w α) : Ensures P (⟨c, v⟩ : WM w α) :=
  ⟨⟨⟨c, ⟨v, h⟩⟩, ⟨fun k => by
    show WM.mk (c + (k v).c - w {a // P a}) (k v).v = WM.mk (c + (k v).c - w α) (k v).v
    rw [hw]⟩⟩⟩

/-- `Option` whose `bind` is constantly `none` (`pure`/`map` as usual), with `Option`'s lawful
`attach` (`CanReturn x a := x = some a`). Not a lawful monad; every `Ensures` holds (refinement `none`). -/
def ZB (α : Type) : Type := Option α
instance : Monad ZB where
  pure a := (some a : Option _)
  bind _ _ := (none : Option _)
  map f x := Option.map f (show Option _ from x)
instance : MonadAttach ZB where
  CanReturn x a := (show Option _ from x) = some a
  attach x := Option.attach (show Option _ from x)
instance : LawfulMonadAttach ZB where
  map_attach {_ x} := by cases x <;> rfl
  canReturn_map_imp {_ P x a} h := by
    cases x with
    | none => cases h
    | some z => cases h; exact z.2

theorem zb_ens {α : Type} (P : α → Prop) (x : ZB α) : Ensures P x := ⟨⟨(none : Option _), ⟨fun _ => rfl⟩⟩⟩

/-- `Option` (a lawful monad) with empty `CanReturn` and `attach x = none`: not weakly lawful. -/
def BF (α : Type) : Type := Option α
instance : Monad BF := inferInstanceAs (Monad Option)
instance : LawfulMonad BF := inferInstanceAs (LawfulMonad Option)
instance : MonadAttach BF where
  CanReturn _ _ := False
  attach _ := (none : Option _)

/-- `Option` (a lawful monad) with full `CanReturn` and `attach x = none`: not weakly lawful. -/
def BT (α : Type) : Type := Option α
instance : Monad BT := inferInstanceAs (Monad Option)
instance : LawfulMonad BT := inferInstanceAs (LawfulMonad Option)
instance : MonadAttach BT where
  CanReturn _ _ := True
  attach _ := (none : Option _)

/-- `Nat × α` writer monad (`bind` adds counters) whose `map` adds one: not lawful. -/
def MC (α : Type) : Type := Nat × α
instance : Monad MC where
  pure a := ((0 : Nat), a)
  bind x f := (x.1 + (f x.2).1, (f x.2).2)
  map f x := (x.1 + 1, f x.2)

/-- In `Option`, `some 0` only ensures predicates that hold at `0`. -/
theorem opt_ens {P : Nat → Prop} (h : @Ensures Option _ Nat P (some 0)) : P 0 := by
  obtain ⟨y, hy⟩ := h
  have := hy.bind_eq (β := Nat) some
  cases y with
  | none => cases this
  | some z => exact (Option.some.inj this : z.1 = 0) ▸ z.2

/-- In `Id`, `x` ensures `P` iff `P x`. -/
theorem id_ens {P : Nat → Prop} {x : Nat} (h : P x) : Ensures (m := Id) P (x : Id Nat) :=
  ⟨⟨⟨x, h⟩, ⟨fun _ => rfl⟩⟩⟩
theorem id_ens_val {P : Nat → Prop} {x : Nat} (h : Ensures (m := Id) P (x : Id Nat)) : P x := by
  obtain ⟨y, hy⟩ := h
  have : y.run.1 = x := hy.bind_eq (β := Nat) fun a => (pure a : Id Nat)
  exact this ▸ y.run.2

end DoSPredHand


namespace DoSPredHand
open Std.Do Std.Do.Internal

/-! ## `Std.Do.Internal.Ensures` -/

-- `Std.Do.Internal.ErasesTo.bind_eq`: in `Option`, `none` does not erase to `some 0`.
theorem ErasesTo_bind_eq_6 : ¬ drop0% Std.Do.Internal.ErasesTo.bind_eq 6 := fun H =>
  absurd (H (m := Option) (P := fun _ : Nat => True) (x := none) (y := some 0) (k := some)) nofun

-- `Std.Do.Internal.Ensures.exists_refinement`: in `Id`, `0` has no refinement into `{a // False}`.
theorem Ensures_exists_refinement_5 : ¬ drop0% Std.Do.Internal.Ensures.exists_refinement 5 := fun H =>
  have ⟨y, _⟩ := H (m := Id) (P := fun _ : Nat => False) (x := (0 : Nat))
  y.run.2

-- `Std.Do.Internal.MayReturn.imp`: in `Id`, `0` ensures `· = 0`, but `1 ≠ 0`.
theorem MayReturn_imp_5 : ¬ drop0% Std.Do.Internal.MayReturn.imp 5 := fun H =>
  absurd (H (m := Id) (x := (0 : Nat)) (a := 1) (P := fun b => b = 0) (id_ens rfl)) (by decide)

-- `Std.Do.Internal.MayReturn.imp`: in `Id`, `0` may return `0`, which `fun _ => False` excludes.
theorem MayReturn_imp_7 : ¬ drop0% Std.Do.Internal.MayReturn.imp 7 := fun H =>
  H (m := Id) (x := (0 : Nat)) (a := 0) ⟨fun h => id_ens_val h⟩ (P := fun _ => False)

-- `Std.Do.Internal.IsAttach.erases`: in `Option`, `attach := none` does not erase to `some 0`.
theorem IsAttach_erases_3 : ¬ drop0% Std.Do.Internal.IsAttach.erases 3 := fun H =>
  absurd ((H (m := Option) (attach := fun _ _ => none) (some 0)).bind_eq (β := Nat) some) nofun

-- `Std.Do.Internal.ErasesTo.map_eq`: in `MC` (`map` counts one) `(0, ⟨0, _⟩)` erases to `(0, 0)`,
-- but `Subtype.val <$> (0, ⟨0, _⟩) = (1, 0)`.
theorem ErasesTo_map_eq_6 : ¬ drop0% Std.Do.Internal.ErasesTo.map_eq 6 := fun H =>
  absurd (congrArg Prod.fst (show ((1 : Nat), (0 : Nat)) = ((0 : Nat), (0 : Nat)) from
    H (m := MC) (P := fun _ : Nat => True) (x := ((0 : Nat), ⟨0, trivial⟩)) (y := ((0 : Nat), (0 : Nat)))
      ⟨fun _ => rfl⟩)) (by decide)

-- `Std.Do.Internal.ErasesTo.map_eq`: in `Option`, `Subtype.val <$> none ≠ some 0`.
theorem ErasesTo_map_eq_7 : ¬ drop0% Std.Do.Internal.ErasesTo.map_eq 7 := fun H =>
  absurd (H (m := Option) (P := fun _ : Nat => True) (x := none) (y := some 0)) nofun

-- `Std.Do.Internal.ErasesTo.of_attach`: in `WM wS` (lawful attach, unlawful bind) `attach ⟨0, 0⟩` has
-- weight-0 type `{a // a = 0}`, so binding it counts one more than binding `⟨0, 0⟩ : WM wS Nat`.
theorem ErasesTo_of_attach_2 : ¬ drop0% Std.Do.Internal.ErasesTo.of_attach 2 := fun H => by
  have h := congrArg WM.c ((H (m := WM wS) (x := (⟨0, (0 : Nat)⟩ : WM wS Nat))).bind_eq (β := Nat) fun a => ⟨1, a⟩)
  change 0 + 1 - wS {a : Nat // a = 0} = 0 + 1 - wS Nat at h
  rw [wS_sub (fun ⟨a, ha⟩ ⟨b, hb⟩ => by subst ha; subst hb; rfl), wS_ne 0 1 (by decide)] at h
  omega

-- `Std.Do.Internal.ErasesTo.of_attach`: `BF` (`Option`, `attach = none`): `none` does not erase to `some 0`.
theorem ErasesTo_of_attach_4 : ¬ drop0% Std.Do.Internal.ErasesTo.of_attach 4 := fun H =>
  absurd ((H (m := BF) (x := (some (0 : Nat) : Option Nat))).bind_eq (β := Nat) fun a => (some a : Option Nat)) nofun

-- `Std.Do.Internal.Ensures.pure`: in `WM wS`, `pure 0 = ⟨0, 0⟩ : WM wS Nat` has no refinement at the
-- weight-0 type `{a // a = 0}`.
theorem Ensures_pure_2 : ¬ drop0% Std.Do.Internal.Ensures.pure 2 := fun H =>
  wm_not_ens (wS_sub (fun ⟨a, ha⟩ ⟨b, hb⟩ => by subst ha; subst hb; rfl)) (wS_ne 0 1 (by decide))
    (H (m := WM wS) (a := (0 : Nat)))

-- `Std.Do.Internal.Ensures.weaken`: in `WM wT` (weight 0 exactly on two-element types) `⟨0, 0⟩ : WM wT Nat`
-- ensures `· = 0` (weight 1 like `Nat`) but not the weaker `a = 0 ∨ a = 1` (weight 0).
theorem Ensures_weaken_2 : ¬ drop0% Std.Do.Internal.Ensures.weaken 2 := fun H =>
  wm_not_ens (P := fun a : Nat => a = 0 ∨ a = 1)
    (wT_two ⟨0, .inl rfl⟩ ⟨1, .inr rfl⟩ (by decide) (fun ⟨c, hc⟩ => by
      rcases hc with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl)) wT_nat
    (H (m := WM wT) (P := fun a : Nat => a = 0) (x := ⟨0, 0⟩)
      (wm_ens rfl (wT_single.trans wT_nat.symm)) (fun _ h => .inl h))

-- `Std.Do.Internal.Ensures.weaken`: in `Id`, nothing ensures `fun _ => False`.
theorem Ensures_weaken_7 : ¬ drop0% Std.Do.Internal.Ensures.weaken 7 := fun H =>
  id_ens_val (H (m := Id) (P := fun _ : Nat => False) (Q := fun _ => False) (x := (0 : Nat)) (fun _ h => h))

-- `Std.Do.Internal.Ensures.weaken`: in `Id`, `0` ensures `True` but not `False`.
theorem Ensures_weaken_8 : ¬ drop0% Std.Do.Internal.Ensures.weaken 8 := fun H =>
  id_ens_val (H (m := Id) (P := fun _ : Nat => True) (Q := fun _ => False) (x := (0 : Nat)) (id_ens trivial))

-- `Std.Do.Internal.Ensures.bind`: in `WM wS`, `x = ⟨0, 0⟩` ensures `True`, `k _ = ⟨1, 0⟩` ensures `· = 0`,
-- but `x >>= k = ⟨0, 0⟩` does not (`{a // a = 0}` has weight 0, `Nat` weight 1).
theorem Ensures_bind_2 : ¬ drop0% Std.Do.Internal.Ensures.bind 2 := fun H => by
  have h1 : wS Nat = 1 := wS_ne 0 1 (by decide)
  have h0 : wS {a : Nat // a = 0} = 0 := wS_sub (fun ⟨a, ha⟩ ⟨b, hb⟩ => by subst ha; subst hb; rfl)
  have := H (m := WM wS) (x := (⟨0, 0⟩ : WM wS Nat)) (P := fun _ => True) (k := fun _ => ⟨1, 0⟩)
    (Q := fun a : Nat => a = 0)
    (wm_ens trivial ((wS_ne (⟨0, trivial⟩ : {a : Nat // True}) ⟨1, trivial⟩ (by simp)).trans h1.symm))
    (fun _ _ => ⟨⟨⟨0, ⟨0, rfl⟩⟩, ⟨fun k => by
      show WM.mk (0 + (k 0).c - wS {a : Nat // a = 0}) (k 0).v = WM.mk (1 + (k 0).c - wS Nat) (k 0).v
      rw [h0, h1]; congr 1; omega⟩⟩⟩)
  have e : ((⟨0, 0⟩ : WM wS Nat) >>= fun _ => (⟨1, 0⟩ : WM wS Nat)) = ⟨0, 0⟩ := by
    show WM.mk (0 + 1 - wS Nat) 0 = _
    rw [h1]
  rw [e] at this
  exact wm_not_ens h0 h1 this

-- `Std.Do.Internal.Ensures.bind`: in `Id`, nothing ensures `fun _ => False` (premise vacuous).
theorem Ensures_bind_9 : ¬ drop0% Std.Do.Internal.Ensures.bind 9 := fun H =>
  id_ens_val (H (m := Id) (x := (0 : Nat)) (P := fun _ => False) (k := fun a => (a : Id Nat))
    (Q := fun _ => False) (fun _ h => h.elim))

-- `Std.Do.Internal.Ensures.bind`: in `Id`, `0` ensures `True`, but `0 >>= pure` doesn't ensure `False`.
theorem Ensures_bind_10 : ¬ drop0% Std.Do.Internal.Ensures.bind 10 := fun H =>
  id_ens_val (H (m := Id) (x := (0 : Nat)) (P := fun _ => True) (k := fun a => (a : Id Nat))
    (Q := fun _ => False) (id_ens trivial))

-- `Std.Do.Internal.Ensures.canReturn`: in `WM wS`, `CanReturn ⟨0, 0⟩ = (· = 0)` (weight 0) and
-- `⟨0, 0⟩ : WM wS Nat` has no refinement there.
theorem Ensures_canReturn_2 : ¬ drop0% Std.Do.Internal.Ensures.canReturn 2 := fun H =>
  wm_not_ens (P := fun a : Nat => a = 0) (wS_sub (fun ⟨a, ha⟩ ⟨b, hb⟩ => by subst ha; subst hb; rfl))
    (wS_ne 0 1 (by decide)) (H (m := WM wS) (x := (⟨0, (0 : Nat)⟩ : WM wS Nat)))

-- `Std.Do.Internal.Ensures.canReturn`: `BF` (`CanReturn` empty): `some 0` ensures only predicates true at 0.
theorem Ensures_canReturn_4 : ¬ drop0% Std.Do.Internal.Ensures.canReturn 4 := fun H =>
  opt_ens (P := fun _ => False) (H (m := BF) (x := (some (0 : Nat) : Option Nat)))

-- `Std.Do.Internal.MayReturn.of_canReturn`: `ZB` (`bind` constantly `none`, lawful attach):
-- `some 0` can return `0`, but ensures `fun _ => False`.
theorem MayReturn_of_canReturn_3 : ¬ drop0% Std.Do.Internal.MayReturn.of_canReturn 3 := fun H =>
  (H (m := ZB) (x := (some (0 : Nat) : Option Nat)) (a := 0) rfl).imp (P := fun _ => False) (zb_ens _ _)

-- `Std.Do.Internal.MayReturn.of_canReturn`: `BT` (`Option`, `CanReturn` full): `none` can return `0`,
-- but ensures `fun _ => False`.
theorem MayReturn_of_canReturn_5 : ¬ drop0% Std.Do.Internal.MayReturn.of_canReturn 5 := fun H =>
  (H (m := BT) (x := (none : Option Nat)) (a := 0) trivial).imp (P := fun _ => False)
    ⟨⟨(none : Option _), ⟨fun _ => rfl⟩⟩⟩

-- `Std.Do.Internal.MayReturn.of_canReturn`: in `Id`, `0` ensures `· = 0`, so it may not return `1`.
theorem MayReturn_of_canReturn_8 : ¬ drop0% Std.Do.Internal.MayReturn.of_canReturn 8 := fun H =>
  absurd ((H (m := Id) (x := (0 : Nat)) (a := 1)).imp (P := fun b => b = 0) (id_ens rfl)) (by decide)

/-- In `WM wS`, `⟨0, true⟩ : WM wS Bool` may return `false`: its only refinements are at non-subsingleton
types, i.e. at predicates true on both booleans. -/
theorem wm_may_false : MayReturn (⟨0, true⟩ : WM wS Bool) false := ⟨fun {P} h => by
  apply Classical.byContradiction
  intro hf
  apply wm_not_ens (P := P) (v := true) _ (wS_ne true false (by decide)) h
  exact wS_sub fun ⟨a, ha⟩ ⟨b, hb⟩ => by
    cases a <;> cases b <;> first | rfl | exact absurd ha hf | exact absurd hb hf⟩

-- `Std.Do.Internal.MayReturn.canReturn`: in `WM wS`, `⟨0, true⟩` may return `false` but `CanReturn` is `· = true`.
theorem MayReturn_canReturn_3 : ¬ drop0% Std.Do.Internal.MayReturn.canReturn 3 := fun H =>
  absurd (H (m := WM wS) wm_may_false) (fun h => absurd (show false = true from h) (by decide))

-- `Std.Do.Internal.MayReturn.canReturn`: `BF` (`CanReturn` empty): `some 0` may return `0`.
theorem MayReturn_canReturn_5 : ¬ drop0% Std.Do.Internal.MayReturn.canReturn 5 := fun H =>
  H (m := BF) (x := (some (0 : Nat) : Option Nat)) (a := 0) ⟨fun h => opt_ens h⟩

-- `Std.Do.Internal.MayReturn.canReturn`: in `Id`, `CanReturn 0 1` is `0 = 1`.
theorem MayReturn_canReturn_8 : ¬ drop0% Std.Do.Internal.MayReturn.canReturn 8 := fun H =>
  absurd (H (m := Id) (x := (0 : Nat)) (a := 1)) (fun h => absurd (show (0 : Nat) = 1 from h) (by decide))

-- `Std.Do.Internal.MayReturn.canReturn_iff`: `ZB`: `some 0` can return `0` but ensures `fun _ => False`.
theorem MayReturn_canReturn_iff_3 : ¬ drop0% Std.Do.Internal.MayReturn.canReturn_iff 3 := fun H =>
  ((H (m := ZB) (some (0 : Nat) : Option Nat) 0).mp rfl).imp (P := fun _ => False) (zb_ens _ _)

-- `Std.Do.Internal.MayReturn.canReturn_iff`: `BF` (`CanReturn` empty): `some 0` may return `0`.
theorem MayReturn_canReturn_iff_5 : ¬ drop0% Std.Do.Internal.MayReturn.canReturn_iff 5 := fun H =>
  (H (m := BF) (some (0 : Nat) : Option Nat) 0).mpr ⟨fun h => opt_ens h⟩

-- `Std.Do.Internal.MayReturn.canReturn_eq`: `ZB`: `some 0` can return `0` but ensures `fun _ => False`.
theorem MayReturn_canReturn_eq_3 : ¬ drop0% Std.Do.Internal.MayReturn.canReturn_eq 3 := fun H => by
  have e := congrFun (H (m := ZB) (some (0 : Nat) : Option Nat)) 0
  have c : MonadAttach.CanReturn (m := ZB) (some (0 : Nat) : Option Nat) 0 := rfl
  rw [e] at c
  exact c.imp (P := fun _ => False) (zb_ens _ _)

-- `Std.Do.Internal.MayReturn.canReturn_eq`: `BF` (`CanReturn` empty): `some 0` may return `0`.
theorem MayReturn_canReturn_eq_5 : ¬ drop0% Std.Do.Internal.MayReturn.canReturn_eq 5 := fun H => by
  have e := congrFun (H (m := BF) (some (0 : Nat) : Option Nat)) 0
  have c : MayReturn (m := BF) (some (0 : Nat) : Option Nat) 0 := ⟨fun h => opt_ens h⟩
  rw [← e] at c
  exact c

-- `Std.Do.Internal.IsAttach.of_attach`: `ZB` has a lawful `attach` but `pure 0 >>= some ≠ some 0`.
theorem IsAttach_of_attach_2 : ¬ indep0% Std.Do.Internal.IsAttach.of_attach 2 := fun H =>
  absurd (@LawfulMonad.pure_bind ZB _ (H (m := ZB)) Nat Nat 0 fun a => (some a : Option Nat)) nofun

-- `Std.Do.Internal.IsAttach.of_attach`: `BT` (`Option`, `attach = none`) is not weakly lawful.
theorem IsAttach_of_attach_4 : ¬ indep0% Std.Do.Internal.IsAttach.of_attach 4 := fun H =>
  absurd (@WeaklyLawfulMonadAttach.map_attach BT _ _ (H (m := BT)).toWeaklyLawfulMonadAttach Nat
    (some (0 : Nat) : Option Nat)) nofun

end DoSPredHand


namespace DoSPredHand
open Std.Do

/-! ## `Std.Do.PostCond` and `Std.Do.PredTrans`: one exception layer `ps = .except Unit .pure` -/

/-- Exception conditions that always / never hold, for one `Unit` exception. -/
def eT : ExceptConds (.except Unit .pure) := (fun _ => SPred.pure True, ⟨⟩)
def eF : ExceptConds (.except Unit .pure) := (fun _ => SPred.pure False, ⟨⟩)
/-- Postconditions over `Unit` with no exceptions that always / never hold. -/
def pT : PostCond Unit .pure := (fun _ => SPred.pure True, ⟨⟩)
def pF : PostCond Unit .pure := (fun _ => SPred.pure False, ⟨⟩)

theorem eT_eF : ¬ ExceptConds.entails eT eF := fun h => h.1 () trivial
theorem pT_pF : ¬ PostCond.entails pT pF := fun h => h.1 () trivial

-- `Std.Do.ExceptConds.entails.trans`: `eF ⊢ₑ eF` but not `eT ⊢ₑ eF`.
theorem ExceptConds_entails_trans_4 : ¬ drop0% Std.Do.ExceptConds.entails.trans 4 := fun H =>
  eT_eF (H (x := eT) (y := eF) (z := eF) (.refl _))

-- `Std.Do.ExceptConds.entails.trans`: `eT ⊢ₑ eT` but not `eT ⊢ₑ eF`.
theorem ExceptConds_entails_trans_5 : ¬ drop0% Std.Do.ExceptConds.entails.trans 5 := fun H =>
  eT_eF (H (x := eT) (y := eT) (z := eF) (.refl _))

-- `Std.Do.ExceptConds.and_eq_left`: `eT ≠ eT ∧ₑ eF`.
theorem ExceptConds_and_eq_left_3 : ¬ drop0% Std.Do.ExceptConds.and_eq_left 3 := fun H =>
  (show True ∧ False from
    Eq.mp (congrArg (fun e : ExceptConds (.except Unit .pure) => (e.1 ()).down) (H (p := eT) (q := eF))) trivial).2

-- `Std.Do.ExceptConds.imp_intro`: `eT` does not entail `eT →ₑ eF`.
theorem ExceptConds_imp_intro_4 : ¬ drop0% Std.Do.ExceptConds.imp_intro 4 := fun H =>
  (H (P := eT) (Q := eT) (R := eF)).1 () trivial trivial

-- `Std.Do.ExceptConds.imp_elim`: `eT ∧ₑ eT` does not entail `eF`.
theorem ExceptConds_imp_elim_4 : ¬ drop0% Std.Do.ExceptConds.imp_elim 4 := fun H =>
  (H (P := eT) (Q := eT) (R := eF)).1 () ⟨trivial, trivial⟩

-- `Std.Do.PostCond.entails.mk`: without exceptions the second premise is trivial; `pT ⊬ₚ pF`.
theorem PostCond_entails_mk_4 : ¬ drop0% Std.Do.PostCond.entails.mk 4 := fun H =>
  pT_pF (H (P := pT) (Q := pF) trivial)

-- `Std.Do.PostCond.entails.mk`: equal value assertions, exception conditions `eT ⊬ₑ eF`.
theorem PostCond_entails_mk_5 : ¬ drop0% Std.Do.PostCond.entails.mk 5 := fun H =>
  eT_eF (H (α := Unit) (P := (fun _ => SPred.pure True, eT)) (Q := (fun _ => SPred.pure True, eF))
    (fun _ h => h)).2

-- `Std.Do.PostCond.entails.trans`: `pF ⊢ₚ pF` but not `pT ⊢ₚ pF`.
theorem PostCond_entails_trans_5 : ¬ drop0% Std.Do.PostCond.entails.trans 5 := fun H =>
  pT_pF (H (P := pT) (Q := pF) (R := pF) (.refl _))

-- `Std.Do.PostCond.entails.trans`: `pT ⊢ₚ pT` but not `pT ⊢ₚ pF`.
theorem PostCond_entails_trans_6 : ¬ drop0% Std.Do.PostCond.entails.trans 6 := fun H =>
  pT_pF (H (P := pT) (Q := pT) (R := pF) (.refl _))

-- `Std.Do.PostCond.and_left_of_entails`: `pT ≠ pT ∧ₚ pF`.
theorem PostCond_and_left_of_entails_4 : ¬ drop0% Std.Do.PostCond.and_left_of_entails 4 := fun H =>
  (show True ∧ False from
    Eq.mp (congrArg (fun p : PostCond Unit .pure => (p.1 ()).down) (H (p := pT) (q := pF))) trivial).2

-- `Std.Do.PredTrans.Conjunctive.mono`: the antitone transformer `Q ↦ ¬ Q.1 ()` is not monotonic.
theorem PredTrans_Conjunctive_mono_3 : ¬ drop0% Std.Do.PredTrans.Conjunctive.mono 3 := fun H =>
  H (ps := .pure) (α := Unit) (fun Q => ⟨¬ (Q.1 ()).down⟩) pF pT ⟨fun _ h => h.elim, trivial⟩
    (fun h => h) trivial

-- `Std.Do.PredTrans.ext`: `const ⌜True⌝ ≠ const ⌜False⌝`.
theorem PredTrans_ext_4 : ¬ drop0% Std.Do.PredTrans.ext 4 := fun H =>
  Eq.mp (congrArg (fun t : PredTrans .pure Unit => (t.apply pT).down)
    (H (t₁ := PredTrans.const (SPred.pure True)) (t₂ := PredTrans.const (SPred.pure False)))) trivial

-- `Std.Do.PredTrans.bind_mono`: `const ⌜False⌝ >>= pure ≤ const ⌜True⌝ >>= pure` fails at `pT`.
theorem PredTrans_bind_mono_6 : ¬ drop0% Std.Do.PredTrans.bind_mono 6 := fun H =>
  H (ps := .pure) (α := Unit) (β := Unit) (x := PredTrans.const (SPred.pure False))
    (y := PredTrans.const (SPred.pure True)) (f := PredTrans.pure) pT trivial

/-! ## `Std.Do.SPred`: rows needing a `PropAsSPredTautology` instance or an equation of predicates -/

-- `Std.Do.SPred.Tactic.PropAsSPredTautology.iff`: `True` is not `⊢ₛ ⌜False⌝`.
theorem PropAsSPredTautology_iff_3 : ¬ drop0% Std.Do.SPred.Tactic.PropAsSPredTautology.iff 3 := fun H =>
  (H (φ := True) (σs := []) (P := SPred.pure False)).mp trivial trivial

-- `Std.Do.SPred.Tactic.ProofMode.start_entails`: instance `PropAsSPredTautology (⊢ₛ ⌜False⌝) ⌜False⌝`.
theorem ProofMode_start_entails_4 : ¬ drop0% Std.Do.SPred.Tactic.ProofMode.start_entails 4 := fun H =>
  H (σs := []) (P := SPred.pure False) (φ := SPred.entails (SPred.pure True) (SPred.pure False)) trivial

-- `Std.Do.SPred.Tactic.ProofMode.elim_entails`: instance `PropAsSPredTautology (⊢ₛ ⌜False⌝) ⌜False⌝`.
theorem ProofMode_elim_entails_4 : ¬ drop0% Std.Do.SPred.Tactic.ProofMode.elim_entails 4 := fun H =>
  H (σs := []) (P := SPred.pure False) (φ := SPred.entails (SPred.pure True) (SPred.pure False)) trivial

-- `Std.Do.SPred.Tactic.Exact.from_tautology`: `T = ⌜False⌝` with `φ = ⊢ₛ ⌜False⌝`, `P = ⌜True⌝`.
theorem Exact_from_tautology_5 : ¬ drop0% Std.Do.SPred.Tactic.Exact.from_tautology 5 := fun H =>
  H (σs := []) (φ := SPred.entails (SPred.pure True) (SPred.pure False)) (P := SPred.pure True)
    (T := SPred.pure False) trivial

-- `Std.Do.SPred.Tactic.Specialize.imp_pure`: `Q = R = ⌜False⌝` (`φ = ⊢ₛ ⌜False⌝`), `P = ⌜True⌝`.
theorem Specialize_imp_pure_6 : ¬ drop0% Std.Do.SPred.Tactic.Specialize.imp_pure 6 := fun H =>
  (H (σs := []) (φ := SPred.entails (SPred.pure True) (SPred.pure False)) (P := SPred.pure True)
    (Q := SPred.pure False) (R := SPred.pure False) ⟨trivial, fun h => h⟩).2

-- `Std.Do.SPred.Tactic.Specialize.pure_start`: `H = T = ⌜False⌝` (`φ = ⊢ₛ ⌜False⌝`), `P = ⌜True⌝`.
theorem Specialize_pure_start_6 : ¬ drop0% Std.Do.SPred.Tactic.Specialize.pure_start 6 := fun H =>
  H (σs := []) (φ := SPred.entails (SPred.pure True) (SPred.pure False)) (H := SPred.pure False)
    (P := SPred.pure True) (T := SPred.pure False) (fun h => h.2) trivial

-- `Std.Do.SPred.Tactic.Specialize.pure_start`: `H = ⌜True⌝` (`φ = ⊢ₛ ⌜True⌝`), `P = ⌜True⌝`, `T = ⌜False⌝`.
theorem Specialize_pure_start_7 : ¬ drop0% Std.Do.SPred.Tactic.Specialize.pure_start 7 := fun H =>
  H (σs := []) (φ := SPred.entails (SPred.pure True) (SPred.pure True)) (H := SPred.pure True)
    (P := SPred.pure True) (T := SPred.pure False) (fun h => h) trivial

-- `Std.Do.SPred.bientails.to_eq`: `⌜True⌝ ≠ ⌜False⌝` in `SPred []`.
theorem bientails_to_eq_3 : ¬ drop0% Std.Do.SPred.bientails.to_eq 3 := fun H =>
  Eq.mp (congrArg ULift.down (H (σs := []) (P := SPred.pure True) (Q := SPred.pure False))) trivial

-- `Std.Do.SPred.ext_nil`: `⌜True⌝ ≠ ⌜False⌝` in `SPred []`.
theorem ext_nil_2 : ¬ drop0% Std.Do.SPred.ext_nil 2 := fun H =>
  Eq.mp (congrArg ULift.down (H (P := SPred.pure True) (Q := SPred.pure False))) trivial

-- `Std.Do.SPred.ext_cons`: `⌜True⌝ ≠ ⌜False⌝` in `SPred [Unit]`.
theorem ext_cons_4 : ¬ drop0% Std.Do.SPred.ext_cons 4 := fun H =>
  Eq.mp (congrArg (fun P : SPred [Unit] => (P ()).down)
    (H (σs := []) (σ := Unit) (P := SPred.pure True) (Q := SPred.pure False))) trivial

end DoSPredHand


namespace DoSPredHand

/-! ## `Std.Do.SPred`: rows refuted by `spred_cex` -/

-- `Std.Do.SPred.bientails.of_eq`: σs := [], P := ⌜True⌝, Q := ⌜False⌝.
theorem bientails_of_eq_3 : ¬ drop0% Std.Do.SPred.bientails.of_eq 3 := by spred_cex

-- `Std.Do.SPred.bientails.mp`: σs := [], P := ⌜True⌝, Q := ⌜False⌝.
theorem bientails_mp_3 : ¬ drop0% Std.Do.SPred.bientails.mp 3 := by spred_cex

-- `Std.Do.SPred.bientails.mpr`: σs := [], P := ⌜False⌝, Q := ⌜True⌝.
theorem bientails_mpr_3 : ¬ drop0% Std.Do.SPred.bientails.mpr 3 := by spred_cex

-- `Std.Do.SPred.and_intro_l`: σs := [], P := ⌜True⌝, Q := ⌜False⌝.
theorem and_intro_l_3 : ¬ drop0% Std.Do.SPred.and_intro_l 3 := by spred_cex

-- `Std.Do.SPred.and_intro_r`: σs := [], P := ⌜True⌝, Q := ⌜False⌝.
theorem and_intro_r_3 : ¬ drop0% Std.Do.SPred.and_intro_r 3 := by spred_cex

-- `Std.Do.SPred.and_elim_l'`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem and_elim_l'_4 : ¬ drop0% Std.Do.SPred.and_elim_l' 4 := by spred_cex

-- `Std.Do.SPred.and_elim_r'`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem and_elim_r'_4 : ¬ drop0% Std.Do.SPred.and_elim_r' 4 := by spred_cex

-- `Std.Do.SPred.or_intro_l'`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, R := ⌜False⌝.
theorem or_intro_l'_4 : ¬ drop0% Std.Do.SPred.or_intro_l' 4 := by spred_cex

-- `Std.Do.SPred.or_intro_r'`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, R := ⌜False⌝.
theorem or_intro_r'_4 : ¬ drop0% Std.Do.SPred.or_intro_r' 4 := by spred_cex

-- `Std.Do.SPred.imp_intro'`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem imp_intro'_4 : ¬ drop0% Std.Do.SPred.imp_intro' 4 := by spred_cex

-- `Std.Do.SPred.entails.trans'`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, R := ⌜False⌝.
theorem entails_trans'_4 : ¬ drop0% Std.Do.SPred.entails.trans' 4 := by spred_cex

-- `Std.Do.SPred.entails.trans'`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem entails_trans'_5 : ¬ drop0% Std.Do.SPred.entails.trans' 5 := by spred_cex

-- `Std.Do.SPred.mp`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem mp_4 : ¬ drop0% Std.Do.SPred.mp 4 := by spred_cex

-- `Std.Do.SPred.mp`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, R := ⌜False⌝.
theorem mp_5 : ¬ drop0% Std.Do.SPred.mp 5 := by spred_cex

-- `Std.Do.SPred.imp_elim'`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem imp_elim'_4 : ¬ drop0% Std.Do.SPred.imp_elim' 4 := by spred_cex

-- `Std.Do.SPred.exists_intro'`: α := True, σs := [], P := ⌜True⌝, Ψ := fun a => ⌜False⌝.
theorem exists_intro'_5 : ¬ drop0% Std.Do.SPred.exists_intro' 5 := by spred_cex

-- `Std.Do.SPred.and_or_elim_l`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, R := ⌜True⌝, T := ⌜False⌝.
theorem and_or_elim_l_5 : ¬ drop0% Std.Do.SPred.and_or_elim_l 5 := by spred_cex

-- `Std.Do.SPred.and_or_elim_l`: σs := [], P := ⌜False⌝, Q := ⌜True⌝, R := ⌜True⌝, T := ⌜False⌝.
theorem and_or_elim_l_6 : ¬ drop0% Std.Do.SPred.and_or_elim_l 6 := by spred_cex

-- `Std.Do.SPred.and_or_elim_r`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝, T := ⌜False⌝.
theorem and_or_elim_r_5 : ¬ drop0% Std.Do.SPred.and_or_elim_r 5 := by spred_cex

-- `Std.Do.SPred.and_or_elim_r`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, R := ⌜True⌝, T := ⌜False⌝.
theorem and_or_elim_r_6 : ¬ drop0% Std.Do.SPred.and_or_elim_r 6 := by spred_cex

-- `Std.Do.SPred.exfalso`: σs := [], P := ⌜True⌝, Q := ⌜False⌝.
theorem exfalso_3 : ¬ drop0% Std.Do.SPred.exfalso 3 := by spred_cex

-- `Std.Do.SPred.and_mono`: σs := [], P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜True⌝, Q' := ⌜True⌝.
theorem and_mono_5 : ¬ drop0% Std.Do.SPred.and_mono 5 := by spred_cex

-- `Std.Do.SPred.and_mono`: σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem and_mono_6 : ¬ drop0% Std.Do.SPred.and_mono 6 := by spred_cex

-- `Std.Do.SPred.and_mono_l`: σs := [], P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜True⌝.
theorem and_mono_l_4 : ¬ drop0% Std.Do.SPred.and_mono_l 4 := by spred_cex

-- `Std.Do.SPred.and_mono_r`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem and_mono_r_4 : ¬ drop0% Std.Do.SPred.and_mono_r 4 := by spred_cex

-- `Std.Do.SPred.and_congr`: σs := [], P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜True⌝, Q' := ⌜True⌝.
theorem and_congr_5 : ¬ drop0% Std.Do.SPred.and_congr 5 := by spred_cex

-- `Std.Do.SPred.and_congr`: σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem and_congr_6 : ¬ drop0% Std.Do.SPred.and_congr 6 := by spred_cex

-- `Std.Do.SPred.and_congr_l`: σs := [], P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜True⌝.
theorem and_congr_l_4 : ¬ drop0% Std.Do.SPred.and_congr_l 4 := by spred_cex

-- `Std.Do.SPred.and_congr_r`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem and_congr_r_4 : ¬ drop0% Std.Do.SPred.and_congr_r 4 := by spred_cex

-- `Std.Do.SPred.or_mono`: σs := [], P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜False⌝, Q' := ⌜False⌝.
theorem or_mono_5 : ¬ drop0% Std.Do.SPred.or_mono 5 := by spred_cex

-- `Std.Do.SPred.or_mono`: σs := [], P := ⌜False⌝, P' := ⌜False⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem or_mono_6 : ¬ drop0% Std.Do.SPred.or_mono 6 := by spred_cex

-- `Std.Do.SPred.or_mono_l`: σs := [], P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜False⌝.
theorem or_mono_l_4 : ¬ drop0% Std.Do.SPred.or_mono_l 4 := by spred_cex

-- `Std.Do.SPred.or_mono_r`: σs := [], P := ⌜False⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem or_mono_r_4 : ¬ drop0% Std.Do.SPred.or_mono_r 4 := by spred_cex

-- `Std.Do.SPred.or_congr`: σs := [], P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜False⌝, Q' := ⌜False⌝.
theorem or_congr_5 : ¬ drop0% Std.Do.SPred.or_congr 5 := by spred_cex

-- `Std.Do.SPred.or_congr`: σs := [], P := ⌜False⌝, P' := ⌜False⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem or_congr_6 : ¬ drop0% Std.Do.SPred.or_congr 6 := by spred_cex

-- `Std.Do.SPred.or_congr_l`: σs := [], P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜False⌝.
theorem or_congr_l_4 : ¬ drop0% Std.Do.SPred.or_congr_l 4 := by spred_cex

-- `Std.Do.SPred.or_congr_r`: σs := [], P := ⌜False⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem or_congr_r_4 : ¬ drop0% Std.Do.SPred.or_congr_r 4 := by spred_cex

-- `Std.Do.SPred.imp_mono`: σs := [], P := ⌜False⌝, P' := ⌜False⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem imp_mono_5 : ¬ drop0% Std.Do.SPred.imp_mono 5 := by spred_cex

-- `Std.Do.SPred.imp_mono`: σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem imp_mono_6 : ¬ drop0% Std.Do.SPred.imp_mono 6 := by spred_cex

-- `Std.Do.SPred.imp_mono_l`: σs := [], P := ⌜False⌝, P' := ⌜True⌝, Q := ⌜False⌝.
theorem imp_mono_l_4 : ¬ drop0% Std.Do.SPred.imp_mono_l 4 := by spred_cex

-- `Std.Do.SPred.imp_mono_r`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem imp_mono_r_4 : ¬ drop0% Std.Do.SPred.imp_mono_r 4 := by spred_cex

-- `Std.Do.SPred.imp_congr`: σs := [], P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜False⌝, Q' := ⌜False⌝.
theorem imp_congr_5 : ¬ drop0% Std.Do.SPred.imp_congr 5 := by spred_cex

-- `Std.Do.SPred.imp_congr`: σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem imp_congr_6 : ¬ drop0% Std.Do.SPred.imp_congr 6 := by spred_cex

-- `Std.Do.SPred.imp_congr_l`: σs := [], P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜False⌝.
theorem imp_congr_l_4 : ¬ drop0% Std.Do.SPred.imp_congr_l 4 := by spred_cex

-- `Std.Do.SPred.imp_congr_r`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem imp_congr_r_4 : ¬ drop0% Std.Do.SPred.imp_congr_r 4 := by spred_cex

-- `Std.Do.SPred.forall_mono`: σs := [], α := True, Φ := fun a => ⌜True⌝, Ψ := fun a => ⌜False⌝.
theorem forall_mono_4 : ¬ drop0% Std.Do.SPred.forall_mono 4 := by spred_cex

-- `Std.Do.SPred.forall_congr`: σs := [], α := True, Φ := fun a => ⌜True⌝, Ψ := fun a => ⌜False⌝.
theorem forall_congr_4 : ¬ drop0% Std.Do.SPred.forall_congr 4 := by spred_cex

-- `Std.Do.SPred.exists_mono`: σs := [], α := True, Φ := fun a => ⌜True⌝, Ψ := fun a => ⌜False⌝.
theorem exists_mono_4 : ¬ drop0% Std.Do.SPred.exists_mono 4 := by spred_cex

-- `Std.Do.SPred.exists_congr`: σs := [], α := True, Φ := fun a => ⌜True⌝, Ψ := fun a => ⌜False⌝.
theorem exists_congr_4 : ¬ drop0% Std.Do.SPred.exists_congr 4 := by spred_cex

-- `Std.Do.SPred.of_and_imp`: σs := [], P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜True⌝, Q' := ⌜True⌝.
theorem of_and_imp_5 : ¬ drop0% Std.Do.SPred.of_and_imp 5 := by spred_cex

-- `Std.Do.SPred.of_and_imp`: σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜False⌝.
theorem of_and_imp_6 : ¬ drop0% Std.Do.SPred.of_and_imp 6 := by spred_cex

-- `Std.Do.SPred.pure_elim`: σs := [], Q := ⌜True⌝, R := ⌜False⌝, φ := False.
theorem pure_elim_4 : ¬ drop0% Std.Do.SPred.pure_elim 4 := by spred_cex

-- `Std.Do.SPred.pure_elim`: σs := [], Q := ⌜True⌝, R := ⌜False⌝, φ := True.
theorem pure_elim_5 : ¬ drop0% Std.Do.SPred.pure_elim 5 := by spred_cex

-- `Std.Do.SPred.pure_elim_l`: σs := [], Q := ⌜True⌝, R := ⌜False⌝, φ := True.
theorem pure_elim_l_4 : ¬ drop0% Std.Do.SPred.pure_elim_l 4 := by spred_cex

-- `Std.Do.SPred.pure_elim_r`: σs := [], Q := ⌜True⌝, R := ⌜False⌝, φ := True.
theorem pure_elim_r_4 : ¬ drop0% Std.Do.SPred.pure_elim_r 4 := by spred_cex

-- `Std.Do.SPred.apply_pure_cons_entails_l`: σs := [], Q := ⌜False⌝, φ := True, σ := Unit, s := default.
theorem apply_pure_cons_entails_l_5 : ¬ drop0% Std.Do.SPred.apply_pure_cons_entails_l 5 := by spred_cex

-- `Std.Do.SPred.apply_pure_cons_entails_r`: σs := [], P := ⌜True⌝, φ := False, σ := Unit, s := default.
theorem apply_pure_cons_entails_r_5 : ¬ drop0% Std.Do.SPred.apply_pure_cons_entails_r 5 := by spred_cex

-- `Std.Do.SPred.Tactic.IsPure.to_pure`: σs := [], P := ⌜True⌝, φ := False.
theorem Tactic_IsPure_to_pure_3 : ¬ drop0% Std.Do.SPred.Tactic.IsPure.to_pure 3 := by spred_cex

-- `Std.Do.SPred.Tactic.instIsPure`: φ := True, σ := Unit, s := default, σs := [], P := ⌜False⌝.
theorem Tactic_instIsPure_5 : ¬ drop0% Std.Do.SPred.Tactic.instIsPure 5 := by spred_cex

-- `Std.Do.SPred.Tactic.instIsPure_1`: φ := True, σ := Unit, σs := [], P := ⌜False⌝.
theorem Tactic_instIsPure_1_4 : ¬ drop0% Std.Do.SPred.Tactic.instIsPure_1 4 := by spred_cex

-- `Std.Do.SPred.Tactic.IsAnd.to_and`: σs := [], P := ⌜True⌝, Q₁ := { down := True }, Q₂ := { down := False }.
theorem Tactic_IsAnd_to_and_4 : ¬ drop0% Std.Do.SPred.Tactic.IsAnd.to_and 4 := by spred_cex

-- `Std.Do.SPred.Tactic.instIsAnd`: σ := Unit, σs := [], P := fun a => ⌜True⌝, Q₁ := fun a => ⌜True⌝, Q₂ := fun a => ⌜False⌝.
theorem Tactic_instIsAnd_5 : ¬ drop0% Std.Do.SPred.Tactic.instIsAnd 5 := by spred_cex

-- `Std.Do.SPred.Tactic.ProofMode.start_entails`: σs := [], P := ⌜True⌝, φ := False.
theorem Tactic_ProofMode_start_entails_3 : ¬ drop0% Std.Do.SPred.Tactic.ProofMode.start_entails 3 := by spred_cex

-- `Std.Do.SPred.Tactic.ProofMode.elim_entails`: σs := [], P := ⌜False⌝, φ := True.
theorem Tactic_ProofMode_elim_entails_3 : ¬ drop0% Std.Do.SPred.Tactic.ProofMode.elim_entails 3 := by spred_cex

-- `Std.Do.SPred.Tactic.Assumption.left`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem Tactic_Assumption_left_4 : ¬ drop0% Std.Do.SPred.Tactic.Assumption.left 4 := by spred_cex

-- `Std.Do.SPred.Tactic.Assumption.right`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem Tactic_Assumption_right_4 : ¬ drop0% Std.Do.SPred.Tactic.Assumption.right 4 := by spred_cex

-- `Std.Do.SPred.Tactic.Cases.add_goal`: σs := [], P := ⌜False⌝, Q := ⌜True⌝, H := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Cases_add_goal_5 : ¬ drop0% Std.Do.SPred.Tactic.Cases.add_goal 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Cases.add_goal`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, H := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Cases_add_goal_6 : ¬ drop0% Std.Do.SPred.Tactic.Cases.add_goal 6 := by spred_cex

-- `Std.Do.SPred.Tactic.Cases.clear`: σs := [], Q := ⌜True⌝, H := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Cases_clear_4 : ¬ drop0% Std.Do.SPred.Tactic.Cases.clear 4 := by spred_cex

-- `Std.Do.SPred.Tactic.Cases.pure`: σs := [], Q := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Cases_pure_3 : ¬ drop0% Std.Do.SPred.Tactic.Cases.pure 3 := by spred_cex

-- `Std.Do.SPred.Tactic.Cases.and_1`: σs := [], Q := ⌜True⌝, H₁' := ⌜True⌝, H₂' := ⌜True⌝, H₁₂' := ⌜False⌝, T := ⌜False⌝.
theorem Tactic_Cases_and_1_6 : ¬ drop0% Std.Do.SPred.Tactic.Cases.and_1 6 := by spred_cex

-- `Std.Do.SPred.Tactic.Cases.and_1`: σs := [], Q := ⌜True⌝, H₁' := ⌜True⌝, H₂' := ⌜True⌝, H₁₂' := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Cases_and_1_7 : ¬ drop0% Std.Do.SPred.Tactic.Cases.and_1 7 := by spred_cex

-- `Std.Do.SPred.Tactic.Cases.and_2`: σs := [], Q := ⌜True⌝, H₁' := ⌜True⌝, H₂ := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Cases_and_2_5 : ¬ drop0% Std.Do.SPred.Tactic.Cases.and_2 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Cases.and_3`: σs := [], Q := ⌜True⌝, H₁ := ⌜True⌝, H₂ := ⌜False⌝, H := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Cases_and_3_6 : ¬ drop0% Std.Do.SPred.Tactic.Cases.and_3 6 := by spred_cex

-- `Std.Do.SPred.Tactic.Cases.and_3`: σs := [], Q := ⌜True⌝, H₁ := ⌜True⌝, H₂ := ⌜True⌝, H := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Cases_and_3_7 : ¬ drop0% Std.Do.SPred.Tactic.Cases.and_3 7 := by spred_cex

-- `Std.Do.SPred.Tactic.Cases.exists`: σs := [], α := True, Q := ⌜True⌝, ψ := fun a => ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Cases_exists_5 : ¬ drop0% Std.Do.SPred.Tactic.Cases.exists 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Clear.clear`: σs := [], P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜False⌝.
theorem Tactic_Clear_clear_5 : ¬ drop0% Std.Do.SPred.Tactic.Clear.clear 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Clear.clear`: σs := [], P := ⌜True⌝, P' := ⌜True⌝, A := ⌜True⌝, Q := ⌜False⌝.
theorem Tactic_Clear_clear_6 : ¬ drop0% Std.Do.SPred.Tactic.Clear.clear 6 := by spred_cex

-- `Std.Do.SPred.Tactic.Exact.assumption`: σs := [], P := ⌜True⌝, A := ⌜False⌝.
theorem Tactic_Exact_assumption_4 : ¬ drop0% Std.Do.SPred.Tactic.Exact.assumption 4 := by spred_cex

-- `Std.Do.SPred.Tactic.Exact.from_tautology`: σs := [], φ := True, P := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Exact_from_tautology_4 : ¬ drop0% Std.Do.SPred.Tactic.Exact.from_tautology 4 := by spred_cex

-- `Std.Do.SPred.Tactic.Focus.left`: σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜True⌝, C := ⌜True⌝, R := ⌜False⌝.
theorem Tactic_Focus_left_6 : ¬ drop0% Std.Do.SPred.Tactic.Focus.left 6 := by spred_cex

-- `Std.Do.SPred.Tactic.Focus.left`: σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜True⌝, C := ⌜False⌝, R := ⌜True⌝.
theorem Tactic_Focus_left_7 : ¬ drop0% Std.Do.SPred.Tactic.Focus.left 7 := by spred_cex

-- `Std.Do.SPred.Tactic.Focus.right`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜True⌝, C := ⌜True⌝, R := ⌜False⌝.
theorem Tactic_Focus_right_6 : ¬ drop0% Std.Do.SPred.Tactic.Focus.right 6 := by spred_cex

-- `Std.Do.SPred.Tactic.Focus.right`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜True⌝, C := ⌜False⌝, R := ⌜True⌝.
theorem Tactic_Focus_right_7 : ¬ drop0% Std.Do.SPred.Tactic.Focus.right 7 := by spred_cex

-- `Std.Do.SPred.Tactic.Focus.rewrite_hyps`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, R := ⌜False⌝.
theorem Tactic_Focus_rewrite_hyps_4 : ¬ drop0% Std.Do.SPred.Tactic.Focus.rewrite_hyps 4 := by spred_cex

-- `Std.Do.SPred.Tactic.Focus.rewrite_hyps`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem Tactic_Focus_rewrite_hyps_5 : ¬ drop0% Std.Do.SPred.Tactic.Focus.rewrite_hyps 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Have.dup`: σs := [], P := ⌜True⌝, H := ⌜False⌝, T := ⌜False⌝.
theorem Tactic_Have_dup_5 : ¬ drop0% Std.Do.SPred.Tactic.Have.dup 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Have.dup`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, H := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Have_dup_6 : ¬ drop0% Std.Do.SPred.Tactic.Have.dup 6 := by spred_cex

-- `Std.Do.SPred.Tactic.Have.have`: σs := [], P := ⌜True⌝, H := ⌜True⌝, PH := ⌜False⌝, T := ⌜False⌝.
theorem Tactic_Have_have_5 : ¬ drop0% Std.Do.SPred.Tactic.Have.have 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Have.have`: σs := [], P := ⌜True⌝, H := ⌜False⌝, PH := ⌜False⌝, T := ⌜False⌝.
theorem Tactic_Have_have_6 : ¬ drop0% Std.Do.SPred.Tactic.Have.have 6 := by spred_cex

-- `Std.Do.SPred.Tactic.Have.have`: σs := [], P := ⌜True⌝, H := ⌜True⌝, PH := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Have_have_7 : ¬ drop0% Std.Do.SPred.Tactic.Have.have 7 := by spred_cex

-- `Std.Do.SPred.Tactic.Have.replace`: σs := [], P := ⌜False⌝, H' := ⌜True⌝, PH := ⌜True⌝, PH' := ⌜False⌝, T := ⌜False⌝.
theorem Tactic_Have_replace_7 : ¬ drop0% Std.Do.SPred.Tactic.Have.replace 7 := by spred_cex

-- `Std.Do.SPred.Tactic.Have.replace`: σs := [], P := ⌜True⌝, H := ⌜True⌝, H' := ⌜True⌝, PH := ⌜True⌝, PH' := ⌜False⌝, T := ⌜False⌝.
theorem Tactic_Have_replace_8 : ¬ drop0% Std.Do.SPred.Tactic.Have.replace 8 := by spred_cex

-- `Std.Do.SPred.Tactic.Have.replace`: σs := [], P := ⌜True⌝, H := ⌜True⌝, H' := ⌜False⌝, PH := ⌜True⌝, PH' := ⌜False⌝, T := ⌜False⌝.
theorem Tactic_Have_replace_9 : ¬ drop0% Std.Do.SPred.Tactic.Have.replace 9 := by spred_cex

-- `Std.Do.SPred.Tactic.Have.replace`: σs := [], P := ⌜True⌝, H := ⌜True⌝, H' := ⌜True⌝, PH := ⌜True⌝, PH' := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Have_replace_10 : ¬ drop0% Std.Do.SPred.Tactic.Have.replace 10 := by spred_cex

-- `Std.Do.SPred.Tactic.Intro.intro`: σs := [], P := ⌜False⌝, Q := ⌜True⌝, H := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Intro_intro_5 : ¬ drop0% Std.Do.SPred.Tactic.Intro.intro 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Intro.intro`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, H := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Intro_intro_6 : ¬ drop0% Std.Do.SPred.Tactic.Intro.intro 6 := by spred_cex

-- `Std.Do.SPred.Tactic.Revert.and_pure_intro_r`: σs := [], φ := False, P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜False⌝.
theorem Tactic_Revert_and_pure_intro_r_5 : ¬ drop0% Std.Do.SPred.Tactic.Revert.and_pure_intro_r 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Revert.and_pure_intro_r`: σs := [], φ := True, P := ⌜True⌝, P' := ⌜False⌝, Q := ⌜False⌝.
theorem Tactic_Revert_and_pure_intro_r_6 : ¬ drop0% Std.Do.SPred.Tactic.Revert.and_pure_intro_r 6 := by spred_cex

-- `Std.Do.SPred.Tactic.Revert.and_pure_intro_r`: σs := [], φ := True, P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜False⌝.
theorem Tactic_Revert_and_pure_intro_r_7 : ¬ drop0% Std.Do.SPred.Tactic.Revert.and_pure_intro_r 7 := by spred_cex

-- `Std.Do.SPred.Tactic.Pure.thm`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, T := ⌜False⌝, φ := False.
theorem Tactic_Pure_thm_5 : ¬ drop0% Std.Do.SPred.Tactic.Pure.thm 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Pure.thm`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, T := ⌜False⌝, φ := True.
theorem Tactic_Pure_thm_6 : ¬ drop0% Std.Do.SPred.Tactic.Pure.thm 6 := by spred_cex

-- `Std.Do.SPred.Tactic.Pure.intro`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, φ := True.
theorem Tactic_Pure_intro_4 : ¬ drop0% Std.Do.SPred.Tactic.Pure.intro 4 := by spred_cex

-- `Std.Do.SPred.Tactic.Pure.intro`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, φ := False.
theorem Tactic_Pure_intro_5 : ¬ drop0% Std.Do.SPred.Tactic.Pure.intro 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Revert.revert`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, H := ⌜False⌝, T := ⌜False⌝.
theorem Tactic_Revert_revert_5 : ¬ drop0% Std.Do.SPred.Tactic.Revert.revert 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Revert.revert`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, H := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Revert_revert_6 : ¬ drop0% Std.Do.SPred.Tactic.Revert.revert 6 := by spred_cex

-- `Std.Do.SPred.Tactic.Specialize.imp_stateful`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, R := ⌜False⌝.
theorem Tactic_Specialize_imp_stateful_5 : ¬ drop0% Std.Do.SPred.Tactic.Specialize.imp_stateful 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Specialize.imp_pure`: σs := [], φ := True, P := ⌜True⌝, Q := ⌜False⌝, R := ⌜False⌝.
theorem Tactic_Specialize_imp_pure_5 : ¬ drop0% Std.Do.SPred.Tactic.Specialize.imp_pure 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Specialize.pure_start`: σs := [], φ := True, H := ⌜False⌝, P := ⌜True⌝, T := ⌜False⌝.
theorem Tactic_Specialize_pure_start_5 : ¬ drop0% Std.Do.SPred.Tactic.Specialize.pure_start 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Specialize.pure_taut`: σs := [], φ := True, P := ⌜False⌝.
theorem Tactic_Specialize_pure_taut_3 : ¬ drop0% Std.Do.SPred.Tactic.Specialize.pure_taut 3 := by spred_cex

-- `Std.Do.SPred.Tactic.Specialize.pure_taut`: σs := [], φ := False, P := ⌜False⌝.
theorem Tactic_Specialize_pure_taut_4 : ¬ drop0% Std.Do.SPred.Tactic.Specialize.pure_taut 4 := by spred_cex

-- `Std.Do.SPred.Tactic.Specialize.focus`: σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜False⌝, R := ⌜False⌝.
theorem Tactic_Specialize_focus_5 : ¬ drop0% Std.Do.SPred.Tactic.Specialize.focus 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Specialize.focus`: σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem Tactic_Specialize_focus_6 : ¬ drop0% Std.Do.SPred.Tactic.Specialize.focus 6 := by spred_cex

-- `Std.Do.SPred.Tactic.SimpAnd.simp_and`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, PQ := { down := False }.
theorem Tactic_SimpAnd_simp_and_4 : ¬ drop0% Std.Do.SPred.Tactic.SimpAnd.simp_and 4 := by spred_cex

-- `Std.Do.SPred.Tactic.HasFrame.reassoc`: σs := [], P := ⌜True⌝, P' := { down := True }, φ := False.
theorem Tactic_HasFrame_reassoc_4 : ¬ drop0% Std.Do.SPred.Tactic.HasFrame.reassoc 4 := by spred_cex

-- `Std.Do.SPred.Tactic.instHasFrameAndOfSimpAnd`: φ := True, σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜False⌝, QP := ⌜False⌝.
theorem Tactic_instHasFrameAndOfSimpAnd_6 : ¬ drop0% Std.Do.SPred.Tactic.instHasFrameAndOfSimpAnd 6 := by spred_cex

-- `Std.Do.SPred.Tactic.instHasFrameAndOfSimpAnd`: φ := True, σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜True⌝, QP := ⌜False⌝.
theorem Tactic_instHasFrameAndOfSimpAnd_7 : ¬ drop0% Std.Do.SPred.Tactic.instHasFrameAndOfSimpAnd 7 := by spred_cex

-- `Std.Do.SPred.Tactic.instHasFrameAndOfSimpAnd_1`: φ := True, σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q' := ⌜False⌝, PQ := ⌜False⌝.
theorem Tactic_instHasFrameAndOfSimpAnd_1_6 : ¬ drop0% Std.Do.SPred.Tactic.instHasFrameAndOfSimpAnd_1 6 := by spred_cex

-- `Std.Do.SPred.Tactic.instHasFrameAndOfSimpAnd_1`: φ := True, σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q' := ⌜True⌝, PQ := ⌜False⌝.
theorem Tactic_instHasFrameAndOfSimpAnd_1_7 : ¬ drop0% Std.Do.SPred.Tactic.instHasFrameAndOfSimpAnd_1 7 := by spred_cex

-- `Std.Do.SPred.Tactic.instHasFramePureAndOfAnd`: φ := True, σs := [], P := True, P' := True, Q := ⌜False⌝.
theorem Tactic_instHasFramePureAndOfAnd_5 : ¬ drop0% Std.Do.SPred.Tactic.instHasFramePureAndOfAnd 5 := by spred_cex

-- `Std.Do.SPred.Tactic.instHasFrameCurryULiftPropUpAndOfAnd`: φ := True, σs := [], P := fun a => True, P' := fun a => True, Q := ⌜False⌝.
theorem Tactic_instHasFrameCurryULiftPropUpAndOfAnd_5 : ¬ drop0% Std.Do.SPred.Tactic.instHasFrameCurryULiftPropUpAndOfAnd 5 := by spred_cex

-- `Std.Do.SPred.Tactic.instHasFrameAndAndOfSimpAnd`: φ := True, ψ := True, σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜False⌝, Q' := ⌜True⌝, QQ := ⌜False⌝.
theorem Tactic_instHasFrameAndAndOfSimpAnd_8 : ¬ drop0% Std.Do.SPred.Tactic.instHasFrameAndAndOfSimpAnd 8 := by spred_cex

-- `Std.Do.SPred.Tactic.instHasFrameAndAndOfSimpAnd`: φ := True, ψ := True, σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜False⌝, QQ := ⌜False⌝.
theorem Tactic_instHasFrameAndAndOfSimpAnd_9 : ¬ drop0% Std.Do.SPred.Tactic.instHasFrameAndAndOfSimpAnd 9 := by spred_cex

-- `Std.Do.SPred.Tactic.instHasFrameAndAndOfSimpAnd`: φ := True, ψ := True, σs := [], P := ⌜True⌝, P' := ⌜True⌝, Q := ⌜True⌝, Q' := ⌜True⌝, QQ := ⌜False⌝.
theorem Tactic_instHasFrameAndAndOfSimpAnd_10 : ¬ drop0% Std.Do.SPred.Tactic.instHasFrameAndAndOfSimpAnd 10 := by spred_cex

-- `Std.Do.SPred.Tactic.instHasFrameAndPureAnd`: φ := True, ψ := True, σs := [], P := ⌜True⌝, Q := ⌜False⌝.
theorem Tactic_instHasFrameAndPureAnd_5 : ¬ drop0% Std.Do.SPred.Tactic.instHasFrameAndPureAnd 5 := by spred_cex

-- `Std.Do.SPred.Tactic.instHasFrameAndPureAnd_1`: φ := True, ψ := True, σs := [], P := ⌜True⌝, Q := ⌜False⌝.
theorem Tactic_instHasFrameAndPureAnd_1_5 : ¬ drop0% Std.Do.SPred.Tactic.instHasFrameAndPureAnd_1 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Frame.frame`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, T := ⌜False⌝, φ := False.
theorem Tactic_Frame_frame_5 : ¬ drop0% Std.Do.SPred.Tactic.Frame.frame 5 := by spred_cex

-- `Std.Do.SPred.Tactic.Frame.frame`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, T := ⌜False⌝, φ := True.
theorem Tactic_Frame_frame_6 : ¬ drop0% Std.Do.SPred.Tactic.Frame.frame 6 := by spred_cex

-- `Std.Do.SPred.entails.trans`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, R := ⌜False⌝.
theorem entails_trans_4 : ¬ drop0% Std.Do.SPred.entails.trans 4 := by spred_cex

-- `Std.Do.SPred.entails.trans`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem entails_trans_5 : ¬ drop0% Std.Do.SPred.entails.trans 5 := by spred_cex

-- `Std.Do.SPred.bientails.trans`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, R := ⌜False⌝.
theorem bientails_trans_4 : ¬ drop0% Std.Do.SPred.bientails.trans 4 := by spred_cex

-- `Std.Do.SPred.bientails.trans`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem bientails_trans_5 : ¬ drop0% Std.Do.SPred.bientails.trans 5 := by spred_cex

-- `Std.Do.SPred.bientails.symm`: σs := [], P := ⌜True⌝, Q := ⌜False⌝.
theorem bientails_symm_3 : ¬ drop0% Std.Do.SPred.bientails.symm 3 := by spred_cex

-- `Std.Do.SPred.pure_intro`: σs := [], φ := False, P := ⌜True⌝.
theorem pure_intro_3 : ¬ drop0% Std.Do.SPred.pure_intro 3 := by spred_cex

-- `Std.Do.SPred.pure_elim'`: σs := [], φ := True, P := ⌜False⌝.
theorem pure_elim'_3 : ¬ drop0% Std.Do.SPred.pure_elim' 3 := by spred_cex

-- `Std.Do.SPred.and_intro`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, R := ⌜True⌝.
theorem and_intro_4 : ¬ drop0% Std.Do.SPred.and_intro 4 := by spred_cex

-- `Std.Do.SPred.and_intro`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem and_intro_5 : ¬ drop0% Std.Do.SPred.and_intro 5 := by spred_cex

-- `Std.Do.SPred.or_elim`: σs := [], P := ⌜True⌝, Q := ⌜False⌝, R := ⌜False⌝.
theorem or_elim_4 : ¬ drop0% Std.Do.SPred.or_elim 4 := by spred_cex

-- `Std.Do.SPred.or_elim`: σs := [], P := ⌜False⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem or_elim_5 : ¬ drop0% Std.Do.SPred.or_elim 5 := by spred_cex

-- `Std.Do.SPred.imp_intro`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem imp_intro_4 : ¬ drop0% Std.Do.SPred.imp_intro 4 := by spred_cex

-- `Std.Do.SPred.imp_elim`: σs := [], P := ⌜True⌝, Q := ⌜True⌝, R := ⌜False⌝.
theorem imp_elim_4 : ¬ drop0% Std.Do.SPred.imp_elim 4 := by spred_cex

-- `Std.Do.SPred.forall_intro`: σs := [], α := True, P := ⌜True⌝, Ψ := fun a => ⌜False⌝.
theorem forall_intro_4 : ¬ drop0% Std.Do.SPred.forall_intro 4 := by spred_cex

-- `Std.Do.SPred.exists_elim`: σs := [], α := True, Φ := fun a => ⌜True⌝, Q := ⌜False⌝.
theorem exists_elim_4 : ¬ drop0% Std.Do.SPred.exists_elim 4 := by spred_cex

-- `Std.Do.SPred.entails_nil_intro`: P := ⌜True⌝, Q := ⌜False⌝.
theorem entails_nil_intro_2 : ¬ drop0% Std.Do.SPred.entails_nil_intro 2 := by spred_cex

-- `Std.Do.SPred.entails_nil_pure_intro`: φ := True, Q := ⌜False⌝.
theorem entails_nil_pure_intro_2 : ¬ drop0% Std.Do.SPred.entails_nil_pure_intro 2 := by spred_cex

-- `Std.Do.SPred.entails_cons_intro`: σs := [], σ := Unit, P := ⌜True⌝, Q := ⌜False⌝.
theorem entails_cons_intro_4 : ¬ drop0% Std.Do.SPred.entails_cons_intro 4 := by spred_cex

-- `Std.Do.SPred.bientails_cons_intro`: σs := [], σ := Unit, P := ⌜True⌝, Q := ⌜False⌝.
theorem bientails_cons_intro_4 : ¬ drop0% Std.Do.SPred.bientails_cons_intro 4 := by spred_cex

end DoSPredHand
