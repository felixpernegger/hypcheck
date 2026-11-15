import Std
import Lean

/-!
Hand pass `WPSoundIndep` (hand17, 2026-11-08): the `[LawfulMonad m]` premises of the three
`WPSound` lifting instances (`Std.Do.instWPSoundStateTArgOfLawfulMonad` idx 4,
`Std.Do.instWPSoundExceptTExceptPureOfLawfulMonad` idx 3,
`Std.Do.instWPSoundOptionTExceptPUnitPureOfLawfulMonad` idx 2) are independent (kind
type-identity). Lean support, both halves:

* Half 1, `CanonX → T'`: if the subtype of the base result type is equal to the lifted type and
  the cast is the canonical map, the base refinement is cast over and `T'` holds without any law
  (bind is natural along equalities). In a model that interprets `Subtype`, `Prod`, `Except` and
  `Option` literally (subtypes as subsets), the identity holds with the cast being the identity,
  so `T'` holds there and its negation is unprovable.
* Half 2, `(type disequalities) → ¬T'`: if no subtype equals a fixed type `B` and the base result
  type differs from `B`, the monad `M γ := γ`, `bind x f := f (θ x)`, `wp x Q := Q (θ x)` with
  `θ` the identity except constant on `B` is `WPSound` but its lift is not. In the standard
  set-theoretic model with tagged constructors these disequalities hold, so `T'` is unprovable.

Both hypotheses are statements about type identity that Lean neither proves nor refutes.
The models are by Fable (chat, 2026-11-08); the Lean support is checked here.
The three `same_as_drop%` checks at the end confirm that the half-1 conclusions are exactly the
library statements with the premise dropped; the half-2 statements use `drop0%` directly.

Run with the lean4 repo's stage1 binary: `runs/hand15/lean.sh checks/WPSoundIndepHand.lean`.
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

open Std.Do

namespace WPSoundIndepHand

universe u v

/-! ### Half 1: `T'` from a canonical type identity

Under the hypothesis that the subtype of the base result type *is* the lifted type, with `cast`
the canonical map, the base refinement is cast to the lifted type; `bind` is natural along
equalities (`subst`), so no monad law is used. -/

/-- `bind` is natural along type equalities. -/
theorem cast_bind {m : Type u → Type v} [Bind m] {A B β : Type u} (h : A = B) (X : m A)
    (G : B → m β) : cast (congrArg m h) X >>= G = X >>= (fun a => G (cast h a)) := by
  subst h; rfl

/-- The StateT canonical identity: `{p : α × σ // P p.1} = {a // P a} × σ` with `cast = φ`. -/
def CanonState : Prop := ∀ (α σ : Type u) (P : α → Prop),
  ∃ h : {p : α × σ // P p.1} = ({a // P a} × σ),
    ∀ p, cast h p = (⟨p.val.1, p.property⟩, p.val.2)

/-- The ExceptT canonical identity. -/
def CanonExcept : Prop := ∀ (ε α : Type u) (P : α → Prop),
  ∃ h : {r : Except ε α // match r with | .ok a => P a | .error _ => True} = Except ε {a // P a},
    ∀ r, cast h r = (match r with
      | ⟨.ok a, hp⟩ => .ok ⟨a, hp⟩
      | ⟨.error e, _⟩ => .error e)

/-- The OptionT canonical identity. -/
def CanonOption : Prop := ∀ (α : Type u) (P : α → Prop),
  ∃ h : {r : Option α // match r with | some a => P a | none => True} = Option {a // P a},
    ∀ r, cast h r = (match r with
      | ⟨some a, hp⟩ => some ⟨a, hp⟩
      | ⟨none, _⟩ => none)

-- `Std.Do.instWPSoundStateTArgOfLawfulMonad`: `[LawfulMonad m]` is unnecessary under the
-- canonical identity `CanonState` (type-identity half 1).
theorem stateT_of_canon (hc : CanonState.{u}) :
    ∀ {m : Type u → Type v} {ps : PostShape.{u}} {σ : Type u} [Monad m] [WP m ps] [WPSound m ps],
      WPSound (StateT σ m) (.arg σ ps) := by
  intro m ps σ _ _ _
  refine ⟨fun {α} {x} {P} hwp => ?_⟩
  obtain ⟨X, hX⟩ := Classical.skolem.mp fun s =>
    (WPSound.ensures_of_wp (m := m) (ps := ps) (hwp s)).exists_refinement
  obtain ⟨h, hcast⟩ := hc α σ P
  refine ⟨⟨fun s => cast (congrArg m h) (X s), ⟨fun {β} k => funext fun s => ?_⟩⟩⟩
  show cast (congrArg m h) (X s) >>= (fun (b : {a // P a} × σ) => (k b.1.val).run b.2) =
       x.run s >>= (fun (a : α × σ) => (k a.1).run a.2)
  rw [cast_bind h]
  simp only [hcast]
  exact (hX s).bind_eq (fun r : α × σ => (k r.1).run r.2)

-- `Std.Do.instWPSoundExceptTExceptPureOfLawfulMonad`: `[LawfulMonad m]` is unnecessary under
-- `CanonExcept` (type-identity half 1).
theorem exceptT_of_canon (hc : CanonExcept.{u}) :
    ∀ {m : Type u → Type v} {ε : Type u} [Monad m] [WP m .pure] [WPSound m .pure],
      WPSound (ExceptT ε m) (.except ε .pure) := by
  intro m ε _ _ _
  refine ⟨fun {α} {x} {P} hwp => ?_⟩
  have hwp_inner : ⊢ₛ wp⟦x.run⟧
      (⇓? r => ⌜match r with | .ok a => P a | .error _ => True⌝) := by
    simp only [WP.wp, PredTrans.apply_pushExcept, ExceptConds.fst_true, ExceptConds.snd_true] at hwp
    apply SPred.entails.trans hwp; apply (wp x.run).mono
    simp [PostCond.entails]; intro r <;> cases r <;> simp
  obtain ⟨X, hX⟩ := (WPSound.ensures_of_wp (m := m) (ps := .pure) hwp_inner).exists_refinement
  obtain ⟨h, hcast⟩ := hc ε α P
  refine ⟨⟨ExceptT.mk (cast (congrArg m h) X), ⟨fun {β} k => ?_⟩⟩⟩
  show ExceptT.mk _ >>= _ = x >>= k
  simp only [Bind.bind, ExceptT.bind, ExceptT.mk]
  have := cast_bind h X (ExceptT.bindCont (fun a => k a.val))
  rw [this]
  refine Eq.trans ?_ (hX.bind_eq (β := Except ε β) (ExceptT.bindCont k))
  congr 1
  funext r
  rw [hcast r]
  rcases r with ⟨(e | a), hp⟩ <;> rfl

-- `Std.Do.instWPSoundOptionTExceptPUnitPureOfLawfulMonad`: `[LawfulMonad m]` is unnecessary
-- under `CanonOption` (type-identity half 1).
theorem optionT_of_canon (hc : CanonOption.{u}) :
    ∀ {m : Type u → Type v} [Monad m] [WP m .pure] [WPSound m .pure],
      WPSound (OptionT m) (.except PUnit .pure) := by
  intro m _ _ _
  refine ⟨fun {α} {x} {P} hwp => ?_⟩
  have hwp_inner : ⊢ₛ wp⟦x.run⟧
      (⇓? r => ⌜match r with | some a => P a | none => True⌝) := by
    simp only [WP.wp, PredTrans.apply_pushOption, ExceptConds.fst_true, ExceptConds.snd_true] at hwp
    apply SPred.entails.trans hwp; apply (wp x.run).mono
    simp [PostCond.entails]; intro r <;> cases r <;> simp
  obtain ⟨X, hX⟩ := (WPSound.ensures_of_wp (m := m) (ps := .pure) hwp_inner).exists_refinement
  obtain ⟨h, hcast⟩ := hc α P
  refine ⟨⟨OptionT.mk (cast (congrArg m h) X), ⟨fun {β} k => ?_⟩⟩⟩
  show OptionT.mk _ >>= _ = x >>= k
  simp only [Bind.bind, OptionT.bind, OptionT.mk]
  rw [cast_bind h]
  refine Eq.trans ?_
    (hX.bind_eq (β := Option β) (fun r => match r with | some a => (k a).run | none => pure none))
  congr 1
  funext r
  rw [hcast r]
  rcases r with ⟨(_ | a), hp⟩ <;> rfl

/-! ### Half 2: `¬T'` from a type disequality

The model: carrier `M γ := γ`, `bind x f := f (θ x)`, `wp x Q := Q (θ x)`, where `θ` is the
identity except on one fixed type `B`, where it is constant. Base soundness needs that no subtype
is `B`; the lift fails at the base type `Bool × Bool` (resp. `Except Unit Bool`, `Option Bool`),
which must also differ from `B`. Both disequalities are unprovable in Lean but hold in the
standard set-theoretic model. -/

section Model
variable (B : Type) (b₀ : B)

/-- Identity except on `B`, where it is constantly `b₀`. -/
noncomputable def θ (γ : Type) (x : γ) : γ :=
  @dite _ (γ = B) (Classical.propDecidable _) (fun h => cast h.symm b₀) (fun _ => x)

theorem θ_ne {γ : Type} (h : γ ≠ B) (x : γ) : θ B b₀ γ x = x := by
  unfold θ; split
  · exact absurd ‹_› h
  · rfl

theorem θ_B (x : B) : θ B b₀ B x = b₀ := by
  unfold θ; split
  · rfl
  · exact absurd rfl ‹_›

/-- The carrier. -/
def M (_B : Type) (_b₀ : _B) (α : Type) : Type := α

noncomputable instance instMonadM : Monad (M B b₀) where
  pure a := a
  bind x f := f (θ B b₀ _ x)

noncomputable instance instWPM : WP (M B b₀) .pure where
  wp x := ⟨fun Q => Q.1 (θ B b₀ _ x),
    fun _ _ => ⟨fun h => h, fun h => h⟩⟩

theorem soundM (hS : ∀ (γ : Type) (P : γ → Prop), ({a // P a} : Type) ≠ B) :
    WPSound (M B b₀) .pure where
  ensures_of_wp {γ} {x} {P} hwp := by
    have hp : P (θ B b₀ γ x) := hwp True.intro
    refine ⟨⟨(⟨θ B b₀ γ x, hp⟩ : {a // P a}), ⟨fun {β} k => ?_⟩⟩⟩
    show k (θ B b₀ _ (⟨θ B b₀ γ x, hp⟩ : {a // P a})).val = k (θ B b₀ γ x)
    rw [θ_ne B b₀ (hS γ P)]

end Model

/-- The distinguished type for the StateT refutation. -/
abbrev BS : Type := {a : Bool // a = true} × Bool

-- `Std.Do.instWPSoundStateTArgOfLawfulMonad`: `[LawfulMonad m]` is necessary if no subtype equals
-- `{a : Bool // a = true} × Bool` and `Bool × Bool` does not either (type-identity half 2).
theorem stateT_not_of_ne (hS : ∀ (γ : Type) (P : γ → Prop), ({a // P a} : Type) ≠ BS)
    (hBB : (Bool × Bool : Type) ≠ BS) :
    ¬ drop0% Std.Do.instWPSoundStateTArgOfLawfulMonad 4 := by
  intro H
  let b₀ : BS := (⟨true, rfl⟩, false)
  have hs := soundM BS b₀ hS
  have hl := @H (M BS b₀) .pure Bool (instMonadM BS b₀) (instWPM BS b₀) hs
  let x : StateT Bool (M BS b₀) Bool := fun _ => ((true, true) : Bool × Bool)
  have hwp : ⊢ₛ wp⟦x⟧ (⇓? a => ⌜a = true⌝) := by
    intro s _
    show (θ BS b₀ (Bool × Bool) (true, true)).1 = true
    rw [θ_ne BS b₀ hBB]
  obtain ⟨Y, hY⟩ := (hl.ensures_of_wp hwp).exists_refinement
  have h0 := congrFun (hY.bind_eq (β := Unit) (fun _ s' => (((), s') : Unit × Bool))) true
  have h1 : (θ BS b₀ BS (Y true)).2 = (θ BS b₀ (Bool × Bool) (true, true)).2 :=
    congrArg Prod.snd h0
  have e1 : θ BS b₀ BS (Y true) = b₀ := θ_B BS b₀ (Y true)
  have e2 : θ BS b₀ (Bool × Bool) (true, true) = (true, true) := θ_ne BS b₀ hBB _
  rw [e1, e2] at h1
  exact Bool.noConfusion h1

/-- The distinguished type for the ExceptT refutation. -/
abbrev BE : Type := Except Unit {a : Bool // True}

-- `Std.Do.instWPSoundExceptTExceptPureOfLawfulMonad`: `[LawfulMonad m]` is necessary if no subtype
-- equals `Except Unit {a : Bool // True}` and `Except Unit Bool` does not either (type-identity half 2).
theorem exceptT_not_of_ne (hS : ∀ (γ : Type) (P : γ → Prop), ({a // P a} : Type) ≠ BE)
    (hBE : (Except Unit Bool : Type) ≠ BE) :
    ¬ drop0% Std.Do.instWPSoundExceptTExceptPureOfLawfulMonad 3 := by
  intro H
  let b₀ : BE := .ok ⟨false, trivial⟩
  have hs := soundM BE b₀ hS
  have hl := @H (M BE b₀) Unit (instMonadM BE b₀) (instWPM BE b₀) hs
  let x : ExceptT Unit (M BE b₀) Bool :=
    ExceptT.mk (show M BE b₀ (Except Unit Bool) from Except.ok true)
  have e2 : θ BE b₀ (Except Unit Bool) x.run = Except.ok true := θ_ne BE b₀ hBE _
  have hwp : ⊢ₛ wp⟦x⟧ (⇓? a => ⌜True⌝) := by
    intro _
    simp only [WP.wp, PredTrans.apply_pushExcept, PredTrans.apply, e2]
    exact True.intro
  obtain ⟨Y, hY⟩ := (hl.ensures_of_wp hwp).exists_refinement
  let k : Bool → ExceptT Unit (M BE b₀) Bool :=
    fun a => ExceptT.mk (show M BE b₀ (Except Unit Bool) from Except.ok a)
  have h0 := hY.bind_eq (β := Bool) k
  have h1 : ExceptT.bindCont (fun a : {a : Bool // True} => k a.val) (θ BE b₀ BE Y) =
      ExceptT.bindCont k (θ BE b₀ (Except Unit Bool) x.run) := h0
  have e1 : θ BE b₀ BE Y = b₀ := θ_B BE b₀ Y
  rw [e1, e2] at h1
  have h2 : (Except.ok false : Except Unit Bool) = Except.ok true := h1
  exact Bool.noConfusion (Except.ok.inj h2)

/-- The distinguished type for the OptionT refutation. -/
abbrev BO : Type := Option {a : Bool // True}

-- `Std.Do.instWPSoundOptionTExceptPUnitPureOfLawfulMonad`: `[LawfulMonad m]` is necessary if no
-- subtype equals `Option {a : Bool // True}` and `Option Bool` does not either (type-identity half 2).
theorem optionT_not_of_ne (hS : ∀ (γ : Type) (P : γ → Prop), ({a // P a} : Type) ≠ BO)
    (hBO : (Option Bool : Type) ≠ BO) :
    ¬ drop0% Std.Do.instWPSoundOptionTExceptPUnitPureOfLawfulMonad 2 := by
  intro H
  let b₀ : BO := some ⟨false, trivial⟩
  have hs := soundM BO b₀ hS
  have hl := @H (M BO b₀) (instMonadM BO b₀) (instWPM BO b₀) hs
  let x : OptionT (M BO b₀) Bool := OptionT.mk (show M BO b₀ (Option Bool) from some true)
  have e2 : θ BO b₀ (Option Bool) x.run = some true := θ_ne BO b₀ hBO _
  have hwp : ⊢ₛ wp⟦x⟧ (⇓? a => ⌜True⌝) := by
    intro _
    simp only [WP.wp, PredTrans.apply_pushOption, PredTrans.apply, e2]
    exact True.intro
  obtain ⟨Y, hY⟩ := (hl.ensures_of_wp hwp).exists_refinement
  let k : Bool → OptionT (M BO b₀) Bool :=
    fun a => OptionT.mk (show M BO b₀ (Option Bool) from some a)
  have h0 := hY.bind_eq (β := Bool) k
  simp only [Bind.bind, OptionT.bind, OptionT.mk] at h0
  have e1 : θ BO b₀ (Option {b : Bool // True}) Y = b₀ := θ_B BO b₀ Y
  have e2' : θ BO b₀ (Option Bool) x = some true := e2
  rw [e1, e2'] at h0
  have h2 : (some false : Option Bool) = some true := h0
  exact Bool.noConfusion (Option.some.inj h2)

end WPSoundIndepHand

open Lean Meta Elab Term in
/-- `same_as_drop% c T i`: check that the conclusion of `c` (after its one hypothesis) is `drop% T i`. -/
elab "same_as_drop% " c:ident T:ident i:num : term => do
  let t1 ← elabTerm (← `(drop% $T $i)) none
  let ci ← getConstInfo c.getId
  let ty ← instantiateTypeLevelParams ci.toConstantVal (← ci.levelParams.mapM fun _ => mkFreshLevelMVar)
  let .forallE _ _ body _ := ty | throwError "not a forall"
  if body.hasLooseBVars then throwError "dependent"
  unless ← isDefEq t1 body do throwError "statement differs from drop%"
  logInfo m!"{c.getId}: statement matches drop% {T.getId} {i.getNat}"
  return mkConst ``True

#check same_as_drop% WPSoundIndepHand.stateT_of_canon Std.Do.instWPSoundStateTArgOfLawfulMonad 4
#check same_as_drop% WPSoundIndepHand.exceptT_of_canon Std.Do.instWPSoundExceptTExceptPureOfLawfulMonad 3
#check same_as_drop% WPSoundIndepHand.optionT_of_canon Std.Do.instWPSoundOptionTExceptPUnitPureOfLawfulMonad 2
