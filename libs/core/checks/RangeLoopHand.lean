import Lean
set_option linter.deprecated false

/-!
Hand pass `RangeLoop` (hand11): the last 3 undecided Init.Data hypotheses, `[LawfulMonad n]` of
`Std.Rxc.Iterator.instLawfulIteratorLoop`, `Std.Rxo.Iterator.instLawfulIteratorLoop` and
`Std.Rxi.Iterator.instLawfulIteratorLoop`. All 3 are removable: each declaration proves `T'`
(`drop% T i`, universe-polymorphic).

Why: the custom range loop and `IterM.DefaultConsumers.forIn'` unfold to the same
`bind (f x …) (fun r => match r with …)` at every step. The library proof needs `LawfulMonad n` only
because it goes through `forIn'_eq_wf` and the private `loop_eq_wf`/`loopWf_eq` lemmas. Here both
fixpoints are unfolded with `WellFounded.extrinsicFix₃_eq_apply` (well-founded by `wf`) and compared
by well-founded induction on `IteratorLoop.rel` (`key`). The only facts about `n` used are
`LawfulMonadLiftBindFunction.liftBind_pure` (an assumption of `lawful`) and `congr` on `bind`.
`none_case`: the default loop on an exhausted iterator is `pure acc`.

Run with the lean4 repo's stage1 binary: `lean checks/RangeLoopHand.lean`.
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
/-- `drop0% T i`: like `drop% T i`, with all universes of `T` set to `0` (for `¬` verdicts). -/
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


namespace RangeLoopHand
open Std Std.PRange Std.Iterators

set_option linter.unusedVariables false

-- `Std.Rxc.Iterator.instLawfulIteratorLoop` (hypothesis 8): removable, the custom loop unfolds step by step to the default forIn' without monad laws.
theorem rxc : drop% Std.Rxc.Iterator.instLawfulIteratorLoop 8 := by
  intros α _ _ _ _ _ n _
  refine ⟨?_⟩
  intro lift hlift γ it init Pl wf f
  have none_case : ∀ (P : α → Prop) (g : (b : α) → P b → (c : γ) → n (Subtype (Pl b c)))
      (it : IterM (α := Rxc.Iterator α) Id α) (acc : γ)
      (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b), it.internalState.next = none →
      IterM.DefaultConsumers.forIn' lift γ Pl it acc P hP g = pure acc := by
    intro P g it acc hP hn
    haveI : Nonempty γ := ⟨acc⟩
    rcases it with ⟨⟨nx, ub⟩⟩
    cases hn
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [IterM.step_mk, Rxc.Iterator.Monadic.step_eq_step]
    dsimp only
    rw [hlift.liftBind_pure, Shrink.inflate_deflate]
    simp only [Rxc.Iterator.Monadic.step]
  have key : ∀ (LE' : α → Prop) (hl : ∀ a b : α, a ≤ b → LE' a → LE' b) (ub : α)
      (F : (out : α) → LE' out → out ≤ ub → (c : γ) → n (Subtype (Pl out c)))
      (P : α → Prop) (g : (b : α) → P b → (c : γ) → n (Subtype (Pl b c)))
      (hFg : ∀ a h1 h2 c (p : P a), F a h1 h2 c = g a p c)
      (q : IterM (α := Rxc.Iterator α) Id α × γ) (x : α)
      (hq : q.1 = (⟨⟨some x, ub⟩⟩ : IterM (α := Rxc.Iterator α) Id α)) (h : LE' x)
      (hP : ∀ b, q.1.IsPlausibleIndirectOutput b → P b),
      Rxc.Iterator.instIteratorLoop.loop γ Pl LE' hl ub q.2 x h F =
        IterM.DefaultConsumers.forIn' lift γ Pl q.1 q.2 P hP g := by
    intro LE' hl ub F P g hFg q
    induction q using WellFounded.induction wf with
    | _ q ih => ?_
    intro x hq h hP
    rcases q with ⟨it1, acc⟩
    dsimp only at hq hP ih ⊢
    subst hq
    haveI : Nonempty γ := ⟨acc⟩
    rw [Rxc.Iterator.instIteratorLoop.loop, WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [IterM.step_mk, Rxc.Iterator.Monadic.step_eq_step]
    dsimp only
    rw [hlift.liftBind_pure, Shrink.inflate_deflate]
    by_cases hu : x ≤ ub
    · rw [dif_pos hu]
      simp only [Rxc.Iterator.Monadic.step, if_pos hu]
      congr 1
      · apply hFg
      · funext r
        rcases r with ⟨r, hr⟩
        cases r with
        | done c => rfl
        | yield c =>
          dsimp only
          split
          · next next' hs =>
            refine ih (⟨⟨succ? x, ub⟩⟩, c) ?_ next' (by simp [hs]) _ _
            refine Or.inl ⟨x, ?_, hr⟩
            simp [Rxc.Iterator.Monadic.isPlausibleStep_iff, Rxc.Iterator.Monadic.step, hu]
          · next hs =>
            exact (none_case P g ⟨⟨succ? x, ub⟩⟩ c _ hs).symm
    · rw [dif_neg hu]
      simp only [Rxc.Iterator.Monadic.step, if_neg hu]
  rcases it with ⟨⟨_ | next, ub⟩⟩
  · exact (none_case _ f _ init (fun _ => id) rfl).symm
  · exact key _ _ ub _ _ f (fun _ _ _ _ _ => rfl) (_, init) next rfl _ (fun _ => id)

-- `Std.Rxo.Iterator.instLawfulIteratorLoop` (hypothesis 8): removable, the custom loop unfolds step by step to the default forIn' without monad laws.
theorem rxo : drop% Std.Rxo.Iterator.instLawfulIteratorLoop 8 := by
  intros α _ _ _ _ _ n _
  refine ⟨?_⟩
  intro lift hlift γ it init Pl wf f
  have none_case : ∀ (P : α → Prop) (g : (b : α) → P b → (c : γ) → n (Subtype (Pl b c)))
      (it : IterM (α := Rxo.Iterator α) Id α) (acc : γ)
      (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b), it.internalState.next = none →
      IterM.DefaultConsumers.forIn' lift γ Pl it acc P hP g = pure acc := by
    intro P g it acc hP hn
    haveI : Nonempty γ := ⟨acc⟩
    rcases it with ⟨⟨nx, ub⟩⟩
    cases hn
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [IterM.step_mk, Rxo.Iterator.Monadic.step_eq_step]
    dsimp only
    rw [hlift.liftBind_pure, Shrink.inflate_deflate]
    simp only [Rxo.Iterator.Monadic.step]
  have key : ∀ (LE' : α → Prop) (hl : ∀ a b : α, UpwardEnumerable.LE a b → LE' a → LE' b) (ub : α)
      (F : (out : α) → LE' out → out < ub → (c : γ) → n (Subtype (Pl out c)))
      (P : α → Prop) (g : (b : α) → P b → (c : γ) → n (Subtype (Pl b c)))
      (hFg : ∀ a h1 h2 c (p : P a), F a h1 h2 c = g a p c)
      (q : IterM (α := Rxo.Iterator α) Id α × γ) (x : α)
      (hq : q.1 = (⟨⟨some x, ub⟩⟩ : IterM (α := Rxo.Iterator α) Id α)) (h : LE' x)
      (hP : ∀ b, q.1.IsPlausibleIndirectOutput b → P b),
      Rxo.Iterator.instIteratorLoop.loop γ Pl LE' hl ub q.2 x h F =
        IterM.DefaultConsumers.forIn' lift γ Pl q.1 q.2 P hP g := by
    intro LE' hl ub F P g hFg q
    induction q using WellFounded.induction wf with
    | _ q ih => ?_
    intro x hq h hP
    rcases q with ⟨it1, acc⟩
    dsimp only at hq hP ih ⊢
    subst hq
    haveI : Nonempty γ := ⟨acc⟩
    rw [Rxo.Iterator.instIteratorLoop.loop, WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [IterM.step_mk, Rxo.Iterator.Monadic.step_eq_step]
    dsimp only
    rw [hlift.liftBind_pure, Shrink.inflate_deflate]
    by_cases hu : x < ub
    · rw [dif_pos hu]
      simp only [Rxo.Iterator.Monadic.step, if_pos hu]
      congr 1
      · apply hFg
      · funext r
        rcases r with ⟨r, hr⟩
        cases r with
        | done c => rfl
        | yield c =>
          dsimp only
          split
          · next next' hs =>
            refine ih (⟨⟨succ? x, ub⟩⟩, c) ?_ next' (by simp [hs]) _ _
            refine Or.inl ⟨x, ?_, hr⟩
            simp [Rxo.Iterator.Monadic.isPlausibleStep_iff, Rxo.Iterator.Monadic.step, hu]
          · next hs =>
            exact (none_case P g ⟨⟨succ? x, ub⟩⟩ c _ hs).symm
    · rw [dif_neg hu]
      simp only [Rxo.Iterator.Monadic.step, if_neg hu]
  rcases it with ⟨⟨_ | next, ub⟩⟩
  · exact (none_case _ f _ init (fun _ => id) rfl).symm
  · exact key _ _ ub _ _ f (fun _ _ _ _ _ => rfl) (_, init) next rfl _ (fun _ => id)

-- `Std.Rxi.Iterator.instLawfulIteratorLoop` (hypothesis 5): removable, the custom loop unfolds step by step to the default forIn' without monad laws.
theorem rxi : drop% Std.Rxi.Iterator.instLawfulIteratorLoop 5 := by
  intros α _ _ n _
  refine ⟨?_⟩
  intro lift hlift γ it init Pl wf f
  have none_case : ∀ (P : α → Prop) (g : (b : α) → P b → (c : γ) → n (Subtype (Pl b c)))
      (it : IterM (α := Rxi.Iterator α) Id α) (acc : γ)
      (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b), it.internalState.next = none →
      IterM.DefaultConsumers.forIn' lift γ Pl it acc P hP g = pure acc := by
    intro P g it acc hP hn
    haveI : Nonempty γ := ⟨acc⟩
    rcases it with ⟨⟨nx⟩⟩
    cases hn
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [Rxi.Iterator.Monadic.step_eq_step]
    dsimp only
    rw [hlift.liftBind_pure, Shrink.inflate_deflate]
    simp only [Rxi.Iterator.Monadic.step]
  have key : ∀ (LE' : α → Prop) (hl : ∀ a b : α, UpwardEnumerable.LE a b → LE' a → LE' b)
      (F : (out : α) → LE' out → (c : γ) → n (Subtype (Pl out c)))
      (P : α → Prop) (g : (b : α) → P b → (c : γ) → n (Subtype (Pl b c)))
      (hFg : ∀ a h1 c (p : P a), F a h1 c = g a p c)
      (q : IterM (α := Rxi.Iterator α) Id α × γ) (x : α)
      (hq : q.1 = (⟨⟨some x⟩⟩ : IterM (α := Rxi.Iterator α) Id α)) (h : LE' x)
      (hP : ∀ b, q.1.IsPlausibleIndirectOutput b → P b),
      Rxi.Iterator.instIteratorLoop.loop γ Pl LE' hl q.2 x h F =
        IterM.DefaultConsumers.forIn' lift γ Pl q.1 q.2 P hP g := by
    intro LE' hl F P g hFg q
    induction q using WellFounded.induction wf with
    | _ q ih => ?_
    intro x hq h hP
    rcases q with ⟨it1, acc⟩
    dsimp only at hq hP ih ⊢
    subst hq
    haveI : Nonempty γ := ⟨acc⟩
    rw [Rxi.Iterator.instIteratorLoop.loop, WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [Rxi.Iterator.Monadic.step_eq_step]
    dsimp only
    rw [hlift.liftBind_pure, Shrink.inflate_deflate]
    simp only [Rxi.Iterator.Monadic.step]
    congr 1
    · apply hFg
    · funext r
      rcases r with ⟨r, hr⟩
      cases r with
      | done c => rfl
      | yield c =>
        dsimp only
        split
        · next next' hs =>
          refine ih (⟨⟨succ? x⟩⟩, c) ?_ next' (by simp [hs]) _ _
          refine Or.inl ⟨x, ?_, hr⟩
          simp [Rxi.Iterator.Monadic.isPlausibleStep_iff, Rxi.Iterator.Monadic.step]
        · next hs =>
          exact (none_case P g ⟨⟨succ? x⟩⟩ c _ hs).symm
  rcases it with ⟨⟨_ | next⟩⟩
  · exact (none_case _ f _ init (fun _ => id) rfl).symm
  · exact key (UpwardEnumerable.LE next ·) _ _ _ f (fun _ _ _ _ => rfl) (_, init) next rfl _ (fun _ => id)

#print axioms rxc
#print axioms rxo
#print axioms rxi

end RangeLoopHand
