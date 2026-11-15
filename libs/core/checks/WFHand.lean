import Lean

/-!
Hand pass `WF` (hand13): 80 hypotheses of `Init.WF` (41), `Init.WFExtrinsicFix` (37),
`Init.System.Promise` (1) and `Init.System.ST` (1): accessibility and well-foundedness lemmas,
lexicographic orders, `FixGraph`, `Nat.fix.go_congr`, and the `extrinsicFix`/`partialExtrinsicFix`
unfolding lemmas with their `Nonempty (C a)`, `WellFounded R` and `Acc R a` hypotheses.

63 necessary, 14 removable, 3 independent (opaque fixpoint; `runs/hand13/WF_independent.jsonl`,
support lemmas at the end of this file).

* Accessibility/well-foundedness rows are refuted with the total relation on `True` (a reflexive
  point is never accessible: `not_acc_of_rel`, `not_wf_total`), the empty relation (`wf_false`) or
  `R1` on `Bool` (`false` accessible, `true` not). Universes are set to `0` where a `Prop` carrier
  suffices, otherwise to `1` (`dropu%`/`indepu%`).
* Removable: in the `FixGraph` uniqueness lemma, `Acc r x` follows from either `FixGraph` premise
  (`acc_of_fixGraph`); the `Nonempty (C a)` instances of the `extrinsicFix` lemmas that also assume
  `WellFounded R` are derivable from it (the well-founded fixpoint of `F` inhabits every `C a`).
* With only `Acc R a`, the `Nonempty` instance is necessary: `R1`, `a := false`, `C b := b = false`
  (empty at the inaccessible `true`).
* The unfolding equations without well-foundedness are refuted by descent: total relation and
  `F a g := g a trivial + 1` into `Nat` turn them into `v = v + 1` for the opaque value `v`.

Reusable models (namespace `WFHand`): `not_acc_of_rel`, `not_wf_total`, `wf_false`, `R1` with
`acc_R1_false`/`not_acc_R1_true`/`not_wf_R1`, `acc_of_fixGraph`, `CB`/`FB` (a family empty at an
inaccessible point and a functional into it), `R1₂`/`R1₃` (the same on `PSigma`s).

Run with `runs/hand13/lean.sh checks/WFHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.defProp false


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
/-- `indep0% T i`: like `indep% T i`, with all universes set to `0` (for refutations) for the dependent Prop binder `i` of `T` (all independent binders). -/
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

open Lean Meta Elab Term in
/-- `drop0% T i`: universes set to `0`; `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
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
/-- `dropu% [l₁, …] T i`: `drop% T i` with `T`'s universe parameters set to the given levels (for refutations). -/
elab "dropu% " "[" ls:num,* "]" T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := (ls.getElems.map fun l => Level.ofNat l.getNat).toList
  unless us.length == ci.levelParams.length do throwError "wrong number of universe levels"
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indepu% [l₁, …] T i`: `indep% T i` with `T`'s universe parameters set to the given levels (for refutations). -/
elab "indepu% " "[" ls:num,* "]" T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := (ls.getElems.map fun l => Level.ofNat l.getNat).toList
  unless us.length == ci.levelParams.length do throwError "wrong number of universe levels"
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



namespace WFHand

open WellFounded Relation

/-! ## Models -/

universe u v

/-- A relation with a reflexive point has no accessible point there. -/
theorem not_acc_of_rel {α : Sort u} {r : α → α → Prop} {x : α} (h : r x x) : ¬ Acc r x := by
  intro hacc
  induction hacc with
  | intro y _ ih => exact ih y h h

/-- The total relation is not well-founded on an inhabited type. -/
theorem not_wf_total {α : Sort u} (a : α) : ¬ WellFounded (fun _ _ : α => True) :=
  fun h => not_acc_of_rel (r := fun _ _ : α => True) trivial (h.apply a)

/-- The empty relation is well-founded. -/
theorem wf_false {α : Sort u} : WellFounded (fun _ _ : α => False) :=
  ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩

/-- `R1` on `Bool`: only `true` is related, to itself. `false` is accessible, `true` is not. -/
def R1 (a b : Bool) : Prop := a = true ∧ b = true

theorem acc_R1_false : Acc R1 false := ⟨false, fun _ h => absurd h.2 (by decide)⟩

theorem not_acc_R1_true : ¬ Acc R1 true := not_acc_of_rel ⟨rfl, rfl⟩

theorem not_wf_R1 : ¬ WellFounded R1 := fun h => not_acc_R1_true (h.apply true)

/-- A point carrying a `FixGraph` value is accessible. -/
theorem acc_of_fixGraph {α : Sort u} {r : α → α → Prop} {C : α → Sort v}
    {F : (x : α) → ((y : α) → r y x → C y) → C x} {x : α} {c : C x}
    (h : FixGraph F x c) : Acc r x := by
  induction h with
  | mk x g _ ih => exact Acc.intro x ih

/-! ## System -/

-- `IO.instNonemptyPromise`: `Promise Empty` would contain a proof of `Nonempty Empty`.
theorem IO.instNonemptyPromise.h1 : ¬ drop0% IO.instNonemptyPromise 1 := fun h => by
  obtain ⟨p⟩ := @h Empty
  cases p
  rename_i hn
  obtain ⟨e⟩ := hn
  exact nomatch e

-- `ST.instNonemptyRef`: `Ref σ Empty` would contain a proof of `Nonempty Empty`.
theorem ST.instNonemptyRef.h2 : ¬ drop0% ST.instNonemptyRef 2 := fun h => by
  obtain ⟨r⟩ := @h Unit Empty
  obtain ⟨e⟩ := r.h
  exact nomatch e

/-! ## Acc, FixGraph, fix -/

-- `Acc.inv`: total relation on `True`, `x` not accessible.
theorem Acc.inv.h4 : ¬ drop0% Acc.inv 4 := fun h =>
  not_acc_of_rel (r := fun _ _ : True => True) trivial (@h True (fun _ _ => True) trivial trivial trivial)

-- `Acc.inv`: `R1`, `false` accessible, `true` not (and `R1 true false` fails).
theorem Acc.inv.h5 : ¬ dropu% [1] Acc.inv 5 := fun h =>
  not_acc_R1_true (@h Bool R1 false true acc_R1_false)

-- `WellFounded.FixGraph.nonempty`: total relation, no `FixGraph` value exists.
theorem FixGraph.nonempty.h5 : ¬ drop0% WellFounded.FixGraph.nonempty 5 := fun h => by
  obtain ⟨⟨c, hc⟩⟩ := @h True (fun _ _ => True) (fun _ => True) (fun x g => g x trivial) trivial
  exact not_acc_of_rel (r := fun _ _ : True => True) trivial (acc_of_fixGraph hc)

-- `WellFounded.FixGraph.unique`: removable, a `FixGraph` value already forces `Acc r x`.
theorem FixGraph.unique.h5 : drop% WellFounded.FixGraph.unique 5 := by
  intro α r C F x c₁ c₂ h₁ h₂
  exact WellFounded.FixGraph.unique F (acc_of_fixGraph h₁) c₁ c₂ h₁ h₂

-- `WellFounded.FixGraph.unique`: empty relation, `F` constant `true`, `c₁ := false`.
theorem FixGraph.unique.h8 : ¬ dropu% [0, 1] WellFounded.FixGraph.unique 8 := fun h => by
  have := @h True (fun _ _ => False) (fun _ => Bool) (fun _ _ => true) trivial (wf_false.apply _)
    false true (FixGraph.mk trivial (fun _ h => h.elim) (fun _ h => h.elim))
  exact Bool.noConfusion this

-- `WellFounded.FixGraph.unique`: empty relation, `F` constant `true`, `c₂ := false`.
theorem FixGraph.unique.h9 : ¬ dropu% [0, 1] WellFounded.FixGraph.unique 9 := fun h => by
  have := @h True (fun _ _ => False) (fun _ => Bool) (fun _ _ => true) trivial (wf_false.apply _)
    true false (FixGraph.mk trivial (fun _ h => h.elim) (fun _ h => h.elim))
  exact Bool.noConfusion this

-- `WellFounded.fixGraph_fixF`: `Acc r x` fails for the total relation.
theorem fixGraph_fixF.h5 : ¬ indep0% WellFounded.fixGraph_fixF 5 := fun h =>
  not_acc_of_rel (r := fun _ _ : True => True) trivial
    (@h True (fun _ _ => True) (fun _ => True) (fun _ _ => trivial) trivial)

-- `WellFounded.fixF_eq`: `Acc r x` fails for the total relation.
theorem fixF_eq.h5 : ¬ indep0% WellFounded.fixF_eq 5 := fun h =>
  not_acc_of_rel (r := fun _ _ : True => True) trivial
    (@h True (fun _ _ => True) (fun _ => True) (fun _ _ => trivial) trivial)

-- `WellFounded.induction`: total relation, `C := False`, the step is `ih x trivial`.
theorem induction.h2 : ¬ drop0% WellFounded.induction 2 := fun h =>
  @h True (fun _ _ => True) (fun _ => False) trivial (fun x ih => ih x trivial)

-- `WellFounded.induction`: empty relation, `C := False`.
theorem induction.h5 : ¬ drop0% WellFounded.induction 5 := fun h =>
  @h True (fun _ _ => False) wf_false (fun _ => False) trivial

-- `WellFounded.val_wrap`: the total relation is not well-founded.
theorem val_wrap.h2 : ¬ indep0% WellFounded.val_wrap 2 := fun h =>
  not_wf_total trivial (@h True (fun _ _ => True) trivial)

-- `WellFounded.fix_eq`: the total relation is not well-founded.
theorem fix_eq.h3 : ¬ indep0% WellFounded.fix_eq 3 := fun h =>
  not_wf_total trivial (@h True (fun _ => True) (fun _ _ => True) (fun _ _ => trivial) trivial)

-- `Acc.rec'_intro`: total relation, `trivial` is not accessible.
theorem rec'_intro.h5 : ¬ indep0% Acc.rec'_intro 5 := fun h =>
  not_acc_of_rel (r := fun _ _ : True => True) trivial
    (@h True (fun _ _ => True) (fun _ _ => True) (fun _ _ _ => trivial) trivial trivial trivial)

-- `Acc.rec'_eq`: total relation, `trivial` is not accessible.
theorem rec'_eq.h5 : ¬ indep0% Acc.rec'_eq 5 := fun h =>
  not_acc_of_rel (r := fun _ _ : True => True) trivial
    (@h True (fun _ _ => True) (fun _ _ => True) (fun _ _ _ => trivial) trivial)

/-! ## Subrelation, InvImage, TransGen -/

-- `Subrelation.accessible`: `r` empty, `q` total.
theorem Subrelation.accessible.h4 : ¬ drop0% Subrelation.accessible 4 := fun h =>
  not_acc_of_rel (r := fun _ _ : True => True) trivial
    (@h True (fun _ _ => False) (fun _ _ => True) trivial (wf_false.apply _))

-- `Subrelation.accessible`: `q = r` total.
theorem Subrelation.accessible.h5 : ¬ drop0% Subrelation.accessible 5 := fun h =>
  not_acc_of_rel (r := fun _ _ : True => True) trivial
    (@h True (fun _ _ => True) (fun _ _ => True) trivial (fun h => h))

-- `Subrelation.wf`: `r` empty, `q` total.
theorem Subrelation.wf.h3 : ¬ drop0% Subrelation.wf 3 := fun h =>
  not_wf_total trivial (@h True (fun _ _ => False) (fun _ _ => True) wf_false)

-- `Subrelation.wf`: `q = r` total.
theorem Subrelation.wf.h4 : ¬ drop0% Subrelation.wf 4 := fun h =>
  not_wf_total trivial (@h True (fun _ _ => True) (fun _ _ => True) (fun h => h))

-- `InvImage.accAux`: total relation.
theorem InvImage.accAux.h5 : ¬ drop0% InvImage.accAux 5 := fun h =>
  not_acc_of_rel (r := InvImage (fun _ _ : True => True) id) trivial
    (@h True True (fun _ _ => True) id trivial trivial rfl)

-- `InvImage.accAux`: `R1`, `b := false` accessible, `f` constant `true`.
theorem InvImage.accAux.h7 : ¬ dropu% [0, 1] InvImage.accAux 7 := fun h =>
  not_acc_of_rel (r := InvImage R1 (fun _ : True => true)) (x := trivial) ⟨rfl, rfl⟩
    (@h True Bool R1 (fun _ => true) false acc_R1_false trivial)

-- `InvImage.accessible`: total relation.
theorem InvImage.accessible.h5 : ¬ drop0% InvImage.accessible 5 := fun h =>
  not_acc_of_rel (r := InvImage (fun _ _ : True => True) id) trivial
    (@h True True (fun _ _ => True) trivial id)

-- `Acc.transGen`: total relation.
theorem Acc.transGen.h3 : ¬ drop0% Acc.transGen 3 := fun h =>
  not_acc_of_rel (TransGen.single (r := fun _ _ : True => True) trivial)
    (@h True (fun _ _ => True) trivial)

-- `Acc.inv_of_transGen`: total relation.
theorem Acc.inv_of_transGen.h4 : ¬ drop0% Acc.inv_of_transGen 4 := fun h =>
  not_acc_of_rel (r := fun _ _ : True => True) trivial
    (@h True (fun _ _ => True) trivial trivial (TransGen.single trivial))

-- `Acc.inv_of_transGen`: `R1`, `false` accessible, `true` not.
theorem Acc.inv_of_transGen.h5 : ¬ dropu% [1] Acc.inv_of_transGen 5 := fun h =>
  not_acc_R1_true (@h Bool R1 false true acc_R1_false)

-- `WellFounded.transGen`: total relation.
theorem WellFounded.transGen.h2 : ¬ drop0% WellFounded.transGen 2 := fun h =>
  not_acc_of_rel (TransGen.single (r := fun _ _ : True => True) trivial)
    ((@h True (fun _ _ => True)).apply trivial)

/-! ## Prod, PSigma -/

-- `Prod.Lex.right'`: `a₁ := 1`, `a₂ := 0`, `rb` total.
theorem Prod.Lex.right'.h6 : ¬ dropu% [0] Prod.Lex.right' 6 := fun h => by
  have := @h Unit (fun _ _ => True) 0 () 1 () trivial
  rcases Prod.lex_def.mp this with h | ⟨h, _⟩
  · exact Nat.not_lt_zero _ h
  · exact Nat.noConfusion h

-- `Prod.Lex.right'`: `a₁ = a₂ = 0`, `rb` empty.
theorem Prod.Lex.right'.h7 : ¬ dropu% [0] Prod.Lex.right' 7 := fun h => by
  have := @h Unit (fun _ _ => False) 0 () 0 () (Nat.le_refl 0)
  rcases Prod.lex_def.mp this with h | ⟨_, h⟩
  · exact Nat.lt_irrefl 0 h
  · exact h

-- `Prod.lexAccessible`: `ra` total, `rb` empty.
theorem Prod.lexAccessible.h5 : ¬ dropu% [0, 0] Prod.lexAccessible 5 := fun h =>
  not_acc_of_rel (Prod.Lex.left (ra := fun _ _ : Unit => True) (rb := fun _ _ : Unit => False) () () trivial)
    (@h Unit Unit (fun _ _ => True) (fun _ _ => False) () (wf_false.apply) ())

-- `Prod.lexAccessible`: `ra` empty, `rb` total.
theorem Prod.lexAccessible.h6 : ¬ dropu% [0, 0] Prod.lexAccessible 6 := fun h =>
  not_acc_of_rel (Prod.Lex.right (ra := fun _ _ : Unit => False) (rb := fun _ _ : Unit => True) () trivial)
    (@h Unit Unit (fun _ _ => False) (fun _ _ => True) () (wf_false.apply _) ())

-- `Prod.RProdSubLex`: both relations empty.
theorem Prod.RProdSubLex.h6 : ¬ dropu% [0, 0] Prod.RProdSubLex 6 := fun h => by
  have := @h Unit Unit (fun _ _ => False) (fun _ _ => False) ((), ()) ((), ())
  cases this with
  | left _ _ h => exact h
  | right _ h => exact h

-- `PSigma.lexAccessible`: `r` total, `s` empty.
theorem PSigma.lexAccessible.h5 : ¬ drop0% PSigma.lexAccessible 5 := fun h =>
  not_acc_of_rel (PSigma.Lex.left (r := fun _ _ : True => True) (s := fun _ (_ _ : True) => False) trivial trivial trivial)
    (@h True (fun _ => True) (fun _ _ => True) (fun _ _ _ => False) trivial (fun _ => wf_false) trivial)

-- `PSigma.lexAccessible`: `r` empty, `s` total.
theorem PSigma.lexAccessible.h6 : ¬ drop0% PSigma.lexAccessible 6 := fun h =>
  not_acc_of_rel (PSigma.Lex.right (r := fun _ _ : True => False) (s := fun _ (_ _ : True) => True) trivial trivial)
    (@h True (fun _ => True) (fun _ _ => False) (fun _ _ _ => True) trivial (wf_false.apply _) trivial)

-- `PSigma.lexNdepWf`: `r` total, `s` empty.
theorem PSigma.lexNdepWf.h4 : ¬ drop0% PSigma.lexNdepWf 4 := fun h =>
  not_acc_of_rel (r := PSigma.lexNdep (fun _ _ : True => True) (fun _ _ : True => False))
    (PSigma.Lex.left trivial trivial trivial)
    ((@h True True (fun _ _ => True) (fun _ _ => False) wf_false).apply ⟨trivial, trivial⟩)

-- `PSigma.lexNdepWf`: `r` empty, `s` total.
theorem PSigma.lexNdepWf.h5 : ¬ drop0% PSigma.lexNdepWf 5 := fun h =>
  not_acc_of_rel (r := PSigma.lexNdep (fun _ _ : True => False) (fun _ _ : True => True))
    (PSigma.Lex.right trivial trivial)
    ((@h True True (fun _ _ => False) (fun _ _ => True) wf_false).apply ⟨trivial, trivial⟩)

-- `PSigma.revLexAccessible`: `s` total, `r` empty.
theorem PSigma.revLexAccessible.h5 : ¬ drop0% PSigma.revLexAccessible 5 := fun h =>
  not_acc_of_rel (PSigma.RevLex.right (r := fun _ _ : True => False) (s := fun _ _ : True => True) trivial trivial trivial)
    (@h True True (fun _ _ => False) (fun _ _ => True) trivial (wf_false.apply) trivial)

-- `PSigma.revLexAccessible`: `r` total, `s` empty.
theorem PSigma.revLexAccessible.h6 : ¬ drop0% PSigma.revLexAccessible 6 := fun h =>
  not_acc_of_rel (PSigma.RevLex.left (r := fun _ _ : True => True) (s := fun _ _ : True => False) trivial trivial)
    (@h True True (fun _ _ => True) (fun _ _ => False) trivial (wf_false.apply _) trivial)

-- `PSigma.revLex`: `r` total, `s` empty.
theorem PSigma.revLex.h4 : ¬ drop0% PSigma.revLex 4 := fun h =>
  not_acc_of_rel (PSigma.RevLex.left (r := fun _ _ : True => True) (s := fun _ _ : True => False) trivial trivial)
    ((@h True True (fun _ _ => True) (fun _ _ => False) wf_false).apply ⟨trivial, trivial⟩)

-- `PSigma.revLex`: `r` empty, `s` total.
theorem PSigma.revLex.h5 : ¬ drop0% PSigma.revLex 5 := fun h =>
  not_acc_of_rel (PSigma.RevLex.right (r := fun _ _ : True => False) (s := fun _ _ : True => True) trivial trivial trivial)
    ((@h True True (fun _ _ => False) (fun _ _ => True) wf_false).apply ⟨trivial, trivial⟩)

-- `PSigma.mkSkipLeft`: `s` empty, so neither `RevLex` constructor applies.
theorem PSigma.mkSkipLeft.h7 : ¬ dropu% [0, 0] PSigma.mkSkipLeft 7 := fun h => by
  have := @h Unit Unit () () (fun _ _ => False) () ()
  cases this with
  | left _ h => exact h
  | right _ _ h => exact h

-- `WellFounded.Nat.fix.go_congr`: `h := 0`, `fuel₁ := 0`, `fuel₂ := 1`.
theorem Nat.fix.go_congr.h7 : ¬ indep0% WellFounded.Nat.fix.go_congr 7 := fun h =>
  Nat.lt_irrefl 0 (@h True (fun _ => True) (fun _ => 0) (fun _ _ => trivial) trivial 0 1 (Nat.zero_lt_one))

-- `WellFounded.Nat.fix.go_congr`: `h := 0`, `fuel₁ := 1`, `fuel₂ := 0`.
theorem Nat.fix.go_congr.h8 : ¬ indep0% WellFounded.Nat.fix.go_congr 8 := fun h =>
  Nat.lt_irrefl 0 (@h True (fun _ => True) (fun _ => 0) (fun _ _ => trivial) trivial 1 0 (Nat.zero_lt_one))

/-! ## extrinsicFix: `Nonempty` instances (derivable from well-foundedness, refuted with only `Acc`) -/

-- `WellFounded.extrinsicFix_eq_fix`: removable (derivable), wf.fix F a inhabits C a.
theorem extrinsicFix_eq_fix.h2 : indep% WellFounded.extrinsicFix_eq_fix 2 := by
  intro α C R F wf a a'
  exact ⟨wf.fix F a'⟩

-- `WellFounded.extrinsicFix_eq_apply`: removable (derivable), h.fix F a inhabits C a.
theorem extrinsicFix_eq_apply.h2 : indep% WellFounded.extrinsicFix_eq_apply 2 := by
  intro α C R F wf a a'
  exact ⟨wf.fix F a'⟩

-- `WellFounded.extrinsicFix_invImage`: removable (derivable), h.fix F a inhabits C a.
theorem extrinsicFix_invImage.h3 : indep% WellFounded.extrinsicFix_invImage 3 := by
  intro α C α' R f F F' hF a wf a'
  exact ⟨wf.fix F a'⟩

-- `WellFounded.extrinsicFix₂_eq_fix`: removable (derivable), from wf.fix.
theorem extrinsicFix₂_eq_fix.h3 : indep% WellFounded.extrinsicFix₂_eq_fix 3 := by
  intro α β C₂ R F wf a b a' b'
  exact ⟨wf.fix (C := fun x => C₂ x.1 x.2) (fun x G => F x.1 x.2 (fun a b h => G ⟨a, b⟩ h)) ⟨a', b'⟩⟩

-- `WellFounded.extrinsicFix₂_eq_apply`: removable (derivable), from wf.fix.
theorem extrinsicFix₂_eq_apply.h3 : indep% WellFounded.extrinsicFix₂_eq_apply 3 := by
  intro α β C₂ R F wf a b a' b'
  exact ⟨wf.fix (C := fun x => C₂ x.1 x.2) (fun x G => F x.1 x.2 (fun a b h => G ⟨a, b⟩ h)) ⟨a', b'⟩⟩

-- `WellFounded.extrinsicFix₃_eq_fix`: removable (derivable), from wf.fix.
theorem extrinsicFix₃_eq_fix.h4 : indep% WellFounded.extrinsicFix₃_eq_fix 4 := by
  intro α β γ C₃ R F wf a b c a' b' c'
  exact ⟨wf.fix (C := fun x => C₃ x.1 x.2.1 x.2.2)
    (fun x G => F x.1 x.2.1 x.2.2 (fun a b c h => G ⟨a, b, c⟩ h)) ⟨a', b', c'⟩⟩

-- `WellFounded.extrinsicFix₃_eq_apply`: removable (derivable), from wf.fix.
theorem extrinsicFix₃_eq_apply.h4 : indep% WellFounded.extrinsicFix₃_eq_apply 4 := by
  intro α β γ C₃ R F wf a b c a' b' c'
  exact ⟨wf.fix (C := fun x => C₃ x.1 x.2.1 x.2.2)
    (fun x G => F x.1 x.2.1 x.2.2 (fun a b c h => G ⟨a, b, c⟩ h)) ⟨a', b', c'⟩⟩

-- `WellFounded.partialExtrinsicFix_eq_apply`: removable (derivable), from wf.fix.
theorem partialExtrinsicFix_eq_apply.h2 : indep% WellFounded.partialExtrinsicFix_eq_apply 2 := by
  intro α C R F a wf a'
  exact ⟨wf.fix F a'⟩

-- `WellFounded.partialExtrinsicFix_eq_fix`: removable (derivable), from wf.fix.
theorem partialExtrinsicFix_eq_fix.h2 : indep% WellFounded.partialExtrinsicFix_eq_fix 2 := by
  intro α C R F wf a a'
  exact ⟨wf.fix F a'⟩

-- `WellFounded.partialExtrinsicFix₂_eq_apply`: removable (derivable), from wf.fix.
theorem partialExtrinsicFix₂_eq_apply.h3 : indep% WellFounded.partialExtrinsicFix₂_eq_apply 3 := by
  intro α β C₂ R F a b wf a' b'
  exact ⟨wf.fix (C := fun x => C₂ x.1 x.2) (fun x G => F x.1 x.2 (fun a b h => G ⟨a, b⟩ h)) ⟨a', b'⟩⟩

-- `WellFounded.partialExtrinsicFix₂_eq_fix`: removable (derivable), from wf.fix.
theorem partialExtrinsicFix₂_eq_fix.h3 : indep% WellFounded.partialExtrinsicFix₂_eq_fix 3 := by
  intro α β C₂ R F wf a b a' b'
  exact ⟨wf.fix (C := fun x => C₂ x.1 x.2) (fun x G => F x.1 x.2 (fun a b h => G ⟨a, b⟩ h)) ⟨a', b'⟩⟩

-- `WellFounded.partialExtrinsicFix₃_eq_apply`: removable (derivable), from wf.fix.
theorem partialExtrinsicFix₃_eq_apply.h4 : indep% WellFounded.partialExtrinsicFix₃_eq_apply 4 := by
  intro α β γ C₃ R F a b c wf a' b' c'
  exact ⟨wf.fix (C := fun x => C₃ x.1 x.2.1 x.2.2)
    (fun x G => F x.1 x.2.1 x.2.2 (fun a b c h => G ⟨a, b, c⟩ h)) ⟨a', b', c'⟩⟩

-- `WellFounded.partialExtrinsicFix₃_eq_fix`: removable (derivable), from wf.fix.
theorem partialExtrinsicFix₃_eq_fix.h4 : indep% WellFounded.partialExtrinsicFix₃_eq_fix 4 := by
  intro α β γ C₃ R F wf a b c a' b' c'
  exact ⟨wf.fix (C := fun x => C₃ x.1 x.2.1 x.2.2)
    (fun x G => F x.1 x.2.1 x.2.2 (fun a b c h => G ⟨a, b, c⟩ h)) ⟨a', b', c'⟩⟩

/-- Family on `Bool` that is empty at `true`. -/
abbrev CB (b : Bool) : Prop := b = false

/-- Functional for `R1` into `CB`: at `true` it calls itself (`R1 true true`). -/
theorem FB : (x : Bool) → ((y : Bool) → R1 y x → CB y) → CB x
  | false, _ => rfl
  | true, g => g true ⟨rfl, rfl⟩

-- `WellFounded.partialExtrinsicFix_eq_apply_of_acc`: `R1`, `a := false` accessible, `C true` empty.
theorem partialExtrinsicFix_eq_apply_of_acc.h2 :
    ¬ indepu% [0, 1] WellFounded.partialExtrinsicFix_eq_apply_of_acc 2 := fun h => by
  obtain ⟨e⟩ := @h Bool CB R1 FB false acc_R1_false true
  exact Bool.noConfusion e

/-- `R1` on the first component of `(a : Bool) ×' Unit`. -/
def R1₂ (p q : (_ : Bool) ×' Unit) : Prop := R1 p.1 q.1

theorem acc_R1₂ : Acc R1₂ ⟨false, ()⟩ := ⟨_, fun _ h => absurd h.2 (by decide)⟩

-- `WellFounded.partialExtrinsicFix₂_eq_partialExtrinsicFix`: as for the 1-ary version, on `Bool ×' Unit`.
theorem partialExtrinsicFix₂_eq_partialExtrinsicFix.h3 :
    ¬ indepu% [0, 1, 1] WellFounded.partialExtrinsicFix₂_eq_partialExtrinsicFix 3 := fun h => by
  obtain ⟨e⟩ := @h Bool (fun _ => Unit) (fun a _ => CB a) R1₂ (fun a _ g => FB a (fun y hy => g y () hy))
    false () acc_R1₂ true ()
  exact Bool.noConfusion e

-- `WellFounded.partialExtrinsicFix₂_eq_apply_of_acc`: as for the 1-ary version, on `Bool ×' Unit`.
theorem partialExtrinsicFix₂_eq_apply_of_acc.h3 :
    ¬ indepu% [0, 1, 1] WellFounded.partialExtrinsicFix₂_eq_apply_of_acc 3 := fun h => by
  obtain ⟨e⟩ := @h Bool (fun _ => Unit) (fun a _ => CB a) R1₂ (fun a _ g => FB a (fun y hy => g y () hy))
    false () acc_R1₂ true ()
  exact Bool.noConfusion e

/-- `R1` on the first component of `(a : Bool) ×' (_ : Unit) ×' Unit`. -/
def R1₃ (p q : (_ : Bool) ×' (_ : Unit) ×' Unit) : Prop := R1 p.1 q.1

theorem acc_R1₃ : Acc R1₃ ⟨false, (), ()⟩ := ⟨_, fun _ h => absurd h.2 (by decide)⟩

-- `WellFounded.partialExtrinsicFix₃_eq_partialExtrinsicFix`: as for the 1-ary version.
theorem partialExtrinsicFix₃_eq_partialExtrinsicFix.h4 :
    ¬ indepu% [0, 1, 1, 1] WellFounded.partialExtrinsicFix₃_eq_partialExtrinsicFix 4 := fun h => by
  obtain ⟨e⟩ := @h Bool (fun _ => Unit) (fun _ _ => Unit) (fun a _ _ => CB a) R1₃
    (fun a _ _ g => FB a (fun y hy => g y () () hy)) false () () acc_R1₃ true () ()
  exact Bool.noConfusion e

-- `WellFounded.partialExtrinsicFix₃_eq_apply_of_acc`: as for the 1-ary version.
theorem partialExtrinsicFix₃_eq_apply_of_acc.h4 :
    ¬ indepu% [0, 1, 1, 1] WellFounded.partialExtrinsicFix₃_eq_apply_of_acc 4 := fun h => by
  obtain ⟨e⟩ := @h Bool (fun _ => Unit) (fun _ _ => Unit) (fun a _ _ => CB a) R1₃
    (fun a _ _ g => FB a (fun y hy => g y () () hy)) false () () acc_R1₃ true () ()
  exact Bool.noConfusion e

/-! ## extrinsicFix: well-foundedness in `_eq_fix` (dependent: wf.fix uses it) -/

-- `WellFounded.extrinsicFix_eq_fix`: the total relation is not well-founded.
theorem extrinsicFix_eq_fix.h5 : ¬ indep0% WellFounded.extrinsicFix_eq_fix 5 := fun h =>
  not_wf_total trivial (@h True (fun _ => True) (fun _ => ⟨trivial⟩) (fun _ _ => True) (fun _ _ => trivial) trivial)

-- `WellFounded.extrinsicFix₂_eq_fix`: the total relation is not well-founded.
theorem extrinsicFix₂_eq_fix.h6 : ¬ indep0% WellFounded.extrinsicFix₂_eq_fix 6 := fun h =>
  not_wf_total ⟨trivial, trivial⟩ (@h True (fun _ => True) (fun _ _ => True) (fun _ _ => ⟨trivial⟩)
    (fun _ _ => True) (fun _ _ _ => trivial) trivial trivial)

-- `WellFounded.extrinsicFix₃_eq_fix`: the total relation is not well-founded.
theorem extrinsicFix₃_eq_fix.h7 : ¬ indep0% WellFounded.extrinsicFix₃_eq_fix 7 := fun h =>
  not_wf_total ⟨trivial, trivial, trivial⟩ (@h True (fun _ => True) (fun _ _ => True) (fun _ _ _ => True)
    (fun _ _ _ => ⟨trivial⟩) (fun _ _ => True) (fun _ _ _ _ => trivial) trivial trivial trivial)

-- `WellFounded.partialExtrinsicFix_eq_fix`: the total relation is not well-founded.
theorem partialExtrinsicFix_eq_fix.h5 : ¬ indep0% WellFounded.partialExtrinsicFix_eq_fix 5 := fun h =>
  not_wf_total trivial (@h True (fun _ => True) (fun _ => ⟨trivial⟩) (fun _ _ => True) (fun _ _ => trivial) trivial)

-- `WellFounded.partialExtrinsicFix₂_eq_fix`: the total relation is not well-founded.
theorem partialExtrinsicFix₂_eq_fix.h6 : ¬ indep0% WellFounded.partialExtrinsicFix₂_eq_fix 6 := fun h =>
  not_wf_total ⟨trivial, trivial⟩ (@h True (fun _ => True) (fun _ _ => True) (fun _ _ => ⟨trivial⟩)
    (fun _ _ => True) (fun _ _ _ => trivial) trivial trivial)

-- `WellFounded.partialExtrinsicFix₃_eq_fix`: the total relation is not well-founded.
theorem partialExtrinsicFix₃_eq_fix.h7 : ¬ indep0% WellFounded.partialExtrinsicFix₃_eq_fix 7 := fun h =>
  not_wf_total ⟨trivial, trivial, trivial⟩ (@h True (fun _ => True) (fun _ _ => True) (fun _ _ _ => True)
    (fun _ _ _ => ⟨trivial⟩) (fun _ _ => True) (fun _ _ _ _ => trivial) trivial trivial trivial)

/-! ## extrinsicFix: unfolding equations without well-foundedness (descent)

With the total relation and `F a g := g a trivial + 1` into `Nat`, the unfolding equation reads
`v = v + 1` for the (opaque) value `v`, whatever it is. -/

-- `WellFounded.extrinsicFix_eq_apply`: descent, `v = v + 1`.
theorem extrinsicFix_eq_apply.h5 : ¬ dropu% [1, 0] WellFounded.extrinsicFix_eq_apply 5 := fun h =>
  Nat.succ_ne_self _ (@h True (fun _ => Nat) (fun _ => ⟨0⟩) (fun _ _ => True)
    (fun a g => g a trivial + 1) trivial).symm

-- `WellFounded.extrinsicFix₂_eq_apply`: descent, `v = v + 1`.
theorem extrinsicFix₂_eq_apply.h6 : ¬ dropu% [1, 0, 0] WellFounded.extrinsicFix₂_eq_apply 6 := fun h =>
  Nat.succ_ne_self _ (@h True (fun _ => True) (fun _ _ => Nat) (fun _ _ => ⟨0⟩) (fun _ _ => True)
    (fun a b g => g a b trivial + 1) trivial trivial).symm

-- `WellFounded.extrinsicFix₃_eq_apply`: descent, `v = v + 1`.
theorem extrinsicFix₃_eq_apply.h7 : ¬ dropu% [1, 0, 0, 0] WellFounded.extrinsicFix₃_eq_apply 7 := fun h =>
  Nat.succ_ne_self _ (@h True (fun _ => True) (fun _ _ => True) (fun _ _ _ => Nat) (fun _ _ _ => ⟨0⟩)
    (fun _ _ => True) (fun a b c g => g a b c trivial + 1) trivial trivial trivial).symm

-- `WellFounded.partialExtrinsicFix_eq_apply_of_acc`: descent, `v = v + 1`.
theorem partialExtrinsicFix_eq_apply_of_acc.h6 :
    ¬ dropu% [1, 0] WellFounded.partialExtrinsicFix_eq_apply_of_acc 6 := fun h =>
  Nat.succ_ne_self _ (@h True (fun _ => Nat) (fun _ => ⟨0⟩) (fun _ _ => True)
    (fun a g => g a trivial + 1) trivial).symm

-- `WellFounded.partialExtrinsicFix_eq_apply`: descent, `v = v + 1`.
theorem partialExtrinsicFix_eq_apply.h6 : ¬ dropu% [1, 0] WellFounded.partialExtrinsicFix_eq_apply 6 := fun h =>
  Nat.succ_ne_self _ (@h True (fun _ => Nat) (fun _ => ⟨0⟩) (fun _ _ => True)
    (fun a g => g a trivial + 1) trivial).symm

-- `WellFounded.partialExtrinsicFix₂_eq_apply_of_acc`: descent, `v = v + 1`.
theorem partialExtrinsicFix₂_eq_apply_of_acc.h8 :
    ¬ dropu% [1, 0, 0] WellFounded.partialExtrinsicFix₂_eq_apply_of_acc 8 := fun h =>
  Nat.succ_ne_self _ (@h True (fun _ => True) (fun _ _ => Nat) (fun _ _ => ⟨0⟩) (fun _ _ => True)
    (fun a b g => g a b trivial + 1) trivial trivial).symm

-- `WellFounded.partialExtrinsicFix₂_eq_apply`: descent, `v = v + 1`.
theorem partialExtrinsicFix₂_eq_apply.h8 : ¬ dropu% [1, 0, 0] WellFounded.partialExtrinsicFix₂_eq_apply 8 := fun h =>
  Nat.succ_ne_self _ (@h True (fun _ => True) (fun _ _ => Nat) (fun _ _ => ⟨0⟩) (fun _ _ => True)
    (fun a b g => g a b trivial + 1) trivial trivial).symm

-- `WellFounded.partialExtrinsicFix₃_eq_apply_of_acc`: descent, `v = v + 1`.
theorem partialExtrinsicFix₃_eq_apply_of_acc.h10 :
    ¬ dropu% [1, 0, 0, 0] WellFounded.partialExtrinsicFix₃_eq_apply_of_acc 10 := fun h =>
  Nat.succ_ne_self _ (@h True (fun _ => True) (fun _ _ => True) (fun _ _ _ => Nat) (fun _ _ _ => ⟨0⟩)
    (fun _ _ => True) (fun a b c g => g a b c trivial + 1) trivial trivial trivial).symm

-- `WellFounded.partialExtrinsicFix₃_eq_apply`: descent, `v = v + 1`.
theorem partialExtrinsicFix₃_eq_apply.h10 :
    ¬ dropu% [1, 0, 0, 0] WellFounded.partialExtrinsicFix₃_eq_apply 10 := fun h =>
  Nat.succ_ne_self _ (@h True (fun _ => True) (fun _ _ => True) (fun _ _ _ => Nat) (fun _ _ _ => ⟨0⟩)
    (fun _ _ => True) (fun a b c g => g a b c trivial + 1) trivial trivial trivial).symm

/-! ## extrinsicFix_invImage -/

-- `WellFounded.extrinsicFix_invImage`: without the compatibility of `F` and `F'`, take the empty
-- relation (well-founded), `F` constant `0` and `F'` constant `1`.
theorem extrinsicFix_invImage.h8 : ¬ dropu% [0, 1, 0] WellFounded.extrinsicFix_invImage 8 := fun h => by
  have := @h True (fun _ => Nat) True (fun _ => ⟨0⟩) (fun _ _ => False) id (fun _ _ => 0) (fun _ _ => 1)
    trivial wf_false
  rw [extrinsicFix_eq_apply (InvImage.wf _ wf_false), extrinsicFix_eq_apply wf_false] at this
  exact Nat.noConfusion this

/-! ## Independent rows: support

For the three rows below `T'` turns on the value of `extrinsicFix` at a relation that is not
well-founded, where it is the opaque `opaqueFix` (a `partial def`, so nothing is known about its
values). Each lemma shows that `T'` at a concrete instance is exactly an equation involving such
opaque values, so `¬T'` follows from any interpretation of `opaqueFix` in which it fails. -/

/-- Inverse image of `R1` along the constant `false`: empty, hence well-founded. -/
theorem wf_invImage_R1 : WellFounded (InvImage R1 (fun _ : True => false)) :=
  ⟨fun a => ⟨a, fun _ h => Bool.noConfusion h.1⟩⟩

-- support for WellFounded.extrinsicFix_invImage, idx 10
theorem extrinsicFix_invImage.h10_support
    (hne : extrinsicFix (C := fun _ : Bool => Nat) R1 (fun _ _ => 0) false ≠ 0) :
    ¬ dropu% [0, 1, 1] WellFounded.extrinsicFix_invImage 10 := fun h => by
  have := @h Bool (fun _ => Nat) True (fun _ => ⟨0⟩) R1 (fun _ => false) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => rfl) trivial
  rw [extrinsicFix_eq_apply wf_invImage_R1] at this
  exact hne this.symm

/-- Total relation on `(_ : True) ×' True`. -/
abbrev Rt₂ : (_ : True) ×' True → (_ : True) ×' True → Prop := fun _ _ => True

/-- Self-calling functional into `Nat` for `Rt₂`. -/
abbrev Ft₂ : (a : True) → (b : True) → ((a' : True) → (b' : True) → Rt₂ ⟨a', b'⟩ ⟨a, b⟩ → Nat) → Nat :=
  fun a b g => g a b trivial + 1

-- support for WellFounded.partialExtrinsicFix₂_eq_partialExtrinsicFix, idx 8
theorem partialExtrinsicFix₂_eq_partialExtrinsicFix.h8_support
    (hne : partialExtrinsicFix₂ (C₂ := fun _ _ => Nat) Rt₂ Ft₂ trivial trivial ≠
      partialExtrinsicFix (C := fun _ => Nat) Rt₂ (fun p r => Ft₂ p.1 p.2 fun a' b' hR => r ⟨a', b'⟩ hR)
        ⟨trivial, trivial⟩) :
    ¬ dropu% [1, 0, 0] WellFounded.partialExtrinsicFix₂_eq_partialExtrinsicFix 8 := fun h =>
  hne (@h True (fun _ => True) (fun _ _ => Nat) (fun _ _ => ⟨0⟩) Rt₂ Ft₂ trivial trivial)

/-- Total relation on `(_ : True) ×' (_ : True) ×' True`. -/
abbrev Rt₃ : (_ : True) ×' (_ : True) ×' True → (_ : True) ×' (_ : True) ×' True → Prop := fun _ _ => True

/-- Self-calling functional into `Nat` for `Rt₃`. -/
abbrev Ft₃ : (a : True) → (b : True) → (c : True) →
    ((a' : True) → (b' : True) → (c' : True) → Rt₃ ⟨a', b', c'⟩ ⟨a, b, c⟩ → Nat) → Nat :=
  fun a b c g => g a b c trivial + 1

-- support for WellFounded.partialExtrinsicFix₃_eq_partialExtrinsicFix, idx 10
theorem partialExtrinsicFix₃_eq_partialExtrinsicFix.h10_support
    (hne : partialExtrinsicFix₃ (C₃ := fun _ _ _ => Nat) Rt₃ Ft₃ trivial trivial trivial ≠
      partialExtrinsicFix (C := fun _ => Nat) Rt₃
        (fun p r => Ft₃ p.1 p.2.1 p.2.2 fun a' b' c' hR => r ⟨a', b', c'⟩ hR) ⟨trivial, trivial, trivial⟩) :
    ¬ dropu% [1, 0, 0, 0] WellFounded.partialExtrinsicFix₃_eq_partialExtrinsicFix 10 := fun h =>
  hne (@h True (fun _ => True) (fun _ _ => True) (fun _ _ _ => Nat) (fun _ _ _ => ⟨0⟩) Rt₃ Ft₃
    trivial trivial trivial)

/-- The relations handed to `extrinsicFix` by the two sides of the support instance above are total
on inhabited types, so both sides are values of `opaqueFix`. -/
theorem partialExtrinsicFix₂_sides_not_wf :
    ¬ WellFounded (fun (p q : (a' : True) ×' { b' : True // (PSigma.mk a' b' : (_ : True) ×' True) = ⟨trivial, trivial⟩ ∨
        TransGen Rt₂ ⟨a', b'⟩ ⟨trivial, trivial⟩ }) => Rt₂ ⟨p.1, p.2.1⟩ ⟨q.1, q.2.1⟩) ∧
    ¬ WellFounded (fun (p q : { x : (_ : True) ×' True // x = ⟨trivial, trivial⟩ ∨ TransGen Rt₂ x ⟨trivial, trivial⟩ }) =>
        Rt₂ p.1 q.1) :=
  ⟨not_wf_total ⟨trivial, ⟨trivial, Or.inl rfl⟩⟩, not_wf_total ⟨⟨trivial, trivial⟩, Or.inl rfl⟩⟩

/-- Same for `R1`: not well-founded, so `extrinsicFix R1 F false` is a value of `opaqueFix`. -/
theorem extrinsicFix_invImage_R1_not_wf : ¬ WellFounded R1 := not_wf_R1

end WFHand
