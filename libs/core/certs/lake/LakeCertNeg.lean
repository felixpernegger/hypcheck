import Lake

/-! SwapCheck certificate: `Lake.NConfigDecl.data_eq_target` without `h : ¬self.kind.isAnonymous`
(idx 3), in the library with `Lake.CustomOut` swapped to `fun _ => (ConfigTarget .anonymous → Bool)` (`T'` fails). With `OpaqueConfigTarget.def`, the
statement for an anonymous-kind declaration says `CustomOut (p, n) = ConfigTarget .anonymous`.
Check with `scripts/swapcheck.sh certs/lake/LakeCertNeg.lean`. -/

open Lean Meta Elab Term in
/-- `T` without its non-dependent Prop binder `i`, all universe parameters set to `0`. -/
elab "pdrop0% " T:ident i:num : term => do
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
/-- `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T`, universe parameters set to `0`. -/
elab "pindep0% " T:ident i:num : term => do
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


axiom LakeCert.swap : @Lake.CustomOut = fun _ => (Lake.ConfigTarget .anonymous → Bool)

/-- Cantor: no type equals its own predicate type. -/
theorem LakeCert.ne_pred (X : Type) : X ≠ (X → Bool) := fun h => by
  let f : X → X → Bool := fun x => cast h x
  have hs : ∀ g : X → Bool, ∃ x, f x = g := fun g => ⟨cast h.symm g, by simp [f]⟩
  obtain ⟨x, hx⟩ := hs fun y => !f y y
  have := congrFun hx x
  cases h' : f x x <;> simp [h'] at this

theorem LakeCert.neg.Lake.NConfigDecl.data_eq_target.h3 : ¬ pdrop0% Lake.NConfigDecl.data_eq_target 3 := by
  intro h
  let d : Lake.NConfigDecl .anonymous .anonymous :=
    { pkg := .anonymous, name := .anonymous, kind := .anonymous, config := Classical.ofNonempty,
      wf_data := fun h => absurd rfl h }
  have := h d
  change Lake.CustomOut (.anonymous, .anonymous) = Lake.OpaqueConfigTarget .anonymous at this
  rw [LakeCert.swap, Lake.OpaqueConfigTarget.def] at this
  exact LakeCert.ne_pred _ this.symm
