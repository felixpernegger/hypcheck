import Lake

/-! SwapCheck certificate: `Lake.NConfigDecl.data_eq_target` without `h : ¬self.kind.isAnonymous`
(idx 3), in the library with `Lake.CustomOut` swapped to `fun _ => ConfigTarget .anonymous` (`T'` holds). With `OpaqueConfigTarget.def`, the
statement for an anonymous-kind declaration says `CustomOut (p, n) = ConfigTarget .anonymous`.
Check with `scripts/swapcheck.sh certs/lake/LakeCertPos.lean`. -/

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


axiom LakeCert.swap : @Lake.CustomOut = fun _ => Lake.ConfigTarget .anonymous

theorem LakeCert.pos.Lake.NConfigDecl.data_eq_target.h3 : pdrop0% Lake.NConfigDecl.data_eq_target 3 := by
  intro p n self
  by_cases hk : self.kind.isAnonymous
  · have hk' : self.kind = .anonymous := Lake.Name.isAnonymous_iff_eq_anonymous.mp hk
    show Lake.CustomOut (p, n) = _
    rw [LakeCert.swap, Lake.OpaqueConfigTarget.def, hk']
  · exact self.data_eq_target hk
