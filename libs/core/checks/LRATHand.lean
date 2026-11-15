import Std
import Lean

/-!
Hand pass `LRAT` (hand20, 2026-11-08): the last open non-`Data` Std row,
`h2 : s.toCNF.Sat a` of the RAT soundness lemma, is necessary.

Construction: the RAT check returns `true` without any propagation when the candidate clause is a
tautology (`Assignment.ofClause` gives `none`, shown via the library's `ofClause_spec`). On the
unsatisfiable state with the unit clauses `x0` and `¬x0`, adding the tautology `x0 ∨ ¬x0` with
pivot `x0` passes the check, but the result is still unsatisfiable. This avoids evaluating the
hash-map based assignments.

Helpers (namespace `LRATHand`): `tc`, `s0`, `tc_none`, `check_true`, `s0_unsat`.

Run with the lean4 repo's stage1 binary: `runs/hand15/lean.sh checks/LRATHand.lean`.
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

open Std.Sat Std.Tactic.BVDecide.LRAT.Internal

namespace LRATHand

/-- The tautological clause `x0 ∨ ¬x0`. -/
def tc : CNF.Clause Nat := (CNF.Clause.unit 0 true).add 0 false

/-- The unsatisfiable state with the unit clauses `x0` and `¬x0`. -/
def s0 : State := ⟨#[some (CNF.Clause.unit 0 true), some (CNF.Clause.unit 0 false)]⟩

-- helper: `ofClause` rejects the tautology (both polarities of atom 0)
theorem tc_none : Assignment.ofClause tc = none := by
  have h := Assignment.ofClause_spec tc
  cases hc : Assignment.ofClause tc with
  | none => rfl
  | some asg =>
    rw [hc] at h
    have h1 := (h (0, true)).1 (by simp [tc, CNF.Clause.mem_add, CNF.Clause.mem_unit])
    have h2 := (h (0, false)).1 (by simp [tc, CNF.Clause.mem_add, CNF.Clause.mem_unit])
    simp only [Bool.not_true, Bool.not_false] at h1 h2
    rw [h1] at h2
    cases h2

-- helper: the RAT check accepts the tautology with pivot `x0` (it returns before any propagation)
theorem check_true : State.checkRat s0 tc (0, true) #[] #[] = true := by
  unfold State.checkRat
  rw [tc_none]
  simp [tc, CNF.Clause.mem_add, CNF.Clause.mem_unit]

-- helper: `s0` plus the tautology is unsatisfiable
theorem s0_unsat (a : Nat → Bool) : ¬ (s0.add tc).toCNF.Sat a := by
  intro h
  simp [s0, State.toCNF, CNF.sat_def, CNF.eval] at h
  have h0 := h 0 (by simp [State.add])
  have h1 := h 1 (by simp [State.add])
  simp [State.add, CNF.Clause.eval_unit] at h0 h1
  simp_all

-- `Std.Tactic.BVDecide.LRAT.Internal.State.unsat_of_unsat_of_checkRat`: necessary; the RAT check
-- accepts the tautology `x0 ∨ ¬x0` (pivot `x0`) on the unsatisfiable state `[x0], [¬x0]`, so
-- without `h2` the statement would make that state plus the tautology satisfiable.
theorem lrat_7 : ¬ drop0% Std.Tactic.BVDecide.LRAT.Internal.State.unsat_of_unsat_of_checkRat 7 := by
  intro H
  obtain ⟨a', ha⟩ := H (a := fun _ => false) (s := s0) (clause := tc) (pivot := (0, true)) (rupHints := #[]) (ratHints := #[])
    check_true
  exact s0_unsat a' ha

end LRATHand
