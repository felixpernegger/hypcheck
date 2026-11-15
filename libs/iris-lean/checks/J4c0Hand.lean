import Lean.Elab.Command
import Iris
-- hypkit toolkit header: drop%/indep%/drop0%/indep0% state T' and ∀ indep, Hᵢ straight from the library.
-- Agents copy this file unchanged as the start of their output file (scripts/verify.sh checks it).
-- No `xs[i]!` here: libraries may declare a `]!` token (Foundation does), which breaks that syntax.


set_option linter.unusedVariables false

open Lean Meta Elab Term

/-- `_private.M.«0».x` ↦ `_private.M.0.x`: all-digit string components become numeric. -/
def hcFixName : Name → Name
  | .str p s => if !s.isEmpty && s.all Char.isDigit then .num (hcFixName p) s.toNat! else .str (hcFixName p) s
  | .num p k => .num (hcFixName p) k
  | .anonymous => .anonymous

/-- The constant named by `T`: a public name (resolved as usual) or a private one written in full
as `_private.Mod.«0».x` (private names are not reachable by their short name from another module). -/
def hcConst (T : Ident) : TermElabM Name := do
  let n := hcFixName T.getId
  if isPrivateName n then
    unless (← getEnv).contains n do throwError "unknown private constant {n}"
    return n
  realizeGlobalConstNoOverloadWithInfo T

/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    unless or (decide (dep.size > 1)) (body.containsFVar x.fvarId!) do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    unless or (decide (dep.size > 1)) (body.containsFVar x.fvarId!) do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

/-! ## Joint removal of two hypotheses (J1c0)

`drop2% T i j` / `drop2_0% T i j`: `T` with its two non-dependent Prop binders `i < j` dropped
(`_0`: universes set to `0`, for refutations only).
`indep2% T i j` / `indep2_0% T i j`: for two dependent Prop binders (the conclusion or later
binders mention them): `∀ rest, Hᵢ ∧ Hⱼ`, where `rest` are the binders that depend on neither;
"jointly removable" means both are derivable from `rest`. -/

def hcDrop2 (T : Ident) (i j : Nat) (zero : Bool) : TermElabM Lean.Expr := do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← if zero then pure (ci.levelParams.map fun _ => Level.zero)
    else ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    unless i < j && j < xs.size do throwError "need i < j < {xs.size}"
    for k in [i, j] do
      let x := xs[k]!
      unless ← isProp (← inferType x) do throwError "binder {k} of {n} is not a Prop"
      for l in [k+1:xs.size] do
        if (← inferType xs[l]!).containsFVar x.fvarId! then throwError "binder {k} of {n} is dependent"
      if body.containsFVar x.fvarId! then throwError "binder {k} of {n} is dependent"
    mkForallFVars (xs.filter fun y => y != xs[i]! && y != xs[j]!) body

def hcIndep2 (T : Ident) (i j : Nat) (zero : Bool) : TermElabM Lean.Expr := do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← if zero then pure (ci.levelParams.map fun _ => Level.zero)
    else ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    unless i < j && j < xs.size do throwError "need i < j < {xs.size}"
    let xi := xs[i]!; let xj := xs[j]!
    for x in [xi, xj] do
      unless ← isProp (← inferType x) do throwError "binder of {n} is not a Prop"
    let hi ← inferType xi; let hj ← inferType xj
    if hj.containsFVar xi.fvarId! then throwError "Hⱼ mentions binder {i}"
    let mut dep := #[xi, xj]
    for l in [i+1:xs.size] do
      if l == j then continue
      let t ← inferType xs[l]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[l]!
    unless or (dep.size > 2) (or (body.containsFVar xi.fvarId!) (body.containsFVar xj.fvarId!)) do
      throwError "neither binder is dependent: use drop2%"
    mkForallFVars (xs.filter (!dep.contains ·)) (mkAnd hi hj)

elab "drop2% " T:ident i:num j:num : term => hcDrop2 T i.getNat j.getNat false
elab "drop2_0% " T:ident i:num j:num : term => hcDrop2 T i.getNat j.getNat true
elab "indep2% " T:ident i:num j:num : term => hcIndep2 T i.getNat j.getNat false
elab "indep2_0% " T:ident i:num j:num : term => hcIndep2 T i.getNat j.getNat true

/-! ## Helpers (copied from the hand files that proved the single removals) -/


namespace J4c0
open Iris Iris.BI Iris.Std

/-- `fupd_vs_trans` without `[IncOrd M]` and without `vs_impl` (T3c6's proof uses neither). -/
theorem j4_0 : drop2% Iris.fupd_vs_trans 3 12 := by
  intro M _ vs E1 E2 E3 P hpers vs_trans vs_exists vs_persistent_intro_r
  have self : ∀ (E E' : CoPset) (A B : UPred M),
      (emp : UPred M) ⊢ vs E E' iprop(A ∗ vs E E' A B) B := fun E E' A B =>
    (wand_intro emp_sep.1).trans (@vs_persistent_intro_r E E' A B (vs E E' A B) hpers)
  have K : (emp : UPred M) ⊢ vs E2 E3 (fupd_vs vs E2 E3 P) P :=
    (forall_intro fun A => self E2 E3 A P).trans (vs_exists E2 E3 (fun A => iprop(A ∗ vs E2 E3 A P)) P)
  refine exists_elim fun A => ?_
  have h13 : (emp : UPred M) ⊢ vs E1 E3 iprop(A ∗ vs E1 E2 A (fupd_vs vs E2 E3 P)) P :=
    (and_intro (self E1 E2 A _) K).trans (vs_trans _ _ _ _ _ _)
  exact sep_emp.2.trans ((sep_mono_right h13).trans
    (exists_intro (Ψ := fun X => iprop(X ∗ vs E1 E3 X P)) _))

end J4c0
