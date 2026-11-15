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

namespace T3c0
open Iris Iris.HeapLang Iris.Std Iris.ProgramLogic Iris.ProgramLogic.Language Iris.ProgramLogic.PrimStep
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage FromMathlib
open Language.Notation EctxLanguage.Notation

/-- `fst ((r0, r1), r2)` is not stuck whenever `Resolve r0 r1 r2` is not: both evaluate r2, r1, r0 in this
order, and a base step of `Resolve` is a base step of r0 with r1, r2 values. -/
theorem nsFst {r0 r1 r2 : Exp} {σ : HeapLang.State}
    (hns : NotStuck (Exp.resolve r0 r1 r2, σ)) :
    NotStuck (Exp.fst (.pair (.pair r0 r1) r2), σ) := by
  rcases hns with hval | ⟨_, _, _, _, hstep⟩
  · simp [ToVal.toVal] at hval
  right
  generalize heq : Exp.resolve r0 r1 r2 = ee at hstep
  rcases hstep with @⟨f1, f2, K, bs⟩
  rcases fill_eq_snoc heq with ⟨rfl, rfl⟩ | ⟨K', Ki, rfl, hf⟩
  · cases bs with
    | resolveS p v _ _ w _ _ _ bs_inner hused =>
      exact ⟨_, _, _, _, .ofBaseStep' [.pairL (.lit (.prophecy p)), .pairL w, .fst]
        (by simp [fill_append, fillItem, ECtxItem.fill]) rfl bs_inner⟩
  · cases Ki with
    | resolveL ctx v1 v2 =>
      simp only [ECtxItem.fill, Exp.resolve.injEq] at hf
      obtain ⟨rfl, rfl, rfl⟩ := hf
      exact ⟨_, _, _, _, .ofBaseStep' (K' ++ [ctx, .pairL v1, .pairL v2, .fst])
        (by simp [fill_append, fillItem, ECtxItem.fill]) rfl bs⟩
    | resolveM e0 v2 =>
      simp only [ECtxItem.fill, Exp.resolve.injEq] at hf
      obtain ⟨rfl, rfl, rfl⟩ := hf
      exact ⟨_, _, _, _, .ofBaseStep' (K' ++ [.pairR r0, .pairL v2, .fst])
        (by simp [fill_append, fillItem, ECtxItem.fill]) rfl bs⟩
    | resolveR e0 e1 =>
      simp only [ECtxItem.fill, Exp.resolve.injEq] at hf
      obtain ⟨rfl, rfl, rfl⟩ := hf
      exact ⟨_, _, _, _, .ofBaseStep' (K' ++ [.pairR (.pair r0 r1), .fst])
        (by simp [fill_append, fillItem, ECtxItem.fill]) rfl bs⟩
    | _ => simp only [ECtxItem.fill] at hf; cases hf

/-- A matched step of `fst ((r0, r1), r2)` gives a matched step of `Resolve r0 r1 r2` (target under one
more `fst`): context steps in r2, r1 or inside r0 carry over, a base step of r0 becomes the `Resolve` base
step (by `resolve_baseStep_inv`), followed by the projections. -/
theorem matchedFst {r0 r1 r2 Z : Exp} {σ1 σ2 : HeapLang.State} {efs : List Exp}
    (hns : NotStuck (Exp.resolve r0 r1 r2, σ1))
    (hm : PrimStepMatchedByErasedSteps (.fst (.pair (.pair r0 r1) r2)) σ1 Z σ2 efs) :
    PrimStepMatchedByErasedSteps (.resolve r0 r1 r2) σ1 (.fst Z) σ2 efs := by
  obtain ⟨Y, σ', κ', efs', _, hstep, hpure, rfl, hσ, hef⟩ := hm
  have hpure' : Exp.fst Z -ᵖ->* Exp.fst (eraseExpr Y) := by
    simpa [fill_append, fillItem, ECtxItem.fill] using
      ReflTransGen_pureStep_fill (fill [ECtxItem.fst]) hpure
  generalize heq : Exp.fst (.pair (.pair r0 r1) r2) = ee at hstep
  rcases hstep with @⟨f1, f2, K, hb⟩
  rcases fill_eq_fst heq with ⟨rfl, rfl⟩ | ⟨K1, rfl, h1⟩
  · cases hb
  rcases fill_eq_pair h1 with ⟨rfl, rfl⟩ | ⟨K2, v2, rfl, rfl, h2⟩ | ⟨K2, rfl, rfl⟩
  · cases hb
  · rcases fill_eq_pair h2 with ⟨rfl, rfl⟩ | ⟨K3, v1, rfl, rfl, rfl⟩ | ⟨K3, rfl, rfl⟩
    · cases hb
      exact absurd hns (Resolve_3_vals_unsafe _ _ _ _)
    · cases K3 using FromMathlib.List.reverseRec with
      | nil =>
        simp only [fill_nil] at hb hpure' ⊢
        obtain ⟨p, w, rfl, hused, rfl⟩ :=
          (priv% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.resolve_baseStep_inv) hns hb
        refine ⟨.ofVal w, σ', _, efs', _, .ofBaseStep [] (.resolveS p w f1 σ1 v2 σ' κ' efs' hb hused),
          hpure'.trans ?_, rfl, hσ, hef⟩
        simpa [fill_append, fillItem, ECtxItem.fill, eraseExpr, eraseResolve] using
          projs_pure_steps (eraseVal w) (eraseVal (.lit (.prophecy p))) (eraseVal v2)
      | append_singleton K4 Ki _ =>
        refine ⟨.resolve (ProgramLogic.fill (K4 ++ [Ki]) f2) (.ofVal v1) (.ofVal v2), σ', κ', efs', _,
          .ofBaseStep' (K4 ++ [.resolveL Ki v1 v2]) (by simp [fill_append, fillItem, ECtxItem.fill])
          (by simp [fill_append, fillItem, ECtxItem.fill]) hb,
          hpure', ?_, hσ, hef⟩
        simp [fill_append, fillItem, ECtxItem.fill, eraseExpr, eraseResolve]
    · refine ⟨.resolve r0 (ProgramLogic.fill K3 f2) (.ofVal v2), σ', κ', efs', _,
        .ofBaseStep' (K3 ++ [.resolveM r0 v2]) (by simp [fill_append, fillItem, ECtxItem.fill])
          (by simp [fill_append, fillItem, ECtxItem.fill]) hb,
        hpure', ?_, hσ, hef⟩
      simp [fill_append, fillItem, ECtxItem.fill, eraseExpr, eraseResolve]
  · refine ⟨.resolve r0 r1 (ProgramLogic.fill K2 f2), σ', κ', efs', _,
      .ofBaseStep' (K2 ++ [.resolveR r0 r1]) (by simp [fill_append, fillItem, ECtxItem.fill])
          (by simp [fill_append, fillItem, ECtxItem.fill]) hb,
      hpure', ?_, hσ, hef⟩
    simp [fill_append, fillItem, ECtxItem.fill, eraseExpr, eraseResolve]

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.resolve_fst_primStepMatched` idx 10: removable
theorem t3c0_0 : drop% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.resolve_fst_primStepMatched 10 := by
  intro r0 r1 r2 Ks e1' e2' σ1 σ2 κ efs hns heq_e IHapp
  have h := IHapp (K' := Ks) (e0 := .fst (.pair (.pair r0 r1) r2)) (Nat.le_refl _)
    (by simpa [eraseExpr] using heq_e) (nsFst hns)
  rw [fill_snoc]
  exact matchedFst hns h

end T3c0
