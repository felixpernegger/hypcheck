import Lean.Elab.Command
import Cslib
-- CSLib toolkit header (copy of hypcheck runs/hand22/Header.lean with `import Cslib`; ~150 MB, 1.5 s to import)


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
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
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

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
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

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

namespace W1c4
open Cslib Relation LambdaCalculus.LocallyNameless.Untyped Term

universe u

theorem rtgStuck {α : Type} {r : α → α → Prop} {a b : α} (hs : ∀ t, ¬ r a t)
    (h : ReflTransGen r a b) : b = a := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => subst ih; exact (hs _ hbc).elim

theorem xiFvar {R : Term ℕ → Term ℕ → Prop} (hR : ∀ y t, ¬ R (fvar y) t) {y : ℕ} {t : Term ℕ} :
    ¬ Xi R (fvar y) t := by
  intro h; cases h with
  | base h => exact hR _ _ h

theorem betaFvar {y : ℕ} {t : Term ℕ} : ¬ Beta (fvar y) t := by intro h; cases h

theorem fbFvarApp {a b : ℕ} {t : Term ℕ} : ¬ FullBeta (app (fvar a) (fvar b)) t := by
  intro h; cases h with
  | base h => cases h
  | appL _ h => exact xiFvar (fun _ _ => betaFvar) h
  | appR _ h => exact xiFvar (fun _ _ => betaFvar) h

theorem betaAtFvar {i y : ℕ} {t : Term ℕ} : ¬ BetaAt i (fvar y) t := by intro h; cases h

theorem betaAtFvarApp {i a b : ℕ} {t : Term ℕ} : ¬ BetaAt i (app (fvar a) (fvar b)) t := by
  intro h; cases h with
  | appL h => exact betaAtFvar h
  | appR h => exact betaAtFvar h

theorem lcId : LC (abs (bvar 0) : Term ℕ) := .abs ∅ _ (fun x _ => LC.fvar x)
theorem lcK : LC (abs (fvar 1) : Term ℕ) := .abs ∅ _ (fun _ _ => LC.fvar 1)

-- the redex (λ.0) x0 and its step
def B : Term ℕ := app (abs (bvar 0)) (fvar 0)
theorem lcB : LC B := .app lcId (.fvar 0)
theorem fbB : FullBeta B (fvar 0) := .base (.beta lcId (.fvar 0))
theorem baB : BetaAt 0 B (fvar 0) := .outer lcId (.fvar 0)

-- no full-beta step from a term that is not locally closed
theorem fbNotLC {M t : Term ℕ} (h : ¬ LC M) : ¬ FullBeta M t := fun s => h (FullBeta.step_lc_l s)

theorem fbAbsFvar {a : ℕ} {t : Term ℕ} : ¬ FullBeta (abs (fvar a)) t := by
  intro h; cases h with
  | base h => cases h
  | abs xs h =>
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset xs
    exact xiFvar (fun _ _ => betaFvar) (h y hy)

theorem baAbsFvar {i a : ℕ} {t : Term ℕ} : ¬ BetaAt i (abs (fvar a)) t := by
  intro h; cases h with
  | abs xs h =>
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset xs
    exact betaAtFvar (h y hy)

theorem baBinv {i : ℕ} {t : Term ℕ} (h : BetaAt i B t) : i = 0 := by
  unfold B at h
  cases h with
  | outer => rfl
  | appL h =>
    cases h with
    | abs xs h =>
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset xs
      exact (betaAtFvar (h y hy)).elim
  | appR h => exact (betaAtFvar h).elim

theorem lcApp {a b : Term ℕ} (h : LC (app a b)) : LC a ∧ LC b := by cases h; exact ⟨by assumption, by assumption⟩
theorem notLCbvar {n : ℕ} : ¬ LC (bvar n : Term ℕ) := nofun
theorem notLCappR {a : Term ℕ} {n : ℕ} : ¬ LC (app a (bvar n)) := fun h => notLCbvar (lcApp h).2
theorem notLCappL {a : Term ℕ} {n : ℕ} : ¬ LC (app (bvar n) a) := fun h => notLCbvar (lcApp h).1

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appNoAbsL` idx 5: necessary (x x)
theorem ba1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appNoAbsL 5 := fun h =>
  betaAtFvarApp (@h ℕ (fvar 0) (fvar 0) (fvar 0) 0 (fun h => by cases h))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appNoAbsL` idx 6: necessary (M = λ.B steps at position 0, M N at position 1)
theorem ba2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appNoAbsL 6 := fun h => by
  have := @h ℕ (abs B) (abs (fvar 0)) (fvar 0) 0 (.abs ∅ (fun x _ => baB))
  generalize hj : (0:ℕ) = j at this
  cases this with
  | appL h' => simp [IsAbs.abs] at hj

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appAbsL` idx 5: necessary ((λ.x0) x0 has no step to itself)
theorem ba3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appAbsL 5 := fun h => by
  have := @h ℕ (abs (fvar 0)) (abs (fvar 0)) (fvar 0) 0 (.abs _)
  generalize hj : (0:ℕ) + 1 = j at this
  cases this with
  | appL h' => exact baAbsFvar h'
  | appR h' => exact betaAtFvar h'

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appAbsL` idx 6: necessary (M = B is no abstraction)
theorem ba4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appAbsL 6 := fun h => by
  have := @h ℕ B (fvar 0) (fvar 0) 0 baB
  unfold B at this
  generalize hj : (0:ℕ) + 1 = j at this
  cases this with
  | appL h' => have hn : ¬ IsAbs (app (abs (bvar 0)) (fvar 0) : Term ℕ) := nofun; simp only [hn, ↓reduceIte] at hj; subst hj; exact absurd (baBinv h') (by decide)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appNoAbsR` idx 6: necessary (N = λ.x0, M = B)
theorem ba5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appNoAbsR 6 := fun h => by
  have := @h ℕ B (fvar 0) (abs (fvar 0)) 0 baB
  unfold B at this
  generalize hj : (0:ℕ) + countRedexes (abs (fvar 0) : Term ℕ) = j at this
  cases this with
  | appR h' => simp [countRedexes, IsAbs.abs] at hj

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appAbsR` idx 5: necessary ((λ.x0) x0 has no step to itself)
theorem ba6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appAbsR 5 := fun h => by
  have := @h ℕ (fvar 0) (fvar 0) (abs (fvar 0)) 0 (.abs _)
  generalize hj : (0:ℕ) + countRedexes (abs (fvar 0) : Term ℕ) + 1 = j at this
  cases this with
  | appL h' => exact baAbsFvar h'
  | appR h' => exact betaAtFvar h'

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appAbsR` idx 6: necessary (N = x1, M = B)
theorem ba7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appAbsR 6 := fun h => by
  have := @h ℕ B (fvar 0) (fvar 1) 0 baB
  unfold B at this
  generalize hj : (0:ℕ) + countRedexes (fvar 1 : Term ℕ) + 1 = j at this
  cases this with
  | appR h' => have hn : ¬ IsAbs (fvar 1 : Term ℕ) := nofun; simp only [hn, ↓reduceIte] at hj; simp [countRedexes] at hj; subst hj; exact absurd (baBinv h') (by decide)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.isAbs_r` idx 5: necessary (B steps to x0)
theorem ba8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.isAbs_r 5 := fun h =>
  nomatch @h ℕ B (fvar 0) 0 baB

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.of_cbn_step` idx 3: necessary (x0 to x0)
theorem ba9 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.of_cbn_step 3 := fun h =>
  betaAtFvar (@h ℕ (fvar 0) (fvar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.to_step` idx 6: necessary (B 0 steps by BetaAt but is not LC)
theorem ba10 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.to_step 6 := fun h =>
  notLCappR (FullBeta.step_lc_l (@h ℕ (app B (bvar 0)) (app (fvar 0) (bvar 0)) 0 _ (BetaAt.appNoAbsL baB nofun)))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.rename` idx 6: necessary (x0 to x0)
theorem ba11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.rename 6 := fun h =>
  betaAtFvar (@h ℕ (fvar 0) (fvar 0) 0 _ _ 0 0)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.lc_r` idx 7: necessary (B 0 steps to x0 0)
theorem ba12 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.lc_r 7 := fun h =>
  notLCappR (@h ℕ (app B (bvar 0)) (app (fvar 0) (bvar 0)) 0 _ _ (BetaAt.appNoAbsL baB nofun))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.abs_close` idx 7: necessary (λ.x1 has no step)
theorem ba13 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.abs_close 7 := fun h =>
  baAbsFvar (@h ℕ (fvar 1) (fvar 1) 0 _ _ 0 (.fvar 1))

end W1c4

namespace W1c4
open Cslib Relation LambdaCalculus.LocallyNameless.Untyped Term

theorem cbnLC {M t : Term ℕ} (h : ¬ LC M) : ¬ CBN M t := fun s => h s.lc_l
theorem cbnFvar {a : ℕ} {t : Term ℕ} : ¬ CBN (fvar a) t := fun s => by cases s with | base h => cases h
theorem cbnFvarApp {a b : ℕ} {t : Term ℕ} : ¬ CBN (app (fvar a) (fvar b)) t := fun s => by
  cases s with
  | base h => cases h
  | app _ h => exact cbnFvar h
theorem cbnB : CBN B (fvar 0) := .base (.beta lcId (.fvar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.step_to_redex` idx 3: necessary (x0 to x1)
theorem cb1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.step_to_redex 3 := fun h => by
  have := rtgStuck (fun _ => xiFvar (fun _ _ => betaFvar)) (@h ℕ (fvar 0) (fvar 1))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.to_redex` idx 3: necessary (x0 to x1)
theorem cb2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.to_redex 3 := fun h => by
  have := rtgStuck (fun _ => xiFvar (fun _ _ => betaFvar)) (@h ℕ (fvar 0) (fvar 1))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.steps_app_l_cong` idx 4: necessary (x0 x0 to x1 x0)
theorem cb3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.steps_app_l_cong 4 := fun h => by
  have := rtgStuck (fun _ => cbnFvarApp) (@h ℕ (fvar 0) (fvar 1) (fvar 0) (.fvar 0))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.steps_app_l_cong` idx 5: necessary (B to x0, N = bvar 0)
theorem cb4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.steps_app_l_cong 5 := fun h => by
  have := rtgStuck (fun _ => cbnLC notLCappR) (@h ℕ B (fvar 0) (bvar 0) (.single cbnB))
  simp [B] at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.steps_subst` idx 7: necessary (x0 to x1)
theorem cb5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.steps_subst 7 := fun h => by
  have := @h ℕ (fvar 0) (fvar 1) (fvar 0) _ _ 5 (.fvar 0)
  have := rtgStuck (fun _ => cbnFvar) (by simpa [subst_fvar] using this)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.steps_subst` idx 8: necessary (substituting bvar 0 into B)
theorem cb6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.steps_subst 8 := fun h => by
  have := @h ℕ B (fvar 0) (bvar 0) _ _ 0 (.single cbnB)
  change ReflTransGen CBN (app (abs (bvar 0)) (bvar 0)) (bvar 0) at this
  have := rtgStuck (fun _ => cbnLC notLCappR) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Xi.step_lc_r` idx 4: necessary (R total, bvar 0)
theorem xi1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Xi.step_lc_r 4 := fun h =>
  notLCbvar (@h ℕ (fun _ _ => True) (bvar 0) (bvar 0) (.base trivial))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Xi.step_lc_l` idx 4: necessary (R total, bvar 0)
theorem xi2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Xi.step_lc_l 4 := fun h =>
  notLCbvar (@h ℕ (fun _ _ => True) (bvar 0) (bvar 0) (.base trivial))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_app_l_cong` idx 5: necessary (B to x0, N = bvar 0)
theorem fb1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_app_l_cong 5 := fun h => by
  have := rtgStuck (fun _ => fbNotLC notLCappR) (@h ℕ B (fvar 0) (bvar 0) (.single fbB))
  simp [B] at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_app_r_cong` idx 4: necessary (x0 x0 to x0 x1)
theorem fb2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_app_r_cong 4 := fun h => by
  have := rtgStuck (fun _ => fbFvarApp) (@h ℕ (fvar 0) (fvar 1) (fvar 0) (.fvar 0))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_app_r_cong` idx 5: necessary (B to x0, N = bvar 0)
theorem fb3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_app_r_cong 5 := fun h => by
  have := rtgStuck (fun _ => fbNotLC notLCappL) (@h ℕ B (fvar 0) (bvar 0) (.single fbB))
  simp [B] at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_subst_cong_lc` idx 8: necessary (substituting bvar 0 into B)
theorem fb4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_subst_cong_lc 8 := fun h => by
  have := @h ℕ _ _ B (fvar 0) (bvar 0) 0 fbB
  change FullBeta (app (abs (bvar 0)) (bvar 0)) (bvar 0) at this
  exact notLCappR (FullBeta.step_lc_l this)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_abs_close` idx 6: necessary (λ.x1 to λ.x2)
theorem fb5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_abs_close 6 := fun h => by
  have := @h ℕ (fvar 1) (fvar 2) _ _ 0
  change ReflTransGen FullBeta (abs (fvar 1)) (abs (fvar 2)) at this
  have := rtgStuck (fun _ => fbAbsFvar) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_abs_cong` idx 6: necessary (λ.x0 has no step)
theorem fb6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_abs_cong 6 := fun h =>
  fbAbsFvar (@h ℕ (fvar 0) (fvar 0) _ _ ∅)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_abs_cong` idx 6: necessary (λ.x0 to λ.x1)
theorem fb7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_abs_cong 6 := fun h => by
  have := rtgStuck (fun _ => fbAbsFvar) (@h ℕ (fvar 0) (fvar 1) _ _ ∅)
  simp at this

-- body (λ.0) 0, which opens to a redex
def S0 : Term ℕ := app (abs (bvar 0)) (bvar 0)
theorem stepS0 (x : ℕ) : FullBeta (S0 ^ fvar x) (bvar 0 ^ fvar x) := .base (.beta lcId (.fvar x))
theorem absS0 : FullBeta (abs S0) (abs (bvar 0)) := .abs ∅ (fun x _ => stepS0 x)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_open_cong_l` idx 8: necessary (s = (λ.0) 0, t = bvar 5)
theorem fb8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_open_cong_l 8 := fun h => by
  have := @h ℕ _ _ S0 (bvar 0) (bvar 5) ∅ (fun x _ => stepS0 x)
  change FullBeta (app (abs (bvar 0)) (bvar 5)) (bvar 5) at this
  exact notLCappR (FullBeta.step_lc_l this)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_open_cong_l_abs` idx 6: necessary (x0 to x1)
theorem fb9 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_open_cong_l_abs 6 := fun h => by
  have := @h ℕ _ _ (fvar 0) (fvar 1) (fvar 0) (.fvar 0)
  change ReflTransGen FullBeta (fvar 0) (fvar 1) at this
  have := rtgStuck (fun _ => xiFvar (fun _ _ => betaFvar)) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_open_cong_l_abs` idx 7: necessary (s = (λ.0) 0, t = bvar 5)
theorem fb10 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_open_cong_l_abs 7 := fun h => by
  have := @h ℕ _ _ S0 (bvar 0) (bvar 5) (.single absS0)
  change ReflTransGen FullBeta (app (abs (bvar 0)) (bvar 5)) (bvar 5) at this
  have := rtgStuck (fun _ => fbNotLC notLCappR) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_subst_cong_r` idx 7: necessary (x0[0 := x1] to x0[0 := x2])
theorem fb11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_subst_cong_r 7 := fun h => by
  have := @h ℕ _ _ 0 (fvar 0) (fvar 1) (fvar 2) (.fvar 0)
  have := rtgStuck (fun _ => xiFvar (fun _ _ => betaFvar)) (by simpa [subst_fvar] using this)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_subst_cong_r` idx 8: necessary (s = bvar 0 x0, B to x1)
theorem fb12 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_subst_cong_r 8 := fun h => by
  have := @h ℕ _ _ 0 (app (bvar 0) (fvar 0)) (app (abs (bvar 0)) (fvar 1)) (fvar 1) (.base (.beta lcId (.fvar 1)))
  change ReflTransGen FullBeta (app (bvar 0) (app (abs (bvar 0)) (fvar 1))) (app (bvar 0) (fvar 1)) at this
  have := rtgStuck (fun _ => fbNotLC notLCappL) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_subst_cong_r` idx 7: necessary (x0[0 := x1] to x0[0 := x2])
theorem fb13 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_subst_cong_r 7 := fun h => by
  have := @h ℕ _ _ 0 (fvar 0) (fvar 1) (fvar 2) (.fvar 0)
  have := rtgStuck (fun _ => xiFvar (fun _ _ => betaFvar)) (by simpa [subst_fvar] using this)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_subst_cong_r` idx 8: necessary (s = bvar 0 x0, B to x1)
theorem fb14 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_subst_cong_r 8 := fun h => by
  have := @h ℕ _ _ 0 (app (bvar 0) (fvar 0)) (app (abs (bvar 0)) (fvar 1)) (fvar 1) (.single (.base (.beta lcId (.fvar 1))))
  change ReflTransGen FullBeta (app (bvar 0) (app (abs (bvar 0)) (fvar 1))) (app (bvar 0) (fvar 1)) at this
  have := rtgStuck (fun _ => fbNotLC notLCappL) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_open_cong_abs` idx 8: necessary (s = bvar 0, s' = x1, t = x0)
theorem fb15 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_open_cong_abs 8 := fun h => by
  have := @h ℕ _ _ (bvar 0) (fvar 1) (fvar 0) (fvar 0) .refl (.fvar 0) lcId
  change ReflTransGen FullBeta (fvar 0) (fvar 1) at this
  have := rtgStuck (fun _ => xiFvar (fun _ _ => betaFvar)) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_open_cong_abs` idx 9: necessary (s = (λ.0) 0, t = bvar 5)
theorem fb16 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_open_cong_abs 9 := fun h => by
  have := @h ℕ _ _ S0 (bvar 0) (bvar 5) (bvar 5) .refl (.single absS0)
    (.abs ∅ _ (fun x _ => FullBeta.step_lc_l (stepS0 x)))
  change ReflTransGen FullBeta (app (abs (bvar 0)) (bvar 5)) (bvar 5) at this
  have := rtgStuck (fun _ => fbNotLC notLCappR) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_open_cong_abs` idx 10: necessary (s = bvar 1 0, t = B, t' = x0)
theorem fb17 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_open_cong_abs 10 := fun h => by
  have := @h ℕ _ _ (app (bvar 1) (bvar 0)) (app (bvar 1) (bvar 0)) B (fvar 0) (.single fbB) .refl lcB
  change ReflTransGen FullBeta (app (bvar 1) B) (app (bvar 1) (fvar 0)) at this
  have := rtgStuck (fun _ => fbNotLC notLCappL) this
  simp [B] at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_open_out` idx 9: necessary (M = N = bvar 0, x0 to x1)
theorem pa1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_open_out 9 := fun h => by
  have := @h ℕ (bvar 0) (fvar 0) (bvar 0) (fvar 1) _ _ ∅ (fun x _ => .fvar x)
  change Parallel (fvar 0) (fvar 1) at this
  cases this

theorem fbeNotLC {M t : Term ℕ} (h : ¬ LC M) : ¬ FullBetaEta M t := fun s => by
  rcases s with s | s
  · exact h (FullBeta.step_lc_l s)
  · exact h (FullEta.step_lc_l s)

theorem fbeFvarApp {a b : ℕ} {t : Term ℕ} : ¬ FullBetaEta (app (fvar a) (fvar b)) t := fun s => by
  rcases s with s | s
  · exact fbFvarApp s
  · cases s with
    | base h => cases h
    | appL _ h => cases h with | base h => cases h
    | appR _ h => cases h with | base h => cases h

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBetaEta.redex_app_l_cong` idx 4: necessary (x0 x0 to x1 x0)
theorem fbe1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBetaEta.redex_app_l_cong 4 := fun h => by
  have := rtgStuck (fun _ => fbeFvarApp) (@h ℕ (fvar 0) (fvar 1) (fvar 0) (.fvar 0))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBetaEta.redex_app_l_cong` idx 5: necessary (B to x0, N = bvar 0)
theorem fbe2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBetaEta.redex_app_l_cong 5 := fun h => by
  have := rtgStuck (fun _ => fbeNotLC notLCappR) (@h ℕ B (fvar 0) (bvar 0) (.single (Or.inl fbB)))
  simp [B] at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBetaEta.redex_app_r_cong` idx 4: necessary (x0 x0 to x0 x1)
theorem fbe3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBetaEta.redex_app_r_cong 4 := fun h => by
  have := rtgStuck (fun _ => fbeFvarApp) (@h ℕ (fvar 0) (fvar 1) (fvar 0) (.fvar 0))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBetaEta.redex_app_r_cong` idx 5: necessary (B to x0, N = bvar 0)
theorem fbe4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBetaEta.redex_app_r_cong 5 := fun h => by
  have := rtgStuck (fun _ => fbeNotLC notLCappL) (@h ℕ B (fvar 0) (bvar 0) (.single (Or.inl fbB)))
  simp [B] at this

end W1c4

namespace W1c4
open Cslib Relation LambdaCalculus.LocallyNameless.Untyped Term

universe u

-- closing x at level k then opening with z = opening with z then renaming x to z (no LC needed)
theorem openClose {Var : Type u} [DecidableEq Var] (x z : Var) :
    ∀ (M : Term Var) (k : ℕ), Term.openRec k (fvar z) (Term.closeRec k x M) =
      Term.subst (Term.openRec k (fvar z) M) x (fvar z)
  | .bvar i, k => by
    simp only [Term.closeRec, Term.openRec]; split <;> simp [Term.subst]
  | .fvar y, k => by
    by_cases hxy : x = y
    · subst hxy; simp [Term.closeRec, Term.openRec, Term.subst]
    · simp [Term.closeRec, Term.openRec, Term.subst, hxy]
  | .app a b, k => by simp [Term.closeRec, Term.openRec, Term.subst, openClose x z a k, openClose x z b k]
  | .abs t, k => by simp [Term.closeRec, Term.openRec, Term.subst, openClose x z t (k+1)]

-- openings with free variables at distinct levels commute
theorem openComm {Var : Type u} (a b : Var) :
    ∀ (M : Term Var) (j k : ℕ), j ≠ k → Term.openRec j (fvar a) (Term.openRec k (fvar b) M) =
      Term.openRec k (fvar b) (Term.openRec j (fvar a) M)
  | .bvar i, j, k, h => by
    simp only [Term.openRec]; split_ifs <;> simp_all [Term.openRec]
  | .fvar y, j, k, h => by simp [Term.openRec]
  | .app c d, j, k, h => by simp [Term.openRec, openComm a b c j k h, openComm a b d j k h]
  | .abs t, j, k, h => by simp [Term.openRec, openComm a b t (j+1) (k+1) (by omega)]

theorem isAbsOpen {Var : Type u} {z : Var} {k : ℕ} {M : Term Var} :
    IsAbs (Term.openRec k (fvar z) M) ↔ IsAbs M := by
  cases M with
  | bvar j => simp only [Term.openRec]; split <;> exact ⟨nofun, nofun⟩
  | fvar => exact ⟨nofun, nofun⟩
  | app => exact ⟨nofun, nofun⟩
  | abs => exact ⟨fun _ => .abs _, fun _ => .abs _⟩

-- BetaAt is stable under opening with a free variable at any level (no LC needed)
theorem baOpen {Var : Type u} [HasFresh Var] [DecidableEq Var] {z : Var} {i : ℕ} {M M' : Term Var}
    (h : BetaAt i M M') : ∀ k, BetaAt i (Term.openRec k (fvar z) M) (Term.openRec k (fvar z) M') := by
  induction h with
  | @outer M N lcM lcN =>
    intro k
    rw [open_lc k (fvar z) _ (.app lcM lcN), open_lc k (fvar z) _ (beta_lc lcM lcN)]
    exact .outer lcM lcN
  | @appL i M M' N _ ih =>
    intro k
    have := (ih k).appL (N := Term.openRec k (fvar z) N)
    simp only [isAbsOpen] at this
    simpa [Term.openRec] using this
  | @appR i M M' N _ ih =>
    intro k
    have := (ih k).appR (N := Term.openRec k (fvar z) N)
    simp only [isAbsOpen, countRedexes_openRec_fvar] at this
    simpa [Term.openRec] using this
  | @abs i M M' xs _ ih =>
    intro k
    simp only [Term.openRec]
    refine .abs xs (fun y hy => ?_)
    have := ih y hy (k+1)
    simp only [Term.open'] at this ⊢
    rwa [openComm y z M 0 (k+1) (by omega), openComm y z M' 0 (k+1) (by omega)]

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.abs_close` idx 8: removable (closing then opening is opening then renaming; both preserve BetaAt without LC)
theorem ba14 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.abs_close 8 := by
  intro Var M M' i _ _ x h
  refine BetaAt.abs ∅ (fun z _ => ?_)
  simp only [Term.open']
  rw [openClose x z M 0, openClose x z M' 0]
  exact (baOpen h 0).rename x z

end W1c4

namespace W1c4
open Cslib Relation LambdaCalculus.LocallyNameless.Untyped Term LambdaCalculus.LocallyNameless.Stlc

abbrev bT : Ty Unit := Ty.base ()

theorem ok1 (a : ℕ) (τ : Ty Unit) : HasWellFormed.wf ([⟨a, τ⟩] : LambdaCalculus.LocallyNameless.Context ℕ (Ty Unit)) :=
  List.nodupKeys_singleton _
theorem var1 (a : ℕ) (τ : Ty Unit) : Typing [⟨a, τ⟩] (fvar a : Term ℕ) τ :=
  .var (ok1 a τ) (List.mem_singleton_self _)
theorem notOk2 (a : ℕ) (σ τ : Ty Unit) : ¬ HasWellFormed.wf ([⟨a, σ⟩, ⟨a, τ⟩] : LambdaCalculus.LocallyNameless.Context ℕ (Ty Unit)) := by
  intro h
  have : List.NodupKeys ([⟨a, σ⟩, ⟨a, τ⟩] : LambdaCalculus.LocallyNameless.Context ℕ (Ty Unit)) := h
  simp [List.nodupKeys_cons] at this

-- ω = λ.0 0 and Ω = ω ω
def om : Term ℕ := abs (app (bvar 0) (bvar 0))
def Om : Term ℕ := app om om
theorem lcOm : LC om := .abs ∅ _ (fun x _ => .app (.fvar x) (.fvar x))
theorem lcOmega : LC Om := .app lcOm lcOm
theorem stepOm : FullBeta Om Om := .base (.beta lcOm lcOm)
theorem notSNloop {t : Term ℕ} (h : FullBeta t t) : ¬ SN FullBeta t := by
  intro hs
  induction hs with
  | intro x _ ih => exact ih x h h
theorem notSNOm : ¬ SN FullBeta Om := notSNloop stepOm
theorem snOm : SN FullBeta om := Acc.intro _ (fun y hy => by
  cases hy with
  | base h => cases h
  | abs xs h =>
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset xs
    exact (fbFvarApp (h z hz)).elim)
theorem snFvar (a : ℕ) : SN FullBeta (fvar a : Term ℕ) :=
  Acc.intro _ (fun y hy => (xiFvar (fun _ _ => betaFvar) hy).elim)
theorem snBvar (n : ℕ) : SN FullBeta (bvar n : Term ℕ) :=
  Acc.intro _ (fun y hy => (fbNotLC notLCbvar hy).elim)
theorem lcK0 : LC (abs (fvar 0) : Term ℕ) := .abs ∅ _ (fun _ _ => LC.fvar 0)

abbrev semB : Set (Term ℕ) := semanticMap (Var := ℕ) bT
theorem satB : Saturated semB := semanticMap_saturated bT

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.perm` idx 6: necessary (bvar 0 is untypable)
theorem st1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.perm 6 := fun h =>
  notLCbvar (Typing.lc (@h ℕ Unit [] [] (bvar 0) bT List.Perm.nil))

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.perm` idx 7: necessary (x0 typed in [x0] but not in [])
theorem st2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.perm 7 := fun h => by
  have := @h ℕ Unit [⟨0, bT⟩] [] (fvar 0) bT (var1 0 bT)
  cases this with | var _ hm => simp at hm

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.weaken_aux` idx 8: necessary (bvar 0 is untypable)
theorem st3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.weaken_aux 8 := fun h =>
  notLCbvar (Typing.lc (@h ℕ Unit _ [] [] [] (bvar 0) bT List.nodupKeys_nil))

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.weaken_aux` idx 9: necessary (duplicate key x0)
theorem st4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.weaken_aux 9 := fun h => by
  have := @h ℕ Unit _ [] [⟨0, bT⟩] [⟨0, bT⟩] (fvar 0) bT (var1 0 bT)
  cases this with | var hok _ => exact notOk2 0 bT bT hok

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.weaken` idx 7: necessary (bvar 0 is untypable)
theorem st5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.weaken 7 := fun h =>
  notLCbvar (Typing.lc (@h ℕ Unit _ [] [] (bvar 0) bT List.nodupKeys_nil))

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.weaken` idx 8: necessary (duplicate key x0)
theorem st6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.weaken 8 := fun h => by
  have := @h ℕ Unit _ [⟨0, bT⟩] [⟨0, bT⟩] (fvar 0) bT (var1 0 bT)
  cases this with | var hok _ => exact notOk2 0 bT bT hok

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.lc` idx 5: necessary (bvar 0)
theorem st7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.lc 5 := fun h =>
  notLCbvar (@h ℕ Unit [] (bvar 0) bT)

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.subst_aux` idx 11: necessary (t = bvar 0)
theorem st8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.subst_aux 11 := fun h =>
  notLCbvar (Typing.lc (h (Var := ℕ) (Base := Unit) (Γ := [⟨1, bT⟩]) (Δ := []) (x := 0) (σ := bT)
    (t := bvar 0) (τ := bT) (s := fvar 1) (var1 1 bT)))

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.subst_aux` idx 12: necessary (t = x0, s = bvar 0)
theorem st9 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.subst_aux 12 := fun h => by
  have := Typing.lc (h (Var := ℕ) (Base := Unit) (Γ := []) (Δ := []) (x := 0) (σ := bT)
    (t := fvar 0) (τ := bT) (s := bvar 0) (var1 0 bT))
  simp [subst_fvar] at this
  exact notLCbvar this

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.typing_subst_head` idx 10: necessary (t = bvar 0)
theorem st10 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.typing_subst_head 10 := fun h =>
  notLCbvar (Typing.lc (h (Var := ℕ) (Base := Unit) (Γ := [⟨1, bT⟩]) (x := 0) (σ := bT)
    (t := bvar 0) (τ := bT) (s := fvar 1) (var1 1 bT)))

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.typing_subst_head` idx 11: necessary (t = x0, s = bvar 0)
theorem st11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.typing_subst_head 11 := fun h => by
  have := Typing.lc (h (Var := ℕ) (Base := Unit) (Γ := []) (x := 0) (σ := bT)
    (t := fvar 0) (τ := bT) (s := bvar 0) (var1 0 bT))
  simp [subst_fvar] at this
  exact notLCbvar this

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.preservation_open` idx 10: necessary (m = bvar 1)
theorem st12 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.preservation_open 10 := fun h =>
  notLCbvar (Typing.lc (h (Var := ℕ) (Base := Unit) (Γ := [⟨1, bT⟩]) (xs := ∅) (σ := bT)
    (m := bvar 1) (τ := bT) (n := fvar 1) (var1 1 bT)))

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.preservation_open` idx 11: necessary (m = bvar 0, n = bvar 5)
theorem st13 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.preservation_open 11 := fun h =>
  notLCbvar (Typing.lc (h (Var := ℕ) (Base := Unit) (Γ := []) (xs := ∅) (σ := bT)
    (m := bvar 0) (τ := bT) (n := bvar 5) (fun x _ => var1 x bT)))

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.FullBeta.progress` idx 4: necessary (bvar 0 is neither value nor reducible)
theorem st14 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.FullBeta.progress 4 := fun h => by
  rcases h (Var := ℕ) (Base := Unit) (t := bvar 0) (τ := bT) with h | ⟨t', h⟩
  · cases h
  · exact fbNotLC notLCbvar h

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.lc` idx 2: necessary (S = {bvar 0})
theorem sa1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.lc 2 := fun h =>
  notLCbvar (@h ℕ {bvar 0} (bvar 0) rfl)

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.lc` idx 4: necessary (bvar 0 outside semanticMap)
theorem sa2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.lc 4 := fun h =>
  notLCbvar (@h ℕ semB satB (bvar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.sn` idx 2: necessary (S = {Ω})
theorem sa3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.sn 2 := fun h =>
  notSNOm (@h ℕ {Om} Om rfl)

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.sn` idx 4: necessary (Ω)
theorem sa4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.sn 4 := fun h =>
  notSNOm (@h ℕ semB satB Om)

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.neutal_lc` idx 2: necessary (S = ∅)
theorem sa5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.neutal_lc 2 := fun h =>
  @h ℕ ∅ (fvar 0) (.fvar 0) (.fvar 0)

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.neutal_lc` idx 4: necessary (Ω is LC, not SN)
theorem sa6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.neutal_lc 4 := fun h =>
  notSNOm (@h ℕ semB satB Om lcOmega).1

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.neutal_lc` idx 5: necessary (bvar 0 is neutral, not LC)
theorem sa7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.neutal_lc 5 := fun h =>
  notLCbvar (@h ℕ semB satB (bvar 0) (.bvar 0)).2

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.multiApp` idx 2: necessary (S = {x0})
theorem sa8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.multiApp 2 := fun h => by
  have := @h ℕ {fvar 0} (bvar 0) (fvar 0) [] (.fvar 0) (snFvar 0) rfl
  cases this

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.multiApp` idx 6: necessary (N = bvar 0)
theorem sa9 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.multiApp 6 := fun h =>
  notLCappR (@h ℕ semB satB (fvar 0) (bvar 0) [] (snBvar 0) ⟨snFvar 0, .fvar 0⟩).2

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.multiApp` idx 7: necessary (N = Ω)
theorem sa10 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.multiApp 7 := fun h =>
  notSNloop (.appL lcK0 stepOm) (@h ℕ semB satB (fvar 0) Om [] lcOmega ⟨snFvar 0, .fvar 0⟩).1

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.multiApp` idx 8: necessary (M = bvar 5)
theorem sa11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.Saturated.multiApp 8 := fun h => by
  have := (lcApp (@h ℕ semB satB (bvar 5) (fvar 0) [] (.fvar 0) (snFvar 0)).2).1
  cases this with
  | abs xs _ h =>
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset xs
    exact notLCbvar (h z hz)

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.entailsContext_cons` idx 8: necessary (x0 rebound to ω, ω ω not SN)
theorem ec1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.entailsContext_cons 8 := fun h => by
  have := @h ℕ Unit _ [] [⟨0, bT ⤳ bT⟩] 0 bT om ⟨snOm, lcOm⟩ entailsContext_empty
  have := @this 0 (bT ⤳ bT) (by simp)
  simp [multiSubst, subst_fvar] at this
  exact notSNOm (this om snOm lcOm).1

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.entailsContext_cons` idx 9: necessary (sub = bvar 0)
theorem ec2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.entailsContext_cons 9 := fun h => by
  have := @h ℕ Unit _ [] [] 0 bT (bvar 0) (by simp [Env.fv]) (fun h => nomatch h)
  have := @this 0 bT (by simp)
  simp [multiSubst, subst_fvar] at this
  exact notLCbvar this.2

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.entailsContext_cons` idx 10: necessary (E = [x1 ↦ bvar 0])
theorem ec3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.entailsContext_cons 10 := fun h => by
  have := @h ℕ Unit _ [⟨1, bvar 0⟩] [⟨1, bT⟩] 0 bT (fvar 0) (by simp [Env.fv, LambdaCalculus.LocallyNameless.Context.dom, fv])
    ⟨snFvar 0, .fvar 0⟩
  have := @this 1 bT (by simp)
  simp [multiSubst, subst_fvar] at this
  exact notLCbvar this.2

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.soundness` idx 7: necessary (bvar 0)
theorem so1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.soundness 7 := fun h =>
  notLCbvar (h (Var := ℕ) (Base := Unit) (Γ := []) (t := bvar 0) (τ := bT) [] (fun h => nomatch h)
    (fun h => nomatch h)).2

-- `Cslib.LambdaCalculus.LocallyNameless.Stlc.strong_norm` idx 7: necessary (Ω)
theorem so2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Stlc.strong_norm 7 := fun h =>
  notSNOm (h (Var := ℕ) (Base := Unit) (Γ := []) (t := Om) (τ := bT))

end W1c4

namespace W1c4
open Cslib LambdaCalculus.LocallyNameless.Fsub

universe u

-- Fsub: well-formedness of a type only depends on which keys look up to a sub binding
theorem wfMono {Var : Type u} [DecidableEq Var] {Γ : Env Var} {σ : Ty Var} (wf : σ.Wf Γ) :
    ∀ {Γ' : Env Var}, (∀ Y τ, Binding.sub τ ∈ Γ.dlookup Y → ∃ τ', Binding.sub τ' ∈ Γ'.dlookup Y) →
      σ.Wf Γ' := by
  induction wf with
  | top => intros; exact .top
  | var h => intro Γ' hm; obtain ⟨τ', h'⟩ := hm _ _ h; exact .var h'
  | arrow _ _ ih1 ih2 => intro Γ' hm; exact .arrow (ih1 hm) (ih2 hm)
  | sum _ _ ih1 ih2 => intro Γ' hm; exact .sum (ih1 hm) (ih2 hm)
  | @all Γ σ τ L _ _ ih1 ih2 =>
    intro Γ' hm
    refine .all L (ih1 hm) (fun X hX => ih2 X hX (fun Y ρ h => ?_))
    by_cases hY : Y = X
    · subst hY; exact ⟨σ, by simp⟩
    · rw [List.dlookup_cons_ne _ _ hY] at h ⊢; exact hm Y ρ h

theorem dlNarrow {Var : Type u} [DecidableEq Var] {X Y : Var} {τ τ' ρ : Ty Var} {Δ : Env Var} :
    ∀ (Γ : Env Var), Binding.sub ρ ∈ (Γ ++ ⟨X, .sub τ⟩ :: Δ).dlookup Y →
      ∃ ρ', Binding.sub ρ' ∈ (Γ ++ ⟨X, .sub τ'⟩ :: Δ).dlookup Y
  | [], h => by
    by_cases hY : Y = X
    · subst hY; exact ⟨τ', by simp⟩
    · refine ⟨ρ, ?_⟩; rw [List.nil_append, List.dlookup_cons_ne _ _ hY] at h ⊢; exact h
  | ⟨Z, b⟩ :: Γ, h => by
    by_cases hY : Y = Z
    · subst hY; exact ⟨ρ, by simpa using h⟩
    · rw [List.cons_append, List.dlookup_cons_ne _ _ hY] at h ⊢; exact dlNarrow Γ h

theorem wfDedup {Var : Type u} [DecidableEq Var] {Γ : Env Var} {σ : Ty Var} :
    σ.Wf Γ ↔ σ.Wf Γ.dedupKeys :=
  ⟨fun h => wfMono h (fun Y τ h => ⟨τ, by rwa [List.dlookup_dedupKeys]⟩),
   fun h => wfMono h (fun Y τ h => ⟨τ, by rwa [List.dlookup_dedupKeys] at h⟩)⟩

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.narrow` idx 9: removable (lookup of sub bindings is preserved without NodupKeys)
theorem fw1 : drop% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.narrow 9 := by
  intro Var _ Γ Δ σ τ τ' X wf
  exact wfMono wf (fun Y ρ h => dlNarrow Γ h)

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.narrow_cons` idx 8: removable (as for narrow, with Γ = [])
theorem fw2 : drop% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.narrow_cons 8 := by
  intro Var _ Δ σ τ τ' X wf
  exact wfMono wf (fun Y ρ h => dlNarrow (τ := τ) [] h)

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.open_lc` idx 7: removable (pass to dedupKeys, which has the same lookups)
theorem fw3 : drop% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.open_lc 7 := by
  intro Var _ Γ σ τ δ _ wfa wfd
  exact wfDedup.mpr (Ty.Wf.open_lc (List.nodupKeys_dedupKeys Γ) (wfDedup.mp wfa) (wfDedup.mp wfd))

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env` idx 7: removable (NodupKeys transfers along the permutation)
theorem fw4 : drop% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env 7 := by
  intro Var _ Γ Δ σ wf perm okΔ
  exact Ty.Wf.perm_env wf perm ((List.perm_nodupKeys perm).mpr okΔ) okΔ

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env` idx 8: removable (NodupKeys transfers along the permutation)
theorem fw5 : drop% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env 8 := by
  intro Var _ Γ Δ σ wf perm okΓ
  exact Ty.Wf.perm_env wf perm okΓ ((List.perm_nodupKeys perm).mp okΓ)

end W1c4

namespace W1c4
open Cslib LambdaCalculus.LocallyNameless.Fsub

theorem fNoLook {Γ : Env ℕ} {X : ℕ} (h : ∀ σ, Binding.sub σ ∉ Γ.dlookup X) : ¬ Ty.Wf Γ (.fvar X) := by
  intro w; cases w with | var hm => exact h _ hm

theorem fNotWf0 {X : ℕ} : ¬ Ty.Wf ([] : Env ℕ) (.fvar X) := fNoLook (by simp)

theorem fwSub (a : ℕ) : Env.Wf ([⟨a, .sub .top⟩] : Env ℕ) := .sub .empty .top (by simp)
theorem fwTy (a : ℕ) : Env.Wf ([⟨a, .ty .top⟩] : Env ℕ) := .ty .empty .top (by simp)
theorem fwVar (a : ℕ) : Ty.Wf ([⟨a, .sub .top⟩] : Env ℕ) (.fvar a) :=
  .var (show Binding.sub .top ∈ _ from by simp)
theorem fSubTop : Sub ([] : Env ℕ) .top .top := .top .empty .top

-- polymorphic identity at type ⊤ → ⊤ in any well-formed context
theorem fIdIn {Γ : Env ℕ} (h : Γ.Wf) : Typing Γ (.abs .top (.bvar 0)) (.arrow .top .top) :=
  .abs (LambdaCalculus.LocallyNameless.Context.dom Γ) (fun x hx => .var (.ty h .top hx) (by simp))
theorem fId (σ : Ty ℕ) (h : Ty.Wf [] σ) : Typing ([] : Env ℕ) (.abs σ (.bvar 0)) (.arrow σ σ) :=
  .abs ∅ (fun x _ => .var (.ty .empty h (by simp)) (by simp))
theorem fLcId : Term.LC (.abs .top (.bvar 0) : Term ℕ) := .abs ∅ .top (fun x _ => .var)

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.to_ok` idx 3: necessary (duplicate key)
theorem fe1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.to_ok 3 := fun h => by
  have : List.NodupKeys ([⟨0, .ty .top⟩, ⟨0, .ty .top⟩] : Env ℕ) := @h ℕ _ _
  simp [List.nodupKeys_cons] at this

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.weaken` idx 7: necessary (Δ shadows the sub binding of x0)
theorem fe2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.weaken 7 := fun h =>
  fNoLook (by simp) (h (Var := ℕ) (Γ := []) (Δ := [⟨0, .ty .top⟩]) (Θ := [⟨0, .sub .top⟩]) (fwVar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.weaken_head` idx 6: necessary (Γ shadows the sub binding of x0)
theorem fe3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.weaken_head 6 := fun h =>
  fNoLook (by simp) (h (Var := ℕ) (Γ := [⟨0, .ty .top⟩]) (Δ := [⟨0, .sub .top⟩]) (fwVar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.weaken_cons` idx 6: necessary (x5 unbound)
theorem fe4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.weaken_cons 6 := fun h =>
  fNoLook (by simp) (h (Var := ℕ) (σ := .fvar 5) (Δ := []) (X := 0) (b := .ty .top)
    (List.nodupKeys_singleton _))

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.weaken_cons` idx 7: necessary (head shadows the sub binding of x0)
theorem fe5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.weaken_cons 7 := fun h =>
  fNoLook (by simp) (h (Var := ℕ) (Δ := [⟨0, .sub .top⟩]) (X := 0) (b := .ty .top) (fwVar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.narrow` idx 8: necessary (x5 unbound)
theorem fe6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.narrow 8 := fun h =>
  fNoLook (by simp) (h (Var := ℕ) (σ := .fvar 5) (Γ := []) (Δ := []) (X := 0) (τ := .top) (τ' := .top)
    (List.nodupKeys_singleton _))

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.narrow_cons` idx 7: necessary (x5 unbound)
theorem fe7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.narrow_cons 7 := fun h =>
  fNoLook (by simp) (h (Var := ℕ) (σ := .fvar 5) (Δ := []) (X := 0) (τ := .top) (τ' := .top)
    (List.nodupKeys_singleton _))

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.map_subst` idx 11: necessary (Γ = [x0 : ⊤] shadows x0 <: ⊤ in Δ)
theorem fe8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.map_subst 11 := fun h => by
  have := h (Var := ℕ) (σ := .fvar 1) (X := 1) (Γ := [⟨0, .ty .top⟩]) (Δ := [⟨0, .sub .top⟩])
    (τ := .top) (τ' := .fvar 0) (.var (show Binding.sub .top ∈ _ from by simp)) (fwVar 0)
  simp [LambdaCalculus.LocallyNameless.Context.mapVal, HasSubstitution.subst, Ty.subst,
    Binding.subst] at this
  exact fNoLook (by simp) this

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.open_lc` idx 9: necessary (∀ <: ⊤. 0 opened with x0)
theorem fe9 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.open_lc 9 := fun h =>
  fNotWf0 (h (Var := ℕ) (Γ := []) (σ := .top) (τ := .bvar 0) (δ := .fvar 0) List.nodupKeys_nil
    (.all ∅ .top (fun X _ => fwVar X)))

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.of_bind_ty` idx 5: necessary (x0 : x5 with x5 unbound)
theorem fe10 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.of_bind_ty 5 := fun h =>
  fNoLook (by simp) (h (Var := ℕ) (Γ := [⟨0, .ty (.fvar 5)⟩]) (σ := .fvar 5) (X := 0) (by simp))

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.nmem_fv` idx 7: necessary (X = x0 bound)
theorem fe11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.nmem_fv 7 := fun h => by
  have := h (Var := ℕ) (Γ := [⟨0, .sub .top⟩]) (σ := .fvar 0) (X := 0) (fwVar 0)
  simp [Ty.fv] at this

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.narrow` idx 7: necessary (Γ = [x0 : x7])
theorem fe12 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.narrow 7 := fun h => by
  have := h (Var := ℕ) (Γ := [⟨0, .ty (.fvar 7)⟩]) (X := 1) (τ := .top) (τ' := .top) (Δ := []) .top
  cases this with | ty _ hw _ => exact fNoLook (by simp) hw

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.narrow` idx 8: necessary (τ' = x5 unbound)
theorem fe13 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.narrow 8 := fun h => by
  have := h (Var := ℕ) (Γ := []) (X := 0) (τ := .top) (τ' := .fvar 5) (Δ := []) (fwSub 0)
  cases this with | sub _ hw _ => exact fNotWf0 hw

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.strengthen` idx 6: necessary (Δ = [x1 : x3])
theorem fe14 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.strengthen 6 := fun h => by
  have := h (Var := ℕ) (Γ := []) (X := 0) (τ := .top) (Δ := [⟨1, .ty (.fvar 3)⟩])
  cases this with | ty _ hw _ => exact fNotWf0 hw

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.map_subst` idx 8: necessary (Γ = [x0 : x7])
theorem fe15 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.map_subst 8 := fun h => by
  have := h (Var := ℕ) (Γ := [⟨0, .ty (.fvar 7)⟩]) (X := 1) (τ := .top) (τ' := .top) (Δ := []) .top
  simp [LambdaCalculus.LocallyNameless.Context.mapVal, HasSubstitution.subst, Ty.subst,
    Binding.subst] at this
  cases this with | ty _ hw _ => exact fNotWf0 hw

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.map_subst` idx 9: necessary (substituting unbound x5)
theorem fe16 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.map_subst 9 := fun h => by
  have := h (Var := ℕ) (Γ := [⟨0, .ty (.fvar 1)⟩]) (X := 1) (τ := .top) (τ' := .fvar 5) (Δ := [])
    (.ty (fwSub 1) (fwVar 1) (by simp))
  simp [LambdaCalculus.LocallyNameless.Context.mapVal, HasSubstitution.subst, Ty.subst,
    Binding.subst] at this
  cases this with | ty _ hw _ => exact fNotWf0 hw

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.map_subst_nmem` idx 6: necessary (Γ = [x0 : x1], X = x1)
theorem fe17 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.map_subst_nmem 6 := fun h => by
  have := @h ℕ _ _ [⟨0, .ty (.fvar 1)⟩] 1 .top (by simp [LambdaCalculus.LocallyNameless.Context.dom])
  simp [LambdaCalculus.LocallyNameless.Context.mapVal, HasSubstitution.subst, Ty.subst,
    Binding.subst] at this

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.map_subst_nmem` idx 7: necessary (X = x1 bound, used by x0)
theorem fe18 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.map_subst_nmem 7 := fun h => by
  have := @h ℕ _ _ [⟨0, .ty (.fvar 1)⟩, ⟨1, .sub .top⟩] 1 .top (.ty (fwSub 1) (fwVar 1) (by simp))
  simp [LambdaCalculus.LocallyNameless.Context.mapVal, HasSubstitution.subst, Ty.subst,
    Binding.subst] at this

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env` idx 6: necessary (x0 bound in Γ, Δ = [])
theorem fe19 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env 6 := fun h =>
  fNotWf0 (h (Var := ℕ) (Γ := [⟨0, .sub .top⟩]) (Δ := []) (σ := .fvar 0) (fwVar 0)
    (List.nodupKeys_singleton _) List.nodupKeys_nil)

end W1c4

namespace W1c4
open Cslib LambdaCalculus.LocallyNameless.Fsub

theorem fTyNotLC {Γ : Env ℕ} {n : ℕ} {τ : Ty ℕ} : ¬ Typing Γ (.bvar n) τ := fun h =>
  nomatch (Typing.wf h).2.1
theorem fSubNotWfR {Γ : Env ℕ} {σ : Ty ℕ} {X : ℕ} (h0 : ¬ Ty.Wf Γ (.fvar X)) : ¬ Sub Γ σ (.fvar X) :=
  fun s => h0 (Sub.wf _ _ _ s).2.2
theorem fSubNotWfL {Γ : Env ℕ} {σ : Ty ℕ} {X : ℕ} (h0 : ¬ Ty.Wf Γ (.fvar X)) : ¬ Sub Γ (.fvar X) σ :=
  fun s => h0 (Sub.wf _ _ _ s).2.1
theorem fwSubTy : Env.Wf ([⟨1, .ty .top⟩, ⟨0, .sub .top⟩] : Env ℕ) := .ty (fwSub 0) .top (by simp)
theorem fwArr : Ty.Wf ([] : Env ℕ) (.arrow .top .top) := .arrow .top .top
theorem fwAll : Ty.Wf ([] : Env ℕ) (.all .top (.arrow .top .top)) := .all ∅ .top (fun _ _ => .arrow .top .top)
theorem fTabs : Typing ([] : Env ℕ) (.tabs .top (.abs .top (.bvar 0))) (.all .top (.arrow .top .top)) :=
  .tabs ∅ (fun X _ => fIdIn (fwSub X))
theorem fSubAll : Sub ([] : Env ℕ) (.all .top .top) (.all .top .top) :=
  .all ∅ fSubTop (fun X _ => .top (fwSub X) .top)

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.weaken` idx 9: necessary (Θ binds x1 : x7, ill-formed)
theorem ft1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.weaken 9 := fun h => by
  have := h (Var := ℕ) (Γ := []) (Δ := [⟨0, .ty .top⟩]) (Θ := [⟨1, .ty (.fvar 7)⟩])
    (t := .fvar 0) (τ := .top) (.var (fwTy 0) (by simp))
  cases (Typing.wf this).1 with | ty _ hw _ => exact fNoLook (by simp) hw

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.weaken_head` idx 8: necessary (Γ binds x1 : x7, ill-formed)
theorem ft2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.weaken_head 8 := fun h => by
  have := h (Var := ℕ) (Γ := [⟨1, .ty (.fvar 7)⟩]) (Δ := [⟨0, .ty .top⟩])
    (t := .fvar 0) (τ := .top) (.var (fwTy 0) (by simp))
  cases (Typing.wf this).1 with | ty _ hw _ => exact fNoLook (by simp) hw

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.narrow` idx 10: necessary (narrowing to unbound x7)
theorem ft3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.narrow 10 := fun h => by
  have := h (Var := ℕ) (Γ := [⟨1, .ty .top⟩]) (X := 0) (δ' := .top) (Δ := []) (δ := .fvar 7)
    (t := .fvar 1) (τ := .top) (.var fwSubTy (by simp))
  cases (Typing.wf this).1 with
  | ty hw _ _ => cases hw with | sub _ hw' _ => exact fNotWf0 hw'

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.narrow` idx 11: necessary (bvar 0 is untypable)
theorem ft4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.narrow 11 := fun h =>
  fTyNotLC (h (Var := ℕ) (Γ := []) (X := 0) (δ' := .top) (Δ := []) (δ := .top)
    (t := .bvar 0) (τ := .top) fSubTop)

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.subst_tm` idx 10: necessary (t = bvar 0)
theorem ft5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.subst_tm 10 := fun h => by
  have := h (Var := ℕ) (Γ := []) (X := 0) (σ := .top) (Δ := [⟨1, .ty .top⟩])
    (t := .bvar 0) (τ := .top) (s := .fvar 1) (.var (fwTy 1) (by simp))
  exact nomatch (Typing.wf this).2.1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.subst_tm` idx 11: necessary (t = x0, s = bvar 0)
theorem ft6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.subst_tm 11 := fun h => by
  have := h (Var := ℕ) (Γ := []) (X := 0) (σ := .top) (Δ := [])
    (t := .fvar 0) (τ := .top) (s := .bvar 0) (.var (fwTy 0) (by simp))
  simp [HasSubstitution.subst, Term.substTm] at this
  exact fTyNotLC this

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.subst_ty` idx 10: necessary (t = bvar 0)
theorem ft7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.subst_ty 10 := fun h => by
  have := h (Var := ℕ) (Γ := []) (X := 0) (δ' := .top) (Δ := []) (δ := .top)
    (t := .bvar 0) (τ := .top) fSubTop
  exact nomatch (Typing.wf this).2.1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.subst_ty` idx 11: necessary (substituting unbound x7 into x1 : x0)
theorem ft8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.subst_ty 11 := fun h => by
  have := h (Var := ℕ) (Γ := [⟨1, .ty (.fvar 0)⟩]) (X := 0) (δ' := .top) (Δ := []) (δ := .fvar 7)
    (t := .fvar 1) (τ := .fvar 0) (.var (.ty (fwSub 0) (fwVar 0) (by simp)) (by simp))
  have h1 := (Typing.wf this).1
  simp [LambdaCalculus.LocallyNameless.Context.mapVal, HasSubstitution.subst, Ty.subst,
    Binding.subst] at h1
  cases h1 with | ty _ hw _ => exact fNotWf0 hw

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.abs_inv` idx 8: necessary (γ' = x5 unbound)
theorem ft9 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.abs_inv 8 := fun h =>
  fSubNotWfR fNotWf0 (h (Var := ℕ) (Γ := []) (γ' := .fvar 5) (t := .bvar 0) (τ := .arrow .top .top)
    (γ := .top) (δ := .top) (.arrow fSubTop fSubTop)).1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.abs_inv` idx 9: necessary (γ = x5 unbound)
theorem ft10 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.abs_inv 9 := fun h =>
  fSubNotWfL fNotWf0 (h (Var := ℕ) (Γ := []) (γ' := .top) (t := .bvar 0) (τ := .arrow .top .top)
    (γ := .fvar 5) (δ := .top) (fId .top .top)).1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.tabs_inv` idx 9: necessary (γ' = x5 unbound)
theorem ft11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.tabs_inv 9 := fun h =>
  fSubNotWfR fNotWf0 (h (Var := ℕ) (Γ := []) (γ' := .fvar 5) (t := .bvar 0) (τ := .all .top .top)
    (γ := .top) (δ := .top) fSubAll).1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.tabs_inv` idx 10: necessary (γ = x5 unbound)
theorem ft12 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.tabs_inv 10 := fun h =>
  fSubNotWfL fNotWf0 (h (Var := ℕ) (Γ := []) (γ' := .top) (t := .abs .top (.bvar 0))
    (τ := .all .top (.arrow .top .top)) (γ := .fvar 5) (δ := .top) fTabs).1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.inl_inv` idx 7: necessary (t = bvar 0)
theorem ft13 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.inl_inv 7 := fun h => by
  obtain ⟨_, ht, _⟩ := h (Var := ℕ) (Γ := []) (t := .bvar 0) (τ := .sum .top .top) (γ := .top) (δ := .top)
    (.sum fSubTop fSubTop)
  exact fTyNotLC ht

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.inl_inv` idx 8: necessary (γ = x5 unbound)
theorem ft14 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.inl_inv 8 := fun h => by
  obtain ⟨_, _, hs⟩ := h (Var := ℕ) (Γ := []) (t := .abs .top (.bvar 0)) (τ := .sum (.arrow .top .top) .top)
    (γ := .fvar 5) (δ := .top) (.inl (fId .top .top) .top)
  exact fSubNotWfR fNotWf0 hs

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.inr_inv` idx 7: necessary (t = bvar 0)
theorem ft15 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.inr_inv 7 := fun h => by
  obtain ⟨_, ht, _⟩ := h (Var := ℕ) (Γ := []) (t := .bvar 0) (T := .sum .top .top) (γ := .top) (δ := .top)
    (.sum fSubTop fSubTop)
  exact fTyNotLC ht

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.inr_inv` idx 8: necessary (δ = x5 unbound)
theorem ft16 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.inr_inv 8 := fun h => by
  obtain ⟨_, _, hs⟩ := h (Var := ℕ) (Γ := []) (t := .abs .top (.bvar 0)) (T := .sum .top (.arrow .top .top))
    (γ := .top) (δ := .fvar 5) (.inr (fId .top .top) .top)
  exact fSubNotWfR fNotWf0 hs

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.canonical_form_abs` idx 5: necessary (application of identities)
theorem ft17 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.canonical_form_abs 5 := fun h => by
  obtain ⟨_, _, e⟩ := h (Var := ℕ) (σ := .top) (τ := .top)
    (t := .app (.abs (.arrow .top .top) (.bvar 0)) (.abs .top (.bvar 0)))
    (.app (fId _ fwArr) (fId .top .top))
  cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.canonical_form_abs` idx 6: necessary (inl value)
theorem ft18 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.canonical_form_abs 6 := fun h => by
  obtain ⟨_, _, e⟩ := h (Var := ℕ) (σ := .top) (τ := .top) (t := .inl (.abs .top (.bvar 0)))
    (.inl (.abs fLcId))
  cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.canonical_form_tabs` idx 5: necessary (identity applied to a type abstraction)
theorem ft19 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.canonical_form_tabs 5 := fun h => by
  obtain ⟨_, _, e⟩ := h (Var := ℕ) (σ := .top) (τ := .arrow .top .top)
    (t := .app (.abs (.all .top (.arrow .top .top)) (.bvar 0)) (.tabs .top (.abs .top (.bvar 0))))
    (.app (fId _ fwAll) fTabs)
  cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.canonical_form_tabs` idx 6: necessary (inl value)
theorem ft20 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.canonical_form_tabs 6 := fun h => by
  obtain ⟨_, _, e⟩ := h (Var := ℕ) (σ := .top) (τ := .top) (t := .inl (.abs .top (.bvar 0)))
    (.inl (.abs fLcId))
  cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.canonical_form_sum` idx 5: necessary (identity applied to an inl)
theorem ft21 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.canonical_form_sum 5 := fun h => by
  obtain ⟨_, e | e⟩ := h (Var := ℕ) (σ := .arrow .top .top) (τ := .top)
    (t := .app (.abs (.sum (.arrow .top .top) .top) (.bvar 0)) (.inl (.abs .top (.bvar 0))))
    (.app (fId _ (.sum fwArr .top)) (.inl (fId .top .top) .top)) <;> cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.canonical_form_sum` idx 6: necessary (abstraction value)
theorem ft22 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.canonical_form_sum 6 := fun h => by
  obtain ⟨_, e | e⟩ := h (Var := ℕ) (σ := .top) (τ := .top) (t := .abs .top (.bvar 0)) (.abs fLcId) <;> cases e

end W1c4
