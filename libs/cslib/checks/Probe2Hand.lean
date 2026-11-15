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

-- ===== part A =====

namespace Probe2Hand
open Cslib Relation

theorem rtgInv {α : Type} {r : α → α → Prop} (P : α → Prop) (hP : ∀ a b, r a b → P a → P b)
    {a b : α} (h : ReflTransGen r a b) (ha : P a) : P b := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hP _ _ hbc ih

theorem eqvEmpty {α : Type} {a b : α} (h : EqvGen (fun _ _ : α => False) a b) : a = b := by
  induction h with
  | rel _ _ h => exact h.elim
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

-- `Relation.SymmGen.to_eqvGen` idx 4: necessary (empty relation, true ≠ false)
theorem r1 : ¬ drop0% Relation.SymmGen.to_eqvGen 4 := fun h =>
  absurd (eqvEmpty (@h Bool (fun _ _ => False) true false)) (by decide)

def R2a : ℕ → ℕ → Prop := fun a b => (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 4)
def R2b : ℕ → ℕ → Prop := fun a b => (a = 1 ∧ b = 3) ∨ (a = 2 ∧ b = 4)

-- `Relation.Commute.isTrans_join₂_reflTransGen` idx 3: necessary (0→3←1, 1→4←2 but 0,2 not joined)
theorem r2 : ¬ drop0% Relation.Commute.isTrans_join₂_reflTransGen 3 := fun h => by
  have := @IsTrans.trans _ _ (@h ℕ R2a R2b) 0 1 2
    ⟨3, .single (by simp [R2a]), .single (by simp [R2b])⟩ ⟨4, .single (by simp [R2a]), .single (by simp [R2b])⟩
  obtain ⟨c, h1, h2⟩ := this
  have a := rtgInv (fun c => c = 0 ∨ c = 3) (by intro a b hab ha; simp [R2a] at hab; omega) h1 (by simp)
  have b := rtgInv (fun c => c = 2 ∨ c = 4) (by intro a b hab ha; simp [R2b] at hab; omega) h2 (by simp)
  omega

def R3 : ℕ → ℕ → Prop := fun a b => (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨ (a = 2 ∧ b = 3)

theorem R3lc : LocallyConfluent R3 := by
  have p20 : ReflTransGen R3 2 0 := .head (show R3 2 1 by simp [R3]) (.single (show R3 1 0 by simp [R3]))
  have p13 : ReflTransGen R3 1 3 := .head (show R3 1 2 by simp [R3]) (.single (show R3 2 3 by simp [R3]))
  intro a b c hb hc
  simp only [R3] at hb hc
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hc with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> (try omega) <;>
  first
  | exact ⟨_, .refl, .refl⟩
  | exact ⟨0, .refl, p20⟩ | exact ⟨0, p20, .refl⟩
  | exact ⟨3, .refl, p13⟩ | exact ⟨3, p13, .refl⟩

-- `Relation.LocallyConfluent.Terminating_toConfluent` idx 3: necessary (0←1⇄2→3)
theorem r3 : ¬ drop0% Relation.LocallyConfluent.Terminating_toConfluent 3 := fun h => by
  obtain ⟨d, h1, h2⟩ := (@h ℕ R3 R3lc) (a := 1) (b := 0) (c := 3) (.single (by simp [R3]))
    (.head (show R3 1 2 by simp [R3]) (.single (show R3 2 3 by simp [R3])))
  have a := rtgInv (fun c => c = 0) (by intro a b hab ha; simp [R3] at hab; omega) h1 rfl
  have b := rtgInv (fun c => c = 3) (by intro a b hab ha; simp [R3] at hab; omega) h2 rfl
  omega

-- `Relation.StronglyCommute.extend` idx 8: necessary (empty relations, z ≠ y)
theorem r4 : ¬ drop0% Relation.StronglyCommute.extend 8 := fun h => by
  obtain ⟨w, h1, h2⟩ := @h ℕ (fun _ _ => False) (fun _ _ => False) 0 0 1
    (by intro _ _ _ h; exact h.elim) .refl
  have b := rtgInv (fun c => c = 1) (by intro a b hab; exact hab.elim) h2 rfl
  cases h1 with
  | refl => simp at b
  | single h => exact h

def R5 : ℕ → ℕ → Prop := fun a b => a = 0 ∧ (b = 1 ∨ b = 2)

-- `Relation.StronglyConfluent.toConfluent` idx 2: necessary (0→1, 0→2)
theorem r5 : ¬ drop0% Relation.StronglyConfluent.toConfluent 2 := fun h => by
  obtain ⟨d, h1, h2⟩ := (@h ℕ R5) (a := 0) (b := 1) (c := 2) (.single (by simp [R5])) (.single (by simp [R5]))
  have a := rtgInv (fun c => c = 1) (by intro a b hab ha; simp [R5] at hab; omega) h1 rfl
  have b := rtgInv (fun c => c = 2) (by intro a b hab ha; simp [R5] at hab; omega) h2 rfl
  omega

def R6 : ℕ → ℕ → Prop := fun a b => a = 0 ∧ b = 1

-- `Relation.RightEuclidean.rightTotal_cod` idx 2: necessary (single edge 0→1)
theorem r6 : ¬ drop0% Relation.RightEuclidean.rightTotal_cod 2 := fun h => by
  obtain ⟨⟨a, c, hc⟩, hab⟩ := (@h ℕ R6) ⟨1, 0, by simp [R6]⟩
  simp [R6] at hc hab; omega

def R7 : ℕ → ℕ → Prop := fun a b => (a = 0 ∨ a = 1) ∧ b = 2

-- `Relation.LeftEuclidean.antisymm_leftUnique` idx 2: necessary (0→2, 1→2)
theorem r7 : ¬ drop0% Relation.LeftEuclidean.antisymm_leftUnique 2 := fun h => by
  have := (@h ℕ R7 ⟨fun a b h1 h2 => by simp [R7] at h1 h2; omega⟩) (a := 0) (b := 1) (c := 2)
    (by simp [R7]) (by simp [R7])
  simp at this

-- `Set.SymmOn.of_dom` idx 7: necessary (single edge 0→1)
theorem r8 : ¬ drop0% Set.SymmOn.of_dom 7 := fun h => by
  have := @h ℕ 0 1 0 R6 (by intro a _ b hb hab; obtain ⟨c, hc⟩ := hb; simp [R6] at hab hc; omega)
    (by simp [R6])
  simp [R6] at this

def LU : LTS Unit Unit := ⟨fun _ _ _ => True⟩
def LE0 : LTS Unit Unit := ⟨fun _ _ _ => False⟩

theorem LUmtr (n : ℕ) : LU.MTr () (List.replicate n ()) () := by
  induction n with
  | zero => exact .refl
  | succ n ih => exact .stepL trivial ih

-- `Cslib.LTS.Bounded.bounded` idx 3: necessary (one state with a self-loop)
theorem r9 : ¬ drop0% Cslib.LTS.Bounded.bounded 3 := fun h => by
  obtain ⟨n, hn⟩ := @h Unit Unit LU
  have := hn () (List.replicate n ()) () (LUmtr n)
  simp at this

-- `Cslib.LTS.IsBisimulation.match_deterministic` idx 12: necessary (empty bisimulation)
theorem r10 : ¬ drop0% Cslib.LTS.IsBisimulation.match_deterministic 12 := fun h =>
  @h Unit Unit Unit LU LU (fun _ _ => False) () () () () () (by intro _ _ h; exact h.elim)
    (by intro _ _ _ _; rfl) trivial trivial

def LB : LTS Bool Unit := ⟨fun s _ t => s = false ∧ t = true⟩

-- `Cslib.LTS.IsBisimulationUpTo.le_bisimilarity` idx 6: necessary (total relation; false steps, true doesn't)
theorem r11 : ¬ drop0% Cslib.LTS.IsBisimulationUpTo.le_bisimilarity 6 := fun h => by
  have : LTS.Bisimilarity LB LB false true := @h Bool Bool Unit LB LB (fun _ _ => True) false true trivial
  obtain ⟨R, hR, hb⟩ := this
  obtain ⟨s, hs, _⟩ := (hb hR ()).1 true ⟨rfl, rfl⟩
  exact absurd hs.1 (by decide)

def LN0 : LTS ℕ Unit := ⟨fun _ _ _ => False⟩

-- `Cslib.LTS.Execution.split` idx 7: necessary (s = 1, ss = [0], n = 0)
theorem r12 : ¬ drop0% Cslib.LTS.Execution.split 7 := fun h => by
  have := (@h ℕ Unit LN0 1 [] 0 [0] 0 (by simp)).1
  simp at this
  cases this

def LS : LTS ℕ ℕ := ⟨fun s _ t => t = s + 1⟩

-- `Cslib.LTS.OmegaExecution.prepend_execution` idx 9: necessary (successor LTS, sl = [5])
theorem r13 : ¬ drop0% Cslib.LTS.OmegaExecution.prepend_execution 9 := fun h => by
  have := @h ℕ ℕ LS 0 [0] 0 [5] ⟨fun n => n⟩ ⟨fun _ => 0⟩ (fun i => rfl) rfl 0
  simp [LS, ωSequence.tail] at this

-- `Cslib.LTS.SimulationEquiv.trans` idx 11: necessary (lts₃ has a step, lts₁ none)
theorem r14 : ¬ drop0% Cslib.LTS.SimulationEquiv.trans 11 := fun h => by
  have := (@h Unit Unit LE0 Unit LE0 () () Unit LU ()
    ⟨⟨fun _ _ => True, trivial, by intro _ _ _ _ _ h; exact h.elim⟩,
     ⟨fun _ _ => True, trivial, by intro _ _ _ _ _ h; exact h.elim⟩⟩).2
  obtain ⟨R, hR, hs⟩ := this
  obtain ⟨_, h2, _⟩ := hs hR () () trivial
  exact h2

def LUB : LTS Unit Bool := ⟨fun _ _ _ => True⟩
def LUB0 : LTS Unit Bool := ⟨fun _ _ _ => False⟩

-- `Cslib.LTS.IsSimulation.isSimulation_saturate_left` idx 7: necessary (τ = false; lts₁ steps with true, lts₂ empty)
theorem r15 : ¬ drop0% Cslib.LTS.IsSimulation.isSimulation_saturate_left 7 := fun h => by
  let : HasTau Bool := ⟨false⟩
  obtain ⟨_, hs, _⟩ := @h Bool Unit Unit (fun _ _ => True) this LUB LUB0 () () trivial true ()
    (LTS.STr.single trivial)
  rcases hs with _ | ⟨_, h2, _⟩
  exact h2

-- `Cslib.LTS.Total.extend_omegaExecution` idx 4: necessary (empty LTS)
theorem r16 : ¬ drop0% Cslib.LTS.Total.extend_omegaExecution 4 := fun h => by
  obtain ⟨μs, ss, hω, _, _⟩ := @h ℕ Unit LN0 _ [] 0 0 .refl
  exact hω 0

instance LStotal : LTS.Total (⟨fun s _ t => t = s + 1⟩ : LTS ℕ Unit) := ⟨fun s _ => ⟨s + 1, rfl⟩⟩

-- `Cslib.LTS.Total.extend_omegaExecution` idx 8: necessary (successor LTS, μl = [], s = 0, t = 1)
theorem r17 : ¬ drop0% Cslib.LTS.Total.extend_omegaExecution 8 := fun h => by
  obtain ⟨μs, ss, _, h1, h2⟩ := @h ℕ Unit ⟨fun s _ t => t = s + 1⟩ _ _ [] 0 1
  simp at h2; omega

-- `Cslib.LTS.TraceEq.symm` idx 7: necessary (empty vs one-loop LTS)
theorem r18 : ¬ drop0% Cslib.LTS.TraceEq.symm 7 := fun h => by
  have e := @h Unit Unit LU Unit LE0 () ()
  have m : [()] ∈ LU.traces () := ⟨(), .stepL trivial .refl⟩
  unfold LTS.TraceEq at e
  rw [← e] at m
  obtain ⟨s, hs⟩ := m
  cases hs with
  | stepL h _ => exact h

end Probe2Hand

-- ===== part B =====

namespace Probe2Hand
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

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appNoAbsR` idx 5: necessary (M = M' = N = fvar 0)
theorem l23 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.appNoAbsR 5 := fun h =>
  betaAtFvarApp (@h ℕ (fvar 0) (fvar 0) (fvar 0) 0 (fun h => by cases h))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.step_subst` idx 8: necessary (substituting bvar 0 into (λ.0) x)
theorem l24 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.step_subst 8 := fun h => by
  have := @h ℕ (app (abs (bvar 0)) (fvar 0)) (fvar 0) (bvar 0) _ _ 0 (.base (.beta lcId (.fvar 0)))
  change CBN (app (abs (bvar 0)) (bvar 0)) (bvar 0) at this
  cases this with
  | base h => cases h with | beta _ h => cases h

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_app_l_cong` idx 4: necessary (x x ↠ y x)
theorem l25 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_app_l_cong 4 := fun h => by
  have := rtgStuck (fun _ => fbFvarApp) (@h ℕ (fvar 0) (fvar 1) (fvar 0) (.fvar 0))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_abs_close` idx 6: necessary (M = M' = fvar 0)
theorem l26 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_abs_close 6 := fun h => by
  have := @h ℕ (fvar 0) (fvar 0) _ _ 0
  change FullBeta (abs (bvar 0)) (abs (bvar 0)) at this
  cases this with
  | base h => cases h
  | abs xs h =>
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset xs
    exact xiFvar (fun _ _ => betaFvar) (h y hy)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_open_cong_abs` idx 7: necessary (s = s' = bvar 0, t = fvar 0, t' = fvar 1)
theorem l27 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_open_cong_abs 7 := fun h => by
  have := @h ℕ _ _ (bvar 0) (bvar 0) (fvar 0) (fvar 1) .refl (.fvar 0) lcId
  change ReflTransGen FullBeta (fvar 0) (fvar 1) at this
  have := rtgStuck (fun _ => xiFvar (fun _ _ => betaFvar)) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_open_cong_r` idx 6: necessary (s = app (bvar 0) (bvar 1), η-redex t)
theorem l28 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_open_cong_r 6 := fun h => by
  have := @h ℕ _ _ (app (bvar 0) (bvar 1)) (abs (app (fvar 5) (bvar 0))) (fvar 5)
    (.single (.base (.eta (.fvar 5))))
  change ReflTransGen FullEta (app (abs (app (fvar 5) (bvar 0))) (bvar 1)) (app (fvar 5) (bvar 1)) at this
  have := rtgStuck (fun t ht => by
    cases ht with
    | base h => cases h
    | appL _ h => cases h with | base h => cases h
    | appR h _ => cases h) this
  simp at this

def M29 : Term ℕ := app (abs (fvar 1)) (app (abs (bvar 0)) (fvar 0))

theorem lcK : LC (abs (fvar 1) : Term ℕ) := .abs ∅ _ (fun _ _ => LC.fvar 1)

theorem M29step {j : ℕ} {t : Term ℕ} (h : BetaAt j M29 t) (hj : j = 0) : t = fvar 1 := by
  unfold M29 at h
  cases h with
  | outer => rfl
  | appL h => simp [IsAbs.abs] at hj
  | appR h => simp at hj; exact absurd (IsAbs.abs _) hj.2

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.normalization` idx 7: necessary ((λ.y)((λ.0) x) reduces the argument first)
theorem l29 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.normalization 7 := fun h => by
  have := @h ℕ M29 (app (abs (fvar 1)) (fvar 0)) _ _ (.app lcK (.app lcId (.fvar 0)))
    (.single (.appL lcK (.base (.beta lcId (.fvar 0)))))
  have := rtgInv' this
  simp [M29] at this
where
  rtgInv' {N : Term ℕ} (h : ReflTransGen Leftmost M29 N) : N = M29 ∨ N = fvar 1 := by
    induction h with
    | refl => exact .inl rfl
    | tail _ hbc ih =>
      rcases ih with rfl | rfl
      · exact .inr (M29step hbc rfl)
      · exact (betaAtFvar hbc).elim

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_eq_app` idx 7: necessary (m = fvar 0 = x, n = app (bvar 0) (bvar 0))
theorem l30 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_eq_app 7 := fun h => by
  have := @h ℕ _ _ 0 (fvar 0) (app (bvar 0) (bvar 0)) (by simp [fv]) (.fvar 0) rfl
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.beta_lc` idx 5: necessary (M = bvar 1)
theorem l31 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.beta_lc 5 := fun h => by
  have := @h ℕ _ _ (bvar 1) (fvar 0) (.fvar 0)
  change LC (bvar 1) at this
  cases this

-- helper: closing then opening is substitution for any term with bound indices below the level
theorem coAux {Var : Type u} [DecidableEq Var] (x : Var) (n : Term Var) :
    ∀ (m : Term Var) (k : ℕ), LcAt k m = true →
      Term.openRec k n (Term.closeRec k x m) = Term.subst m x n
  | .bvar i, k, h => by
    simp [LcAt] at h; simp only [Term.closeRec, Term.openRec, Term.subst]; split <;> first | rfl | omega
  | .fvar y, k, h => by by_cases hxy : x = y <;> simp [Term.closeRec, Term.openRec, Term.subst, hxy]
  | .app a b, k, h => by
    simp [LcAt] at h
    simp [Term.closeRec, Term.openRec, Term.subst, coAux x n a k h.1, coAux x n b k h.2]
  | .abs t, k, h => by
    simp [LcAt] at h; simp [Term.closeRec, Term.openRec, Term.subst, coAux x n t (k+1) h]

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.close_open_to_subst` idx 7: removable (opening inserts n without shifting; LC of m suffices)
theorem l32 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.close_open_to_subst 7 := by
  intro Var _ _ m n x hm
  exact coAux x n m 0 ((lcAt_iff_LC m).mpr hm)

theorem ssStuck {n : ℕ} {M N : Term ℕ} (hs : ∀ j t, ¬ BetaAt j M t) (h : StandardSeq n M N) : N = M := by
  induction h with
  | refl => rfl
  | tail _ hb _ ih => rw [ih hs] at hb; exact (hs _ _ hb).elim

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_trans` idx 7: necessary (x x vs x y)
theorem l33 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_trans 7 := fun h => by
  obtain ⟨d, hd, _⟩ := @h ℕ (fvar 0) (fvar 0) (fvar 0) (fvar 1) 0 0 .refl (Nat.zero_le _)
  have := ssStuck (fun _ _ => betaAtFvarApp) hd
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst` idx 10: removable (Standard.lc_r gives N'.LC)
theorem l34 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst 10 := by
  intro Var M M' N N' _ _ h1 h2 h3
  exact Standard.abs_subst h1 h2 h3 h2.lc_r

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.neutral_step` idx 3: necessary ((λλ.0) x → λ.0)
theorem l35 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.neutral_step 3 := fun h => by
  have := @h ℕ (app (abs (abs (bvar 0))) (fvar 0)) (abs (bvar 0))
    (.base (.beta (.abs ∅ _ (fun _ _ => lcId)) (.fvar 0)))
  cases this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp` idx 8: removable (if N is not LC, the term is not LC, has no step, so is SN)
theorem l36 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp 8 := by
  intro Var _ _ Ps M N sN sMN lcMN
  by_cases hN : N.LC
  · exact sn_abs_app_multiApp sN sMN hN lcMN
  · refine Acc.intro _ (fun y hy => ?_)
    exact absurd (multiApp_lc.mp (FullBeta.step_lc_l hy)).1 (fun h => by cases h with | app _ h2 => exact hN h2)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp` idx 9: removable (if the reduct is not LC, the term is not LC, has no step, so is SN)
theorem l37 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp 9 := by
  intro Var _ _ Ps M N sN sMN lcN
  by_cases hl : ((M.open' N).multiApp Ps).LC
  · exact sn_abs_app_multiApp sN sMN lcN hl
  · refine Acc.intro _ (fun y hy => absurd ?_ hl)
    obtain ⟨h1, h2⟩ := multiApp_lc.mp (FullBeta.step_lc_l hy)
    cases h1 with | app hM _ => exact multiApp_lc.mpr ⟨beta_lc hM lcN, h2⟩

end Probe2Hand

-- ===== part C =====

namespace Probe2Hand
open Cslib Relation

-- `Cslib.SKI.add_correct` idx 4: necessary (same a, b at n = 0 and n = 1; Church numerals are injective)
theorem s22 : ¬ drop0% Cslib.SKI.add_correct 4 := fun h => by
  have h0 := h 0 0 SKI.Zero SKI.Zero SKI.zero_correct
  have h1 := h 1 0 SKI.Zero SKI.Zero SKI.zero_correct
  have := SKI.isChurch_injective _ _ 0 (1 + 0) h0 h1 ⟨_, .refl, .refl⟩
  omega

-- `Cslib.SKI.RFind_correct` idx 5: necessary (fNat = 0 everywhere: n = 0 and n = 1 are both roots)
theorem s21 : ¬ drop0% Cslib.SKI.RFind_correct 5 := fun h => by
  have hf : ∀ (i : ℕ) (y : SKI), SKI.IsChurch i y → SKI.IsChurch ((fun _ => 0) i) (SKI.app (SKI.app SKI.K SKI.Zero) y) :=
    fun i y _ => SKI.isChurch_trans 0 (.single (SKI.Red.red_K _ _)) SKI.zero_correct
  have h0 := h (fun _ => 0) _ hf 0 rfl
  have h1 := h (fun _ => 0) _ hf 1 rfl
  have := SKI.isChurch_injective _ _ 0 1 h0 h1 ⟨_, .refl, .refl⟩
  omega

-- `Cslib.SKI.prec_rec_correct` idx 4: necessary (f = g = zero code, tf = K ⬝ 1)
theorem s20 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.prec_rec_correct 4 :=
  fun h => by
  have hm : (0 : ℕ) ∈ (Nat.Partrec.Code.zero.prec Nat.Partrec.Code.zero).eval (Nat.pair 0 0) := by
    rw [Nat.Partrec.Code.eval_prec_zero]; exact Part.mem_some _
  have hT := h .zero .zero (SKI.app SKI.K (SKI.toChurch 1)) Nat.Partrec.Code.zero.toSKI
    (Nat.Partrec.Code.toSKI_correct _) 0 SKI.Zero SKI.zero_correct 0 0 hm SKI.Zero SKI.zero_correct
  have := SKI.isChurch_injective _ _ 0 1 hT (SKI.toChurch_correct 1)
    ⟨_, (SKI.rec_zero _ _ _ SKI.zero_correct).trans (.single (SKI.Red.red_K _ _)), .refl⟩
  omega

-- `Cslib.Logic.Modal.Satisfies.btl_past_always_elim` idx 6: necessary (φ = ⊥)
theorem m38 : ¬ drop0% Cslib.Logic.Modal.Satisfies.btl_past_always_elim 6 := fun h =>
  @h Unit Unit ⟨fun _ _ => True, fun _ _ => False⟩ () () .false trivial

abbrev τU : PFunctor := PFunctor.mkUnary Unit
abbrev τB : PFunctor := PFunctor.mkUnary Bool

-- `Cslib.Logic.Modal.theoryEq_satisfies` idx 8: necessary (φ = ⊥, w₁ = w₂)
theorem m44 : ¬ drop0% Cslib.Logic.Modal.theoryEq_satisfies 8 := fun h =>
  @h Unit τU Unit () () .false ⟨⟨fun _ _ _ => False⟩, fun _ _ => False⟩ rfl

-- `Cslib.Logic.Modal.Satisfies.dynBox_dynDiamond_diagonalInverse₁` idx 8: necessary (op₁ total, op₂ empty, φ = ⊤)
theorem m45 : ¬ drop0% Cslib.Logic.Modal.Satisfies.dynBox_dynDiamond_diagonalInverse₁ 8 := fun h => by
  have := @h τB _ Unit Unit () ⟨⟨fun op _ _ => op = true⟩, fun _ _ => False⟩ true false Logic.Modal.Proposition.true
  have h1 := Logic.Modal.Satisfies.imp_iff_imp.mp this Logic.Modal.Satisfies.true
  have h2 := Logic.Modal.Satisfies.dynBox_iff_forall.mp h1 () rfl
  obtain ⟨w', hw', _⟩ := Logic.Modal.Satisfies.dynDiamond_iff_exists.mp h2
  exact absurd hw' (by simp [Frame.diagonal])

-- `Cslib.Logic.Modal.Satisfies.unimodal_five_rightEuclidean` idx 7: necessary (single edge false → true)
theorem m46 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodal_five_rightEuclidean 7 := fun h => by
  have := (@h τU _ _ Bool Unit (Frame.ofRelation (fun a b => a = false ∧ b = true)) _).rightEuclidean
    (a := false) (b := true) (c := true) (by simp [Frame.ofRelation_rel_iff]) (by simp [Frame.ofRelation_rel_iff])
  simp [Frame.ofRelation_rel_iff] at this

def PU := Unit
instance : CommMonoid PU := inferInstanceAs (CommMonoid Unit)
instance : Logic.CLL.PhaseSpace PU := { bot := ∅ }

theorem orthE : Logic.CLL.PhaseSpace.orthogonal (∅ : Set PU) = Set.univ := by
  ext x; simp [Logic.CLL.PhaseSpace.orthogonal, Logic.CLL.PhaseSpace.imp]

theorem orthU : Logic.CLL.PhaseSpace.orthogonal (Set.univ : Set PU) = ∅ := by
  ext x
  simp only [Logic.CLL.PhaseSpace.orthogonal, Logic.CLL.PhaseSpace.imp, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hx () trivial

theorem psU_empty_fact : Logic.CLL.PhaseSpace.isFact (∅ : Set PU) := by
  unfold Logic.CLL.PhaseSpace.isFact
  rw [orthE, orthU]

-- `Cslib.Logic.CLL.PhaseSpace.of_Fact` idx 4: necessary (bot = ∅ on Unit; the empty fact)
theorem c41 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.of_Fact 4 := fun h => by
  have := @h PU _ ⟨∅, psU_empty_fact⟩ ()
  exact this

-- `Cslib.Logic.CLL.PhaseSpace.Fact.mkDual_coe` idx 4: necessary (G = H = ∅, ∅⫠ = univ)
theorem c42 : ¬ indep0% Cslib.Logic.CLL.PhaseSpace.Fact.mkDual_coe 4 := fun h => by
  have := @h PU _ ∅ ∅
  rw [orthE] at this
  exact (Set.eq_empty_iff_forall_notMem.mp this.symm) () trivial

-- `Cslib.Logic.CLL.PhaseSpace.biorth_least_fact` idx 5: necessary (G = univ, F = ∅)
theorem c43 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.biorth_least_fact 5 := fun h => by
  have := @h PU _ Set.univ ∅ psU_empty_fact
  rw [orthU, orthE] at this
  exact this (Set.mem_univ ())

open Logic.CLL in
-- `Cslib.Logic.CLL.Proof.isMLL_cutFree` idx 4: necessary (cut on 1 ⊕ 1)
theorem c40 : ¬ drop0% Cslib.Logic.CLL.Proof.isMLL_cutFree 4 := fun h => by
  have := @h Unit _ (Proof.cut (Γ := 0) (Δ := {1}) (a := Proposition.oplus 1 1) (Proof.oplus₁ Proof.one)
    (show Proof ((Proposition.with ⊥ ⊥ : Proposition Unit) ::ₘ {1}) from
      Proof.with (Proof.bot Proof.one) (Proof.bot Proof.one))) (by simp [Sequent.IsMLL])
  simp [Proof.IsMLL] at this

-- `Cslib.MachineLearning.PACLearning.SetShatters.superset` idx 5: necessary (C = univ, C' = ∅, W = ∅)
theorem p49 : ¬ drop0% Cslib.MachineLearning.PACLearning.SetShatters.superset 5 := fun h => by
  have := @h Unit Set.univ ∅ ∅ (fun W' hW' => ⟨fun _ => true, trivial, by simp [Set.subset_empty_iff.mp hW']⟩)
  obtain ⟨c, hc, _⟩ := this ∅ (subset_refl _)
  exact hc

open Cslib.Probability.PMF in
-- `Cslib.Probability.PMF.StatisticallyClose.trans` idx 7: necessary (ε = δ = 0, q = r = pure true, p = pure false)
theorem p50 : ¬ drop0% Cslib.Probability.PMF.StatisticallyClose.trans 7 := fun h => by
  have := @h Bool _ (PMF.pure false) (PMF.pure true) (PMF.pure true) 0 0 (StatisticallyClose.refl _)
  rw [zero_add, statisticallyClose_zero_iff] at this
  have := congrArg (fun p : PMF Bool => p true) this
  simp at this

end Probe2Hand

-- ===== part D =====

namespace Probe2Hand
open Cslib Relation

def T1 : LTS ℕ Bool := ⟨fun s μ t => (s = 0 ∧ μ = false ∧ (t = 1 ∨ t = 2)) ∨ (s = 1 ∧ μ = true ∧ t = 3)⟩
def T2 : LTS ℕ Bool := ⟨fun s μ t => (s = 0 ∧ μ = false ∧ t = 1) ∨ (s = 1 ∧ μ = true ∧ t = 2)⟩

instance T2det : T2.Deterministic := ⟨fun s μ t₁ t₂ h₁ h₂ => by simp [T2] at h₁ h₂; omega⟩

theorem T12sim : LTS.IsSimulation T1 T2
    (fun s t => (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) ∨ (s = 2 ∧ t = 1) ∨ (s = 3 ∧ t = 2)) := by
  intro s₁ s₂ hr μ s₁' htr
  simp only [T1] at htr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases htr with ⟨h0, rfl, ht⟩ | ⟨h0, rfl, rfl⟩ <;> (try omega)
  · exact ⟨1, by simp [T2], by omega⟩
  · exact ⟨2, by simp [T2], by omega⟩

theorem T21sim : LTS.IsSimulation T2 T1
    (fun s t => (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) ∨ (s = 2 ∧ t = 3)) := by
  intro s₁ s₂ hr μ s₁' htr
  simp only [T2] at htr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases htr with ⟨h0, rfl, rfl⟩ | ⟨h0, rfl, rfl⟩ <;> (try omega)
  · exact ⟨1, by simp [T1], by omega⟩
  · exact ⟨3, by simp [T1], by omega⟩

-- `Cslib.LTS.TraceEq.traceEq_of_tr_of_tr` idx 10: necessary (lts₁: 0 -a→ 1 -b→ 3, 0 -a→ 2; lts₂: 0 -a→ 1 -b→ 2)
theorem t19 : ¬ drop0% Cslib.LTS.TraceEq.traceEq_of_tr_of_tr 10 := fun h => by
  have e := @h ℕ Bool ℕ 0 0 false 2 1 T1 T2 T2det
    (LTS.SimulationEquiv.traceEq ⟨⟨_, by simp, T12sim⟩, ⟨_, by simp, T21sim⟩⟩)
    (by simp [T1]) (by simp [T2])
  have m : [true] ∈ T2.traces 1 := ⟨2, .stepL (by simp [T2]) .refl⟩
  unfold LTS.TraceEq at e
  rw [← e] at m
  obtain ⟨s, hs⟩ := m
  cases hs with
  | stepL h _ => simp [T1] at h

end Probe2Hand

-- ===== part E =====

namespace Probe2Hand
open Cslib Logic.CLL

/-- classical (Boolean) reading of CLL propositions -/
def bv : Proposition Unit → Prop
  | .atom _ => True
  | .atomDual _ => False
  | .one => True
  | .zero => False
  | .top => True
  | .bot => False
  | .tensor a b => bv a ∧ bv b
  | .parr a b => bv a ∨ bv b
  | .oplus a b => bv a ∨ bv b
  | .with a b => bv a ∧ bv b
  | .bang a => bv a
  | .quest a => bv a

theorem bv_dual (a : Proposition Unit) : bv a.dual ↔ ¬ bv a := by
  induction a <;> simp_all [bv, Proposition.dual] <;> tauto

theorem bv_sound {Γ : Sequent Unit} (p : Proof Γ) : ∃ a ∈ Γ, bv a := by
  induction p with
  | @ax a =>
    by_cases h : bv a
    · exact ⟨a, by simp, h⟩
    · exact ⟨a.dual, by simp, (bv_dual _).mpr h⟩
  | cut p q ihp ihq =>
    obtain ⟨b, hb, hbv⟩ := ihp
    obtain ⟨c, hc, hcv⟩ := ihq
    rw [Multiset.mem_cons] at hb hc
    rcases hb with rfl | hb
    · rcases hc with rfl | hc
      · exact absurd hbv ((bv_dual _).mp hcv)
      · exact ⟨c, Multiset.mem_add.mpr (.inr hc), hcv⟩
    · exact ⟨b, Multiset.mem_add.mpr (.inl hb), hbv⟩
  | one => exact ⟨_, Multiset.mem_cons_self _ _, trivial⟩
  | bot p ih => obtain ⟨b, hb, h⟩ := ih; exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | parr p ih =>
    obtain ⟨b, hb, h⟩ := ih
    simp only [Multiset.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · exact ⟨_, Multiset.mem_cons_self _ _, Or.inl h⟩
    · exact ⟨_, Multiset.mem_cons_self _ _, Or.inr h⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | tensor p q ihp ihq =>
    obtain ⟨b, hb, hbv⟩ := ihp
    obtain ⟨c, hc, hcv⟩ := ihq
    rw [Multiset.mem_cons] at hb hc
    rcases hb with rfl | hb
    · rcases hc with rfl | hc
      · exact ⟨_, Multiset.mem_cons_self _ _, And.intro hbv hcv⟩
      · exact ⟨c, by simp [hc], hcv⟩
    · exact ⟨b, by simp [hb], hbv⟩
  | oplus₁ p ih =>
    obtain ⟨b, hb, h⟩ := ih
    rw [Multiset.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, Multiset.mem_cons_self _ _, Or.inl h⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | oplus₂ p ih =>
    obtain ⟨b, hb, h⟩ := ih
    rw [Multiset.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, Multiset.mem_cons_self _ _, Or.inr h⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | «with» p q ihp ihq =>
    obtain ⟨b, hb, hbv⟩ := ihp
    obtain ⟨c, hc, hcv⟩ := ihq
    rw [Multiset.mem_cons] at hb hc
    rcases hb with rfl | hb
    · rcases hc with rfl | hc
      · exact ⟨_, Multiset.mem_cons_self _ _, And.intro hbv hcv⟩
      · exact ⟨c, Multiset.mem_cons_of_mem hc, hcv⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, hbv⟩
  | top => exact ⟨_, Multiset.mem_cons_self _ _, trivial⟩
  | quest p ih =>
    obtain ⟨b, hb, h⟩ := ih
    rw [Multiset.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, Multiset.mem_cons_self _ _, h⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | weaken p ih => obtain ⟨b, hb, h⟩ := ih; exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | contract p ih =>
    obtain ⟨b, hb, h⟩ := ih
    simp only [Multiset.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · exact ⟨_, Multiset.mem_cons_self _ _, h⟩
    · exact ⟨_, Multiset.mem_cons_self _ _, h⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | bang _ p ih =>
    obtain ⟨b, hb, h⟩ := ih
    rw [Multiset.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, Multiset.mem_cons_self _ _, h⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩

-- `Cslib.Logic.CLL.Proposition.Proposition.equiv_bang` idx 3: necessary (a = 1, a' = 0: ⊢ ʔ⊥, !0 is classically false)
theorem c39 : ¬ drop0% _private.Cslib.Logics.LinearLogic.CLL.Basic.«0».Cslib.Logic.CLL.Proposition.Proposition.equiv_bang 3 :=
  fun h => by
  obtain ⟨⟨p⟩, _⟩ := @h Unit .one .zero
  obtain ⟨b, hb, hbv⟩ := bv_sound p
  simp at hb
  rcases hb with rfl | rfl <;> simp [bv, Proposition.dual] at hbv

end Probe2Hand

-- ===== part F =====

namespace Probe2Hand
open Cslib MeasureTheory

universe u

open scoped Classical in
-- `Cslib.MachineLearning.PACLearning.error_map_eq_hypothesisError` idx 5: removable (map ≥ preimage for any set; ≤ via the measurable cover toMeasurable (h ∆ c) × univ ∪ graph complement)
theorem p48 : drop% Cslib.MachineLearning.PACLearning.error_map_eq_hypothesisError 5 := by
  intro α _ P h c hc
  simp only [MachineLearning.PACLearning.error, MachineLearning.PACLearning.hypothesisError]
  have hf : Measurable (fun x => (x, decide (x ∈ c))) :=
    Measurable.prodMk measurable_id
      (measurable_to_bool (by convert hc using 1; ext x; simp [decide_eq_true_eq]))
  refine le_antisymm ?_ ?_
  · set U := toMeasurable P (symmDiff h c)
    have hT : MeasurableSet (U ×ˢ (Set.univ : Set Bool) ∪ cᶜ ×ˢ {true} ∪ c ×ˢ {false}) :=
      (((measurableSet_toMeasurable _ _).prod MeasurableSet.univ).union
        (hc.compl.prod (measurableSet_singleton _))).union (hc.prod (measurableSet_singleton _))
    refine le_trans (measure_mono (μ := P.map _) (t := U ×ˢ (Set.univ : Set Bool) ∪ cᶜ ×ˢ {true} ∪ c ×ˢ {false}) ?_) ?_
    · rintro ⟨x, b⟩ hp
      simp only [Set.mem_ofPred_eq] at hp
      have hU : symmDiff h c ⊆ U := subset_toMeasurable _ _
      by_cases hx : x ∈ h <;> by_cases hxc : x ∈ c <;> cases b <;> simp_all [symmDiff_def] <;>
        first | exact (hU.1 hx).resolve_left hxc | exact (hU.2 hxc).resolve_left hx
    · rw [Measure.map_apply hf hT]
      apply le_of_eq
      rw [← measure_toMeasurable (symmDiff h c)]
      congr 1; ext x; by_cases hxc : x ∈ c <;> simp [hxc, U]
  · refine le_trans (le_of_eq ?_) (Measure.le_map_apply hf.aemeasurable _)
    congr 1; ext x
    by_cases hx : x ∈ h <;> by_cases hxc : x ∈ c <;> simp [symmDiff_def, hx, hxc]

end Probe2Hand

-- ===== part G =====

namespace Probe2Hand
open Cslib MeasureTheory MachineLearning.PACLearning
open scoped NNReal ENNReal

noncomputable def q1 : ℝ≥0 := 1/4
noncomputable def q3 : ℝ≥0 := 3/4
noncomputable def q2 : ℝ≥0 := 1/2

theorem q13 : q1 + q3 = 1 := by rw [← NNReal.coe_inj]; simp [q1, q3]; norm_num
theorem q1le3 : q1 ≤ q3 := by rw [← NNReal.coe_le_coe]; simp [q1, q3]; norm_num
theorem q3le : q3 ≤ q1 + q2 := by rw [← NNReal.coe_le_coe]; simp [q1, q2, q3]; norm_num
theorem q11lt : q1 + q1 < q3 := by rw [← NNReal.coe_lt_coe]; simp [q1, q3]; norm_num
theorem q1le2 : q1 ≤ q2 := by rw [← NNReal.coe_le_coe]; simp [q1, q2]; norm_num
theorem q2lt1 : q2 < 1 := by rw [← NNReal.coe_lt_coe]; simp [q2]; norm_num

def pa : Unit × Bool := ((), true)
def pb : Unit × Bool := ((), false)
noncomputable def Dt : Measure (Unit × Bool) := Measure.dirac pa
noncomputable def Df : Measure (Unit × Bool) :=
  (q1 : ℝ≥0∞) • Measure.dirac pa + (q3 : ℝ≥0∞) • Measure.dirac pb

theorem Dt_a : Dt {pa} = 1 := by simp [Dt]
theorem Dt_b : Dt {pb} = 0 := by simp [Dt, pa, pb]
theorem Df_a : Df {pa} = (q1 : ℝ≥0∞) := by simp [Df, pa, pb]
theorem Df_b : Df {pb} = (q3 : ℝ≥0∞) := by simp [Df, pa, pb]

instance : IsProbabilityMeasure Dt := by unfold Dt; infer_instance
instance : IsProbabilityMeasure Df := ⟨by
  simp only [Df, add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact_mod_cast q13⟩

theorem errT (D : Measure (Unit × Bool)) : error D (fun _ => true) = D {pb} := by
  unfold error; congr 1; ext ⟨u, v⟩; cases v <;> simp [pb]
theorem errF (D : Measure (Unit × Bool)) : error D (fun _ => false) = D {pa} := by
  unfold error; congr 1; ext ⟨u, v⟩; cases v <;> simp [pa]

theorem errC (D : Measure (Unit × Bool)) (c : Unit → Bool) :
    error D c = if c () then D {pb} else D {pa} := by
  have hc : c = fun _ => c () := funext fun u => rfl
  rw [hc]; cases c () <;> simp [errT, errF]

theorem optE (D : Measure (Unit × Bool)) : optimalError D Set.univ = min (D {pb}) (D {pa}) := by
  unfold optimalError
  apply le_antisymm
  · exact le_min (by rw [← errT]; exact iInf₂_le _ trivial) (by rw [← errF]; exact iInf₂_le _ trivial)
  · refine le_iInf₂ fun c _ => ?_
    rw [errC]; split
    · exact min_le_left _ _
    · exact min_le_right _ _

theorem optDf : optimalError Df Set.univ = (q1 : ℝ≥0∞) := by
  rw [optE, Df_a, Df_b]; exact min_eq_right (by exact_mod_cast q1le3)

noncomputable def e12 : Set.Ioo (0 : ℝ≥0) 1 := ⟨q2, by simp [q2], q2lt1⟩
noncomputable def e14 : Set.Ioo (0 : ℝ≥0) 1 :=
  ⟨q1, by simp [q1], lt_of_le_of_lt q1le2 q2lt1⟩
noncomputable def DD : Set (Measure (Unit × Bool)) := {Dt, Df}

theorem P0 : IsPACLearnerFor 0 e12 e12 Set.univ DD := by
  refine ⟨fun _ _ => true, fun D _ hD => ?_⟩
  have : {S : LabeledSample Unit Bool 0 | optimalError D Set.univ + ↑e12.val < error D ((fun _ _ => true) S)} = ∅ := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    rw [errT]
    rcases hD with rfl | rfl
    · rw [Dt_b]; exact zero_le
    · rw [Df_b, optDf]
      exact_mod_cast q3le
  rw [this]; simp

theorem piFin1 (D : Measure (Unit × Bool)) [IsProbabilityMeasure D] (B : Set (Unit × Bool)) :
    Measure.pi (fun _ : Fin 1 => D) {S | S 0 ∈ B} = D B := by
  have : {S : Fin 1 → Unit × Bool | S 0 ∈ B} = Set.pi Set.univ (fun _ => B) := by
    ext S; simp [Fin.forall_fin_one]
  rw [this, Measure.pi_pi]; simp

theorem P1 : IsPACLearnerFor 1 e14 e12 Set.univ DD := by
  refine ⟨fun S _ => (S 0).2, fun D _ hD => ?_⟩
  rcases hD with rfl | rfl
  · refine le_trans (measure_mono (t := {S | S 0 ∈ ({pb} : Set (Unit × Bool))}) ?_) ?_
    · intro S hS
      simp only [Set.mem_ofPred_eq] at hS
      rw [errC, optE, Dt_a, Dt_b] at hS
      simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
      generalize S 0 = p at hS ⊢
      obtain ⟨u, v⟩ := p
      cases v
      · rfl
      · simp at hS
    · rw [piFin1, Dt_b]; exact zero_le
  · refine le_trans (measure_mono (t := {S | S 0 ∈ ({pa} : Set (Unit × Bool))}) ?_) ?_
    · intro S hS
      simp only [Set.mem_ofPred_eq] at hS
      rw [errC, optDf, Df_a, Df_b] at hS
      simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
      generalize S 0 = p at hS ⊢
      obtain ⟨u, v⟩ := p
      cases v
      · simp only [Bool.false_eq_true, ite_false] at hS
        exact absurd hS (not_lt.mpr le_self_add)
      · rfl
    · rw [piFin1, Df_a]; exact_mod_cast q1le2

theorem P0' : ¬ IsPACLearnerFor 0 e14 e12 Set.univ DD := by
  rintro ⟨A, hA⟩
  have huniv : ∀ (D : Measure (Unit × Bool)) [IsProbabilityMeasure D],
      (∀ S, optimalError D Set.univ + ↑e14.val < error D (A S)) →
      Measure.pi (fun _ : Fin 0 => D) {S | optimalError D Set.univ + ↑e14.val < error D (A S)} = 1 := by
    intro D _ hall
    have : {S : LabeledSample Unit Bool 0 | optimalError D Set.univ + ↑e14.val < error D (A S)} = Set.univ :=
      Set.eq_univ_of_forall hall
    rw [this]; simp
  have hS : ∀ S : LabeledSample Unit Bool 0, S = Fin.elim0 := fun S => funext (fun i => i.elim0)
  have h2 : ¬ (1 : ℝ≥0∞) ≤ ↑e12.val := by
    intro h; exact absurd (show (1 : ℝ≥0) ≤ q2 by exact_mod_cast h) (not_le.mpr q2lt1)
  cases hv : A Fin.elim0 ()
  · have := hA Dt (by simp [DD])
    rw [huniv Dt (fun S => by
      rw [hS S, errC, hv, optE, Dt_a, Dt_b]
      simp only [Bool.false_eq_true, ite_false, zero_le, min_eq_left, zero_add]
      exact_mod_cast lt_of_le_of_lt q1le2 q2lt1)] at this
    exact h2 this
  · have := hA Df (by simp [DD])
    rw [huniv Df (fun S => by
      rw [hS S, errC, hv, optDf, Df_b]
      simp only [ite_true]
      exact_mod_cast q11lt)] at this
    exact h2 this

-- `Cslib.MachineLearning.PACLearning.sampleComplexity_antitone_ε` idx 7: necessary (Unit × Bool, 𝒟 = {dirac (·,true), ¼ dirac true + ¾ dirac false}, C = univ, δ = ½: 0 samples suffice at ε = ½, one sample is needed at ε = ¼)
theorem p47 : ¬ drop0% Cslib.MachineLearning.PACLearning.sampleComplexity_antitone_ε 7 := fun h => by
  have hle := @h Unit Bool _ _ e12 e14 e12 Set.univ DD ⟨0, P0⟩
  have hz : sampleComplexity IsPACLearnerFor Set.univ e12 e12 DD = 0 := Nat.eq_zero_of_le_zero (Nat.sInf_le P0)
  have hne : sampleComplexity IsPACLearnerFor Set.univ e14 e12 DD ≠ 0 := by
    intro h0
    have hm := Nat.sInf_mem (⟨1, P1⟩ : Set.Nonempty {m | IsPACLearnerFor m e14 e12 Set.univ DD})
    unfold sampleComplexity at h0
    rw [h0] at hm
    exact P0' hm
  omega

end Probe2Hand
