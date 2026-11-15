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

namespace W2c2
open Cslib Relation LambdaCalculus.LocallyNameless.Untyped Term

universe u

theorem rtgStuck {α : Type} {r : α → α → Prop} {a b : α} (hs : ∀ t, ¬ r a t)
    (h : ReflTransGen r a b) : b = a := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => subst ih; exact (hs _ hbc).elim

theorem rtgNotLCr {r : Term ℕ → Term ℕ → Prop} (hr : ∀ a b, r a b → LC b) {a b : Term ℕ}
    (h : ReflTransGen r a b) (hb : ¬ LC b) : b = a := by
  cases h with
  | refl => rfl
  | tail _ s => exact absurd (hr _ _ s) hb

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
theorem lcK0 : LC (abs (fvar 0) : Term ℕ) := .abs ∅ _ (fun _ _ => LC.fvar 0)

-- the redex (λ.0) x0 and the stuck non-LC redex (λ.0) 0
local notation "𝔹" => (app (abs (bvar 0)) (fvar 0) : Term ℕ)
local notation "𝕊" => (app (abs (bvar 0)) (bvar 0) : Term ℕ)
theorem lcB : LC 𝔹 := .app lcId (.fvar 0)
theorem fbB : FullBeta 𝔹 (fvar 0) := .base (.beta lcId (.fvar 0))
theorem baB : BetaAt 0 𝔹 (fvar 0) := .outer lcId (.fvar 0)

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

theorem lcApp {a b : Term ℕ} (h : LC (app a b)) : LC a ∧ LC b := by cases h; exact ⟨by assumption, by assumption⟩
theorem notLCbvar {n : ℕ} : ¬ LC (bvar n : Term ℕ) := nofun
theorem notLCappR {a : Term ℕ} {n : ℕ} : ¬ LC (app a (bvar n)) := fun h => notLCbvar (lcApp h).2
theorem notLCappL {a : Term ℕ} {n : ℕ} : ¬ LC (app (bvar n) a) := fun h => notLCbvar (lcApp h).1
theorem notLCabs1 : ¬ LC (abs (bvar 1) : Term ℕ) := fun h => absurd ((lcAt_iff_LC _).2 h) (by decide)

-- η: λ.(x 0) ⭢ x
local notation "𝔼" x => (abs (app (fvar x) (bvar 0)) : Term ℕ)
theorem feE (x : ℕ) : FullEta (𝔼 x) (fvar x) := .base (.eta (.fvar x))
theorem feNotLC {M t : Term ℕ} (h : ¬ LC M) : ¬ FullEta M t := fun s => h (FullEta.step_lc_l s)
theorem feFvar {a : ℕ} {t : Term ℕ} : ¬ FullEta (fvar a) t := xiFvar (fun _ _ h => by cases h)
theorem feAbsFvar {a : ℕ} {t : Term ℕ} : ¬ FullEta (abs (fvar a)) t := by
  intro h; cases h with
  | base h => cases h
  | abs xs h =>
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset xs
    exact feFvar (h y hy)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.redex_app_l_cong` idx 5: necessary (λ.(x0 0) to x0, N = bvar 0)
theorem fe1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.redex_app_l_cong 5 := fun h => by
  have := rtgStuck (fun _ => feNotLC notLCappR) (@h ℕ (𝔼 0) (fvar 0) (bvar 0) (.single (feE 0)))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.redex_app_r_cong` idx 5: necessary (λ.(x0 0) to x0, N = bvar 0)
theorem fe2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.redex_app_r_cong 5 := fun h => by
  have := rtgStuck (fun _ => feNotLC notLCappL) (@h ℕ (𝔼 0) (fvar 0) (bvar 0) (.single (feE 0)))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_subst_cong_l` idx 8: necessary (substituting bvar 0 for x0)
theorem fe3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_subst_cong_l 8 := fun h => by
  have := @h ℕ _ _ 0 (𝔼 0) (fvar 0) (bvar 0) (feE 0)
  exact notLCbvar (n := 0) (FullEta.step_lc_r this)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_subst_cong_l` idx 8: necessary (substituting bvar 0 for x0)
theorem fe4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_subst_cong_l 8 := fun h => by
  have := @h ℕ _ _ 0 (𝔼 0) (fvar 0) (bvar 0) (.single (feE 0))
  change ReflTransGen FullEta (abs (app (bvar 0) (bvar 0))) (bvar 0) at this
  have := rtgNotLCr (fun _ _ s => FullEta.step_lc_r s) this notLCbvar
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_abs_close` idx 6: necessary (λ.x0 has no step)
theorem fe5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_abs_close 6 := fun h =>
  feAbsFvar (@h ℕ (fvar 0) (fvar 0) _ _ 1)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.redex_abs_close` idx 6: necessary (λ.x0 to λ.x1)
theorem fe6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.redex_abs_close 6 := fun h => by
  have := @h ℕ (fvar 0) (fvar 1) _ _ 2
  change ReflTransGen FullEta (abs (fvar 0)) (abs (fvar 1)) at this
  have := rtgStuck (fun _ => feAbsFvar) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.redex_abs_cong` idx 6: necessary (λ.x0 to λ.x1)
theorem fe7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.redex_abs_cong 6 := fun h => by
  have := rtgStuck (fun _ => feAbsFvar) (@h ℕ _ _ (fvar 0) (fvar 1) ∅)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_subst_cong_r` idx 8: necessary (s = bvar 0 x0)
theorem fe8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_subst_cong_r 8 := fun h => by
  have := @h ℕ _ _ 0 (app (bvar 0) (fvar 0)) (𝔼 1) (fvar 1) (feE 1)
  change ReflTransGen FullEta (app (bvar 0) (𝔼 1)) (app (bvar 0) (fvar 1)) at this
  have := rtgStuck (fun _ => feNotLC notLCappL) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_subst_cong_r` idx 8: necessary (s = bvar 0 x0)
theorem fe9 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_subst_cong_r 8 := fun h => by
  have := @h ℕ _ _ 0 (app (bvar 0) (fvar 0)) (𝔼 1) (fvar 1) (.single (feE 1))
  change ReflTransGen FullEta (app (bvar 0) (𝔼 1)) (app (bvar 0) (fvar 1)) at this
  have := rtgStuck (fun _ => feNotLC notLCappL) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_open_cong_r` idx 7: necessary (s = bvar 0, x0 to x1)
theorem fe10 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_open_cong_r 7 := fun h => by
  have := @h ℕ _ _ (bvar 0) (fvar 0) (fvar 1) lcId
  change ReflTransGen FullEta (fvar 0) (fvar 1) at this
  have := rtgStuck (fun _ => feFvar) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_open_cong_r` idx 7: necessary (s = bvar 0, x0 to x1)
theorem fe11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_open_cong_r 7 := fun h => by
  have := @h ℕ _ _ (bvar 0) (fvar 0) (fvar 1) lcId
  change ReflTransGen FullEta (fvar 0) (fvar 1) at this
  have := rtgStuck (fun _ => feFvar) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.close_eta_steps` idx 6: necessary (M = x0 = x)
theorem fe12 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.close_eta_steps 6 := fun h => by
  have := @h ℕ (fvar 0) (fvar 0) _ _ 0 .refl
  change ReflGen FullEta (abs (fvar 0)) (abs (bvar 0)) at this
  cases this with
  | single s => exact feAbsFvar s

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.close_eta_steps` idx 7: necessary (M = x0, N = x2, x = 1)
theorem fe13 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.close_eta_steps 7 := fun h => by
  have := @h ℕ (fvar 0) (fvar 2) _ _ 1 (by simp)
  change ReflGen FullEta (abs (fvar 0)) (abs (fvar 2)) at this
  cases this with
  | single s => exact feAbsFvar s

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.ind_on_depth` idx 2: necessary (P = not a bvar)
theorem id2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.ind_on_depth 2 := fun h =>
  @h ℕ (fun t => match t with | .bvar _ => False | _ => True) (fun _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) (bvar 0)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.ind_on_depth` idx 3: necessary (P = not an fvar)
theorem id3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.ind_on_depth 3 := fun h =>
  @h ℕ (fun t => match t with | .fvar _ => False | _ => True) (fun _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) (fvar 0)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.ind_on_depth` idx 4: necessary (P = not an app)
theorem id4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.ind_on_depth 4 := fun h =>
  @h ℕ (fun t => match t with | .app _ _ => False | _ => True) (fun _ => trivial) (fun _ => trivial)
    (fun _ _ _ => trivial) (app (fvar 0) (fvar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.ind_on_depth` idx 5: necessary (P = not an abs)
theorem id5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.ind_on_depth 5 := fun h =>
  @h ℕ (fun t => match t with | .abs _ => False | _ => True) (fun _ => trivial) (fun _ => trivial)
    (fun _ _ _ _ => trivial) (abs (fvar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.lcAt_openRec_lcAt` idx 4: necessary (M = bvar 5)
theorem la1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.lcAt_openRec_lcAt 4 := fun h =>
  absurd (@h ℕ (bvar 5) (fvar 0) 0) (by decide)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_abs_lc` idx 4: necessary (M = bvar 1)
theorem la2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_abs_lc 4 := fun h =>
  notLCabs1 (@h ℕ _ (bvar 1) (fvar 0))


-- Leftmost helpers: no position-0 step from an application with an abstraction head that is not a redex
theorem lmAbsHead {X M t : Term ℕ} {k : ℕ} (hb : BetaAt k (app (abs X) M) t) (h : ¬ LC (abs X) ∨ ¬ LC M) :
    k ≠ 0 := by
  cases hb with
  | outer h1 h2 => rcases h with h | h <;> contradiction
  | appL _ => simp [IsAbs.abs]
  | appR _ => simp [IsAbs.abs]

-- no position-0 step from an application whose head is a stuck non-abstraction with a redex
theorem lmStuckHead {L M t : Term ℕ} {k : ℕ} (hb : BetaAt k (app L M) t) (hna : ¬ IsAbs L)
    (hs : ∀ i t, ¬ BetaAt i L t) (hc : 0 < countRedexes L) : k ≠ 0 := by
  cases hb with
  | outer => exact absurd (IsAbs.abs _) hna
  | appL h => exact absurd h (hs _ _)
  | appR _ => simp [hna]; omega

theorem baS0 {i : ℕ} {t : Term ℕ} : ¬ BetaAt i 𝕊 t := by
  intro h; cases h with
  | outer _ h2 => exact notLCbvar h2
  | appL h =>
    cases h with
    | abs xs h =>
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset xs
      exact betaAtFvar (h y hy)
  | appR h => cases h

theorem cS0 : 0 < countRedexes 𝕊 := by decide
theorem naF {a : ℕ} : ¬ IsAbs (fvar a : Term ℕ) := fun h => by cases h
theorem naApp {a b : Term ℕ} : ¬ IsAbs (app a b) := fun h => by cases h

-- BetaAt is stable under opening with a free variable at any level (W1c4)
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

-- BetaAt.abs_close without its LC premise (W1c4 ba14)
theorem baAbsClose {Var : Type u} [HasFresh Var] [DecidableEq Var] {M M' : Term Var} {i : ℕ} {x : Var}
    (h : BetaAt i M M') : BetaAt i (Term.closeRec 0 x M).abs (Term.closeRec 0 x M').abs := by
  refine BetaAt.abs ∅ (fun z _ => ?_)
  simp only [Term.open']
  rw [openClose x z M 0, openClose x z M' 0]
  exact (baOpen h 0).rename x z

theorem lmStepsAbsClose {Var : Type u} [HasFresh Var] [DecidableEq Var] {M M' : Term Var} {x : Var}
    (h : ReflTransGen Leftmost M M') :
    ReflTransGen Leftmost (Term.closeRec 0 x M).abs (Term.closeRec 0 x M').abs := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.tail (baAbsClose step)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_l_cong` idx 4: necessary (x0 x0 to x1 x0)
theorem lm1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_l_cong 4 := fun h => by
  have := rtgStuck (fun _ => betaAtFvarApp) (@h ℕ (fvar 0) (fvar 1) (fvar 0) naF)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_l_cong` idx 5: necessary (L = λ.B to λ.x0, M = bvar 0 blocks the outer redex)
theorem lm2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_l_cong 5 := fun h => by
  have := @h ℕ (abs 𝔹) (abs (fvar 0)) (bvar 0) (.single (BetaAt.abs ∅ (fun x _ => baB)))
  have := rtgStuck (fun _ hb => lmAbsHead hb (Or.inr notLCbvar) rfl) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.app_r_cong` idx 5: necessary (x0 x0 has no step)
theorem lm3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.app_r_cong 5 := fun h =>
  betaAtFvarApp (@h ℕ (fvar 0) (fvar 0) (fvar 0) 0 rfl naF)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.app_r_cong` idx 6: necessary (L = (λ.0) 0, position shifts)
theorem lm4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.app_r_cong 6 := fun h =>
  lmStuckHead (@h ℕ 𝕊 𝔹 (fvar 0) 0 baB naApp) naApp (fun _ _ => baS0) cS0 rfl

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.app_r_cong` idx 7: necessary (L = λ.1)
theorem lm5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.app_r_cong 7 := fun h =>
  lmAbsHead (@h ℕ (abs (bvar 1)) 𝔹 (fvar 0) 0 baB rfl) (Or.inl notLCabs1) rfl

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_r_cong` idx 4: necessary (x0 x0 to x0 x1)
theorem lm6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_r_cong 4 := fun h => by
  have := rtgStuck (fun _ => betaAtFvarApp) (@h ℕ (fvar 0) (fvar 0) (fvar 1) rfl naF)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_r_cong` idx 5: necessary (L = (λ.0) 0)
theorem lm7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_r_cong 5 := fun h => by
  have := rtgStuck (fun _ hb => lmStuckHead hb naApp (fun _ _ => baS0) cS0 rfl)
    (@h ℕ 𝕊 𝔹 (fvar 0) (.single baB) naApp)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_r_cong` idx 6: necessary (L = λ.1)
theorem lm8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_r_cong 6 := fun h => by
  have := rtgStuck (fun _ hb => lmAbsHead hb (Or.inl notLCabs1) rfl)
    (@h ℕ (abs (bvar 1)) 𝔹 (fvar 0) (.single baB) rfl)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_cong` idx 5: necessary (x0 x0 to x1 x0)
theorem lm9 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_cong 5 := fun h => by
  have := rtgStuck (fun _ => betaAtFvarApp) (@h ℕ (fvar 0) (fvar 1) (fvar 0) (fvar 0) .refl rfl naF)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_cong` idx 6: necessary (x0 x0 to x0 x1)
theorem lm10 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_cong 6 := fun h => by
  have := rtgStuck (fun _ => betaAtFvarApp) (@h ℕ (fvar 0) (fvar 0) (fvar 0) (fvar 1) .refl rfl naF)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_cong` idx 7: necessary (L = (λ.0) 0)
theorem lm11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_cong 7 := fun h => by
  have := rtgStuck (fun _ hb => lmStuckHead hb naApp (fun _ _ => baS0) cS0 rfl)
    (@h ℕ 𝕊 𝕊 𝔹 (fvar 0) .refl (.single baB) naApp)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_cong` idx 8: necessary (L = λ.1)
theorem lm12 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_app_cong 8 := fun h => by
  have := rtgStuck (fun _ hb => lmAbsHead hb (Or.inl notLCabs1) rfl)
    (@h ℕ (abs (bvar 1)) (abs (bvar 1)) 𝔹 (fvar 0) .refl (.single baB) rfl)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.of_cbn` idx 3: necessary (x0 to x1)
theorem lm13 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.of_cbn 3 := fun h => by
  have := rtgStuck (fun _ => betaAtFvar) (@h ℕ (fvar 0) (fvar 1))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_abs_close` idx 6: necessary (λ.x0 to λ.x1)
theorem lm14 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_abs_close 6 := fun h => by
  have := @h ℕ (fvar 0) (fvar 1) _ _ 2 (.fvar 0)
  change ReflTransGen Leftmost (abs (fvar 0)) (abs (fvar 1)) at this
  have := rtgStuck (fun _ => baAbsFvar) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_abs_close` idx 7: removable (BetaAt.abs_close holds without LC, W1c4 ba14)
theorem lm15 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_abs_close 7 := by
  intro Var M M' _ _ x h
  exact lmStepsAbsClose h

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_abs_cong` idx 6: necessary (λ.x0 to λ.x1)
theorem lm16 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_abs_cong 6 := fun h => by
  have := rtgStuck (fun _ => baAbsFvar) (@h ℕ (fvar 0) (fvar 1) _ _ ∅ lcK0)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_abs_cong` idx 7: removable (same proof with the LC-free steps_abs_close)
theorem lm17 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_abs_cong 7 := by
  intro Var M M' _ _ xs cofin
  obtain ⟨w, hw⟩ := fresh_exists (xs ∪ M.fv ∪ M'.fv)
  simp only [Finset.mem_union, not_or] at hw
  rw [open_close w M 0 hw.1.2, open_close w M' 0 hw.2]
  exact lmStepsAbsClose (cofin w hw.1.1)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.of_standard` idx 5: necessary (x0 to x1)
theorem lm18 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.of_standard 5 := fun h => by
  have := rtgStuck (fun _ => betaAtFvar) (@h ℕ (fvar 0) (fvar 1) _ _ rfl)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.normalization` idx 5: removable (a non-LC term has no full-beta step, so N = M)
theorem lm19 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.normalization 5 := by
  intro Var M N _ _ h hn
  by_cases lc : LC M
  · exact Leftmost.normalization lc h hn
  · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, s, _⟩
    · rfl
    · exact absurd (FullBeta.step_lc_l s) lc

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.normalization` idx 6: necessary (x0 to x1)
theorem lm20 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.normalization 6 := fun h => by
  have := rtgStuck (fun _ => betaAtFvar) (@h ℕ (fvar 0) (fvar 1) _ _ (.fvar 0) rfl)
  simp at this


-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.step_multiApp_l` idx 5: necessary (Ns = [bvar 0])
theorem ma1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.step_multiApp_l 5 := fun h =>
  fbNotLC notLCappR (@h ℕ 𝔹 (fvar 0) [bvar 0] fbB)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.steps_multiApp_l` idx 4: necessary (x0 to x1)
theorem ma2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.steps_multiApp_l 4 := fun h => by
  have := rtgStuck (fun _ => xiFvar (fun _ _ => betaFvar)) (@h ℕ (fvar 0) (fvar 1) [] (by simp))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.steps_multiApp_l` idx 5: necessary (Ns = [bvar 0])
theorem ma3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.steps_multiApp_l 5 := fun h => by
  have := rtgStuck (fun _ => fbNotLC notLCappR) (@h ℕ 𝔹 (fvar 0) [bvar 0] (.single fbB))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.step_multiApp_r` idx 5: necessary (M = bvar 0)
theorem ma4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.step_multiApp_r 5 := fun h =>
  fbNotLC notLCappL (@h ℕ (bvar 0) [𝔹] [fvar 0] (.step fbB (by simp)))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.steps_multiApp_r` idx 4: necessary (x0 x0 to x0 x1)
theorem ma5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.steps_multiApp_r 4 := fun h => by
  have := rtgStuck (fun _ => fbFvarApp) (@h ℕ (fvar 0) [fvar 0] [fvar 1] (.fvar 0))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.steps_multiApp_r` idx 5: necessary (M = bvar 0)
theorem ma6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.steps_multiApp_r 5 := fun h => by
  have := rtgStuck (fun _ => fbNotLC notLCappL) (@h ℕ (bvar 0) [𝔹] [fvar 0] (.single (.step fbB (by simp))))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.listFullBeta_cons_r` idx 5: necessary (l = [bvar 0])
theorem ma7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.listFullBeta_cons_r 5 := fun h => by
  have := @h ℕ [𝔹] [fvar 0] [bvar 0] (.step fbB (by simp))
  change ListFullBeta [bvar 0, 𝔹] [bvar 0, fvar 0] at this
  cases this with
  | cons hl _ => exact notLCbvar hl

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.listFullBeta_cons_l` idx 5: necessary (l = [bvar 0])
theorem ma8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.listFullBeta_cons_l 5 := fun h => by
  have := @h ℕ [𝔹] [fvar 0] [bvar 0] (.step fbB (by simp))
  change ListFullBeta [𝔹, bvar 0] [fvar 0, bvar 0] at this
  cases this with
  | step _ hl => exact notLCbvar (hl (bvar 0) (by simp))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.invert_abs_multiApp_mst` idx 5: necessary ((λ.x0) x0 does not reach x5)
theorem ma9 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.invert_abs_multiApp_mst 5 := fun h => by
  obtain ⟨M', N', Ns', h1, h2, h3, h4⟩ := @h ℕ [] (fvar 0) (fvar 0) (fvar 5)
  have e1 := rtgStuck (fun _ => fbAbsFvar) h1
  have e2 := rtgStuck (fun _ => xiFvar (fun _ _ => betaFvar)) h2
  have e3 := rtgStuck (fun _ => nofun) h3
  simp only [abs.injEq] at e1
  subst e1 e2 e3
  rcases h4 with h4 | ⟨_, h4⟩
  · simp at h4
  · change ReflTransGen FullBeta (fvar 0) (fvar 5) at h4
    have := rtgStuck (fun _ => xiFvar (fun _ _ => betaFvar)) h4
    simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiApp_step_lc_r` idx 7: necessary (N = bvar 0 need not be in Ns')
theorem ma10 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiApp_step_lc_r 7 := fun h =>
  notLCbvar (@h ℕ [𝔹] [fvar 0] _ _ (.step fbB (by simp)) (bvar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiApp_steps_lc` idx 6: necessary (Ns = Ns' = [bvar 0])
theorem ma11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiApp_steps_lc 6 := fun h =>
  notLCbvar (@h ℕ [bvar 0] [bvar 0] _ _ .refl (bvar 0) (by simp))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.envLC_cons` idx 4: necessary (sub = bvar 0)
theorem ms1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.envLC_cons 4 := fun h =>
  notLCbvar (@h ℕ (bvar 0) [] 0 (fun hm => by simp at hm) 0 (bvar 0) (by simp))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.envLC_cons` idx 5: necessary (E = [0 ↦ bvar 0])
theorem ms2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.envLC_cons 5 := fun h =>
  notLCbvar (@h ℕ (fvar 0) [⟨0, bvar 0⟩] 1 (.fvar 0) 0 (bvar 0) (by simp))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiSubst_open_var` idx 6: necessary (E = [0 ↦ x1], x = 0, M = bvar 0)
theorem ms3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiSubst_open_var 6 := fun h => by
  have := @h ℕ _ _ (bvar 0) [⟨0, fvar 1⟩] 0 (fun hm => by simp at hm; rw [hm.2]; exact .fvar 1)
  exact absurd this (by decide)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiSubst_open_var` idx 7: necessary (E = [1 ↦ bvar 0], x = 0, M = x1)
theorem ms4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiSubst_open_var 7 := fun h => by
  have := @h ℕ _ _ (fvar 1) [⟨1, bvar 0⟩] 0 (by decide)
  exact absurd this (by decide)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.swap_open` idx 8: necessary (t₁ = bvar 1, m = bvar 0)
theorem pr1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.swap_open 8 := fun h =>
  absurd (@h ℕ _ 0 1 (bvar 1) (fvar 0) (bvar 0) (by decide) (.fvar 0)) (by decide)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.swap_open` idx 9: necessary (t₂ = bvar 0, m = bvar 1)
theorem pr2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.swap_open 9 := fun h =>
  absurd (@h ℕ _ 0 1 (fvar 0) (bvar 0) (bvar 1) (by decide) (.fvar 0)) (by decide)

-- opening with fvar x leaves a term unchanged when x does not occur in the result
theorem openNotin {Var : Type u} [DecidableEq Var] {x : Var} :
    ∀ (t : Term Var) (k : ℕ), x ∉ (Term.openRec k (fvar x) t).fv → Term.openRec k (fvar x) t = t
  | .bvar i, k, h => by
    simp only [Term.openRec] at h ⊢; split_ifs at h ⊢ with hk
    · simp at h
    · rfl
  | .fvar y, k, h => rfl
  | .app a b, k, h => by
    simp only [Term.openRec, fv, Finset.mem_union, not_or] at h ⊢
    rw [openNotin a k h.1, openNotin b k h.2]
  | .abs t, k, h => by
    simp only [Term.openRec, fv] at h ⊢
    rw [openNotin t (k+1) h]

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_eq_app` idx 8: removable (n = app n1 n2; x ∉ fv m forces n1 = m, x ∉ fv n forces n2 = bvar 0)
theorem pr3 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_eq_app 8 := by
  intro Var _ _ x m n hn hm h
  cases n with
  | bvar i =>
    simp only [Term.open', Term.openRec] at h; split at h <;> simp at h
  | fvar y => simp [Term.open', Term.openRec] at h
  | abs t => simp [Term.open', Term.openRec] at h
  | app n1 n2 =>
    simp only [Term.open', Term.openRec, app.injEq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [fv, Finset.mem_union, not_or] at hn
    congr 1
    · subst h1; exact (openNotin n1 0 hm).symm
    · cases n2 with
      | bvar i => simp only [Term.openRec] at h2; split at h2 <;> simp_all
      | fvar y => simp only [Term.openRec, fvar.injEq] at h2; subst h2; simp at hn
      | abs => simp [Term.openRec] at h2
      | app => simp [Term.openRec] at h2

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.beta_lc` idx 6: necessary (M = N = bvar 0)
theorem pr4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.beta_lc 6 := fun h =>
  notLCbvar (n := 0) (@h ℕ _ _ (bvar 0) (bvar 0) lcId)

theorem lcAtMono {Var : Type u} : ∀ (m : Term Var) (j k : ℕ), j ≤ k → LcAt j m = true → LcAt k m = true
  | .bvar i, j, k, hjk, h => by simp [LcAt] at h ⊢; omega
  | .fvar _, _, _, _, _ => rfl
  | .app a b, j, k, hjk, h => by
    simp only [LcAt, Bool.and_eq_true] at h ⊢
    exact ⟨lcAtMono a j k hjk h.1, lcAtMono b j k hjk h.2⟩
  | .abs t, j, k, hjk, h => by
    simp only [LcAt] at h ⊢
    exact lcAtMono t (j+1) (k+1) (by omega) h

-- closing then opening is substitution for any term with bound indices below the level (Probe2 coAux)
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

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.close_openRec_to_subst` idx 8: removable (opening inserts n without shifting; LC of m suffices)
theorem pr5 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.close_openRec_to_subst 8 := by
  intro Var _ _ m n x k hm
  exact coAux x n m k (lcAtMono m 0 k (Nat.zero_le _) ((lcAt_iff_LC m).mpr hm))


theorem ssStuck {n : ℕ} {M N : Term ℕ} (hs : ∀ j t, ¬ BetaAt j M t) (h : StandardSeq n M N) : N = M := by
  induction h with
  | refl => rfl
  | tail _ hb _ ih => rw [ih hs] at hb; exact (hs _ _ hb).elim

-- a term with exactly one standard step (to a stuck term, at position p)
theorem ssOne {A C : Term ℕ} {p : ℕ} (hA : ∀ m t, BetaAt m A t → t = C ∧ m = p)
    (hC : ∀ m t, ¬ BetaAt m C t) : ∀ k t, StandardSeq k A t → t = A ∨ (t = C ∧ k = p) := by
  intro k t h
  induction h with
  | refl => exact .inl rfl
  | tail _ s _ ih =>
    rcases ih hA with rfl | ⟨rfl, rfl⟩
    · exact .inr (hA _ _ s)
    · exact (hC _ _ s).elim

theorem baB2 {i : ℕ} {t : Term ℕ} (h : BetaAt i 𝔹 t) : i = 0 ∧ t = fvar 0 := by
  cases h with
  | outer => exact ⟨rfl, rfl⟩
  | appL h =>
    cases h with
    | abs xs h =>
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset xs
      exact (betaAtFvar (h y hy)).elim
  | appR h => exact (betaAtFvar h).elim

theorem baAbsBvar1 {i : ℕ} {t : Term ℕ} : ¬ BetaAt i (abs (bvar 1)) t := by
  intro h; cases h with
  | abs xs h =>
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset xs
    have h' : BetaAt i (bvar 1) _ := h y hy
    cases h'

theorem stuckAB1 {a i : ℕ} {t : Term ℕ} : ¬ BetaAt i (app (abs (bvar 1)) (fvar a)) t := by
  intro h; cases h with
  | outer h1 _ => exact notLCabs1 h1
  | appL h => exact baAbsBvar1 h
  | appR h => exact betaAtFvar h

theorem stFvarNe {a b : ℕ} (hab : a ≠ b) : ¬ Standard (fvar a : Term ℕ) (fvar b) := fun h => by
  cases h; exact hab rfl

theorem cbnFvar {a : ℕ} {t : Term ℕ} : ¬ CBN (fvar a) t := fun s => by cases s with | base h => cases h

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_cbn_step` idx 4: necessary (Var = Unit: λ.1 is LC vacuously, (λ.1) () steps to bvar 1)
theorem st1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_cbn_step 4 := fun h => by
  have lc1 : LC (abs (bvar 1) : Term Unit) := .abs {()} _ (fun x hx => absurd (Finset.mem_singleton_self x) hx)
  have := (@h Unit (app (abs (bvar 1)) (fvar ())) _ (.base (.beta lc1 (.fvar ())))).lc_r
  exact (nofun : ¬ LC (bvar 1 : Term Unit)) this

theorem fbAbsBvar0 {t : Term ℕ} : ¬ FullBeta (abs (bvar 0)) t := by
  intro h; cases h with
  | base h => cases h
  | abs xs h =>
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset xs
    exact xiFvar (fun _ _ => betaFvar) (h y hy)

-- B reaches only B and x0
theorem fbB2 {t : Term ℕ} (h : FullBeta 𝔹 t) : t = fvar 0 := by
  cases h with
  | base h => cases h; rfl
  | appR _ h => exact (fbAbsBvar0 h).elim
  | appL _ h => exact (xiFvar (fun _ _ => betaFvar) h).elim

theorem reachB {t : Term ℕ} (h : ReflTransGen FullBeta 𝔹 t) : t = 𝔹 ∨ t = fvar 0 := by
  induction h with
  | refl => exact .inl rfl
  | tail _ s ih =>
    rcases ih with rfl | rfl
    · exact .inr (fbB2 s)
    · exact (xiFvar (fun _ _ => betaFvar) s).elim

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.cbn_step_trans` idx 5: necessary (B does not reach x1)
theorem st2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.cbn_step_trans 5 := fun h => by
  have := (@h ℕ 𝔹 (fvar 1) (fvar 0) (.base (.beta lcId (.fvar 0)))).to_redex
  rcases reachB this with e | e <;> simp at e

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.head_leftmost` idx 4: necessary (B does not reach x1)
theorem st3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.head_leftmost 4 := fun h => by
  obtain ⟨k, _, hk⟩ := @h ℕ (fvar 1) (fvar 0) 0 𝔹 baB
  rcases ssOne (fun _ _ hb => (baB2 hb).symm) (fun _ _ => betaAtFvar) k _ hk with e | ⟨e, _⟩ <;> simp at e

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.head_leftmost` idx 6: necessary (M = x1 unrelated)
theorem st4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.head_leftmost 6 := fun h => by
  obtain ⟨k, _, hk⟩ := @h ℕ (fvar 0) (fvar 0) 0 .refl (fvar 1)
  have := ssStuck (fun _ _ => betaAtFvar) hk
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.cbn_head` idx 5: necessary (M = x1, P = N = x0)
theorem st5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.cbn_head 5 := fun h => by
  obtain ⟨k, hk⟩ := @h ℕ (fvar 1) (fvar 0) (fvar 0) 0 .refl
  have := ssStuck (fun _ _ => betaAtFvar) hk
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.cbn_head` idx 6: necessary (M = P = x0, N = x1)
theorem st6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.cbn_head 6 := fun h => by
  obtain ⟨k, hk⟩ := @h ℕ (fvar 0) (fvar 1) (fvar 0) 0 .refl
  have := ssStuck (fun _ _ => betaAtFvar) hk
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_abs` idx 5: necessary (L = λ.1, x0 to x1)
theorem st7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_abs 5 := fun h => by
  have := ssStuck (fun _ _ => stuckAB1) (@h ℕ (abs (bvar 1)) (fvar 0) (fvar 1) 0 (.abs _))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_abs` idx 6: necessary (L = x0: the step x0 B to x0 x0 sits at position 0, not 1)
theorem st8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_abs 6 := fun h => by
  have hk := @h ℕ (fvar 0) 𝔹 (fvar 0) 0 (StandardSeq.refl.tail baB le_rfl)
  have hA : ∀ m t, BetaAt m (app (fvar 0) 𝔹) t → t = app (fvar 0) (fvar 0) ∧ m = 0 := by
    intro m t hb
    cases hb with
    | appL hb => exact (betaAtFvar hb).elim
    | appR hb => obtain ⟨rfl, rfl⟩ := baB2 hb; simp [naF, countRedexes]
  rcases ssOne hA (fun _ _ => betaAtFvarApp) _ _ hk with e | ⟨_, e⟩ <;> simp at e

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_noAbs` idx 5: necessary (x0 x0 to x0 x1)
theorem st9a : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_noAbs 5 := fun h => by
  have := ssStuck (fun _ _ => betaAtFvarApp) (@h ℕ (fvar 0) (fvar 0) (fvar 1) 0 naF)
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_noAbs` idx 6: necessary (L = λ.1: the operand step sits at position 1, not 0)
theorem st9 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_noAbs 6 := fun h => by
  have hk := @h ℕ (abs (bvar 1)) 𝔹 (fvar 0) 0 (StandardSeq.refl.tail baB le_rfl)
  have hA : ∀ m t, BetaAt m (app (abs (bvar 1)) 𝔹) t → t = app (abs (bvar 1)) (fvar 0) ∧ m = 1 := by
    intro m t hb
    cases hb with
    | outer h1 _ => exact absurd h1 notLCabs1
    | appL hb => exact (baAbsBvar1 hb).elim
    | appR hb => obtain ⟨rfl, rfl⟩ := baB2 hb; simp [IsAbs.abs, countRedexes]
  rcases ssOne hA (fun _ _ => stuckAB1) _ _ hk with e | ⟨_, e⟩ <;> simp [countRedexes] at e

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_cong` idx 5: necessary (x0 x0 to x0 x1)
theorem st10 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_cong 5 := fun h => by
  obtain ⟨k, hk, _⟩ := @h ℕ (fvar 0) (fvar 0) (fvar 1) 0
  have := ssStuck (fun _ _ => betaAtFvarApp) hk
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_l_cong` idx 5: necessary (x0 x0 to x1 x0)
theorem st11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_l_cong 5 := fun h => by
  obtain ⟨k, hk, _⟩ := @h ℕ (fvar 0) (fvar 1) (fvar 0) 0
  have := ssStuck (fun _ _ => betaAtFvarApp) hk
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_l_cong_of_ne` idx 6: necessary (x0 x0 to x1 x0)
theorem st12 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_l_cong_of_ne 6 := fun h => by
  obtain ⟨k, hk, _⟩ := @h ℕ (fvar 0) (fvar 1) (fvar 0) 0 _ (by simp)
  have := ssStuck (fun _ _ => betaAtFvarApp) hk
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_l_cong_of_ne` idx 7: removable (if L = L' the empty sequence at index 0 meets the bound)
theorem st13 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_l_cong_of_ne 7 := by
  intro Var L L' M n _ h
  by_cases e : L = L'
  · subst e; exact ⟨0, .refl, Nat.zero_le _⟩
  · exact StandardSeq.app_l_cong_of_ne h e

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_tail` idx 8: necessary (x0 x5 does not reach x0 x0)
theorem st14 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_tail 8 := fun h => by
  have := ssStuck (fun _ _ => betaAtFvarApp) (@h ℕ (fvar 0) (fvar 0) (fvar 5) 𝔹 (fvar 0) 0 0 baB (Nat.zero_le _))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_tail` idx 9: necessary (x0 x0 to x0 x1)
theorem st15 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_tail 9 := fun h => by
  have := ssStuck (fun _ _ => betaAtFvarApp)
    (@h ℕ (fvar 0) (fvar 0) (fvar 0) (fvar 0) (fvar 1) 0 0 .refl (Nat.zero_le _))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_trans` idx 8: necessary (x0 x0 to x1 x0)
theorem st17 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_trans 8 := fun h => by
  obtain ⟨d, hd, _⟩ := @h ℕ (fvar 0) (fvar 1) (fvar 0) (fvar 0) 0 0 .refl (Nat.zero_le _)
  have := ssStuck (fun _ _ => betaAtFvarApp) hd
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_cong` idx 8: necessary (x0 x0 to x1 x0)
theorem st19 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_cong 8 := fun h => by
  obtain ⟨k, hk⟩ := @h ℕ (fvar 0) (fvar 1) (fvar 0) (fvar 0) 0 0 _ .refl
  have := ssStuck (fun _ _ => betaAtFvarApp) hk
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_cong` idx 9: necessary (x0 x0 to x0 x1)
theorem st20 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_cong 9 := fun h => by
  obtain ⟨k, hk⟩ := @h ℕ (fvar 0) (fvar 0) (fvar 0) (fvar 1) 0 0 _ .refl
  have := ssStuck (fun _ _ => betaAtFvarApp) hk
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst` idx 10: removable (Standard.lc_l of hN gives N.LC)
theorem st21 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst 10 := by
  intro Var M M' N N' _ _ hM hN x lcN'
  exact Standard.subst hM hN x hN.lc_l lcN'

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst` idx 11: removable (Standard.lc_r of hN gives N'.LC)
theorem st21b : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst 11 := by
  intro Var M M' N N' _ _ hM hN x lcN
  exact Standard.subst hM hN x lcN hN.lc_r

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_beta_step` idx 6: removable (FullBeta.step_lc_l gives M.LC)
theorem st22 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_beta_step 6 := by
  intro Var M N _ _ step
  exact Standard.of_beta_step step (FullBeta.step_lc_l step)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_inv` idx 5: necessary (M = x0, N = λ.x0)
theorem st23 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_inv 5 := fun h => by
  obtain ⟨M'', h1, _⟩ := @h ℕ (fvar 0) (abs (fvar 0)) _ _ (fvar 0) rfl
  have := rtgStuck (fun _ => cbnFvar) h1
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_inv` idx 7: necessary (M = N = x0)
theorem st24 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_inv 7 := fun h => by
  obtain ⟨M'', h1, _⟩ := @h ℕ (fvar 0) (fvar 0) _ _ (.fvar 0) (fvar 0)
  have := rtgStuck (fun _ => cbnFvar) h1
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst` idx 8: necessary (M = M' = bvar 0, x0 vs x1)
theorem st25a : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst 8 := fun h =>
  stFvarNe (a := 0) (b := 1) (by decide)
    (@h ℕ (bvar 0) (bvar 0) (fvar 0) (fvar 1) _ _ (Standard.lc_refl _ lcId) (.fvar 0) (.fvar 1))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst` idx 9: removable (Standard.lc_l of hN gives N.LC)
theorem st25b : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst 9 := by
  intro Var M M' N N' _ _ h1 h2 h3
  exact Standard.abs_subst h1 h2 h2.lc_l h3

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.trans_step` idx 6: necessary (M = x1, B to x0)
theorem st26 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.trans_step 6 := fun h =>
  stFvarNe (a := 1) (b := 0) (by decide) (@h ℕ (fvar 1) (fvar 0) 𝔹 _ _ fbB)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.iff_redex` idx 5: necessary (M = N = bvar 0)
theorem st28 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.iff_redex 5 := fun h =>
  notLCbvar (n := 0) ((@h ℕ (bvar 0) (bvar 0) _ _).2 .refl).lc_l

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.abs_close` idx 7: necessary (λ.x0 to λ.x1)
theorem st29 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.abs_close 7 := fun h => by
  have := @h ℕ (fvar 0) (fvar 1) 0 _ _ 2 (.fvar 0)
  change StandardSeq 0 (abs (fvar 0)) (abs (fvar 1)) at this
  have := ssStuck (fun _ _ => baAbsFvar) this
  simp at this

theorem ssAbsClose {Var : Type u} [HasFresh Var] [DecidableEq Var] {M M' : Term Var} {n : ℕ} {x : Var}
    (h : StandardSeq n M M') : StandardSeq n (Term.closeRec 0 x M).abs (Term.closeRec 0 x M').abs := by
  induction h with
  | refl => exact .refl
  | tail _ step hni ih => exact ih.tail (baAbsClose step) hni

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.abs_close` idx 8: removable (BetaAt.abs_close holds without LC, W1c4 ba14)
theorem st30 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.abs_close 8 := by
  intro Var M M' n _ _ x h
  exact ssAbsClose h

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.abs_cong` idx 6: necessary (λ.x0 to λ.x1)
theorem st31 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.abs_cong 6 := fun h => by
  obtain ⟨n, hn⟩ := @h ℕ (fvar 0) (fvar 1) _ _ ∅ lcK0
  have := ssStuck (fun _ _ => baAbsFvar) hn
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.abs_cong` idx 7: removable (same proof with the LC-free abs_close)
theorem st32 : drop% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.abs_cong 7 := by
  intro Var M M' _ _ xs cofin
  obtain ⟨w, hw⟩ := fresh_exists (xs ∪ M.fv ∪ M'.fv)
  simp only [Finset.mem_union, not_or] at hw
  obtain ⟨n, hn⟩ := cofin w hw.1.1
  rw [open_close w M 0 hw.1.2, open_close w M' 0 hw.2]
  exact ⟨n, ssAbsClose hn⟩

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.to_redex` idx 6: necessary (x0 to x1)
theorem st33 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.to_redex 6 := fun h => by
  have := rtgStuck (fun _ => xiFvar (fun _ _ => betaFvar)) (@h ℕ (fvar 0) (fvar 1) 0 _ _ (.fvar 0))
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.to_redex` idx 7: necessary (B (bvar 0) to x0 (bvar 0) by BetaAt, not by FullBeta)
theorem st34 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.to_redex 7 := fun h => by
  have := @h ℕ (app 𝔹 (bvar 0)) (app (fvar 0) (bvar 0)) 0 _ _ (StandardSeq.refl.tail (baB.appNoAbsL naApp) le_rfl)
  have := rtgStuck (fun _ => fbNotLC notLCappR) this
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.to_seq` idx 5: necessary (x0 to x1)
theorem st35 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.to_seq 5 := fun h => by
  obtain ⟨n, hn⟩ := @h ℕ (fvar 0) (fvar 1) _ _
  have := ssStuck (fun _ _ => betaAtFvar) hn
  simp at this

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.iff_seq` idx 5: necessary (M = N = bvar 0)
theorem st36 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.iff_seq 5 := fun h =>
  notLCbvar (n := 0) ((@h ℕ (bvar 0) (bvar 0) _ _).2 ⟨0, .refl⟩).lc_l


theorem baI {i : ℕ} {t : Term ℕ} : ¬ BetaAt i (abs (bvar 0)) t := by
  intro h; cases h with
  | abs xs h =>
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset xs
    exact betaAtFvar (h y hy)

-- leftmost (position-0) reachability from x0 ((I K1) B), K1 = λ.x1
theorem rtInv0 {k : ℕ} {v : Term ℕ} (hb : BetaAt k (app (abs (bvar 0)) (abs (fvar 1))) v) : v = abs (fvar 1) := by
  cases hb with
  | outer => rfl
  | appL h => exact (baI h).elim
  | appR h => exact (baAbsFvar h).elim

theorem rtInv1' {j : ℕ} {u : Term ℕ} (h : BetaAt j (app (app (abs (bvar 0)) (abs (fvar 1))) 𝔹) u) :
    j = 0 → u = app (abs (fvar 1)) 𝔹 := by
  cases h with
  | appL h => intro _; rw [rtInv0 h]
  | appR h => intro hj; simp [countRedexes, naApp] at hj

theorem rtInv1 {a m : ℕ} {t : Term ℕ} (hb : BetaAt m (app (fvar a) (app (app (abs (bvar 0)) (abs (fvar 1))) 𝔹)) t) :
    m = 0 → t = app (fvar a) (app (abs (fvar 1)) 𝔹) := by
  cases hb with
  | appL h => exact (betaAtFvar h).elim
  | appR h =>
    intro hm; simp [countRedexes, naF] at hm
    rw [rtInv1' h hm]

theorem rtInv2' {j : ℕ} {u : Term ℕ} (h : BetaAt j (app (abs (fvar 1)) 𝔹) u) : j = 0 → u = fvar 1 := by
  cases h with
  | outer => intro _; rfl
  | appL h => exact (baAbsFvar h).elim
  | appR h => intro hj; simp [countRedexes, IsAbs.abs] at hj

theorem rtInv2 {a m : ℕ} {t : Term ℕ} (hb : BetaAt m (app (fvar a) (app (abs (fvar 1)) 𝔹)) t) :
    m = 0 → t = app (fvar a) (fvar 1) := by
  cases hb with
  | appL h => exact (betaAtFvar h).elim
  | appR h =>
    intro hm; simp [countRedexes, naF] at hm
    rw [rtInv2' h hm]

-- reachability by position-0 standard sequences
theorem ssLm {A : Term ℕ} {P : Term ℕ → Prop} (hA : P A) (hP : ∀ m s t, P s → BetaAt m s t → m = 0 → P t) :
    ∀ k t, StandardSeq k A t → k = 0 → P t := by
  intro k t hs
  induction hs with
  | refl => intro; exact hA
  | tail _ s hnm ih => intro hm; exact hP _ _ _ (ih hA (by omega)) s hm

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_tail` idx 10: necessary (x0 ((I K1) B): step at 1 then at 0; x0 (K1 x0) is not reached by position-0 steps)
theorem st16 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_tail 10 := fun h => by
  have s1 : BetaAt 1 (app (app (abs (bvar 0)) (abs (fvar 1))) 𝔹) (app (app (abs (bvar 0)) (abs (fvar 1))) (fvar 0)) := by
    simpa [countRedexes] using BetaAt.appNoAbsR (N := app (abs (bvar 0)) (abs (fvar 1))) baB naApp
  have s2 : BetaAt 1 (app (fvar 0) (app (app (abs (bvar 0)) (abs (fvar 1))) 𝔹))
      (app (fvar 0) (app (app (abs (bvar 0)) (abs (fvar 1))) (fvar 0))) := by
    simpa [countRedexes] using BetaAt.appNoAbsR (N := fvar 0) s1 naF
  have s3 : BetaAt 0 (app (app (abs (bvar 0)) (abs (fvar 1))) (fvar 0)) (app (abs (fvar 1)) (fvar 0)) :=
    BetaAt.appNoAbsL (BetaAt.outer lcId lcK) naApp
  have := @h ℕ (fvar 0) (fvar 0) _ _ _ 0 1 (StandardSeq.refl.tail s2 (Nat.zero_le 1)) s3
  have key := ssLm (A := app (fvar 0) (app (app (abs (bvar 0)) (abs (fvar 1))) 𝔹))
    (P := fun t => t = app (fvar 0) (app (app (abs (bvar 0)) (abs (fvar 1))) 𝔹) ∨
      t = app (fvar 0) (app (abs (fvar 1)) 𝔹) ∨ t = app (fvar 0) (fvar 1)) (.inl rfl) (by
      intro m s t hs hb hm
      rcases hs with rfl | rfl | rfl
      · exact .inr (.inl (rtInv1 hb hm))
      · exact .inr (.inr (rtInv2 hb hm))
      · exact (betaAtFvarApp hb).elim)
  rcases key _ _ this (by simp [countRedexes, naF]) with e | e | e <;> simp at e


-- L = λ.(x9 ((I K1) B)) ignores its argument M = (I K1) x0
local notation "𝕃" => (abs (app (fvar 9) (app (app (abs (bvar 0)) (abs (fvar 1))) 𝔹)) : Term ℕ)
theorem rtInv0' {m : ℕ} {t : Term ℕ} (hb : BetaAt m (app 𝕃 (app (app (abs (bvar 0)) (abs (fvar 1))) (fvar 0))) t) :
    m = 0 → t = app (fvar 9) (app (app (abs (bvar 0)) (abs (fvar 1))) 𝔹) := by
  cases hb with
  | outer => intro _; rfl
  | appL h => intro hm; simp [IsAbs.abs] at hm
  | appR h => intro hm; simp [IsAbs.abs] at hm

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_trans` idx 9: necessary (L = λ.x9 ((I K1) B), L' = x9, M = (I K1) x0: the operator sequence ends at position 1)
theorem st18 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_r_trans 9 := fun h => by
  have s1 : BetaAt 1 (app (app (abs (bvar 0)) (abs (fvar 1))) 𝔹) (app (app (abs (bvar 0)) (abs (fvar 1))) (fvar 0)) := by
    simpa [countRedexes] using BetaAt.appNoAbsR (N := app (abs (bvar 0)) (abs (fvar 1))) baB naApp
  have s2 : BetaAt 1 (app (fvar 9) (app (app (abs (bvar 0)) (abs (fvar 1))) 𝔹))
      (app (fvar 9) (app (app (abs (bvar 0)) (abs (fvar 1))) (fvar 0))) := by
    simpa [countRedexes] using BetaAt.appNoAbsR (N := fvar 9) s1 naF
  have s3 : BetaAt 0 (app (app (abs (bvar 0)) (abs (fvar 1))) (fvar 0)) (app (abs (fvar 1)) (fvar 0)) :=
    BetaAt.appNoAbsL (BetaAt.outer lcId lcK) naApp
  have lcL : LC 𝕃 := .abs ∅ _ (fun _ _ => .app (.fvar 9) (.app (.app lcId lcK) lcB))
  have s0 : BetaAt 0 (app 𝕃 (app (app (abs (bvar 0)) (abs (fvar 1))) (fvar 0)))
      (app (fvar 9) (app (app (abs (bvar 0)) (abs (fvar 1))) 𝔹)) := BetaAt.outer lcL (.app (.app lcId lcK) (.fvar 0))
  obtain ⟨d, hd, hdle⟩ := @h ℕ 𝕃 (fvar 9) _ _ 1 0 (StandardSeq.refl.tail s3 le_rfl)
    ((StandardSeq.refl.tail s0 le_rfl).tail s2 (Nat.zero_le 1))
  have key := ssLm (A := app 𝕃 (app (app (abs (bvar 0)) (abs (fvar 1))) (fvar 0)))
    (P := fun t => t = app 𝕃 (app (app (abs (bvar 0)) (abs (fvar 1))) (fvar 0)) ∨
      t = app (fvar 9) (app (app (abs (bvar 0)) (abs (fvar 1))) 𝔹) ∨
      t = app (fvar 9) (app (abs (fvar 1)) 𝔹) ∨ t = app (fvar 9) (fvar 1)) (.inl rfl) (by
      intro m s t hs hb hm
      rcases hs with rfl | rfl | rfl | rfl
      · exact .inr (.inl (rtInv0' hb hm))
      · exact .inr (.inr (.inl (rtInv1 hb hm)))
      · exact .inr (.inr (.inr (rtInv2 hb hm)))
      · exact (betaAtFvarApp hb).elim)
  rcases key _ _ hd (by simpa [countRedexes, naF] using hdle) with e | e | e | e <;> simp at e

local notation "ω₀" => (abs (app (bvar 0) (bvar 0)) : Term ℕ)
local notation "Ω₀" => (app ω₀ ω₀ : Term ℕ)
theorem lcOm : LC ω₀ := .abs ∅ _ (fun x _ => .app (.fvar x) (.fvar x))
theorem stepOm : FullBeta Ω₀ Ω₀ := .base (.beta lcOm lcOm)
theorem notSNloop {t : Term ℕ} (h : FullBeta t t) : ¬ SN FullBeta t := by
  intro hs
  induction hs with
  | intro x _ ih => exact ih x h h
theorem notSNOm : ¬ SN FullBeta Ω₀ := notSNloop stepOm
theorem fbOm {t : Term ℕ} : ¬ FullBeta ω₀ t := by
  intro h; cases h with
  | base h => cases h
  | abs xs h =>
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset xs
    exact fbFvarApp (h z hz)
theorem snOm : SN FullBeta ω₀ := Acc.intro _ (fun _ hy => (fbOm hy).elim)
theorem snFvar (a : ℕ) : SN FullBeta (fvar a : Term ℕ) :=
  Acc.intro _ (fun y hy => (xiFvar (fun _ _ => betaFvar) hy).elim)
theorem snNotLC {t : Term ℕ} (h : ¬ LC t) : SN FullBeta t := Acc.intro _ (fun _ hy => (fbNotLC h hy).elim)
theorem omInv {t : Term ℕ} (h : FullBeta Ω₀ t) : t = Ω₀ := by
  cases h with
  | base h => cases h; rfl
  | appL _ h => exact (fbOm h).elim
  | appR _ h => exact (fbOm h).elim
theorem reachOm {t : Term ℕ} (h : ReflTransGen FullBeta Ω₀ t) : t = Ω₀ := by
  induction h with
  | refl => rfl
  | tail _ s ih => subst ih; exact omInv s

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_step` idx 3: necessary (x0 is SN, Ω is not)
theorem sn1 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_step 3 := fun h =>
  notSNOm (@h ℕ (fvar 0) Ω₀ (snFvar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_step` idx 4: necessary (Ω steps to Ω)
theorem sn2 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_step 4 := fun h =>
  notSNOm (@h ℕ Ω₀ Ω₀ stepOm)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_steps` idx 3: necessary (x0 is SN, Ω is not)
theorem sn3 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_steps 3 := fun h =>
  notSNOm (@h ℕ (fvar 0) Ω₀ (snFvar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_steps` idx 4: necessary (Ω reaches Ω)
theorem sn4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_steps 4 := fun h =>
  notSNOm (@h ℕ Ω₀ Ω₀ .refl)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app` idx 3: necessary (t = Ω, which never reaches an abstraction)
theorem sn5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app 3 := fun h =>
  notSNloop (Xi.appR (.fvar 0) stepOm)
    (@h ℕ Ω₀ (fvar 0) (snFvar 0) (fun h1 _ => absurd (reachOm h1) (by simp)))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app` idx 4: necessary (t = x0, s = Ω)
theorem sn6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app 4 := fun h =>
  notSNloop (Xi.appL (.fvar 0) stepOm)
    (@h ℕ (fvar 0) Ω₀ (snFvar 0) (fun h1 _ => absurd (rtgStuck (fun _ => xiFvar (fun _ _ => betaFvar)) h1) (by simp)))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app` idx 5: necessary (ω ω = Ω)
theorem sn7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app 5 := fun h =>
  notSNOm (@h ℕ ω₀ ω₀ snOm snOm)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app_left` idx 3: necessary (Ω (bvar 0) is not LC, hence SN)
theorem sn8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app_left 3 := fun h =>
  notSNOm (@h ℕ Ω₀ (bvar 0) (snNotLC notLCappR))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app_left` idx 4: necessary (M = Ω)
theorem sn9 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app_left 4 := fun h =>
  notSNOm (@h ℕ Ω₀ (fvar 0) (.fvar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app_right` idx 3: necessary ((bvar 0) Ω is not LC, hence SN)
theorem sn10 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app_right 3 := fun h =>
  notSNOm (@h ℕ (bvar 0) Ω₀ (snNotLC notLCappL))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app_right` idx 4: necessary (N = Ω)
theorem sn11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_app_right 4 := fun h =>
  notSNOm (@h ℕ (fvar 0) Ω₀ (.fvar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_neutral` idx 2: necessary (Ω)
theorem sn12 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_neutral 2 := fun h =>
  notSNOm (@h ℕ Ω₀)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs` idx 5: necessary (λ.Ω)
theorem sn13 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs 5 := fun h =>
  notSNloop (t := abs Ω₀) (.abs ∅ (fun _ _ => stepOm)) (@h ℕ _ _ Ω₀ (fvar 0) (.fvar 0))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs` idx 6: necessary (M = 0 Ω, N = bvar 0)
theorem sn14 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs 6 := fun h =>
  notSNloop (t := abs (app (bvar 0) Ω₀)) (.abs ∅ (fun x _ => Xi.appL (.fvar x) stepOm))
    (@h ℕ _ _ (app (bvar 0) Ω₀) (bvar 0) (snNotLC notLCappL))

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp` idx 6: necessary (M = x0, N = Ω, no args)
theorem sn15 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp 6 := fun h =>
  notSNloop (Xi.appL lcK0 stepOm) (@h ℕ _ _ [] (fvar 0) Ω₀ (snFvar 0) lcOmega' (.fvar 0))
where lcOmega' : LC Ω₀ := .app lcOm lcOm

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp` idx 7: necessary (M = bvar 0, N = ω, Ps = [ω]: reduces to Ω)
theorem sn16 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp 7 := fun h =>
  notSNOm (sn_step (Xi.appR lcOm (.base (.beta lcId lcOm)))
    (@h ℕ _ _ [ω₀] (bvar 0) ω₀ snOm lcOm (.app lcOm lcOm)))

end W2c2
namespace W2c2
open Cslib LambdaCalculus.Named.Untyped Term

theorem notAE {m n : Term ℕ} (h : m.fv ≠ n.fv) : ¬ m =α n := fun e => h (AlphaEquiv.same_fv e)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.rename_unused` idx 5: necessary (var 0, rename 0 to 1)
theorem nm1 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.rename_unused 5 := fun h =>
  absurd (@h ℕ _ (var 0) 0 1) (by decide)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.rename_vars_used` idx 5: necessary (var 0, rename 5 to 1)
theorem nm2 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.rename_vars_used 5 := fun h =>
  absurd (@h ℕ _ (var 0) 5 1) (by decide)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.rename_remove` idx 5: necessary (x = y = 0)
theorem nm3 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.rename_remove 5 := fun h =>
  absurd (@h ℕ _ (var 0) 0 0) (by decide)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.rename_fv` idx 5: necessary (λ1.0, rename 0 to 1 captures)
theorem nm4 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.rename_fv 5 := fun h =>
  absurd (@h ℕ _ (abs 1 (var 0)) 0 1) (by decide)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.rename_concat` idx 6: necessary (var 1, 0 to 1 to 2)
theorem nm5 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.rename_concat 6 := fun h =>
  absurd (@h ℕ _ (var 1) 0 1 2) (by decide)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.rename_comm_fresh` idx 7: necessary (x = z = 0)
theorem nm6 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.rename_comm_fresh 7 := fun h =>
  absurd (@h ℕ _ (var 0) 0 1 0 2 (by decide) (by decide)) (by decide)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.rename_comm_fresh` idx 8: necessary (y = z = 1)
theorem nm7 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.rename_comm_fresh 8 := fun h =>
  absurd (@h ℕ _ (var 0) 0 1 1 2 (by decide) (by decide)) (by decide)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.rename_comm_fresh` idx 9: necessary (w = x = 0)
theorem nm8 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.rename_comm_fresh 9 := fun h =>
  absurd (@h ℕ _ (var 1) 0 2 1 0 (by decide) (by decide)) (by decide)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.rename_comm` idx 7: necessary (y = z = 1)
theorem nm9 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.rename_comm 7 := fun h =>
  absurd (@h ℕ _ (var 0) 0 1 1 2 (by decide)) (by decide)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.rename_comm` idx 8: necessary (w = x = 0)
theorem nm10 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.rename_comm 8 := fun h =>
  absurd (@h ℕ _ (var 1) 0 2 1 0 (by decide)) (by decide)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.induction_by_sizeOf` idx 2: necessary (C = False)
theorem nm11 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.induction_by_sizeOf 2 := fun h =>
  @h ℕ (fun _ => False) (var 0)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.eq_sizeOf` idx 4: necessary (var 0 vs var 0 var 0)
theorem nm12 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.eq_sizeOf 4 := fun h =>
  absurd (@h ℕ _ (var 0) (app (var 0) (var 0))) (by simp)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.same_fv` idx 4: necessary (var 0 vs var 1)
theorem nm13 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.same_fv 4 := fun h =>
  absurd (@h ℕ _ (var 0) (var 1)) (by decide)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.symm` idx 4: necessary (var 0 vs var 1)
theorem nm14 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.symm 4 := fun h =>
  notAE (by decide) (@h ℕ _ (var 0) (var 1))

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.rename_preserve` idx 7: necessary (λ0.2 =α λ1.2, rename 2 to 0 captures)
theorem nm15 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.rename_preserve 7 := fun h =>
  notAE (by decide) (@h ℕ _ _ (abs 0 (var 2)) (abs 1 (var 2)) 2 0 (AlphaEquiv.abs (y := 3) (by decide) .var))

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.rename_preserve` idx 8: necessary (var 0 vs var 1)
theorem nm16 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.rename_preserve 8 := fun h =>
  notAE (by decide) (@h ℕ _ _ (var 0) (var 1) 5 6 (by decide))

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.abs_elim` idx 8: necessary (λ0.λ2.0 =α λ1.λ3.1, y = 2 captures)
theorem nm17 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.abs_elim 8 := fun h =>
  notAE (by decide) (@h ℕ _ _ (abs 2 (var 0)) (abs 3 (var 1)) 0 1 2
    (AlphaEquiv.abs (y := 4) (by decide) (AlphaEquiv.abs (y := 5) (by decide) .var)))

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.abs_elim` idx 9: necessary (var 0 vs var 1)
theorem nm18 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.abs_elim 9 := fun h =>
  notAE (by decide) (@h ℕ _ _ (var 0) (var 1) 5 5 6 (by decide))

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.trans` idx 6: necessary (var 0, var 1, var 1)
theorem nm19 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.trans 6 := fun h =>
  notAE (by decide) (@h ℕ _ _ (var 0) (var 1) (var 1) .var)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.trans` idx 7: necessary (var 0, var 0, var 1)
theorem nm20 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.trans 7 := fun h =>
  notAE (by decide) (@h ℕ _ _ (var 0) (var 0) (var 1) .var)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.rename_non_fv` idx 6: necessary (var 0, 0 to 1)
theorem nm21 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.rename_non_fv 6 := fun h =>
  notAE (by decide) (@h ℕ _ _ (var 0) 0 1 (by decide))

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.rename_non_fv` idx 7: necessary (λ0.1, 0 to 1 captures)
theorem nm22 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.rename_non_fv 7 := fun h =>
  notAE (by decide) (@h ℕ _ _ (abs 0 (var 1)) 0 1 (by decide))

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.abs_non_fv` idx 7: necessary (λ5.0 vs λ5.1)
theorem nm23 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.abs_non_fv 7 := fun h =>
  notAE (by decide) (@h ℕ _ _ (var 0) (var 1) 5 5 (by decide) (by decide))

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.abs_non_fv` idx 8: necessary (λ0.0 vs λ1.0)
theorem nm24 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.abs_non_fv 8 := fun h =>
  notAE (by decide) (@h ℕ _ _ (var 0) (var 0) 0 1 .var (by decide))

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.abs_non_fv` idx 9: necessary (λ1.0 vs λ0.0)
theorem nm25 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.abs_non_fv 9 := fun h =>
  notAE (by decide) (@h ℕ _ _ (var 0) (var 0) 1 0 .var (by decide))

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.abs_rename` idx 6: necessary (λ0.1 vs λ1.1)
theorem nm26 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.abs_rename 6 := fun h =>
  notAE (by decide) (@h ℕ _ _ (var 1) 0 1)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.context` idx 6: necessary (hole, var 0 vs var 1)
theorem nm27 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.AlphaEquiv.context 6 := fun h =>
  notAE (by decide) (@h ℕ _ _ (var 0) (var 1) .hole)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.subst.non_free` idx 6: necessary ((var 0)[0 := var 1])
theorem nm28 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.subst.non_free 6 := fun h =>
  notAE (by simp [Term.subst]) (@h ℕ _ _ (var 0) (var 1) 0)

-- `_private.Cslib.Languages.LambdaCalculus.Named.Untyped.Properties.0.Cslib.LambdaCalculus.Named.Untyped.Term.subst.abs_fresh_helper` idx 8: necessary (λ0.1 with z = 1 captures)
theorem nm29 : ¬ drop0% _private.Cslib.Languages.LambdaCalculus.Named.Untyped.Properties.«0».Cslib.LambdaCalculus.Named.Untyped.Term.subst.abs_fresh_helper 8 := fun h =>
  notAE (by simp [Term.subst]) (@h ℕ _ _ (var 1) (var 6) 5 0 1).1

-- `Cslib.LambdaCalculus.Named.Untyped.Term.subst.abs_fresh` idx 8: necessary (λ0.1 with z = 1 captures)
theorem nm30 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.subst.abs_fresh 8 := fun h =>
  notAE (by simp [Term.subst]) (@h ℕ _ _ (var 1) (var 6) 5 0 1)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.subst.preserve_AlphaEquiv` idx 8: necessary (var 0 vs var 1)
theorem nm31 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.subst.preserve_AlphaEquiv 8 := fun h =>
  notAE (by simp [Term.subst]) (@h ℕ _ _ (var 0) (var 1) (var 2) (var 2) 5 .var)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.subst.preserve_AlphaEquiv` idx 9: necessary (substituting var 0 vs var 1)
theorem nm32 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.subst.preserve_AlphaEquiv 9 := fun h =>
  notAE (by simp [Term.subst]) (@h ℕ _ _ (var 5) (var 5) (var 0) (var 1) 5 .var)

-- `Cslib.LambdaCalculus.Named.Untyped.Term.subst.commutativity` idx 8: necessary (x = y = 0)
theorem nm33 : ¬ drop0% Cslib.LambdaCalculus.Named.Untyped.Term.subst.commutativity 8 := fun h =>
  notAE (by simp [Term.subst]) (@h ℕ _ _ (var 0) (var 1) (var 2) 0 0)

end W2c2
