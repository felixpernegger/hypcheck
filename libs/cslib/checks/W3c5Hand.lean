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

namespace W3c5.ND
open Cslib Relation

abbrev τU : PFunctor := PFunctor.mkUnary Unit

section ND
open Cslib.Logic Cslib.Logic.PL Cslib.Logic.PL.NaturalDeduction Cslib.Logic.InferenceSystem

/-- Boolean (Prop-valued) reading of propositions. -/
def ev {Atom : Type} (v : Atom → Prop) : Proposition Atom → Prop
  | .atom x => v x
  | .falsum => False
  | .and a b => ev v a ∧ ev v b
  | .or a b => ev v a ∨ ev v b
  | .imp a b => ev v a → ev v b

/-- soundness of natural deduction for the reading `ev v` -/
theorem sound {Atom : Type} [DecidableEq Atom] {T : Set (Proposition Atom)} {Γ : Ctx Atom}
    {A : Proposition Atom} (v : Atom → Prop) (D : Derivation T Γ A) (hT : ∀ B ∈ T, ev v B) :
    (∀ B ∈ Γ, ev v B) → ev v A := by
  induction D with
  | ax h => exact fun _ => hT _ h
  | ass h => exact fun hΓ => hΓ _ h
  | efq A D ih => exact fun hΓ => (ih hΓ).elim
  | andI _ _ ih1 ih2 => exact fun hΓ => (show _ ∧ _ from ⟨ih1 hΓ, ih2 hΓ⟩)
  | andE₁ _ ih => exact fun hΓ => (show _ ∧ _ from ih hΓ).1
  | andE₂ _ ih => exact fun hΓ => (show _ ∧ _ from ih hΓ).2
  | orI₁ _ ih => exact fun hΓ => (show _ ∨ _ from Or.inl (ih hΓ))
  | orI₂ _ ih => exact fun hΓ => (show _ ∨ _ from Or.inr (ih hΓ))
  | orE _ _ _ ih ih1 ih2 =>
    intro hΓ
    rcases (show _ ∨ _ from ih hΓ) with h | h
    · exact ih1 fun B hB => by
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact h
        · exact hΓ _ hB
    · exact ih2 fun B hB => by
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact h
        · exact hΓ _ hB
  | impI Γ _ ih =>
    exact fun hΓ => (show _ → _ from fun h => ih fun B hB => by
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact h
        · exact hΓ _ hB)
  | impE _ _ ih1 ih2 => exact fun hΓ => (show _ → _ from ih1 hΓ) (ih2 hΓ)

theorem sound' {Atom : Type} [DecidableEq Atom] {T : Set (Proposition Atom)} {Γ : Ctx Atom}
    {A : Proposition Atom} (v : Atom → Prop) (h : DerivableIn (ND T) (Γ, A))
    (hT : ∀ B ∈ T, ev v B) (hΓ : ∀ B ∈ Γ, ev v B) : ev v A :=
  let ⟨D⟩ := h; sound v D hT hΓ

abbrev PU := Proposition Unit
abbrev E0 : Set PU := ∅
abbrev aU : PU := .atom ()
/-- `{⊤} ⊢ ⊥` is not derivable without axioms -/
theorem noTopBot (h : DerivableIn (ND E0) (({⊤} : Ctx Unit), (⊥ : PU))) : False :=
  sound' (fun _ => False) h (by simp) (by simp [ev])
/-- `⊢ ⊥` is not derivable without axioms -/
theorem noBot (h : DerivableIn (ND E0) ((∅ : Ctx Unit), (⊥ : PU))) : False :=
  sound' (fun _ => False) h (by simp) (by simp)
/-- `⊢ a` is not derivable without axioms -/
theorem noAt (h : DerivableIn (ND E0) ((∅ : Ctx Unit), aU)) : False :=
  sound' (fun _ => False) h (by simp) (by simp)
theorem derTop : DerivableIn (ND E0) ((∅ : Ctx Unit), (⊤ : PU)) := derivableIn_top
theorem derAss (A : PU) : DerivableIn (ND E0) (({A} : Ctx Unit), A) :=
  ⟨Derivation.ass (by simp)⟩
theorem derAx : DerivableIn (ND ({aU} : Set PU)) ((∅ : Ctx Unit), aU) :=
  ⟨Derivation.ax (by simp)⟩

-- `Cslib.Logic.PL.NaturalDeduction.Equiv.mp` idx 5: necessary (A = ⊤, B = ⊥)
theorem ndmp5 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.Equiv.mp 5 := fun h =>
  noTopBot (@h Unit _ ∅ ⊤ ⊥)
-- `Cslib.Logic.PL.NaturalDeduction.Equiv.mpr` idx 5: necessary (A = ⊥, B = ⊤)
theorem ndmpr5 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.Equiv.mpr 5 := fun h =>
  noTopBot (@h Unit _ ∅ ⊥ ⊤)
-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken` idx 8: necessary (T = {a}, T' = ∅, ⊢ a)
theorem ndw7 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken 8 := fun h =>
  noAt (@h Unit _ {.atom ()} ∅ ∅ ∅ aU derAx (subset_refl _))
-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken` idx 9: necessary (Γ = {a}, Δ = ∅)
theorem ndw8 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken 9 := fun h =>
  noAt (@h Unit _ ∅ ∅ {.atom ()} ∅ aU (derAss _) (subset_refl _))
-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken` idx 7: necessary (⊢ ⊥)
theorem ndw9 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken 7 := fun h =>
  noBot (@h Unit _ ∅ ∅ ∅ ∅ ⊥ (subset_refl _) (subset_refl _))
-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken_ax` idx 7: necessary (T = {a}, T' = ∅)
theorem ndwt6 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken_ax 7 := fun h =>
  noAt (@h Unit _ {.atom ()} ∅ ∅ aU derAx)
-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken_ax` idx 6: necessary (⊢ ⊥)
theorem ndwt7 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken_ax 6 := fun h =>
  noBot (@h Unit _ ∅ ∅ ∅ ⊥ (subset_refl _))
-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken_ctx` idx 7: necessary (Γ = {a}, Δ = ∅)
theorem ndwc6 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken_ctx 7 := fun h =>
  noAt (@h Unit _ ∅ {.atom ()} ∅ aU (derAss _))
-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken_ctx` idx 6: necessary (⊢ ⊥)
theorem ndwc7 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_weaken_ctx 6 := fun h =>
  noBot (@h Unit _ ∅ ∅ ∅ ⊥ (subset_refl _))
-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_cut` idx 7: necessary (A = B = ⊥, Γ = Δ = ∅)
theorem ndcut7 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_cut 7 := fun h =>
  noBot (by simpa using @h Unit _ ∅ ∅ ∅ ⊥ ⊥ (by simpa using derAss ⊥))
-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_cut` idx 8: necessary (A = ⊤, B = ⊥)
theorem ndcut8 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_cut 8 := fun h =>
  noBot (by simpa using @h Unit _ ∅ ∅ ∅ ⊤ ⊥ derTop)
-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_cut_away` idx 6: necessary (Γ' = {⊥}, B = ⊥)
theorem ndca6 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_cut_away 6 := fun h =>
  noBot (@h Unit _ ∅ ∅ {⊥} ⊥ (by simpa using derAss ⊥))
-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_cut_away` idx 7: necessary (Γ = Γ' = ∅, B = ⊥)
theorem ndca7 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_cut_away 7 := fun h =>
  noBot (@h Unit _ ∅ ∅ ∅ ⊥ (by simp))
-- `Cslib.Logic.PL.NaturalDeduction.derivableIn_subst_atom` idx 8: necessary (B = ⊥, f = atom)
theorem ndsa8 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.derivableIn_subst_atom 8 := fun h =>
  (sound' (fun _ => False) (@h Unit Unit _ _ ∅ .atom ∅ ⊥) (by simp) (by simp) : False)
-- `Cslib.Logic.PL.NaturalDeduction.equiv_top_of_derivableIn` idx 4: necessary (A = ⊥)
theorem ndet4 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.equiv_top_of_derivableIn 4 := fun h =>
  noTopBot (@h Unit _ ∅ ⊥).mpr
-- `Cslib.Logic.PL.NaturalDeduction.Equiv.symm` idx 5: necessary (A = ⊥, B = ⊤)
theorem ndsy5 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.Equiv.symm 5 := fun h =>
  noTopBot (@h Unit _ ∅ ⊥ ⊤).mp
-- `Cslib.Logic.PL.NaturalDeduction.Equiv.trans` idx 6: necessary (A = ⊥, B = C = ⊤)
theorem ndtr6 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.Equiv.trans 6 := fun h =>
  noTopBot (@h Unit _ ∅ ⊥ ⊤ ⊤ (NaturalDeduction.Equiv.refl _)).mpr
-- `Cslib.Logic.PL.NaturalDeduction.Equiv.trans` idx 7: necessary (A = B = ⊤, C = ⊥)
theorem ndtr7 : ¬ drop0% Cslib.Logic.PL.NaturalDeduction.Equiv.trans 7 := fun h =>
  noTopBot (@h Unit _ ∅ ⊤ ⊤ ⊥ (NaturalDeduction.Equiv.refl _)).mp
end ND

section Modal
open Cslib.Logic.Modal

-- `Cslib.Logic.Modal.Satisfies.unimodalOfPredicates_preserves_reflTransGen` idx 6: necessary (r total on Bool, P = (· = true))
theorem mpr6 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodalOfPredicates_preserves_reflTransGen 6 :=
  fun h => by
  have := (Satisfies.unimodalOfPredicates_preserves_iff (τ := τU) _).mp
    (fun a => @h τU _ _ Bool (fun _ _ => True) (· = true) a)
  exact absurd (this (a := true) (b := false) (.single trivial) rfl) (by decide)

-- `Relation.instSerialOfSMulOfNonempty` idx 3: necessary (M = Empty)
theorem ser3 : ¬ drop0% Relation.instSerialOfSMulOfNonempty 3 := fun h => by
  obtain ⟨y, m, _⟩ := (@h Empty Unit ⟨fun e _ => e.elim⟩).serial ()
  exact m.elim

/-- Bool acting on ℕ by `b • n = 2n + b`: from 0 the two successors 0, 1 have disjoint futures -/
@[instance_reducible] def smB : SMul Bool ℕ := ⟨fun b n => 2 * n + b.toNat⟩

-- `Relation.ofSMul_diamond` idx 3: necessary (Bool acts on ℕ by b • n = 2n + b; no join of 0 and 1)
theorem dia3 : ¬ drop0% Relation.ofSMul_diamond 3 := fun h => by
  obtain ⟨d, ⟨m, hm⟩, ⟨n, hn⟩⟩ := @h Bool ℕ smB 0 0 1 ⟨false, rfl⟩ ⟨true, rfl⟩
  have e1 : 2 * 0 + m.toNat = d := hm
  have e2 : 2 * 1 + n.toNat = d := hn
  cases m <;> cases n <;> simp at e1 e2 <;> omega

/-- a SetLike wrapper of `Set α` (no closure under any action) -/
def SL (α : Type) := Set α
instance (α : Type) : SetLike (SL α) α := ⟨fun s => (s : Set α), fun _ _ h => h⟩
def sT : SL Bool := ({true} : Set Bool)
def s0 : SL Bool := (∅ : Set Bool)
theorem nsT : false ∉ sT := fun h => by
  change false ∈ ({true} : Set Bool) at h; simp at h
theorem ns0 (b : Bool) : b ∉ s0 := fun h => (show b ∈ (∅ : Set Bool) from h)
/-- the set `{true}` as a container, closed under the empty / trivial actions -/
@[instance_reducible] def smN : SMul Unit Bool := ⟨fun _ b => !b⟩
@[instance_reducible] def smT : SMul Unit Bool := ⟨fun _ b => b⟩
@[instance_reducible] def smE : SMul Empty Bool := ⟨fun e _ => e.elim⟩
theorem smmT : @SMulMemClass (SL Bool) Unit Bool smT _ := @SMulMemClass.mk _ _ _ smT _ fun {_} _ {_} h => h
theorem smmE : @SMulMemClass (SL Bool) Empty Bool smE _ := @SMulMemClass.mk _ _ _ smE _ fun e _ => e.elim

-- `Relation.ofSMul_preserves_mem` idx 5: necessary (Unit acts on Bool by negation, s = {true})
theorem pm5 : ¬ drop0% Relation.ofSMul_preserves_mem 5 := fun h => by
  have := @h Unit Bool (SL Bool) smN _ sT (a := true) (b := false) ⟨(), rfl⟩ rfl
  exact nsT this
-- `Relation.ofSMul_mem_of_mem` idx 5: necessary (Unit acts on Bool by negation, p = {true})
theorem mm5 : ¬ drop0% Relation.ofSMul_mem_of_mem 5 := fun h => by
  have := @h Unit Bool (SL Bool) smN _ sT true false ⟨(), rfl⟩ rfl
  exact nsT this
-- `Relation.ofSMul_mem_of_mem` idx 9: necessary (empty action, a = true, b = false, p = {true})
theorem mm9 : ¬ drop0% Relation.ofSMul_mem_of_mem 9 := fun h => by
  have := @h Empty Bool (SL Bool) smE _ smmE sT true false rfl
  exact nsT this
-- `Relation.ofSMul_mem_of_mem` idx 10: necessary (trivial action, p = ∅)
theorem mm10 : ¬ drop0% Relation.ofSMul_mem_of_mem 10 := fun h => by
  have := @h Unit Bool (SL Bool) smT _ smmT s0 true true ⟨(), rfl⟩
  exact ns0 _ this

/-- a SetLike wrapper of `Set ℕ` (no closure under any action) -/
abbrev SS := SL ℕ

-- `Cslib.Logic.Modal.Proposition.ofSMul_diamond_and_equiv` idx 9: necessary (ℕ acting on ℕ by multiplication, p = {2}, q = {3}, world 1)
theorem dae9 : ¬ drop0% Cslib.Logic.Modal.Proposition.ofSMul_diamond_and_equiv 9 := fun h => by
  have := Proposition.equiv_iff_forall_iff.mp
    (@h τU _ _ ℕ ℕ SS _ _ _ (({2} : Set ℕ) : SS) (({3} : Set ℕ) : SS)) 1
  simp only [Satisfies.diamond_iff_exists, Satisfies.and_iff_and,
    Frame.ofRelation_rel_iff] at this
  obtain ⟨w, -, h2, h3⟩ := this.mpr ⟨⟨2, ⟨2, rfl⟩, (show (2:ℕ) ∈ ({2} : Set ℕ) from rfl)⟩,
    ⟨3, ⟨3, rfl⟩, (show (3:ℕ) ∈ ({3} : Set ℕ) from rfl)⟩⟩
  change w ∈ ({2} : Set ℕ) at h2
  change w ∈ ({3} : Set ℕ) at h3
  simp at h2 h3; omega
end Modal

end W3c5.ND

namespace W3c5.PV
open Cslib MeasureTheory MachineLearning.PACLearning
open scoped NNReal ENNReal

section PMFrows
open Cslib.Probability.PMF

theorem pureNe : PMF.pure true ≠ PMF.pure false := fun h => by
  have := congrArg (fun p : PMF Bool => p true) h; simp at this

universe u v w
-- `Cslib.Probability.PMF.uniformOfFintype_map_equiv` idx 4: removable (Nonempty α from Nonempty γ via e.symm)
theorem ume4 : indep% Cslib.Probability.PMF.uniformOfFintype_map_equiv 4 := by
  intro α γ _ _ _ e; exact ⟨e.symm (Classical.arbitrary γ)⟩
-- `Cslib.Probability.PMF.uniformOfFintype_map_equiv` idx 5: removable (Nonempty γ from Nonempty α via e)
theorem ume5 : indep% Cslib.Probability.PMF.uniformOfFintype_map_equiv 5 := by
  intro α γ _ _ _ e; exact ⟨e (Classical.arbitrary α)⟩
-- `Cslib.Probability.PMF.uniformOfFintype_prod` idx 3: necessary (α = Empty)
theorem up3 : ¬ indep0% Cslib.Probability.PMF.uniformOfFintype_prod 3 := fun h => by
  obtain ⟨e⟩ := (@h Empty Unit _ _ ⟨()⟩ : Nonempty Empty); exact e.elim
-- `Cslib.Probability.PMF.uniformOfFintype_prod` idx 5: necessary (β = Empty)
theorem up5 : ¬ indep0% Cslib.Probability.PMF.uniformOfFintype_prod 5 := fun h => by
  obtain ⟨e⟩ := (@h Unit Empty _ ⟨()⟩ _ : Nonempty Empty); exact e.elim
-- `Cslib.Probability.PMF.posteriorDist_apply` idx 5: necessary (p = pure true, f = pure, b = false)
theorem pda5 : ¬ indep0% Cslib.Probability.PMF.posteriorDist_apply 5 := fun h => by
  have := @h Bool Bool (PMF.pure true) PMF.pure false true
  simp at this
-- `Cslib.Probability.PMF.posteriorDist_eq_prior_of_outputIndist` idx 6: necessary (f constant pure true, b = false)
theorem pdo6 : ¬ indep0% Cslib.Probability.PMF.posteriorDist_eq_prior_of_outputIndist 6 := fun h => by
  have := @h Bool Bool (PMF.pure true) (fun _ => PMF.pure true) (fun _ _ => rfl) false
  simp at this
-- `Cslib.Probability.PMF.posteriorDist_eq_prior_of_outputIndist` idx 4: necessary (uniform prior on Bool, identity channel, b = true)
theorem pdo4 : ¬ drop0% Cslib.Probability.PMF.posteriorDist_eq_prior_of_outputIndist 4 := fun h => by
  have hb : true ∈ ((uniformOfFintype Bool).bind PMF.pure).support := by simp
  have := congrArg (fun p : PMF Bool => p false) (@h Bool Bool (uniformOfFintype Bool) PMF.pure true hb)
  simp [posteriorDist_apply, PMF.bind_apply, tsum_fintype] at this
  exact absurd this.symm (by simp)
-- `Cslib.Probability.PMF.dist_eq_one_of_disjoint_support` idx 4: necessary (p = q)
theorem dd4 : ¬ drop0% Cslib.Probability.PMF.dist_eq_one_of_disjoint_support 4 := fun h => by
  have := @h Unit _ (PMF.pure ()) (PMF.pure ())
  simp at this
-- `Cslib.Probability.PMF.StatisticallyClose.symm` idx 5: necessary (ε = 0, p ≠ q)
theorem scs5 : ¬ drop0% Cslib.Probability.PMF.StatisticallyClose.symm 5 := fun h =>
  pureNe ((statisticallyClose_zero_iff _ _).mp (@h Bool _ (PMF.pure false) (PMF.pure true) 0))
-- `Cslib.Probability.PMF.StatisticallyClose.trans` idx 8: necessary (ε = δ = 0, p = q = pure true, r = pure false)
theorem sct8 : ¬ drop0% Cslib.Probability.PMF.StatisticallyClose.trans 8 := fun h => by
  have := @h Bool _ (PMF.pure true) (PMF.pure true) (PMF.pure false) 0 0 (StatisticallyClose.refl _)
  rw [zero_add, statisticallyClose_zero_iff] at this
  exact pureNe this
-- `Cslib.Probability.PMF.StatisticallyClose.bind` idx 7: necessary (ε = 0, kernel = pure)
theorem scb7 : ¬ drop0% Cslib.Probability.PMF.StatisticallyClose.bind 7 := fun h => by
  have := (statisticallyClose_zero_iff _ _).mp (@h Bool Bool _ _ (PMF.pure true) (PMF.pure false) 0 PMF.pure)
  simp only [PMF.pure_bind] at this
  exact pureNe this
-- `Cslib.Probability.PMF.StatisticallyClose.map` idx 7: necessary (ε = 0, f = id)
theorem scm7 : ¬ drop0% Cslib.Probability.PMF.StatisticallyClose.map 7 := fun h => by
  have := (statisticallyClose_zero_iff _ _).mp (@h Bool Bool _ _ (PMF.pure true) (PMF.pure false) 0 id)
  simp only [PMF.pure_map, id] at this
  exact pureNe this
end PMFrows

section VS
-- `Cslib.MachineLearning.PACLearning.SetShatters.subset` idx 4: necessary (C = ∅)
theorem ss4 : ¬ drop0% Cslib.MachineLearning.PACLearning.SetShatters.subset 4 := fun h => by
  obtain ⟨c, hc, _⟩ := @h Unit ∅ ∅ ∅ (subset_refl _) ∅ (subset_refl _)
  exact hc
-- `Cslib.MachineLearning.PACLearning.SetShatters.subset` idx 5: necessary (C = {const false}, W = ∅, V = univ)
theorem ss5 : ¬ drop0% Cslib.MachineLearning.PACLearning.SetShatters.subset 5 := fun h => by
  have hW : SetShatters ({fun _ => false} : ConceptClass Unit Bool) ∅ := fun W' hW' =>
    ⟨_, rfl, by simp [Set.subset_empty_iff.mp hW']⟩
  obtain ⟨c, hc, hcW⟩ := @h Unit _ ∅ Set.univ hW Set.univ (subset_refl _)
  rw [Set.mem_singleton_iff.mp hc] at hcW
  simp at hcW
  exact Set.empty_ne_univ hcW
-- `Cslib.MachineLearning.PACLearning.SetShatters.superset` idx 4: necessary (C = C' = ∅, W = ∅)
theorem ssup4 : ¬ drop0% Cslib.MachineLearning.PACLearning.SetShatters.superset 4 := fun h => by
  obtain ⟨c, hc, _⟩ := @h Unit ∅ ∅ ∅ (subset_refl _) ∅ (subset_refl _)
  exact hc
-- `Finset.Shatters.toSetShatters` idx 3: necessary (𝒜 = ∅, s = ∅)
theorem fst3 : ¬ drop0% Finset.Shatters.toSetShatters 3 := fun h => by
  obtain ⟨c, ⟨t, ht, _⟩, _⟩ := @h Unit ∅ ∅ ∅ (by simp)
  simp at ht
-- `Cslib.MachineLearning.PACLearning.versionSpace_antitone` idx 4: necessary (m = 1, n = 0)
theorem vsa4 : ¬ indep0% Cslib.MachineLearning.PACLearning.versionSpace_antitone 4 := fun h =>
  absurd (@h Unit Unit 1 0 ∅ Fin.elim0) (by omega)
-- `Cslib.MachineLearning.PACLearning.versionSpace_mono_C` idx 5: necessary (C = univ, C' = ∅)
theorem vsm5 : ¬ drop0% Cslib.MachineLearning.PACLearning.versionSpace_mono_C 5 := fun h =>
  (@h Unit Unit 0 Set.univ ∅ Fin.elim0 id ⟨trivial, fun i => i.elim0⟩).1
-- `Cslib.MachineLearning.PACLearning.IsConsistent.output_mem_conceptClass` idx 5: necessary (C = {const true}, A outputs const false)
theorem omc5 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsConsistent.output_mem_conceptClass 5 := fun h => by
  have := @h Unit Bool 0 (fun _ _ => false) {fun _ => true} Fin.elim0 ⟨_, rfl, fun i => i.elim0⟩
  have := congrFun (Set.mem_singleton_iff.mp this) (); simp at this
-- `Cslib.MachineLearning.PACLearning.IsConsistent.output_mem_conceptClass` idx 7: necessary (C = ∅)
theorem omc7 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsConsistent.output_mem_conceptClass 7 := fun h =>
  @h Unit Bool 0 (fun _ _ => false) ∅ (fun _ ⟨_, hc, _⟩ => hc.elim) Fin.elim0
def S1 : LabeledSample Unit Bool 1 := fun _ => ((), true)
theorem realS1 : Realizable (Set.univ : ConceptClass Unit Bool) S1 := ⟨fun _ => true, trivial, fun _ => rfl⟩
theorem consE (m : ℕ) (A : Learner Unit Bool m) : IsConsistent A ∅ := fun _ ⟨_, hc, _⟩ => hc.elim
-- `Cslib.MachineLearning.PACLearning.IsConsistent.output_agrees` idx 5: necessary (C = univ, A = const false, S = ((), true))
theorem oa5 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsConsistent.output_agrees 5 := fun h => by
  have := @h Unit Bool 1 (fun _ _ => false) Set.univ S1 realS1 0; simp [S1] at this
-- `Cslib.MachineLearning.PACLearning.IsConsistent.output_agrees` idx 7: necessary (C = ∅)
theorem oa7 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsConsistent.output_agrees 7 := fun h => by
  have := @h Unit Bool 1 (fun _ _ => false) ∅ (consE _ _) S1 0; simp [S1] at this
-- `Cslib.MachineLearning.PACLearning.IsConsistent.empiricalMiscount_eq_zero` idx 6: necessary (C = univ, A = const false, S = ((), true))
theorem emz6 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsConsistent.empiricalMiscount_eq_zero 6 := fun h => by
  have := @h Unit Bool _ 1 (fun _ _ => false) Set.univ S1 realS1; simp [empiricalMiscount, S1] at this
-- `Cslib.MachineLearning.PACLearning.IsConsistent.empiricalMiscount_eq_zero` idx 8: necessary (C = ∅)
theorem emz8 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsConsistent.empiricalMiscount_eq_zero 8 := fun h => by
  have := @h Unit Bool _ 1 (fun _ _ => false) ∅ (consE _ _) S1; simp [empiricalMiscount, S1] at this
theorem eeS1 : empiricalError (fun _ => false : Unit → Bool) S1 ≠ 0 := by
  simp [empiricalError, empiricalMeasure, error, S1]
-- `Cslib.MachineLearning.PACLearning.IsConsistent.empiricalError_eq_zero` idx 9: necessary (C = univ, A = const false, S = ((), true))
theorem eez9 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsConsistent.empiricalError_eq_zero 9 := fun h =>
  eeS1 (@h Unit Bool _ _ _ _ 1 (fun _ _ => false) Set.univ S1 realS1)
-- `Cslib.MachineLearning.PACLearning.IsConsistent.empiricalError_eq_zero` idx 11: necessary (C = ∅)
theorem eez11 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsConsistent.empiricalError_eq_zero 11 := fun h =>
  eeS1 (@h Unit Bool _ _ _ _ 1 (fun _ _ => false) ∅ (consE _ _) S1)
-- `Cslib.MachineLearning.PACLearning.mem_versionSpace_of_realizable` idx 5: necessary (C = ∅)
theorem mvr5 : ¬ drop0% Cslib.MachineLearning.PACLearning.mem_versionSpace_of_realizable 5 := fun h =>
  (@h Unit Unit 0 ∅ id Fin.elim0 (fun i => i.elim0)).1
-- `Cslib.MachineLearning.PACLearning.mem_versionSpace_of_realizable` idx 7: necessary (c = const false, S = ((), true))
theorem mvr7 : ¬ drop0% Cslib.MachineLearning.PACLearning.mem_versionSpace_of_realizable 7 := fun h => by
  have := (@h Unit Bool 1 Set.univ (fun _ => false) trivial S1).2 0; simp [S1] at this
-- `Cslib.MachineLearning.PACLearning.Realizable.versionSpace_nonempty` idx 5: necessary (C = ∅)
theorem rvn5 : ¬ drop0% Cslib.MachineLearning.PACLearning.Realizable.versionSpace_nonempty 5 := fun h => by
  obtain ⟨c, hc, _⟩ := @h Unit Unit 0 ∅ Fin.elim0; exact hc
end VS

section SC
def L0 : LearnerModel Unit Bool := fun _ _ _ _ _ => False
def L1 : LearnerModel Unit Bool := fun m _ _ _ _ => m = 1
def Lz : LearnerModel Unit Bool := fun m _ _ _ _ => m = 0
noncomputable def eh : Set.Ioo (0 : ℝ≥0) 1 := ⟨1/2, by norm_num, by norm_num⟩
theorem scL1 : sampleComplexity L1 Set.univ eh eh Set.univ = 1 := by
  simp [sampleComplexity, L1]
theorem scL0 : sampleComplexity L0 Set.univ eh eh Set.univ = 0 := by
  simp [sampleComplexity, L0]
theorem scLz : sampleComplexity Lz Set.univ eh eh Set.univ = 0 := by
  simp [sampleComplexity, Lz]
-- `Cslib.MachineLearning.PACLearning.sampleComplexity_le_of_forall` idx 14: necessary (L₁ = (m = 0), L₂ = (m = 1))
theorem slf14 : ¬ drop0% Cslib.MachineLearning.PACLearning.sampleComplexity_le_of_forall 14 := fun h => by
  have := @h Unit Bool _ _ Lz L1 eh eh eh eh Set.univ Set.univ Set.univ Set.univ ⟨0, rfl⟩
  rw [scL1, scLz] at this; omega
-- `Cslib.MachineLearning.PACLearning.sampleComplexity_le_of_forall` idx 15: necessary (L₁ empty, L₂ = (m = 1))
theorem slf15 : ¬ drop0% Cslib.MachineLearning.PACLearning.sampleComplexity_le_of_forall 15 := fun h => by
  have := @h Unit Bool _ _ L0 L1 eh eh eh eh Set.univ Set.univ Set.univ Set.univ (fun h => h.elim)
  rw [scL1, scL0] at this; omega
end SC

section Rem
universe u₁ u₂
-- `Cslib.MachineLearning.PACLearning.hypothesisError_eq_add` idx 5: removable (split along the measurable c: μ s = μ (s ∩ c) + μ (s \ c))
theorem hea5 : drop% Cslib.MachineLearning.PACLearning.hypothesisError_eq_add 5 := by
  intro α _ P h c hc
  have := measure_inter_add_sdiff (μ := P) (symmDiff h c) hc
  have e1 : symmDiff h c ∩ c = c \ h := by ext x; by_cases hx : x ∈ h <;> by_cases hxc : x ∈ c <;> simp [symmDiff_def, hx, hxc]
  have e2 : symmDiff h c \ c = h \ c := by ext x; by_cases hx : x ∈ h <;> by_cases hxc : x ∈ c <;> simp [symmDiff_def, hx, hxc]
  rw [e1, e2] at this
  simp only [hypothesisError, falsePositiveError, falseNegativeError, ← this, add_comm]
-- `Cslib.MachineLearning.PACLearning.hypothesisError_eq_add` idx 6: removable (split along the measurable h: μ s = μ (s ∩ h) + μ (s \ h))
theorem hea6 : drop% Cslib.MachineLearning.PACLearning.hypothesisError_eq_add 6 := by
  intro α _ P h c hh
  have := measure_inter_add_sdiff (μ := P) (symmDiff h c) hh
  have e1 : symmDiff h c ∩ h = h \ c := by ext x; by_cases hx : x ∈ h <;> by_cases hxc : x ∈ c <;> simp [symmDiff_def, hx, hxc]
  have e2 : symmDiff h c \ h = c \ h := by ext x; by_cases hx : x ∈ h <;> by_cases hxc : x ∈ c <;> simp [symmDiff_def, hx, hxc]
  rw [e1, e2] at this
  simp only [hypothesisError, falsePositiveError, falseNegativeError, ← this]
-- `Cslib.MachineLearning.PACLearning.empiricalError_eq_div` idx 8: removable (m = 0: both sides are 0, as 0 / 0 = 0 in ℝ≥0∞)
theorem eed8 : drop% Cslib.MachineLearning.PACLearning.empiricalError_eq_div 8 := by
  intro α β _ _ _ _ _ m h S
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [empiricalError, empiricalMeasure, error, empiricalMiscount]
  · exact empiricalError_eq_div hm h S

theorem mapOne {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {c : α → β}
    (hcm : Measurable c) (P : Measure α) [IsProbabilityMeasure P] (G : Set (α × β))
    (hG : ∀ x, (x, c x) ∈ G) : (P.map (fun x => (x, c x))) G = 1 := by
  have hφ : Measurable (fun x : α => (x, c x)) := measurable_id.prodMk hcm
  refine le_antisymm prob_le_one ?_
  rw [← measure_univ (μ := P)]
  refine le_trans (le_of_eq ?_) (Measure.le_map_apply hφ.aemeasurable _)
  congr 1; ext x; simp [hG]

-- `_private.Cslib.MachineLearning.PACLearning.VersionSpace.0.Cslib.MachineLearning.PACLearning.map_graph_eq_one` idx 8: removable (le_map_apply: map μ G ≥ μ (preimage G) = 1 for any set G)
theorem mge8 : drop% _private.Cslib.MachineLearning.PACLearning.VersionSpace.«0».Cslib.MachineLearning.PACLearning.map_graph_eq_one 8 := by
  intro α β _ _ c hcm P _
  exact mapOne hcm P _ (fun x => rfl)
-- `_private.Cslib.MachineLearning.PACLearning.VersionSpace.0.Cslib.MachineLearning.PACLearning.pi_map_graph_eq_one` idx 8: removable (pi_pi holds for arbitrary sets; each factor is 1 by le_map_apply)
theorem pmge8 : drop% _private.Cslib.MachineLearning.PACLearning.VersionSpace.«0».Cslib.MachineLearning.PACLearning.pi_map_graph_eq_one 8 := by
  intro α β _ _ c hcm P _ m
  have hφ : Measurable (fun x : α => (x, c x)) := measurable_id.prodMk hcm
  rw [Measure.pi_pi]
  simp only [Finset.prod_const]
  rw [mapOne hcm P {p : α × β | p.2 = c p.1} (fun x => by simp)]
  simp
-- `_private.Cslib.MachineLearning.PACLearning.VersionSpace.0.Cslib.MachineLearning.PACLearning.map_graph_eq_one` idx 7: necessary (P = 0)
theorem mge7 : ¬ drop0% _private.Cslib.MachineLearning.PACLearning.VersionSpace.«0».Cslib.MachineLearning.PACLearning.map_graph_eq_one 7 := fun h => by
  have := @h Unit Unit _ _ id measurable_id 0 (Set.toFinite _).measurableSet
  simp at this
-- `_private.Cslib.MachineLearning.PACLearning.VersionSpace.0.Cslib.MachineLearning.PACLearning.pi_map_graph_eq_one` idx 7: necessary (P = 0, m = 1)
theorem pmge7 : ¬ drop0% _private.Cslib.MachineLearning.PACLearning.VersionSpace.«0».Cslib.MachineLearning.PACLearning.pi_map_graph_eq_one 7 := fun h => by
  have := @h Unit Unit _ _ id measurable_id 0 (Set.toFinite _).measurableSet 1
  rw [Measure.pi_pi] at this
  simp at this
-- `Cslib.MachineLearning.PACLearning.ae_mem_versionSpace_of_realizable` idx 6: necessary (C = ∅, m = 0)
theorem aem6 : ¬ drop0% Cslib.MachineLearning.PACLearning.ae_mem_versionSpace_of_realizable 6 := fun h => by
  have := @h Unit Unit _ _ ∅ id measurable_id (Set.toFinite _).measurableSet (Measure.dirac ()) _ 0
  rw [ae_iff] at this
  have e : {S : LabeledSample Unit Unit 0 | ¬ id ∈ VersionSpace ∅ S} = Set.univ := by
    ext S; simp [VersionSpace]
  rw [e, Measure.pi_empty_univ] at this
  exact one_ne_zero this

end Rem

end W3c5.PV

namespace W3c5.PA
open Cslib MeasureTheory MachineLearning.PACLearning
open scoped NNReal ENNReal

-- Probe2 part G model (Unit × Bool; Dt = dirac (·,true), Df = ¼ true + ¾ false)
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


/-- every family is learnable for the empty concept class (optimal error ⊤) -/
theorem pacC0 (m : ℕ) (ε δ : Set.Ioo (0 : ℝ≥0) 1) (𝒟 : Set (Measure (Unit × Bool))) :
    IsPACLearnerFor m ε δ (∅ : ConceptClass Unit Bool) 𝒟 :=
  ⟨fun _ _ => true, fun D _ _ => by simp [optimalError]⟩
/-- the empty family is learnable -/
theorem pacE (m : ℕ) (ε δ : Set.Ioo (0 : ℝ≥0) 1) (C : ConceptClass Unit Bool) :
    IsPACLearnerFor m ε δ C ∅ := ⟨fun _ _ => true, fun D _ hD => hD.elim⟩
/-- {Dt} is learnable with 0 samples (output true) -/
theorem pacDt (ε δ : Set.Ioo (0 : ℝ≥0) 1) : IsPACLearnerFor 0 ε δ Set.univ {Dt} := by
  refine ⟨fun _ _ => true, fun D _ hD => ?_⟩
  rw [Set.mem_singleton_iff.mp hD]
  have : {S : LabeledSample Unit Bool 0 | optimalError Dt Set.univ + ↑ε.val < error Dt ((fun _ _ => true) S)} = ∅ := by
    ext S; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]; rw [errT, Dt_b]; exact zero_le
  rw [this]; simp
theorem scDt : sampleComplexity IsPACLearnerFor Set.univ e14 e12 {Dt} = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (pacDt _ _))
theorem scC0 : sampleComplexity IsPACLearnerFor (∅ : ConceptClass Unit Bool) e14 e12 DD = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (pacC0 0 _ _ _))
theorem scDD : sampleComplexity IsPACLearnerFor Set.univ e14 e12 DD ≠ 0 := by
  intro h0
  have hm := Nat.sInf_mem (⟨1, P1⟩ : Set.Nonempty {m | IsPACLearnerFor m e14 e12 Set.univ DD})
  unfold sampleComplexity at h0
  rw [h0] at hm
  exact P0' hm

-- `Cslib.MachineLearning.PACLearning.IsPACLearnerFor.antitone_family` idx 10: necessary (𝒟' = ∅, 𝒟 = DD, m = 0, ε = ¼, δ = ½)
theorem paf10 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnerFor.antitone_family 10 := fun h =>
  P0' (@h Unit Bool _ _ 0 e14 e12 Set.univ DD ∅ (pacE _ _ _ _))
-- `Cslib.MachineLearning.PACLearning.IsPACLearnerFor.antitone_family` idx 11: necessary (𝒟 = 𝒟' = DD, m = 0, ε = ¼, δ = ½)
theorem paf11 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnerFor.antitone_family 11 := fun h =>
  P0' (@h Unit Bool _ _ 0 e14 e12 Set.univ DD DD subset_rfl)
-- `Cslib.MachineLearning.PACLearning.IsPACLearnerFor.mono_δ` idx 11: necessary (DD, m = 0, ε = ¼, δ₁ = δ₂ = ½)
theorem pmd11 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnerFor.mono_δ 11 := fun h =>
  P0' (@h Unit Bool _ _ 0 e14 e12 e12 le_rfl Set.univ DD)
-- `Cslib.MachineLearning.PACLearning.IsPACLearnerFor.mono_ε` idx 11: necessary (DD, m = 0, ε₁ = ε₂ = ¼, δ = ½)
theorem pme11 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnerFor.mono_ε 11 := fun h =>
  P0' (@h Unit Bool _ _ 0 e12 e14 e14 le_rfl Set.univ DD)
-- `Cslib.MachineLearning.PACLearning.IsPACLearnerFor.antitone_C` idx 9: necessary (C' = ∅ (vacuous), C = univ, DD, m = 0)
theorem pac9 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnerFor.antitone_C 9 := fun h =>
  P0' (@h Unit Bool _ _ 0 e14 e12 Set.univ ∅ DD (pacC0 _ _ _ _))
-- `Cslib.MachineLearning.PACLearning.IsPACLearnerFor.antitone_C` idx 11: necessary (C = C' = univ, DD, m = 0)
theorem pac11 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnerFor.antitone_C 11 := fun h =>
  P0' (@h Unit Bool _ _ 0 e14 e12 Set.univ Set.univ subset_rfl DD)
-- `Cslib.MachineLearning.PACLearning.sampleComplexity_mono_family` idx 9: necessary (𝒟' = {Dt} needs 0 samples, 𝒟 = DD needs 1)
theorem smf9 : ¬ drop0% Cslib.MachineLearning.PACLearning.sampleComplexity_mono_family 9 := fun h => by
  have := @h Unit Bool _ _ e14 e12 Set.univ DD {Dt} ⟨0, pacDt _ _⟩
  rw [scDt] at this; exact scDD (Nat.eq_zero_of_le_zero this)
-- `Cslib.MachineLearning.PACLearning.sampleComplexity_mono_C` idx 8: necessary (C' = ∅ needs 0 samples, C = univ on DD needs 1)
theorem smc8 : ¬ drop0% Cslib.MachineLearning.PACLearning.sampleComplexity_mono_C 8 := fun h => by
  have := @h Unit Bool _ _ e14 e12 Set.univ ∅ DD ⟨0, pacC0 _ _ _ _⟩
  rw [scC0] at this; exact scDD (Nat.eq_zero_of_le_zero this)
-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_mono_family` idx 8: necessary (𝒟' = {Dt} learnable with 0 samples, 𝒟 = DD needs 1)
theorem lsmf8 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_mono_family 8 := fun h => by
  have := @h Unit Bool _ _ Set.univ DD {Dt} (fun ε δ => ⟨0, pacDt ε δ⟩) e14 e12
  rw [scDt] at this; exact scDD (Nat.eq_zero_of_le_zero this)
-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_mono_C` idx 8: necessary (C' = ∅ learnable with 0 samples, C = univ on DD needs 1)
theorem lsmc8 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_mono_C 8 := fun h => by
  have := @h Unit Bool _ _ Set.univ ∅ DD (fun ε δ => ⟨0, pacC0 0 ε δ DD⟩) e14 e12
  rw [scC0] at this; exact scDD (Nat.eq_zero_of_le_zero this)

end W3c5.PA

namespace W3c5.TS
open Cslib MeasureTheory MachineLearning.PACLearning
open scoped NNReal ENNReal

/-- Bool with the trivial σ-algebra (no measurable singletons) -/
def BB := Bool
def tB : BB := true
def fB : BB := false
instance : MeasurableSpace BB := ⊥
instance : DecidableEq BB := inferInstanceAs (DecidableEq Bool)

theorem bbMeas (s : Set BB) (hs : MeasurableSet s) : s = ∅ ∨ s = Set.univ :=
  MeasurableSpace.measurableSet_bot_iff.mp hs

/-- measurable sets of `BB × Bool` are saturated along the first coordinate -/
theorem mBT {t : Set (BB × Bool)} (ht : MeasurableSet t) {a a' : BB} {b : Bool}
    (h : (a, b) ∈ t) : (a', b) ∈ t := by
  have e : (Prod.instMeasurableSpace : MeasurableSpace (BB × Bool)) =
      MeasurableSpace.comap Prod.snd inferInstance := by
    change MeasurableSpace.comap (Prod.fst : BB × Bool → BB) (⊥ : MeasurableSpace BB) ⊔
      MeasurableSpace.comap (Prod.snd : BB × Bool → Bool) inferInstance = _
    rw [MeasurableSpace.comap_bot, bot_sup_eq]
  rw [e, MeasurableSpace.measurableSet_comap] at ht
  obtain ⟨s, -, rfl⟩ := ht; exact h
/-- measurable sets of `Bool × BB` are saturated along the second coordinate -/
theorem mTB {t : Set (Bool × BB)} (ht : MeasurableSet t) {a : Bool} {b b' : BB}
    (h : (a, b) ∈ t) : (a, b') ∈ t := by
  have e : (Prod.instMeasurableSpace : MeasurableSpace (Bool × BB)) =
      MeasurableSpace.comap Prod.fst inferInstance := by
    change MeasurableSpace.comap (Prod.fst : Bool × BB → Bool) inferInstance ⊔
      MeasurableSpace.comap (Prod.snd : Bool × BB → BB) (⊥ : MeasurableSpace BB) = _
    rw [MeasurableSpace.comap_bot, sup_bot_eq]
  rw [e, MeasurableSpace.measurableSet_comap] at ht
  obtain ⟨s, -, rfl⟩ := ht; exact h

/-- outer measure of a set whose only measurable superset is univ -/
theorem outer1 {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (B : Set X)
    (hB : ∀ t, MeasurableSet t → B ⊆ t → t = Set.univ) : μ B = 1 := by
  rw [← measure_toMeasurable, hB _ (measurableSet_toMeasurable _ _) (subset_toMeasurable _ _),
    measure_univ]

theorem offBT (t : Set (BB × Bool)) (ht : MeasurableSet t) (h : {p : BB × Bool | p.1 ≠ p.2} ⊆ t) :
    t = Set.univ := by
  have h1 : ((false : Bool), true) ∈ t := h (Bool.false_ne_true : (false : Bool) ≠ true)
  have h2 : ((true : Bool), false) ∈ t := h (fun e => Bool.noConfusion e : (true : Bool) ≠ false)
  ext ⟨a, b⟩; simp only [Set.mem_univ, iff_true]
  cases b
  · exact mBT ht h2
  · exact mBT ht h1
theorem offTB (t : Set (Bool × BB)) (ht : MeasurableSet t) (h : {p : Bool × BB | p.1 ≠ p.2} ⊆ t) :
    t = Set.univ := by
  have h1 : (false, (true : Bool)) ∈ t := h (Bool.false_ne_true : (false : Bool) ≠ true)
  have h2 : (true, (false : Bool)) ∈ t := h (fun e => Bool.noConfusion e : (true : Bool) ≠ false)
  ext ⟨a, b⟩; simp only [Set.mem_univ, iff_true]
  cases a
  · exact mTB ht h1
  · exact mTB ht h2

def SBT : LabeledSample BB Bool 1 := fun _ => ((true : Bool), true)
def STB : LabeledSample Bool BB 1 := fun _ => (true, (true : Bool))
def hBT : BB → Bool := fun x => x
def hTB : Bool → BB := fun x => x

theorem eeBT : empiricalError hBT SBT = 1 := by
  simp only [empiricalError, empiricalMeasure, error]
  simp only [one_ne_zero, ↓reduceDIte, Nat.cast_one, inv_one, one_smul, Finset.univ_unique,
    Finset.sum_singleton]
  exact outer1 _ _ (fun t ht h => offBT t ht h)
theorem eeTB : empiricalError hTB STB = 1 := by
  simp only [empiricalError, empiricalMeasure, error]
  simp only [one_ne_zero, ↓reduceDIte, Nat.cast_one, inv_one, one_smul, Finset.univ_unique,
    Finset.sum_singleton]
  exact outer1 _ _ (fun t ht h => offTB t ht h)

-- `Cslib.MachineLearning.PACLearning.mem_versionSpace_iff_empiricalError_zero` idx 4: necessary (α = Bool with trivial σ-algebra: the disagreement set has outer measure 1 under the Dirac at a correctly labeled point)
theorem mve4 : ¬ drop0% Cslib.MachineLearning.PACLearning.mem_versionSpace_iff_empiricalError_zero 4 := fun h => by
  have := (@h BB Bool _ _ _ 1 Set.univ SBT hBT).mp ⟨trivial, fun i => rfl⟩
  rw [eeBT] at this; exact one_ne_zero this.2
-- `Cslib.MachineLearning.PACLearning.mem_versionSpace_iff_empiricalError_zero` idx 5: necessary (β = Bool with trivial σ-algebra)
theorem mve5 : ¬ drop0% Cslib.MachineLearning.PACLearning.mem_versionSpace_iff_empiricalError_zero 5 := fun h => by
  have := (@h Bool BB _ _ _ 1 Set.univ STB hTB).mp ⟨trivial, fun i => rfl⟩
  rw [eeTB] at this; exact one_ne_zero this.2
-- `Cslib.MachineLearning.PACLearning.empiricalError_eq_div` idx 5: necessary (α = Bool with trivial σ-algebra; miscount 0, empirical error 1)
theorem eed5 : ¬ drop0% Cslib.MachineLearning.PACLearning.empiricalError_eq_div 5 := fun h => by
  have := @h BB Bool _ _ _ _ 1 one_pos hBT SBT
  have hm : empiricalMiscount hBT SBT = 0 := by decide
  rw [eeBT, hm] at this; simp at this
-- `Cslib.MachineLearning.PACLearning.empiricalError_eq_div` idx 6: necessary (β = Bool with trivial σ-algebra)
theorem eed6 : ¬ drop0% Cslib.MachineLearning.PACLearning.empiricalError_eq_div 6 := fun h => by
  have := @h Bool BB _ _ _ _ 1 one_pos hTB STB
  have hm : empiricalMiscount hTB STB = 0 := by decide
  rw [eeTB, hm] at this; simp at this
-- `Cslib.MachineLearning.PACLearning.IsConsistent.empiricalError_eq_zero` idx 4: necessary (α = Bool with trivial σ-algebra, C = {id}, A = const id)
theorem iez4 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsConsistent.empiricalError_eq_zero 4 := fun h => by
  have := @h BB Bool _ _ _ 1 (fun _ => hBT) {hBT}
    (fun S ⟨c, hc, hS⟩ => ⟨rfl, fun i => by rw [hS i, Set.mem_singleton_iff.mp hc]⟩) SBT
    ⟨hBT, rfl, fun _ => rfl⟩
  rw [eeBT] at this; exact one_ne_zero this
-- `Cslib.MachineLearning.PACLearning.IsConsistent.empiricalError_eq_zero` idx 5: necessary (β = Bool with trivial σ-algebra)
theorem iez5 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsConsistent.empiricalError_eq_zero 5 := fun h => by
  have := @h Bool BB _ _ _ 1 (fun _ => hTB) {hTB}
    (fun S ⟨c, hc, hS⟩ => ⟨rfl, fun i => by rw [hS i, Set.mem_singleton_iff.mp hc]⟩) STB
    ⟨hTB, rfl, fun _ => rfl⟩
  rw [eeTB] at this; exact one_ne_zero this

-- `Cslib.MachineLearning.PACLearning.ae_mem_versionSpace_of_realizable` idx 8: necessary (β = Bool with trivial σ-algebra, c = id: the off-graph set has outer measure 1)
theorem aem8 : ¬ drop0% Cslib.MachineLearning.PACLearning.ae_mem_versionSpace_of_realizable 8 := fun h => by
  have := @h Bool BB _ _ Set.univ hTB trivial (Measurable.of_discrete) (Measure.dirac true) _ 1
  rw [ae_iff] at this
  have e : {S : LabeledSample Bool BB 1 | ¬ hTB ∈ VersionSpace Set.univ S} =
      Set.univ.pi (fun _ => {p : Bool × BB | p.1 ≠ p.2}) := by
    ext S; simp [VersionSpace, hTB, Fin.forall_fin_one]; exact Iff.rfl
  rw [e, Measure.pi_pi] at this
  simp only [Finset.univ_unique, Finset.prod_singleton] at this
  rw [outer1 _ _ (fun t ht h => offTB t ht h)] at this
  exact one_ne_zero this

/-- a probability measure on `BB × Bool` cannot give mass 1 to both label classes -/
theorem twoOne (μ' : Measure (BB × Bool)) [IsProbabilityMeasure μ'] (h1 : μ' {p | p.2 = true} = 1)
    (h2 : μ' {p | p.2 = false} = 1) : False := by
  have hB : MeasurableSet {p : BB × Bool | p.2 = false} := measurable_snd (measurableSet_singleton false)
  have hU := measure_union (μ := μ') (s₁ := {p : BB × Bool | p.2 = true}) (s₂ := {p | p.2 = false})
    (Set.disjoint_left.mpr fun p h1 h2 => by simp_all) hB
  have hu : {p : BB × Bool | p.2 = true} ∪ {p | p.2 = false} = Set.univ := by
    ext ⟨a, b⟩; cases b <;> simp
  rw [hu, measure_univ, h1, h2] at hU
  norm_num at hU

-- `Cslib.MachineLearning.PACLearning.error_map_eq_hypothesisError` idx 6: necessary (α = Bool with trivial σ-algebra, P = dirac true, c = {true}, h = ∅ and h = univ: both right sides are 1, the left sides sum to 1)
theorem emh6 : ¬ drop0% Cslib.MachineLearning.PACLearning.error_map_eq_hypothesisError 6 := fun h => by
  have E1 := @h BB _ (Measure.dirac tB) ∅ {tB} MeasurableSet.empty
  have E2 := @h BB _ (Measure.dirac tB) Set.univ {tB} MeasurableSet.univ
  simp [error, hypothesisError] at E1 E2
  have r1 : (Measure.dirac tB : Measure BB) (symmDiff ∅ {tB}) = 1 :=
    Measure.dirac_apply_of_mem (Or.inr ⟨rfl, fun h => h⟩)
  have r2 : (Measure.dirac tB : Measure BB) (symmDiff Set.univ {tB}) = 1 := by
    refine outer1 _ _ fun t ht hsub => ?_
    rcases bbMeas t ht with rfl | rfl
    · exact absurd (hsub (show fB ∈ symmDiff (Set.univ : Set BB) {tB} from Or.inl ⟨trivial, fun h => Bool.noConfusion h⟩)) (fun h => h)
    · rfl
  exact twoOne _ (E1.trans r1) (E2.trans r2)

end W3c5.TS

namespace W3c5.RP
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


noncomputable def Dff : Measure (Unit × Bool) := Measure.dirac pb
instance : IsProbabilityMeasure Dff := by unfold Dff; infer_instance
theorem Dff_a : Dff {pa} = 0 := by simp [Dff, pa, pb]
theorem Dff_b : Dff {pb} = 1 := by simp [Dff]
noncomputable def D2 : Set (Measure (Unit × Bool)) := {Dt, Dff}

theorem q11 : (q1 : ℝ≥0∞) + q1 < 1 := by
  have : q1 + q1 < 1 := lt_of_lt_of_le q11lt (by rw [← q13]; exact le_add_self)
  exact_mod_cast this
theorem q3lt1 : q3 < 1 := by rw [← NNReal.coe_lt_coe]; simp [q3]; norm_num
noncomputable def e34 : Set.Ioo (0 : ℝ≥0) 1 := ⟨q3, by simp [q3], q3lt1⟩

theorem pi0in (D : Measure (Unit × Bool)) (s : Set (LabeledSample Unit Bool 0))
    (h : (Fin.elim0 : LabeledSample Unit Bool 0) ∈ s) : Measure.pi (fun _ : Fin 0 => D) s = 1 := by
  have : s = Set.univ := Set.eq_univ_of_forall (fun S => (funext (fun i => i.elim0) : S = Fin.elim0) ▸ h)
  rw [this, Measure.pi_empty_univ]
theorem pi0out (D : Measure (Unit × Bool)) (s : Set (LabeledSample Unit Bool 0))
    (h : (Fin.elim0 : LabeledSample Unit Bool 0) ∉ s) : Measure.pi (fun _ : Fin 0 => D) s = 0 := by
  have : s = ∅ := Set.eq_empty_of_forall_notMem (fun S hs => h ((funext (fun i => i.elim0) : S = Fin.elim0) ▸ hs))
  rw [this]; simp

theorem epsLt (ε : Set.Ioo (0 : ℝ≥0) 1) : ((ε.val : ℝ≥0) : ℝ≥0∞) < 1 := by exact_mod_cast ε.2.2
/-- failure probability of a 0-sample learner under Dt / Dff -/
theorem failT (ε : Set.Ioo (0 : ℝ≥0) 1) (A : Learner Unit Bool 0) :
    Measure.pi (fun _ : Fin 0 => Dt) {S | optimalError Dt Set.univ + ↑ε.val < error Dt (A S)} =
      if A Fin.elim0 () = true then 0 else 1 := by
  by_cases hA : A Fin.elim0 () = true
  · rw [if_pos hA]; apply pi0out
    simp only [Set.mem_ofPred_eq, errC, hA, optE, Dt_a, Dt_b]; simp
  · rw [if_neg hA]; apply pi0in
    simp only [Set.mem_ofPred_eq, errC, hA, optE, Dt_a, Dt_b]; simpa using epsLt ε
theorem failF (ε : Set.Ioo (0 : ℝ≥0) 1) (A : Learner Unit Bool 0) :
    Measure.pi (fun _ : Fin 0 => Dff) {S | optimalError Dff Set.univ + ↑ε.val < error Dff (A S)} =
      if A Fin.elim0 () = true then 1 else 0 := by
  by_cases hA : A Fin.elim0 () = true
  · rw [if_pos hA]; apply pi0in
    simp only [Set.mem_ofPred_eq, errC, hA, optE, Dff_a, Dff_b]; simpa using epsLt ε
  · rw [if_neg hA]; apply pi0out
    simp only [Set.mem_ofPred_eq, errC, hA, optE, Dff_a, Dff_b]; simp

/-- no randomized 0-sample learner for {Dt, Dff} with confidence ¼ -/
theorem notR0 (ε : Set.Ioo (0 : ℝ≥0) 1) : ¬ IsRPACLearnerFor.{0, 0, 0} 0 ε e14 Set.univ D2 := by
  rintro ⟨Ω, mΩ, Q, hQ, A, hA⟩
  obtain ⟨hmt, it⟩ := hA Dt (by simp [D2])
  obtain ⟨-, iF⟩ := hA Dff (by simp [D2])
  rw [lintegral_congr (fun ω => failT ε (A ω))] at it
  rw [lintegral_congr (fun ω => failF ε (A ω))] at iF
  have hm := hmt.congr (Filter.Eventually.of_forall (fun ω => failT ε (A ω)))
  have hsum := lintegral_add_left' hm (fun ω => if A ω Fin.elim0 () = true then (1 : ℝ≥0∞) else 0)
  rw [lintegral_congr (fun ω => show (if A ω Fin.elim0 () = true then (0 : ℝ≥0∞) else 1) +
      (if A ω Fin.elim0 () = true then 1 else 0) = 1 by split_ifs <;> simp)] at hsum
  simp only [lintegral_const, measure_univ, mul_one] at hsum
  have : (1 : ℝ≥0∞) ≤ q1 + q1 := hsum ▸ add_le_add it iF
  exact absurd q11 (not_lt.mpr this)

/-- a fair coin learner: confidence ½ ≤ ¾ with 0 samples -/
theorem coin : IsRPACLearnerFor.{0, 0, 0} 0 e12 e34 Set.univ D2 := by
  refine ⟨Bool, inferInstance, (Cslib.Probability.PMF.uniformOfFintype Bool).toMeasure, inferInstance,
    fun ω _ _ => ω, fun D _ hD => ⟨Measurable.of_discrete.aemeasurable, ?_⟩⟩
  rw [lintegral_fintype]
  simp only [Fintype.sum_bool, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
  have h2 : (2 : ℝ≥0∞)⁻¹ ≤ q3 := by
    rw [← ENNReal.coe_ofNat, ← ENNReal.coe_inv two_ne_zero]
    exact_mod_cast (show (2 : ℝ≥0)⁻¹ ≤ q3 by rw [← NNReal.coe_le_coe]; simp [q3]; norm_num)
  rcases hD with rfl | rfl
  · rw [failT, failT]; simpa [e34] using h2
  · rw [failF, failF]; simpa [e34] using h2

/-- with one sample the label is revealed: a perfect learner for {Dt, Dff} -/
theorem perf (ε δ : Set.Ioo (0 : ℝ≥0) 1) : IsPACLearnerFor 1 ε δ Set.univ D2 := by
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
      rw [errC, optE, Dff_a, Dff_b] at hS
      simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
      generalize S 0 = p at hS ⊢
      obtain ⟨u, v⟩ := p
      cases v
      · simp at hS
      · rfl
    · rw [piFin1, Dff_a]; exact zero_le
theorem rscPos : rsampleComplexity Set.univ e12 e14 D2 ≠ 0 := by
  intro h0
  have hm := Nat.sInf_mem (⟨1, (perf e12 e14).toIsRPACLearnerFor⟩ :
    Set.Nonempty {m | IsRPACLearnerFor.{0, 0, 0} m e12 e14 Set.univ D2})
  unfold rsampleComplexity sampleComplexity at h0
  rw [h0] at hm
  exact notR0 _ hm
theorem rscCoin : rsampleComplexity Set.univ e12 e34 D2 = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le coin)
theorem pacDt (ε δ : Set.Ioo (0 : ℝ≥0) 1) : IsPACLearnerFor 0 ε δ Set.univ {Dt} := by
  refine ⟨fun _ _ => true, fun D _ hD => ?_⟩
  rw [Set.mem_singleton_iff.mp hD]
  have : {S : LabeledSample Unit Bool 0 | optimalError Dt Set.univ + ↑ε.val < error Dt ((fun _ _ => true) S)} = ∅ := by
    ext S; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]; rw [errT, Dt_b]; exact zero_le
  rw [this]; simp
theorem rscDt : rsampleComplexity Set.univ e12 e14 {Dt} = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (pacDt _ _).toIsRPACLearnerFor)
theorem pacE (m : ℕ) (ε δ : Set.Ioo (0 : ℝ≥0) 1) (C : ConceptClass Unit Bool) :
    IsPACLearnerFor m ε δ C ∅ := ⟨fun _ _ => true, fun D _ hD => hD.elim⟩

-- `Cslib.MachineLearning.PACLearning.IsPACLearnerFor.toIsRPACLearnerFor` idx 9: necessary ({dirac ((),true), dirac ((),false)}, m = 0, δ = ¼: the two failure probabilities of any randomized learner sum to 1)
theorem tir9 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnerFor.toIsRPACLearnerFor 9 := fun h =>
  notR0 _ (@h Unit Bool _ _ 0 e12 e14 Set.univ D2)
-- `Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.antitone_family` idx 10: necessary (𝒟' = ∅, 𝒟 = {Dt, Dff}, m = 0, δ = ¼)
theorem raf10 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.antitone_family 10 := fun h =>
  notR0 _ (@h Unit Bool _ _ 0 e12 e14 Set.univ D2 ∅ (pacE _ _ _ _).toIsRPACLearnerFor)
-- `Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.antitone_family` idx 11: necessary (𝒟 = 𝒟' = {Dt, Dff}, m = 0, δ = ¼)
theorem raf11 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.antitone_family 11 := fun h =>
  notR0 _ (@h Unit Bool _ _ 0 e12 e14 Set.univ D2 D2 subset_rfl)
-- `Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.mono_δ` idx 8: necessary (fair coin learner has confidence ½ ≤ ¾ but no learner reaches ¼, m = 0)
theorem rmd8 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.mono_δ 8 := fun h =>
  notR0 _ (@h Unit Bool _ _ 0 e12 e34 e14 Set.univ D2 coin)
-- `Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.mono_δ` idx 11: necessary (δ₁ = δ₂ = ¼, m = 0)
theorem rmd11 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.mono_δ 11 := fun h =>
  notR0 _ (@h Unit Bool _ _ 0 e12 e14 e14 le_rfl Set.univ D2)
-- `Cslib.MachineLearning.PACLearning.rsampleComplexity_antitone_δ` idx 7: necessary (δ₁ = ¾ needs 0 samples (coin), δ₂ = ¼ needs 1)
theorem rsa7 : ¬ drop0% Cslib.MachineLearning.PACLearning.rsampleComplexity_antitone_δ 7 := fun h => by
  have := @h Unit Bool _ _ e12 e34 e14 Set.univ D2 ⟨0, coin⟩
  rw [rscCoin] at this; exact rscPos (Nat.eq_zero_of_le_zero this)
-- `Cslib.MachineLearning.PACLearning.rsampleComplexity_mono_family` idx 9: necessary (𝒟' = {Dt} needs 0 samples, 𝒟 = {Dt, Dff} needs 1 at δ = ¼)
theorem rmf9 : ¬ drop0% Cslib.MachineLearning.PACLearning.rsampleComplexity_mono_family 9 := fun h => by
  have := @h Unit Bool _ _ e12 e14 Set.univ D2 {Dt} ⟨0, (pacDt _ _).toIsRPACLearnerFor⟩
  rw [rscDt] at this; exact rscPos (Nat.eq_zero_of_le_zero this)
-- `Cslib.MachineLearning.PACLearning.IsRPACLearnable.rsampleComplexity_antitone_δ` idx 10: necessary ({Dt, Dff} learnable with 1 sample; δ₁ = ¾ needs 0 samples, δ₂ = ¼ needs 1)
theorem lrsa10 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsRPACLearnable.rsampleComplexity_antitone_δ 10 := fun h => by
  have := @h Unit Bool _ _ Set.univ D2 (fun ε δ => ⟨1, (perf ε δ).toIsRPACLearnerFor⟩) e12 e34 e14
  rw [rscCoin] at this; exact rscPos (Nat.eq_zero_of_le_zero this)
-- `Cslib.MachineLearning.PACLearning.IsRPACLearnable.rsampleComplexity_mono_family` idx 8: necessary (𝒟' = {Dt} learnable with 0 samples, 𝒟 = {Dt, Dff} needs 1)
theorem lrmf8 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsRPACLearnable.rsampleComplexity_mono_family 8 := fun h => by
  have := @h Unit Bool _ _ Set.univ D2 {Dt} (fun ε δ => ⟨0, (pacDt ε δ).toIsRPACLearnerFor⟩) e12 e14
  rw [rscDt] at this; exact rscPos (Nat.eq_zero_of_le_zero this)

end W3c5.RP

namespace W3c5.DP
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


noncomputable def q8 : ℝ≥0 := 1/8
theorem q8lt1 : q8 < q1 := by rw [← NNReal.coe_lt_coe]; simp [q1, q8]; norm_num
theorem q8le2 : q8 ≤ q2 := by rw [← NNReal.coe_le_coe]; simp [q2, q8]; norm_num
theorem q1sq : q1 ^ 2 ≤ q8 := by rw [← NNReal.coe_le_coe]; simp [q1, q8]; norm_num
noncomputable def e18 : Set.Ioo (0 : ℝ≥0) 1 := ⟨q8, by simp [q8], lt_of_lt_of_le q8lt1 (le_trans q1le2 q2lt1.le)⟩
theorem epsLt (ε : Set.Ioo (0 : ℝ≥0) 1) : ((ε.val : ℝ≥0) : ℝ≥0∞) < 1 := by exact_mod_cast ε.2.2

/-- "output true iff every sample is ((), true)" learns DD whenever (¼)^m ≤ δ -/
theorem pacAll (m : ℕ) (ε δ : Set.Ioo (0 : ℝ≥0) 1) (hm : (q1 : ℝ≥0∞) ^ m ≤ δ.val) :
    IsPACLearnerFor m ε δ Set.univ DD := by
  classical
  refine ⟨fun S _ => decide (∀ i, S i = pa), fun D _ hD => ?_⟩
  rcases hD with rfl | rfl
  · refine le_trans (measure_mono_null (t := ⋃ i, Function.eval i ⁻¹' ({pb} : Set (Unit × Bool))) ?_ ?_).le zero_le
    · intro S hS
      simp only [Set.mem_ofPred_eq] at hS
      rw [errC, optE, Dt_a, Dt_b] at hS
      by_contra hn
      simp only [Set.mem_iUnion, Set.mem_preimage, Function.eval, Set.mem_singleton_iff, not_exists] at hn
      have hall : ∀ i, S i = pa := fun i => by
        have := hn i; generalize S i = p at this ⊢; obtain ⟨u, v⟩ := p
        cases v
        · exact absurd rfl this
        · rfl
      simp [hall] at hS
    · exact measure_iUnion_null fun i => Measure.pi_eval_preimage_null _ Dt_b
  · refine le_trans (measure_mono (t := Set.univ.pi (fun _ => ({pa} : Set (Unit × Bool)))) ?_) ?_
    · intro S hS
      simp only [Set.mem_ofPred_eq] at hS
      rw [errC, optDf, Df_a, Df_b] at hS
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_singleton_iff, forall_const]
      by_contra hn
      rw [if_neg (by simpa using hn)] at hS
      exact absurd hS (not_lt.mpr le_self_add)
    · rw [Measure.pi_pi]; simp [Df_a]; exact hm

/-- no deterministic 1-sample learner for DD at ε = ¼, δ = ⅛ -/
theorem notP1 : ¬ IsPACLearnerFor 1 e14 e18 Set.univ DD := by
  rintro ⟨A, hA⟩
  have hsub : ∀ S : LabeledSample Unit Bool 1, S 0 ∈ ({pa} : Set (Unit × Bool)) → S = fun _ => pa :=
    fun S h => funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h
  cases hv : A (fun _ => pa) ()
  · have := hA Dt (by simp [DD])
    have hle : Measure.pi (fun _ : Fin 1 => Dt) {S | S 0 ∈ ({pa} : Set (Unit × Bool))} ≤
        Measure.pi (fun _ : Fin 1 => Dt) {S | optimalError Dt Set.univ + ↑e14.val < error Dt (A S)} := by
      refine measure_mono fun S hS => ?_
      rw [hsub S hS]
      simp only [Set.mem_ofPred_eq]
      rw [errC, hv, optE, Dt_a, Dt_b]
      simpa using epsLt e14
    rw [piFin1, Dt_a] at hle
    have h1 := le_trans hle this
    exact absurd (show (1 : ℝ≥0) ≤ q8 by exact_mod_cast h1) (not_le.mpr (lt_of_lt_of_le q8lt1 (le_trans q1le2 q2lt1.le)))
  · have := hA Df (by simp [DD])
    have hle : Measure.pi (fun _ : Fin 1 => Df) {S | S 0 ∈ ({pa} : Set (Unit × Bool))} ≤
        Measure.pi (fun _ : Fin 1 => Df) {S | optimalError Df Set.univ + ↑e14.val < error Df (A S)} := by
      refine measure_mono fun S hS => ?_
      rw [hsub S hS]
      simp only [Set.mem_ofPred_eq]
      rw [errC, hv, optDf, Df_b]
      simp only [ite_true]
      exact_mod_cast q11lt
    rw [piFin1, Df_a] at hle
    have h1 := le_trans hle this
    exact absurd (show q1 ≤ q8 by exact_mod_cast h1) (not_le.mpr q8lt1)

theorem notP0 : ¬ IsPACLearnerFor 0 e14 e18 Set.univ DD := fun h =>
  P0' (h.mono_δ (show e18.val ≤ e12.val from q8le2))
theorem pac1 : IsPACLearnerFor 1 e14 e14 Set.univ DD := pacAll 1 e14 e14 (by simp [e14])
theorem pac2 : IsPACLearnerFor 2 e14 e18 Set.univ DD :=
  pacAll 2 e14 e18 (by simp only [e18]; exact_mod_cast q1sq)
theorem sc14 : sampleComplexity IsPACLearnerFor Set.univ e14 e14 DD ≤ 1 := Nat.sInf_le pac1
theorem sc18 : 2 ≤ sampleComplexity IsPACLearnerFor Set.univ e14 e18 DD := by
  have hm := Nat.sInf_mem (⟨2, pac2⟩ : Set.Nonempty {m | IsPACLearnerFor m e14 e18 Set.univ DD})
  unfold sampleComplexity
  generalize sInf {m | IsPACLearnerFor m e14 e18 Set.univ DD} = v at hm ⊢
  rcases v with _ | _ | v
  · exact absurd hm notP0
  · exact absurd hm notP1
  · omega
theorem learnDD : IsPACLearnable Set.univ DD := by
  intro ε δ
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one δ.2.1 (lt_of_le_of_lt q1le2 q2lt1)
  exact ⟨k, pacAll k ε δ (by exact_mod_cast hk.le)⟩
theorem sc12 : sampleComplexity IsPACLearnerFor Set.univ e12 e12 DD = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le P0)
theorem scDD : sampleComplexity IsPACLearnerFor Set.univ e14 e12 DD ≠ 0 := by
  intro h0
  have hm := Nat.sInf_mem (⟨1, P1⟩ : Set.Nonempty {m | IsPACLearnerFor m e14 e12 Set.univ DD})
  unfold sampleComplexity at h0
  rw [h0] at hm
  exact P0' hm

-- `Cslib.MachineLearning.PACLearning.IsPACLearnerFor.mono_δ` idx 8: necessary (DD, m = 1, ε = ¼: confidence ¼ is reachable, ⅛ is not)
theorem pmd8 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnerFor.mono_δ 8 := fun h =>
  notP1 (@h Unit Bool _ _ 1 e14 e14 e18 Set.univ DD pac1)
-- `Cslib.MachineLearning.PACLearning.sampleComplexity_antitone_δ` idx 7: necessary (DD, ε = ¼: δ = ¼ needs ≤ 1 sample, δ = ⅛ needs 2)
theorem sad7 : ¬ drop0% Cslib.MachineLearning.PACLearning.sampleComplexity_antitone_δ 7 := fun h => by
  have := @h Unit Bool _ _ e14 e14 e18 Set.univ DD ⟨1, pac1⟩
  have := sc14; have := sc18; omega
-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_δ` idx 10: necessary (DD is learnable; ε = ¼: δ = ¼ needs ≤ 1 sample, δ = ⅛ needs 2)
theorem lsad10 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_δ 10 := fun h => by
  have := @h Unit Bool _ _ Set.univ DD learnDD e14 e14 e18
  have := sc14; have := sc18; omega
-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_ε` idx 10: necessary (DD is learnable; δ = ½: ε = ½ needs 0 samples, ε = ¼ needs 1)
theorem lsae10 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_ε 10 := fun h => by
  have := @h Unit Bool _ _ Set.univ DD learnDD e12 e14 e12
  rw [sc12] at this; exact scDD (Nat.eq_zero_of_le_zero this)

end W3c5.DP

namespace W3c5.AE
open Cslib MeasureTheory MachineLearning.PACLearning
open scoped NNReal ENNReal

/-- a cylinder over a null measurable set is null for `Measure.pi`, without σ-finiteness -/
theorem piCylNull {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (i : ι) {t : Set X} (ht : MeasurableSet t) (h0 : μ t = 0) :
    Measure.pi (fun _ : ι => μ) (Function.eval i ⁻¹' t) = 0 := by
  rw [← Set.univ_pi_update_univ]
  have hm : MeasurableSet (Set.univ.pi (Function.update (fun _ : ι => (Set.univ : Set X)) i t)) :=
    MeasurableSet.pi Set.countable_univ fun j _ => by
      by_cases hj : j = i
      · subst hj; simpa using ht
      · simp [Function.update_of_ne hj]
  rw [Measure.pi, toMeasure_apply _ _ hm]
  refine le_antisymm (le_trans (OuterMeasure.pi_pi_le _ _) ?_) zero_le
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using h0)]

-- `Cslib.MachineLearning.PACLearning.ae_mem_versionSpace_of_realizable` idx 10: removable (off-graph cylinders are null for the outer-measure product, no σ-finiteness needed)
theorem aem10 : drop% Cslib.MachineLearning.PACLearning.ae_mem_versionSpace_of_realizable 10 := by
  intro α β _ _ C c hc hcm hG P m
  classical
  have hf : Measurable (fun x : α => (x, c x)) := measurable_id.prodMk hcm
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ i, Function.eval i ⁻¹' {p : α × β | p.2 = c p.1}ᶜ) ?_ ?_
  · intro S hS
    simp only [VersionSpace, Set.mem_ofPred_eq, hc, true_and, not_forall] at hS
    obtain ⟨i, hi⟩ := hS
    exact Set.mem_iUnion.mpr ⟨i, fun h => hi h.symm⟩
  · refine measure_iUnion_null fun i => piCylNull _ i hG.compl ?_
    rw [Measure.map_apply hf hG.compl]
    convert measure_empty (μ := P)
    ext x; simp

end W3c5.AE

namespace W3c5.VL
open Cslib MachineLearning.PACLearning

/-- distinct concepts are separated by a one-point version space, so a class with finitely
many version spaces is finite -/
theorem vsInf {α β : Type*} (C : ConceptClass α β) (hC : C.Infinite) : (VersionSpaces C).Infinite := by
  intro hfin
  have : Finite (VersionSpaces C) := hfin.to_subtype
  apply hC
  refine Set.Finite.of_injOn (f := fun h => {V : VersionSpaces C | h ∈ V.1}) (t := Set.univ)
    (fun _ _ => trivial) ?_ Set.finite_univ
  intro h hh h' hh' heq
  by_contra hne
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
  let V : VersionSpaces C := ⟨VersionSpace C (fun _ : Fin 1 => (x, h x)), 1, _, rfl⟩
  have hV : V ∈ {V : VersionSpaces C | h ∈ V.1} := ⟨hh, fun _ => rfl⟩
  have hV' : V ∈ {V : VersionSpaces C | h' ∈ V.1} := by
    have := congrArg (fun s => V ∈ s) heq; simp only at this; exact this.mp hV
  exact hx (hV'.2 0).symm

universe u₁ u₂
-- `Cslib.MachineLearning.PACLearning.versionSpaces_ncard_le` idx 3: removable (an infinite class has infinitely many version spaces, so both sides degenerate: ncard = 0)
theorem vnl3 : drop% Cslib.MachineLearning.PACLearning.versionSpaces_ncard_le 3 := by
  intro α β C
  by_cases hC : C.Finite
  · exact versionSpaces_ncard_le hC
  · rw [Set.Infinite.ncard (vsInf C hC)]; exact Nat.zero_le _
-- `Cslib.MachineLearning.PACLearning.versionSpaces_finite` idx 3: necessary (C = all functions ℕ → Bool)
theorem vf3 : ¬ drop0% Cslib.MachineLearning.PACLearning.versionSpaces_finite 3 := fun h =>
  vsInf (Set.univ : ConceptClass ℕ Bool) Set.infinite_univ (@h ℕ Bool Set.univ)

def W : ConceptClass Bool Bool := {id, not}
/-- `{id, not}` is not a version space of all functions `Bool → Bool` -/
theorem wNot : W ∉ VersionSpaces (Set.univ : ConceptClass Bool Bool) := by
  rintro ⟨m, S, hS⟩
  have hid : (id : Bool → Bool) ∈ VersionSpace Set.univ S := hS ▸ (Or.inl rfl : (id : Bool → Bool) ∈ W)
  have hnot : (not : Bool → Bool) ∈ VersionSpace Set.univ S := hS ▸ (Or.inr rfl : (not : Bool → Bool) ∈ W)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : (fun _ => true : Bool → Bool) ∈ VersionSpace Set.univ S := ⟨trivial, fun i => i.elim0⟩
    rw [← hS] at this
    rcases this with h | h
    · have := congrFun h false; simp at this
    · have := congrFun (Set.mem_singleton_iff.mp h) true; simp at this
  · have h1 := hid.2 ⟨0, hm⟩; have h2 := hnot.2 ⟨0, hm⟩
    rw [← h1] at h2; simp at h2
-- `Cslib.MachineLearning.PACLearning.inter_mem_versionSpaces` idx 5: necessary (C = all of Bool → Bool, U = {id, not}, V = C)
theorem imv5 : ¬ drop0% Cslib.MachineLearning.PACLearning.inter_mem_versionSpaces 5 := fun h =>
  wNot (by simpa using @h Bool Bool Set.univ W Set.univ (self_mem_versionSpaces _))
-- `Cslib.MachineLearning.PACLearning.inter_mem_versionSpaces` idx 6: necessary (C = all of Bool → Bool, U = C, V = {id, not})
theorem imv6 : ¬ drop0% Cslib.MachineLearning.PACLearning.inter_mem_versionSpaces 6 := fun h =>
  wNot (by simpa using @h Bool Bool Set.univ Set.univ W (self_mem_versionSpaces _))

end W3c5.VL
