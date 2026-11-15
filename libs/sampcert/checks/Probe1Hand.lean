import Lean.Elab.Command
import SampCert
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

namespace Probe1
open SLang

-- Helpers (models and lemmas)

/-- constant mechanisms -/
def Cst {T Z : Type} (m : Mechanism T Z) : Prop := ∀ l l', m l = m l'

/-- DP system: constant mechanisms at every level, everything at level ≥ 1 -/
noncomputable def sys (T : Type) : DPSystem T where
  prop m ε := Cst m ∨ 1 ≤ ε
  of_app_dp δ _ := if 0 < δ then 0 else 1
  prop_adp := by
    intro Z _ m δ hδ ε' h
    simp only [hδ, ite_true] at h
    rcases h with h | h
    · intro l₁ l₂ _ S
      rw [h l₁ l₂]
      have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp ε') :=
        ENNReal.one_le_ofReal.mpr (Real.one_le_exp ε'.2)
      exact le_add_left (le_mul_of_one_le_left (by simp) h1)
    · exact absurd h (by norm_num)
  prop_mono := by
    intro Z m ε₁ ε₂ hle h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hle)
  adaptive_compose_prop := by
    intro U V _ _ m₁ m₂ ε₁ ε₂ ε h1 h2 he
    by_cases hb : 1 ≤ ε
    · exact Or.inr hb
    have hb1 : ¬ 1 ≤ ε₁ := fun h => hb (he ▸ le_add_right h)
    have hb2 : ¬ 1 ≤ ε₂ := fun h => hb (he ▸ le_add_left h)
    have c1 : Cst m₁ := h1.resolve_right hb1
    have c2 : ∀ u, Cst (m₂ u) := fun u => (h2 u).resolve_right hb2
    left
    intro l l'
    unfold privComposeAdaptive
    rw [c1 l l']
    congr 1
    funext A
    rw [c2 A l l']
  postprocess_prop := by
    intro V U _ pp m ε h
    rcases h with h | h
    · left; intro l l'; unfold privPostProcess; rw [h l l']
    · exact Or.inr h
  const_prop := by
    intro U _ u ε _
    left; intro l l'; rfl

noncomputable def sysPar (T : Type) : DPPar T :=
  { sys T with
    prop_par := by
      intro U V m1 m2 ε₁ ε₂ ε he f h1 h2
      by_cases hb : 1 ≤ ε
      · exact Or.inr hb
      have hb1 : ¬ 1 ≤ ε₁ := fun h => hb (he ▸ h.trans (le_max_left _ _))
      have hb2 : ¬ 1 ≤ ε₂ := fun h => hb (he ▸ h.trans (le_max_right _ _))
      have c1 : Cst m1 := h1.resolve_right hb1
      have c2 : Cst m2 := h2.resolve_right hb2
      left
      intro l l'
      unfold privParCompose
      rw [c1 _ (List.filter f l'), c2 _ (List.filter ((! ·) ∘ f) l')] }

/-- the deterministic length mechanism -/
noncomputable def mlen : Mechanism Unit ℕ := fun l => SPMF_pure l.length

theorem spmf_apply {α : Type} (p : SPMF α) (a : α) : p a = p.1 a := rfl

theorem ncst_of {T Z : Type} {m : Mechanism T Z} (l l' : List T) (x : Z) (h : (m l).1 x ≠ (m l').1 x) :
    ¬ Cst m := fun hc => h (by rw [hc l l'])

theorem mlen_ncst : ¬ Cst mlen := fun h => by
  have := congrArg (fun p : SPMF ℕ => p.1 0) (h [] [()])
  simp [mlen, probPure] at this

noncomputable def noiseless {T : Type} (dps : DPSystem T) : DPNoise dps where
  noise q _ _ _ l := SPMF_pure (q l)
  noise_priv _ _ _ := False
  noise_prop h := h.elim

theorem nb1 : Neighbour [()] [] := Neighbour.Deletion (a := []) (b := []) (n := ()) rfl rfl

theorem lenSens : sensitivity (fun l : List Unit => (l.length : ℤ)) 1 := by
  intro l₁ l₂ h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega

/-- unbounded below queries: never lucky, also after shifting -/
theorem negq_unlucky (n : ℕ) : ¬ has_lucky (shift_qs n (fun A (_ : List Unit) => -(A : ℤ))) 0 := fun H => by
  rcases H 0 [] with ⟨K, HK⟩
  have := HK (K.toNat + 1) K le_rfl
  simp [shift_qs] at this
  omega

theorem nbN : Neighbour [1] ([] : List ℕ) := Neighbour.Deletion (a := []) (b := []) (n := 1) rfl rfl

theorem alg1 (n : ℕ) : ((3/2:ℝ)^n) ^ (2:ℝ) * (2⁻¹:ℝ)^(n+1) = 2⁻¹ * (9/8 : ℝ)^n := by
  rw [Real.rpow_two, ← pow_mul, pow_succ, show (9/8 : ℝ) = (3/2)^2 * 2⁻¹ by norm_num, mul_pow, ← pow_mul,
    mul_comm 2 n]
  ring

theorem alg2 (n : ℕ) : (3/2:ℝ)^n * (2⁻¹:ℝ)^(n+1) = 2⁻¹ * (3/4 : ℝ)^n := by
  rw [pow_succ, show (3/4 : ℝ) = (3/2) * 2⁻¹ by norm_num, mul_pow]
  ring

/-- geometric PMF on ℕ: n ↦ 2⁻¹^(n+1) -/
noncomputable def geomPMF : PMF ℕ := ⟨fun n => (2⁻¹ : ENNReal) ^ (n+1), by
    rw [ENNReal.summable.hasSum_iff]
    simp_rw [pow_succ, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)⟩

theorem geomPMF_toReal (n : ℕ) : (geomPMF n).toReal = (2⁻¹ : ℝ)^(n+1) := by
  show ((2⁻¹ : ENNReal) ^ (n+1)).toReal = _
  simp

-- `PMF_mul_mul_inv_eq_mul_cancel` idx 3: necessary
theorem p1_1 : ¬ drop0% PMF_mul_mul_inv_eq_mul_cancel 3 := fun h => by
  have := h (T := Bool) (PMF.pure true) (PMF.pure false) true
  simp at this

-- `RenyiDivergenceExpectation_pointwise` idx 3: necessary
theorem p1_2 : ¬ drop0% RenyiDivergenceExpectation_pointwise 3 := fun h => by
  have := h 1 ⊤ (α := 1/2) (by simp)
  norm_num [ENNReal.top_rpow_of_pos, ENNReal.zero_rpow_of_pos] at this

-- `RenyiDivergenceExpectation_pointwise` idx 4: necessary
theorem p1_3 : ¬ drop0% RenyiDivergenceExpectation_pointwise 4 := fun h => by
  have := h 1 0 (α := 2) (by norm_num)
  norm_num [ENNReal.zero_rpow_of_neg] at this

-- `RenyiDivergenceExpectation` idx 4: necessary
theorem p1_4 : ¬ drop0% RenyiDivergenceExpectation 4 := fun h => by
  have := h (T := Unit) (fun _ => 1) (fun _ => ⊤) (α := 1/2) (fun _ h => by simp at h)
  norm_num [tsum_fintype, ENNReal.top_rpow_of_pos, ENNReal.zero_rpow_of_pos] at this

-- `ENNReal_rpow_sub_one_mul` idx 3: necessary
theorem p1_5 : ¬ drop0% ENNReal_rpow_sub_one_mul 3 := fun h => by
  have := h ⊤ (α := 0) (by simp)
  norm_num [ENNReal.top_rpow_of_neg] at this

-- `RenyiDivergenceExpectation'` idx 4: necessary
theorem p1_6 : ¬ drop0% RenyiDivergenceExpectation' 4 := fun h => by
  have := h (T := Bool) (PMF.pure true) (PMF.pure false) (α := 0)
  norm_num [tsum_fintype, ENNReal.top_rpow_of_neg, ENNReal.zero_rpow_of_neg] at this

-- `reducedPMF_pos` idx 4: necessary
theorem p1_7 : ¬ indep0% reducedPMF_pos 4 := fun h =>
  h (T := Bool) (q := PMF.pure true) (fun _ h => h) false (by simp)

-- `Renyi_Jensen_ENNReal_converse` idx 2: removable
theorem p1_8 : drop% Renyi_Jensen_ENNReal_converse 2 := by
  intro T inst _ p q α h1 h2 h3
  exact @Renyi_Jensen_ENNReal_converse T ⊤ (@MeasurableSingletonClass.mk T ⊤ (fun _ => MeasurableSpace.measurableSet_top)) _ p q α h1 h2 h3

-- `Renyi_Jensen_ENNReal_converse` idx 7: necessary
theorem p1_9 : ¬ drop0% Renyi_Jensen_ENNReal_converse 7 := fun h => by
  have := h (T := Bool) (PMF.pure true) (PMF.uniformOfFintype Bool) (α := 1)
    (fun x hx => by simp [PMF.uniformOfFintype_apply] at hx) (by simp)
  have := congrArg (fun r : PMF Bool => r false) this
  simp [PMF.uniformOfFintype_apply] at this
  exact absurd this.symm (by simp)

-- `Renyi_Jensen_ENNReal_converse` idx 8: necessary
theorem p1_10 : ¬ drop0% Renyi_Jensen_ENNReal_converse 8 := fun h => by
  have := h (T := Bool) (PMF.uniformOfFintype Bool) (PMF.pure true) (α := 2) (by norm_num)
    (by simp [tsum_fintype, PMF.uniformOfFintype_apply])
  have := congrArg (fun r : PMF Bool => r false) this
  simp [PMF.uniformOfFintype_apply] at this

-- `Neighbour_symm` idx 3: necessary
theorem p1_11 : ¬ drop0% Neighbour_symm 3 := fun h => by
  rcases (h (T := Unit) [] []) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp at *

-- `Integrable_rpow` idx 8: necessary
theorem p1_12 : ¬ drop0% Integrable_rpow 8 := fun h => by
  have := h (T := ℕ) (fun _ => (0:ℝ)) (fun _ => le_rfl) MeasureTheory.Measure.count ⊤
    (MeasureTheory.MemLp.zero) (by simp)
  simp [MeasureTheory.integrable_const_iff] at this
  have h2 := this.measure_univ_lt_top
  simp [MeasureTheory.Measure.count_univ] at h2

-- `SLang.DPSystem.prop_adp` idx 6: necessary
theorem p1_13 : ¬ drop0% SLang.DPSystem.prop_adp 6 := fun h => by
  have := @h Unit (sys Unit) ℕ inferInstance mlen 0 0 (Or.inr (by show (1:NNReal) ≤ (if (0:NNReal) < 0 then 0 else 1); simp))
  have := this [()] [] (Neighbour.Deletion (a := []) (b := []) (n := ()) rfl rfl) {1}
  simp [mlen, probPure, spmf_apply] at this

-- `SLang.DPSystem.prop_mono` idx 6: necessary
theorem p1_14 : ¬ drop0% SLang.DPSystem.prop_mono 6 := fun h =>
  mlen_ncst ((@h Unit (sys Unit) ℕ mlen 1 0 (Or.inr le_rfl)).resolve_right (by norm_num))

-- `SLang.DPSystem.prop_mono` idx 7: necessary
theorem p1_15 : ¬ drop0% SLang.DPSystem.prop_mono 7 := fun h =>
  mlen_ncst ((@h Unit (sys Unit) ℕ mlen 0 0 le_rfl).resolve_right (by norm_num))

-- `SLang.DPSystem_prop_ext` idx 7: necessary
theorem p1_16 : ¬ drop0% SLang.DPSystem_prop_ext 7 := fun h =>
  mlen_ncst ((@h Unit ℕ (sys Unit) 0 0 mlen rfl).resolve_right (by norm_num))

-- `SLang.DPSystem.adaptive_compose_prop` idx 12: necessary
theorem p1_17 : ¬ drop0% SLang.DPSystem.adaptive_compose_prop 12 := fun h => by
  have := (@h Unit (sys Unit) ℕ ℕ inferInstance inferInstance (privConst 0) (fun _ => mlen) 0 0 0
    (Or.inl (fun _ _ => rfl)) (by simp)).resolve_right (by norm_num)
  refine ncst_of [] [()] (0, 0) ?_ this
  simp [privComposeAdaptive, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure]

-- `SLang.DPSystem.adaptive_compose_prop` idx 13: necessary
theorem p1_18 : ¬ drop0% SLang.DPSystem.adaptive_compose_prop 13 := fun h => by
  have := (@h Unit (sys Unit) ℕ ℕ inferInstance inferInstance mlen (fun _ => privConst 0) 1 0 0
    (Or.inr le_rfl) (fun _ => Or.inl (fun _ _ => rfl))).resolve_right (by norm_num)
  refine ncst_of [] [()] (0, 0) ?_ this
  simp [privComposeAdaptive, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure]

-- `SLang.DPPar.prop_par` idx 9: necessary
theorem p1_19 : ¬ drop0% SLang.DPPar.prop_par 9 := fun h => by
  have := (@h Unit (sysPar Unit) ℕ ℕ mlen (privConst 0) 1 0 0 (fun _ => true)
    (Or.inr le_rfl) (Or.inl (fun _ _ => rfl))).resolve_right (by norm_num)
  refine ncst_of [] [()] (0, 0) ?_ this
  simp [privParCompose, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure]

-- `SLang.DPPar.prop_par` idx 12: necessary
theorem p1_20 : ¬ drop0% SLang.DPPar.prop_par 12 := fun h => by
  have := (@h Unit (sysPar Unit) ℕ ℕ (privConst 0) mlen 0 0 0 (by simp) (fun _ => false)
    (Or.inl (fun _ _ => rfl))).resolve_right (by norm_num)
  refine ncst_of [] [()] (0, 0) ?_ this
  simp [privParCompose, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure]

-- `SLang.privNoisedBoundedSum_DP` idx 6: necessary
theorem p1_21 : ¬ drop0% SLang.privNoisedBoundedSum_DP 6 := fun h => by
  have := (@h (sys ℕ) (noiseless (sys ℕ)) 1 1 1 0).resolve_right (by norm_num)
  refine ncst_of [] [1] 0 ?_ this
  unfold privNoisedBoundedSum noiseless
  simp [exactBoundedSum, probPure]

-- `SLang.singleton_to_event` idx 4: necessary
theorem p1_22 : ¬ drop0% SLang.singleton_to_event 4 := fun h => by
  have := h mlen 0 [()] [] nb1 {1}
  simp [mlen, probPure, spmf_apply] at this

-- `SLang.ApproximateDP_of_DP` idx 4: necessary
theorem p1_23 : ¬ drop0% SLang.ApproximateDP_of_DP 4 := fun h => by
  have := h mlen 0 0 [()] [] nb1 {1}
  simp [mlen, probPure, spmf_apply] at this

-- `SLang.pureDP_priv_Par` idx 11: necessary
theorem p1_24 : ¬ drop0% SLang.pureDP_priv_Par 11 := fun h => by
  have := @h Unit ℕ ℕ (privConst 0) mlen 0 0 0 (by simp) (fun _ => false) privConst_DP_Bound [()] [] nb1 {(0, 1)}
  simp [privParCompose, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure, spmf_apply] at this

-- `SLang.privPostProcess_DP_bound` idx 5: necessary
theorem p1_25 : ¬ drop0% SLang.privPostProcess_DP_bound 5 := fun h => by
  have := @h Unit ℕ ℕ mlen 0 id [()] [] nb1 {1}
  simp [privPostProcess, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure, spmf_apply] at this

-- `RenyiDivergence_def_exp` idx 4: removable
theorem p1_26 : drop% RenyiDivergence_def_exp 4 := by
  intro T p q α
  by_cases hα : α = 1
  · subst hα
    rw [EReal_coe_sub_one]
    simp
  rw [RenyiDivergence_def, ← mul_assoc]
  have Hcancel : (α.toEReal - OfNat.ofNat 1) * (α - OfNat.ofNat 1)⁻¹.toEReal = 1 := by
    rw [EReal_coe_sub_one, ← EReal.coe_mul,
        mul_inv_cancel₀ (sub_ne_zero.mpr hα), EReal.coe_one]
  rw [Hcancel, one_mul, ENNReal.elog_eexp]

-- `RenyiDivergenceExpectation'_pointwise` idx 5: removable
theorem p1_27 : drop% RenyiDivergenceExpectation'_pointwise 5 := by
  intro a b α h ha
  by_cases hat : a = ⊤
  · subst hat
    rcases eq_or_ne b ⊤ with rfl | hbt
    · rw [ENNReal.top_rpow_of_neg (y := 1 - α) (by linarith), ENNReal.div_top,
        ENNReal.zero_rpow_of_pos (by linarith)]
      simp
    · have hb : b ^ (1 - α) ≠ 0 := by
        rw [Ne, ENNReal.rpow_eq_zero_iff]
        rintro (⟨_, h'⟩ | ⟨h', _⟩)
        · linarith
        · exact hbt h'
      rw [ENNReal.top_rpow_of_pos (by linarith), ENNReal.top_div_of_ne_top hbt,
        ENNReal.top_rpow_of_pos (by linarith), ENNReal.top_mul hb, ENNReal.top_mul_top]
  · exact RenyiDivergenceExpectation'_pointwise a b h ha hat

-- `Integrable_rpow_of_one_lt` idx 5: removable
theorem p1_28 : drop% Integrable_rpow_of_one_lt 5 := by
  intro T _ f α h μ mem
  have hα0 : ENNReal.ofReal α ≠ 0 := by simp; linarith
  have hαt : ENNReal.ofReal α ≠ ⊤ := by simp
  have Z := mem.integrable_norm_rpow hα0 hαt
  rw [ENNReal.toReal_ofReal (by linarith)] at Z
  refine Z.mono' ((Real.continuous_rpow_const (by linarith)).comp_aestronglyMeasurable mem.aestronglyMeasurable) ?_
  refine MeasureTheory.ae_of_all _ (fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact Real.abs_rpow_le_abs_rpow _ _

-- `Integrable_of_MemLp_one_lt` idx 7: necessary
theorem p1_29 : ¬ drop0% Integrable_of_MemLp_one_lt 7 := fun h => by
  have := @h ℝ _ (fun x => x ^ (-1 : ℝ)) 2 (by norm_num)
    (MeasureTheory.volume.restrict (Set.Ioo 0 1)) inferInstance
  have h2 := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -1) (t := 1) one_pos).mp this
  norm_num at h2

-- `Renyi_Jensen_strict_real` idx 7: necessary
theorem p1_30 : ¬ drop0% Renyi_Jensen_strict_real 7 := fun h => by
  have := h (T := Bool) (fun b => if b then 1 else 0) (PMF.uniformOfFintype Bool) 1
    (fun x => by cases x <;> simp) (MeasureTheory.MemLp.of_discrete) (by simp [PMF.uniformOfFintype_apply])
  simp [tsum_fintype, PMF.uniformOfFintype_apply] at this

-- `Renyi_Jensen_strict_real` idx 8: necessary
theorem p1_31 : ¬ drop0% Renyi_Jensen_strict_real 8 := fun h => by
  have := h (T := Bool) (fun b => if b then -1 else 0) (PMF.uniformOfFintype Bool) 3 (by norm_num)
    (MeasureTheory.MemLp.of_discrete) (by simp [PMF.uniformOfFintype_apply])
  simp [tsum_fintype, PMF.uniformOfFintype_apply] at this
  norm_num at this

-- `Renyi_Jensen_ENNReal` idx 7: necessary
theorem p1_32 : ¬ drop0% Renyi_Jensen_ENNReal 7 := fun h => by
  have := h (T := Fin 4) (PMF.pure 0) (PMF.uniformOfFintype (Fin 4)) (α := 1/2)
    (fun x hx => by simp [PMF.uniformOfFintype_apply] at hx)
  have h4 : (4 : ENNReal) ^ ((2:ℝ)⁻¹) = 2 := by
    rw [show (4 : ENNReal) = 2 ^ (2:ℝ) by norm_num, ← ENNReal.rpow_mul]; norm_num
  simp [tsum_fintype, Fin.sum_univ_four, PMF.uniformOfFintype_apply] at this
  have h24 : (2 : ENNReal) * 4⁻¹ = 2⁻¹ := by
    rw [show (4:ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), ENNReal.one_rpow, h4, h24] at this
  simp at this

-- `Renyi_Jensen_real` idx 2: removable
theorem p1_33 : drop% Renyi_Jensen_real 2 := by
  intro T inst f q α h h2 mem
  have Htrim : @PMF.toMeasure T inst q = (@PMF.toMeasure T ⊤ q).trim le_top := by
    ext s hs
    rw [MeasureTheory.trim_measurableSet_eq _ hs, PMF.toMeasure_apply _ hs,
      @PMF.toMeasure_apply T ⊤ q s MeasurableSpace.measurableSet_top]
  rw [Htrim] at mem
  exact @Renyi_Jensen_real T ⊤ (@MeasurableSingletonClass.mk T ⊤ (fun _ => MeasurableSpace.measurableSet_top))
    f q α h h2 (MeasureTheory.memLp_of_memLp_trim le_top mem)

-- `SLang.DSN` idx 6: necessary
theorem p1_34 : ¬ drop0% SLang.DSN 6 := fun h => by
  have := h (sv_T := Unit) (fun _ l => (l.length : ℤ)) (L1 := [(), ()]) (L2 := []) (fun _ => lenSens) 0
  norm_num at this

-- `SLang.Hsens_cov_τ_lemma` idx 6: necessary
theorem p1_35 : ¬ drop0% SLang.Hsens_cov_τ_lemma 6 := fun h => by
  have := h (sv_T := Unit) (fun _ l => 2 * (l.length : ℤ)) (l₁ := [()]) (l₂ := []) (H := []) (v0 := 0) nb1
  simp [sv8_sum] at this

-- `SLang.Hsens_cov_τ` idx 2: necessary
theorem p1_36 : ¬ drop0% SLang.Hsens_cov_τ 2 := fun h => by
  have := h (sv_T := Unit) (fun _ l => 2 * (l.length : ℤ)) 0 [] [()] [] nb1
  simp [cov_τ_def, sv8_G, sv8_sum, sens_cov_τ] at this

-- `SLang.Hsens_cov_vk` idx 2: necessary
theorem p1_37 : ¬ drop0% SLang.Hsens_cov_vk 2 := fun h => by
  have := h (sv_T := Unit) (fun i l => if i = 0 then 0 else 3 * (l.length : ℤ)) 0 [] [] [()] 0
    (Neighbour.Addition (a := []) (b := []) (n := ()) rfl rfl)
  simp [cov_vk_def, cov_τ_def, sv8_G, sv8_sum, sens_cov_vk, sens_cov_τ] at this

-- `SLang.tsum_eq_tsum_of_ne_zero_bij` idx 9: necessary
theorem p1_38 : ¬ drop0% SLang.tsum_eq_tsum_of_ne_zero_bij 9 := fun h => by
  have := h (α := ℕ) (β := Unit) (γ := Empty) (f := fun _ => 1) (g := fun _ => 0)
    (fun x => ()) (fun x => x.1.elim) (fun x => x.1.elim)
  simp at this

-- `SLang.cone_left_edge_constancy` idx 14: removable
theorem p1_39 : drop% SLang.cone_left_edge_constancy 14 := by
  intro dps dpn sv_T qs T ε₁ ε₂ τ data v0 vk cut initial hist hc
  exact cone_constancy cut initial hist hc

-- `SLang.sv6_loop_ind` idx 10: necessary
theorem p1_40 : ¬ drop0% SLang.sv6_loop_ind 10 := fun h => by
  have := h (sv_T := Unit) (fun _ _ => 0) 0 0 [] 1 [] [] 0 0 (by simp)
  simp [sv6_loop, sv6_cond_rec, sv4_aboveThreshC, sv1_aboveThreshC, sv1_threshold, sv1_noise, probZero] at this

-- `SLang.sv5_sv6_loop_eq_point` idx 10: necessary
theorem p1_41 : ¬ drop0% SLang.sv5_sv6_loop_eq_point 10 := fun h => by
  have := h (sv_T := Unit) (fun _ _ => 0) 0 0 [] 5 0 [] [] 0 rfl
  simp [sv5_loop, sv6_loop, sv6_cond_rec, sv4_aboveThreshC, sv1_aboveThreshC, sv1_threshold, sv1_noise,
    probZero, probWhileCut, probWhileFunctional] at this
  rw [ENNReal.tsum_eq_zero.mpr (fun a => by
    by_cases ha : a = (([], 0), [])
    · subst ha; simp
    · simp [probPure, ha]; exact fun _ => ha)] at this
  simp at this

-- `SLang.shift_qs_lucky` idx 4: necessary
theorem p1_42 : ¬ drop0% SLang.shift_qs_lucky 4 := fun h => negq_unlucky 0 (h 0 0 _)

-- `SLang.privSparse_DP` idx 6: necessary
theorem p1_43 : ¬ indep0% SLang.privSparse_DP 6 := fun h => by
  have := h 0 1 1 (sv_T := Unit) (dps := sys Unit) (fun A _ => -(A : ℤ))
    (fun N H => absurd H (negq_unlucky N)) _ 0 rfl
  have e : shift_qs 0 (fun (A : ℕ) (_ : List Unit) => -(A : ℤ)) = (fun (A : ℕ) (_ : List Unit) => -(A : ℤ)) := by
    funext A l; simp [shift_qs]
  apply negq_unlucky 0
  rw [e]
  exact this

-- `combinePure` idx 5: necessary
theorem p1_44 : ¬ drop0% combinePure 5 := fun h => by
  have H := @h (noiseless PureDPSystem) 1 1 1 0
  have H2 : DP (@privNoisedBoundedMean PureDPSystem (noiseless PureDPSystem) 1 1 1) ((0:NNReal):ℝ) := H
  have := H2 [1] [] nbN {1}
  unfold privNoisedBoundedMean privNoisedBoundedSum privNoisedCount noiseless at this
  simp [exactBoundedSum, exactCount, Bind.bind, Pure.pure, SLang.pure_bind, probPure, spmf_apply] at this

-- `Renyi_Jensen_ENNReal_converse` idx 3: removable
theorem p1_45 : drop% Renyi_Jensen_ENNReal_converse 3 := by
  intro T inst _ p q α h H Hsum
  let S : Set T := q.support
  haveI : Countable S := q.support_countable.to_subtype
  have hp : Function.support p ⊆ S := fun x hx => by
    rw [PMF.mem_support_iff]; intro hq; exact hx (H x hq)
  have hq : Function.support q ⊆ S := fun x hx => (PMF.mem_support_iff q x).mpr hx
  let p' : PMF S := ⟨fun x => p x, (hasSum_subtype_iff_of_support_subset hp).mpr (PMF.hasSum_coe_one p)⟩
  let q' : PMF S := ⟨fun x => q x, (hasSum_subtype_iff_of_support_subset hq).mpr (PMF.hasSum_coe_one q)⟩
  have s1 : Function.support (fun x => p x / q x * q x) ⊆ S := fun x hx => by
    rw [PMF.mem_support_iff]; intro h0; apply hx; simp [h0]
  have s2 : Function.support (fun x => (p x / q x) ^ α * q x) ⊆ S := fun x hx => by
    rw [PMF.mem_support_iff]; intro h0; apply hx; simp [h0]
  rw [← tsum_subtype_eq_of_support_subset s1, ← tsum_subtype_eq_of_support_subset s2] at Hsum
  have key : p' = q' := Renyi_Jensen_ENNReal_converse p' q' h (fun x hx => H x hx) Hsum
  ext x
  by_cases hx : x ∈ S
  · exact congrArg (fun r : PMF S => r ⟨x, hx⟩) key
  · have hq0 : q x = 0 := by
      by_contra hne; exact hx ((PMF.mem_support_iff q x).mpr hne)
    rw [hq0, H x hq0]

-- `Renyi_Jensen_real` idx 8: necessary
theorem p1_46 : ¬ drop0% Renyi_Jensen_real 8 := fun h => by
  have := h (T := ℕ) (fun n => (3/2 : ℝ)^n) geomPMF 2 (by norm_num) (fun n => by positivity)
  simp only [geomPMF_toReal, alg1, alg2] at this
  have hns : ¬ Summable (fun n : ℕ => 2⁻¹ * (9/8 : ℝ)^n) := by
    rw [summable_mul_left_iff (by norm_num), summable_geometric_iff_norm_lt_one]
    norm_num
  have hs : Summable (fun n : ℕ => 2⁻¹ * (3/4 : ℝ)^n) :=
    (summable_mul_left_iff (by norm_num)).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  rw [tsum_eq_zero_of_not_summable hns] at this
  have hpos : 0 < ∑' n : ℕ, 2⁻¹ * (3/4 : ℝ)^n :=
    hs.tsum_pos (fun n => by positivity) 0 (by norm_num)
  have := lt_of_lt_of_le (Real.rpow_pos_of_pos hpos 2) this
  exact lt_irrefl _ this

end Probe1
