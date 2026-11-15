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

section W1c2_s1
open Classical Real Filter Asymptotics FourierTransform

namespace W1c2
theorem g0 (μ : ℝ) : gauss_term_ℝ 0 μ = fun _ => 1 := by
  funext x; simp [gauss_term_ℝ]
theorem tsum_one_int : ∑' (_ : ℤ), (1:ℝ) = 0 := by
  simp
theorem not_summable_one_nat : ¬ Summable (fun (_ : ℕ) => (1:ℝ)) := by
  simp [summable_const_iff]
end W1c2

-- `tsum_shift` idx 2
theorem w2_1 : drop% tsum_shift 2 := by
  intro f μ
  exact (Equiv.addRight μ).tsum_eq f
-- `tsum_shift₁` idx 2
theorem w2_2 : drop% tsum_shift₁ 2 := by
  intro f μ _
  exact ((Equiv.addRight (μ:ℤ)).tsum_eq f).symm
-- `tsum_shift₁` idx 3
theorem w2_3 : drop% tsum_shift₁ 3 := by
  intro f μ _
  exact ((Equiv.addRight (μ:ℤ)).tsum_eq f).symm
-- `tsum_shift₂` idx 2
theorem w2_4 : drop% tsum_shift₂ 2 := by
  intro f μ _
  exact (Equiv.subRight (μ:ℤ)).tsum_eq f
-- `tsum_shift₂` idx 3
theorem w2_5 : drop% tsum_shift₂ 3 := by
  intro f μ _
  exact (Equiv.subRight (μ:ℤ)).tsum_eq f

-- `sum_gauss_term_ne_zero` idx 1
theorem w2_6 : ¬ drop0% sum_gauss_term_ne_zero 1 := by
  intro h; have := @h 0 0; simp [W1c2.g0] at this
-- `discrete_gaussian_pos` idx 1
theorem w2_7 : ¬ drop0% discrete_gaussian_pos 1 := by
  intro h; have := @h 0 0 0; simp [discrete_gaussian, W1c2.g0] at this
-- `discrete_gaussian_normalizes` idx 1
theorem w2_8 : ¬ drop0% discrete_gaussian_normalizes 1 := by
  intro h; have := @h 0 0; simp [discrete_gaussian, W1c2.g0] at this
-- `discrete_gaussian_normal` idx 1
theorem w2_9 : ¬ drop0% discrete_gaussian_normal 1 := by
  intro h; have := @h 0 0; simp [discrete_gaussian, W1c2.g0] at this
  exact zero_ne_one (hasSum_zero.unique this)
-- `gauss_convergence_nat_neg` idx 1
theorem w2_10 : ¬ drop0% gauss_convergence_nat_neg 1 := by
  intro h; have := @h 0 0; simp [W1c2.g0, summable_const_iff] at this
-- `shifted_gauss_summable_pos` idx 1
theorem w2_11 : ¬ drop0% shifted_gauss_summable_pos 1 := by
  intro h; have := @h 0 0 0; simp [W1c2.g0, summable_const_iff] at this
-- `shifted_gauss_summable_neg` idx 1
theorem w2_12 : ¬ drop0% shifted_gauss_summable_neg 1 := by
  intro h; have := @h 0 0 0; simp [W1c2.g0, summable_const_iff] at this
-- `sum_gauss_term_nonneg` idx 1
theorem w2_13 : drop% sum_gauss_term_nonneg 1 := by
  intro σ μ; exact tsum_nonneg fun n => (Real.exp_pos _).le
-- `discrete_gaussian_nonneg` idx 1
theorem w2_14 : drop% discrete_gaussian_nonneg 1 := by
  intro σ μ n; exact div_nonneg (Real.exp_pos _).le (tsum_nonneg fun n => (Real.exp_pos _).le)
-- `discrete_gaussian_summable` idx 1
theorem w2_15 : drop% discrete_gaussian_summable 1 := by
  intro σ
  by_cases h : σ = 0
  · subst h; simp [discrete_gaussian, W1c2.g0]
  · exact discrete_gaussian_summable h
-- `discrete_gaussian_summable'` idx 1
theorem w2_16 : drop% discrete_gaussian_summable' 1 := by
  intro σ μ
  by_cases h : σ = 0
  · subst h; simp [discrete_gaussian, W1c2.g0]
  · exact discrete_gaussian_summable' h μ
-- `sum_gauss_term_bound` idx 1
theorem w2_17 : drop% sum_gauss_term_bound 1 := by
  intro σ μ
  by_cases h : σ = 0
  · subst h; simp [W1c2.g0]
  · exact sum_gauss_term_bound h μ
-- `gauss_sum_1_periodic` idx 1
theorem w2_18 : drop% gauss_sum_1_periodic 1 := by
  intro σ μ
  by_cases h : σ = 0
  · subst h; simp [W1c2.g0]
  · exact gauss_sum_1_periodic h μ
-- `shifted_gauss_sum_pos` idx 1
theorem w2_19 : drop% shifted_gauss_sum_pos 1 := by
  intro σ μ k
  by_cases h : σ = 0
  · subst h; simp [W1c2.g0]
  · exact shifted_gauss_sum_pos h μ k
-- `shifted_gauss_sum_neg` idx 1
theorem w2_20 : drop% shifted_gauss_sum_neg 1 := by
  intro σ μ k
  by_cases h : σ = 0
  · subst h; simp [W1c2.g0]
  · exact shifted_gauss_sum_neg h μ k

end W1c2_s1

section W1c2_s2
open Classical Real Filter Asymptotics FourierTransform

-- `ENNReal.ofEReal_mul_nonneg` idx 3
theorem w2_21 : drop% ENNReal.ofEReal_mul_nonneg 3 := by
  intro w z Hw
  by_cases hz : 0 ≤ z
  · exact ENNReal.ofEReal_mul_nonneg Hw hz
  · push_neg at hz
    have h1 : ENNReal.ofEReal z = 0 := (ENNReal.ofEReal_eq_zero_iff z).1 hz.le
    have h2 : ENNReal.ofEReal (w * z) = 0 :=
      (ENNReal.ofEReal_eq_zero_iff _).1 (EReal.mul_nonpos_iff.2 (Or.inl ⟨Hw, hz.le⟩))
    rw [h1, h2, mul_zero]
-- `ENNReal.ofEReal_nonneg_scal_l` idx 3
theorem w2_22 : ¬ drop0% ENNReal.ofEReal_nonneg_scal_l 3 := by
  intro h; have := @h 1 (-1) (by norm_num); exact absurd this (by norm_num)
-- `ENNReal.ofReal_injective_nonneg` idx 2
theorem w2_23 : ¬ drop0% ENNReal.ofReal_injective_nonneg 2 := by
  intro h; have := @h (-1) 0 (le_refl 0) (by simp); norm_num at this
-- `ENNReal.elog_of_pos_real` idx 1
theorem w2_24 : ¬ drop0% ENNReal.elog_of_pos_real 1 := by
  intro h; have := @h 0; simp [ENNReal.elog_zero] at this
-- `ENNReal.elog_ENNReal_ofReal_of_pos` idx 1
theorem w2_25 : ¬ drop0% ENNReal.elog_ENNReal_ofReal_of_pos 1 := by
  intro h; have := @h 0; simp [ENNReal.elog_zero] at this
-- `ENNReal.ereal_smul_lt_left` idx 4
theorem w2_26 : drop% ENNReal.ereal_smul_lt_left 4 := by
  intro w z s Hr1 H
  rcases lt_or_eq_of_le (le_top : s ≤ ⊤) with hs | hs
  · exact ENNReal.ereal_smul_lt_left s Hr1 hs H
  · subst hs
    by_contra hc; push_neg at hc
    rcases lt_trichotomy w 0 with hw | hw | hw
    · have hz : z < 0 := lt_of_le_of_lt hc hw
      rw [EReal.top_mul_of_neg hw, EReal.top_mul_of_neg hz] at H; exact lt_irrefl _ H
    · subst hw
      rcases lt_or_eq_of_le hc with hz | hz
      · rw [EReal.top_mul_of_neg hz] at H; exact not_lt_bot H
      · subst hz; exact lt_irrefl _ H
    · rw [EReal.top_mul_of_pos hw] at H; exact not_top_lt H
-- `ENNReal.ereal_smul_distr_le_left` idx 3
theorem w2_27 : ¬ drop0% ENNReal.ereal_smul_distr_le_left 3 := by
  intro h; have := @h ⊤ ⊥ ((-1:ℝ):EReal) (EReal.coe_lt_top _)
  rw [EReal.coe_mul_bot_of_neg (by norm_num), EReal.coe_mul_top_of_neg (by norm_num)] at this
  simp at this
-- `ENNReal.ereal_smul_distr_le_left` idx 4
theorem w2_28 : ¬ drop0% ENNReal.ereal_smul_distr_le_left 4 := by
  intro h; have := @h ((1:ℝ):EReal) ((-1:ℝ):EReal) ⊤ (by simp)
  have e : ((1:ℝ):EReal) + ((-1:ℝ):EReal) = 0 := by rw [← EReal.coe_add]; norm_num
  rw [e, mul_zero, EReal.top_mul_of_neg (x := ((-1:ℝ):EReal)) (by exact_mod_cast (by norm_num : (-1:ℝ) < 0)), EReal.top_mul_of_pos (x := ((1:ℝ):EReal)) (by exact_mod_cast (by norm_num : (0:ℝ) < 1))] at this
  simp at this
-- `ENNReal.ereal_le_smul_left` idx 3
theorem w2_29 : ¬ drop0% ENNReal.ereal_le_smul_left 3 := by
  intro h; have := @h 0 1 ((-1:ℝ):EReal) (EReal.coe_lt_top _) zero_le_one
  rw [mul_zero, mul_one] at this
  exact absurd this (not_le.2 (by exact_mod_cast (by norm_num : (-1:ℝ) < 0)))
-- `ENNReal.galois_connection_smul_l` idx 2
theorem w2_30 : ¬ drop0% ENNReal.galois_connection_smul_l 2 := by
  intro h; have := (@h ⊤ (by simp) 1 ⊤).1 le_top
  simp [ENNReal.ofEReal_top] at this
  exact absurd this (not_le.2 zero_lt_one)
-- `SLang.ext` idx 3
theorem w2_31 : ¬ drop0% SLang.ext 3 := by
  intro h; have := congrFun (@h Unit (fun _ => 0) (fun _ => 1)) (); simp at this
-- `SLang.probWhile_apply` idx 6
theorem w2_32 : ¬ drop0% SLang.probWhile_apply 6 := by
  intro h
  have h0 := @h Unit (fun _ => false) (fun _ _ => 0) () () 0
  have h1 := @h Unit (fun _ => false) (fun _ _ => 0) () () 1
  rw [h0] at h1; exact zero_ne_one h1
-- `SLang.probBind_norm` idx 4
theorem w2_33 : ¬ drop0% SLang.probBind_norm 4 := by
  intro h; have := @h Unit Unit (fun _ => 0) (fun _ _ => 1) (by simp)
  simp [SLang.probBind] at this
-- `SLang.rpow_nonzero` idx 2
theorem w2_34 : ¬ drop0% SLang.rpow_nonzero 2 := by
  intro h; have := @h 0 1; simp at this
-- `SLang.UniformSample_apply` idx 2
theorem w2_35 : ¬ drop0% SLang.UniformSample_apply 2 := by
  intro h; have := @h 1 1; rw [SLang.UniformSample_apply_out 1 1 (le_refl _)] at this; simp at this
-- `SLang.UniformSample_apply_out` idx 2
theorem w2_36 : ¬ drop0% SLang.UniformSample_apply_out 2 := by
  intro h; have := @h 1 0; rw [SLang.UniformSample_apply 1 0 (by simp)] at this; simp at this
-- `SLang.UniformSample_apply_ite` idx 3
theorem w2_37 : ¬ drop0% SLang.UniformSample_apply_ite 3 := by
  intro h; have := @h 1 2 1; simp only [show (1:ℕ) < 2 from by norm_num, if_true] at this
  rw [SLang.UniformSample_apply_out 1 1 (le_refl _)] at this; simp at this
-- `SLang.gamma_extract'` idx 3
theorem w2_38 : drop% SLang.gamma_extract' 3 := by
  intro num den x h2
  by_cases h1 : x = 0
  · subst h1
    by_cases hn : num = 0
    · subst hn; simp
    · have : (num : ENNReal) / (den : ENNReal) ≠ 0 := by
        rw [ne_eq, ENNReal.div_eq_zero_iff]; push_neg; exact ⟨by exact_mod_cast hn, ENNReal.natCast_ne_top _⟩
      simp [ENNReal.div_zero, hn, ENNReal.mul_top this, ENNReal.natCast_ne_top]
  · exact SLang.gamma_extract' num den x h1 h2
-- `SLang.gamma_extract` idx 3
theorem w2_39 : drop% SLang.gamma_extract 3 := by
  intro num den n
  by_cases h : n > 1
  · exact SLang.gamma_extract num den n h
  · have : n - 2 = 0 := by omega
    simp [this]
-- `SLang.ENNReal_Real_mul_absorb` idx 2
theorem w2_40 : ¬ drop0% SLang.ENNReal_Real_mul_absorb 2 := by
  intro h; have := @h 1 (-1); rw [ENNReal.ofReal_of_nonpos (by norm_num)] at this; simp at this
-- `exists_summable_bound_exp_mul_sq` idx 1
theorem w2_41 : ¬ drop0% exists_summable_bound_exp_mul_sq 1 := by
  intro h; obtain ⟨bd, hs, hb⟩ := @h 0
  have h1 : ∀ n, (1:ℝ) ≤ bd n := fun n => by have := @hb 0 (by simp) n; simpa using this
  have := hs.tendsto_cofinite_zero
  have h2 : ∀ᶠ n in cofinite, bd n < 1 := this.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨n, hn⟩ := h2.exists
  linarith [h1 n]
-- `summable_exp_mul_sq` idx 1
theorem w2_42 : ¬ drop0% summable_exp_mul_sq 1 := by
  intro h; have := @h 0; simp [summable_const_iff] at this

end W1c2_s2

section W1c2_s3
open Classical Real Filter Asymptotics FourierTransform

namespace W1c2
theorem gc0 : (gauss_term_ℂ 0 0 : ℝ → ℂ) = fun _ => 1 := by
  funext x; simp [gauss_term_ℂ, gauss_term_ℝ]
theorem F0 : 𝓕 (gauss_term_ℂ 0 0 : ℝ → ℂ) = 0 := by
  funext w
  rw [Real.fourier_real_eq, gc0]
  apply MeasureTheory.integral_undef
  intro hi
  have h2 := hi.norm
  have e : (fun v : ℝ => ‖Real.fourierChar (-(v * w)) • (fun _ => (1:ℂ)) v‖) = fun _ => (1:ℝ) := by
    funext v; simp
  rw [e, MeasureTheory.integrable_const_iff] at h2
  rcases h2 with h2 | h2
  · exact one_ne_zero h2
  · have := h2.measure_univ_lt_top; rw [Real.volume_univ] at this; exact lt_irrefl _ this
theorem fgt0 : fourier_gauss_term 0 = 0 := by
  funext x; simp [fourier_gauss_term]
end W1c2

-- `fourier_gauss_term_correspondance` idx 1
theorem w2_43 : drop% fourier_gauss_term_correspondance 1 := by
  intro σ
  by_cases h : σ = 0
  · subst h; rw [W1c2.F0, W1c2.fgt0]
  · exact fourier_gauss_term_correspondance h
-- `asymptotics_fourier_gauss_term` idx 1
theorem w2_44 : drop% asymptotics_fourier_gauss_term 1 := by
  intro σ
  by_cases h : σ = 0
  · subst h; rw [W1c2.F0]; exact isBigO_zero _ _
  · exact asymptotics_fourier_gauss_term h
-- `poisson_gauss_term` idx 1
theorem w2_45 : drop% poisson_gauss_term 1 := by
  intro σ x
  by_cases h : σ = 0
  · subst h; rw [W1c2.F0]; simp [W1c2.gc0]
  · exact poisson_gauss_term h x
-- `summable_fourier_gauss_term` idx 1
theorem w2_46 : drop% summable_fourier_gauss_term 1 := by
  intro σ
  by_cases h : σ = 0
  · subst h; rw [W1c2.F0]; exact summable_zero
  · exact summable_fourier_gauss_term h
-- `summable_fourier_gauss_term'` idx 1
theorem w2_47 : drop% summable_fourier_gauss_term' 1 := by
  intro σ μ
  by_cases h : σ = 0
  · subst h; rw [W1c2.F0]; simp
  · exact summable_fourier_gauss_term' h μ
-- `fourier_coeff_correspondance` idx 1
theorem w2_48 : drop% fourier_coeff_correspondance 1 := by
  intro σ n
  by_cases h : σ = 0
  · subst h
    have e : (gauss_series_circle 0 : UnitAddCircle → ℂ) = 0 := by
      funext t
      induction t using QuotientAddGroup.induction_on with
      | H x =>
        have e1 : ∀ n : ℤ, (gauss_term_ℂ 0 0).comp (ContinuousMap.addRight (n:ℝ)) = 1 := fun n => by
          ext y; simp [gauss_term_ℂ, gauss_term_ℝ]
        simp [gauss_series_circle, Function.Periodic.lift_coe, e1, tsum_const]
    rw [e, W1c2.F0]; simp [fourierCoeff]
  · exact fourier_coeff_correspondance h n
-- `asymptotics_gauss_term` idx 1
theorem w2_49 : ¬ drop0% asymptotics_gauss_term 1 := by
  intro h
  have h0 := @h 0
  rw [W1c2.gc0] at h0
  have t : Tendsto (fun x : ℝ => |x| ^ (-2:ℝ)) (cocompact ℝ) (nhds 0) := by
    exact (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 2)).comp tendsto_norm_cocompact_atTop
  have := h0.trans_tendsto t
  exact one_ne_zero (tendsto_const_nhds_iff.1 this)
-- `SLang.mass'_series_converges'` idx 1
theorem w2_50 : ¬ drop0% SLang.mass'_series_converges' 1 := by
  intro h; apply h ⊤; apply eq_top_iff.2
  refine le_trans ?_ (ENNReal.le_tsum 0); simp [SLang.mass']
-- `SLang.mass'_series_converges'_odd` idx 1
theorem w2_51 : ¬ drop0% SLang.mass'_series_converges'_odd 1 := by
  intro h; apply h ⊤; apply eq_top_iff.2
  refine le_trans ?_ (ENNReal.le_tsum 0); simp [SLang.mass']
-- `SLang.mass'_series_exp'` idx 1
theorem w2_52 : ¬ drop0% SLang.mass'_series_exp' 1 := by
  intro h; have := h ⊤
  have h2 : (⊤ : ENNReal) ≤ ∑' (i : ℕ), SLang.mass' i ⊤ := by
    refine le_trans ?_ (ENNReal.le_tsum 1); simp [SLang.mass']
  rw [this] at h2; simp at h2
-- `SLang.mass_simpl` idx 2
theorem w2_53 : ¬ drop0% SLang.mass_simpl 2 := by
  intro h; have := h 0 0; simp [SLang.mass, SLang.mass'] at this
-- `SLang.mass'_antitone` idx 2
theorem w2_54 : ¬ drop0% SLang.mass'_antitone 2 := by
  intro h; have := h 0 2; simp [SLang.mass'] at this
-- `SLang.mass'_series_converges'_sub` idx 2
theorem w2_55 : drop% SLang.mass'_series_converges'_sub 2 := by
  intro γ h1
  have hall : ∑' (n : ℕ), SLang.mass' n γ ≠ ⊤ := by
    rw [SLang.mass'_series_exp' γ h1]; exact ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top hall (le_trans (ENNReal.tsum_le_tsum fun n => tsub_le_self) ?_)
  exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℕ => 2 * n) (fun a b hab => by simpa using hab) (fun n => SLang.mass' n γ)
-- `SLang.probUniformByteUpperBits_eval_zero` idx 2
theorem w2_56 : ¬ drop0% SLang.probUniformByteUpperBits_eval_zero 2 := by
  intro h; have := @h 0 0
  rw [SLang.probUniformByteUpperBits_eval_support (by norm_num)] at this
  norm_num [UInt8.size] at this
-- `SLang.partial_geometric_series` idx 1
theorem w2_57 : ¬ drop0% SLang.partial_geometric_series 1 := by
  intro h; have := @h 1 1
  rw [tsum_eq_single 0 (fun b hb => by simp [Nat.lt_one_iff, hb])] at this
  simp at this
-- `SLang.probGeometric_normalizes'` idx 1
theorem w2_58 : ¬ drop0% SLang.probGeometric_normalizes' 1 := by
  intro h; have := h 0 (by simp); simp at this
-- `SLang.probGeometric_normalizes'` idx 2
theorem w2_59 : ¬ drop0% SLang.probGeometric_normalizes' 2 := by
  intro h; have := h (fun b => if b then 1 else 0) (by simp); simp at this

end W1c2_s3

section W1c2_s4
open Classical Real Filter Asymptotics FourierTransform

namespace W1c2
theorem mass_top (n : ℕ) : SLang.mass n ⊤ = 0 := by
  unfold SLang.mass
  have : ((n:ENNReal) - 1)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.2 (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) tsub_le_self)
  rw [ENNReal.top_mul this]; simp
theorem two_sub_one : (2:ENNReal) - 1 = 1 := ENNReal.sub_eq_of_eq_add ENNReal.one_ne_top one_add_one_eq_two.symm
end W1c2

-- `SLang.BernoulliExpNegSampleUnitAux_apply'` idx 4
theorem w2_60 : ¬ drop0% SLang.BernoulliExpNegSampleUnitAux_apply' 4 := by
  intro h; have := h 0 1 0 (Nat.zero_le _) 0 (by simp)
  rw [SLang.BernoulliExpNegSampleUnitAux_at_zero] at this; simp [SLang.mass] at this
-- `SLang.BernoulliExpNegSampleUnitAux_apply'` idx 6
theorem w2_61 : ¬ drop0% SLang.BernoulliExpNegSampleUnitAux_apply' 6 := by
  intro h
  have h0 := h 0 1 2 (Nat.zero_le _) (by norm_num) 0
  have h1 := h 0 1 2 (Nat.zero_le _) (by norm_num) 1
  rw [h0] at h1; norm_num [SLang.mass] at h1; rw [W1c2.two_sub_one] at h1; simp at h1
-- `SLang.if_ge_2` idx 5
theorem w2_62 : ¬ drop0% SLang.if_ge_2 5 := by
  intro h
  have h0 := @h 0 2 0 1 (Nat.zero_le _)
  have h1 := @h 1 2 0 1 (Nat.zero_le _)
  rw [h0] at h1; norm_num [SLang.mass] at h1; rw [W1c2.two_sub_one] at h1; simp at h1
-- `SLang.series_step_1` idx 4
theorem w2_63 : ¬ drop0% SLang.series_step_1 4 := by
  intro h
  have h0 := h 0 1 (Nat.zero_le _) 0
  have h1 := h 0 1 (Nat.zero_le _) ⊤
  rw [h0] at h1
  simp only [W1c2.mass_top, tsum_zero] at h1
  rw [tsum_eq_single 0 (fun b hb => by simp [SLang.mass]; omega)] at h1
  simp [SLang.mass] at h1
-- `SLang.BernoulliExpNegSampleUnit_apply_false` idx 4
theorem w2_64 : ¬ drop0% SLang.BernoulliExpNegSampleUnit_apply_false 4 := by
  intro h
  have h0 := h 0 1 (Nat.zero_le _) 0
  have h1 := h 0 1 (Nat.zero_le _) 1
  rw [h0] at h1; simp at h1
  have : ENNReal.ofReal (Real.exp (-1)) < 1 := ENNReal.ofReal_lt_one.2 (Real.exp_lt_one_iff.2 (by norm_num))
  have h2 := tsub_pos_of_lt this
  rw [← h1] at h2; exact lt_irrefl _ h2
-- `SLang.δ_normalizes` idx 5
theorem w2_65 : ¬ drop0% SLang.δ_normalizes 5 := by
  intro h
  have := @h Unit Unit 0 id () (by simp)
  have e : SLang.δ (0 : SLang Unit) id () = 0 := by funext x; simp [SLang.δ]
  rw [e] at this; exact zero_ne_one (hasSum_zero.unique this)
-- `SLang.δ_normalizes` idx 6
theorem w2_66 : ¬ drop0% SLang.δ_normalizes 6 := by
  intro h
  haveI : Infinite ↑{n : ℕ | () = (fun _ : ℕ => ()) n} :=
    Set.infinite_coe_iff.2 (by simpa using Set.infinite_univ (α := ℕ))
  have s : ∑' (i : ↑{n : ℕ | () = (fun _ : ℕ => ()) n}), (fun _ : ℕ => (1:ENNReal)) ↑i = ⊤ :=
    ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  have := @h ℕ Unit (fun _ => 1) (fun _ => ()) () (by rw [s]; simp)
  have e : SLang.δ (fun _ : ℕ => (1:ENNReal)) (fun _ => ()) () = 0 := by
    funext x; simp only [SLang.δ]; rw [s]; simp
  rw [e] at this; exact zero_ne_one (hasSum_zero.unique this)
-- `SLang.convergent_subset` idx 5
theorem w2_67 : ¬ drop0% SLang.convergent_subset 5 := by
  intro h
  haveI : Infinite ↑{n : ℕ | () = (fun _ : ℕ => ()) n} :=
    Set.infinite_coe_iff.2 (by simpa using Set.infinite_univ (α := ℕ))
  exact @h ℕ Unit () (fun _ => 1) (fun _ => ()) (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero)
-- `SLang.DiscreteLaplaceSampleLoopIn1_apply` idx 2
theorem w2_68 : ¬ drop0% SLang.DiscreteLaplaceSampleLoopIn1_apply 2 := by
  intro h; have := h 1 1
  rw [SLang.DiscreteLaplaceSampleLoopIn1_apply_pre, SLang.DiscreteLaplaceSampleLoopIn1Aux_apply_true] at this
  simp at this
  have e : Real.exp (-1) ≠ 1 := by
    intro e; have := Real.exp_eq_one_iff (-1) |>.1 e; norm_num at this
  have e2 : 1 - Real.exp (-1) ≠ 0 := sub_ne_zero.2 (Ne.symm e)
  rw [div_self e2] at this
  linarith [Real.exp_pos (-1)]
-- `SLang.geometric_monotone_counter` idx 5
theorem w2_69 : ¬ drop0% SLang.geometric_monotone_counter 5 := by
  intro h
  have h0 := h (fun _ => 1) 2 1 (true, 0) (by simp)
  have h1 := SLang.geometric_progress (fun _ => 1) 0 0
  simp only [zero_add, pow_zero, one_mul] at h1; rw [h0] at h1; exact zero_ne_one h1
-- `SLang.geometric_preservation` idx 4
theorem w2_70 : ¬ drop0% SLang.geometric_preservation 4 := by
  intro h
  have h0 := h (fun _ => 1) 0 1 0
  have h1 := SLang.geometric_progress (fun _ => 1) 1 0
  simp only [Nat.reduceAdd, zero_add, add_zero, pow_one, mul_one] at h1 h0
  rw [h1] at h0
  simp [SLang.geometric_succ_true, SLang.geometric_succ_false] at h0
-- `SLang.geometric_preservation'` idx 4
theorem w2_71 : ¬ drop0% SLang.geometric_preservation' 4 := by
  intro h
  have h0 := h (fun _ => 1) 1 2 (by norm_num)
  have h1 := SLang.geometric_progress (fun _ => 1) 1 0
  simp only [Nat.reduceAdd, zero_add, add_zero, pow_one, mul_one] at h1 h0
  rw [h1] at h0
  simp [SLang.geometric_succ_true, SLang.geometric_succ_false] at h0
-- `SLang.BernoulliExpNegSampleUnitAux_preservation'` idx 6
theorem w2_72 : ¬ drop0% SLang.BernoulliExpNegSampleUnitAux_preservation' 6 := by
  intro h
  have h0 := h 0 1 1 2 (Nat.zero_le _) (by norm_num)
  simp [SLang.BernoulliExpNegSampleUnitAux_succ_true, SLang.BernoulliExpNegSampleUnitAux_succ_false] at h0
  exact h0 rfl
-- `SLang.BernoulliExpNegSampleUnitAux_preservation` idx 6
theorem w2_73 : ¬ drop0% SLang.BernoulliExpNegSampleUnitAux_preservation 6 := by
  intro h
  have h0 := h 1 1 0 1 0 (Nat.le_of_eq (rfl : (1:ℕ) = ((1:ℕ+):ℕ)))
  rw [show 1 + 0 + 2 = Nat.succ (Nat.succ (Nat.succ 0)) from rfl, show 0 + 2 = Nat.succ (Nat.succ 0) from rfl] at h0
  simp only [SLang.BernoulliExpNegSampleUnitAux_succ_true, SLang.BernoulliExpNegSampleUnitAux_succ_false,
    SLang.BernoulliExpNegSampleUnitAux_zero] at h0
  simp [SLang.plus_one, SLang.plus_two] at h0
  exact h0 rfl

end W1c2_s4

section W1c2_s5
open SLang ENNReal

namespace W1c2
open SLang
open SLang

theorem sq_rpow_half (x : ENNReal) : (x ^ 2) ^ (1/2 : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem sq_rpow_inv_two (x : ENNReal) : (x ^ 2) ^ (2⁻¹ : ℝ) = x := by
  rw [← one_div]; exact sq_rpow_half x

theorem five_inv : (5 : ENNReal) * 5⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- masses (9/25, 16/25) for the empty list and (16/25, 9/25) otherwise, written as squares -/
noncomputable def sf (l : List Unit) (x : Bool) : ENNReal :=
  if (l = []) = x then (3 * 5⁻¹) ^ 2 else (4 * 5⁻¹) ^ 2

theorem sf_sum (l : List Unit) : HasSum (sf l) 1 := by
  have h : ∑ b, sf l b = 1 := by
    rw [Fintype.sum_bool]
    unfold sf
    have e : ((3:ENNReal) * 5⁻¹) ^ 2 + (4 * 5⁻¹) ^ 2 = (5 * 5⁻¹) ^ 2 := by ring
    by_cases hl : l = [] <;> simp [hl, e, add_comm, five_inv]
  rw [← h]; exact hasSum_fintype _

theorem sf_ne (l : List Unit) (x : Bool) : sf l x ≠ 0 := by
  unfold sf; split <;> simp
open SLang

/-- restriction of a PMF to a set containing its support -/
noncomputable def restr {T : Type} (p : PMF T) (s : Set T) (h : Function.support p ⊆ s) : PMF s :=
  ⟨(⇑p) ∘ (↑), (hasSum_subtype_iff_of_support_subset h).2 (PMF.hasSum_coe_one p)⟩

theorem restr_apply {T : Type} (p : PMF T) (s : Set T) (h : Function.support p ⊆ s) (x : s) :
    restr p s h x = p x := rfl

theorem supp_sub {T : Type} (p q : PMF T) (hac : AbsCts p q) : Function.support p ⊆ q.support := by
  intro x hx; rw [PMF.mem_support_iff]; exact fun h => hx (hac x h)

theorem renyi_restr {T : Type} (p q : PMF T) (hac : AbsCts p q) {α : ℝ} (hα : 1 < α) :
    RenyiDivergence_def p q α =
      RenyiDivergence_def (restr p q.support (supp_sub p q hac)) (restr q q.support subset_rfl) α := by
  unfold RenyiDivergence_def
  congr 2
  refine (tsum_subtype_eq_of_support_subset (s := q.support) ?_).symm
  intro x hx
  rw [PMF.mem_support_iff]
  intro hq
  apply hx
  simp only [hq, hac x hq]
  rw [ENNReal.zero_rpow_of_pos (by linarith), zero_mul]

theorem ac_restr {T : Type} (p q : PMF T) (hac : AbsCts p q) :
    AbsCts (restr p q.support (supp_sub p q hac)) (restr q q.support subset_rfl) :=
  fun x hx => hac x hx

theorem restr_eq_iff {T : Type} (p q : PMF T) (hac : AbsCts p q) :
    restr p q.support (supp_sub p q hac) = restr q q.support subset_rfl ↔ p = q := by
  constructor
  · intro he
    ext x
    by_cases hx : x ∈ q.support
    · have := congrArg (fun r : PMF q.support => r ⟨x, hx⟩) he
      exact this
    · rw [PMF.mem_support_iff, not_not] at hx
      rw [hx, hac x hx]
  · rintro rfl; rfl

open SLang
open scoped Classical

theorem pp_apply {T U V : Type} (nq : SLang.Mechanism T U) (f : U → V) (l : List T) (v : V) :
    (SLang.privPostProcess nq f l).1 v = ∑' a, if v = f a then (nq l).1 a else 0 := by
  simp [privPostProcess, Bind.bind, Pure.pure, probBind, probPure]

theorem renyi_restr2 {U : Type} (p q : PMF U) (s : Set U) (hp : Function.support p ⊆ s)
    (hq : Function.support q ⊆ s) {α : ℝ} (hα : 1 < α) :
    RenyiDivergence (restr p s hp) (restr q s hq) α = RenyiDivergence p q α := by
  unfold RenyiDivergence RenyiDivergence_def
  congr 3
  refine tsum_subtype_eq_of_support_subset (s := s) (f := fun x => p x ^ α * q x ^ (1 - α)) ?_
  intro x hx
  by_contra hxs
  apply hx
  have h1 : p x = 0 := by by_contra h; exact hxs (hp (Function.mem_support.2 h))
  have h2 : q x = 0 := by by_contra h; exact hxs (hq (Function.mem_support.2 h))
  simp only [h1]
  rw [ENNReal.zero_rpow_of_pos (by linarith), zero_mul]

/-- an SPMF seen as a PMF -/
def toP {U : Type} (x : SLang.SPMF U) : PMF U := ⟨x.1, x.2⟩

/-- the union of the supports of two outputs of a mechanism -/
def pset {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) : Set U :=
  PMF.support (toP (m l₁)) ∪ PMF.support (toP (m l₂))

theorem pset_countable {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) :
    Countable (pset m l₁ l₂) :=
  ((PMF.support_countable _).union (PMF.support_countable _)).to_subtype

theorem sub1 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) :
    Function.support (toP (m l₁)) ⊆ pset m l₁ l₂ := Set.subset_union_left

theorem sub2 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) :
    Function.support (toP (m l₂)) ⊆ pset m l₁ l₂ := Set.subset_union_right

/-- the mechanism restricted to pset: the output for l₂ at l₂, the output for l₁ elsewhere -/
noncomputable def mresP {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (l : List T) :
    PMF (pset m l₁ l₂) :=
  if l = l₂ then restr (toP (m l₂)) (pset m l₁ l₂) (sub2 m l₁ l₂)
  else restr (toP (m l₁)) (pset m l₁ l₂) (sub1 m l₁ l₂)

theorem mresP_eq {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) :
    mresP m l₁ l₂ l₂ = restr (toP (m l₂)) (pset m l₁ l₂) (sub2 m l₁ l₂) := if_pos rfl

theorem mresP_ne {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ l : List T) (h : l ≠ l₂) :
    mresP m l₁ l₂ l = restr (toP (m l₁)) (pset m l₁ l₂) (sub1 m l₁ l₂) := if_neg h

noncomputable def mres {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) :
    SLang.Mechanism T (pset m l₁ l₂) := fun l => ⟨(mresP m l₁ l₂ l).1, (mresP m l₁ l₂ l).2⟩

theorem mres_val1 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (x : pset m l₁ l₂) :
    (mres m l₁ l₂ l₁).1 x = (m l₁).1 x.1 := by
  show (mresP m l₁ l₂ l₁) x = _
  by_cases h : l₁ = l₂
  · subst h; rw [mresP_eq]; rfl
  · rw [mresP_ne _ _ _ _ h]; rfl

theorem mres_val2 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (x : pset m l₁ l₂) :
    (mres m l₁ l₂ l₂).1 x = (m l₂).1 x.1 := by
  show (mresP m l₁ l₂ l₂) x = _
  rw [mresP_eq]; rfl

theorem renyi_self {S : Type} [Countable S] (P : PMF S) {α : ℝ} (hα : 1 < α) :
    RenyiDivergence P P α = 0 :=
  (@RenyiDivergence_aux_zero S ⊤ _ _ P P α hα (fun x h => h)).1 rfl

theorem mres_zcdp {T U : Type} (m : SLang.Mechanism T U) (ε : ℝ) (h : SLang.zCDPBound m ε)
    (l₁ l₂ : List T) (hN : Neighbour l₁ l₂) : SLang.zCDPBound (mres m l₁ l₂) ε := by
  have := pset_countable m l₁ l₂
  intro α hα a b _
  show RenyiDivergence (mresP m l₁ l₂ a) (mresP m l₁ l₂ b) α ≤ _
  by_cases ha : a = l₂ <;> by_cases hb : b = l₂
  · rw [ha, hb, renyi_self _ hα]; exact zero_le
  · rw [ha, mresP_eq, mresP_ne _ _ _ _ hb, renyi_restr2 _ _ _ _ _ hα]
    exact h α hα l₂ l₁ (Neighbour_symm _ _ hN)
  · rw [hb, mresP_eq, mresP_ne _ _ _ _ ha, renyi_restr2 _ _ _ _ _ hα]
    exact h α hα l₁ l₂ hN
  · rw [mresP_ne _ _ _ _ ha, mresP_ne _ _ _ _ hb, renyi_self _ hα]; exact zero_le

theorem mres_ac {T U : Type} (m : SLang.Mechanism T U) (h : SLang.ACNeighbour m)
    (l₁ l₂ : List T) (hN : Neighbour l₁ l₂) : SLang.ACNeighbour (mres m l₁ l₂) := by
  intro a b _ x hx
  change (mresP m l₁ l₂ b) x = 0 at hx
  show (mresP m l₁ l₂ a) x = 0
  by_cases ha : a = l₂ <;> by_cases hb : b = l₂
  · rw [ha]; rw [hb] at hx; exact hx
  · rw [ha, mresP_eq]; rw [mresP_ne _ _ _ _ hb] at hx; exact h l₂ l₁ (Neighbour_symm _ _ hN) x.1 hx
  · rw [mresP_ne _ _ _ _ ha]; rw [hb, mresP_eq] at hx; exact h l₁ l₂ hN x.1 hx
  · rw [mresP_ne _ _ _ _ ha]; rw [mresP_ne _ _ _ _ hb] at hx; exact hx

theorem supp_ite1 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (P : U → Prop) :
    Function.support (fun a => if P a then (m l₁).1 a else 0) ⊆ pset m l₁ l₂ := by
  intro a ha
  apply sub1 m l₁ l₂
  rw [Function.mem_support] at ha ⊢
  intro h0; apply ha
  change (m l₁).1 a = 0 at h0
  simp [h0]

theorem supp_ite2 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (P : U → Prop) :
    Function.support (fun a => if P a then (m l₂).1 a else 0) ⊆ pset m l₁ l₂ := by
  intro a ha
  apply sub2 m l₁ l₂
  rw [Function.mem_support] at ha ⊢
  intro h0; apply ha
  change (m l₂).1 a = 0 at h0
  simp [h0]

theorem pp_mres1 {T U V : Type} (m : SLang.Mechanism T U) (f : U → V) (l₁ l₂ : List T) :
    SLang.privPostProcess (mres m l₁ l₂) (f ∘ Subtype.val) l₁ = SLang.privPostProcess m f l₁ := by
  apply Subtype.ext; funext v
  rw [pp_apply, pp_apply]
  simp only [Function.comp, mres_val1]
  exact tsum_subtype_eq_of_support_subset (supp_ite1 m l₁ l₂ (fun a => v = f a))

theorem pp_mres2 {T U V : Type} (m : SLang.Mechanism T U) (f : U → V) (l₁ l₂ : List T) :
    SLang.privPostProcess (mres m l₁ l₂) (f ∘ Subtype.val) l₂ = SLang.privPostProcess m f l₂ := by
  apply Subtype.ext; funext v
  rw [pp_apply, pp_apply]
  simp only [Function.comp, mres_val2]
  exact tsum_subtype_eq_of_support_subset (supp_ite2 m l₁ l₂ (fun a => v = f a))

/-- deterministic mechanism: true on the empty list, false otherwise -/
noncomputable def mech2 : SLang.Mechanism Unit Bool := fun l => ⟨⇑(PMF.pure (l == [])), PMF.hasSum_coe_one _⟩

/-- PMF version of sf -/
noncomputable def sfP (l : List Unit) : PMF Bool := ⟨sf l, sf_sum l⟩
end W1c2

-- `SLang.privPostPocess_DP_pre` idx 7
theorem w2_74 : drop% SLang.privPostPocess_DP_pre 7 := by
  intro T U V inst cnt dms nq f α h1 l₁ l₂ HN Habs Habs'
  exact SLang.privPostPocess_DP_pre (fun l => PMF.hasSum_coe_one (nq l)) f h1 HN Habs Habs'
-- `SLang.privPostPocess_DP_pre` idx 5
theorem w2_75 : drop% SLang.privPostPocess_DP_pre 5 := by
  intro T U V inst cnt
  exact @SLang.privPostPocess_DP_pre T U V ⊤ cnt _
-- `SLang.privPostProcess_zCDPBound` idx 5
theorem w2_76 : drop% SLang.privPostProcess_zCDPBound 5 := by
  intro T U V inst cnt
  exact @SLang.privPostProcess_zCDPBound T U V ⊤ cnt _
-- `SLang.privPostProcess_zCDP` idx 5
theorem w2_77 : drop% SLang.privPostProcess_zCDP 5 := by
  intro T U V inst cnt
  exact @SLang.privPostProcess_zCDP T U V ⊤ cnt _
-- `SLang.privPostPocess_DP_pre` idx 14
theorem w2_78 : drop% SLang.privPostPocess_DP_pre 14 := by
  intro T U V inst cnt dms nq HNorm f α h1 l₁ l₂ HN Habs'
  by_cases Habs : AbsCts (nq l₁) (nq l₂)
  · exact SLang.privPostPocess_DP_pre HNorm f h1 HN Habs Habs'
  · simp only [AbsCts, not_forall] at Habs
    obtain ⟨x, hq, hp⟩ := Habs
    refine le_of_le_of_eq le_top (ENNReal.tsum_eq_top_of_eq_top ⟨x, ?_⟩).symm
    rw [hq, ENNReal.zero_rpow_of_neg (by linarith)]
    have hα : (0:ℝ) ≤ α := by linarith
    exact ENNReal.mul_top (by simp [ENNReal.rpow_eq_zero_iff, hp, hα])
-- `SLang.privPostPocess_DP_pre_reduct` idx 15
theorem w2_79 : drop% SLang.privPostPocess_DP_pre_reduct 15 := by
  intro T V U m2 cnt dms inh nq f α h1 l₁ l₂ HN1 HN2 Hnq2 h2
  by_cases Habs : AbsCts (nq l₁) (nq l₂)
  · exact SLang.privPostPocess_DP_pre_reduct f h1 HN1 HN2 Habs Hnq2 h2
  · simp only [AbsCts, not_forall] at Habs
    obtain ⟨x, hq, hp⟩ := Habs
    refine le_of_le_of_eq le_top (ENNReal.tsum_eq_top_of_eq_top ⟨x, ?_⟩).symm
    rw [hq, ENNReal.zero_rpow_of_neg (by linarith)]
    have hα : (0:ℝ) ≤ α := by linarith
    exact ENNReal.mul_top (by simp [ENNReal.rpow_eq_zero_iff, hp, hα])
-- `SLang.privPostPocess_DP_pre_reduct` idx 4
theorem w2_80 : drop% SLang.privPostPocess_DP_pre_reduct 4 := by
  intro T V U m2 dms inh nq f α h1 l₁ l₂ HN1 HN2 Habs Hnq2 h2
  have hsum : ∑' u, nq l₁ u ≠ ⊤ := by rw [HN1.tsum_eq]; exact ENNReal.one_ne_top
  have hs := Summable.countable_support_ennreal hsum
  have e : Function.support (nq l₁) = Set.univ := Set.eq_univ_of_forall fun u => Hnq2 u
  rw [e] at hs
  have hc : Countable U := Set.countable_univ_iff.1 hs
  exact SLang.privPostPocess_DP_pre_reduct f h1 HN1 HN2 Habs Hnq2 h2
-- `SLang.privPostProcess_zCDPBound` idx 4
theorem w2_81 : drop% SLang.privPostProcess_zCDPBound 4 := by
  intro T U V inst disc nq ε hb f hac α hα l₁ l₂ hN
  have := W1c2.pset_countable nq l₁ l₂
  have key := @SLang.privPostProcess_zCDPBound T (W1c2.pset nq l₁ l₂) V ⊤ _ _
    (W1c2.mres nq l₁ l₂) ε (W1c2.mres_zcdp nq ε hb l₁ l₂ hN) (f ∘ Subtype.val)
    (W1c2.mres_ac nq hac l₁ l₂ hN) α hα l₁ l₂ hN
  rw [W1c2.pp_mres1, W1c2.pp_mres2] at key
  exact key
-- `SLang.privPostProcess_zCDPBound` idx 10
theorem w2_82 : drop% SLang.privPostProcess_zCDPBound 10 := by
  intro T U V inst cnt dms nq ε h f
  refine SLang.privPostProcess_zCDPBound h f ?_
  intro l₁ l₂ hN x hx
  by_contra hpx
  have H := h 2 (by norm_num) l₁ l₂ hN
  unfold RenyiDivergence RenyiDivergence_def at H
  have key : ∀ (g : U → ENNReal), g x = ⊤ → ∑' y, g y = ⊤ := fun g hg => ENNReal.tsum_eq_top_of_eq_top ⟨x, hg⟩
  rw [key _ (by
    erw [hx, ENNReal.zero_rpow_of_neg (by norm_num)]
    exact ENNReal.mul_top (by simpa [ENNReal.rpow_eq_zero_iff] using hpx))] at H
  rw [ENNReal.elog_top] at H
  norm_num at H
-- `SLang.privPostProcess_AC` idx 5
theorem w2_83 : ¬ drop0% SLang.privPostProcess_AC 5 := by
  intro h
  have H := @h Unit Bool Bool id W1c2.mech2 [] [()] (Neighbour.Addition (a := []) (b := []) (n := ()) rfl rfl) true
  change (SLang.privPostProcess W1c2.mech2 id [()]).1 true = 0 → (SLang.privPostProcess W1c2.mech2 id []).1 true = 0 at H
  rw [W1c2.pp_apply, W1c2.pp_apply] at H
  simp [W1c2.mech2] at H
-- `SLang.privPostProcess_zCDP` idx 9
theorem w2_84 : ¬ drop0% SLang.privPostProcess_zCDP 9 := by
  intro h
  have H := (@h Unit Bool Bool _ _ _ id W1c2.mech2 0).1 [] [()] (Neighbour.Addition (a := []) (b := []) (n := ()) rfl rfl) true
  change (SLang.privPostProcess W1c2.mech2 id [()]).1 true = 0 → (SLang.privPostProcess W1c2.mech2 id []).1 true = 0 at H
  rw [W1c2.pp_apply, W1c2.pp_apply] at H
  simp [W1c2.mech2] at H


-- `SLang.privPostPocess_DP_pre` idx 10
theorem w2_85 : ¬ drop0% SLang.privPostPocess_DP_pre 10 := fun h => by
  have hac : ∀ l l' : List Unit, AbsCts ⇑(W1c2.sfP l) ⇑(W1c2.sfP l') :=
    fun l l' x hx => absurd hx (W1c2.sf_ne _ x)
  have h1 := @h Unit Bool Unit _ _ _ W1c2.sfP (fun l => PMF.hasSum_coe_one _) (fun _ => ()) (1/2) [] [()]
    (Neighbour.Addition (a := []) (b := []) (n := ()) rfl rfl) (hac _ _) (hac _ _)
  have e : ∀ l a, (W1c2.sfP l) a = W1c2.sf l a := fun _ _ => rfl
  simp only [e] at h1
  have hs : ∑ a, W1c2.sf [] a = 1 := by simpa [tsum_fintype] using (W1c2.sf_sum []).tsum_eq
  have hs' : ∑ a, W1c2.sf [()] a = 1 := by simpa [tsum_fintype] using (W1c2.sf_sum [()]).tsum_eq
  simp only [if_true, tsum_fintype, Finset.univ_unique, Finset.sum_singleton] at h1
  rw [hs, hs', Fintype.sum_bool] at h1
  have e2 : (1:ℝ) - 1/2 = 1/2 := by norm_num
  simp only [e2, ENNReal.one_rpow, W1c2.sf] at h1
  simp only [W1c2.sq_rpow_half, reduceCtorEq, if_true, if_false] at h1
  simp at h1
  rw [W1c2.sq_rpow_inv_two] at h1
  have e3 : (3 * 5⁻¹ * (4 * 5⁻¹) + 4 * 5⁻¹ * (3 * 5⁻¹) : ENNReal) = (5⁻¹)^2 * 24 := by ring
  have e4 : (1 : ENNReal) = (5⁻¹)^2 * 25 := by
    rw [show (5⁻¹ : ENNReal)^2 * 25 = (5 * 5⁻¹)^2 by ring, W1c2.five_inv, one_pow]
  have hlt : (5⁻¹ : ENNReal)^2 * 24 < (5⁻¹)^2 * 25 :=
    ENNReal.mul_lt_mul_right (by simp) (by simp) (by norm_num)
  rw [e3] at h1
  exact absurd (h1.trans_lt hlt) (by rw [← e4]; exact lt_irrefl _)
open scoped Classical in
-- `SLang.privPostPocess_DP_pre` idx 4
theorem w2_86 : drop% SLang.privPostPocess_DP_pre 4 := by
  intro T U V inst dms nq HNorm f α h1 l₁ l₂ HN Habs Habs'
  let s : Set U := (nq l₁).support ∪ (nq l₂).support
  have hc : Countable s := ((PMF.support_countable _).union (PMF.support_countable _)).to_subtype
  have h1s : Function.support (nq l₁) ⊆ s := Set.subset_union_left
  have h2s : Function.support (nq l₂) ⊆ s := Set.subset_union_right
  let nq' : List T → PMF s := fun l => if l = l₂ then W1c2.restr (nq l₂) s h2s else W1c2.restr (nq l₁) s h1s
  have v1 : ∀ x : s, nq' l₁ x = nq l₁ x := by
    intro x
    by_cases h : l₁ = l₂
    · simp only [nq', if_pos h]; subst h; rfl
    · simp only [nq', if_neg h]; rfl
  have v2 : ∀ x : s, nq' l₂ x = nq l₂ x := by
    intro x; simp only [nq', if_pos rfl]; rfl
  have key := @SLang.privPostPocess_DP_pre T s V ⊤ hc _ nq' (fun l => PMF.hasSum_coe_one _)
    (f ∘ Subtype.val) α h1 l₁ l₂ HN
    (fun x hx => by rw [v1]; rw [v2] at hx; exact Habs x hx)
    (fun x hx => by rw [v2]; rw [v1] at hx; exact Habs' x hx)
  simp only [v1, v2, Function.comp] at key
  have e1 : ∀ v : V, ∑' a : s, (if v = f a then nq l₁ a else 0) = ∑' a : U, if v = f a then nq l₁ a else 0 :=
    fun v => tsum_subtype_eq_of_support_subset (f := fun a => if v = f a then nq l₁ a else 0) (fun a ha => h1s (by
      rw [Function.mem_support] at ha ⊢; intro h0; apply ha; simp [h0]))
  have e2 : ∀ v : V, ∑' a : s, (if v = f a then nq l₂ a else 0) = ∑' a : U, if v = f a then nq l₂ a else 0 :=
    fun v => tsum_subtype_eq_of_support_subset (f := fun a => if v = f a then nq l₂ a else 0) (fun a ha => h2s (by
      rw [Function.mem_support] at ha ⊢; intro h0; apply ha; simp [h0]))
  have e3 : ∑' x : s, nq l₁ x ^ α * nq l₂ x ^ (1 - α) = ∑' x : U, nq l₁ x ^ α * nq l₂ x ^ (1 - α) :=
    tsum_subtype_eq_of_support_subset (f := fun x => nq l₁ x ^ α * nq l₂ x ^ (1 - α)) (by
      intro a ha; by_contra hn; apply ha
      have : nq l₁ a = 0 := by by_contra h; exact hn (h1s h)
      simp only [this]; rw [ENNReal.zero_rpow_of_pos (by linarith), zero_mul])
  simp only [e1, e2, e3] at key
  exact key

end W1c2_s5

section W1c2_s6
namespace W1c2
theorem sum_mass'' (x : ℝ) : ∑' n : ℕ, SLang.mass'' n x = Real.exp x := by
  unfold SLang.mass''
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp [div_eq_mul_inv]

theorem bad2 : ¬ (∑' (n : ℕ), (SLang.mass' (2 * n) 2 - SLang.mass' (2 * n + 1) 2)) ≤ ENNReal.ofReal (Real.exp (-2)) := by
  intro H
  have H1 := le_trans (ENNReal.le_tsum 1) H
  simp only [mul_one, Nat.reduceAdd] at H1
  have n2 : SLang.mass' 2 2 ≠ ⊤ := SLang.mass'_neq_top 2 2 (by simp)
  have n3 : SLang.mass' 3 2 ≠ ⊤ := SLang.mass'_neq_top 3 2 (by simp)
  have r2 : (SLang.mass' 2 2).toReal = 2 := by
    simp [SLang.mass', ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, Nat.factorial]; norm_num
  have r3 : (SLang.mass' 3 2).toReal = 4/3 := by
    simp [SLang.mass', ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, Nat.factorial]; norm_num
  have hle : SLang.mass' 3 2 ≤ SLang.mass' 2 2 := by
    rw [← ENNReal.toReal_le_toReal n3 n2, r2, r3]; norm_num
  have H2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top H1
  rw [ENNReal.toReal_sub_of_le hle n2, r2, r3, ENNReal.toReal_ofReal (Real.exp_pos _).le] at H2
  have e3 : (3:ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
  have : Real.exp (-2) ≤ 1/3 := by
    rw [Real.exp_neg]; rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) e3
  linarith
end W1c2

-- `SLang.series_step_4` idx 2
theorem w2_87 : ¬ drop0% SLang.series_step_4 2 := by
  intro h; have := h 2 (by simp)
  apply W1c2.bad2; rw [this]; simp
-- `SLang.series_step_4_pre` idx 2
theorem w2_88 : ¬ drop0% SLang.series_step_4_pre 2 := by
  intro h; have := h 2 (by simp)
  apply W1c2.bad2; rw [this, W1c2.sum_mass'']; simp

end W1c2_s6

section W1c2_s7
open SLang

namespace W1c2
open scoped Classical

theorem rpow_anti {x y : ENNReal} {z : ℝ} (hz : z ≤ 0) (hxy : x ≤ y) : y ^ z ≤ x ^ z := by
  have := ENNReal.rpow_le_rpow hxy (by linarith : 0 ≤ -z)
  rw [← neg_neg z, ENNReal.rpow_neg y (-z), ENNReal.rpow_neg x (-z)]
  exact ENNReal.inv_le_inv.2 this

/-- the reduct inequality for q of any finite nonzero mass (homogeneity in q) -/
theorem scaleA {U V : Type} [Countable U] [Inhabited U] (p q : U → ENNReal) (f : U → V) {α : ℝ}
    (h1 : 1 < α) (hp : HasSum p 1) (c : ENNReal) (hc : HasSum q c) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hac : AbsCts p q) (hnz : ∀ u, p u ≠ 0) :
    ∑' x : V, (∑' a, if x = f a then p a else 0) ^ α * (∑' a, if x = f a then q a else 0) ^ (1 - α)
      ≤ ∑' u, p u ^ α * q u ^ (1 - α) := by
  let nq : List Unit → SLang U := fun l => if l = [] then p else fun u => c⁻¹ * q u
  have hinv : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hc0
  have hinv0 : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hct
  have hq1 : HasSum (fun u => c⁻¹ * q u) 1 := by
    exact ENNReal.summable.hasSum_iff.2 (by rw [ENNReal.tsum_mul_left, hc.tsum_eq, ENNReal.inv_mul_cancel hc0 hct])
  have H := @SLang.privPostPocess_DP_pre_reduct Unit V U ⊤ _ _ _ nq f α h1 [] [()]
    (by simpa [nq] using hp) (by simpa [nq] using hq1)
    (by
      intro x hx
      simp only [nq, if_true, List.cons_ne_nil, if_false, reduceCtorEq] at hx ⊢
      rcases mul_eq_zero.1 hx with h | h
      · exact absurd h hinv0
      · exact hac x h)
    (by intro u; simpa [nq] using hnz u)
    (Neighbour.Addition (a := []) (b := []) (n := ()) rfl rfl)
  simp only [nq, if_true, List.cons_ne_nil, if_false, reduceCtorEq] at H
  have eQ : ∀ x, (∑' a, if x = f a then c⁻¹ * q a else 0) = c⁻¹ * ∑' a, (if x = f a then q a else 0) := by
    intro x; rw [← ENNReal.tsum_mul_left]; congr 1; funext a; split_ifs <;> simp
  have qfin : ∀ x, (∑' a, if x = f a then q a else 0) ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top (hc.tsum_eq ▸ hct) (ENNReal.tsum_le_tsum fun a => by split_ifs <;> simp)
  have qu : ∀ u, q u ≠ ⊤ := fun u => ne_top_of_le_ne_top (hc.tsum_eq ▸ hct) (ENNReal.le_tsum u)
  simp only [eQ, ENNReal.mul_rpow_of_ne_top hinv (qfin _), ENNReal.mul_rpow_of_ne_top hinv (qu _)] at H
  have e : ∀ (a b : ENNReal), a * (c⁻¹ ^ (1 - α) * b) = c⁻¹ ^ (1 - α) * (a * b) := fun a b => by ring
  simp only [e, ENNReal.tsum_mul_left] at H
  have hk0 : c⁻¹ ^ (1 - α) ≠ 0 := by simp [ENNReal.rpow_eq_zero_iff, hinv0, hinv]
  have hkt : c⁻¹ ^ (1 - α) ≠ ⊤ := by simp [ENNReal.rpow_eq_top_iff, hinv0, hinv]
  exact (ENNReal.mul_le_mul_iff_right hk0 hkt).1 H

/-- the reduct inequality without the nonvanishing hypothesis (restrict to the support of p) -/
theorem noNz {U V : Type} [Countable U] (p q : U → ENNReal) (f : U → V) {α : ℝ} (h1 : 1 < α)
    (hp : HasSum p 1) (hq : HasSum q 1) (hac : AbsCts p q) :
    ∑' x : V, (∑' a, if x = f a then p a else 0) ^ α * (∑' a, if x = f a then q a else 0) ^ (1 - α)
      ≤ ∑' u, p u ^ α * q u ^ (1 - α) := by
  let S := Function.support p
  obtain ⟨u0, hu0⟩ : ∃ u, p u ≠ 0 := by
    by_contra hne; push_neg at hne
    have := hp.tsum_eq; simp [hne] at this
  haveI : Inhabited S := ⟨⟨u0, hu0⟩⟩
  have hpS : HasSum (fun s : S => p s) 1 := (hasSum_subtype_iff_of_support_subset (subset_refl _)).2 hp
  have hc : HasSum (fun s : S => q s) (∑' s : S, q s) := ENNReal.summable.hasSum
  have hc0 : (∑' s : S, q s) ≠ 0 := by
    intro h0
    have := (ENNReal.tsum_eq_zero.1 h0) ⟨u0, hu0⟩
    exact hu0 (hac u0 this)
  have hct : (∑' s : S, q s) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (hq.tsum_eq ▸ ENNReal.one_ne_top) ?_
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective q
  have A := scaleA (fun s : S => p s) (fun s => q s) (fun s => f s) h1 hpS _ hc hc0 hct
    (fun x hx => hac x hx) (fun s => s.2)
  have eR : ∑' s : S, p s ^ α * q s ^ (1 - α) = ∑' u, p u ^ α * q u ^ (1 - α) :=
    tsum_subtype_eq_of_support_subset (f := fun u => p u ^ α * q u ^ (1 - α)) (by
      intro a ha; by_contra hn; apply ha
      have : p a = 0 := by by_contra h; exact hn h
      simp only [this]; rw [ENNReal.zero_rpow_of_pos (by linarith), zero_mul])
  rw [eR] at A
  refine le_trans (ENNReal.tsum_le_tsum fun x => ?_) A
  have eP : (∑' a : S, if x = f a then p a else 0) = ∑' a, if x = f a then p a else 0 :=
    tsum_subtype_eq_of_support_subset (f := fun a => if x = f a then p a else 0) (by
      intro a ha; rw [Function.mem_support] at ha ⊢; intro h0; apply ha; simp [h0])
  rw [eP]
  refine mul_le_mul_of_nonneg_left (rpow_anti (by linarith) ?_) zero_le
  exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun a => if x = f a then q a else 0)
/-- one-fiber Hölder: (∑ p)^α (∑ q)^(1-α) ≤ ∑ p^α q^(1-α) for finite nonzero masses -/
theorem fib {W : Type} [Countable W] (p q : W → ENNReal) {α : ℝ} (h1 : 1 < α)
    (hP0 : ∑' w, p w ≠ 0) (hPt : ∑' w, p w ≠ ⊤) (hQ0 : ∑' w, q w ≠ 0) (hQt : ∑' w, q w ≠ ⊤)
    (hac : AbsCts p q) :
    (∑' w, p w) ^ α * (∑' w, q w) ^ (1 - α) ≤ ∑' w, p w ^ α * q w ^ (1 - α) := by
  set P := ∑' w, p w with hPdef
  set Q := ∑' w, q w with hQdef
  have hPi : P⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hP0
  have hQi : Q⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hQ0
  have hp' : HasSum (fun w => P⁻¹ * p w) 1 :=
    ENNReal.summable.hasSum_iff.2 (by rw [ENNReal.tsum_mul_left, ← hPdef, ENNReal.inv_mul_cancel hP0 hPt])
  have hq' : HasSum (fun w => Q⁻¹ * q w) 1 :=
    ENNReal.summable.hasSum_iff.2 (by rw [ENNReal.tsum_mul_left, ← hQdef, ENNReal.inv_mul_cancel hQ0 hQt])
  have hac' : AbsCts (fun w => P⁻¹ * p w) (fun w => Q⁻¹ * q w) := by
    intro w hw
    rcases mul_eq_zero.1 hw with h | h
    · exact absurd h (ENNReal.inv_ne_zero.2 hQt)
    · simp [hac w h]
  have A := noNz (fun w => P⁻¹ * p w) (fun w => Q⁻¹ * q w) (fun _ => ()) h1 hp' hq' hac'
  simp only [if_true, tsum_fintype, Finset.univ_unique, Finset.sum_singleton] at A
  rw [hp'.tsum_eq, hq'.tsum_eq, ENNReal.one_rpow, ENNReal.one_rpow, one_mul] at A
  have qu : ∀ w, q w ≠ ⊤ := fun w => ne_top_of_le_ne_top hQt (ENNReal.le_tsum w)
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ α),
    ENNReal.mul_rpow_of_ne_top hQi (qu _)] at A
  have e : ∀ a b : ENNReal, P⁻¹ ^ α * a * (Q⁻¹ ^ (1 - α) * b) = (P⁻¹ ^ α * Q⁻¹ ^ (1 - α)) * (a * b) :=
    fun a b => by ring
  simp only [e, ENNReal.tsum_mul_left] at A
  have k1 : P ^ α * P⁻¹ ^ α = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ α), ENNReal.mul_inv_cancel hP0 hPt,
      ENNReal.one_rpow]
  have k2 : Q ^ (1 - α) * Q⁻¹ ^ (1 - α) = 1 := by
    rw [← ENNReal.mul_rpow_of_ne_top hQt hQi, ENNReal.mul_inv_cancel hQ0 hQt, ENNReal.one_rpow]
  calc P ^ α * Q ^ (1 - α) = P ^ α * Q ^ (1 - α) * 1 := (mul_one _).symm
    _ ≤ P ^ α * Q ^ (1 - α) * ((P⁻¹ ^ α * Q⁻¹ ^ (1 - α)) * ∑' w, p w ^ α * q w ^ (1 - α)) :=
        mul_le_mul_of_nonneg_left A zero_le
    _ = (P ^ α * P⁻¹ ^ α) * (Q ^ (1 - α) * Q⁻¹ ^ (1 - α)) * ∑' w, p w ^ α * q w ^ (1 - α) := by ring
    _ = ∑' w, p w ^ α * q w ^ (1 - α) := by rw [k1, k2, one_mul, one_mul]

/-- if p has infinite mass and q mass at most 1 (p ≪ q), then ∑ p^α q^(1-α) = ⊤ (Hölder via finite pieces) -/
theorem infmass {W : Type} [Countable W] (p q : W → ENNReal) {α : ℝ} (h1 : 1 < α)
    (hq : ∑' w, q w ≤ 1) (hac : AbsCts p q) (hP : ∑' w, p w = ⊤) :
    ∑' w, p w ^ α * q w ^ (1 - α) = ⊤ := by
  by_contra hS
  by_cases hA : ∃ w, p w = ⊤
  · obtain ⟨w, hw⟩ := hA
    apply hS; apply ENNReal.tsum_eq_top_of_eq_top ⟨w, ?_⟩
    have hqw : q w ≠ 0 := fun h0 => by rw [hac w h0] at hw; exact ENNReal.zero_ne_top hw
    have hqt : q w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.le_tsum w).trans hq)
    rw [hw, ENNReal.top_rpow_of_pos (by linarith)]
    exact ENNReal.top_mul (by simp [ENNReal.rpow_eq_zero_iff, hqw, hqt])
  push_neg at hA
  set S := ∑' w, p w ^ α * q w ^ (1 - α) with hSdef
  have hb : ∑' w, p w ≤ S ^ (1/α) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    by_cases h0 : ∑ w ∈ s, p w = 0
    · rw [h0]; exact zero_le
    have hPt : ∑ w ∈ s, p w ≠ ⊤ := ENNReal.sum_ne_top.2 fun w _ => hA w
    have hQs : ∑ w ∈ s, q w ≤ 1 := le_trans (ENNReal.sum_le_tsum s) hq
    have hQ0 : ∑ w ∈ s, q w ≠ 0 := by
      intro hz; apply h0
      rw [Finset.sum_eq_zero_iff] at hz ⊢
      intro w hw; exact hac w (hz w hw)
    have hQt : ∑ w ∈ s, q w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hQs
    have F := fib (fun w : s => p w) (fun w : s => q w) h1
      (by rw [Finset.tsum_subtype s p]; exact h0) (by rw [Finset.tsum_subtype s p]; exact hPt)
      (by rw [Finset.tsum_subtype s q]; exact hQ0) (by rw [Finset.tsum_subtype s q]; exact hQt)
      (fun w hw => hac w hw)
    rw [Finset.tsum_subtype s p, Finset.tsum_subtype s q] at F
    have F2 : (∑' w : s, p w ^ α * q w ^ (1 - α)) ≤ S :=
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun w => p w ^ α * q w ^ (1 - α))
    have one_le : 1 ≤ (∑ w ∈ s, q w) ^ (1 - α) := by
      have := rpow_anti (z := 1 - α) (by linarith) hQs; rwa [ENNReal.one_rpow] at this
    have G : (∑ w ∈ s, p w) ^ α ≤ S := le_trans (le_mul_of_one_le_right zero_le one_le) (F.trans F2)
    calc ∑ w ∈ s, p w = ((∑ w ∈ s, p w) ^ α) ^ (1/α) := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel (by linarith), ENNReal.rpow_one]
      _ ≤ S ^ (1/α) := ENNReal.rpow_le_rpow G (by positivity)
  rw [hP] at hb
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hS (top_le_iff.1 hb)
end W1c2

-- `SLang.privPostPocess_DP_pre_reduct` idx 16
theorem w2_89 : drop% SLang.privPostPocess_DP_pre_reduct 16 := by
  intro T V U m2 cnt dms inh nq f α h1 l₁ l₂ HN1 HN2 Habs h2
  exact W1c2.noNz (nq l₁) (nq l₂) f h1 HN1 HN2 Habs
-- `SLang.privPostPocess_DP_pre` idx 15
theorem w2_90 : drop% SLang.privPostPocess_DP_pre 15 := by
  intro T U V inst cnt dms nq HNorm f α h1 l₁ l₂ HN Habs
  exact W1c2.noNz (⇑(nq l₁)) (⇑(nq l₂)) f h1 (HNorm l₁) (HNorm l₂) Habs


open scoped Classical in
-- `SLang.privPostPocess_DP_pre_reduct` idx 14
theorem w2_91 : drop% SLang.privPostPocess_DP_pre_reduct 14 := by
  intro T V U m2 cnt dms inh nq f α h1 l₁ l₂ HN1 Habs Hnq2 h2
  rw [← ENNReal.tsum_fiberwise (fun u => nq l₁ u ^ α * nq l₂ u ^ (1 - α)) f]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have eP : ∀ g : U → ENNReal, (∑' a, if x = f a then g a else 0) = ∑' b : f ⁻¹' {x}, g b := by
    intro g; rw [tsum_subtype]; congr 1; funext a
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, eq_comm]
  rw [eP, eP]
  by_cases hP0 : ∑' b : f ⁻¹' {x}, nq l₁ b = 0
  · rw [hP0, ENNReal.zero_rpow_of_pos (by linarith), zero_mul]; exact zero_le
  by_cases hQt : ∑' b : f ⁻¹' {x}, nq l₂ b = ⊤
  · rw [hQt, ENNReal.top_rpow_of_neg (by linarith), mul_zero]; exact zero_le
  have hQ0 : ∑' b : f ⁻¹' {x}, nq l₂ b ≠ 0 := by
    intro h0; apply hP0
    exact ENNReal.tsum_eq_zero.2 fun b => Habs b ((ENNReal.tsum_eq_zero.1 h0) b)
  have hPt : ∑' b : f ⁻¹' {x}, nq l₁ b ≠ ⊤ := by
    refine ne_top_of_le_ne_top (HN1.tsum_eq ▸ ENNReal.one_ne_top) ?_
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (nq l₁)
  exact W1c2.fib (fun b : f ⁻¹' {x} => nq l₁ b) (fun b => nq l₂ b) h1 hP0 hPt hQ0 hQt (fun b hb => Habs b hb)

open scoped Classical in
-- `SLang.privPostPocess_DP_pre_reduct` idx 13
theorem w2_92 : drop% SLang.privPostPocess_DP_pre_reduct 13 := by
  intro T V U m2 cnt dms inh nq f α h1 l₁ l₂ HN2 Habs Hnq2 h2
  rw [← ENNReal.tsum_fiberwise (fun u => nq l₁ u ^ α * nq l₂ u ^ (1 - α)) f]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have eP : ∀ g : U → ENNReal, (∑' a, if x = f a then g a else 0) = ∑' b : f ⁻¹' {x}, g b := by
    intro g; rw [tsum_subtype]; congr 1; funext a
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, eq_comm]
  rw [eP, eP]
  by_cases hP0 : ∑' b : f ⁻¹' {x}, nq l₁ b = 0
  · rw [hP0, ENNReal.zero_rpow_of_pos (by linarith), zero_mul]; exact zero_le
  have hQle : ∑' b : f ⁻¹' {x}, nq l₂ b ≤ 1 :=
    (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (nq l₂)).trans HN2.tsum_eq.le
  have hQt : ∑' b : f ⁻¹' {x}, nq l₂ b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hQle
  have hQ0 : ∑' b : f ⁻¹' {x}, nq l₂ b ≠ 0 := by
    intro h0; apply hP0
    exact ENNReal.tsum_eq_zero.2 fun b => Habs b ((ENNReal.tsum_eq_zero.1 h0) b)
  by_cases hPt : ∑' b : f ⁻¹' {x}, nq l₁ b = ⊤
  · rw [W1c2.infmass (fun b : f ⁻¹' {x} => nq l₁ b) (fun b => nq l₂ b) h1 hQle (fun b hb => Habs b hb) hPt]
    exact le_top
  · exact W1c2.fib (fun b : f ⁻¹' {x} => nq l₁ b) (fun b => nq l₂ b) h1 hP0 hPt hQ0 hQt (fun b hb => Habs b hb)

end W1c2_s7
