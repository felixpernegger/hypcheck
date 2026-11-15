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

set_option linter.unusedSimpArgs false

namespace T1c1
open Real Nat

-- Copied from the proof of Renyi_Gauss_divergence_bound' (inner `have A`, which does not use 1 < α).
theorem renyi_eq {σ α : ℝ} (h : σ ≠ 0) (μ ν : ℤ) :
    RenyiDivergence (discrete_gaussian_pmf h μ) (discrete_gaussian_pmf h ν) α =
    ENNReal.ofReal (RenyiDivergence' (fun (x : ℤ) => discrete_gaussian σ μ x) (fun (x : ℤ) => discrete_gaussian σ ν x) α) := by
    unfold RenyiDivergence
    unfold RenyiDivergence_def
    unfold RenyiDivergence'
    simp
    unfold discrete_gaussian_pmf

    have Hdg_pos (x : ℤ) (w : ℝ) : OfNat.ofNat 0 < discrete_gaussian σ w x.cast := by
      exact discrete_gaussian_pos h w x
    have Hdg_pow_pos (x : ℤ) w : OfNat.ofNat 0 ≤ discrete_gaussian σ w x.cast ^ α := by
      apply rpow_nonneg
      exact discrete_gaussian_nonneg h w x

    conv =>
      lhs
      arg 1
      arg 2
      arg 1
      arg 1
      intro x
      simp [DFunLike.coe]
      rw [ENNReal.ofReal_rpow_of_pos (Hdg_pos x μ.cast)]
      rw [ENNReal.ofReal_rpow_of_pos (Hdg_pos x ν.cast)]
      rw [<- ENNReal.ofReal_mul (Hdg_pow_pos x μ.cast)]
    rw [<- ENNReal.ofEReal_ofReal_toENNReal]
    simp
    congr
    cases (Classical.em (0 = ∑' (x : ℤ), discrete_gaussian σ μ.cast x.cast ^ α * discrete_gaussian σ ν.cast x.cast ^ (1 - α)))
    · rename_i Hzero
      rw [<- Hzero]
      simp
      rw [<- ENNReal.ofReal_tsum_of_nonneg]
      · rw [<- Hzero]
        exfalso
        symm at Hzero
        have Hzero' : (ENNReal.ofReal (∑' (x : ℤ), discrete_gaussian σ ↑μ ↑x ^ α * discrete_gaussian σ ↑ν ↑x ^ (1 - α)) = 0) := by
          simp [Hzero]
        rw [ENNReal.ofReal_tsum_of_nonneg ?G1 ?G2] at Hzero'
        case G1 => exact fun n => Renyi_sum_SG_nonneg h μ ν n
        case G2 => exact Renyi_Gauss_summable h μ ν α
        apply ENNReal.tsum_eq_zero.mp at Hzero'
        have Hzero'' := Hzero' (0 : ℤ)
        simp at Hzero''
        have C : (0 < discrete_gaussian σ (↑μ) 0 ^ α * discrete_gaussian σ (↑ν) 0 ^ (1 - α)) := by
          apply mul_pos
          · apply Real.rpow_pos_of_pos
            have A := discrete_gaussian_pos h μ (0 : ℤ)
            simp at A
            apply A
          · apply Real.rpow_pos_of_pos
            have A := discrete_gaussian_pos h ν (0 : ℤ)
            simp at A
            apply A
        linarith
      · exact fun n => Renyi_sum_SG_nonneg h μ ν n
      · exact Renyi_Gauss_summable h μ ν α
    · rename_i Hnz
      rw [<- ENNReal.elog_ENNReal_ofReal_of_pos]
      · rw [ENNReal.ofReal_tsum_of_nonneg ?Hnn]
        · exact Renyi_Gauss_summable h μ ν α
        · intro n
          exact Renyi_sum_SG_nonneg h μ ν n
      apply lt_of_le_of_ne
      · apply tsum_nonneg
        intro i
        exact Renyi_sum_SG_nonneg h μ ν i
      · apply Hnz

-- With 2σ² = 1/8 the Gaussian term is exp(-8(x-μ)²).
theorem g_eq {σ : ℝ} (h2 : 2 * σ ^ 2 = 1 / 8) (μ x : ℝ) : gauss_term_ℝ σ μ x = Real.exp (-8 * (x - μ) ^ 2) := by
  unfold gauss_term_ℝ; rw [h2]; congr 1; ring

theorem ne0 {σ : ℝ} (h2 : 2 * σ ^ 2 = 1 / 8) : σ ≠ 0 := by rintro rfl; norm_num at h2

/-- Termwise: sqrt(dg 1 x · dg 0 x) ≤ e⁻⁴ (dg 1 x + dg 0 x), by completing the square on each side of 1/2. -/
theorem term_le {σ : ℝ} (h2 : 2 * σ ^ 2 = 1 / 8) (x : ℤ) :
    discrete_gaussian σ ((1:ℤ):ℝ) x ^ (1/2:ℝ) * discrete_gaussian σ ((0:ℤ):ℝ) x ^ (1 - 1/2:ℝ)
      ≤ Real.exp (-4) * (discrete_gaussian σ ((1:ℤ):ℝ) x + discrete_gaussian σ ((0:ℤ):ℝ) x) := by
  have h := ne0 h2
  have hZ := shifted_gauss_sum_0 h 1
  set Z := ∑' (n : ℤ), gauss_term_ℝ σ 0 n with hZdef
  have Zpos : 0 < Z := sum_gauss_term_pos h 0
  have d1 : discrete_gaussian σ ((1:ℤ):ℝ) x = Real.exp (-8 * ((x:ℝ) - 1) ^ 2) / Z := by
    unfold discrete_gaussian; rw [hZ, g_eq h2]; simp
  have d0 : discrete_gaussian σ ((0:ℤ):ℝ) x = Real.exp (-8 * (x:ℝ) ^ 2) / Z := by
    unfold discrete_gaussian; simp only [Int.cast_zero]; rw [g_eq h2]; simp [hZdef]
  rw [d1, d0, show (1:ℝ) - 1/2 = 1/2 by norm_num,
    Real.div_rpow (Real.exp_pos _).le Zpos.le, Real.div_rpow (Real.exp_pos _).le Zpos.le,
    ← Real.exp_mul, ← Real.exp_mul,
    show ∀ a b c : ℝ, a / c * (b / c) = a * b / (c * c) from fun a b c => by ring, ← Real.rpow_add Zpos,
    show (1/2:ℝ) + 1/2 = 1 by norm_num, Real.rpow_one, ← Real.exp_add, ← add_div]
  conv_rhs => rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ Zpos.le
  rcases le_or_gt 1 x with hx | hx
  · have hx' : (1:ℝ) ≤ x := by exact_mod_cast hx
    calc Real.exp (-8 * ((x:ℝ) - 1) ^ 2 * (1/2) + -8 * (x:ℝ) ^ 2 * (1/2))
        ≤ Real.exp (-4) * Real.exp (-8 * ((x:ℝ) - 1) ^ 2) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          linarith [Real.exp_pos (-8 * (x:ℝ) ^ 2)]
  · have hx' : (x:ℝ) ≤ 0 := by exact_mod_cast (show x ≤ 0 by omega)
    calc Real.exp (-8 * ((x:ℝ) - 1) ^ 2 * (1/2) + -8 * (x:ℝ) ^ 2 * (1/2))
        ≤ Real.exp (-4) * Real.exp (-8 * (x:ℝ) ^ 2) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          linarith [Real.exp_pos (-8 * ((x:ℝ) - 1) ^ 2)]

/-- The Rényi-1/2 series between the discrete Gaussians at 1 and 0 (2σ² = 1/8) is in (0, 2e⁻⁴]. -/
theorem S_bounds {σ : ℝ} (h2 : 2 * σ ^ 2 = 1 / 8) :
    0 < ∑' x : ℤ, discrete_gaussian σ ((1:ℤ):ℝ) x ^ (1/2:ℝ) * discrete_gaussian σ ((0:ℤ):ℝ) x ^ (1 - 1/2:ℝ) ∧
    ∑' x : ℤ, discrete_gaussian σ ((1:ℤ):ℝ) x ^ (1/2:ℝ) * discrete_gaussian σ ((0:ℤ):ℝ) x ^ (1 - 1/2:ℝ)
      ≤ 2 * Real.exp (-4) := by
  have h := ne0 h2
  have hs := Renyi_Gauss_summable h 1 0 (1/2)
  constructor
  · apply hs.tsum_pos (fun n => Renyi_sum_SG_nonneg h 1 0 n) 0
    exact mul_pos (Real.rpow_pos_of_pos (discrete_gaussian_pos h _ 0) _)
      (Real.rpow_pos_of_pos (discrete_gaussian_pos h _ 0) _)
  · have s1 := discrete_gaussian_summable' h ((1:ℤ):ℝ)
    have s0 := discrete_gaussian_summable' h ((0:ℤ):ℝ)
    calc _ ≤ ∑' x : ℤ, Real.exp (-4) * (discrete_gaussian σ ((1:ℤ):ℝ) x + discrete_gaussian σ ((0:ℤ):ℝ) x) :=
          hs.tsum_le_tsum (term_le h2) ((s1.add s0).mul_left _)
      _ = 2 * Real.exp (-4) := by
          rw [tsum_mul_left, s1.tsum_add s0, discrete_gaussian_normalizes h, discrete_gaussian_normalizes h]
          ring

/-- At α = 1/2 the Rényi divergence between the discrete Gaussians at 1 and 0 exceeds 6 (claimed bound: 4). -/
theorem rd_big {σ : ℝ} (h2 : 2 * σ ^ 2 = 1 / 8) :
    6 < RenyiDivergence' (fun x : ℤ => discrete_gaussian σ ((1:ℤ):ℝ) x)
      (fun x : ℤ => discrete_gaussian σ ((0:ℤ):ℝ) x) (1/2) := by
  obtain ⟨Spos, Sle⟩ := S_bounds h2
  unfold RenyiDivergence'
  have hl : Real.log (∑' x : ℤ, discrete_gaussian σ ((1:ℤ):ℝ) x ^ (1/2:ℝ) *
      discrete_gaussian σ ((0:ℤ):ℝ) x ^ (1 - 1/2:ℝ)) ≤ Real.log 2 - 4 := by
    calc _ ≤ Real.log (2 * Real.exp (-4)) := Real.log_le_log Spos Sle
      _ = Real.log 2 - 4 := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]; ring
  have l2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num); linarith
  rw [show (1:ℝ) / (1/2 - 1) = -2 by norm_num]
  linarith

theorem h2_quarter : 2 * (1/4 : ℝ) ^ 2 = 1 / 8 := by norm_num

theorem ne_quarter : (1/4 : ℝ) ≠ 0 := by norm_num

end T1c1

-- `Renyi_divergence_bound` idx 4: necessary (σ = 1/4, μ = 1, α = 1/2: the Rényi-1/2 series is ≤ 2e⁻⁴, so the divergence is ≥ 8 - 2 log 2 > 4 = α μ²/(2σ²))
theorem t1c1_1 : ¬ drop0% Renyi_divergence_bound 4 := fun h => by
  have H := h (σ := 1/4) T1c1.ne_quarter 1 (1/2)
  have := T1c1.rd_big T1c1.h2_quarter
  change RenyiDivergence' (fun x : ℤ => discrete_gaussian (1/4) ((1:ℤ):ℝ) x)
      (fun x : ℤ => discrete_gaussian (1/4) ((0:ℤ):ℝ) x) (1/2) ≤ _ at H
  norm_num at H
  linarith

-- `Renyi_divergence_bound_pre` idx 3: necessary (same counterexample: σ = 1/4, μ = 1, ν = 0, α = 1/2)
theorem t1c1_2 : ¬ drop0% Renyi_divergence_bound_pre 3 := fun h => by
  have H := h (σ := 1/4) (α := 1/2) T1c1.ne_quarter 1 0
  have := T1c1.rd_big T1c1.h2_quarter
  norm_num at H
  linarith

-- `Renyi_Gauss_divergence_bound'` idx 3: necessary (same counterexample; the ENNReal divergence is ofReal of the real one)
theorem t1c1_3 : ¬ drop0% Renyi_Gauss_divergence_bound' 3 := fun h => by
  have H := h (σ := 1/4) (α := 1/2) T1c1.ne_quarter 1 0
  rw [T1c1.renyi_eq] at H
  have := T1c1.rd_big T1c1.h2_quarter
  rw [← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity)] at H
  norm_num at H
  linarith

-- `SLang.discrete_GaussianGenSample_ZeroConcentrated` idx 1: necessary (num = 1, den = 4, μ = 1, ν = 0, α = 1/2; the sampler's PMF is discrete_gaussian_pmf with σ = 1/4)
theorem t1c1_4 : ¬ drop0% SLang.discrete_GaussianGenSample_ZeroConcentrated 1 := fun h => by
  have H := h (α := 1/2) 1 4 1 0
  have Hpmf (w : ℤ) : (discrete_gaussian_pmf T1c1.ne_quarter w = SLang.DiscreteGaussianGenPMF 1 4 w) := by
    simp [discrete_gaussian_pmf]
    simp [SLang.DiscreteGaussianGenPMF]
    congr
    apply funext
    intro z
    rw [SLang.DiscreteGaussianGenSample_apply]
    norm_num
  rw [← Hpmf, ← Hpmf, T1c1.renyi_eq] at H
  have := T1c1.rd_big T1c1.h2_quarter
  simp only [show ∀ (n : ℕ+), (NNReal.ofPNat n : NNReal) = ((n.val : ℕ) : NNReal) from fun _ => rfl] at H
  have Hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top (by simp) (by simp))) H
  rw [ENNReal.toReal_ofReal (by norm_num at this ⊢; linarith)] at Hr
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div] at Hr this
  linarith
