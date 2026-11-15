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

namespace T1c2
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
-- With σ = 1 the Gaussian term is exp(-(x-μ)²/2).
theorem gt1 (μ x : ℝ) : gauss_term_ℝ 1 μ x = Real.exp (-(x - μ) ^ 2 / 2) := by
  unfold gauss_term_ℝ; norm_num

-- Termwise at α = 2 (σ = 1, means 2 and 0): p² q⁻¹ = e⁴ · (discrete Gaussian at 4), by completing the square.
theorem term_eq (x : ℤ) :
    discrete_gaussian 1 ((2:ℤ):ℝ) x ^ (2:ℝ) * discrete_gaussian 1 ((0:ℤ):ℝ) x ^ (1 - 2:ℝ)
      = Real.exp 4 * discrete_gaussian 1 ((4:ℤ):ℝ) x := by
  have h : (1:ℝ) ≠ 0 := one_ne_zero
  have hZ2 := shifted_gauss_sum_0 h 2
  have hZ4 := shifted_gauss_sum_0 h 4
  set Z := ∑' (n : ℤ), gauss_term_ℝ 1 0 n with hZdef
  have Zpos : 0 < Z := sum_gauss_term_pos h 0
  have d2 : discrete_gaussian 1 ((2:ℤ):ℝ) x = Real.exp (-((x:ℝ) - 2) ^ 2 / 2) / Z := by
    unfold discrete_gaussian; rw [hZ2, gt1]; simp
  have d4 : discrete_gaussian 1 ((4:ℤ):ℝ) x = Real.exp (-((x:ℝ) - 4) ^ 2 / 2) / Z := by
    unfold discrete_gaussian; rw [hZ4, gt1]; simp
  have d0 : discrete_gaussian 1 ((0:ℤ):ℝ) x = Real.exp (-((x:ℝ)) ^ 2 / 2) / Z := by
    unfold discrete_gaussian; simp only [Int.cast_zero]; rw [gt1]; simp [hZdef]
  rw [d2, d0, d4, Real.rpow_two, show (1:ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
  have key : Real.exp (-((x:ℝ) - 2) ^ 2 / 2) ^ 2 / Real.exp (-((x:ℝ)) ^ 2 / 2)
      = Real.exp 4 * Real.exp (-((x:ℝ) - 4) ^ 2 / 2) := by
    rw [sq, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]; congr 1; ring
  have hB := (Real.exp_pos (-((x:ℝ)) ^ 2 / 2)).ne'
  calc (Real.exp (-((x:ℝ) - 2) ^ 2 / 2) / Z) ^ 2 * (Real.exp (-((x:ℝ)) ^ 2 / 2) / Z)⁻¹
      = Real.exp (-((x:ℝ) - 2) ^ 2 / 2) ^ 2 / Real.exp (-((x:ℝ)) ^ 2 / 2) / Z := by
        field_simp
    _ = _ := by rw [key]; ring

-- The real Rényi-2 divergence between the discrete Gaussians (σ = 1) at 2 and 0 is exactly 4 = (μ-ν)²/σ².
theorem rd_eq : RenyiDivergence' (fun x : ℤ => discrete_gaussian 1 ((2:ℤ):ℝ) x)
    (fun x : ℤ => discrete_gaussian 1 ((0:ℤ):ℝ) x) 2 = 4 := by
  unfold RenyiDivergence'
  simp only [term_eq]
  rw [tsum_mul_left, discrete_gaussian_normalizes one_ne_zero, mul_one, Real.log_exp]
  norm_num

-- The query 2·length (sensitivity 2), noised with Δ = ε₁ = ε₂ = 1, on the neighbours [()] and [].
theorem rd_val : RenyiDivergence (SLang.privNoisedQuery (fun l : List Unit => 2 * (l.length : ℤ)) 1 1 1 [()])
    (SLang.privNoisedQuery (fun l : List Unit => 2 * (l.length : ℤ)) 1 1 1 []) 2 = ENNReal.ofReal 4 := by
  have Hpmf (w : ℤ) : (discrete_gaussian_pmf (one_ne_zero : (1:ℝ) ≠ 0) w = SLang.DiscreteGaussianGenPMF (1 * 1) 1 w) := by
    simp [discrete_gaussian_pmf]
    simp [SLang.DiscreteGaussianGenPMF]
    congr
    apply funext
    intro z
    rw [SLang.DiscreteGaussianGenSample_apply]
    norm_num
  change RenyiDivergence (SLang.DiscreteGaussianGenPMF (1 * 1) 1 2) (SLang.DiscreteGaussianGenPMF (1 * 1) 1 0) 2 = _
  rw [← Hpmf, ← Hpmf, renyi_eq, rd_eq]

end T1c2

-- `SLang.privNoisedQuery_zCDPBound` idx 5: necessary (query = 2·length on List Unit, Δ = ε₁ = ε₂ = 1, α = 2, neighbours [()] and []: the Rényi-2 divergence is exactly (μ-ν)²/σ² = 4 > 1 = claimed bound)
theorem t1c2_2 : ¬ drop0% SLang.privNoisedQuery_zCDPBound 5 := fun h => by
  have H := h (T := Unit) (fun l => 2 * (l.length : ℤ)) 1 1 1 2 (by norm_num) [()] []
    (Neighbour.Deletion (a := []) (b := []) (n := ()) rfl rfl)
  rw [T1c2.rd_val, ENNReal.ofReal_le_ofReal_iff (by positivity)] at H
  simp only [show ∀ n : ℕ+, (NNReal.ofPNat n : NNReal) = ((n.val : ℕ) : NNReal) from fun _ => rfl] at H
  norm_num at H

-- `SLang.privNoisedQuery_zCDP` idx 5: necessary (same counterexample; its zCDPBound component fails)
theorem t1c2_1 : ¬ drop0% SLang.privNoisedQuery_zCDP 5 := fun h => by
  have H := (h (T := Unit) (fun l => 2 * (l.length : ℤ)) 1 1 1).2 2 (by norm_num) [()] []
    (Neighbour.Deletion (a := []) (b := []) (n := ()) rfl rfl)
  rw [T1c2.rd_val, ENNReal.ofReal_le_ofReal_iff (by positivity)] at H
  simp only [show ∀ n : ℕ+, (NNReal.ofPNat n : NNReal) = ((n.val : ℕ) : NNReal) from fun _ => rfl] at H
  norm_num at H
