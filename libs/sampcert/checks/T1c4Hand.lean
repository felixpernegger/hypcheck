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

namespace T1c4
open SLang

noncomputable abbrev G : SPMF ℤ := @privNoiseGuess PureDPSystem laplace_pureDPSystem 4 1
noncomputable abbrev Th : SPMF ℤ := @privNoiseThresh PureDPSystem laplace_pureDPSystem 4 1

theorem G_val (x : ℤ) : G x = ENNReal.ofReal (((Real.exp 1 - 1) / (Real.exp 1 + 1)) * Real.exp (-|x|)) := by
  show DiscreteLaplaceGenSample (1 * (2 * sens_cov_vk * 1)) 4 0 x = _
  have h4 : (1 * (2 * sens_cov_vk * 1) : ℕ+) = 4 := rfl
  rw [DiscreteLaplaceGenSample_apply, h4]
  norm_num

theorem G_sum : ∑' x, G x = 1 := SPMF_sum_one _

theorem G_tail (m : ℤ) (hm : 0 ≤ m) :
    ∑' v, (if m ≤ v then G v else 0) ≤ ENNReal.ofReal (Real.exp (-m)) := by
  rw [← (Equiv.addRight m).tsum_eq]
  calc ∑' w, (if m ≤ (Equiv.addRight m) w then G ((Equiv.addRight m) w) else 0)
      ≤ ∑' w, ENNReal.ofReal (Real.exp (-m)) * G w := by
        apply ENNReal.tsum_le_tsum
        intro w
        simp only [Equiv.coe_addRight]
        by_cases h : m ≤ w + m
        · simp only [h, ite_true]
          have hw : (0:ℝ) ≤ (w:ℝ) := by exact_mod_cast (by omega : (0:ℤ) ≤ w)
          have hm' : (0:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
          rw [G_val, G_val, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          apply le_of_eq
          congr 1
          push_cast
          rw [abs_of_nonneg (by linarith), abs_of_nonneg hw, neg_add, Real.exp_add]
          ring
        · simp only [h, ite_false]; exact zero_le
    _ = ENNReal.ofReal (Real.exp (-m)) := by rw [ENNReal.tsum_mul_left, G_sum, mul_one]

theorem exp_neg_one_le : Real.exp (-1) ≤ 1 / 2 := by
  have h1 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have h2 := Real.add_one_le_exp (1:ℝ)
  nlinarith [Real.exp_pos (-1)]

theorem exp_le_half (n : ℕ) : ENNReal.ofReal (Real.exp (-((n:ℤ):ℝ))) ≤ (1/2 : ENNReal) ^ n := by
  have h : Real.exp (-((n:ℤ):ℝ)) = Real.exp (-1) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h, ENNReal.ofReal_pow (Real.exp_pos _).le]
  apply pow_le_pow_left₀ zero_le
  rw [show (1/2 : ENNReal) = ENNReal.ofReal (1/2) by
    rw [ENNReal.ofReal_div_of_pos two_pos]; simp]
  exact ENNReal.ofReal_le_ofReal exp_neg_one_le

theorem tail_half (n : ℕ) : ∑' v, (if (n:ℤ) ≤ v then G v else 0) ≤ (1/2 : ENNReal) ^ n :=
  (G_tail n (by omega)).trans (exp_le_half n)

theorem half_add (n : ℕ) : (1/2 : ENNReal) ^ (n+1) + (1/2) ^ (n+1) = (1/2) ^ n := by
  rw [pow_succ, ← mul_add, ENNReal.add_halves, mul_one]

theorem step_sum (n : ℕ) :
    ∑' b, G b * (if b < ((n + 1 : ℕ) : ℤ) then (1/2 : ENNReal) ^ (n+1) else 1) ≤ (1/2) ^ n := by
  calc ∑' b, G b * (if b < ((n + 1 : ℕ) : ℤ) then (1/2 : ENNReal) ^ (n+1) else 1)
      ≤ ∑' b, (G b * (1/2 : ENNReal) ^ (n+1) + (if ((n+1 : ℕ) : ℤ) ≤ b then G b else 0)) := by
        apply ENNReal.tsum_le_tsum
        intro b
        by_cases h : b < ((n + 1 : ℕ) : ℤ)
        · have h' : ¬ ((n+1 : ℕ) : ℤ) ≤ b := by omega
          simp only [h, h', if_true, if_false, add_zero]; exact le_refl _
        · have h' : ((n+1 : ℕ) : ℤ) ≤ b := by omega
          simp only [h, h', if_true, if_false, mul_one]; exact le_add_self
    _ = (∑' b, G b) * (1/2 : ENNReal) ^ (n+1) + ∑' b, (if ((n+1 : ℕ) : ℤ) ≤ b then G b else 0) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ 1 * (1/2 : ENNReal) ^ (n+1) + (1/2) ^ (n+1) := by
        rw [G_sum]; gcongr; exact tail_half (n+1)
    _ = (1/2) ^ n := by rw [one_mul, half_add]

def qs0 : sv_query Unit := fun k _ => -((k:ℤ) + 2)

noncomputable abbrev body : sv1_state → SLang sv1_state :=
  @sv1_aboveThreshF PureDPSystem laplace_pureDPSystem 4 1

theorem body_bind (s : sv1_state) (g : sv1_state → SLang sv1_state) (x : sv1_state) :
    (body s >>= g) x = ∑' b, G b * g (s.1 ++ [s.2], b) x := by
  simp only [sv1_aboveThreshF, Bind.bind, Pure.pure]
  refine (congrFun (SLang.bind_bind _ _ g) x).trans ?_
  refine tsum_congr (fun b => ?_)
  exact congrArg (G b * ·) (congrFun (SLang.pure_bind _ g) x)

theorem loop_bd (cut : ℕ) : ∀ (s : sv1_state),
    ∑' x, probWhileCut (sv1_aboveThreshC qs0 0 0 []) body cut s x
      ≤ if s.2 < ((s.1.length + 2 : ℕ) : ℤ) then (1/2 : ENNReal) ^ (s.1.length + 2) else 1 := by
  induction cut with
  | zero => intro s; simp [probWhileCut, probZero]
  | succ cut IH =>
    intro s
    rw [probWhileCut_succ]
    unfold probWhileFunctional
    by_cases hc : s.2 < ((s.1.length + 2 : ℕ) : ℤ)
    · have hcond : sv1_aboveThreshC qs0 0 0 [] s = true := by
        simp [sv1_aboveThreshC, sv1_threshold, sv1_noise, qs0]; omega
      rw [if_pos hcond, if_pos hc]
      simp only [body_bind]
      rw [ENNReal.tsum_comm]
      simp only [ENNReal.tsum_mul_left]
      calc ∑' b, G b * ∑' x, probWhileCut (sv1_aboveThreshC qs0 0 0 []) body cut (s.1 ++ [s.2], b) x
          ≤ ∑' b, G b * (if b < ((s.1.length + 2 + 1 : ℕ) : ℤ) then (1/2 : ENNReal) ^ (s.1.length + 2 + 1) else 1) := by
            apply ENNReal.tsum_le_tsum
            intro b
            gcongr
            have := IH (s.1 ++ [s.2], b)
            simp only [List.length_append, List.length_singleton] at this
            rw [show s.1.length + 1 + 2 = s.1.length + 2 + 1 by omega] at this
            exact this
        _ ≤ _ := step_sum _
    · have hcond : ¬ sv1_aboveThreshC qs0 0 0 [] s = true := by
        simp [sv1_aboveThreshC, sv1_threshold, sv1_noise, qs0]; omega
      rw [if_neg hcond, if_neg hc]
      exact le_of_eq (probPure_norm _)

theorem tau0_bd :
    ∑' v0, G v0 * ∑' b, probWhile (sv1_aboveThreshC qs0 0 0 []) body (([], v0) : sv1_state) b ≤ 1/2 := by
  calc ∑' v0, G v0 * ∑' b, probWhile (sv1_aboveThreshC qs0 0 0 []) body (([], v0) : sv1_state) b
      ≤ ∑' v0, G v0 * (if v0 < ((1 + 1 : ℕ) : ℤ) then (1/2 : ENNReal) ^ (1 + 1) else 1) := by
        apply ENNReal.tsum_le_tsum
        intro v0
        gcongr
        unfold probWhile
        rw [sv1_tsum_iSup_probWhileCut_comm]
        apply iSup_le
        intro i
        exact loop_bd i (([], v0) : sv1_state)
    _ ≤ (1/2) ^ 1 := step_sum 1
    _ = 1/2 := pow_one _

section gen
variable [dps : DPSystem ℕ] [dpn : DPNoise dps] {sv_T : Type}

theorem ub_gen (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    ∑'s, sv1_aboveThresh qs T ε₁ ε₂ l s ≤
      ∑' (a : ℤ), (privNoiseThresh ε₁ ε₂) a * ∑' (a_1 : ℤ), (privNoiseGuess ε₁ ε₂) a_1 *
        ∑' (b : sv1_state), probWhile (sv1_aboveThreshC qs T a l) (sv1_aboveThreshF ε₁ ε₂) ([], a_1) b := by
  unfold sv1_aboveThresh
  unfold sv1_threshold
  simp
  conv =>
    rw [ENNReal.tsum_comm]
    enter [1, 1, b]
    rw [ENNReal.tsum_mul_left]
    enter [2]
    rw [ENNReal.tsum_comm]
    enter [1, i]
    rw [ENNReal.tsum_mul_left]
    enter [2]
    rw [ENNReal.tsum_comm]
  apply ENNReal.tsum_le_tsum
  intro τ
  apply mul_le_mul_right
  apply ENNReal.tsum_le_tsum
  intro v0
  apply mul_le_mul_right
  apply ENNReal.tsum_le_tsum
  intro a
  rw [tsum_ite_eq]

end gen

theorem Th_pos : Th 0 ≠ 0 := by
  show DiscreteLaplaceGenSample (1 * (2 * sens_cov_τ * 1)) 4 0 0 ≠ 0
  rw [DiscreteLaplaceGenSample_apply]
  apply ne_of_gt
  rw [ENNReal.ofReal_pos]
  apply mul_pos (div_pos (sub_pos.mpr (lt_of_eq_of_lt Real.exp_zero.symm (Real.exp_lt_exp.mpr (by positivity)))) (by positivity)) (Real.exp_pos _)

theorem Th_ne_top : Th 0 ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.le_tsum 0).trans (le_of_eq (SPMF_sum_one _)))

theorem B_le_one (τ : ℤ) :
    ∑' v0, G v0 * ∑' b, probWhile (sv1_aboveThreshC qs0 0 τ []) body (([], v0) : sv1_state) b ≤ 1 := by
  calc ∑' v0, G v0 * ∑' b, probWhile (sv1_aboveThreshC qs0 0 τ []) body (([], v0) : sv1_state) b
      ≤ ∑' v0, G v0 * 1 := by
        apply ENNReal.tsum_le_tsum
        intro v0
        gcongr
        unfold probWhile
        rw [sv1_tsum_iSup_probWhileCut_comm]
        apply iSup_le
        intro i
        exact sv1_loop_ub qs0 0 τ 4 1 [] i [] v0
    _ = 1 := by rw [ENNReal.tsum_mul_right, G_sum, one_mul]

theorem mass_lt : ∑' s, @sv1_aboveThresh PureDPSystem laplace_pureDPSystem Unit qs0 0 4 1 [] s < 1 := by
  refine lt_of_le_of_lt (ub_gen qs0 0 4 1 []) ?_
  rw [ENNReal.tsum_eq_add_tsum_ite 0]
  have hsum : Th 0 + ∑' τ, (if τ = 0 then 0 else Th τ) = 1 := by
    convert (ENNReal.tsum_eq_add_tsum_ite (f := fun τ => Th τ) 0).symm.trans (SPMF_sum_one _)
  have hR : ∑' τ, (if τ = 0 then 0 else Th τ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_add_self)
  calc _ ≤ Th 0 * (1/2) + ∑' τ, (if τ = 0 then 0 else Th τ) := by
        gcongr
        · exact tau0_bd
        · split_ifs
          · exact le_refl _
          · refine le_trans ?_ (le_of_eq (mul_one (Th _)))
            gcongr
            exact B_le_one _
    _ < Th 0 + ∑' τ, (if τ = 0 then 0 else Th τ) := by
        apply ENNReal.add_lt_add_right hR
        rw [one_div, ← div_eq_mul_inv]
        exact ENNReal.half_lt_self Th_pos Th_ne_top
    _ = 1 := hsum

end T1c4

-- `SLang.sv1_lb` idx 3: necessary
theorem t1c4_1 : ¬ drop0% SLang.sv1_lb 3 := fun h =>
  absurd (h T1c4.qs0 0 4 1 []) (not_le.mpr T1c4.mass_lt)

-- `SLang.sv1_hasSum_one` idx 3: necessary
theorem t1c4_2 : ¬ drop0% SLang.sv1_hasSum_one 3 := fun h =>
  absurd (h T1c4.qs0 0 4 1 []).tsum_eq (ne_of_lt T1c4.mass_lt)
