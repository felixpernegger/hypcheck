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

namespace T1c0
open SLang

-- Helpers copied from Probe2 (checks/Probe2Hand.lean): a pure (log 2)-DP mechanism on lists of Unit.
noncomputable def eps2 : NNReal := ⟨Real.log 2, Real.log_nonneg (by norm_num)⟩

theorem eps2_exp : Real.exp (eps2 : ℝ) = 2 := Real.exp_log (by norm_num)

/-- mass of true is (1/2)^(min n 5 + 1) for list length n -/
noncomputable def w (n : ℕ) (x : Bool) : ℝ :=
  if x then (1/2 : ℝ) ^ (min n 5 + 1) else 1 - (1/2 : ℝ) ^ (min n 5 + 1)

theorem w_pos (n : ℕ) (x : Bool) : 0 < w n x := by
  unfold w
  cases x
  · simp only [Bool.false_eq_true, if_false, sub_pos]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  · simp only [if_true]; positivity

theorem w_sum (n : ℕ) : w n false + w n true = 1 := by
  unfold w; simp

theorem w_le (n n' : ℕ) (h : n' = n + 1 ∨ n = n' + 1) (x : Bool) : w n x ≤ 2 * w n' x := by
  rcases h with rfl | rfl
  · rcases Nat.lt_or_ge n 5 with hm | hm
    · interval_cases n <;> cases x <;> norm_num [w]
    · have e1 : min n 5 = 5 := min_eq_right hm
      have e2 : min (n + 1) 5 = 5 := min_eq_right (by omega)
      have := w_pos n x
      unfold w at this ⊢; rw [e1, e2] at *; cases x <;> simp only [Bool.false_eq_true, if_false, if_true] at * <;> linarith
  · rcases Nat.lt_or_ge n' 5 with hm | hm
    · interval_cases n' <;> cases x <;> norm_num [w]
    · have e1 : min n' 5 = 5 := min_eq_right hm
      have e2 : min (n' + 1) 5 = 5 := min_eq_right (by omega)
      have := w_pos n' x
      unfold w at this ⊢; rw [e1, e2] at *; cases x <;> simp only [Bool.false_eq_true, if_false, if_true] at * <;> linarith

noncomputable def q27 (l : List Unit) : PMF Bool :=
  ⟨fun x => ENNReal.ofReal (w l.length x), by
    rw [Summable.hasSum_iff ENNReal.summable, tsum_bool, ← ENNReal.ofReal_add (w_pos _ _).le
      (w_pos _ _).le, w_sum, ENNReal.ofReal_one]⟩

theorem nb_len {l₁ l₂ : List Unit} (h : Neighbour l₁ l₂) :
    l₂.length = l₁.length + 1 ∨ l₁.length = l₂.length + 1 := by
  cases h with
  | Addition h1 h2 => left; subst h1 h2; simp; omega
  | Deletion h1 h2 => right; subst h1 h2; simp; omega

theorem q27_dp : SLang.PureDP q27 eps2 := by
  intro l₁ l₂ hN S
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun x => ?_)
  split_ifs
  · show ENNReal.ofReal (w l₁.length x) ≤ ENNReal.ofReal (Real.exp eps2) * ENNReal.ofReal (w l₂.length x)
    rw [eps2_exp, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (w_le _ _ (nb_len hN) x)
  · simp

theorem nbA : Neighbour ([] : List Unit) [()] := Neighbour.Addition (a := []) (b := []) (n := ()) (by simp) (by simp)

theorem eps2_coe : (eps2 : ℝ) = Real.log 2 := rfl

theorem half_eps2 : (((1/2) * eps2 ^ 2 : NNReal) : ℝ) = (1/2) * (Real.log 2) ^ 2 := by
  push_cast [eps2_coe]; ring

theorem log2_lt_one : Real.log 2 < 1 := by
  have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num); linarith

theorem log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- q27 is not (x, 0)-DP for any x < log 2: the event {true} has mass 1/2 at [] and 1/4 at [()]. -/
theorem dp_fail (x : ℝ) (hx : x < Real.log 2) : ¬ SLang.DP' q27 x 0 := fun H => by
  have h := H [] [()] nbA {true}
  simp only [tsum_bool, Set.mem_singleton_iff, Bool.false_eq_true, if_false, if_true, zero_add,
    ENNReal.coe_zero] at h
  change ENNReal.ofReal (w 0 true) ≤ ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (w 1 true) at h
  rw [← ENNReal.ofReal_mul (Real.exp_pos x).le, ENNReal.ofReal_le_ofReal_iff (mul_pos (Real.exp_pos x) (w_pos 1 true)).le] at h
  norm_num [w] at h
  have : Real.exp x < 2 := by
    rw [← Real.exp_log (show (0:ℝ) < 2 by norm_num)]; exact Real.exp_lt_exp.mpr hx
  linarith

/-- At δ = 0 the approximate-DP parameter collapses: log (1/0) = 0. -/
theorem eps_delta0 (ε : ℝ) :
    ε ^ 2 / 2 + ε * (2 * Real.log (1 / ((0 : NNReal) : ℝ))) ^ (1 / 2 : ℝ) = ε ^ 2 / 2 := by
  simp

theorem zbound : zCDPBound q27 ((1/2) * (Real.log 2) ^ 2) := by
  have := (SLang.ofDP eps2 q27 q27_dp).2
  rwa [half_eps2] at this

theorem small : (Real.log 2) ^ 2 / 2 < Real.log 2 := by
  nlinarith [log2_lt_one, log2_pos]

theorem zcdp_adp0 (ε' : NNReal) : SLang.zCDP_of_adp 0 ε' = ε' := by
  unfold SLang.zCDP_of_adp SLang.zCDP_of_adp_def.ε SLang.zCDP_of_adp_def.D
  apply NNReal.eq
  simp [discrim]
  rw [show (2:ℝ)⁻¹ = 1/2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [max_eq_left (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  ring

end T1c0

-- `SLang.ApproximateDP_of_zCDP` idx 9: necessary (δ = 0: log (1/0) = 0 in Lean, so the claim is pure (log 2)²/2-DP; the pure (log 2)-DP mechanism q27 is ½(log 2)²-zCDP by SLang.ofDP but has ratio 2 > exp((log 2)²/2) on {true})
theorem t1c0_1 : ¬ drop0% SLang.ApproximateDP_of_zCDP 9 := fun h => by
  have H := @h Unit Bool _ T1c0.q27 (Real.log 2) T1c0.log2_pos.le T1c0.zbound
    (SLang.ofDP T1c0.eps2 T1c0.q27 T1c0.q27_dp).1 0
  rw [T1c0.eps_delta0] at H
  exact T1c0.dp_fail _ T1c0.small H

-- `SLang.ApproximateDP_of_zCDP_pos` idx 9: necessary (same counterexample as for SLang.ApproximateDP_of_zCDP: ε = log 2, δ = 0)
theorem t1c0_2 : ¬ drop0% SLang.ApproximateDP_of_zCDP_pos 9 := fun h => by
  have H := @h Unit Bool _ T1c0.q27 (Real.log 2) T1c0.log2_pos T1c0.zbound
    (SLang.ofDP T1c0.eps2 T1c0.q27 T1c0.q27_dp).1 0
  rw [T1c0.eps_delta0] at H
  exact T1c0.dp_fail _ T1c0.small H

-- `SLang.ApproximateDP_of_zCDP_pos_lt_one` idx 9: necessary (same counterexample, δ = 0 < 1)
theorem t1c0_3 : ¬ drop0% SLang.ApproximateDP_of_zCDP_pos_lt_one 9 := fun h => by
  have H := @h Unit Bool _ T1c0.q27 (Real.log 2) T1c0.log2_pos T1c0.zbound
    (SLang.ofDP T1c0.eps2 T1c0.q27 T1c0.q27_dp).1 0 (by norm_num)
  rw [T1c0.eps_delta0] at H
  exact T1c0.dp_fail _ T1c0.small H

-- `SLang.zCDP_ApproximateDP` idx 5: necessary (δ = 0 gives zCDP_of_adp 0 ε' = ε'; with ε' = ½(log 2)² the mechanism q27 is ε'-zCDP by SLang.ofDP but not (ε', 0)-DP)
theorem t1c0_4 : ¬ drop0% SLang.zCDP_ApproximateDP 5 := fun h => by
  have hz := SLang.ofDP T1c0.eps2 T1c0.q27 T1c0.q27_dp
  have H := @h Unit Bool _ T1c0.q27 0 ((1/2) * T1c0.eps2 ^ 2) (by rw [T1c0.zcdp_adp0]; exact hz)
  apply T1c0.dp_fail _ _ H
  rw [T1c0.half_eps2]; linarith [T1c0.small]
