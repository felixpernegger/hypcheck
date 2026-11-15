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

set_option linter.unusedSectionVars false
noncomputable section
open Classical Nat Int Real ENNReal MeasureTheory Measure SLang

namespace T1c5

theorem nonneg' {T : Type} [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
    (p q : PMF T) {α : ℝ} (hα : 1 < α) : 0 ≤ RenyiDivergence_def p q α := by
  by_cases hac : AbsCts p q
  · exact RenyiDivergence_def_nonneg p q hac hα
  · obtain ⟨x, hqx, hpx⟩ : ∃ x, q x = 0 ∧ p x ≠ 0 := by simpa [AbsCts] using hac
    have hpos : p x ^ α ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hpx) (PMF.apply_ne_top p x)).ne'
    have hsum : ∑' x, p x ^ α * q x ^ (1 - α) = ⊤ := ENNReal.tsum_eq_top_of_eq_top
      ⟨x, by rw [hqx, ENNReal.zero_rpow_of_neg (by linarith)]; exact ENNReal.mul_top hpos⟩
    simp only [RenyiDivergence_def, hsum]
    rw [show ENNReal.elog ⊤ = ⊤ from rfl, EReal.mul_top_of_pos]
    · exact le_top
    · exact_mod_cast inv_pos.2 (sub_pos.2 hα)

theorem fv_top {c : ℝ} (hc : c < 0) : ofEReal ((c : EReal) * elog ⊤) = 0 := by
  rw [elog_top, EReal.coe_mul_top_of_neg hc]; rfl

theorem fv_zero {c : ℝ} (hc : c < 0) : ofEReal ((c : EReal) * elog 0) = ⊤ := by
  rw [elog_zero, EReal.coe_mul_bot_of_neg hc]; rfl

theorem fv_pos (c : ℝ) {r : ℝ} (hr : 0 < r) :
    ofEReal ((c : EReal) * elog (ENNReal.ofReal r)) = ENNReal.ofReal (c * Real.log r) := by
  rw [elog_of_pos_real hr, ← EReal.coe_mul]; rfl

theorem as_ofReal {x : ENNReal} (h0 : x ≠ 0) (ht : x ≠ ⊤) :
    0 < x.toReal ∧ x = ENNReal.ofReal x.toReal :=
  ⟨ENNReal.toReal_pos h0 ht, (ENNReal.ofReal_toReal ht).symm⟩

theorem lemA {c m : ℝ} (hc : c < 0) (hm : 0 ≤ m) (x : ENNReal)
    (h : ofEReal ((c : EReal) * elog x) ≤ ENNReal.ofReal m) : ENNReal.ofReal (Real.exp (m / c)) ≤ x := by
  by_cases ht : x = ⊤
  · rw [ht]; exact le_top
  by_cases h0 : x = 0
  · rw [h0, fv_zero hc] at h; exact absurd h (by simp)
  obtain ⟨hr, hx⟩ := as_ofReal h0 ht
  rw [hx] at h ⊢
  rw [fv_pos c hr, ENNReal.ofReal_le_ofReal_iff hm] at h
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.exp_log hr]
  apply Real.exp_le_exp.2
  rw [div_le_iff_of_neg hc]; linarith

theorem anti {c : ℝ} (hc : c < 0) {x y : ENNReal} (h : y ≤ x) :
    ofEReal ((c : EReal) * elog x) ≤ ofEReal ((c : EReal) * elog y) := by
  by_cases ht : x = ⊤
  · rw [ht, fv_top hc]; exact bot_le
  by_cases hy0 : y = 0
  · rw [hy0, fv_zero hc]; exact le_top
  have hx0 : x ≠ 0 := fun e => hy0 (le_antisymm (e ▸ h) bot_le)
  have hyt : y ≠ ⊤ := ne_top_of_le_ne_top ht h
  obtain ⟨hr, hx⟩ := as_ofReal hx0 ht
  obtain ⟨hs, hy⟩ := as_ofReal hy0 hyt
  rw [hx, hy, fv_pos c hr, fv_pos c hs]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonpos_left _ hc.le
  apply Real.log_le_log hs
  exact (ENNReal.toReal_le_toReal hyt ht).2 h

theorem lemB {c m : ℝ} (hc : c < 0) (x y : ENNReal)
    (h : ENNReal.ofReal (Real.exp (m / c)) * y ≤ x) :
    ofEReal ((c : EReal) * elog x) ≤ ofEReal ((c : EReal) * elog y) + ENNReal.ofReal m := by
  refine (anti hc h).trans ?_
  have hk : ENNReal.ofReal (Real.exp (m / c)) ≠ 0 := by simp [Real.exp_pos]
  by_cases ht : y = ⊤
  · rw [ht, ENNReal.mul_top hk, fv_top hc]; exact bot_le
  by_cases h0 : y = 0
  · rw [h0, mul_zero, fv_zero hc]; exact le_top.trans (by simp)
  obtain ⟨hr, hy⟩ := as_ofReal h0 ht
  rw [hy, ← ENNReal.ofReal_mul (Real.exp_pos _).le, fv_pos c (mul_pos (Real.exp_pos _) hr), fv_pos c hr,
    Real.log_mul (Real.exp_pos _).ne' hr.ne', Real.log_exp, mul_add, mul_div_cancel₀ _ hc.ne, add_comm]
  exact ENNReal.ofReal_add_le

theorem alpha_one {T' : Type} (p q : PMF T') : RenyiDivergence p q 1 = 0 := by
  simp [RenyiDivergence, RenyiDivergence_def]


variable {T : Type}
variable { U V : Type }
theorem chain (nq1 : List T → PMF U) (nq2 : U -> List T → PMF V) (α : ℝ) (l₁ l₂ : List T) :
    ∑' x : U × V, (privComposeAdaptive nq1 nq2 l₁ x) ^ α * (privComposeAdaptive nq1 nq2 l₂ x) ^ (1 - α)
    = ∑' u, (nq1 l₁ u ^ α * nq1 l₂ u ^ (1 - α)) * ∑' v, (nq2 u l₁ v ^ α * nq2 u l₂ v ^ (1 - α)) := by
  rw [ENNReal.tsum_prod']
  congr 1; funext u
  rw [← ENNReal.tsum_mul_left]
  congr 1; funext v
  erw [privComposeChainRule, privComposeChainRule]
  erw [ENNReal.mul_rpow_of_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  erw [ENNReal.mul_rpow_of_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  ring

variable [HU : Inhabited U] [HU_meas : MeasurableSpace U] [HU_discr : MeasurableSingletonClass U] [HU_count : Countable U]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

theorem lt_one {nq1 : List T → PMF U} {nq2 : U -> List T → PMF V}
    {α : ℝ} (Hα : α < 1) {l₁ l₂ : List T} :
    RenyiDivergence (privComposeAdaptive nq1 nq2 l₁) (privComposeAdaptive nq1 nq2 l₂) α ≤
    RenyiDivergence (nq1 l₁) (nq1 l₂) α + (⨆ (u : U), RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) := by
  have hc : (α - 1)⁻¹ < 0 := inv_lt_zero.2 (by linarith)
  rcases eq_or_ne (⨆ (u : U), RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) ⊤ with hM | hM
  · rw [hM]; exact le_top.trans (add_top _).ge
  set M := ⨆ (u : U), RenyiDivergence (nq2 u l₁) (nq2 u l₂) α with hMdef
  have hMm : M = ENNReal.ofReal M.toReal := (ENNReal.ofReal_toReal hM).symm
  have hk : ∀ u, ENNReal.ofReal (Real.exp (M.toReal / (α - 1)⁻¹)) ≤
      ∑' v, (nq2 u l₁ v ^ α * nq2 u l₂ v ^ (1 - α)) := by
    intro u
    apply lemA hc ENNReal.toReal_nonneg
    rw [← hMm]
    exact le_iSup (fun u => RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) u
  rw [hMm]
  unfold RenyiDivergence RenyiDivergence_def
  apply lemB hc
  refine le_trans ?_ (chain nq1 nq2 α l₁ l₂).ge
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro u
  rw [mul_comm]
  gcongr
  exact hk u

theorem gen1 {nq1 : List T → PMF U} {nq2 : U -> List T → PMF V}
    {α : ℝ} (Hα : 1 < α) {l₁ l₂ : List T} :
    RenyiDivergence (privComposeAdaptive nq1 nq2 l₁) (privComposeAdaptive nq1 nq2 l₂) α ≤
    RenyiDivergence (nq1 l₁) (nq1 l₂) α + (⨆ (u : U), RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) := by
  unfold RenyiDivergence
  rw [<- (GaloisConnection.l_iSup galois_connection_ofReal)]
  rw [<- ofEReal_plus_nonneg ?G1 ?G2]
  case G1 => exact nonneg' (nq1 l₁) (nq1 l₂) Hα
  case G2 =>
    apply le_iSup_iff.mpr
    intro b Hb
    rcases HU with ⟨ u' ⟩
    have Hb := Hb u'
    apply le_trans ?G3 ?G4
    case G4 => apply Hb
    exact nonneg' (nq2 u' l₁) (nq2 u' l₂) Hα
  apply ofEReal_le_mono
  have Hα' : ((1 : ℝ).toEReal < α.toEReal ) := by exact EReal.coe_lt_coe_iff.mpr Hα
  simp at Hα'
  have Hanz : 0 < α.toEReal - 1 := by
    have X : (0 : EReal) = (Real.toEReal 1) - (Real.toEReal 1) := by
      rw [SubNegMonoid.sub_eq_add_neg]
      rw [<- EReal.coe_neg]
      rw [<- EReal.coe_add]
      simp
    rw [X]
    apply EReal.sub_lt_sub_of_lt_of_le
    · apply Hα'
    · simp
    · exact ne_of_beq_false rfl
    · exact ne_of_beq_false rfl
  have Hant : α.toEReal - 1 < ⊤ := by
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  apply ereal_smul_le_left (α.toEReal - 1) Hanz Hant
  rw [ereal_smul_distr_le_left _ Hanz Hant]
  apply eexp_mono_le.mpr
  rw [<- eexp_add]
  rw [RenyiDivergence_def_exp _ _ Hα]
  rw [RenyiDivergence_def_exp (privComposeAdaptive nq1 nq2 l₁) (privComposeAdaptive nq1 nq2 l₂) Hα]
  rw [sup_lemma Hanz Hant]
  conv =>
    enter [2, 2, 1, u]
    rw [RenyiDivergence_def_exp _ _ Hα]
  rw [ENNReal.tsum_prod']
  conv =>
    enter [1, 1, a, 1, b]
    erw [privComposeChainRule]
    erw [privComposeChainRule]
    erw [ENNReal.mul_rpow_of_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
    erw [ENNReal.mul_rpow_of_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  rw [<- ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro a
  conv =>
    enter [1, 1, b]
    rw [mul_assoc]
    right
    rw [mul_comm]
    rw [mul_assoc]
    skip
  conv =>
    enter [1, 1, b]
    rw [<- mul_assoc]
    skip
  rw [ENNReal.tsum_mul_left]
  apply _root_.mul_le_mul_right
  conv =>
    enter [1, 1, b]
    rw [mul_comm]
  exact le_iSup_iff.mpr fun b a_1 => a_1 a

theorem genAll {nq1 : List T → PMF U} {nq2 : U -> List T → PMF V}
    {α : ℝ} {l₁ l₂ : List T} :
    RenyiDivergence (privComposeAdaptive nq1 nq2 l₁) (privComposeAdaptive nq1 nq2 l₂) α ≤
    RenyiDivergence (nq1 l₁) (nq1 l₂) α + (⨆ (u : U), RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) := by
  rcases lt_trichotomy α 1 with h | h | h
  · exact lt_one h
  · subst h; refine le_trans (le_of_eq (alpha_one _ _)) ?_; exact _root_.zero_le
  · exact gen1 h

end T1c5

-- `SLang.privComposeAdaptive_renyi_bound` idx 16: removable
theorem t5_1 : drop% SLang.privComposeAdaptive_renyi_bound 16 := by
  intros; exact T1c5.gen1 (by assumption)

-- `SLang.privComposeAdaptive_renyi_bound` idx 17: removable
theorem t5_2 : drop% SLang.privComposeAdaptive_renyi_bound 17 := by
  intros; exact T1c5.gen1 (by assumption)

-- `SLang.privComposeAdaptive_renyi_bound` idx 18: removable
theorem t5_3 : drop% SLang.privComposeAdaptive_renyi_bound 18 := by
  intros; exact T1c5.gen1 (by assumption)

-- `SLang.privComposeAdaptive_renyi_bound` idx 13: removable
theorem t5_4 : drop% SLang.privComposeAdaptive_renyi_bound 13 := by
  intros; exact T1c5.genAll
