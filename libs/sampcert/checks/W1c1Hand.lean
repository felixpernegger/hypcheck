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

namespace W1c1
theorem e11 : (1:EReal) - 1 = 0 := EReal.sub_self (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)
theorem cs1 (a : ℝ) : (a : EReal) - 1 = ((a - 1 : ℝ) : EReal) := by rw [EReal.coe_sub, EReal.coe_one]
theorem two_le_e : (2:ENNReal) ≤ ENNReal.ofReal (Real.exp 1) := by
  rw [← ENNReal.ofReal_ofNat 2]
  exact ENNReal.ofReal_le_ofReal (by have := Real.add_one_lt_exp (x := (1:ℝ)) one_ne_zero; linarith)
theorem hqp_fail (ε : NNReal) : ¬ ∀ x : Bool, ENNReal.ofReal (Real.exp (-↑ε)) ≤ (PMF.pure true) x / (PMF.uniformOfFintype Bool) x :=
  fun H => by have := H false; simp at this; exact absurd this (Real.exp_pos _).not_ge
theorem hpq1 : ∀ x : Bool, (PMF.pure true) x / (PMF.uniformOfFintype Bool) x ≤ ENNReal.ofReal (Real.exp ↑(1:NNReal)) := by
  intro x; cases x <;> simp
  linarith [Real.add_one_lt_exp (x := (1:ℝ)) one_ne_zero]
theorem hac1 : AbsCts ⇑(PMF.pure true) ⇑(PMF.uniformOfFintype Bool) := fun x hx => by simp at hx
theorem D_zero (δ : NNReal) (h : δ = 0 ∨ 1 ≤ δ) : SLang.zCDP_of_adp_def.D δ = 0 := by
  unfold SLang.zCDP_of_adp_def.D
  rw [show (1:ℝ)/(2:ℝ) = 1/2 by norm_num, ← Real.sqrt_eq_rpow]
  apply Real.sqrt_eq_zero'.mpr
  rcases h with h | h
  · subst h; simp
  · have : Real.log (1 / (δ:ℝ)) ≤ 0 := by
      rw [one_div, Real.log_inv]; have : (1:ℝ) ≤ δ := by exact_mod_cast h
      linarith [Real.log_nonneg this]
    linarith
theorem eqε_D0 (ε' δ : NNReal) (hD : SLang.zCDP_of_adp_def.D δ = 0) :
    (ε' : ℝ) = ↑(SLang.zCDP_of_adp_def.ε ε' δ) ^ 2 / ↑(2:NNReal) + ↑(SLang.zCDP_of_adp_def.ε ε' δ) * SLang.zCDP_of_adp_def.D δ := by
  rw [hD, mul_zero, add_zero]; unfold SLang.zCDP_of_adp_def.ε; rw [hD]
  simp [discrim]
  rw [show (2:ℝ)⁻¹ = 1/2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [max_eq_left (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  ring
theorem nb1 : Neighbour [()] ([] : List Unit) := Neighbour.Deletion (a := []) (b := []) (n := ()) (by simp) (by simp)
theorem notAC : ¬ SLang.ACNeighbour (fun l : List Unit => (PMF.pure l.length : PMF ℕ)) := fun h => by
  have := h [()] [] nb1 1 (by simp); simp at this
theorem renyi_top : RenyiDivergence (PMF.pure 1 : PMF ℕ) (PMF.pure 0) 2 = ⊤ := by
  unfold RenyiDivergence RenyiDivergence_def
  have : ∑' x : ℕ, (PMF.pure 1 : PMF ℕ) x ^ (2:ℝ) * (PMF.pure 0 : PMF ℕ) x ^ (1 - (2:ℝ)) = ⊤ :=
    ENNReal.tsum_eq_top_of_eq_top ⟨1, by simp [ENNReal.zero_rpow_of_neg]⟩
  rw [this]; simp
theorem ac_of_renyi {U : Type} (p q : PMF U) (α : ℝ) (hα : 1 < α) (h : RenyiDivergence p q α ≠ ⊤) :
    AbsCts p q := by
  intro x hx; by_contra hp
  apply h
  unfold RenyiDivergence RenyiDivergence_def
  have : ∑' y, p y ^ α * q y ^ (1 - α) = ⊤ := ENNReal.tsum_eq_top_of_eq_top ⟨x, by
    rw [hx, ENNReal.zero_rpow_of_neg (by linarith)]
    exact ENNReal.mul_top (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hp) (PMF.apply_ne_top p x)).ne'⟩
  rw [this, ENNReal.elog_top]
  first
    | rw [EReal.coe_mul_top_of_pos (inv_pos.mpr (by linarith))]
    | rw [← EReal.coe_inv, EReal.coe_mul_top_of_pos (inv_pos.mpr (by linarith))]
  simp
open scoped Classical in
theorem comp_apply {T U V : Type} (nq1 : SLang.Mechanism T U) (nq2 : U → SLang.Mechanism T V)
    (l : List T) (u : U) (v : V) :
    (SLang.privComposeAdaptive nq1 nq2 l).1 (u, v) = (nq1 l).1 u * (nq2 u l).1 v := by
  simp [SLang.privComposeAdaptive, Bind.bind, Pure.pure, SLang.probBind, SLang.probPure]
  exact SLang.compose_sum_rw_adaptive nq1 nq2 u v l
noncomputable def cst1 : SLang.Mechanism Unit Unit := fun _ => SLang.SPMF_pure ()
noncomputable def len1 : SLang.Mechanism Unit ℕ := fun l => SLang.SPMF_pure l.length
theorem msc_top (X : Type) : @MeasurableSingletonClass X ⊤ := @MeasurableSingletonClass.mk X ⊤ (fun _ => MeasurableSpace.measurableSet_top)
theorem renyi_self {X : Type} (p : PMF X) {α : ℝ} (hα : 1 < α) : RenyiDivergence p p α = 0 := by
  unfold RenyiDivergence; rw [← RenyiDivergence_refl_zero p hα]; simp
theorem spmf_apply {α : Type} (p : SLang.SPMF α) (a : α) : p a = p.1 a := rfl
theorem pw (a b : ENNReal) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (α : ℝ) (hab : a ≠ 0) (hbb : b ≠ 0) :
    a * (a / b) ^ (α - 1) = a ^ α * b ^ (1 - α) := by
  rw [div_eq_mul_inv, ENNReal.mul_rpow_of_ne_top ha (ENNReal.inv_ne_top.mpr hbb), ← mul_assoc]
  congr 1
  · rw [show a ^ α = a ^ ((1:ℝ) + (α - 1)) by ring_nf, ENNReal.rpow_add _ _ hab ha, ENNReal.rpow_one]
  · rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg, neg_sub]
noncomputable def S4 : ℝ := (2 * Real.log (1 / ((1/4:NNReal):ℝ))) ^ (1/2:ℝ)
theorem S4_sq : S4 ^ 2 = 2 * Real.log 4 := by
  unfold S4; rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · norm_num
  · have : (0:ℝ) ≤ Real.log (1 / ((1/4:NNReal):ℝ)) := Real.log_nonneg (by norm_num)
    linarith
theorem dp_fail : ¬ SLang.DP' cst1 ((-S4)^2/2 + (-S4) * S4) (1/4) := fun H => by
  have hε' : (-S4)^2/2 + (-S4) * S4 = -Real.log 4 := by nlinarith [S4_sq]
  rw [hε'] at H
  have := H [()] [] nb1 Set.univ
  rw [Real.exp_neg, Real.exp_log (by norm_num)] at this
  simp [cst1, spmf_apply, SLang.SPMF_pure, SLang.probPure] at this
  have := ENNReal.toReal_mono (by simp) this
  rw [ENNReal.toReal_add (by simp) (by simp)] at this
  norm_num at this
theorem t_lt_one (x y : ℝ) : SLang.t x y < 1 := by
  unfold SLang.t
  have a := Real.abs_tanh_lt_one (x/2); have b := Real.abs_tanh_lt_one (y/2)
  refine lt_of_le_of_lt (le_abs_self _) ?_
  rw [abs_mul]; nlinarith [abs_nonneg (Real.tanh (x/2)), abs_nonneg (Real.tanh (y/2))]
theorem tanh_ratio (w : ℝ) : (1 + Real.tanh w) / (1 - Real.tanh w) = Real.exp (2 * w) := by
  have hc := Real.cosh_pos w
  rw [Real.tanh_eq_sinh_div_cosh]
  have e1 : 1 + Real.sinh w / Real.cosh w = Real.exp w / Real.cosh w := by
    rw [← Real.cosh_add_sinh]; field_simp
  have e2 : 1 - Real.sinh w / Real.cosh w = Real.exp (-w) / Real.cosh w := by
    rw [← Real.cosh_sub_sinh]; field_simp
  rw [e1, e2, div_div_div_cancel_right₀ (ne_of_gt hc), ← Real.exp_sub]; ring_nf
theorem exp_one_lt_four : Real.exp 1 < 4 := by
  have h1 : 1 - 1/2 < Real.exp (-(1/2)) := by
    have := Real.add_one_lt_exp (x := -(1/2)) (by norm_num); linarith
  have h2 : Real.exp (1/2) < 2 := by
    rw [Real.exp_neg] at h1
    have hp := Real.exp_pos (1/2)
    rw [lt_inv_comm₀ (by norm_num) hp] at h1
    linarith
  have : Real.exp 1 = Real.exp (1/2) * Real.exp (1/2) := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith [Real.exp_pos (1/2)]
noncomputable def pB : PMF Bool := PMF.bernoulli (199/200) (by apply div_le_one_of_le₀ <;> norm_num)
noncomputable def qB : PMF Bool := PMF.bernoulli (1/200) (by apply div_le_one_of_le₀ <;> norm_num)
noncomputable def mB : List Unit → PMF Bool := fun l => if l = [] then pB else qB
theorem pB_ne (x : Bool) : pB x ≠ 0 := by
  unfold pB; rw [PMF.bernoulli_apply]
  cases x
  · simp only [cond_false]; exact ENNReal.coe_ne_zero.mpr (tsub_pos_of_lt (by norm_num)).ne'
  · simp only [cond_true]; exact ENNReal.coe_ne_zero.mpr (by norm_num)
theorem qB_ne (x : Bool) : qB x ≠ 0 := by
  unfold qB; rw [PMF.bernoulli_apply]
  cases x
  · simp only [cond_false]; exact ENNReal.coe_ne_zero.mpr (tsub_pos_of_lt (by norm_num)).ne'
  · simp only [cond_true]; exact ENNReal.coe_ne_zero.mpr (by norm_num)
theorem mB_ac : SLang.ACNeighbour mB := fun l₁ l₂ _ x hx => by
  exfalso
  unfold mB at hx
  rcases em (l₂ = []) with hl | hl
  · rw [if_pos hl] at hx; exact pB_ne x hx
  · rw [if_neg hl] at hx; exact qB_ne x hx
theorem nbA : Neighbour ([] : List Unit) [()] := Neighbour.Addition (a := []) (b := []) (n := ()) (by simp) (by simp)
theorem eps_bound : Real.exp ((1:ℝ) ^ 2 / 2 + 1 * (2 * Real.log (1 / ((1/2 : NNReal) : ℝ))) ^ (1/2:ℝ)) < 64 := by
  have hl : Real.log (1 / ((1/2 : NNReal) : ℝ)) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / ((1/2 : NNReal) : ℝ) by norm_num)
    norm_num at this ⊢; linarith
  have hl0 : 0 ≤ Real.log (1 / ((1/2 : NNReal) : ℝ)) := Real.log_nonneg (by norm_num)
  have hs : (2 * Real.log (1 / ((1/2 : NNReal) : ℝ))) ^ (1/2:ℝ) ≤ 2 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]; nlinarith
  have h3 : Real.exp 3 < 64 := by
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; have := exp_one_lt_four
    have h0 := Real.exp_pos 1
    nlinarith [pow_lt_pow_left₀ this h0.le (by norm_num : (3:ℕ) ≠ 0)]
  calc _ ≤ Real.exp 3 := Real.exp_le_exp.mpr (by nlinarith)
    _ < 64 := h3
theorem dp_failB : ¬ SLang.DP' mB ((1:ℝ) ^ 2 / 2 + 1 * (2 * Real.log (1 / ((1/2 : NNReal) : ℝ))) ^ (1/2:ℝ)) (1/2) := fun H => by
  have := H [] [()] nbA {true}
  simp only [tsum_bool, Set.mem_singleton_iff, Bool.false_eq_true, if_false, if_true, add_zero, zero_add] at this
  replace this : pB true ≤ ((1/2 : NNReal) : ENNReal) + ENNReal.ofReal (Real.exp ((1:ℝ) ^ 2 / 2 + 1 *
      (2 * Real.log (1 / ((1/2 : NNReal) : ℝ))) ^ (1/2:ℝ))) * qB true := this
  have hE : ENNReal.ofReal (Real.exp ((1:ℝ) ^ 2 / 2 + 1 * (2 * Real.log (1 / ((1/2 : NNReal) : ℝ))) ^ (1/2:ℝ))) ≤ 64 :=
    (ENNReal.ofReal_le_ofReal eps_bound.le).trans_eq (ENNReal.ofReal_ofNat 64)
  have := this.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hE (by positivity)))
  simp only [pB, qB, PMF.bernoulli_apply, cond_true] at this
  norm_cast at this
  norm_num at this
  rw [← NNReal.coe_le_coe] at this; norm_num at this

/-- restriction of a PMF to a set containing its support -/
noncomputable def restr {T : Type} (p : PMF T) (s : Set T) (h : Function.support p ⊆ s) : PMF s :=
  ⟨(⇑p) ∘ (↑), (hasSum_subtype_iff_of_support_subset h).2 (PMF.hasSum_coe_one p)⟩

theorem restr_apply {T : Type} (p : PMF T) (s : Set T) (h : Function.support p ⊆ s) (x : s) :
    restr p s h x = p x := rfl

theorem supp_sub {T : Type} (p q : PMF T) (hac : AbsCts p q) : Function.support p ⊆ q.support := by
  intro x hx; rw [PMF.mem_support_iff]; exact fun h => hx (hac x h)

open SLang
open scoped Classical
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

theorem dsum1 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (S : Set U) :
    ∑' x : pset m l₁ l₂, (if x.1 ∈ S then (mres m l₁ l₂ l₁).1 x else 0) =
      ∑' x : U, if x ∈ S then (m l₁).1 x else 0 := by
  simp only [mres_val1]
  exact tsum_subtype_eq_of_support_subset (supp_ite1 m l₁ l₂ (fun a => a ∈ S))
theorem dsum2 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (S : Set U) :
    ∑' x : pset m l₁ l₂, (if x.1 ∈ S then (mres m l₁ l₂ l₂).1 x else 0) =
      ∑' x : U, if x ∈ S then (m l₂).1 x else 0 := by
  simp only [mres_val2]
  exact tsum_subtype_eq_of_support_subset (supp_ite2 m l₁ l₂ (fun a => a ∈ S))
theorem lb200 (l : List Unit) (x : Bool) : (1:ENNReal) ≤ 200 * mB l x := by
  have key : ∀ c : NNReal, 1/200 ≤ c → (1:ENNReal) ≤ 200 * (c : ENNReal) := fun c hc => by
    have : (1:NNReal) ≤ 200 * c := by
      have := mul_le_mul_of_nonneg_left hc (show (0:NNReal) ≤ 200 by positivity)
      rwa [show (200:NNReal) * (1/200) = 1 by norm_num] at this
    exact_mod_cast this
  unfold mB
  rcases em (l = []) with hl | hl
  · rw [if_pos hl]; unfold pB; rw [PMF.bernoulli_apply]
    cases x
    · exact key _ (le_tsub_of_add_le_left (by rw [← NNReal.coe_le_coe]; norm_num))
    · exact key _ (by rw [← NNReal.coe_le_coe]; norm_num)
  · rw [if_neg hl]; unfold qB; rw [PMF.bernoulli_apply]
    cases x
    · exact key _ (le_tsub_of_add_le_left (by rw [← NNReal.coe_le_coe]; norm_num))
    · exact key _ (by rw [← NNReal.coe_le_coe]; norm_num)
theorem mB_bound : SLang.zCDPBound mB 10 := by
  intro α hα l₁ l₂ _
  apply RenyiDivergence_le_MaxDivergence hα
  intro t
  rw [EReal.coe_ennreal_ofReal, max_eq_left (by positivity), ENNReal.eexp_ofReal]
  have h1 : mB l₁ t / mB l₂ t ≤ 200 := by
    apply ENNReal.div_le_of_le_mul
    exact (PMF.coe_le_one _ _).trans (lb200 l₂ t)
  refine h1.trans ?_
  have he : 2 < Real.exp 1 := by have := Real.add_one_lt_exp (x := (1:ℝ)) one_ne_zero; linarith
  have h10 : (200:ℝ) ≤ Real.exp (10 * α) := by
    have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : (2:ℝ) ^ 10 ≤ Real.exp 10 := by rw [this]; exact pow_le_pow_left₀ (by norm_num) he.le 10
    have h3 : Real.exp 10 ≤ Real.exp (10 * α) := Real.exp_le_exp.mpr (by nlinarith)
    norm_num at h2; linarith
  rw [← ENNReal.ofReal_ofNat 200]
  exact ENNReal.ofReal_le_ofReal h10
theorem pq_ne : pB true ≠ qB true := by
  unfold pB qB; rw [PMF.bernoulli_apply, PMF.bernoulli_apply]
  simp only [cond_true, ne_eq, ENNReal.coe_inj]; norm_num
theorem msc_bool : @MeasurableSingletonClass Bool ⊤ := msc_top Bool
noncomputable def cstP : List Unit → PMF Unit := fun _ => PMF.pure ()
theorem cstP_ac : SLang.ACNeighbour cstP := fun _ _ _ _ h => h
theorem cstP_bound (r : ℝ) : SLang.zCDPBound cstP r := fun α hα l₁ l₂ _ => by
  show RenyiDivergence (PMF.pure ()) (PMF.pure ()) α ≤ _
  rw [renyi_self _ hα]; positivity
theorem not_zero_bound {X : Type} [Countable X] (m : List Unit → PMF X) (hac : AbsCts (m []) (m [()]))
    (hne : m [] ≠ m [()]) : ¬ SLang.zCDPBound m 0 := fun h => by
  have := h 2 (by norm_num) [] [()] nbA
  simp at this
  exact hne ((@RenyiDivergence_aux_zero X ⊤ (msc_top X) _ (m []) (m [()]) 2 (by norm_num) hac).mpr this)
theorem cstP_one' (l : List Unit) : (cstP l).1 () = 1 := by show PMF.pure () () = 1; simp
noncomputable def eps4 : NNReal := ⟨Real.log 4, Real.log_nonneg (by norm_num)⟩
theorem eps4_exp : Real.exp (eps4 : ℝ) = 4 := Real.exp_log (by norm_num)
theorem eps4_exp_neg : Real.exp (-(eps4 : ℝ)) = 4⁻¹ := by rw [Real.exp_neg, eps4_exp]
theorem eps4_pos : 0 < eps4 := by
  rw [← NNReal.coe_pos]; show 0 < Real.log 4; exact Real.log_pos (by norm_num)
theorem hqp4 : ∀ x : Unit, ENNReal.ofReal (Real.exp (-(eps4 : ℝ))) ≤
    (PMF.pure ()) x / (PMF.pure ()) x := by
  intro x; rw [eps4_exp_neg]; simp
theorem beta4 : SLang.β eps4 (PMF.pure ()) (PMF.pure ()) () = ENNReal.ofReal (4/5) := by
  unfold SLang.β
  rw [eps4_exp, eps4_exp_neg]
  have hd : (PMF.pure ()) () / (PMF.pure ()) () = ENNReal.ofReal 1 := by simp
  rw [hd, ← ENNReal.ofReal_sub _ zero_le_one, ← ENNReal.ofReal_sub _ (by norm_num),
    ← ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num
theorem apmf_false : (SLang.A_pmf eps4 (PMF.pure ()) (PMF.pure ()) hqp4 ()) false = ENNReal.ofReal (4/5) :=
  beta4
theorem apmf_true : (SLang.A_pmf eps4 (PMF.pure ()) (PMF.pure ()) hqp4 ()) true = ENNReal.ofReal (1/5) := by
  show 1 - SLang.β eps4 (PMF.pure ()) (PMF.pure ()) () = _
  rw [beta4, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
  norm_num
noncomputable def bpm (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => if b then ENNReal.ofReal a else ENNReal.ofReal (1 - a)) (by
    rw [Fintype.sum_bool]; simp only [if_true, Bool.false_eq_true, if_false]
    rw [← ENNReal.ofReal_add ha0 (by linarith)]; simp)
theorem bpm_t (a : ℝ) h0 h1 : bpm a h0 h1 true = ENNReal.ofReal a := by simp [bpm]
theorem bpm_f (a : ℝ) h0 h1 : bpm a h0 h1 false = ENNReal.ofReal (1 - a) := by simp [bpm]
noncomputable def pH : PMF Bool := bpm (1/2) (by norm_num) (by norm_num)
noncomputable def qT : PMF Bool := bpm (1/10) (by norm_num) (by norm_num)
theorem rt : pH true / qT true = ENNReal.ofReal 5 := by
  rw [pH, qT, bpm_t, bpm_t, ← ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
theorem rf : pH false / qT false = ENNReal.ofReal (5/9) := by
  rw [pH, qT, bpm_f, bpm_f, ← ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
theorem hqpH : ∀ x : Bool, ENNReal.ofReal (Real.exp (-(eps4 : ℝ))) ≤ pH x / qT x := by
  intro x; rw [eps4_exp_neg]; cases x
  · rw [rf]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  · rw [rt]; exact ENNReal.ofReal_le_ofReal (by norm_num)
theorem hacH : AbsCts pH qT := fun x hx => by
  cases x
  · rw [qT, bpm_f] at hx; simp at hx; try norm_num at hx
  · rw [qT, bpm_t] at hx; simp at hx; try norm_num at hx
theorem betaH (x : Bool) (r : ℝ) (hr : pH x / qT x = ENNReal.ofReal r) (hr0 : 0 ≤ r) :
    SLang.β eps4 pH qT x = ENNReal.ofReal ((4 - r) / (4 - 4⁻¹)) := by
  unfold SLang.β
  rw [eps4_exp, eps4_exp_neg, hr, ← ENNReal.ofReal_sub _ hr0, ← ENNReal.ofReal_sub _ (by norm_num),
    ← ENNReal.ofReal_div_of_pos (by norm_num)]
theorem bt : SLang.β eps4 pH qT true = 0 := by
  rw [betaH true 5 rt (by norm_num)]; exact ENNReal.ofReal_of_nonpos (by norm_num)
theorem bf : SLang.β eps4 pH qT false = ENNReal.ofReal (124/135) := by
  rw [betaH false (5/9) rf (by norm_num)]; norm_num
theorem div_swap (x y z w : ℝ) : (x - y) / (z - w) = (y - x) / (w - z) := by
  rw [← neg_sub y x, ← neg_sub w z, neg_div_neg_eq]
theorem sinh_big (ε α : ℝ) (hε : 0 < ε) (hα : 1 < α) (h2 : 2 ≤ ε * α) :
    Real.exp (-ε) ^ α * ((Real.exp ε - 1) / (Real.exp ε - Real.exp (-ε))) +
    Real.exp ε ^ α * ((1 - Real.exp (-ε)) / (Real.exp ε - Real.exp (-ε))) ≤
    Real.exp ((α - 1) * (1/2 * ε^2 * α)) := by
  rw [← Real.exp_mul, ← Real.exp_mul]
  have ha : 1 < Real.exp ε := by have := Real.add_one_lt_exp hε.ne'; linarith
  have hb : Real.exp (-ε) < 1 := by rw [Real.exp_neg]; exact inv_lt_one_of_one_lt₀ ha
  have hD : 0 < Real.exp ε - Real.exp (-ε) := by linarith
  have hw1 : 0 ≤ (Real.exp ε - 1) / (Real.exp ε - Real.exp (-ε)) := div_nonneg (by linarith) hD.le
  have hw2 : 0 ≤ (1 - Real.exp (-ε)) / (Real.exp ε - Real.exp (-ε)) := div_nonneg (by linarith) hD.le
  set M := Real.exp (ε * (α - 1))
  have e1 : Real.exp (-ε * α) ≤ Real.exp (-ε) * M := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  have e2 : Real.exp (ε * α) = Real.exp ε * M := by rw [← Real.exp_add]; ring_nf
  have hsum : Real.exp (-ε) * ((Real.exp ε - 1) / (Real.exp ε - Real.exp (-ε))) +
      Real.exp ε * ((1 - Real.exp (-ε)) / (Real.exp ε - Real.exp (-ε))) = 1 := by
    field_simp; ring
  have hM : M ≤ Real.exp ((α - 1) * (1/2 * ε^2 * α)) := Real.exp_le_exp.mpr (by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hα.le) hε.le) (show 0 ≤ ε * α / 2 - 1 by linarith)])
  calc Real.exp (-ε * α) * ((Real.exp ε - 1) / (Real.exp ε - Real.exp (-ε))) +
        Real.exp (ε * α) * ((1 - Real.exp (-ε)) / (Real.exp ε - Real.exp (-ε)))
      ≤ Real.exp (-ε) * M * ((Real.exp ε - 1) / (Real.exp ε - Real.exp (-ε))) +
        Real.exp ε * M * ((1 - Real.exp (-ε)) / (Real.exp ε - Real.exp (-ε))) := by
        rw [e2]; gcongr
    _ = M * (Real.exp (-ε) * ((Real.exp ε - 1) / (Real.exp ε - Real.exp (-ε))) +
      Real.exp ε * ((1 - Real.exp (-ε)) / (Real.exp ε - Real.exp (-ε)))) := by ring
    _ ≤ _ := by rw [hsum, mul_one]; exact hM
theorem dtanh_lin (a z : ℝ) : HasDerivAt (fun z => Real.tanh (a * z)) (1 / Real.cosh (a * z) ^ 2 * a) z := by
  have h1 : HasDerivAt Real.tanh (1 / Real.cosh (a * z) ^ 2) (a * z) := by
    rw [← SLang.deriv.deriv_tanh]
    exact (show DifferentiableAt ℝ Real.tanh (a * z) by
      apply Differentiable.differentiableAt; apply Differentiable.differentiable_tanh).hasDerivAt
  have h2 : HasDerivAt (fun z => a * z) a z := by simpa using (hasDerivAt_id z).const_mul a
  exact h1.comp z h2
theorem dform (x z : ℝ) : deriv (fun z => Real.tanh (x * z / 4) - Real.tanh (x / 2) * Real.tanh (z / 2)) z =
    1 / Real.cosh (x / 4 * z) ^ 2 * (x / 4) - Real.tanh (x / 2) * (1 / Real.cosh (1 / 2 * z) ^ 2 * (1 / 2)) := by
  have e : (fun z => Real.tanh (x * z / 4) - Real.tanh (x / 2) * Real.tanh (z / 2)) =
      (fun z => Real.tanh (x / 4 * z) - Real.tanh (x / 2) * Real.tanh (1 / 2 * z)) := by
    funext w; ring_nf
  rw [e]
  exact ((dtanh_lin (x/4) z).sub ((dtanh_lin (1/2) z).const_mul (Real.tanh (x / 2)))).deriv
theorem tanh_mono {u v : ℝ} (h : u ≤ v) : Real.tanh u ≤ Real.tanh v := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, div_le_div_iff₀ (Real.cosh_pos u) (Real.cosh_pos v),
    Real.sinh_eq, Real.sinh_eq, Real.cosh_eq, Real.cosh_eq]
  have : Real.exp u * Real.exp (-v) ≤ Real.exp (-u) * Real.exp v := by
    rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  nlinarith
theorem step3_all (x y : ℝ) (Hy : 0 ≤ y) (Hyx : y < x) :
    Real.tanh (x / 2) * Real.tanh (y / 2) ≤ Real.tanh (x * y / 4) := by
  by_cases hx : x ≤ 2
  · exact SLang.lemma_step_3 x y Hy Hyx hx
  · have h0 : 0 ≤ Real.tanh (y / 2) := SLang.tanh_nonneg (by linarith)
    have h1 := Real.tanh_lt_one (x / 2)
    calc Real.tanh (x / 2) * Real.tanh (y / 2) ≤ 1 * Real.tanh (y / 2) := mul_le_mul_of_nonneg_right h1.le h0
      _ = Real.tanh (y / 2) := one_mul _
      _ ≤ Real.tanh (x * y / 4) := tanh_mono (by nlinarith)
theorem cstP_one (l : List Unit) : (cstP l).1 () = 1 := by show PMF.pure () () = 1; simp
theorem tanh_pos' {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)
theorem sinh_key : Real.exp (-1) < (Real.sinh 1 + Real.sinh 2) / Real.sinh 3 := by
  have hu : 2 < Real.exp 1 := by have := Real.add_one_lt_exp (x := (1:ℝ)) one_ne_zero; linarith
  have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : 0 < Real.sinh 3 := Real.sinh_pos_iff.mpr (by norm_num)
  rw [lt_div_iff₀ h3]
  simp only [Real.sinh_eq, Real.exp_neg, e2, e3]
  generalize Real.exp 1 = u at *
  have hv : u * u⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  have hv0 : 0 < u⁻¹ := by positivity
  rw [← inv_pow, ← inv_pow]
  generalize u⁻¹ = v at *
  have h1 : v * u ^ 3 = u ^ 2 := by
    calc v * u ^ 3 = (u * v) * u ^ 2 := by ring
      _ = u ^ 2 := by rw [hv, one_mul]
  have hv2 : v < 1/2 := by nlinarith
  nlinarith [h1, hv2, hv0, sq_nonneg v, mul_pos hv0 hv0]
theorem t0 : ∑' _ : ℤ, (1:ℝ) = 0 := by rw [tsum_const, Nat.card_eq_zero_of_infinite, zero_smul]
end W1c1
open W1c1

-- `SLang.HαSpecial_algebraic` idx 3
theorem c_1 : ¬ drop0% SLang.HαSpecial_algebraic 3 := fun h => by
  have := @h 0 1 (1/2) (by norm_num); norm_num at this

-- `SLang.ApproximateDP_ε'_nonneg` idx 3
theorem c_2 : drop% SLang.ApproximateDP_ε'_nonneg 3 := by
  intro ε hε δ _; rw [← Real.sqrt_eq_rpow]; positivity

-- `SLang.ApproximateDP_ε'_nonneg` idx 4
theorem c_3 : drop% SLang.ApproximateDP_ε'_nonneg 4 := by
  intro ε hε δ _; rw [← Real.sqrt_eq_rpow]; positivity

-- `SLang.ApproximateDP_ε'_nonneg` idx 1
theorem c_4 : ¬ drop0% SLang.ApproximateDP_ε'_nonneg 1 := fun h => by
  have h := h (-1) (1/2) (by norm_num) (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h
  have hl : 1 - (2:ℝ)⁻¹ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hs : (1/2:ℝ) < Real.sqrt (2 * Real.log 2) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith
  have e : (1:ℝ) / ((1/2 : NNReal) : ℝ) = 2 := by norm_num
  rw [e] at h; nlinarith

-- `SLang.ApproximateDP_α_gt_one` idx 1
theorem c_5 : ¬ drop0% SLang.ApproximateDP_α_gt_one 1 := fun h => by
  have := h 0 (1/2) (by norm_num) (by norm_num); simp [e11, cs1] at this

-- `SLang.ApproximateDP_α_gt_one` idx 4
theorem c_6 : ¬ drop0% SLang.ApproximateDP_α_gt_one 4 := fun h => by
  have := h 1 (by norm_num) 1 (by norm_num); simp [e11] at this

-- `SLang.ApproximateDP_α_toEReal_sub_one_pos` idx 1
theorem c_7 : ¬ drop0% SLang.ApproximateDP_α_toEReal_sub_one_pos 1 := fun h => by
  have := h 0 (1/2) (by norm_num) (by norm_num); simp [e11, cs1] at this

-- `SLang.ApproximateDP_α_toEReal_sub_one_pos` idx 3
theorem c_8 : ¬ drop0% SLang.ApproximateDP_α_toEReal_sub_one_pos 3 := fun h => by
  have := h 1 (by norm_num) 0 (by norm_num); simp [e11, cs1] at this

-- `SLang.ApproximateDP_α_toEReal_sub_one_pos` idx 4
theorem c_9 : ¬ drop0% SLang.ApproximateDP_α_toEReal_sub_one_pos 4 := fun h => by
  have := h 1 (by norm_num) 1 (by norm_num); simp [e11] at this

-- `SLang.ApproximateDP_HαSpecial_bound` idx 1
theorem c_10 : ¬ drop0% SLang.ApproximateDP_HαSpecial_bound 1 := fun h => by
  have := h 0 (1/2) (by norm_num) (by norm_num) 1 (by simp) 0 (by simp); simp [e11, cs1] at this

-- `SLang.ApproximateDP_HαSpecial_bound` idx 3
theorem c_11 : ¬ drop0% SLang.ApproximateDP_HαSpecial_bound 3 := fun h => by
  have := h 1 (by norm_num) 0 (by norm_num) 1 (by simp) (1/2) (by simp); simp [e11, cs1] at this

-- `SLang.ApproximateDP_HαSpecial_bound` idx 6
theorem c_12 : ¬ drop0% SLang.ApproximateDP_HαSpecial_bound 6 := fun h => by
  have := h 1 (by norm_num) (1/2) (by norm_num) (by norm_num) 1 _ rfl; simp [e11, cs1] at this

-- `SLang.ApproximateDP_ite_eq` idx 2
theorem c_13 : ¬ drop0% SLang.ApproximateDP_ite_eq 2 := fun h => by
  have := h 1 0 le_rfl ⊥ (Classical.dec _) (Classical.dec _); simp [e11, cs1] at this

-- `SLang.ApproximateDP_ite_eq` idx 3
theorem c_14 : ¬ drop0% SLang.ApproximateDP_ite_eq 3 := fun h => by
  have := h 2 (-1) (by rw [cs1]; exact EReal.coe_lt_coe_iff.mpr (by norm_num)) ((-1/2 : ℝ) : EReal) (Classical.dec _) (Classical.dec _)
  simp only [cs1] at this; norm_num at this
  rw [← EReal.coe_neg, ENNReal.eexp_ofReal, ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _), Real.exp_lt_exp] at this
  norm_num at this

-- `SLang.C_ne_zero` idx 2
theorem c_15 : ¬ drop0% SLang.C_ne_zero 2 := fun h => h 1 1 (by simp [SLang.C])

-- `SLang.t_nonneg` idx 2
theorem c_16 : ¬ drop0% SLang.t_nonneg 2 := fun h => by
  have := h 1 (-1) (by norm_num); unfold SLang.t at this
  rw [show (-1:ℝ)/2 = -(1/2) by norm_num, Real.tanh_neg] at this
  nlinarith [tanh_pos' (show (0:ℝ) < 1/2 by norm_num)]

-- `SLang.t_nonneg` idx 3
theorem c_17 : ¬ drop0% SLang.t_nonneg 3 := fun h => by
  have := h (-1) 1 (by norm_num); unfold SLang.t at this
  rw [show (-1:ℝ)/2 = -(1/2) by norm_num, Real.tanh_neg] at this
  nlinarith [tanh_pos' (show (0:ℝ) < 1/2 by norm_num)]

-- `SLang.tanh_nonneg` idx 1
theorem c_18 : ¬ drop0% SLang.tanh_nonneg 1 := fun h => by
  have := @h (-1); rw [Real.tanh_neg] at this; linarith [tanh_pos' (show (0:ℝ) < 1 by norm_num)]

-- `SLang.tanh_lt_id_nonneg` idx 1
theorem c_19 : ¬ drop0% SLang.tanh_lt_id_nonneg 1 := fun h => by
  have := @h (-1); linarith [Real.neg_one_lt_tanh (-1)]

-- `SLang.t_le_one` idx 2
theorem c_20 : drop% SLang.t_le_one 2 := by
  intro x y _; unfold SLang.t
  have a := Real.abs_tanh_lt_one (x/2); have b := Real.abs_tanh_lt_one (y/2)
  refine lt_of_le_of_lt (le_abs_self _) ?_
  rw [abs_mul]; nlinarith [abs_nonneg (Real.tanh (x/2)), abs_nonneg (Real.tanh (y/2))]

-- `SLang.lemma_step_3` idx 2
theorem c_21 : ¬ drop0% SLang.lemma_step_3 2 := fun h => by
  have := h 1 (-2) (by norm_num) (by norm_num)
  rw [show (-2:ℝ)/2 = -1 by norm_num, show (1:ℝ) * -2 / 4 = -(1/2) by norm_num, Real.tanh_neg, Real.tanh_neg] at this
  nlinarith [tanh_pos' (show (0:ℝ) < 1/2 by norm_num), Real.tanh_lt_one 1]

-- `SLang.lemma_step_3` idx 3
theorem c_22 : ¬ drop0% SLang.lemma_step_3 3 := fun h => by
  have := h (-2) 1 (by norm_num) (by norm_num)
  rw [show (-2:ℝ)/2 = -1 by norm_num, show (-2:ℝ) * 1 / 4 = -(1/2) by norm_num, Real.tanh_neg, Real.tanh_neg] at this
  nlinarith [tanh_pos' (show (0:ℝ) < 1/2 by norm_num), Real.tanh_lt_one 1]

-- `SLang.sinh_inequality` idx 2
theorem c_23 : ¬ drop0% SLang.sinh_inequality 2 := fun h => by
  have := h 1 (-2) (by norm_num) (by norm_num)
  rw [show (1:ℝ) - -2 = 3 by norm_num, show (1:ℝ) * -2 / 2 = -1 by norm_num, Real.sinh_neg, sub_neg_eq_add] at this
  linarith [sinh_key]

-- `SLang.sinh_inequality` idx 3
theorem c_24 : ¬ drop0% SLang.sinh_inequality 3 := fun h => by
  have := h (-2) 1 (by norm_num) (by norm_num)
  rw [show (-2:ℝ) - 1 = -3 by norm_num, show (-2:ℝ) * 1 / 2 = -1 by norm_num, Real.sinh_neg, Real.sinh_neg,
    show (-Real.sinh 2 - Real.sinh 1) / -Real.sinh 3 = (Real.sinh 1 + Real.sinh 2) / Real.sinh 3 by ring] at this
  linarith [sinh_key]

-- `SLang.ofDP_bound_SC1` idx 3
theorem c_25 : drop% SLang.ofDP_bound_SC1 3 := by
  intro ε hε α
  have := SLang.ofDP_bound_SC1 ε hε 0 le_rfl
  rw [ENNReal.rpow_zero, one_mul] at this
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top) this

-- `SLang.ofDP_bound_SC2` idx 3
theorem c_26 : drop% SLang.ofDP_bound_SC2 3 := by
  intro ε hε α
  have := SLang.ofDP_bound_SC2 ε hε 0 le_rfl
  rw [ENNReal.rpow_zero, one_mul] at this
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top) this

-- `SLang.B_eval_false_closed_form` idx 1
theorem c_27 : ¬ drop0% SLang.B_eval_false_closed_form 1 := fun h => by
  have := h 0 2⁻¹ (by simp) (by simp [ENNReal.one_sub_inv_two, ENNReal.inv_two_add_inv_two])
  simp [ENNReal.inv_two_add_inv_two] at this

-- `SLang.B_eval_false_closed_form` idx 4
theorem c_28 : ¬ drop0% SLang.B_eval_false_closed_form 4 := fun h => by
  have he : 1 < ENNReal.ofReal (Real.exp 1) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos 1)).mpr
      (by have := Real.add_one_lt_exp (x := (1:ℝ)) one_ne_zero; linarith)
  have hrel : ENNReal.ofReal (Real.exp (-1)) * ENNReal.ofReal (Real.exp 1)
      + ENNReal.ofReal (Real.exp 1) * (1 - ENNReal.ofReal (Real.exp 1)) = 1 := by
    rw [tsub_eq_zero_of_le he.le, mul_zero, add_zero, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  have H := h 1 (by norm_num) (ENNReal.ofReal (Real.exp 1)) ENNReal.ofReal_ne_top (by simpa using hrel)
  simp only [NNReal.coe_one] at H
  have hle : (ENNReal.ofReal (Real.exp 1) - 1) / (ENNReal.ofReal (Real.exp 1) - ENNReal.ofReal (Real.exp (-1))) ≤ 1 := by
    apply ENNReal.div_le_of_le_mul; rw [one_mul]
    exact tsub_le_tsub_left (by rw [ENNReal.ofReal_le_one]; exact Real.exp_le_one_iff.mpr (by norm_num)) _
  rw [← H] at hle; exact absurd hle (not_le.mpr he)

-- `Renyi_sum_SG_nonneg` idx 2
theorem c_29 : drop% Renyi_sum_SG_nonneg 2 := by
  intro σ α μ ν n
  have hg : ∀ m : ℤ, 0 ≤ discrete_gaussian σ m n := fun m => by
    unfold discrete_gaussian gauss_term_ℝ
    exact div_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le)
  exact mul_nonneg (Real.rpow_nonneg (hg _) _) (Real.rpow_nonneg (hg _) _)

-- `Renyi_Gauss_divergence_bound'` idx 2
theorem c_30 : ¬ indep0% Renyi_Gauss_divergence_bound' 2 := fun h => @h 0 2 (by norm_num) 0 0 rfl

-- `Renyi_divergence_bound` idx 1
theorem c_31 : drop% Renyi_divergence_bound 1 := by
  intro σ μ α h'
  by_cases hσ : σ = 0
  · subst hσ
    have hα : α ≠ 0 := by linarith
    simp [RenyiDivergence', gauss_term_ℝ, t0, Real.zero_rpow hα]
  · exact Renyi_divergence_bound hσ μ α h'

-- `SG_Renyi_shift` idx 1
theorem c_32 : drop% SG_Renyi_shift 1 := by
  intro σ α μ ν τ
  by_cases hσ : σ = 0
  · subst hσ; simp [gauss_term_ℝ]
  · exact SG_Renyi_shift hσ α μ ν τ

-- `Renyi_divergence_bound_pre` idx 2
theorem c_33 : drop% Renyi_divergence_bound_pre 2 := by
  intro σ α h' μ ν
  by_cases hσ : σ = 0
  · subst hσ
    have hα : α ≠ 0 := by linarith
    simp [RenyiDivergence', discrete_gaussian, gauss_term_ℝ, t0, Real.zero_rpow hα]
  · exact Renyi_divergence_bound_pre hσ h' μ ν


-- `SLang.zCDP_of_adp_def.eqε` idx 2
theorem c_34 : drop% SLang.zCDP_of_adp_def.eqε 2 := by
  intro ε' δ H1
  rcases eq_or_lt_of_le (show (0:NNReal) ≤ δ by positivity) with h0 | h0
  · exact eqε_D0 ε' δ (D_zero δ (Or.inl h0.symm))
  · exact SLang.zCDP_of_adp_def.eqε ε' δ h0 H1

-- `SLang.zCDP_of_adp_def.eqε` idx 3
theorem c_35 : drop% SLang.zCDP_of_adp_def.eqε 3 := by
  intro ε' δ H0
  by_cases H1 : δ < 1
  · exact SLang.zCDP_of_adp_def.eqε ε' δ H0 H1
  · exact eqε_D0 ε' δ (D_zero δ (Or.inr (not_lt.mp H1)))

-- `SLang.ApproximateDP_HαSpecial_bound` idx 4
theorem c_36 : drop% SLang.ApproximateDP_HαSpecial_bound 4 := by
  intro ε hε δ hδ0 α Dα ε' Dε'
  by_cases hδ1 : (δ:ℝ) < 1
  · exact SLang.ApproximateDP_HαSpecial_bound ε hε δ hδ0 hδ1 α Dα ε' Dε'
  · have S0 : (2 * Real.log (1 / (δ:ℝ))) ^ (1/2:ℝ) = 0 := by
      rw [← Real.sqrt_eq_rpow]; apply Real.sqrt_eq_zero'.mpr
      have : Real.log (1 / (δ:ℝ)) ≤ 0 := by
        rw [one_div, Real.log_inv]; linarith [Real.log_nonneg (not_lt.mp hδ1)]
      linarith
    rw [S0] at Dα; simp at Dα; subst Dα
    have : (1:NNReal) ≤ δ := by exact_mod_cast (not_lt.mp hδ1)
    simp [e11]
    exact_mod_cast this

-- `SLang.ApproximateDP_HαSpecial_bound` idx 8
theorem c_37 : ¬ drop0% SLang.ApproximateDP_HαSpecial_bound 8 := fun h => by
  have H := h 1 one_pos (1/2) (by norm_num) (by norm_num) _ rfl 0
  set S := (2 * Real.log (1 / ((1/2:NNReal):ℝ))) ^ (1/2:ℝ) with hS
  have hl : 0 ≤ Real.log (1 / ((1/2:NNReal):ℝ)) := Real.log_nonneg (by norm_num)
  have hS0 : 0 ≤ S := Real.rpow_nonneg (by linarith) _
  have hpos : (0:EReal) ≤ (↑(1 / 1 * S + 1) - 1) * ↑(ENNReal.ofReal (2⁻¹ * 1 ^ 2 * (1 / 1 * S + 1))) := by
    apply EReal.mul_nonneg
    · rw [cs1]; exact EReal.coe_nonneg.mpr (by linarith)
    · exact EReal.coe_ennreal_nonneg _
  have h1 := ENNReal.eexp_mono_le.mp hpos
  simp only [ENNReal.eexp_zero] at h1
  have h2 := h1.trans H
  simp at h2


-- `SLang.β_le_one` idx 4
theorem c_38 : ¬ drop0% SLang.β_le_one 4 := fun h => by
  have := @h Bool 0 (PMF.pure true) (PMF.pure false) false; simp [SLang.β] at this

-- `SLang.one_sub_β` idx 4
theorem c_39 : ¬ drop0% SLang.one_sub_β 4 := fun h => by
  have := @h Unit 0 (PMF.pure ()) (PMF.pure ()) (by intro x; simp) (); simp [SLang.β] at this

-- `SLang.one_sub_β` idx 5
theorem c_40 : ¬ drop0% SLang.one_sub_β 5 := fun h => by
  have := @h Bool 1 (PMF.pure true) (PMF.pure false) one_pos true; simp [SLang.β] at this
  rw [ENNReal.top_div_of_ne_top (ENNReal.sub_ne_top ENNReal.ofReal_ne_top)] at this
  exact ENNReal.one_ne_top this

-- `SLang.ofDP_bound_ratio_inv` idx 6
theorem c_41 : ¬ drop0% SLang.ofDP_bound_ratio_inv 6 := fun h => by
  have := @h Bool (PMF.uniformOfFintype Bool) (PMF.pure true) 0 true (by simp); simp at this

-- `SLang.A_expectation` idx 4
theorem c_42 : drop% SLang.A_expectation 4 := by
  intro U ε p q Hqp Hpq Hac x
  rcases eq_or_lt_of_le (show (0:NNReal) ≤ ε by positivity) with h0 | hpos
  · subst h0
    have h1 : p x / q x = 1 := le_antisymm (by simpa using Hpq x) (by simpa using Hqp x)
    have hA : ∀ b, SLang.A_val 0 b = 1 := by intro b; cases b <;> simp [SLang.A_val]
    rw [h1]; simp only [hA, one_mul]; exact PMF.tsum_coe _
  · exact SLang.A_expectation ε p q hpos Hqp Hpq Hac x

-- `SLang.A_expectation` idx 5
theorem c_43 : ¬ indep0% SLang.A_expectation 5 := fun h =>
  hqp_fail 1 (@h Bool 1 (PMF.pure true) (PMF.uniformOfFintype Bool) one_pos hpq1 hac1 true)

-- `SLang.B_eval_false` idx 5
theorem c_44 : ¬ indep0% SLang.B_eval_false 5 := fun h =>
  hqp_fail 1 (@h Bool 1 (PMF.pure true) (PMF.uniformOfFintype Bool) one_pos hpq1 hac1)

-- `SLang.B_eval_true` idx 5
theorem c_45 : ¬ indep0% SLang.B_eval_true 5 := fun h =>
  hqp_fail 1 (@h Bool 1 (PMF.pure true) (PMF.uniformOfFintype Bool) one_pos hpq1 hac1)

-- `SLang.A_jensen_real` idx 4
theorem c_46 : ¬ indep0% SLang.A_jensen_real 4 := fun h =>
  hqp_fail 0 (@h Bool 0 (PMF.pure true) (PMF.uniformOfFintype Bool) 2 (by norm_num) true)

-- `SLang.A_jensen` idx 5
theorem c_47 : ¬ indep0% SLang.A_jensen 5 := fun h =>
  hqp_fail 1 (@h Bool 1 (PMF.pure true) (PMF.uniformOfFintype Bool) one_pos 2 (by norm_num) true)

-- `SLang.B_eval_open` idx 4
theorem c_48 : ¬ indep0% SLang.B_eval_open 4 := fun h =>
  hqp_fail 0 (@h Bool 0 (PMF.pure true) (PMF.uniformOfFintype Bool) true)

-- `SLang.B_eval_false` idx 7
theorem c_49 : drop% SLang.B_eval_false 7 := by
  intro U ε p q Hε Hqp Hpq
  refine SLang.B_eval_false ε p q Hε Hqp Hpq (fun x hx => ?_)
  by_contra hne
  have := Hpq x; rw [hx, ENNReal.div_zero hne] at this; simp at this

-- `SLang.B_eval_true` idx 7
theorem c_50 : drop% SLang.B_eval_true 7 := by
  intro U ε p q Hε Hqp Hpq
  refine SLang.B_eval_true ε p q Hε Hqp Hpq (fun x hx => ?_)
  by_contra hne
  have := Hpq x; rw [hx, ENNReal.div_zero hne] at this; simp at this

-- `SLang.B_eval_true` idx 4
theorem c_51 : ¬ drop0% SLang.B_eval_true 4 := fun h => by
  have hqp : ∀ x : Unit, ENNReal.ofReal (Real.exp (-↑(0:NNReal))) ≤ (PMF.pure ()) x / (PMF.pure ()) x := by
    intro x; simp
  have H := @h Unit 0 (PMF.pure ()) (PMF.pure ()) hqp (by intro x; simp) (fun _ h => h)
  rw [SLang.B_eval_open] at H
  have hA : ∀ x, (SLang.A_pmf 0 (PMF.pure ()) (PMF.pure ()) hqp x) true = 1 - SLang.β 0 (PMF.pure ()) (PMF.pure ()) x :=
    fun x => rfl
  simp only [hA] at H
  simp [SLang.β] at H

-- `SLang.B_eval_false` idx 4
theorem c_52 : drop% SLang.B_eval_false 4 := by
  intro U ε p q Hqp Hpq Hac
  rcases eq_or_lt_of_le (show (0:NNReal) ≤ ε by positivity) with h0 | hpos
  · subst h0
    rw [SLang.B_eval_open]
    have hb : ∀ x, (SLang.A_pmf 0 p q Hqp x) false = 0 := fun x => by
      show SLang.β 0 p q x = 0
      have := Hqp x; simp at this
      simp [SLang.β, tsub_eq_zero_of_le this]
    simp [hb]
  · exact SLang.B_eval_false ε p q hpos Hqp Hpq Hac

-- `SLang.ApproximateDP_renyi_tsum_le` idx 7
theorem c_53 : drop% SLang.ApproximateDP_renyi_tsum_le 7 := by
  intro U _ m₁ m₂ Hm12 Hm21 ε α Hα Hα' h
  have := SLang.ApproximateDP_renyi_tsum_le m₁ m₂ Hm12 Hm21 |ε| (abs_nonneg ε) α Hα Hα' (by rwa [sq_abs])
  rwa [sq_abs] at this

-- `SLang.ApproximateDP_renyi_tsum_le` idx 9
theorem c_54 : drop% SLang.ApproximateDP_renyi_tsum_le 9 := by
  intro U _ m₁ m₂ Hm12 Hm21 ε Hε α Hα' h
  have : 1 < α := by
    rw [cs1] at Hα'; have := EReal.coe_pos.mp Hα'; linarith
  exact SLang.ApproximateDP_renyi_tsum_le m₁ m₂ Hm12 Hm21 ε Hε α this Hα' h


-- `SLang.ACNeighbour_of_DP` idx 4
theorem c_55 : ¬ drop0% SLang.ACNeighbour_of_DP 4 := fun h => notAC (h 0 _)

-- `SLang.ofDP` idx 4
theorem c_56 : ¬ drop0% SLang.ofDP 4 := fun h => notAC (h 0 _).1

-- `SLang.zCDP_mono` idx 6
theorem c_57 : ¬ drop0% SLang.zCDP_mono 6 := fun h => notAC (@h Unit ℕ _ 0 0 le_rfl).1

-- `SLang.ofDP_bound` idx 4
theorem c_58 : ¬ drop0% SLang.ofDP_bound 4 := fun h => by
  have := h 0 (fun l : List Unit => (PMF.pure l.length : PMF ℕ)) 2 (by norm_num) [()] [] nb1
  change RenyiDivergence (PMF.pure 1 : PMF ℕ) (PMF.pure 0) 2 ≤ _ at this
  rw [renyi_top, top_le_iff] at this; exact ENNReal.ofReal_ne_top this

-- `SLang.ofDP_bound_large_εα` idx 4
theorem c_59 : ¬ drop0% SLang.ofDP_bound_large_εα 4 := fun h => by
  have := h (fun l : List Unit => (PMF.pure l.length : PMF ℕ)) 3 2 (by norm_num) [()] [] nb1 (by norm_num)
  change RenyiDivergence (PMF.pure 1 : PMF ℕ) (PMF.pure 0) 2 ≤ _ at this
  rw [renyi_top, top_le_iff] at this; exact ENNReal.ofReal_ne_top this

-- `SLang.ApproximateDP_of_zCDP_pos_lt_one` idx 7
theorem c_60 : drop% SLang.ApproximateDP_of_zCDP_pos_lt_one 7 := by
  intro T U _ m ε hε h
  exact SLang.ApproximateDP_of_zCDP_pos_lt_one m ε hε h (fun l₁ l₂ hn =>
    ac_of_renyi _ _ 2 (by norm_num) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h 2 (by norm_num) l₁ l₂ hn)))

-- `SLang.ApproximateDP_of_zCDP_pos` idx 7
theorem c_61 : drop% SLang.ApproximateDP_of_zCDP_pos 7 := by
  intro T U _ m ε hε h
  exact SLang.ApproximateDP_of_zCDP_pos m ε hε h (fun l₁ l₂ hn =>
    ac_of_renyi _ _ 2 (by norm_num) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h 2 (by norm_num) l₁ l₂ hn)))

-- `SLang.ApproximateDP_of_zCDP` idx 7
theorem c_62 : drop% SLang.ApproximateDP_of_zCDP 7 := by
  intro T U _ m ε hε h
  exact SLang.ApproximateDP_of_zCDP m ε hε h (fun l₁ l₂ hn =>
    ac_of_renyi _ _ 2 (by norm_num) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h 2 (by norm_num) l₁ l₂ hn)))

-- `SLang.privComposeAdaptive_zCDPBound` idx 16
theorem c_63 : drop% SLang.privComposeAdaptive_zCDPBound 16 := by
  intro T U V _ _ _ _ _ _ _ nq1 nq2 ε₁ ε₂ h1 h2 hac2 hb1 hb2
  exact SLang.privComposeAdaptive_zCDPBound h1 h2 (fun l₁ l₂ hn =>
    ac_of_renyi _ _ 2 (by norm_num) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb1 2 (by norm_num) l₁ l₂ hn))) hac2 hb1 hb2

-- `SLang.privComposeAdaptive_zCDPBound` idx 17
theorem c_64 : drop% SLang.privComposeAdaptive_zCDPBound 17 := by
  intro T U V _ _ _ _ _ _ _ nq1 nq2 ε₁ ε₂ h1 h2 hac1 hb1 hb2
  exact SLang.privComposeAdaptive_zCDPBound h1 h2 hac1 (fun u l₁ l₂ hn =>
    ac_of_renyi _ _ 2 (by norm_num) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb2 u 2 (by norm_num) l₁ l₂ hn))) hb1 hb2

-- `SLang.ApproximateDP_renyi_tsum_le` idx 4
theorem c_65 : drop% SLang.ApproximateDP_renyi_tsum_le 4 := by
  intro U _ m₁ m₂ Hm21 ε Hε α Hα Hα' h
  exact SLang.ApproximateDP_renyi_tsum_le m₁ m₂
    (ac_of_renyi _ _ α Hα (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)) Hm21 ε Hε α Hα Hα' h

-- `SLang.privComposeAdaptive_renyi_bound` idx 5
theorem c_66 : drop% SLang.privComposeAdaptive_renyi_bound 5 := by
  intro T U V _ _ _ _ _ _ nq1 nq2 α Hα l₁ l₂ HN H1 H2
  exact @SLang.privComposeAdaptive_renyi_bound T U V _ ⊤ (msc_top U) _ _ _ _ nq1 nq2 α Hα l₁ l₂ HN H1 H2

-- `SLang.privComposeAdaptive_renyi_bound` idx 8
theorem c_67 : drop% SLang.privComposeAdaptive_renyi_bound 8 := by
  intro T U V _ _ _ _ _ _ nq1 nq2 α Hα l₁ l₂ HN H1 H2
  exact @SLang.privComposeAdaptive_renyi_bound T U V _ _ _ _ ⊤ (msc_top V) _ nq1 nq2 α Hα l₁ l₂ HN H1 H2

-- `SLang.privComposeAdaptive_zCDPBound` idx 8
theorem c_68 : drop% SLang.privComposeAdaptive_zCDPBound 8 := by
  intro T U V _ _ _ _ _ _ nq1 nq2 ε₁ ε₂ a b c d e f
  exact @SLang.privComposeAdaptive_zCDPBound T U V _ _ _ _ ⊤ (msc_top V) _ nq1 nq2 ε₁ ε₂ a b c d e f

-- `SLang.privComposeAdaptive_zCDP` idx 8
theorem c_69 : drop% SLang.privComposeAdaptive_zCDP 8 := by
  intro T U V _ _ _ _ _ _ nq1 nq2 ε₁ ε₂ a b
  exact @SLang.privComposeAdaptive_zCDP T U V _ _ _ _ ⊤ (msc_top V) _ nq1 nq2 ε₁ ε₂ a b

-- `SLang.privComposeAdaptive_AC` idx 6
theorem c_70 : ¬ drop0% SLang.privComposeAdaptive_AC 6 := fun h => by
  have H := h cst1 (fun _ => len1) (fun l₁ l₂ _ x hx => by simpa [cst1] using hx) [()] [] nb1 ((), 1)
    (by show (SLang.privComposeAdaptive cst1 (fun _ => len1) []).1 ((), 1) = 0
        rw [comp_apply]; simp [cst1, len1, SLang.SPMF_pure, SLang.probPure])
  change (SLang.privComposeAdaptive cst1 (fun _ => len1) [()]).1 ((), 1) = 0 at H
  rw [comp_apply] at H; simp [cst1, len1, SLang.SPMF_pure, SLang.probPure] at H

-- `SLang.privComposeAdaptive_zCDP` idx 14
theorem c_71 : ¬ drop0% SLang.privComposeAdaptive_zCDP 14 := fun h => by
  have H := (@h Unit ℕ Unit _ ⊤ (msc_top ℕ) _ ⊤ (msc_top Unit) _ len1 (fun _ => cst1) 0 0
    (fun _ => ⟨fun l₁ l₂ _ x hx => by simpa [cst1] using hx, fun α hα l₁ l₂ _ => by
      show RenyiDivergence (cst1 []) (cst1 []) α ≤ _
      exact (renyi_self (cst1 []) hα).trans_le (by positivity)⟩)).1
    [()] [] nb1 (1, ())
    (by show (SLang.privComposeAdaptive len1 (fun _ => cst1) []).1 (1, ()) = 0
        rw [comp_apply]; simp [cst1, len1, SLang.SPMF_pure, SLang.probPure])
  change (SLang.privComposeAdaptive len1 (fun _ => cst1) [()]).1 (1, ()) = 0 at H
  rw [comp_apply] at H; simp [cst1, len1, SLang.SPMF_pure, SLang.probPure] at H

-- `SLang.privComposeAdaptive_zCDP` idx 15
theorem c_72 : ¬ drop0% SLang.privComposeAdaptive_zCDP 15 := fun h => by
  have H := (@h Unit Unit ℕ _ ⊤ (msc_top Unit) _ ⊤ (msc_top ℕ) _ cst1 (fun _ => len1) 0 0
    ⟨fun l₁ l₂ _ x hx => by simpa [cst1] using hx, fun α hα l₁ l₂ _ => by
      show RenyiDivergence (cst1 []) (cst1 []) α ≤ _
      exact (renyi_self (cst1 []) hα).trans_le (by positivity)⟩).1
    [()] [] nb1 ((), 1)
    (by show (SLang.privComposeAdaptive cst1 (fun _ => len1) []).1 ((), 1) = 0
        rw [comp_apply]; simp [cst1, len1, SLang.SPMF_pure, SLang.probPure])
  change (SLang.privComposeAdaptive cst1 (fun _ => len1) [()]).1 ((), 1) = 0 at H
  rw [comp_apply] at H; simp [cst1, len1, SLang.SPMF_pure, SLang.probPure] at H

-- `SLang.ApproximateDP_renyi_pointwise_eq` idx 3
theorem c_73 : drop% SLang.ApproximateDP_renyi_pointwise_eq 3 := by
  intro V p q Hqp α Hα u
  rw [cs1, EReal.toReal_coe]
  by_cases hb : q u = 0
  · by_cases ha : p u = 0
    · simp [ha, hb, ENNReal.zero_rpow_of_pos (show (0:ℝ) < α by linarith)]
    · rw [hb, ENNReal.div_zero ha, ENNReal.top_rpow_of_pos (by linarith), ENNReal.mul_top ha,
        ENNReal.zero_rpow_of_neg (by linarith), ENNReal.mul_top]
      exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr ha) (PMF.apply_ne_top p u)).ne'
  · exact pw _ _ (PMF.apply_ne_top p u) (PMF.apply_ne_top q u) α (fun h => hb (Hqp u h)) hb

-- `SLang.ApproximateDP_renyi_pointwise_eq` idx 4
theorem c_74 : drop% SLang.ApproximateDP_renyi_pointwise_eq 4 := by
  intro V p q Hpq α Hα u
  rw [cs1, EReal.toReal_coe]
  by_cases ha : p u = 0
  · simp [ha, ENNReal.zero_rpow_of_pos (show (0:ℝ) < α by linarith)]
  · exact pw _ _ (PMF.apply_ne_top p u) (PMF.apply_ne_top q u) α ha (fun h => ha (Hpq u h))

-- `SLang.ApproximateDP_renyi_pointwise_eq` idx 6
theorem c_75 : drop% SLang.ApproximateDP_renyi_pointwise_eq 6 := by
  intro V p q Hpq Hqp α u
  rw [cs1, EReal.toReal_coe]
  by_cases ha : p u = 0
  · have hb : q u = 0 := Hqp u ha
    rw [ha, hb, zero_mul]
    rcases lt_trichotomy α 1 with h | h | h
    · rw [ENNReal.zero_rpow_of_pos (show (0:ℝ) < 1 - α by linarith), mul_zero]
    · subst h; simp
    · rw [ENNReal.zero_rpow_of_pos (show (0:ℝ) < α by linarith), zero_mul]
  · exact pw _ _ (PMF.apply_ne_top p u) (PMF.apply_ne_top q u) α ha (fun h => ha (Hpq u h))

-- `SLang.zCDP_ApproximateDP` idx 7
theorem c_76 : ¬ drop0% SLang.zCDP_ApproximateDP 7 := fun h => by
  have := @h Unit ℕ _ len1 (1/2) (by norm_num) 0 [()] [] nb1 {1}
  simp [len1, spmf_apply, SLang.SPMF_pure, SLang.probPure] at this

-- `SLang.sup_lemma` idx 3
theorem c_77 : ¬ drop0% SLang.sup_lemma 3 := fun h => by
  have H := @h (Set.Iio (0:EReal)) ⊤ (by simp) Subtype.val
  have hs : (⨆ u : Set.Iio (0:EReal), u.val) = 0 := by
    exact iSup_Iio_eq_self_iff_isSuccPrelimit.mpr (Order.IsSuccPrelimit.of_dense _)
  have hr : ∀ u : Set.Iio (0:EReal), ENNReal.eexp (⊤ * u.val) = 0 := fun u => by
    rw [EReal.top_mul_of_neg u.2]; simp
  rw [hs] at H; simp only [hr] at H; simp at H

-- `SLang.ApproximateDP_of_zCDP_pos_lt_one` idx 5
theorem c_78 : ¬ drop0% SLang.ApproximateDP_of_zCDP_pos_lt_one 5 := fun h => dp_fail
  (@h Unit Unit _ cst1 (-S4) (fun α hα l₁ l₂ _ => by
      show RenyiDivergence (cst1 []) (cst1 []) α ≤ _
      exact (renyi_self (cst1 []) hα).trans_le (by positivity))
    (fun _ _ _ x hx => by simpa [cst1] using hx) (1/4) (by norm_num) (by norm_num))

-- `SLang.ApproximateDP_of_zCDP_pos` idx 5
theorem c_79 : ¬ drop0% SLang.ApproximateDP_of_zCDP_pos 5 := fun h => dp_fail
  (@h Unit Unit _ cst1 (-S4) (fun α hα l₁ l₂ _ => by
      show RenyiDivergence (cst1 []) (cst1 []) α ≤ _
      exact (renyi_self (cst1 []) hα).trans_le (by positivity))
    (fun _ _ _ x hx => by simpa [cst1] using hx) (1/4) (by norm_num))

-- `SLang.ApproximateDP_of_zCDP` idx 5
theorem c_80 : ¬ drop0% SLang.ApproximateDP_of_zCDP 5 := fun h => dp_fail
  (@h Unit Unit _ cst1 (-S4) (fun α hα l₁ l₂ _ => by
      show RenyiDivergence (cst1 []) (cst1 []) α ≤ _
      exact (renyi_self (cst1 []) hα).trans_le (by positivity))
    (fun _ _ _ x hx => by simpa [cst1] using hx) (1/4) (by norm_num))

-- `SLang.lemma_step_2` idx 2
theorem c_81 : drop% SLang.lemma_step_2 2 := by
  intro x y hyx H
  have ht := t_lt_one x y
  have hT := Real.tanh_lt_one (x * y / 4)
  have key := tanh_ratio (x * y / 4)
  rw [show 2 * (x * y / 4) = x * y / 2 by ring] at key
  rw [← key, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

-- `SLang.ofDP_bound_sinh_step` idx 3
theorem c_82 : ¬ drop0% SLang.ofDP_bound_sinh_step 3 := fun h => by
  have H := h 4 (1/2) (by norm_num) (by norm_num)
  have e1 : Real.exp (-4) ^ (1/2:ℝ) = Real.exp (-2) := by rw [← Real.exp_mul]; norm_num
  have e2 : Real.exp 4 ^ (1/2:ℝ) = Real.exp 2 := by rw [← Real.exp_mul]; norm_num
  have e3 : Real.exp 4 = Real.exp 2 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e4 : Real.exp (-4) = (Real.exp 2 ^ 2)⁻¹ := by rw [Real.exp_neg, e3]
  rw [e1, e2, show ((1:ℝ)/2 - 1) * (1/2 * 4^2 * (1/2)) = -2 by norm_num, e4, Real.exp_neg 2, e3] at H
  have hu : 1 < Real.exp 2 := by have := Real.add_one_lt_exp (x := (2:ℝ)) (by norm_num); linarith
  generalize Real.exp 2 = u at H hu
  have hu0 : 0 < u := by linarith
  have key : u⁻¹ * ((u ^ 2 - 1) / (u ^ 2 - (u ^ 2)⁻¹)) + u * ((1 - (u ^ 2)⁻¹) / (u ^ 2 - (u ^ 2)⁻¹))
      = 2 * u / (u ^ 2 + 1) := by
    have h1 : u ^ 2 - (u ^ 2)⁻¹ ≠ 0 := by
      have : (u ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
      nlinarith
    have h2 : (-1 + u ^ 4) ≠ 0 := ne_of_gt (by have : 1 < u^4 := one_lt_pow₀ hu (by norm_num); linarith)
    field_simp
    ring_nf
    field_simp
    ring
  rw [key, div_le_iff₀ (by positivity)] at H
  have : u⁻¹ * (u ^ 2 + 1) < 2 * u := by
    rw [inv_mul_lt_iff₀ hu0]; nlinarith
  linarith

-- `SLang.ApproximateDP_of_zCDP_pos_lt_one` idx 6
theorem c_83 : ¬ drop0% SLang.ApproximateDP_of_zCDP_pos_lt_one 6 := fun h =>
  dp_failB (@h Unit Bool _ mB 1 one_pos mB_ac (1/2) (by norm_num) (by norm_num))

-- `SLang.ApproximateDP_of_zCDP_pos` idx 6
theorem c_84 : ¬ drop0% SLang.ApproximateDP_of_zCDP_pos 6 := fun h =>
  dp_failB (@h Unit Bool _ mB 1 one_pos mB_ac (1/2) (by norm_num))

-- `SLang.ApproximateDP_of_zCDP` idx 6
theorem c_85 : ¬ drop0% SLang.ApproximateDP_of_zCDP 6 := fun h =>
  dp_failB (@h Unit Bool _ mB 1 zero_le_one mB_ac (1/2) (by norm_num))

open scoped Classical in
-- `SLang.ApproximateDP_of_zCDP` idx 2
theorem c_86 : drop% SLang.ApproximateDP_of_zCDP 2 := by
  intro T U m ε hε h Hm δ hδ l₁ l₂ hN S
  have hc := pset_countable m l₁ l₂
  have H := @SLang.ApproximateDP_of_zCDP T (pset m l₁ l₂) hc (mres m l₁ l₂) ε hε (mres_zcdp m _ h l₁ l₂ hN)
    (mres_ac m Hm l₁ l₂ hN) δ hδ l₁ l₂ hN {x | x.1 ∈ S}
  calc (∑' x : U, if x ∈ S then m l₁ x else 0)
      = ∑' x : pset m l₁ l₂, (if x.1 ∈ S then (mres m l₁ l₂ l₁).1 x else 0) := (dsum1 m l₁ l₂ S).symm
    _ ≤ _ := H
    _ = _ := congrArg (HAdd.hAdd _) (congrArg (HMul.hMul _) (dsum2 m l₁ l₂ S))

open scoped Classical in
-- `SLang.ApproximateDP_of_zCDP_pos_lt_one` idx 2
theorem c_87 : drop% SLang.ApproximateDP_of_zCDP_pos_lt_one 2 := by
  intro T U m ε hε h Hm δ hδ hδ1 l₁ l₂ hN S
  have hc := pset_countable m l₁ l₂
  have H := @SLang.ApproximateDP_of_zCDP_pos_lt_one T (pset m l₁ l₂) hc (mres m l₁ l₂) ε hε (mres_zcdp m _ h l₁ l₂ hN)
    (mres_ac m Hm l₁ l₂ hN) δ hδ hδ1 l₁ l₂ hN {x | x.1 ∈ S}
  calc (∑' x : U, if x ∈ S then m l₁ x else 0)
      = ∑' x : pset m l₁ l₂, (if x.1 ∈ S then (mres m l₁ l₂ l₁).1 x else 0) := (dsum1 m l₁ l₂ S).symm
    _ ≤ _ := H
    _ = _ := congrArg (HAdd.hAdd _) (congrArg (HMul.hMul _) (dsum2 m l₁ l₂ S))

open scoped Classical in
-- `SLang.zCDP_ApproximateDP` idx 2
theorem c_88 : drop% SLang.zCDP_ApproximateDP 2 := by
  intro T U m δ hδ ε' hz l₁ l₂ hN S
  have hc := pset_countable m l₁ l₂
  have H := @SLang.zCDP_ApproximateDP T (pset m l₁ l₂) hc (mres m l₁ l₂) δ hδ ε'
    ⟨mres_ac m hz.1 l₁ l₂ hN, mres_zcdp m _ hz.2 l₁ l₂ hN⟩ l₁ l₂ hN {x | x.1 ∈ S}
  calc (∑' x : U, if x ∈ S then m l₁ x else 0)
      = ∑' x : pset m l₁ l₂, (if x.1 ∈ S then (mres m l₁ l₂ l₁).1 x else 0) := (dsum1 m l₁ l₂ S).symm
    _ ≤ _ := H
    _ = _ := congrArg (HAdd.hAdd _) (congrArg (HMul.hMul _) (dsum2 m l₁ l₂ S))

-- `SLang.ApproximateDP_renyi_tsum_le` idx 1
theorem c_89 : drop% SLang.ApproximateDP_renyi_tsum_le 1 := by
  intro U m₁ m₂ Hm12 Hm21 ε Hε α Hα Hα' h
  have hs1 : Function.support m₁ ⊆ m₂.support := supp_sub m₁ m₂ Hm12
  have hs2 : Function.support m₂ ⊆ m₂.support := fun x hx => hx
  have hc : Countable m₂.support := (PMF.support_countable m₂).to_subtype
  have H := @SLang.ApproximateDP_renyi_tsum_le m₂.support hc (restr m₁ _ hs1) (restr m₂ _ hs2)
    (fun x hx => Hm12 x hx) (fun x hx => Hm21 x hx) ε Hε α Hα Hα' (by rw [renyi_restr2 _ _ _ _ _ Hα]; exact h)
  refine le_trans (le_of_eq ?_) H
  refine (tsum_subtype_eq_of_support_subset (s := m₂.support) ?_).symm
  intro x hx
  by_contra hxs
  apply hx
  have h2 : m₂ x = 0 := by rwa [PMF.mem_support_iff, not_not] at hxs
  have h1 : m₁ x = 0 := Hm12 x h2
  simp only [h1, zero_mul]

-- `SLang.zCDP_mono` idx 5
theorem c_90 : ¬ drop0% SLang.zCDP_mono 5 := fun h => by
  have H := (@h Unit Bool mB 10 0 ⟨mB_ac, by exact_mod_cast mB_bound⟩).2
  refine not_zero_bound mB (mB_ac [] [()] nbA) (fun he => pq_ne ?_) (by exact_mod_cast H)
  have := congrArg (fun p : PMF Bool => p true) he
  simpa [mB] using this


-- `SLang.privComposeAdaptive_zCDPBound` idx 14
theorem c_91 : ¬ drop0% SLang.privComposeAdaptive_zCDPBound 14 := fun h => by
  have H := @h Unit Unit Bool _ ⊤ (msc_top Unit) _ ⊤ (msc_top Bool) _ cstP (fun _ => mB) (-10) 10 (by norm_num)
    cstP_ac (fun _ => mB_ac) (cstP_bound _) (fun _ => mB_bound)
  refine not_zero_bound (X := Unit × Bool) (SLang.privComposeAdaptive cstP (fun _ => mB))
    (SLang.privComposeAdaptive_AC cstP (fun _ => mB) cstP_ac (fun _ => mB_ac) [] [()] nbA) (fun he => ?_)
    (by norm_num at H; exact H)
  have := congrArg (fun p : PMF (Unit × Bool) => p ((), true)) he
  change (SLang.privComposeAdaptive cstP (fun _ => mB) []).1 ((), true)
    = (SLang.privComposeAdaptive cstP (fun _ => mB) [()]).1 ((), true) at this
  have e1 : (SLang.privComposeAdaptive cstP (fun _ => mB) []).1 ((), true) = pB true :=
    (comp_apply cstP (fun _ => mB) [] () true).trans (by rw [cstP_one, one_mul]; rfl)
  have e2 : (SLang.privComposeAdaptive cstP (fun _ => mB) [()]).1 ((), true) = qB true :=
    (comp_apply cstP (fun _ => mB) [()] () true).trans (by rw [cstP_one, one_mul]; rfl)
  exact pq_ne (e1.symm.trans (this.trans e2))

-- `SLang.privComposeAdaptive_zCDPBound` idx 15
theorem c_92 : ¬ drop0% SLang.privComposeAdaptive_zCDPBound 15 := fun h => by
  have H := @h Unit Bool Unit _ ⊤ (msc_top Bool) _ ⊤ (msc_top Unit) _ mB (fun _ => cstP) 10 (-10) (by norm_num)
    mB_ac (fun _ => cstP_ac) mB_bound (fun _ => cstP_bound _)
  refine not_zero_bound (X := Bool × Unit) (SLang.privComposeAdaptive mB (fun _ => cstP))
    (SLang.privComposeAdaptive_AC mB (fun _ => cstP) mB_ac (fun _ => cstP_ac) [] [()] nbA) (fun he => ?_)
    (by norm_num at H; exact H)
  have := congrArg (fun p : PMF (Bool × Unit) => p (true, ())) he
  change (SLang.privComposeAdaptive mB (fun _ => cstP) []).1 (true, ())
    = (SLang.privComposeAdaptive mB (fun _ => cstP) [()]).1 (true, ()) at this
  have e1 : (SLang.privComposeAdaptive mB (fun _ => cstP) []).1 (true, ()) = pB true :=
    (comp_apply mB (fun _ => cstP) [] true ()).trans (by rw [cstP_one, mul_one]; rfl)
  have e2 : (SLang.privComposeAdaptive mB (fun _ => cstP) [()]).1 (true, ()) = qB true :=
    (comp_apply mB (fun _ => cstP) [()] true ()).trans (by rw [cstP_one, mul_one]; rfl)
  exact pq_ne (e1.symm.trans (this.trans e2))

-- `SLang.privComposeAdaptive_zCDPBound` idx 18
theorem c_93 : ¬ drop0% SLang.privComposeAdaptive_zCDPBound 18 := fun h => by
  have H := @h Unit Bool Unit _ ⊤ (msc_top Bool) _ ⊤ (msc_top Unit) _ mB (fun _ => cstP) 0 0 le_rfl le_rfl
    mB_ac (fun _ => cstP_ac) (fun _ => cstP_bound _)
  refine not_zero_bound (X := Bool × Unit) (SLang.privComposeAdaptive mB (fun _ => cstP))
    (SLang.privComposeAdaptive_AC mB (fun _ => cstP) mB_ac (fun _ => cstP_ac) [] [()] nbA) (fun he => ?_)
    (by norm_num at H; exact H)
  have := congrArg (fun p : PMF (Bool × Unit) => p (true, ())) he
  have e1 : (SLang.privComposeAdaptive mB (fun _ => cstP) []).1 (true, ()) = pB true :=
    (comp_apply mB (fun _ => cstP) [] true ()).trans (by rw [cstP_one', mul_one]; rfl)
  have e2 : (SLang.privComposeAdaptive mB (fun _ => cstP) [()]).1 (true, ()) = qB true :=
    (comp_apply mB (fun _ => cstP) [()] true ()).trans (by rw [cstP_one', mul_one]; rfl)
  exact pq_ne (e1.symm.trans (this.trans e2))

-- `SLang.privComposeAdaptive_zCDPBound` idx 19
theorem c_94 : ¬ drop0% SLang.privComposeAdaptive_zCDPBound 19 := fun h => by
  have H := @h Unit Unit Bool _ ⊤ (msc_top Unit) _ ⊤ (msc_top Bool) _ cstP (fun _ => mB) 0 0 le_rfl le_rfl
    cstP_ac (fun _ => mB_ac) (cstP_bound _)
  refine not_zero_bound (X := Unit × Bool) (SLang.privComposeAdaptive cstP (fun _ => mB))
    (SLang.privComposeAdaptive_AC cstP (fun _ => mB) cstP_ac (fun _ => mB_ac) [] [()] nbA) (fun he => ?_)
    (by norm_num at H; exact H)
  have := congrArg (fun p : PMF (Unit × Bool) => p ((), true)) he
  have e1 : (SLang.privComposeAdaptive cstP (fun _ => mB) []).1 ((), true) = pB true :=
    (comp_apply cstP (fun _ => mB) [] () true).trans (by rw [cstP_one', one_mul]; rfl)
  have e2 : (SLang.privComposeAdaptive cstP (fun _ => mB) [()]).1 ((), true) = qB true :=
    (comp_apply cstP (fun _ => mB) [()] () true).trans (by rw [cstP_one', one_mul]; rfl)
  exact pq_ne (e1.symm.trans (this.trans e2))

open SLang in
open scoped Classical in
-- `SLang.ApproximateDP_renyi_tsum_le` idx 5
theorem c_95 : drop% SLang.ApproximateDP_renyi_tsum_le 5 := by
  intro U _ m₁ m₂ Hm12 ε Hε α Hα Hα' h
  conv_lhs =>
    rw [show (fun x => m₁ x * (m₁ x / m₂ x) ^ (α.toEReal - 1).toReal) =
           (fun x => m₁ x ^ α * m₂ x ^ (1 - α)) from
      funext fun x => c_74 m₁ m₂ Hm12 α Hα x]
  erw [<- RenyiDivergence_def_exp m₁ m₂ Hα]
  apply ENNReal.eexp_mono_le.mp
  refine ENNReal.ereal_le_smul_left (↑α - 1) ?Hr1 ?Hr2 ?H
  case Hr1 => exact Hα'
  case Hr2 =>
    rw [show ((α : EReal) - 1) = ((α - 1 : ℝ) : EReal) from by
      rw [EReal.coe_sub, EReal.coe_one]]
    exact EReal.coe_lt_top _
  rw [RenyiDivergence] at h
  rw [<- ENNReal.ofEReal_ofReal_toENNReal] at h
  apply ENNReal.ofEReal_le_mono_conv_nonneg at h
  · apply (le_trans h)
    rw [EReal.coe_mul]
    rw [ENNReal.ofReal_mul ?G1]
    case G1 =>
      apply mul_nonneg
      · simp
      · exact sq_nonneg ε
    rw [ENNReal.ofReal_mul ?G1]
    case G1 => simp
    rw [EReal.coe_mul]
    simp
    apply Eq.le
    rw [max_eq_left (sq_nonneg ε), max_eq_left (by linarith : (0 : ℝ) ≤ α)]
    rw [EReal.coe_pow]
    congr 1
    congr 1
    norm_num
    simp
    refine (EReal.toReal_eq_toReal ?_ ?_ ?_ ?_).mp ?_ <;> try simp
  · apply @RenyiDivergence_def_nonneg U ⊤ ?G1 _ m₁ m₂ Hm12 _ Hα
    infer_instance
  · simp
    apply mul_nonneg
    · apply mul_nonneg
      · apply EReal.coe_nonneg.mpr
        apply inv_nonneg_of_nonneg
        exact zero_le_two
      · rw [sq]
        apply mul_nonneg <;> exact EReal.coe_nonneg.mpr Hε
    · apply EReal.coe_nonneg.mpr
      linarith

-- `SLang.ApproximateDP_renyi_tsum_le` idx 11
theorem c_96 : ¬ drop0% SLang.ApproximateDP_renyi_tsum_le 11 := fun h => by
  have H := h pB qB (fun x hx => absurd hx (qB_ne x)) (fun x hx => absurd hx (pB_ne x)) 0 le_rfl 2 (by norm_num)
    (by rw [cs1]; exact EReal.coe_lt_coe_iff.mpr (by norm_num))
  rw [cs1, EReal.toReal_coe] at H
  norm_num at H
  have h1 := le_self_add.trans H
  unfold pB qB at h1
  rw [PMF.bernoulli_apply, PMF.bernoulli_apply] at h1
  simp only [cond_true] at h1
  rw [← ENNReal.coe_div (by norm_num), ← ENNReal.coe_mul] at h1
  have : (1:NNReal) < 199 / 200 * (199 / 200 / (1 / 200)) := by rw [← NNReal.coe_lt_coe]; norm_num
  exact absurd h1 (not_le.mpr (by exact_mod_cast this))

-- `SLang.ApproximateDP_HDP_bound` idx 3
theorem c_97 : drop% SLang.ApproximateDP_HDP_bound 3 := by
  intro U p q S _ ε' Hε'
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hS : a ∈ S
  · simp only [hS, if_true, one_mul, mul_one]
    split_ifs with hE
    · rw [mul_one]
      have hlt : p a / q a < ENNReal.eexp ↑(ENNReal.ofReal ε') :=
        ENNReal.elog_mono_lt.mpr (by rw [ENNReal.eexp_elog]; exact hE)
      rw [EReal.coe_ennreal_ofReal, max_eq_left Hε', ENNReal.eexp_ofReal] at hlt
      by_cases hq : q a = 0
      · have hp : p a = 0 := by
          by_contra hp; rw [hq, ENNReal.div_zero hp] at hlt; exact absurd hlt (not_lt.mpr le_top)
        rw [hp]; positivity
      · calc p a = p a / q a * q a := (ENNReal.div_mul_cancel hq (PMF.apply_ne_top q a)).symm
          _ ≤ ENNReal.ofReal (Real.exp ε') * q a := mul_le_mul_of_nonneg_right hlt.le (by positivity)
    · rw [mul_zero]; positivity
  · simp [hS]

open scoped Classical in
-- `SLang.ApproximateDP_HDP_bound` idx 7
theorem c_98 : ¬ drop0% SLang.ApproximateDP_HDP_bound 7 := fun h => by
  have H := h pB qB (fun x hx => absurd hx (qB_ne x)) {false} (-10)
  simp only [tsum_bool, Set.mem_singleton_iff, Bool.true_eq_false, if_false, if_true, mul_zero, zero_add,
    one_mul, mul_one, add_zero] at H
  have hr : pB false / qB false < 1 := by
    unfold pB qB; rw [PMF.bernoulli_apply, PMF.bernoulli_apply]; simp only [cond_false]
    rw [← ENNReal.coe_div (tsub_pos_of_lt (by rw [← NNReal.coe_lt_coe]; norm_num)).ne', ← ENNReal.coe_one, ENNReal.coe_lt_coe]
    rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_sub (by rw [← NNReal.coe_le_coe]; norm_num),
      NNReal.coe_sub (by rw [← NNReal.coe_le_coe]; norm_num)]
    norm_num
  have hE : ENNReal.elog (pB false / qB false) < ↑(ENNReal.ofReal (-10)) := by
    rw [ENNReal.ofReal_of_nonpos (by norm_num)]
    have := ENNReal.elog_mono_lt.mp hr
    have h1 : ENNReal.elog 1 = 0 := by
      have := ENNReal.elog_of_pos_real (r := 1) one_pos; simpa using this
    rw [h1] at this; exact_mod_cast this
  rw [if_pos hE, mul_one, zero_mul, mul_zero, add_zero] at H
  have he : (200:ℝ) < Real.exp 10 := by
    have he : 2 < Real.exp 1 := by have := Real.add_one_lt_exp (x := (1:ℝ)) one_ne_zero; linarith
    have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : (2:ℝ) ^ 10 ≤ Real.exp 10 := by rw [this]; exact pow_le_pow_left₀ (by norm_num) he.le 10
    norm_num at h2; linarith
  have hq1 : qB false ≤ 1 := PMF.coe_le_one _ _
  have hlow : (1:ENNReal) ≤ 200 * pB false := lb200 [] false
  have hexp : ENNReal.ofReal (Real.exp (-10)) * 200 < 1 := by
    rw [← ENNReal.ofReal_ofNat 200, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_one]
    apply (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr
    rw [Real.exp_neg, inv_mul_lt_iff₀ (Real.exp_pos _)]; norm_num at he ⊢; linarith
  have h1 := hlow.trans (mul_le_mul_of_nonneg_left H (by positivity))
  have h2 : 200 * (ENNReal.ofReal (Real.exp (-10)) * qB false) ≤ ENNReal.ofReal (Real.exp (-10)) * 200 := by
    rw [mul_comm 200, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc qB false * 200 ≤ 1 * 200 := mul_le_mul_of_nonneg_right hq1 (by positivity)
      _ = 200 := one_mul _
  exact absurd (h1.trans h2) (not_le.mpr hexp)

-- `SLang.A_jensen` idx 7
theorem c_99 : ¬ drop0% SLang.A_jensen 7 := fun h => by
  have h1 := @h Unit eps4 (PMF.pure ()) (PMF.pure ()) eps4_pos hqp4 (1/2) ()
  simp only [tsum_bool, apmf_false, apmf_true, SLang.A_val, eps4_exp, eps4_exp_neg] at h1
  have e2 : (4:ℝ) ^ (1/2 : ℝ) = 2 := by
    rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have e3 : (4⁻¹:ℝ) ^ (1/2 : ℝ) = 2⁻¹ := by
    rw [Real.inv_rpow (by norm_num), e2]
  have L : ENNReal.ofReal 4⁻¹ * ENNReal.ofReal (4/5) + ENNReal.ofReal 4 * ENNReal.ofReal (1/5) = 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  rw [L, ENNReal.one_rpow, ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num), e2, e3,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num), ENNReal.one_le_ofReal] at h1
  norm_num at h1

-- `SLang.A_expectation` idx 6
theorem c_100 : ¬ drop0% SLang.A_expectation 6 := fun h => by
  have H := @h Bool eps4 pH qT eps4_pos hqpH hacH true
  rw [tsum_bool, rt] at H
  have e1 : (SLang.A_pmf eps4 pH qT hqpH true) false = 0 := bt
  have e2 : (SLang.A_pmf eps4 pH qT hqpH true) true = 1 := by
    show 1 - SLang.β eps4 pH qT true = 1; rw [bt]; simp
  rw [e1, e2] at H
  simp only [SLang.A_val, eps4_exp, mul_zero, zero_add, mul_one] at H
  rw [ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at H
  norm_num at H

-- `SLang.B_eval_true` idx 6
theorem c_101 : ¬ drop0% SLang.B_eval_true 6 := fun h => by
  have H := @h Bool eps4 pH qT eps4_pos hqpH hacH
  rw [SLang.B_eval_open, tsum_bool] at H
  have e1 : (SLang.A_pmf eps4 pH qT hqpH false) true = ENNReal.ofReal (11/135) := by
    show 1 - SLang.β eps4 pH qT false = _
    rw [bf, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
  have e2 : (SLang.A_pmf eps4 pH qT hqpH true) true = 1 := by
    show 1 - SLang.β eps4 pH qT true = 1; rw [bt]; simp
  rw [e1, e2, qT, bpm_f, bpm_t, eps4_exp, eps4_exp_neg, one_mul, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num),
    ← ENNReal.ofReal_sub _ (by norm_num), ← ENNReal.ofReal_div_of_pos (by norm_num),
    ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at H
  norm_num at H

-- `SLang.B_eval_false` idx 6
theorem c_102 : ¬ drop0% SLang.B_eval_false 6 := fun h => by
  have H := @h Bool eps4 pH qT eps4_pos hqpH hacH
  rw [SLang.B_eval_open, tsum_bool] at H
  have e1 : (SLang.A_pmf eps4 pH qT hqpH false) false = ENNReal.ofReal (124/135) := bf
  have e2 : (SLang.A_pmf eps4 pH qT hqpH true) false = 0 := bt
  rw [e1, e2, qT, bpm_f, eps4_exp, eps4_exp_neg, zero_mul, add_zero, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num),
    ← ENNReal.ofReal_sub _ (by norm_num), ← ENNReal.ofReal_div_of_pos (by norm_num),
    ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at H
  norm_num at H

-- `SLang.ofDP_bound_sinh_step` idx 4
theorem c_103 : drop% SLang.ofDP_bound_sinh_step 4 := by
  intro ε α hε hα
  by_cases h2 : ε * α ≤ 2
  · exact SLang.ofDP_bound_sinh_step ε α hε hα h2
  · exact sinh_big ε α hε hα (by linarith)

-- `SLang.ofDP_bound_sinh_step` idx 2
theorem c_104 : drop% SLang.ofDP_bound_sinh_step 2 := by
  intro ε α hα hεα
  rcases lt_trichotomy ε 0 with hn | h0 | hp
  · have key : ∀ e : ℝ, 0 < e → e * α ≤ 2 → Real.exp (-e) ^ α * ((Real.exp e - 1) / (Real.exp e - Real.exp (-e))) +
        Real.exp e ^ α * ((1 - Real.exp (-e)) / (Real.exp e - Real.exp (-e))) ≤
        Real.exp ((α - 1) * (1/2 * e^2 * α)) := fun e he h => SLang.ofDP_bound_sinh_step e α he hα h
    have hm : 0 < -ε := by linarith
    have sym : Real.exp (-ε) ^ α * ((Real.exp ε - 1) / (Real.exp ε - Real.exp (-ε))) +
        Real.exp ε ^ α * ((1 - Real.exp (-ε)) / (Real.exp ε - Real.exp (-ε))) =
        Real.exp (-(-ε)) ^ α * ((Real.exp (-ε) - 1) / (Real.exp (-ε) - Real.exp (-(-ε)))) +
        Real.exp (-ε) ^ α * ((1 - Real.exp (-(-ε))) / (Real.exp (-ε) - Real.exp (-(-ε)))) := by
      rw [neg_neg, div_swap (Real.exp ε) 1, div_swap 1 (Real.exp (-ε))]; ring
    rw [sym, show ε ^ 2 = (-ε) ^ 2 by ring]
    by_cases h2 : (-ε) * α ≤ 2
    · exact key (-ε) hm h2
    · exact sinh_big (-ε) α hm hα (by linarith)
  · subst h0; simp
  · exact SLang.ofDP_bound_sinh_step ε α hp hα hεα

-- `SLang.lemma_step_3_deriv_nonneg` idx 3
theorem c_105 : ¬ drop0% SLang.lemma_step_3_deriv_nonneg 3 := fun h => by
  have H := h (-2) 0 (by norm_num) le_rfl
  rw [dform] at H
  simp at H
  linarith [Real.tanh_lt_one 1]

-- `SLang.lemma_step_3_deriv_nonneg` idx 2
theorem c_106 : ¬ drop0% SLang.lemma_step_3_deriv_nonneg 2 := fun h => by
  have H := h 400 1 (by norm_num) (by norm_num)
  rw [dform, show (400:ℝ) / 4 * 1 = 100 by norm_num, show (400:ℝ) / 4 = 100 by norm_num,
    show (400:ℝ) / 2 = 200 by norm_num, show (1:ℝ) / 2 * 1 = 1 / 2 by norm_num] at H
  have hA : 50 < Real.cosh 100 := by
    rw [Real.cosh_eq]; have := Real.add_one_lt_exp (x := (100:ℝ)) (by norm_num)
    have := Real.exp_pos (-100); linarith
  have hT : 1 / 2 ≤ Real.tanh 200 := by
    have hc := Real.one_le_cosh (200:ℝ)
    have hs : Real.sinh 200 = Real.cosh 200 - Real.exp (-200) := by rw [← Real.cosh_sub_sinh]; ring
    have he : Real.exp (-200) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := Real.add_one_lt_exp (x := (200:ℝ)) (by norm_num); linarith
    rw [Real.tanh_eq_sinh_div_cosh, hs, le_div_iff₀ (by linarith)]; linarith
  have hB : Real.cosh (1 / 2) < 2 := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (1/2) < 2 := by
      have h1 : 1 - 1/2 < Real.exp (-(1/2)) := by
        have := Real.add_one_lt_exp (x := -(1/2)) (by norm_num); linarith
      rw [Real.exp_neg] at h1
      rw [lt_inv_comm₀ (by norm_num) (Real.exp_pos _)] at h1; linarith
    have h2 : Real.exp (-(1/2)) < 1 := by
      rw [Real.exp_neg]; exact inv_lt_one_of_one_lt₀ (by have := Real.add_one_lt_exp (x := (1/2:ℝ)) (by norm_num); linarith)
    linarith
  have hB1 := Real.one_le_cosh (1/2 : ℝ)
  generalize Real.cosh 100 = A at hA H
  generalize Real.cosh (1/2) = B at hB hB1 H
  generalize Real.tanh 200 = T at hT H
  have h1 : 1 / A ^ 2 * 100 < 1 / 25 := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)]; nlinarith
  have h2 : 1 / 4 < 1 / B ^ 2 := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have h3 : 1 / 16 ≤ T * (1 / B ^ 2 * (1 / 2)) := by nlinarith
  linarith

-- `SLang.lemma_step_3` idx 4
theorem c_107 : drop% SLang.lemma_step_3 4 := fun x y Hy Hyx => step3_all x y Hy Hyx

-- `SLang.lemma_step_2` idx 4
theorem c_108 : drop% SLang.lemma_step_2 4 := fun x y Hy Hyx =>
  SLang.lemma_step_2 x y Hy Hyx (by unfold SLang.t; exact step3_all x y Hy Hyx)

-- `SLang.sinh_inequality` idx 4
theorem c_109 : drop% SLang.sinh_inequality 4 := by
  intro x y Hy Hyx
  rw [SLang.lemma_step_1 _ _ Hyx]
  apply SLang.lemma_step_2 _ _ Hy Hyx
  unfold SLang.t
  exact step3_all x y Hy Hyx
