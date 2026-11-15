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
namespace T1c6
open SLang

noncomputable abbrev PT (ε₁ ε₂ : ℕ+) : SPMF ℤ := @privNoiseThresh PureDPSystem laplace_pureDPSystem ε₁ ε₂
noncomputable abbrev PG (ε₁ ε₂ : ℕ+) : SPMF ℤ := @privNoiseGuess PureDPSystem laplace_pureDPSystem ε₁ ε₂

theorem PT_pos (ε₁ ε₂ : ℕ+) (k : ℤ) : 0 < PT ε₁ ε₂ k := by
  simp [PT, privNoiseThresh, privNoiseZero, DPNoise.noise, privNoisedQueryPure, DiscreteLaplaceGenSamplePMF]
  simp [DFunLike.coe]
  apply mul_pos
  · apply div_pos
    · simp
    · apply Right.add_pos'
      · apply Real.exp_pos
      · simp
  · apply Real.exp_pos

/-- probability of output 0 of AboveThresh as a function of the query value q at index 0 -/
noncomputable def G (ε₁ ε₂ : ℕ+) (T q : ℤ) : ENNReal :=
  ∑' τ : ℤ, PT ε₁ ε₂ τ * ∑' v : ℤ, if τ + T ≤ q + v then PG ε₁ ε₂ v else 0

theorem sv9_zero {sv_T : Type} (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    @sv9_aboveThresh PureDPSystem laplace_pureDPSystem sv_T qs T ε₁ ε₂ l 0 = G ε₁ ε₂ T (qs 0 l) := by
  simp only [sv9_aboveThresh, sv8_sum, G]
  simp
  refine tsum_congr fun τ => ?_
  congr 1
  refine tsum_congr fun v => ?_
  split_ifs <;> simp [probPure, probZero]

/-- G as one sum over pairs (τ, v) -/
theorem G_prod (ε₁ ε₂ : ℕ+) (T q : ℤ) :
    G ε₁ ε₂ T q = ∑' p : ℤ × ℤ, if p.1 + T ≤ q + p.2 then PT ε₁ ε₂ p.1 * PG ε₁ ε₂ p.2 else 0 := by
  rw [ENNReal.tsum_prod', G]
  refine tsum_congr fun τ => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun v => ?_
  split_ifs <;> simp

theorem joint_ne_top (ε₁ ε₂ : ℕ+) : ∑' p : ℤ × ℤ, PT ε₁ ε₂ p.1 * PG ε₁ ε₂ p.2 ≠ ⊤ := by
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_mul_left, SPMF_sum_one, mul_one]
  rw [SPMF_sum_one]
  exact ENNReal.one_ne_top

/-- the probability that v − τ ≥ M is eventually below any positive bound -/
theorem G_tail (ε₁ ε₂ : ℕ+) (δ : ENNReal) (hδ : 0 < δ) : ∃ M : ℕ, G ε₁ ε₂ M 0 < δ := by
  obtain ⟨s, hs⟩ := ((ENNReal.tendsto_tsum_compl_atTop_zero (joint_ne_top ε₁ ε₂)).eventually
    (gt_mem_nhds hδ)).exists
  refine ⟨s.sup (fun p : ℤ × ℤ => (p.2 - p.1).toNat) + 1, lt_of_le_of_lt ?_ hs⟩
  rw [G_prod]
  have e := tsum_subtype ({x | x ∉ s} : Set (ℤ × ℤ)) (fun p : ℤ × ℤ => PT ε₁ ε₂ p.1 * PG ε₁ ε₂ p.2)
  refine le_trans ?_ e.ge
  refine ENNReal.tsum_le_tsum fun p => ?_
  split_ifs with h1
  · have hp : p ∉ s := by
      intro hp
      have h2 := Finset.le_sup (f := fun p : ℤ × ℤ => (p.2 - p.1).toNat) hp
      have h3 := Int.self_le_toNat (p.2 - p.1)
      push_cast at h1
      omega
    rw [Set.indicator_of_mem (show p ∈ {x | x ∉ s} from hp)]
  · exact bot_le

/-- the query M times the length at every index -/
def qM (M : ℕ) : sv_query Unit := fun _ l => (M : ℤ) * l.length

theorem qM_lucky (M : ℕ) (T : ℤ) : has_lucky (qM M) T := fun τ l => ⟨τ + T, fun A K' hK => by
  have : 0 ≤ (M : ℤ) * l.length := by positivity
  simp only [qM]; omega⟩

theorem nb1 : Neighbour [()] ([] : List Unit) := Neighbour.Deletion (a := []) (b := []) (n := ()) (by simp) (by simp)

/-- DP gives the ratio bound for one point mass (from W1c0) -/
theorem dp_single {T U : Type} {m : Mechanism T U} {ε : ℝ} (h : DP m ε) (l₁ l₂ : List T)
    (hn : Neighbour l₁ l₂) (x : U) : (m l₁).1 x / (m l₂).1 x ≤ ENNReal.ofReal (Real.exp ε) := by
  have := h l₁ l₂ hn {x}
  convert this using 2 <;>
    (rw [tsum_eq_single x (fun b hb => by simp [hb]), if_pos (Set.mem_singleton x)]; try rfl)

theorem spmf_ne_top {U : Type} (p : SPMF U) (x : U) : p.1 x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (by
    have := ENNReal.le_tsum (f := p.1) x
    rwa [p.2.tsum_eq] at this)

/-- G at q = T is at least the mass of τ = v = 0 -/
theorem G_diag (ε₁ ε₂ : ℕ+) (T : ℤ) : PT ε₁ ε₂ 0 * PG ε₁ ε₂ 0 ≤ G ε₁ ε₂ T T := by
  rw [G_prod]
  refine le_trans ?_ (ENNReal.le_tsum ((0 : ℤ), (0 : ℤ)))
  simp

end T1c6

-- `SLang.sv9_aboveThresh_pmf_DP` idx 5: necessary (query M·length, sensitivity M, T = M, ε₁ = ε₂ = 1, [()] vs [], M large)
theorem t6_1 : ¬ drop0% SLang.sv9_aboveThresh_pmf_DP 5 := fun h => by
  set E : ENNReal := ENNReal.ofReal (Real.exp (((1 : NNReal) : ℝ))) with hE
  have hE0 : E ≠ 0 := by rw [hE]; simp [Real.exp_pos]
  have hEt : E ≠ ⊤ := ENNReal.ofReal_ne_top
  set c : ENNReal := T1c6.PT 1 1 0 * T1c6.PG 1 1 0 with hc
  have hc0 : 0 < c := ENNReal.mul_pos (T1c6.PT_pos 1 1 0).ne' (SLang.privNoiseGuess_pure_pos 1 1 0).ne'
  have hδ : 0 < c / E := ENNReal.div_pos hc0.ne' hEt
  obtain ⟨M, hM⟩ := T1c6.G_tail 1 1 (c / E) hδ
  have H := @h Unit (T1c6.qM M) (M : ℤ) 1 1 (T1c6.qM_lucky M M) 1 (by simp)
  have D := T1c6.dp_single H [()] [] T1c6.nb1 0
  change @SLang.sv9_aboveThresh SLang.PureDPSystem SLang.laplace_pureDPSystem Unit (T1c6.qM M) M 1 1 [()] 0
    / @SLang.sv9_aboveThresh SLang.PureDPSystem SLang.laplace_pureDPSystem Unit (T1c6.qM M) M 1 1 [] 0 ≤ E at D
  rw [T1c6.sv9_zero, T1c6.sv9_zero] at D
  have q1 : T1c6.qM M 0 [()] = (M : ℤ) := by simp [T1c6.qM]
  have q0 : T1c6.qM M 0 [] = 0 := by simp [T1c6.qM]
  rw [q1, q0] at D
  have hne : T1c6.G 1 1 M 0 ≠ ⊤ := by
    have := T1c6.sv9_zero (T1c6.qM M) (M : ℤ) 1 1 []
    rw [q0] at this
    rw [← this]
    exact T1c6.spmf_ne_top (SLang.sv9_aboveThresh_SPMF (T1c6.qM M) M (T1c6.qM_lucky M M) 1 1 []) 0
  rw [ENNReal.div_le_iff_le_mul (Or.inr hEt) (Or.inl hne)] at D
  have h1 := ENNReal.mul_lt_mul_left hE0 hEt hM
  rw [ENNReal.div_mul_cancel hE0 hEt] at h1
  have h2 : T1c6.G 1 1 M M < c := lt_of_le_of_lt D (by rw [mul_comm]; exact h1)
  exact absurd (lt_of_le_of_lt (T1c6.G_diag 1 1 M) h2) (lt_irrefl _)
