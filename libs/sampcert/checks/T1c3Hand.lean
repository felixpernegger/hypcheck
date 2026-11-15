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
namespace T1c3
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

theorem sv19 {sv_T : Type} (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    @sv1_aboveThresh PureDPSystem laplace_pureDPSystem sv_T qs T ε₁ ε₂ l
      = @sv9_aboveThresh PureDPSystem laplace_pureDPSystem sv_T qs T ε₁ ε₂ l := by
  erw [← sv8_sv9_eq, ← sv7_sv8_eq, ← sv6_sv7_eq, ← sv5_sv6_eq,
      ← sv4_sv5_eq, ← sv3_sv4_eq, ← sv2_sv3_eq, ← sv1_sv2_eq]

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

theorem inner_le (ε₁ ε₂ : ℕ+) (a : ℤ) (q : ℤ) :
    ∑' v : ℤ, (if a ≤ q + v then PG ε₁ ε₂ v else 0) ≤ 1 := by
  calc _ ≤ ∑' v : ℤ, PG ε₁ ε₂ v := ENNReal.tsum_le_tsum fun v => by
          split_ifs <;> simp
    _ = 1 := SPMF_sum_one _

theorem inner_lt (ε₁ ε₂ : ℕ+) (a : ℤ) (q : ℤ) :
    ∑' v : ℤ, (if a ≤ q + v then PG ε₁ ε₂ v else 0)
      < ∑' v : ℤ, (if a ≤ (q + 1) + v then PG ε₁ ε₂ v else 0) := by
  apply ENNReal.tsum_lt_tsum (i := a - q - 1)
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (inner_le ε₁ ε₂ a q)
  · intro v
    split_ifs with h1 h2 <;> first | exact le_rfl | (exfalso; omega) | simp
  · have h1 : ¬ a ≤ q + (a - q - 1) := by omega
    have h2 : a ≤ (q + 1) + (a - q - 1) := by omega
    rw [if_neg h1, if_pos h2]
    exact privNoiseGuess_pure_pos ε₁ ε₂ _

theorem G_lt (ε₁ ε₂ : ℕ+) (T q : ℤ) : G ε₁ ε₂ T q < G ε₁ ε₂ T (q + 1) := by
  unfold G
  apply ENNReal.tsum_lt_tsum (i := 0)
  · refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc _ ≤ ∑' τ : ℤ, PT ε₁ ε₂ τ * 1 := ENNReal.tsum_le_tsum fun τ => by
            gcongr; exact inner_le ε₁ ε₂ _ _
      _ = 1 := by rw [ENNReal.tsum_mul_right, SPMF_sum_one, one_mul]
  · intro τ
    exact mul_le_mul_of_nonneg_left (inner_lt ε₁ ε₂ _ _).le zero_le
  · have hne : PT ε₁ ε₂ 0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
      (by rw [← SPMF_sum_one (PT ε₁ ε₂)]; exact ENNReal.le_tsum 0)
    rw [mul_comm (PT ε₁ ε₂ 0), mul_comm (PT ε₁ ε₂ 0)]
    exact ENNReal.mul_lt_mul_left (PT_pos ε₁ ε₂ 0).ne' hne (inner_lt ε₁ ε₂ _ _)

/-- constant mechanisms (copied from Probe1) -/
def Cst {T Z : Type} (m : Mechanism T Z) : Prop := ∀ l l', m l = m l'

/-- DP system: constant mechanisms at every level, everything at level ≥ 1 (copied from Probe1) -/
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

theorem ncst_of {T Z : Type} {m : Mechanism T Z} (l l' : List T) (x : Z) (h : (m l).1 x ≠ (m l').1 x) :
    ¬ Cst m := fun hc => h (by rw [hc l l'])

theorem nb1 : Neighbour [()] ([] : List Unit) := Neighbour.Deletion (a := []) (b := []) (n := ()) (by simp) (by simp)
theorem nbN : Neighbour ([] : List ℕ) [1] := Neighbour.Addition (a := []) (b := []) (n := 1) (by simp) (by simp)

theorem lenSens : sensitivity (fun l : List Unit => (l.length : ℤ)) 1 := by
  intro l₁ l₂ h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega

/-- the length query at every index -/
def qL : sv_query Unit := fun _ l => (l.length : ℤ)

theorem qL_lucky (T : ℤ) : has_lucky qL T := fun τ l => ⟨τ + T, fun A K' hK => by simp only [qL]; omega⟩

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

/-- pure DP at level 0 forces equal point masses on neighbours -/
theorem dp0_contra {T U : Type} {m : Mechanism T U} (h : DP m ((0 : NNReal) : ℝ)) (l₁ l₂ : List T)
    (hn : Neighbour l₁ l₂) (x : U) (hlt : (m l₂).1 x < (m l₁).1 x) : False := by
  have := dp_single h l₁ l₂ hn x
  rw [NNReal.coe_zero, Real.exp_zero, ENNReal.ofReal_one,
    ENNReal.div_le_iff_le_mul (Or.inr ENNReal.one_ne_top) (Or.inl (spmf_ne_top _ _)), one_mul] at this
  exact absurd hlt (not_lt.2 this)

/-- output 0 of AboveThresh (sv1, Laplace noise) is G at the query value -/
theorem sv1_zero {sv_T : Type} (qs : sv_query sv_T) (T : ℤ) (HL : has_lucky qs T) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    (sv1_aboveThresh_PMF qs T HL ε₁ ε₂ l).1 0 = G ε₁ ε₂ T (qs 0 l) := by
  show @sv1_aboveThresh PureDPSystem laplace_pureDPSystem sv_T qs T ε₁ ε₂ l 0 = _
  rw [sv19, sv9_zero]

open scoped Classical in
theorem pp_apply {T U V : Type} (nq : SLang.Mechanism T U) (f : U → V) (l : List T) (v : V) :
    (SLang.privPostProcess nq f l).1 v = ∑' a, if v = f a then (nq l).1 a else 0 := by
  simp [privPostProcess, Bind.bind, Pure.pure, probBind, probPure]

open scoped Classical in
theorem comp_apply {T U V : Type} (nq1 : SLang.Mechanism T U) (nq2 : U → SLang.Mechanism T V)
    (l : List T) (u : U) (v : V) :
    (SLang.privComposeAdaptive nq1 nq2 l).1 (u, v) = (nq1 l).1 u * (nq2 u l).1 v := by
  simp [privComposeAdaptive, Bind.bind, Pure.pure, probBind, probPure]
  exact SLang.compose_sum_rw_adaptive nq1 nq2 u v l

/-- one round of Sparse outputs [0] with the probability that AboveThresh outputs 0 -/
theorem sparse1_val (T : ℤ) (ε₁ ε₂ : ℕ+) {U : Type} (qs' : sv_query U) (HL' : has_lucky qs' T) (l : List U) :
    (privSparseAux T ε₁ ε₂ qs' HL' 1 l).1 [0] = G ε₁ ε₂ T (qs' 0 l) := by
  simp only [privSparseAux]
  rw [pp_apply, tsum_eq_single ((0:ℕ), ([] : List ℕ))]
  · rw [comp_apply, sv1_zero]
    simp [privConst, SPMF_pure, probPure, snoc, Function.uncurry]
  · rintro ⟨n, L⟩ hne
    rw [if_neg]
    intro h
    apply hne
    simp only [Function.uncurry, snoc] at h
    rcases L with _ | ⟨a, L⟩
    · simp at h; subst h; rfl
    · simp at h

theorem sparse1_ncst (T : ℤ) (ε₁ ε₂ : ℕ+) (qs' : sv_query Unit) (HL' : has_lucky qs' T)
    (hq : qs' 0 [()] = qs' 0 [] + 1) : ¬ Cst (privSparseAux T ε₁ ε₂ qs' HL' 1) := by
  apply ncst_of [()] [] [0]
  rw [sparse1_val, sparse1_val, hq]
  exact (G_lt ε₁ ε₂ T _).ne'

end T1c3

-- `SLang.sv9_aboveThresh_pmf_DP` idx 8: necessary (ε = 0, length query, [()] vs [])
theorem t3_1 : ¬ drop0% SLang.sv9_aboveThresh_pmf_DP 8 := fun h => by
  have H := @h Unit T1c3.qL 0 1 1 (fun _ => T1c3.lenSens) (T1c3.qL_lucky 0) 0
  refine T1c3.dp0_contra H [()] [] T1c3.nb1 0 ?_
  show @SLang.sv9_aboveThresh SLang.PureDPSystem SLang.laplace_pureDPSystem Unit T1c3.qL 0 1 1 [] 0
    < @SLang.sv9_aboveThresh SLang.PureDPSystem SLang.laplace_pureDPSystem Unit T1c3.qL 0 1 1 [()] 0
  rw [T1c3.sv9_zero, T1c3.sv9_zero]
  simpa [T1c3.qL] using T1c3.G_lt 1 1 0 0

-- `SLang.privUnboundedMax_DP` idx 3: necessary (ε = 0, [] vs [1])
theorem t3_2 : ¬ drop0% SLang.privUnboundedMax_DP 3 := fun h => by
  have H := h 1 1 0
  refine T1c3.dp0_contra H [] [1] T1c3.nbN 0 ?_
  show (SLang.sv1_aboveThresh_PMF SLang.exactDiffSum 0 SLang.lucky_guess 1 1 [1]).1 0
    < (SLang.sv1_aboveThresh_PMF SLang.exactDiffSum 0 SLang.lucky_guess 1 1 []).1 0
  have e1 : SLang.exactDiffSum 0 [1] = -1 := by
    first | decide | simp [SLang.exactDiffSum, SLang.exactClippedSum]
  have e0 : SLang.exactDiffSum 0 [] = -1 + 1 := by
    first | decide | simp [SLang.exactDiffSum, SLang.exactClippedSum]
  calc _ = T1c3.G 1 1 0 (-1) := by
        rw [← e1]; exact T1c3.sv1_zero (sv_T := ℕ) SLang.exactDiffSum 0 SLang.lucky_guess 1 1 [1]
    _ < T1c3.G 1 1 0 (-1 + 1) := T1c3.G_lt 1 1 0 (-1)
    _ = _ := by
        rw [← e0]; exact (T1c3.sv1_zero (sv_T := ℕ) SLang.exactDiffSum 0 SLang.lucky_guess 1 1 []).symm

-- `SLang.privSparseAux_DP` idx 6: necessary (sys model, ε₁/ε₂ = 1/2, c = 1)
theorem t3_3 : ¬ drop0% SLang.privSparseAux_DP 6 := fun h => by
  have H := @h 0 1 2 Unit (T1c3.sys Unit) T1c3.qL (1/2) 1 (by norm_num) 0 (SLang.shift_qs_lucky 0 0 _ (T1c3.qL_lucky 0))
  rcases H with H | H
  · exact T1c3.sparse1_ncst 0 1 2 _ _ (by simp [SLang.shift_qs, T1c3.qL]) H
  · have H' := NNReal.coe_le_coe.2 H; push_cast at H'; norm_num at H'

-- `SLang.privSparseAux_DP` idx 9: necessary (sys model, ε₁ = ε₂ = 1 so HDP holds, ε = 0, c = 1)
theorem t3_4 : ¬ drop0% SLang.privSparseAux_DP 9 := fun h => by
  have H := @h 0 1 1 Unit (T1c3.sys Unit) T1c3.qL
    (fun N HN ε hε => Or.inr (by rw [hε]; simp)) 0 1 0 (SLang.shift_qs_lucky 0 0 _ (T1c3.qL_lucky 0))
  rcases H with H | H
  · exact T1c3.sparse1_ncst 0 1 1 _ _ (by simp [SLang.shift_qs, T1c3.qL]) H
  · have H' := NNReal.coe_le_coe.2 H; push_cast at H'; norm_num at H'

-- `SLang.privSparse_DP` idx 7: necessary (sys model, ε₁/ε₂ = 1/2, c = 1)
theorem t3_5 : ¬ drop0% SLang.privSparse_DP 7 := fun h => by
  have H := @h 0 1 2 Unit (T1c3.sys Unit) T1c3.qL (T1c3.qL_lucky 0) (1/2) 1 (by norm_num)
  rcases H with H | H
  · exact T1c3.sparse1_ncst 0 1 2 _ _ (by simp [SLang.shift_qs, T1c3.qL]) H
  · have H' := NNReal.coe_le_coe.2 H; push_cast at H'; norm_num at H'

-- `SLang.privSparse_DP` idx 10: necessary (sys model, ε₁ = ε₂ = 1 so HDP holds, ε = 0, c = 1)
theorem t3_6 : ¬ drop0% SLang.privSparse_DP 10 := fun h => by
  have H := @h 0 1 1 Unit (T1c3.sys Unit) T1c3.qL (T1c3.qL_lucky 0)
    (fun N HN ε hε => Or.inr (by rw [hε]; simp)) 0 1
  rcases H with H | H
  · exact T1c3.sparse1_ncst 0 1 1 _ _ (by simp [SLang.shift_qs, T1c3.qL]) H
  · have H' := NNReal.coe_le_coe.2 H; push_cast at H'; norm_num at H'
