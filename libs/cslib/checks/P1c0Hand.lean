import Lean.Elab.Command
import Cslib
-- CSLib toolkit header (copy of hypcheck runs/hand22/Header.lean with `import Cslib`; ~150 MB, 1.5 s to import)


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
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

/-! # P1c0: the 19 PAC-learning rows

One construction (designed with a web LLM, checked here) refutes all of them.
Domain ℕ (anchors 0 and 1, tail n + 2), labels Bool, discrete σ-algebras.
`DD b T = 3/8·δ(0,b) + 3/8·δ(1,b) + 1/4·(T pushed to the tail)`, `Dstar` = all of these
(T a probability measure on ℕ × Bool), `Cstar` = all concepts.
- `imp`: no randomized learner for (Cstar, Dstar) at ε = 1/8, δ = 1/3, any sample size
  (No-Free-Lunch counting: binomial anti-concentration + averaging over 2^N tail labellings).
- One sample suffices, zero samples don't, for: (ε, δ) = (1/8, 5/8) [`L_anc`, `Z4`];
  (1/4, 1/3) [`L_e4`, `Z2`]; (1/8, 1/3) with the two-constant class `C0` [`L_C0`] or the
  two-distribution family `D0` [`L_D0`].
Because `sInf ∅ = 0`, each dropped "∃ m, learner" hypothesis turns a monotonicity statement
into `1 ≤ 0`. -/

namespace P1c0
open MeasureTheory Set Cslib.MachineLearning.PACLearning
open scoped ENNReal NNReal

-- weights as coerced nonnegative reals (ENNReal literals are hard to compute with)
def q (x : ℝ≥0) : ℝ≥0∞ := x
macro "enn" : tactic => `(tactic| (simp only [q, ← ENNReal.coe_add, ← ENNReal.coe_mul, ← ENNReal.coe_one, ← ENNReal.coe_zero, ENNReal.coe_le_coe, ENNReal.coe_lt_coe, ENNReal.coe_inj, ← NNReal.coe_le_coe, ← NNReal.coe_lt_coe, ← NNReal.coe_inj] <;> push_cast <;> norm_num))

abbrev X := ℕ × Bool

def tl (p : X) : X := (p.1 + 2, p.2)

theorem msX (s : Set X) : MeasurableSet s := s.to_countable.measurableSet

noncomputable def DD (b : Bool) (T : Measure X) : Measure X :=
  q (3/8) • Measure.dirac ((0 : ℕ), b) + q (3/8) • Measure.dirac ((1 : ℕ), b) + q (1/4) • T.map tl

theorem DD_apply (b : Bool) (T : Measure X) (s : Set X) :
    DD b T s = q (3/8) * s.indicator 1 ((0 : ℕ), b) + q (3/8) * s.indicator 1 ((1 : ℕ), b)
      + q (1/4) * T (tl ⁻¹' s) := by
  simp only [DD, Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Measure.map_apply (measurable_of_countable tl) (msX s)]

instance DD_prob (b : Bool) (T : Measure X) [IsProbabilityMeasure T] :
    IsProbabilityMeasure (DD b T) :=
  ⟨by rw [DD_apply]; simp only [Set.indicator_univ, Pi.one_apply, Set.preimage_univ, measure_univ]; enn⟩

theorem DD_le (b : Bool) (T : Measure X) [IsProbabilityMeasure T] (s : Set X) :
    DD b T s ≤ q (3/8) * s.indicator 1 ((0 : ℕ), b) + q (3/8) * s.indicator 1 ((1 : ℕ), b) + q (1/4) := by
  rw [DD_apply]; gcongr; exact mul_le_of_le_one_right zero_le (prob_le_one (μ := T) (s := tl ⁻¹' s))

def Dstar : Set (Measure X) := {D | ∃ b T, IsProbabilityMeasure T ∧ D = DD b T}
def Cstar : ConceptClass ℕ Bool := Set.univ
def C0 : ConceptClass ℕ Bool := {fun _ => false, fun _ => true}
noncomputable def D0 : Set (Measure X) :=
  {DD false (Measure.dirac ((0 : ℕ), false)), DD true (Measure.dirac ((0 : ℕ), true))}

theorem D0_sub : D0 ⊆ Dstar := by
  rintro D (rfl | rfl) <;> exact ⟨_, _, inferInstance, rfl⟩

noncomputable def e8 : Set.Ioo (0 : ℝ≥0) 1 := ⟨1/8, by rw [Set.mem_Ioo]; constructor <;> enn⟩
noncomputable def e4 : Set.Ioo (0 : ℝ≥0) 1 := ⟨1/4, by rw [Set.mem_Ioo]; constructor <;> enn⟩
noncomputable def d3 : Set.Ioo (0 : ℝ≥0) 1 := ⟨1/3, by rw [Set.mem_Ioo]; constructor <;> enn⟩
noncomputable def d58 : Set.Ioo (0 : ℝ≥0) 1 := ⟨5/8, by rw [Set.mem_Ioo]; constructor <;> enn⟩

/-! ## Errors -/

theorem err_ge0 (b : Bool) (T : Measure X) (h : ℕ → Bool) (hb : h 0 ≠ b) :
    q (3/8) ≤ error (DD b T) h := by
  rw [error, DD_apply]
  have : ({p : X | h p.1 ≠ p.2}).indicator (1 : X → ℝ≥0∞) ((0 : ℕ), b) = 1 := by
    simp [Set.indicator_apply, hb]
  rw [this, mul_one]; exact le_add_right (le_add_right le_rfl)

theorem err_ge_tail (b : Bool) (T : Measure X) (h : ℕ → Bool) :
    q (1/4) * T {p | h (p.1 + 2) ≠ p.2} ≤ error (DD b T) h := by
  rw [error, DD_apply]; exact le_add_left le_rfl

theorem err_tail (b : Bool) (T : Measure X) (h : ℕ → Bool) (h0 : h 0 = b) (h1 : h 1 = b) :
    error (DD b T) h = q (1/4) * T {p | h (p.1 + 2) ≠ p.2} := by
  rw [error, DD_apply]; simp [Set.indicator_apply, h0, h1]; rfl

theorem err_const_le (b : Bool) (T : Measure X) [IsProbabilityMeasure T] :
    error (DD b T) (fun _ => b) ≤ q (1/4) := by
  rw [err_tail b T _ rfl rfl]; exact mul_le_of_le_one_right (zero_le) prob_le_one

theorem err_witness (b c : Bool) :
    error (DD b (Measure.dirac ((0 : ℕ), c))) (fun n => if n < 2 then b else c) = 0 := by
  rw [err_tail b _ _ (by simp) (by simp), Measure.dirac_apply]; simp [Set.indicator_apply]

theorem opt_zero (b c : Bool) {C : ConceptClass ℕ Bool} (hC : (fun n => if n < 2 then b else c) ∈ C) :
    optimalError (DD b (Measure.dirac ((0 : ℕ), c))) C = 0 :=
  le_antisymm ((iInf₂_le _ hC).trans (err_witness b c).le) (zero_le)

/-! ## One-sample learners -/

theorem pi1 (D : Measure X) (P : (Fin 1 → X) → Prop) :
    Measure.pi (fun _ : Fin 1 => D) {S | P S} = D {x | P (fun _ => x)} := by
  have h := (measurePreserving_funUnique D (Fin 1)).symm.measure_preimage_equiv {S | P S}
  convert h.symm using 2
  · congr
  · ext x; rfl

theorem bound1 {C : ConceptClass ℕ Bool} {ε δ : Set.Ioo (0 : ℝ≥0) 1} {𝒟 : Set (Measure X)}
    (A : Learner ℕ Bool 1)
    (h : ∀ D ∈ 𝒟, ∃ (b : Bool) (T : Measure X), IsProbabilityMeasure T ∧ D = DD b T ∧
      ∃ G : Set X, DD b T Gᶜ ≤ δ.val ∧
        ∀ x ∈ G, ¬ (optimalError (DD b T) C + ε.val < error (DD b T) (A (fun _ => x)))) :
    IsPACLearnerFor 1 ε δ C 𝒟 := by
  refine ⟨A, fun D _ hD => ?_⟩
  obtain ⟨b, T, _, rfl, G, hG, hgood⟩ := h D hD
  rw [pi1]
  refine (measure_mono fun x hx => ?_).trans hG
  exact fun hxG => hgood x hxG hx

def Acst : Learner ℕ Bool 1 := fun S _ => (S 0).2
def Aanc : Learner ℕ Bool 1 := fun S n => if n < 2 then (S 0).2 else decide ((S 0).1 = 1)

theorem anchors_compl (b : Bool) (T : Measure X) [IsProbabilityMeasure T] :
    DD b T ({((0 : ℕ), b), ((1 : ℕ), b)}ᶜ) ≤ q (1/4) :=
  (DD_le b T _).trans (by simp [Set.indicator_apply])

theorem anchor_compl (b : Bool) (T : Measure X) [IsProbabilityMeasure T] (i : ℕ) (hi : i = 0 ∨ i = 1) :
    DD b T ({(i, b)}ᶜ) ≤ q (5/8) := by
  refine (DD_le b T _).trans ?_
  rcases hi with rfl | rfl <;> simp [Set.indicator_apply] <;> enn

theorem Acst_anchor (b : Bool) (x : X) (hx : x ∈ ({((0 : ℕ), b), ((1 : ℕ), b)} : Set X)) :
    Acst (fun _ => x) = fun _ => b := by
  rcases hx with rfl | rfl <;> rfl

-- (ε, δ) = (1/4, 1/3): output the observed label as a constant
theorem L_e4 : IsPACLearnerFor 1 e4 d3 Cstar Dstar := by
  refine bound1 Acst fun D hD => ?_
  obtain ⟨b, T, hT, rfl⟩ := hD
  refine ⟨b, T, hT, rfl, _, (anchors_compl b T).trans (by show q (1/4) ≤ q (1/3); enn), fun x hx => ?_⟩
  rw [Acst_anchor b x hx, not_lt]
  exact le_add_left (err_const_le b T)

-- the two-constant class at (1/8, 1/3): the observed label is an optimal constant
theorem L_C0 : IsPACLearnerFor 1 e8 d3 C0 Dstar := by
  refine bound1 Acst fun D hD => ?_
  obtain ⟨b, T, hT, rfl⟩ := hD
  refine ⟨b, T, hT, rfl, _, (anchors_compl b T).trans (by show q (1/4) ≤ q (1/3); enn), fun x hx => ?_⟩
  rw [Acst_anchor b x hx, not_lt]
  refine le_add_right (le_iInf₂ fun c hc => ?_)
  have hb := err_const_le b T
  rcases hc with rfl | rfl <;> cases b <;>
    first | exact le_rfl | exact hb.trans ((by enn : q (1/4) ≤ q (3/8)).trans (err_ge0 _ T _ (by simp)))

-- the two-distribution family at (1/8, 1/3): the observed label is the only label
theorem L_D0 : IsPACLearnerFor 1 e8 d3 Cstar D0 := by
  refine bound1 Acst fun D hD => ?_
  have key : ∀ c : Bool, ∃ (b : Bool) (T : Measure X), IsProbabilityMeasure T ∧
      DD c (Measure.dirac ((0 : ℕ), c)) = DD b T ∧ ∃ G : Set X, DD b T Gᶜ ≤ (d3.val : ℝ≥0∞) ∧
        ∀ x ∈ G, ¬ (optimalError (DD b T) Cstar + (e8.val : ℝ≥0∞) < error (DD b T) (Acst (fun _ => x))) := by
    intro c
    refine ⟨c, _, inferInstance, rfl, _, (anchors_compl c _).trans (by show q (1/4) ≤ q (1/3); enn), fun x hx => ?_⟩
    rw [Acst_anchor c x hx, not_lt]
    have := err_witness c c
    simp only [ite_self] at this
    rw [this]; exact zero_le
  rcases hD with rfl | rfl
  · exact key false
  · exact key true

-- (1/8, 5/8): predict the anchor label on the anchors and "which anchor was seen" on the tail
theorem L_anc : IsPACLearnerFor 1 e8 d58 Cstar Dstar := by
  refine bound1 Aanc fun D hD => ?_
  obtain ⟨b, T, hT, rfl⟩ := hD
  have hsum : T {p : X | false ≠ p.2} + T {p : X | true ≠ p.2} = 1 := by
    have : {p : X | true ≠ p.2} = {p : X | false ≠ p.2}ᶜ := by
      ext ⟨n, y⟩; cases y <;> simp
    rw [this, measure_add_measure_compl (msX _), measure_univ]
  have good : ∀ i : ℕ, (i = 0 ∨ i = 1) → T {p : X | decide (i = 1) ≠ p.2} ≤ q (1/2) →
      ∃ G : Set X, DD b T Gᶜ ≤ (d58.val : ℝ≥0∞) ∧ ∀ x ∈ G,
        ¬ (optimalError (DD b T) Cstar + (e8.val : ℝ≥0∞) < error (DD b T) (Aanc (fun _ => x))) := by
    intro i hi hT2
    refine ⟨{(i, b)}, anchor_compl b T i hi, fun x hx => ?_⟩
    rw [Set.mem_singleton_iff.mp hx, not_lt]
    refine le_add_left ?_
    rw [err_tail b T _ (by simp [Aanc]) (by simp [Aanc])]
    have : {p : X | Aanc (fun _ => (i, b)) (p.1 + 2) ≠ p.2} = {p : X | decide (i = 1) ≠ p.2} := by
      ext p; simp [Aanc]
    rw [this]
    calc q (1/4) * T {p : X | decide (i = 1) ≠ p.2} ≤ q (1/4) * q (1/2) := by gcongr
      _ = q (1/8) := by enn
  refine ⟨b, T, hT, rfl, ?_⟩
  by_cases h0 : T {p : X | false ≠ p.2} ≤ q (1/2)
  · exact good 0 (Or.inl rfl) (by simpa using h0)
  · refine good 1 (Or.inr rfl) ?_
    simp only [decide_true]
    by_contra h1
    push Not at h0 h1
    have := ENNReal.add_lt_add h0 h1
    rw [hsum, show q (1/2) + q (1/2) = 1 by enn] at this
    exact lt_irrefl _ this

/-! ## Zero samples -/

def f0 : Fin 0 → X := Fin.elim0

theorem pi0_ge (D : Measure X) (P : (Fin 0 → X) → Prop) (hP : P f0) :
    1 ≤ Measure.pi (fun _ : Fin 0 => D) {S | P S} := by
  have : {S | P S} = univ := Set.eq_univ_of_forall fun S => by rwa [Subsingleton.elim S f0]
  rw [this, Measure.pi_of_empty, measure_univ]

theorem int2 {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] (F G : Ω → ℝ≥0∞)
    (hF : AEMeasurable F Q) (k : ∀ ω, 1 ≤ F ω + G ω) : 1 ≤ ∫⁻ ω, F ω ∂Q + ∫⁻ ω, G ω ∂Q := by
  rw [← lintegral_add_left' hF]
  calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂Q := by simp
    _ ≤ _ := lintegral_mono k

theorem int4 {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] (F G H K : Ω → ℝ≥0∞)
    (hF : AEMeasurable F Q) (hG : AEMeasurable G Q) (hH : AEMeasurable H Q)
    (k : ∀ ω, 3 ≤ F ω + G ω + H ω + K ω) :
    3 ≤ ∫⁻ ω, F ω ∂Q + ∫⁻ ω, G ω ∂Q + ∫⁻ ω, H ω ∂Q + ∫⁻ ω, K ω ∂Q := by
  have hFG : AEMeasurable (fun ω => F ω + G ω) Q := hF.add hG
  have hFGH : AEMeasurable (fun ω => F ω + G ω + H ω) Q := hFG.add hH
  have e : ∫⁻ ω, (F ω + G ω + H ω + K ω) ∂Q
      = ∫⁻ ω, F ω ∂Q + ∫⁻ ω, G ω ∂Q + ∫⁻ ω, H ω ∂Q + ∫⁻ ω, K ω ∂Q := by
    rw [lintegral_add_left' hFGH, lintegral_add_left' hFG, lintegral_add_left' hF]
  rw [← e]
  calc (3 : ℝ≥0∞) = ∫⁻ _, 3 ∂Q := by simp
    _ ≤ _ := lintegral_mono k

theorem fail_anchor {C : ConceptClass ℕ Bool} (b : Bool) (ε : ℝ≥0∞) (hε : ε < q (3/8))
    (hC : (fun _ => b) ∈ C) (h : ℕ → Bool) (hb : h 0 ≠ b) :
    optimalError (DD b (Measure.dirac ((0 : ℕ), b))) C + ε < error (DD b (Measure.dirac ((0 : ℕ), b))) h := by
  rw [opt_zero b b (by simpa using hC), zero_add]
  exact hε.trans_le (err_ge0 b _ h hb)

-- zero samples, two constant-labelled distributions: some distribution fails with probability ≥ 1/2
theorem Z2 {C : ConceptClass ℕ Bool} (hC0 : (fun _ => false) ∈ C) (hC1 : (fun _ => true) ∈ C)
    {𝒟 : Set (Measure X)} (h𝒟 : D0 ⊆ 𝒟)
    {ε δ : Set.Ioo (0 : ℝ≥0) 1} (hε : (ε.val : ℝ≥0∞) < q (3/8)) (hδ : δ.val < 1/2) :
    ¬ IsRPACLearnerFor.{0, 0, 0} 0 ε δ C 𝒟 := by
  rintro ⟨Ω, _, Q, _, A, hA⟩
  obtain ⟨m0, i0⟩ := hA _ (h𝒟 (Or.inl rfl))
  obtain ⟨m1, i1⟩ := hA _ (h𝒟 (Or.inr rfl))
  have hlt : (δ.val : ℝ≥0∞) + δ.val < 1 := by
    simp only [← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_lt_coe]
    rw [← NNReal.coe_lt_coe] at *; push_cast at *; linarith
  refine absurd ((int2 Q _ _ m0 ?_).trans (add_le_add i0 i1)) (not_le.mpr hlt)
  intro ω
  cases hb : A ω f0 0
  · exact le_add_left (pi0_ge _ _ (fail_anchor true _ hε hC1 _ (by simp [hb])))
  · exact le_add_right (pi0_ge _ _ (fail_anchor false _ hε hC0 _ (by simp [hb])))

-- zero samples, four distributions with one tail point: failure probability ≥ 3/4 somewhere
theorem Z4 : ¬ IsRPACLearnerFor.{0, 0, 0} 0 e8 d58 Cstar Dstar := by
  rintro ⟨Ω, _, Q, _, A, hA⟩
  have mem : ∀ b c : Bool, DD b (Measure.dirac ((0 : ℕ), c)) ∈ Dstar :=
    fun b c => ⟨_, _, inferInstance, rfl⟩
  obtain ⟨m1, i1⟩ := hA _ (mem false false)
  obtain ⟨m2, i2⟩ := hA _ (mem false true)
  obtain ⟨m3, i3⟩ := hA _ (mem true false)
  obtain ⟨_, i4⟩ := hA _ (mem true true)
  have fail : ∀ b c : Bool, ∀ h : ℕ → Bool, (h 0 ≠ b ∨ h 2 ≠ c) →
      optimalError (DD b (Measure.dirac ((0 : ℕ), c))) Cstar + (e8.val : ℝ≥0∞)
        < error (DD b (Measure.dirac ((0 : ℕ), c))) h := by
    intro b c h hbc
    rw [opt_zero b c (C := Cstar) (Set.mem_univ _), zero_add]
    rcases hbc with hb | hc
    · exact (by show q (1/8) < q (3/8); enn : (e8.val : ℝ≥0∞) < q (3/8)).trans_le (err_ge0 b _ h hb)
    · refine lt_of_lt_of_le ?_ (err_ge_tail b _ h)
      have : (Measure.dirac ((0 : ℕ), c)) {p : X | h (p.1 + 2) ≠ p.2} = 1 := by
        rw [Measure.dirac_apply]; simp [hc]
      rw [this, mul_one]; show q (1/8) < q (1/4); enn
  have hlt : (d58.val : ℝ≥0∞) + d58.val + d58.val + d58.val < 3 := by
    show q (5/8) + q (5/8) + q (5/8) + q (5/8) < 3
    rw [show (3 : ℝ≥0∞) = q 3 by simp [q]]; enn
  refine absurd ((int4 Q _ _ _ _ m1 m2 m3 ?_).trans
    (add_le_add (add_le_add (add_le_add i1 i2) i3) i4)) (not_le.mpr hlt)
  intro ω
  have one : ∀ b c : Bool, (A ω f0 0 ≠ b ∨ A ω f0 2 ≠ c) →
      1 ≤ Measure.pi (fun _ : Fin 0 => DD b (Measure.dirac ((0 : ℕ), c)))
        {S | optimalError (DD b (Measure.dirac ((0 : ℕ), c))) Cstar + (e8.val : ℝ≥0∞)
          < error (DD b (Measure.dirac ((0 : ℕ), c))) (A ω S)} :=
    fun b c hbc => pi0_ge _ _ (fail b c _ hbc)
  cases h0 : A ω f0 0 <;> cases h2 : A ω f0 2
  · -- succeeds only at (false, false)
    have := one false true (by simp [h2]); have := one true false (by simp [h0])
    have := one true true (by simp [h0])
    calc (3 : ℝ≥0∞) = 0 + 1 + 1 + 1 := by norm_num
      _ ≤ _ := by gcongr <;> first | exact zero_le | assumption
  · have := one false false (by simp [h2]); have := one true false (by simp [h0])
    have := one true true (by simp [h0])
    calc (3 : ℝ≥0∞) = 1 + 0 + 1 + 1 := by norm_num
      _ ≤ _ := by gcongr <;> first | exact zero_le | assumption
  · have := one false false (by simp [h0]); have := one false true (by simp [h0])
    have := one true true (by simp [h2])
    calc (3 : ℝ≥0∞) = 1 + 1 + 0 + 1 := by norm_num
      _ ≤ _ := by gcongr <;> first | exact zero_le | assumption
  · have := one false false (by simp [h0]); have := one false true (by simp [h0])
    have := one true false (by simp [h2])
    calc (3 : ℝ≥0∞) = 1 + 1 + 1 + 0 := by norm_num
      _ ≤ _ := by gcongr <;> first | exact zero_le | assumption

/-! ## The impossibility (No-Free-Lunch counting)

Fix m and N = 32 (m + 2)² + m. For a labelling f : Fin N → Bool of N tail points, `Df f` puts
3/8 on each anchor (label false) and 1/(4N) on each tail point (j + 2, f j). Average over all
2^N labellings: for any deterministic m-sample learner, conditioned on the sample locations the
k ≥ N − m unseen labels are fair coins, so with probability ≥ 3/8 the learner is wrong on more than
half of the tail (binomial anti-concentration), i.e. error > 1/8. Averaging the per-seed bound over
a randomized learner's seed contradicts failure probability ≤ 1/3 for every `Df f`. -/

section Imp
open Finset
open scoped Classical

/-! ### Step 1: binomial tail (pure ℕ) -/

theorem central_sq (t : ℕ) : t.centralBinom ^ 2 * (t + 1) ≤ 16 ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have key := Nat.succ_mul_centralBinom_succ t
    set c := t.centralBinom
    set c' := (t + 1).centralBinom
    have h1 : (t + 1) ^ 3 * (c' ^ 2 * (t + 1 + 1)) = 4 * (2 * t + 1) ^ 2 * (t + 2) * (c ^ 2 * (t + 1)) := by
      calc (t + 1) ^ 3 * (c' ^ 2 * (t + 1 + 1)) = ((t + 1) * c') ^ 2 * ((t + 1) * (t + 2)) := by ring
        _ = (2 * (2 * t + 1) * c) ^ 2 * ((t + 1) * (t + 2)) := by rw [key]
        _ = _ := by ring
    have h2 := Nat.mul_le_mul_left (4 * (2 * t + 1) ^ 2 * (t + 2)) ih
    have h3 : 4 * (2 * t + 1) ^ 2 * (t + 2) ≤ 16 * (t + 1) ^ 3 := by ring_nf; nlinarith
    have h4 : (t + 1) ^ 3 * (c' ^ 2 * (t + 1 + 1)) ≤ (t + 1) ^ 3 * 16 ^ (t + 1) := by
      rw [h1]
      calc _ ≤ 4 * (2 * t + 1) ^ 2 * (t + 2) * 16 ^ t := h2
        _ ≤ 16 * (t + 1) ^ 3 * 16 ^ t := Nat.mul_le_mul_right _ h3
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left h4 (by positivity)

theorem choose_mid_sq (k : ℕ) : (k.choose (k / 2)) ^ 2 * (k / 2 + 1) ≤ 4 ^ k := by
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' k
  · have h2 : 2 * t / 2 = t := by omega
    rw [h2, ← Nat.centralBinom_eq_two_mul_choose, pow_mul]
    exact (central_sq t).trans (by norm_num)
  · have h2 : (2 * t + 1) / 2 = t := by omega
    rw [h2]
    have hc : (2 * t + 1).choose t ≤ 2 * t.centralBinom := by
      have e := Nat.add_one_mul_choose_eq (2 * t) t
      rw [Nat.choose_symm_half] at e
      rw [Nat.centralBinom_eq_two_mul_choose]
      have : (2 * t + 1).choose t * (t + 1) ≤ 2 * (2 * t).choose t * (t + 1) := by
        rw [← e]; nlinarith
      exact Nat.le_of_mul_le_mul_right this (by omega)
    calc (2 * t + 1).choose t ^ 2 * (t + 1) ≤ (2 * t.centralBinom) ^ 2 * (t + 1) := by gcongr
      _ = 4 * (t.centralBinom ^ 2 * (t + 1)) := by ring
      _ ≤ 4 * 16 ^ t := Nat.mul_le_mul_left _ (central_sq t)
      _ = 4 ^ (2 * t + 1) := by rw [pow_succ, pow_mul]; norm_num; ring

theorem binom_tail (k m : ℕ) (hk : 32 * (m + 2) ^ 2 ≤ k) :
    3 * 2 ^ k ≤ 8 * ∑ j ∈ range (k + 1), if k + m < 2 * j then k.choose j else 0 := by
  set T := ∑ j ∈ range (k + 1), if k + m < 2 * j then k.choose j else 0
  set L := ∑ j ∈ range (k + 1), if 2 * j + m < k then k.choose j else 0
  set M := ∑ j ∈ range (k + 1), if ¬ (k + m < 2 * j) ∧ ¬ (2 * j + m < k) then k.choose j else 0
  have htot : 2 ^ k = T + L + M := by
    rw [← Nat.sum_range_choose k, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> omega
  have hLT : L = T := by
    simp only [L, T]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have e : k + 1 - 1 - j = k - j := by omega
    rw [e, Nat.choose_symm (by omega)]
    congr 1; apply propext; omega
  have hmid : M ≤ (m + 1) * k.choose (k / 2) := by
    calc M ≤ ∑ j ∈ range (k + 1), if ¬ (k + m < 2 * j) ∧ ¬ (2 * j + m < k) then k.choose (k / 2) else 0 :=
          Finset.sum_le_sum fun j _ => by split_ifs <;> simp [Nat.choose_le_middle]
      _ = #{j ∈ range (k + 1) | ¬ (k + m < 2 * j) ∧ ¬ (2 * j + m < k)} * k.choose (k / 2) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
      _ ≤ (m + 1) * k.choose (k / 2) := by
          gcongr
          calc _ ≤ #(Icc ((k + 1 - m) / 2) ((k + 1 - m) / 2 + m)) := by
                apply Finset.card_le_card
                intro j hj
                simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hj ⊢
                omega
            _ = m + 1 := by simp; omega
  have hsq : 16 * (m + 1) ^ 2 ≤ k / 2 + 1 := by
    have : (m + 1) ^ 2 ≤ (m + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have h4 : 4 * (m + 1) * k.choose (k / 2) ≤ 2 ^ k := by
    have : (4 * (m + 1) * k.choose (k / 2)) ^ 2 ≤ (2 ^ k) ^ 2 := by
      calc (4 * (m + 1) * k.choose (k / 2)) ^ 2 = (16 * (m + 1) ^ 2) * k.choose (k / 2) ^ 2 := by ring
        _ ≤ (k / 2 + 1) * k.choose (k / 2) ^ 2 := Nat.mul_le_mul_right _ hsq
        _ = k.choose (k / 2) ^ 2 * (k / 2 + 1) := by ring
        _ ≤ 4 ^ k := choose_mid_sq k
        _ = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
  have : 4 * M ≤ 2 ^ k := by
    calc 4 * M ≤ 4 * ((m + 1) * k.choose (k / 2)) := Nat.mul_le_mul_left _ hmid
      _ = 4 * (m + 1) * k.choose (k / 2) := by ring
      _ ≤ _ := h4
  omega

/-! ### Step 2: counting labellings -/

theorem count_far {U : Type} [Fintype U] (c : U → Bool) (N m : ℕ)
    (hk : 32 * (m + 2) ^ 2 ≤ Fintype.card U) (hN : N ≤ Fintype.card U + m) :
    3 * 2 ^ Fintype.card U ≤ 8 * #{g : U → Bool | N < 2 * #{u | g u ≠ c u}} := by
  have e1 : #{g : U → Bool | N < 2 * #{u | g u ≠ c u}} = #{s : Finset U | N < 2 * #s} := by
    refine Finset.card_bij' (fun g _ => univ.filter (fun u => g u ≠ c u))
      (fun s _ => fun u => if u ∈ s then !c u else c u) ?_ ?_ ?_ ?_
    · intro g hg; simpa using hg
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      convert hs using 3
      ext u; by_cases hu : u ∈ s <;> simp [hu]
    · intro g _; funext u
      by_cases hu : g u = c u <;> simp [hu]
      cases h1 : g u <;> cases h2 : c u <;> simp_all
    · intro s _; ext u; by_cases hu : u ∈ s <;> simp [hu]
  have e2 : #{s : Finset U | N < 2 * #s}
      = ∑ j ∈ range (Fintype.card U + 1), (Fintype.card U).choose j • (if N < 2 * j then 1 else 0) := by
    rw [Finset.card_filter, ← Finset.powerset_univ, Finset.sum_powerset_apply_card (fun j => if N < 2 * j then 1 else 0), Finset.card_univ]
  rw [e1, e2]
  refine (binom_tail _ m hk).trans (Nat.mul_le_mul_left _ (Finset.sum_le_sum fun j _ => ?_))
  simp only [smul_eq_mul]
  split_ifs <;> omega

def Nm (m : ℕ) : ℕ := 32 * (m + 2) ^ 2 + m

instance (m : ℕ) : NeZero (Nm m) := ⟨by unfold Nm; positivity⟩

theorem count_core (m : ℕ) (R : Finset (Fin (Nm m))) (hR : #R ≤ m)
    (H : (Fin (Nm m) → Bool) → Fin (Nm m) → Bool)
    (hH : ∀ f f', (∀ j ∈ R, f j = f' j) → H f = H f') :
    3 * 2 ^ Nm m ≤ 8 * #{f : Fin (Nm m) → Bool | Nm m < 2 * #{j | H f j ≠ f j}} := by
  set e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ R) (fun _ => Bool)
  have hR' : Fintype.card {j // j ∈ R} = #R := Fintype.card_coe R
  have hcardU : Fintype.card {j // j ∉ R} = Nm m - #R := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hR']
  have hNm : 32 * (m + 2) ^ 2 + m = Nm m := rfl
  have per : ∀ r : {j // j ∈ R} → Bool, 3 * 2 ^ Fintype.card {j // j ∉ R} ≤
      8 * #{g : {j // j ∉ R} → Bool | Nm m < 2 * #{j | H (e.symm (r, g)) j ≠ e.symm (r, g) j}} := by
    intro r
    let c : {j // j ∉ R} → Bool := fun u => H (e.symm (r, fun _ => false)) u.1
    refine (count_far c (Nm m) m (by omega) (by omega)).trans (Nat.mul_le_mul_left _ ?_)
    refine Finset.card_le_card fun g hg => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    refine lt_of_lt_of_le hg (Nat.mul_le_mul_left _ ?_)
    have hHe : H (e.symm (r, g)) = H (e.symm (r, fun _ => false)) := hH _ _ fun j hj => by
      simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hj]
    refine Finset.card_le_card_of_injOn (fun u => u.1) ?_ ?_
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hu ⊢
      have : e.symm (r, g) u.1 = g u := by simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, u.2]
      rw [hHe, this]; exact fun h => hu h.symm
    · intro u _ v _ h; exact Subtype.ext h
  calc 3 * 2 ^ Nm m = ∑ _r : {j // j ∈ R} → Bool, 3 * 2 ^ Fintype.card {j // j ∉ R} := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, hR', smul_eq_mul, hcardU,
          ← mul_assoc, mul_comm (2 ^ #R) 3, mul_assoc, ← pow_add]
        congr 2; omega
    _ ≤ ∑ r, 8 * #{g : {j // j ∉ R} → Bool | Nm m < 2 * #{j | H (e.symm (r, g)) j ≠ e.symm (r, g) j}} :=
        Finset.sum_le_sum fun r _ => per r
    _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finset.card_filter]
        rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]

/-! ### Step 3: the distributions -/

abbrev Loc (N : ℕ) := Bool ⊕ Fin N

def pt {N : ℕ} (f : Fin N → Bool) : Loc N → X
  | .inl a => (if a then 1 else 0, false)
  | .inr j => ((j : ℕ) + 2, f j)

noncomputable def w (N : ℕ) : Loc N → ℝ≥0∞
  | .inl _ => q (3/8)
  | .inr _ => q (1/4) * (N : ℝ≥0∞)⁻¹

noncomputable def Tf {N : ℕ} (f : Fin N → Bool) : Measure X :=
  ∑ j : Fin N, (N : ℝ≥0∞)⁻¹ • Measure.dirac ((j : ℕ), f j)

noncomputable def Df {N : ℕ} (f : Fin N → Bool) : Measure X := DD false (Tf f)

theorem Tf_apply {N : ℕ} (f : Fin N → Bool) (s : Set X) :
    Tf f s = (N : ℝ≥0∞)⁻¹ * #{j : Fin N | ((j : ℕ), f j) ∈ s} := by
  simp only [Tf, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    Measure.dirac_apply, ← Finset.mul_sum, Set.indicator_apply, Pi.one_apply, Finset.sum_boole]

instance Tf_prob {N : ℕ} [NeZero N] (f : Fin N → Bool) : IsProbabilityMeasure (Tf f) := by
  constructor
  rw [Tf_apply]
  simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_fin]
  exact ENNReal.inv_mul_cancel (by simp [NeZero.ne N]) (by simp)

instance Df_prob {N : ℕ} [NeZero N] (f : Fin N → Bool) : IsProbabilityMeasure (Df f) := by
  unfold Df; infer_instance

theorem Df_mem {N : ℕ} [NeZero N] (f : Fin N → Bool) : Df f ∈ Dstar := ⟨_, _, inferInstance, rfl⟩

theorem Df_pt {N : ℕ} (f : Fin N → Bool) (x : Loc N) : Df f {pt f x} = w N x := by
  rcases x with a | j
  · cases a <;> simp [Df, DD_apply, pt, tl, Set.indicator_apply, w, Set.preimage, Tf_apply]
  · rw [Df, DD_apply, Tf_apply]
    have : #{j' : Fin N | ((j' : ℕ), f j') ∈ tl ⁻¹' {pt f (.inr j)}} = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨j, ?_⟩
      ext j'
      simp [pt, tl, Fin.ext_iff]
      intro h; rw [Fin.ext h]
    rw [this]
    simp [pt, Set.indicator_apply, w]

theorem opt_Df {N : ℕ} (f : Fin N → Bool) : optimalError (Df f) Cstar = 0 := by
  let g : ℕ → Bool := fun n => if h : 2 ≤ n ∧ n - 2 < N then f ⟨n - 2, h.2⟩ else false
  have hg : error (Df f) g = 0 := by
    rw [Df, err_tail false (Tf f) g (by simp [g]) (by simp [g]), Tf_apply]
    simp [g]
  exact le_antisymm ((iInf₂_le g (Set.mem_univ _)).trans hg.le) (zero_le)

theorem lt_aux (N a : ℕ) [NeZero N] (hh : N < 2 * a) :
    q (1/8) < q (1/4) * ((N : ℝ≥0∞)⁻¹ * (a : ℝ≥0∞)) := by
  have ha : (N : ℝ) < 2 * a := by exact_mod_cast hh
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have key : (1/8 : ℝ) < 1/4 * ((N : ℝ)⁻¹ * a) := by
    have : 1/2 < (N : ℝ)⁻¹ * a := by
      rw [lt_inv_mul_iff₀ hN]; linarith
    linarith
  have e : q (1/4) * ((N : ℝ≥0∞)⁻¹ * (a : ℝ≥0∞)) = ((1/4 * ((N : ℝ≥0)⁻¹ * a) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_inv (by exact_mod_cast NeZero.ne N)]
    simp [q]
  rw [e]; simp only [q]
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]; push_cast; exact key

theorem fail_Df {N : ℕ} [NeZero N] (f : Fin N → Bool) (h : ℕ → Bool)
    (hh : N < 2 * #{j : Fin N | h ((j : ℕ) + 2) ≠ f j}) : q (1/8) < error (Df f) h := by
  have e := err_ge_tail false (Tf f) h
  rw [Tf_apply] at e
  refine lt_of_lt_of_le (lt_aux N _ ?_) e
  convert hh using 4

/-! ### Step 4: the m-sample measure, bounded below by a finite sum over sample locations -/

theorem sum_w (N m : ℕ) [NeZero N] : ∑ ℓ : Fin m → Loc N, ∏ i, w N (ℓ i) = 1 := by
  have h1 : ∑ x, w N x = 1 := by
    rw [Fintype.sum_sum_type]
    simp only [w, Fintype.sum_bool, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm (q (1/4)), ← mul_assoc, ENNReal.mul_inv_cancel (by simp [NeZero.ne N]) (by simp), one_mul]
    try simp only [Fintype.card_bool, Nat.cast_ofNat]
    rw [two_mul]; enn
  rw [← Fintype.sum_pow, h1, one_pow]

theorem pi_ge {N m : ℕ} [NeZero N] (f : Fin N → Bool) (E : Set (Fin m → X)) :
    ∑ ℓ : Fin m → Loc N, (∏ i, w N (ℓ i)) * E.indicator 1 (fun i => pt f (ℓ i))
      ≤ Measure.pi (fun _ => Df f) E := by
  set S : (Fin m → Loc N) → (Fin m → X) := fun ℓ i => pt f (ℓ i) with hSdef
  have hpt : Function.Injective (pt f) := by
    rintro (a | j) (b | k) h <;> simp only [pt, Prod.mk.injEq] at h
    · cases a <;> cases b <;> simp_all
    · cases a <;> simp at h <;> omega
    · cases b <;> simp at h <;> omega
    · exact congrArg Sum.inr (Fin.ext (by have := h.1; omega))
  have hS : Function.Injective S := fun ℓ ℓ' h => funext fun i => hpt (congrFun h i)
  have hsing : ∀ ℓ, Measure.pi (fun _ : Fin m => Df f) {S ℓ} = ∏ i, w N (ℓ i) := by
    intro ℓ
    rw [← Set.univ_pi_singleton, Measure.pi_pi]
    exact Finset.prod_congr rfl fun i _ => Df_pt f (ℓ i)
  calc ∑ ℓ, (∏ i, w N (ℓ i)) * E.indicator 1 (S ℓ)
      = ∑ ℓ ∈ Finset.univ.filter (fun ℓ => S ℓ ∈ E), Measure.pi (fun _ : Fin m => Df f) {S ℓ} := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        by_cases h : S ℓ ∈ E <;> simp [h, hsing]
    _ = Measure.pi (fun _ : Fin m => Df f) (⋃ ℓ ∈ Finset.univ.filter (fun ℓ => S ℓ ∈ E), {S ℓ}) :=
        (measure_biUnion_finset (fun ℓ _ ℓ' _ hne => Set.disjoint_singleton.mpr fun h => hne (hS h))
          (fun ℓ _ => measurableSet_singleton _)).symm
    _ ≤ _ := measure_mono (Set.iUnion₂_subset fun ℓ hℓ => by
        simpa using (Finset.mem_filter.mp hℓ).2)

/-! ### Step 5: for fixed sample locations, ≥ 3/8 of the labellings make the learner fail -/

theorem count_loc (m : ℕ) (A0 : Learner ℕ Bool m) (ℓ : Fin m → Loc (Nm m)) :
    3 * 2 ^ Nm m ≤ 8 * #{f : Fin (Nm m) → Bool | q (1/8) < error (Df f) (A0 (fun i => pt f (ℓ i)))} := by
  let R : Finset (Fin (Nm m)) := Finset.univ.biUnion fun i => (ℓ i).elim (fun _ => ∅) (fun j => {j})
  have hR : #R ≤ m := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ i, #((ℓ i).elim (fun _ => (∅ : Finset (Fin (Nm m)))) (fun j => {j})) ≤ ∑ _i : Fin m, 1 :=
          Finset.sum_le_sum fun i _ => by cases ℓ i <;> simp
      _ = m := by simp
  have hH : ∀ f f' : Fin (Nm m) → Bool, (∀ j ∈ R, f j = f' j) →
      (fun g : Fin (Nm m) → Bool => fun j : Fin (Nm m) => A0 (fun i => pt g (ℓ i)) ((j : ℕ) + 2)) f
        = (fun g : Fin (Nm m) → Bool => fun j : Fin (Nm m) => A0 (fun i => pt g (ℓ i)) ((j : ℕ) + 2)) f' := by
    intro f f' hff
    have : (fun i => pt f (ℓ i)) = (fun i => pt f' (ℓ i)) := by
      funext i
      cases hℓ : ℓ i with
      | inl a => rfl
      | inr j =>
        have hj : j ∈ R := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hℓ]⟩
        simp [pt, hff j hj]
    simp only [this]
  refine (count_core m R hR _ hH).trans (Nat.mul_le_mul_left _ (Finset.card_le_card fun f hf => ?_))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
  exact fail_Df f _ hf

/-! ### Step 6: average over labellings, for a deterministic learner -/

theorem avg_det (m : ℕ) (A0 : Learner ℕ Bool m) :
    3 * 2 ^ Nm m ≤ 8 * ∑ f : Fin (Nm m) → Bool, Measure.pi (fun _ : Fin m => Df f)
      {S | optimalError (Df f) Cstar + (e8.val : ℝ≥0∞) < error (Df f) (A0 S)} := by
  have he8 : (e8.val : ℝ≥0∞) = q (1/8) := rfl
  have step : ∀ f : Fin (Nm m) → Bool, ∑ ℓ : Fin m → Loc (Nm m), (∏ i, w (Nm m) (ℓ i)) *
      (if q (1/8) < error (Df f) (A0 (fun i => pt f (ℓ i))) then 1 else 0) ≤
      Measure.pi (fun _ : Fin m => Df f)
        {S | optimalError (Df f) Cstar + (e8.val : ℝ≥0∞) < error (Df f) (A0 S)} := by
    intro f
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun ℓ _ => ?_)) (pi_ge f _)
    by_cases h : q (1/8) < error (Df f) (A0 (fun i => pt f (ℓ i))) <;>
      simp [h, Set.indicator_apply, opt_Df, he8]
  calc (3 : ℝ≥0∞) * 2 ^ Nm m = ∑ ℓ : Fin m → Loc (Nm m), (∏ i, w (Nm m) (ℓ i)) * (3 * 2 ^ Nm m) := by
        rw [← Finset.sum_mul, sum_w, one_mul]
    _ ≤ ∑ ℓ : Fin m → Loc (Nm m), (∏ i, w (Nm m) (ℓ i)) *
          (8 * (#{f : Fin (Nm m) → Bool | q (1/8) < error (Df f) (A0 (fun i => pt f (ℓ i)))} : ℝ≥0∞)) := by
        refine Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left ?_ (zero_le)
        exact_mod_cast count_loc m A0 ℓ
    _ = 8 * ∑ f : Fin (Nm m) → Bool, ∑ ℓ : Fin m → Loc (Nm m), (∏ i, w (Nm m) (ℓ i)) *
          (if q (1/8) < error (Df f) (A0 (fun i => pt f (ℓ i))) then 1 else 0) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [← Finset.mul_sum, Finset.sum_boole]
        ring
    _ ≤ _ := by gcongr with f; exact step f

/-! ### Step 7: randomized learners -/

theorem imp (m : ℕ) : ¬ IsRPACLearnerFor.{0, 0, 0} m e8 d3 Cstar Dstar := by
  rintro ⟨Ω, _, Q, _, A, hA⟩
  let F : (Fin (Nm m) → Bool) → Ω → ℝ≥0∞ := fun f ω => Measure.pi (fun _ : Fin m => Df f)
    {S | optimalError (Df f) Cstar + (e8.val : ℝ≥0∞) < error (Df f) (A ω S)}
  have hm : ∀ f, AEMeasurable (F f) Q := fun f => (hA (Df f) (Df_mem f)).1
  have hi : ∀ f, ∫⁻ ω, F f ω ∂Q ≤ (d3.val : ℝ≥0∞) := fun f => (hA (Df f) (Df_mem f)).2
  have h1 : (3 : ℝ≥0∞) * 2 ^ Nm m ≤ 8 * ∑ f, ∫⁻ ω, F f ω ∂Q := by
    rw [← lintegral_finsetSum' _ (fun f _ => hm f), ← lintegral_const_mul' _ _ (by simp)]
    calc (3 : ℝ≥0∞) * 2 ^ Nm m = ∫⁻ _, 3 * 2 ^ Nm m ∂Q := by simp
      _ ≤ _ := lintegral_mono fun ω => avg_det m (A ω)
  have h2 : ∑ f, ∫⁻ ω, F f ω ∂Q ≤ 2 ^ Nm m * q (1/3) := by
    refine (Finset.sum_le_sum fun f _ => hi f).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; rfl
  have hP0 : (2 : ℝ≥0∞) ^ Nm m ≠ 0 := by simp
  have hPt : (2 : ℝ≥0∞) ^ Nm m ≠ ⊤ := by simp
  have h3 : (3 : ℝ≥0∞) * 2 ^ Nm m ≤ (8 * q (1/3)) * 2 ^ Nm m := by
    calc _ ≤ _ := h1
      _ ≤ 8 * (2 ^ Nm m * q (1/3)) := by gcongr
      _ = _ := by ring
  have h4 := (ENNReal.mul_le_mul_iff_left hP0 hPt).mp h3
  have : (8 : ℝ≥0∞) * q (1/3) < 3 := by
    rw [show (8 : ℝ≥0∞) = q 8 by simp [q], show (3 : ℝ≥0∞) = q 3 by simp [q]]; enn
  exact absurd h4 (not_le.mpr this)

end Imp

/-! ## Consequences -/

theorem impD (m : ℕ) : ¬ IsPACLearnerFor m e8 d3 Cstar Dstar := fun h => imp m h.toIsRPACLearnerFor

theorem notL : ¬ IsPACLearnable Cstar Dstar := fun h => (h e8 d3).elim impD
theorem notRL : ¬ IsRPACLearnable Cstar Dstar := fun h => (h e8 d3).elim imp

theorem hC0 : (fun _ => false) ∈ C0 := Or.inl rfl
theorem hC1 : (fun _ => true) ∈ C0 := Or.inr rfl

theorem Z4D : ¬ IsPACLearnerFor 0 e8 d58 Cstar Dstar := fun h => Z4 h.toIsRPACLearnerFor
theorem Z2e4 : ¬ IsRPACLearnerFor.{0, 0, 0} 0 e4 d3 Cstar Dstar :=
  Z2 (Set.mem_univ _) (Set.mem_univ _) D0_sub (by show q (1/4) < q (3/8); enn) (by show (1/3 : ℝ≥0) < 1/2; enn)
theorem Z2D0 : ¬ IsRPACLearnerFor.{0, 0, 0} 0 e8 d3 Cstar D0 :=
  Z2 (Set.mem_univ _) (Set.mem_univ _) subset_rfl (by show q (1/8) < q (3/8); enn) (by show (1/3 : ℝ≥0) < 1/2; enn)
theorem Z2C0 : ¬ IsRPACLearnerFor.{0, 0, 0} 0 e8 d3 C0 Dstar :=
  Z2 hC0 hC1 D0_sub (by show q (1/8) < q (3/8); enn) (by show (1/3 : ℝ≥0) < 1/2; enn)

theorem sc_one {L : LearnerModel ℕ Bool} {C : ConceptClass ℕ Bool} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {𝒟 : Set (Measure X)} (h1 : L 1 ε δ C 𝒟) (h0 : ¬ L 0 ε δ C 𝒟) :
    1 ≤ sampleComplexity L C ε δ 𝒟 := by
  rw [Nat.one_le_iff_ne_zero]
  intro h
  rcases Nat.sInf_eq_zero.mp h with h | h
  · exact h0 h
  · have : (1 : ℕ) ∈ {m | L m ε δ C 𝒟} := h1
    rw [h] at this; exact this

theorem sc_zero {L : LearnerModel ℕ Bool} {C : ConceptClass ℕ Bool} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {𝒟 : Set (Measure X)} (h : ∀ m, ¬ L m ε δ C 𝒟) : sampleComplexity L C ε δ 𝒟 = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inr (by ext m; simpa using h m))

theorem contra {a b : ℕ} (ha : 1 ≤ a) (hb : b = 0) (h : a ≤ b) : False := by omega

theorem learn_empty {C : ConceptClass ℕ Bool} : IsPACLearnable C (∅ : Set (Measure X)) :=
  fun _ _ => ⟨0, fun _ _ => false, fun D _ hD => by simp at hD⟩
theorem rlearn_empty {C : ConceptClass ℕ Bool} : IsRPACLearnable C (∅ : Set (Measure X)) :=
  fun ε δ => (learn_empty ε δ).imp fun _ h => h.toIsRPACLearnerFor
theorem learnC_empty : IsPACLearnable (∅ : ConceptClass ℕ Bool) Dstar :=
  fun _ _ => ⟨0, fun _ _ => false, fun D _ _ => by simp [optimalError]⟩

theorem hd : d3.val ≤ d58.val := by show (1/3 : ℝ≥0) ≤ 5/8; enn
theorem he : e8.val ≤ e4.val := by show (1/8 : ℝ≥0) ≤ 1/4; enn

/-! ## The 19 rows -/

-- `Cslib.MachineLearning.PACLearning.sampleComplexity_antitone_δ` idx 10: necessary (sc at δ = 5/8 is 1, at δ = 1/3 it is sInf ∅ = 0)
theorem r1 : ¬ drop0% Cslib.MachineLearning.PACLearning.sampleComplexity_antitone_δ 10 := fun h =>
  contra (sc_one L_anc Z4D) (sc_zero impD) (@h ℕ Bool _ _ e8 d3 d58 hd Cstar Dstar)

-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_δ` idx 6: necessary (as r1)
theorem r2 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_δ 6 := fun h =>
  contra (sc_one L_anc Z4D) (sc_zero impD) (@h ℕ Bool _ _ Cstar Dstar e8 d3 d58 hd)

-- `Cslib.MachineLearning.PACLearning.rsampleComplexity_antitone_δ` idx 10: necessary (as r1, randomized)
theorem r3 : ¬ drop0% Cslib.MachineLearning.PACLearning.rsampleComplexity_antitone_δ 10 := fun h =>
  contra (sc_one L_anc.toIsRPACLearnerFor Z4) (sc_zero imp) (@h ℕ Bool _ _ e8 d3 d58 hd Cstar Dstar)

-- `Cslib.MachineLearning.PACLearning.IsRPACLearnable.rsampleComplexity_antitone_δ` idx 6: necessary (as r3)
theorem r4 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsRPACLearnable.rsampleComplexity_antitone_δ 6 := fun h =>
  contra (sc_one L_anc.toIsRPACLearnerFor Z4) (sc_zero imp) (@h ℕ Bool _ _ Cstar Dstar e8 d3 d58 hd)

-- `Cslib.MachineLearning.PACLearning.sampleComplexity_antitone_ε` idx 10: necessary (sc at ε = 1/4 is 1, at ε = 1/8 it is 0)
theorem r5 : ¬ drop0% Cslib.MachineLearning.PACLearning.sampleComplexity_antitone_ε 10 := fun h =>
  contra (sc_one L_e4 fun h0 => Z2e4 h0.toIsRPACLearnerFor) (sc_zero impD)
    (@h ℕ Bool _ _ e8 e4 d3 he Cstar Dstar)

-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_ε` idx 6: necessary (as r5)
theorem r6 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_ε 6 := fun h =>
  contra (sc_one L_e4 fun h0 => Z2e4 h0.toIsRPACLearnerFor) (sc_zero impD)
    (@h ℕ Bool _ _ Cstar Dstar e8 e4 d3 he)

-- `Cslib.MachineLearning.PACLearning.sampleComplexity_mono_family` idx 10: necessary (sc for D0 is 1, for Dstar 0)
theorem r7 : ¬ drop0% Cslib.MachineLearning.PACLearning.sampleComplexity_mono_family 10 := fun h =>
  contra (sc_one L_D0 fun h0 => Z2D0 h0.toIsRPACLearnerFor) (sc_zero impD)
    (@h ℕ Bool _ _ e8 d3 Cstar D0 Dstar D0_sub)

-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_mono_family` idx 7: necessary (as r7)
theorem r8 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_mono_family 7 := fun h =>
  contra (sc_one L_D0 fun h0 => Z2D0 h0.toIsRPACLearnerFor) (sc_zero impD)
    (@h ℕ Bool _ _ Cstar D0 Dstar D0_sub e8 d3)

-- `Cslib.MachineLearning.PACLearning.rsampleComplexity_mono_family` idx 10: necessary (as r7, randomized)
theorem r9 : ¬ drop0% Cslib.MachineLearning.PACLearning.rsampleComplexity_mono_family 10 := fun h =>
  contra (sc_one L_D0.toIsRPACLearnerFor Z2D0) (sc_zero imp) (@h ℕ Bool _ _ e8 d3 Cstar D0 Dstar D0_sub)

-- `Cslib.MachineLearning.PACLearning.IsRPACLearnable.rsampleComplexity_mono_family` idx 7: necessary (as r9)
theorem r10 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsRPACLearnable.rsampleComplexity_mono_family 7 := fun h =>
  contra (sc_one L_D0.toIsRPACLearnerFor Z2D0) (sc_zero imp) (@h ℕ Bool _ _ Cstar D0 Dstar D0_sub e8 d3)

-- `Cslib.MachineLearning.PACLearning.sampleComplexity_mono_C` idx 10: necessary (sc for C0 is 1, for Cstar 0)
theorem r11 : ¬ drop0% Cslib.MachineLearning.PACLearning.sampleComplexity_mono_C 10 := fun h =>
  contra (sc_one L_C0 fun h0 => Z2C0 h0.toIsRPACLearnerFor) (sc_zero impD)
    (@h ℕ Bool _ _ e8 d3 C0 Cstar (Set.subset_univ _) Dstar)

-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_mono_C` idx 7: necessary (as r11)
theorem r12 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_mono_C 7 := fun h =>
  contra (sc_one L_C0 fun h0 => Z2C0 h0.toIsRPACLearnerFor) (sc_zero impD)
    (@h ℕ Bool _ _ C0 Cstar Dstar (Set.subset_univ _) e8 d3)

-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.antitone_family` idx 7: necessary (𝒟' = ∅ is learnable, Dstar is not)
theorem r13 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.antitone_family 7 := fun h =>
  notL (@h ℕ Bool _ _ Cstar Dstar ∅ learn_empty)

-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.antitone_family` idx 8: necessary (Cstar, Dstar not learnable)
theorem r14 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.antitone_family 8 := fun h =>
  notL (@h ℕ Bool _ _ Cstar Dstar Dstar subset_rfl)

-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.antitone_C` idx 6: necessary (C' = ∅ is learnable, Cstar is not)
theorem r15 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.antitone_C 6 := fun h =>
  notL (@h ℕ Bool _ _ Cstar ∅ Dstar learnC_empty)

-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.antitone_C` idx 8: necessary (Cstar, Dstar not learnable)
theorem r16 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.antitone_C 8 := fun h =>
  notL (@h ℕ Bool _ _ Cstar Cstar subset_rfl Dstar)

-- `Cslib.MachineLearning.PACLearning.IsPACLearnable.toIsRPACLearnable` idx 6: necessary (Cstar, Dstar not randomized-learnable)
theorem r17 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsPACLearnable.toIsRPACLearnable 6 := fun h =>
  notRL (@h ℕ Bool _ _ Cstar Dstar)

-- `Cslib.MachineLearning.PACLearning.IsRPACLearnable.antitone_family` idx 7: necessary (𝒟' = ∅ is learnable, Dstar is not)
theorem r18 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsRPACLearnable.antitone_family 7 := fun h =>
  notRL (@h ℕ Bool _ _ Cstar Dstar ∅ rlearn_empty)

-- `Cslib.MachineLearning.PACLearning.IsRPACLearnable.antitone_family` idx 8: necessary (Cstar, Dstar not randomized-learnable)
theorem r19 : ¬ drop0% Cslib.MachineLearning.PACLearning.IsRPACLearnable.antitone_family 8 := fun h =>
  notRL (@h ℕ Bool _ _ Cstar Dstar Dstar subset_rfl)

end P1c0
