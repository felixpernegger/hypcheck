import Lean.Elab.Command
import Cslib
import Mathlib.MeasureTheory.MeasurableSpace.Card
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

/-! # M1c0: the three measure rows (`hcm : Measurable c` with a measurable graph)

Model: `α = ℝ` (Borel), `β = D` (a copy of `ℝ` with the discrete σ-algebra), `P` = uniform
probability on `[0,1]`, `c = Ft t : x ↦ x + t`. The graph of `c` is measurable (it is the preimage
of the closed diagonal), but `x ↦ (x, c x)` is not a.e. measurable: a measurable `g : ℝ → D` equal
to the injective `c` off a null set would make every subset of a closed uncountable set Borel,
giving `2 ^ 𝔠 ≤ 𝔠`. Hence `P.map (x ↦ (x, c x))` is Mathlib's junk Dirac mass at a fixed point
`p0`, and `t ∈ {0, 1}` is chosen so that `p0` is off the graph. -/

open MeasureTheory Cardinal

namespace M1c0

-- ℝ with the discrete σ-algebra
def D : Type := ℝ
instance : MeasurableSpace D := ⊤
def toD : ℝ → D := id
def ofD : D → ℝ := id

-- the concepts: shifts, viewed as maps into the discrete copy
def Ft (t : ℝ) (x : ℝ) : D := toD (x + t)

-- uniform probability on [0,1]
noncomputable def U : Measure ℝ := volume.restrict (Set.Icc 0 1)
instance : IsProbabilityMeasure U := ⟨by simp [U]⟩

-- Borel sets of ℝ: at most continuum many
theorem card_meas : #{s : Set ℝ | MeasurableSet s} ≤ 𝔠 := by
  have h := MeasurableSpace.cardinal_measurableSet_le_continuum (α := ℝ)
    (s := MeasurableSpace.countableGeneratingSet ℝ)
    ((MeasurableSpace.countable_countableGeneratingSet).le_aleph0.trans aleph0_le_continuum)
  rwa [MeasurableSpace.generateFrom_countableGeneratingSet] at h

-- an injective map into the discrete copy is not a.e. measurable for U
theorem not_aem {F : ℝ → D} (hF : Function.Injective F) : ¬ AEMeasurable F U := by
  rintro ⟨g, hg, hfg⟩
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hfg)
  have h1 : U Nᶜ = 1 := by rw [prob_compl_eq_one_sub hN, hN0, tsub_zero]
  obtain ⟨K, hKN, hK, hKpos⟩ :=
    hN.compl.exists_lt_isClosed_of_ne_top (μ := U) (by simp [h1]) (r := 0) (by simp [h1])
  have hKunc : ¬ K.Countable := fun hc => by
    have h0 : U K = 0 :=
      le_antisymm ((Measure.le_iff'.1 Measure.restrict_le_self K).trans_eq (hc.measure_zero _))
        bot_le
    exact hKpos.ne' h0
  obtain ⟨φ, hφK, -, hφi⟩ := hK.exists_nat_bool_injection_of_not_countable hKunc
  have hgφ : ∀ z, g (φ z) = F (φ z) := fun z => by
    have hz : φ z ∉ N := hKN (hφK ⟨z, rfl⟩)
    by_contra hne
    exact hz (hsub (Ne.symm hne))
  have key : ∀ S z, z ∈ S ↔ φ z ∈ g ⁻¹' (F '' (φ '' S)) := fun S z => by
    rw [Set.mem_preimage, hgφ, Set.image_image]
    exact (hF.comp hφi).mem_set_image.symm
  let Φ : Set (ℕ → Bool) → {s : Set ℝ | MeasurableSet s} :=
    fun S => ⟨g ⁻¹' (F '' (φ '' S)), hg (MeasurableSpace.measurableSet_top)⟩
  have hΦ : Function.Injective Φ := fun S S' h => by
    have h' : g ⁻¹' (F '' (φ '' S)) = g ⁻¹' (F '' (φ '' S')) := congrArg Subtype.val h
    ext z; rw [key S, key S', h']
  have hle := (mk_le_of_injective hΦ).trans card_meas
  rw [mk_set, mk_arrow] at hle
  simp only [mk_fintype, Fintype.card_bool, Nat.cast_ofNat, lift_ofNat, mk_nat, lift_aleph0,
    two_power_aleph0] at hle
  exact (cantor 𝔠).not_ge hle

-- the graph of every shift is measurable in ℝ × D
theorem graph_meas (t : ℝ) : MeasurableSet {p : ℝ × D | p.2 = Ft t p.1} := by
  have e : {p : ℝ × D | p.2 = Ft t p.1} =
      (fun p : ℝ × D => ((p.1 + t, ofD p.2) : ℝ × ℝ)) ⁻¹' {q : ℝ × ℝ | q.1 = q.2} := by
    ext p; exact eq_comm
  rw [e]
  exact ((measurable_fst.add_const t).prodMk (measurable_from_top.comp measurable_snd))
    (measurableSet_eq_fun measurable_fst measurable_snd)

-- the junk point of `Measure.map` for non-a.e.-measurable maps into ℝ × D
noncomputable def p0 : ℝ × D := @Classical.ofNonempty _ ⟨(0, toD 0)⟩

theorem map_eq (t : ℝ) : U.map (fun x => (x, Ft t x)) = Measure.dirac p0 := by
  have hf : ¬ AEMeasurable (fun x => (x, Ft t x)) U := fun h =>
    not_aem (fun x y hxy => add_right_cancel (hxy : x + t = y + t)) h.snd
  rw [Measure.map_of_not_aemeasurable_of_ne_zero hf (IsProbabilityMeasure.ne_zero U)]
  rfl

-- the shift whose graph misses p0
open scoped Classical in
noncomputable def t0 : ℝ := if p0.2 = Ft 0 p0.1 then 1 else 0

theorem off : p0 ∉ {p : ℝ × D | p.2 = Ft t0 p.1} := by
  intro h
  change p0.2 = Ft t0 p0.1 at h
  unfold t0 at h
  split_ifs at h with h0
  · have e : ofD (Ft 0 p0.1) = ofD (Ft 1 p0.1) := h0 ▸ h ▸ rfl
    have e' : p0.1 + 0 = p0.1 + 1 := e
    linarith
  · exact h0 h

theorem dirac_graph : Measure.dirac p0 {p : ℝ × D | p.2 = Ft t0 p.1} = 0 := by
  rw [Measure.dirac_apply' _ (graph_meas t0)]
  exact Set.indicator_of_notMem off _

-- `_private.Cslib.MachineLearning.PACLearning.VersionSpace.0.Cslib.MachineLearning.PACLearning.map_graph_eq_one` idx 5: necessary (α = ℝ, β = ℝ discrete, c = x ↦ x + t0, P = uniform on [0,1]: map is the junk Dirac mass off the graph)
theorem mge5 : ¬ drop0% _private.Cslib.MachineLearning.PACLearning.VersionSpace.«0».Cslib.MachineLearning.PACLearning.map_graph_eq_one 5 := fun h => by
  have := @h ℝ D _ _ (Ft t0) U _ (graph_meas t0)
  rw [map_eq, dirac_graph] at this
  exact zero_ne_one this

-- `_private.Cslib.MachineLearning.PACLearning.VersionSpace.0.Cslib.MachineLearning.PACLearning.pi_map_graph_eq_one` idx 5: necessary (same model as map_graph_eq_one idx 5, m = 1)
theorem pmge5 : ¬ drop0% _private.Cslib.MachineLearning.PACLearning.VersionSpace.«0».Cslib.MachineLearning.PACLearning.pi_map_graph_eq_one 5 := fun h => by
  have := @h ℝ D _ _ (Ft t0) U _ (graph_meas t0) 1
  rw [map_eq, Measure.pi_pi] at this
  simp [Measure.dirac_apply' _ (graph_meas t0), Set.indicator_of_notMem off] at this

-- `Cslib.MachineLearning.PACLearning.ae_mem_versionSpace_of_realizable` idx 7: necessary (same model, C = {c}, m = 1: the one sample point is off the graph almost surely)
theorem aem7 : ¬ drop0% Cslib.MachineLearning.PACLearning.ae_mem_versionSpace_of_realizable 7 := fun h => by
  have := @h ℝ D _ _ {Ft t0} (Ft t0) rfl (graph_meas t0) U _ 1
  rw [map_eq, ae_iff] at this
  have hsub : Set.univ.pi (fun _ : Fin 1 => {p : ℝ × D | p.2 = Ft t0 p.1}ᶜ) ⊆
      {S | ¬ Ft t0 ∈ Cslib.MachineLearning.PACLearning.VersionSpace {Ft t0} S} := by
    intro S hS hv
    exact hS 0 (Set.mem_univ _) (hv.2 0).symm
  have h1 := (measure_mono hsub).trans_eq this
  rw [Measure.pi_pi] at h1
  simp [Measure.dirac_apply' _ (graph_meas t0).compl, Set.indicator_of_mem (show p0 ∈ {p : ℝ × D | p.2 = Ft t0 p.1}ᶜ from off)] at h1

end M1c0
