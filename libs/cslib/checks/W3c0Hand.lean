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

namespace W3c0
section
open Turing Turing.MultiTapeNTM
abbrev C1 := Turing.Cfg 1 Unit Unit ([] : List Unit)
def cfg (p : ℤ) (t : ℤ → Option Unit) : C1 := ⟨some (), 0, fun _ => t, fun _ => p, []⟩
def actR : Action 1 Unit Unit := ⟨0, fun _ => (some (some ()), 1), none, some ()⟩
def M : MultiTapeNTM 1 Unit Unit := ⟨(), fun _ _ _ a => a = actR⟩
theorem stepR (p : ℤ) (t) : M.Step (cfg p t) (actR.apply (cfg p t)) := ⟨actR, rfl, rfl⟩
def bl : ℤ → Option Unit := fun _ => none
end
section
/-- constant false and the projections on coordinate 0 / 1 -/
def fc (n : ℕ) : Cslib.BooleanFunction n := fun _ => false
def p0 : Cslib.BooleanFunction 1 := fun y => y 0
def p1 : Cslib.BooleanFunction 2 := fun y => y 1
def x0 (n : ℕ) : Cslib.BitString n := fun _ => false
end
section
open Cslib.URM
/-- the one-instruction infinite loop `J 0 0 0` -/
def L : Program := [Instr.J 0 0 0]
def one : Regs := fun _ => 1
def zr : Regs := fun _ => 0
theorem stepL {s t : Cslib.URM.State} (h : Cslib.URM.Step L s t) : t.pc = 0 := by
  rcases s with ⟨_ | _, r⟩ <;> cases h <;> simp_all [L] <;> (obtain ⟨rfl, rfl, rfl⟩ := ‹_ ∧ _ ∧ _›; simp_all)
theorem stepsL {s t : Cslib.URM.State} (h : Cslib.URM.Steps L s t) (hs : s.pc = 0) : t.pc = 0 := by
  induction h with
  | refl => exact hs
  | tail _ h2 _ => exact stepL h2
theorem loopNH (inputs : List ℕ) : ¬ Cslib.URM.Halts L inputs := fun ⟨s, hs, hh⟩ => by
  have := stepsL hs rfl
  simp [Cslib.URM.State.isHalted, L, this] at hh
theorem sfL : L.toStandardForm = L := by decide
theorem nostep0 {s t : Cslib.URM.State} : ¬ Cslib.URM.Step [] s t := fun h => by cases h <;> simp_all
theorem steps0 {s t : Cslib.URM.State} (h : Cslib.URM.Steps [] s t) : t = s := by
  induction h with
  | refl => rfl
  | tail _ h2 _ => exact absurd h2 nostep0
end
section
open scoped NNReal
open Cslib.Crypto Cslib.Crypto.PRG
theorem notNeg {ε : ℕ → ℝ≥0} (h : ∀ n, 1 ≤ ε n) : ¬ Negligible ε := fun hn => by
  obtain ⟨m, hm⟩ := (negligible_iff ε).1 hn 0 1 one_pos
  have := hm m le_rfl
  simp at this
  exact absurd (h m) (not_le.2 this)
theorem negHalf : Negligible (fun n => (2⁻¹ : ℝ≥0) ^ n) := by
  intro k
  rw [← NNReal.tendsto_coe]
  simpa using tendsto_pow_const_mul_const_pow_of_abs_lt_one k (r := (2⁻¹ : ℝ)) (by norm_num [abs_of_pos])
theorem two_half (n : ℕ) : (2 : ℝ≥0) ^ n * 2⁻¹ ^ n = 1 := by
  rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
theorem nd1 : ¬ Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ))
    (fun _ => ((1 : ℝ≥0) : ℝ)) := fun h => by
  have := h 0
  norm_num at this
theorem ndc (c : ℝ≥0) (hc : c ≠ 0) : ¬ Asymptotics.SuperpolynomialDecay Filter.atTop
    (fun n : ℕ => (n : ℝ)) (fun _ => (c : ℝ)) := fun h => by
  have := h 0
  simp only [pow_zero, one_mul] at this
  exact hc (by exact_mod_cast (tendsto_nhds_unique this tendsto_const_nhds).symm)
theorem spd0 : Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ))
    (fun _ => ((0 : ℝ≥0) : ℝ)) := by
  simp only [NNReal.coe_zero]; exact Asymptotics.superpolynomialDecay_zero _ _
theorem pmfU {α : Type*} [Subsingleton α] (p q : PMF α) : p = q := by
  ext a
  have h1 := p.tsum_coe
  have h2 := q.tsum_coe
  rw [tsum_eq_single a (fun b hb => absurd (Subsingleton.elim b a) hb)] at h1 h2
  rw [h1, h2]
theorem advU {S O : Type*} [Fintype S] [Nonempty S] [Fintype O] [Nonempty O] [Subsingleton O]
    (G : Generator S O) (A : Adversary O) : G.advantage A = 0 := by
  simp [Generator.advantage, Generator.realExperiment, Generator.idealExperiment,
    pmfU G.outputDist (Cslib.Probability.PMF.uniformOfFintype O)]
/-- a family with subsingleton outputs is secure against every adversary class -/
theorem secU {S O : ℕ → Type} [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)] [∀ n, Fintype (O n)]
    [∀ n, Nonempty (O n)] [∀ n, Subsingleton (O n)] (G : Family S O) (Adm) : G.Secure Adm :=
  fun A _ => by
    have : (fun n => (G n).advantage (A n)) = fun _ => 0 := funext fun n => advU _ _
    rw [this]; exact Asymptotics.superpolynomialDecay_zero _ _
def GB : Family (fun _ => Unit) (fun _ => Bool) := fun _ => ⟨fun _ => true⟩
def GU : Family (fun _ => Unit) (fun _ => Unit) := fun _ => ⟨id⟩
def GE : Family (fun _ => Empty) (fun _ => Unit) := fun _ => ⟨Empty.elim⟩
theorem insecB : ¬ GB.Secure (fun _ => True) :=
  Family.not_secure_of_two_mul_card_le GB trivial (Filter.Eventually.of_forall fun n => by simp)
end
end W3c0

universe u v

section
open W3c0

-- `Turing.MultiTapeNTM.Step.workTapePos_le` idx 7: necessary (k=1 NTM, c' with head at 2, c at 0 (no step))
theorem r0 : ¬ drop0% Turing.MultiTapeNTM.Step.workTapePos_le 7 := fun h => by
  have := @h 1 Unit Unit [] M (cfg 0 bl) (cfg 2 bl) 0
  simp [cfg] at this
-- `Turing.MultiTapeNTM.Step.workTapes_eq_of_ne` idx 7: necessary (c' with a different tape cell away from the head (no step))
theorem r1 : ¬ drop0% Turing.MultiTapeNTM.Step.workTapes_eq_of_ne 7 := fun h => by
  have := @h 1 Unit Unit [] M (cfg 0 bl) (cfg 0 (fun _ => some ())) 0 1 (by simp [cfg])
  simp [cfg, bl] at this
-- `Turing.MultiTapeNTM.Step.workTapes_eq_of_ne` idx 10: necessary (machine writes at the head: cell 0 changes)
theorem r2 : ¬ drop0% Turing.MultiTapeNTM.Step.workTapes_eq_of_ne 10 := fun h => by
  have := @h 1 Unit Unit [] M (cfg 0 bl) _ (stepR 0 bl) 0 0
  simp [cfg, bl, actR] at this
-- `Turing.MultiTapeNTM.RunPath.mem_visitedByTapeHead_of_workTapes_ne` idx 8: necessary (singleton path at head 0; cell 1 not visited)
theorem r3 : ¬ drop0% Turing.MultiTapeNTM.RunPath.mem_visitedByTapeHead_of_workTapes_ne 8 := fun h => by
  have := @h 1 Unit Unit [] M (RelSeries.singleton _ (cfg 0 bl)) 0 1
  simp only [Turing.MultiTapeNTM.RunPath.visitedByTapeHead, Finset.mem_image] at this
  obtain ⟨a, -, ha⟩ := this
  exact absurd (show (0:ℤ) = 1 from ha) (by decide)
-- `Turing.MultiTapeNTM.RunPath.natAbs_le_spaceUsedByTape_of_mem_visited` idx 8: necessary (singleton path, z = 5: |5| > space 1)
theorem r4 : ¬ drop0% Turing.MultiTapeNTM.RunPath.natAbs_le_spaceUsedByTape_of_mem_visited 8 := fun h => by
  have := @h 1 Unit Unit [] M (RelSeries.singleton _ (cfg 0 bl)) 0 5
  have := this.trans Finset.card_image_le
  rw [Finset.card_univ, Fintype.card_fin] at this
  change 5 ≤ 0 + 1 at this
  omega
-- `Turing.MultiTapeNTM.RunPath.inWindow_of_space_le` idx 7: necessary (singleton path with head at 5, space 1 <= 1, 5 not in window 1)
theorem r5 : ¬ drop0% Turing.MultiTapeNTM.RunPath.inWindow_of_space_le 7 := fun h => by
  have := @h 1 Unit Unit [] M (RelSeries.singleton _ (cfg 5 bl)) 1
    (by
      simp only [Turing.MultiTapeNTM.RunPath.space, Turing.MultiTapeNTM.RunPath.spaceUsedByTape,
        Turing.MultiTapeNTM.RunPath.visitedByTapeHead, Fin.sum_univ_one]
      exact Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin]; exact le_refl _))
  have := this (cfg 5 bl) ⟨0, rfl⟩ 0
  simp [cfg, Turing.window] at this
-- `Turing.MultiTapeNTM.RunPath.inWindow_of_space_le` idx 8: necessary (path moving the head 0 -> 1 with s = 0)
theorem r6 : ¬ drop0% Turing.MultiTapeNTM.RunPath.inWindow_of_space_le 8 := fun h => by
  have := @h 1 Unit Unit [] M ((RelSeries.singleton _ (cfg 0 bl)).snoc _ (stepR 0 bl)) 0
    (fun i => by simp [cfg])
  have := this _ (RelSeries.last_mem _) 0
  simp [cfg, Turing.window, actR] at this
end

section
-- `Cslib.Computability.Turing.SingleTape.TrLabel.applyToTape_isSome` idx 4: necessary (ot = none)
theorem r7 : ¬ drop0% Cslib.Computability.Turing.SingleTape.TrLabel.applyToTape_isSome 4 := fun h =>
  absurd (@h Unit _ .skip none) (by decide)
-- `Cslib.Computability.Turing.SingleTape.TrLabel.applyToTape_foldl_isSome` idx 4: necessary (ot = none, empty label list)
theorem r8 : ¬ drop0% Cslib.Computability.Turing.SingleTape.TrLabel.applyToTape_foldl_isSome 4 := fun h =>
  absurd (@h Unit _ [] none) (by decide)
-- `Cslib.Turing.SingleTapeTM.Cfg.spaceUsed_step` idx 6: necessary (idComputer, cfg' = initCfg [(),(),()] (space 3) vs initCfg [] (space 1))
theorem r9 : ¬ drop0% Cslib.Turing.SingleTapeTM.Cfg.spaceUsed_step 6 := fun h => by
  have := @h Unit _ _ Cslib.Turing.SingleTapeTM.idComputer (Cslib.Turing.SingleTapeTM.initCfg _ [])
    (Cslib.Turing.SingleTapeTM.initCfg _ [(), (), ()])
  simp [Cslib.Turing.SingleTapeTM.Cfg.spaceUsed_initCfg] at this
-- `Cslib.Turing.SingleTapeTM.output_length_le_input_length_add_time` idx 7: necessary (l = [], l' = [(),()], t = 0)
theorem r10 : ¬ drop0% Cslib.Turing.SingleTapeTM.output_length_le_input_length_add_time 7 := fun h => by
  have := @h Unit _ _ Cslib.Turing.SingleTapeTM.idComputer [] [(), ()] 0
  simp at this
-- `_private.Cslib.Computability.Machines.Turing.SingleTape.Deterministic.0.Cslib.Turing.SingleTapeTM.map_toCompCfg_left_step` idx 6: necessary (cfg1 halted: left side none, composed machine steps)
theorem r11 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.SingleTape.Deterministic.«0».Cslib.Turing.SingleTapeTM.map_toCompCfg_left_step 6 := fun h => by
  have := @h Unit _ _ Cslib.Turing.SingleTapeTM.idComputer Cslib.Turing.SingleTapeTM.idComputer ⟨none, default⟩
  exact Option.some_ne_none _ this.symm
-- `_private.Cslib.Computability.Machines.Turing.SingleTape.Deterministic.0.Cslib.Turing.SingleTapeTM.comp_left_relatesWithinSteps` idx 8: necessary (t = 0: initial (inl) and intermediate (inr) configs differ)
theorem r12 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.SingleTape.Deterministic.«0».Cslib.Turing.SingleTapeTM.comp_left_relatesWithinSteps 8 := fun h => by
  have := congrArg (·.state) (Relation.RelatesWithinSteps.zero
    (@h Unit _ _ Cslib.Turing.SingleTapeTM.idComputer Cslib.Turing.SingleTapeTM.idComputer [] [] 0))
  change (some (Sum.inl PUnit.unit) : Option (PUnit ⊕ PUnit)) = some (Sum.inr PUnit.unit) at this
  simp at this
-- `_private.Cslib.Computability.Machines.Turing.SingleTape.Deterministic.0.Cslib.Turing.SingleTapeTM.comp_right_relatesWithinSteps` idx 8: necessary (t = 0: intermediate (running) and final (halted) configs differ)
theorem r13 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.SingleTape.Deterministic.«0».Cslib.Turing.SingleTapeTM.comp_right_relatesWithinSteps 8 := fun h => by
  have := congrArg (·.state) (Relation.RelatesWithinSteps.zero
    (@h Unit _ _ Cslib.Turing.SingleTapeTM.idComputer Cslib.Turing.SingleTapeTM.idComputer [] [] 0))
  change (some (Sum.inr PUnit.unit) : Option (PUnit ⊕ PUnit)) = none at this
  simp at this
-- `Cslib.Computability.Turing.SingleTape.SingleTapeNTM.accept_halting` idx 4: necessary (NTM with Tr = True and accept = ∅)
theorem r14 : ¬ drop0% Cslib.Computability.Turing.SingleTape.SingleTapeNTM.accept_halting 4 := fun h =>
  @h Unit Unit { Tr := fun _ _ _ => True, start := ∅, accept := ∅, accept_halting := by simp } ()
    ⟨.skip, (), trivial⟩
end

section
open W3c0

-- `Cslib.BitString.flipBlock_apply_of_mem` idx 4: necessary (B = ∅)
theorem r15 : ¬ drop0% Cslib.BitString.flipBlock_apply_of_mem 4 := fun h =>
  absurd (@h 1 ∅ (x0 1) 0) (by decide)
-- `Cslib.BitString.flipBlock_apply_of_notMem` idx 4: necessary (B = {0})
theorem r16 : ¬ drop0% Cslib.BitString.flipBlock_apply_of_notMem 4 := fun h =>
  absurd (@h 1 {0} (x0 1) 0) (by decide)
-- `Cslib.BitString.card_le_sensitivityAt` idx 4: necessary (n = 1, constant f, S = univ (sensitivity 0))
theorem r17 : ¬ drop0% Cslib.BitString.card_le_sensitivityAt 4 := fun h =>
  absurd (@h 1 (fc 1) (x0 1) Finset.univ) (by decide)
-- `Cslib.BitString.card_le_sensitivity_of_forall_isSensitiveCoord` idx 4: necessary (n = 1, constant f, S = univ (sensitivity 0))
theorem r18 : ¬ drop0% Cslib.BitString.card_le_sensitivity_of_forall_isSensitiveCoord 4 := fun h =>
  absurd (@h 1 (fc 1) (x0 1) Finset.univ) (by decide)
-- `Cslib.QueryComplexity.card_le_blockSensitivityAt` idx 4: necessary (n = 0, F = {∅}: card 1 > bs ≤ 0)
theorem r19 : ¬ drop0% Cslib.QueryComplexity.card_le_blockSensitivityAt 4 := fun h =>
  absurd ((@h 0 (fc 0) (x0 0) {∅}).trans (Cslib.QueryComplexity.blockSensitivityAt_le_card _ _))
    (by decide)
-- `Cslib.QueryComplexity.card_le_blockSensitivity` idx 4: necessary (n = 0, F = {∅}: card 1 > bs ≤ 0)
theorem r20 : ¬ drop0% Cslib.QueryComplexity.card_le_blockSensitivity 4 := fun h =>
  absurd ((@h 0 (fc 0) (x0 0) {∅}).trans (Cslib.QueryComplexity.blockSensitivity_le_card _))
    (by decide)
-- `Cslib.QueryComplexity.IsMinimalSensitiveBlock.not_isSensitiveBlock_erase` idx 5: necessary (n = 2, f = x1, B = {0,1}, i = 0 (not minimal, {1} sensitive))
theorem r21 : ¬ drop0% Cslib.QueryComplexity.IsMinimalSensitiveBlock.not_isSensitiveBlock_erase 5 := fun h =>
  @h 2 p1 (x0 2) {0, 1} 0 (by decide) (by decide)
-- `Cslib.QueryComplexity.IsMinimalSensitiveBlock.not_isSensitiveBlock_erase` idx 6: necessary (n = 2, f = x1, B = {1} minimal, i = 0 ∉ B)
theorem r22 : ¬ drop0% Cslib.QueryComplexity.IsMinimalSensitiveBlock.not_isSensitiveBlock_erase 6 := fun h =>
  @h 2 p1 (x0 2) {1} 0 (by decide) (by decide)
-- `Cslib.QueryComplexity.IsMinimalSensitiveBlock.isSensitiveCoord_flipBlock` idx 5: necessary (constant f, B = {0})
theorem r23 : ¬ drop0% Cslib.QueryComplexity.IsMinimalSensitiveBlock.isSensitiveCoord_flipBlock 5 := fun h =>
  absurd (@h 1 (fc 1) (x0 1) {0} 0 (by decide)) (by decide)
-- `Cslib.QueryComplexity.IsMinimalSensitiveBlock.isSensitiveCoord_flipBlock` idx 6: necessary (n = 2, f = x1, B = {1} minimal, i = 0 ∉ B)
theorem r24 : ¬ drop0% Cslib.QueryComplexity.IsMinimalSensitiveBlock.isSensitiveCoord_flipBlock 6 := fun h =>
  absurd (@h 2 p1 (x0 2) {1} 0 (by decide)) (by decide)
-- `Cslib.QueryComplexity.IsMinimalSensitiveBlock.card_le_sensitivity` idx 4: necessary (n = 1, constant f, B = univ)
theorem r25 : ¬ drop0% Cslib.QueryComplexity.IsMinimalSensitiveBlock.card_le_sensitivity 4 := fun h =>
  absurd (@h 1 (fc 1) (x0 1) Finset.univ) (by decide)
-- `Cslib.QueryComplexity.certificateComplexityAt_le` idx 4: necessary (n = 1, f = x0, S = ∅ (C(f,x) = 1))
theorem r26 : ¬ drop0% Cslib.QueryComplexity.certificateComplexityAt_le 4 := fun h =>
  absurd (@h 1 p0 (x0 1) ∅) (by decide)
-- `Cslib.QueryComplexity.sensitiveBlock_inter_nonempty` idx 4: necessary (B = ∅, S = univ)
theorem r27 : ¬ drop0% Cslib.QueryComplexity.sensitiveBlock_inter_nonempty 4 := fun h =>
  absurd (@h 1 (fc 1) (x0 1) ∅ Finset.univ (by decide)) (by decide)
-- `Cslib.QueryComplexity.sensitiveBlock_inter_nonempty` idx 6: necessary (f = x0, B = univ, S = ∅)
theorem r28 : ¬ drop0% Cslib.QueryComplexity.sensitiveBlock_inter_nonempty 6 := fun h =>
  absurd (@h 1 p0 (x0 1) Finset.univ (by decide) ∅) (by decide)
-- `Cslib.QueryComplexity.card_le_card_of_isSensitiveFamily` idx 5: necessary (n = 0, F = {∅}, S = ∅)
theorem r29 : ¬ drop0% Cslib.QueryComplexity.card_le_card_of_isSensitiveFamily 5 := fun h =>
  absurd (@h 0 (fc 0) (x0 0) {∅} ∅ (by decide)) (by decide)
-- `Cslib.QueryComplexity.card_le_card_of_isSensitiveFamily` idx 6: necessary (n = 1, f = x0, F = {univ}, S = ∅)
theorem r30 : ¬ drop0% Cslib.QueryComplexity.card_le_card_of_isSensitiveFamily 6 := fun h =>
  absurd (@h 1 p0 (x0 1) {Finset.univ} ∅ (by decide)) (by decide)
end

section
open W3c0 Cslib.URM

-- `Cslib.URM.Instr.shiftJumps_of_nonJump` idx 1: necessary (J 0 0 0, offset 1)
theorem r31 : ¬ drop0% Cslib.URM.Instr.shiftJumps_of_nonJump 1 := fun h =>
  absurd (@h (.J 0 0 0) 1) (by decide)
-- `Cslib.URM.Instr.JumpsBoundedBy.mono` idx 3: necessary (J 0 0 5, len1 = len2 = 0)
theorem r32 : ¬ drop0% Cslib.URM.Instr.JumpsBoundedBy.mono 3 := fun h =>
  absurd (@h (.J 0 0 5) 0 0 le_rfl) (by decide)
-- `Cslib.URM.Instr.JumpsBoundedBy.mono` idx 4: necessary (J 0 0 5, len1 = 5, len2 = 0)
theorem r33 : ¬ drop0% Cslib.URM.Instr.JumpsBoundedBy.mono 4 := fun h =>
  absurd (@h (.J 0 0 5) 5 0 (by decide)) (by decide)
-- `Cslib.URM.Instr.JumpsBoundedBy.shiftJumps` idx 3: necessary (J 0 0 5, len = offset = 0)
theorem r34 : ¬ drop0% Cslib.URM.Instr.JumpsBoundedBy.shiftJumps 3 := fun h =>
  absurd (@h (.J 0 0 5) 0 0) (by decide)
-- `Cslib.URM.Program.mem_maxRegister` idx 2: necessary (p = [], Z 5)
theorem r35 : ¬ drop0% Cslib.URM.Program.mem_maxRegister 2 := fun h =>
  absurd (@h [] (.Z 5)) (by decide)
-- `Cslib.URM.Step.no_step_of_halted` idx 3: necessary (p = [Z 0] at pc 0 steps)
theorem r36 : ¬ drop0% Cslib.URM.Step.no_step_of_halted 3 := fun h =>
  @h [.Z 0] ⟨0, zr⟩ _ (Step.zero rfl)
-- `Cslib.URM.Step.preserves_register` idx 4: necessary (p = [] (hr vacuous), s' with other registers)
theorem r37 : ¬ drop0% Cslib.URM.Step.preserves_register 4 := fun h =>
  absurd (@h [] ⟨0, zr⟩ ⟨0, one⟩ 0 (fun _ h => by simp at h)) (by simp [zr, one, Regs.read])
-- `Cslib.URM.Step.preserves_register` idx 5: necessary (p = [Z 0] zeroes register 0)
theorem r38 : ¬ drop0% Cslib.URM.Step.preserves_register 5 := fun h =>
  absurd (@h [.Z 0] ⟨0, one⟩ _ 0 (Step.zero rfl)) (by simp [one, Regs.read, Regs.write])
-- `Cslib.URM.Steps.preserves_register` idx 4: necessary (p = [] (hr vacuous), s' with other registers)
theorem r39 : ¬ drop0% Cslib.URM.Steps.preserves_register 4 := fun h =>
  absurd (@h [] ⟨0, zr⟩ ⟨0, one⟩ 0 (fun _ h => by simp at h)) (by simp [zr, one, Regs.read])
-- `Cslib.URM.Steps.preserves_register` idx 5: necessary (p = [Z 0] zeroes register 0)
theorem r40 : ¬ drop0% Cslib.URM.Steps.preserves_register 5 := fun h =>
  absurd (@h [.Z 0] ⟨0, one⟩ _ 0 (.single (Step.zero rfl))) (by simp [one, Regs.read, Regs.write])
-- `Cslib.URM.Steps.eq_of_halts` idx 5: necessary (p = [Z 0]: s1 = init (not halted), s2 after one step)
theorem r41 : ¬ drop0% Cslib.URM.Steps.eq_of_halts 5 := fun h =>
  absurd (congrArg Cslib.URM.State.pc (@h [.Z 0] ⟨0, one⟩ ⟨0, one⟩ _ .refl (.single (Step.zero rfl)) (by decide)))
    (by decide)
-- `Cslib.URM.Steps.eq_of_halts` idx 6: necessary (p = []: two unrelated halted states)
theorem r42 : ¬ drop0% Cslib.URM.Steps.eq_of_halts 6 := fun h =>
  absurd (congrArg Cslib.URM.State.pc (@h [] ⟨0, zr⟩ ⟨0, zr⟩ ⟨1, zr⟩ .refl (by decide) (by decide))) (by decide)
-- `Cslib.URM.Steps.eq_of_halts` idx 7: necessary (p = [Z 0]: s2 = init (not halted))
theorem r43 : ¬ drop0% Cslib.URM.Steps.eq_of_halts 7 := fun h =>
  absurd (congrArg Cslib.URM.State.pc (@h [.Z 0] ⟨0, one⟩ _ ⟨0, one⟩ (.single (Step.zero rfl)) (by decide) .refl))
    (by decide)
-- `Cslib.URM.HaltsWithResult.toHalts` idx 3: necessary (p = [J 0 0 0] loops forever)
theorem r44 : ¬ drop0% Cslib.URM.HaltsWithResult.toHalts 3 := fun h => loopNH [] (@h L [] 0)
-- `Cslib.URM.evalState_spec` idx 2: necessary (p = [J 0 0 0] does not halt)
theorem r45 : ¬ indep0% Cslib.URM.evalState_spec 2 := fun h => loopNH [] (@h L [])
-- `Cslib.URM.Halts.toHaltsWithResult` idx 2: necessary (p = [J 0 0 0] does not halt)
theorem r46 : ¬ indep0% Cslib.URM.Halts.toHaltsWithResult 2 := fun h => loopNH [] (@h L [])
-- `Cslib.URM.straight_line_IsStandardForm` idx 1: necessary ([J 0 0 5])
theorem r47 : ¬ drop0% Cslib.URM.straight_line_IsStandardForm 1 := fun h =>
  absurd (@h [.J 0 0 5]) (by decide)
-- `Cslib.URM.Step.toStandardForm` idx 3: necessary (p = []: no step at all)
theorem r48 : ¬ drop0% Cslib.URM.Step.toStandardForm 3 := fun h => by
  rcases @h [] ⟨0, zr⟩ ⟨0, zr⟩ with h1 | ⟨-, s₂, h2, -⟩
  · exact nostep0 h1
  · exact nostep0 h2
-- `Cslib.URM.Steps.toStandardForm_halts` idx 3: necessary (p = []: only reachable state is s, registers differ from s')
theorem r49 : ¬ drop0% Cslib.URM.Steps.toStandardForm_halts 3 := fun h => by
  obtain ⟨s₂, h1, -, h3⟩ := @h [] ⟨0, zr⟩ ⟨0, one⟩ (by decide)
  rw [steps0 (s := ⟨0, zr⟩) h1] at h3
  exact absurd (congrFun h3 0) (by simp [zr, one])
-- `Cslib.URM.Steps.toStandardForm_halts` idx 4: necessary (loop J 0 0 0 never halts)
theorem r50 : ¬ drop0% Cslib.URM.Steps.toStandardForm_halts 4 := fun h => by
  obtain ⟨s₂, h1, h2, -⟩ := @h L ⟨0, zr⟩ ⟨0, zr⟩ .refl
  rw [sfL] at h1 h2
  have := stepsL h1 rfl
  simp [Cslib.URM.State.isHalted, L, this] at h2
-- `Cslib.URM.Halts.toStandardForm` idx 2: necessary (loop J 0 0 0 (its own standard form))
theorem r51 : ¬ drop0% Cslib.URM.Halts.toStandardForm 2 := fun h => loopNH [] (sfL ▸ @h L [])
-- `Cslib.URM.Step.from_toStandardForm` idx 3: necessary (p = []: no step at all)
theorem r52 : ¬ drop0% Cslib.URM.Step.from_toStandardForm 3 := fun h => by
  rcases @h [] ⟨0, zr⟩ ⟨0, zr⟩ with h1 | ⟨-, s₂, h2, -⟩
  · exact nostep0 h1
  · exact nostep0 h2
-- `Cslib.URM.Steps.from_toStandardForm_halts` idx 3: necessary (p = []: only reachable state is s, registers differ from s')
theorem r53 : ¬ drop0% Cslib.URM.Steps.from_toStandardForm_halts 3 := fun h => by
  obtain ⟨s₂, h1, -, h3⟩ := @h [] ⟨0, zr⟩ ⟨0, one⟩ (by decide)
  rw [steps0 (s := ⟨0, zr⟩) h1] at h3
  exact absurd (congrFun h3 0) (by simp [zr, one])
-- `Cslib.URM.Steps.from_toStandardForm_halts` idx 4: necessary (loop J 0 0 0 never halts)
theorem r54 : ¬ drop0% Cslib.URM.Steps.from_toStandardForm_halts 4 := fun h => by
  obtain ⟨s₂, h1, h2, -⟩ := @h L ⟨0, zr⟩ ⟨0, zr⟩ (sfL ▸ .refl)
  have := stepsL h1 rfl
  simp [Cslib.URM.State.isHalted, L, this] at h2
-- `Cslib.URM.Halts.of_toStandardForm` idx 2: necessary (loop J 0 0 0 never halts)
theorem r55 : ¬ drop0% Cslib.URM.Halts.of_toStandardForm 2 := fun h => loopNH [] (@h L [])
-- `Cslib.URM.evalState_toStandardForm_regs` idx 2: removable (hp follows from hq (Halts.of_toStandardForm))
theorem r56 : indep% Cslib.URM.evalState_toStandardForm_regs 2 := fun hq => Cslib.URM.Halts.of_toStandardForm hq
-- `Cslib.URM.evalState_toStandardForm_regs` idx 3: removable (hq follows from hp (Halts.toStandardForm))
theorem r57 : indep% Cslib.URM.evalState_toStandardForm_regs 3 := fun hp => Cslib.URM.Halts.toStandardForm hp
-- `Cslib.URM.Program.IsStraightLine.append` idx 2: necessary (p = [J 0 0 0], q = [])
theorem r58 : ¬ drop0% Cslib.URM.Program.IsStraightLine.append 2 := fun h =>
  absurd (@h [.J 0 0 0] [] (by decide)) (by decide)
-- `Cslib.URM.Program.IsStraightLine.append` idx 3: necessary (p = [], q = [J 0 0 0])
theorem r59 : ¬ drop0% Cslib.URM.Program.IsStraightLine.append 3 := fun h =>
  absurd (@h [] [.J 0 0 0] (by decide)) (by decide)
-- `Cslib.URM.Program.IsStraightLine.cons` idx 2: necessary (instr = J 0 0 0, p = [])
theorem r60 : ¬ drop0% Cslib.URM.Program.IsStraightLine.cons 2 := fun h =>
  absurd (@h (.J 0 0 0) [] (by decide)) (by decide)
-- `Cslib.URM.Program.IsStraightLine.cons` idx 3: necessary (instr = Z 0, p = [J 0 0 0])
theorem r61 : ¬ drop0% Cslib.URM.Program.IsStraightLine.cons 3 := fun h =>
  absurd (@h (.Z 0) [.J 0 0 0] (by decide)) (by decide)
-- `Cslib.URM.Program.IsStraightLine.singleton` idx 1: necessary (J 0 0 0)
theorem r62 : ¬ drop0% Cslib.URM.Program.IsStraightLine.singleton 1 := fun h =>
  absurd (@h (.J 0 0 0)) (by decide)
-- `Cslib.URM.Step.of_nonJump` idx 2: necessary (p = [], pc 0)
theorem r63 : ¬ indep0% Cslib.URM.Step.of_nonJump 2 := fun h =>
  absurd (@h [] ⟨0, zr⟩) (by decide)
-- `Cslib.URM.Step.of_nonJump` idx 3: necessary (loop J 0 0 0 jumps back to pc 0)
theorem r64 : ¬ drop0% Cslib.URM.Step.of_nonJump 3 := fun h => by
  obtain ⟨s', h1, h2⟩ := @h L ⟨0, zr⟩ (by decide)
  rw [stepL h1] at h2
  exact absurd h2 (by decide)
-- `Cslib.URM.straight_line_halts_from_regs` idx 1: necessary (loop J 0 0 0 never halts)
theorem r65 : ¬ drop0% Cslib.URM.straight_line_halts_from_regs 1 := fun h => by
  obtain ⟨s, h1, h2, -⟩ := @h L zr
  have := stepsL h1 rfl
  simp [Cslib.URM.State.isHalted, L, this] at h2
-- `Cslib.URM.straight_line_halts` idx 1: necessary (loop J 0 0 0 never halts)
theorem r66 : ¬ drop0% Cslib.URM.straight_line_halts 1 := fun h => loopNH [] (@h L [])
-- `Cslib.URM.straightLinefinalState_spec` idx 1: necessary (p = [J 0 0 0])
theorem r67 : ¬ indep0% Cslib.URM.straightLinefinalState_spec 1 := fun h =>
  absurd (@h L zr) (by decide)
-- `Cslib.URM.straightLineFinalRegs_eq_of_halted` idx 1: necessary (p = [J 0 0 1] halts at pc 1 but is not straight-line)
theorem r68 : ¬ indep0% Cslib.URM.straightLineFinalRegs_eq_of_halted 1 := fun h =>
  absurd (@h [.J 0 0 1] zr ⟨1, zr⟩ (.single (Step.jump_eq rfl rfl)) (by decide)) (by decide)
-- `Cslib.URM.straightLineFinalRegs_eq_of_halted` idx 5: necessary (p = [Z 0], s = initial state (not halted), registers differ from final)
theorem r69 : ¬ drop0% Cslib.URM.straightLineFinalRegs_eq_of_halted 5 := fun h => by
  have hsl : Program.IsStraightLine [.Z 0] := by decide
  have h1 := @h [.Z 0] hsl one ⟨0, one⟩ .refl
  have h2 := straightLineFinalRegs_eq_of_halted hsl one _ (.single (Step.zero rfl)) (by decide)
  have := congrFun (h1.trans h2.symm) 0
  simp [one, Regs.write] at this
-- `Cslib.URM.straight_line_state_at_pc` idx 1: necessary (loop J 0 0 0, target pc 1)
theorem r70 : ¬ drop0% Cslib.URM.straight_line_state_at_pc 1 := fun h => by
  obtain ⟨s, h1, h2⟩ := @h L zr 1 (by decide)
  rw [stepsL h1 rfl] at h2
  exact absurd h2 (by decide)
-- `Cslib.URM.straight_line_state_at_pc` idx 4: necessary (p = [], target pc 1)
theorem r71 : ¬ drop0% Cslib.URM.straight_line_state_at_pc 4 := fun h => by
  obtain ⟨s, h1, h2⟩ := @h [] (by decide) zr 1
  rw [steps0 h1] at h2
  exact absurd h2 (by decide)
end

section
open W3c0

-- `Cslib.Crypto.Negligible.congr'` idx 2: necessary (ε = δ = 1)
theorem r72 : ¬ drop0% Cslib.Crypto.Negligible.congr' 2 := fun h =>
  notNeg (ε := fun _ => 1) (fun _ => le_rfl) (@h (fun _ => 1) _ Filter.EventuallyEq.rfl)
-- `Cslib.Crypto.Negligible.congr'` idx 3: necessary (ε = 0, δ = 1)
theorem r73 : ¬ drop0% Cslib.Crypto.Negligible.congr' 3 := fun h =>
  notNeg (ε := fun _ => 1) (fun _ => le_rfl) (@h (fun _ => 0) _ Cslib.Crypto.negligible_zero)
-- `Cslib.Crypto.Negligible.add` idx 2: necessary (ε = 1, δ = 0)
theorem r74 : ¬ drop0% Cslib.Crypto.Negligible.add 2 := fun h =>
  notNeg (fun _ => by simp) (@h (fun _ => 1) (fun _ => 0) Cslib.Crypto.negligible_zero)
-- `Cslib.Crypto.Negligible.add` idx 3: necessary (ε = 0, δ = 1)
theorem r75 : ¬ drop0% Cslib.Crypto.Negligible.add 3 := fun h =>
  notNeg (fun _ => by simp) (@h (fun _ => 0) (fun _ => 1) Cslib.Crypto.negligible_zero)
-- `Cslib.Crypto.Negligible.mul` idx 2: necessary (ε = 2^n, δ = 2^-n (negligible), product 1)
theorem r76 : ¬ drop0% Cslib.Crypto.Negligible.mul 2 := fun h =>
  notNeg (fun n => by simp) (@h (fun n => 2 ^ n) _ negHalf)
-- `Cslib.Crypto.Negligible.mul` idx 3: necessary (ε = 2^-n, δ = 2^n, product 1)
theorem r77 : ¬ drop0% Cslib.Crypto.Negligible.mul 3 := fun h =>
  notNeg (fun n => by simp) (@h _ (fun n => 2 ^ n) negHalf)
-- `Cslib.Crypto.Negligible.sum` idx 3: necessary (ι = Unit, ε = 1)
theorem r78 : ¬ drop0% Cslib.Crypto.Negligible.sum 3 := fun h =>
  notNeg (fun _ => by simp) (@h Unit Finset.univ (fun _ _ => 1))
-- `Cslib.Crypto.negligible_of_eventually_le` idx 2: necessary (ε = δ = 1)
theorem r79 : ¬ drop0% Cslib.Crypto.negligible_of_eventually_le 2 := fun h =>
  notNeg (ε := fun _ => 1) (fun _ => le_rfl) (@h _ (fun _ => 1) (Filter.Eventually.of_forall fun _ => le_rfl))
-- `Cslib.Crypto.negligible_of_eventually_le` idx 3: necessary (ε = 1, δ = 0)
theorem r80 : ¬ drop0% Cslib.Crypto.negligible_of_eventually_le 3 := fun h =>
  notNeg (ε := fun _ => 1) (fun _ => le_rfl) (@h _ (fun _ => 0) Cslib.Crypto.negligible_zero)
-- `Cslib.Crypto.negligible_of_le` idx 2: necessary (ε = δ = 1)
theorem r81 : ¬ drop0% Cslib.Crypto.negligible_of_le 2 := fun h =>
  notNeg (ε := fun _ => 1) (fun _ => le_rfl) (@h _ (fun _ => 1) (fun _ => le_rfl))
-- `Cslib.Crypto.negligible_of_le` idx 3: necessary (ε = 1, δ = 0)
theorem r82 : ¬ drop0% Cslib.Crypto.negligible_of_le 3 := fun h =>
  notNeg (ε := fun _ => 1) (fun _ => le_rfl) (@h _ (fun _ => 0) Cslib.Crypto.negligible_zero)
-- `Cslib.Crypto.Negligible.polynomiallyBounded_mul` idx 2: necessary (ε = 1, p = 1)
theorem r83 : ¬ drop0% Cslib.Crypto.Negligible.polynomiallyBounded_mul 2 := fun h =>
  notNeg (fun _ => by simp) (@h (fun _ => 1) (fun _ => 1) ⟨0, Filter.Eventually.of_forall fun _ => by simp⟩)
-- `Cslib.Crypto.Negligible.polynomiallyBounded_mul` idx 3: necessary (ε = 2^-n, p = 2^n)
theorem r84 : ¬ drop0% Cslib.Crypto.Negligible.polynomiallyBounded_mul 3 := fun h =>
  notNeg (fun n => by simp) (@h _ (fun n => 2 ^ n) negHalf)
-- `Cslib.Crypto.PRG.Family.Secure.of_admissible` idx 3: necessary (Seed n = Empty, Output n = Unit)
theorem r85 : ¬ indep0% Cslib.Crypto.PRG.Family.Secure.of_admissible 3 := fun h =>
  (@h (fun _ => Empty) (fun _ => Unit) _ _ _ GE (fun _ => True) (fun _ => True) (fun _ h => h) 0).elim
    fun e => e.elim
-- `Cslib.Crypto.PRG.Family.Secure.of_admissible` idx 9: necessary (G: Unit -> Bool (insecure by two_mul_card_le), all adversaries admissible)
theorem r87 : ¬ drop0% Cslib.Crypto.PRG.Family.Secure.of_admissible 9 := fun h =>
  insecB (@h _ _ _ _ _ _ GB (fun _ => True) _ (fun _ h => h))
-- `Cslib.Crypto.PRG.Family.Secure.of_admissible` idx 10: necessary (Admissible = False (h vacuous), Restricted = True, G: Unit -> Bool)
theorem r88 : ¬ drop0% Cslib.Crypto.PRG.Family.Secure.of_admissible 10 := fun h =>
  insecB (@h _ _ _ _ _ _ GB (fun _ => False) _ (fun _ h => h.elim))
-- `Cslib.Crypto.PRG.Family.SecureWithError.secure` idx 3: necessary (Seed n = Empty, Output n = Unit, ε = 0)
theorem r89 : ¬ indep0% Cslib.Crypto.PRG.Family.SecureWithError.secure 3 := fun h =>
  (@h (fun _ => Empty) (fun _ => Unit) _ _ _ GE (fun _ => True) (fun _ => 0) spd0 0).elim
    fun e => e.elim
-- `Cslib.Crypto.PRG.Family.SecureWithError.secure` idx 9: necessary (ε = 0, G: Unit -> Bool insecure)
theorem r91 : ¬ drop0% Cslib.Crypto.PRG.Family.SecureWithError.secure 9 := fun h =>
  insecB (@h _ _ _ _ _ _ GB (fun _ => True) (fun _ => 0) spd0)
-- `Cslib.Crypto.PRG.Family.SecureWithError.secure` idx 10: necessary (ε = 1 (advantage ≤ 1), G: Unit -> Bool insecure)
theorem r92 : ¬ drop0% Cslib.Crypto.PRG.Family.SecureWithError.secure 10 := fun h =>
  insecB (@h _ _ _ _ _ _ GB (fun _ => True) (fun _ => 1)
    (fun A _ n => by simpa using (GB n).advantage_le_one (A n)))
-- `Cslib.Crypto.PRG.Family.not_secure_of_rangeAdversary` idx 3: necessary (Seed n = Empty, Output n = Unit, δ = 1 (gap 1))
theorem r93 : ¬ indep0% Cslib.Crypto.PRG.Family.not_secure_of_rangeAdversary 3 := fun h =>
  (@h (fun _ => Empty) (fun _ => Unit) _ _ _ _ GE (fun _ => True) trivial (fun _ => 1) nd1
    (Filter.Eventually.of_forall fun n => by simp) 0).elim fun e => e.elim
-- `Cslib.Crypto.PRG.Family.not_secure_of_rangeAdversary` idx 9: necessary (Admissible = False, G: Unit -> Bool, δ = 1/2)
theorem r95 : ¬ drop0% Cslib.Crypto.PRG.Family.not_secure_of_rangeAdversary 9 := fun h =>
  @h _ _ _ _ _ _ _ GB (fun _ => False) (fun _ => 2⁻¹) (ndc _ (by norm_num))
    (Filter.Eventually.of_forall fun n => by simp [GB]; norm_num) (fun _ h => h.elim)
-- `Cslib.Crypto.PRG.Family.not_secure_of_rangeAdversary` idx 11: necessary (Output n = Unit (every family secure), δ = 0)
theorem r96 : ¬ drop0% Cslib.Crypto.PRG.Family.not_secure_of_rangeAdversary 11 := fun h =>
  @h _ _ _ _ _ _ _ GU (fun _ => True) trivial (fun _ => 0)
    (Filter.Eventually.of_forall fun n => by simp [GU]) (secU _ _)
-- `Cslib.Crypto.PRG.Family.not_secure_of_rangeAdversary` idx 12: necessary (Output n = Unit (every family secure), δ = 1)
theorem r97 : ¬ drop0% Cslib.Crypto.PRG.Family.not_secure_of_rangeAdversary 12 := fun h =>
  @h _ _ _ _ _ _ _ GU (fun _ => True) trivial (fun _ => 1) nd1 (secU _ _)
-- `Cslib.Crypto.PRG.Family.not_secure_of_two_mul_card_le` idx 3: necessary (Seed n = Empty, Output n = Unit)
theorem r98 : ¬ indep0% Cslib.Crypto.PRG.Family.not_secure_of_two_mul_card_le 3 := fun h =>
  (@h (fun _ => Empty) (fun _ => Unit) _ _ _ _ GE (fun _ => True) trivial
    (Filter.Eventually.of_forall fun n => by simp) 0).elim fun e => e.elim
-- `Cslib.Crypto.PRG.Family.not_secure_of_two_mul_card_le` idx 9: necessary (Admissible = False, G: Unit -> Bool)
theorem r100 : ¬ drop0% Cslib.Crypto.PRG.Family.not_secure_of_two_mul_card_le 9 := fun h =>
  @h _ _ _ _ _ _ _ GB (fun _ => False) (Filter.Eventually.of_forall fun n => by simp) (fun _ h => h.elim)
-- `Cslib.Crypto.PRG.Family.not_secure_of_two_mul_card_le` idx 10: necessary (Output n = Unit (every family secure))
theorem r101 : ¬ drop0% Cslib.Crypto.PRG.Family.not_secure_of_two_mul_card_le 10 := fun h =>
  @h _ _ _ _ _ _ _ GU (fun _ => True) trivial (secU _ _)
-- `Cslib.Crypto.PRG.Family.not_secure_of_bitstring_stretch` idx 4: necessary (Admissible = False, lengths 0 -> 1)
theorem r102 : ¬ drop0% Cslib.Crypto.PRG.Family.not_secure_of_bitstring_stretch 4 := fun h =>
  @h (fun _ => 0) (fun _ => 1) (fun _ => ⟨fun _ _ => true⟩) (fun _ => False)
    (Filter.Eventually.of_forall fun n => by simp) (fun _ h => h.elim)
-- `Cslib.Crypto.PRG.Family.not_secure_of_bitstring_stretch` idx 5: necessary (lengths 0 -> 0: outputs are subsingletons, G secure)
theorem r103 : ¬ drop0% Cslib.Crypto.PRG.Family.not_secure_of_bitstring_stretch 5 := fun h =>
  @h (fun _ => 0) (fun _ => 0) (fun _ => ⟨id⟩) (fun _ => True) trivial (secU _ _)
-- `Cslib.Crypto.PRG.Family.not_exists_secure_bitstring_stretch` idx 2: necessary (lengths 0 -> 0: identity family is secure)
theorem r104 : ¬ drop0% Cslib.Crypto.PRG.Family.not_exists_secure_bitstring_stretch 2 := fun h =>
  @h (fun _ => 0) (fun _ => 0) ⟨fun _ => ⟨id⟩, secU _ _⟩
-- `Cslib.Crypto.PRG.Family.not_secure_of_bitVec_stretch` idx 4: necessary (Admissible = False, lengths 0 -> 1)
theorem r105 : ¬ drop0% Cslib.Crypto.PRG.Family.not_secure_of_bitVec_stretch 4 := fun h =>
  @h (fun _ => 0) (fun _ => 1) (fun _ => ⟨fun _ => 0⟩) (fun _ => False)
    (Filter.Eventually.of_forall fun n => by simp) (fun _ h => h.elim)

-- `Cslib.Crypto.PRG.Family.Secure.of_admissible` idx 5: removable (Nonempty Output follows from G and Nonempty Seed)
theorem r86 : indep% Cslib.Crypto.PRG.Family.Secure.of_admissible 5 := by
  intro Seed Output _ _ _ G
  intros
  rename_i n
  exact ⟨G n (Classical.arbitrary _)⟩
-- `Cslib.Crypto.PRG.Family.SecureWithError.secure` idx 5: removable (Nonempty Output follows from G and Nonempty Seed)
theorem r90 : indep% Cslib.Crypto.PRG.Family.SecureWithError.secure 5 := by
  intro Seed Output _ _ _ G
  intros
  rename_i n
  exact ⟨G n (Classical.arbitrary _)⟩
-- `Cslib.Crypto.PRG.Family.not_secure_of_rangeAdversary` idx 5: removable (Nonempty Output follows from G and Nonempty Seed)
theorem r94 : indep% Cslib.Crypto.PRG.Family.not_secure_of_rangeAdversary 5 := by
  intro Seed Output _ _ _ _ G
  intros
  rename_i n
  exact ⟨G n (Classical.arbitrary _)⟩
-- `Cslib.Crypto.PRG.Family.not_secure_of_two_mul_card_le` idx 5: removable (Nonempty Output follows from G and Nonempty Seed)
theorem r99 : indep% Cslib.Crypto.PRG.Family.not_secure_of_two_mul_card_le 5 := by
  intro Seed Output _ _ _ _ G
  intros
  rename_i n
  exact ⟨G n (Classical.arbitrary _)⟩
end
