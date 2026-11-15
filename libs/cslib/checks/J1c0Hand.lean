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

/-! ## Joint removal of two hypotheses (J1c0)

`drop2% T i j` / `drop2_0% T i j`: `T` with its two non-dependent Prop binders `i < j` dropped
(`_0`: universes set to `0`, for refutations only).
`indep2% T i j` / `indep2_0% T i j`: for two dependent Prop binders (the conclusion or later
binders mention them): `∀ rest, Hᵢ ∧ Hⱼ`, where `rest` are the binders that depend on neither;
"jointly removable" means both are derivable from `rest`. -/

def hcDrop2 (T : Ident) (i j : Nat) (zero : Bool) : TermElabM Lean.Expr := do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← if zero then pure (ci.levelParams.map fun _ => Level.zero)
    else ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    unless i < j && j < xs.size do throwError "need i < j < {xs.size}"
    for k in [i, j] do
      let x := xs[k]!
      unless ← isProp (← inferType x) do throwError "binder {k} of {n} is not a Prop"
      for l in [k+1:xs.size] do
        if (← inferType xs[l]!).containsFVar x.fvarId! then throwError "binder {k} of {n} is dependent"
      if body.containsFVar x.fvarId! then throwError "binder {k} of {n} is dependent"
    mkForallFVars (xs.filter fun y => y != xs[i]! && y != xs[j]!) body

def hcIndep2 (T : Ident) (i j : Nat) (zero : Bool) : TermElabM Lean.Expr := do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← if zero then pure (ci.levelParams.map fun _ => Level.zero)
    else ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    unless i < j && j < xs.size do throwError "need i < j < {xs.size}"
    let xi := xs[i]!; let xj := xs[j]!
    for x in [xi, xj] do
      unless ← isProp (← inferType x) do throwError "binder of {n} is not a Prop"
    let hi ← inferType xi; let hj ← inferType xj
    if hj.containsFVar xi.fvarId! then throwError "Hⱼ mentions binder {i}"
    let mut dep := #[xi, xj]
    for l in [i+1:xs.size] do
      if l == j then continue
      let t ← inferType xs[l]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[l]!
    unless dep.size > 2 || body.containsFVar xi.fvarId! || body.containsFVar xj.fvarId! do
      throwError "neither binder is dependent: use drop2%"
    mkForallFVars (xs.filter (!dep.contains ·)) (mkAnd hi hj)

elab "drop2% " T:ident i:num j:num : term => hcDrop2 T i.getNat j.getNat false
elab "drop2_0% " T:ident i:num j:num : term => hcDrop2 T i.getNat j.getNat true
elab "indep2% " T:ident i:num j:num : term => hcIndep2 T i.getNat j.getNat false
elab "indep2_0% " T:ident i:num j:num : term => hcIndep2 T i.getNat j.getNat true

/-! ## Helpers (copied from the hand files that proved the single removals) -/

namespace J1c0
open Cslib

-- W2c0: a size-0 single-output circuit outputs an input
theorem size0proj {σ : Circuits.Signature.{v}} {U : Type u} {n : ℕ} (I : Circuits.Interpretation σ U)
    (c : Circuits.Circuit σ n 1) (hs : c.size = 0) : ∃ i, ∀ x, c.eval I x 0 = x i := by
  rcases c with ⟨_ | ⟨p, l⟩, out⟩
  · cases h : out 0 with
    | input i => exact ⟨i, fun x => by simp [Circuits.Circuit.eval, h]⟩
    | gate g => exact g.elim0
  · simp at hs

-- W2c3
theorem getForall {α : Type*} {r : Option α → Prop} {l : List (Option α)} (hf : l.Forall r)
    (hn : r none) (i : ℕ) : r l[i]! := by
  rw [List.getElem!_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact hn
  | some x => exact List.forall_iff_forall_mem.mp hf x (List.mem_of_getElem? h)

-- W3c0: the one-instruction infinite loop `J 0 0 0`
def L : URM.Program := [URM.Instr.J 0 0 0]
theorem stepL {s t : URM.State} (h : URM.Step L s t) : t.pc = 0 := by
  rcases s with ⟨_ | _, r⟩ <;> cases h <;> simp_all [L] <;>
    (obtain ⟨rfl, rfl, rfl⟩ := ‹_ ∧ _ ∧ _›; simp_all)
theorem stepsL {s t : URM.State} (h : URM.Steps L s t) (hs : s.pc = 0) : t.pc = 0 := by
  induction h with
  | refl => exact hs
  | tail _ h2 _ => exact stepL h2
theorem loopNH (inputs : List ℕ) : ¬ URM.Halts L inputs := fun ⟨s, hs, hh⟩ => by
  have := stepsL hs rfl
  simp [URM.State.isHalted, L, this] at hh

-- W1c1: {[n, n]} over ℕ
def lnn : Language ℕ := {u | ∃ n, u = [n, n]}
/-- the "trie" DFA: its state is the word read so far -/
def Mtrie : Automata.DA.FinAcc (List ℕ) ℕ := ⟨⟨⟨fun s a => s ++ [a]⟩, []⟩, lnn⟩
theorem foldl_app (x s : List ℕ) : x.foldl (fun s a => s ++ [a]) s = s ++ x := by
  induction x generalizing s with
  | nil => simp
  | cons a x ih => simp [ih]
theorem Mtrie_mtr (x : List ℕ) : Mtrie.mtr Mtrie.start x = x := foldl_app x []

-- a measurable space with only ∅ and univ measurable: every nonempty set has full measure
theorem bot_nonempty {α : Type*} [MeasurableSpace α] (P : MeasureTheory.Measure α)
    (hbot : ∀ t : Set α, MeasurableSet t → t = ∅ ∨ t = Set.univ) (s : Set α) (hs : s.Nonempty) :
    P s = P Set.univ := by
  rw [← MeasureTheory.measure_toMeasurable s]
  rcases hbot _ (MeasureTheory.measurableSet_toMeasurable P s) with h | h
  · have := MeasureTheory.subset_toMeasurable P s
    rw [h] at this
    exact absurd (Set.subset_empty_iff.mp this) hs.ne_empty
  · rw [h]
end J1c0

/-! ## Verdicts: one declaration per pair -/
namespace J1c0
open Cslib

-- `Nat.segment_zero` 1 2: jointly removable (segment f 0 = 0 for every f)
theorem segz12 : drop2% Nat.segment_zero 1 2 := by
  intro f
  unfold Nat.segment
  rw [Nat.count_succ, Nat.count_zero]
  split <;> rfl

-- `Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex` 7 8: jointly removable (Kleene: every NFA)
theorem nsaer78 : drop2% Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex 7 8 := by
  intro Symbol State _ _ nfa _ _
  exact Cslib.Automata.NA.FinAcc.nfa_eq_regex nfa

-- `Cslib.Circuits.Shannon.exists_hard_function` 2 3: jointly removable (finite U: simulate by the
-- binary full basis; infinite U: Nat.card U = 0 and a constant needs a gate)
theorem ehf23 : drop2% Cslib.Circuits.Shannon.exists_hard_function 2 3 := by
  intro σ U _ I harity
  open Cslib.Circuits in
  by_cases hU : Finite U
  · obtain ⟨N, hN⟩ := Shannon.exists_hard_function (fullInterpretation (k := 2) (Carrier := U))
      (by rintro (_ | _) <;> simp [fullSignature])
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨f, hf⟩ := hN n hn
    refine ⟨f, fun c hc => ?_⟩
    obtain ⟨d, hd, hsize⟩ := c.exists_simulation_le (fullInterpretation_simulatesWithCost I harity)
    have h1 := hf d (fun x => (congrFun hd x).trans (hc x))
    have h2 : (d.size : ℝ) ≤ c.size := by exact_mod_cast (by simpa using hsize)
    linarith
  · have : Infinite U := not_finite_iff_infinite.mp hU
    obtain ⟨a, b, hab⟩ := exists_pair_ne U
    refine ⟨1, fun n hn => ⟨fun _ => a, fun c hc => ?_⟩⟩
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, zero_pow (by omega), zero_div]
    rcases Nat.eq_zero_or_pos c.size with h0 | hpos
    · obtain ⟨i, hi⟩ := size0proj I c h0
      have := (hi (fun _ => b)).symm.trans (congrFun (hc (fun _ => b)) 0)
      exact absurd ((this : b = a).symm) hab
    · exact_mod_cast hpos

-- `Cslib.FLP.FairScheduler.omega_forall_actions` 10 12: jointly removable (neither fairness nor q s0 is used)
theorem ofa1012 : drop2% Cslib.FLP.FairScheduler.omega_forall_actions 10 12 := by
  intro P M S _ _ a d ps q r s0 ha hn k
  rw [ωSequence.flatten_def]
  exact getForall (FLP.FairScheduler.fairSeg_forallActions ps s0 _ ha hn) hn _

-- `Cslib.Automata.DA.FinAcc.unique_minimal` 3 5: NOT jointly removable (l = {[n, n]} over ℕ, M = the
-- trie DFA on List ℕ: both have Nat.card 0, but [0, 1] and [1, 0] are distinct states with the same Nerode class)
theorem um35 : ¬ drop2_0% Cslib.Automata.DA.FinAcc.unique_minimal 3 5 := fun h => by
  have hinf : Infinite lnn.NerodeQuotient := Infinite.of_injective
    (fun i : ℕ => (⟦[i]⟧ : lnn.NerodeQuotient)) (fun i j hij => by
      obtain ⟨k, hk⟩ := (Quotient.exact hij [j]).2 ⟨j, rfl⟩
      simp at hk; omega)
  have hlang : Automata.Acceptor.language Mtrie = lnn := by
    ext x
    show Mtrie.mtr Mtrie.start x ∈ lnn ↔ x ∈ lnn
    rw [Mtrie_mtr]
  obtain ⟨φ, hφ, -⟩ := @h (List ℕ) ℕ Mtrie lnn ⟨hlang, by simp [Nat.card_eq_zero_of_infinite]⟩
  have hq : (⟦[0, 1]⟧ : lnn.NerodeQuotient) = ⟦[1, 0]⟧ := Quotient.sound fun z => by
    constructor <;> rintro ⟨n, hn⟩ <;> rcases z with _ | ⟨a, _ | ⟨b, z⟩⟩ <;> simp at hn <;> omega
  have := φ.injective ((hφ [0, 1]).trans (hq.trans (hφ [1, 0]).symm))
  rw [Mtrie_mtr, Mtrie_mtr] at this
  simp at this

-- `Cslib.URM.evalState_toStandardForm_regs` 2 3: NOT jointly removable (p = [J 0 0 0] does not halt)
theorem etsr23 : ¬ indep2_0% Cslib.URM.evalState_toStandardForm_regs 2 3 := fun h =>
  loopNH [] ⟨_, Cslib.URM.evalState_spec L (@h L []).1⟩

-- `Cslib.Probability.PMF.uniformOfFintype_map_equiv` 4 5: NOT jointly removable (α = γ = Empty)
theorem ume45 : ¬ indep2_0% Cslib.Probability.PMF.uniformOfFintype_map_equiv 4 5 := fun h =>
  (@h Empty Empty _ _ (Equiv.refl _)).1.elim fun x => x.elim

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env` 7 8: NOT jointly removable (Γ binds 0 twice,
-- first as a subtype bound, Δ swaps the two bindings, so fvar 0 is well-formed in Γ but not in Δ)
theorem pe78 : ¬ drop2_0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env 7 8 := fun h => by
  open Cslib.LambdaCalculus.LocallyNameless.Fsub in
  have := @h ℕ _ [⟨0, .sub .top⟩, ⟨0, .ty .top⟩] [⟨0, .ty .top⟩, ⟨0, .sub .top⟩] (.fvar 0)
    (.var (σ := .top) rfl) (List.Perm.swap _ _ _)
  cases this with
  | var h => cases h

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp` 8 9: jointly removable (if the
-- term is LC, both premises follow; otherwise it has no step and is SN)
theorem sn89 : drop2% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp 8 9 := by
  open Cslib.LambdaCalculus.LocallyNameless.Untyped Term in
  intro Var _ _ Ps M N sN sMN
  by_cases hT : ((M.abs.app N).multiApp Ps).LC
  · obtain ⟨h1, h2⟩ := multiApp_lc.mp hT
    cases h1 with
    | app hM hN => exact sn_abs_app_multiApp sN sMN hN (multiApp_lc.mpr ⟨beta_lc hM hN, h2⟩)
  · exact Acc.intro _ (fun y hy => absurd (FullBeta.step_lc_l hy) hT)

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst` 9 10: jointly removable (both from hN)
theorem sas910 : drop2% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst 9 10 := by
  intro Var M M' N N' _ _ h_abs hN
  exact Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst h_abs hN hN.lc_l hN.lc_r

-- `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst` 10 11: jointly removable (both from hN)
theorem ss1011 : drop2% Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst 10 11 := by
  intro Var M M' N N' _ _ hM hN x
  exact Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst hM hN x hN.lc_l hN.lc_r

-- `Cslib.MachineLearning.PACLearning.hypothesisError_eq_add` 5 6: NOT jointly removable (Bool with only ∅ and
-- univ measurable, P = dirac true, h = {true}, c = {false}: every nonempty set has measure 1, so 1 = 1 + 1)
theorem hea56 : ¬ drop2_0% Cslib.MachineLearning.PACLearning.hypothesisError_eq_add 5 6 := fun h => by
  have hbot : ∀ t : Set Bool, @MeasurableSet Bool ⊥ t → t = ∅ ∨ t = Set.univ :=
    fun t ht => MeasurableSpace.measurableSet_bot_iff.mp ht
  have := @h Bool ⊥ (@MeasureTheory.Measure.dirac Bool ⊥ true) {true} {false}
  simp only [MachineLearning.PACLearning.hypothesisError, MachineLearning.PACLearning.falsePositiveError,
    MachineLearning.PACLearning.falseNegativeError] at this
  have e : ∀ s : Set Bool, s.Nonempty → (@MeasureTheory.Measure.dirac Bool ⊥ true) s = 1 := fun s hs => by
    rw [@bot_nonempty Bool ⊥ _ hbot s hs,
      @MeasureTheory.Measure.dirac_apply_of_mem Bool ⊥ _ _ (Set.mem_univ true)]
  rw [e _ ⟨true, by simp [symmDiff_def]⟩, e _ ⟨true, by simp⟩, e _ ⟨false, by simp⟩] at this
  norm_num at this
end J1c0
