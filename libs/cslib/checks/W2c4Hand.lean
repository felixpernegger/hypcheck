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
namespace W2c4
noncomputable def tmU : Turing.MultiTapeTM 0 Bool Unit :=
  Turing.MultiTapeTM.ofTr () (fun _ _ _ => ⟨0, fun i => i.elim0, none, none⟩)
-- one work tape; writes, moves every head right, outputs `true`, halts
noncomputable def tm1 : Turing.MultiTapeTM 1 Bool Unit :=
  Turing.MultiTapeTM.ofTr () (fun _ _ _ => ⟨1, fun _ => (some (some true), 1), some true, none⟩)
def cfgH1 : Turing.Cfg 1 Bool Unit [] := ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
def lnn : Language ℕ := {w | ∃ n, w = [n, n]}
theorem nonreg_of (l : Language ℕ) (h1 : ∀ i, [i, i] ∈ l) (h2 : ∀ i j, [j, i] ∈ l → j = i) :
    ¬ l.IsRegular := fun h => by
  have := Language.IsRegular.finite_myhillQuotient h
  refine not_injective_infinite_finite
    (fun i : ℕ => Quotient.mk (l.MyhillCongruence.eq) [i]) ?_
  intro i j hij
  exact (h2 i j ((Quotient.exact hij [] [i]).1 (h1 i))).symm
theorem lnn_nonreg : ¬ lnn.IsRegular :=
  nonreg_of _ (fun i => ⟨i, rfl⟩) (fun i j ⟨n, h⟩ => by simp at h; omega)
-- parity vector of a word over ℕ
def g2 : FreeMonoid ℕ →* Multiplicative (ℕ → ZMod 2) :=
  FreeMonoid.lift fun i => Multiplicative.ofAdd (Pi.single i 1)
theorem g2_nonreg : ¬ Language.IsRegular ((⇑g2 ∘ FreeMonoid.ofList) ⁻¹' {1} : Language ℕ) := by
  refine nonreg_of _ (fun i => ?_) (fun i j h => ?_)
  · simp only [g2, Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff,
      FreeMonoid.ofList_cons, FreeMonoid.ofList_nil, map_mul, FreeMonoid.lift_eval_of, map_one, mul_one]
    funext x
    change (((Pi.single i 1 : ℕ → ZMod 2) + Pi.single i 1 : ℕ → ZMod 2)) x = (0 : ℕ → ZMod 2) x
    by_cases hx : x = i
    · subst hx; simp; decide
    · simp [hx]
  · by_contra hne
    simp only [g2, Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff,
      FreeMonoid.ofList_cons, FreeMonoid.ofList_nil, map_mul, FreeMonoid.lift_eval_of, map_one,
      mul_one] at h
    have := congrFun h i
    change (((Pi.single j 1 : ℕ → ZMod 2) + Pi.single i 1 : ℕ → ZMod 2)) i = (0 : ℕ → ZMod 2) i at this
    simp [Ne.symm hne] at this
end W2c4
namespace W2c4
open Turing
def ntmH0 : Turing.MultiTapeNTM 0 Bool Unit := ⟨(), fun _ _ _ _ => False⟩
def ntmH1 : Turing.MultiTapeNTM 1 Bool Unit := ⟨(), fun _ _ _ _ => False⟩
def cfgH0 : Turing.Cfg 0 Bool Unit [] := ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
def encU : Unit ↪ List Bool := ⟨fun _ => [], fun _ _ _ => rfl⟩
abbrev nop1 : Turing.MultiTapeTM 1 Bool Unit := Turing.MultiTapeTM.nop 1 Bool

-- tmU halts after one step from its initial configuration
theorem tmU_halt1 : (tmU.runFrom (tmU.initCfg [])  1).state = none := by
  rw [Turing.MultiTapeTM.runFrom, Function.iterate_one,
    Turing.MultiTapeTM.step_of_state (q := ()) rfl]
  simp [tmU, Turing.Action.apply]
-- no deterministic machine runs in time 0
theorem noRT0 {k : ℕ} {State : Type} {tm : Turing.MultiTapeTM k Bool State} {input : List Bool}
    (h : tm.RunsInTime input 0) : False := by
  have := h (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tm input 0) (Nat.zero_le _)
  change (tm.initCfg input).state = none at this
  simp at this
-- a run path between a running and a halted words configuration takes a step
theorem tp {k : ℕ} {State : Type} {tm : Turing.MultiTapeTM k Bool State} {input : List Bool}
    (p : tm.RunPath input) {q : State} {ws ws' : Fin k → List Bool} {out out' : List Bool}
    (hh : p.head = Turing.wordsCfg input (some q) ws out)
    (hl : p.last = Turing.wordsCfg input none ws' out') : 0 < p.time := by
  rcases Nat.eq_zero_or_pos p.time with h0 | h0
  · have e : p.last = Turing.MultiTapeTM.runFrom p.head p.length :=
      Turing.MultiTapeTM.runPath_apply_eq_runFrom p (Fin.last _)
    change p.length = 0 at h0
    rw [h0, hh, hl] at e
    exact absurd (congrArg (·.state) e) (by simp [Turing.MultiTapeTM.runFrom, Turing.wordsCfg])
  · exact h0
-- a run path with one work tape visits a cell
theorem rpS {State : Type} {ntm : Turing.MultiTapeNTM 1 Bool State} {input : List Bool}
    (p : ntm.RunPath input) : 0 < p.space := by
  simp [Turing.MultiTapeNTM.RunPath.space, Turing.MultiTapeNTM.RunPath.spaceUsedByTape,
    Turing.MultiTapeNTM.RunPath.visitedByTapeHead]
theorem noT0 {k : ℕ} {State : Type} {tm : Turing.MultiTapeTM k Bool State} {P Q} {s : ℕ}
    (hP : P [] (fun _ => [])) (H : tm.TransformsTapes P Q 0 s) : False := by
  obtain ⟨_, _, _, p, hh, hl, ht, _⟩ := H [] (fun _ => []) [] hP
  have := tp p hh hl
  omega
theorem noS0 {State : Type} {tm : Turing.MultiTapeTM 1 Bool State} {P Q} {t : ℕ}
    (hP : P [] (fun _ => [])) (H : tm.TransformsTapes P Q t 0) : False := by
  obtain ⟨_, _, _, p, -, -, -, hs⟩ := H [] (fun _ => []) [] hP
  have := rpS p
  omega
theorem noQ {k : ℕ} {State : Type} {tm : Turing.MultiTapeTM k Bool State} {P} {t s : ℕ}
    (hP : P [] (fun _ => [])) (H : tm.TransformsTapes P (fun _ _ _ _ => False) t s) : False := by
  obtain ⟨_, _, h, -⟩ := H [] (fun _ => []) [] hP
  exact h
theorem nopTT : nop1.TransformsTapes (fun _ _ => True)
    (fun _ ws ws' emitted => ws' = ws ∧ emitted = []) 1 1 :=
  Turing.MultiTapeTM.transformsTapes_nop 1 Bool
theorem nopTidy : nop1.ComputesTidilyInTimeAndSpace [] [] 1 1 :=
  nopTT.imp (fun _ _ _ => trivial) (fun _ _ _ _ ⟨_, hws⟩ ⟨h1, h2⟩ => ⟨h1.trans hws, h2⟩) le_rfl le_rfl
-- nop never moves the work head
theorem nopPos {input : List Bool} (c : Turing.Cfg 1 Bool Unit input) (n : ℕ) :
    (nop1.runFrom c n).workTapePos 0 = c.workTapePos 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply', ← Turing.MultiTapeTM.runFrom]
    rcases hq : (nop1.runFrom c n).state with _ | q
    · rw [Turing.MultiTapeTM.step_of_halt hq, ih]
    · rw [Turing.MultiTapeTM.step_workTapePos_of_state hq, ih]
      simp [Turing.MultiTapeTM.nop]
theorem nopSpace (input : List Bool) : nop1.RunsInSpace input 1 := fun q => by
  refine (Turing.MultiTapeNTM.RunPath.space_le_sum_card q.toRunPath (S := fun _ => {0}) ?_).trans
    (by simp)
  rintro c ⟨i, rfl⟩ j
  rw [Subsingleton.elim j 0]
  change (q.toRunPath i).workTapePos 0 ∈ ({0} : Finset ℤ)
  rw [Turing.MultiTapeTM.runPath_apply_eq_runFrom, nopPos, q.head_eq]
  simp
theorem nopComp : nop1.ComputesInTimeAndSpace [] [] 1 1 := by
  have h1 : nop1.runFrom (nop1.initCfg []) 1 = ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩ := by
    rw [Turing.MultiTapeTM.runFrom, Function.iterate_one,
      Turing.MultiTapeTM.step_of_state (q := ()) rfl]
    ext <;> simp [Turing.MultiTapeTM.nop, Turing.Action.apply, SignType.cast]
  refine ⟨⟨1, by rw [h1], by rw [h1]⟩, Turing.MultiTapeTM.runsInTime_of_halted (by rw [h1]), nopSpace _⟩
end W2c4
namespace W2c4
def cfgH1' : Turing.Cfg 1 Bool Unit [] := ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
-- one work tape; moves the work head right forever
noncomputable def tmR : Turing.MultiTapeTM 1 Bool Unit :=
  Turing.MultiTapeTM.ofTr () (fun _ _ _ => ⟨0, fun _ => (none, 1), none, some ()⟩)
theorem tmR_run {input : List Bool} (c : Turing.Cfg 1 Bool Unit input) (hc : c.state = some ())
    (n : ℕ) : (tmR.runFrom c n).state = some () ∧
      (tmR.runFrom c n).workTapePos 0 = c.workTapePos 0 + n := by
  induction n with
  | zero => exact ⟨hc, by simp [Turing.MultiTapeTM.runFrom]⟩
  | succ n ih =>
    rw [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply', ← Turing.MultiTapeTM.runFrom]
    refine ⟨?_, ?_⟩
    · rw [Turing.MultiTapeTM.step_of_state ih.1]; simp [tmR, Turing.Action.apply]
    · rw [Turing.MultiTapeTM.step_workTapePos_of_state ih.1, ih.2]; simp [tmR]; ring
theorem tmR_sut {input : List Bool} (c : Turing.Cfg 1 Bool Unit input) (hc : c.state = some ())
    (n : ℕ) : (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR c n).spaceUsedByTape 0 = n + 1 := by
  simp only [Turing.MultiTapeNTM.RunPath.spaceUsedByTape,
    Turing.MultiTapeNTM.RunPath.visitedByTapeHead]
  rw [Finset.card_image_of_injective _ ?_]
  · simp; rfl
  · intro i j hij
    have hi := (tmR_run c hc i).2
    have hj := (tmR_run c hc j).2
    change (tmR.runFrom c i).workTapePos 0 = (tmR.runFrom c j).workTapePos 0 at hij
    rw [hi, hj] at hij
    exact Fin.ext (by omega)
theorem tmR_space {input : List Bool} (c : Turing.Cfg 1 Bool Unit input) (hc : c.state = some ())
    (n : ℕ) : (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR c n).space = n + 1 := by
  rw [Turing.MultiTapeNTM.RunPath.space, Fin.sum_univ_one, tmR_sut c hc]
-- shift the work head of a configuration by one: a step homomorphism of the machine with no steps
def shiftH : (ntmH1.stepRel []).Hom (ntmH1.stepRel []) :=
  ⟨fun c => ⟨c.state, c.inputPos, c.workTapes, fun _ => c.workTapePos 0 + 1, c.output⟩,
   fun {c c'} h => by
    change ntmH1.Step c c' at h
    change ntmH1.Step _ _
    by_cases hc : c.state = none
    · have : c' = c := (Turing.MultiTapeNTM.step_of_halt hc).mp h
      subst this
      refine (Turing.MultiTapeNTM.step_of_halt ?_).mpr rfl
      exact hc
    · obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
      simp [Turing.MultiTapeNTM.Step, hq, ntmH1] at h⟩
-- singleton paths at work position 0 stay in the window of size 0
theorem iwS (c : Turing.Cfg 1 Bool Unit []) (hc : c.workTapePos 0 = 0) :
    Turing.MultiTapeNTM.RunPath.InWindow (RelSeries.singleton (ntmH1.stepRel []) c) 0 := by
  rintro x ⟨j, rfl⟩ i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  change c.workTapePos 0 ∈ _
  simp [hc, Turing.window]
def ntmT : Turing.MultiTapeNTM 0 Bool Unit := ⟨(), fun _ i _ _ => i = some true⟩
def stay : Turing.Action 0 Bool Unit := ⟨0, fun i => i.elim0, none, some ()⟩
end W2c4
namespace W2c4
-- tmR's storages along its run are pairwise distinct
theorem tmR_inj : Function.Injective fun n : ℕ =>
    (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tmR [] n).last.storage := by
  intro i j hij
  have := congrFun (congrArg Turing.Storage.workTapePos hij) 0
  change (tmR.runFrom (tmR.initCfg []) i).workTapePos 0 = (tmR.runFrom (tmR.initCfg []) j).workTapePos 0 at this
  rw [(tmR_run _ rfl i).2, (tmR_run _ rfl j).2] at this
  simpa using this
-- no tapes; counts its states up forever
noncomputable def tmC : Turing.MultiTapeTM 0 Bool ℕ :=
  Turing.MultiTapeTM.ofTr 0 (fun q _ _ => ⟨0, fun i => i.elim0, none, some (q + 1)⟩)
theorem tmC_run (n : ℕ) : (tmC.runFrom (tmC.initCfg []) n).state = some n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply', ← Turing.MultiTapeTM.runFrom,
      Turing.MultiTapeTM.step_of_state ih]
    simp [tmC, Turing.Action.apply]
theorem tmC_inj : Function.Injective fun n : ℕ =>
    (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tmC [] n).last.storage := by
  intro i j hij
  have := congrArg Turing.Storage.state hij
  change (tmC.runFrom (tmC.initCfg []) i).state = (tmC.runFrom (tmC.initCfg []) j).state at this
  rw [tmC_run, tmC_run] at this
  simpa using this
-- one tape over ℕ; never moves, increments the symbol under its head forever
noncomputable def tmW : Turing.MultiTapeTM 1 ℕ Unit :=
  Turing.MultiTapeTM.ofTr () (fun _ _ w => ⟨0, fun _ => (some (some ((w 0).elim 0 Nat.succ)), 0),
    none, some ()⟩)
def cellW : ℕ → Option ℕ
  | 0 => none
  | n + 1 => some n
theorem tmW_run (n : ℕ) : (tmW.runFrom (tmW.initCfg []) n).state = some () ∧
    (tmW.runFrom (tmW.initCfg []) n).workTapePos 0 = 0 ∧
    (tmW.runFrom (tmW.initCfg []) n).workTapes 0 0 = cellW n := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    rw [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply', ← Turing.MultiTapeTM.runFrom,
      Turing.MultiTapeTM.step_of_state ih.1]
    obtain ⟨h1, h2, h3⟩ := ih
    generalize tmW.runFrom (tmW.initCfg []) n = c at *
    refine ⟨by simp [tmW, Turing.Action.apply], ?_, ?_⟩
    · simp [tmW, Turing.Action.apply, h2]
    · simp [tmW, Turing.Action.apply, h2, Turing.Cfg.workTapeSymbols, h3, cellW]
      cases n <;> rfl
theorem tmW_inj : Function.Injective fun n : ℕ =>
    (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tmW [] n).last.storage := by
  intro i j hij
  have := congrFun (congrFun (congrArg Turing.Storage.workTapes hij) 0) 0
  change (tmW.runFrom (tmW.initCfg []) i).workTapes 0 0 =
    (tmW.runFrom (tmW.initCfg []) j).workTapes 0 0 at this
  rw [(tmW_run i).2.2, (tmW_run j).2.2] at this
  cases i <;> cases j <;> simp_all [cellW]
theorem tmW_space : tmW.RunsInSpace [] 1 := fun q => by
  refine (Turing.MultiTapeNTM.RunPath.space_le_sum_card q.toRunPath (S := fun _ => {0}) ?_).trans
    (by simp)
  rintro c ⟨i, rfl⟩ j
  rw [Subsingleton.elim j 0]
  change (q.toRunPath i).workTapePos 0 ∈ ({0} : Finset ℤ)
  rw [Turing.MultiTapeTM.runPath_apply_eq_runFrom, q.head_eq, (tmW_run _).2.1]
  simp
-- an infinite range of storages / cores
theorem infSt {k : ℕ} {Sy St : Type} {tm : Turing.MultiTapeTM k Sy St}
    (hi : Function.Injective fun n : ℕ =>
      (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tm [] n).last.storage) :
    (Set.range fun p : tm.ComputationPath [] => p.last.storage).encard = ⊤ :=
  (Set.infinite_of_injective_forall_mem hi
    (fun n => Set.mem_range_self (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tm [] n))).encard_eq
theorem infCo {k : ℕ} {Sy St : Type} {tm : Turing.MultiTapeTM k Sy St}
    (hi : Function.Injective fun n : ℕ =>
      (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tm [] n).last.storage) :
    (Set.range fun p : tm.ComputationPath [] => p.last.core).encard = ⊤ :=
  (Set.infinite_of_injective_forall_mem (f := fun n : ℕ =>
      (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tm [] n).last.core)
    (fun i j h => hi (congrArg Prod.snd h))
    (fun n => Set.mem_range_self (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tm [] n))).encard_eq
end W2c4
namespace W2c4
open Turing Turing.MultiTapeTM
def encR : ℕ ↪ List Bool := ⟨fun n => List.replicate n true, fun a b h => by
  simpa using congrArg List.length h⟩
-- a machine appends at most one output symbol per step
theorem outLen {k : ℕ} {Sy St : Type} (tm : Turing.MultiTapeTM k Sy St) {input : List Sy}
    (c : Turing.Cfg k Sy St input) (u : ℕ) :
    (tm.runFrom c u).output.length ≤ c.output.length + u := by
  induction u with
  | zero => simp [Turing.MultiTapeTM.runFrom]
  | succ u ih =>
    rw [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply', ← Turing.MultiTapeTM.runFrom]
    rcases hq : (tm.runFrom c u).state with _ | q
    · rw [Turing.MultiTapeTM.step_of_halt hq]; omega
    · rw [Turing.MultiTapeTM.step_of_state hq]
      simp only [Turing.Action.apply_output, List.length_append]
      generalize (tm.tr q _ _).output = o
      cases o <;> simp <;> omega
-- the output of a computation within time t has length at most t
theorem outBound {k : ℕ} {St : Type} {tm : Turing.MultiTapeTM k Bool St} {input output : List Bool}
    {t s : ℕ} (h : tm.ComputesInTimeAndSpace input output t s) : output.length ≤ t := by
  obtain ⟨⟨u, hu, ho⟩, ht, -⟩ := h
  have hT : (tm.runFrom (tm.initCfg input) t).Halted :=
    ht (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tm input t) le_rfl
  rcases le_total u t with hut | htu
  · have := outLen tm (tm.initCfg input) u
    rw [ho] at this; simp at this; omega
  · rw [Turing.MultiTapeTM.runFrom_eq_of_halt tm _ htu hT] at ho
    have := outLen tm (tm.initCfg input) t
    rw [ho] at this; simp at this; omega
-- the identity on ℕ (unary) is not computable in constant time
theorem noConst (c : ℕ) : ¬ Turing.MultiTapeTM.ComputableInTimeAndSpace (id : ℕ → ℕ) encR encR
    (fun _ => c) (fun _ => 0) := fun ⟨k, S, _, tm, htm⟩ => by
  have := outBound (htm (c + 1))
  change (List.replicate (c + 1) true).length ≤ c at this
  simp at this
-- steps of the rewinding machine
theorem rws_start {Sy : Type*} {input : List Sy} {write : Option (Option Sy)}
    {ip : Fin (input.length + 2)} {t : ℤ → Option Sy} {out : List Sy} {p : ℤ} :
    (rewindWork Sy write).step ⟨some (rewindWork Sy write).q₀, ip, fun _ => t, fun _ => p, out⟩ =
      ⟨some .scan, ip, fun _ => t, fun _ => p - 1, out⟩ := by
  rw [step_of_state rfl]
  simp [rewindWork, Action.apply, sub_eq_add_neg]
theorem rws_some {Sy : Type*} {input : List Sy} {write : Option (Option Sy)}
    {ip : Fin (input.length + 2)} {t : ℤ → Option Sy} {out : List Sy} {p : ℤ} {s : Sy}
    (hs : t p = some s) :
    (rewindWork Sy write).step ⟨some .scan, ip, fun _ => t, fun _ => p, out⟩ =
      ⟨some .scan, ip, fun _ => write.elim t (Function.update t p), fun _ => p - 1, out⟩ := by
  rw [step_of_state rfl]
  cases write <;> simp [rewindWork, Action.apply, Cfg.workTapeSymbols, hs, sub_eq_add_neg]
theorem rws_none {Sy : Type*} {input : List Sy} {write : Option (Option Sy)}
    {ip : Fin (input.length + 2)} {t : ℤ → Option Sy} {out : List Sy} {p : ℤ}
    (hs : t p = none) :
    (rewindWork Sy write).step ⟨some .scan, ip, fun _ => t, fun _ => p, out⟩ =
      ⟨none, ip, fun _ => t, fun _ => p + 1, out⟩ := by
  rw [step_of_state rfl]
  simp [rewindWork, Action.apply, Cfg.workTapeSymbols, hs]
end W2c4

namespace W2c4
-- one tape; never moves, outputs `true` forever
noncomputable def tmO : Turing.MultiTapeTM 1 Bool Unit :=
  Turing.MultiTapeTM.ofTr () (fun _ _ _ => ⟨0, fun _ => (none, 0), some true, some ()⟩)
theorem tmO_run (n : ℕ) : (tmO.runFrom (tmO.initCfg []) n).state = some () ∧
    (tmO.runFrom (tmO.initCfg []) n).workTapePos 0 = 0 ∧
    (tmO.runFrom (tmO.initCfg []) n).output.length = n := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    rw [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply', ← Turing.MultiTapeTM.runFrom,
      Turing.MultiTapeTM.step_of_state ih.1]
    obtain ⟨h1, h2, h3⟩ := ih
    generalize tmO.runFrom (tmO.initCfg []) n = c at *
    refine ⟨by simp [tmO, Turing.Action.apply], by simp [tmO, Turing.Action.apply, h2], ?_⟩
    simp [tmO, Turing.Action.apply, h3]
-- the output length of tmO becomes the head position of tmR
def oToR (c : Turing.Cfg 1 Bool Unit []) : Turing.Cfg 1 Bool Unit [] :=
  ⟨c.state, c.inputPos, c.workTapes, fun _ => c.output.length, []⟩
def homOR : (tmO.stepRel []).Hom (tmR.stepRel []) :=
  ⟨oToR, fun {c c'} h => by
    change tmO.Step c c' at h
    change tmR.Step (oToR c) (oToR c')
    rw [Turing.MultiTapeTM.step_iff] at h ⊢
    subst h
    rcases hc : c.state with _ | q
    · rw [Turing.MultiTapeTM.step_of_halt hc,
        Turing.MultiTapeTM.step_of_halt (show (oToR c).state = none from hc)]
    · rw [Turing.MultiTapeTM.step_of_state (show (oToR c).state = some q from hc),
        Turing.MultiTapeTM.step_of_state hc]
      ext <;> simp [tmO, tmR, oToR, Turing.Action.apply]⟩
end W2c4

open W2c4

-- `Turing.MultiTapeNTM.RunPath.space_map_le` 13
theorem sml13 : ¬ drop0% Turing.MultiTapeNTM.RunPath.space_map_le 13 := fun h => by
  have H := @h 1 1 Unit Unit Bool [] [] tmO.toMultiTapeNTM tmR.toMultiTapeNTM
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmO (tmO.initCfg []) 1) homOR
    (Function.Embedding.refl _) (fun _ => ∅) (fun _ _ l hl => absurd ⟨l, rfl⟩ hl)
  have hp : (Turing.MultiTapeNTM.RunPath.ofDeterministic tmO (tmO.initCfg []) 1).space ≤ 1 := by
    refine (Turing.MultiTapeNTM.RunPath.space_le_sum_card _ (S := fun _ => {0}) ?_).trans (by simp)
    rintro c ⟨i, rfl⟩ j
    rw [Subsingleton.elim j 0]
    change (tmO.runFrom (tmO.initCfg []) i).workTapePos 0 ∈ ({0} : Finset ℤ)
    rw [(tmO_run _).2.1]
    simp
  have hm : ((Turing.MultiTapeNTM.RunPath.ofDeterministic tmO (tmO.initCfg []) 1).map homOR).space
      = 2 := by
    simp only [Turing.MultiTapeNTM.RunPath.space, Fin.sum_univ_one,
      Turing.MultiTapeNTM.RunPath.spaceUsedByTape, Turing.MultiTapeNTM.RunPath.visitedByTapeHead]
    rw [Finset.card_image_of_injective _ ?_]
    · simp; rfl
    · intro i j hij
      change ((tmO.runFrom (tmO.initCfg []) i).output.length : ℤ) =
        (tmO.runFrom (tmO.initCfg []) j).output.length at hij
      rw [(tmO_run _).2.2, (tmO_run _).2.2] at hij
      exact Fin.ext (by omega)
  rw [hm] at H
  simp only [Finset.card_empty, Finset.sum_const_zero, add_zero] at H
  omega


-- `Language.IsRegular.exists_finite_monoid` 2: necessary (l = {[n,n]} is not regular)
theorem efm2 : ¬ drop0% Language.IsRegular.exists_finite_monoid 2 := fun h => by
  obtain ⟨M, hM, hF, f, s, hs⟩ := @h ℕ lnn
  exact lnn_nonreg (hs ▸ @Language.IsRegular.of_finite_monoid ℕ M hM f hF s)

-- `Language.instFiniteQuotientListInducedCongr` 4: necessary (M = FreeMonoid Unit)
theorem ifq4 : ¬ drop0% Language.instFiniteQuotientListInducedCongr 4 := fun h => by
  have := @h Unit (FreeMonoid Unit) _ (MonoidHom.id _)
  refine not_injective_infinite_finite
    (fun n : ℕ => Quotient.mk (Language.inducedCongr (MonoidHom.id (FreeMonoid Unit))).eq
      (List.replicate n ())) ?_
  intro i j hij
  have := Quotient.exact hij
  simpa using congrArg (fun w : FreeMonoid Unit => w.toList.length) this

-- `Language.IsRegular.of_finite_monoid_singleton` 4: necessary (parity vectors in ℕ → ZMod 2)
theorem ofs4 : ¬ drop0% Language.IsRegular.of_finite_monoid_singleton 4 := fun h =>
  g2_nonreg (@h ℕ _ _ g2 1)

-- `Language.IsRegular.of_finite_monoid` 4: necessary (parity vectors in ℕ → ZMod 2)
theorem ofm4 : ¬ drop0% Language.IsRegular.of_finite_monoid 4 := fun h =>
  g2_nonreg (@h ℕ _ _ g2 {1})

-- `Turing.Cfg.ext` 6
theorem ce6 : ¬ drop0% Turing.Cfg.ext 6 := fun h => by
  have := @h 0 Bool Unit [] ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
    ⟨some (), 0, fun _ _ => none, fun _ => 0, []⟩ rfl rfl rfl rfl
  simpa using congrArg (·.state) this
-- `Turing.Cfg.ext` 7
theorem ce7 : ¬ drop0% Turing.Cfg.ext 7 := fun h => by
  have := @h 0 Bool Unit [] ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
    ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩ rfl rfl rfl rfl
  simpa using congrArg (·.inputPos) this
-- `Turing.Cfg.ext` 8
theorem ce8 : ¬ drop0% Turing.Cfg.ext 8 := fun h => by
  have := @h 1 Bool Unit [] ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
    ⟨none, 0, fun _ _ => some true, fun _ => 0, []⟩ rfl rfl rfl rfl
  simpa using congrFun (congrFun (congrArg (·.workTapes) this) 0) 0
-- `Turing.Cfg.ext` 9
theorem ce9 : ¬ drop0% Turing.Cfg.ext 9 := fun h => by
  have := @h 1 Bool Unit [] ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
    ⟨none, 0, fun _ _ => none, fun _ => 1, []⟩ rfl rfl rfl rfl
  simpa using congrFun (congrArg (·.workTapePos) this) 0
-- `Turing.Cfg.ext` 10
theorem ce10 : ¬ drop0% Turing.Cfg.ext 10 := fun h => by
  have := @h 0 Bool Unit [] ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
    ⟨none, 0, fun _ _ => none, fun _ => 0, [true]⟩ rfl rfl rfl rfl
  simpa using congrArg (·.output) this

-- `Turing.Cfg.ext_zero_tapes` 5
theorem cz5 : ¬ drop0% Turing.Cfg.ext_zero_tapes 5 := fun h => by
  have := @h Bool Unit [] ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
    ⟨some (), 0, fun _ _ => none, fun _ => 0, []⟩ rfl rfl
  simpa using congrArg (·.state) this
-- `Turing.Cfg.ext_zero_tapes` 6
theorem cz6 : ¬ drop0% Turing.Cfg.ext_zero_tapes 6 := fun h => by
  have := @h Bool Unit [] ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
    ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩ rfl rfl
  simpa using congrArg (·.inputPos) this
-- `Turing.Cfg.ext_zero_tapes` 7
theorem cz7 : ¬ drop0% Turing.Cfg.ext_zero_tapes 7 := fun h => by
  have := @h Bool Unit [] ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
    ⟨none, 0, fun _ _ => none, fun _ => 0, [true]⟩ rfl rfl
  simpa using congrArg (·.output) this

-- `Turing.inputSymbol_eq_none_of_boundary` 5
theorem isb5 : ¬ drop0% Turing.inputSymbol_eq_none_of_boundary 5 := fun h => by
  have := @h 0 Unit Bool [true] ⟨none, 1, fun i => i.elim0, fun i => i.elim0, []⟩
  simp [Turing.Cfg.inputSymbol] at this
-- `Turing.inputSymbolInner` 6
theorem isi6 : ¬ drop0% Turing.inputSymbolInner 6 := fun h => by
  have := @h 0 Unit Bool [true, false] ⟨none, 1, fun i => i.elim0, fun i => i.elim0, []⟩ 1 (by decide)
  simp [Turing.Cfg.inputSymbol] at this
-- `Turing.inputSymbolInner` 7 (dependent)
theorem isi7 : ¬ indep0% Turing.inputSymbolInner 7 := fun h => by
  have := @h 0 Unit Bool [] ⟨none, 1, fun i => i.elim0, fun i => i.elim0, []⟩ 0 rfl
  simp at this

-- `Turing.MultiTapeTM.step_of_state` 7
theorem sos7 : ¬ drop0% Turing.MultiTapeTM.step_of_state 7 := fun h => by
  have e := @h 1 Unit Bool tm1 [] cfgH1 ()
  rw [Turing.MultiTapeTM.step_of_halt rfl] at e
  have := congrArg (·.output) e
  simp [tm1, cfgH1, Turing.Action.apply] at this
-- `Turing.MultiTapeTM.step_inputPos_of_state` 7
theorem sip7 : ¬ drop0% Turing.MultiTapeTM.step_inputPos_of_state 7 := fun h => by
  have e := @h 1 Unit Bool tm1 [] cfgH1 ()
  rw [Turing.MultiTapeTM.step_of_halt rfl] at e
  simp [tm1, cfgH1, Turing.moveInputPos] at e
-- `Turing.MultiTapeTM.step_workTapes_of_state` 7
theorem swt7 : ¬ drop0% Turing.MultiTapeTM.step_workTapes_of_state 7 := fun h => by
  have e := @h 1 Unit Bool tm1 [] cfgH1 () 0
  rw [Turing.MultiTapeTM.step_of_halt rfl] at e
  have := congrFun e 0
  simp [tm1, cfgH1] at this
-- `Turing.MultiTapeTM.step_workTapePos_of_state` 7
theorem swp7 : ¬ drop0% Turing.MultiTapeTM.step_workTapePos_of_state 7 := fun h => by
  have e := @h 1 Unit Bool tm1 [] cfgH1 () 0
  rw [Turing.MultiTapeTM.step_of_halt rfl] at e
  simp [tm1, cfgH1] at e
-- `Turing.MultiTapeTM.step_of_halt` 6
theorem soh6 : ¬ drop0% Turing.MultiTapeTM.step_of_halt 6 := fun h => by
  have e := @h 1 Unit Bool tm1 [] (tm1.initCfg [])
  rw [Turing.MultiTapeTM.step_of_state (q := ()) rfl] at e
  have := congrArg (·.state) e
  simp [tm1, Turing.Action.apply] at this


-- `Turing.MultiTapeTM.runFrom_eq_of_halt` 9
theorem rfh9 : ¬ drop0% Turing.MultiTapeTM.runFrom_eq_of_halt 9 := fun h => by
  have := congrArg (·.state) (@h 0 Unit Bool [] tmU (tmU.initCfg []) 0 1 (Nat.zero_le 1))
  change (tmU.runFrom (tmU.initCfg []) 1).state = (tmU.initCfg []).state at this
  rw [tmU_halt1] at this
  cases this
-- `Turing.MultiTapeTM.runsInTime_of_halted` 6
theorem rih6 : ¬ drop0% Turing.MultiTapeTM.runsInTime_of_halted 6 := fun h =>
  noRT0 (@h 0 Unit Bool tmU [] 0)
-- `Turing.MultiTapeTM.not_halts_of_repeat_nonhalt` 6
theorem nhr6 : ¬ drop0% Turing.MultiTapeTM.not_halts_of_repeat_nonhalt 6 := fun h =>
  @h 0 Unit Bool tmU [] cfgH0 0
    ((tmU.runFrom_eq_of_halt cfgH0 (Nat.zero_le 1) rfl).trans rfl) 0 rfl
-- `Turing.MultiTapeTM.not_halts_of_repeat_nonhalt` 8
theorem nhr8 : ¬ drop0% Turing.MultiTapeTM.not_halts_of_repeat_nonhalt 8 := fun h =>
  @h 0 Unit Bool tmU [] (tmU.initCfg []) (by simp) 0 1 tmU_halt1
-- `RelSeries.exists_of_mem_map` 7
theorem eom7 : ¬ drop0% RelSeries.exists_of_mem_map 7 := fun h => by
  obtain ⟨a, ha, hb⟩ := @h Bool Bool Set.univ Set.univ (RelSeries.singleton _ false)
    ⟨id, fun h => h⟩ true
  obtain ⟨i, rfl⟩ := ha
  simp [RelSeries.singleton] at hb
-- `RelSeries.mem_or_mem_of_mem_smash` 4 (dependent)
theorem mms4 : ¬ indep0% RelSeries.mem_or_mem_of_mem_smash 4 := fun h => by
  have := @h Bool Set.univ (RelSeries.singleton _ false) (RelSeries.singleton _ true)
  simp at this
-- `RelSeries.mem_or_mem_of_mem_smash` 6
theorem mms6 : ¬ drop0% RelSeries.mem_or_mem_of_mem_smash 6 := fun h => by
  have := @h Bool Set.univ (RelSeries.singleton _ false) (RelSeries.singleton _ false) rfl true
  rcases this with ⟨i, hi⟩ | ⟨i, hi⟩ <;> simp [RelSeries.singleton] at hi
-- `Turing.MultiTapeNTM.step_of_halt` 7
theorem nsh7 : ¬ drop0% Turing.MultiTapeNTM.step_of_halt 7 := fun h => by
  have := (@h 0 Unit Bool [] ntmH0 (ntmH0.initCfg []) (ntmH0.initCfg [])).mpr rfl
  obtain ⟨_, h, _⟩ := this
  exact h
-- `Turing.MultiTapeNTM.RunPath.last_eq_of_head_halted` 6
theorem leh6 : ¬ drop0% Turing.MultiTapeNTM.RunPath.last_eq_of_head_halted 6 := fun h => by
  have := congrArg (·.state) (@h 0 Unit Bool [] tmU.toMultiTapeNTM
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmU (tmU.initCfg []) 1))
  change (tmU.runFrom (tmU.initCfg []) 1).state = (tmU.initCfg []).state at this
  rw [tmU_halt1] at this
  cases this
-- `Turing.MultiTapeNTM.RunPath.last_eq_of_halted` 7
theorem leh7 : ¬ drop0% Turing.MultiTapeNTM.RunPath.last_eq_of_halted 7 := fun h => by
  have := congrArg (·.state) (@h 0 Unit Bool [] tmU.toMultiTapeNTM
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmU (tmU.initCfg []) 1) 0)
  change (tmU.runFrom (tmU.initCfg []) 1).state = (tmU.initCfg []).state at this
  rw [tmU_halt1] at this
  cases this
-- `Turing.MultiTapeNTM.RunsInTime.mono` 7
theorem rtm7 : ¬ drop0% Turing.MultiTapeNTM.RunsInTime.mono 7 := fun h =>
  noRT0 (@h 0 Unit Bool tmU.toMultiTapeNTM [] 0 0 le_rfl)
-- `Turing.MultiTapeNTM.RunsInTime.mono` 8
theorem rtm8 : ¬ drop0% Turing.MultiTapeNTM.RunsInTime.mono 8 := fun h =>
  noRT0 (@h 0 Unit Bool tmU.toMultiTapeNTM [] 1 0
    (Turing.MultiTapeTM.runsInTime_of_halted tmU_halt1))
-- `Turing.MultiTapeNTM.RunPath.eq_take` 7
theorem et7 : ¬ drop0% Turing.MultiTapeNTM.RunPath.eq_take 7 := fun h => by
  have := congrArg (fun p => (RelSeries.head p).state) (@h 0 Unit Bool tmU []
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmU cfgH0 0)
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmU (tmU.initCfg []) 0) le_rfl)
  simp [RelSeries.head_take] at this
  cases this
-- `Turing.MultiTapeNTM.RunPath.eq_take` 8 (dependent)
theorem et8 : ¬ indep0% Turing.MultiTapeNTM.RunPath.eq_take 8 := fun h => by
  have := @h 0 Unit Bool tmU []
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmU (tmU.initCfg []) 1)
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmU (tmU.initCfg []) 0) rfl
  exact absurd this (by decide)

-- `Turing.MultiTapeTM.ComputesFunInTimeAndSpace.mono` 14
theorem cfm14 : ¬ drop0% Turing.MultiTapeTM.ComputesFunInTimeAndSpace.mono 14 := fun h =>
  noRT0 ((@h 1 Unit Bool nop1 Unit Unit encU encU id (fun _ => 1) (fun _ => 1) (fun _ => 0)
    (fun _ => 1) (fun _ => nopComp) (fun _ => le_rfl) ()).2.1)
-- `Turing.MultiTapeTM.ComputesFunInTimeAndSpace.mono` 15
theorem cfm15 : ¬ drop0% Turing.MultiTapeTM.ComputesFunInTimeAndSpace.mono 15 := fun h => by
  have h1 : (Turing.MultiTapeNTM.ComputationPath.ofDeterministic nop1 [] 0).space ≤ 0 :=
    (@h 1 Unit Bool nop1 Unit Unit encU encU id (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 0) (fun _ => nopComp) (fun _ => le_rfl) ()).2.2 _
  have h2 : 0 < (Turing.MultiTapeNTM.ComputationPath.ofDeterministic nop1 [] 0).space := rpS _
  omega
-- `Turing.MultiTapeTM.ComputableInTimeAndSpace.mono` 9
theorem cam9 : ¬ drop0% Turing.MultiTapeTM.ComputableInTimeAndSpace.mono 9 := fun h => by
  obtain ⟨k, S, _, tm, htm⟩ := @h Unit Unit id encU encU (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => le_rfl) (fun _ => le_rfl)
  exact noRT0 (htm ()).2.1
-- `Turing.MultiTapeTM.ComputableInTimeAndSpace.mono` 10
theorem cam10 : ¬ drop0% Turing.MultiTapeTM.ComputableInTimeAndSpace.mono 10 := fun h => by
  obtain ⟨c, hc⟩ := Turing.MultiTapeTM.computableInTimeAndSpace_of_finite (α := Unit) (encIn := encU) (encOut := encU) id
  obtain ⟨k, S, _, tm, htm⟩ := @h Unit Unit id encU encU (fun _ => c) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) hc (fun _ => le_rfl)
  exact noRT0 (htm ()).2.1

-- `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.mono` 10
theorem ctm10 : ¬ drop0% Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.mono 10 := fun h =>
  noT0 ⟨rfl, rfl⟩ (@h 1 Bool Unit nop1 0 0 [] [] 0 0 le_rfl le_rfl)
-- `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.mono` 11
theorem ctm11 : ¬ drop0% Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.mono 11 := fun h =>
  noT0 ⟨rfl, rfl⟩ (@h 1 Bool Unit nop1 1 1 [] [] 0 1 nopTidy le_rfl)
-- `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.mono` 12
theorem ctm12 : ¬ drop0% Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.mono 12 := fun h =>
  noS0 ⟨rfl, rfl⟩ (@h 1 Bool Unit nop1 1 1 [] [] 1 0 nopTidy le_rfl)
-- `Turing.MultiTapeTM.ComputesFunTidilyInTimeAndSpace.mono` 14
theorem cftm14 : ¬ drop0% Turing.MultiTapeTM.ComputesFunTidilyInTimeAndSpace.mono 14 := fun h =>
  noT0 ⟨rfl, rfl⟩ (@h 1 Bool Unit nop1 Unit Unit encU encU id (fun _ => 1) (fun _ => 1)
    (fun _ => 0) (fun _ => 1) (fun _ => nopTidy) (fun _ => le_rfl) ())
-- `Turing.MultiTapeTM.ComputesFunTidilyInTimeAndSpace.mono` 15
theorem cftm15 : ¬ drop0% Turing.MultiTapeTM.ComputesFunTidilyInTimeAndSpace.mono 15 := fun h =>
  noS0 ⟨rfl, rfl⟩ (@h 1 Bool Unit nop1 Unit Unit encU encU id (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => 0) (fun _ => nopTidy) (fun _ => le_rfl) ())
-- `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.mono` 9
theorem catm9 : ¬ drop0% Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.mono 9 := fun h => by
  obtain ⟨k, S, _, tm, htm⟩ := @h Unit Unit id encU encU (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => le_rfl) (fun _ => le_rfl)
  exact noT0 ⟨rfl, rfl⟩ (htm ())
-- `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.mono` 10
theorem catm10 : ¬ drop0% Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.mono 10 := fun h => by
  obtain ⟨k, S, _, tm, htm⟩ := @h Unit Unit id encU encU (fun _ => 1) (fun _ => 1) (fun _ => 0)
    (fun _ => 1) ⟨1, Unit, inferInstance, nop1, fun _ => nopTidy⟩ (fun _ => le_rfl)
  exact noT0 ⟨rfl, rfl⟩ (htm ())

-- `Turing.MultiTapeTM.TransformsTapes.imp` 12
theorem tti12 : ¬ drop0% Turing.MultiTapeTM.TransformsTapes.imp 12 := fun h =>
  noQ (P := fun _ _ => True) trivial (@h 1 Bool Unit nop1 (fun _ _ => True) (fun _ _ => True)
    (fun _ _ _ _ => False) (fun _ _ _ _ => False) 0 0 0 0 (fun _ _ h => h) (fun _ _ _ _ _ h => h)
    le_rfl le_rfl)
-- `Turing.MultiTapeTM.TransformsTapes.imp` 13
theorem tti13 : ¬ drop0% Turing.MultiTapeTM.TransformsTapes.imp 13 := fun h =>
  noQ (P := fun _ _ => True) trivial (@h 1 Bool Unit nop1 (fun _ _ => False) (fun _ _ => True)
    (fun _ _ _ _ => False) (fun _ _ _ _ => False) 0 0 0 0 (fun _ _ _ h => h.elim)
    (fun _ _ _ _ _ h => h) le_rfl le_rfl)
-- `Turing.MultiTapeTM.TransformsTapes.imp` 14
theorem tti14 : ¬ drop0% Turing.MultiTapeTM.TransformsTapes.imp 14 := fun h =>
  noQ (P := fun _ _ => True) trivial (@h 1 Bool Unit nop1 (fun _ _ => True) (fun _ _ => True)
    _ (fun _ _ _ _ => False) 1 1 1 1 nopTT (fun _ _ h => h) le_rfl le_rfl)
-- `Turing.MultiTapeTM.TransformsTapes.imp` 15
theorem tti15 : ¬ drop0% Turing.MultiTapeTM.TransformsTapes.imp 15 := fun h =>
  noT0 (P := fun _ _ => True) trivial (@h 1 Bool Unit nop1 (fun _ _ => True) (fun _ _ => True)
    _ _ 1 1 0 1 nopTT (fun _ _ h => h) (fun _ _ _ _ _ h => h) le_rfl)
-- `Turing.MultiTapeTM.TransformsTapes.imp` 16
theorem tti16 : ¬ drop0% Turing.MultiTapeTM.TransformsTapes.imp 16 := fun h =>
  noS0 (P := fun _ _ => True) trivial (@h 1 Bool Unit nop1 (fun _ _ => True) (fun _ _ => True)
    _ _ 1 1 1 0 nopTT (fun _ _ h => h) (fun _ _ _ _ _ h => h) le_rfl)
-- `Turing.MultiTapeTM.TransformsTapes.mono` 10
theorem ttm10 : ¬ drop0% Turing.MultiTapeTM.TransformsTapes.mono 10 := fun h =>
  noQ (P := fun _ _ => True) trivial (@h 1 Bool Unit nop1 (fun _ _ => True)
    (fun _ _ _ _ => False) 0 0 0 0 le_rfl le_rfl)
-- `Turing.MultiTapeTM.TransformsTapes.mono` 11
theorem ttm11 : ¬ drop0% Turing.MultiTapeTM.TransformsTapes.mono 11 := fun h =>
  noT0 (P := fun _ _ => True) trivial (@h 1 Bool Unit nop1 _ _ 1 1 0 1 nopTT le_rfl)
-- `Turing.MultiTapeTM.TransformsTapes.mono` 12
theorem ttm12 : ¬ drop0% Turing.MultiTapeTM.TransformsTapes.mono 12 := fun h =>
  noS0 (P := fun _ _ => True) trivial (@h 1 Bool Unit nop1 _ _ 1 1 1 0 nopTT le_rfl)

-- `Turing.MultiTapeNTM.RunsInSpace.mono` 7
theorem rsm7 : ¬ drop0% Turing.MultiTapeNTM.RunsInSpace.mono 7 := fun h => by
  exact absurd (@h 1 Unit Bool [] ntmH1 0 0 le_rfl ⟨.singleton _ (ntmH1.initCfg []), rfl⟩)
    (not_le.mpr (rpS _))
-- `Turing.MultiTapeNTM.RunsInSpace.mono` 8
theorem rsm8 : ¬ drop0% Turing.MultiTapeNTM.RunsInSpace.mono 8 := fun h => by
  exact absurd (@h 1 Unit Bool [] nop1.toMultiTapeNTM 1 0 (nopSpace [])
    ⟨.singleton _ (nop1.initCfg []), rfl⟩) (not_le.mpr (rpS _))
-- `Turing.MultiTapeNTM.RunPath.spaceUsedByTape_le_card` 8
theorem sul8 : ¬ drop0% Turing.MultiTapeNTM.RunPath.spaceUsedByTape_le_card 8 := fun h => by
  have := @h 1 Unit Bool [] ntmH1 (.singleton _ (ntmH1.initCfg [])) 0 ∅
  simp [Turing.MultiTapeNTM.RunPath.spaceUsedByTape, Turing.MultiTapeNTM.RunPath.visitedByTapeHead] at this
  exact Finset.univ_nonempty.ne_empty this
-- `Turing.MultiTapeNTM.RunPath.space_le_sum_card` 7
theorem slc7 : ¬ drop0% Turing.MultiTapeNTM.RunPath.space_le_sum_card 7 := fun h => by
  have := @h 1 Unit Bool [] ntmH1 (.singleton _ (ntmH1.initCfg [])) (fun _ => ∅)
  have := rpS (RelSeries.singleton (ntmH1.stepRel []) (ntmH1.initCfg []))
  simp at *
  omega
-- `Turing.MultiTapeNTM.RunPath.visitedByTapeHead_snoc` 7 (dependent)
theorem vhs7 : ¬ indep0% Turing.MultiTapeNTM.RunPath.visitedByTapeHead_snoc 7 := fun h => by
  obtain ⟨_, h, _⟩ := @h 1 Unit Bool [] ntmH1 (.singleton _ (ntmH1.initCfg [])) (ntmH1.initCfg []) 0
  exact h


universe u_1 u_2
-- `Turing.MultiTapeNTM.RunPath.exists_running` 6: removable (if the last configuration is running, no configuration of the path is halted, so the path itself is a running path)
theorem er6 : drop% Turing.MultiTapeNTM.RunPath.exists_running 6 := by
  intro k State Symbol input ntm p
  by_cases hl : (RelSeries.last p).Halted
  · exact p.exists_running hl
  · refine ⟨⟨p.length, p.toFun, fun i => ⟨fun hi => hl ?_, p.step i⟩⟩, rfl, rfl, le_rfl,
      fun c hc => by obtain ⟨i, hi⟩ := hc; exact ⟨i, hi⟩⟩
    rw [p.last_eq_of_halted i.castSucc hi]
    exact hi

-- `Turing.MultiTapeNTM.Follows.step` 11
theorem fs11 : ¬ drop0% Turing.MultiTapeNTM.Follows.step 11 := fun h => by
  obtain ⟨_, h, _⟩ := @h 0 Unit Bool [] tmU.toMultiTapeNTM 0 Unit [] ntmH0 id
    (.mapState id) id (tmU.initCfg []) (tmU.step (tmU.initCfg []))
    (Turing.MultiTapeTM.step_iff.mpr rfl) rfl rfl (fun _ ha => ha)
  exact h
-- `Turing.MultiTapeNTM.Follows.step` 15
theorem fs15 : ¬ drop0% Turing.MultiTapeNTM.Follows.step 15 := fun h => by
  obtain ⟨_, h, _⟩ := @h 0 Unit Bool [] ntmH0 0 Unit [] ntmH0 id
    (.mapState id) (fun _ _ _ h => h.elim) id (ntmH0.initCfg []) (ntmH0.initCfg [])
    rfl rfl (fun _ ha => ha)
  exact h
-- `Turing.MultiTapeNTM.Follows.step` 16
theorem fs16 : ¬ drop0% Turing.MultiTapeNTM.Follows.step 16 := fun h => by
  obtain ⟨_, h, _⟩ := @h 0 Unit Bool [] ntmH0 0 Unit [] ntmH0 id
    ⟨id, fun _ a => { a with state := some () }⟩ (fun _ _ _ h => h.elim)
    (fun c => c.withState (some ())) cfgH0 cfgH0 ((Turing.MultiTapeNTM.step_of_halt rfl).mpr rfl)
    rfl (fun a ha => Turing.Cfg.ext_zero_tapes rfl (congrArg (·.inputPos) ha) (congrArg (·.output) ha))
  exact h
-- `Turing.MultiTapeNTM.Follows.step` 17
theorem fs17 : ¬ drop0% Turing.MultiTapeNTM.Follows.step 17 := fun h => by
  let c : Turing.Cfg 0 Bool Unit [true] := ⟨some (), 1, fun i => i.elim0, fun i => i.elim0, []⟩
  let d : Turing.Cfg 0 Bool Unit [true] := ⟨some (), 0, fun i => i.elim0, fun i => i.elim0, []⟩
  have hc : c = stay.apply c := Turing.Cfg.ext_zero_tapes rfl (by simp [stay, c]) (by simp [stay, c])
  have hd : stay.apply d = d := Turing.Cfg.ext_zero_tapes rfl (by simp [stay, d]) (by simp [stay, d])
  obtain ⟨_, h, _⟩ := @h 0 Unit Bool [true] ntmT 0 Unit [true] ntmT id
    ⟨id, fun _ _ => stay⟩ (fun _ _ _ h => h) (fun _ => d) c c
    ⟨stay, by simp [c, Turing.Cfg.inputSymbol, ntmT], hc⟩ rfl (fun _ _ => hd)
  simp [d, Turing.Cfg.inputSymbol, ntmT] at h
-- `Turing.MultiTapeNTM.Follows.step` 18
theorem fs18 : ¬ drop0% Turing.MultiTapeNTM.Follows.step 18 := fun h => by
  have := Turing.MultiTapeTM.step_iff.mp (@h 0 Unit Bool [] tmU.toMultiTapeNTM 0 Unit []
    tmU.toMultiTapeNTM id (.mapState id) (fun _ _ _ h => h) (fun _ => tmU.initCfg [])
    (tmU.initCfg []) (tmU.step (tmU.initCfg [])) (Turing.MultiTapeTM.step_iff.mpr rfl) rfl rfl)
  have := congrArg (·.state) this
  change (tmU.runFrom (tmU.initCfg []) 1).state = _ at this
  rw [tmU_halt1] at this
  cases this

-- `Turing.MultiTapeNTM.ComputationPath.spaceUsedByTape_le_of_space_le` 7
theorem sls7 : ¬ drop0% Turing.MultiTapeNTM.ComputationPath.spaceUsedByTape_le_of_space_le 7 :=
  fun h => by
  have e := @h 1 Unit Bool tmR [] (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tmR [] 1)
    (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tmR [] 0) 0
  change (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR (tmR.initCfg []) 1).spaceUsedByTape 0 ≤
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR (tmR.initCfg []) 0).spaceUsedByTape 0 at e
  rw [tmR_sut _ rfl, tmR_sut _ rfl] at e
  omega
-- `Turing.MultiTapeNTM.RunPath.space_le_of_subset` 7
theorem slo7 : ¬ drop0% Turing.MultiTapeNTM.RunPath.space_le_of_subset 7 := fun h => by
  have e := @h 1 Unit Bool [] tmR.toMultiTapeNTM
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR (tmR.initCfg []) 0)
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR (tmR.initCfg []) 1)
  rw [tmR_space _ rfl, tmR_space _ rfl] at e
  omega
-- `Turing.MultiTapeNTM.RunPath.InWindow.space_le` 7
theorem iws7 : ¬ drop0% Turing.MultiTapeNTM.RunPath.InWindow.space_le 7 := fun h => by
  have e := @h 1 Unit Bool [] tmR.toMultiTapeNTM
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR (tmR.initCfg []) 1) 0
  rw [tmR_space _ rfl] at e
  omega
-- `Turing.MultiTapeNTM.RunsInSpace.exists_space_max` 6
theorem esm6 : ¬ drop0% Turing.MultiTapeNTM.RunsInSpace.exists_space_max 6 := fun h => by
  obtain ⟨p, hp⟩ := @h 1 Unit Bool [] tmR.toMultiTapeNTM 0
  have e := hp (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tmR [] p.space)
  change (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR (tmR.initCfg []) p.space).space ≤ _ at e
  rw [tmR_space _ rfl] at e
  omega
-- `Turing.MultiTapeNTM.RunPath.InWindow.smash` 7 (dependent)
theorem iwm7 : ¬ indep0% Turing.MultiTapeNTM.RunPath.InWindow.smash 7 := fun h => by
  have := congrArg (·.state) (@h 1 Unit Bool [] ntmH1 (.singleton _ cfgH1')
    (.singleton _ (ntmH1.initCfg [])) 0 (iwS _ rfl) (iwS _ rfl))
  cases this
-- `Turing.MultiTapeNTM.RunPath.InWindow.smash` 9
theorem iwm9 : ¬ drop0% Turing.MultiTapeNTM.RunPath.InWindow.smash 9 := fun h => by
  let c : Turing.Cfg 1 Bool Unit [] := ⟨some (), 1, fun _ _ => none, fun _ => -1, []⟩
  have H := @h 1 Unit Bool [] tmR.toMultiTapeNTM
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR c 1)
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR (tmR.runFrom c 1) 0) rfl 0 (by
      rintro x ⟨j, rfl⟩ i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      change (tmR.step^[(j : ℕ)] (tmR.runFrom c 1)).workTapePos 0 ∈ Turing.window 0
      rw [show (j : ℕ) = 0 from by have := j.isLt; change _ < 0 + 1 at this; omega]
      change (tmR.runFrom c 1).workTapePos 0 ∈ Turing.window 0
      rw [(tmR_run c rfl 1).2]
      simp [c, Turing.window])
  have hm := RelSeries.head_mem (RelSeries.smash
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR c 1)
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR (tmR.runFrom c 1) 0) rfl)
  have := H _ hm 0
  erw [RelSeries.head_smash] at this
  change c.workTapePos 0 ∈ Turing.window 0 at this
  simp [c, Turing.window] at this
-- `Turing.MultiTapeNTM.RunPath.InWindow.smash` 10
theorem iwm10 : ¬ drop0% Turing.MultiTapeNTM.RunPath.InWindow.smash 10 := fun h => by
  have H := @h 1 Unit Bool [] tmR.toMultiTapeNTM
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR (tmR.initCfg []) 0)
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR (tmR.initCfg []) 1) rfl 0 (by
      rintro x ⟨j, rfl⟩ i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      change (tmR.step^[(j : ℕ)] (tmR.initCfg [])).workTapePos 0 ∈ Turing.window 0
      rw [show (j : ℕ) = 0 from by have := j.isLt; change _ < 0 + 1 at this; omega]
      simp [Turing.window])
  have hm := RelSeries.last_mem (RelSeries.smash
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR (tmR.initCfg []) 0)
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmR (tmR.initCfg []) 1) rfl)
  have := H _ hm 0
  erw [RelSeries.last_smash] at this
  change (tmR.runFrom (tmR.initCfg []) 1).workTapePos 0 ∈ Turing.window 0 at this
  rw [(tmR_run _ rfl 1).2] at this
  simp [Turing.window] at this
-- `Turing.MultiTapeNTM.RunPath.visitedByTapeHead_map` 13
theorem vhm13 : ¬ drop0% Turing.MultiTapeNTM.RunPath.visitedByTapeHead_map 13 := fun h => by
  have := congrArg (fun s => (1 : ℤ) ∈ s)
    (@h 1 1 Unit Unit Bool [] [] ntmH1 ntmH1 (.singleton _ cfgH1') shiftH 0 0)
  simp [Turing.MultiTapeNTM.RunPath.visitedByTapeHead, shiftH, cfgH1', Fin.exists_fin_one,
    RelSeries.singleton, RelSeries.map, Turing.MultiTapeNTM.RunPath.map] at this
  exact this (Finset.mem_univ _)


-- `Turing.Storage.ext` 6
theorem se6 : ¬ drop0% Turing.Storage.ext 6 := fun h => by
  have := @h Bool Unit 1 ⟨none, fun _ _ => none, fun _ => 0⟩ ⟨none, fun _ _ => some true, fun _ => 0⟩
    rfl rfl
  simpa using congrFun (congrFun (congrArg (·.workTapes) this) 0) 0
-- `Turing.Storage.ext` 7
theorem se7 : ¬ drop0% Turing.Storage.ext 7 := fun h => by
  have := @h Bool Unit 1 ⟨none, fun _ _ => none, fun _ => 0⟩ ⟨none, fun _ _ => none, fun _ => 1⟩
    rfl rfl
  simpa using congrFun (congrArg (·.workTapePos) this) 0
-- `Turing.encard_fitsIn_le` 7
theorem efl7 : ¬ drop0% Turing.encard_fitsIn_le 7 := fun h => by
  have H := @h 1 Empty Empty _ _ (fun _ => 1) 0
  have hsub : ({⟨none, fun _ _ => none, fun _ => 0⟩, ⟨none, fun _ _ => none, fun _ => 1⟩} :
      Set (Turing.Storage Empty Empty 1)) ⊆ {x | x.FitsIn fun _ => 1} := by
    rintro x (rfl | rfl) <;> exact ⟨fun j => by simp, fun j z hz => by simp at hz⟩
  have h2 := (Set.encard_le_encard hsub).trans H
  rw [Set.encard_pair (by intro e; simpa using congrFun (congrArg (·.workTapePos) e) 0)] at h2
  simp [Turing.storageBound] at h2
-- `Turing.MultiTapeTM.encard_storages_le` 8
theorem esl8 : ¬ drop0% Turing.MultiTapeTM.encard_storages_le 8 := fun h => by
  have := @h 1 Unit Bool [] tmR _ _ 0
  rw [infSt tmR_inj] at this
  norm_cast at this
-- `Turing.MultiTapeTM.encard_cores_le` 8
theorem ecl8 : ¬ drop0% Turing.MultiTapeTM.encard_cores_le 8 := fun h => by
  have := @h 1 Unit Bool [] tmR _ _ 0
  rw [infCo tmR_inj] at this
  norm_cast at this
-- `Turing.MultiTapeTM.encard_storages_le_pow` 4
theorem eslp4 : ¬ drop0% Turing.MultiTapeTM.encard_storages_le_pow 4 := fun h => by
  obtain ⟨a, c, hac⟩ := @h 1 Unit ℕ tmW _
  have := hac [] 1 tmW_space
  rw [infSt tmW_inj] at this
  norm_cast at this
-- `Turing.MultiTapeTM.encard_storages_le_pow` 5
theorem eslp5 : ¬ drop0% Turing.MultiTapeTM.encard_storages_le_pow 5 := fun h => by
  obtain ⟨a, c, hac⟩ := @h 0 ℕ Bool tmC _
  have := hac [] 0 (Turing.MultiTapeNTM.runsInSpace_zero_tapes _ _ _)
  rw [infSt tmC_inj] at this
  norm_cast at this
-- `Turing.MultiTapeTM.encard_cores_le_pow` 4
theorem eclp4 : ¬ drop0% Turing.MultiTapeTM.encard_cores_le_pow 4 := fun h => by
  obtain ⟨a, c, hac⟩ := @h 1 Unit ℕ tmW _
  have := hac [] 1 tmW_space
  rw [infCo tmW_inj] at this
  norm_cast at this
-- `Turing.MultiTapeTM.encard_cores_le_pow` 5
theorem eclp5 : ¬ drop0% Turing.MultiTapeTM.encard_cores_le_pow 5 := fun h => by
  obtain ⟨a, c, hac⟩ := @h 0 ℕ Bool tmC _
  have := hac [] 0 (Turing.MultiTapeNTM.runsInSpace_zero_tapes _ _ _)
  rw [infCo tmC_inj] at this
  norm_cast at this


-- `Turing.MultiTapeTM.runFrom_read` 9 (dependent)
theorem rfr9 : ¬ indep0% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.«0».Turing.MultiTapeTM.runFrom_read 9 := fun h => by
  have := @h Unit Unit encU encU id ∅ [] () 1 (Finset.mem_insert_self _ _)
  exact absurd this (by decide)
-- `Turing.MultiTapeTM.runFrom_write` 11 (dependent)
theorem rfw11 : ¬ indep0% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.«0».Turing.MultiTapeTM.runFrom_write 11 := fun h => by
  have := @h Unit Unit encU encU id ∅ [] [] 0 [] [true] 0 (Nat.zero_le _)
  exact absurd this (by decide)
-- `Turing.MultiTapeTM.runFrom_write_halted` 11 (dependent)
theorem rfwh11 : ¬ indep0% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.«0».Turing.MultiTapeTM.runFrom_write_halted 11 := fun h => by
  have := @h Unit Unit encU encU id ∅ [] [] 0 [] [true]
  exact absurd this (by decide)
-- `Turing.MultiTapeTM.runFrom_write` 13
theorem rfw13 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.«0».Turing.MultiTapeTM.runFrom_write 13 := fun h => by
  have hw : [] ∈ (priv% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.«0».Turing.MultiTapeTM.outSuffixes) encU (id : Unit → Unit) ∅ [] := by decide
  have e2 := congrArg (·.state) (@h Unit Unit encU encU id ∅ [] [] 0 [] [] hw 2)
  have e1 := (priv% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.«0».Turing.MultiTapeTM.runFrom_write_halted) (encIn := encU) (f := (id : Unit → Unit)) (input := ([] : List Bool)) 0 [] hw
  rw [Turing.MultiTapeTM.runFrom_eq_of_halt _ _ (by decide : ([] : List Bool).length + 1 ≤ 2) (by rw [e1])] at e2
  rw [e1] at e2
  cases e2
-- `Turing.MultiTapeTM.computesFunInTimeAndSpace_almostConstTM` 7
theorem cfa7 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.«0».Turing.MultiTapeTM.computesFunInTimeAndSpace_almostConstTM 7 := fun h => by
  have := outBound (@h Unit ℕ encU encR (fun _ => 3) ∅ [] ())
  change (List.replicate 3 true).length ≤ Turing.MultiTapeTM.almostConstTime _ _ _ _ _ at this
  simp [Turing.MultiTapeTM.almostConstTime] at this
-- `Turing.MultiTapeTM.computableInTimeAndSpace_almostConstTime` 7
theorem caa7 : ¬ drop0% Turing.MultiTapeTM.computableInTimeAndSpace_almostConstTime 7 := fun h => by
  obtain ⟨k, S, _, tm, htm⟩ := @h Unit ℕ encU encR (fun _ => 3) ∅ []
  have := outBound (htm ())
  change (List.replicate 3 true).length ≤ Turing.MultiTapeTM.almostConstTime _ _ _ _ _ at this
  simp [Turing.MultiTapeTM.almostConstTime] at this
-- `Turing.MultiTapeTM.computableInTimeAndSpace_of_exists_finite_ne` 5
theorem cef5 : ¬ drop0% Turing.MultiTapeTM.computableInTimeAndSpace_of_exists_finite_ne 5 :=
  fun h => by
  obtain ⟨c, hc⟩ := @h ℕ ℕ encR encR id
  exact noConst c hc
-- `Turing.MultiTapeTM.computableInTimeAndSpace_finiteFunTime` 2 (dependent)
theorem cff2 : ¬ indep0% Turing.MultiTapeTM.computableInTimeAndSpace_finiteFunTime 2 := fun h =>
  @not_finite ℕ _ (@h ℕ ℕ encR encR id)
-- `Turing.MultiTapeTM.computableInTimeAndSpace_of_finite` 2
theorem cof2 : ¬ drop0% Turing.MultiTapeTM.computableInTimeAndSpace_of_finite 2 := fun h => by
  obtain ⟨c, hc⟩ := @h ℕ ℕ encR encR id
  exact noConst c hc
-- `Turing.MultiTapeTM.combineLeftHom_apply` 10 (dependent)
theorem clh10 : ¬ indep0% Turing.MultiTapeTM.combineLeftHom_apply 10 := fun h => by
  have := @h 0 Bool Unit Unit tmU tmU (fun _ => none) (fun _ => none) (.inl ()) [] cfgH0 ()
  cases this

-- `Turing.MultiTapeTM.ForwardWork.runFrom_walk` 7
theorem fww7 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ForwardWork.«0».Turing.MultiTapeTM.ForwardWork.runFrom_walk 7 := fun h => by
  have := congrArg (·.state) (@h Bool [] 0 [] [] 0 1)
  rw [Turing.MultiTapeTM.runFrom, Function.iterate_one, Turing.MultiTapeTM.step_of_state rfl] at this
  simp [Turing.MultiTapeTM.forwardWork, Turing.Action.apply, Turing.Cfg.workTapeSymbols] at this
-- `Turing.MultiTapeTM.runFrom_forwardWork` 7
theorem rfw7 : ¬ drop0% Turing.MultiTapeTM.runFrom_forwardWork 7 := fun h => by
  have := congrFun (congrArg (·.workTapePos) (@h Bool [] 0 [] [] 1 0)) 0
  rw [Turing.MultiTapeTM.runFrom, Function.iterate_one, Turing.MultiTapeTM.step_of_state rfl] at this
  simp [Turing.MultiTapeTM.forwardWork, Turing.Action.apply, Turing.Cfg.workTapeSymbols] at this
-- `Turing.MultiTapeTM.workTapePos_runFrom_forwardWork` 6
theorem wfw6 : ¬ drop0% Turing.MultiTapeTM.workTapePos_runFrom_forwardWork 6 := fun h => by
  have := @h Bool [] 0 [] [] 1 0
  simp [Turing.MultiTapeTM.runFrom] at this

-- `Turing.MultiTapeTM.RewindWork.step_scan_some` 8
theorem rss8 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork.«0».Turing.MultiTapeTM.RewindWork.step_scan_some 8 := fun h => by
  have := @h Bool [] none 0 (fun _ => none) [] 0 true
  rw [rws_none rfl] at this
  have := congrArg (·.state) this
  simp at this
-- `Turing.MultiTapeTM.RewindWork.step_scan_none` 7
theorem rsn7 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork.«0».Turing.MultiTapeTM.RewindWork.step_scan_none 7 := fun h => by
  have := @h Bool [] none 0 (fun _ => some true) [] 0
  rw [rws_some (s := true) rfl] at this
  have := congrArg (·.state) this
  simp at this
-- `Turing.MultiTapeTM.RewindWork.runFrom_scan` 11
theorem rsc11 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork.«0».Turing.MultiTapeTM.RewindWork.runFrom_scan 11 := fun h => by
  have := congrArg (·.state) (@h Bool [] none 0 (Turing.tapeOfList []) [] [] rfl 0 le_rfl 1)
  rw [Turing.MultiTapeTM.runFrom, Function.iterate_one, rws_none (by simp [Turing.tapeOfList_nil])] at this
  simp at this
-- `Turing.MultiTapeTM.RewindWork.runFrom_scan` 9
theorem rsc9 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork.«0».Turing.MultiTapeTM.RewindWork.runFrom_scan 9 := fun h => by
  have := congrArg (·.state) (@h Bool [] none 0 (Turing.tapeOfList []) [] [] rfl 1 1 le_rfl)
  rw [Turing.MultiTapeTM.runFrom, Function.iterate_one, rws_none (by simp [Turing.tapeOfList_nil])] at this
  simp at this
-- `Turing.MultiTapeTM.RewindWork.runFrom_scan` 7
theorem rsc7 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork.«0».Turing.MultiTapeTM.RewindWork.runFrom_scan 7 := fun h => by
  have := congrArg (·.state) (@h Bool [] none 0 (fun _ => none) [] [true] 1 (by simp) 1 le_rfl)
  rw [Turing.MultiTapeTM.runFrom, Function.iterate_one, rws_none rfl] at this
  simp at this


-- `Turing.MultiTapeTM.runFrom_rewindWork` 9
theorem rrw9 : ¬ drop0% Turing.MultiTapeTM.runFrom_rewindWork 9 := fun h => by
  have e := congrFun (congrArg (·.workTapePos) (@h Bool [] none 0 (Turing.tapeOfList []) [] [] rfl 1)) 0
  change ((Turing.MultiTapeTM.rewindWork Bool none).step ((Turing.MultiTapeTM.rewindWork Bool none).step
    ((Turing.MultiTapeTM.rewindWork Bool none).step _))).workTapePos 0 = _ at e
  rw [rws_start, rws_none (by simp [Turing.tapeOfList_nil]), Turing.MultiTapeTM.step_of_halt rfl] at e
  simp at e
-- `Turing.MultiTapeTM.runFrom_rewindWork` 7
theorem rrw7 : ¬ drop0% Turing.MultiTapeTM.runFrom_rewindWork 7 := fun h => by
  have e := congrArg (·.state) (@h Bool [] none 0 (fun _ => some true) [] [] 0 le_rfl)
  change ((Turing.MultiTapeTM.rewindWork Bool none).step
    ((Turing.MultiTapeTM.rewindWork Bool none).step _)).state = _ at e
  rw [rws_start, rws_some (s := true) rfl] at e
  simp at e
-- `Turing.MultiTapeTM.runFrom_rewindWork_none` 8
theorem rrn8 : ¬ drop0% Turing.MultiTapeTM.runFrom_rewindWork_none 8 := fun h => by
  have e := congrFun (congrArg (·.workTapePos) (@h Bool [] 0 (Turing.tapeOfList []) [] [] rfl 1)) 0
  change ((Turing.MultiTapeTM.rewindWork Bool).step ((Turing.MultiTapeTM.rewindWork Bool).step
    ((Turing.MultiTapeTM.rewindWork Bool).step _))).workTapePos 0 = _ at e
  rw [rws_start, rws_none (by simp [Turing.tapeOfList_nil]), Turing.MultiTapeTM.step_of_halt rfl] at e
  simp at e
-- `Turing.MultiTapeTM.runFrom_rewindWork_none` 6
theorem rrn6 : ¬ drop0% Turing.MultiTapeTM.runFrom_rewindWork_none 6 := fun h => by
  have e := congrArg (·.state) (@h Bool [] 0 (fun _ => some true) [] [] 0 le_rfl)
  change ((Turing.MultiTapeTM.rewindWork Bool).step
    ((Turing.MultiTapeTM.rewindWork Bool).step _)).state = _ at e
  rw [rws_start, rws_some (s := true) rfl] at e
  simp at e
-- `Turing.MultiTapeTM.runFrom_rewindWork_erase` 6
theorem rre6 : ¬ drop0% Turing.MultiTapeTM.runFrom_rewindWork_erase 6 := fun h => by
  have e := congrArg (·.state) (@h Bool [] 0 (fun _ => some true) [] [])
  change ((Turing.MultiTapeTM.rewindWork Bool (some none)).step
    ((Turing.MultiTapeTM.rewindWork Bool (some none)).step _)).state = _ at e
  rw [rws_start, rws_some (s := true) rfl] at e
  simp at e
-- `Turing.MultiTapeTM.workTapePos_runFrom_rewindWork` 7
theorem wrr7 : ¬ drop0% Turing.MultiTapeTM.workTapePos_runFrom_rewindWork 7 := fun h => by
  have e := @h Bool [] none 0 (fun _ => some true) [] [] 0 le_rfl 2
  change ((Turing.MultiTapeTM.rewindWork Bool none).step
    ((Turing.MultiTapeTM.rewindWork Bool none).step _)).workTapePos 0 ∈ _ at e
  rw [rws_start, rws_some (s := true) rfl] at e
  simp at e
-- `Turing.MultiTapeTM.workTapePos_runFrom_rewindWork` 9: removable (for p > w.length the head moves p, p - 1, p and halts: it stays in [p - 1, p])
theorem wrr9 : drop% Turing.MultiTapeTM.workTapePos_runFrom_rewindWork 9 := by
  intro Symbol input write ip t out w hw p m
  rcases le_or_gt p w.length with hp | hp
  · exact Turing.MultiTapeTM.workTapePos_runFrom_rewindWork write ip t out hw hp m
  · have hb : t ((p : ℤ) - 1) = none := by
      rw [hw, show (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) by omega, Turing.tapeOfList_ofNat]
      exact List.getElem?_eq_none (by omega)
    have h2 : (Turing.MultiTapeTM.rewindWork Symbol write).runFrom
        ⟨some (Turing.MultiTapeTM.rewindWork Symbol write).q₀, ip, fun _ => t, fun _ => (p : ℤ), out⟩ 2
        = ⟨none, ip, fun _ => t, fun _ => (p : ℤ) - 1 + 1, out⟩ := by
      change (Turing.MultiTapeTM.rewindWork Symbol write).step
        ((Turing.MultiTapeTM.rewindWork Symbol write).step _) = _
      rw [rws_start, rws_none hb]
    rcases m with _ | _ | m
    · simp [Turing.MultiTapeTM.runFrom]
    · change ((Turing.MultiTapeTM.rewindWork Symbol write).step _).workTapePos 0 ∈ _
      rw [rws_start]
      simp
      omega
    · rw [Turing.MultiTapeTM.runFrom_eq_of_halt _ _ (by omega : 2 ≤ m + 1 + 1) (by rw [h2]), h2]
      simp

-- `Turing.MultiTapeTM.Rewind.step_eq` 4
theorem rse4 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput.«0».Turing.MultiTapeTM.Rewind.step_eq 4 := fun h => by
  have := @h Bool [] ⟨none, 1, fun i => i.elim0, fun i => i.elim0, []⟩ .start
  rw [Turing.MultiTapeTM.step_of_halt rfl] at this
  have := congrArg (·.state) this
  simp [Turing.MultiTapeTM.rewindInput] at this
-- `Turing.MultiTapeTM.Rewind.runFrom_walk` 6
theorem rrwk6 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput.«0».Turing.MultiTapeTM.Rewind.runFrom_walk 6 := fun h => by
  have e := congrArg (·.inputPos) (@h Bool [true] (fun i => i.elim0) (fun i => i.elim0) [] 2)
  have s1 : (Turing.MultiTapeTM.rewindInput Bool).step
      (⟨some .walk, 2, fun i => i.elim0, fun i => i.elim0, []⟩ : Turing.Cfg 0 Bool _ [true]) =
      ⟨none, 2, fun i => i.elim0, fun i => i.elim0, []⟩ := by
    rw [Turing.MultiTapeTM.step_of_state rfl]
    apply Turing.Cfg.ext_zero_tapes <;>
      simp [Turing.MultiTapeTM.rewindInput, Turing.Action.apply, Turing.Cfg.inputSymbol,
        Turing.moveInputPos] <;> decide
  change ((Turing.MultiTapeTM.rewindInput Bool).step ((Turing.MultiTapeTM.rewindInput Bool).step
    ((Turing.MultiTapeTM.rewindInput Bool).step _))).inputPos = _ at e
  have hh : (Turing.MultiTapeTM.rewindInput Bool).step
      (⟨none, 2, fun i => i.elim0, fun i => i.elim0, []⟩ : Turing.Cfg 0 Bool _ [true]) =
      ⟨none, 2, fun i => i.elim0, fun i => i.elim0, []⟩ := Turing.MultiTapeTM.step_of_halt rfl
  rw [s1, hh, hh] at e
  exact absurd e (by decide)
-- `Turing.MultiTapeTM.Copy.step_scan` 3
theorem ids3 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id.«0».Turing.MultiTapeTM.Copy.step_scan 3 := fun h => by
  have e := (priv% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id.«0».Turing.MultiTapeTM.Copy.step_halt) (input := ([] : List Bool))
  have := e.symm.trans (@h Bool [] 0)
  exact absurd (congrArg Turing.Cfg.state this) (by intro h; cases h)

-- `Turing.MultiTapeTM.exists_runPath_seq` 8
theorem ers8 : ¬ drop0% Turing.MultiTapeTM.exists_runPath_seq 8 := fun h => by
  obtain ⟨p, hh, hl, hlen, -⟩ := @h 0 Bool Unit Unit [] tmU tmU
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmU (tmU.initCfg []) 0)
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmU ((tmU.initCfg []).withState (some tmU.q₀)) 0) rfl
  have e : RelSeries.last p = Turing.MultiTapeTM.runFrom (RelSeries.head p) p.length :=
    Turing.MultiTapeTM.runPath_apply_eq_runFrom p (Fin.last _)
  change p.length ≤ 0 + 0 at hlen
  rw [show p.length = 0 by omega, hh, hl] at e
  have := congrArg (·.state) e
  change Option.map Sum.inr (some ()) = Turing.MultiTapeTM.handOver () (some ()) at this
  simp at this
-- `Turing.MultiTapeTM.exists_runPath_seq` 10
theorem ers10 : ¬ drop0% Turing.MultiTapeTM.exists_runPath_seq 10 := fun h => by
  obtain ⟨p, hh, hl, hlen, -⟩ := @h 0 Bool Unit Unit [] tmU tmU
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmU cfgH0 0) rfl
    (Turing.MultiTapeNTM.RunPath.ofDeterministic tmU (tmU.initCfg []) 0)
  have e : RelSeries.last p = Turing.MultiTapeTM.runFrom (RelSeries.head p) p.length :=
    Turing.MultiTapeTM.runPath_apply_eq_runFrom p (Fin.last _)
  change p.length ≤ 0 + 0 at hlen
  rw [show p.length = 0 by omega, hh, hl] at e
  have := congrArg (·.inputPos) e
  change (1 : Fin 2) = 0 at this
  exact absurd this (by decide)
-- `Turing.MultiTapeTM.transformsTapes_seq` 14
theorem tss14 : ¬ drop0% Turing.MultiTapeTM.transformsTapes_seq 14 := fun h => by
  obtain ⟨_, _, ⟨_, _, _, hf, -⟩, -⟩ := @h 1 Bool Unit Unit nop1 nop1 (fun _ _ => True)
    (fun _ _ => True) (fun _ _ _ _ => False) _ 0 0 1 1 nopTT (fun _ _ _ _ _ _ => trivial)
    [] (fun _ => []) [] trivial
  exact hf
-- `Turing.MultiTapeTM.transformsTapes_seq` 15
theorem tss15 : ¬ drop0% Turing.MultiTapeTM.transformsTapes_seq 15 := fun h => by
  obtain ⟨_, _, ⟨_, _, _, -, hf, -⟩, -⟩ := @h 1 Bool Unit Unit nop1 nop1 (fun _ _ => True)
    (fun _ _ => True) _ (fun _ _ _ _ => False) 1 1 0 0 nopTT (fun _ _ _ _ _ _ => trivial)
    [] (fun _ => []) [] trivial
  exact hf
-- `Turing.MultiTapeTM.transformsTapes_seq` 16
theorem tss16 : ¬ drop0% Turing.MultiTapeTM.transformsTapes_seq 16 := fun h => by
  obtain ⟨_, _, ⟨_, _, _, -, hf, -⟩, -⟩ := @h 1 Bool Unit Unit nop1 nop1 (fun _ _ => True)
    (fun _ _ => False) _ (fun _ _ _ _ => False) 1 1 0 0 nopTT (fun _ _ _ h => h.elim)
    [] (fun _ => []) [] trivial
  exact hf
-- `Turing.MultiTapeTM.RepeatUntilBlank.exists_round` 10
theorem rer10 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank.«0».Turing.MultiTapeTM.RepeatUntilBlank.exists_round 10 := fun h => by
  obtain ⟨_, _, hf, -⟩ := @h 1 Bool Unit [] 0 nop1 (fun _ _ => True) (fun _ _ _ _ => False) 0 0
    (fun _ => []) [] trivial
  exact hf
-- `Turing.MultiTapeTM.RepeatUntilBlank.exists_round` 13
theorem rer13 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank.«0».Turing.MultiTapeTM.RepeatUntilBlank.exists_round 13 := fun h => by
  obtain ⟨_, _, hf, -⟩ := @h 1 Bool Unit [] 0 nop1 (fun _ _ => False) (fun _ _ _ _ => False) 0 0
    (fun _ _ _ h => h.elim) (fun _ => []) []
  exact hf
-- `Turing.MultiTapeTM.transformsTapes_repeatUntilBlank` 11
theorem tru11 : ¬ drop0% Turing.MultiTapeTM.transformsTapes_repeatUntilBlank 11 := fun h => by
  obtain ⟨_, _, hf, -⟩ := @h 1 Bool Unit 0 nop1 (fun _ _ _ _ => True) (fun _ _ _ => False) 0 0 0
    (fun n hn => absurd hn (Nat.not_lt_zero _)) [] (fun _ => []) [] trivial
  exact hf
-- `Turing.MultiTapeTM.transformsTapes_repeatUntilBlank` 10
theorem tru10 : ¬ drop0% Turing.MultiTapeTM.transformsTapes_repeatUntilBlank 10 := fun h => by
  obtain ⟨_, _, hf, -⟩ := @h 1 Bool Unit 0 nop1 (fun n _ _ _ => n = 0) (fun _ _ _ => False) 1 0 0
    (fun _ _ _ _ h => absurd h Nat.one_ne_zero) [] (fun _ => []) [] rfl
  exact hf
-- `Turing.MultiTapeTM.TransformsTapes.tapeEmb` 8
theorem tte8 : ¬ drop0% Turing.MultiTapeTM.TransformsTapes.tapeEmb 8 := fun h => by
  obtain ⟨_, _, ⟨v, hv, -⟩, -⟩ := @h Bool Unit 1 nop1 (fun _ _ => True) (fun _ _ _ _ => False) 0 0 0
    [] (fun _ => []) [] trivial
  exact hv
