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

/-! T1c0: the 16 OnePseudoConsensus rows that keep hpc1 : a.PseudoConsensus 1. No verdicts.

Every row is decided (necessary) as soon as some algorithm with PseudoConsensus 1 is available, and
all rows would be vacuously removable if none existed. Such an algorithm exists for card P >= 3
(single-decree Paxos: majority quorums, unbounded ballots, self-addressed tick messages as ballot
triggers), but bounded protocols (one-shot votes, majority of inputs, pair camps, tokens, bounded
ballots) all reach states where both live processes are committed and wait for the silent one, and
formalising Paxos safety plus liveness from every reachable state did not fit the time box.

The helpers below reduce 12 of the 16 rows to that single existence question: c_X (a) (hpc) ...
refutes row X for ANY algorithm a with PseudoConsensus 1 (and two distinct processes p q where
needed). Rows not covered: nonUniform_step_exists idx 12, canDecideWithout_uniform idx 13 and 17,
nonUniform_step idx 10 (they need algorithm-specific behaviour). -/

namespace T1c0
open Cslib Cslib.FLP

variable {P M S : Type} [DecidableEq P] [DecidableEq M]

-- the state with no messages and no decisions
def emptyS (a : Algorithm P M S) : State P M S := ⟨0, fun r => ⟨a.init r, none⟩⟩

-- a state where p decided true and everybody else false, with one message m in flight
def confS (a : Algorithm P M S) (p : P) (m : Message P M) : State P M S :=
  ⟨{m}, fun r => ⟨a.init r, some (decide (r = p))⟩⟩

theorem emptyS_mtr {a : Algorithm P M S} {xl : List (Action P M)} {t : State P M S}
    (h : a.lts.MTr (emptyS a) xl t) : t = emptyS a := by
  generalize hs : emptyS a = s at h
  induction h with
  | refl => rfl
  | @stepL s1 x s2 xl t htr _ ih =>
    subst hs
    cases x with
    | none => exact (ih (Algorithm.tr_none htr)).trans (Algorithm.tr_none htr).symm
    | some m => exact absurd htr.1 (by simp [emptyS])

theorem emptyS_noCDW {a : Algorithm P M S} (p : P) (b : Bool) : ¬ a.CanDecideWithout (emptyS a) p b := by
  rintro ⟨t, hc, r, hr⟩
  obtain ⟨xl, h⟩ := CanReachVia.canReach hc
  rw [emptyS_mtr h] at hr
  simp [emptyS, State.ProcDecided] at hr

theorem confS_dec {a : Algorithm P M S} {p q : P} (hpq : p ≠ q) (m : Message P M) (b : Bool) :
    (confS a p m).Decided b := by
  cases b
  · exact ⟨q, by simp [confS, State.ProcDecided, Ne.symm hpq]⟩
  · exact ⟨p, by simp [confS, State.ProcDecided]⟩

theorem confS_unreach [Fintype P] {a : Algorithm P M S} (hpc : a.PseudoConsensus 1) {p q : P} (hpq : p ≠ q)
    (m : Message P M) {inp : P → Bool} {t : State P M S} (hc : a.lts.CanReach (confS a p m) t) :
    ¬ a.Reachable inp t := fun hr =>
  absurd ((hpc.1 inp t hr).1 true false ⟨Algorithm.decided_stable (confS_dec hpq m true) hc,
    Algorithm.decided_stable (confS_dec hpq m false) hc⟩) (by decide)

-- a reachable decided state exists
theorem reachDec [Fintype P] {a : Algorithm P M S} (hpc : a.PseudoConsensus 1) (inp : P → Bool) (p : P) :
    ∃ s b, a.Reachable inp s ∧ s.Decided b := by
  obtain ⟨s', b, hc, hd⟩ := OnePseudoConsensus.pseudoTermination hpc (Algorithm.reachable_start (inp := inp)) p
  exact ⟨s', b, Algorithm.reachable_stable Algorithm.reachable_start (CanReachVia.canReach hc), hd⟩

-- conditional refutations: each needs only some algorithm with PseudoConsensus 1 and two processes

theorem c_pt10 (a : Algorithm P M S) [Fintype P] (hpc : a.PseudoConsensus 1) (p : P) :
    ¬ drop0% Cslib.FLP.OnePseudoConsensus.pseudoTermination 10 := fun h => by
  obtain ⟨s', b, hc, hd⟩ := @h P M S _ _ a (fun _ => true) _ hpc (emptyS a) p
  exact emptyS_noCDW p b ⟨s', hc, hd⟩

theorem c_cdwe10 (a : Algorithm P M S) [Fintype P] (hpc : a.PseudoConsensus 1) (p : P) :
    ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_exists 10 := fun h => by
  obtain ⟨b, hb⟩ := @h P M S _ _ a (fun _ => true) _ hpc (emptyS a) p
  exact emptyS_noCDW p b hb

theorem c_uon10 (a : Algorithm P M S) [Fintype P] (hpc : a.PseudoConsensus 1) (p : P) :
    ¬ drop0% Cslib.FLP.OnePseudoConsensus.uniform_or_nonUniform 10 := fun h => by
  rcases @h P M S _ _ a (fun _ => true) _ hpc (emptyS a) with h | h | h
  · exact emptyS_noCDW p _ (h p).1
  · exact emptyS_noCDW p _ (h p).1
  · obtain ⟨r, hr⟩ := h true; exact emptyS_noCDW r _ hr

theorem c_dec10 (a : Algorithm P M S) [Fintype P] (hpc : a.PseudoConsensus 1) {p q : P} (hpq : p ≠ q)
    (m : Message P M) : ¬ drop0% Cslib.FLP.OnePseudoConsensus.decided_eq_canDecideWithout 10 := fun h =>
  absurd (@h P M S _ _ a (fun _ => true) _ hpc (confS a p m) true false p (confS_dec hpq m true)
    ⟨_, CanReachVia.refl _ _, confS_dec hpq m false⟩) (by decide)

theorem c_dec14 (a : Algorithm P M S) [Fintype P] (hpc : a.PseudoConsensus 1) (p : P) :
    ¬ drop0% Cslib.FLP.OnePseudoConsensus.decided_eq_canDecideWithout 14 := fun h => by
  obtain ⟨b, hb⟩ := OnePseudoConsensus.canDecideWithout_exists hpc
    (Algorithm.reachable_start (a := a) (inp := fun _ => true)) p
  exact absurd (@h P M S _ _ a (fun _ => true) _ hpc _ Algorithm.reachable_start (!b) b p hb) (by cases b <;> decide)

theorem c_dec15 (a : Algorithm P M S) [Fintype P] (hpc : a.PseudoConsensus 1) (p : P) :
    ¬ drop0% Cslib.FLP.OnePseudoConsensus.decided_eq_canDecideWithout 15 := fun h => by
  obtain ⟨s, b, hr, hd⟩ := reachDec hpc (fun _ => true) p
  exact absurd (@h P M S _ _ a (fun _ => true) _ hpc s hr b (!b) p hd) (by cases b <;> decide)

theorem c_diu10 (a : Algorithm P M S) [Fintype P] (hpc : a.PseudoConsensus 1) {p q : P} (hpq : p ≠ q)
    (m : Message P M) : ¬ drop0% Cslib.FLP.OnePseudoConsensus.decided_imp_uniform 10 := fun h =>
  ((@h P M S _ _ a (fun _ => true) _ hpc (confS a p m) true (confS_dec hpq m true)) p).2
    ⟨_, CanReachVia.refl _ _, confS_dec hpq m false⟩

theorem c_diu12 (a : Algorithm P M S) [Fintype P] (hpc : a.PseudoConsensus 1) (p : P) :
    ¬ drop0% Cslib.FLP.OnePseudoConsensus.decided_imp_uniform 12 := fun h => by
  have h1 := @h P M S _ _ a (fun _ => true) _ hpc _ Algorithm.reachable_start true
  have h0 := @h P M S _ _ a (fun _ => true) _ hpc _ Algorithm.reachable_start false
  exact (h0 p).2 (h1 p).1

theorem c_fnu10 (a : Algorithm P M S) [Fintype P] (hpc : a.PseudoConsensus 1) {p q : P} (hpq : p ≠ q)
    (m : Message P M) : ¬ drop0% Cslib.FLP.OnePseudoConsensus.fair_nonUniform 10 := fun h => by
  obtain ⟨ss, xs, he, h0, -, hf⟩ := @h P M S _ _ a _ (fun _ => true) hpc (confS a p m)
  obtain ⟨n, hn, -⟩ := hf.exists
  refine confS_unreach hpc hpq m ⟨xs.extract 0 n, ?_⟩ hn
  rw [← h0]; exact he.extract_mTr (Nat.zero_le n)

theorem c_cdu14 (a : Algorithm P M S) [Fintype P] (hpc : a.PseudoConsensus 1) (p : P) (m : Message P M) :
    ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_uniform 14 := fun h => by
  obtain ⟨s, b, hr, hd⟩ := reachDec hpc (fun _ => true) p
  have hu := OnePseudoConsensus.decided_imp_uniform hpc hr hd p
  exact emptyS_noCDW p b (@h P M S _ _ a (fun _ => true) _ hpc s (emptyS a) m b hr p hu.1 hu.2)

theorem c_nus11 (a : Algorithm P M S) [Fintype P] (hpc : a.PseudoConsensus 1) (p : P) :
    ¬ drop0% Cslib.FLP.OnePseudoConsensus.nonUniform_step 11 := fun h => by
  obtain ⟨s, b, hr, hd⟩ := reachDec hpc (fun _ => true) p
  obtain ⟨s', hc, hall⟩ := @h P M S _ _ a (fun _ => true) _ hpc s hr p
  obtain ⟨t, hct, hdt⟩ := hall (!b)
  have hc2 : a.lts.CanReach s t := by
    obtain ⟨x1, h1⟩ := hc; obtain ⟨x2, h2⟩ := CanReachVia.canReach hct
    exact ⟨x1 ++ x2, LTS.MTr.comp _ h1 h2⟩
  exact absurd ((hpc.1 _ t (Algorithm.reachable_stable hr hc2)).1 b (!b)
    ⟨Algorithm.decided_stable hd hc2, hdt⟩) (by cases b <;> decide)

theorem c_nuse11 (a : Algorithm P M S) [Fintype P] (hpc : a.PseudoConsensus 1) {p q : P} (hpq : p ≠ q)
    (m : Message P M) : ¬ drop0% Cslib.FLP.OnePseudoConsensus.nonUniform_step_exists 11 := fun h => by
  obtain ⟨xl, t, hmtr, -, hr, -⟩ := @h P M S _ _ a _ (fun _ => true) hpc (confS a p m) m (by simp [confS])
  exact confS_unreach hpc hpq m ⟨xl, hmtr⟩ hr

end T1c0
