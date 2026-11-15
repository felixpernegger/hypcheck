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

-- ===== batch 1 =====

-- `Cslib.URM.State.ext` 3
theorem urmext3 : ¬ drop0% Cslib.URM.State.ext 3 := fun h => by
  have := congrArg (fun s => s.regs 0) (@h ⟨0, fun _ => 0⟩ ⟨0, fun _ => 1⟩ rfl)
  simp at this

-- `Cslib.URM.Instr.jumpsBoundedBy_of_nonJump` 1
theorem urmjb1 : ¬ drop0% Cslib.URM.Instr.jumpsBoundedBy_of_nonJump 1 := fun h => by
  have := @h (.J 0 0 5) 0
  simp [Cslib.URM.Instr.JumpsBoundedBy] at this

-- `Nat.segment_zero` 1
theorem segz1 : drop% Nat.segment_zero 1 := by
  intro f h0
  unfold Nat.segment
  rw [Nat.count_succ, Nat.count_zero]
  split <;> rfl

-- `Cslib.URM.straightLineFinalRegs_eq_of_halted` 4
theorem slfr4 : ¬ drop0% Cslib.URM.straightLineFinalRegs_eq_of_halted 4 := fun h => by
  have hsl : Cslib.URM.Program.IsStraightLine [] := by simp [Cslib.URM.Program.IsStraightLine]
  have h1 := @h [] hsl (fun _ => 0) ⟨0, fun _ => 0⟩ (by simp)
  have h2 := @h [] hsl (fun _ => 0) ⟨0, fun _ => 1⟩ (by simp)
  have := congrFun (h1.trans h2.symm) 0
  simp at this

-- `Cslib.ωSequence.nhds_cylinders` 3
theorem nhc3 : ¬ drop0% Cslib.ωSequence.nhds_cylinders 3 := fun h => by
  obtain ⟨ys, n, h1, h2⟩ := @h ℕ ⟨fun n => n⟩ ∅ isOpen_empty
  exact h2 h1

-- `Cslib.ωSequence.nhds_cylinders` 4
theorem nhc4 : ¬ drop0% Cslib.ωSequence.nhds_cylinders 4 := fun h => by
  obtain ⟨ys, n, h1, h2⟩ := @h Bool ⟨fun _ => true⟩ {⟨fun _ => true⟩} rfl
  rw [Cslib.ωSequence.cylinder_def] at h1 h2
  have : (⟨fun k => decide (k < n)⟩ : Cslib.ωSequence Bool) ∈ ({⟨fun _ => true⟩} : Set _) :=
    h2 (fun k hk => by rw [← h1 k hk]; simp [DFunLike.coe, hk])
  have := congrArg (fun xs : Cslib.ωSequence Bool => xs n) this
  simp [DFunLike.coe] at this

-- `Cslib.ωSequence.leadsTo_trans` 5
theorem lt5 : ¬ drop0% Cslib.ωSequence.leadsTo_trans 5 := fun h => by
  obtain ⟨k, -, hk⟩ := @h ℕ ⟨fun n => n⟩ Set.univ ∅ ∅ (fun k hk => hk.elim) 0 trivial
  exact hk

-- `Cslib.ωSequence.frequently_leadsTo_frequently` 5
theorem flf5 : ¬ drop0% Cslib.ωSequence.frequently_leadsTo_frequently 5 := fun h => by
  have := @h ℕ ⟨fun n => n⟩ Set.univ ∅ (Filter.Frequently.of_forall (fun _ => trivial))
  simp at this

-- `PFunctor.ext` 3
theorem pfe3 : ¬ drop0% PFunctor.ext 3 := fun h => by
  have e := @h ⟨Unit, fun _ => Unit⟩ ⟨Unit, fun _ => Empty⟩ rfl
  have c := congrArg (fun R : PFunctor.{0,0} => ∀ a : R.A, Nonempty (R.B a)) e
  have h2 : ∀ _ : Unit, Nonempty Empty := cast c (fun _ => ⟨()⟩)
  exact (h2 ()).elim (fun e => e.elim)

-- `Finset.card_div_two_le_card_filter_of_involution` 6
theorem cdt6 : ¬ drop0% Finset.card_div_two_le_card_filter_of_involution 6 := fun h => by
  have := @h ℕ {0, 1} (fun x => if x < 10 then x + 10 else x - 10) (fun x => 10 ≤ x) _
    (by decide) (by decide)
  exact absurd this (by decide)

-- `List.allButFirstLast_imp` 4
theorem abfl4 : ¬ drop0% List.allButFirstLast_imp 4 := fun h => by
  have := @h ℕ (fun _ => true) (fun _ => false) [0, 0, 0] (fun _ _ => rfl) 0 (by simp)
  simp at this

-- `Cslib.IsApplicativeHom.map_pure` 5
theorem amp5 : ¬ drop0% Cslib.IsApplicativeHom.map_pure 5 := fun h => by
  have := @h Option Option _ _ (fun _ => none) Unit ()
  simp at this

-- `Cslib.IsAlternativeHom.map_orElse` 5
theorem aoe5 : ¬ drop0% Cslib.IsAlternativeHom.map_orElse 5 := fun h => by
  have := @h Option (OptionT (StateM ℕ)) _ _
    (fun x => OptionT.mk (do modify (· + 1); pure x)) Unit none (fun _ => none)
  have := congrArg (fun z => (z.run.run 0).2) this
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.mk'` 8
theorem mhmk8 : ¬ drop0% Cslib.IsMonadHom.mk' 8 := fun h => by
  have hh := @h (StateM ℕ) (StateM ℕ) _ _ _ _ (fun x => (fun s => ((x.run s).1, s) : StateT ℕ Id _))
    (fun _ => rfl)
  have := congrArg (fun z => (z.run 0).1) (hh.map_bind (modify (· + 1)) (fun _ => get))
  exact absurd this (by decide)

-- `Cslib.IsMonadHom.map_orderedInsertM` 6
theorem moi6 : ¬ drop0% Cslib.IsMonadHom.map_orderedInsertM 6 := fun h => by
  have := @h Unit Option Option _ _ (fun _ => none) (fun _ _ => some true) () []
  simp [List.orderedInsertM] at this

-- `Cslib.IsMonadHom.map_listMergeM` 6
theorem mlm6 : ¬ drop0% Cslib.IsMonadHom.map_listMergeM 6 := fun h => by
  have := @h Option Option _ _ Unit (fun _ => none) [] [] (fun _ _ => some true)
  simp at this

-- `Cslib.IsMonadHom.map_pfunctorFreeMLiftM` 7
theorem mpf7 : ¬ drop0% Cslib.IsMonadHom.map_pfunctorFreeMLiftM 7 := fun h => by
  have := @h ⟨Unit, fun _ => Unit⟩ Option Unit _ Option _ (fun _ => none) (fun _ => some ()) (pure ())
  simp at this

-- `Cslib.Crypto.Protocols.SecretSharing.Scheme.not_authorized_of_subset` 7
theorem nas7 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Scheme.not_authorized_of_subset 7 :=
  fun h => @h Unit Unit Unit Unit
    { gen := PMF.pure (), share := fun _ _ _ => (), reconstruct := fun _ _ => (),
      authorized := fun s => s.Nonempty, authorized_mono := fun _ _ hst hs => hs.mono hst,
      correct := fun _ _ _ _ => rfl, view_indist := fun _ _ a b => by cases a; cases b; rfl }
    {()} ∅ (by simp) (by simp)

-- `Cslib.Crypto.Protocols.SecretSharing.Scheme.not_authorized_of_subset` 8
theorem nas8 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Scheme.not_authorized_of_subset 8 :=
  fun h => @h Unit Unit Unit Unit
    { gen := PMF.pure (), share := fun _ _ _ => (), reconstruct := fun _ _ => (),
      authorized := fun _ => True, authorized_mono := fun _ _ _ _ => trivial,
      correct := fun _ _ _ _ => rfl, view_indist := fun _ h => (h trivial).elim }
    ∅ ∅ (subset_refl _) trivial

-- ===== batch 2 =====

-- `Cslib.LTS.bddLang_eq_regex` 2
theorem bre2 : ¬ indep0% Cslib.LTS.bddLang_eq_regex 2 := fun h =>
  (Infinite.not_finite (α := ℕ)) (@h ℕ 1 0 ⟨fun _ _ _ => False⟩ 0 0)

-- `Cslib.Crypto.PRG.Generator.idealExperiment_leftReduction` 3
theorem iel3 : ¬ indep0% Cslib.Crypto.PRG.Generator.idealExperiment_leftReduction 3 := fun h => by
  obtain ⟨e⟩ := @h Empty Unit inferInstance inferInstance ⟨()⟩ ⟨Empty.elim⟩ (fun _ => PMF.pure true)
  exact e.elim

-- the interpretation of the empty signature is not complete
def emptyI : Cslib.Circuits.Interpretation ⟨Empty, Empty.elim⟩ Bool := fun op => op.elim
theorem emptySigNotComplete : ¬ Cslib.Circuits.Interpretation.IsComplete emptyI := by
  intro hc
  obtain ⟨c, -⟩ := hc.exists_computes_single (n := 0) (fun _ => true)
  rcases c with ⟨_ | ⟨p, ⟨op, _⟩⟩, out⟩
  · cases out 0 with
    | input i => exact i.elim0
    | gate g => exact g.elim0
  · exact op.elim

-- `Cslib.Circuits.exists_computes_size_eq_complexity` 6
theorem cx6 : ¬ indep0% Cslib.Circuits.exists_computes_size_eq_complexity 6 := fun h =>
  emptySigNotComplete (@h ⟨Empty, Empty.elim⟩ Bool 0 0 emptyI (fun _ _ => true))

-- `Cslib.Circuits.complexityOn_le_complexity` 7
theorem col7 : ¬ indep0% Cslib.Circuits.complexityOn_le_complexity 7 := fun h =>
  emptySigNotComplete (@h ⟨Empty, Empty.elim⟩ Bool 0 0 emptyI ∅ (fun _ _ => true))

-- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.correct` 5
theorem ecor5 : ¬ drop0% Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.correct 5 := fun h => by
  have := @h Bool Bool Bool
    { gen := PMF.pure true, enc := fun _ m => PMF.pure m, dec := fun k c => if k then c else !c,
      correct := fun k hk m c hc => by
        simp only [PMF.support_pure, Set.mem_singleton_iff] at hk hc; subst hk hc; rfl }
    false true true (by simp)
  simp at this

-- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.encrypt_key_injective` 6
theorem eki6 : ¬ drop0% _private.Cslib.Crypto.Protocols.PerfectSecrecy.Basic.«0».Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.encrypt_key_injective 6 := fun h => by
  have := @h Bool Bool (Option Bool)
    { gen := PMF.pure true, enc := fun k m => PMF.pure (if k then some m else none),
      dec := fun _ c => c.getD false,
      correct := fun k hk m c hc => by
        simp only [PMF.support_pure, Set.mem_singleton_iff] at hk hc; subst hk hc; rfl }
    (fun _ => false) none (by simp)
  exact absurd (@this false true rfl) (by decide)

-- `Cslib.Crypto.PRG.Family.not_exists_secure_bitVec_stretch` 2
theorem nes2 : ¬ drop0% Cslib.Crypto.PRG.Family.not_exists_secure_bitVec_stretch 2 := fun h => by
  apply @h id id
  refine ⟨fun n => ⟨id⟩, fun A _ => ?_⟩
  have : (fun n => (Cslib.Crypto.PRG.Generator.advantage ⟨id⟩ (A n))) = (0 : ℕ → ℝ) := by
    funext n
    refine le_antisymm ?_ (Cslib.Crypto.PRG.Generator.advantage_nonneg _ _)
    have := Cslib.Crypto.PRG.Generator.secure_zero_of_outputDist_eq (⟨id⟩ : Cslib.Crypto.PRG.Generator (BitVec n) (BitVec n))
      (by simp [Cslib.Crypto.PRG.Generator.outputDist]; exact PMF.map_id _) (fun _ => True) (A n) trivial
    simpa using this
  simp only [this]
  exact Asymptotics.superpolynomialDecay_zero _ _

-- FLP test algorithm: one process, never decides
def flpA : Cslib.FLP.Algorithm Unit Unit Unit := ⟨fun _ => (), fun _ _ => (), fun _ _ => 0, fun _ _ => none⟩
-- FLP test algorithm: one process, decides true on its first message
def flpT : Cslib.FLP.Algorithm Unit Unit Unit := ⟨fun _ => (), fun _ _ => (), fun _ _ => 0, fun _ _ => some true⟩
def flpS0 : Cslib.FLP.State Unit Unit Unit := ⟨0, fun _ => ⟨(), none⟩⟩
def flpS1 : Cslib.FLP.State Unit Unit Unit := ⟨{⟨(), .inl true⟩}, fun _ => ⟨(), none⟩⟩
def flpSd : Cslib.FLP.State Unit Unit Unit := ⟨0, fun _ => ⟨(), some true⟩⟩

-- restricted reachability through a set of no processes stays put
theorem flpCrvStay {P M S : Type} [DecidableEq P] [DecidableEq M] (a : Cslib.FLP.Algorithm P M S)
    {ps : Set P} (hps : ∀ p, p ∉ ps) {s t : Cslib.FLP.State P M S} (h : a.CanReachVia ps s t) :
    t = s := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨x, hx, ht⟩ := hst
    subst ih
    cases x with
    | none => exact ht
    | some m => exact absurd hx (hps _)

-- `Cslib.FLP.Algorithm.mTr_notRcvd_enabled` 11
theorem mne11 : ¬ drop0% Cslib.FLP.Algorithm.mTr_notRcvd_enabled 11 := fun h => by
  have := @h Unit Unit Unit _ _ flpA flpS0 flpS0 [] ⟨(), .inl true⟩ .refl (by simp)
  simp [flpS0] at this

-- `Cslib.FLP.Algorithm.tr_diamond` 15
theorem trd15 : ¬ drop0% Cslib.FLP.Algorithm.tr_diamond 15 := fun h => by
  obtain ⟨s', h1, h2⟩ := @h Unit Unit Unit _ _ flpA ∅ none none flpS0 flpS0 flpS1 trivial
    (by simp [Cslib.FLP.Algorithm.lts]) trivial
  simp only [Cslib.FLP.Algorithm.lts] at h1 h2
  have := congrArg (·.msgs) (h1.symm.trans h2)
  simp [flpS0, flpS1] at this

-- `Cslib.FLP.CanReachVia.stepL` 13
theorem crvs13 : ¬ drop0% Cslib.FLP.CanReachVia.stepL 13 := fun h => by
  have := flpCrvStay flpA (fun p hp => hp) (@h Unit Unit Unit _ _ flpA ∅ none flpS0 flpS0 flpS1 trivial
    (by simp [Cslib.FLP.Algorithm.lts]))
  have := congrArg (·.msgs) this
  simp [flpS0, flpS1] at this

-- `Cslib.FLP.OnePseudoConsensus.canDecideWithout_dest` 10
theorem cdwd10 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_dest 10 := fun h => by
  obtain ⟨s'', hr, p, hp⟩ := @h Unit Unit Unit _ _ flpA flpSd flpS0 ⟨(), .inl true⟩ true
    ⟨flpSd, .refl, ⟨(), rfl⟩⟩
  have := flpCrvStay flpA (by simp) hr
  subst this
  simp [flpS0, Cslib.FLP.State.ProcDecided] at hp

-- `Cslib.FLP.Consensus.fault_mono` 10
theorem fm10 : ¬ drop0% Cslib.FLP.Consensus.fault_mono 10 := fun h => by
  obtain ⟨hs, -⟩ := @h Unit Unit Unit _ _ flpT _ 0 0 le_rfl
  obtain ⟨-, h2⟩ := hs (fun _ => false) (flpT.recvMsg ⟨(), .inl false⟩ (flpT.start fun _ => false))
    ⟨[some ⟨(), .inl false⟩], .single _ ⟨by simp [Cslib.FLP.Algorithm.start], rfl⟩⟩
  obtain ⟨p, hp⟩ := h2 true ⟨(), by simp [Cslib.FLP.Algorithm.recvMsg, Cslib.FLP.Algorithm.start, flpT]⟩
  simp at hp

-- `Cslib.FLP.Consensus.ge_one_not_exists` 8
theorem gon8 : ¬ drop0% Cslib.FLP.Consensus.ge_one_not_exists 8 := fun h =>
  @h (Fin 2) Bool Unit _ _ _ 0 (by simp) ⟨_, Cslib.FLP.ZeroFaultAlg.consensus_zero (n := 2) (by decide)⟩

-- ===== batch 3 =====

open Cslib.DistributedConsistency in
-- an abstract execution on Bool with one session, rb = ar = (· < ·) and empty visibility
def aeB : AbstractExecution Bool Unit Unit Unit where
  op _ := ()
  se _ := ()
  rval _ := some ()
  rb := (· < ·)
  rb_strict_order := inferInstance
  rb_pred_finite _ := Set.toFinite _
  rb_interval_order := ⟨inferInstance, by decide⟩
  rb_rval_ne_none _ _ _ := by simp
  so_strict_total_order u := by
    cases u
    exact {
      trichotomous := by
        rintro ⟨a, -⟩ ⟨b, -⟩
        simp only [Cslib.DistributedConsistency.BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq,
          Subtype.mk.injEq, true_and]
        revert a b; decide
      irrefl := by
        rintro ⟨a, -⟩
        simp only [Cslib.DistributedConsistency.BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq,
          true_and]
        revert a; decide
      trans := by
        rintro ⟨a, -⟩ ⟨b, -⟩ ⟨c, -⟩
        simp only [Cslib.DistributedConsistency.BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq,
          true_and]
        revert a b c; decide }
  vis _ _ := False
  ar := (· < ·)
  vis_acyclic := ⟨fun a h => by
    cases h with
    | single h => exact h
    | tail _ h => exact h⟩
  vis_pred_finite _ := Set.toFinite _
  ar_strict_total_order := inferInstance

-- `Cslib.DistributedConsistency.readMyWrites_imp_hb_le_trans_vis` 5
theorem rmw5 : ¬ drop0% Cslib.DistributedConsistency.readMyWrites_imp_hb_le_trans_vis 5 := fun h => by
  have := @h Bool Unit Unit Unit aeB false true (.single (Or.inr ⟨(), rfl, rfl, Bool.false_lt_true⟩))
  cases this with
  | single h => exact h
  | tail _ h => exact h

-- `Cslib.DistributedConsistency.singleOrder_realTime_imp_readMyWrites` 5
theorem sor5 : ¬ drop0% Cslib.DistributedConsistency.singleOrder_realTime_imp_readMyWrites 5 := fun h =>
  @h Bool Unit Unit Unit aeB (fun _ _ h => h) () false true ⟨rfl, rfl, Bool.false_lt_true⟩

-- ===== batch 4 =====

-- a one-state machine with no work tapes that halts at once
noncomputable def tmU : Turing.MultiTapeTM 0 Bool Unit :=
  Turing.MultiTapeTM.ofTr () (fun _ _ _ => ⟨0, fun i => i.elim0, none, none⟩)
def encU : Unit ↪ List Bool := ⟨fun _ => [], fun _ _ _ => rfl⟩
def encU1 : Unit ↪ List Bool := ⟨fun _ => [true], fun _ _ _ => rfl⟩
def encB : Bool ↪ List Bool := ⟨fun b => [b], fun a b h => by simpa using h⟩

-- `Turing.MultiTapeTM.ComputesFunInTimeAndSpace.mono` 13
theorem cfm13 : ¬ drop0% Turing.MultiTapeTM.ComputesFunInTimeAndSpace.mono 13 := fun h => by
  have h1 := @h 0 Unit Bool tmU Unit Bool encU encB (fun _ => true) 0 0 0 0 (fun _ => le_rfl) (fun _ => le_rfl)
  have h2 := @h 0 Unit Bool tmU Unit Bool encU encB (fun _ => false) 0 0 0 0 (fun _ => le_rfl) (fun _ => le_rfl)
  obtain ⟨u1, hh1, ho1⟩ := (h1 ()).1
  obtain ⟨u2, hh2, ho2⟩ := (h2 ()).1
  have e1 := Turing.MultiTapeTM.runFrom_eq_of_halt tmU (tmU.initCfg (encU ())) (Nat.le_add_right u1 u2) hh1
  have e2 := Turing.MultiTapeTM.runFrom_eq_of_halt tmU (tmU.initCfg (encU ())) (Nat.le_add_left u2 u1) hh2
  have := ho1.symm.trans ((congrArg (·.output) e1).symm.trans ((congrArg (·.output) e2).trans ho2))
  simp [encB] at this

-- `Turing.MultiTapeTM.ComputesFunTidilyInTimeAndSpace.mono` 13
theorem ctm13 : ¬ drop0% Turing.MultiTapeTM.ComputesFunTidilyInTimeAndSpace.mono 13 := fun h => by
  have h1 := @h 0 Bool Unit tmU Unit Bool encU encB (fun _ => true) 0 0 0 0 (fun _ => le_rfl) (fun _ => le_rfl)
  obtain ⟨p, hh, hl, ht, -⟩ := Turing.MultiTapeTM.computesTidily_iff.mp (h1 ())
  have hl0 : p.length = 0 := by simpa [Turing.MultiTapeNTM.RunPath.time] using ht
  have e : p.last = Turing.MultiTapeTM.runFrom (tm := tmU) p.head p.length :=
    Turing.MultiTapeTM.runPath_apply_eq_runFrom p (Fin.last _)
  rw [hl0, hl, hh] at e
  have := congrArg (·.state) e
  simp [Turing.MultiTapeTM.runFrom, Turing.wordsCfg] at this

-- `Turing.MultiTapeTM.runFrom_eq_of_halt` 8
theorem rfh8 : ¬ drop0% Turing.MultiTapeTM.runFrom_eq_of_halt 8 := fun h => by
  have hs : (tmU.step (tmU.initCfg [])).state = none := by
    rw [Turing.MultiTapeTM.step_of_state (q := ()) rfl]
    simp [tmU, Turing.Action.apply]
  have := congrArg (·.state) (@h 0 Unit Bool [] tmU (tmU.initCfg []) 1 0 hs)
  change (tmU.initCfg []).state = (tmU.step (tmU.initCfg [])).state at this
  rw [hs] at this
  cases this

-- `Turing.MultiTapeTM.Copy.runFrom_scan` 3
theorem crs3 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id.«0».Turing.MultiTapeTM.Copy.runFrom_scan 3 := fun h => by
  have e1 := @h Bool [] 1
  have e2 := (priv% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id.«0».Turing.MultiTapeTM.Copy.runFrom_full) ([] : List Bool)
  have := congrArg (·.state) (e1.symm.trans e2)
  cases this

-- `Turing.MultiTapeTM.runFrom_read` 10
theorem rfr10 : ¬ indep0% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant.«0».Turing.MultiTapeTM.runFrom_read 10 := fun h => by
  have := @h Unit Unit encU1 encU1 id ∅ [] () 1 (le_refl 1)
  exact absurd this (by decide)

-- ===== batch 5 =====

-- `Cslib.Automata.NA.totalize_run_mtr` 7
theorem trm7 : ¬ drop0% Cslib.Automata.NA.totalize_run_mtr 7 := fun h => by
  obtain ⟨s, t, -, -, -, ht⟩ := @h Unit Unit ⟨⟨fun _ _ _ => False⟩, {()}⟩ ⟨fun _ => ()⟩
    ⟨fun n => if n = 0 then some () else none⟩ 1
    ⟨by simp [Cslib.Automata.NA.totalize, DFunLike.coe],
     fun i => by cases i <;> simp [Cslib.Automata.NA.totalize, Cslib.LTS.totalize, DFunLike.coe]⟩
  simp [DFunLike.coe] at ht

-- `Cslib.Automata.TwoWayNA.mTr_take_of_mTr_toCfgNA` 8
theorem tw8 : ¬ drop0% Cslib.Automata.TwoWayNA.mTr_take_of_mTr_toCfgNA 8 := fun h => by
  have := @h Unit Unit [()] ⟨⟨⟨fun _ _ _ => False⟩, {()}⟩, ∅⟩ ⟨[()], (), 0⟩ ⟨[()], (), 1⟩ []
    ⟨rfl, rfl, rfl⟩
  simp at this

-- ===== batch 6 =====

-- `Cslib.FreeM.exists_mem_countQueries_ge_clog` 3
theorem fmc3 : ¬ drop0% _private.Cslib.Algorithms.Lean.Query.FreeM.«0».Cslib.FreeM.exists_mem_countQueries_ge_clog 3 := fun h => by
  obtain ⟨i, -, hi⟩ := @h (fun ρ => Fin 4 → ρ) (Fin 4) 2 (Fin 4) (.liftBind (ι := Fin 4) id .pure)
    Finset.univ Finset.univ_nonempty (fun i {_} g => g i)
    (by intro a _ b _ hab; simpa using hab)
  simp only [Finset.card_univ, Fintype.card_fin] at hi
  change 1 ≥ Nat.clog 2 4 at hi
  have : Nat.clog 2 4 = 2 := Nat.clog_pow 2 2 (by norm_num)
  omega

-- no zero-gate circuit computes negation on one input
theorem noZeroNot {σ : Cslib.Circuits.Signature} (I : Cslib.Circuits.Interpretation σ Bool)
    (c : Cslib.Circuits.Circuit σ 1 1) (hs : c.size = 0)
    (hc : c.ComputesOn I Set.univ (fun x _ => !x 0)) : False := by
  rcases c with ⟨_ | ⟨p, l⟩, out⟩
  · have := congrFun (hc (Set.mem_univ (fun _ => true))) 0
    cases h : out 0 with
    | input i => simp [Cslib.Circuits.Circuit.eval, h] at this
    | gate g => exact g.elim0
  · simp at hs

-- `Cslib.Circuits.le_size_of_le_complexity` 10
theorem lsc10 : ¬ drop0% Cslib.Circuits.le_size_of_le_complexity 10 := fun h => by
  have := @h _ Bool 1 1 Cslib.Circuits.Boolean.interpretation (fun x _ => !x 0) 1 _
    (Cslib.Circuits.le_complexityOn_iff.mpr fun c hc => by
      by_contra hlt
      exact noZeroNot _ c (by omega) hc) (Cslib.Circuits.Circuit.id _ 1)
  simp at this

-- `Cslib.Circuits.Circuit.ComputesOn.simulation` 10
theorem cos10 : ¬ drop0% Cslib.Circuits.Circuit.ComputesOn.simulation 10 := fun h => by
  obtain ⟨d, hd⟩ := @h ⟨Empty, Empty.elim⟩ ⟨Empty, Empty.elim⟩ Bool (fun op => op.elim) (fun op => op.elim)
    1 1 (Cslib.Circuits.Circuit.id _ 1) Set.univ (fun x _ => !x 0) ⟨fun _ => 0, fun op => op.elim⟩
  refine noZeroNot _ d ?_ hd
  rcases d with ⟨_ | ⟨p, ⟨op, _⟩⟩, out⟩
  · rfl
  · exact op.elim

-- ===== batch 7 =====

-- halted configurations with zero and one work tape
def ntmH0 : Turing.MultiTapeNTM 0 Bool Unit := ⟨(), fun _ _ _ _ => False⟩
def ntmH1 : Turing.MultiTapeNTM 1 Bool Unit := ⟨(), fun _ _ _ _ => False⟩
def cfgH0 : Turing.Cfg 0 Bool Unit [] := ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
def cfgH1 : Turing.Cfg 1 Bool Unit [] := ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩

-- `Turing.MultiTapeNTM.RunPath.space_map_le` 14
theorem sml14 : ¬ drop0% Turing.MultiTapeNTM.RunPath.space_map_le 14 := fun h => by
  have := @h 0 1 Unit Unit Bool [] [] ntmH0 ntmH1 (RelSeries.singleton _ cfgH0)
    ⟨fun _ => cfgH1, fun _ => rfl⟩ ⟨Fin.elim0, fun i => i.elim0⟩ (fun _ => ∅) (fun _ _ j => j.elim0)
  simp [Turing.MultiTapeNTM.RunPath.space, Turing.MultiTapeNTM.RunPath.spaceUsedByTape,
    Turing.MultiTapeNTM.RunPath.visitedByTapeHead] at this
  exact Finset.univ_nonempty.ne_empty this

-- `Cslib.Automata.NA.Buchi.frequently_via_accept` 9
theorem fva9 : ¬ drop0% _private.Cslib.Computability.Languages.Congruences.BuchiCongruence.«0».Cslib.Automata.NA.Buchi.frequently_via_accept 9 := fun h => by
  have hc : ∀ k, Cslib.ωSequence.cumLen (⟨fun _ => []⟩ : Cslib.ωSequence (List Unit)) k = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [Cslib.ωSequence.cumLen, ih, DFunLike.coe]
  have := @h Unit Bool ⟨⟨⟨fun _ _ _ => True⟩, Set.univ⟩, {true}⟩ _ [] ⟨fun _ => []⟩
    ⟨fun k => decide (k ≠ 0)⟩
    (Filter.Eventually.frequently (Filter.eventually_atTop.mpr ⟨1, fun k hk => by
      simp [DFunLike.coe]; omega⟩))
    (fun _ => trivial)
  simp only [hc, List.length_nil, Nat.add_zero] at this
  simp [DFunLike.coe] at this

-- a three-state cycle 0 → 2 → 1 → 0
def lts3 : Cslib.LTS (Fin 3) Unit :=
  ⟨fun i _ j => (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0)⟩

-- `Cslib.LTS.splitFirst_mem` 9
theorem sfm9 : ¬ drop0% Cslib.LTS.splitFirst_mem 9 := fun h => by
  have hex : lts3.Execution 0 [(), (), ()] 0 [0, 2, 1, 0] :=
    .stepL (Or.inl ⟨rfl, rfl⟩) (.stepL (Or.inr (Or.inl ⟨rfl, rfl⟩)) (.stepL (Or.inr (Or.inr ⟨rfl, rfl⟩)) (.refl _)))
  have hnb : ¬ List.AllButFirstLast (fun x => decide (x < (1 : Fin 3))) [0, 2, 1, 0] := by
    simp [List.AllButFirstLast]
  obtain ⟨h1, -⟩ := @h Unit 3 lts3 0 0 1 [(), (), ()] [0, 2, 1, 0] hex hnb
  have e : Cslib.LTS.splitFirstTake [(), (), ()] ([0, 2, 1, 0] : List (Fin 3)) 1 = [(), ()] := by
    decide
  rw [e] at h1
  obtain ⟨ss, hex', hb⟩ := h1
  cases hex' with
  | stepL htr hex2 =>
    cases hex2 with
    | stepL htr2 hex3 =>
      cases hex3 with
      | refl =>
        simp [lts3, List.AllButFirstLast] at htr htr2 hb
        omega

-- ===== batch 8 =====

open Cslib.FLP in
-- two processes; only process false decides (the value of the first input-tagged message it gets);
-- process true forwards its input to process false
def flpN : Algorithm Bool Unit Unit where
  init _ := ()
  next _ _ := ()
  send m _ := if m.dest = true then (match m.msg with | .inl b => {⟨false, .inl b⟩} | .inr _ => 0) else 0
  out m _ := if m.dest = false then (match m.msg with | .inl b => some b | .inr _ => none) else none

open Cslib.FLP in
theorem flpN_tr_true {t u : State Bool Unit Unit} {x : Action Bool Unit} (h : flpN.lts.Tr t x u)
    (ht : (t.proc true).out = none) : (u.proc true).out = none := by
  cases x with
  | none => cases h; exact ht
  | some m =>
    obtain ⟨-, rfl⟩ := h
    rcases m with ⟨d, msg⟩
    cases d <;> simp_all [Algorithm.recvMsg, flpN]

open Cslib.FLP in
theorem flpN_mtr_true {t u : State Bool Unit Unit} {μs : List (Action Bool Unit)}
    (h : flpN.lts.MTr t μs u) (ht : (t.proc true).out = none) : (u.proc true).out = none := by
  induction h with
  | refl => exact ht
  | stepL htr _ ih => exact ih (flpN_tr_true htr ht)

open Cslib.FLP in
theorem flpN_crv_false {t u : State Bool Unit Unit} (h : flpN.CanReachVia {false}ᶜ t u) :
    u.proc false = t.proc false := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨x, hx, htr⟩ := hst
    rw [← ih]
    cases x with
    | none => cases htr; rfl
    | some m =>
      obtain ⟨-, rfl⟩ := htr
      rcases m with ⟨d, msg⟩
      cases d
      · simp [DestIn] at hx
      · simp [Algorithm.recvMsg]

open Cslib.FLP in
-- `Cslib.FLP.OnePseudoConsensus.nonUniform_step` 8
theorem nus8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.nonUniform_step 8 := fun h => by
  let inp : Bool → Bool := id
  let s := flpN.recvMsg ⟨true, .inl true⟩ (flpN.start inp)
  have hmem : ∀ b, (⟨false, .inl b⟩ : Message Bool Unit) ∈ s.msgs := by
    intro b; cases b <;> decide
  have hs : (s.proc true).out = none := by simp [s, Algorithm.recvMsg, Algorithm.start, flpN]
  have hsf : (s.proc false).out = none := by simp [s, Algorithm.recvMsg, Algorithm.start]
  have hr : flpN.Reachable inp s := ⟨[some ⟨true, .inl true⟩], .single _ ⟨by decide, rfl⟩⟩
  have hn : flpN.NonUniform s := fun b => ⟨true, flpN.recvMsg ⟨false, .inl b⟩ s,
    .single ⟨some ⟨false, .inl b⟩, by simp [DestIn], hmem b, rfl⟩,
    ⟨false, by simp [Algorithm.recvMsg, hsf, flpN, State.ProcDecided]⟩⟩
  obtain ⟨s', ⟨μs, hm⟩, hb⟩ := @h Bool Unit Unit _ _ flpN inp _ s hr hn false
  have hs' := flpN_mtr_true hm hs
  have key : ∀ b, (s'.proc false).out = some b := by
    intro b
    obtain ⟨u, hu, q, hq⟩ := hb b
    have hut : (u.proc true).out = none := by
      obtain ⟨ν, hν⟩ := CanReachVia.canReach hu
      exact flpN_mtr_true hν hs'
    cases q
    · rw [← flpN_crv_false hu]; exact hq
    · have hq' : (u.proc true).out = some b := hq
      rw [hut] at hq'; cases hq'
  have := (key true).symm.trans (key false)
  simp at this
