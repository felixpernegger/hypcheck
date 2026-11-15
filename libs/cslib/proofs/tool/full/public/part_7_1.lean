import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Cslib.LTS.IsBisimulation.follow_fst, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Cslib.LTS.IsBisimulation.follow_fst.h10.inst : ¬∃ (s₂' : ℕ),
        { Tr := fun (a : ℕ) (a_1 : Bool) (n : ℕ) => n = 0 : Cslib.LTS ℕ Bool }.Tr 1 Bool.false s₂' ∧
          (fun (a b : ℕ) => a < b) 0 s₂' := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Cslib.LTS.IsBisimulation.follow_fst.h10.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Cslib.LTS.IsBisimulation.follow_fst.h10.prem1 : { Tr := fun (a : ℕ) (a_1 : Bool) (n : ℕ) => n = 0 : Cslib.LTS ℕ Bool }.Tr 0 Bool.false 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Cslib.LTS.IsBisimulation.follow_fst.h10 : ¬∀ {State₁ State₂ Label : Type} {lts₁ : Cslib.LTS State₁ Label} {lts₂ : Cslib.LTS State₂ Label}
        {r : State₁ → State₂ → Prop} {s₁ : State₁} {s₂ : State₂} {μ : Label} {s₁' : State₁},
        r s₁ s₂ → lts₁.Tr s₁ μ s₁' → ∃ (s₂' : State₂), lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂' := fun hc_h => HypCheckProof.Cslib.LTS.IsBisimulation.follow_fst.h10.inst (@hc_h (ℕ) (ℕ) (Bool) ({ Tr := fun (a : ℕ) (a_1 : Bool) (n : ℕ) => n = 0 : Cslib.LTS ℕ Bool }) ({ Tr := fun (a : ℕ) (a_1 : Bool) (n : ℕ) => n = 0 : Cslib.LTS ℕ Bool }) (fun (a b : ℕ) => a < b) (0) (1) (Bool.false) (0) HypCheckProof.Cslib.LTS.IsBisimulation.follow_fst.h10.prem0 HypCheckProof.Cslib.LTS.IsBisimulation.follow_fst.h10.prem1)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.swap_open, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.swap_open.h7 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] (k n : ℕ) (t₁ t₂ m : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        t₁.LC →
          t₂.LC →
            Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec k t₁
                (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec n t₂ m) =
              Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec n t₂
                (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec k t₁ m) := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (0) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 1 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Cslib.LTS.DeterministicStateLabel.not_tr_of_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.DeterministicStateLabel.not_tr_of_ne.h7 : ¬∀ {State Label : Type} (lts : Cslib.LTS State Label) {s : State} {μ : Label} {s₁ s₂ : State},
        s₁ ≠ s₂ → lts.Tr s μ s₁ → ¬lts.Tr s μ s₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 ≤ b : Cslib.LTS ℕ ℕ }) (0) (0) (0) (1) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Relation.RelatesInSteps.map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesInSteps.map.h5 : ¬∀ {α α' : Type} {r : α → α → Prop} {r' : α' → α' → Prop} (g : α → α') {a b : α} {n : ℕ},
        Relation.RelatesInSteps r a b n → Relation.RelatesInSteps r' (g a) (g b) n := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ _ => True : Bool → Bool → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (fun b => if b then 1 else 0 : Bool → ℕ) (Bool.false) (Bool.false) (1) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Relation.RelatesInSteps.map, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesInSteps.map.h9 : ¬∀ {α α' : Type} {r : α → α → Prop} {r' : α' → α' → Prop} (g : α → α'),
        (∀ (a b : α), r a b → r' (g a) (g b)) → ∀ {a b : α} {n : ℕ}, Relation.RelatesInSteps r' (g a) (g b) n := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) (by
  simp) (0) (1) (0)) (by
  simp)

-- Set.SymmOn.of_cod, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.SymmOn.of_cod.h5.inst : ¬(fun (a b : ℕ) => a ≤ b) 1 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.SymmOn.of_cod.h5.prem0 : (fun (a b : ℕ) => a ≤ b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.SymmOn.of_cod.h5.prem1 : (fun (a b : ℕ) => a ≤ b) 0 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.SymmOn.of_cod.h5 : ¬∀ {α : Type} {a b c : α} {r : α → α → Prop}, r a b → r c a → r b a := fun hc_h => HypCheckProof.Set.SymmOn.of_cod.h5.inst (@hc_h (ℕ) (0) (1) (0) (fun (a b : ℕ) => a ≤ b) HypCheckProof.Set.SymmOn.of_cod.h5.prem0 HypCheckProof.Set.SymmOn.of_cod.h5.prem1)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.trans_redex, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.trans_redex.h6 : ¬∀ {Var : Type} {M N P : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var],
        Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta P N → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  rfl)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.trans_redex, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.trans_redex.h7 : ¬∀ {Var : Type} {M N P : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], M.Standard P → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.weaken_head, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.weaken_head.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ σ' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        (Γ ++ Δ).Wf → Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub (Γ ++ Δ) σ σ' := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.Automata.TwoWayNA.IsRejectionCert.start_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.TwoWayNA.IsRejectionCert.start_mem.h5 : ¬∀ {State Symbol : Type} {a : Cslib.Automata.TwoWayNA State Symbol} {input : List Symbol}
        {cert : Cslib.ωSequence (Set State)}, ∀ s ∈ a.start, s ∈ cert 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (q x : ℕ) (m : SignType) (n : ℕ) => n = 0, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.TwoWayNA ℕ ℕ }) ([]) ({ get := fun (a : ℕ) => {x : ℕ | False} : Cslib.ωSequence (Set ℕ) }) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.standardization, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.standardization.h5 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var],
        Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta M N → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  rfl)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.standardization, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.standardization.h6 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], M.LC → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_beta_step, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_beta_step.h5 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], M.LC → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_lc_r, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_lc_r.h5 : ¬∀ {Var : Type} {M M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : DecidableEq Var]
        [inst : Cslib.HasFresh Var], M.LC → M'.LC := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_lc_r, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_lc_r.h6 : ¬∀ {Var : Type} {M M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : DecidableEq Var]
        [inst : Cslib.HasFresh Var],
        Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost M M' → M'.LC := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (by
  rfl)) (by
  nofun)

-- Relation.Join₂.single_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Join₂.single_right.h5 : ¬∀ {α : Type} {r₁ r₂ : α → α → Prop} {a b : α}, r₂ a b → Relation.Join₂ r₁ r₂ b a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a = b : ℕ → ℕ → Prop) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  nofun)

-- Relation.Join₂.single_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Join₂.single_right.h6 : ¬∀ {α : Type} {r₁ r₂ : α → α → Prop} {a b : α} [inst : Std.Refl r₁], Relation.Join₂ r₁ r₂ b a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) _) (by
  nofun)

-- Cslib.LTS.Execution.cons_cons_invert, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.cons_cons_invert.h10 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {r : State} {μ : Label} {μs : List Label} {t : State} {r' : State}
        {s : State} {ss : List State}, lts.Execution s μs t (s :: ss) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) ([]) (0) (0) (0) ([0])) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.refl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.refl.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}, Γ.Wf → Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ σ σ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Set.ReflOn.of_cod, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.ReflOn.of_cod.h4.inst : ¬(fun (a b : ℕ) => a < b) 1 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.ReflOn.of_cod.h4.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.ReflOn.of_cod.h4 : ¬∀ {α : Type} {a b : α} {r : α → α → Prop}, r a b → r b b := fun hc_h => HypCheckProof.Set.ReflOn.of_cod.h4.inst (@hc_h (ℕ) (0) (1) (fun (a b : ℕ) => a < b) HypCheckProof.Set.ReflOn.of_cod.h4.prem0)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.cbn_trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.cbn_trans.h4 : ¬∀ {Var : Type} {M N P : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, P.Standard N → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.cbn_trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.cbn_trans.h5 : ¬∀ {Var : Type} {M N P : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var},
        Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN M P → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  rfl)) (by
  nofun)

-- Relation.Join.single, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Join.single.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} [inst : Std.Refl r], Relation.Join r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (0) (1) _) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.open_subst, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.open_subst.h6 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var]
        {δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} (σ τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var)
        (X : Var), (σ.open' τ)[X := δ] = σ[X := δ].open' τ[X := δ] := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0)) (by
  nofun)

-- Turing.Storage.FitsIn.pos_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.Storage.FitsIn.pos_le.h5 : ¬∀ {k : ℕ} {State Symbol : Type} {x : Turing.Storage Symbol State k} {w : Fin k → ℕ} (j : Fin k),
        (x.workTapePos j).natAbs ≤ w j := fun hc_h => absurd (@hc_h (1) (ℕ) (ℕ) ({ state := Option.none, workTapes := fun (i : Fin 1) (a : ℤ) => Option.none, workTapePos := fun (i : Fin 1) => 1 :
      Turing.Storage ℕ ℕ 1 }) (fun (a : Fin 1) => 0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Cslib.LTS.Execution.of_mTr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.of_mTr.h6 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State},
        ∃ (ss : List State), lts.Execution s μs t ss := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (1)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_intro_openRec, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_intro_openRec.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] {x : Var} {t e : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {k : ℕ},
        Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec k t e =
          (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec k
              (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) e)[x :=
            t] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0)) (by
  decide +kernel)

-- Cslib.ωSequence.extract_append_right_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.extract_append_right_right.h5 : ¬∀ {α : Type} {xl : List α} {xs : Cslib.ωSequence α} {m n : ℕ},
        (xl ++ω xs).extract m n = xs.extract (m - xl.length) (n - xl.length) := fun hc_h => absurd (@hc_h (ℕ) ([0]) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (0) (1)) (by
  decide +kernel)

-- Relation.of_dom, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.of_dom.h5 : ¬∀ {α β : Type} {r : α → β → Prop} {a : α} {b : β}, a ∈ Relation.dom r := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun (a : ℕ) (x : Bool) => False) (0) (Bool.false)) (by
  nofun)

-- List.IsChainFromTo.head_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.head_eq.h5 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b : α}, List.IsChainFromTo r chain a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (0)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.lc_r, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.lc_r.h5 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var],
        N.LC := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat)) (by
  nofun)

-- Turing.MultiTapeTM.partialInv_eq_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.partialInv_eq_some.h5 : Not
      (∀ {k k' : Nat} (e : Function.Embedding (Fin k) (Fin k')) {l : Fin k'} {j : Fin k},
        @Eq (Fin k')
          (@DFunLike.coe (Function.Embedding (Fin k) (Fin k')) (Fin k) (fun (x : Fin k) => Fin k')
            (@Function.instFunLikeEmbedding (Fin k) (Fin k')) e j)
          l) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Function.Embedding.mk (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (fun (a : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
        @Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@of_decide_eq_true
            (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@id
              (@Eq Bool
                (@Decidable.decide
                  (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                Bool.true)
              (@Eq.refl Bool Bool.true))))
      (@of_decide_eq_true
        (@Function.Injective (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          fun (a : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
          @Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@of_decide_eq_true
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  Bool.true)
                (@Eq.refl Bool Bool.true))))
        (@Fintype.decidableInjectiveFintype (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          fun (a : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
          @Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@of_decide_eq_true
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  Bool.true)
                (@Eq.refl Bool Bool.true))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Function.Injective (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                fun (a : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                @Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@of_decide_eq_true
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@id
                      (@Eq Bool
                        (@Decidable.decide
                          (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        Bool.true)
                      (@Eq.refl Bool Bool.true))))
              (@Fintype.decidableInjectiveFintype (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin.fintype (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                fun (a : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                @Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@of_decide_eq_true
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@id
                      (@Eq Bool
                        (@Decidable.decide
                          (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        Bool.true)
                      (@Eq.refl Bool Bool.true)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Cslib.LTS.Total.total, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Total.total.h3 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} (s : State) (μ : Label), ∃ (s' : State), lts.Tr s μ s' := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({ Tr := fun (a : ℕ) (a_1 : Bool) (x : ℕ) => False : Cslib.LTS ℕ Bool }) (0) (Bool.false)) (by
  simp)

-- Cslib.ωSequence.take_get, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.take_get.h4 : ¬∀ {α : Type} (m n : ℕ) (a : Cslib.ωSequence α), m < (Cslib.ωSequence.take n a).length := fun hc_h => absurd (@hc_h (ℕ) (0) (0) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ })) (by
  decide +kernel)

-- Turing.MultiTapeTM.partialInv_eq_none, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.MultiTapeTM.partialInv_eq_none.h4 : Not
      (∀ {k k' : Nat} (e : Function.Embedding (Fin k) (Fin k')) {l : Fin k'},
        @Eq (Option (Fin k)) (@Turing.MultiTapeTM.partialInv k k' e l) (@Option.none (Fin k))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Function.Embedding.mk (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (fun (a : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
        @Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@of_decide_eq_true
            (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@id
              (@Eq Bool
                (@Decidable.decide
                  (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bool.true)
              (@Eq.refl Bool Bool.true))))
      (@of_decide_eq_true
        (@Function.Injective (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          fun (a : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
          @Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@of_decide_eq_true
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bool.true)
                (@Eq.refl Bool Bool.true))))
        (@Fintype.decidableInjectiveFintype (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          fun (a : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
          @Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@of_decide_eq_true
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bool.true)
                (@Eq.refl Bool Bool.true))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Function.Injective (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                fun (a : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                @Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@of_decide_eq_true
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@id
                      (@Eq Bool
                        (@Decidable.decide
                          (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        Bool.true)
                      (@Eq.refl Bool Bool.true))))
              (@Fintype.decidableInjectiveFintype (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (Fin.fintype (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                fun (a : Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                @Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@of_decide_eq_true
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@id
                      (@Eq Bool
                        (@Decidable.decide
                          (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        Bool.true)
                      (@Eq.refl Bool Bool.true)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Cslib.ωSequence.flatten_get_cumLen, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.flatten_get_cumLen.h4 : ¬∀ {α : Type} [inst : Inhabited α] (ls : Cslib.ωSequence (List α)) {n : ℕ} (n : ℕ), 0 < (ls n).length := fun hc_h => absurd (@hc_h (ℕ) (instInhabitedNat) ({ get := fun (x : ℕ) => [] : Cslib.ωSequence (List ℕ) }) (0)) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.Value.lc, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.Value.lc.h2 : ¬∀ {Var : Type} {t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var}, t.LC := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ)) (by
  nofun)

-- Cslib.SKI.Ka_irreducible, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.Ka_irreducible.h2 : ¬∀ (a c : Cslib.SKI), ∃ (a' : Cslib.SKI), a.ParallelReduction a' ∧ c = Cslib.SKI.K.app a' := fun hc_h => absurd (@hc_h (.S : Cslib.SKI) (.S : Cslib.SKI)) (by
  simp)

-- Cslib.FLP.ZeroFaultAlg.inv_start, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.FLP.ZeroFaultAlg.inv_start.h1 : ¬∀ {n : ℕ} (inp : Fin n → Bool), 0 < n := fun hc_h => absurd (@hc_h (0) (fun (a : Fin 0) => Bool.false)) (by
  decide +kernel)

