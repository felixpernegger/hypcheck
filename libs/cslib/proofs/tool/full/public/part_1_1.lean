import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst.h7 : ¬∀ {Var : Type} {M M' N N' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], N.Standard N' → ∀ (x : Var), N.LC → N'.LC → M[x := N].Standard M'[x := N'] := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done) (0) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst.h8 : ¬∀ {Var : Type} {M M' N N' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], M.Standard M' → ∀ (x : Var), N.LC → N'.LC → M[x := N].Standard M'[x := N'] := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 1 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done) (0) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LTS.IsSimulation.follow, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Cslib.LTS.IsSimulation.follow.h10.inst : ¬∃ (s₂' : ℕ),
        { Tr := fun (a : ℕ) (a_1 : Bool) (n : ℕ) => n = 0 : Cslib.LTS ℕ Bool }.Tr 1 Bool.false s₂' ∧
          (fun (a b : ℕ) => a < b) 0 s₂' := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Cslib.LTS.IsSimulation.follow.h10.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Cslib.LTS.IsSimulation.follow.h10.prem1 : { Tr := fun (a : ℕ) (a_1 : Bool) (n : ℕ) => n = 0 : Cslib.LTS ℕ Bool }.Tr 0 Bool.false 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Cslib.LTS.IsSimulation.follow.h10 : ¬∀ {State Label : Type} {lts₁ : Cslib.LTS State Label} {State_1 : Type} {lts₂ : Cslib.LTS State_1 Label}
        {r : State → State_1 → Prop} {s₁ : State} {s₂ : State_1} {μ : Label} {s₁' : State},
        r s₁ s₂ → lts₁.Tr s₁ μ s₁' → ∃ (s₂' : State_1), lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂' := fun hc_h => HypCheckProof.Cslib.LTS.IsSimulation.follow.h10.inst (@hc_h (ℕ) (Bool) ({ Tr := fun (a : ℕ) (a_1 : Bool) (n : ℕ) => n = 0 : Cslib.LTS ℕ Bool }) (ℕ) ({ Tr := fun (a : ℕ) (a_1 : Bool) (n : ℕ) => n = 0 : Cslib.LTS ℕ Bool }) (fun (a b : ℕ) => a < b) (0) (1) (Bool.false) (0) HypCheckProof.Cslib.LTS.IsSimulation.follow.h10.prem0 HypCheckProof.Cslib.LTS.IsSimulation.follow.h10.prem1)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.map_subst, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.map_subst.h10 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ τ δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} [inst_1 : Cslib.HasFresh Var] {X : Var}
        {δ' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Δ δ δ' →
          Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub
            (Cslib.LambdaCalculus.LocallyNameless.Context.mapVal
                (fun (x : Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) => x[X := δ]) Γ ++
              Δ)
            σ[X := δ] τ[X := δ] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (Cslib.instHasFreshNat) (1) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Relation.RelatesWithinSteps.map, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesWithinSteps.map.h9 : ¬∀ {α α' : Type} {r : α → α → Prop} {r' : α' → α' → Prop} (g : α → α'),
        (∀ (a b : α), r a b → r' (g a) (g b)) → ∀ {a b : α} {n : ℕ}, Relation.RelatesWithinSteps r' (g a) (g b) n := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) (by
  simp) (0) (1) (0)) (by
  simp)

-- Cslib.LTS.MTr.stepR, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.MTr.stepR.h9 : ¬∀ {State Label : Type} (lts : Cslib.LTS State Label) {s1 : State} {μs : List Label} {s2 : State} {μ : Label}
        {s3 : State}, lts.MTr s1 μs s2 → lts.MTr s1 (μs ++ [μ]) s3 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) (0) (0) (by
  simp)) (by
  simp)

-- Cslib.LTS.pairLang_append, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.pairLang_append.h8 : ¬∀ {Symbol State : Type} {lts : Cslib.LTS State Symbol} {s0 s1 s2 : State} {xs1 xs2 : List Symbol},
        xs2 ∈ lts.pairLang s1 s2 → xs1 ++ xs2 ∈ lts.pairLang s0 s2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) (0) ([0]) ([]) (by
  simp)) (by
  simp)

-- Cslib.LTS.pairLang_append, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.pairLang_append.h9 : ¬∀ {Symbol State : Type} {lts : Cslib.LTS State Symbol} {s0 s1 s2 : State} {xs1 xs2 : List Symbol},
        xs1 ∈ lts.pairLang s0 s1 → xs1 ++ xs2 ∈ lts.pairLang s0 s2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) (0) ([]) ([0]) (by
  simp)) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.weaken_head, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.weaken_head.h7 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var]
        {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var} {τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}
        {t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var},
        (Γ ++ Δ).Wf → Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing (Γ ++ Δ) t τ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) ([]) ([]) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.abs .top (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_open_var, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_open_var.h7 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var] (x y : Var)
        (u e : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        u.LC →
          (e.open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x))[y := u] =
            e[y := u].open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (1) (1) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_open_var, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_open_var.h8 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var] (x y : Var)
        (u e : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        y ≠ x →
          (e.open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x))[y := u] =
            e[y := u].open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (1) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.close_openRec_to_subst, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.close_openRec_to_subst.h7 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var]
        (m n : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (x : Var) (k : ℕ),
        n.LC →
          Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec k n
              (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.closeRec k x m) =
            m[x := n] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.swap_open_fvar_close, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.swap_open_fvar_close.h7 : ¬∀ {Var : Type} [inst : DecidableEq Var] (k n : ℕ) (x y : Var)
        (m : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        x ≠ y →
          Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.closeRec k x
              (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec n
                (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar y) m) =
            Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec n
              (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar y)
              (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.closeRec k x m) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0) (0) (1) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.swap_open_fvar_close, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.swap_open_fvar_close.h8 : ¬∀ {Var : Type} [inst : DecidableEq Var] (k n : ℕ) (x y : Var)
        (m : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        k ≠ n →
          Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.closeRec k x
              (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec n
                (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar y) m) =
            Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec n
              (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar y)
              (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.closeRec k x m) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (1) (0) (0) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  decide)) (by
  decide +kernel)

-- List.IsChainFromTo.of_cons_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.of_cons_cons.h7 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a : α} {b : α} {x : α} {y : α}, List.IsChainFromTo r (y :: chain) y b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (0) (0) (1)) (by
  nofun)

-- Turing.card_boundedStorage_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.card_boundedStorage_le.h7 : ¬∀ {k : ℕ} {State Symbol : Type} [inst : Fintype Symbol] [inst_1 : Fintype State] {w : Fin k → ℕ} {s : ℕ},
        Fintype.card (Turing.BoundedStorage Symbol State w) ≤ Turing.storageBound Symbol State k s := fun hc_h => absurd (@hc_h (1) (Bool) (Bool) (Bool.fintype) (Bool.fintype) (fun (a : Fin 1) => 1) (0)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTm_substTm, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTm_substTm.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var]
        {s : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var}
        (t₁ t₂ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var) (x : Var),
        (t₁.openTm t₂)[x := s] = t₁[x := s].openTm t₂[x := s] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (.abs .top (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (0)) (by
  nofun)

-- Cslib.LTS.setImageMultistep_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.setImageMultistep_mono.h5 : ¬∀ {State Label : Type} (lts : Cslib.LTS State Label) {S T : Set State} (μs : List Label),
        lts.setImageMultistep S μs ⊆ lts.setImageMultistep T μs := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) ({n : ℕ | n = 0}) ({x : ℕ | False}) ([])) (by
  simp)

-- Cslib.LTS.MTr.nil_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.MTr.nil_eq.h5 : ¬∀ {State Label : Type} (lts : Cslib.LTS State Label) {s1 s2 : State}, s1 = s2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (1)) (by
  decide +kernel)

-- Cslib.Algorithms.Lean.TimeM.mem_either_merge, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Algorithms.Lean.TimeM.mem_either_merge.h5 : ¬∀ {α : Type} [inst : LinearOrder α] (xs ys : List α) (z : α), z ∈ xs ∨ z ∈ ys := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([]) ([]) (0)) (by
  decide +kernel)

-- Relation.RelatesWithinSteps.of_relatesInSteps, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesWithinSteps.of_relatesInSteps.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} {n : ℕ}, Relation.RelatesWithinSteps r a b n := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (1) (0)) (by
  simp)

-- Relation.RightEuclidean.rightTotal_equiv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RightEuclidean.rightTotal_equiv.h3 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Relation.RightEuclidean r], IsEquiv α r := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) (@Relation.RightEuclidean.mk (Bool) (fun (x x_1 : Bool) => False) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.toRefl.refl (Bool.false : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.of_env_sub, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.of_env_sub.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {X : Var},
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf Γ σ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.nmem_fv_open, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.nmem_fv_open.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}
        {γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {X : Var}, X ∉ σ.fv := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0)) (by
  decide +kernel)

-- Relation.RightEuclidean.instSymmOfRefl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RightEuclidean.instSymmOfRefl.h2 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Refl r], Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Relation.RightEuclidean.instSymmOfRefl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RightEuclidean.instSymmOfRefl.h3 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Relation.RightEuclidean r], Std.Symm r := fun hc_h => absurd (@hc_h (Bool) (fun (a b : Bool) => b = Bool.true) (@Relation.RightEuclidean.mk (Bool) (fun (a b : Bool) => @Eq Bool b Bool.true) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.invert_step_app_fvar, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.invert_step_app_fvar.h4 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {x : Var},
        ∃ (M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
          N = M'.app (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) ∧ M.FullEta M' := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0)) (by
  (simp <;> omega))

-- Relation.MJoin.single, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.MJoin.single.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Relation.MJoin r a b := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) (Bool.false) (Bool.true)) (by
  nofun)

-- Cslib.ωSequence.extract_succ_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.extract_succ_right.h4 : ¬∀ {α : Type} {xs : Cslib.ωSequence α} {m n : ℕ}, xs.extract m (n + 1) = xs.extract m n ++ [xs n] := fun hc_h => absurd (@hc_h (ℕ) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (1) (0)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.lc_l, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.lc_l.h3 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, M.LC := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  nofun)

-- Cslib.SKI.Red.ne, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.Red.ne.h2 : ¬∀ {x y : Cslib.SKI}, x ≠ y := fun hc_h => absurd (@hc_h (.S : Cslib.SKI) (.S : Cslib.SKI)) (by
  decide +kernel)

-- Cslib.FLP.ZeroFaultAlg.trInv_inv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.FLP.ZeroFaultAlg.trInv_inv.h1 : ¬∀ {n : ℕ} (inp : Fin n → Bool), 0 < n := fun hc_h => absurd (@hc_h (0) (fun (a : Fin 0) => Bool.false)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.lc_refl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.lc_refl.h2 : ¬∀ {Var : Type} (M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var), M.Standard M := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  nofun)

