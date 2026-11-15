import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow_aux, hypothesis 9: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow_aux.h9.gneg.{u_1} : ∀ {Var : Type u_1} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
      {σ τ δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {X : Var}
      {δ' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
      (¬∀ (Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var) (σ τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var),
            Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ σ δ →
              Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ δ τ → Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ σ τ) →
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub
            (Γ ++
              (⟨X, Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding.sub δ⟩ :
                  (_ : Var) × Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) ::
                Δ)
            σ τ →
          Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Δ δ' δ →
            Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub
              (Γ ++
                (⟨X, Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding.sub δ'⟩ :
                    (_ : Var) × Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) ::
                  Δ)
              σ τ := by
  (intros; grind)
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow_aux.h9.{u_1} : ∀ {Var : Type u_1} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
      {σ τ δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {X : Var}
      {δ' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
      Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub
          (Γ ++
            (⟨X, Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding.sub δ⟩ :
                (_ : Var) × Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) ::
              Δ)
          σ τ →
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Δ δ' δ →
          Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub
            (Γ ++
              (⟨X, Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding.sub δ'⟩ :
                  (_ : Var) × Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) ::
                Δ)
            σ τ := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10 hc_x11
  exact Classical.byCases (fun hc_h => @Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow_aux hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10 hc_x11) (fun hc_hn => @HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow_aux.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10 hc_x11)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow_aux.h9.derivable.{u_1} : ∀ {Var : Type u_1} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
      {σ τ δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {X : Var}
      {δ' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
      Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub
          (Γ ++
            (⟨X, Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding.sub δ⟩ :
                (_ : Var) × Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) ::
              Δ)
          σ τ →
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Δ δ' δ →
          ∀ (Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var)
            (σ τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var),
            Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ σ δ →
              Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ δ τ → Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ σ τ := by
  (intros; grind)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow_aux, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow_aux.h10 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ τ δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {X : Var}
        {δ' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        (∀ (Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var) (σ τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var),
            Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ σ δ →
              Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ δ τ → Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ σ τ) →
          Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Δ δ' δ →
            Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub
              (Γ ++
                (⟨X, Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding.sub δ'⟩ :
                    (_ : Var) × Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) ::
                  Δ)
              σ τ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  grind) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.map_subst, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.map_subst.h9 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}
        {τ' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} [inst_1 : Cslib.HasFresh Var] {X : Var},
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf Δ τ' →
          Cslib.HasWellFormed.wf
              (Cslib.LambdaCalculus.LocallyNameless.Context.mapVal
                  (fun (x : Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) => x[X := τ']) Γ ++
                Δ) →
            Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf
              (Cslib.LambdaCalculus.LocallyNameless.Context.mapVal
                  (fun (x : Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) => x[X := τ']) Γ ++
                Δ)
              σ[X := τ'] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (Cslib.instHasFreshNat) (1) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.map_subst, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.map_subst.h10 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ τ τ' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} [inst_1 : Cslib.HasFresh Var] {X : Var},
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf
            (Γ ++
              (⟨X, Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding.sub τ⟩ :
                  (_ : Var) × Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) ::
                Δ)
            σ →
          Cslib.HasWellFormed.wf
              (Cslib.LambdaCalculus.LocallyNameless.Context.mapVal
                  (fun (x : Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) => x[X := τ']) Γ ++
                Δ) →
            Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf
              (Cslib.LambdaCalculus.LocallyNameless.Context.mapVal
                  (fun (x : Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) => x[X := τ']) Γ ++
                Δ)
              σ[X := τ'] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (Cslib.instHasFreshNat) (0) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.open_lc, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.open_lc.h8 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {τ δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}
        [inst_1 : Cslib.HasFresh Var],
        Cslib.HasWellFormed.wf Γ →
          Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf Γ δ →
            Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf Γ (τ.open' δ) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (Cslib.instHasFreshNat) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        List.Perm Γ Δ →
          Cslib.HasWellFormed.wf Γ → Cslib.HasWellFormed.wf Δ → Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf Δ σ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  rfl) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Language.dfa_num_state_ge, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Language.dfa_num_state_ge.h3.gneg.{u_1} : ∀ {α : Type} {l : Language α} {ws : Set (List α)},
      ¬Finite ↑ws →
        (ws.Pairwise fun (x1 x2 : List α) => ¬l.NerodeCongruence.eq x1 x2) →
          ∀ {State : Type u_1} [inst : Finite State] {M : Cslib.Automata.DA.FinAcc State α},
            Cslib.Automata.Acceptor.language M = l → Nat.card ↑ws ≤ Nat.card State := by
  (intros; simp_all; done)
theorem HypCheckProof.Language.dfa_num_state_ge.h3.{u_1} : ∀ {α : Type} {l : Language α} {ws : Set (List α)},
      (ws.Pairwise fun (x1 x2 : List α) => ¬l.NerodeCongruence.eq x1 x2) →
        ∀ {State : Type u_1} [inst : Finite State] {M : Cslib.Automata.DA.FinAcc State α},
          Cslib.Automata.Acceptor.language M = l → Nat.card ↑ws ≤ Nat.card State := by
  intro hc_x0 hc_x1 hc_x2 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact Classical.byCases (fun hc_h => @Language.dfa_num_state_ge hc_x0 hc_x1 hc_x2 hc_h hc_x4 hc_x5 hc_x6 hc_x7 hc_x8) (fun hc_hn => @HypCheckProof.Language.dfa_num_state_ge.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4 hc_x5 hc_x6 hc_x7 hc_x8)

-- Cslib.LTS.Deterministic.eq_of_tr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Deterministic.eq_of_tr.h7 : ¬∀ {State Label : Type} {s1 : State} {μ : Label} {s2 s2' : State} {lts : Cslib.LTS State Label},
        lts.Tr s1 μ s2 → lts.Tr s1 μ s2' → s2 = s2' := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) (0) (0) (1) ({ Tr := fun (a a_1 b : ℕ) => a_1 ≤ b : Cslib.LTS ℕ ℕ }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Relation.RightEuclidean.rightEuclidean, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.RightEuclidean.rightEuclidean.h2.inst : ¬(fun (a b : ℕ) => a < b) 1 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.RightEuclidean.rightEuclidean.h2.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.RightEuclidean.rightEuclidean.h2.prem1 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Relation.RightEuclidean.rightEuclidean.h2 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, r a b → r a c → r b c := fun hc_h => HypCheckProof.Relation.RightEuclidean.rightEuclidean.h2.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (0) (1) (1) HypCheckProof.Relation.RightEuclidean.rightEuclidean.h2.prem0 HypCheckProof.Relation.RightEuclidean.rightEuclidean.h2.prem1)

-- Relation.RightEuclidean.rightEuclidean, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RightEuclidean.rightEuclidean.h6 : ¬∀ {α : Type} {r : α → α → Prop} [self : Relation.RightEuclidean r] {a b c : α}, r a c → r b c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (@Relation.RightEuclidean.mk (Nat) (fun (a b : Nat) => @Eq Nat a b) (by (try dsimp only);   (intros; omega))) (0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Relation.RightEuclidean.rightEuclidean, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RightEuclidean.rightEuclidean.h7 : ¬∀ {α : Type} {r : α → α → Prop} [self : Relation.RightEuclidean r] {a b c : α}, r a b → r b c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (@Relation.RightEuclidean.mk (Nat) (fun (a b : Nat) => @Eq Nat a b) (by (try dsimp only);   (intros; omega))) (0) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Cslib.LTS.Execution.take, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.take.h9 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        lts.Execution s μs t ss → ∀ (n : ℕ), n < ss.length := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([0]) (by
  (repeat' constructor) <;> done) (1)) (by
  decide +kernel)

-- Finset.card_div_two_le_card_filter_of_involution, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_div_two_le_card_filter_of_involution.h7 : ¬∀ {α : Type} {s : Finset α} {σ : α → α} {p : α → Prop} [inst : DecidablePred p],
        (∀ x ∈ s, σ (σ x) = x) → (∀ x ∈ s, σ x ∈ s) → s.card / 2 ≤ (Finset.filter p s).card := fun hc_h => absurd (@hc_h (Bool) (Finset.univ : Finset Bool) (not : Bool → Bool) (fun _ => False : Bool → Prop) (fun (a : Bool) => instDecidableFalse) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_subst, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_subst.h8 : ¬∀ {Var : Type} {M M' N N' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var] (x : Var), N.Parallel N' → M[x := N].Parallel M'[x := N'] := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_subst, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_subst.h9 : ¬∀ {Var : Type} {M M' N N' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var] (x : Var), M.Parallel M' → M[x := N].Parallel M'[x := N'] := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_subst_cong_l, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_subst_cong_l.h7 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var] {x : Var}
        (s s' N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var), N.LC → s[x := N].FullEta s'[x := N] := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_subst_cong_r, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_subst_cong_r.h7 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var] {x : Var}
        (s t t' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        s.LC → Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta s[x := t] s[x := t'] := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiApp_step_lc_r, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiApp_step_lc_r.h5 : ¬∀ {Var : Type} {Ns : List (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var)}
        {Ns' : List (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var)} [inst : DecidableEq Var]
        [inst : Cslib.HasFresh Var], ∀ N ∈ Ns', N.LC := fun hc_h => absurd (@hc_h (ℕ) ([]) ([Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.bvar 0]) (instDecidableEqNat) (Cslib.instHasFreshNat) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  decide)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.lc_r, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.lc_r.h6 : ¬∀ {Var : Type} {M M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {i : ℕ} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], M.LC → M'.LC := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.trans_step, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.trans_step.h7 : ¬∀ {Var : Type} {M N P : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], M.Standard P → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- List.IsChainFromTo.snoc, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChainFromTo.snoc.h6.inst : ¬List.IsChainFromTo (fun (a b : ℕ) => a < b) ([] ++ [1]) 0 1 := by
  nofun
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChainFromTo.snoc.h6.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChainFromTo.snoc.h6 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b c : α}, r b c → List.IsChainFromTo r (chain ++ [c]) a c := fun hc_h => HypCheckProof.List.IsChainFromTo.snoc.h6.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) ([]) (0) (0) (1) HypCheckProof.List.IsChainFromTo.snoc.h6.prem0)

-- List.IsChainFromTo.snoc, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.snoc.h7 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b c : α},
        List.IsChainFromTo r chain a b → List.IsChainFromTo r (chain ++ [c]) a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) (0) (0) (by
  simp)) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.close_open_to_subst, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.close_open_to_subst.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var]
        (m n : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (x : Var), n.LC → (m.close x).open' n = m[x := n] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.lcAt_openRec_above_lcAt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.lcAt_openRec_above_lcAt.h5 : ¬∀ {Var : Type} (M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (i j : ℕ),
        Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.LcAt i M = Bool.true →
          Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec j N M = M := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.lcAt_openRec_above_lcAt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.lcAt_openRec_above_lcAt.h6 : ¬∀ {Var : Type} (M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (i j : ℕ),
        i ≤ j → Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec j N M = M := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.step_multiApp_l, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.step_multiApp_l.h4 : ¬∀ {Var : Type} {M M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {Ns : List (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var)},
        (∀ N ∈ Ns, N.LC) → (M.multiApp Ns).FullBeta (M'.multiApp Ns) := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) ([]) (by
  decide)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.isAbs_r, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.isAbs_r.h4 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {i : ℕ}, M.IsAbs → N.IsAbs := fun hc_h => absurd (@hc_h (ℕ) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_open_close, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_open_close.h8 : ¬∀ {Var : Type} {M M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var] (x y : Var) (z : ℕ),
        (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec z
              (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar y)
              (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.closeRec z x M)).Parallel
          (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec z
            (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar y)
            (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.closeRec z x M')) := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (0) (0) (1)) (by
  nofun)

-- Cslib.LTS.reindex.bisim_trace, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.reindex.bisim_trace.h8 : Not
      (∀ {State₁ State₂ Label : Type} (lts₁ : Cslib.LTS State₁ Label) (e : Equiv State₁ State₂) (s₁ t₁ : State₁)
        (μs : List Label),
        @Cslib.LTS.MTr State₂ Label (@Cslib.LTS.reindex State₁ State₂ Label lts₁ e)
          (@DFunLike.coe (Equiv State₁ State₂) State₁ (fun (x : State₁) => State₂)
            (@EquivLike.toFunLike (Equiv State₁ State₂) State₁ State₂ (@Equiv.instEquivLike State₁ State₂)) e s₁)
          μs
          (@DFunLike.coe (Equiv State₁ State₂) State₁ (fun (x : State₁) => State₂)
            (@EquivLike.toFunLike (Equiv State₁ State₂) State₁ State₂ (@Equiv.instEquivLike State₁ State₂)) e t₁)) := fun hc_h => absurd (@hc_h (Bool) (Bool) (Nat) (@Cslib.LTS.mk Bool Nat fun (a : Bool) (a_1 : Nat) (b : Bool) => @Eq Bool b Bool.true) (@Equiv.mk Bool Bool Bool.not Bool.not
      (@of_decide_eq_true (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
        (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
        (@id
          (@Eq Bool
            (@Decidable.decide (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
              (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
        (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
        (@id
          (@Eq Bool
            (@Decidable.decide (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
              (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (Bool.false) (Bool.true) (@List.nil Nat)) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.strengthen, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.strengthen.h8 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}
        {X : Var}, Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub (Γ ++ Δ) σ τ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0)) (by
  nofun)

-- Cslib.Automata.εNA.FinAcc.concat_mTr_inl, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.εNA.FinAcc.concat_mTr_inl.h8 : ¬∀ {Symbol S₁ S₂ : Type} {a : Cslib.Automata.εNA.FinAcc S₁ Symbol} {b : Cslib.Automata.εNA.FinAcc S₂ Symbol} {s : S₁}
        {t : S₂} {μs : List (Option Symbol)},
        ∃ s₁ ∈ a.accept,
          ∃ s₂ ∈ b.start,
            ∃ (μs₁ : List (Option Symbol)) (μs₂ : List (Option Symbol)),
              a.MTr s μs₁ s₁ ∧ b.MTr s₂ μs₂ t ∧ μs = μs₁ ++ Option.none :: μs₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({ Tr := fun (a : ℕ) (a_1 : Option ℕ) (n : ℕ) => n = 0, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.εNA.FinAcc ℕ ℕ }) ({ Tr := fun (a : ℕ) (a_1 : Option ℕ) (n : ℕ) => n = 0, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.εNA.FinAcc ℕ ℕ }) (0) (0) ([])) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_open, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_open.h7 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var] (x : Var)
        (t u e : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var), (e.open' u)[x := t] = e[x := t].open' u[x := t] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  decide +kernel)

-- Cslib.LTS.MTr.split, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.MTr.split.h7 : ¬∀ {State Label : Type} {s1 : State} {μs μs' : List Label} {s2 : State} {lts : Cslib.LTS State Label},
        ∃ (s : State), lts.MTr s1 μs s ∧ lts.MTr s μs' s2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) ([]) ([]) (1) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ })) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_tm_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_tm_eq.h6 : ¬∀ {Var : Type} {t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var} {Y : ℕ}
        {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {x : ℕ}
        {s : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var},
        t = Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm x s t := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (0) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ)) (by
  nofun)

-- Relation.dom_cod_rightEuclidean, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.dom_cod_rightEuclidean.h2 : ¬∀ {α : Type} {r : α → α → Prop} [equiv_dom : IsEquiv ↑(Relation.dom r) fun (a b : ↑(Relation.dom r)) => r ↑a ↑b],
        Relation.RightEuclidean r := fun hc_h => absurd (@hc_h (Bool) (fun a _ => a = false : Bool → Bool → Prop) (@IsEquiv.mk (@Set.Elem Bool (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false)) (fun (a b : @Set.Elem Bool (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false)) =>
      (fun (a x : Bool) => @Eq Bool a Bool.false)
        (@Subtype.val Bool
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false) x)
          a)
        (@Subtype.val Bool
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false) x)
          b)) (@IsPreorder.mk (@Set.Elem Bool (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false)) (fun (a b : @Set.Elem Bool (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false)) =>
      (fun (a x : Bool) => @Eq Bool a Bool.false)
        (@Subtype.val Bool
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false) x)
          a)
        (@Subtype.val Bool
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false) x)
          b)) (@Std.Refl.mk (@Set.Elem Bool (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false)) (fun (a b : @Set.Elem Bool (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false)) =>
      (fun (a x : Bool) => @Eq Bool a Bool.false)
        (@Subtype.val Bool
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false) x)
          a)
        (@Subtype.val Bool
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false) x)
          b)) (by (try dsimp only);   grind)) (@IsTrans.mk (@Set.Elem Bool (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false)) (fun (a b : @Set.Elem Bool (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false)) =>
      (fun (a x : Bool) => @Eq Bool a Bool.false)
        (@Subtype.val Bool
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false) x)
          a)
        (@Subtype.val Bool
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false) x)
          b)) (by (try dsimp only);   (intros; omega)))) (@Std.Symm.mk (@Set.Elem Bool (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false)) (fun (a b : @Set.Elem Bool (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false)) =>
      (fun (a x : Bool) => @Eq Bool a Bool.false)
        (@Subtype.val Bool
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false) x)
          a)
        (@Subtype.val Bool
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Relation.dom Bool Bool fun (a x : Bool) => @Eq Bool a Bool.false) x)
          b)) (by (try dsimp only);   grind)))) (by
  exact fun hc_c =>
    absurd
      (hc_c.rightEuclidean (a := (Bool.false : Bool)) (b := (Bool.true : Bool)) (c := (Bool.false : Bool))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Relation.dom_cod_rightEuclidean, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.dom_cod_rightEuclidean.h3 : ¬∀ {α : Type} {r : α → α → Prop}, Relation.dom r = Relation.cod r → Relation.RightEuclidean r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) : ℕ → ℕ → Prop) (by
  grind)) (by
  exact fun hc_c =>
    absurd
      (hc_c.rightEuclidean (a := (0 : ℕ)) (b := (1 : ℕ)) (c := (1 : ℕ))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Relation.of_cod, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.of_cod.h5 : ¬∀ {α β : Type} {r : α → β → Prop} {a : α} {b : β}, b ∈ Relation.cod r := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0)) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_not_fv, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_not_fv.h5 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], N.fv ⊆ M.fv := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat)) (by
  decide +kernel)

-- Cslib.FinFun.ext, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.FinFun.ext.h5 : Not (∀ {β α : Type} [inst : Zero β] {f g : @Cslib.FinFun α β inst}, @Eq (@Cslib.FinFun α β inst) f g) := fun hc_h => absurd (@hc_h (Nat) (Bool) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (@Cslib.FinFun.mk Bool Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
      (fun (x : Bool) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool))
      (@of_decide_eq_true
        (∀ {a : Bool},
          Iff
            (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
              (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
            (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
        (@Bool.instDecidableForallOfDecidablePred
          (fun (a : Bool) =>
            Iff
              (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
              (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
          fun (a : Bool) =>
          @instDecidableIff
            (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
              (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
            (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
            (@Finset.decidableMem Bool instDecidableEqBool a
              (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)))
            (@instDecidableNot
              (@Eq Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
              (instDecidableEqNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ {a : Bool},
                Iff
                  (@Membership.mem Bool (Finset Bool)
                    (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                    (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
                  (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
              (@Bool.instDecidableForallOfDecidablePred
                (fun (a : Bool) =>
                  Iff
                    (@Membership.mem Bool (Finset Bool)
                      (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                      (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
                    (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
                fun (a : Bool) =>
                @instDecidableIff
                  (@Membership.mem Bool (Finset Bool)
                    (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                    (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
                  (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                  (@Finset.decidableMem Bool instDecidableEqBool a
                    (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)))
                  (@instDecidableNot
                    (@Eq Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                    (instDecidableEqNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 0)
                        (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Cslib.FinFun.mk Bool Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
      (fun (b : Bool) =>
        @ite Nat (@Eq Bool b Bool.true) (instDecidableEqBool b Bool.true)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true)
      (@of_decide_eq_true
        (∀ {a : Bool},
          Iff
            (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
              (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
            (@Ne Nat
              (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
        (@Bool.instDecidableForallOfDecidablePred
          (fun (a : Bool) =>
            Iff
              (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
              (@Ne Nat
                (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
          fun (a : Bool) =>
          @instDecidableIff
            (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
              (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
            (@Ne Nat
              (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
            (@Finset.decidableMem Bool instDecidableEqBool a
              (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true))
            (@instDecidableNot
              (@Eq Nat
                (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
              (instDecidableEqNat
                (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ {a : Bool},
                Iff
                  (@Membership.mem Bool (Finset Bool)
                    (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                    (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
                  (@Ne Nat
                    (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
              (@Bool.instDecidableForallOfDecidablePred
                (fun (a : Bool) =>
                  Iff
                    (@Membership.mem Bool (Finset Bool)
                      (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                      (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
                    (@Ne Nat
                      (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
                fun (a : Bool) =>
                @instDecidableIff
                  (@Membership.mem Bool (Finset Bool)
                    (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                    (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
                  (@Ne Nat
                    (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                  (@Finset.decidableMem Bool instDecidableEqBool a
                    (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true))
                  (@instDecidableNot
                    (@Eq Nat
                      (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                    (instDecidableEqNat
                      (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@OfNat.ofNat Nat (nat_lit 0)
                        (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Cslib.FinFun.fn_eq_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.FinFun.fn_eq_eq.h5 : Not (∀ {β α : Type} [inst : Zero β] {f g : @Cslib.FinFun α β inst}, @Eq (@Cslib.FinFun α β inst) f g) := fun hc_h => absurd (@hc_h (Nat) (Bool) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (@Cslib.FinFun.mk Bool Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
      (fun (x : Bool) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool))
      (@of_decide_eq_true
        (∀ {a : Bool},
          Iff
            (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
              (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
            (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
        (@Bool.instDecidableForallOfDecidablePred
          (fun (a : Bool) =>
            Iff
              (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
              (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
          fun (a : Bool) =>
          @instDecidableIff
            (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
              (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
            (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
            (@Finset.decidableMem Bool instDecidableEqBool a
              (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)))
            (@instDecidableNot
              (@Eq Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
              (instDecidableEqNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ {a : Bool},
                Iff
                  (@Membership.mem Bool (Finset Bool)
                    (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                    (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
                  (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
              (@Bool.instDecidableForallOfDecidablePred
                (fun (a : Bool) =>
                  Iff
                    (@Membership.mem Bool (Finset Bool)
                      (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                      (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
                    (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
                fun (a : Bool) =>
                @instDecidableIff
                  (@Membership.mem Bool (Finset Bool)
                    (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                    (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)) a)
                  (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                  (@Finset.decidableMem Bool instDecidableEqBool a
                    (@EmptyCollection.emptyCollection (Finset Bool) (@Finset.instEmptyCollection Bool)))
                  (@instDecidableNot
                    (@Eq Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                    (instDecidableEqNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat Nat (nat_lit 0)
                        (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Cslib.FinFun.mk Bool Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
      (fun (b : Bool) =>
        @ite Nat (@Eq Bool b Bool.true) (instDecidableEqBool b Bool.true)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true)
      (@of_decide_eq_true
        (∀ {a : Bool},
          Iff
            (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
              (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
            (@Ne Nat
              (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
        (@Bool.instDecidableForallOfDecidablePred
          (fun (a : Bool) =>
            Iff
              (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
              (@Ne Nat
                (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
          fun (a : Bool) =>
          @instDecidableIff
            (@Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
              (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
            (@Ne Nat
              (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
            (@Finset.decidableMem Bool instDecidableEqBool a
              (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true))
            (@instDecidableNot
              (@Eq Nat
                (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
              (instDecidableEqNat
                (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ {a : Bool},
                Iff
                  (@Membership.mem Bool (Finset Bool)
                    (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                    (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
                  (@Ne Nat
                    (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
              (@Bool.instDecidableForallOfDecidablePred
                (fun (a : Bool) =>
                  Iff
                    (@Membership.mem Bool (Finset Bool)
                      (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                      (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
                    (@Ne Nat
                      (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))
                fun (a : Bool) =>
                @instDecidableIff
                  (@Membership.mem Bool (Finset Bool)
                    (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
                    (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) a)
                  (@Ne Nat
                    (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                  (@Finset.decidableMem Bool instDecidableEqBool a
                    (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true))
                  (@instDecidableNot
                    (@Eq Nat
                      (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                    (instDecidableEqNat
                      (@ite Nat (@Eq Bool a Bool.true) (instDecidableEqBool a Bool.true)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@OfNat.ofNat Nat (nat_lit 0)
                        (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- List.IsChainFromTo.reflTransGen, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.reflTransGen.h5 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b : α}, Relation.ReflTransGen r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (1) (0)) (by
  nofun)

-- Cslib.ωSequence.get_extract, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.get_extract.h5 : ¬∀ {α : Type} {xs : Cslib.ωSequence α} {m n k : ℕ}, k < n - m := fun hc_h => absurd (@hc_h (ℕ) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (0) (0) (0)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.wf, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.wf.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] (Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var)
        (σ σ' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var),
        Γ.Wf ∧ Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf Γ σ ∧ Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf Γ σ' := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ)) (by
  nofun)

-- Relation.LeftEuclidean.leftUnique_antisymm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.LeftEuclidean.leftUnique_antisymm.h3 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Relation.LeftEuclidean r], Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (@Relation.LeftEuclidean.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd
      (hc_c.antisymm (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_intro, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_intro.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] (x : Var) (t e : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        e.open' t = (e.open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x))[x := t] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.substTm_fresh, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.substTm_fresh.h4 : ¬∀ {Var : Type} [inst : DecidableEq Var] {t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var} {x : Var}
        (s : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var), t = t[x := s] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ)) (by
  nofun)

-- Relation.join_inl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.join_inl.h5 : ¬∀ {α : Type} {r₁ r₂ : α → α → Prop} {a b : α}, (r₁ ⊔ r₂) a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0)) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_lc, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_lc.h5 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] (k : ℕ) (t e : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec k t e = e := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  decide +kernel)

-- Relation.RelatesInSteps.succ, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesInSteps.succ.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} {n : ℕ}, ∃ (t' : α), Relation.RelatesInSteps r a t' n ∧ r t' b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (0)) (by
  simp)

-- Relation.RightEuclidean.trichotomous_trans, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RightEuclidean.trichotomous_trans.h2 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Trichotomous r], IsTrans α r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≠ b : ℕ → ℕ → Prop) (@Std.Trichotomous.mk (Nat) (fun (a b : Nat) => @Ne Nat a b) (by (try dsimp only);   (intros; omega)))) (by
  exact fun hc_c =>
    absurd
      (hc_c.trans (0 : ℕ) (1 : ℕ) (0 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Relation.LeftEuclidean.leftTotal_equiv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.LeftEuclidean.leftTotal_equiv.h3 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Relation.LeftEuclidean r], IsEquiv α r := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) (@Relation.LeftEuclidean.mk (Bool) (fun (x x_1 : Bool) => False) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.toRefl.refl (Bool.false : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.invert_step_app_fvar, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.invert_step_app_fvar.h4 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {x : Var},
        (∃ (M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
            N = M'.app (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) ∧ M.FullBeta M') ∨
          ∃ (M1 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
            M = M1.abs ∧ N = M1.open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0)) (by
  (simp <;> decide))

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.countRedexes_app_abs, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.countRedexes_app_abs.h2 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        (N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        (M.app N).countRedexes = M.countRedexes + N.countRedexes + 1 := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_lc_r, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_lc_r.h3 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, M'.LC := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.lc_l, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.lc_l.h3 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, M.LC := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  nofun)

-- Cslib.SKI.Sa_irreducible, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.Sa_irreducible.h2 : ¬∀ (a c : Cslib.SKI), ∃ (a' : Cslib.SKI), a.ParallelReduction a' ∧ c = Cslib.SKI.S.app a' := fun hc_h => absurd (@hc_h (.S : Cslib.SKI) (.S : Cslib.SKI)) (by
  simp)

-- Cslib.SKI.evalStep_right_correct, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.evalStep_right_correct.h2 : ¬∀ (x y : Cslib.SKI), x.Red y := fun hc_h => absurd (@hc_h (.S : Cslib.SKI) (.S : Cslib.SKI)) (by
  nofun)

-- Relation.Terminating.to_normalizing, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Terminating.to_normalizing.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Relation.Normalizing r := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop)) (by
  simp)

-- Relation.Convergent.isNormalizing, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Convergent.isNormalizing.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Relation.Normalizing r := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop)) (by
  simp)

-- Cslib.CCS.Act.isVisible_neq_τ, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Cslib.CCS.Act.isVisible_neq_τ.h2.{u_1} : ¬∀ {Name : Type u_1} {μ : Cslib.CCS.Act Name}, μ ≠ Cslib.CCS.Act.τ := by
  (simp_all; done)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Parallel.lc_refl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Parallel.lc_refl.h2 : ¬∀ {Var : Type} (M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var), M.Parallel M := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  nofun)

-- Cslib.ωSequence.instIsEmpty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.instIsEmpty.h1 : ¬∀ {α : Type}, IsEmpty (Cslib.ωSequence α) := fun hc_h => absurd (@hc_h (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ } : Cslib.ωSequence ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Cslib.SKI.redexFree_of_normal_red, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.redexFree_of_normal_red.h1 : ¬∀ {x : Cslib.SKI}, x.RedexFree := fun hc_h => absurd (@hc_h (.app .I .I : Cslib.SKI)) (by
  decide +kernel)

-- Nat.strictMono_infinite, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.strictMono_infinite.h1 : ¬∀ {f : ℕ → ℕ}, (Set.range f).Infinite := fun hc_h => absurd (@hc_h (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Cslib.FLP.ZeroFaultAlg.consensus_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.FLP.ZeroFaultAlg.consensus_zero.h1 : ¬∀ {n : ℕ}, 0 < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

