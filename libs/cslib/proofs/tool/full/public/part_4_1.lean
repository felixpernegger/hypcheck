import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Cslib.LTS.IsBisimulation.follow_snd, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Cslib.LTS.IsBisimulation.follow_snd.h10.inst : ¬∃ (s₁' : ℕ), { Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }.Tr 0 0 s₁' ∧ (fun (a b : ℕ) => a < b) s₁' 1 := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Cslib.LTS.IsBisimulation.follow_snd.h10.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Cslib.LTS.IsBisimulation.follow_snd.h10.prem1 : { Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }.Tr 1 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Cslib.LTS.IsBisimulation.follow_snd.h10 : ¬∀ {State₁ State₂ Label : Type} {lts₁ : Cslib.LTS State₁ Label} {lts₂ : Cslib.LTS State₂ Label}
        {r : State₁ → State₂ → Prop} {s₁ : State₁} {s₂ : State₂} {μ : Label} {s₂' : State₂},
        r s₁ s₂ → lts₂.Tr s₂ μ s₂' → ∃ (s₁' : State₁), lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂' := fun hc_h => HypCheckProof.Cslib.LTS.IsBisimulation.follow_snd.h10.inst (@hc_h (ℕ) (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (fun (a b : ℕ) => a < b) (0) (1) (0) (1) HypCheckProof.Cslib.LTS.IsBisimulation.follow_snd.h10.prem0 HypCheckProof.Cslib.LTS.IsBisimulation.follow_snd.h10.prem1)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_subst_cong_lc, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_subst_cong_lc.h7 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var]
        (s s' t : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (x : Var), t.LC → s[x := t].FullBeta s'[x := t] := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.subst_lc, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.subst_lc.h5 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var]
        {σ τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}, τ.LC → ∀ (X : Var), σ[X := τ].LC := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  (repeat' constructor) <;> done) (0)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.subst_lc, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.subst_lc.h6 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var]
        {σ τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}, σ.LC → ∀ (X : Var), σ[X := τ].LC := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  (repeat' constructor) <;> done) (0)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.weaken, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.weaken.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ Δ Θ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        Cslib.HasWellFormed.wf (Γ ++ Δ ++ Θ) → Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf (Γ ++ Δ ++ Θ) σ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.Automata.TwoWayNA.IsRejectionCert.accept_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.TwoWayNA.IsRejectionCert.accept_notMem.h5 : ¬∀ {State Symbol : Type} {a : Cslib.Automata.TwoWayNA State Symbol} {input : List Symbol}
        {cert : Cslib.ωSequence (Set State)}, ∀ s ∈ cert input.length, s ∉ a.accept := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (q x : ℕ) (m : SignType) (n : ℕ) => n = 0, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.TwoWayNA ℕ ℕ }) ([]) ({ get := fun (a : ℕ) => {n : ℕ | n = 0} : Cslib.ωSequence (Set ℕ) }) (0) (by
  rfl)) (by
  decide +kernel)

-- Cslib.ωSequence.append_extract_extract, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.append_extract_extract.h5 : ¬∀ {α : Type} {xs : Cslib.ωSequence α} {k m n : ℕ}, m ≤ n → xs.extract k m ++ xs.extract m n = xs.extract k n := fun hc_h => absurd (@hc_h (ℕ) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Cslib.ωSequence.append_extract_extract, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.append_extract_extract.h6 : ¬∀ {α : Type} {xs : Cslib.ωSequence α} {k m n : ℕ}, k ≤ m → xs.extract k m ++ xs.extract m n = xs.extract k n := fun hc_h => absurd (@hc_h (ℕ) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.le_countRedexes_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.le_countRedexes_of_ne.h5 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {n : ℕ} [inst : Cslib.HasFresh Var],
        M ≠ N → n ≤ N.countRedexes := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (1) (Cslib.instHasFreshNat) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.le_countRedexes_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.le_countRedexes_of_ne.h6 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {n : ℕ} [inst : Cslib.HasFresh Var],
        Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq n M N → n ≤ N.countRedexes := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (1) (Cslib.instHasFreshNat) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.steps_lc_r, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.steps_lc_r.h5 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN M N → N.LC := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  rfl)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.steps_lc_r, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.steps_lc_r.h6 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], M.LC → N.LC := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.to_step, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.to_step.h5 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} {i : ℕ} [inst : DecidableEq Var],
        M.LC → M.FullBeta N := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (instDecidableEqNat) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.of_bind_ty, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.of_bind_ty.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {X : Var},
        Γ.Wf → Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf Γ σ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Relation.RelatesInSteps.reflTransGen, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesInSteps.reflTransGen.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} {n : ℕ}, Relation.ReflTransGen r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0) (0)) (by
  nofun)

-- Cslib.ωSequence.getElem?_take, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.getElem?_take.h4 : ¬∀ {α : Type} {s : Cslib.ωSequence α} {k n : ℕ}, (Cslib.ωSequence.take n s)[k]? = Option.some (s k) := fun hc_h => absurd (@hc_h (ℕ) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (0) (0)) (by
  decide +kernel)

-- Relation.ReflTransGen.relatesInSteps_lt_encard, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.ReflTransGen.relatesInSteps_lt_encard.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α},
        ∃ (n : ℕ), Relation.RelatesInSteps r a b n ∧ ↑n < {x : α | Relation.ReflTransGen r a x}.encard := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0)) (by
  nofun)

-- Relation.RelatesWithinSteps.zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesWithinSteps.zero.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, a = b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (1)) (by
  decide +kernel)

-- Cslib.QueryComplexity.le_certificateComplexityAt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.QueryComplexity.le_certificateComplexityAt.h4 : ¬∀ {n : ℕ} {f : Cslib.BooleanFunction n} {x : Cslib.BitString n} {k : ℕ},
        k ≤ Cslib.QueryComplexity.certificateComplexityAt f x := fun hc_h => absurd (@hc_h (0) (fun (a : Cslib.BitString 0) => Bool.false) (fun (a : Fin 0) => Bool.false) (1)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_close_var, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_close_var.h4 : ¬∀ {Var : Type} [inst : DecidableEq Var] (x : Var) (t : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        t = (t.open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x)).close x := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_lc_l, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_lc_l.h4 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var], M.LC := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat)) (by
  nofun)

-- Nat.segment_plus_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.segment_plus_one.h1 : Not
      (∀ {f : Nat → Nat} (k : Nat),
        @Eq Nat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (Nat.segment f k)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Nat.count (fun (x : Nat) => @Membership.mem Nat (Set Nat) (@Set.instMembership Nat) (@Set.range Nat Nat f) x)
            (fun (a : Nat) =>
              Classical.propDecidable (@Membership.mem Nat (Set Nat) (@Set.instMembership Nat) (@Set.range Nat Nat f) a))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := fun hc_h => absurd (@hc_h (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  (simp <;> decide))

-- Turing.moveInputPos_pos_of_ne_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.moveInputPos_pos_of_ne_right.h2 : ¬∀ {n : ℕ} (p : Fin (n + 2)), ↑p ≠ n + 1 := fun hc_h => absurd (@hc_h (0) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Cslib.SKI.I_irreducible, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.I_irreducible.h1 : ¬∀ (a : Cslib.SKI), a = Cslib.SKI.I := fun hc_h => absurd (@hc_h (.S : Cslib.SKI)) (by
  decide +kernel)

-- Cslib.SKI.S_irreducible, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.S_irreducible.h1 : ¬∀ (a : Cslib.SKI), a = Cslib.SKI.S := fun hc_h => absurd (@hc_h (.K : Cslib.SKI)) (by
  decide +kernel)

-- Cslib.FLP.ZeroFaultAlg.safeConsensus, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.FLP.ZeroFaultAlg.safeConsensus.h1 : ¬∀ {n : ℕ}, 0 < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

