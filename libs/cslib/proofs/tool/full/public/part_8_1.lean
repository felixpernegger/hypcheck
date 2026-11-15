import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_eq_app, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_eq_app.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var] {x : Var}
        {m n : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var},
        x ∉ m.fv →
          m.LC →
            n.open' (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) =
                m.app (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) →
              n = m.app (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.bvar 0) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (1) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.app (.fvar 0) (.fvar 1) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  decide) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_eq_app, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_eq_app.h9 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var] {x : Var}
        {m n : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var},
        x ∉ n.fv → x ∉ m.fv → m.LC → n = m.app (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.bvar 0) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (1) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  decide) (by
  decide) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Cslib.LTS.Execution.comp, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.comp.h10 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s r t : State} {μs₁ μs₂ : List Label} {ss₁ ss₂ : List State},
        lts.Execution r μs₂ t ss₂ → lts.Execution s (μs₁ ++ μs₂) t (ss₁ ++ ss₂.tail) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) (0) ([]) ([]) ([]) ([0]) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LTS.Execution.comp, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.comp.h11 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s r t : State} {μs₁ μs₂ : List Label} {ss₁ ss₂ : List State},
        lts.Execution s μs₁ r ss₁ → lts.Execution s (μs₁ ++ μs₂) t (ss₁ ++ ss₂.tail) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) (0) ([]) ([0]) ([0]) ([]) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiApp_steps_lc, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiApp_steps_lc.h5 : ¬∀ {Var : Type} {Ns Ns' : List (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var)} [inst : DecidableEq Var]
        [inst : Cslib.HasFresh Var], (∀ N ∈ Ns, N.LC) → ∀ N ∈ Ns', N.LC := fun hc_h => absurd (@hc_h (ℕ) ([]) ([Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.bvar 0]) (instDecidableEqNat) (Cslib.instHasFreshNat) (by
  decide) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  decide)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiApp_steps_lc, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.multiApp_steps_lc.h8 : ¬∀ {Var : Type} {Ns Ns' : List (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var)} [inst : DecidableEq Var]
        [inst : Cslib.HasFresh Var],
        Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.ListFullBeta Ns Ns' →
          (∀ N ∈ Ns, N.LC) → ∀ (N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var), N.LC := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (instDecidableEqNat) (Cslib.instHasFreshNat) (by
  rfl) (by
  decide) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  nofun)

-- Cslib.LTS.pairViaLang_append_pairLang, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.pairViaLang_append_pairLang.h9 : ¬∀ {Symbol State : Type} {lts : Cslib.LTS State Symbol} {s0 s1 s2 : State} {xs1 xs2 : List Symbol} {via : Set State},
        xs2 ∈ lts.pairLang s1 s2 → xs1 ++ xs2 ∈ lts.pairViaLang via s0 s2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (1) (0) (0) ([]) ([]) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Cslib.LTS.pairViaLang_append_pairLang, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.pairViaLang_append_pairLang.h10 : ¬∀ {Symbol State : Type} {lts : Cslib.LTS State Symbol} {s0 s1 s2 : State} {xs1 xs2 : List Symbol} {via : Set State},
        xs1 ∈ lts.pairViaLang via s0 s1 → xs1 ++ xs2 ∈ lts.pairViaLang via s0 s2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) (1) ([]) ([]) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Cslib.LTS.Execution.trans, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.trans.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        ∀ k < μs.length, lts.Execution s μs t ss := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([0]) (0) ([]) (0) (by
  decide)) (by
  nofun)

-- Cslib.LTS.Execution.trans, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.trans.h9 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        lts.Execution s μs t ss → ∀ (k : ℕ), k < μs.length := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([0]) (by
  (repeat' constructor) <;> done) (0)) (by
  decide +kernel)

-- Cslib.LTS.MTr.comp, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.MTr.comp.h8 : ¬∀ {State Label : Type} (lts : Cslib.LTS State Label) {s1 : State} {μs1 : List Label} {s2 : State} {μs2 : List Label}
        {s3 : State}, lts.MTr s2 μs2 s3 → lts.MTr s1 (μs1 ++ μs2) s3 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([0]) (0) ([]) (0) (by
  simp)) (by
  simp)

-- Cslib.LTS.MTr.comp, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.MTr.comp.h9 : ¬∀ {State Label : Type} (lts : Cslib.LTS State Label) {s1 : State} {μs1 : List Label} {s2 : State} {μs2 : List Label}
        {s3 : State}, lts.MTr s1 μs1 s2 → lts.MTr s1 (μs1 ++ μs2) s3 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([]) (1) (by
  simp)) (by
  simp)

-- Relation.LeftEuclidean.leftEuclidean, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.LeftEuclidean.leftEuclidean.h2.inst : ¬(fun (a b : ℕ) => a < b) 0 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.LeftEuclidean.leftEuclidean.h2.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.LeftEuclidean.leftEuclidean.h2.prem1 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Relation.LeftEuclidean.leftEuclidean.h2 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, r a c → r b c → r a b := fun hc_h => HypCheckProof.Relation.LeftEuclidean.leftEuclidean.h2.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (0) (0) (1) HypCheckProof.Relation.LeftEuclidean.leftEuclidean.h2.prem0 HypCheckProof.Relation.LeftEuclidean.leftEuclidean.h2.prem1)

-- Relation.LeftEuclidean.leftEuclidean, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.LeftEuclidean.leftEuclidean.h6 : ¬∀ {α : Type} {r : α → α → Prop} [self : Relation.LeftEuclidean r] {a b c : α}, r b c → r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (@Relation.LeftEuclidean.mk (Nat) (fun (a b : Nat) => @Eq Nat a b) (by (try dsimp only);   (intros; omega))) (1) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Relation.LeftEuclidean.leftEuclidean, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.LeftEuclidean.leftEuclidean.h7 : ¬∀ {α : Type} {r : α → α → Prop} [self : Relation.LeftEuclidean r] {a b c : α}, r a c → r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (@Relation.LeftEuclidean.mk (Nat) (fun (a b : Nat) => @Eq Nat a b) (by (try dsimp only);   (intros; omega))) (0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Set.SymmOn.of_dom, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.SymmOn.of_dom.h5.inst : ¬(fun (a b : ℕ) => a ≤ b) 1 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.SymmOn.of_dom.h5.prem0 : (fun (a b : ℕ) => a ≤ b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.SymmOn.of_dom.h5.prem1 : (fun (a b : ℕ) => a ≤ b) 1 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.SymmOn.of_dom.h5 : ¬∀ {α : Type} {a b c : α} {r : α → α → Prop}, r a b → r b c → r b a := fun hc_h => HypCheckProof.Set.SymmOn.of_dom.h5.inst (@hc_h (ℕ) (0) (1) (1) (fun (a b : ℕ) => a ≤ b) HypCheckProof.Set.SymmOn.of_dom.h5.prem0 HypCheckProof.Set.SymmOn.of_dom.h5.prem1)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.nmem_fv, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.nmem_fv.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        [inst_1 : Cslib.HasFresh Var] {X : Var} {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        X ∉ Cslib.LambdaCalculus.LocallyNameless.Context.dom Γ → X ∉ σ.fv := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (Cslib.instHasFreshNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.trans, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.trans.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ τ δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ δ τ → Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ σ τ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.trans, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.trans.h7 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ τ δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ σ δ → Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Γ σ τ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.Automata.NA.totalize_run_mtr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.NA.totalize_run_mtr.h6 : ¬∀ {Symbol State : Type} {na : Cslib.Automata.NA State Symbol} {xs : Cslib.ωSequence Symbol}
        {ss : Cslib.ωSequence (Option State)} {n : ℕ},
        (ss n).isSome = Bool.true →
          ∃ (s : State) (t : State),
            na.MTr s (Cslib.ωSequence.take n xs) t ∧ s ∈ na.start ∧ ss 0 = Option.some s ∧ ss n = Option.some t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b, start := {n : ℕ | n = 0} : Cslib.Automata.NA ℕ ℕ }) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) ({ get := Option.some : Cslib.ωSequence (Option ℕ) }) (1) (by
  decide)) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_lc, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_lc.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var] {x : Var}
        {e u : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, u.LC → e[x := u].LC := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_lc, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_lc.h7 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var] {x : Var}
        {e u : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, e.LC → e[x := u].LC := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.substTy_lc, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.substTy_lc.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] {t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var}
        {δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} [inst_1 : Cslib.HasFresh Var],
        δ.LC → ∀ (X : Var), t[X := δ].LC := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (Cslib.instHasFreshNat) (by
  (repeat' constructor) <;> done) (0)) (by
  nofun)

-- List.IsChainFromTo.relatesInSteps, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.relatesInSteps.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} {chain : List α} {n : ℕ},
        chain.length = n + 1 → Relation.RelatesInSteps r a b n := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (1) ([0]) (0) (by
  decide)) (by
  simp)

-- List.IsChainFromTo.relatesInSteps, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.relatesInSteps.h7 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} {chain : List α} {n : ℕ},
        List.IsChainFromTo r chain a b → Relation.RelatesInSteps r a b n := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) ([0]) (1) (by
  simp)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.substTm_lc, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.substTm_lc.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] {t s : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var}
        [inst_1 : Cslib.HasFresh Var], s.LC → ∀ (x : Var), t[x := s].LC := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (Cslib.instHasFreshNat) (by
  (repeat' constructor) <;> done) (0)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.substTm_lc, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.substTm_lc.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] {t s : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var}
        [inst_1 : Cslib.HasFresh Var], t.LC → ∀ (x : Var), t[x := s].LC := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (Cslib.instHasFreshNat) (by
  (repeat' constructor) <;> done) (0)) (by
  nofun)

-- Relation.Join₂.single_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Join₂.single_left.h5 : ¬∀ {α : Type} {r₁ r₂ : α → α → Prop} {a b : α}, r₁ a b → Relation.Join₂ r₁ r₂ a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  nofun)

-- Relation.Join₂.single_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Join₂.single_left.h6 : ¬∀ {α : Type} {r₁ r₂ : α → α → Prop} {a b : α} [inst : Std.Refl r₂], Relation.Join₂ r₁ r₂ a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a = b : ℕ → ℕ → Prop) (0) (0) _) (by
  nofun)

-- Cslib.FinFun.update_comm, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.FinFun.update_comm.h10 : Not
      (∀ {β α : Type} [inst : Zero β] [inst_1 : DecidableEq α] [inst_2 : @Cslib.DecidableEqZero β inst] {a a' : α}
        {b b' : β} (f : @Cslib.FinFun α β inst),
        @Eq (@Cslib.FinFun α β inst)
          (@Cslib.FinFun.update β α inst inst_1 inst_2 (@Cslib.FinFun.update β α inst inst_1 inst_2 f a b) a' b')
          (@Cslib.FinFun.update β α inst inst_1 inst_2 (@Cslib.FinFun.update β α inst inst_1 inst_2 f a' b') a b)) := fun hc_h => absurd (@hc_h (Nat) (Bool) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (instDecidableEqBool) (fun (a : Nat) =>
      instDecidableEqNat a
        (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))) (Bool.false) (Bool.false) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Cslib.FinFun.mk Bool Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
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
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.listFullBeta_cons_l, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.listFullBeta_cons_l.h4 : ¬∀ {Var : Type} {Ns Ns' l : List (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var)},
        (∀ M ∈ l, M.LC) → Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.ListFullBeta (Ns ++ l) (Ns' ++ l) := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) ([]) (by
  decide)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.redex_app_r_cong, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.redex_app_r_cong.h4 : ¬∀ {Var : Type} {M M' N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var},
        N.LC → Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta (N.app M) (N.app M') := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Relation.Normal.reflTransGen_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Normal.reflTransGen_eq.h4 : ¬∀ {α : Type} {r : α → α → Prop} {x y : α}, Relation.ReflTransGen r x y → x = y := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (1) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Relation.Normal.reflTransGen_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Normal.reflTransGen_eq.h5 : ¬∀ {α : Type} {r : α → α → Prop} {x y : α}, Relation.Normal r x → x = y := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) (Bool.false) (Bool.true) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.neutral_steps, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.neutral_steps.h3 : ¬∀ {Var : Type} {t t' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var},
        Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta t t' → t'.Neutral := fun hc_h => absurd (@hc_h (ℕ) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  rfl)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.neutral_steps, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.neutral_steps.h4 : ¬∀ {Var : Type} {t t' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, t.Neutral → t'.Neutral := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.wf, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.wf.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var]
        {Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var} {t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var}
        {τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        Γ.Wf ∧ t.LC ∧ Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf Γ τ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.nmem_fv_openRec, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.nmem_fv_openRec.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}
        {γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {k : ℕ} {X : Var}, X ∉ σ.fv := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0) (0)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm_lc, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm_lc.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] {t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var}
        [inst : Cslib.HasFresh Var] {x : ℕ} {s : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var},
        t = Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm x s t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (Cslib.instHasFreshNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ)) (by
  nofun)

-- List.mergeSortM_pure, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mergeSortM_pure.h3 : Not
      (∀ {m : Type → Type} [inst : Monad m] {α : Type} (xs : List α) (le : α → α → Bool),
        @Eq (m (List α))
          (@List.mergeSortM m inst α xs fun (x y : α) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) Bool (le x y))
          (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List α) (@List.mergeSort α xs le))) := fun hc_h => absurd (@hc_h (Option : Type → Type) ({ pure := some, bind := fun _ _ => none } : Monad Option) (Nat) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))) (fun a b => a < b : Nat → Nat → Bool)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.lc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.lc.h4 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}, σ.LC := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ)) (by
  nofun)

-- Cslib.URM.Regs.write_read_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.URM.Regs.write_read_of_ne.h4 : ¬∀ (σ : Cslib.URM.Regs) (m n v : ℕ), (σ.write n v).read m = σ.read m := fun hc_h => absurd (@hc_h (fun _ => 0 : ℕ → ℕ) (0) (0) (1)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.lcAt_openRec_iff_lcAt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.lcAt_openRec_iff_lcAt.h4 : ¬∀ {Var : Type} (M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (i : ℕ),
        Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.LcAt i
            (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec i N M) =
          Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.LcAt (i + 1) M := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0)) (by
  decide +kernel)

-- Cslib.Crypto.PRG.Generator.ext, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Crypto.PRG.Generator.ext.h4 : ¬∀ {Seed Output : Type} {x y : Cslib.Crypto.PRG.Generator Seed Output}, x = y := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0 : Cslib.Crypto.PRG.Generator Bool ℕ }) ({ toFun := fun (x : Bool) => 0 : Cslib.Crypto.PRG.Generator Bool ℕ })) (by
  (simp <;> decide))

-- Cslib.ωSequence.take_prefix_take_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.take_prefix_take_left.h4 : ¬∀ {α : Type} (m n : ℕ) (a : Cslib.ωSequence α), Cslib.ωSequence.take m a <+: Cslib.ωSequence.take n a := fun hc_h => absurd (@hc_h (ℕ) (1) (0) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ })) (by
  decide +kernel)

-- Cslib.ωSequence.extract_append_zero_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.extract_append_zero_right.h4 : ¬∀ {α : Type} {xl : List α} {xs : Cslib.ωSequence α} {n : ℕ},
        (xl ++ω xs).extract 0 n = xl ++ xs.extract 0 (n - xl.length) := fun hc_h => absurd (@hc_h (ℕ) ([0]) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (0)) (by
  decide +kernel)

-- Cslib.Automata.εNA.FinAcc.toSingleStartAccept_tr_accept, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.εNA.FinAcc.toSingleStartAccept_tr_accept.h4 : ¬∀ {State Symbol : Type} {a : Cslib.Automata.εNA.FinAcc State Symbol} {s : State},
        a.toSingleStartAccept.Tr (Sum.inr s) Option.none (Sum.inl Bool.true) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a : ℕ) (a_1 : Option ℕ) (n : ℕ) => n = 0, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.εNA.FinAcc ℕ ℕ }) (1)) (by
  nofun)

-- Cslib.QueryComplexity.eq_restrict_support, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.QueryComplexity.eq_restrict_support.h3 : ¬∀ {n : ℕ} {C : Cslib.QueryComplexity.PartialAssignment n} {x : Cslib.BitString n},
        C = Cslib.QueryComplexity.restrict x (Cslib.QueryComplexity.support C) := fun hc_h => absurd (@hc_h (1) (fun (a : Fin 1) => Option.some Bool.false) (fun (a : Fin 1) => Bool.true)) (by
  decide +kernel)

-- Cslib.Probability.PMF.mem_support_uniformOfFinset_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Probability.PMF.mem_support_uniformOfFinset_iff.h2 : ¬∀ {α : Type} {s : Finset α} (a : α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (∅ : Finset ℕ) (0)) (by
  decide +kernel)

-- Cslib.Probability.PMF.uniformOfFintype_apply, hypothesis 2: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Cslib.Probability.PMF.uniformOfFintype_apply.h2.der.{u} : ∀ {α : Type u} [inst : Fintype α] (a : α), Nonempty α := by
  (intros; tauto)
theorem HypCheckProof.Cslib.Probability.PMF.uniformOfFintype_apply.h2.{u} : ∀ {α : Type u} [inst : Fintype α] (a : α),
      @Eq ENNReal
        (@DFunLike.coe (PMF α) α (fun (x : α) => ENNReal) (@PMF.instFunLike α)
          (@Cslib.Probability.PMF.uniformOfFintype α inst
            (@HypCheckProof.Cslib.Probability.PMF.uniformOfFintype_apply.h2.der α inst a))
          a)
        (@Inv.inv ENNReal ENNReal.instInv
          (@Nat.cast ENNReal
            (@AddMonoidWithOne.toNatCast ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
            (@Fintype.card α inst))) := by
  intro hc_x0 hc_x1 hc_x2
  exact @Cslib.Probability.PMF.uniformOfFintype_apply hc_x0 hc_x1 (@HypCheckProof.Cslib.Probability.PMF.uniformOfFintype_apply.h2.der hc_x0 hc_x1 hc_x2) hc_x2

-- Cslib.SKI.Sab_irreducible, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.Sab_irreducible.h3 : ¬∀ (a b c : Cslib.SKI),
        ∃ (a' : Cslib.SKI) (b' : Cslib.SKI),
          a.ParallelReduction a' ∧ b.ParallelReduction b' ∧ c = (Cslib.SKI.S.app a').app b' := fun hc_h => absurd (@hc_h (.S : Cslib.SKI) (.S : Cslib.SKI) (.S : Cslib.SKI)) (by
  simp)

