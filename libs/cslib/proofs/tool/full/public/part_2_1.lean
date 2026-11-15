import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Cslib.LTS.IsSimulationMap.sim_trace, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.IsSimulationMap.sim_trace.h6 : ¬∀ {State₁ Label State₂ : Type} {lts₁ : Cslib.LTS State₁ Label} {lts₂ : Cslib.LTS State₂ Label} {f : State₁ → State₂}
        {s s' : State₁} {μs : List Label}, lts₁.MTr s μs s' → lts₂.MTr (f s) μs (f s') := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) ({ Tr := fun (a : ℕ) (a_1 : Bool) (n : ℕ) => n = 0 : Cslib.LTS ℕ Bool }) ({ Tr := fun (a : ℕ) (a_1 : Bool) (n : ℕ) => n = 0 : Cslib.LTS ℕ Bool }) (fun n => n + 1 : ℕ → ℕ) (0) (0) ([Bool.false]) (by
  simp)) (by
  simp)

-- Cslib.LTS.pairLang_append_pairViaLang, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.pairLang_append_pairViaLang.h9 : ¬∀ {Symbol State : Type} {lts : Cslib.LTS State Symbol} {s0 s1 s2 : State} {xs1 xs2 : List Symbol} {via : Set State},
        xs2 ∈ lts.pairViaLang via s1 s2 → xs1 ++ xs2 ∈ lts.pairViaLang via s0 s2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (1) (0) (0) ([]) ([]) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Cslib.LTS.pairLang_append_pairViaLang, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.pairLang_append_pairViaLang.h10 : ¬∀ {Symbol State : Type} {lts : Cslib.LTS State Symbol} {s0 s1 s2 : State} {xs1 xs2 : List Symbol} {via : Set State},
        xs1 ∈ lts.pairLang s0 s1 → xs1 ++ xs2 ∈ lts.pairViaLang via s0 s2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) (1) ([]) ([]) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.step_multiApp_r, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.step_multiApp_r.h4 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {Ns Ns' : List (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var)},
        M.LC → (M.multiApp Ns).FullBeta (M.multiApp Ns') := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) ([]) ([]) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.SKI.eq_of_mJoin_red_redexFree, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.eq_of_mJoin_red_redexFree.h2 : ¬∀ {x y : Cslib.SKI}, x.RedexFree → y.RedexFree → x = y := fun hc_h => absurd (@hc_h (.S : Cslib.SKI) (.K : Cslib.SKI) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Cslib.SKI.eq_of_mJoin_red_redexFree, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.eq_of_mJoin_red_redexFree.h4 : ¬∀ {x y : Cslib.SKI}, Relation.Join (Relation.ReflTransGen Cslib.SKI.Red) x y → x.RedexFree → x = y := fun hc_h => absurd (@hc_h (.I : Cslib.SKI) (.app .I .I : Cslib.SKI) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_cbn, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_cbn.h3 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, N.LC → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_cbn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_cbn.h4 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var},
        Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN M N → M.Standard N := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  rfl)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Context.mapVal_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Context.mapVal_mem.h6 : ¬∀ {α β : Type} [inst : DecidableEq α] {Γ : Cslib.LambdaCalculus.LocallyNameless.Context α β} {x : α} {σ : β}
        (f : β → β), f σ ∈ List.dlookup x (Cslib.LambdaCalculus.LocallyNameless.Context.mapVal f Γ) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) ([]) (0) (0) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_isAbs_r, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_isAbs_r.h3 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, M.IsAbs → N.IsAbs := fun hc_h => absurd (@hc_h (ℕ) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  decide)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_isAbs_r, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_isAbs_r.h4 : ¬∀ {Var : Type} {M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var},
        Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost M N → N.IsAbs := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  rfl)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec_lc, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec_lc.h6 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var] {X : ℕ}
        {σ τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        σ = Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec X τ σ := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ)) (by
  nofun)

-- Cslib.ωSequence.take_extract, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.take_extract.h5 : ¬∀ {α : Type} {xs : Cslib.ωSequence α} {m n k : ℕ}, List.take k (xs.extract m n) = xs.extract m (m + k) := fun hc_h => absurd (@hc_h (ℕ) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (0) (0) (1)) (by
  decide +kernel)

-- Cslib.FinFun.eq_fields_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.FinFun.eq_fields_eq.h5 : Not
      (∀ {β α : Type} [inst : Zero β] {f g : @Cslib.FinFun α β inst},
        And (@Eq (α → β) (@Cslib.FinFun.fn α β inst f) (@Cslib.FinFun.fn α β inst g))
          (@Eq (Finset α) (@Cslib.FinFun.support α β inst f) (@Cslib.FinFun.support α β inst g))) := fun hc_h => absurd (@hc_h (Nat) (Bool) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (@Cslib.FinFun.mk Bool Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)
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

-- Cslib.SKI.rice, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.rice.h1 : ¬∀ {P : Cslib.SKI},
        (∃ (x : Cslib.SKI), Relation.ReflTransGen Cslib.SKI.Red (P.app x) Cslib.SKI.TT) →
          (∃ (x : Cslib.SKI), Relation.ReflTransGen Cslib.SKI.Red (P.app x) Cslib.SKI.FF) → False := fun hc_h => absurd (@hc_h (.I : Cslib.SKI) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Relation.RightEuclidean.rightUnique_antisymm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RightEuclidean.rightUnique_antisymm.h3 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Relation.RightEuclidean r], Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (@Relation.RightEuclidean.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
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

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.Red.lc, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.Red.lc.h5 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var]
        {t t' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var}, t.LC ∧ t'.LC := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ)) (by
  nofun)

-- List.IsChainFromTo.length_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.length_pos.h5 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b : α}, 0 < chain.length := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (0)) (by
  decide +kernel)

-- Relation.instRightEuclideanElemValMemSet, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.instRightEuclideanElemValMemSet.h2 : ¬∀ {α : Type} {r : α → α → Prop} (s : Set α), Relation.RightEuclidean fun (a b : ↑s) => r ↑a ↑b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ({n : ℕ | n % 2 = 0})) (by
  exact fun hc_c =>
    absurd
      (hc_c.rightEuclidean (a :=
        ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }) :
          { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }))
        (b :=
        ((⟨2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }) :
          { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }))
        (c :=
        ((⟨2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }) :
          { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }))
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

-- Relation.RightEuclidean.leftEuclidean_swap, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RightEuclidean.leftEuclidean_swap.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Relation.LeftEuclidean fun (a b : α) => r b a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.leftEuclidean (a := (1 : ℕ)) (b := (1 : ℕ)) (c := (0 : ℕ))
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

-- Cslib.ωSequence.strictMono_of_infinite, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.strictMono_of_infinite.h1 : ¬∀ {ns : Set ℕ}, ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Set.range φ = ns := fun hc_h => absurd (@hc_h ({x : ℕ | False})) (by
  simp)

