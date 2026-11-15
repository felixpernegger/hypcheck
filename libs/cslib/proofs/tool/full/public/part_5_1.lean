import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTm_substTm_var, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTm_substTm_var.h7 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var]
        {s : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var} {x y : Var}
        (t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var),
        s.LC →
          (t.openTm (Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.fvar y))[x := s] =
            t[x := s].openTm (Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.fvar y) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (1) (1) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTm_substTm_var, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTm_substTm_var.h8 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var]
        {s : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var} {x y : Var}
        (t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var),
        y ≠ x →
          (t.openTm (Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.fvar y))[x := s] =
            t[x := s].openTm (Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.fvar y) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (0) (1) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (by
  decide)) (by
  nofun)

-- Cslib.LTS.tr_setImage, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.tr_setImage.h8 : ¬∀ {State Label : Type} {S : Set State} {s : State} {μ : Label} {s' : State} {lts : Cslib.LTS State Label},
        s ∈ S → s' ∈ lts.setImage S μ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (0) (0) (0) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (by
  decide)) (by
  nofun)

-- Cslib.LTS.Execution.tail_of_length_pos, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.tail_of_length_pos.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        0 < μs.length → lts.Execution s μs t ss := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([0]) (0) ([]) (by
  decide)) (by
  nofun)

-- Cslib.LTS.Execution.tail_of_length_pos, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.tail_of_length_pos.h8 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        lts.Execution s μs t ss → 0 < μs.length := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([0]) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- List.IsChainFromTo.reflTransGen_of_mem', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.reflTransGen_of_mem'.h5 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a : α} {b x : α}, x ∈ chain → Relation.ReflTransGen r x b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1]) (0) (0) (1) (by
  decide)) (by
  nofun)

-- List.IsChainFromTo.reflTransGen_of_mem', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.reflTransGen_of_mem'.h7 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b : α},
        List.IsChainFromTo r chain a b → ∀ {x : α}, Relation.ReflTransGen r x b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) (0) (by
  simp) (1)) (by
  nofun)

-- List.IsChainFromTo.take, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.take.h7 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b : α},
        List.IsChainFromTo r chain a b → ∀ {i : ℕ}, i < chain.length := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) (0) (by
  simp) (1)) (by
  decide +kernel)

-- Cslib.ωSequence.append_left_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.append_left_injective.h5 : ¬∀ {α : Type} (x y : List α) (a b : Cslib.ωSequence α), x.length = y.length → x = y := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([1]) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (by
  decide)) (by
  decide +kernel)

-- Turing.HeadSymbols.ext, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.HeadSymbols.ext.h4 : ¬∀ {k : ℕ} {Symbol : Type} {x y : Turing.HeadSymbols k Symbol}, x.workTapeSymbols = y.workTapeSymbols → x = y := fun hc_h => absurd (@hc_h (0) (ℕ) ({ inputSymbol := Option.none, workTapeSymbols := fun (a : Fin 0) => Option.none : Turing.HeadSymbols 0 ℕ }) ({ inputSymbol := Option.some 0, workTapeSymbols := fun (a : Fin 0) => Option.none : Turing.HeadSymbols 0 ℕ }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Turing.HeadSymbols.ext, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.HeadSymbols.ext.h5 : ¬∀ {k : ℕ} {Symbol : Type} {x y : Turing.HeadSymbols k Symbol}, x.inputSymbol = y.inputSymbol → x = y := fun hc_h => absurd (@hc_h (1) (ℕ) ({ inputSymbol := Option.none, workTapeSymbols := fun (a : Fin 1) => Option.none : Turing.HeadSymbols 1 ℕ }) ({ inputSymbol := Option.none, workTapeSymbols := fun (a : Fin 1) => Option.some 0 : Turing.HeadSymbols 1 ℕ }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  (simp <;> decide))

-- Cslib.Computability.Turing.SingleTape.Cfg.ext, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Computability.Turing.SingleTape.Cfg.ext.h4 : Not
      (∀ {State Symbol : Type} {x y : Cslib.Computability.Turing.SingleTape.Cfg State Symbol},
        @Eq (Cslib.Turing.BiTape Symbol) (@Cslib.Computability.Turing.SingleTape.Cfg.tape State Symbol x)
            (@Cslib.Computability.Turing.SingleTape.Cfg.tape State Symbol y) →
          @Eq (Cslib.Computability.Turing.SingleTape.Cfg State Symbol) x y) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Cslib.Computability.Turing.SingleTape.Cfg.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Cslib.Turing.BiTape.mk Nat (@Option.none Nat)
        (@Cslib.Turing.StackTape.mk Nat (@List.nil (Option Nat))
          (@of_decide_eq_true
            (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
              (@Option.some (Option Nat) (@Option.none Nat)))
            (@instDecidableNot
              (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                (@Option.some (Option Nat) (@Option.none Nat)))
              (@Option.instDecidableEq (Option Nat)
                (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                (@List.getLast? (Option Nat) (@List.nil (Option Nat))) (@Option.some (Option Nat) (@Option.none Nat))))
            (@id
              (@Eq Bool
                (@Decidable.decide
                  (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                    (@Option.some (Option Nat) (@Option.none Nat)))
                  (@instDecidableNot
                    (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))
                    (@Option.instDecidableEq (Option Nat)
                      (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                      (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))))
                Bool.true)
              (@Eq.refl Bool Bool.true))))
        (@Cslib.Turing.StackTape.mk Nat (@List.nil (Option Nat))
          (@of_decide_eq_true
            (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
              (@Option.some (Option Nat) (@Option.none Nat)))
            (@instDecidableNot
              (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                (@Option.some (Option Nat) (@Option.none Nat)))
              (@Option.instDecidableEq (Option Nat)
                (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                (@List.getLast? (Option Nat) (@List.nil (Option Nat))) (@Option.some (Option Nat) (@Option.none Nat))))
            (@id
              (@Eq Bool
                (@Decidable.decide
                  (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                    (@Option.some (Option Nat) (@Option.none Nat)))
                  (@instDecidableNot
                    (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))
                    (@Option.instDecidableEq (Option Nat)
                      (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                      (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))))
                Bool.true)
              (@Eq.refl Bool Bool.true)))))) (@Cslib.Computability.Turing.SingleTape.Cfg.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Cslib.Turing.BiTape.mk Nat (@Option.none Nat)
        (@Cslib.Turing.StackTape.mk Nat (@List.nil (Option Nat))
          (@of_decide_eq_true
            (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
              (@Option.some (Option Nat) (@Option.none Nat)))
            (@instDecidableNot
              (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                (@Option.some (Option Nat) (@Option.none Nat)))
              (@Option.instDecidableEq (Option Nat)
                (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                (@List.getLast? (Option Nat) (@List.nil (Option Nat))) (@Option.some (Option Nat) (@Option.none Nat))))
            (@id
              (@Eq Bool
                (@Decidable.decide
                  (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                    (@Option.some (Option Nat) (@Option.none Nat)))
                  (@instDecidableNot
                    (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))
                    (@Option.instDecidableEq (Option Nat)
                      (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                      (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))))
                Bool.true)
              (@Eq.refl Bool Bool.true))))
        (@Cslib.Turing.StackTape.mk Nat (@List.nil (Option Nat))
          (@of_decide_eq_true
            (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
              (@Option.some (Option Nat) (@Option.none Nat)))
            (@instDecidableNot
              (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                (@Option.some (Option Nat) (@Option.none Nat)))
              (@Option.instDecidableEq (Option Nat)
                (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                (@List.getLast? (Option Nat) (@List.nil (Option Nat))) (@Option.some (Option Nat) (@Option.none Nat))))
            (@id
              (@Eq Bool
                (@Decidable.decide
                  (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                    (@Option.some (Option Nat) (@Option.none Nat)))
                  (@instDecidableNot
                    (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))
                    (@Option.instDecidableEq (Option Nat)
                      (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                      (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))))
                Bool.true)
              (@Eq.refl Bool Bool.true)))))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Cslib.Computability.Turing.SingleTape.Cfg.ext, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Computability.Turing.SingleTape.Cfg.ext.h5 : Not
      (∀ {State Symbol : Type} {x y : Cslib.Computability.Turing.SingleTape.Cfg State Symbol},
        @Eq State (@Cslib.Computability.Turing.SingleTape.Cfg.state State Symbol x)
            (@Cslib.Computability.Turing.SingleTape.Cfg.state State Symbol y) →
          @Eq (Cslib.Computability.Turing.SingleTape.Cfg State Symbol) x y) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Cslib.Computability.Turing.SingleTape.Cfg.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Cslib.Turing.BiTape.mk Nat (@Option.none Nat)
        (@Cslib.Turing.StackTape.mk Nat (@List.nil (Option Nat))
          (@of_decide_eq_true
            (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
              (@Option.some (Option Nat) (@Option.none Nat)))
            (@instDecidableNot
              (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                (@Option.some (Option Nat) (@Option.none Nat)))
              (@Option.instDecidableEq (Option Nat)
                (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                (@List.getLast? (Option Nat) (@List.nil (Option Nat))) (@Option.some (Option Nat) (@Option.none Nat))))
            (@id
              (@Eq Bool
                (@Decidable.decide
                  (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                    (@Option.some (Option Nat) (@Option.none Nat)))
                  (@instDecidableNot
                    (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))
                    (@Option.instDecidableEq (Option Nat)
                      (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                      (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))))
                Bool.true)
              (@Eq.refl Bool Bool.true))))
        (@Cslib.Turing.StackTape.mk Nat (@List.nil (Option Nat))
          (@of_decide_eq_true
            (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
              (@Option.some (Option Nat) (@Option.none Nat)))
            (@instDecidableNot
              (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                (@Option.some (Option Nat) (@Option.none Nat)))
              (@Option.instDecidableEq (Option Nat)
                (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                (@List.getLast? (Option Nat) (@List.nil (Option Nat))) (@Option.some (Option Nat) (@Option.none Nat))))
            (@id
              (@Eq Bool
                (@Decidable.decide
                  (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                    (@Option.some (Option Nat) (@Option.none Nat)))
                  (@instDecidableNot
                    (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))
                    (@Option.instDecidableEq (Option Nat)
                      (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                      (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))))
                Bool.true)
              (@Eq.refl Bool Bool.true)))))) (@Cslib.Computability.Turing.SingleTape.Cfg.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Cslib.Turing.BiTape.mk Nat (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Cslib.Turing.StackTape.mk Nat (@List.nil (Option Nat))
          (@of_decide_eq_true
            (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
              (@Option.some (Option Nat) (@Option.none Nat)))
            (@instDecidableNot
              (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                (@Option.some (Option Nat) (@Option.none Nat)))
              (@Option.instDecidableEq (Option Nat)
                (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                (@List.getLast? (Option Nat) (@List.nil (Option Nat))) (@Option.some (Option Nat) (@Option.none Nat))))
            (@id
              (@Eq Bool
                (@Decidable.decide
                  (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                    (@Option.some (Option Nat) (@Option.none Nat)))
                  (@instDecidableNot
                    (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))
                    (@Option.instDecidableEq (Option Nat)
                      (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                      (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))))
                Bool.true)
              (@Eq.refl Bool Bool.true))))
        (@Cslib.Turing.StackTape.mk Nat (@List.nil (Option Nat))
          (@of_decide_eq_true
            (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
              (@Option.some (Option Nat) (@Option.none Nat)))
            (@instDecidableNot
              (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                (@Option.some (Option Nat) (@Option.none Nat)))
              (@Option.instDecidableEq (Option Nat)
                (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                (@List.getLast? (Option Nat) (@List.nil (Option Nat))) (@Option.some (Option Nat) (@Option.none Nat))))
            (@id
              (@Eq Bool
                (@Decidable.decide
                  (@Ne (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                    (@Option.some (Option Nat) (@Option.none Nat)))
                  (@instDecidableNot
                    (@Eq (Option (Option Nat)) (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))
                    (@Option.instDecidableEq (Option Nat)
                      (fun (a b : Option Nat) => @Option.instDecidableEq Nat instDecidableEqNat a b)
                      (@List.getLast? (Option Nat) (@List.nil (Option Nat)))
                      (@Option.some (Option Nat) (@Option.none Nat)))))
                Bool.true)
              (@Eq.refl Bool Bool.true)))))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.redex_app_l_cong, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.redex_app_l_cong.h4 : ¬∀ {Var : Type} {M M' N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var},
        N.LC → Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta (M.app N) (M'.app N) := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_openRec, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_openRec.h8 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var] (x : Var)
        (t : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (k : ℕ)
        (u e : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec k u e)[x := t] =
          Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec k u[x := t] e[x := t] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  decide +kernel)

-- Cslib.Automata.εNA.FinAcc.concat_mTr_inr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.εNA.FinAcc.concat_mTr_inr.h8 : ¬∀ {Symbol S₁ S₂ : Type} {a : Cslib.Automata.εNA.FinAcc S₁ Symbol} {b : Cslib.Automata.εNA.FinAcc S₂ Symbol} {s t : S₂}
        {μs : List (Option Symbol)}, b.MTr s μs t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({ Tr := fun (a : ℕ) (a_1 : Option ℕ) (n : ℕ) => n = 0, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.εNA.FinAcc ℕ ℕ }) ({ Tr := fun (a : ℕ) (a_1 : Option ℕ) (n : ℕ) => n = 0, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.εNA.FinAcc ℕ ℕ }) (0) (1) ([])) (by
  simp)

-- Cslib.SKI.eq_of_join_mRed_redexFree, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.eq_of_join_mRed_redexFree.h2 : ¬∀ {x y : Cslib.SKI}, x.RedexFree → y.RedexFree → x = y := fun hc_h => absurd (@hc_h (.S : Cslib.SKI) (.K : Cslib.SKI) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Cslib.SKI.eq_of_join_mRed_redexFree, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.eq_of_join_mRed_redexFree.h4 : ¬∀ {x y : Cslib.SKI}, Relation.Join (Relation.ReflTransGen Cslib.SKI.Red) x y → x.RedexFree → x = y := fun hc_h => absurd (@hc_h (.I : Cslib.SKI) (.app .I .I : Cslib.SKI) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  decide +kernel)

-- Cslib.ωSequence.extract_eq_extract, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.extract_eq_extract.h7 : ¬∀ {α : Type} {xs xs' : Cslib.ωSequence α} {m n m' n' : ℕ}, n - m = n' - m' ∧ ∀ k < n - m, xs (m + k) = xs' (m' + k) := fun hc_h => absurd (@hc_h (ℕ) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (0) (0) (0) (1)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.strengthen, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.strengthen.h7 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {τ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var}
        {X : Var}, Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf (Γ ++ Δ) σ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0)) (by
  nofun)

-- Cslib.LTS.Execution.length, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.length.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        ss.length = μs.length + 1 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([])) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_fv, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.steps_fv.h5 : ¬∀ {Var : Type} {M M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], M.fv = M'.fv := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat)) (by
  decide +kernel)

-- Cslib.URM.State.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.URM.State.ext.h2 : ¬∀ {s₁ s₂ : Cslib.URM.State}, s₁.regs = s₂.regs → s₁ = s₂ := fun hc_h => absurd (@hc_h ({ pc := 0, regs := fun (a : ℕ) => 0 : Cslib.URM.State }) ({ pc := 1, regs := fun (a : ℕ) => 0 : Cslib.URM.State }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_lc_or_rfl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.steps_lc_or_rfl.h5 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var]
        {M M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, M.LC ∧ M'.LC ∨ M = M' := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_lc_r, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_lc_r.h5 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var],
        M'.LC := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_not_fv, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_not_fv.h5 : ¬∀ {Var : Type} {M M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var], M.fv = M'.fv := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_close, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_close.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] (x : Var) (t : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (k : ℕ),
        t =
          Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.closeRec k x
            (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec k
              (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x) t) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0)) (by
  decide +kernel)

-- Cslib.Automata.εNA.FinAcc.toSingleStartAccept_mTr_inr_inl_true, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.εNA.FinAcc.toSingleStartAccept_mTr_inr_inl_true.h5 : ¬∀ {State Symbol : Type} {a : Cslib.Automata.εNA.FinAcc State Symbol} {s : State} {μs : List (Option Symbol)},
        ∃ t ∈ a.accept, ∃ (μs' : List (Option Symbol)), μs = μs' ++ [Option.none] ∧ a.MTr s μs' t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a : ℕ) (a_1 : Option ℕ) (n : ℕ) => n = 0, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.εNA.FinAcc ℕ ℕ }) (0) ([])) (by
  simp)

-- Relation.RelatesInSteps.succ', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesInSteps.succ'.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} {n : ℕ}, ∃ (t' : α), r a t' ∧ Relation.RelatesInSteps r t' b n := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (0)) (by
  simp)

-- Relation.dom_cod_leftEuclidean, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.dom_cod_leftEuclidean.h3 : ¬∀ {α : Type} {r : α → α → Prop}, Relation.dom r = Relation.cod r → Relation.LeftEuclidean r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) : ℕ → ℕ → Prop) (by
  grind)) (by
  exact fun hc_c =>
    absurd
      (hc_c.leftEuclidean (a := (0 : ℕ)) (b := (0 : ℕ)) (c := (1 : ℕ))
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

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.invert_abs_multiApp_st, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.invert_abs_multiApp_st.h5 : ¬∀ {Var : Type} {Ps : List (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var)}
        {M N Q : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var},
        (∃ (M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
            M.abs.FullBeta M'.abs ∧ Q = (M'.abs.app N).multiApp Ps) ∨
          (∃ (N' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var), N.FullBeta N' ∧ Q = (M.abs.app N').multiApp Ps) ∨
            (∃ (Ps' : List (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var)),
                Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.ListFullBeta Ps Ps' ∧ Q = (M.abs.app N).multiApp Ps') ∨
              Q = (M.open' N).multiApp Ps := fun hc_h => absurd (@hc_h (ℕ) ([]) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  nofun)

-- Cslib.ωSequence.extract_0u_extract_lu, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.extract_0u_extract_lu.h5 : ¬∀ {α : Type} {xs : Cslib.ωSequence α} {n i j : ℕ}, (xs.extract 0 n).extract i j = xs.extract i j := fun hc_h => absurd (@hc_h (ℕ) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (0) (0) (1)) (by
  decide +kernel)

-- Relation.LeftEuclidean.instSymmOfRefl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.LeftEuclidean.instSymmOfRefl.h2 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Refl r], Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) _) (by
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

-- Relation.LeftEuclidean.instSymmOfRefl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.LeftEuclidean.instSymmOfRefl.h3 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Relation.LeftEuclidean r], Std.Symm r := fun hc_h => absurd (@hc_h (Bool) (fun a _ => a = false : Bool → Bool → Prop) (@Relation.LeftEuclidean.mk (Bool) (fun (a x : Bool) => @Eq Bool a Bool.false) (by (try dsimp only);   decide))) (by
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

-- Relation.LeftEuclidean.trichotomous_trans, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.LeftEuclidean.trichotomous_trans.h2 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Trichotomous r], IsTrans α r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≠ b : ℕ → ℕ → Prop) (@Std.Trichotomous.mk (Nat) (fun (a b : Nat) => @Ne Nat a b) (by (try dsimp only);   (intros; omega)))) (by
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

-- Cslib.ωSequence.get_append_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.get_append_left.h4 : ¬∀ {α : Type} (n : ℕ) (x : List α) (a : Cslib.ωSequence α), n < x.length := fun hc_h => absurd (@hc_h (ℕ) (0) ([]) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ })) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.cbn_not_isAbs, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.cbn_not_isAbs.h3 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, ¬M.IsAbs := fun hc_h => absurd (@hc_h (ℕ) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_lc_l, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_lc_l.h3 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, M.LC := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  nofun)

-- Cslib.Probability.PMF.uniformOfFinset_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Probability.PMF.uniformOfFinset_apply.h2 : ¬∀ {α : Type} (s : Finset α) (a : α), s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (∅ : Finset ℕ) (0)) (by
  decide +kernel)

-- Relation.Convergent.unique_Normal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.Convergent.unique_Normal.h2 : ¬∀ {α : Type} {r : α → α → Prop} (a : α), ∃! n : α, Relation.ReflTransGen r a n ∧ Relation.Normal r n := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (Bool.false)) (by
  simp)

-- Turing.moveInputPos_neg_of_ne_left, hypothesis 2: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Turing.moveInputPos_neg_of_ne_left.h2.gneg : ∀ {n : ℕ} (p : Fin (n + 2)), ¬p ≠ 0 → Turing.moveInputPos p SignType.neg = (⟨↑p - 1, (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)⟩ : Fin (n + 2)) := by
  (intros; simp_all; done)
theorem HypCheckProof.Turing.moveInputPos_neg_of_ne_left.h2 : ∀ {n : ℕ} (p : Fin (n + 2)), Turing.moveInputPos p SignType.neg = (⟨↑p - 1, (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)⟩ : Fin (n + 2)) := by
  intro hc_x0 hc_x1
  exact Classical.byCases (fun hc_h => @Turing.moveInputPos_neg_of_ne_left hc_x0 hc_x1 hc_h) (fun hc_hn => @HypCheckProof.Turing.moveInputPos_neg_of_ne_left.h2.gneg hc_x0 hc_x1 hc_hn)

