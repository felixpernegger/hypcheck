import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow.h10 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ Δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ τ δ δ' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {X : Var},
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub Δ δ δ' →
          Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub
            (Γ ++
              (⟨X, Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding.sub δ⟩ :
                  (_ : Var) × Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding Var) ::
                Δ)
            σ τ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LTS.Execution.split, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.split.h9 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        lts.Execution s μs t ss → ∀ {n : ℕ}, n < ss.length := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([0]) (by
  (repeat' constructor) <;> done) (1)) (by
  decide +kernel)

-- Turing.Storage.ext, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Turing.Storage.ext.h5 : ¬∀ {Symbol State : Type} {k : ℕ} {x y : Turing.Storage Symbol State k},
        x.workTapes = y.workTapes → x.workTapePos = y.workTapePos → x = y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) ({ state := Option.none, workTapes := fun (i : Fin 1) (a : ℤ) => Option.none, workTapePos := fun (i : Fin 1) => 0 :
      Turing.Storage ℕ ℕ 1 }) ({ state := Option.some 0, workTapes := fun (i : Fin 1) (a : ℤ) => Option.none, workTapePos := fun (i : Fin 1) => 0 :
      Turing.Storage ℕ ℕ 1 }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Finset.card_filter_not_le_card_filter_of_involution, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h6.inst : Not
      (@LE.le Nat instLENat
        (@Finset.card Bool
          ({x ∈ @Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true |
            Not ((fun (b : Bool) => @Eq Bool b Bool.false) x)}))
        (@Finset.card Bool
          ({b ∈ @Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true | @Eq Bool b Bool.false}))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h6.prem0 : ∀ (x : Bool),
      @Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
          (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) x →
        @Eq Bool x.not.not x := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h6.prem1 : ∀ (x : Bool),
      @Membership.mem Bool (Finset Bool) (@SetLike.instMembership (Finset Bool) Bool (@Finset.instSetLike Bool))
          (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) x →
        Or ((fun (b : Bool) => @Eq Bool b Bool.false) x) ((fun (b : Bool) => @Eq Bool b Bool.false) x.not) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h6 : Not
      (∀ {α : Type} {s : Finset α} {σ : α → α} {p : α → Prop} [inst : @DecidablePred α p],
        (∀ (x : α),
            @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x →
              @Eq α (σ (σ x)) x) →
          (∀ (x : α),
              @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x →
                Or (p x) (p (σ x))) →
            @LE.le Nat instLENat (@Finset.card α ({x ∈ s | Not (p x)})) (@Finset.card α (@Finset.filter α p inst s))) := fun hc_h => HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h6.inst (@hc_h (Bool) (@Singleton.singleton Bool (Finset Bool) (@Finset.instSingleton Bool) Bool.true) (Bool.not) (fun (b : Bool) => @Eq Bool b Bool.false) (fun (a : Bool) => instDecidableEqBool a Bool.false) HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h6.prem0 HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h6.prem1)

-- Finset.card_filter_not_le_card_filter_of_involution, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h7.inst : Not
      (@LE.le Nat instLENat
        (@Finset.card Nat
          ({x ∈
              @Singleton.singleton Nat (Finset Nat) (@Finset.instSingleton Nat)
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) |
            Not ((fun (x : Nat) => False) x)}))
        (@Finset.card Nat
          ({x ∈
              @Singleton.singleton Nat (Finset Nat) (@Finset.instSingleton Nat)
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) |
            False}))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h7.prem0 : ∀ (x : Nat),
      @Membership.mem Nat (Finset Nat) (@SetLike.instMembership (Finset Nat) Nat (@Finset.instSetLike Nat))
          (@Singleton.singleton Nat (Finset Nat) (@Finset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          x →
        @Eq Nat
          ((fun (x : Nat) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            ((fun (x : Nat) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x))
          x := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h7.prem1 : ∀ (x : Nat),
      @Membership.mem Nat (Finset Nat) (@SetLike.instMembership (Finset Nat) Nat (@Finset.instSetLike Nat))
          (@Singleton.singleton Nat (Finset Nat) (@Finset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          x →
        @Membership.mem Nat (Finset Nat) (@SetLike.instMembership (Finset Nat) Nat (@Finset.instSetLike Nat))
          (@Singleton.singleton Nat (Finset Nat) (@Finset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          ((fun (x : Nat) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h7 : Not
      (∀ {α : Type} {s : Finset α} {σ : α → α} {p : α → Prop} [inst : @DecidablePred α p],
        (∀ (x : α),
            @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x →
              @Eq α (σ (σ x)) x) →
          (∀ (x : α),
              @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s x →
                @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s (σ x)) →
            @LE.le Nat instLENat (@Finset.card α ({x ∈ s | Not (p x)})) (@Finset.card α (@Finset.filter α p inst s))) := fun hc_h => HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h7.inst (@hc_h (Nat) (@Singleton.singleton Nat (Finset Nat) (@Finset.instSingleton Nat)
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (fun (x : Nat) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun (x : Nat) => False) (fun (a : Nat) => instDecidableFalse) HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h7.prem0 HypCheckProof.Finset.card_filter_not_le_card_filter_of_involution.h7.prem1)

-- Relation.RelatesInSteps.trans, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesInSteps.trans.h7 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α} {n m : ℕ},
        Relation.RelatesInSteps r b c m → Relation.RelatesInSteps r a c (n + m) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (0) (1) (0) (by
  simp)) (by
  nofun)

-- Relation.RelatesInSteps.trans, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesInSteps.trans.h8 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α} {n m : ℕ},
        Relation.RelatesInSteps r a b n → Relation.RelatesInSteps r a c (n + m) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (0) (0) (1) (by
  simp)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_open_cong_l, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_open_cong_l.h7 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var]
        (s s' t : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (L : Finset Var),
        t.LC → (s.open' t).FullBeta (s'.open' t) := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (∅ : Finset ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.weaken, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.weaken.h7 : ¬∀ {Var : Type} [inst : DecidableEq Var] {Γ Δ Θ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var}
        {σ σ' : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var},
        (Γ ++ Δ ++ Θ).Wf → Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub (Γ ++ Δ ++ Θ) σ σ' := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) ([]) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- List.IsChainFromTo.append_tail, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.append_tail.h6 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b c : α} {chain' : List α},
        List.IsChainFromTo r chain' b c → List.IsChainFromTo r (chain ++ chain'.tail) a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (0) (0) ([0]) (by
  simp)) (by
  nofun)

-- List.IsChainFromTo.append_tail, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.append_tail.h8 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b c : α},
        List.IsChainFromTo r chain a b → ∀ {chain' : List α}, List.IsChainFromTo r (chain ++ chain'.tail) a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) (0) (1) (by
  simp) ([])) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.step_subst, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.CBN.step_subst.h7 : ¬∀ {Var : Type} {M M' N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var]
        [inst : DecidableEq Var] (x : Var), N.LC → M[x := N].CBN M'[x := N] := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_subst_cong_r, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta.step_subst_cong_r.h7 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var] {x : Var}
        (s t t' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        s.LC → Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullEta s[x := t] s[x := t'] := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- List.IsChainFromTo.append_dropLast, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.append_dropLast.h6 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b c : α} {chain' : List α},
        List.IsChainFromTo r chain' b c → List.IsChainFromTo r (chain.dropLast ++ chain') a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (1) (0) (0) ([0]) (by
  simp)) (by
  nofun)

-- List.IsChainFromTo.append_dropLast, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.append_dropLast.h8 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b c : α},
        List.IsChainFromTo r chain a b → ∀ {chain' : List α}, List.IsChainFromTo r (chain.dropLast ++ chain') a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) (0) (0) (by
  simp) ([])) (by
  nofun)

-- Cslib.LTS.mTr_setImage, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.mTr_setImage.h7 : ¬∀ {State Label : Type} {S : Set State} {s : State} {μs : List Label} {s' : State} {lts : Cslib.LTS State Label},
        lts.MTr s μs s' → s' ∈ lts.setImageMultistep S μs := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({b : Bool | b = Bool.true}) (Bool.false) ([]) (Bool.false) ({ Tr := fun (a : Bool) (a_1 : ℕ) (b : Bool) => b = Bool.true : Cslib.LTS Bool ℕ }) (by
  simp)) (by
  simp)

-- Cslib.LTS.mTr_setImage, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.mTr_setImage.h8 : ¬∀ {State Label : Type} {S : Set State} {s : State} {μs : List Label} {s' : State} {lts : Cslib.LTS State Label},
        s ∈ S → s' ∈ lts.setImageMultistep S μs := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (0) ([]) (1) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (by
  decide)) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm_neq_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm_neq_eq.h6 : ¬∀ {Var : Type} {t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var} {x y : ℕ}
        {s₁ s₂ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var},
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm y s₁ t =
            Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm x s₂
              (Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm y s₁ t) →
          t = Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm x s₂ t := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (0) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (by
  rfl)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm_neq_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm_neq_eq.h7 : ¬∀ {Var : Type} {t : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var} {x y : ℕ}
        {s₁ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var} {s₂ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var},
        x ≠ y → t = Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm x s₂ t := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (0) (1) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (by
  decide)) (by
  nofun)

-- Cslib.Algorithms.Lean.TimeM.min_all_merge, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Algorithms.Lean.TimeM.min_all_merge.h5 : ¬∀ {α : Type} [inst : LinearOrder α] (x : α) (xs ys : List α),
        Cslib.Algorithms.Lean.TimeM.MinOfList x ys →
          Cslib.Algorithms.Lean.TimeM.MinOfList x (Cslib.Algorithms.Lean.TimeM.merge xs ys).ret := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (1) ([0]) ([]) (by
  decide)) (by
  simp)

-- Cslib.Algorithms.Lean.TimeM.min_all_merge, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Algorithms.Lean.TimeM.min_all_merge.h6 : ¬∀ {α : Type} [inst : LinearOrder α] (x : α) (xs ys : List α),
        Cslib.Algorithms.Lean.TimeM.MinOfList x xs →
          Cslib.Algorithms.Lean.TimeM.MinOfList x (Cslib.Algorithms.Lean.TimeM.merge xs ys).ret := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (1) ([]) ([0]) (by
  decide)) (by
  simp)

-- Set.ReflOn.of_dom, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.ReflOn.of_dom.h4.inst : ¬(fun (a b : ℕ) => a < b) 0 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.ReflOn.of_dom.h4.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.ReflOn.of_dom.h4 : ¬∀ {α : Type} {a b : α} {r : α → α → Prop}, r a b → r a a := fun hc_h => HypCheckProof.Set.ReflOn.of_dom.h4.inst (@hc_h (ℕ) (0) (1) (fun (a b : ℕ) => a < b) HypCheckProof.Set.ReflOn.of_dom.h4.prem0)

-- Cslib.LTS.Execution.cons_invert, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.cons_invert.h8 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μ : Label} {μs : List Label} {t : State}
        {ss : List State}, lts.Execution s (μ :: μs) t (s :: ss) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) ([]) (0) ([])) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_subst_cong, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_subst_cong.h7 : ¬∀ {Var : Type} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var]
        (s s' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (x y : Var),
        s[x := Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar y].FullBeta
          s'[x := Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar y] := fun hc_h => absurd (@hc_h (ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0) (0)) (by
  nofun)

-- Cslib.LTS.Execution.isChainFromTo, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.isChainFromTo.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        List.IsChainFromTo lts.UnlabelledTr ss s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([])) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.neutral_step, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.neutral_step.h4 : ¬∀ {Var : Type} {t t' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, t.Neutral → t'.Neutral := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.abs (.bvar 0) : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Cslib.LTS.Execution.length', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.length'.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        μs.length = ss.length - 1 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([0]) (0) ([])) (by
  decide +kernel)

-- Cslib.LTS.pairLang_split, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.pairLang_split.h7 : ¬∀ {Symbol State : Type} {lts : Cslib.LTS State Symbol} {s0 s2 : State} {xs1 xs2 : List Symbol},
        ∃ (s1 : State), xs1 ∈ lts.pairLang s0 s1 ∧ xs2 ∈ lts.pairLang s1 s2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) ([]) ([0])) (by
  simp)

-- Cslib.LTS.Execution.ss_ne_nil, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.ss_ne_nil.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        ss ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([])) (by
  decide +kernel)

-- Cslib.LTS.Execution.start, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.start.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        lts.Execution s μs t ss := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([])) (by
  nofun)

-- Cslib.LTS.Execution.length_ss_pos, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.length_ss_pos.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        0 < ss.length := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([])) (by
  decide +kernel)

-- Cslib.LTS.Execution.last, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.last.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        lts.Execution s μs t ss := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([])) (by
  nofun)

-- Cslib.LTS.Execution.last', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Execution.last'.h7 : ¬∀ {State Label : Type} {lts : Cslib.LTS State Label} {s : State} {μs : List Label} {t : State} {ss : List State},
        lts.Execution s μs t ss := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) ([]) (0) ([])) (by
  nofun)

-- Cslib.FinFun.fromFun_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.FinFun.fromFun_eq.h7 : ¬∀ {β α : Type} [inst : Zero β] [inst_1 : DecidableEq α] [inst_2 : (y : β) → Decidable (y = 0)] (f : α → β)
        (support : Finset α), ⇑(Cslib.FinFun.fromFun f support) = f := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Nat.instMulZeroClass.toZero) (instDecidableEqBool) (fun (y : ℕ) => instDecidableEqNat y 0) (fun b => if b then 1 else 0 : Bool → ℕ) (∅ : Finset Bool)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec_subst_intro, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec_subst_intro.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] {γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var} {X : Var} (Y : ℕ)
        (δ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty Var),
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec Y δ γ =
          (Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.openRec Y (Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.fvar X)
              γ)[X :=
            δ] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ) (0) (0) (.top : Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty ℕ)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.close_open, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.close_open.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] [inst_1 : Cslib.HasFresh Var] (x : Var)
        (t : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var) (k : ℕ),
        Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec k
            (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fvar x)
            (Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.closeRec k x t) =
          t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Cslib.instHasFreshNat) (0) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (0)) (by
  decide +kernel)

-- Cslib.LTS.MTr.single, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.MTr.single.h6 : ¬∀ {State Label : Type} (lts : Cslib.LTS State Label) {s1 : State} {μ : Label} {s2 : State}, lts.MTr s1 [μ] s2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) (0)) (by
  simp)

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm_substTm_intro, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm_substTm_intro.h6 : ¬∀ {Var : Type} [inst : DecidableEq Var] {x : Var} (y : ℕ) (t s : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var),
        Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm y s t =
          (Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm y
              (Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.fvar x) t)[x :=
            s] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ)) (by
  nofun)

-- Cslib.LTS.MTr.single_invert, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.MTr.single_invert.h6 : ¬∀ {State Label : Type} (lts : Cslib.LTS State Label) (s1 : State) (μ : Label) (s2 : State), lts.Tr s1 μ s2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b : Cslib.LTS ℕ ℕ }) (0) (0) (0)) (by
  decide +kernel)

-- Cslib.ωSequence.extract_lu_extract_lu, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.extract_lu_extract_lu.h6 : ¬∀ {α : Type} {xs : Cslib.ωSequence α} {m n i j : ℕ}, (xs.extract m n).extract i j = xs.extract (m + i) (m + j) := fun hc_h => absurd (@hc_h (ℕ) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) (0) (0) (0) (1)) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_lc_r, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_lc_r.h5 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var} [inst : Cslib.HasFresh Var] [inst : DecidableEq Var],
        N.LC := fun hc_h => absurd (@hc_h (ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (Cslib.instHasFreshNat) (instDecidableEqNat)) (by
  nofun)

-- Cslib.Automata.NA.Run.start, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.NA.Run.start.h5 : ¬∀ {State Symbol : Type} {na : Cslib.Automata.NA State Symbol} {xs : Cslib.ωSequence Symbol}
        {ss : Cslib.ωSequence State}, ss 0 ∈ na.start := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a a_1 b : ℕ) => a_1 < b, start := {n : ℕ | n = 0} : Cslib.Automata.NA ℕ ℕ }) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ }) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ })) (by
  decide +kernel)

-- List.IsChainFromTo.getLast_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChainFromTo.getLast_eq.h5 : ¬∀ {α : Type} {r : α → α → Prop} {chain : List α} {a b : α}, List.IsChainFromTo r chain a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (0)) (by
  nofun)

-- Nat.segment_upper_bound', hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.segment_upper_bound'.h1.inst : ¬0 < (fun (x : ℕ) => 0) (Nat.segment (fun (x : ℕ) => 0) 0 + 1) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.segment_upper_bound'.h1.prem0 : (fun (x : ℕ) => 0) 0 ≤ 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.segment_upper_bound'.h1 : ¬∀ {f : ℕ → ℕ} {k : ℕ}, f 0 ≤ k → k < f (Nat.segment f k + 1) := fun hc_h => HypCheckProof.Nat.segment_upper_bound'.h1.inst (@hc_h (fun (x : ℕ) => 0) (0) HypCheckProof.Nat.segment_upper_bound'.h1.prem0)

-- Relation.join_inr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.join_inr.h5 : ¬∀ {α : Type} {r₁ r₂ : α → α → Prop} {a b : α}, (r₁ ⊔ r₂) a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0)) (by
  simp)

-- Cslib.Automata.εNA.FinAcc.star_mTr_inr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Automata.εNA.FinAcc.star_mTr_inr.h5 : ¬∀ {Symbol S₁ : Type} {a : Cslib.Automata.εNA.FinAcc S₁ Symbol} {s : S₁} {μs : List (Option Symbol)},
        ∃ t ∈ a.accept,
          ∃ (μs₁ : List (Option Symbol)) (μs₂ : List (Option Symbol)),
            a.MTr s μs₁ t ∧ a.star.MTr (Sum.inl ()) μs₂ (Sum.inl ()) ∧ μs = μs₁ ++ Option.none :: μs₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({ Tr := fun (a : ℕ) (a_1 : Option ℕ) (n : ℕ) => n = 0, start := {n : ℕ | n = 0}, accept := {n : ℕ | n = 0} :
      Cslib.Automata.εNA.FinAcc ℕ ℕ }) (0) ([])) (by
  simp)

-- Cslib.LTS.Total.chooseFLTS, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Total.chooseFLTS.h3 : ¬∀ {State Label : Type} (lts : Cslib.LTS State Label) (s : State) (μ : Label), lts.Total := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({ Tr := fun (a : Bool) (a_1 : ℕ) (x : Bool) => False : Cslib.LTS Bool ℕ }) (Bool.false) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.total (Bool.false : Bool) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTm_substTm_intro, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTm_substTm_intro.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] {x : Var} (t s : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term Var),
        t.openTm s = (t.openTm (Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.fvar x))[x := s] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Fsub.Term ℕ)) (by
  nofun)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_fresh, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_fresh.h5 : ¬∀ {Var : Type} [inst : DecidableEq Var] (x : Var) (t sub : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var),
        t[x := sub] = t := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  decide +kernel)

-- Nat.segment_upper_bound, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.segment_upper_bound.h1 : ¬∀ {f : ℕ → ℕ}, f 0 = 0 → ∀ (k : ℕ), k < f (Nat.segment f k + 1) := fun hc_h => absurd (@hc_h (fun _ => 0 : ℕ → ℕ) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0)) (by
  decide +kernel)

-- Relation.RelatesInSteps.single, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.RelatesInSteps.single.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Relation.RelatesInSteps r a b 1 := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0)) (by
  nofun)

-- Cslib.ωSequence.append_get_zero_of_ne_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.ωSequence.append_get_zero_of_ne_nil.h3 : ¬∀ {α : Type} {x : List α} {s : Cslib.ωSequence α}, x ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([]) ({ get := fun (n : ℕ) => n + 1 : Cslib.ωSequence ℕ })) (by
  decide +kernel)

-- Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_lc_l, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.step_lc_l.h3 : ¬∀ {Var : Type} {M : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}
        {M' : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Var}, M.LC := fun hc_h => absurd (@hc_h (ℕ) (.bvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ) (.fvar 0 : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ)) (by
  nofun)

-- Cslib.SKI.K_irreducible, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.SKI.K_irreducible.h1 : ¬∀ (a : Cslib.SKI), a = Cslib.SKI.K := fun hc_h => absurd (@hc_h (.S : Cslib.SKI)) (by
  decide +kernel)

-- Nat.infinite_strictMono, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.infinite_strictMono.h1 : ¬∀ {ns : Set ℕ}, ∃ (f : ℕ → ℕ), StrictMono f ∧ Set.range f = ns := fun hc_h => absurd (@hc_h ({x : ℕ | False})) (by
  simp)

