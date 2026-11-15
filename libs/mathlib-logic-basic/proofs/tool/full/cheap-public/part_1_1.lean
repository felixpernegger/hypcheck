import HCImportsM

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Function.update_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.update_congr.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {β : Type} {f₁ f₂ : α → β} {a'₁ a'₂ : α},
        a'₁ = a'₂ →
          ∀ {v₁ v₂ : β}, v₁ = v₂ → ∀ {a₁ a₂ : α}, a₁ = a₂ → Function.update f₁ a'₁ v₁ a₁ = Function.update f₂ a'₂ v₂ a₂ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) _ (0) rfl _ (0) rfl _ (1) rfl) (by
  decide +kernel)

-- Function.update_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.update_congr.h8 : ¬∀ {α : Type} [inst : DecidableEq α] {β : Type} {f₁ f₂ : α → β},
        f₁ = f₂ →
          ∀ {a'₁ a'₂ : α} {v₁ v₂ : β},
            v₁ = v₂ → ∀ {a₁ a₂ : α}, a₁ = a₂ → Function.update f₁ a'₁ v₁ a₁ = Function.update f₂ a'₂ v₂ a₂ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (ℕ) _ (fun n => n + 1 : ℕ → ℕ) rfl (0) (1) _ (0) rfl _ (0) rfl) (by
  decide +kernel)

-- Function.update_congr, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.update_congr.h11 : ¬∀ {α : Type} [inst : DecidableEq α] {β : Type} {f₁ f₂ : α → β},
        f₁ = f₂ →
          ∀ {a'₁ a'₂ : α},
            a'₁ = a'₂ → ∀ {v₁ v₂ : β} {a₁ a₂ : α}, a₁ = a₂ → Function.update f₁ a'₁ v₁ a₁ = Function.update f₂ a'₂ v₂ a₂ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (ℕ) _ (fun n => n + 1 : ℕ → ℕ) rfl _ (0) rfl (0) (1) _ (0) rfl) (by
  decide +kernel)

-- Function.update_congr, hypothesis 14: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.update_congr.h14 : ¬∀ {α : Type} [inst : DecidableEq α] {β : Type} {f₁ f₂ : α → β},
        f₁ = f₂ →
          ∀ {a'₁ a'₂ : α},
            a'₁ = a'₂ → ∀ {v₁ v₂ : β}, v₁ = v₂ → ∀ {a₁ a₂ : α}, Function.update f₁ a'₁ v₁ a₁ = Function.update f₂ a'₂ v₂ a₂ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (ℕ) _ (fun n => n + 1 : ℕ → ℕ) rfl _ (0) rfl _ (0) rfl (0) (1)) (by
  decide +kernel)

-- PartialEquiv.copy_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_apply.h4 : ¬∀ {α β : Type} (e : PartialEquiv α β) (f : α → β) (g : β → α),
        ↑e.symm = g → ∀ (s : Set α), e.source = s → ∀ (t : Set β), e.target = t → ↑e = f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Inhabited.default) (fun b => if b then 1 else 0 : Bool → ℕ) _ rfl _ rfl _ rfl) (by
  decide +kernel)

-- PartialEquiv.copy_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_apply.h6 : ¬∀ {α β : Type} (e : PartialEquiv α β) (f : α → β),
        ↑e = f → ∀ (g : β → α) (s : Set α), e.source = s → ∀ (t : Set β), e.target = t → ↑e.symm = g := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Inhabited.default) _ rfl (fun b => if b then 1 else 0 : Bool → ℕ) _ rfl _ rfl) (by
  decide +kernel)

-- PartialEquiv.copy_apply, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_apply.h8 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) (f : α → β),
        @Eq (α → β) (@PartialEquiv.toFun α β e) f →
          ∀ (g : β → α),
            @Eq (β → α) (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e)) g →
              ∀ (s : Set α) (t : Set β),
                @Eq (Set β) (@PartialEquiv.target α β e) t → @Eq (Set α) (@PartialEquiv.source α β e) s) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) _ rfl _ rfl (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) _ rfl) (by
  simp)

-- PartialEquiv.copy_apply, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_apply.h10 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) (f : α → β),
        @Eq (α → β) (@PartialEquiv.toFun α β e) f →
          ∀ (g : β → α),
            @Eq (β → α) (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e)) g →
              ∀ (s : Set α),
                @Eq (Set α) (@PartialEquiv.source α β e) s → ∀ (t : Set β), @Eq (Set β) (@PartialEquiv.target α β e) t) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) _ rfl _ rfl _ rfl (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)) (by
  simp)

-- PartialEquiv.copy_target, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_target.h4 : ¬∀ {α β : Type} (e : PartialEquiv α β) (f : α → β) (g : β → α),
        ↑e.symm = g → ∀ (s : Set α), e.source = s → ∀ (t : Set β), e.target = t → ↑e = f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Inhabited.default) (fun b => if b then 1 else 0 : Bool → ℕ) _ rfl _ rfl _ rfl) (by
  decide +kernel)

-- PartialEquiv.copy_target, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_target.h6 : ¬∀ {α β : Type} (e : PartialEquiv α β) (f : α → β),
        ↑e = f → ∀ (g : β → α) (s : Set α), e.source = s → ∀ (t : Set β), e.target = t → ↑e.symm = g := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Inhabited.default) _ rfl (fun b => if b then 1 else 0 : Bool → ℕ) _ rfl _ rfl) (by
  decide +kernel)

-- PartialEquiv.copy_target, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_target.h8 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) (f : α → β),
        @Eq (α → β) (@PartialEquiv.toFun α β e) f →
          ∀ (g : β → α),
            @Eq (β → α) (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e)) g →
              ∀ (s : Set α) (t : Set β),
                @Eq (Set β) (@PartialEquiv.target α β e) t → @Eq (Set α) (@PartialEquiv.source α β e) s) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) _ rfl _ rfl (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) _ rfl) (by
  simp)

-- PartialEquiv.copy_target, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_target.h10 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) (f : α → β),
        @Eq (α → β) (@PartialEquiv.toFun α β e) f →
          ∀ (g : β → α),
            @Eq (β → α) (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e)) g →
              ∀ (s : Set α),
                @Eq (Set α) (@PartialEquiv.source α β e) s → ∀ (t : Set β), @Eq (Set β) (@PartialEquiv.target α β e) t) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) _ rfl _ rfl _ rfl (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)) (by
  simp)

-- PartialEquiv.copy_symm_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_symm_apply.h4 : ¬∀ {α β : Type} (e : PartialEquiv α β) (f : α → β) (g : β → α),
        ↑e.symm = g → ∀ (s : Set α), e.source = s → ∀ (t : Set β), e.target = t → ↑e = f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Inhabited.default) (fun b => if b then 1 else 0 : Bool → ℕ) _ rfl _ rfl _ rfl) (by
  decide +kernel)

-- PartialEquiv.copy_symm_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_symm_apply.h6 : ¬∀ {α β : Type} (e : PartialEquiv α β) (f : α → β),
        ↑e = f → ∀ (g : β → α) (s : Set α), e.source = s → ∀ (t : Set β), e.target = t → ↑e.symm = g := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Inhabited.default) _ rfl (fun b => if b then 1 else 0 : Bool → ℕ) _ rfl _ rfl) (by
  decide +kernel)

-- PartialEquiv.copy_symm_apply, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_symm_apply.h8 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) (f : α → β),
        @Eq (α → β) (@PartialEquiv.toFun α β e) f →
          ∀ (g : β → α),
            @Eq (β → α) (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e)) g →
              ∀ (s : Set α) (t : Set β),
                @Eq (Set β) (@PartialEquiv.target α β e) t → @Eq (Set α) (@PartialEquiv.source α β e) s) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) _ rfl _ rfl (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) _ rfl) (by
  simp)

-- PartialEquiv.copy_symm_apply, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_symm_apply.h10 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) (f : α → β),
        @Eq (α → β) (@PartialEquiv.toFun α β e) f →
          ∀ (g : β → α),
            @Eq (β → α) (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e)) g →
              ∀ (s : Set α),
                @Eq (Set α) (@PartialEquiv.source α β e) s → ∀ (t : Set β), @Eq (Set β) (@PartialEquiv.target α β e) t) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) _ rfl _ rfl _ rfl (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)) (by
  simp)

-- if_congr, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.if_congr.h9 : ¬∀ {α : Type} {P Q : Prop} [inst : Decidable P] [inst_1 : Decidable Q] {x y u v : α},
        x = u → y = v → (if P then x else y) = if Q then u else v := fun hc_h => absurd (@hc_h (ℕ) (True) (False) (instDecidableTrue) (instDecidableFalse) _ _ (0) (1) rfl rfl) (by
  decide +kernel)

-- if_congr, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.if_congr.h10 : ¬∀ {α : Type} {P Q : Prop} [inst : Decidable P] [inst_1 : Decidable Q] {x y u v : α},
        (P ↔ Q) → y = v → (if P then x else y) = if Q then u else v := fun hc_h => absurd (@hc_h (ℕ) (True) (True) (instDecidableTrue) (instDecidableTrue) (0) _ (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) rfl) (by
  decide +kernel)

-- if_congr, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.if_congr.h11 : ¬∀ {α : Type} {P Q : Prop} [inst : Decidable P] [inst_1 : Decidable Q] {x y u v : α},
        (P ↔ Q) → x = u → (if P then x else y) = if Q then u else v := fun hc_h => absurd (@hc_h (ℕ) (False) (False) (instDecidableFalse) (instDecidableFalse) _ (0) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) rfl) (by
  decide +kernel)

-- ENNReal.biSup_add_biSup_le, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.biSup_add_biSup_le.h9 : ¬∀ {ι κ : Type} {s : Set ι} {t : Set κ},
        s.Nonempty → t.Nonempty → ∀ {f : ι → ENNReal} {g : κ → ENNReal} {a : ENNReal}, (⨆ i ∈ s, f i) + ⨆ j ∈ t, g j ≤ a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp) (by
  simp) (fun (a : ℕ) => 1) (fun (a : ℕ) => 1) (0)) (by
  (simp <;> omega))

-- Set.Pairwise.eq, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.Pairwise.eq.h5.inst : ¬2 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.Pairwise.eq.h5.prem0 : 2 ∈ {n : ℕ | n % 2 = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.Pairwise.eq.h5.prem1 : 0 ∈ {n : ℕ | n % 2 = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.Pairwise.eq.h5.prem2 : ¬(fun (a b : ℕ) => a < b) 2 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.Pairwise.eq.h5 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α} {a b : α}, a ∈ s → b ∈ s → ¬r a b → a = b := fun hc_h => HypCheckProof.Set.Pairwise.eq.h5.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) ({n : ℕ | n % 2 = 0}) (2) (0) HypCheckProof.Set.Pairwise.eq.h5.prem0 HypCheckProof.Set.Pairwise.eq.h5.prem1 HypCheckProof.Set.Pairwise.eq.h5.prem2)

-- Set.Pairwise.eq, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.Pairwise.eq.h6.inst : ¬1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.Pairwise.eq.h6.prem0 : {n : ℕ | n = 0}.Pairwise fun (a b : ℕ) => a < b := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.Pairwise.eq.h6.prem1 : 0 ∈ {n : ℕ | n = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.Pairwise.eq.h6.prem2 : ¬(fun (a b : ℕ) => a < b) 1 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.Pairwise.eq.h6 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α} {a b : α}, s.Pairwise r → b ∈ s → ¬r a b → a = b := fun hc_h => HypCheckProof.Set.Pairwise.eq.h6.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) ({n : ℕ | n = 0}) (1) (0) HypCheckProof.Set.Pairwise.eq.h6.prem0 HypCheckProof.Set.Pairwise.eq.h6.prem1 HypCheckProof.Set.Pairwise.eq.h6.prem2)

-- Set.Pairwise.eq, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.Pairwise.eq.h7.inst : ¬0 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.Pairwise.eq.h7.prem0 : {n : ℕ | n = 0}.Pairwise fun (a b : ℕ) => a = b := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.Pairwise.eq.h7.prem1 : 0 ∈ {n : ℕ | n = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.Pairwise.eq.h7.prem2 : ¬(fun (a b : ℕ) => a = b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.Pairwise.eq.h7 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α} {a b : α}, s.Pairwise r → a ∈ s → ¬r a b → a = b := fun hc_h => HypCheckProof.Set.Pairwise.eq.h7.inst (@hc_h (ℕ) (fun (a b : ℕ) => a = b) ({n : ℕ | n = 0}) (0) (1) HypCheckProof.Set.Pairwise.eq.h7.prem0 HypCheckProof.Set.Pairwise.eq.h7.prem1 HypCheckProof.Set.Pairwise.eq.h7.prem2)

-- ENNReal.biSup_add_biSup_le', hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.biSup_add_biSup_le'.h9 : ¬∀ {ι κ : Type} {f : ι → ENNReal} {a : ENNReal} {p : ι → Prop} {q : κ → Prop},
        (∃ (i : ι), p i) →
          (∃ (j : κ), q j) → ∀ {g : κ → ENNReal}, (⨆ (i : ι), ⨆ (_ : p i), f i) + ⨆ (j : κ), ⨆ (_ : q j), g j ≤ a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => 0) (0) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (by
  simp) (by
  simp) (fun (a : ℕ) => 1)) (by
  simp)

-- Archimedean.ratLt_nonempty, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Archimedean.ratLt_nonempty.h6 : ¬∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] [inst_3 : One M]
        [inst_4 : ZeroLEOneClass M] [inst_5 : Archimedean M] (x : M), (Archimedean.ratLt x).Nonempty := fun hc_h => absurd (@hc_h (Unit) (PUnit.addCommGroup) (PUnit.instLinearOrder) (@IsOrderedAddMonoid.mk (Unit) (@AddCommGroup.toAddCommMonoid Unit PUnit.addCommGroup) (@PartialOrder.toPreorder Unit
      (@SemilatticeInf.toPartialOrder Unit
        (@Lattice.toSemilatticeInf Unit
          (@DistribLattice.toLattice Unit (@instDistribLatticeOfLinearOrder Unit PUnit.instLinearOrder))))) (by (try dsimp only);   decide) (by (try dsimp only);   decide)) (PUnit.instOne_mathlib) _ (@Archimedean.mk (Unit) (@AddCommGroup.toAddCommMonoid Unit PUnit.addCommGroup) (@SemilatticeInf.toPartialOrder Unit
      (@Lattice.toSemilatticeInf Unit
        (@DistribLattice.toLattice Unit (@instDistribLatticeOfLinearOrder Unit PUnit.instLinearOrder)))) (by (try dsimp only);   (intros; simp_all; done))) (PUnit.unit)) (by
  nofun)

-- Function.Injective.dite, hypothesis 7: necessary
/- FAILED: 8:3: `simp` made no progress | 14:3: `simp` made no progress | 8:3: `simp` made no progress | 14:3: `simp` made no progress | 23:411: don't know how to synthesize implicit argument `hx'`
  @h7.prem1 (?m.42 hc_h) (?m.43 hc_h) (?m.44 hc_h) (?m.45 hc_h)
context:
hc_h :
  ∀ {α β : Type} (p : α → Prop) [inst : DecidablePred p] {f : { a // p a } → β} {f' : { a // ¬p a } → β},
    Function.Injective f →
      (∀ {x x' : α} {hx : p x} {hx' : ¬p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) →
        Function.Injective fun x => if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩
x✝ x'✝ : Bool
hx✝ : False
hx'✝ : ¬False
⊢ ¬(fun x => False) (?m.43 hc_h) | 39:110: don't know how to synthesize implicit argument `hx'`
  @h7.prem1 (?m.10 hc_h) (?m.11 hc_h) (?m.12 hc_h) (?m.13 hc_h)
context:
hc_h :
  ∀ {α β : Type} (p : α → Prop) [inst : DecidablePred p] {f : { a // p a } → β} {f' : { a // ¬p a } → β},
    Function.Injective f →
      (∀ {x x' : α} {hx : p x} {hx' : ¬p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) →
        Function.Injective fun x => if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩
x✝ x'✝ : Bool
hx✝ : False
hx'✝ : ¬False
⊢ ¬(fun x => False) (?m.11 hc_h) | 23:411: don't know how to synthesize implicit argument `hx'`
  @h7.prem1 (?m.42 hc_h) (?m.43 hc_h) (?m.44 hc_h) (?m.45 hc_h)
context:
hc_h :
  ∀ {α β : Type} (p : α → Prop) [inst : DecidablePred p] {f : { a // p a } → β} {f' : { a // ¬p a } → β},
    Function.Injective f →
      (∀ {x x' : α} {hx : p x} {hx' : ¬p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) →
        Function.Injective fun x => if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩
x✝ x'✝ : Bool
hx✝ : False
hx'✝ : ¬False
⊢ ¬(fun x => False) (?m.43 hc_h) | 39:110: don't know how to synthesize implicit argument `hx'`
  @h7.prem1 (?m.10 hc_h) (?m.11 hc_h) (?m.12 hc_h) (?m.13 hc_h)
context:
hc_h :
  ∀ {α β : Type} (p : α → Prop) [inst : DecidablePred p] {f : { a // p a } → β} {f' : { a // ¬p a } → β},
    Function.Injective f →
      (∀ {x x' : α} {hx : p x} {hx' : ¬p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) →
        Function.Injective fun x => if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩
x✝ x'✝ : Bool
hx✝ : False
hx'✝ : ¬False
⊢ ¬(fun x => False) (?m.11 hc_h)
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.dite.h7 : ¬∀ {α β : Type} (p : α → Prop) [inst : DecidablePred p] {f : { a : α // p a } → β} {f' : { a : α // ¬p a } → β},
        Function.Injective f →
          (∀ {x x' : α} {hx : p x} {hx' : ¬p x'}, f (⟨x, hx⟩ : { a : α // p a }) ≠ f' (⟨x', hx'⟩ : { a : α // ¬p a })) →
            Function.Injective fun (x : α) =>
              if h : p x then f (⟨x, h⟩ : { a : α // p a }) else f' (⟨x, h⟩ : { a : α // ¬p a }) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => False : Bool → Prop) (fun (a : Bool) => instDecidableFalse) (fun (a : { a : Bool // (fun (x : Bool) => False) a }) => 0) (fun (a : { a : Bool // ¬(fun (x : Bool) => False) a }) => 0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)
-/

-- Function.Injective.dite, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.dite.h8 : ¬∀ {α β : Type} (p : α → Prop) [inst : DecidablePred p] {f : { a : α // p a } → β} {f' : { a : α // ¬p a } → β},
        Function.Injective f →
          Function.Injective f' →
            Function.Injective fun (x : α) =>
              if h : p x then f (⟨x, h⟩ : { a : α // p a }) else f' (⟨x, h⟩ : { a : α // ¬p a }) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => b = true : Bool → Prop) (fun (a : Bool) => instDecidableEqBool a Bool.true) (fun (a : { a : Bool // (fun (b : Bool) => b = Bool.true) a }) => 0) (fun (a : { a : Bool // ¬(fun (b : Bool) => b = Bool.true) a }) => 0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Function.IsConstOn.eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.IsConstOn.eq.h4 : ¬∀ {β α : Type} {f : α → β} {s : Set α} {x y : α}, x ∈ s → y ∈ s → f x = f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n % 2 = 0}) (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Function.IsConstOn.eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.IsConstOn.eq.h7 : ¬∀ {β α : Type} {f : α → β} {s : Set α}, Function.IsConstOn f s → ∀ {x y : α}, y ∈ s → f x = f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (by
  simp) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Function.IsConstOn.eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.IsConstOn.eq.h8 : ¬∀ {β α : Type} {f : α → β} {s : Set α}, Function.IsConstOn f s → ∀ {x y : α}, x ∈ s → f x = f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (by
  simp) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Function.not_isConstOn_of_apply_ne, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Function.not_isConstOn_of_apply_ne.h6.inst : ¬¬Function.IsConstOn (fun (n : ℕ) => n + 1) {n : ℕ | n = 0} := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Function.not_isConstOn_of_apply_ne.h6.prem0 : 0 ∈ {n : ℕ | n = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Function.not_isConstOn_of_apply_ne.h6.prem1 : (fun (n : ℕ) => n + 1) 1 ≠ (fun (n : ℕ) => n + 1) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Function.not_isConstOn_of_apply_ne.h6 : ¬∀ {β α : Type} {f : α → β} {s : Set α} {x y : α}, y ∈ s → f x ≠ f y → ¬Function.IsConstOn f s := fun hc_h => HypCheckProof.Function.not_isConstOn_of_apply_ne.h6.inst (@hc_h (ℕ) (ℕ) (fun (n : ℕ) => n + 1) ({n : ℕ | n = 0}) (1) (0) HypCheckProof.Function.not_isConstOn_of_apply_ne.h6.prem0 HypCheckProof.Function.not_isConstOn_of_apply_ne.h6.prem1)

-- Function.not_isConstOn_of_apply_ne, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Function.not_isConstOn_of_apply_ne.h7.inst : ¬¬Function.IsConstOn (fun (n : ℕ) => n + 1) {n : ℕ | n = 0} := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Function.not_isConstOn_of_apply_ne.h7.prem0 : 0 ∈ {n : ℕ | n = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Function.not_isConstOn_of_apply_ne.h7.prem1 : (fun (n : ℕ) => n + 1) 0 ≠ (fun (n : ℕ) => n + 1) 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Function.not_isConstOn_of_apply_ne.h7 : ¬∀ {β α : Type} {f : α → β} {s : Set α} {x y : α}, x ∈ s → f x ≠ f y → ¬Function.IsConstOn f s := fun hc_h => HypCheckProof.Function.not_isConstOn_of_apply_ne.h7.inst (@hc_h (ℕ) (ℕ) (fun (n : ℕ) => n + 1) ({n : ℕ | n = 0}) (0) (1) HypCheckProof.Function.not_isConstOn_of_apply_ne.h7.prem0 HypCheckProof.Function.not_isConstOn_of_apply_ne.h7.prem1)

-- Function.not_isConstOn_of_apply_ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.not_isConstOn_of_apply_ne.h8 : ¬∀ {β α : Type} {f : α → β} {s : Set α} {x y : α}, x ∈ s → y ∈ s → ¬Function.IsConstOn f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (0) (0) (by
  decide) (by
  decide)) (by
  simp)

-- Or.elim3, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Or.elim3.h4 : ¬∀ {a b c d : Prop}, (a → d) → (b → d) → (c → d) → d := fun hc_h => absurd (@hc_h (False) (False) (False) (False) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Or.elim3, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Or.elim3.h5 : ¬∀ {a b c d : Prop}, a ∨ b ∨ c → (b → d) → (c → d) → d := fun hc_h => absurd (@hc_h (True) (False) (False) (False) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Or.elim3, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Or.elim3.h6 : ¬∀ {a b c d : Prop}, a ∨ b ∨ c → (a → d) → (c → d) → d := fun hc_h => absurd (@hc_h (False) (True) (False) (False) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Or.elim3, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Or.elim3.h7 : ¬∀ {a b c d : Prop}, a ∨ b ∨ c → (a → d) → (b → d) → d := fun hc_h => absurd (@hc_h (False) (False) (True) (False) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- NNReal.le_iInf_add_iInf, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.le_iInf_add_iInf.h7 : ¬∀ {ι ι' : Type} [inst : Nonempty ι] [inst : Nonempty ι'] {f : ι → NNReal} {g : ι' → NNReal} {a : NNReal},
        a ≤ (⨅ (i : ι), f i) + ⨅ (j : ι'), g j := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ _ (fun (a : ℕ) => 0) (fun (a : ℕ) => 0) (1)) (by
  simp)

-- Equiv.subtypeEquiv_trans, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypeEquiv_trans.h8 : ¬∀ {α β γ : Type} {p : α → Prop} {q : β → Prop} {r : γ → Prop} (e : α ≃ β) (f : β ≃ γ),
        (∀ (b : β), q b ↔ r (f b)) → ∀ (a : α), p a ↔ q (e a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun _ => False : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (1) (1) (by
  simp)) (by
  simp)

-- Equiv.subtypeEquiv_trans, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypeEquiv_trans.h9 : ¬∀ {α β γ : Type} {p : α → Prop} {q : β → Prop} {r : γ → Prop} (e : α ≃ β) (f : β ≃ γ),
        (∀ (a : α), p a ↔ q (e a)) → ∀ (b : β), q b ↔ r (f b) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (1) (1) (by
  simp)) (by
  simp)

-- SetRel.prodMk_mem_comp, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.prodMk_mem_comp.h8 : ¬∀ {α β γ : Type} {R : SetRel α β} {S : SetRel β γ} {a : α} {b : β} {c : γ}, (b, c) ∈ S → (a, c) ∈ R.comp S := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (∅) (⊤) (0) (0) (0) (by
  simp)) (by
  simp)

-- SetRel.prodMk_mem_comp, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.prodMk_mem_comp.h9 : ¬∀ {α β γ : Type} {R : SetRel α β} {S : SetRel β γ} {a : α} {b : β} {c : γ}, (a, b) ∈ R → (a, c) ∈ R.comp S := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (⊤) (∅) (0) (0) (0) (by
  simp)) (by
  simp)

-- Function.Embedding.setValue_eq_of_ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.setValue_eq_of_ne.h8 : ¬∀ {α β : Type} {f : α ↪ β} {a : α} {b : β} {c : α} [inst : (a' : α) → Decidable (a' = a)]
        [inst_1 : (a' : α) → Decidable (f a' = b)], f c ≠ b → (f.setValue a b) c = f c := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) (Bool.false) (1) (Bool.false) (fun (a' : Bool) => instDecidableEqBool a' Bool.false) (fun (a' : Bool) =>
      instDecidableEqNat
        ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
            Bool ↪ ℕ }
          a')
        1) (by
  decide)) (by
  decide +kernel)

-- Function.Embedding.setValue_eq_of_ne, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.setValue_eq_of_ne.h9 : ¬∀ {α β : Type} {f : α ↪ β} {a : α} {b : β} {c : α} [inst : (a' : α) → Decidable (a' = a)]
        [inst_1 : (a' : α) → Decidable (f a' = b)], c ≠ a → (f.setValue a b) c = f c := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) (Bool.true) (0) (Bool.false) (fun (a' : Bool) => instDecidableEqBool a' Bool.true) (fun (a' : Bool) =>
      instDecidableEqNat
        ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
            Bool ↪ ℕ }
          a')
        0) (by
  decide)) (by
  decide +kernel)

-- Relation.TransGen.closed', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.TransGen.closed'.h3 : ¬∀ {α : Type} {r : α → α → Prop} {P : α → Prop} {a b : α}, Relation.TransGen r a b → P b → P a := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (fun b => b = true : Bool → Prop) (Bool.false) (Bool.true) (by
  grind) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Relation.TransGen.closed', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.TransGen.closed'.h6 : ¬∀ {α : Type} {r : α → α → Prop} {P : α → Prop}, (∀ {a b : α}, r a b → P b → P a) → ∀ {a b : α}, P b → P a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (by
  omega) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Relation.TransGen.closed', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.TransGen.closed'.h7 : ¬∀ {α : Type} {r : α → α → Prop} {P : α → Prop},
        (∀ {a b : α}, r a b → P b → P a) → ∀ {a b : α}, Relation.TransGen r a b → P a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (by
  omega) (1) (2) (by
  grind)) (by
  decide +kernel)

-- mul_smul_one_lt_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.mul_smul_one_lt_iff.h3 : Not
      (∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : One M] {num : Int} {n den : Nat},
        @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
          ∀ {x : M},
            Iff
              (@LT.lt M
                (@Preorder.toLT M
                  (@PartialOrder.toPreorder M
                    (@SemilatticeInf.toPartialOrder M
                      (@Lattice.toSemilatticeInf M
                        (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))
                (@HSMul.hSMul Int M M
                  (@instHSMul Int M
                    (@ZSMul.toSMul M
                      (@SubNegMonoid.toZSMul M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst)))))
                  (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) num (@Nat.cast Int instNatCastInt n))
                  (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_2)))
                (@HSMul.hSMul Int M M
                  (@instHSMul Int M
                    (@ZSMul.toSMul M
                      (@SubNegMonoid.toZSMul M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst)))))
                  (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@Nat.cast Int instNatCastInt n)
                    (@Nat.cast Int instNatCastInt den))
                  x))
              (@LT.lt M
                (@Preorder.toLT M
                  (@PartialOrder.toPreorder M
                    (@SemilatticeInf.toPartialOrder M
                      (@Lattice.toSemilatticeInf M
                        (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))
                (@HSMul.hSMul Int M M
                  (@instHSMul Int M
                    (@ZSMul.toSMul M
                      (@SubNegMonoid.toZSMul M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst)))))
                  num (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_2)))
                (@HSMul.hSMul Nat M M
                  (@instHSMul Nat M
                    (@NSMul.toSMul M
                      (@AddMonoid.toNSMul M
                        (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst))))))
                  den x))) := fun hc_h => absurd (@hc_h (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@Fin.addCommGroup (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Fin.instLinearOrder (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@MulOne.toOne (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@MulOneClass.toMulOne (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Monoid.toMulOneClass (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@CommMonoid.toMonoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Fin.instCommMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- mul_smul_one_lt_iff, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.mul_smul_one_lt_iff.h8 : Not
      (∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M]
        [inst_2 :
          @IsOrderedAddMonoid M (@AddCommGroup.toAddCommMonoid M inst)
            (@PartialOrder.toPreorder M
              (@SemilatticeInf.toPartialOrder M
                (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1)))))]
        [inst_3 : One M] {num : Int} {n den : Nat} {x : M},
        Iff
          (@LT.lt M
            (@Preorder.toLT M
              (@PartialOrder.toPreorder M
                (@SemilatticeInf.toPartialOrder M
                  (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))
            (@HSMul.hSMul Int M M
              (@instHSMul Int M
                (@ZSMul.toSMul M (@SubNegMonoid.toZSMul M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst)))))
              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) num (@Nat.cast Int instNatCastInt n))
              (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_3)))
            (@HSMul.hSMul Int M M
              (@instHSMul Int M
                (@ZSMul.toSMul M (@SubNegMonoid.toZSMul M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst)))))
              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@Nat.cast Int instNatCastInt n)
                (@Nat.cast Int instNatCastInt den))
              x))
          (@LT.lt M
            (@Preorder.toLT M
              (@PartialOrder.toPreorder M
                (@SemilatticeInf.toPartialOrder M
                  (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))
            (@HSMul.hSMul Int M M
              (@instHSMul Int M
                (@ZSMul.toSMul M (@SubNegMonoid.toZSMul M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst)))))
              num (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_3)))
            (@HSMul.hSMul Nat M M
              (@instHSMul Nat M
                (@NSMul.toSMul M
                  (@AddMonoid.toNSMul M
                    (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst))))))
              den x))) := fun hc_h => absurd (@hc_h (Int) (Int.instAddCommGroup) (Int.instLinearOrder) _ (@AddMonoidWithOne.toOne Int (@AddGroupWithOne.toAddMonoidWithOne Int (@Ring.toAddGroupWithOne Int Int.instRing))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide +kernel)

-- Function.RightInverse.comp, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.RightInverse.comp.h8 : ¬∀ {α β γ : Type} {f : α → β} {g : β → α} {h : β → γ} {i : γ → β},
        Function.RightInverse f g → Function.RightInverse (h ∘ f) (g ∘ i) := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (not : Bool → Bool) (not : Bool → Bool) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (by
  decide)) (by
  decide +kernel)

-- Equiv.extendSubtype_apply_of_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.extendSubtype_apply_of_mem.h8 : ¬∀ {α : Type} {p q : α → Prop} [inst : DecidablePred p] [inst : DecidablePred q] [inst : Finite ↑{x : α | p x}]
        (e : { x : α // p x } ≃ { x : α // q x }) (x : α), p x := fun hc_h => absurd (@hc_h (Bool) (fun b => b = true : Bool → Prop) (fun b => b = true : Bool → Prop) (fun (a : Bool) => instDecidableEqBool a Bool.true) (fun (a : Bool) => instDecidableEqBool a Bool.true) _ ({
      toFun := fun (a : { x : Bool // (fun (b : Bool) => b = Bool.true) x }) =>
        (⟨Bool.true, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Bool // (fun (b : Bool) => b = Bool.true) x }),
      invFun := fun (a : { x : Bool // (fun (b : Bool) => b = Bool.true) x }) =>
        (⟨Bool.true, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Bool // (fun (b : Bool) => b = Bool.true) x }),
      left_inv := of_decide_eq_true (id (Eq.refl Bool.true)), right_inv := of_decide_eq_true (id (Eq.refl Bool.true)) :
      { x : Bool // (fun (b : Bool) => b = Bool.true) x } ≃ { x : Bool // (fun (b : Bool) => b = Bool.true) x } }) (Bool.false)) (by
  decide +kernel)

-- ENNReal.add_lt_add_of_le_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_lt_add_of_le_of_lt.h6 : ¬∀ {a b c d : ENNReal}, a ≠ ⊤ → a ≤ b → a + c < b + d := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (by
  decide) (by
  rfl)) (by
  simp)

-- ENNReal.HolderTriple.unique_of_ne_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.unique_of_ne_zero.h5 : ¬∀ (p q : ENNReal) {r : ENNReal} [inst : p.HolderTriple q r] (q' : ENNReal) [inst : p.HolderTriple q' r], q = q' := fun hc_h => absurd (@hc_h (0) (0) (0) _ (1) _) (by
  simp)

-- PartialEquiv.IsImage.symm_apply_mem_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.IsImage.symm_apply_mem_iff.h5 : Not
      (∀ {α β : Type} {e : PartialEquiv α β} {s : Set α} {t : Set β} ⦃y : β⦄,
        @Membership.mem β (Set β) (@Set.instMembership β) (@PartialEquiv.target α β e) y →
          Iff (@Membership.mem α (Set α) (@Set.instMembership α) s (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e) y))
            (@Membership.mem β (Set β) (@Set.instMembership β) t y)) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (Bool.true) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- finAddFlip_apply_mk_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finAddFlip_apply_mk_left.h3 : ¬∀ {m : ℕ} {n : ℕ} {k : ℕ}, k < m := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- finAddFlip_apply_mk_left, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.finAddFlip_apply_mk_left.h4.der : ∀ {m n k : ℕ} (h : k < m), optParam (n + k < n + m) (Nat.add_lt_add_left h n) → k < m + n := by
  (intros; lia)
theorem HypCheckProof.finAddFlip_apply_mk_left.h4 : ∀ {m n k : ℕ} (h : k < m) (hnk : optParam (n + k < n + m) (Nat.add_lt_add_left h n)),
      finAddFlip (⟨k, HypCheckProof.finAddFlip_apply_mk_left.h4.der h hnk⟩ : Fin (m + n)) = (⟨n + k, hnk⟩ : Fin (n + m)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @finAddFlip_apply_mk_left hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.finAddFlip_apply_mk_left.h4.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4) hc_x4

-- finAddFlip_apply_mk_left, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.finAddFlip_apply_mk_left.h5.der : ∀ {m n k : ℕ} (h : k < m), optParam (k < m + n) (Nat.lt_add_right n h) → n + k < n + m := by
  (intros; lia)
theorem HypCheckProof.finAddFlip_apply_mk_left.h5 : ∀ {m n k : ℕ} (h : k < m) (hk : optParam (k < m + n) (Nat.lt_add_right n h)),
      finAddFlip (⟨k, hk⟩ : Fin (m + n)) = (⟨n + k, HypCheckProof.finAddFlip_apply_mk_left.h5.der h hk⟩ : Fin (n + m)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @finAddFlip_apply_mk_left hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.finAddFlip_apply_mk_left.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- Function.bijective_of_subsingleton', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.bijective_of_subsingleton'.h3 : ¬∀ {α β : Type} [inst : Nonempty α] [inst : Subsingleton β] (f : α → β), Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (Unit) _ _ (fun (a : Bool) => PUnit.unit)) (by
  decide +kernel)

-- Function.bijective_of_subsingleton', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.bijective_of_subsingleton'.h4 : ¬∀ {α β : Type} [inst : Nonempty α] [inst : Subsingleton α] (f : α → β), Function.Bijective f := fun hc_h => absurd (@hc_h (Unit) (Bool) _ _ (fun (a : Unit) => Bool.false)) (by
  decide +kernel)

-- Function.LeftInverse.eq_rightInverse, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.eq_rightInverse.h5 : ¬∀ {α β : Type} {f : α → β} {g₁ g₂ : β → α}, Function.RightInverse g₂ f → g₁ = g₂ := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool) (fun _ => true : Bool → Bool) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Function.LeftInverse.eq_rightInverse, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.eq_rightInverse.h6 : ¬∀ {α β : Type} {f : α → β} {g₁ g₂ : β → α}, Function.LeftInverse g₁ f → g₁ = g₂ := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool) (not : Bool → Bool) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- ENNReal.toReal_le_add', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_le_add'.h3 : ¬∀ {a b c : ENNReal}, (b = ⊤ → a = ⊤) → (c = ⊤ → a = ⊤) → a.toReal ≤ b.toReal + c.toReal := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide) (by
  decide)) (by
  simp)

-- ENNReal.sub_lt_of_sub_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_lt_of_sub_lt.h3 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ ∨ b ≠ ⊤ → a - b < c → a - c < b := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide) (by
  simp)) (by
  simp)

-- ENNReal.sub_lt_of_sub_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_lt_of_sub_lt.h5 : ¬∀ {a b c : ENNReal}, c ≤ a → a ≠ ⊤ ∨ b ≠ ⊤ → a - c < b := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  rfl) (by
  decide)) (by
  simp)

-- ENNReal.div_lt_div_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_lt_div_right.h5 : ¬∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → a / c < b / c := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  simp) (by
  decide)) (by
  simp)

-- ENNReal.div_lt_div_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_lt_div_left.h3 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → c < b → a / b < a / c := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide) (by
  simp)) (by
  simp)

-- ENNReal.div_lt_div_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_lt_div_left.h5 : ¬∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / b < a / c := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  simp) (by
  decide)) (by
  simp)

-- ENNReal.exists_mem_Ioc_zpow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_mem_Ioc_zpow.h2 : ¬∀ {x y : ENNReal}, x ≠ ⊤ → 1 < y → y ≠ ⊤ → ∃ (n : ℤ), x ∈ Set.Ioc (y ^ n) (y ^ (n + 1)) := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (by
  simp) (by
  decide)) (by
  simp)

-- sign_intCast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.sign_intCast.h4 : Not
      (∀ {α : Type} [inst : Ring α] [inst_1 : PartialOrder α] [inst_2 : @IsOrderedRing α (@Ring.toSemiring α inst) inst_1]
        [inst_3 : @DecidableLT α (@Preorder.toLT α (@PartialOrder.toPreorder α inst_1))] (n : Int),
        @Eq SignType
          (@DFunLike.coe
            (@OrderHom α SignType (@PartialOrder.toPreorder α inst_1)
              (@PartialOrder.toPreorder SignType
                (@SemilatticeInf.toPartialOrder SignType
                  (@Lattice.toSemilatticeInf SignType
                    (@DistribLattice.toLattice SignType
                      (@instDistribLatticeOfLinearOrder SignType SignType.instLinearOrder))))))
            α (fun (x : α) => SignType)
            (@OrderHom.instFunLike α SignType (@PartialOrder.toPreorder α inst_1)
              (@PartialOrder.toPreorder SignType
                (@SemilatticeInf.toPartialOrder SignType
                  (@Lattice.toSemilatticeInf SignType
                    (@DistribLattice.toLattice SignType
                      (@instDistribLatticeOfLinearOrder SignType SignType.instLinearOrder))))))
            (@SignType.sign α (@MulZeroClass.toZero α (@instMulZeroClassOfSemiring α (@Ring.toSemiring α inst)))
              (@PartialOrder.toPreorder α inst_1) inst_3)
            (@Int.cast α (@AddGroupWithOne.toIntCast α (@Ring.toAddGroupWithOne α inst)) n))
          (@DFunLike.coe
            (@OrderHom Int SignType Int.instPreorder
              (@PartialOrder.toPreorder SignType
                (@SemilatticeInf.toPartialOrder SignType
                  (@Lattice.toSemilatticeInf SignType
                    (@DistribLattice.toLattice SignType
                      (@instDistribLatticeOfLinearOrder SignType SignType.instLinearOrder))))))
            Int (fun (x : Int) => SignType)
            (@OrderHom.instFunLike Int SignType Int.instPreorder
              (@PartialOrder.toPreorder SignType
                (@SemilatticeInf.toPartialOrder SignType
                  (@Lattice.toSemilatticeInf SignType
                    (@DistribLattice.toLattice SignType
                      (@instDistribLatticeOfLinearOrder SignType SignType.instLinearOrder))))))
            (@SignType.sign Int (@MulZeroClass.toZero Int (@instMulZeroClassOfSemiring Int Int.instSemiring))
              Int.instPreorder Int.decLt)
            n)) := fun hc_h => absurd (@hc_h (Unit) (@CommRing.toRing Unit PUnit.commRing) (@ChainCompletePartialOrder.toPartialOrder Unit
      (@ChainCompletePartialOrder.instOfCompleteLattice Unit
        (@CompleteBooleanAlgebra.toCompleteLattice Unit PUnit.instCompleteBooleanAlgebra))) (@IsOrderedRing.mk (Unit) (@Ring.toSemiring Unit (@CommRing.toRing Unit PUnit.commRing)) (@ChainCompletePartialOrder.toPartialOrder Unit
      (@ChainCompletePartialOrder.instOfCompleteLattice Unit
        (@CompleteBooleanAlgebra.toCompleteLattice Unit PUnit.instCompleteBooleanAlgebra))) (@IsOrderedAddMonoid.mk (Unit) (@Semiring.toAddCommMonoid Unit (@Ring.toSemiring Unit (@CommRing.toRing Unit PUnit.commRing))) (@PartialOrder.toPreorder Unit
      (@ChainCompletePartialOrder.toPartialOrder Unit
        (@ChainCompletePartialOrder.instOfCompleteLattice Unit
          (@CompleteBooleanAlgebra.toCompleteLattice Unit PUnit.instCompleteBooleanAlgebra)))) (by (try dsimp only);   decide) (by (try dsimp only);   decide)) inferInstance (@PosMulMono.mk (Unit) (@Distrib.toMul Unit (@instDistribOfSemiring Unit (@Ring.toSemiring Unit (@CommRing.toRing Unit PUnit.commRing)))) (@MulZeroClass.toZero Unit
      (@instMulZeroClassOfSemiring Unit (@Ring.toSemiring Unit (@CommRing.toRing Unit PUnit.commRing)))) (@PartialOrder.toPreorder Unit
      (@ChainCompletePartialOrder.toPartialOrder Unit
        (@ChainCompletePartialOrder.instOfCompleteLattice Unit
          (@CompleteBooleanAlgebra.toCompleteLattice Unit PUnit.instCompleteBooleanAlgebra)))) (by (try dsimp only);   decide)) (@MulPosMono.mk (Unit) (@Distrib.toMul Unit (@instDistribOfSemiring Unit (@Ring.toSemiring Unit (@CommRing.toRing Unit PUnit.commRing)))) (@MulZeroClass.toZero Unit
      (@instMulZeroClassOfSemiring Unit (@Ring.toSemiring Unit (@CommRing.toRing Unit PUnit.commRing)))) (@PartialOrder.toPreorder Unit
      (@ChainCompletePartialOrder.toPartialOrder Unit
        (@ChainCompletePartialOrder.instOfCompleteLattice Unit
          (@CompleteBooleanAlgebra.toCompleteLattice Unit PUnit.instCompleteBooleanAlgebra)))) (by (try dsimp only);   decide))) (@LinearOrder.toDecidableLT Unit PUnit.instLinearOrder) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide +kernel)

-- Function.iterate_cancel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.iterate_cancel.h5 : ¬∀ {α : Type} {f : α → α} {m n : ℕ} {a : α}, f^[m] a = f^[n] a → f^[m - n] a = a := fun hc_h => absurd (@hc_h (ℕ) (fun _ => 0 : ℕ → ℕ) (2) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Function.iterate_cancel, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.iterate_cancel.h6 : ¬∀ {α : Type} {f : α → α} {m n : ℕ} {a : α}, Function.Injective f → f^[m - n] a = a := fun hc_h => absurd (@hc_h (Bool) (not : Bool → Bool) (1) (0) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Function.IsPartialInv.get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.IsPartialInv.get_eq.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → Option α} (x : β) (h : (g x).isSome = Bool.true), f ((g x).get h) = x := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (some : ℕ → Option ℕ) (0) hc_k0) (by
  decide +kernel)

-- Equiv.swap_apply_of_ne_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.swap_apply_of_ne_of_ne.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a b x : α}, x ≠ b → (Equiv.swap a b) x = x := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Equiv.swap_apply_of_ne_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.swap_apply_of_ne_of_ne.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {a b x : α}, x ≠ a → (Equiv.swap a b) x = x := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Relation.TransGen.head', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.TransGen.head'.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, Relation.ReflTransGen r b c → Relation.TransGen r a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (0) (by
  rfl)) (by
  nofun)

-- Relation.TransGen.head', hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.TransGen.head'.h6.inst : ¬Relation.TransGen (fun (a b : ℕ) => a < b) 0 0 := by
  nofun
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.TransGen.head'.h6.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Relation.TransGen.head'.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, r a b → Relation.TransGen r a c := fun hc_h => HypCheckProof.Relation.TransGen.head'.h6.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (0) (1) (0) HypCheckProof.Relation.TransGen.head'.h6.prem0)

-- Encodable.decode₂_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Encodable.decode₂_inj.h5 : ¬∀ {α : Type} [inst : Encodable α] {n : ℕ} {a₁ a₂ : α}, a₂ ∈ Encodable.decode₂ α n → a₁ = a₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.encodable) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Encodable.decode₂_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Encodable.decode₂_inj.h6 : ¬∀ {α : Type} [inst : Encodable α] {n : ℕ} {a₁ a₂ : α}, a₁ ∈ Encodable.decode₂ α n → a₁ = a₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.encodable) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Relation.ReflTransGen.trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.ReflTransGen.trans.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, Relation.ReflTransGen r b c → Relation.ReflTransGen r a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0) (0) (by
  rfl)) (by
  nofun)

-- Relation.ReflTransGen.trans, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.ReflTransGen.trans.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, Relation.ReflTransGen r a b → Relation.ReflTransGen r a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (1) (0) (by
  rfl)) (by
  nofun)

-- Function.Injective.isPartialOrder_onFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.isPartialOrder_onFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) {f : α → β} [inst : IsPartialOrder β r], IsPartialOrder α (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun n => n / 2 : ℕ → ℕ) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.toAntisymm.antisymm (0 : ℕ) (1 : ℕ)
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

-- Function.Injective.isPartialOrder_onFun, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.isPartialOrder_onFun.h5 : ¬∀ {α β : Type} (r : β → β → Prop) {f : α → β}, Function.Injective f → IsPartialOrder α (Function.onFun r f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.toRefl.refl (Bool.false : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Refl.map, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Refl.map.h3 : ¬∀ {α β : Type} {r : α → α → Prop} {f : α → β}, Function.Surjective f → Std.Refl (Relation.Map r f f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ _ => False : Bool → Bool → Prop) (not : Bool → Bool) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.refl (Bool.false : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Refl.map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Refl.map.h5 : ¬∀ {α β : Type} {r : α → α → Prop} [inst : Std.Refl r] {f : α → β}, Std.Refl (Relation.Map r f f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ _ => True : Bool → Bool → Prop) (@Std.Refl.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.refl (2 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- SetRel.symm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.symm.h5 : ¬∀ {α : Type} (R : SetRel α α) {a b : α} [inst : R.IsSymm], (b, a) ∈ R := fun hc_h => absurd (@hc_h (ℕ) (∅) (0) (0) _) (by
  decide +kernel)

-- Function.LeftInverse.rightInverse_of_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.rightInverse_of_injective.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α}, Function.Injective f → Function.RightInverse f g := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (by
  decide)) (by
  decide +kernel)

-- Function.Injective2.right', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective2.right'.h4 : ¬∀ {α β γ : Type} {f : α → β → γ} [inst : Nonempty α], Function.Injective fun (b : β) (a : α) => f a b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) _) (by
  simp)

-- ENNReal.mul_lt_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_lt_mul.h4 : ¬∀ {a b c d : ENNReal}, b < d → a * b < c * d := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (by
  simp)) (by
  simp)

-- ENNReal.mul_lt_mul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_lt_mul.h5 : ¬∀ {a b c d : ENNReal}, a < c → a * b < c * d := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  simp)) (by
  simp)

-- Function.Injective2.left', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective2.left'.h4 : ¬∀ {α β γ : Type} {f : α → β → γ} [inst : Nonempty β], Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) (fun (a : ℕ) (b : Bool) => if b = Bool.true then 1 else 0) _) (by
  simp)

-- Std.Refl.rel_of_ne_imp, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Refl.rel_of_ne_imp.h2.inst : ¬(fun (a b : ℕ) => a < b) 0 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.Refl.rel_of_ne_imp.h2.prem0 : 0 ≠ 0 → (fun (a b : ℕ) => a < b) 0 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.Refl.rel_of_ne_imp.h2 : ¬∀ {α : Type} {r : α → α → Prop} {x y : α}, (x ≠ y → r x y) → r x y := fun hc_h => HypCheckProof.Std.Refl.rel_of_ne_imp.h2.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (0) (0) HypCheckProof.Std.Refl.rel_of_ne_imp.h2.prem0)

-- Std.Refl.rel_of_ne_imp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Refl.rel_of_ne_imp.h5 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Refl r] {x y : α}, r x y := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) _ (1) (0)) (by
  decide +kernel)

-- Function.Injective.trichotomous_onFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.trichotomous_onFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) {f : α → β} [inst : Std.Trichotomous r], Std.Trichotomous (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun _ => 0 : ℕ → ℕ) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.trichotomous (0 : ℕ) (1 : ℕ)
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

-- Function.Injective.trichotomous_onFun, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.trichotomous_onFun.h5 : ¬∀ {α β : Type} (r : β → β → Prop) {f : α → β}, Function.Injective f → Std.Trichotomous (Function.onFun r f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  exact fun hc_c =>
    absurd
      (hc_c.trichotomous (Bool.false : Bool) (Bool.true : Bool)
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

-- Function.RightInverse.leftInverse_of_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.RightInverse.leftInverse_of_injective.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α}, Function.Injective g → Function.LeftInverse f g := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun n => n % 2 == 0 : ℕ → Bool) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  decide +kernel)

-- NNReal.le_mul_iInf, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.le_mul_iInf.h5 : ¬∀ {ι : Type} [inst : Nonempty ι] {a g : NNReal} {h : ι → NNReal}, a ≤ g * iInf h := fun hc_h => absurd (@hc_h (ℕ) _ (1) (0) (fun (a : ℕ) => 0)) (by
  simp)

-- NNReal.le_iInf_mul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.le_iInf_mul.h5 : ¬∀ {ι : Type} [inst : Nonempty ι] {a : NNReal} {g : ι → NNReal} {h : NNReal}, a ≤ iInf g * h := fun hc_h => absurd (@hc_h (ℕ) _ (1) (fun (a : ℕ) => 0) (0)) (by
  simp)

-- Iff.imp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.imp.h4 : ¬∀ {a b c d : Prop}, (b ↔ d) → (a → b ↔ c → d) := fun hc_h => absurd (@hc_h (True) (False) (False) (False) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Iff.imp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.imp.h5 : ¬∀ {a b c d : Prop}, (a ↔ c) → (a → b ↔ c → d) := fun hc_h => absurd (@hc_h (True) (True) (True) (False) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Function.Injective.map_swap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.map_swap.h5 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst_1 : DecidableEq β] {f : α → β} (x y z : α),
        f ((Equiv.swap x y) z) = (Equiv.swap (f x) (f y)) (f z) := fun hc_h => absurd (@hc_h (ℕ) (Bool) (instDecidableEqNat) (instDecidableEqBool) (fun n => n % 2 == 0 : ℕ → Bool) (0) (1) (2)) (by
  decide +kernel)

-- Equiv.subtypePreimage_symm_apply_coe_pos, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypePreimage_symm_apply_coe_pos.h7 : ¬∀ {α β : Type} (p : α → Prop) [inst : DecidablePred p] (x₀ : { a : α // p a } → β) (x : { a : α // ¬p a } → β) (a : α),
        p a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (fun (a : { a : ℕ // (fun (n : ℕ) => n = 0) a }) => 0) (fun (a : { a : ℕ // ¬(fun (n : ℕ) => n = 0) a }) => 0) (1)) (by
  decide +kernel)

-- Equiv.subtypeEquivCodomain_symm_apply_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypeEquivCodomain_symm_apply_ne.h7 : ¬∀ {X Y : Type} [inst : DecidableEq X] {x : X} (f : { x' : X // x' ≠ x } → Y) (y : Y) (x' : X), x' ≠ x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (0) (fun (a : { x' : ℕ // x' ≠ 0 }) => 0) (0) (0)) (by
  decide +kernel)

-- ENNReal.div_mul_div_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_mul_div_cancel.h3 : ¬∀ {a b c : ENNReal}, b ≠ ⊤ → a / b * (b / c) = a / c := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.div_lt_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_lt_iff.h3 : ¬∀ {a b c : ENNReal}, b ≠ ⊤ ∨ c ≠ ⊤ → (c / b < a ↔ c < a * b) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.mul_div_mul_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_div_mul_left.h3 : ¬∀ {c : ENNReal} (a b : ENNReal), c ≠ ⊤ → c * a / (c * b) = a / b := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  norm_num)

-- ENNReal.inv_mul_le_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_mul_le_iff.h3 : ¬∀ {x y z : ENNReal}, x ≠ ⊤ → (x⁻¹ * y ≤ z ↔ y ≤ x * z) := fun hc_h => absurd (@hc_h (0) (1) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.div_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_mul.h3 : ¬∀ {b c : ENNReal} (a : ENNReal), b ≠ ⊤ ∨ c ≠ ⊤ → a / b * c = a / (b / c) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.zpow_add, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.zpow_add.h1 : ¬∀ {x : ENNReal}, x ≠ ⊤ → ∀ (m n : ℤ), x ^ (m + n) = x ^ m * x ^ n := fun hc_h => absurd (@hc_h (0) (by
  decide) (1) (-1)) (by
  simp)

-- ENNReal.eq_div_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eq_div_iff.h3 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → (b = c / a ↔ a * b = c) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

-- Function.surjective_to_subsingleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.surjective_to_subsingleton.h3 : ¬∀ {α β : Type} [na : Nonempty α] (f : α → β), Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- Classical.some_spec₂, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Classical.some_spec₂.h2 : ¬∀ {α : Type} {p : α → Prop} (q : α → Prop), (∀ (a : α), p a → q a) → ∃ (a : α), p a := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (by
  simp)) (by
  simp)

-- Classical.some_spec₂, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Classical.some_spec₂.h4 : ¬∀ {α : Type} {p : α → Prop} {h : ∃ (a : α), p a} (q : α → Prop), q (Classical.choose h) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) hc_k0 (fun _ => False : ℕ → Prop)) (by
  simp)

-- Function.Surjective.uncountable, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.uncountable.h2 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective f → Uncountable α := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool) (by
  decide)) (by
  simp)

-- not_surjective_countable_uncountable, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_surjective_countable_uncountable.h3 : ¬∀ {α β : Type} [inst : Countable α] (f : α → β), ¬Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (not : Bool → Bool)) (by
  decide +kernel)

-- CompTriple.comp_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CompTriple.comp_apply.h6 : ¬∀ {M N P : Type} {φ : M → N} {ψ : N → P} {χ : M → P} (x : M), ψ (φ x) = χ x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- ENNReal.le_sub_of_add_le_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_sub_of_add_le_left.h4 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → b ≤ c - a := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.eq_sub_of_add_eq', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eq_sub_of_add_eq'.h3 : ¬∀ {a b c : ENNReal}, a + c = b → a = b - c := fun hc_h => absurd (@hc_h (1) _ (⊤) rfl) (by
  simp)

-- ENNReal.eq_sub_of_add_eq', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eq_sub_of_add_eq'.h4 : ¬∀ {a b c : ENNReal}, b ≠ ⊤ → a = b - c := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.lt_add_of_sub_lt_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.lt_add_of_sub_lt_left.h4 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ ∨ b ≠ ⊤ → a < b + c := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.sub_lt_of_lt_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_lt_of_lt_add.h3 : ¬∀ {a b c : ENNReal}, a < b + c → a - c < b := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  simp)) (by
  simp)

-- ENNReal.sub_lt_of_lt_add, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_lt_of_lt_add.h4 : ¬∀ {a b c : ENNReal}, c ≤ a → a - c < b := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  rfl)) (by
  simp)

-- ENNReal.mul_le_mul_iff_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_le_mul_iff_right.h3 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → (a * b ≤ a * c ↔ b ≤ c) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.mul_right_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_right_inj.h3 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → (a * b = a * c ↔ b = c) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.add_lt_add_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_lt_add_right.h4 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → b + a < c + a := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.mul_le_mul_iff_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_le_mul_iff_left.h3 : ¬∀ {a b c : ENNReal}, c ≠ ⊤ → (a * c ≤ b * c ↔ a ≤ b) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  simp)

-- Function.not_surjective_of_isEmpty_of_nonempty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.not_surjective_of_isEmpty_of_nonempty.h2 : ¬∀ {α β : Type} [inst : Nonempty β] (f : α → β), ¬Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (not : Bool → Bool)) (by
  decide +kernel)

-- ENNReal.sub_le_sub_iff_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_le_sub_iff_left.h3 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → (a - b ≤ a - c ↔ c ≤ b) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- Iff.ne_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.ne_right.h6 : ¬∀ {α β : Type} {a b : α} {c d : β}, a = b ↔ c ≠ d := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) (0) (0) (0)) (by
  decide +kernel)

-- Equiv.image_strictAnti, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.image_strictAnti.h6 : Not
      (∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {e : Equiv α β} (s : Set α),
        @StrictAnti (@Set.Elem α s)
          (@Set.Elem β
            (@Set.image α β
              (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
              s))
          (@Subtype.preorder α inst fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) s x)
          (@Subtype.preorder β inst_1 fun (x : β) =>
            @Membership.mem β (Set β) (@Set.instMembership β)
              (@Set.image α β
                (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                  (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
                s)
              x)
          (@DFunLike.coe
            (Equiv (@Set.Elem α s)
              (@Set.Elem β
                (@Set.image α β
                  (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
                  s)))
            (@Set.Elem α s)
            (fun (x : @Set.Elem α s) =>
              @Set.Elem β
                (@Set.image α β
                  (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
                  s))
            (@EquivLike.toFunLike
              (Equiv (@Set.Elem α s)
                (@Set.Elem β
                  (@Set.image α β
                    (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                      (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
                    s)))
              (@Set.Elem α s)
              (@Set.Elem β
                (@Set.image α β
                  (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
                  s))
              (@Equiv.instEquivLike (@Set.Elem α s)
                (@Set.Elem β
                  (@Set.image α β
                    (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                      (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
                    s))))
            (@Equiv.image α β e s))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialOrder.toPreorder Bool Bool.instPartialOrder) (@PartialOrder.toPreorder Bool Bool.instPartialOrder) (@Equiv.mk Bool Bool (fun (b : Bool) => b) (fun (b : Bool) => b)
      (@of_decide_eq_true
        (autoParam (@Function.LeftInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b) Equiv.left_inv._autoParam)
        (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
          fun (b : Bool) => b)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (autoParam (@Function.LeftInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b)
                Equiv.left_inv._autoParam)
              (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
                fun (b : Bool) => b))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (autoParam (@Function.RightInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b) Equiv.right_inv._autoParam)
        (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
          fun (b : Bool) => b)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (autoParam (@Function.RightInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b)
                Equiv.right_inv._autoParam)
              (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
                fun (b : Bool) => b))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Set.ofPred Bool fun (x : Bool) => True)) (by
  decide +kernel)

-- Equiv.subtypeEquiv_apply, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypeEquiv_apply.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} (e : α ≃ β) (a : { a : α // p a }) (a : α), p a ↔ q (e a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { a : ℕ // (fun (n : ℕ) => n = 0) a }))) (by
  simp)

-- Equiv.Perm.subtypeCongr.right_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Perm.subtypeCongr.right_apply.h6 : ¬∀ {ε : Type} {p : ε → Prop} [inst : DecidablePred p] (ep : Equiv.Perm { a : ε // p a })
        (en : Equiv.Perm { a : ε // ¬p a }) {a : ε}, ¬p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ({
      toFun := fun (a : { a : ℕ // (fun (n : ℕ) => n = 0) a }) =>
        (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { a : ℕ // (fun (n : ℕ) => n = 0) a }),
      invFun := fun (a : { a : ℕ // (fun (n : ℕ) => n = 0) a }) =>
        (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { a : ℕ // (fun (n : ℕ) => n = 0) a }),
      left_inv := of_decide_eq_true (id (Eq.refl Bool.true)), right_inv := of_decide_eq_true (id (Eq.refl Bool.true)) :
      { a : ℕ // (fun (n : ℕ) => n = 0) a } ≃ { a : ℕ // (fun (n : ℕ) => n = 0) a } }) (1) (0)) (by
  decide +kernel)

-- ENNReal.zpow_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.zpow_ne_top.h2 : ¬∀ {a : ENNReal}, a ≠ 0 → ∀ (n : ℤ), a ^ n ≠ ⊤ := fun hc_h => absurd (@hc_h (⊤) (by
  decide) (1)) (by
  simp)

-- congr_refl_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.congr_refl_right.h4 : ¬∀ {α β : Type} {f g : α → β} (a : α), f = g := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ => 0 : Bool → ℕ) (Bool.false)) (by
  decide +kernel)

-- ENNReal.mul_div_cancel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_div_cancel.h2 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → a * (b / a) = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.mul_div_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_div_cancel.h3 : ¬∀ {a b : ENNReal}, a ≠ 0 → a * (b / a) = b := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.mul_inv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_inv.h2 : ¬∀ {a b : ENNReal}, a ≠ ⊤ ∨ b ≠ 0 → (a * b)⁻¹ = a⁻¹ * b⁻¹ := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.mul_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_inv.h3 : ¬∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → (a * b)⁻¹ = a⁻¹ * b⁻¹ := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide)) (by
  simp)

-- Ne.ite_eq_right_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ne.ite_eq_right_iff.h5 : ¬∀ {α : Type} {P : Prop} [inst : Decidable P] {a b : α}, (if P then a else b) = b ↔ ¬P := fun hc_h => absurd (@hc_h (ℕ) (True) (instDecidableTrue) (0) (0)) (by
  decide +kernel)

-- Ne.dite_eq_right_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ne.dite_eq_right_iff.h5 : ¬∀ {α : Type} {P : Prop} [inst : Decidable P] {b : α} {A : P → α}, (dite P A fun (x : ¬P) => b) = b ↔ ¬P := fun hc_h => absurd (@hc_h (ℕ) (True) (instDecidableTrue) (0) (fun (a : True) => 0)) (by
  decide +kernel)

-- ENNReal.div_eq_one_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_eq_one_iff.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → (a / b = 1 ↔ a = b) := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.div_eq_one_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_eq_one_iff.h3 : ¬∀ {a b : ENNReal}, b ≠ 0 → (a / b = 1 ↔ a = b) := fun hc_h => absurd (@hc_h (⊤) (⊤) (by
  decide)) (by
  simp)

-- Function.Embedding.codRestrict_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.codRestrict_apply.h4 : ¬∀ {α β : Type} (p : Set β) (f : α ↪ β) (a a : α), f a ∈ p := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({n : ℕ | n = 0}) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) (Bool.false)) (by
  decide +kernel)

-- ENNReal.exists_nnreal_pos_mul_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_nnreal_pos_mul_lt.h3 : Not
      (∀ {a b : ENNReal},
        @Ne ENNReal a (@Top.top ENNReal ENNReal.instTop) →
          ∃ (n : NNReal),
            And
              (@GT.gt NNReal (@Preorder.toLT NNReal (@PartialOrder.toPreorder NNReal NNReal.instPartialOrder)) n
                (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal NNReal.instZero)))
              (@LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
                (@HMul.hMul ENNReal ENNReal ENNReal
                  (@instHMul ENNReal
                    (@Distrib.toMul ENNReal
                      (@instDistribOfSemiring ENNReal (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring))))
                  (↑n) a)
                b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) (by
  decide)) (by
  simp)

-- Function.update_left_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.update_left_injective.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {ι : Type} {f : α → ι} {a : ι},
        Function.Injective fun (i : α) => Function.update f i a := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (ℕ) (fun _ => 0 : ℕ → ℕ) (0)) (by
  simp)

-- ENNReal.exists_pos_mul_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_pos_mul_lt.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → ∃ (c : ENNReal), 0 < c ∧ c * a < b := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.mul_inv_cancel_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_inv_cancel_right.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → a * b * b⁻¹ = a := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.mul_inv_cancel_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_inv_cancel_right.h3 : ¬∀ {a b : ENNReal}, b ≠ 0 → a * b * b⁻¹ = a := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- instUncountableProdOfNonempty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instUncountableProdOfNonempty.h2 : ¬∀ {α β : Type} [inst : Nonempty β], Uncountable (α × β) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _) (by
  simp)

-- congr_refl_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.congr_refl_left.h5 : ¬∀ {α β : Type} (f : α → β) {a b : α}, a = b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (1)) (by
  decide +kernel)

-- Equiv.subtypeEquiv_symm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypeEquiv_symm.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} (e : α ≃ β) (a : α), p a ↔ q (e a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (1)) (by
  simp)

-- ENNReal.lt_add_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.lt_add_right.h2 : ¬∀ {a b : ENNReal}, b ≠ 0 → a < a + b := fun hc_h => absurd (@hc_h (⊤) (1) (by
  simp)) (by
  decide +kernel)

-- ENNReal.lt_add_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.lt_add_right.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → a < a + b := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- Function.IsConst.eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.IsConst.eq.h3 : ¬∀ {α β : Type} {f : α → β} (x y : α), f x = f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (1)) (by
  decide +kernel)

-- Function.Surjective.of_comp_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.of_comp_iff.h5 : ¬∀ {α β γ : Type} (f : α → β) {g : γ → α}, Function.Surjective (f ∘ g) ↔ Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool) (not : Bool → Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- sign_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.sign_neg.h5 : ¬∀ {α : Type} [inst : Zero α] [inst_1 : Preorder α] [inst_2 : DecidableLT α] {a : α}, SignType.sign a = -1 := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instPreorder) (Nat.decLt) (0)) (by
  decide +kernel)

-- Right.sign_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Right.sign_neg.h4 : ¬∀ {α : Type} [inst : AddGroup α] [inst_1 : Preorder α] [inst_2 : DecidableLT α] (a : α),
        SignType.sign (-a) = -SignType.sign a := fun hc_h => absurd (@hc_h (Fin 2) ((Fin.addCommGroup 2).toAddGroup) (Fin.instPartialOrder.toPreorder) (Fin.decLt) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Left.sign_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Left.sign_neg.h4 : ¬∀ {α : Type} [inst : AddGroup α] [inst_1 : Preorder α] [inst_2 : DecidableLT α] (a : α),
        SignType.sign (-a) = -SignType.sign a := fun hc_h => absurd (@hc_h (Fin 2) ((Fin.addCommGroup 2).toAddGroup) (Fin.instPartialOrder.toPreorder) (Fin.decLt) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- SetLike.eta, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.SetLike.eta.h5.der.{u_1, u_2} : ∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p : A} (x : ↥p), ↑x ∈ p := by
  (intros; simp; done)
theorem HypCheckProof.SetLike.eta.h5.{u_1, u_2} : ∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p : A} (x : ↥p), (⟨↑x, HypCheckProof.SetLike.eta.h5.der x⟩ : ↥p) = x := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @SetLike.eta hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.SetLike.eta.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- SetRel.preimage_subset_preimage_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.preimage_subset_preimage_left.h5 : ¬∀ {α β : Type} {R₁ R₂ : SetRel α β} {t : Set β}, R₁.preimage t ⊆ R₂.preimage t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (⊤) (∅) ({n : ℕ | n = 0})) (by
  simp)

-- NNReal.exists_mem_Ioc_zpow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.exists_mem_Ioc_zpow.h2 : ¬∀ {x y : NNReal}, 1 < y → ∃ (n : ℤ), x ∈ Set.Ioc (y ^ n) (y ^ (n + 1)) := fun hc_h => absurd (@hc_h (0) (2) (by
  simp)) (by
  (simp <;> decide))

-- NNReal.exists_mem_Ioc_zpow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.exists_mem_Ioc_zpow.h3 : ¬∀ {x y : NNReal}, x ≠ 0 → ∃ (n : ℤ), x ∈ Set.Ioc (y ^ n) (y ^ (n + 1)) := fun hc_h => absurd (@hc_h (1) (1) (by
  simp)) (by
  simp)

-- NNReal.inv_lt_inv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.inv_lt_inv.h2 : ¬∀ {x y : NNReal}, x < y → y⁻¹ < x⁻¹ := fun hc_h => absurd (@hc_h (0) (1) (by
  simp)) (by
  simp)

-- NNReal.inv_lt_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.inv_lt_inv.h3 : ¬∀ {x y : NNReal}, x ≠ 0 → y⁻¹ < x⁻¹ := fun hc_h => absurd (@hc_h (1) (1) (by
  simp)) (by
  simp)

-- NNReal.exists_pow_lt_of_lt_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.exists_pow_lt_of_lt_one.h2 : ¬∀ {a b : NNReal}, b < 1 → ∃ (n : ℕ), b ^ n < a := fun hc_h => absurd (@hc_h (0) (0) (by
  simp)) (by
  simp)

-- NNReal.exists_pow_lt_of_lt_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.exists_pow_lt_of_lt_one.h3 : ¬∀ {a b : NNReal}, 0 < a → ∃ (n : ℕ), b ^ n < a := fun hc_h => absurd (@hc_h (1) (1) (by
  simp)) (by
  simp)

-- ENNReal.le_of_top_imp_top_of_toNNReal_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_of_top_imp_top_of_toNNReal_le.h2 : ¬∀ {a b : ENNReal}, (a ≠ ⊤ → b ≠ ⊤ → a.toNNReal ≤ b.toNNReal) → a ≤ b := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide)) (by
  decide +kernel)

-- ENNReal.le_of_top_imp_top_of_toNNReal_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_of_top_imp_top_of_toNNReal_le.h3 : ¬∀ {a b : ENNReal}, (a = ⊤ → b = ⊤) → a ≤ b := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.toNNReal_le_toNNReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_le_toNNReal.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → (a.toNNReal ≤ b.toNNReal ↔ a ≤ b) := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide)) (by
  simp)

-- ENNReal.toNNReal_le_toNNReal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_le_toNNReal.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → (a.toNNReal ≤ b.toNNReal ↔ a ≤ b) := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.toReal_le_toReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_le_toReal.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → (a.toReal ≤ b.toReal ↔ a ≤ b) := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide)) (by
  simp)

-- ENNReal.toReal_le_toReal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_le_toReal.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → (a.toReal ≤ b.toReal ↔ a ≤ b) := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.le_toNNReal_of_coe_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_toNNReal_of_coe_le.h2 : ¬∀ {a : ENNReal} {p : NNReal}, a ≠ ⊤ → p ≤ a.toNNReal := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.toNNReal_mono, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_mono.h2 : ¬∀ {a b : ENNReal}, a ≤ b → a.toNNReal ≤ b.toNNReal := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.toNNReal_mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_mono.h3 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → a.toNNReal ≤ b.toNNReal := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.toReal_min, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_min.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → (Min.min a b).toReal = Min.min a.toReal b.toReal := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.toReal_min, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_min.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → (Min.min a b).toReal = Min.min a.toReal b.toReal := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.toReal_sup, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_sup.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → (Max.max a b).toReal = Max.max a.toReal b.toReal := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.toReal_sup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_sup.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → (Max.max a b).toReal = Max.max a.toReal b.toReal := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- Ne.dite_ne_left_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ne.dite_ne_left_iff.h5 : ¬∀ {α : Type} {P : Prop} [inst : Decidable P] {a : α} {B : ¬P → α}, dite P (fun (x : P) => a) B ≠ a ↔ ¬P := fun hc_h => absurd (@hc_h (ℕ) (False) (instDecidableFalse) (0) (fun (a : ¬False) => 0)) (by
  decide +kernel)

-- Equiv.exists_congr', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.exists_congr'.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} (e : α ≃ β), (∃ (a : α), p a) ↔ ∃ (b : β), q b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (1)) (by
  simp)

-- Function.Surjective.of_comp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.of_comp.h5 : ¬∀ {α β γ : Type} {f : α → β} {g : γ → α}, Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (fun _ => true : Bool → Bool) (fun n => n % 2 == 0 : ℕ → Bool)) (by
  decide +kernel)

-- ENNReal.mul_eq_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_eq_right.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → (a * b = b ↔ a = 1) := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.mul_eq_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_eq_right.h3 : ¬∀ {a b : ENNReal}, b ≠ 0 → (a * b = b ↔ a = 1) := fun hc_h => absurd (@hc_h (2) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.Finiteness.add_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.Finiteness.add_ne_top.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → a + b ≠ ⊤ := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide)) (by
  decide +kernel)

-- ENNReal.Finiteness.add_ne_top, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.Finiteness.add_ne_top.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → a + b ≠ ⊤ := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide)) (by
  decide +kernel)

-- Equiv.forall_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.forall_congr.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} (e : α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), q b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => False : ℕ → Prop) (fun _ => True : ℕ → Prop) (1)) (by
  simp)

-- ENNReal.mul_lt_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_lt_top.h2 : ¬∀ {a b : ENNReal}, b < ⊤ → a * b < ⊤ := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.mul_lt_top, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_lt_top.h3 : ¬∀ {a b : ENNReal}, a < ⊤ → a * b < ⊤ := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- Equiv.Set.union_symm_apply_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.union_symm_apply_left.h4 : ¬∀ {α : Type} {s t : Set α} [inst : DecidablePred fun (x : α) => x ∈ s] (a : ↑s), Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun (a : ℕ) => Set.decidableOfPred a fun (n : ℕ) => n = 0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} }))) (by
  simp)

-- PartialEquiv.IsImage.image_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.IsImage.image_eq.h5 : Not
      (∀ {α β : Type} {e : PartialEquiv α β} {s : Set α} {t : Set β},
        @Eq (Set β)
          (@Set.image α β (@PartialEquiv.toFun α β e) (@Min.min (Set α) (@Set.instMin α) (@PartialEquiv.source α β e) s))
          (@Min.min (Set β) (@Set.instMin β) (@PartialEquiv.target α β e) t)) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)) (by
  simp)

-- Equiv.Set.insert_symm_apply_inr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.insert_symm_apply_inr.h4 : ¬∀ {α : Type} {s : Set α} [inst : DecidablePred fun (x : α) => x ∈ s] {a : α} (b : PUnit.{1}), a ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => Set.decidableOfPred a fun (n : ℕ) => n = 0) (0) (PUnit.unit)) (by
  decide +kernel)

-- Equiv.existsUnique_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.existsUnique_congr.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} (e : α ≃ β), (∃! a : α, p a) ↔ ∃! b : β, q b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (1)) (by
  simp)

-- Equiv.Set.union_symm_apply_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.union_symm_apply_right.h4 : ¬∀ {α : Type} {s t : Set α} [inst : DecidablePred fun (x : α) => x ∈ s] (a : ↑t), Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun (a : ℕ) => Set.decidableOfPred a fun (n : ℕ) => n = 0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} }))) (by
  simp)

-- ENNReal.mul_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_pos.h2 : ¬∀ {a b : ENNReal}, b ≠ 0 → 0 < a * b := fun hc_h => absurd (@hc_h (0) (1) (by
  simp)) (by
  simp)

-- ENNReal.mul_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_pos.h3 : ¬∀ {a b : ENNReal}, a ≠ 0 → 0 < a * b := fun hc_h => absurd (@hc_h (1) (0) (by
  simp)) (by
  simp)

-- Equiv.toPartialEquivOfImageEq_symm_apply, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.toPartialEquivOfImageEq_symm_apply.h5 : ¬∀ {α β : Type} (e : α ≃ β) (s : Set α) (t : Set β), ⇑e '' s = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Equiv.Set.image_symm_preimage, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.image_symm_preimage.h3 : ¬∀ {α β : Type} {f : α → β} (u s : Set α), Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Equiv.forall_congr', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.forall_congr'.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} (e : α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), q b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => False : ℕ → Prop) (fun _ => True : ℕ → Prop) (1)) (by
  simp)

-- Function.Injective.of_comp_iff', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.of_comp_iff'.h5 : ¬∀ {α β γ : Type} (f : α → β) {g : γ → α}, Function.Injective (f ∘ g) ↔ Function.Injective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ => true : ℕ → Bool)) (by
  simp)

-- Function.IsPartialInv.eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.IsPartialInv.eq.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → Option α} (x : α), g (f x) = Option.some x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => none : ℕ → Option ℕ) (0)) (by
  decide +kernel)

-- PartialEquiv.IsImage.symm_preimage_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.IsImage.symm_preimage_eq.h5 : Not
      (∀ {α β : Type} {e : PartialEquiv α β} {s : Set α} {t : Set β},
        @Eq (Set β)
          (@Min.min (Set β) (@Set.instMin β) (@PartialEquiv.target α β e)
            (@Set.preimage β α (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e)) s))
          (@Min.min (Set β) (@Set.instMin β) (@PartialEquiv.target α β e) t)) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)) (by
  simp)

-- Equiv.toPartialEquivOfImageEq_target, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.toPartialEquivOfImageEq_target.h5 : ¬∀ {α β : Type} (e : α ≃ β) (s : Set α) (t : Set β), ⇑e '' s = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Function.Injective.of_comp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.of_comp.h5 : ¬∀ {α β γ : Type} {f : α → β} {g : γ → α}, Function.Injective g := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Relation.SymmGen.swap, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.SymmGen.swap.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Relation.SymmGen (Function.swap r) a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0)) (by
  decide +kernel)

-- Relation.SymmGen.of_le, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.SymmGen.of_le.h4.inst : ¬Relation.SymmGen (fun (x1 x2 : Bool) => False) Bool.false Bool.false := by
  decide +kernel
theorem HypCheckProof.Relation.SymmGen.of_le.h4 : ¬∀ {α : Type} [inst : LE α] {a b : α}, Relation.SymmGen (fun (x1 x2 : α) => x1 ≤ x2) a b := fun hc_h => HypCheckProof.Relation.SymmGen.of_le.h4.inst (@hc_h (Bool) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (Bool.false) (Bool.false))

-- CompTriple.instComp_id, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CompTriple.instComp_id.h3 : ¬∀ {N P : Type} {φ : N → N} {ψ : N → P}, CompTriple φ ψ ψ := fun hc_h => absurd (@hc_h (Bool) (ℕ) (not : Bool → Bool) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.comp_eq)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- LE.le.symmGen, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.LE.le.symmGen.h4.inst : ¬Relation.SymmGen (fun (x1 x2 : Bool) => False) Bool.false Bool.false := by
  decide +kernel
theorem HypCheckProof.LE.le.symmGen.h4 : ¬∀ {α : Type} [inst : LE α] {a b : α}, Relation.SymmGen (fun (x1 x2 : α) => x1 ≤ x2) a b := fun hc_h => HypCheckProof.LE.le.symmGen.h4.inst (@hc_h (Bool) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (Bool.false) (Bool.false))

-- Std.Refl.ne_imp_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Refl.ne_imp_iff.h2 : ¬∀ {α : Type} {r : α → α → Prop} {x y : α}, x ≠ y → r x y ↔ r x y := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0)) (by
  decide +kernel)

-- Symmetric.comap, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Symmetric.comap.h3 : ¬∀ {α β : Type} {r : β → β → Prop} (f : α → β), Std.Symm (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
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

-- Relation.TransGen.to_reflTransGen, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.TransGen.to_reflTransGen.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Relation.ReflTransGen r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0)) (by
  nofun)

-- IsTrans.comap, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsTrans.comap.h3 : ¬∀ {α β : Type} {r : β → β → Prop} (f : α → β), IsTrans α (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≠ b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
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

-- Relation.ReflTransGen.single, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.ReflTransGen.single.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Relation.ReflTransGen r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0)) (by
  nofun)

-- LE.le.symmGen_symm, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.LE.le.symmGen_symm.h4.inst : ¬Relation.SymmGen (fun (x1 x2 : Bool) => False) Bool.false Bool.false := by
  decide +kernel
theorem HypCheckProof.LE.le.symmGen_symm.h4 : ¬∀ {α : Type} [inst : LE α] {a b : α}, Relation.SymmGen (fun (x1 x2 : α) => x1 ≤ x2) a b := fun hc_h => HypCheckProof.LE.le.symmGen_symm.h4.inst (@hc_h (Bool) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (Bool.false) (Bool.false))

-- Function.instIsEquivOnFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsEquivOnFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) (f : α → β), IsEquiv α (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.toRefl.refl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.LeftInverse.rightInverse, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.rightInverse.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α}, Function.RightInverse f g := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool)) (by
  decide +kernel)

-- Function.Injective.comp_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.comp_left.h4 : ¬∀ {α β γ : Type} {g : β → γ}, Function.Injective fun (x : α → β) => g ∘ x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) (fun _ => true : ℕ → Bool)) (by
  simp)

-- Equiv.Perm.congr_arg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Perm.congr_arg.h4 : ¬∀ {α : Type} {f : Equiv.Perm α} {x x' : α}, f x = f x' := fun hc_h => absurd (@hc_h (ℕ) (1) (0) (1)) (by
  decide +kernel)

-- Function.instSymmOnFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instSymmOnFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) (f : α → β), Std.Symm (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
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

-- Function.Surjective.forall, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.forall.h3 : ¬∀ {α β : Type} {f : α → β} {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f x) := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun _ => true : ℕ → Bool) (fun b => b = true : Bool → Prop)) (by
  simp)

-- Function.Bijective.comp_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.comp_left.h4 : ¬∀ {α β γ : Type} {g : β → γ}, Function.Bijective fun (x : α → β) => g ∘ x := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (fun _ => 0 : Bool → ℕ)) (by
  nofun)

-- Equiv.subtypeEquivRight_apply_coe, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypeEquivRight_apply_coe.h3 : ¬∀ {α : Type} {p q : α → Prop} (a : { a : α // p a }) (x : α), p x ↔ q x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { a : ℕ // (fun (n : ℕ) => n = 0) a }))) (by
  simp)

-- Equiv.subtypeEquivRight_symm_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypeEquivRight_symm_apply.h3 : ¬∀ {α : Type} {p q : α → Prop} (z : { x : α // q x }) (x : α), p x ↔ q x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // (fun (n : ℕ) => n = 0) x }))) (by
  simp)

-- Equiv.Set.sumCompl_symm_apply_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.sumCompl_symm_apply_of_notMem.h4 : ¬∀ {α : Type} {s : Set α} [inst : DecidablePred fun (x : α) => x ∈ s] {x : α}, x ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => Set.decidableOfPred a fun (n : ℕ) => n = 0) (0)) (by
  decide +kernel)

-- Function.instIrreflOnFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIrreflOnFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) (f : α → β), Std.Irrefl (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.irrefl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- NNReal.mul_iSup_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.mul_iSup_le.h4 : ¬∀ {ι : Type} {a g : NNReal} {h : ι → NNReal}, g * iSup h ≤ a := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (fun (a : ℕ) => 1)) (by
  simp)

-- Equiv.subtypeEquivRight_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypeEquivRight_apply.h3 : ¬∀ {α : Type} {p q : α → Prop} (z : { x : α // p x }) (x : α), p x ↔ q x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // (fun (n : ℕ) => n = 0) x }))) (by
  simp)

-- Function.Surjective.comp_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.comp_left.h4 : ¬∀ {α β γ : Type} {g : β → γ}, Function.Surjective fun (x : α → β) => g ∘ x := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- SetRel.dom_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.dom_mono.h4 : ¬∀ {α β : Type} {R₁ R₂ : SetRel α β}, R₁.dom ⊆ R₂.dom := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (⊤) (∅)) (by
  simp)

-- Function.LeftInverse.iterate, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.iterate.h3 : ¬∀ {α : Type} {f g : α → α} (n : ℕ), Function.LeftInverse g^[n] f^[n] := fun hc_h => absurd (@hc_h (Bool) (not : Bool → Bool) (fun _ => true : Bool → Bool) (1)) (by
  decide +kernel)

-- SetRel.inv_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.inv_mono.h4 : ¬∀ {α β : Type} {R₁ R₂ : SetRel α β}, R₁.inv ⊆ R₂.inv := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (⊤) (∅)) (by
  simp)

-- PEquiv.single_subsingleton_eq_refl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PEquiv.single_subsingleton_eq_refl.h2 : ¬∀ {α : Type} [inst : DecidableEq α] (a b : α), PEquiv.single a b = PEquiv.refl α := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (Bool.false) (Bool.false)) (by
  decide +kernel)

-- Equiv.strictMono_setCongr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.strictMono_setCongr.h4 : ¬∀ {α : Type} {s t : Set α} [inst : Preorder α], s = t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (Nat.instPreorder)) (by
  simp)

-- ne_and_eq_iff_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ne_and_eq_iff_right.h4 : ¬∀ {α : Type} {a b c : α}, a ≠ b ∧ a = c ↔ a = c := fun hc_h => absurd (@hc_h (ℕ) (0) (0) (0)) (by
  decide +kernel)

-- Function.Embedding.sumSet_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.sumSet_apply.h3 : ¬∀ {α : Type} {s t : Set α} (a : ↑s ⊕ ↑t), Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (Sum.inl (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} }))) (by
  simp)

-- PartialEquiv.image_symm_image_of_subset_target, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.image_symm_image_of_subset_target.h4 : ¬∀ {α β : Type} (e : PartialEquiv α β) {s : Set β}, ↑e '' ↑e.symm '' s = s := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Inhabited.default) ({b : Bool | b = Bool.true})) (by
  (simp <;> decide))

-- PartialEquiv.map_source, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.map_source.h4 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) {x : α},
        @Membership.mem β (Set β) (@Set.instMembership β) (@PartialEquiv.target α β e) (@PartialEquiv.toFun α β e x)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Inhabited.default (PartialEquiv Nat Nat) (@PartialEquiv.instInhabited Nat Nat instInhabitedNat instInhabitedNat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  nofun)

-- PartialEquiv.left_inv, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.left_inv.h4 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) {x : α},
        @Eq α (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e) (@PartialEquiv.toFun α β e x)) x) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Inhabited.default (PartialEquiv Nat Nat) (@PartialEquiv.instInhabited Nat Nat instInhabitedNat instInhabitedNat)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- PartialEquiv.map_target, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.map_target.h4 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) {x : β},
        @Membership.mem α (Set α) (@Set.instMembership α) (@PartialEquiv.source α β e)
          (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e) x)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Inhabited.default (PartialEquiv Nat Nat) (@PartialEquiv.instInhabited Nat Nat instInhabitedNat instInhabitedNat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  nofun)

-- Function.surjInv_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.surjInv_eq.h3 : ¬∀ {α β : Type} {f : α → β} (b : β), Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool) (Bool.false)) (by
  decide +kernel)

-- Std.Symm.comap, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Symm.comap.h3 : ¬∀ {α β : Type} {r : β → β → Prop} (f : α → β), Std.Symm (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
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

-- PartialEquiv.left_inv', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.left_inv'.h4 : Not
      (∀ {α β : Type} (self : PartialEquiv α β) ⦃x : α⦄,
        @Eq α (@PartialEquiv.invFun α β self (@PartialEquiv.toFun α β self x)) x) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Inhabited.default (PartialEquiv Nat Nat) (@PartialEquiv.instInhabited Nat Nat instInhabitedNat instInhabitedNat)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- ENNReal.add_left_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_left_inj.h3 : ¬∀ {a b c : ENNReal}, b + a = c + a ↔ b = c := fun hc_h => absurd (@hc_h (⊤) (0) (1)) (by
  simp)

-- ENNReal.add_lt_add_iff_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_lt_add_iff_right.h3 : ¬∀ {a b c : ENNReal}, b + a < c + a ↔ b < c := fun hc_h => absurd (@hc_h (⊤) (0) (1)) (by
  simp)

-- Relation.SymmGen.refl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.SymmGen.refl.h2 : ¬∀ {α : Type} (r : α → α → Prop) (a : α), Relation.SymmGen r a a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0)) (by
  decide +kernel)

-- ENNReal.exists_add_lt_of_add_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_add_lt_of_add_lt.h3 : ¬∀ {x y z : ENNReal}, ∃ y' > y, ∃ z' > z, y' + z' < x := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- ENNReal.add_lt_add_iff_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_lt_add_iff_left.h3 : ¬∀ {a b c : ENNReal}, a + b < a + c ↔ b < c := fun hc_h => absurd (@hc_h (⊤) (0) (1)) (by
  simp)

-- Function.injective_of_subsingleton, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.injective_of_subsingleton.h2 : ¬∀ {α β : Type} (f : α → β), Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Set.pairwise_iff_of_refl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.pairwise_iff_of_refl.h3 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α}, s.Pairwise r ↔ ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ({n : ℕ | n = 0})) (by
  simp)

-- Function.IsFixedPt.eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.IsFixedPt.eq.h3 : ¬∀ {α : Type} {f : α → α} {x : α}, f x = x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- ENNReal.half_lt_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.half_lt_self.h1 : ¬∀ {a : ENNReal}, a ≠ ⊤ → a / 2 < a := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- Function.Surjective.of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.of_isEmpty.h2 : ¬∀ {α β : Type} (f : α → β), Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- Equiv.sumEmpty_symm_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.sumEmpty_symm_apply.h2 : ¬∀ (α β : Type) (val : α), IsEmpty β := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.false (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Equiv.emptySum_symm_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.emptySum_symm_apply.h2 : ¬∀ (α β : Type) (a : β), IsEmpty α := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.false (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Equiv.emptySum_apply_inr, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.emptySum_apply_inr.h2 : ¬∀ {α β : Type} (b : β), IsEmpty α := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.false (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.Involutive.leftInverse_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Involutive.leftInverse_iff.h2 : ¬∀ {α : Type} {f g : α → α}, Function.LeftInverse g f ↔ g = f := fun hc_h => absurd (@hc_h (Bool) (fun _ => true : Bool → Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- existsUnique_congr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.existsUnique_congr.h3 : ¬∀ {α : Type} {p q : α → Prop}, (∃! a : α, p a) ↔ ∃! a : α, q a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop)) (by
  simp)

-- Function.injective_surjInv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.injective_surjInv.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- ENNReal.HolderTriple.inv_le_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.inv_le_inv.h3 : ¬∀ (p q r : ENNReal), p⁻¹ ≤ r⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- ENNReal.HolderTriple.inv_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.inv_eq.h3 : ¬∀ (p q r : ENNReal), r⁻¹ = p⁻¹ + q⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- ENNReal.HolderTriple.le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.le.h3 : ¬∀ (p q r : ENNReal), r ≤ p := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- ENNReal.HolderTriple.one_div_add_one_div, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.one_div_add_one_div.h3 : ¬∀ (p q r : ENNReal), 1 / p + 1 / q = 1 / r := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- signHom_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.signHom_apply.h3 : ¬∀ {α : Type} [inst : Ring α] [inst_1 : LinearOrder α], IsStrictOrderedRing α := fun hc_h => absurd (@hc_h (Unit) (PUnit.commRing.toRing) (PUnit.instLinearOrder)) (by
  exact fun hc_c =>
    absurd (hc_c.toNontrivial.exists_pair_ne)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.Surjective.iterate, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.iterate.h2 : ¬∀ {α : Type} {f : α → α} (n : ℕ), Function.Surjective f^[n] := fun hc_h => absurd (@hc_h (Bool) (fun _ => true : Bool → Bool) (1)) (by
  decide +kernel)

-- Fin.castLEquiv_symm_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castLEquiv_symm_apply.h2 : ¬∀ {n m : ℕ} (i : { i : Fin m // ↑i < n }), n ≤ m := fun hc_h => absurd (@hc_h (2) (1) ((⟨(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1), of_decide_eq_true (id (Eq.refl Bool.true))⟩ :
      { i : Fin 1 // ↑i < 2 }))) (by
  decide +kernel)

-- IsSymmOp.flip_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsSymmOp.flip_eq.h3 : ¬∀ {α β : Type} (op : α → α → β), flip op = op := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a b : Bool) => if b = Bool.true then 1 else 0)) (by
  decide +kernel)

-- finSuccEquiv'_above, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finSuccEquiv'_above.h3 : ¬∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, (finSuccEquiv' i) m.succ = Option.some m := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.castLEquiv_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castLEquiv_apply.h2 : ¬∀ {n m : ℕ} (i : Fin n), n ≤ m := fun hc_h => absurd (@hc_h (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- finSuccEquiv'_symm_some_above, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finSuccEquiv'_symm_some_above.h3 : ¬∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, (finSuccEquiv' i).symm (Option.some m) = m.succ := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- finSuccEquiv'_symm_coe_above, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finSuccEquiv'_symm_coe_above.h3 : ¬∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, (finSuccEquiv' i).symm (Option.some m) = m.succ := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- finSuccEquiv'_below, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finSuccEquiv'_below.h3 : ¬∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, (finSuccEquiv' i) m.castSucc = Option.some m := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Function.IsFixedPt.of_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.IsFixedPt.of_subsingleton.h1 : ¬∀ {α : Type} (f : α → α) (x : α), Function.IsFixedPt f x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Function.comp_iterate_pred_of_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.comp_iterate_pred_of_pos.h3 : ¬∀ {α : Type} (f : α → α) {n : ℕ}, f ∘ f^[n.pred] = f^[n] := fun hc_h => absurd (@hc_h (Bool) (not : Bool → Bool) (0)) (by
  decide +kernel)

-- Function.Embedding.coeFn_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.coeFn_mk.h3 : ¬∀ {α β : Type} (f : α → β), Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Equiv.self_comp_ofInjective_symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.self_comp_ofInjective_symm.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Equiv.coe_ofInjective_symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.coe_ofInjective_symm.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- nonempty_unique, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.nonempty_unique.h1 : ¬∀ (α : Type) [inst : Nonempty α], Nonempty (Unique α) := fun hc_h => absurd (@hc_h (Bool) _) (by
  nofun)

-- NNReal.HolderTriple.nonneg', hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.NNReal.HolderTriple.nonneg'.h3.gneg : ∀ {p q r : NNReal}, ¬p.HolderTriple q r → 0 ≤ r := by
  (intros; simp; done)
theorem HypCheckProof.NNReal.HolderTriple.nonneg'.h3 : ∀ {p q : NNReal} {r : NNReal}, 0 ≤ r := by
  intro hc_x0 hc_x1 hc_x2
  exact Classical.byCases (fun hc_h => @NNReal.HolderTriple.nonneg' hc_x0 hc_x1 hc_x2 hc_h) (fun hc_hn => @HypCheckProof.NNReal.HolderTriple.nonneg'.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn)

-- NNReal.HolderTriple.nonneg, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.NNReal.HolderTriple.nonneg.h3.gneg : ∀ {p q r : NNReal}, ¬p.HolderTriple q r → 0 ≤ p := by
  (intros; simp; done)
theorem HypCheckProof.NNReal.HolderTriple.nonneg.h3 : ∀ {p : NNReal} {q r : NNReal}, 0 ≤ p := by
  intro hc_x0 hc_x1 hc_x2
  exact Classical.byCases (fun hc_h => @NNReal.HolderTriple.nonneg hc_x0 hc_x1 hc_x2 hc_h) (fun hc_hn => @HypCheckProof.NNReal.HolderTriple.nonneg.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn)

-- Real.HolderTriple.inv_lt_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.inv_lt_inv.h3 : ¬∀ {p : ℝ} {q : ℝ} {r : ℝ}, p⁻¹ < r⁻¹ := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ })) (by
  simp)

-- NNReal.HolderTriple.one_div_nonneg, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.NNReal.HolderTriple.one_div_nonneg.h3.gneg : ∀ {p q r : NNReal}, ¬p.HolderTriple q r → 0 ≤ 1 / p := by
  (intros; simp; done)
theorem HypCheckProof.NNReal.HolderTriple.one_div_nonneg.h3 : ∀ {p : NNReal} {q r : NNReal}, 0 ≤ 1 / p := by
  intro hc_x0 hc_x1 hc_x2
  exact Classical.byCases (fun hc_h => @NNReal.HolderTriple.one_div_nonneg hc_x0 hc_x1 hc_x2 hc_h) (fun hc_hn => @HypCheckProof.NNReal.HolderTriple.one_div_nonneg.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn)

-- NNReal.HolderTriple.one_div_add_one_div, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.one_div_add_one_div.h3 : ¬∀ {p q r : NNReal}, 1 / p + 1 / q = 1 / r := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- NNReal.HolderTriple.ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.ne_zero.h3 : ¬∀ {p : NNReal} {q r : NNReal}, p ≠ 0 := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- false_of_nontrivial_of_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.false_of_nontrivial_of_subsingleton.h1 : ¬∀ (α : Type) [inst : Subsingleton α], False := fun hc_h => absurd (@hc_h (Unit) _) (by
  decide +kernel)

-- false_of_nontrivial_of_subsingleton, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.false_of_nontrivial_of_subsingleton.h2 : ¬∀ (α : Type) [inst : Nontrivial α], False := fun hc_h => absurd (@hc_h (ℕ) _) (by
  decide +kernel)

-- Uncountable.of_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Uncountable.of_equiv.h2 : ¬∀ {β : Type} (α : Type) (e : α ≃ β), Uncountable β := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1)) (by
  simp)

-- exists_of_exists_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.exists_of_exists_mem.h3 : ¬∀ {α : Type} {p : α → Prop} {q : α → Prop}, ∃ (x : α), q x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop)) (by
  simp)

-- ENNReal.toReal_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_pos.h1 : ¬∀ {a : ENNReal}, a ≠ ⊤ → 0 < a.toReal := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- ENNReal.toReal_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_pos.h2 : ¬∀ {a : ENNReal}, a ≠ 0 → 0 < a.toReal := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  simp)

-- Sigma.uncountable, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sigma.uncountable.h3 : ¬∀ {α : Type} {π : α → Type} (a : α), Uncountable (Sigma π) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (0)) (by
  simp)

-- Function.comp_surjInv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.comp_surjInv.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- PartialEquiv.surjective_of_target_eq_univ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.surjective_of_target_eq_univ.h3 : Not (∀ {α β : Type} (e : PartialEquiv α β), @Function.Surjective α β (@PartialEquiv.toFun α β e)) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool (fun (x : Bool) => Bool.true) (fun (x : Bool) => Bool.true)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
              (instDecidableEqBool Bool.true Bool.true))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
                    (instDecidableEqBool Bool.true Bool.true)))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
              (instDecidableEqBool Bool.true Bool.true))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
                    (instDecidableEqBool Bool.true Bool.true)))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool Bool.true x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool Bool.true x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool Bool.true a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            instDecidableEqBool Bool.true a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool Bool.true x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool Bool.true x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool Bool.true a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  instDecidableEqBool Bool.true a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool Bool.true x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool Bool.true x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool Bool.true a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            instDecidableEqBool Bool.true a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool Bool.true x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool Bool.true x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool Bool.true a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  instDecidableEqBool Bool.true a))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- ENNReal.pow_lt_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.pow_lt_top.h2 : ¬∀ {a : ENNReal} {n : ℕ}, a ^ n < ⊤ := fun hc_h => absurd (@hc_h (⊤) (1)) (by
  decide +kernel)

-- ENNReal.HolderConjugate.lt_top_iff_one_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.lt_top_iff_one_lt.h2 : ¬∀ (p q : ENNReal), p < ⊤ ↔ 1 < q := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Int.divModEquiv_apply, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.divModEquiv_apply.h1 : ¬∀ (n : ℕ) (a : ℤ), NeZero n := fun hc_h => absurd (@hc_h (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.divModEquiv_apply, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.divModEquiv_apply.h1 : ¬∀ (n a : ℕ), NeZero n := fun hc_h => absurd (@hc_h (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- finSumNatEquiv_symm_apply_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finSumNatEquiv_symm_apply_of_lt.h2 : ¬∀ {n i : ℕ}, i < n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- NNReal.iSup_of_not_bddAbove, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.iSup_of_not_bddAbove.h2 : ¬∀ {ι : Type} {f : ι → NNReal}, ⨆ (i : ι), f i = 0 := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => 1)) (by
  simp)

-- ENNReal.nnreal_smul_ne_top_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.nnreal_smul_ne_top_iff.h2 : ¬∀ {x : NNReal} {y : ENNReal}, x • y ≠ ⊤ ↔ y ≠ ⊤ := fun hc_h => absurd (@hc_h (0) (⊤)) (by
  simp)

-- SetRel.instIsTransOfPredProdMatch_1PropOfIsTrans, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.instIsTransOfPredProdMatch_1PropOfIsTrans.h2 : ¬∀ {α : Type} {R : α → α → Prop}, SetRel.IsTrans {(a, b) : α × α | R a b} := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≠ b : ℕ → ℕ → Prop)) (by
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

-- Function.instSymmSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instSymmSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), Std.Symm (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (1 : ℕ) (0 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.inv_lt_inv', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_lt_inv'.h2 : ¬∀ {a b : ENNReal}, b⁻¹ < a⁻¹ := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- ENNReal.mulLeftOrderIso_symm_apply, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mulLeftOrderIso_symm_apply.h1 : ¬∀ (a x : ENNReal), IsUnit a := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- ENNReal.coe_div, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.coe_div.h2 : Not
      (∀ {r p : NNReal},
        @Eq ENNReal (↑(@HDiv.hDiv NNReal NNReal NNReal (@instHDiv NNReal NNReal.instDiv) p r))
          (@HDiv.hDiv ENNReal ENNReal ENNReal (@instHDiv ENNReal (@DivInvMonoid.toDiv ENNReal ENNReal.instDivInvMonoid)) ↑p
            ↑r)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal NNReal.instZero)) (@OfNat.ofNat NNReal (nat_lit 1) (@One.toOfNat1 NNReal NNReal.instOne))) (by
  simp)

-- CauSeq.Completion.ofRat_rat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CauSeq.Completion.ofRat_rat.h1 : ¬∀ {abv : ℚ → ℚ} (q : ℚ), IsAbsoluteValue abv := fun hc_h => absurd (@hc_h (fun (a : ℚ) => 0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.abv_eq_zero' (x := (1 : ℚ)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- PProd.isEmpty_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PProd.isEmpty_right.h2 : ¬∀ {α β : Type}, IsEmpty (α ×' β) := fun hc_h => absurd (@hc_h (ℕ) (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false (⟨0, 0⟩ : ℕ ×' ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- instIsEmptySubtype, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instIsEmptySubtype.h1 : ¬∀ {α : Type} (p : α → Prop), IsEmpty (Subtype p) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.false ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 }) : { n : ℕ // n = 0 }))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- IsEmpty.false, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsEmpty.false.h1 : ¬∀ {α : Type} (a : α), False := fun hc_h => absurd (@hc_h (ℕ) (0)) (by
  decide +kernel)

-- Quot.instIsEmpty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Quot.instIsEmpty.h1 : ¬∀ {α : Type} {r : α → α → Prop}, IsEmpty (Quot r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.false (Inhabited.default : Quot fun (a b : ℕ) => a < b))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Subtype.isEmpty_of_false, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.isEmpty_of_false.h2 : ¬∀ {α : Type} {p : α → Prop}, IsEmpty (Subtype p) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.false ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 }) : { n : ℕ // n = 0 }))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Prod.isEmpty_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.isEmpty_right.h2 : ¬∀ {α β : Type}, IsEmpty (α × β) := fun hc_h => absurd (@hc_h (ℕ) (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false ((0, 0) : ℕ × ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- NNReal.iInf_empty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.iInf_empty.h1 : ¬∀ {ι : Type} (f : ι → NNReal), ⨅ (i : ι), f i = 0 := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => 1)) (by
  simp)

-- NNReal.HolderConjugate.inv_add_inv_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderConjugate.inv_add_inv_eq_one.h2 : ¬∀ {p q : NNReal}, p⁻¹ + q⁻¹ = 1 := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- ENNReal.pow_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.pow_pos.h1 : ¬∀ {a : ENNReal} (n : ℕ), 0 < a ^ n := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- NNReal.HolderConjugate.sub_one_mul_conj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderConjugate.sub_one_mul_conj.h2 : ¬∀ {p q : NNReal}, (p - 1) * q = p := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- Equiv.equiv_subsingleton_dom, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.equiv_subsingleton_dom.h2 : ¬∀ {α β : Type}, Subsingleton (α ≃ β) := fun hc_h => absurd (@hc_h (Bool) (Bool)) (by
  exact fun hc_c =>
    absurd
      (hc_c.allEq
        (@Equiv.mk Bool Bool Bool.not Bool.not
            (@of_decide_eq_true (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
              (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
                    (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
                  Bool.true)
                (@Eq.refl Bool Bool.true)))
            (@of_decide_eq_true
              (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
              (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
                    (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
                  Bool.true)
                (@Eq.refl Bool Bool.true))) :
          Equiv Bool Bool)
        (@Equiv.mk Bool Bool (fun (b : Bool) => b) (fun (b : Bool) => b)
            (@of_decide_eq_true
              (autoParam (@Function.LeftInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b)
                Equiv.left_inv._autoParam)
              (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
                fun (b : Bool) => b)
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (autoParam (@Function.LeftInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b)
                      Equiv.left_inv._autoParam)
                    (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
                      fun (b : Bool) => b))
                  Bool.true)
                (@Eq.refl Bool Bool.true)))
            (@of_decide_eq_true
              (autoParam (@Function.RightInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b)
                Equiv.right_inv._autoParam)
              (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
                fun (b : Bool) => b)
              (@id
                (@Eq Bool
                  (@Decidable.decide
                    (autoParam (@Function.RightInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b)
                      Equiv.right_inv._autoParam)
                    (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype
                      (fun (b : Bool) => b) fun (b : Bool) => b))
                  Bool.true)
                (@Eq.refl Bool Bool.true))) :
          Equiv Bool Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.mulLeftOrderIso_apply, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mulLeftOrderIso_apply.h1 : ¬∀ (a x : ENNReal), IsUnit a := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- ENNReal.HolderConjugate.div_conj_eq_sub_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.div_conj_eq_sub_one.h2 : ¬∀ {p q : ENNReal}, p / q = p - 1 := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- ENNReal.HolderConjugate.mul_eq_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.mul_eq_add.h2 : ¬∀ {p q : ENNReal}, p * q = p + q := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- Equiv.Perm.coe_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Perm.coe_subsingleton.h1 : Not
      (∀ {α : Type} (e : Equiv.Perm α),
        @Eq (α → α)
          (@DFunLike.coe (Equiv.Perm α) α (fun (x : α) => α)
            (@EquivLike.toFunLike (Equiv.Perm α) α α (@Equiv.instEquivLike α α)) e)
          (@id α)) := fun hc_h => absurd (@hc_h (Bool) (@Equiv.mk Bool Bool Bool.not Bool.not
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
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- ENNReal.eq_of_forall_le_nnreal_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eq_of_forall_le_nnreal_iff.h2 : ¬∀ {x y : ENNReal}, x = y := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- Function.instIsEquivSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsEquivSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), IsEquiv α (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.toRefl.refl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Iff.not, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.not.h2 : ¬∀ {a b : Prop}, ¬a ↔ ¬b := fun hc_h => absurd (@hc_h (True) (False)) (by
  decide +kernel)

-- ENNReal.coe_le_coe_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.coe_le_coe_of_le.h2 : Not (∀ {r q : NNReal}, @LE.le ENNReal ENNReal.instLE ↑r ↑q) := fun hc_h => absurd (@hc_h (@OfNat.ofNat NNReal (nat_lit 1) (@One.toOfNat1 NNReal NNReal.instOne)) (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal NNReal.instZero))) (by
  simp)

-- Xor.or, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Xor.or.h2 : ¬∀ {a b : Prop}, a ∨ b := fun hc_h => absurd (@hc_h (False) (False)) (by
  decide +kernel)

-- instSubsingletonSubtype_mathlib, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instSubsingletonSubtype_mathlib.h1 : ¬∀ {α : Type} (p : α → Prop), Subsingleton (Subtype p) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 = 0 : ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.allEq ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n % 2 = 0 }) : { n : ℕ // n % 2 = 0 })
        ((⟨2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n % 2 = 0 }) : { n : ℕ // n % 2 = 0 }))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Equiv.subtypeEquiv_refl, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Equiv.subtypeEquiv_refl.h2.der.{u_1} : ∀ {α : Sort u_1} {p : α → Prop} (a : α), p a ↔ p ((Equiv.refl α) a) := by
  (intros; trivial)
theorem HypCheckProof.Equiv.subtypeEquiv_refl.h2.{u_1} : ∀ {α : Sort u_1} {p : α → Prop},
      (Equiv.refl α).subtypeEquiv HypCheckProof.Equiv.subtypeEquiv_refl.h2.der = Equiv.refl { a : α // p a } := by
  intro hc_x0 hc_x1
  exact @Equiv.subtypeEquiv_refl hc_x0 hc_x1 (@HypCheckProof.Equiv.subtypeEquiv_refl.h2.der hc_x0 hc_x1)

-- ENNReal.add_sub_cancel_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_sub_cancel_left.h2 : ¬∀ {a b : ENNReal}, a + b - a = b := fun hc_h => absurd (@hc_h (⊤) (1)) (by
  simp)

-- Nat.Subtype.exists_succ, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Subtype.exists_succ.h1 : ¬∀ {s : Set ℕ} (x : ↑s), ∃ (n : ℕ), ↑x + n + 1 ∈ s := fun hc_h => absurd (@hc_h ({n : ℕ | n = 0}) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} }))) (by
  simp)

-- NNReal.inv_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.inv_le.h2 : ¬∀ {r p : NNReal}, r⁻¹ ≤ p ↔ 1 ≤ r * p := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- NNReal.coe_sub_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.coe_sub_of_lt.h2 : Not
      (∀ {a b : NNReal},
        @Eq Real (↑(@HSub.hSub NNReal NNReal NNReal (@instHSub NNReal NNReal.instSub) b a))
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) ↑b ↑a)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat NNReal (nat_lit 1) (@One.toOfNat1 NNReal NNReal.instOne)) (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal NNReal.instZero))) (by
  simp)

-- ENNReal.ofReal_le_ofNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_le_ofNat.h2 : ¬∀ {r : ℝ} {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Sum.uncountable_inl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.uncountable_inl.h2 : ¬∀ {α β : Type}, Uncountable (α ⊕ β) := fun hc_h => absurd (@hc_h (ℕ) (ℕ)) (by
  simp)

-- Sum.uncountable_inr, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.uncountable_inr.h2 : ¬∀ {α β : Type}, Uncountable (α ⊕ β) := fun hc_h => absurd (@hc_h (ℕ) (ℕ)) (by
  simp)

-- Complex.conj_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Complex.conj_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.eq_top_of_forall_nnreal_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eq_top_of_forall_nnreal_le.h1 : ¬∀ {x : ENNReal}, x = ⊤ := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- ENNReal.mulRightOrderIso_toEquiv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mulRightOrderIso_toEquiv.h1 : ¬∀ (a : ENNReal), IsUnit a := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- NNReal.half_lt_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.half_lt_self.h1 : ¬∀ {a : NNReal}, a / 2 < a := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- ENNReal.exists_inv_two_pow_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_inv_two_pow_lt.h1 : ¬∀ {a : ENNReal}, ∃ (n : ℕ), 2⁻¹ ^ n < a := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- ENNReal.dichotomy, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.dichotomy.h1 : ¬∀ (p : ENNReal), p = ⊤ ∨ 1 ≤ p.toReal := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- ENNReal.toNNReal_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Complex.re_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Complex.re_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.ofNat_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofNat_ne_top.h1 : ¬∀ {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.ofNat_eq_coe_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofNat_eq_coe_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Equiv.cast_refl, hypothesis 1: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Equiv.cast_refl.h1.der.{u_1} : ∀ {α : Sort u_1}, α = α := by
  (intros; trivial)
theorem HypCheckProof.Equiv.cast_refl.h1.{u_1} : ∀ {α : Sort u_1}, Equiv.cast HypCheckProof.Equiv.cast_refl.h1.der = Equiv.refl α := by
  intro hc_x0
  exact @Equiv.cast_refl hc_x0 (@HypCheckProof.Equiv.cast_refl.h1.der hc_x0)

-- Fact.out, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fact.out.h1 : ¬∀ {p : Prop}, p := fun hc_h => absurd (@hc_h (False)) (by
  decide +kernel)

-- ENNReal.coe_toNNReal, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.coe_toNNReal.h1 : ¬∀ {a : ENNReal}, ↑a.toNNReal = a := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- iff_mpr_iff_true_intro, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.iff_mpr_iff_true_intro.h1 : ¬∀ {P : Prop}, P := fun hc_h => absurd (@hc_h (False)) (by
  decide +kernel)

-- ENNReal.top_sub, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.top_sub.h1 : ¬∀ {a : ENNReal}, ⊤ - a = ⊤ := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- of_not_not, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.of_not_not.h1 : ¬∀ {a : Prop}, a := fun hc_h => absurd (@hc_h (False)) (by
  decide +kernel)

-- Mathlib.Meta.Positivity.nnreal_coe_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Mathlib.Meta.Positivity.nnreal_coe_pos.h1 : ¬∀ {r : NNReal}, 0 < ↑r := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- eq_false_intro, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.eq_false_intro.h1 : ¬∀ {a : Prop}, a = False := fun hc_h => absurd (@hc_h (True)) (by
  decide +kernel)

-- ENNReal.div_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_zero.h1 : ¬∀ {a : ENNReal}, a / 0 = ⊤ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Finite.nonempty_decidableEq, hypothesis 1: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finite.nonempty_decidableEq.h1.gneg.{u_1} : ∀ (α : Sort u_1), ¬Finite α → Nonempty (DecidableEq α) := by
  (intros; infer_instance)
theorem HypCheckProof.Finite.nonempty_decidableEq.h1.{u_1} : ∀ (α : Sort u_1), Nonempty (DecidableEq α) := by
  intro hc_x0
  exact Classical.byCases (fun hc_h => @Finite.nonempty_decidableEq hc_x0 hc_h) (fun hc_hn => @HypCheckProof.Finite.nonempty_decidableEq.h1.gneg hc_x0 hc_hn)

-- Real.toNNReal_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.toReal_pos_iff_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_pos_iff_ne_top.h1 : ¬∀ (p : ENNReal), 0 < p.toReal ↔ p ≠ ⊤ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- WithBot.instUncountable, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithBot.instUncountable.h1 : ¬∀ {α : Type}, Uncountable (WithBot α) := fun hc_h => absurd (@hc_h (ℕ)) (by
  simp)

-- NNReal.mk_coe, hypothesis 1: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.NNReal.mk_coe.h1.der : ∀ (a : NNReal), 0 ≤ ↑a := by
  (intros; simp; done)
theorem HypCheckProof.NNReal.mk_coe.h1 : ∀ (a : NNReal), NNReal.mk (↑a) (HypCheckProof.NNReal.mk_coe.h1.der a) = a := by
  intro hc_x0
  exact @NNReal.mk_coe hc_x0 (@HypCheckProof.NNReal.mk_coe.h1.der hc_x0)

-- by_contradiction, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.by_contradiction.h1 : ¬∀ {p : Prop}, p := fun hc_h => absurd (@hc_h (False)) (by
  decide +kernel)

-- NNReal.exists_nat_pos_inv_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.exists_nat_pos_inv_lt.h1 : ¬∀ {b : NNReal}, ∃ (n : ℕ), 0 < n ∧ (↑n)⁻¹ < b := fun hc_h => absurd (@hc_h (0)) (by
  simp)

