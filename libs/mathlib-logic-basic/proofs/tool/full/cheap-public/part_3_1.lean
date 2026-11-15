import HCImportsM

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- PartialEquiv.copy_source, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_source.h4 : ¬∀ {α β : Type} (e : PartialEquiv α β) (f : α → β) (g : β → α),
        ↑e.symm = g → ∀ (s : Set α), e.source = s → ∀ (t : Set β), e.target = t → ↑e = f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Inhabited.default) (fun b => if b then 1 else 0 : Bool → ℕ) _ rfl _ rfl _ rfl) (by
  decide +kernel)

-- PartialEquiv.copy_source, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_source.h6 : ¬∀ {α β : Type} (e : PartialEquiv α β) (f : α → β),
        ↑e = f → ∀ (g : β → α) (s : Set α), e.source = s → ∀ (t : Set β), e.target = t → ↑e.symm = g := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Inhabited.default) _ rfl (fun b => if b then 1 else 0 : Bool → ℕ) _ rfl _ rfl) (by
  decide +kernel)

-- PartialEquiv.copy_source, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_source.h8 : Not
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

-- PartialEquiv.copy_source, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_source.h10 : Not
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

-- PartialEquiv.copy_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_eq.h4 : ¬∀ {α β : Type} (e : PartialEquiv α β) (f : α → β) (g : β → α),
        ↑e.symm = g → ∀ (s : Set α), e.source = s → ∀ (t : Set β), e.target = t → ↑e = f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Inhabited.default) (fun b => if b then 1 else 0 : Bool → ℕ) _ rfl _ rfl _ rfl) (by
  decide +kernel)

-- PartialEquiv.copy_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_eq.h6 : ¬∀ {α β : Type} (e : PartialEquiv α β) (f : α → β),
        ↑e = f → ∀ (g : β → α) (s : Set α), e.source = s → ∀ (t : Set β), e.target = t → ↑e.symm = g := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Inhabited.default) _ rfl (fun b => if b then 1 else 0 : Bool → ℕ) _ rfl _ rfl) (by
  decide +kernel)

-- PartialEquiv.copy_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_eq.h8 : Not
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

-- PartialEquiv.copy_eq, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.copy_eq.h10 : Not
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

-- if_ctx_congr, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.if_ctx_congr.h9 : ¬∀ {α : Type} {P Q : Prop} [inst : Decidable P] [inst_1 : Decidable Q] {x y u v : α},
        (Q → x = u) → (¬Q → y = v) → (if P then x else y) = if Q then u else v := fun hc_h => absurd (@hc_h (ℕ) (True) (False) (instDecidableTrue) (instDecidableFalse) (1) (0) (0) (0) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- if_ctx_congr, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.if_ctx_congr.h10 : ¬∀ {α : Type} {P Q : Prop} [inst : Decidable P] [inst_1 : Decidable Q] {x y u v : α},
        (P ↔ Q) → (¬Q → y = v) → (if P then x else y) = if Q then u else v := fun hc_h => absurd (@hc_h (ℕ) (True) (True) (instDecidableTrue) (instDecidableTrue) (0) (0) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- if_ctx_congr, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.if_ctx_congr.h11 : ¬∀ {α : Type} {P Q : Prop} [inst : Decidable P] [inst_1 : Decidable Q] {x y u v : α},
        (P ↔ Q) → (Q → x = u) → (if P then x else y) = if Q then u else v := fun hc_h => absurd (@hc_h (ℕ) (False) (False) (instDecidableFalse) (instDecidableFalse) (0) (0) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- PartialEquiv.coe_mk, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.coe_mk.h6 : ¬∀ {α β : Type} (f : α → β) (g : β → α) (s : Set α) (t : Set β),
        (∀ ⦃x : β⦄, x ∈ t → g x ∈ s) →
          (∀ ⦃x : α⦄, x ∈ s → g (f x) = x) → (∀ ⦃x : β⦄, x ∈ t → f (g x) = x) → ∀ ⦃x : α⦄, x ∈ s → f x ∈ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- Set.Pairwise.of_refl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Pairwise.of_refl.h3 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α}, s.Pairwise r → ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ({n : ℕ | n = 0}) (by
  simp) (0) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- Set.Pairwise.of_refl, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Pairwise.of_refl.h4 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α} [inst : Std.Refl r] ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ({n : ℕ | n % 2 = 0}) _ (2) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- Set.Pairwise.of_refl, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Pairwise.of_refl.h6 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α} [inst : Std.Refl r], s.Pairwise r → ∀ ⦃a b : α⦄, b ∈ s → r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ({n : ℕ | n = 0}) _ (by
  simp) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Set.Pairwise.of_refl, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Pairwise.of_refl.h8 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α} [inst : Std.Refl r], s.Pairwise r → ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) ({n : ℕ | n = 0}) _ (by
  simp) (0) (by
  decide) (1)) (by
  decide +kernel)

-- Set.Infinite.image2_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.image2_left.h7 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {b : β},
        b ∈ t → Set.InjOn (fun (a : α) => f a b) s → (Set.image2 f s t).Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (0) (by
  decide) (by
  simp)) (by
  simp)

-- Archimedean.ratLt'_nonempty, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Archimedean.ratLt'_nonempty.h6 : ¬∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] [inst_3 : One M]
        [inst_4 : ZeroLEOneClass M] [inst_5 : Archimedean M] (x : M), (Archimedean.ratLt' x).Nonempty := fun hc_h => absurd (@hc_h (Unit) (PUnit.addCommGroup) (PUnit.instLinearOrder) (@IsOrderedAddMonoid.mk (Unit) (@AddCommGroup.toAddCommMonoid Unit PUnit.addCommGroup) (@PartialOrder.toPreorder Unit
      (@SemilatticeInf.toPartialOrder Unit
        (@Lattice.toSemilatticeInf Unit
          (@DistribLattice.toLattice Unit (@instDistribLatticeOfLinearOrder Unit PUnit.instLinearOrder))))) (by (try dsimp only);   decide) (by (try dsimp only);   decide)) (PUnit.instOne_mathlib) _ (@Archimedean.mk (Unit) (@AddCommGroup.toAddCommMonoid Unit PUnit.addCommGroup) (@SemilatticeInf.toPartialOrder Unit
      (@Lattice.toSemilatticeInf Unit
        (@DistribLattice.toLattice Unit (@instDistribLatticeOfLinearOrder Unit PUnit.instLinearOrder)))) (by (try dsimp only);   (intros; simp_all; done))) (PUnit.unit)) (by
  nofun)

-- ENNReal.div_eq_div_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_eq_div_iff.h4 : ¬∀ {a b c d : ENNReal}, a ≠ ⊤ → b ≠ 0 → b ≠ ⊤ → (c / b = d / a ↔ a * c = b * d) := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (by
  decide) (by
  simp) (by
  decide)) (by
  simp)

-- ENNReal.div_eq_div_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_eq_div_iff.h6 : ¬∀ {a b c d : ENNReal}, a ≠ 0 → a ≠ ⊤ → b ≠ ⊤ → (c / b = d / a ↔ a * c = b * d) := fun hc_h => absurd (@hc_h (1) (0) (0) (1) (by
  simp) (by
  decide) (by
  decide)) (by
  simp)

-- beq_eq_beq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.beq_eq_beq.h3 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : BEq β] [inst_2 : LawfulBEq β] {a₁ a₂ : α} {b₁ b₂ : β},
        (a₁ == a₂) = (b₁ == b₂) ↔ (a₁ = a₂ ↔ b₁ = b₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (instBEqOfDecidableEq) _ (0) (1) (0) (0)) (by
  decide +kernel)

-- beq_eq_beq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.beq_eq_beq.h5 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : LawfulBEq α] [inst_2 : BEq β] {a₁ a₂ : α} {b₁ b₂ : β},
        (a₁ == a₂) = (b₁ == b₂) ↔ (a₁ = a₂ ↔ b₁ = b₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instBEqOfDecidableEq) _ (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (0) (0) (0) (1)) (by
  decide +kernel)

-- BAll.imp_left, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.BAll.imp_left.h4.inst : ¬(fun (b : Bool) => b = Bool.true) Bool.false := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.BAll.imp_left.h4.prem0 : ∀ (x : Bool), x = Bool.true → (fun (b : Bool) => b = Bool.true) x := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.BAll.imp_left.h4.prem1 : (fun (b : Bool) => b = Bool.false) Bool.false := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.BAll.imp_left.h4 : ¬∀ {α : Type} {r p q : α → Prop}, (∀ (x : α), q x → r x) → ∀ (x : α), p x → r x := fun hc_h => HypCheckProof.BAll.imp_left.h4.inst (@hc_h (Bool) (fun (b : Bool) => b = Bool.true) (fun (b : Bool) => b = Bool.false) (fun (b : Bool) => b = Bool.true) HypCheckProof.BAll.imp_left.h4.prem0 (Bool.false) HypCheckProof.BAll.imp_left.h4.prem1)

-- BAll.imp_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.BAll.imp_left.h5 : ¬∀ {α : Type} {r p q : α → Prop}, (∀ (x : α), p x → q x) → ∀ (x : α), p x → r x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (by
  simp) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- BAll.imp_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.BAll.imp_left.h7 : ¬∀ {α : Type} {r p q : α → Prop}, (∀ (x : α), p x → q x) → (∀ (x : α), q x → r x) → ∀ (x : α), r x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (by
  simp) (by
  simp) (1)) (by
  decide +kernel)

-- ENNReal.iSup_add_iSup_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.iSup_add_iSup_le.h7 : ¬∀ {ι κ : Type} {f : ι → ENNReal} {a : ENNReal} [inst : Nonempty ι] [inst : Nonempty κ] {g : κ → ENNReal},
        iSup f + iSup g ≤ a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => 0) (0) _ _ (fun (a : ℕ) => 1)) (by
  simp)

-- congr_heq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.congr_heq.h7 : ¬∀ {α β γ : Type} {f : α → γ} {g : β → γ} {x : α} {y : β}, x ≍ y → f x = g y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (0) (0) (by
  rfl)) (by
  decide +kernel)

-- congr_heq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.congr_heq.h8 : ¬∀ {α β γ : Type} {f : α → γ} {g : β → γ} {x : α} {y : β}, f ≍ g → f x = g y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (1) (by
  rfl)) (by
  decide +kernel)

-- Function.LeftInverse.comp, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.comp.h7 : ¬∀ {α β γ : Type} {f : α → β} {g : β → α} {h : β → γ} {i : γ → β},
        Function.LeftInverse h i → Function.LeftInverse (h ∘ f) (g ∘ i) := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Bool) (fun n => n % 2 == 0 : ℕ → Bool) (fun b => if b then 1 else 0 : Bool → ℕ) (not : Bool → Bool) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Equiv.extendSubtype_apply_of_not_mem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.extendSubtype_apply_of_not_mem.h8 : ¬∀ {α : Type} {p q : α → Prop} [inst : DecidablePred p] [inst : DecidablePred q] [inst : Finite ↑{x : α | p x}]
        (e : { x : α // p x } ≃ { x : α // q x }) (x : α), ¬p x := fun hc_h => absurd (@hc_h (Bool) (fun b => b = true : Bool → Prop) (fun b => b = true : Bool → Prop) (fun (a : Bool) => instDecidableEqBool a Bool.true) (fun (a : Bool) => instDecidableEqBool a Bool.true) _ ({
      toFun := fun (a : { x : Bool // (fun (b : Bool) => b = Bool.true) x }) =>
        (⟨Bool.true, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Bool // (fun (b : Bool) => b = Bool.true) x }),
      invFun := fun (a : { x : Bool // (fun (b : Bool) => b = Bool.true) x }) =>
        (⟨Bool.true, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Bool // (fun (b : Bool) => b = Bool.true) x }),
      left_inv := of_decide_eq_true (id (Eq.refl Bool.true)), right_inv := of_decide_eq_true (id (Eq.refl Bool.true)) :
      { x : Bool // (fun (b : Bool) => b = Bool.true) x } ≃ { x : Bool // (fun (b : Bool) => b = Bool.true) x } }) (Bool.true)) (by
  decide +kernel)

-- Archimedean.mkRat_mem_ratLt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Archimedean.mkRat_mem_ratLt.h3 : ¬∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : One M] {num : ℤ} {den : ℕ},
        den ≠ 0 → ∀ {x : M}, mkRat num den ∈ Archimedean.ratLt x ↔ num • 1 < den • x := fun hc_h => absurd (@hc_h (Fin 2) (Fin.addCommGroup 2) (Fin.instLinearOrder) ((Fin.instCommMonoid 2).toMulOneClass.toMulOne.toOne) (0) (2) (by
  decide) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Archimedean.mkRat_mem_ratLt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Archimedean.mkRat_mem_ratLt.h7 : ¬∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] [inst_3 : One M]
        {num : ℤ} {den : ℕ} {x : M}, mkRat num den ∈ Archimedean.ratLt x ↔ num • 1 < den • x := fun hc_h => absurd (@hc_h (ℤ) (Int.instAddCommGroup) (Int.instLinearOrder) _ (Int.instRing.toAddGroupWithOne.toOne) (0) (0) (1)) (by
  decide +kernel)

-- rec_heq_of_heq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.rec_heq_of_heq.h7 : ¬∀ {α β : Type} {a b : α} {C : α → Type} {x : C a} {y : β}, x ≍ y → a = b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) (1) (fun (a : ℕ) => ℕ) (0) (0) (by
  rfl)) (by
  decide +kernel)

-- rec_heq_of_heq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.rec_heq_of_heq.h8 : ¬∀ {α β : Type} {a b : α} {C : α → Type} {x : C a} {y : β} (e : a = b), e ▸ x ≍ y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) _ (fun (a : ℕ) => ℕ) (0) (1) rfl) (by
  simp)

-- ExistsUnique.unique, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ExistsUnique.unique.h2 : ¬∀ {α : Type} {p : α → Prop} {y₁ y₂ : α}, p y₁ → p y₂ → y₁ = y₂ := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 = 0 : ℕ → Prop) (0) (2) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- ExistsUnique.unique, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ExistsUnique.unique.h5 : ¬∀ {α : Type} {p : α → Prop}, (∃! x : α, p x) → ∀ {y₁ y₂ : α}, p y₂ → y₁ = y₂ := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (by
  simp) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- ExistsUnique.unique, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ExistsUnique.unique.h6 : ¬∀ {α : Type} {p : α → Prop}, (∃! x : α, p x) → ∀ {y₁ y₂ : α}, p y₁ → y₁ = y₂ := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (by
  simp) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Equiv.Perm.exists_extending_pair, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Perm.exists_extending_pair.h5 : ¬∀ {α β : Type} [inst : Finite α] (f g : α → β), Function.Injective g → ∃ (σ : Equiv.Perm β), ∀ (a : α), σ (f a) = g a := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (fun _ => true : Bool → Bool) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Equiv.Perm.exists_extending_pair, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Perm.exists_extending_pair.h6 : ¬∀ {α β : Type} [inst : Finite α] (f g : α → β), Function.Injective f → ∃ (σ : Equiv.Perm β), ∀ (a : α), σ (f a) = g a := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (not : Bool → Bool) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Relation.map_equivalence, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.map_equivalence.h5 : ¬∀ {α β : Type} {r : α → α → Prop},
        Equivalence r → ∀ (f : α → β), (∀ (x y : α), f x = f y → r x y) → Equivalence (Relation.Map r f f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ _ => True : Bool → Bool → Prop) ((@Equivalence.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide) (by (try dsimp only);   decide) (by (try dsimp only);   decide))) (fun _ => true : Bool → Bool) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  nofun)

-- NNReal.exists_lt_of_strictMono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.exists_lt_of_strictMono.h4 : ¬∀ {Γ₀ : Type} [inst : LinearOrderedCommGroupWithZero Γ₀] [h : Nontrivial Γ₀ˣ] {f : Γ₀ →*₀ NNReal} {r : NNReal},
        0 < r → ∃ (d : Γ₀ˣ), f ↑d < r := fun hc_h => absurd (@hc_h (ℚ≥0) (NNRat.instLinearOrderedCommGroupWithZero) _ (1) (1) (by
  simp)) (by
  simp)

-- Function.sometimes_spec, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Function.sometimes_spec.h2.der.{u_1} : ∀ {p : Prop} {α : Sort u_1} (P : α → Prop) (f : p → α) (a : p), P (f a) → Nonempty α := by
  (intros; solve_by_elim)
theorem HypCheckProof.Function.sometimes_spec.h2.{u_1} : ∀ {p : Prop} {α : Sort u_1} (P : α → Prop) (f : p → α) (a : p) (h : P (f a)),
      P (@Function.sometimes p α (@HypCheckProof.Function.sometimes_spec.h2.der p α P f a h) f) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Function.sometimes_spec hc_x0 hc_x1 (@HypCheckProof.Function.sometimes_spec.h2.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x2 hc_x3 hc_x4 hc_x5

-- Function.sometimes_spec, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.sometimes_spec.h5 : ¬∀ {p : Prop} {α : Type} [inst : Nonempty α] (P : α → Prop) (f : p → α), p := fun hc_h => absurd (@hc_h (False) (ℕ) _ (fun n => n = 0 : ℕ → Prop) (fun (a : False) => 0)) (by
  decide +kernel)

-- Function.sometimes_spec, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.sometimes_spec.h6 : ¬∀ {p : Prop} {α : Type} [inst : Nonempty α] (P : α → Prop) (f : p → α), p → P (Function.sometimes f) := fun hc_h => absurd (@hc_h (True) (ℕ) _ (fun _ => False : ℕ → Prop) (fun (a : True) => 0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- PEquiv.inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PEquiv.inj.h6 : ¬∀ {α β : Type} (f : α ≃. β) {a₁ a₂ : α} {b : β}, b ∈ f a₂ → a₁ = a₂ := fun hc_h => absurd (@hc_h (Bool) (Bool) ({ toFun := Option.some, invFun := Option.some, inv := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ≃. Bool }) (Bool.true) (Bool.false) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- PEquiv.inj, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PEquiv.inj.h7 : ¬∀ {α β : Type} (f : α ≃. β) {a₁ a₂ : α} {b : β}, b ∈ f a₁ → a₁ = a₂ := fun hc_h => absurd (@hc_h (Bool) (Bool) ({ toFun := Option.some, invFun := Option.some, inv := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ≃. Bool }) (Bool.false) (Bool.true) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- PartialEquiv.IsImage.apply_mem_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.IsImage.apply_mem_iff.h6 : Not
      (∀ {α β : Type} {e : PartialEquiv α β} {s : Set α} {t : Set β} {x : α},
        @Membership.mem α (Set α) (@Set.instMembership α) (@PartialEquiv.source α β e) x →
          Iff (@Membership.mem β (Set β) (@Set.instMembership β) t (@PartialEquiv.toFun α β e x))
            (@Membership.mem α (Set α) (@Set.instMembership α) s x)) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
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
          (@Eq.refl Bool Bool.true)))) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- ENNReal.mul_lt_mul_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_lt_mul_left.h3 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → b < c → b * a < c * a := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide) (by
  simp)) (by
  simp)

-- ENNReal.mul_lt_mul_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_lt_mul_left.h5 : ¬∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → b * a < c * a := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  simp) (by
  decide)) (by
  simp)

-- ENNReal.exists_lt_add_of_lt_add, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_lt_add_of_lt_add.h4 : ¬∀ {x y z : ENNReal}, x < y + z → z ≠ 0 → ∃ y' < y, ∃ z' < z, x < y' + z' := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  simp) (by
  simp)) (by
  simp)

-- ENNReal.exists_lt_add_of_lt_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_lt_add_of_lt_add.h5 : ¬∀ {x y z : ENNReal}, x < y + z → y ≠ 0 → ∃ y' < y, ∃ z' < z, x < y' + z' := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  simp) (by
  simp)) (by
  simp)

-- ENNReal.toReal_le_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_le_add.h3 : ¬∀ {a b c : ENNReal}, b ≠ ⊤ → c ≠ ⊤ → a.toReal ≤ b.toReal + c.toReal := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide) (by
  decide)) (by
  simp)

-- Function.Injective.of_comp_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.of_comp_right.h5 : ¬∀ {α β γ : Type} {f : α → β} {g : γ → α}, Function.Surjective g → Function.Injective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool) (fun _ => 0 : Bool → ℕ) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Function.Bijective.comp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.comp.h5 : ¬∀ {α β φ : Type} {g : β → φ} {f : α → β}, Function.Bijective f → Function.Bijective (g ∘ f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (fun _ => 0 : Bool → ℕ) (not : Bool → Bool) (by
  decide)) (by
  nofun)

-- Function.Bijective.comp, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.comp.h6 : ¬∀ {α β φ : Type} {g : β → φ} {f : α → β}, Function.Bijective g → Function.Bijective (g ∘ f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool) (not : Bool → Bool) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Function.Embedding.mk_trans_mk, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.mk_trans_mk.h5 : ¬∀ {α β γ : Type} (f : α → β) (g : β → γ), Function.Injective g → Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) (fun _ => true : ℕ → Bool) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  simp)

-- Function.Embedding.mk_trans_mk, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.mk_trans_mk.h6 : ¬∀ {α β γ : Type} (f : α → β) (g : β → γ), Function.Injective f → Function.Injective g := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  decide)) (by
  simp)

-- sign_eq_sign_or_eq_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.sign_eq_sign_or_eq_neg.h5 : ¬∀ {α : Type} [inst : Zero α] [inst_1 : LinearOrder α] {a b : α},
        b ≠ 0 → SignType.sign a = SignType.sign b ∨ SignType.sign a = -SignType.sign b := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instLinearOrder) (0) (1) (by
  decide)) (by
  decide +kernel)

-- sign_eq_sign_or_eq_neg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.sign_eq_sign_or_eq_neg.h6 : ¬∀ {α : Type} [inst : Zero α] [inst_1 : LinearOrder α] {a b : α},
        a ≠ 0 → SignType.sign a = SignType.sign b ∨ SignType.sign a = -SignType.sign b := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instLinearOrder) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Equiv.Set.sumDiffSubset_symm_apply_of_notMem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.sumDiffSubset_symm_apply_of_notMem.h6 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → ∀ [inst : DecidablePred fun (x : α) => x ∈ s] {x : ↑t}, ↑x ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl) (fun (a : ℕ) => Set.decidableOfPred a fun (n : ℕ) => n = 0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} }))) (by
  decide +kernel)

-- Function.iterate_cancel_of_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.iterate_cancel_of_add.h5 : ¬∀ {α : Type} {f : α → α} {m n : ℕ} {a : α}, f^[m + n] a = f^[n] a → f^[m] a = a := fun hc_h => absurd (@hc_h (ℕ) (fun _ => 0 : ℕ → ℕ) (1) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Function.iterate_cancel_of_add, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.iterate_cancel_of_add.h6 : ¬∀ {α : Type} {f : α → α} {m : ℕ} {n : ℕ} {a : α}, Function.Injective f → f^[m] a = a := fun hc_h => absurd (@hc_h (Bool) (not : Bool → Bool) (1) (0) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Function.Commute.iterate_eq_of_map_eq, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Function.Commute.iterate_eq_of_map_eq.h3.inst : ¬Bool.not^[2] Bool.false = (fun (x : Bool) => Bool.true)^[2] Bool.false := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Function.Commute.iterate_eq_of_map_eq.h3.prem0 : (!Bool.false) = (fun (x : Bool) => Bool.true) Bool.false := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Function.Commute.iterate_eq_of_map_eq.h3 : ¬∀ {α : Type} {f g : α → α} (n : ℕ) {x : α}, f x = g x → f^[n] x = g^[n] x := fun hc_h => HypCheckProof.Function.Commute.iterate_eq_of_map_eq.h3.inst (@hc_h (Bool) (Bool.not) (fun (x : Bool) => Bool.true) (2) (Bool.false) HypCheckProof.Function.Commute.iterate_eq_of_map_eq.h3.prem0)

-- Equiv.Set.image_symm_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.image_symm_apply.h4 : ¬∀ {α β : Type} (f : α → β) (s : Set α) (x : α), f x ∈ f '' s → Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) (0) (by
  simp)) (by
  simp)

-- Equiv.Set.image_symm_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.image_symm_apply.h6 : ¬∀ {α β : Type} (f : α → β) (s : Set α), Function.Injective f → ∀ (x : α), f x ∈ f '' s := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) ({b : Bool | b = Bool.true}) (by
  decide) (Bool.false)) (by
  simp)

-- Equiv.Set.union_apply_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.union_apply_left.h4 : ¬∀ {α : Type} {s t : Set α} [inst : DecidablePred fun (x : α) => x ∈ s] {a : ↑(s ∪ t)}, ↑a ∈ s → Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun (a : ℕ) => Set.decidableOfPred a fun (n : ℕ) => n = 0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} ∪ {n : ℕ | n = 0} })) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- SetRel.IsCover.anti, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.IsCover.anti.h6 : ¬∀ {X : Type} {U : SetRel X X} {s t N : Set X}, s ⊆ t → U.IsCover s N := fun hc_h => absurd (@hc_h (ℕ) (∅) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  rfl)) (by
  simp)

-- Relation.ReflTransGen.head, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.ReflTransGen.head.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, Relation.ReflTransGen r b c → Relation.ReflTransGen r a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0) (0) (by
  rfl)) (by
  nofun)

-- Relation.ReflTransGen.head, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.ReflTransGen.head.h6.inst : ¬Relation.ReflTransGen (fun (a b : ℕ) => a < b) 1 0 := by
  nofun
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.ReflTransGen.head.h6.prem0 : (fun (a b : ℕ) => a < b) 1 2 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Relation.ReflTransGen.head.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, r a b → Relation.ReflTransGen r a c := fun hc_h => HypCheckProof.Relation.ReflTransGen.head.h6.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (1) (2) (0) HypCheckProof.Relation.ReflTransGen.head.h6.prem0)

-- Equiv.Set.union_apply_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.union_apply_right.h4 : ¬∀ {α : Type} {s t : Set α} [inst : DecidablePred fun (x : α) => x ∈ s] {a : ↑(s ∪ t)}, ↑a ∈ t → Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun (a : ℕ) => Set.decidableOfPred a fun (n : ℕ) => n = 0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} ∪ {n : ℕ | n = 0} })) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Function.Bijective.of_comp_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.of_comp_left.h5 : ¬∀ {α β γ : Type} {f : α → β} {g : γ → α}, Function.Injective f → Function.Bijective g := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Relation.TransGen.trans_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.TransGen.trans_left.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, Relation.ReflTransGen r b c → Relation.TransGen r a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (0) (by
  rfl)) (by
  nofun)

-- Relation.TransGen.trans_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.TransGen.trans_left.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, Relation.TransGen r a b → Relation.TransGen r a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (1) (0) (by
  grind)) (by
  nofun)

-- Set.BijOn.toPartialEquiv_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.toPartialEquiv_apply.h6 : ¬∀ {α β : Type} [inst : Nonempty α] (f : α → β) (s : Set α) (t : Set β), Set.BijOn f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- PartialEquiv.symm_apply_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.symm_apply_eq.h5 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) {x : α} {y : β},
        @Membership.mem β (Set β) (@Set.instMembership β) (@PartialEquiv.target α β e) y →
          Iff (@Eq α (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e) y) x) (@Eq β y (@PartialEquiv.toFun α β e x))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool (fun (x : Bool) => Bool.true) (fun (x : Bool) => Bool.true)
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
          (@Eq.refl Bool Bool.true)))) (Bool.false) (Bool.true) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- PartialEquiv.symm_apply_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.symm_apply_eq.h6 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) {x : α} {y : β},
        @Membership.mem α (Set α) (@Set.instMembership α) (@PartialEquiv.source α β e) x →
          Iff (@Eq α (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e) y) x) (@Eq β y (@PartialEquiv.toFun α β e x))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not (fun (x : Bool) => Bool.true)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
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
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
              (instDecidableEqBool Bool.true Bool.true))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
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
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool Bool.true.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool Bool.true.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool Bool.true.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            instDecidableEqBool Bool.true.not a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool Bool.true.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool Bool.true.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool Bool.true.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  instDecidableEqBool Bool.true.not a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (Bool.true) (Bool.true) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- CompTriple.comp_inv, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CompTriple.comp_inv.h4 : ¬∀ {M N : Type} {φ : M → N} {ψ : N → M} {χ : M → M} [inst : CompTriple.IsId χ], CompTriple φ ψ χ := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (fun b => b : Bool → Bool) (@CompTriple.IsId.mk (Bool) (fun (b : Bool) => b) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd (hc_c.comp_eq)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- CompTriple.comp_inv, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CompTriple.comp_inv.h6 : ¬∀ {M N : Type} {φ : M → N} {ψ : N → M}, Function.RightInverse φ ψ → ∀ {χ : M → M}, CompTriple φ ψ χ := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool) (not : Bool → Bool) (by
  decide) (not : Bool → Bool)) (by
  exact fun hc_c =>
    absurd (hc_c.comp_eq)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- heq_of_eq_cast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.heq_of_eq_cast.h5 : ¬∀ {α β : Type} {a : α} {b : β}, β = α → a ≍ b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Function.Injective.exists_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.exists_ne.h4 : ¬∀ {α β : Type} [inst : Nontrivial α] {f : α → β} (y : β), ∃ (x : α), f x ≠ y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ (fun _ => 0 : ℕ → ℕ) (0)) (by
  simp)

-- Eq.trans_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Eq.trans_ne.h4 : ¬∀ {α : Type} {a b c : α}, b ≠ c → a ≠ c := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Eq.trans_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Eq.trans_ne.h5 : ¬∀ {α : Type} {a b c : α}, a = b → a ≠ c := fun hc_h => absurd (@hc_h (ℕ) _ (0) (0) rfl) (by
  decide +kernel)

-- Function.RightInverse.leftInverse_of_surjective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.RightInverse.leftInverse_of_surjective.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α}, Function.Surjective f → Function.LeftInverse f g := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Iff.and, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.and.h4 : ¬∀ {a c b d : Prop}, (b ↔ d) → (a ∧ b ↔ c ∧ d) := fun hc_h => absurd (@hc_h (True) (False) (True) (True) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Iff.and, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.and.h5 : ¬∀ {a c b d : Prop}, (a ↔ c) → (a ∧ b ↔ c ∧ d) := fun hc_h => absurd (@hc_h (True) (True) (True) (False) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Set.Infinite.prod_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.prod_right.h4 : ¬∀ {α β : Type} {s : Set α} {t : Set β}, s.Nonempty → (s ×ˢ t).Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Function.Injective.isStrictTotalOrder_onFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.isStrictTotalOrder_onFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) {f : α → β} [inst : IsStrictTotalOrder β r],
        IsStrictTotalOrder α (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun _ => 0 : ℕ → ℕ) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.toTrichotomous.trichotomous (0 : ℕ) (1 : ℕ)
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

-- Function.Injective.isStrictTotalOrder_onFun, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.isStrictTotalOrder_onFun.h5 : ¬∀ {α β : Type} (r : β → β → Prop) {f : α → β}, Function.Injective f → IsStrictTotalOrder α (Function.onFun r f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsStrictOrder.toIrrefl.irrefl (Bool.false : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.Injective.isLinearOrder_onFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.isLinearOrder_onFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) {f : α → β} [inst : IsLinearOrder β r], IsLinearOrder α (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun n => n / 2 : ℕ → ℕ) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsPartialOrder.toAntisymm.antisymm (0 : ℕ) (1 : ℕ)
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

-- Function.Injective.isLinearOrder_onFun, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.isLinearOrder_onFun.h5 : ¬∀ {α β : Type} (r : β → β → Prop) {f : α → β}, Function.Injective f → IsLinearOrder α (Function.onFun r f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPartialOrder.toIsPreorder.toRefl.refl (Bool.false : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.Infinite.prod_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.prod_left.h4 : ¬∀ {α β : Type} {s : Set α} {t : Set β}, t.Nonempty → (s ×ˢ t).Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- SetRel.IsCover.nonempty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.IsCover.nonempty.h4 : ¬∀ {X : Type} {U : SetRel X X} {s N : Set X}, s.Nonempty → N.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (∅) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- SetRel.IsCover.nonempty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.IsCover.nonempty.h5 : ¬∀ {X : Type} {U : SetRel X X} {s N : Set X}, U.IsCover s N → N.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (∅) ({x : ℕ | False}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- ENNReal.add_lt_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_lt_add.h5 : ¬∀ {a b c d : ENNReal}, a < c → a + b < c + d := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (by
  simp)) (by
  simp)

-- imp_congr_ctx_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.imp_congr_ctx_eq.h4 : ¬∀ {a b c d : Prop}, (c → b = d) → (a → b) = (c → d) := fun hc_h => absurd (@hc_h (True) (False) (False) (True) (by
  decide)) (by
  decide +kernel)

-- imp_congr_ctx_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.imp_congr_ctx_eq.h5 : ¬∀ {a b c d : Prop}, a = c → (a → b) = (c → d) := fun hc_h => absurd (@hc_h _ (True) (True) (False) rfl) (by
  decide +kernel)

-- Function.Injective.antisymm_onFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.antisymm_onFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) {f : α → β} [inst : Std.Antisymm r], Std.Antisymm (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun _ => 0 : ℕ → ℕ) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.antisymm (0 : ℕ) (1 : ℕ)
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

-- Function.Injective.antisymm_onFun, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.antisymm_onFun.h5 : ¬∀ {α β : Type} (r : β → β → Prop) {f : α → β}, Function.Injective f → Std.Antisymm (Function.onFun r f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ _ => True : Bool → Bool → Prop) (not : Bool → Bool) (by
  decide)) (by
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

-- ne_of_ne_of_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ne_of_ne_of_eq.h4 : ¬∀ {α : Type} {a b c : α}, b = c → a ≠ c := fun hc_h => absurd (@hc_h (ℕ) (0) _ (0) rfl) (by
  decide +kernel)

-- ne_of_ne_of_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ne_of_ne_of_eq.h5 : ¬∀ {α : Type} {a b c : α}, a ≠ b → a ≠ c := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- NNReal.le_iInf_mul_iInf, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.le_iInf_mul_iInf.h5 : ¬∀ {ι : Type} [inst : Nonempty ι] {a : NNReal} {g h : ι → NNReal}, a ≤ iInf g * iInf h := fun hc_h => absurd (@hc_h (ℕ) _ (1) (fun (a : ℕ) => 0) (fun (a : ℕ) => 0)) (by
  simp)

-- ENNReal.HolderTriple.unique, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.unique.h3 : ¬∀ (p q r r' : ENNReal) [hr' : p.HolderTriple q r'], r = r' := fun hc_h => absurd (@hc_h (0) (0) (1) (0) _) (by
  simp)

-- ENNReal.HolderTriple.unique, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.unique.h5 : ¬∀ (p q r : ENNReal) [inst : p.HolderTriple q r] (r' : ENNReal), r = r' := fun hc_h => absurd (@hc_h (0) (0) (0) _ (1)) (by
  simp)

-- ite_ite_comm, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ite_ite_comm.h8 : ¬∀ {α : Type} (P Q : Prop) [inst : Decidable P] (a b : α) {c : α} [inst_1 : Decidable Q],
        (if P then a else if Q then b else c) = if Q then b else if P then a else c := fun hc_h => absurd (@hc_h (ℕ) (True) (True) (instDecidableTrue) (0) (1) (0) (instDecidableTrue)) (by
  decide +kernel)

-- dite_dite_comm, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.dite_dite_comm.h8 : ¬∀ {α : Type} (P Q : Prop) [inst : Decidable P] {A : P → α} [inst_1 : Decidable Q] {B : Q → α} {C : ¬P → ¬Q → α},
        (if p : P then A p else if q : Q then B q else C p q) = if q : Q then B q else if p : P then A p else C p q := fun hc_h => absurd (@hc_h (ℕ) (True) (True) (instDecidableTrue) (fun (a : True) => 0) (instDecidableTrue) (fun (a : True) => 1) (fun (a a_1 : ¬True) => 0)) (by
  decide +kernel)

-- Function.Injective2.eq_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective2.eq_iff.h4 : ¬∀ {α β γ : Type} {f : α → β → γ} {a₁ a₂ : α} {b₁ b₂ : β}, f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) (0) (0) (1)) (by
  decide +kernel)

-- ENNReal.sub_lt_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_lt_self.h2 : ¬∀ {a b : ENNReal}, a ≠ 0 → b ≠ 0 → a - b < a := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- ENNReal.sub_lt_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_lt_self.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → b ≠ 0 → a - b < a := fun hc_h => absurd (@hc_h (0) (1) (by
  decide) (by
  simp)) (by
  simp)

-- ENNReal.sub_lt_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_lt_self.h4 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → a ≠ 0 → a - b < a := fun hc_h => absurd (@hc_h (1) (0) (by
  decide) (by
  simp)) (by
  simp)

-- ENNReal.le_of_add_le_add_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_of_add_le_add_right.h4 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → b ≤ c := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

-- Equiv.apply_swap_eq_self, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.apply_swap_eq_self.h6 : ¬∀ {α β : Type} [inst : DecidableEq α] {v : α → β} {i j : α} (k : α), v ((Equiv.swap i j) k) = v k := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (fun n => n + 1 : ℕ → ℕ) (0) (1) (0)) (by
  decide +kernel)

-- ENNReal.lt_div_iff_mul_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.lt_div_iff_mul_lt.h3 : ¬∀ {a b c : ENNReal}, b ≠ ⊤ ∨ c ≠ 0 → (c < a / b ↔ c * b < a) := fun hc_h => absurd (@hc_h (1) (0) (⊤) (by
  decide)) (by
  simp)

-- Equiv.subtypePreimage_symm_apply_coe_neg, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypePreimage_symm_apply_coe_neg.h7 : ¬∀ {α β : Type} (p : α → Prop) [inst : DecidablePred p] (x₀ : { a : α // p a } → β) (x : { a : α // ¬p a } → β) (a : α),
        ¬p a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (fun (a : { a : ℕ // (fun (n : ℕ) => n = 0) a }) => 0) (fun (a : { a : ℕ // ¬(fun (n : ℕ) => n = 0) a }) => 0) (0)) (by
  decide +kernel)

-- ENNReal.mul_le_iff_le_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_le_iff_le_inv.h3 : ¬∀ {a b r : ENNReal}, r ≠ ⊤ → (r * a ≤ b ↔ a ≤ r⁻¹ * b) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  simp)

-- exists_mem_of_exists, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.exists_mem_of_exists.h3 : ¬∀ {α : Type} {p q : α → Prop}, (∃ (x : α), q x) → ∃ (x : α) (_ : p x), q x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (by
  simp)) (by
  simp)

-- exists_mem_of_exists, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.exists_mem_of_exists.h4 : ¬∀ {α : Type} {p q : α → Prop}, (∀ (x : α), p x) → ∃ (x : α) (_ : p x), q x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => True : ℕ → Prop) (fun _ => False : ℕ → Prop) (by
  simp)) (by
  simp)

-- ENNReal.zpow_sub, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.zpow_sub.h1 : ¬∀ {x : ENNReal}, x ≠ ⊤ → ∀ (m n : ℤ), x ^ (m - n) = x ^ m * (x ^ n)⁻¹ := fun hc_h => absurd (@hc_h (0) (by
  decide) (1) (1)) (by
  simp)

-- ENNReal.HolderTriple.inv_sub_inv_eq_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.inv_sub_inv_eq_inv.h3 : ¬∀ (p q : ENNReal) {r : ENNReal}, r ≠ 0 → r⁻¹ - q⁻¹ = p⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  simp)) (by
  simp)

-- ENNReal.HolderTriple.inv_sub_inv_eq_inv, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.inv_sub_inv_eq_inv.h4 : ¬∀ (p q : ENNReal) {r : ENNReal} [inst : p.HolderTriple q r], r⁻¹ - q⁻¹ = p⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (0) _) (by
  simp)

-- ExistsUnique.elim, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ExistsUnique.elim.h3 : ¬∀ {α : Type} {p : α → Prop} {b : Prop}, (∀ (x : α), p x → (∀ (y : α), p y → y = x) → b) → b := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (False) (by
  simp)) (by
  decide +kernel)

-- ExistsUnique.elim, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ExistsUnique.elim.h4 : ¬∀ {α : Type} {p : α → Prop} {b : Prop}, (∃! x : α, p x) → b := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (False) (by
  simp)) (by
  decide +kernel)

-- ENNReal.HolderTriple.inv_sub_inv_eq_inv', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.inv_sub_inv_eq_inv'.h3 : ¬∀ (p q r : ENNReal), q ≠ 0 → r⁻¹ - q⁻¹ = p⁻¹ := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  simp)) (by
  simp)

-- ENNReal.HolderTriple.inv_sub_inv_eq_inv', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.inv_sub_inv_eq_inv'.h4 : ¬∀ (p q r : ENNReal) [inst : p.HolderTriple q r], r⁻¹ - q⁻¹ = p⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (0) _) (by
  simp)

-- ENNReal.HolderConjugate.unique, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.unique.h2 : ¬∀ (p q q' : ENNReal) [hq' : p.HolderConjugate q'], q = q' := fun hc_h => absurd (@hc_h (2) (0) (2) _) (by
  simp)

-- ENNReal.HolderConjugate.unique, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.unique.h4 : ¬∀ (p q : ENNReal) [inst : p.HolderConjugate q] (q' : ENNReal), q = q' := fun hc_h => absurd (@hc_h (2) (2) _ (0)) (by
  simp)

-- finSuccEquiv'_ne_last_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finSuccEquiv'_ne_last_apply.h3 : ¬∀ {n : ℕ} {i j : Fin (n + 1)}, j ≠ i → i ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- finSuccEquiv'_ne_last_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finSuccEquiv'_ne_last_apply.h4 : ¬∀ {n : ℕ} {i j : Fin (n + 1)} (hi : i ≠ Fin.last n),
        (finSuccEquiv' i) j = Option.some ((i.castLT (Fin.val_lt_last hi)).predAbove j) := fun hc_h => absurd (fun hc_k0 => @hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) hc_k0) (by
  decide +kernel)

-- Function.Semiconj₂.eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Semiconj₂.eq.h5 : ¬∀ {α β : Type} {f : α → β} {ga : α → α → α} {gb : β → β → β} (x y : α), f (ga x y) = gb (f x) (f y) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) (0)) (by
  decide +kernel)

-- SetRel.isRefl_mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.isRefl_mono.h3 : ¬∀ {α : Type} {R₁ R₂ : SetRel α α}, R₁ ⊆ R₂ → R₂.IsRefl := fun hc_h => absurd (@hc_h (ℕ) (∅) (∅) (by
  rfl)) (by
  exact fun hc_c =>
    absurd (hc_c.refl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.update_left_inj, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.update_left_inj.h7 : ¬∀ {α : Type} [inst : DecidableEq α] {ι : Type} {f : α → ι} {i j : α} {a : ι},
        Function.update f i a = Function.update f j a ↔ i = j := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (ℕ) (fun _ => 0 : ℕ → ℕ) (0) (1) (0)) (by
  simp)

-- Equiv.Perm.viaFintypeEmbedding_apply_notMem_range, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Perm.viaFintypeEmbedding_apply_notMem_range.h7 : Not
      (∀ {α β : Type} [inst : Fintype α] [inst_1 : DecidableEq β] (e : Equiv.Perm α) (f : Function.Embedding α β) {b : β},
        @Eq β
          (@DFunLike.coe (Equiv.Perm β) β (fun (x : β) => β)
            (@EquivLike.toFunLike (Equiv.Perm β) β β (@Equiv.instEquivLike β β))
            (@Equiv.Perm.viaFintypeEmbedding α β inst inst_1 e f) b)
          b) := fun hc_h => absurd (@hc_h (Bool) (Nat) (Bool.fintype) (instDecidableEqNat) (@Equiv.mk Bool Bool Bool.not Bool.not
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
          (@Eq.refl Bool Bool.true)))) (@Function.Embedding.mk Bool Nat
      (fun (b : Bool) =>
        @ite Nat (@Eq Bool b Bool.true) (instDecidableEqBool b Bool.true)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Function.Injective Bool Nat fun (b : Bool) =>
          @ite Nat (@Eq Bool b Bool.true) (instDecidableEqBool b Bool.true)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Fintype.decidableInjectiveFintype Bool Nat instDecidableEqNat Bool.fintype fun (b : Bool) =>
          @ite Nat (@Eq Bool b Bool.true) (instDecidableEqBool b Bool.true)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Function.Injective Bool Nat fun (b : Bool) =>
                @ite Nat (@Eq Bool b Bool.true) (instDecidableEqBool b Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@Fintype.decidableInjectiveFintype Bool Nat instDecidableEqNat Bool.fintype fun (b : Bool) =>
                @ite Nat (@Eq Bool b Bool.true) (instDecidableEqBool b Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Function.Injective.uncountable, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.uncountable.h2 : ¬∀ {α β : Type} {f : α → β}, Function.Injective f → Uncountable β := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  simp)

-- PEquiv.single_apply_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PEquiv.single_apply_of_ne.h6 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst_1 : DecidableEq β] {a₁ a₂ : α} (b : β),
        (PEquiv.single a₁ b) a₂ = Option.none := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (0) (0) (0)) (by
  decide +kernel)

-- not_injective_uncountable_countable, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_injective_uncountable_countable.h2 : ¬∀ {α β : Type} [inst : Countable β] (f : α → β), ¬Function.Injective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) _ (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  decide +kernel)

-- Function.sometimes_eq, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Function.sometimes_eq.h2.der.{u_1} : ∀ {p : Prop} {α : Sort u_1} (f : p → α), p → Nonempty α := by
  (intros; solve_by_elim)
theorem HypCheckProof.Function.sometimes_eq.h2.{u_1} : ∀ {p : Prop} {α : Sort u_1} (f : p → α) (a : p),
      @Eq α (@Function.sometimes p α (@HypCheckProof.Function.sometimes_eq.h2.der p α f a) f) (f a) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Function.sometimes_eq hc_x0 hc_x1 (@HypCheckProof.Function.sometimes_eq.h2.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x2 hc_x3

-- Function.sometimes_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.sometimes_eq.h4 : ¬∀ {p : Prop} {α : Type} [inst : Nonempty α] (f : p → α), p := fun hc_h => absurd (@hc_h (False) (ℕ) _ (fun (a : False) => 0)) (by
  decide +kernel)

-- Not.decidable_imp_symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Not.decidable_imp_symm.h3 : ¬∀ {a b : Prop} [inst : Decidable a], ¬b → a := fun hc_h => absurd (@hc_h (False) (False) (instDecidableFalse) (by
  decide)) (by
  decide +kernel)

-- Not.decidable_imp_symm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Not.decidable_imp_symm.h4 : ¬∀ {a b : Prop} [inst : Decidable a], (¬a → b) → a := fun hc_h => absurd (@hc_h (False) (True) (instDecidableFalse) (by
  decide)) (by
  decide +kernel)

-- congr_fun_congr_arg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.congr_fun_congr_arg.h6 : ¬∀ {α β γ : Type} (f : α → β → γ) {a a' : α} (b : β), a = a' := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) (1) (0)) (by
  decide +kernel)

-- Function.Surjective.isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.isEmpty.h2 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective f → IsEmpty β := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.false (Bool.false : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.Injective.subsingleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.subsingleton.h3 : ¬∀ {α β : Type} {f : α → β} [inst : Subsingleton β], Subsingleton α := fun hc_h => absurd (@hc_h (ℕ) (Unit) (fun (a : ℕ) => PUnit.unit) (@Subsingleton.intro (Unit) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.Injective.subsingleton, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.subsingleton.h4 : ¬∀ {α β : Type} {f : α → β}, Function.Injective f → Subsingleton α := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.Surjective.subsingleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.subsingleton.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective f → Subsingleton β := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.Surjective.subsingleton, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.subsingleton.h4 : ¬∀ {α β : Type} {f : α → β} [inst : Subsingleton α], Subsingleton β := fun hc_h => absurd (@hc_h (Unit) (ℕ) (fun (a : Unit) => 0) (@Subsingleton.intro (Unit) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.IsConst.exists_eq_const, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.IsConst.exists_eq_const.h4 : ¬∀ {α β : Type} [inst : Nonempty β] {f : α → β}, ∃ (b : β), f = Function.const α b := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (not : Bool → Bool)) (by
  decide +kernel)

-- NNReal.pow_antitone_exp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.pow_antitone_exp.h3 : ¬∀ {a : NNReal} (m n : ℕ), a ≤ 1 → a ^ n ≤ a ^ m := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  simp)) (by
  simp)

-- NNReal.pow_antitone_exp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.pow_antitone_exp.h4 : ¬∀ {a : NNReal} (m n : ℕ), m ≤ n → a ^ n ≤ a ^ m := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.le_of_add_le_add_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_of_add_le_add_left.h4 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → b ≤ c := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

-- TwoPointing.ext, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.TwoPointing.ext.h3 : ¬∀ {α : Type} {x y : TwoPointing α}, x.toProd.2 = y.toProd.2 → x = y := fun hc_h => absurd (@hc_h (ℕ) ({ fst := 1, snd := 0, fst_ne_snd := of_decide_eq_true (id (Eq.refl Bool.true)) : TwoPointing ℕ }) ({ fst := 2, snd := 0, fst_ne_snd := of_decide_eq_true (id (Eq.refl Bool.true)) : TwoPointing ℕ }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- TwoPointing.ext, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.TwoPointing.ext.h4 : ¬∀ {α : Type} {x y : TwoPointing α}, x.toProd.1 = y.toProd.1 → x = y := fun hc_h => absurd (@hc_h (ℕ) ({ fst := 0, snd := 1, fst_ne_snd := of_decide_eq_true (id (Eq.refl Bool.true)) : TwoPointing ℕ }) ({ fst := 0, snd := 2, fst_ne_snd := of_decide_eq_true (id (Eq.refl Bool.true)) : TwoPointing ℕ }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- ENNReal.sub_eq_of_eq_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_eq_of_eq_add.h3 : ¬∀ {a b c : ENNReal}, a = c + b → a - b = c := fun hc_h => absurd (@hc_h _ (⊤) (1) rfl) (by
  simp)

-- ENNReal.sub_eq_of_eq_add, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_eq_of_eq_add.h4 : ¬∀ {a b c : ENNReal}, b ≠ ⊤ → a - b = c := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.sub_eq_of_eq_add_rev', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_eq_of_eq_add_rev'.h3 : ¬∀ {a b c : ENNReal}, a = b + c → a - b = c := fun hc_h => absurd (@hc_h _ (⊤) (1) rfl) (by
  simp)

-- ENNReal.sub_eq_of_eq_add_rev', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_eq_of_eq_add_rev'.h4 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → a - b = c := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.le_sub_of_add_le_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_sub_of_add_le_right.h4 : ¬∀ {a b c : ENNReal}, b ≠ ⊤ → a ≤ c - b := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.add_lt_add_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_lt_add_left.h4 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → a + b < a + c := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.sub_eq_of_eq_add', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_eq_of_eq_add'.h3 : ¬∀ {a b c : ENNReal}, a = c + b → a - b = c := fun hc_h => absurd (@hc_h _ (⊤) (1) rfl) (by
  simp)

-- ENNReal.sub_eq_of_eq_add', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_eq_of_eq_add'.h4 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → a - b = c := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.le_sub_iff_add_le_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_sub_iff_add_le_left.h4 : ¬∀ {a b c : ENNReal}, c ≠ ⊤ → (a ≤ b - c ↔ c + a ≤ b) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.lt_add_of_sub_lt_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.lt_add_of_sub_lt_right.h4 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ ∨ c ≠ ⊤ → a < b + c := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.sub_add_eq_add_sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_add_eq_add_sub.h3 : ¬∀ {a b c : ENNReal}, b ≠ ⊤ → a - b + c = a + c - b := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  simp)

-- Equiv.Perm.prodExtendRight_apply_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Perm.prodExtendRight_apply_ne.h6 : Not
      (∀ {α₁ β₁ : Type} [inst : DecidableEq α₁] (e : Equiv.Perm β₁) {a a' : α₁} (b : β₁),
        @Eq (Prod α₁ β₁)
          (@DFunLike.coe (Equiv.Perm (Prod α₁ β₁)) (Prod α₁ β₁) (fun (x : Prod α₁ β₁) => Prod α₁ β₁)
            (@EquivLike.toFunLike (Equiv.Perm (Prod α₁ β₁)) (Prod α₁ β₁) (Prod α₁ β₁)
              (@Equiv.instEquivLike (Prod α₁ β₁) (Prod α₁ β₁)))
            (@Equiv.Perm.prodExtendRight α₁ β₁ inst a e) (@Prod.mk α₁ β₁ a' b))
          (@Prod.mk α₁ β₁ a' b)) := fun hc_h => absurd (@hc_h (Nat) (Bool) (instDecidableEqNat) (@Equiv.mk Bool Bool Bool.not Bool.not
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Bool.false)) (by
  decide +kernel)

-- ENNReal.pow_lt_pow_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.pow_lt_pow_left.h3 : ¬∀ {a b : ENNReal} {n : ℕ}, a < b → a ^ n < b ^ n := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  simp)) (by
  simp)

-- ENNReal.pow_lt_pow_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.pow_lt_pow_left.h4 : ¬∀ {a b : ENNReal} {n : ℕ}, n ≠ 0 → a ^ n < b ^ n := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- Function.Coequalizer.desc_mk, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Coequalizer.desc_mk.h6 : ¬∀ {α β : Type} (f g : α → β) {γ : Type} (u : β → γ) (x : β), u ∘ f = u ∘ g := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ => 0 : Bool → ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Function.update_eq_const_of_subsingleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.update_eq_const_of_subsingleton.h3 : ¬∀ {α α' : Type} [inst : DecidableEq α] (a : α) (v : α') (f : α → α'), Function.update f a v = Function.const α v := fun hc_h => absurd (@hc_h (Bool) (ℕ) (instDecidableEqBool) (Bool.false) (0) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  decide +kernel)

-- Equiv.image_strictMono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.image_strictMono.h6 : Not
      (∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {e : Equiv α β} (s : Set α),
        @StrictMono (@Set.Elem α s)
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
            (@Equiv.image α β e s))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialOrder.toPreorder Bool Bool.instPartialOrder) (@PartialOrder.toPreorder Bool Bool.instPartialOrder) (@Equiv.mk Bool Bool Bool.not Bool.not
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
          (@Eq.refl Bool Bool.true)))) (@Set.ofPred Bool fun (x : Bool) => True)) (by
  decide +kernel)

-- Quot.congr_mk, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Quot.congr_mk.h5 : Not
      (∀ {α β : Type} {ra : α → α → Prop} {rb : β → β → Prop} (e : Equiv α β) (a a₁ a₂ : α),
        Iff (ra a₁ a₂)
          (rb
            (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
              (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e a₁)
            (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
              (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e a₂))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ _ => True : Bool → Bool → Prop) (fun _ _ => False : Bool → Bool → Prop) (@Equiv.mk Bool Bool Bool.not Bool.not
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
          (@Eq.refl Bool Bool.true)))) (Bool.false)) (by
  decide +kernel)

-- eq_rec_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.eq_rec_inj.h3 : ¬∀ {α : Type} {a a' : α} {C : α → Type} (x y : C a), a = a' := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (fun (a : ℕ) => ℕ) (0) (0)) (by
  decide +kernel)

-- Iff.ne_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.ne_left.h6 : ¬∀ {α β : Type} {a b : α} {c d : β}, a ≠ b ↔ c = d := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) (0) (0) (0)) (by
  decide +kernel)

-- Function.funext_iff_of_subsingleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.funext_iff_of_subsingleton.h3 : ¬∀ {α β : Type} {f g : α → β} (x y : α), f x = g y ↔ f = g := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (1)) (by
  simp)

-- CompTriple.comp_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CompTriple.comp_eq.h6 : ¬∀ {M N P : Type} {φ : M → N} {ψ : N → P} {χ : outParam (M → P)}, ψ ∘ φ = χ := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : Bool → ℕ)) (by
  decide +kernel)

-- RightCommutative.right_comm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.RightCommutative.right_comm.h3 : ¬∀ {α β : Type} {op : β → α → β} (b : β) (a₁ a₂ : α), op (op b a₁) a₂ = op (op b a₂) a₁ := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun (a : Bool) (n : ℕ) => n % 2 == 0) (Bool.false) (0) (1)) (by
  decide +kernel)

-- LeftCommutative.left_comm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.LeftCommutative.left_comm.h3 : ¬∀ {α β : Type} {op : α → β → β} (a₁ a₂ : α) (b : β), op a₁ (op a₂ b) = op a₂ (op a₁ b) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) (1) (0)) (by
  decide +kernel)

-- Equiv.image_monotone, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.image_monotone.h6 : Not
      (∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {e : Equiv α β} (s : Set α),
        @Monotone (@Set.Elem α s)
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
            (@Equiv.image α β e s))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialOrder.toPreorder Bool Bool.instPartialOrder) (@PartialOrder.toPreorder Bool Bool.instPartialOrder) (@Equiv.mk Bool Bool Bool.not Bool.not
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
          (@Eq.refl Bool Bool.true)))) (@Set.ofPred Bool fun (x : Bool) => True)) (by
  decide +kernel)

-- ENNReal.inv_le_iff_le_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_le_iff_le_mul.h2 : ¬∀ {a b : ENNReal}, (a = ⊤ → b ≠ 0) → (a⁻¹ ≤ b ↔ 1 ≤ a * b) := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.inv_le_iff_le_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_le_iff_le_mul.h3 : ¬∀ {a b : ENNReal}, (b = ⊤ → a ≠ 0) → (a⁻¹ ≤ b ↔ 1 ≤ a * b) := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide)) (by
  simp)

-- ENNReal.mul_div_cancel', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_div_cancel'.h2 : ¬∀ {a b : ENNReal}, (a = ⊤ → b = 0) → a * (b / a) = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.mul_div_cancel', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_div_cancel'.h3 : ¬∀ {a b : ENNReal}, (a = 0 → b = 0) → a * (b / a) = b := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.mul_inv_cancel_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_inv_cancel_left.h2 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → a * (a⁻¹ * b) = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.mul_inv_cancel_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_inv_cancel_left.h3 : ¬∀ {a b : ENNReal}, a ≠ 0 → a * (a⁻¹ * b) = b := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- by_cases, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.by_cases.h2 : ¬∀ {p q : Prop}, (¬p → q) → q := fun hc_h => absurd (@hc_h (True) (False) (by
  decide)) (by
  decide +kernel)

-- by_cases, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.by_cases.h3 : ¬∀ {p q : Prop}, (p → q) → q := fun hc_h => absurd (@hc_h (False) (False) (by
  decide)) (by
  decide +kernel)

-- ENNReal.mul_div_cancel_right', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_div_cancel_right'.h2 : ¬∀ {a b : ENNReal}, (b = ⊤ → a = 0) → a * b / b = a := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  norm_num)

-- ENNReal.mul_div_cancel_right', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_div_cancel_right'.h3 : ¬∀ {a b : ENNReal}, (b = 0 → a = 0) → a * b / b = a := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- Function.Embedding.optionElim_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.optionElim_apply.h4 : ¬∀ {α β : Type} (f : α ↪ β) (x : β) (a : Option α), x ∉ Set.range ⇑f := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) (0) (Option.none)) (by
  decide +kernel)

-- ENNReal.mul_inv_cancel_right', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_inv_cancel_right'.h2 : ¬∀ {a b : ENNReal}, (b = ⊤ → a = 0) → a * b * b⁻¹ = a := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.mul_inv_cancel_right', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_inv_cancel_right'.h3 : ¬∀ {a b : ENNReal}, (b = 0 → a = 0) → a * b * b⁻¹ = a := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.inv_mul_cancel_right', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_mul_cancel_right'.h2 : ¬∀ {a b : ENNReal}, (b = ⊤ → a = 0) → a * b⁻¹ * b = a := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.inv_mul_cancel_right', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_mul_cancel_right'.h3 : ¬∀ {a b : ENNReal}, (b = 0 → a = 0) → a * b⁻¹ * b = a := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.exists_nat_pos_mul_gt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_nat_pos_mul_gt.h2 : Not
      (∀ {a b : ENNReal},
        @Ne ENNReal b (@Top.top ENNReal ENNReal.instTop) →
          ∃ (n : Nat),
            And (@GT.gt Nat instLTNat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder)) b
                (@HMul.hMul ENNReal ENNReal ENNReal
                  (@instHMul ENNReal
                    (@Distrib.toMul ENNReal
                      (@instDistribOfSemiring ENNReal (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring))))
                  (@Nat.cast ENNReal
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    n)
                  a))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) (by
  decide)) (by
  simp)

-- ENNReal.exists_nat_pos_mul_gt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_nat_pos_mul_gt.h3 : Not
      (∀ {a b : ENNReal},
        @Ne ENNReal a (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) →
          ∃ (n : Nat),
            And (@GT.gt Nat instLTNat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder)) b
                (@HMul.hMul ENNReal ENNReal ENNReal
                  (@instHMul ENNReal
                    (@Distrib.toMul ENNReal
                      (@instDistribOfSemiring ENNReal (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring))))
                  (@Nat.cast ENNReal
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    n)
                  a))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat ENNReal (nat_lit 1) (@One.toOfNat1 ENNReal ENNReal.instOne)) (@Top.top ENNReal ENNReal.instTop) (by
  simp)) (by
  simp)

-- Function.Semiconj.comp_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Semiconj.comp_eq.h5 : ¬∀ {α β : Type} {f : α → β} {ga : α → α} {gb : β → β}, f ∘ ga = gb ∘ f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (not : Bool → Bool) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Equiv.eq_or_eq_of_swap_apply_ne_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.eq_or_eq_of_swap_apply_ne_self.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a b x : α}, x = a ∨ x = b := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0) (1)) (by
  decide +kernel)

-- ENNReal.div_div_cancel', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_div_cancel'.h2 : ¬∀ {a b : ENNReal}, (a = ⊤ → b = 0) → a / (a / b) = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.div_div_cancel', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_div_cancel'.h3 : ¬∀ {a b : ENNReal}, (a = 0 → b = 0) → a / (a / b) = b := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.inv_mul_cancel_left', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_mul_cancel_left'.h2 : ¬∀ {a b : ENNReal}, (a = ⊤ → b = 0) → a⁻¹ * (a * b) = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.inv_mul_cancel_left', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_mul_cancel_left'.h3 : ¬∀ {a b : ENNReal}, (a = 0 → b = 0) → a⁻¹ * (a * b) = b := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- sign_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.sign_pos.h5 : ¬∀ {α : Type} [inst : Zero α] [inst_1 : Preorder α] [inst_2 : DecidableLT α] {a : α}, SignType.sign a = 1 := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instPreorder) (Nat.decLt) (0)) (by
  decide +kernel)

-- Classical.by_cases, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Classical.by_cases.h2 : ¬∀ {p q : Prop}, (¬p → q) → q := fun hc_h => absurd (@hc_h (True) (False) (by
  decide)) (by
  decide +kernel)

-- Classical.by_cases, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Classical.by_cases.h3 : ¬∀ {p q : Prop}, (p → q) → q := fun hc_h => absurd (@hc_h (False) (False) (by
  decide)) (by
  decide +kernel)

-- Nonempty.elim_to_inhabited, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nonempty.elim_to_inhabited.h3 : ¬∀ {α : Type} [h : Nonempty α] {p : Prop}, p := fun hc_h => absurd (@hc_h (ℕ) _ (False)) (by
  decide +kernel)

-- Complex.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Complex.ext.h2 : ¬∀ {z w : ℂ}, z.im = w.im → z = w := fun hc_h => absurd (@hc_h ({ re := { cauchy := 0 : ℝ }, im := { cauchy := 0 : ℝ } : ℂ }) ({ re := { cauchy := 1 : ℝ }, im := { cauchy := 0 : ℝ } : ℂ }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Complex.ext, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Complex.ext.h3 : ¬∀ {z w : ℂ}, z.re = w.re → z = w := fun hc_h => absurd (@hc_h ({ re := { cauchy := 0 : ℝ }, im := { cauchy := 0 : ℝ } : ℂ }) ({ re := { cauchy := 0 : ℝ }, im := { cauchy := 1 : ℝ } : ℂ }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Function.IsPartialInv.surjective_getD, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.IsPartialInv.surjective_getD.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → Option α} (x : α), Function.Surjective fun (x_1 : β) => (g x_1).getD x := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool) (fun _ => none : Bool → Option Bool) (Bool.false)) (by
  decide +kernel)

-- Denumerable.raise_lower', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Denumerable.raise_lower'.h2 : ¬∀ {l : List ℕ} {n : ℕ}, l.SortedLT → Denumerable.raise' (Denumerable.lower' l n) n = l := fun hc_h => absurd (@hc_h ([0]) (1) (by
  decide)) (by
  decide +kernel)

-- Denumerable.raise_lower', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Denumerable.raise_lower'.h3 : ¬∀ {l : List ℕ} {n : ℕ}, (∀ m ∈ l, n ≤ m) → Denumerable.raise' (Denumerable.lower' l n) n = l := fun hc_h => absurd (@hc_h ([1, 0]) (0) (by
  decide)) (by
  decide +kernel)

-- SetRel.subset_iterate_comp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.subset_iterate_comp.h3 : ¬∀ {α β : Type} {R : SetRel α α} {S : SetRel α β} {n : ℕ}, S ⊆ (fun (x : SetRel α β) => R.comp x)^[n] S := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (∅) (⊤) (1)) (by
  simp)

-- Function.Surjective.of_comp_iff', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.of_comp_iff'.h4 : ¬∀ {α β γ : Type} {f : α → β} (g : γ → α), Function.Surjective (f ∘ g) ↔ Function.Surjective g := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool) (fun _ => true : Bool → Bool) (not : Bool → Bool)) (by
  decide +kernel)

-- Ne.ite_ne_right_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ne.ite_ne_right_iff.h5 : ¬∀ {α : Type} {P : Prop} [inst : Decidable P] {a b : α}, (if P then a else b) ≠ b ↔ P := fun hc_h => absurd (@hc_h (ℕ) (True) (instDecidableTrue) (0) (0)) (by
  decide +kernel)

-- Function.iterate_add_eq_iterate, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.iterate_add_eq_iterate.h5 : ¬∀ {α : Type} {f : α → α} {m n : ℕ} {a : α}, f^[m + n] a = f^[n] a ↔ f^[m] a = a := fun hc_h => absurd (@hc_h (ℕ) (fun _ => 0 : ℕ → ℕ) (1) (1) (1)) (by
  decide +kernel)

-- ENNReal.toReal_eq_toReal_iff', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_eq_toReal_iff'.h2 : ¬∀ {x y : ENNReal}, y ≠ ⊤ → (x.toReal = y.toReal ↔ x = y) := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide)) (by
  simp)

-- ENNReal.toReal_eq_toReal_iff', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_eq_toReal_iff'.h3 : ¬∀ {x y : ENNReal}, x ≠ ⊤ → (x.toReal = y.toReal ↔ x = y) := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.toReal_inf, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_inf.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → (Min.min a b).toReal = Min.min a.toReal b.toReal := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.toReal_inf, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_inf.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → (Min.min a b).toReal = Min.min a.toReal b.toReal := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.toReal_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_add.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → (a + b).toReal = a.toReal + b.toReal := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.toReal_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_add.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → (a + b).toReal = a.toReal + b.toReal := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.toReal_mono', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_mono'.h2 : ¬∀ {a b : ENNReal}, (b = ⊤ → a = ⊤) → a.toReal ≤ b.toReal := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  simp)

-- PEquiv.coe_mk_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PEquiv.coe_mk_apply.h4 : ¬∀ {α β : Type} (f₁ : α → Option β) (f₂ : β → Option α) (x a : α) (b : β), f₂ b = Option.some a ↔ f₁ a = Option.some b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => none : ℕ → Option ℕ) (some : ℕ → Option ℕ) (0)) (by
  simp)

-- ENNReal.toReal_mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_mono.h3 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → a.toReal ≤ b.toReal := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.toReal_max, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_max.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → (Max.max a b).toReal = Max.max a.toReal b.toReal := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.toReal_max, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_max.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → (Max.max a b).toReal = Max.max a.toReal b.toReal := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- instIsEmptyForallOfNonempty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instIsEmptyForallOfNonempty.h2 : ¬∀ {α : Type} {p : α → Prop} [h : Nonempty α], IsEmpty (∀ (x : α), p x) := fun hc_h => absurd (@hc_h (ℕ) (fun _ => True : ℕ → Prop) _) (by
  simp)

-- ENNReal.toReal_sub_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_sub_of_le.h2 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → (a - b).toReal = a.toReal - b.toReal := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- Ne.ite_eq_left_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ne.ite_eq_left_iff.h5 : ¬∀ {α : Type} {P : Prop} [inst : Decidable P] {a b : α}, (if P then a else b) = a ↔ P := fun hc_h => absurd (@hc_h (ℕ) (False) (instDecidableFalse) (0) (0)) (by
  decide +kernel)

-- IsSymmOp.symm_op, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsSymmOp.symm_op.h3 : ¬∀ {α β : Type} {op : α → α → β} (a b : α), op a b = op b a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) (1)) (by
  decide +kernel)

-- instRightCommutativeOfCommutativeOfAssociative, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instRightCommutativeOfCommutativeOfAssociative.h3 : ¬∀ {α : Type} {f : α → α → α} [hc : Std.Commutative f], RightCommutative f := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd (hc_c.right_comm (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- beq_eq_decide, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.beq_eq_decide.h2 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : DecidableEq α] (a b : α), (a == b) = Decidable.decide (a = b) := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (instDecidableEqNat) (0) (1)) (by
  decide +kernel)

-- ENNReal.mem_Iio_self_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mem_Iio_self_add.h2 : ¬∀ {x ε : ENNReal}, ε ≠ 0 → x ∈ Set.Iio (x + ε) := fun hc_h => absurd (@hc_h (⊤) (1) (by
  simp)) (by
  decide +kernel)

-- ENNReal.mem_Iio_self_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mem_Iio_self_add.h3 : ¬∀ {x ε : ENNReal}, x ≠ ⊤ → x ∈ Set.Iio (x + ε) := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- Equiv.existsUnique_congr', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.existsUnique_congr'.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} (e : α ≃ β), (∃! a : α, p a) ↔ ∃! b : β, q b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (1)) (by
  simp)

-- subtypeOrLeftEmbedding_apply_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.subtypeOrLeftEmbedding_apply_left.h5 : ¬∀ {α : Type} {p q : α → Prop} [inst : DecidablePred p] (x : { x : α // p x ∨ q x }), p ↑x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n % 2 = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ((⟨2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // (fun (n : ℕ) => n = 0) x ∨ (fun (n : ℕ) => n % 2 = 0) x }))) (by
  decide +kernel)

-- ENNReal.lt_top_of_mul_ne_top_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.lt_top_of_mul_ne_top_right.h2 : ¬∀ {a b : ENNReal}, a ≠ 0 → b < ⊤ := fun hc_h => absurd (@hc_h (1) (⊤) (by
  simp)) (by
  decide +kernel)

-- ENNReal.lt_top_of_mul_ne_top_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.lt_top_of_mul_ne_top_right.h3 : ¬∀ {a b : ENNReal}, a * b ≠ ⊤ → b < ⊤ := fun hc_h => absurd (@hc_h (0) (⊤) (by
  simp)) (by
  decide +kernel)

-- subtypeOrLeftEmbedding_apply_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.subtypeOrLeftEmbedding_apply_right.h5 : ¬∀ {α : Type} {p q : α → Prop} [inst : DecidablePred p] (x : { x : α // p x ∨ q x }), ¬p ↑x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // (fun (n : ℕ) => n = 0) x ∨ (fun (n : ℕ) => n = 0) x }))) (by
  decide +kernel)

-- Function.Injective.of_comp_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.of_comp_iff.h4 : ¬∀ {α β γ : Type} {f : α → β} (g : γ → α), Function.Injective (f ∘ g) ↔ Function.Injective g := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) (fun _ => 0 : ℕ → ℕ) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  decide +kernel)

-- Function.Involutive.ite_not, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Involutive.ite_not.h2 : ¬∀ {α : Type} {f : α → α} (P : Prop) [inst : Decidable P] (x : α), f (if P then x else f x) = if ¬P then x else f x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (False) (instDecidableFalse) (0)) (by
  decide +kernel)

-- Equiv.Set.insert_symm_apply_inl, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.insert_symm_apply_inl.h4 : ¬∀ {α : Type} {s : Set α} [inst : DecidablePred fun (x : α) => x ∈ s] {a : α} (b : ↑s), a ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => Set.decidableOfPred a fun (n : ℕ) => n = 0) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} }))) (by
  decide +kernel)

-- Equiv.swap_bijOn_self, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.swap_bijOn_self.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a b : α} {s : Set α}, Set.BijOn (⇑(Equiv.swap a b)) s s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (1) ({n : ℕ | n = 0})) (by
  simp)

-- Equiv.exists_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.exists_congr.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} (e : α ≃ β), (∃ (a : α), p a) ↔ ∃ (b : β), q b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (1)) (by
  simp)

-- Equiv.toPartialEquivOfImageEq_source, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.toPartialEquivOfImageEq_source.h5 : ¬∀ {α β : Type} (e : α ≃ β) (s : Set α) (t : Set β), ⇑e '' s = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- ENNReal.mul_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_ne_top.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → a * b ≠ ⊤ := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.mul_ne_top, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_ne_top.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → a * b ≠ ⊤ := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- Equiv.congr_fun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.congr_fun.h4 : Not
      (∀ {α β : Type} {f g : Equiv α β} (x : α),
        @Eq β
          (@DFunLike.coe (Equiv α β) α (fun (x : α) => β) (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β))
            f x)
          (@DFunLike.coe (Equiv α β) α (fun (x : α) => β) (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β))
            g x)) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@Equiv.mk Bool Bool Bool.not Bool.not
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
          (@Eq.refl Bool Bool.true)))) (@Equiv.mk Bool Bool (fun (b : Bool) => b) (fun (b : Bool) => b)
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
          (@Eq.refl Bool Bool.true)))) (Bool.false)) (by
  decide +kernel)

-- Equiv.congr_arg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.congr_arg.h5 : ¬∀ {α β : Type} {f : α ≃ β} {x x' : α}, f x = f x' := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) (0) (1)) (by
  decide +kernel)

-- PartialEquiv.IsImage.symm_mapsTo, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.IsImage.symm_mapsTo.h5 : Not
      (∀ {α β : Type} {e : PartialEquiv α β} {s : Set α} {t : Set β},
        @Set.MapsTo β α (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e))
          (@Min.min (Set β) (@Set.instMin β) (@PartialEquiv.target α β e) t)
          (@Min.min (Set α) (@Set.instMin α) (@PartialEquiv.source α β e) s)) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
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

-- ENNReal.inv_div, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_div.h2 : ¬∀ {a b : ENNReal}, b ≠ 0 ∨ a ≠ 0 → (a / b)⁻¹ = b / a := fun hc_h => absurd (@hc_h (⊤) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.inv_div, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_div.h3 : ¬∀ {a b : ENNReal}, b ≠ ⊤ ∨ a ≠ ⊤ → (a / b)⁻¹ = b / a := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.zpow_lt_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.zpow_lt_top.h2 : ¬∀ {a : ENNReal}, a ≠ 0 → ∀ (n : ℤ), a ^ n < ⊤ := fun hc_h => absurd (@hc_h (⊤) (by
  decide) (1)) (by
  simp)

-- ENNReal.div_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_pos.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → 0 < a / b := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.div_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_pos.h3 : ¬∀ {a b : ENNReal}, a ≠ 0 → 0 < a / b := fun hc_h => absurd (@hc_h (1) (⊤) (by
  simp)) (by
  simp)

-- ENNReal.zpow_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.zpow_pos.h1 : ¬∀ {a : ENNReal}, a ≠ ⊤ → ∀ (n : ℤ), 0 < a ^ n := fun hc_h => absurd (@hc_h (0) (by
  decide) (1)) (by
  simp)

-- Function.Involutive.eq_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Involutive.eq_iff.h2 : ¬∀ {α : Type} {f : α → α} {x y : α}, f x = y ↔ x = f y := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (1)) (by
  decide +kernel)

-- CompTriple.instId_comp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CompTriple.instId_comp.h4 : ¬∀ {M N : Type} {φ : M → N} {ψ : N → N}, CompTriple φ ψ φ := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.comp_eq)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Refl.comap, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Refl.comap.h3 : ¬∀ {α β : Type} {r : β → β → Prop} (f : α → β), Std.Refl (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.refl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Relation.ReflGen.to_reflTransGen, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.ReflGen.to_reflTransGen.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Relation.ReflTransGen r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0)) (by
  nofun)

-- Symmetric.iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Symmetric.iff.h2 : ¬∀ {α : Type} {r : α → α → Prop} (x y : α), r x y ↔ r y x := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (1)) (by
  decide +kernel)

-- Equiv.ofBijective_apply_symm_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofBijective_apply_symm_apply.h3 : ¬∀ {α β : Type} (f : α → β) (x : β), Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ) (0)) (by
  nofun)

-- Function.instIsTransOnFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsTransOnFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) (f : α → β), IsTrans α (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≠ b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
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

-- Equiv.ofBijective_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofBijective_apply.h3 : ¬∀ {α β : Type} (f : α → β) (a : α), Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ) (Bool.false)) (by
  nofun)

-- Function.Bijective.existsUnique_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.existsUnique_iff.h3 : ¬∀ {α β : Type} {f : α → β} {p : β → Prop}, (∃! y : β, p y) ↔ ∃! x : α, p (f x) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n = 0 : ℕ → Prop)) (by
  simp)

-- Equiv.ext, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ext.h4 : Not (∀ {α β : Type} {f g : Equiv α β}, @Eq (Equiv α β) f g) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@Equiv.mk Bool Bool Bool.not Bool.not
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
          (@Eq.refl Bool Bool.true)))) (@Equiv.mk Bool Bool (fun (b : Bool) => b) (fun (b : Bool) => b)
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
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Equiv.optionSubtypeNe_symm_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.optionSubtypeNe_symm_of_ne.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a b : α}, b ≠ a := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0)) (by
  decide +kernel)

-- Function.RightInverse.comp_eq_id, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.RightInverse.comp_eq_id.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α}, g ∘ f = id := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool)) (by
  decide +kernel)

-- Function.iterate_fixed, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.iterate_fixed.h3 : ¬∀ {α : Type} {f : α → α} {x : α} (n : ℕ), f^[n] x = x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (1)) (by
  decide +kernel)

-- Function.Embedding.ext, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.ext.h4 : ¬∀ {α β : Type} {f g : α ↪ β}, f = g := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({ toFun := fun (b : Bool) => if b = Bool.true then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ }) ({ toFun := fun (a : Bool) => if a = Bool.false then 1 else 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Bool ↪ ℕ })) (by
  decide +kernel)

-- SetRel.left_subset_comp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.left_subset_comp.h4 : ¬∀ {α β : Type} {S : SetRel β β} {R : SetRel α β}, R ⊆ R.comp S := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (∅) (⊤)) (by
  simp)

-- SetRel.right_subset_comp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.right_subset_comp.h3 : ¬∀ {α β : Type} {R : SetRel α α} {S : SetRel α β}, S ⊆ R.comp S := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (∅) (⊤)) (by
  simp)

-- Equiv.Set.insert_apply_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.insert_apply_left.h4 : ¬∀ {α : Type} {s : Set α} [inst : DecidablePred fun (x : α) => x ∈ s] {a : α}, a ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => Set.decidableOfPred a fun (n : ℕ) => n = 0) (0)) (by
  decide +kernel)

-- Equiv.Set.sumCompl_symm_apply_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.sumCompl_symm_apply_of_mem.h4 : ¬∀ {α : Type} {s : Set α} [inst : DecidablePred fun (x : α) => x ∈ s] {x : α}, x ∈ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => Set.decidableOfPred a fun (n : ℕ) => n = 0) (1)) (by
  decide +kernel)

-- Equiv.Set.Equiv.strictMono_setCongr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.Equiv.strictMono_setCongr.h4 : ¬∀ {α : Type} {s t : Set α} [inst : Preorder α], s = t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (Nat.instPreorder)) (by
  simp)

-- Function.LeftInverse.comp_eq_id, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.comp_eq_id.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α}, f ∘ g = id := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun n => n % 2 == 0 : ℕ → Bool) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  decide +kernel)

-- PEquiv.injective_of_forall_ne_isSome, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PEquiv.injective_of_forall_ne_isSome.h4 : ¬∀ {α β : Type} (f : α ≃. β) (a₂ : α), Function.Injective ⇑f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (⊥) (Bool.false)) (by
  decide +kernel)

-- PEquiv.isSome_symm_get, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PEquiv.isSome_symm_get.h4 : ¬∀ {α β : Type} (f : α ≃. β) {a : α}, (f a).isSome = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (⊥) (0)) (by
  decide +kernel)

-- Function.RightInverse.leftInverse, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.RightInverse.leftInverse.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α}, Function.LeftInverse f g := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun n => n % 2 == 0 : ℕ → Bool) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  decide +kernel)

-- PEquiv.coe_mk, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PEquiv.coe_mk.h4 : ¬∀ {α β : Type} (f₁ : α → Option β) (f₂ : β → Option α) (a : α) (b : β), f₂ b = Option.some a ↔ f₁ a = Option.some b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => none : ℕ → Option ℕ) (some : ℕ → Option ℕ)) (by
  simp)

-- SetRel.IsCover.subset_iUnion_ball, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.IsCover.subset_iUnion_ball.h4 : ¬∀ {X : Type} {U : SetRel X X} {s N : Set X}, s ⊆ ⋃ y ∈ N, U.ball y := fun hc_h => absurd (@hc_h (ℕ) (∅) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Subsingleton.le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subsingleton.le.h2 : ¬∀ {α : Type} [inst : Preorder α] (x y : α), x ≤ y := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (1) (0)) (by
  decide +kernel)

-- PartialEquiv.symm_image_image_of_subset_source, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.symm_image_image_of_subset_source.h4 : ¬∀ {α β : Type} (e : PartialEquiv α β) {s : Set α}, ↑e.symm '' ↑e '' s = s := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Inhabited.default) ({b : Bool | b = Bool.true})) (by
  (simp <;> decide))

-- Function.exists_fixed_point_of_surjective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.exists_fixed_point_of_surjective.h3 : ¬∀ {α β : Type} (f : α → α → β) (g : β → β), ∃ (x : β), g x = x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- PartialEquiv.map_source', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.map_source'.h4 : Not
      (∀ {α β : Type} (self : PartialEquiv α β) ⦃x : α⦄,
        @Membership.mem β (Set β) (@Set.instMembership β) (@PartialEquiv.target α β self) (@PartialEquiv.toFun α β self x)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Inhabited.default (PartialEquiv Nat Nat) (@PartialEquiv.instInhabited Nat Nat instInhabitedNat instInhabitedNat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  nofun)

-- PartialEquiv.right_inv, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.right_inv.h4 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) {x : β},
        @Eq β (@PartialEquiv.toFun α β e (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e) x)) x) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Inhabited.default (PartialEquiv Nat Nat) (@PartialEquiv.instInhabited Nat Nat instInhabitedNat instInhabitedNat)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Function.Surjective.injective_comp_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.injective_comp_right.h4 : ¬∀ {α β γ : Type} {f : α → β}, Function.Injective fun (g : β → γ) => g ∘ f := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- PartialEquiv.map_target', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.map_target'.h4 : ¬∀ {α β : Type} (self : PartialEquiv α β) ⦃x : β⦄, self.invFun x ∈ self.source := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Inhabited.default) (0)) (by
  nofun)

-- ENNReal.toNNReal_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_pos.h1 : ¬∀ {a : ENNReal}, a ≠ ⊤ → 0 < a.toNNReal := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- ENNReal.toNNReal_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_pos.h2 : ¬∀ {a : ENNReal}, a ≠ 0 → 0 < a.toNNReal := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  simp)

-- Function.Bijective.surjective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.surjective.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- Function.Embedding.mk_coe, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Function.Embedding.mk_coe.h3.der.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} (f : α ↪ β), Function.Injective ⇑f := by
  (intros; grind)
theorem HypCheckProof.Function.Embedding.mk_coe.h3.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} (f : α ↪ β),
      { toFun := ⇑f, inj' := HypCheckProof.Function.Embedding.mk_coe.h3.der f : α ↪ β } = f := by
  intro hc_x0 hc_x1 hc_x2
  exact @Function.Embedding.mk_coe hc_x0 hc_x1 hc_x2 (@HypCheckProof.Function.Embedding.mk_coe.h3.der hc_x0 hc_x1 hc_x2)

-- Function.leftInverse_surjInv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.leftInverse_surjInv.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ)) (by
  nofun)

-- Equiv.subsingleton.symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subsingleton.symm.h3 : ¬∀ {α β : Type} (e : α ≃ β), Subsingleton β := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Equiv.subsingleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subsingleton.h3 : ¬∀ {α β : Type} (e : α ≃ β), Subsingleton α := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.add_le_add_iff_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_le_add_iff_right.h3 : ¬∀ {a b c : ENNReal}, b + a ≤ c + a ↔ b ≤ c := fun hc_h => absurd (@hc_h (⊤) (1) (0)) (by
  simp)

-- Equiv.Perm.ext, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Perm.ext.h3 : Not (∀ {α : Type} {σ τ : Equiv.Perm α}, @Eq (Equiv.Perm α) σ τ) := fun hc_h => absurd (@hc_h (Bool) (@Equiv.mk Bool Bool Bool.not Bool.not
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
          (@Eq.refl Bool Bool.true)))) (@Equiv.mk Bool Bool (fun (b : Bool) => b) (fun (b : Bool) => b)
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
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- ENNReal.pow_le_pow_left_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.pow_le_pow_left_iff.h3 : ¬∀ {a b : ENNReal} {n : ℕ}, a ^ n ≤ b ^ n ↔ a ≤ b := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  simp)

-- Equiv.coe_ofBijective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.coe_ofBijective.h3 : ¬∀ {α β : Type} (f : α → β), Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ)) (by
  nofun)

-- Function.Injective.pairwise_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.pairwise_ne.h3 : ¬∀ {α ι : Type} {f : ι → α}, Pairwise (Function.onFun (fun (x1 x2 : α) => x1 ≠ x2) f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- ENNReal.div_lt_of_lt_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_lt_of_lt_mul.h3 : ¬∀ {a b c : ENNReal}, a / c < b := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- Std.Refl.set_pairwise_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Refl.set_pairwise_iff.h3 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α}, s.Pairwise r ↔ ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ({n : ℕ | n = 0})) (by
  simp)

-- ENNReal.mul_le_of_forall_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_le_of_forall_lt.h3 : ¬∀ {a b c : ENNReal}, a * b ≤ c := fun hc_h => absurd (@hc_h (1) (1) (0)) (by
  simp)

-- Function.Bijective.of_isEmpty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.of_isEmpty.h3 : ¬∀ {α β : Type} (f : α → β), Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ)) (by
  nofun)

-- ENNReal.mul_lt_of_lt_div', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_lt_of_lt_div'.h3 : ¬∀ {a b c : ENNReal}, c * a < b := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- ENNReal.mul_le_of_le_div', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_le_of_le_div'.h3 : ¬∀ {a b c : ENNReal}, c * a ≤ b := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  simp)

-- Equiv.sumEmpty_apply_inl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.sumEmpty_apply_inl.h2 : ¬∀ {α β : Type} (a : α), IsEmpty β := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.false (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Equiv.subtypeUnivEquiv_symm_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypeUnivEquiv_symm_apply.h2 : ¬∀ {α : Type} {p : α → Prop} (x x : α), p x := fun hc_h => absurd (@hc_h (Bool) (fun b => b = true : Bool → Prop) (Bool.false)) (by
  decide +kernel)

-- ENNReal.inv_mul_cancel, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_mul_cancel.h1 : ¬∀ {a : ENNReal}, a ≠ ⊤ → a⁻¹ * a = 1 := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- ENNReal.inv_mul_cancel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_mul_cancel.h2 : ¬∀ {a : ENNReal}, a ≠ 0 → a⁻¹ * a = 1 := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  simp)

-- ENNReal.div_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_self.h1 : ¬∀ {a : ENNReal}, a ≠ ⊤ → a / a = 1 := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- ENNReal.div_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_self.h2 : ¬∀ {a : ENNReal}, a ≠ 0 → a / a = 1 := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  simp)

-- ENNReal.div_le_div_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_le_div_right.h2 : ¬∀ {a b : ENNReal} (c : ENNReal), a / c ≤ b / c := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  simp)

-- Function.surjective_of_right_cancellable_Prop, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.surjective_of_right_cancellable_Prop.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- ENNReal.HolderTriple.inv_add_inv_eq_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.inv_add_inv_eq_inv.h3 : ¬∀ (p q : ENNReal) (r : semiOutParam ENNReal), p⁻¹ + q⁻¹ = r⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- instLeftCommutativeOfRightCommutative, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instLeftCommutativeOfRightCommutative.h3 : ¬∀ {α β : Type} {f : β → α → β}, LeftCommutative fun (x : α) (y : β) => f y x := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun (a : Bool) (n : ℕ) => n % 2 == 0)) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (0 : ℕ) (1 : ℕ) (Bool.false : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.iterate_pred_comp_of_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.iterate_pred_comp_of_pos.h3 : ¬∀ {α : Type} (f : α → α) {n : ℕ}, f^[n.pred] ∘ f = f^[n] := fun hc_h => absurd (@hc_h (Bool) (not : Bool → Bool) (0)) (by
  decide +kernel)

-- finSuccEquiv'_symm_coe_below, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finSuccEquiv'_symm_coe_below.h3 : ¬∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, (finSuccEquiv' i).symm (Option.some m) = m.castSucc := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- instRightCommutativeOfLeftCommutative, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instRightCommutativeOfLeftCommutative.h3 : ¬∀ {α β : Type} {f : α → β → β}, RightCommutative fun (x : β) (y : α) => f y x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.right_comm (0 : ℕ) (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- NNReal.div_le_of_le_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.div_le_of_le_mul.h3 : ¬∀ {a b c : NNReal}, a / c ≤ b := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  simp)

-- finSuccEquiv'_symm_some_below, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finSuccEquiv'_symm_some_below.h3 : ¬∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, (finSuccEquiv' i).symm (Option.some m) = m.castSucc := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- finSuccAboveEquiv_symm_apply_ne_last, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finSuccAboveEquiv_symm_apply_ne_last.h2 : ¬∀ {n : ℕ} {p : Fin (n + 1)} (x : { x : Fin (n + 1) // x ≠ p }), p ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2), of_decide_eq_true (id (Eq.refl Bool.true))⟩ :
      { x : Fin (1 + 1) // x ≠ (⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2) }))) (by
  decide +kernel)

-- NNReal.div_le_of_le_mul', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.div_le_of_le_mul'.h3 : ¬∀ {a b c : NNReal}, a / b ≤ c := fun hc_h => absurd (@hc_h (1) (1) (0)) (by
  simp)

-- or_congr_right', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.or_congr_right'.h3 : ¬∀ {a b c : Prop}, a ∨ b ↔ a ∨ c := fun hc_h => absurd (@hc_h (False) (True) (False)) (by
  decide +kernel)

-- Function.Injective.iterate, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.iterate.h2 : ¬∀ {α : Type} {f : α → α} (n : ℕ), Function.Injective f^[n] := fun hc_h => absurd (@hc_h (ℕ) (fun _ => 0 : ℕ → ℕ) (1)) (by
  simp)

-- SetRel.self_subset_image, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.self_subset_image.h2 : ¬∀ {α : Type} {R : SetRel α α} (s : Set α), s ⊆ R.image s := fun hc_h => absurd (@hc_h (ℕ) (∅) ({n : ℕ | n = 0})) (by
  simp)

-- SetRel.irrefl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.irrefl.h3 : ¬∀ {α : Type} (R : SetRel α α) (a : α), (a, a) ∉ R := fun hc_h => absurd (@hc_h (ℕ) (⊤) (0)) (by
  simp)

-- NNReal.mul_lt_of_lt_div, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.mul_lt_of_lt_div.h3 : ¬∀ {a b r : NNReal}, a * r < b := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- Decidable.or_not_of_imp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Decidable.or_not_of_imp.h3 : ¬∀ {a b : Prop} [inst : Decidable a], b ∨ ¬a := fun hc_h => absurd (@hc_h (True) (False) (instDecidableTrue)) (by
  decide +kernel)

-- Function.Bijective.iterate, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.iterate.h2 : ¬∀ {α : Type} {f : α → α} (n : ℕ), Function.Bijective f^[n] := fun hc_h => absurd (@hc_h (Bool) (fun _ => true : Bool → Bool) (1)) (by
  decide +kernel)

-- NNReal.HolderTriple.right_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.right_pos.h3 : ¬∀ {p : NNReal} {q : NNReal} {r : NNReal}, 0 < q := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNReal.HolderTriple.lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.lt.h3 : ¬∀ {p : NNReal} {q : NNReal} {r : NNReal}, r < p := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNReal.HolderTriple.inv_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.inv_eq.h3 : ¬∀ {p q r : NNReal}, r⁻¹ = p⁻¹ + q⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- NNReal.HolderTriple.left_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.left_pos.h3 : ¬∀ {p : NNReal} {q r : NNReal}, 0 < p := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNReal.HolderTriple.all_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.all_pos.h3 : ¬∀ {p q r : NNReal}, 0 < p ∧ 0 < q ∧ 0 < r := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNReal.HolderTriple.one_div_pos', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.one_div_pos'.h3 : ¬∀ {p q : NNReal} {r : NNReal}, 0 < 1 / r := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- Real.HolderTriple.ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.ne_zero.h3 : ¬∀ {p : ℝ} {q r : ℝ}, p ≠ 0 := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ })) (by
  nofun)

-- NNReal.HolderTriple.inv_pos', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.inv_pos'.h3 : ¬∀ {p q : NNReal} {r : NNReal}, 0 < r⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNReal.HolderTriple.inv_lt_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.inv_lt_inv.h3 : ¬∀ {p : NNReal} {q : NNReal} {r : NNReal}, p⁻¹ < r⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNReal.HolderTriple.one_div_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.one_div_eq.h3 : ¬∀ {p q r : NNReal}, 1 / r = 1 / p + 1 / q := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- NNReal.HolderTriple.inv_add_inv_eq_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.inv_add_inv_eq_inv.h3 : ¬∀ {p q r : NNReal}, p⁻¹ + q⁻¹ = r⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- Real.HolderTriple.ne_zero', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.ne_zero'.h3 : ¬∀ {p q : ℝ} {r : ℝ}, r ≠ 0 := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ })) (by
  nofun)

-- NNReal.HolderTriple.pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.pos.h3 : ¬∀ {p : NNReal} {q r : NNReal}, 0 < p := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- ExistsUnique.choose_eq_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ExistsUnique.choose_eq_iff.h3 : ¬∀ {α : Type} {p : α → Prop} {a : α}, ∃! x : α, p x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (0)) (by
  simp)

-- PartialEquiv.injective_of_source_eq_univ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.injective_of_source_eq_univ.h3 : ¬∀ {α β : Type} (e : PartialEquiv α β), Function.Injective ↑e := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Inhabited.default)) (by
  decide +kernel)

-- Nat.coprime_mul_succ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_mul_succ.h3 : ¬∀ {n m a : ℕ}, (n * a + 1).Coprime (m * a + 1) := fun hc_h => absurd (@hc_h (1) (1) (1)) (by
  decide +kernel)

-- Complex.div_ofNat_im, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Complex.div_ofNat_im.h2 : ¬∀ (z : ℂ) (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h ({ re := { cauchy := 0 : ℝ }, im := { cauchy := 0 : ℝ } : ℂ }) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.HolderConjugate.eq_top_iff_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.eq_top_iff_eq_one.h2 : ¬∀ (p q : ENNReal), p = ⊤ ↔ q = 1 := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- ENNReal.HolderConjugate.pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.pos.h2 : ¬∀ (p q : ENNReal), 0 < p := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- ENNReal.sSup_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sSup_add.h2 : ¬∀ {s : Set ENNReal} {a : ENNReal}, SupSet.sSup s + a = ⨆ b ∈ s, b + a := fun hc_h => absurd (@hc_h (∅) (1)) (by
  simp)

-- Equiv.equiv_subsingleton_cod, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.equiv_subsingleton_cod.h2 : ¬∀ {α β : Type}, Subsingleton (α ≃ β) := fun hc_h => absurd (@hc_h (Bool) (Bool)) (by
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

-- ENNReal.HolderConjugate.one_sub_inv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.one_sub_inv.h2 : ¬∀ (p q : ENNReal), 1 - p⁻¹ = q⁻¹ := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- CompTriple.IsId.eq_id, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.CompTriple.IsId.eq_id.h2 : ¬∀ {M : Type} {σ : M → M}, σ = id := fun hc_h => absurd (@hc_h (Bool) (not : Bool → Bool)) (by
  decide +kernel)

-- ENNReal.HolderConjugate.ne_top_iff_ne_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.ne_top_iff_ne_one.h2 : ¬∀ (p q : ENNReal), p ≠ ⊤ ↔ q ≠ 1 := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- Function.instIrreflSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIrreflSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), Std.Irrefl (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.irrefl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.instIsPartialOrderSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsPartialOrderSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), IsPartialOrder α (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.toRefl.refl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- not_or_of_imp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_or_of_imp.h2 : ¬∀ {a b : Prop}, ¬a ∨ b := fun hc_h => absurd (@hc_h (True) (False)) (by
  decide +kernel)

-- Real.toNNReal_eq_ofNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_eq_ofNat.h2 : ¬∀ {r : ℝ} {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.add_sub_cancel_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_sub_cancel_right.h2 : ¬∀ {a b : ENNReal}, a + b - b = a := fun hc_h => absurd (@hc_h (1) (⊤)) (by
  simp)

-- ENNReal.cancel_of_lt', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.cancel_of_lt'.h2 : ¬∀ {a : ENNReal} {b : ENNReal}, AddLECancellable a := fun hc_h => absurd (@hc_h (⊤) (0)) (by
  simp)

-- Equiv.Perm.subsingleton_eq_refl, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Perm.subsingleton_eq_refl.h1 : Not (∀ {α : Type} (e : Equiv.Perm α), @Eq (Equiv.Perm α) e (Equiv.refl α)) := fun hc_h => absurd (@hc_h (Bool) (@Equiv.mk Bool Bool Bool.not Bool.not
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

-- finSuccEquiv'_last_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finSuccEquiv'_last_apply.h2 : ¬∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- ENNReal.nnreal_smul_lt_top_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.nnreal_smul_lt_top_iff.h2 : ¬∀ {x : NNReal} {y : ENNReal}, x • y < ⊤ ↔ y < ⊤ := fun hc_h => absurd (@hc_h (0) (⊤)) (by
  simp)

-- ENNReal.nnreal_smul_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.nnreal_smul_ne_top.h2 : ¬∀ {x : NNReal} {y : ENNReal}, x • y ≠ ⊤ := fun hc_h => absurd (@hc_h (1) (⊤)) (by
  simp)

-- NNReal.lt_inv_iff_mul_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.lt_inv_iff_mul_lt.h2 : ¬∀ {r p : NNReal}, r < p⁻¹ ↔ r * p < 1 := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- ENNReal.le_toReal_sub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_toReal_sub.h2 : ¬∀ {a b : ENNReal}, a.toReal - b.toReal ≤ (a - b).toReal := fun hc_h => absurd (@hc_h (1) (⊤)) (by
  simp)

-- NNReal.div_lt_one_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.div_lt_one_of_lt.h2 : ¬∀ {a b : NNReal}, a / b < 1 := fun hc_h => absurd (@hc_h (1) (1)) (by
  simp)

-- coe_finRotate_of_ne_last, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.coe_finRotate_of_ne_last.h2 : Not
      (∀ {n : Nat} {i : Fin n.succ},
        @Eq Nat
          (@Fin.val
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@DFunLike.coe
              (Equiv.Perm
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (fun
                  (x :
                    Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@EquivLike.toFunLike
                (Equiv.Perm
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Equiv.instEquivLike
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (finRotate
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              i))
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Fin.val n.succ i)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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

-- Real.toNNReal_le_ofNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_le_ofNat.h2 : ¬∀ {r : ℝ} {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- finRotate_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finRotate_of_lt.h2 : ¬∀ {n k : ℕ}, k < n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Sigma.isEmpty_fibers, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sigma.isEmpty_fibers.h2 : ¬∀ {α : Type} {E : α → Type}, IsEmpty (Sigma E) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false ((⟨0, 0⟩ : (_ : ℕ) × ℕ) : (_ : ℕ) × ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- PProd.isEmpty_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PProd.isEmpty_left.h2 : ¬∀ {α β : Type}, IsEmpty (α ×' β) := fun hc_h => absurd (@hc_h (ℕ) (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false (⟨0, 0⟩ : ℕ ×' ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.instIsStrictWeakOrderSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsStrictWeakOrderSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), IsStrictWeakOrder α (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsStrictOrder.toIrrefl.irrefl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- IsEmpty.forall_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsEmpty.forall_iff.h1 : ¬∀ {α : Type} {p : α → Prop}, (∀ (a : α), p a) ↔ True := fun hc_h => absurd (@hc_h (Bool) (fun b => b = true : Bool → Prop)) (by
  decide +kernel)

-- Real.ext_cauchy, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.ext_cauchy.h2 : ¬∀ {x y : ℝ}, x = y := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 1 : ℝ })) (by
  simp)

-- Real.ofNat_le_toNNReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.ofNat_le_toNNReal.h2 : ¬∀ {n : ℕ} {r : ℝ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h (0) ({ cauchy := 0 : ℝ })) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.eq_of_forall_nnreal_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eq_of_forall_nnreal_le_iff.h2 : ¬∀ {x y : ENNReal}, x = y := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- Quotient.instIsEmpty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Quotient.instIsEmpty.h1 : ¬∀ {α : Type} {s : Setoid α}, IsEmpty (Quotient s) := fun hc_h => absurd (@hc_h (PartialEquiv ℕ ℕ) (PartialEquiv.eqOnSourceSetoid)) (by
  exact fun hc_c =>
    absurd (hc_c.false (Inhabited.default : Quotient PartialEquiv.eqOnSourceSetoid))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.instIsPreorderSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsPreorderSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), IsPreorder α (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.toRefl.refl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.instTrichotomousSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instTrichotomousSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), Std.Trichotomous (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop)) (by
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

-- ENNReal.sub_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_ne_top.h2 : ¬∀ {a b : ENNReal}, a - b ≠ ⊤ := fun hc_h => absurd (@hc_h (⊤) (0)) (by
  decide +kernel)

-- ENNReal.coe_div', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.coe_div'.h2 : Not
      (∀ {r p : NNReal},
        @Eq ENNReal (↑(@HDiv.hDiv NNReal NNReal NNReal (@instHDiv NNReal NNReal.instDiv) p r))
          (@HDiv.hDiv ENNReal ENNReal ENNReal (@instHDiv ENNReal (@DivInvMonoid.toDiv ENNReal ENNReal.instDivInvMonoid)) ↑p
            ↑r)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal NNReal.instZero)) (@OfNat.ofNat NNReal (nat_lit 1) (@One.toOfNat1 NNReal NNReal.instOne))) (by
  simp)

-- ENNReal.HolderConjugate.conj_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.conj_eq.h2 : ¬∀ {p q : ENNReal}, q = 1 + (p - 1)⁻¹ := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Function.instIsStrictOrderSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsStrictOrderSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), IsStrictOrder α (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.toIrrefl.irrefl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- NNReal.HolderConjugate.sub_one_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderConjugate.sub_one_ne_zero.h2 : ¬∀ {p : NNReal} {q : NNReal}, p - 1 ≠ 0 := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- NNReal.HolderConjugate.conjugate_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderConjugate.conjugate_eq.h2 : ¬∀ {p q : NNReal}, q = p / (p - 1) := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- forall_true_iff', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.forall_true_iff'.h2 : ¬∀ {α : Type} {p : α → Prop}, (∀ (a : α), p a) ↔ True := fun hc_h => absurd (@hc_h (Bool) (fun b => b = true : Bool → Prop)) (by
  decide +kernel)

-- NNReal.HolderConjugate.one_sub_inv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderConjugate.one_sub_inv.h2 : ¬∀ {p q : NNReal}, 1 - p⁻¹ = q⁻¹ := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Function.instAsymmSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instAsymmSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), Std.Asymm (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.asymm (0 : ℕ) (0 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Complex.div_ofNat_re, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Complex.div_ofNat_re.h2 : ¬∀ (z : ℂ) (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h ({ re := { cauchy := 0 : ℝ }, im := { cauchy := 0 : ℝ } : ℂ }) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.instIsStrictTotalOrderSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsStrictTotalOrderSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), IsStrictTotalOrder α (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsStrictOrder.toIrrefl.irrefl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.toReal_le_coe_of_le_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_le_coe_of_le_coe.h2 : ¬∀ {a : ENNReal} {b : NNReal}, a.toReal ≤ ↑b := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- ENNReal.eq_top_of_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eq_top_of_pow.h2 : ¬∀ {a : ENNReal} (n : ℕ), a = ⊤ := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- NNReal.HolderConjugate.sub_one_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderConjugate.sub_one_pos.h2 : ¬∀ {p : NNReal} {q : NNReal}, 0 < p - 1 := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- ENNReal.le_of_forall_pos_le_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_of_forall_pos_le_add.h2 : ¬∀ {a b : ENNReal}, a ≤ b := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- ENNReal.ofNat_le_ofReal, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofNat_le_ofReal.h1 : ¬∀ {n : ℕ} {p : ℝ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h (0) ({ cauchy := 0 : ℝ })) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.toNNReal_lt_of_lt_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_lt_of_lt_coe.h2 : ¬∀ {a : ENNReal} {p : NNReal}, a.toNNReal < p := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- ENNReal.coe_inv', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.coe_inv'.h1 : Not (∀ {r : NNReal}, @Eq ENNReal (↑(@Inv.inv NNReal NNReal.instInv r)) (@Inv.inv ENNReal ENNReal.instInv ↑r)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal NNReal.instZero))) (by
  simp)

-- ENNReal.cancel_of_ne, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.cancel_of_ne.h1 : ¬∀ {a : ENNReal}, AddLECancellable a := fun hc_h => absurd (@hc_h (⊤)) (by
  simp)

-- ENNReal.ofNat_lt_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofNat_lt_top.h1 : ¬∀ {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.half_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.half_pos.h1 : ¬∀ {a : ENNReal}, 0 < a / 2 := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- NNReal.coe_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.coe_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Complex.normSq_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Complex.normSq_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Complex.im_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Complex.im_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- by_contra, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.by_contra.h1 : ¬∀ {p : Prop}, p := fun hc_h => absurd (@hc_h (False)) (by
  decide +kernel)

-- Encodable.decode_ge_two, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Encodable.decode_ge_two.h1 : Not (∀ (n : Nat), @Eq (Option Bool) (@Encodable.decode Bool Bool.encodable n) (@Option.none Bool)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- ENNReal.exists_nat_gt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_nat_gt.h1 : ¬∀ {r : ENNReal}, ∃ (n : ℕ), r < ↑n := fun hc_h => absurd (@hc_h (⊤)) (by
  simp)

-- ENNReal.coe_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.coe_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.top_ne_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.top_ne_ofNat.h1 : ¬∀ {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.coe_inv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.coe_inv.h1 : Not (∀ {r : NNReal}, @Eq ENNReal (↑(@Inv.inv NNReal NNReal.instInv r)) (@Inv.inv ENNReal ENNReal.instInv ↑r)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal NNReal.instZero))) (by
  simp)

-- ENNReal.ofReal_toReal, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_toReal.h1 : ¬∀ {a : ENNReal}, ENNReal.ofReal a.toReal = a := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- eq_true_intro, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.eq_true_intro.h1 : ¬∀ {a : Prop}, a = True := fun hc_h => absurd (@hc_h (False)) (by
  decide +kernel)

-- ENNReal.top_div_of_lt_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.top_div_of_lt_top.h1 : ¬∀ {a : ENNReal}, ⊤ / a = ⊤ := fun hc_h => absurd (@hc_h (⊤)) (by
  simp)

-- ENNReal.exists_inv_nat_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_inv_nat_lt.h1 : ¬∀ {a : ENNReal}, ∃ (n : ℕ), (↑n)⁻¹ < a := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- WithTop.instUncountable, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithTop.instUncountable.h1 : ¬∀ {α : Type}, Uncountable (WithTop α) := fun hc_h => absurd (@hc_h (ℕ)) (by
  simp)

