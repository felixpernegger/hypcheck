import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.CommRing.le_normQ_expr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.le_normQ_expr.h6 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] [inst_2 : LE α] [inst_3 : LT α]
        [inst_4 : Std.LawfulOrderLT α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
                Lean.Grind.CommRing.normQ_cert bal invs ainvs lhs rhs lhs' rhs' = Bool.true → Std.IsLinearOrder α := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (⟨fun a b => a < b⟩ : LE Rat) (Rat.instLT) (@Std.LawfulOrderLT.mk (Rat) (Rat.instLT) (@LE.mk Rat fun (a b : Rat) => @LT.lt Rat Rat.instLT a b) (by (try dsimp only);   grind)) (.leaf 1 : Lean.RArray Rat) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPartialOrder.toIsPreorder.le_refl (0 : Rat))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.le_normQ_expr, hypothesis 18: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.le_normQ_expr.h18 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] [inst_2 : LE α] [inst_3 : LT α]
        [inst_4 : Std.LawfulOrderLT α] [inst_5 : Std.IsLinearOrder α] [inst_6 : Lean.Grind.OrderedRing α]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
                (Lean.Grind.CommRing.Expr.denote ctx lhs ≤ Lean.Grind.CommRing.Expr.denote ctx rhs) =
                  (Lean.Grind.CommRing.Expr.denote ctx lhs' ≤ Lean.Grind.CommRing.Expr.denote ctx rhs') := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (Rat.instLE) (Rat.instLT) _ _ _ (.leaf 1 : Lean.RArray Rat) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQLin, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQLin.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (invs : Lean.Grind.CommRing.InvVars),
        @Lean.Grind.CommRing.InvVars.ok α inst ctx invs →
          ∀ (d : Nat) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
            @Eq Bool
                (Lean.Grind.CommRing.Expr.linQOk_k invs
                  ((lhs.sub rhs).mul (Lean.Grind.CommRing.Expr.num (@Nat.cast Int instNatCastInt d))) (lhs'.sub rhs'))
                Bool.true →
              @Eq Bool
                  (Lean.Grind.CommRing.Expr.kronQOk_k K invs
                    ((lhs.sub rhs).mul (Lean.Grind.CommRing.Expr.num (@Nat.cast Int instNatCastInt d))) (lhs'.sub rhs'))
                  Bool.true →
                @Eq Bool
                    (Lean.Grind.CommRing.Expr.kronQLinEq_k K invs
                      ((lhs.sub rhs).mul (Lean.Grind.CommRing.Expr.num (@Nat.cast Int instNatCastInt d))) (lhs'.sub rhs'))
                    Bool.true →
                  @Eq α
                    (@HMul.hMul α α α
                      (@instHMul α
                        (@Lean.Grind.Semiring.toMul α
                          (@Lean.Grind.CommSemiring.toSemiring α
                            (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
                      (@HSub.hSub α α α
                        (@instHSub α
                          (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))))
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs)
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs))
                      (@Nat.cast α
                        (@Lean.Grind.Semiring.natCast α
                          (@Lean.Grind.CommSemiring.toSemiring α
                            (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
                        d))
                    (@HSub.hSub α α α
                      (@instHSub α
                        (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))))
                      (@Lean.Grind.CommRing.Expr.denote α
                        (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs')
                      (@Lean.Grind.CommRing.Expr.denote α
                        (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs'))) := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 0 : Lean.RArray Rat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.cons (Prod Lean.Grind.CommRing.Var Nat)
      (@Prod.mk Lean.Grind.CommRing.Var Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 1 : Lean.Grind.CommRing.Expr) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.d_stepsMC, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsMC.h13 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k : Int) (init : Lean.Grind.CommRing.Poly) (K B : Nat)
        (p₁ p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly) (ls : Lean.Grind.CommRing.MList),
        @Eq Bool
            ((Lean.Grind.CommRing.Poly.kron_k K B p).beq'
              (((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k (Lean.Grind.CommRing.MList.kron_k K B ls)).add_k
                ((Int.ofNat c).mul_k (Lean.Grind.CommRing.PPoly.kron_k K E))))
            Bool.true →
          @Lean.Grind.CommRing.MList.AllZero α (@Lean.Grind.CommRing.toRing α inst) ctx ls →
            @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁) →
              @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => absurd (@hc_h (Int : Type) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (.leaf 0 : Lean.RArray Int) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (.num 0 : Lean.Grind.CommRing.Poly) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.PPoly) (.nil : Lean.Grind.CommRing.MList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.d_stepsMC, hypothesis 16: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsMC.h16 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k : Int) (init : Lean.Grind.CommRing.Poly) (K B : Nat)
        (p₁ p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly) (ls : Lean.Grind.CommRing.MList),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.kronOkM_k K B c p₁ p E ls) Bool.true →
          @Eq Bool
              ((Lean.Grind.CommRing.Poly.kron_k K B p).beq'
                (((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k (Lean.Grind.CommRing.MList.kron_k K B ls)).add_k
                  ((Int.ofNat c).mul_k (Lean.Grind.CommRing.PPoly.kron_k K E))))
              Bool.true →
            @Lean.Grind.CommRing.MList.AllZero α (@Lean.Grind.CommRing.toRing α inst) ctx ls →
              @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => absurd (@hc_h (Int : Type) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (.leaf 1 : Lean.RArray Int) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.PPoly) (.nil : Lean.Grind.CommRing.MList) (by
  decide) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.simpsMC, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsMC.h11 : ¬∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] [inst_1 : Lean.Grind.IsCharP α c]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (p₁ p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly)
        (ls : Lean.Grind.CommRing.MList),
        (Lean.Grind.CommRing.Poly.kron_k K B p).beq'
              (((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k (Lean.Grind.CommRing.MList.kron_k K B ls)).add_k
                ((Int.ofNat c).mul_k (Lean.Grind.CommRing.PPoly.kron_k K E))) =
            Bool.true →
          Lean.Grind.CommRing.MList.AllZero ctx ls →
            Lean.Grind.CommRing.Poly.denote ctx p₁ = 0 → Lean.Grind.CommRing.Poly.denote ctx p = 0 := fun hc_h => absurd (@hc_h (Int : Type) (0) (Lean.Grind.instCommRingInt) _ (.leaf 0 : Lean.RArray Int) (0) (0) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.PPoly) (.nil : Lean.Grind.CommRing.MList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.simpsMC, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsMC.h12 : ¬∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] [inst_1 : Lean.Grind.IsCharP α c]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (p₁ p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly)
        (ls : Lean.Grind.CommRing.MList),
        Lean.Grind.CommRing.Stepwise.kronOkM_k K B c p₁ p E ls = Bool.true →
          Lean.Grind.CommRing.MList.AllZero ctx ls →
            Lean.Grind.CommRing.Poly.denote ctx p₁ = 0 → Lean.Grind.CommRing.Poly.denote ctx p = 0 := fun hc_h => absurd (@hc_h (Int : Type) (0) (Lean.Grind.instCommRingInt) _ (.leaf 1 : Lean.RArray Int) (2) (2) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.PPoly) (.nil : Lean.Grind.CommRing.MList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.lt_normA_expr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_normA_expr.h5 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
        (ctx : Lean.Grind.CommRing.Context α) (ainvs : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
          ∀ (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
            Lean.Grind.CommRing.normA_cert ainvs lhs rhs lhs' rhs' = Bool.true → Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.lt_normA_expr, hypothesis 14: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_normA_expr.h14 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
        [inst_4 : Std.IsPreorder α] [inst_5 : Lean.Grind.OrderedRing α] (ctx : Lean.Grind.CommRing.Context α)
        (ainvs : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
          ∀ (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
            (Lean.Grind.CommRing.Expr.denote ctx lhs < Lean.Grind.CommRing.Expr.denote ctx rhs) =
              (Lean.Grind.CommRing.Expr.denote ctx lhs' < Lean.Grind.CommRing.Expr.denote ctx rhs') := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (.leaf 1 : Lean.RArray Int) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.d_stepsM, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsM.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (init : Lean.Grind.CommRing.Poly) (K B : Nat) (p₁ p : Lean.Grind.CommRing.Poly) (ls : Lean.Grind.CommRing.MList),
        @Eq Bool
            ((Lean.Grind.CommRing.Poly.kron_k K B p).beq'
              ((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k (Lean.Grind.CommRing.MList.kron_k K B ls)))
            Bool.true →
          @Lean.Grind.CommRing.MList.AllZero α (@Lean.Grind.CommRing.toRing α inst) ctx ls →
            @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁) →
              @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 0 : Lean.RArray Int) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (.num 0 : Lean.Grind.CommRing.Poly) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (.nil : Lean.Grind.CommRing.MList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.d_stepsM, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsM.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (init : Lean.Grind.CommRing.Poly) (K B : Nat) (p₁ p : Lean.Grind.CommRing.Poly) (ls : Lean.Grind.CommRing.MList),
        @Eq Bool
            (Lean.Grind.CommRing.Stepwise.kronOkM_k K B (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p₁ p
              (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ls)
            Bool.true →
          @Lean.Grind.CommRing.MList.AllZero α (@Lean.Grind.CommRing.toRing α inst) ctx ls →
            @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁) →
              @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 1 : Lean.RArray Int) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (.num 0 : Lean.Grind.CommRing.Poly) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.nil : Lean.Grind.CommRing.MList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.d_stepsM, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsM.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (init : Lean.Grind.CommRing.Poly) (K B : Nat) (p₁ p : Lean.Grind.CommRing.Poly) (ls : Lean.Grind.CommRing.MList),
        @Eq Bool
            (Lean.Grind.CommRing.Stepwise.kronOkM_k K B (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p₁ p
              (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ls)
            Bool.true →
          @Eq Bool
              ((Lean.Grind.CommRing.Poly.kron_k K B p).beq'
                ((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k (Lean.Grind.CommRing.MList.kron_k K B ls)))
              Bool.true →
            @Lean.Grind.CommRing.MList.AllZero α (@Lean.Grind.CommRing.toRing α inst) ctx ls →
              @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 1 : Lean.RArray Int) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) (.nil : Lean.Grind.CommRing.MList) (by
  decide) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  decide +kernel)

-- Lean.Grind.CommRing.MList.denote_eq, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.MList.denote_eq.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B c : Nat)
        (p₁ p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly) (ls : Lean.Grind.CommRing.MList),
        And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B)
            (And (@LT.lt Nat instLTNat p.maxDeg_k B)
              (And (@LT.lt Nat instLTNat p₁.maxDeg_k B) (@Eq Bool (Lean.Grind.CommRing.MList.ok_k B ls) Bool.true))) →
          @LT.lt Nat instLTNat
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) p.norm1_k p₁.norm1_k) ls.norm_k)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) c E.norm1_k)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) K) →
            @Lean.Grind.CommRing.MList.AllZero α (@Lean.Grind.CommRing.toRing α inst) ctx ls →
              @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
                (@HAdd.hAdd α α α
                  (@instHAdd α
                    (@Lean.Grind.Semiring.toAdd α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
                  (@HMul.hMul α α α
                    (@instHMul α
                      (@Lean.Grind.Semiring.toMul α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                    (@Nat.cast α
                      (@Lean.Grind.Semiring.natCast α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))
                      c)
                    (@Lean.Grind.CommRing.PPoly.denote α (@Lean.Grind.CommRing.toRing α inst)
                      (@Lean.Grind.CommRing.Var.denote α ctx) B E)))) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 1 : Lean.RArray Int) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.PPoly) (.nil : Lean.Grind.CommRing.MList) (by
  decide) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  decide +kernel)

-- Lean.Grind.CommRing.KList.denote_eq, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.KList.denote_eq.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B c : Nat)
        (p₁ p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly) (ls : Lean.Grind.CommRing.KList),
        And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B)
            (And (@LT.lt Nat instLTNat p.maxDeg_k B)
              (And (@LT.lt Nat instLTNat p₁.maxDeg_k B) (@Eq Bool (Lean.Grind.CommRing.KList.ok_k B ls) Bool.true))) →
          @LT.lt Nat instLTNat
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) p.norm1_k p₁.norm1_k) ls.norm_k)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) c E.norm1_k)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) K) →
            @Lean.Grind.CommRing.KList.AllZero α (@Lean.Grind.CommRing.toRing α inst) ctx ls →
              @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
                (@HAdd.hAdd α α α
                  (@instHAdd α
                    (@Lean.Grind.Semiring.toAdd α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
                  (@HMul.hMul α α α
                    (@instHMul α
                      (@Lean.Grind.Semiring.toMul α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                    (@Nat.cast α
                      (@Lean.Grind.Semiring.natCast α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))
                      c)
                    (@Lean.Grind.CommRing.PPoly.denote α (@Lean.Grind.CommRing.toRing α inst)
                      (@Lean.Grind.CommRing.Var.denote α ctx) B E)))) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 1 : Lean.RArray Int) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.PPoly) (.nil : Lean.Grind.CommRing.KList) (by
  decide) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS.h10 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst_1 : Lean.Grind.AddRightCancel α]
        (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.PPoly),
        p = Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a →
          p = Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b →
            Lean.Grind.CommRing.Expr.denoteS ctx a = Lean.Grind.CommRing.Expr.denoteS ctx b := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (@Lean.Grind.AddRightCancel.mk (Int) (@Lean.Grind.Semiring.toAdd Int
      (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))) (by (try dsimp only);   (intros; omega))) (.branch 1 (.leaf 1) (.leaf 2) : Lean.RArray Int) (1) (Bool.false) (Bool.false) (.var 0 : Lean.Grind.CommRing.Expr) (.var 1 : Lean.Grind.CommRing.Expr) _ rfl (by
  rfl)) (by
  decide +kernel)

-- Lean.Grind.CommRing.eq_true_of_polyQ0, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_polyQ0.h6 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal : Bool) (invs : Lean.Grind.CommRing.InvVars) (ainvs : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
          ∀ (lhs rhs : Lean.Grind.CommRing.Expr),
            (Lean.Grind.CommRing.Poly.toPolyQX_k bal (Lean.Grind.CommRing.Expr.toPolyX_k bal (lhs.sub rhs)) invs
                    ainvs).num =
                Lean.Grind.CommRing.Poly.num 0 →
              (Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Expr.denote ctx rhs) = True := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 0 : Lean.RArray Rat) (Bool.false) ([(0, 1)]) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.var 0 : Lean.Grind.CommRing.Expr) (.num 1 : Lean.Grind.CommRing.Expr) (by
  rfl)) (by
  decide +kernel)

-- Lean.Grind.CommRing.eq_true_of_polyQ0, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_polyQ0.h11 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal : Bool) (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (lhs rhs : Lean.Grind.CommRing.Expr),
                (Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Expr.denote ctx rhs) = True := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 1 : Lean.RArray Rat) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.eq_of_toPolyQ_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyQ_eq.h6 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal : Bool) (invs : Lean.Grind.CommRing.InvVars) (ainvs : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
          ∀ (a b : Lean.Grind.CommRing.Expr),
            Lean.Grind.CommRing.Expr.toPolyQ_cert bal invs ainvs a b = Bool.true →
              Lean.Grind.CommRing.Expr.denote ctx a = Lean.Grind.CommRing.Expr.denote ctx b := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 0 : Lean.RArray Rat) (Bool.false) ([(0, 1)]) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.var 0 : Lean.Grind.CommRing.Expr) (.num 1 : Lean.Grind.CommRing.Expr) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.eq_of_toPolyQ_eq, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyQ_eq.h11 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal : Bool) (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (a b : Lean.Grind.CommRing.Expr),
                Lean.Grind.CommRing.Expr.denote ctx a = Lean.Grind.CommRing.Expr.denote ctx b := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 1 : Lean.RArray Rat) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.denoteSN_powTL, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denoteSN_powTL.h7 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (f : Nat → α) {B D : Nat},
        1 < B →
          ∀ {p : Lean.Grind.CommRing.PPoly},
            Lean.Grind.CommRing.PPoly.Deg B D p →
              ∀ (k : Nat),
                D * k < B →
                  Lean.Grind.CommRing.PPoly.denoteSN f B (p.powTL k) = Lean.Grind.CommRing.PPoly.denoteSN f B p ^ k := fun hc_h => absurd (@hc_h (Nat) (Lean.Grind.instCommSemiringNat) (fun n => n + 1 : Nat → Nat) (2) (0) (by
  decide) (.num (-1) : Lean.Grind.CommRing.PPoly) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (2) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denote_toPolyQ, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_toPolyQ.h7 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (p : Lean.Grind.CommRing.Poly) (invs : Lean.Grind.CommRing.InvVars) (ainvs : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
          Lean.Grind.CommRing.PolyQ.denote ctx (p.toPolyQ invs ainvs) = Lean.Grind.CommRing.Poly.denote ctx p := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 0 : Lean.RArray Rat) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) ([(0, 1)]) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_mul_go, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_mul_go.h6 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ acc : Lean.Grind.CommRing.Poly),
        p₂.NonnegCoeffs →
          acc.NonnegCoeffs →
            Lean.Grind.CommRing.Poly.denoteS ctx (Lean.Grind.CommRing.Poly.mul.go p₂ p₁ acc) =
              Lean.Grind.CommRing.Poly.denoteS ctx acc +
                Lean.Grind.CommRing.Poly.denoteS ctx p₁ * Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num (-1) : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add))) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_mul_go, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_mul_go.h7 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ acc : Lean.Grind.CommRing.Poly),
        p₁.NonnegCoeffs →
          acc.NonnegCoeffs →
            Lean.Grind.CommRing.Poly.denoteS ctx (Lean.Grind.CommRing.Poly.mul.go p₂ p₁ acc) =
              Lean.Grind.CommRing.Poly.denoteS ctx acc +
                Lean.Grind.CommRing.Poly.denoteS ctx p₁ * Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num (-1) : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add))) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_mul_go, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_mul_go.h8 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ acc : Lean.Grind.CommRing.Poly),
        p₁.NonnegCoeffs →
          p₂.NonnegCoeffs →
            Lean.Grind.CommRing.Poly.denoteS ctx (Lean.Grind.CommRing.Poly.mul.go p₂ p₁ acc) =
              Lean.Grind.CommRing.Poly.denoteS ctx acc +
                Lean.Grind.CommRing.Poly.denoteS ctx p₁ * Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (.num 1 : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (.num (-1) : Lean.Grind.CommRing.Poly) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add))) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.monDenote_mul_pow, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.monDenote_mul_pow.h8 : ¬∀ {B : Nat} {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Nat → α),
        1 < B → ∀ (i x k : Nat), Lean.Grind.CommRing.PPoly.monDenote ctx B i (k * B ^ x) = ctx (i + x) ^ k := fun hc_h => absurd (@hc_h (2) (Nat) (Lean.Grind.instCommSemiringNat.toSemiring) (fun n => n + 1 : Nat → Nat) (by
  decide) (0) (0) (2)) (by
  decide +kernel)

-- Lean.Grind.CommRing.KList.allZero_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.KList.allZero_cons.h7 : ¬∀ {α : Type} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α) (k : Int) (m : Lean.Grind.CommRing.Mon)
        (q : Lean.Grind.CommRing.Poly) (ls : Lean.Grind.CommRing.KList),
        Lean.Grind.CommRing.KList.AllZero ctx ls →
          Lean.Grind.CommRing.KList.AllZero ctx (Lean.Grind.CommRing.KList.cons k m q ls) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (.leaf 1 : Lean.RArray Int) (0) (.unit : Lean.Grind.CommRing.Mon) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.nil : Lean.Grind.CommRing.KList) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))

-- Lean.Grind.CommRing.KList.allZero_cons, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.KList.allZero_cons.h8 : ¬∀ {α : Type} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α) (k : Int) (m : Lean.Grind.CommRing.Mon)
        (q : Lean.Grind.CommRing.Poly) (ls : Lean.Grind.CommRing.KList),
        Lean.Grind.CommRing.Poly.denote ctx q = 0 →
          Lean.Grind.CommRing.KList.AllZero ctx (Lean.Grind.CommRing.KList.cons k m q ls) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (.leaf 1 : Lean.RArray Int) (0) (.unit : Lean.Grind.CommRing.Mon) (.num 0 : Lean.Grind.CommRing.Poly) (.cons 1 .unit (.num 1) .nil : Lean.Grind.CommRing.KList) (by
  decide)) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))

-- Lean.Grind.CommRing.PPoly.denoteSN_addConst, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denoteSN_addConst.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (f : Nat → α) (B : Nat) {q : Lean.Grind.CommRing.PPoly} {k : Int},
        q.NonNeg →
          @Eq α (@Lean.Grind.CommRing.PPoly.denoteSN α inst f B (Lean.Grind.CommRing.PPoly.append.addConst q k))
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α inst))
              (@Lean.Grind.CommRing.PPoly.denoteSN α inst f B q)
              (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) k.toNat))) := fun hc_h => absurd (@hc_h (Nat) (@Lean.Grind.CommSemiring.toSemiring Nat Lean.Grind.instCommSemiringNat) (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (.num 1 : Lean.Grind.CommRing.PPoly) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  decide +kernel)

-- Lean.Grind.CommRing.PolyQ.denote_substInv, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PolyQ.denote_substInv.h7 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (q : Lean.Grind.CommRing.PolyQ) (x : Lean.Grind.CommRing.Var) (c : Nat),
        Lean.Grind.CommRing.PolyQ.denote ctx (q.substInv x c) = Lean.Grind.CommRing.PolyQ.denote ctx q := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 1 : Lean.RArray Rat) ({
      num :=
        Lean.Grind.CommRing.Poly.add 1
          (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num 0),
      den := 1 : Lean.Grind.CommRing.PolyQ }) (0) (2)) (by
  decide +kernel)

-- Lean.Grind.CommRing.InvAtoms.ok_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.InvAtoms.ok_cons.h6 : ¬∀ {α : Type} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α) (y x : Lean.Grind.CommRing.Var)
        (l : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.InvAtoms.ok ctx l → Lean.Grind.CommRing.InvAtoms.ok ctx ((y, x) :: l) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (.leaf 0 : Lean.RArray Int) (0) (0) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))

-- Lean.Grind.CommRing.InvAtoms.ok_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.InvAtoms.ok_cons.h7 : ¬∀ {α : Type} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α) (y x : Lean.Grind.CommRing.Var)
        (l : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.Var.denote ctx x * Lean.Grind.CommRing.Var.denote ctx y = 1 →
          Lean.Grind.CommRing.InvAtoms.ok ctx ((y, x) :: l) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (.branch 1 (.leaf 1) (.leaf 2) : Lean.RArray Int) (0) (0) ([(0, 1)]) (by
  decide)) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))

-- Lean.Grind.CommRing.Poly.denoteS_insert, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_insert.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (m : Lean.Grind.CommRing.Mon) (p : Lean.Grind.CommRing.Poly),
        p.NonnegCoeffs →
          @Eq α (@Lean.Grind.CommRing.Poly.denoteS α inst ctx (Lean.Grind.CommRing.Poly.insert k m p))
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α inst))
              (@HMul.hMul α α α (@instHMul α (@Lean.Grind.Semiring.toMul α inst))
                (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) k.toNat) (@Lean.Grind.CommRing.Mon.denote α inst ctx m))
              (@Lean.Grind.CommRing.Poly.denoteS α inst ctx p))) := fun hc_h => absurd (@hc_h (Int : Type) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (.leaf 1 : Lean.RArray Int) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (.unit : Lean.Grind.CommRing.Mon) (.num 1 : Lean.Grind.CommRing.Poly) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.denoteSN_append, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denoteSN_append.h6 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] (f : Nat → α) (B : Nat) {p q : Lean.Grind.CommRing.PPoly},
        q.NonNeg →
          Lean.Grind.CommRing.PPoly.denoteSN f B (p.append q) =
            Lean.Grind.CommRing.PPoly.denoteSN f B p + Lean.Grind.CommRing.PPoly.denoteSN f B q := fun hc_h => absurd (@hc_h (Nat) (Lean.Grind.instCommSemiringNat.toSemiring) (fun n => n + 1 : Nat → Nat) (0) (.num (-1) : Lean.Grind.CommRing.PPoly) (.num 1 : Lean.Grind.CommRing.PPoly) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.denoteSN_append, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denoteSN_append.h7 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] (f : Nat → α) (B : Nat) {p q : Lean.Grind.CommRing.PPoly},
        p.NonNeg →
          Lean.Grind.CommRing.PPoly.denoteSN f B (p.append q) =
            Lean.Grind.CommRing.PPoly.denoteSN f B p + Lean.Grind.CommRing.PPoly.denoteSN f B q := fun hc_h => absurd (@hc_h (Nat) (Lean.Grind.instCommSemiringNat.toSemiring) (fun n => n + 1 : Nat → Nat) (0) (.num 1 : Lean.Grind.CommRing.PPoly) (.num (-1) : Lean.Grind.CommRing.PPoly) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_addConst, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_addConst.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly)
        (k : Int),
        p.NonnegCoeffs →
          @Eq α (@Lean.Grind.CommRing.Poly.denoteS α inst ctx (p.addConst k))
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α inst))
              (@Lean.Grind.CommRing.Poly.denoteS α inst ctx p) (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) k.toNat))) := fun hc_h => absurd (@hc_h (Int : Type) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (.leaf 1 : Lean.RArray Int) (.num 1 : Lean.Grind.CommRing.Poly) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Mon.code_k_spec, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Mon.code_k_spec.h6 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) {B : Nat},
        1 < B →
          ∀ (m : Lean.Grind.CommRing.Mon),
            Lean.Grind.CommRing.PPoly.dsum B (Lean.Grind.CommRing.Mon.code_k B m) = m.degree ∧
              Lean.Grind.CommRing.PPoly.monDenote (Lean.Grind.CommRing.Var.denote ctx) B 0
                  (Lean.Grind.CommRing.Mon.code_k B m) =
                Lean.Grind.CommRing.Mon.denote ctx m := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (.leaf 1 : Lean.RArray Int) (2) (by
  decide) (.mult ⟨0, 2⟩ .unit : Lean.Grind.CommRing.Mon)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.coeff_eq_zero_of_kron, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.coeff_eq_zero_of_kron.h5 : ¬∀ (X : Int),
        0 < X →
          ∀ (c : Nat) (p : Lean.Grind.CommRing.PPoly),
            Lean.Grind.CommRing.PPoly.kron X p = 0 → Lean.Grind.CommRing.PPoly.coeff c p = 0 := fun hc_h => absurd (@hc_h (1) (by
  decide) (0) (.add 1 1 1 (.num (-1)) : Lean.Grind.CommRing.PPoly) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.IsCharP.natCast_eq_zero_iff_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IsCharP.natCast_eq_zero_iff_of_lt.h5 : Not
      (∀ {α : Type} (p : Nat) [inst : Lean.Grind.Semiring α] [inst_1 : @Lean.Grind.IsCharP α inst p] {x : Nat},
        Iff
          (@Eq α (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) x)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.Semiring.toNatModule α inst))))))
          (@Eq Nat x (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (Fin 2 : Type) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Lean.Grind.CommSemiring.toSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Lean.Grind.CommRing.toCommSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Lean.Grind.Fin.instCommRingFinOfNeZeroNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) _ (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- Lean.Grind.Field.intCast_div_of_dvd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Field.intCast_div_of_dvd.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] {x y : Int},
        @Dvd.dvd Int Int.instDvd y x →
          @Eq α
            (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)))
              (@HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv) x y))
            (@HDiv.hDiv α α α (@instHDiv α (@Lean.Grind.Field.toDiv α inst))
              (@Int.cast α
                (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))) x)
              (@Int.cast α
                (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))) y))) := fun hc_h => absurd (@hc_h (Fin 2 : Type) ({ (inferInstance : Lean.Grind.CommRing (Fin 2)) with inv := id, div := (· * ·), zpow := ⟨fun a n => a ^ n.natAbs⟩, div_eq_mul_inv := (by decide), zero_ne_one := (by decide), inv_zero := (by decide), mul_inv_cancel := (by decide), zpow_zero := fun a => Lean.Grind.Semiring.pow_zero a, zpow_succ := fun a n => Lean.Grind.Semiring.pow_succ a n, zpow_neg := (by intro a n; show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]) } : Lean.Grind.Field (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.Deg.mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.Deg.mono.h3 : ¬∀ {B D D' : Nat} (p : Lean.Grind.CommRing.PPoly),
        Lean.Grind.CommRing.PPoly.Deg B D p → Lean.Grind.CommRing.PPoly.Deg B D' p := fun hc_h => absurd (@hc_h (2) (1) (0) (.add 2 1 1 (.num 0) : Lean.Grind.CommRing.PPoly) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))

-- Lean.Grind.CommRing.PPoly.Deg.mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.Deg.mono.h5 : ¬∀ {B D D' : Nat}, D ≤ D' → ∀ (p : Lean.Grind.CommRing.PPoly), Lean.Grind.CommRing.PPoly.Deg B D' p := fun hc_h => absurd (@hc_h (2) (0) (0) (by
  decide) (.add 2 1 1 (.num 0) : Lean.Grind.CommRing.PPoly)) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))

-- Lean.Grind.CommRing.PPoly.coeff_zero_of_kron, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.coeff_zero_of_kron.h4 : ¬∀ (X : Int),
        0 < X →
          ∀ (p : Lean.Grind.CommRing.PPoly),
            Lean.Grind.CommRing.PPoly.kron X p = 0 →
              Lean.Grind.CommRing.PPoly.coeff 0 p = 0 ∧ Lean.Grind.CommRing.PPoly.kron X p.shiftDown = 0 := fun hc_h => absurd (@hc_h (1) (by
  decide) (.add 1 1 1 (.num (-1)) : Lean.Grind.CommRing.PPoly) (by
  decide)) (by
  decide +kernel)

