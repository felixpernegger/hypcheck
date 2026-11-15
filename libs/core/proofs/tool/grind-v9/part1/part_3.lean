import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.CommRing.lt_cancel_of_kronLinS, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h6 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst : Lean.Grind.AddRightCancel α] [inst : LE α] [inst_1 : LT α]
        [inst_2 : Std.LawfulOrderLT α] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (a b a' b' c : Lean.Grind.CommRing.Expr),
        a.linSOk_k (a'.add c) = Bool.true →
          Lean.Grind.CommRing.Expr.kronOk_k K a (a'.add c) = Bool.true →
            Lean.Grind.CommRing.Expr.kronLinEval_k K a = Lean.Grind.CommRing.Expr.kronLinEval_k K (a'.add c) →
              b.linSOk_k (b'.add c) = Bool.true →
                Lean.Grind.CommRing.Expr.kronOk_k K b (b'.add c) = Bool.true →
                  Lean.Grind.CommRing.Expr.kronLinEval_k K b = Lean.Grind.CommRing.Expr.kronLinEval_k K (b'.add c) →
                    Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (@Lean.Grind.AddRightCancel.mk (Int) (@Lean.Grind.Semiring.toAdd Int
      (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))) (by (try dsimp only);   (intros; omega))) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) (0) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.le_cancel_of_kronLinS, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h5 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst : Lean.Grind.AddRightCancel α] [inst : LE α] [inst_1 : LT α]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b a' b' c : Lean.Grind.CommRing.Expr),
        a.linSOk_k (a'.add c) = Bool.true →
          Lean.Grind.CommRing.Expr.kronOk_k K a (a'.add c) = Bool.true →
            Lean.Grind.CommRing.Expr.kronLinEval_k K a = Lean.Grind.CommRing.Expr.kronLinEval_k K (a'.add c) →
              b.linSOk_k (b'.add c) = Bool.true →
                Lean.Grind.CommRing.Expr.kronOk_k K b (b'.add c) = Bool.true →
                  Lean.Grind.CommRing.Expr.kronLinEval_k K b = Lean.Grind.CommRing.Expr.kronLinEval_k K (b'.add c) →
                    Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (@Lean.Grind.AddRightCancel.mk (Int) (@Lean.Grind.Semiring.toAdd Int
      (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))) (by (try dsimp only);   (intros; omega))) (⟨fun _ _ => False⟩ : LE Int) (Int.instLTInt) (.leaf 1 : Lean.RArray Int) (0) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.le_norm_poly, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h4 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst : LE α] [inst_1 : LT α] (ctx : Lean.Grind.CommRing.Context α)
        (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr) (p lp rp : Lean.Grind.CommRing.Poly),
        p = Lean.Grind.CommRing.Expr.toPolyX_k bal (rhs.sub lhs) →
          lhs' = lp.toExpr_k →
            rhs' = rp.toExpr_k →
              p = rp.combine_k (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc 0) lp) → Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (⟨fun _ _ => False⟩ : LE Int) (Int.instLTInt) (.leaf 1 : Lean.RArray Int) (Bool.false) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) _ _ _ (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) rfl rfl rfl (by
  rfl)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.eq_cancel_of_kronS, hypothesis 16: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h16 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst_1 : Lean.Grind.AddRightCancel α]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b a' b' c : Lean.Grind.CommRing.Expr),
        Lean.Grind.CommRing.Expr.degSOk_k B a (a'.add c) = Bool.true →
          Lean.Grind.CommRing.Expr.kronOk_k K a (a'.add c) = Bool.true →
            Lean.Grind.CommRing.Expr.kronEval_k K B a = Lean.Grind.CommRing.Expr.kronEval_k K B (a'.add c) →
              Lean.Grind.CommRing.Expr.degSOk_k B b (b'.add c) = Bool.true →
                Lean.Grind.CommRing.Expr.kronOk_k K b (b'.add c) = Bool.true →
                  (Lean.Grind.CommRing.Expr.denoteS ctx a = Lean.Grind.CommRing.Expr.denoteS ctx b) =
                    (Lean.Grind.CommRing.Expr.denoteS ctx a' = Lean.Grind.CommRing.Expr.denoteS ctx b') := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (@Lean.Grind.AddRightCancel.mk (Int) (@Lean.Grind.Semiring.toAdd Int
      (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) (2) (2) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQ, hypothesis 16: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.sub_mul_eq_of_kronQ.h16 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (invs : Lean.Grind.CommRing.InvVars),
        @Lean.Grind.CommRing.InvVars.ok α inst ctx invs →
          @Eq Bool invs.nonzero_k Bool.true →
            ∀ (d : Nat) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
              @Eq Bool
                  (Lean.Grind.CommRing.Expr.degQOk_k B invs
                    ((lhs.sub rhs).mul (Lean.Grind.CommRing.Expr.num (@Nat.cast Int instNatCastInt d))) (lhs'.sub rhs'))
                  Bool.true →
                @Eq Bool
                    (Lean.Grind.CommRing.Expr.kronQOk_k K invs
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
                        (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs'))) := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 1 : Lean.RArray Rat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) (by
  rfl) (by
  decide) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.Order.le_trans_k, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h4.inst : Not (@Std.IsPreorder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h4.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h4.prem1 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h4 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst] [inst_3 : Lean.Grind.Ring α]
        {a b c : α} {k₁ k₂ : Int} (k : Int),
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₁)) →
          @LE.le α inst b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₂)) →
            @Eq Bool
                (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
                Bool.true →
              @Std.IsPreorder α inst) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_trans_k.h4.inst (@hc_h (Int) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Order.le_trans_k.h4.prem0 HypCheckProof.Lean.Grind.Order.le_trans_k.h4.prem1 (beq_self_eq_true _))

-- Lean.Grind.CommRing.lt_false_of_kronS, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h5.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        False) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h5.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h5.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h5.prem2 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.IsPreorder α inst_2] (ctx : Lean.Grind.CommRing.Context α)
        (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
              @Eq Prop
                (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                  (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
                False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h5.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk (Int) (@Lean.Grind.Semiring.toAdd Int
      (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))) (by (try dsimp only);   (intros; omega))) (Int.instLEInt) (@LT.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt a b) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h5.prem0 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h5.prem1 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h5.prem2)

-- Lean.Grind.CommRing.lt_norm_exprC_nc, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_exprC_nc.h7 : ¬∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α] [inst : Lean.Grind.IsCharP α c] [inst : LE α] [inst_1 : LT α]
        [inst_2 : Std.LawfulOrderLT α] (ctx : Lean.Grind.CommRing.Context α) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
        Lean.Grind.CommRing.norm_cnstrC_nc_cert lhs rhs lhs' rhs' c = Bool.true → Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (0) (Lean.Grind.instCommRingInt.toRing) _ (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.lt_false_of_kronSN, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h4.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        False) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h4.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h4.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h4.prem2 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
              @Eq Prop
                (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                  (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
                False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h4.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (Int.instLEInt) (@LT.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt a b) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h4.prem0 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h4.prem1 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h4.prem2)

-- Lean.Grind.Linarith.diseq_split_resolve, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h4.inst : Not False := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h4.prem0 : @Eq Bool
      (Lean.Grind.Linarith.diseq_split_cert
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h4.prem1 : @Ne Int
      (@Lean.Grind.Linarith.Poly.denote' Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h4.prem2 : Not False := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsLinearOrder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 (@Std.IsLinearPreorder.toIsPreorder α inst_1 (@Std.IsLinearOrder.toIsLinearPreorder α inst_1 inst_3))]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.diseq_split_cert p₁ p₂) Bool.true →
          @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            Not
                (@LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
                  (@OfNat.ofNat α (nat_lit 0)
                    (@Zero.toOfNat0 α
                      (@Lean.Grind.AddCommMonoid.toZero α
                        (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) →
              @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
                (@OfNat.ofNat α (nat_lit 0)
                  (@Zero.toOfNat0 α
                    (@Lean.Grind.AddCommMonoid.toZero α
                      (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h4.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (@LT.mk Int fun (x x_1 : Int) => False) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h4.prem0 HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h4.prem1 HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h4.prem2)

-- Lean.Grind.Linarith.diseq_split_resolve, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h5 : ¬∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ : Lean.Grind.Linarith.Poly),
        Lean.Grind.Linarith.diseq_split_cert p₁ p₂ = Bool.true →
          Lean.Grind.Linarith.Poly.denote' ctx p₁ ≠ 0 → ¬Lean.Grind.Linarith.Poly.denote' ctx p₁ < 0 → Std.IsLinearOrder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Ring.toIntModule) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) (.add 1 0 .nil : Lean.Grind.Linarith.Poly) (.add (-1) 0 .nil : Lean.Grind.Linarith.Poly) (by
  decide) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPartialOrder.toIsPreorder.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

